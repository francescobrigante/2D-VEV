# training script for RL agent using Stable Baselines3 PPO

import os
import json
from datetime import datetime

# fixes threading issues on macos
os.environ["OMP_NUM_THREADS"] = "1"
os.environ["MKL_NUM_THREADS"] = "1" 
os.environ["NUMEXPR_NUM_THREADS"] = "1"
os.environ["VECLIB_MAXIMUM_THREADS"] = "1"

import multiprocessing
multiprocessing.set_start_method('spawn', force=True)

import torch
from stable_baselines3 import PPO
from stable_baselines3.common.vec_env import DummyVecEnv
from stable_baselines3.common.callbacks import BaseCallback
from maze_env import DigitalEnvironment
from dataset_manager import DatasetManager
import random
from gymnasium import spaces
import numpy as np


try:
    from tqdm import tqdm
except ImportError:
    def tqdm(iterable, **kwargs):
        return iterable

# training constants
ALGORITHM = "PPO"
TOTAL_TIMESTEPS = 100000  # training steps
N_ENVS = 1                # number of parallel environments (macos set to 1)
MODEL_DIR = "models"
LOG_DIR = "logs"
MODEL_NAME_BASE = "verified"
MODEL_APPEND_TIMESTAMP = False   # save with fixed name if False


# callback class to show training progress
class TrainingProgressCallback(BaseCallback):
    
    def __init__(self, total_timesteps: int):
        super().__init__()
        self.total_timesteps = total_timesteps
        self.pbar = None
        self.episode_rewards = []
        self.episode_lengths = []
        self.goals_reached = 0
        self.total_episodes = 0
    
    def _on_training_start(self):
        self.pbar = tqdm(total=self.total_timesteps, desc="training", unit="steps")
    
    def _on_step(self) -> bool:
        # update progress bar
        self.pbar.update(1)
        
        # check if episode ended
        if self.locals.get('dones', [False])[0]:
            self.total_episodes += 1
            
            # get episode info
            info = self.locals.get('infos', [{}])[0]
            if 'episode' in info:
                episode_reward = info['episode']['r']
                episode_length = info['episode']['l']
                
                self.episode_rewards.append(episode_reward)
                self.episode_lengths.append(episode_length)
                
            # count success also via env info
            if info.get('goal_reached', False):
                self.goals_reached += 1
                
                # update progress bar with stats
                if len(self.episode_rewards) > 0:
                    avg_reward = sum(self.episode_rewards[-10:]) / min(10, len(self.episode_rewards))
                    avg_length = sum(self.episode_lengths[-10:]) / min(10, len(self.episode_lengths))
                    success_rate = self.goals_reached / self.total_episodes if self.total_episodes > 0 else 0
                    
                    self.pbar.set_postfix({
                        'episodes': self.total_episodes,
                        'avg_reward': f'{avg_reward:.1f}',
                        'avg_length': f'{avg_length:.0f}',
                        'success_rate': f'{success_rate:.1%}',
                        'goals': self.goals_reached
                    })
        
        return True
    
    def _on_training_end(self):
        if self.pbar:
            self.pbar.close()
        
        # final statistics
        if self.total_episodes > 0:
            final_success_rate = self.goals_reached / self.total_episodes
            avg_reward = sum(self.episode_rewards) / len(self.episode_rewards) if self.episode_rewards else 0
            
            print(f"\ntraining completed!")
            print(f"total episodes: {self.total_episodes}")
            print(f"goals reached: {self.goals_reached}")
            print(f"final success rate: {final_success_rate:.1%}")
            print(f"average reward: {avg_reward:.1f}")



# main training function
def train_agent(dataset_path: str) -> str:
    
    # create directories
    os.makedirs(MODEL_DIR, exist_ok=True)
    os.makedirs(LOG_DIR, exist_ok=True)
    
    # load training environments
    manager = DatasetManager()
    dataset = manager.load_dataset(dataset_path)
    
    # collect all mazes from the dataset
    maze_entries = []
    for key, value in dataset.items():
        if isinstance(value, list) and key.endswith('environments'):
            maze_entries.extend(value)
    mazes = [env_data['maze'] for env_data in maze_entries if isinstance(env_data, dict) and 'maze' in env_data]
    max_dim = max((max(len(m), len(m[0])) for m in mazes), default=None)
    
    print(f"loaded {len(mazes)} training environments (full dataset)")
    
    # function to create a gymnasym env taking a random digital env at each reset
    def make_env(rank: int):
        def _init():
            # create base env with any maze (will be randomized on reset)
            base_maze = mazes[0] if len(mazes) > 0 else None
            env = DigitalEnvironment(maze=base_maze)

            # keep observation space bound large enough for all mazes
            if max_dim is not None:
                env.observation_space = spaces.Box(low=0, high=max_dim, shape=(5,), dtype=np.int32)

            original_reset = env.reset

            def reset_with_randomization(seed=None, options=None):
                if len(mazes) > 0:
                    chosen = random.choice(mazes)
                    # swap maze and dimensions before calling the original reset
                    env.maze = chosen
                    env.height = len(chosen)
                    env.width = len(chosen[0])
                return original_reset(seed=seed, options=options)

            env.reset = reset_with_randomization
            return env
        return _init
    
    # create vectorized environment
    env = DummyVecEnv([make_env(i) for i in range(N_ENVS)])
    # wrap with VecMonitor to collect episode info (reward/length)
    from stable_baselines3.common.vec_env import VecMonitor
    env = VecMonitor(env)
    
    # initialize ppo model
    model = PPO(
        "MlpPolicy", 
        env, 
        verbose=1, 
        tensorboard_log=LOG_DIR,
        learning_rate=1e-4,
        batch_size=64,
        n_epochs=4,
        gamma=0.99,          # discount factor
        gae_lambda=0.95,
        clip_range=0.2,
        ent_coef=0.05,        # exploration bonus
        max_grad_norm=0.5,
        policy_kwargs=dict(net_arch=[64, 64], activation_fn=torch.nn.Tanh)
    )
    
    # create progress callback
    progress_callback = TrainingProgressCallback(TOTAL_TIMESTEPS)
    
    # train the model with progress tracking
    print("starting training...")
    model.learn(total_timesteps=TOTAL_TIMESTEPS, callback=progress_callback)
    
    # save model with configurable name
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    save_name = MODEL_NAME_BASE + (f"_{timestamp}" if MODEL_APPEND_TIMESTAMP else "")
    model_path = os.path.join(MODEL_DIR, save_name)
    model.save(model_path)
    
    # save metadata
    metadata = {
        "algorithm": ALGORITHM,
        "total_timesteps": TOTAL_TIMESTEPS,
        "training_environments": len(mazes),
        "trained_at": timestamp,
        "model_name": save_name
    }
    
    with open(f"{model_path}_metadata.json", 'w') as f:
        json.dump(metadata, f, indent=2)
    
    env.close()
    print(f"training completed! model saved to: {model_path}")
    return model_path


def main():
    import argparse
    
    parser = argparse.ArgumentParser(description="train rl agent on maze environments")
    parser.add_argument("--dataset", type=str, required=True, help="path to training dataset")
    args = parser.parse_args()
    
    train_agent(args.dataset)

if __name__ == "__main__":
    main()