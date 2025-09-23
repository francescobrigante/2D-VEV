# script to test a trained RL agent on a set of maze environments

import os
import json
import statistics
from datetime import datetime
from stable_baselines3 import PPO
from maze_env import DigitalEnvironment
from dataset_manager import DatasetManager

try:
    from tqdm import tqdm
except ImportError:
    # fallback if tqdm not available
    def tqdm(iterable, desc="", total=None):
        if desc:
            print(f"{desc}...")
        return iterable

# testing defaults (can override via CLI)
MAX_STEPS = 1000000
DEFAULT_NUM_EPISODES = 20
MAX_TEST_ENVS = 20

def test_agent(model_path: str, dataset_path: str, num_episodes: int, deterministic: bool) -> dict:
    # load model
    model = PPO.load(model_path)
    print(f"loaded model from {model_path}")
    
    # load dataset
    manager = DatasetManager()
    dataset = manager.load_dataset(dataset_path)
    verified_envs = dataset.get('verified_environments', [])[:MAX_TEST_ENVS]
    
    print(f"testing on {len(verified_envs)} environments")
    
    results = []
    
    # main progress bar for environments
    env_pbar = tqdm(verified_envs, desc="testing environments", unit="env")
    
    for i, env_data in enumerate(env_pbar):
        env_id = env_data.get('id', f'env_{i+1}')
        maze = env_data['maze']
        min_steps_optimal = env_data.get('min_steps', -1)
        
        # update progress bar description
        env_pbar.set_description(f"testing {env_id}")
        
        # test single environment
        env = DigitalEnvironment(maze=maze)
        episode_results = []
        
        # progress bar for episodes within each environment
        episode_pbar = tqdm(range(num_episodes), desc=f"episodes", leave=False, unit="ep")
        
        for episode in episode_pbar:
            obs, info = env.reset()
            steps = 0
            goal_reached = False
            
            for step in range(MAX_STEPS):
                action, _ = model.predict(obs, deterministic=deterministic)
                action = int(action)  # convert numpy array to int
                obs, reward, terminated, truncated, info = env.step(action)
                steps += 1
                
                if terminated:
                    goal_reached = True
                    break
                if truncated:
                    break
            
            episode_results.append({"steps": steps, "success": goal_reached})
            
            # update episode progress bar with current success rate
            current_successes = sum(1 for r in episode_results if r["success"])
            current_rate = current_successes / len(episode_results)
            episode_pbar.set_postfix(success=f"{current_rate:.1%}")
        
        episode_pbar.close()
        env.close()
        
        # calculate statistics
        successful_episodes = [r for r in episode_results if r["success"]]
        success_rate = len(successful_episodes) / num_episodes
        avg_steps = statistics.mean([r["steps"] for r in successful_episodes]) if successful_episodes else float('inf')
        
        results.append({
            "env_id": env_id,
            "success_rate": success_rate,
            "avg_steps": avg_steps,
            "min_steps_optimal": min_steps_optimal,
            "efficiency_ratio": avg_steps / min_steps_optimal if min_steps_optimal > 0 and avg_steps != float('inf') else float('inf'),
            "keys_used": env_data.get('keys_used', [])
        })
        
        # update main progress bar with results
        if success_rate > 0:
            env_pbar.set_postfix(
                success=f"{success_rate:.1%}", 
                steps=f"{avg_steps:.1f}", 
                optimal=min_steps_optimal,
                keys=len(env_data.get('keys_used', []))
            )
        else:
            # for failed environments, show why they might be failing
            keys_needed = len(env_data.get('keys_used', []))
            env_pbar.set_postfix(
                status="failed", 
                keys=keys_needed,
                optimal=min_steps_optimal
            )
    
    env_pbar.close()
    
    # overall statistics
    successful_results = [r for r in results if r["success_rate"] > 0]
    overall_success_rate = len(successful_results) / len(results)
    
    summary = {
        "dataset_path": dataset_path,
        "tested_at": datetime.now().isoformat(),
        "total_environments": len(results),
        "successful_environments": len(successful_results),
        "overall_success_rate": overall_success_rate,
        "environment_results": results
    }
    
    return summary

def print_summary(results: dict):
    print("\n" + "=" * 70)
    print("test results summary")
    print("=" * 70)
    print(f"total environments tested: {results['total_environments']}")
    print(f"successfully solved: {results['successful_environments']}")
    print(f"overall success rate: {results['overall_success_rate']:.1%}")
    
    # detailed breakdown per environment
    print(f"\nper-environment results:")
    print(f"{'env_id':<12} {'success':<8} {'avg_steps':<10} {'optimal':<8} {'efficiency':<10} {'keys'}")
    print("-" * 70)
    
    for env_result in results['environment_results']:
        env_id = env_result['env_id']
        success_rate = env_result['success_rate']
        avg_steps = env_result['avg_steps']
        optimal_steps = env_result['min_steps_optimal']
        efficiency = env_result['efficiency_ratio']
        keys = env_result.get('keys_used', [])
        
        if success_rate > 0:
            print(f"{env_id:<12} {success_rate:>6.1%} {avg_steps:>8.1f} {optimal_steps:>6} {efficiency:>8.1f}x {keys}")
        else:
            print(f"{env_id:<12} {'FAILED':>7} {'N/A':>9} {optimal_steps:>6} {'N/A':>9} {keys}")
    
    # analysis of failures
    failed_envs = [r for r in results['environment_results'] if r['success_rate'] == 0]
    if failed_envs:
        print(f"\nfailure analysis:")
        print(f"- {len(failed_envs)} environments failed completely")
        
        # group by number of keys
        by_keys = {}
        for env in failed_envs:
            num_keys = len(env.get('keys_used', []))
            by_keys[num_keys] = by_keys.get(num_keys, 0) + 1
        
        for num_keys, count in sorted(by_keys.items()):
            print(f"- {count} failed environments with {num_keys} keys")
    
    # success analysis
    successful_envs = [r for r in results['environment_results'] if r['success_rate'] > 0]
    if successful_envs:
        avg_efficiency = sum(r['efficiency_ratio'] for r in successful_envs if r['efficiency_ratio'] != float('inf')) / len(successful_envs)
        print(f"\nsuccess analysis:")
        print(f"- average efficiency ratio: {avg_efficiency:.1f}x optimal")
        print(f"- best performing: {min(successful_envs, key=lambda x: x['efficiency_ratio'])['env_id']}")
        print(f"- worst performing: {max(successful_envs, key=lambda x: x['efficiency_ratio'])['env_id']}")

def main():
    import argparse
    
    parser = argparse.ArgumentParser(description="test trained rl agent on maze environments")
    parser.add_argument("--model", type=str, help="path to trained model")
    parser.add_argument("--dataset", type=str, required=True, help="path to test dataset")
    parser.add_argument("--episodes", type=int, default=DEFAULT_NUM_EPISODES, help="episodes per environment")
    parser.add_argument("--stochastic", action="store_true", help="use stochastic actions (default deterministic)")
    args = parser.parse_args()
    
    # test trained agent if model provided
    if args.model:
        results = test_agent(args.model, args.dataset, num_episodes=args.episodes, deterministic=not args.stochastic)
        print_summary(results)
    else:
        # test untrained agent (demo mode)
        print("\n" + "=" * 50)
        print("testing untrained agent on first environment")
        print("=" * 50)
        
        # load first environment from dataset
        manager = DatasetManager()
        dataset = manager.load_dataset(args.dataset)
        first_env = dataset['verified_environments'][0]
        maze = first_env['maze']
        
        # create environment first
        env = DigitalEnvironment(maze=maze)
        
        # create untrained ppo agent (fix threading issue)
        import torch
        torch.set_num_threads(1)  # fixes threading issue
        untrained_model = PPO("MlpPolicy", env, verbose=0)
        
        # test untrained agent for one episode
        obs, info = env.reset()
        print(f"starting position: {info['agent_position']}")
        print("untrained agent path:")
        
        for step in range(50):  # limit to 50 steps for demo
            action, _ = untrained_model.predict(obs, deterministic=True)
            obs, reward, terminated, truncated, info = env.step(action)
            
            action_names = ['north', 'south', 'east', 'west']
            print(f"step {step+1}: {action_names[action]} -> position {info['agent_position']}, reward: {reward:.2f}")
            
            if terminated:
                print("goal reached!")
                break
            if truncated:
                print("episode truncated")
                break
        
        env.close()

if __name__ == "__main__":
    main()