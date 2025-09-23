# evaluation file to evaluate verified vs unverified models on test set and export CSV
# to run it in docker use:

# docker run --rm \
#   -v "$(pwd):/app" \
#   -e OMP_NUM_THREADS=1 -e MKL_NUM_THREADS=1 \
#   maze-rl python /app/evaluation.py \
#     --dataset /app/test_set.json \
#     --verified /app/models/verified \
#     --unverified /app/models/unverified \
#     --episodes 20 \
#     --output /app/evaluation_results.csv

import os
import csv
import statistics
from datetime import datetime
from typing import Dict, List, Tuple

from stable_baselines3 import PPO
from maze_env import DigitalEnvironment
from dataset_manager import DatasetManager

try:
    from tqdm import tqdm
except ImportError:
    def tqdm(iterable, desc="", total=None, unit=None, leave=True):
        if desc:
            print(f"{desc}...")
        return iterable


# defaults
MAX_STEPS = 1_000_000
DEFAULT_NUM_EPISODES = 20

# given a model and maze, runs multiple episodes and returns success rate and average steps
def run_episodes(model: PPO, maze: List[List[str]], num_episodes: int, deterministic: bool) -> Tuple[float, float]:
    env = DigitalEnvironment(maze=maze)
    episode_results = []

    for _ in range(num_episodes):
        obs, info = env.reset()
        steps = 0
        goal_reached = False

        for _ in range(MAX_STEPS):
            action, _ = model.predict(obs, deterministic=deterministic)
            action = int(action)
            obs, reward, terminated, truncated, info = env.step(action)
            steps += 1
            if terminated:
                goal_reached = True
                break
            if truncated:
                break

        episode_results.append({"steps": steps, "success": goal_reached})

    env.close()

    successful = [r for r in episode_results if r["success"]]
    success_rate = len(successful) / num_episodes
    avg_steps = statistics.mean([r["steps"] for r in successful]) if successful else float('inf')
    return success_rate, avg_steps


# main evaluation function
def evaluate(dataset_path: str, verified_model_path: str, unverified_model_path: str, num_episodes: int, output_csv: str, deterministic: bool) -> Dict:
    if not os.path.exists(verified_model_path + ".zip"):
        raise FileNotFoundError(f"missing model: {verified_model_path}.zip")
    if not os.path.exists(unverified_model_path + ".zip"):
        raise FileNotFoundError(f"missing model: {unverified_model_path}.zip")

    print(f"loading models: '{verified_model_path}', '{unverified_model_path}'")
    verified_model = PPO.load(verified_model_path)
    unverified_model = PPO.load(unverified_model_path)

    manager = DatasetManager()
    dataset = manager.load_dataset(dataset_path)
    test_envs = dataset.get('verified_environments', [])
    print(f"evaluating on {len(test_envs)} environments from {dataset_path}")

    rows = []
    v_avgs, u_avgs, mins = [], [], []

    for i, env_data in enumerate(tqdm(test_envs, desc="evaluating", unit="env", dynamic_ncols=True)):
        env_id = env_data.get('id', f'env_{i+1}')
        maze = env_data['maze']
        min_steps_optimal = env_data.get('min_steps', -1)
        v_rate, v_avg = run_episodes(verified_model, maze, num_episodes, deterministic)
        u_rate, u_avg = run_episodes(unverified_model, maze, num_episodes, deterministic)

        v_success = v_rate > 0
        u_success = u_rate > 0

        rows.append({
            "env_id": env_id,
            "min_steps": min_steps_optimal,
            "verified_success": int(v_success),
            "verified_avg_steps": (f"{v_avg:.1f}" if v_success else ""),
            "unverified_success": int(u_success),
            "unverified_avg_steps": (f"{u_avg:.1f}" if u_success else ""),
        })

        if v_success:
            v_avgs.append(v_avg)
        if u_success:
            u_avgs.append(u_avg)
        if isinstance(min_steps_optimal, (int, float)) and min_steps_optimal > 0:
            mins.append(min_steps_optimal)

    v_mean = statistics.mean(v_avgs) if v_avgs else float('inf')
    u_mean = statistics.mean(u_avgs) if u_avgs else float('inf')
    min_mean = statistics.mean(mins) if mins else float('inf')

    # write CSV
    fieldnames = [
        "env_id",
        "min_steps",
        "verified_success",
        "verified_avg_steps",
        "unverified_success",
        "unverified_avg_steps",
    ]
    with open(output_csv, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        for r in rows:
            writer.writerow(r)
        # summary rows
        writer.writerow({})
        writer.writerow({"env_id": "AVERAGES", "min_steps": f"{min_mean:.1f}", "verified_avg_steps": f"{v_mean:.1f}", "unverified_avg_steps": f"{u_mean:.1f}"})

    print(f"saved results to {output_csv}")

    return {
        "evaluated_at": datetime.now().isoformat(),
        "total_envs": len(test_envs),
        "verified_mean_avg_steps": v_mean,
        "unverified_mean_avg_steps": u_mean,
        "min_steps_mean": min_mean,
        "csv": output_csv,
    }


def main():
    import argparse

    parser = argparse.ArgumentParser(description="evaluate verified vs unverified models on test set and export CSV")
    parser.add_argument("--dataset", type=str, default="test_set.json", help="path to test dataset JSON")
    parser.add_argument("--verified", type=str, default="models/verified", help="path to verified model (without .zip)")
    parser.add_argument("--unverified", type=str, default="models/unverified", help="path to unverified model (without .zip)")
    parser.add_argument("--episodes", type=int, default=DEFAULT_NUM_EPISODES, help="episodes per environment per model")
    parser.add_argument("--output", type=str, default="evaluation_results.csv", help="output CSV path")
    parser.add_argument("--stochastic", action="store_true", help="use stochastic actions (default deterministic)")
    args = parser.parse_args()

    summary = evaluate(args.dataset, args.verified, args.unverified, args.episodes, args.output, deterministic=not args.stochastic)
    print("\nSummary:")
    print(f"- environments: {summary['total_envs']}")
    print(f"- verified mean avg_steps: {summary['verified_mean_avg_steps']:.1f}")
    print(f"- unverified mean avg_steps: {summary['unverified_mean_avg_steps']:.1f}")
    print(f"- min_steps mean: {summary['min_steps_mean']:.1f}")
    print(f"- csv: {summary['csv']}")


if __name__ == "__main__":
    main()
