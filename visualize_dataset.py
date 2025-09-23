# prints dataset from json along with statistics

import sys
from dataset_manager import DatasetManager

def print_maze(maze, title="Maze"):
    print(f"{title}:")
    for row in maze:
        print(''.join(row))
    print()

# loads and visualizes dataset
def visualize_dataset(dataset_path: str):

    # Load the dataset using DatasetManager
    manager = DatasetManager()
    dataset = manager.load_dataset(dataset_path)
    
    # Print dataset statistics
    stats = manager.get_dataset_stats(dataset)
    
    print("DATASET STATISTICS")
    print("=" * 50)
    print(f"Total environments: {stats['total_environments']}")
    print(f"Verified (solvable): {stats['verified_count']}")
    print(f"Unverified: {stats['unverified_count']}")
    print(f"Verification rate: {stats['verification_rate']:.1%}")
    print(f"Dimensions: {stats['dimensions']}")
    print(f"Key usage: {stats['key_usage']}")
    print(f"Generated at: {stats['generated_at']}")
    print(f"Verification enabled: {stats['verification_enabled']}")
    print("=" * 50)
    
    # Get all environments (both verified and unverified)
    all_environments = dataset.get('verified_environments', []) + dataset.get('unverified_environments', [])
    
    # Show all environments
    if all_environments:
        print(f"\nALL ENVIRONMENTS ({len(all_environments)})")
        for env_data in all_environments:
            print(f"\n--- {env_data['id']} ---")
            print(f"Keys: {env_data.get('keys_used', [])}")
            print(f"Verification: {env_data.get('verification_result', 'unknown')}")
            min_steps = env_data.get('min_steps', -1)
            if min_steps > 0:
                print(f"Min steps: {min_steps}")
            else:
                print(f"Min steps: unknown")
            print_maze(env_data['maze'])

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python visualize_dataset.py <dataset.json>")
        sys.exit(1)
    
    visualize_dataset(sys.argv[1])