# handles creation, storage and loading of random denvs that can be verified or non verified

import json
import os
import random
from typing import List, Dict, Optional, Tuple
from datetime import datetime
from create_denv import generate_maze
from environment_verifier import EnvironmentVerifier
from bmc_verifier import BMCVerifier

# constant for trivial solution threshold
TRIVIAL_THRESHOLD = 4


class DatasetManager:
    
    def __init__(self, width: int = 7, height: int = 7):

        self.width = width
        self.height = height
        self.verifier = EnvironmentVerifier()
        self.bmc_verifier = BMCVerifier()
    
    
    # generates a random unverified environment
    def generate_single_environment(self, seed: Optional[int] = None) -> Dict:

        maze, keys_used = generate_maze(self.width, self.height, seed=seed)
        
        return {
            "maze": maze,
            "keys_used": keys_used,
            "width": self.width,
            "height": self.height,
            "seed": seed
        }
    
    # verifies a single environment using BMC
    def verify_single_environment(self, env_data: Dict) -> Dict:

        maze = env_data["maze"]
        is_solvable, message, min_steps = self.bmc_verifier.find_minimum_steps(maze, max_depth=30)
        
        env_data["verification_result"] = "solvable" if is_solvable else "unsolvable"
        env_data["verification_message"] = message
        env_data["min_steps"] = min_steps if is_solvable else -1
        env_data["verified_at"] = datetime.now().isoformat()
        
        return env_data
    
    
    # main function to generate and save the dataset
    def generate_and_save_dataset(self, num_environments: int, filepath: str, verify: bool = True, skip_trivial: bool = False, progress_callback: Optional[callable] = None) -> Dict:
        """
        Args:
            num_environments: number of environments to generate
            filepath: output file path
            verify: whether to generate verified environments or not
            skip_trivial: if True, skip environments with min_steps < TRIVIAL_THRESHOLD
            progress_callback: optional callback function for progress bar
        """
        
        verified_envs = []
        unverified_envs = []
        
        if verify:
            # generate until we have num_environments VERIFIED environments
            # to avoid infinite loop we use a max_attempts variable
            attempts = 0
            max_attempts = num_environments * 10  # safety limit
            
            while len(verified_envs) < num_environments and attempts < max_attempts:
                attempts += 1
                
                # generate unverified environment
                env_data = self.generate_single_environment()
                env_data["id"] = f"env_{len(verified_envs)+1:04d}"
                env_data["generated_at"] = datetime.now().isoformat()
                env_data["attempt"] = attempts
                
                # verify it
                env_data = self.verify_single_environment(env_data)
                
                # if its correct, check if we should skip trivial solutions
                if env_data["verification_result"] == "solvable":
                    min_steps = env_data.get("min_steps", -1)
                    
                    # Skip trivial solutions if skip_trivial is True
                    if skip_trivial and min_steps > 0 and min_steps < TRIVIAL_THRESHOLD:
                        if progress_callback:
                            progress_callback(len(verified_envs), num_environments, env_data, skipped_trivial=True)
                    else:
                        verified_envs.append(env_data)
                        if progress_callback:
                            progress_callback(len(verified_envs), num_environments, env_data)
                # skip unsolvable environments, don't add to dataset
                else:
                    if progress_callback:
                        progress_callback(len(verified_envs), num_environments, env_data)
            
            if len(verified_envs) < num_environments:
                print(f"EXITING: Only found {len(verified_envs)} solvable environments after {attempts} attempts")
        
        else:
            # generate num_environments without verification
            for i in range(num_environments):
                env_data = self.generate_single_environment()
                env_data["id"] = f"env_{i+1:04d}"
                env_data["generated_at"] = datetime.now().isoformat()
                env_data["verification_result"] = "unknown"
                env_data["verification_message"] = "Not verified"
                env_data["min_steps"] = -1  # unverified environments have min_steps = -1
                unverified_envs.append(env_data)
                
                if progress_callback:
                    progress_callback(i + 1, num_environments, env_data)
        
        # create complete dataset
        dataset = {
            "metadata": {
                "total_environments": num_environments,
                "verified_count": len(verified_envs),
                "unverified_count": len(unverified_envs),
                "width": self.width,
                "height": self.height,
                "verification_enabled": verify,
                "generated_at": datetime.now().isoformat(),
                "generator_version": "1.0"
            },
            "verified_environments": verified_envs,
            "unverified_environments": unverified_envs
        }
        
        # save dataset to file JSON
        os.makedirs(os.path.dirname(filepath) if os.path.dirname(filepath) else '.', exist_ok=True)
        with open(filepath, 'w') as f:
            json.dump(dataset, f, indent=2)
        
        return dataset
    
    
    # loads JSON dataset file handling errors
    def load_dataset(self, filepath: str) -> Dict:
        try:
            with open(filepath, 'r') as f:
                return json.load(f)
        except FileNotFoundError:
            raise FileNotFoundError(f"Dataset file not found: {filepath}")
        except json.JSONDecodeError:
            raise ValueError(f"Invalid JSON in dataset file: {filepath}")
    


    # gets statistics about dataset ready for printing
    def get_dataset_stats(self, dataset: Dict) -> Dict:

        metadata = dataset.get("metadata", {})
        verified_envs = dataset.get("verified_environments", [])
        unverified_envs = dataset.get("unverified_environments", [])
        
        # keys used
        key_usage = {"a": 0, "b": 0, "c": 0, "none": 0}
        for env in verified_envs + unverified_envs:
            keys = env.get("keys_used", [])
            if not keys:
                key_usage["none"] += 1
            else:
                for key in keys:
                    if key in key_usage:
                        key_usage[key] += 1
        
        return {
            "total_environments": len(verified_envs) + len(unverified_envs),
            "verified_count": len(verified_envs),
            "unverified_count": len(unverified_envs),
            "verification_rate": len(verified_envs) / (len(verified_envs) + len(unverified_envs)) if (len(verified_envs) + len(unverified_envs)) > 0 else 0,
            "dimensions": f"{metadata.get('width', 'unknown')}x{metadata.get('height', 'unknown')}",
            "key_usage": key_usage,
            "generated_at": metadata.get("generated_at", "unknown"),
            "verification_enabled": metadata.get("verification_enabled", False)
        }




# handles progress bar for verification when creating a dataset
def progress_printer(current: int, total: int, env_data: Dict, skipped_trivial: bool = False) -> None:

    verification = env_data.get("verification_result", "unknown")
    min_steps = env_data.get("min_steps", -1)
    status_symbol = "✓" if verification == "solvable" else "✗" if verification == "unsolvable" else "-"
    
    if skipped_trivial:
        print(f"[{current:3d}/{total:3d}] ⚠ Attempt {env_data.get('attempt', '?')} - SKIPPED (trivial: {min_steps} steps < {TRIVIAL_THRESHOLD})")
    elif verification == "solvable":
        print(f"[{current:3d}/{total:3d}] {status_symbol} {env_data['id']} - SAVED ({min_steps} steps, attempt {env_data.get('attempt', '?')})")
    elif verification == "unsolvable":
        print(f"[{current:3d}/{total:3d}] {status_symbol} Attempt {env_data.get('attempt', '?')} - SKIPPED (unsolvable)")
    else:
        print(f"[{current:3d}/{total:3d}] {status_symbol} {env_data['id']} ({verification})")


# command line interface
def main():
    import argparse
    
    # setup argument parser with help
    parser = argparse.ArgumentParser(
        description="Generate digital environment datasets for RL training",
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    
    parser.add_argument("-n", "--num", type=int, required=True,
                       help="number of environments to generate (REQUIRED)")
    parser.add_argument("--no-verify", action="store_true", 
                       help="skip SPIN verification")
    parser.add_argument("--skip-trivial", action="store_true",
                       help=f"skip trivial solutions with min_steps < {TRIVIAL_THRESHOLD}")
    parser.add_argument("-o", "--output", type=str, default="environments_dataset.json",
                       help="output JSON file path")
    
    # check if no arguments provided, show help
    import sys
    if len(sys.argv) == 1:
        parser.print_help()
        sys.exit(1)
    
    args = parser.parse_args()
    
    # create dataset manager and start generation
    manager = DatasetManager(width=7, height=7)
    
    print(f"Generating {args.num} environments (7x7 grid)")
    print(f"SPIN Verification: {'DISABLED' if args.no_verify else 'ENABLED'}")
    print(f"Skip trivial solutions: {'ENABLED' if args.skip_trivial else 'DISABLED'}")
    if args.skip_trivial:
        print(f"Trivial threshold: < {TRIVIAL_THRESHOLD} steps")
    print(f"Output file: {args.output}")
    print("-" * 50)
    
    # generate and save dataset
    dataset = manager.generate_and_save_dataset(
        num_environments=args.num,
        filepath=args.output,
        verify=not args.no_verify,
        skip_trivial=args.skip_trivial,
        progress_callback=progress_printer
    )
    
    # display final statistics
    stats = manager.get_dataset_stats(dataset)
    print("\n" + "=" * 50)
    print("Dataset generated")
    print("=" * 50)
    print(f"File: {args.output}")
    print(f"Total environments: {stats['total_environments']}")
    print(f"Verified (solvable): {stats['verified_count']}")
    print(f"Unverified: {stats['unverified_count']}")
    print(f"Verification rate: {stats['verification_rate']:.1%}")
    print(f"Dimensions: {stats['dimensions']}")
    print(f"Key usage: {stats['key_usage']}")

    print(f"Generated at: {stats['generated_at']}")
    print("=" * 50)


if __name__ == "__main__":
    main()