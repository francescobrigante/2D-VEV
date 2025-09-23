# representation of denv using gymnasium for RL training
# implementation of reward function

import gymnasium as gym
import numpy as np
from gymnasium import spaces
from typing import Dict, Tuple, Optional, List


class DigitalEnvironment(gym.Env):
    """
    Gymnasium environment for key-door maze navigation.
    
    Symbols:
    - '#': wall
    - '@': free space
    - 'S': start position
    - 'G': goal
    - 'a', 'b', 'c': keys
    - 'A', 'B', 'C': doors (require corresponding keys)
    """
    
    def __init__(self, maze: Optional[List[List[str]]] = None):
        super().__init__()
        
        if maze is None:
            # default if not provided
            self.maze = [
                ['#', '#', '#', '#', '#'],
                ['#', 'S', '@', '@', '#'],
                ['#', '@', '#', '@', '#'],
                ['#', '@', '@', 'G', '#'],
                ['#', '#', '#', '#', '#']
            ]
        else:
            self.maze = maze
            
        self.height = len(self.maze)
        self.width = len(self.maze[0])
        
        # action space: 0=North, 1=South, 2=East, 3=West
        self.action_space = spaces.Discrete(4)
        
        # observation space: [row, col, has_a, has_b, has_c]
        self.observation_space = spaces.Box(
            low=0, 
            high=max(self.height, self.width), 
            shape=(5,), 
            dtype=np.int32
        )
        
        # initialize state
        self.reset()
    
    
    def _find_start_position(self) -> Tuple[int, int]:
        for row in range(self.height):
            for col in range(self.width):
                if self.maze[row][col] == 'S':
                    return row, col
        raise ValueError("No start position 'S' found in maze")
    
    
    # checks if you can walk through a cell
    def _is_passable(self, row: int, col: int) -> bool:
        
        if row < 0 or row >= self.height or col < 0 or col >= self.width:
            return False
            
        cell = self.maze[row][col]
        
        # Wall
        if cell == '#':
            return False
            
        # Doors require corresponding keys
        if cell == 'A' and not self.has_a:
            return False
        if cell == 'B' and not self.has_b:
            return False
        if cell == 'C' and not self.has_c:
            return False
            
        return True
    
    # resets env to initial state
    def reset(self, seed: Optional[int] = None, options: Optional[Dict] = None) -> Tuple[np.ndarray, Dict]:
        super().reset(seed=seed)
        
        # start position
        self.agent_row, self.agent_col = self._find_start_position()
        
        # reset keys
        self.has_a = False
        self.has_b = False
        self.has_c = False
        
        # track which keys have been collected (to avoid multiple rewards)
        self.keys_collected = set()
        
        self.goal_reached = False
        self.steps = 0
        
        # reset visited cells
        self.visited_cells = set()
        self.visited_cells.add((self.agent_row, self.agent_col))  # mark start as visited
        
        observation = self._get_observation()
        info = self._get_info()
        
        return observation, info
    
    # executes one step in the environment
    def step(self, action: int) -> Tuple[np.ndarray, float, bool, bool, Dict]:

        self.steps += 1
        
        moves = {
            0: (-1, 0),  # North
            1: (1, 0),   # South
            2: (0, 1),   # East
            3: (0, -1)   # West
        }
        
        if action not in moves:
            raise ValueError(f"Invalid action: {action}")
        
        # calculate new position
        d_row, d_col = moves[action]
        new_row = self.agent_row + d_row
        new_col = self.agent_col + d_col
        
        # check if move is valid
        if self._is_passable(new_row, new_col):
            self.agent_row = new_row
            self.agent_col = new_col
            
            # check for key collection (defer adding to keys_collected until after reward)
            current_cell = self.maze[self.agent_row][self.agent_col]
            new_key_collected = None
            if current_cell == 'a' and not self.has_a:
                self.has_a = True
                new_key_collected = 'a'
            elif current_cell == 'b' and not self.has_b:
                self.has_b = True
                new_key_collected = 'b'
            elif current_cell == 'c' and not self.has_c:
                self.has_c = True
                new_key_collected = 'c'
            elif current_cell == 'G':
                self.goal_reached = True
        
        # compute reward
        reward = self._calculate_reward()
        
        # add to visited cells after reward calculation
        if self._is_passable(self.agent_row, self.agent_col):
            self.visited_cells.add((self.agent_row, self.agent_col))

        # mark the key as collected
        if 'new_key_collected' in locals() and new_key_collected is not None:
            self.keys_collected.add(new_key_collected)
        
        # check for termination
        terminated = self.goal_reached
        truncated = self.steps >= 10000  # max steps limit<----
        
        observation = self._get_observation()
        info = self._get_info()
        
        return observation, reward, terminated, truncated, info
    
    
    # simple reward function
    def _calculate_reward(self) -> float:
        
        if self.goal_reached:
            return 100.0  # big reward for reaching goal
        
        reward = -0.1  # small step penalty for each move
        
        # reward for collecting keys (only when first collected)
        current_cell = self.maze[self.agent_row][self.agent_col]
        if current_cell in ['a', 'b', 'c'] and current_cell not in self.keys_collected:
            reward += 10.0  # good reward for keys
        
        # exploration bonus if visiting new cell
        current_pos = (self.agent_row, self.agent_col)
        if current_pos not in self.visited_cells:
            reward += 0.1
        
        return reward
    
    def _get_observation(self) -> np.ndarray:
        """Get current observation"""
        return np.array([
            self.agent_row,
            self.agent_col,
            int(self.has_a),
            int(self.has_b),
            int(self.has_c)
        ], dtype=np.int32)
    
    def _get_info(self) -> Dict:
        """Get additional info"""
        return {
            "agent_position": (self.agent_row, self.agent_col),
            "keys": {"a": self.has_a, "b": self.has_b, "c": self.has_c},
            "goal_reached": self.goal_reached,
            "steps": self.steps,
            "current_cell": self.maze[self.agent_row][self.agent_col],
            "visited_cells_count": len(self.visited_cells),
            "exploration_rate": len(self.visited_cells) / (self.width * self.height)
        }
    
    def render(self):
        """Render the environment (simple text output)"""
        print(f"\nStep {self.steps}")
        print(f"Position: ({self.agent_row}, {self.agent_col})")
        print(f"Keys: a={self.has_a}, b={self.has_b}, c={self.has_c}")
        print(f"Current cell: '{self.maze[self.agent_row][self.agent_col]}'")
        print("Maze:")
        
        for row in range(self.height):
            line = ""
            for col in range(self.width):
                if row == self.agent_row and col == self.agent_col:
                    line += "R"  # Robot position
                else:
                    line += self.maze[row][col]
            print(line)
        print()
    
    def load_maze(self, maze: List[List[str]]):
        """Load a new maze into the environment"""
        self.maze = maze
        self.height = len(self.maze)
        self.width = len(self.maze[0])
        
        # Update observation space if dimensions changed
        self.observation_space = spaces.Box(
            low=0, 
            high=max(self.height, self.width), 
            shape=(5,), 
            dtype=np.int32
        )
        
        # Reset the environment with new maze
        self.reset()
    
    def close(self):
        """Clean up resources"""
        pass