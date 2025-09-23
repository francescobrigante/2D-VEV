# includes function to generate a maze with simple constraints

import random

def generate_maze(W, H, seed=None):
    """
    Generates a random digital env (maze) with the following elements:
    - @ : free passage
    - # : wall
    - S : start (only one)
    - G : goal (only one)
    - a,b,c : keys
    - A,B,C : corresponding doors

    Parameters:
    - W: maze width
    - H: maze height
    - seed: random seed (optional, for reproducibility)

    Constraints:
    - 1:1 ratio between keys and doors
    - single S and G

    Returns:
    - maze: maze matrix
    - keys_used: list of used keys
    """
    
    if seed is not None:
        random.seed(seed)
    
    # validating H,W
    if W <= 0 or H <= 0:
        raise ValueError("H and W must be positive integers")
    
    if W * H < 2:
        raise ValueError("Maze must be at least 2 cells to fit S and G")

    # initialize the maze with all walls
    maze = [['#' for _ in range(W)] for _ in range(H)]
    # generate all possible positions
    all_positions = [(i, j) for i in range(H) for j in range(W)]
    # shuffle positions to add randomness
    random.shuffle(all_positions)
    
    # choosing keys
    available_keys = ['a', 'b', 'c']
    # max number of key-door pairs we can place given H,W
    max_key_pairs = min(3, (W * H - 2) // 2)
    # random choice
    num_keys = random.randint(0, max_key_pairs)
    selected_keys = random.sample(available_keys, num_keys) if num_keys > 0 else []
    
    # list of elements we need to place
    elements_to_place = []
    elements_to_place.extend(['S', 'G'])

    for key in selected_keys:
        elements_to_place.append(key)           # key
        elements_to_place.append(key.upper())   # door

    # place special elements
    for i, element in enumerate(elements_to_place):
        if i < len(all_positions):
            row, col = all_positions[i]
            maze[row][col] = element
    
    # for remaining positions, choose between @ and # with probability
    for i in range(len(elements_to_place), len(all_positions)):
        row, col = all_positions[i]
        # 70% prob of @, 30% prob of wall
        if random.random() < 0.7:
            maze[row][col] = '@'
        else:
            maze[row][col] = '#'
    
    return maze, selected_keys

def print_maze(maze):
    for row in maze:
        print(''.join(row))


# ============================ Main for testing ==================================
if __name__ == "__main__":
    W, H = 20, 10
    
    maze, keys_used = generate_maze(W, H, seed=14)
    
    print(f"Generated maze with shape {W}x{H}:\n")
    print_maze(maze)
    print(f"\nUsed keys: {keys_used}")

