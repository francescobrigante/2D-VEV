# BMC verifier for finding minimum steps using SPIN

import os
import subprocess
import tempfile
from typing import List, Tuple


class BMCVerifier:
    
    def __init__(self, template_path: str = "bmc_template.pml"):
        self.template_path = template_path
        self.template_content = self._load_template()
    
    # loads JSON file    
    def _load_template(self) -> str:
        try:
            with open(self.template_path, 'r') as f:
                return f.read()
        except FileNotFoundError:
            raise FileNotFoundError(f"BMC template not found: {self.template_path}")
    
    # generates BMC PROMELA file with maze data with max_steps
    def _create_bmc_file(self, maze: List[List[str]], max_steps: int) -> str:
        
        # generate SET_ROW statements for the maze
        set_row_lines = []
        for row_idx, row in enumerate(maze):
            cells = "','".join(row)
            set_row_line = f"    SET_ROW(env,{row_idx},'{cells}');"
            set_row_lines.append(set_row_line)
        
        maze_data = "\n".join(set_row_lines)
        
        # replace placeholders
        promela_code = self.template_content.replace(
            "/* MAZE_DATA_PLACEHOLDER */", maze_data
        )
        
        promela_code = promela_code.replace("MAX_STEPS", str(max_steps))
        
        return promela_code
    
    # runs BMC verification given depth
    def _run_bmc_at_depth(self, work_dir: str, maze: List[List[str]], depth: int) -> Tuple[bool, str]:
        try:
            # create BMC file for this depth
            bmc_content = self._create_bmc_file(maze, depth)
            bmc_file = os.path.join(work_dir, f"bmc_{depth}.pml")
            
            with open(bmc_file, 'w') as f:
                f.write(bmc_content)
            
            # compile SPIN
            result = subprocess.run(
                ['spin', '-a', bmc_file],
                cwd=work_dir,
                capture_output=True,
                text=True,
                timeout=30
            )
            
            if result.returncode != 0:
                return False, f"SPIN compilation failed: {result.stderr}"
            
            result = subprocess.run(
                ['gcc', '-o', f'pan_{depth}', 'pan.c', '-DVECTORSZ=5000'],
                cwd=work_dir,
                capture_output=True,
                text=True,
                timeout=30
            )
            
            if result.returncode != 0:
                return False, f"GCC compilation failed: {result.stderr}"
            
            # run verification with bounded search
            result = subprocess.run(
                [f'./pan_{depth}', f'-u{depth}', '-N', 'reach_goal', '-e'],
                cwd=work_dir,
                capture_output=True,
                text=True,
                timeout=60
            )
            
            return self._extract_bmc_results(result.stdout, result.stderr)
            
        except subprocess.TimeoutExpired:
            return False, "BMC timeout"
        except Exception as e:
            return False, f"BMC error: {str(e)}"
    
    
    def _extract_bmc_results(self, stdout: str, stderr: str) -> Tuple[bool, str]:
        stdout_lower = stdout.lower()
        
        # for negated LTL property, counterexample means goal is reachable
        if "assertion violated" in stdout_lower:
            return True, "Goal reachable (counterexample found)"
        
        if "acceptance cycle" in stdout_lower:
            return True, "Goal reachable (acceptance cycle found)"
        
        if "errors: 0" in stdout_lower:
            return False, "Goal not reachable at this depth"
        
        if "depth limit" in stdout_lower or "max search depth" in stdout_lower:
            return False, "Depth limit reached"
        
        return False, "Goal not reachable at this depth"
    
    
    # main function to verify with BMC and find minimum steps
    def find_minimum_steps(self, maze: List[List[str]], max_depth: int = 50) -> Tuple[bool, str, int]:
        """
        Returns:
            (is_solvable, message, min_steps): BMC verification result
        """
        try:
            with tempfile.TemporaryDirectory() as temp_dir:
                # try each depth incrementally
                for depth in range(1, max_depth + 1):
                    is_reachable, message = self._run_bmc_at_depth(temp_dir, maze, depth)
                    
                    if is_reachable:
                        return True, f"Goal reachable in minimum {depth} steps", depth
                
                return False, f"Goal not reachable within {max_depth} steps", -1
                
        except Exception as e:
            return False, f"BMC verification error: {str(e)}", -1