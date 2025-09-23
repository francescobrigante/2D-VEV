# verifies a given environment using SPIN to check if GOAL is reachable

import os
import subprocess
import tempfile
from typing import List, Tuple


class EnvironmentVerifier:
    
    def __init__(self, template_path: str = "verification_template.pml"):
        self.template_path = template_path
        self.template_content = self._load_template()
    
    
    # reads PROMELA model implementation from file
    def _load_template(self) -> str:
        """Load the Promela template file"""
        try:
            with open(self.template_path, 'r') as f:
                return f.read()
        except FileNotFoundError:
            raise FileNotFoundError(f"Promela template not found: {self.template_path}")
    
    
    # generates complete PROMELA file with maze data injected
    def _create_verification_file(self, maze: List[List[str]]) -> str:
        
        # Generate SET_ROW statements for the maze
        set_row_lines = []
        for row_idx, row in enumerate(maze):
            cells = "','".join(row)
            set_row_line = f"    SET_ROW(env,{row_idx},'{cells}');"
            set_row_lines.append(set_row_line)
        
        maze_data = "\n".join(set_row_lines)
        
        # Replace placeholder with actual maze data
        promela_code = self.template_content.replace(
            "    /* MAZE_DATA_PLACEHOLDER - This will be replaced by Python script */",
            maze_data
        )
        
        return promela_code
    
    
    # executes SPIN verification
    def _run_spin_verification(self, work_dir: str, pml_file: str) -> Tuple[bool, str]:
        """
        Returns:
            (is_solvable, message): Verification result
        """
        try:
            # compiling spin
            result = subprocess.run(
                ['spin', '-a', pml_file],
                cwd=work_dir,
                capture_output=True,
                text=True,
                timeout=30
            )
            
            if result.returncode != 0:
                return False, f"SPIN compilation failed: {result.stderr}"
            
            # gcc compiling with increased vector size
            result = subprocess.run(
                ['gcc', '-o', 'pan', 'pan.c', '-DVECTORSZ=5000'],
                cwd=work_dir,
                capture_output=True,
                text=True,
                timeout=30
            )
            
            if result.returncode != 0:
                return False, f"GCC compilation failed: {result.stderr}"
            
            # run verification
            result = subprocess.run(
                ['./pan', '-N', 'reach_goal', '-m1000000'],
                cwd=work_dir,
                capture_output=True,
                text=True,
                timeout=60
            )
            
            # returns tuple (is_solvable, message)
            return self._extract_results(result.stdout, result.stderr)
            
        except subprocess.TimeoutExpired:
            return False, "Verification timeout"
        
        except FileNotFoundError as e:
                return False, f"Error: {str(e)}"
    
    
    # interprets SPIN verification output to return if goal is reachable
    def _extract_results(self, stdout: str, stderr: str) -> Tuple[bool, str]:
        """
        Returns:
            (is_solvable, message): Interpretation of results
        """
        stdout_lower = stdout.lower()
        
        if "assertion violated" in stdout_lower:
            return False, "Environment has assertion violations"
        
        if "max search depth too small" in stdout_lower:
            return False, "Search depth limit reached"
        
        if "goal_reached = 1" in stdout and "unreached" in stdout_lower:
            return False, "Goal never reached -> environment is unsolvable"
        
        if "acceptance cycle" in stdout_lower or "trail ends after" in stdout_lower:
            return False, "Goal NOT reachable"
        
        if "errors: 0" in stdout_lower:
            return True, "Goal is reachable"
        
        if "error" in stdout_lower or "error" in stderr.lower():
            return False, f"Verification error: {stdout} {stderr}"
        
        # generic error
        return False, f"Generic error: {stdout}"
    
    
    # main function to verify a maze
    def verify_environment(self, maze: List[List[str]]) -> Tuple[bool, str]:
        """
        Returns:
            (is_solvable, message): Tuple with verification result and message
        """
        try:
            # generate temporary file
            with tempfile.TemporaryDirectory() as temp_dir:
                pml_file = os.path.join(temp_dir, "test_env.pml")
                
                promela_code = self._create_verification_file(maze)
                
                with open(pml_file, 'w') as f:
                    f.write(promela_code)
                
                # run SPIN verification pipeline
                return self._run_spin_verification(temp_dir, pml_file)
                
        except Exception as e:
            return False, f"Verification error: {str(e)}"
    
