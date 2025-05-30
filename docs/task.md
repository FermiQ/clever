# src/clever_bench/task.py

## Overview
The `src/clever_bench/task.py` file defines a system for managing and evaluating tasks related to Lean problems sourced from a `Benchmark`. The central class, `ProblemViewTask`, is responsible for preparing `LeanProblemView` objects tailored to specific `TaskComponent`s (e.g., proof generation, implementation generation). It then orchestrates the "submission" of these views by writing them to temporary Lean files, compiling them using Lean's build tool `lake`, and analyzing the compiler output to validate the submission (e.g., checking for `sorry` placeholders or compilation errors). The module supports asynchronous submissions and generates reports detailing the validation outcomes.

## Key Components
- **`ValidationResult = namedtuple(...)`**: A named tuple used to encapsulate the results of validating a single problem submission.
    - `problem_id: str`: Identifier of the problem.
    - `isomorphism_ok: bool`: True if the isomorphism proof (if applicable) is valid.
    - `correctness_ok: bool`: True if the correctness proof (if applicable) is valid.
    - `compilation_ok: bool`: True if the Lean code compiled successfully.
    - `error_message: str`: Contains error messages from compilation or reasons for validation failure (e.g., "Timeout", "Sorries found").
    - `lean_code: str`: The actual Lean code that was submitted and validated.

- **`ProblemViewTask` class**:
    - `__init__(self, benchmark: Benchmark, component: TaskComponent, lean_folder: str = None, report_dir: str = ".logs/reports")`:
        - Initializes the task with a `Benchmark` instance, a `TaskComponent` (e.g., `TaskComponent.PROOF_GENERATION`), an optional path to the Lean project (`lean_folder`), and a directory for saving reports (`report_dir`).
        - Creates a timestamped subdirectory within `report_dir` for storing results of the current run.
        - Ensures a `temp` directory exists within the Lean project folder for temporary files.
    - `get_view(self, idx: int) -> LeanProblemView`:
        - Fetches a `LeanProblem` by its ID from the `benchmark`.
        - Converts it into a `LeanProblemView`.
        - Modifies the view based on `self.component` by selectively hiding certain fields (e.g., if `component` is `PROOF_GENERATION`, existing proofs are hidden to set up the task of generating them). It also processes test cases to uncomment them.
    - `get_visible_problems(self) -> list[LeanProblemView]`:
        - Iterates through all problems in the `benchmark`.
        - For each problem, calls `get_view` to create a task-specific view.
        - Returns a list of these prepared `LeanProblemView` objects.
    - `submit_async(self, problem: LeanProblemView, timeout_in_ms: float) -> ValidationResult`:
        - Asynchronously validates a submitted `LeanProblemView` (which typically contains model-generated code/proofs).
        - Reconstructs the original problem view and updates it with the submitted content (e.g., generated proofs).
        - Formats the updated view into a Lean code string using `format_problem_as_lean_with_line_ranges`.
        - Writes this code to a unique temporary `.lean` file in the `lean_folder_path / "temp"` directory.
        - Executes `lake lean <temp_file.name>` as an asynchronous subprocess within the Lean project's context.
        - Handles timeouts and compilation errors, returning appropriate `ValidationResult`.
        - If compilation is successful, it parses the output using `_extract_sorry_lines` to detect any remaining `sorry` placeholders.
        - Determines `isomorphism_ok` and `correctness_ok` based on the presence of proofs and absence of sorries (though the current logic is simplified in the main path).
        - Deletes the temporary Lean file upon completion.
    - `_extract_sorry_lines(self, build_log: str, filename: str) -> list[int]`:
        - Parses the build log (output from `lake lean`) to find line numbers where the compiler reports `sorry` for the given `filename`.
    - `_check_sorries_against_ranges(...)`: (Helper method, currently seems bypassed by simpler logic in `submit_async` for final pass/fail of proofs). Intended to check if `sorry` lines fall within specific line ranges designated for proofs (e.g., isomorphism proof range).
    - `submit_benchmark_and_get_report(self, solutions: list[LeanProblemView], timeout_in_ms_per_problem: float)`:
        - Takes a list of `LeanProblemView` objects representing solutions.
        - Uses `asyncio.gather` to run `submit_async` for all solutions concurrently.
        - Collects all `ValidationResult`s.
        - Saves the Lean code of each submission to a file in the `self.report_dir`.
        - Writes a `results.json` file containing a summary of `isomorphism_ok` and `correctness_ok` for each problem.
        - Prints an aggregated report to the console, including success rates for different proof types.

## Important Variables/Constants
- **`ProblemViewTask.benchmark: Benchmark`**: The collection of Lean problems to work with.
- **`ProblemViewTask.component: TaskComponent`**: Defines the nature of the task (e.g., what part of the problem is to be generated or validated).
- **`ProblemViewTask.lean_folder_path: Path`**: The file system path to the root of the Lean project. This is crucial for running `lake` commands correctly.
- **`ProblemViewTask.report_dir: Path`**: The directory where reports and submitted Lean files are stored.
- **`lake lean` command**: The external Lean compiler/build command used for validation.

## Usage Examples
```python
import asyncio
from pathlib import Path
from clever_bench.benchmark import Benchmark
from clever_bench.task import ProblemViewTask, TaskComponent
from clever_bench.lean_problem import LeanProblemView, LeanProblem, ProblemSpecMetadata

# --- Setup a dummy Benchmark for the example ---
# In a real scenario, benchmark would be loaded with actual problems.
dummy_meta = ProblemSpecMetadata(function_signature="def add_one (n:Nat):Nat", docstring="Adds one.", test_cases=[])
dummy_problem = LeanProblem(
    problem_id=0, problem_spec_metadata=dummy_meta,
    problem_spec_nl="A function that adds one to a natural number.",
    problem_spec_formal_ground_truth="theorem add_one_spec (n:Nat) : add_one n = n + 1 := by sorry",
    implementation_signature="def add_one (n:Nat) : Nat :=",
    implementation="  n + 1",
    correctness_theorem="theorem add_one_correct (n:Nat) : add_one n = n + 1 := by sorry" # Target for proof
)
benchmark_instance = Benchmark()
benchmark_instance.problems = [dummy_problem]

# --- Setup a dummy Lean project for 'lake' to run ---
# This is necessary if the default project path isn't suitable for testing.
lean_project_dir = Path("temp_lean_project_for_docs")
lean_project_dir.mkdir(exist_ok=True)
(lean_project_dir / "lakefile.lean").write_text("import Lake\nopen Lake DSL\npackage temp_proj {}")
(lean_project_dir / "Main.lean").write_text("def main := IO.println \"Hello\"") # A minimal main file
imports_dir = lean_project_dir / "Imports"
imports_dir.mkdir(exist_ok=True)
(imports_dir / "AllImports.lean").write_text("import Mathlib.Tactic -- Or any other common import")
# You would need to run `lake build` once manually in `temp_lean_project_for_docs` if Mathlib is new.

# 1. Initialize ProblemViewTask for a specific task (e.g., PROOF_GENERATION)
# Ensure 'lake' is in PATH.
proof_generation_task = ProblemViewTask(
    benchmark=benchmark_instance,
    component=TaskComponent.PROOF_GENERATION,
    lean_folder=str(lean_project_dir) # Point to our dummy Lean project
)

# 2. Get all problems formatted for this task
# (Proofs would be hidden, prompting the "model" to generate them)
problem_views_for_task = proof_generation_task.get_visible_problems()

# 3. Simulate a model providing solutions
# For this example, we'll manually create a "solved" view for the first problem.
solutions_to_validate = []
if problem_views_for_task:
    task_view = problem_views_for_task[0]
    
    # Construct a solution view (normally from a model's output)
    # Key part is filling in the field corresponding to the task component.
    # For PROOF_GENERATION, this is often `correctness_proof`.
    solved_view = LeanProblemView(
        problem_id=task_view.problem_id, # Must match the problem being solved
        task_component=task_view.task_component,
        
        # Copy other necessary fields from the task_view
        problem_spec_formal_ground_truth=task_view.problem_spec_formal_ground_truth,
        implementation_signature=task_view.implementation_signature,
        implementation=task_view.implementation,
        correctness_theorem=task_view.correctness_theorem,
        helper_definitions=task_view.helper_definitions,
        correctness_helper_lemmas=task_view.correctness_helper_lemmas,
        # ... any other fields required by format_problem_as_lean_with_line_ranges

        # The "generated" content:
        correctness_proof="simp [Nat.add_one]" # Example proof
    )
    solutions_to_validate.append(solved_view)

# 4. Submit the "solved" problems and get a report
if solutions_to_validate:
    print(f"Submitting {len(solutions_to_validate)} solution(s) for validation...")
    # The results (pass/fail, errors) are printed to console and saved to files
    # in the '.logs/reports/<timestamp>/' directory by default.
    validation_results = proof_generation_task.submit_benchmark_and_get_report(
        solutions=solutions_to_validate,
        timeout_in_ms_per_problem=15000 # 15 seconds timeout per problem
    )
    # print(f"Validation outcome for problem {validation_results[0].problem_id}: Correctness OK = {validation_results[0].correctness_ok}")
else:
    print("No solutions were prepared for submission.")

# --- Clean up dummy project (optional) ---
# import shutil
# shutil.rmtree(lean_project_dir)
# Also, consider cleaning '.logs/reports' if running tests repeatedly.
```

## Dependencies and Interactions
- **`asyncio`**: Used for running Lean compilation (`lake lean`) as an asynchronous subprocess, allowing for concurrent validation of multiple problems and handling timeouts.
- **`uuid`**: For generating unique names for temporary Lean files created during validation.
- **`os`**: For basic file system operations like creating directories (`os.makedirs`).
- **`time`**: Used to create timestamped directories for storing reports, helping to organize results from different runs.
- **`pathlib.Path`**: For modern, object-oriented file system path manipulations.
- **`collections.namedtuple`**: Used to define the `ValidationResult` data structure.
- **`clever_bench.lean_problem`**: This module is a key dependency, providing:
    - `LeanProblemView`: The data structure for representing a problem instance tailored to a specific task.
    - `TaskComponent`: The enumeration used to define the type of task.
    - `format_problem_as_lean_with_line_ranges`: The function used to convert a `LeanProblemView` into a Lean code string for compilation.
- **`clever_bench.benchmark`**:
    - `Benchmark`: The class that provides the source of `LeanProblem` objects.
    - `get_clever_lean_project_path`: A utility function to find the path to the Lean project.
- **External Tool: `lake`**: The Lean build system and package manager. `ProblemViewTask` relies on `lake` being installed and accessible in the system's PATH to compile and check Lean code. The command `lake lean <file>` is executed as a subprocess.
- **File System**: The class interacts heavily with the file system for:
    - Creating report directories.
    - Creating temporary Lean files (`*.lean`) for compilation.
    - Reading Lean project configuration (implicitly, via `lake`).
    - Writing out submitted Lean code and JSON summary reports.
