# src/clever_bench/benchmark.py

## Overview
The `src/clever_bench/benchmark.py` file defines the `Benchmark` class and several helper functions for managing and processing Lean theorem proving problems within the Clever Lean project. Its primary role is to discover, load, parse, and provide access to these problems. It also supports exporting the benchmark problems into JSON and CSV formats. The helper functions facilitate locating necessary project directories and files.

## Key Components
- **`get_clever_lean_project_path() -> str`**: Returns the absolute path to the main Clever Lean project directory.
- **`get_clever_lean_human_eval_directory() -> str`**: Returns the path to the directory containing Lean problems for human evaluation.
- **`get_clever_lean_sample_examples_directory() -> str`**: Returns the path to the directory containing sample Lean problems.
- **`get_helper_definition_file_path() -> str`**: Returns the path to the `AllImports.lean` file, which contains helper definitions used by the problems.
- **`Benchmark` class**:
    - `__init__(self, directory: str = None, helper_definition_file: str = None, is_sample: bool = False)`: Initializes a new `Benchmark` instance. It sets up paths to problem directories and helper files. The `is_sample` flag determines whether to load standard human evaluation problems or sample problems.
    - `load_all(self)`: Discovers and loads all `.lean` problem files from the configured directory. It uses `LeanSpecParser` to parse each file into a `LeanProblem` object and stores them.
    - `get_problem(self, idx: int) -> LeanProblem`: Retrieves a specific `LeanProblem` by its numerical ID.
    - `to_json(self) -> str`: Serializes the list of loaded `LeanProblem` objects into a JSON formatted string.
    - `to_csv(self) -> Tuple[List[str], List[List[str]]]`: Converts the list of `LeanProblem` objects into a CSV format, returning a tuple containing headers and a list of rows.
    - `save_json(self, filepath: str)`: Saves the benchmark problems to a specified JSON file.
    - `save_csv(self, filepath: str)`: Saves the benchmark problems to a specified CSV file.

## Important Variables/Constants
- **`Benchmark.project_path: str`**: Stores the path to the Clever Lean project.
- **`Benchmark.directory: str`**: The directory from which `.lean` problem files are loaded.
- **`Benchmark.helper_definition_file: str`**: Path to the Lean file containing common helper definitions.
- **`Benchmark.is_sample: bool`**: A boolean flag indicating if the benchmark is for sample problems or standard evaluation problems.
- **`Benchmark.problems: List[LeanProblem]`**: A list that holds all the loaded and parsed `LeanProblem` instances.

## Usage Examples
```python
from clever_bench.benchmark import Benchmark

# Initialize a benchmark for the standard human evaluation problems
human_eval_benchmark = Benchmark()
human_eval_benchmark.load_all()

# Access a specific problem by its ID
if len(human_eval_benchmark.problems) > 0:
    problem_0 = human_eval_benchmark.get_problem(0)
    print(f"Problem 0 Name: {problem_0.name}")
    print(f"Problem 0 Full Theorem: {problem_0.full_theorem}")

# Save the loaded problems to a JSON file
human_eval_benchmark.save_json("human_eval_problems.json")

# Save the loaded problems to a CSV file
human_eval_benchmark.save_csv("human_eval_problems.csv")

# Initialize a benchmark for sample problems
sample_benchmark = Benchmark(is_sample=True)
sample_benchmark.load_all()

# Get the number of sample problems loaded
print(f"Number of sample problems: {len(sample_benchmark.problems)}")

# Save sample problems
sample_benchmark.save_json("sample_problems.json")
```

## Dependencies and Interactions
- **`os`**: Used for operating system-dependent functionalities like path construction (e.g., `os.path.join`, `os.path.dirname`).
- **`json`**: Used for serializing problem data to JSON format (`json.dumps`).
- **`csv`**: Used for serializing problem data to CSV format (`csv.writer`).
- **`typing.List`, `typing.Tuple`**: Used for type hinting to improve code readability and maintainability.
- **`pathlib.Path`**: Used for object-oriented path manipulation and for finding all `.lean` files in a directory (`Path(self.directory).glob("*.lean")`).
- **`clever_bench.lean_problem.LeanProblem`**: This class (defined in another module within the same project) represents a single parsed Lean problem. The `Benchmark` class creates and manages a list of `LeanProblem` objects.
- **`clever_bench.lean_parser_spec.LeanSpecParser`**: This class (also from the same project) is responsible for parsing the content of `.lean` files and extracting problem specifications. The `Benchmark.load_all()` method utilizes this parser.
- **Lean files (`.lean`)**: The script reads `.lean` files from specified directories. The structure and content of these files are crucial for the `LeanSpecParser` to work correctly.
- **`AllImports.lean`**: A specific Lean file that contains helper definitions, which can be included during the parsing of individual problems.
