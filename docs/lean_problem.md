# src/clever_bench/lean_problem.py

## Overview
The `src/clever_bench/lean_problem.py` file defines the core data structures for representing Lean theorem-proving problems within the `clever_bench` framework. It specifies the various components that constitute a problem, such as its metadata (including Python function signatures and docstrings), natural language descriptions, formal Lean specifications (both ground truth and potentially machine-generated versions), implementations, correctness theorems, and associated proofs. The file also includes structures for helper lemmas and an enumeration (`TaskComponent`) to categorize different benchmark tasks (e.g., specification generation, proof generation). Utilities are provided to serialize these problem structures into formats like JSON and CSV, and to format them back into Lean code with line number tracking for specific sections.

## Key Components
- **`TaskComponent(Enum)`**: An enumeration that defines distinct categories of tasks within the benchmark. Examples include:
    - `SPEC_GENERATION`: Generating formal Lean specifications from natural language.
    - `IMPL_GENERATION`: Generating Lean code implementations from specifications.
    - `PROOF_GENERATION`: Generating proofs for theorems (e.g., correctness proofs).
    - `SPEC_ISOMORPHISM`: Proving equivalence between different formal specifications.
- **`@dataclass Lemma`**: A simple data class representing a Lean lemma.
    - `statement: str`: The Lean statement of the lemma.
    - `proof: str`: The Lean proof of the lemma.
    - `to_dict(self)`: Converts the lemma to a dictionary.
- **`@dataclass ProblemSpecMetadata`**: A data class for storing metadata associated with a problem's specification.
    - `function_signature: str`: The Python function signature related to the problem.
    - `docstring: str`: The docstring describing the function or problem.
    - `test_cases: List[Dict]`: A list of dictionaries, presumably representing test cases (e.g., input/output pairs).
    - `to_dict(self)`: Converts the metadata to a dictionary.
- **`@dataclass LeanProblem`**: The main data class that encapsulates all information for a single Lean problem.
    - `problem_id: int`: A unique integer identifier for the problem.
    - `problem_spec_metadata: Optional[ProblemSpecMetadata]`: Metadata including Python signature, docstring, etc.
    - `problem_spec_nl: Optional[str]`: Natural language description of the problem.
    - `problem_spec_formal_ground_truth: Optional[str]`: The definitive formal Lean specification.
    - `problem_spec_formal_generated: Optional[str]`: A machine-generated formal Lean specification.
    - `isomorphism_theorem: Optional[str]`: Theorem statement for specification isomorphism.
    - `isomorphism_proof: Optional[str]`: Proof for specification isomorphism.
    - `implementation_signature: Optional[str]`: Lean signature for the implementation.
    - `implementation: Optional[str]`: The Lean code implementation.
    - `test_cases_lean: Optional[str]`: Lean-based test cases.
    - `correctness_theorem: Optional[str]`: Theorem statement for the correctness of the implementation.
    - `correctness_proof: Optional[str]`: Proof for the correctness theorem.
    - `helper_definitions: List[str]`: List of shared Lean definitions/imports.
    - `isomorphism_helper_lemmas: List[Lemma]`: Helper lemmas for the isomorphism proof.
    - `correctness_helper_lemmas: List[Lemma]`: Helper lemmas for the correctness proof.
    - `to_dict(self) -> Dict[str, Any]`: Serializes the `LeanProblem` to a dictionary.
    - `to_json(self) -> str`: Serializes the `LeanProblem` to a JSON string.
    - `to_csv(self) -> tuple[List[str], List[str]]`: Converts the problem data into a flat list of headers and a list of values for CSV output.
- **`@dataclass LeanProblemView`**: A data class designed to offer a specific "view" or subset of a `LeanProblem`'s data, tailored for a particular `TaskComponent`. It shares many fields with `LeanProblem` but `problem_id` is a string.
    - `task_component: TaskComponent`: Indicates the task for which this view is relevant.
    - `hide_params(self, *args)`: A method to selectively set specified attributes to `None` or empty lists, effectively "hiding" them for certain use cases.
- **`format_problem_as_lean_with_line_ranges(problem: LeanProblemView) -> tuple[str, dict]`**: A function that takes a `LeanProblemView` and generates a multi-line string representing the problem in Lean code format. It also returns a dictionary mapping labels (e.g., "isomorphism", "correctness") to tuples representing the start and end line numbers of those sections in the generated string. If proofs are missing, they default to `by sorry`.

## Important Variables/Constants
The fields within the dataclasses are the primary "variables." Key attributes include:
- `LeanProblem.problem_id`: The unique identifier.
- `LeanProblem.problem_spec_formal_ground_truth`: The canonical Lean specification.
- `LeanProblem.implementation`: The Lean code solution.
- `LeanProblem.correctness_theorem` and `LeanProblem.correctness_proof`: Crucial for verifying the implementation.
- `LeanProblemView.task_component`: Determines the context for the view.

## Usage Examples
```python
from clever_bench.lean_problem import (
    LeanProblem, ProblemSpecMetadata, Lemma, TaskComponent,
    LeanProblemView, format_problem_as_lean_with_line_ranges
)

# 1. Define metadata and lemmas
metadata = ProblemSpecMetadata(
    function_signature="def square (n: Nat) : Nat",
    docstring="Squares a natural number.",
    test_cases=[{"input": "square 3", "output": "9"}]
)
helper_lemma = Lemma(statement="theorem helper_sq: 1 * 1 = 1", proof="rfl")

# 2. Create a LeanProblem instance
problem = LeanProblem(
    problem_id=1,
    problem_spec_metadata=metadata,
    problem_spec_nl="Write a Lean function that squares a natural number and prove its correctness.",
    problem_spec_formal_ground_truth="theorem square_spec (n: Nat) : square n = n * n := by sorry",
    implementation_signature="def square (n: Nat) : Nat :=",
    implementation="  n * n",
    correctness_theorem="theorem square_correct (n: Nat) : square n = n * n := by sorry",
    correctness_proof=None, # To be filled by a proof generation task
    helper_definitions=["import Mathlib.Tactic"],
    correctness_helper_lemmas=[helper_lemma]
)

# 3. Serialize to JSON
print(f"Problem JSON: {problem.to_json(indent=2)}")

# 4. Create a LeanProblemView for a specific task (e.g., proof generation)
proof_gen_view = LeanProblemView(
    problem_id=str(problem.problem_id),
    task_component=TaskComponent.PROOF_GENERATION,
    problem_spec_formal_ground_truth=problem.problem_spec_formal_ground_truth,
    implementation_signature=problem.implementation_signature,
    implementation=problem.implementation,
    correctness_theorem=problem.correctness_theorem,
    correctness_proof=problem.correctness_proof, # This would be None or "by sorry"
    helper_definitions=problem.helper_definitions,
    correctness_helper_lemmas=problem.correctness_helper_lemmas
)

# 5. Format the view as Lean code with line ranges
lean_code, ranges = format_problem_as_lean_with_line_ranges(proof_gen_view)
print(f"\nFormatted Lean Code for Proof Generation:\n{lean_code}")
print(f"\nLine Ranges for Proof Section: {ranges.get('correctness')}")

# Example: If the task was implementation generation, the implementation might be hidden/None
impl_gen_view = LeanProblemView(
    problem_id=str(problem.problem_id),
    task_component=TaskComponent.IMPL_GENERATION,
    problem_spec_formal_ground_truth=problem.problem_spec_formal_ground_truth,
    implementation_signature=problem.implementation_signature,
    implementation=None, # This would be the part to generate
    correctness_theorem=problem.correctness_theorem
)
impl_gen_view.hide_params("correctness_proof", "isomorphism_proof") # Hide irrelevant proofs
lean_code_impl, _ = format_problem_as_lean_with_line_ranges(impl_gen_view)
print(f"\nFormatted Lean Code for Implementation Generation:\n{lean_code_impl}")

```

## Dependencies and Interactions
- **`dataclasses`**: Python's built-in module used extensively for creating structured data classes (`@dataclass`, `field`, `asdict`).
- **`typing`**: Standard Python module for type hints (`List`, `Optional`, `Dict`, `Any`).
- **`enum`**: Standard Python module for creating enumerations (`Enum`, `auto`).
- **`json`**: Python's built-in JSON library, used in `LeanProblem.to_json()` and internally by `LeanProblem.to_csv()` for serializing list/dict fields.
- **Interaction with `LeanSpecParser`**: The `LeanProblem` objects are typically instantiated and populated by `LeanSpecParser` (from `lean_parser_spec.py`) after it parses Lean files.
- **Output Formatting**: The `format_problem_as_lean_with_line_ranges` function produces Lean code strings that are likely consumed by other tools or processes that need to interact with or display Lean problems in a structured textual format.
