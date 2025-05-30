# src/clever_bench/lean_parser_spec.py

## Overview
The `src/clever_bench/lean_parser_spec.py` file provides the `LeanSpecParser` class, designed to parse structured Lean code files. These files are expected to contain specific comment-delimited sections that define theorem proving problems, including their metadata, formal specifications, implementations, proofs, and associated helper lemmas. The parser extracts this information and organizes it into a `LeanProblem` object. A key feature is its ability to selectively include common helper definitions based on the problem's ID and whether it's designated as a sample problem, by parsing metadata embedded in the helper definition files.

## Key Components
- **`LeanSpecParser` class**:
    - `__init__(self, lean_code: str, helper_definitions: str = None, problem_id: int = None, is_sample: bool = False)`: Constructor that initializes the parser with the Lean code content, an optional string of shared helper definitions, a unique problem identifier, and a boolean flag indicating if the problem is a sample. It pre-processes the `lean_code` by calling `_extract_sections`.
    - `_extract_sections(self) -> dict`: Uses regular expressions to identify and extract content from specially formatted comment blocks (e.g., `-- start_def SECTION_NAME ... -- end_def SECTION_NAME`). The extracted sections are stored in a dictionary, where keys are section names and values are lists of strings (content of each section).
    - `_parse_helper_definitions(self) -> List[str]`: If `helper_definitions` are provided, this method parses them to find relevant definitions for the current `problem_id` and `is_sample` status. It looks for YAML metadata within comment blocks in the helper definitions to determine which definitions to include.
    - `_parse_yaml_block(self, raw: str) -> Optional[ProblemSpecMetadata]`: Parses YAML content embedded within a comment block (typically `/-- ... --/`). It extracts fields like `function_signature`, `docstring`, and `test_cases` and populates a `ProblemSpecMetadata` object. Returns `None` if parsing fails or no YAML block is found.
    - `_get_lemmas(self, prefix: str) -> List[Lemma]`: Constructs a list of `Lemma` objects. It retrieves lemma statements and their corresponding proofs from the extracted sections based on a given `prefix` (e.g., `iso_helper_lemmas` for statements and `iso_helper_lemmas_proof` for proofs).
    - `_get_first(self, key: str) -> Optional[str]`: A utility method to retrieve the first string from a list of section contents associated with a `key`, or `None` if the section is empty or not found.
    - `parse(self) -> LeanProblem`: The main public method that drives the parsing process. It calls the various private methods to extract all necessary components (metadata, specifications, implementation, lemmas, etc.) from the `lean_code` and `helper_definitions`, and then instantiates and returns a `LeanProblem` object.

## Important Variables/Constants
- **`LeanSpecParser.lean_code: str`**: The raw Lean code string provided to the parser instance.
- **`LeanSpecParser.helper_definitions: Optional[str]`**: An optional string containing Lean definitions that can be shared across multiple problems.
- **`LeanSpecParser.problem_id: Optional[int]`**: An identifier for the specific problem being parsed, used for linking with specific helper definitions.
- **`LeanSpecParser.is_sample: bool`**: A flag to indicate if the problem is a sample problem, which can affect which helper definitions are loaded.
- **`LeanSpecParser.sections: dict`**: A dictionary populated by `_extract_sections`, holding the raw string content of different parts of the Lean problem file, keyed by section names.
- **Regular Expression Patterns**: Implicitly, the regex patterns used in `_extract_sections` and `_parse_helper_definitions` are crucial for correctly identifying and delimiting the sections within the Lean code and helper files.

## Usage Examples
```python
from clever_bench.lean_parser_spec import LeanSpecParser
from clever_bench.lean_problem import LeanProblem # For context and type hint

# --- Example Lean Code (simplified) ---
lean_file_content = """
-- start_def problem_details
/--
function_signature: "def add_one (n: Nat) : Nat"
docstring: "Adds one to a natural number."
test_cases:
  - "add_one 0 = 1"
  - "add_one 5 = 6"
-/
-- end_def problem_details

-- start_def problem_spec
theorem add_one_spec (n: Nat) : add_one n = n + 1 :=
sorry
-- end_def problem_spec

-- start_def implementation
def add_one (n: Nat) : Nat :=
  n + 1
-- end_def implementation
"""

# --- Example Helper Definitions (simplified) ---
helper_definitions_content = """
-- start_def helper_definitions
/--
problems: [101, 102]
sample_problems: [1] 
-/
def common_nat_lemma : True := trivial
-- end_def helper_definitions

-- start_def helper_definitions
/--
problems: [103]
-/
def specific_lemma_for_103 : True := trivial
-- end_def helper_definitions
"""

# --- Parsing a standard problem ---
# Assume this is problem 101
parser_std = LeanSpecParser(
    lean_code=lean_file_content,
    helper_definitions=helper_definitions_content,
    problem_id=101,
    is_sample=False
)
problem_std: LeanProblem = parser_std.parse()

print(f"Standard Problem ID: {problem_std.problem_id}")
if problem_std.problem_spec_metadata:
    print(f"Signature: {problem_std.problem_spec_metadata.function_signature}")
# This problem (101) should load 'common_nat_lemma'
print(f"Helper definitions loaded: {len(problem_std.helper_definitions)}")
if len(problem_std.helper_definitions) > 0:
    print(f"First helper: {problem_std.helper_definitions[0][:50]}...") # Print start of helper

# --- Parsing a sample problem ---
# Assume this is sample problem 1
parser_sample = LeanSpecParser(
    lean_code=lean_file_content, # Using same content for simplicity
    helper_definitions=helper_definitions_content,
    problem_id=1,
    is_sample=True
)
problem_sample: LeanProblem = parser_sample.parse()

print(f"Sample Problem ID: {problem_sample.problem_id}")
# This sample problem (1) should also load 'common_nat_lemma'
print(f"Helper definitions loaded: {len(problem_sample.helper_definitions)}")
if len(problem_sample.helper_definitions) > 0:
    print(f"First helper: {problem_sample.helper_definitions[0][:50]}...")
```

## Dependencies and Interactions
- **`re` (Regular Expressions)**: Heavily used for pattern matching to find and extract the specially delimited sections within the Lean code (e.g., `re.compile`, `pattern.finditer`).
- **`yaml` (`PyYAML`)**: Used to parse YAML blocks found within comments (specifically `/-- ... --/`) to extract structured metadata like function signatures, docstrings, and test cases (`yaml.safe_load`).
- **`clever_bench.lean_problem.LeanProblem`**: This is the primary output data structure. The `LeanSpecParser` populates instances of `LeanProblem` with the information it extracts. This is an internal dependency from another module in the same project.
- **`clever_bench.lean_problem.ProblemSpecMetadata`**: A data class (likely Pydantic or a standard dataclass) used to hold the structured metadata parsed from the YAML blocks.
- **`clever_bench.lean_problem.Lemma`**: A data class used to represent a lemma, typically containing its statement and proof.
- **`typing.List`, `typing.Optional`**: Standard Python typing library used for type hinting to improve code clarity and robustness.
- **Input Lean Files**: The parser expects Lean files (`.lean`) or strings of Lean code that adhere to a specific commenting convention (e.g., `-- start_def ... -- end_def ...`) for structuring different parts of a problem definition.
- **Helper Definition Files**: Similarly, any provided helper definition strings are expected to follow a similar structure, with additional YAML metadata to specify which problems or sample problems each helper block applies to.
