# src/scripts/score_solutions.py

## Overview
The `src/scripts/score_solutions.py` script is a command-line tool designed to automatically score solutions for tasks within a Lean project. It operates by analyzing a Lean build log file to detect the presence of `sorry` placeholders associated with specific tasks. If a task has no remaining `sorry`s in its relevant files (as indicated by the build log), it is considered complete and awarded a predefined score. Otherwise, it receives a score of zero. The script reads task definitions and their potential scores from a JSON summary file and outputs the results to another JSON file and the console.

## Key Components
The script's functionality is primarily contained within the `main()` function.

- **`main()` function**:
    - **Argument Parsing**: Initializes `argparse` to accept command-line arguments: `--build_log`, `--task_summary_file`, and `--score_file`.
    - **File Reading**:
        - Reads the content of the Lean build log specified by `--build_log`.
        - Reads and parses the JSON task summary specified by `--task_summary_file`. This file contains a list of tasks, each with a name and a potential score.
    - **Scoring Logic**:
        - Iterates through each task defined in the task summary.
        - For each `task_name`, it dynamically constructs a regular expression: `rf"{task_name}:\d+:\d+:([\s]*)declaration uses 'sorry'"`. This regex is designed to find lines in the build log that indicate a `sorry` was used within a file or declaration associated with that `task_name`.
        - It uses `re.compile` and `task_regex.findall(build_log)` to find all occurrences matching this pattern for the current task.
        - If no matches are found (i.e., `len(problems) == 0`), the task is considered successfully completed, and its predefined `score` (from the task summary) is awarded.
        - If matches are found, the task is considered incomplete, and a score of 0 is awarded.
        - Progress messages for each task (done or incomplete) are printed to the console.
    - **Output**:
        - Stores the calculated scores in a dictionary (`scores`) mapping task names to their awarded points.
        - Ensures the output directory for the score file exists (e.g., `src/lean4/temp/`).
        - Writes the `scores` dictionary to the JSON file specified by `--score_file`.
        - Prints the content of the score file and the total sum of scores to the console.

## Important Variables/Constants
- **Command-Line Arguments**:
    - **`--build_log`**:
        - Type: `str`
        - Default: `src/lean4/lean4_build.log`
        - Purpose: Specifies the path to the Lean build log file. This file is crucial as it's parsed for "sorry" messages.
    - **`--task_summary_file`**:
        - Type: `str`
        - Default: `src/lean4/task_summary.json`
        - Purpose: Specifies the path to a JSON file that lists all tasks to be scored. Each task entry should include at least `"task_name"` and `"score"` (the maximum points for that task).
    - **`--score_file`**:
        - Type: `str`
        - Default: `src/lean4/temp/score.json`
        - Purpose: Specifies the path where the output JSON file containing the scores will be saved.

- **Key Internal Variables**:
    - `build_log` (string): Stores the entire content of the build log file.
    - `task_summary` (dict): Stores the parsed content of the task summary JSON.
    - `tasks` (list of dicts): Extracted list of task objects from `task_summary["tasks"]`.
    - `scores` (dict): Accumulates the scores for each task, with task names as keys.
    - `rexp` (string): The dynamically generated regular expression pattern used to find `sorry` messages related to a specific task.
    - `task_regex` (compiled regex object): The compiled version of `rexp` for efficient searching.

## Usage Examples
To use the script, you would typically run it from the command line after a Lean build process has completed and generated a build log.

1.  **Using default file paths**:
    If your build log is at `src/lean4/lean4_build.log` and your task summary is at `src/lean4/task_summary.json`, you can run:
    ```bash
    python src/scripts/score_solutions.py
    ```

2.  **Specifying custom file paths**:
    ```bash
    python src/scripts/score_solutions.py \
        --build_log /path/to/my_project_build.log \
        --task_summary_file /path/to/custom_tasks.json \
        --score_file /path/to/output/final_scores.json
    ```

**Example `task_summary.json` content**:
```json
{
  "tasks": [
    {
      "task_name": "Problem1_Proof",
      "score": 10
    },
    {
      "task_name": "Problem2_Implementation",
      "score": 15
    },
    {
      "task_name": "Problem3_Spec",
      "score": 5
    }
  ]
}
```

**Interpreting Output**:
- **Console Output**:
    ```
    Task Problem1_Proof done successfully.
    Task Problem2_Implementation incomplete.
    Task Problem3_Spec done successfully.
    {
        "Problem1_Proof": 10,
        "Problem2_Implementation": 0,
        "Problem3_Spec": 5
    }
    Total score: 15
    ```
- **Score File (`--score_file`)**:
    The JSON file (e.g., `src/lean4/temp/score.json`) would contain:
    ```json
    {
        "Problem1_Proof": 10,
        "Problem2_Implementation": 0,
        "Problem3_Spec": 5
    }
    ```

## Dependencies and Interactions
- **Python Standard Libraries**:
    - `os`: Used for file system interactions like checking path existence (`os.path.exists`) and creating directories (`os.makedirs`).
    - `json`: Essential for reading the `--task_summary_file` and writing the `--score_file`.
    - `argparse`: Used for parsing command-line arguments provided to the script.
    - `re`: The regular expression library, critical for searching the build log for patterns indicating `sorry` placeholders.

- **File Formats & External Data**:
    - **Lean Build Log (`--build_log`)**: The script assumes this is a text file generated by a Lean build process (e.g., `lake build > lean4_build.log`). The accuracy of scoring heavily depends on the format of "sorry" messages in this log. Specifically, it expects messages like: `[task_name]:[line]:[column]: declaration uses 'sorry'`, where `[task_name]` matches a name in the `task_summary.json`.
    - **Task Summary JSON (`--task_summary_file`)**: This input JSON file must conform to a structure where a top-level key `"tasks"` holds a list of objects, each object having at least a `"task_name"` (string) and a `"score"` (numeric value).
    - **Output Score JSON (`--score_file`)**: The script produces a JSON file containing a simple dictionary mapping task names (strings) to their awarded scores (numbers).

- **Lean Build Process**: Implicitly, the script relies on a preceding Lean build process that generates the build log. The content and format of this log are vital for the script's operation. The `task_name` used in the log messages (e.g., derived from file names or specific Lean project configurations) must align with the `task_name` entries in the `task_summary.json` for accurate scoring.
