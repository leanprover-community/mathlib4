import os
import re
import subprocess
import shutil
import tempfile
from collections import defaultdict

def process_warnings(file_path):
    with open(file_path, 'r') as f:
        lines = f.readlines()

    warnings = defaultdict(list)
    current_file = None

    for line in lines:
        if line.startswith("\u26a0"):
            match = re.search(r"(?:Replayed|Built)\s([\w.]+)", line)
            if match:
                current_file = match.group(1).replace(".", "/") + ".lean"
        elif "warning:" in line:
            match = re.search(r":(\d+):(\d+): Detected a `let` expression", line)
            if match and current_file:
                warnings[current_file].append((int(match.group(1)), int(match.group(2))))

    return warnings

def validate_and_replace(file, line, col, replacement):
    with open(file, 'r') as f:
        lines = f.readlines()

    # Use the provided line and column indices directly
    line_idx = line - 1
    col_idx = col

    if line_idx >= len(lines):
        print(f"Line index {line_idx} is out of range for file {file}")
        return False, lines

    target_line = lines[line_idx]

    # Check if the column index is valid
    if col_idx < 0 or col_idx + 4 > len(target_line):
        print(f"Column index {col_idx} is out of range for line {line_idx + 1} in file {file}")
        return False, lines

    # Check for `let ` (with a trailing space) at the specified position
    if target_line[col_idx:col_idx + 4] == "let ":
        # Replace `let ` with the provided replacement (e.g., `let_fun ` or `letI `)
        updated_line = target_line[:col_idx] + replacement + target_line[col_idx + 4:]
        lines[line_idx] = updated_line

        # Write the updated lines back to the file
        with open(file, 'w') as f:
            f.writelines(lines)

        return True, lines
    else:
        # Print the actual four characters found for debugging
        actual_chars = target_line[col_idx:col_idx + 4]
        print(f"`let ` not found at line {line}, column {col} in file {file}. Line content: '{target_line.strip()}'. Expected 'let ' but found '{actual_chars}'")
        return False, lines

def run_lake_build(file):
    # Convert file path to module format
    module_name = file.replace("/", ".").replace(".lean", "")
    cmd = ["lake", "build", module_name]
    print(f"Running build command: {' '.join(cmd)}")
    result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if result.returncode != 0:
        print(f"Build failed for {file}. Output:\n{result.stdout.decode()}{result.stderr.decode()}")
    return result.returncode == 0

def main(input_file):
    # Read exceptions from exceptions.txt
    with open("exceptions.txt", 'r') as f:
        exceptions = {line.strip() for line in f.readlines()}

    warnings = process_warnings(input_file)
    failed_builds = []

    for file, warnings_list in warnings.items():
        if file in exceptions:
            print(f"Skipping {file} as it is in exceptions.txt")
            continue

        # Process warnings in reverse order
        with open(file, 'r') as f:
            original_content = f.readlines()

        for line, col in reversed(warnings_list):
            # Try replacing with `let_fun ` first
            success, modified_content = validate_and_replace(file, line, col, "let_fun ")
            if success:
                print(f"Modified {file} at line {line}, column {col} with 'let_fun'")
                if not run_lake_build(file):
                    # If build fails, revert and try replacing with `letI `
                    print(f"Build failed for {file} with 'let_fun', trying 'letI'")
                    with open(file, 'w') as f:
                        f.writelines(original_content)  # Revert the last change
                    success, modified_content = validate_and_replace(file, line, col, "letI ")
                    if success:
                        print(f"Modified {file} at line {line}, column {col} with 'letI'")
                        if not run_lake_build(file):
                            # If build still fails, revert the last change
                            print(f"Build failed for {file} with 'letI', reverting to original")
                            with open(file, 'w') as f:
                                f.writelines(original_content)
                            failed_builds.append(file)
                        else:
                            print(f"Build succeeded for {file} with 'letI'")
                    else:
                        print(f"Validation failed for {file} at line {line}, column {col} when trying 'letI'")
                else:
                    print(f"Build succeeded for {file} with 'let_fun'")
            else:
                print(f"Validation failed for {file} at line {line}, column {col} when trying 'let_fun'")

            # Update original_content after each successful build to maintain cumulative changes
            if success:
                original_content = modified_content

    # Print summary of failed builds
    if failed_builds:
        print("\nSummary of files that failed to build:")
        for failed_file in failed_builds:
            print(failed_file)
    else:
        print("\nAll files built successfully.")

if __name__ == "__main__":
    input_file = "build.log"  # Replace with the actual file name
    main(input_file)
