import os
import re
import subprocess
import shutil
import tempfile

def process_warnings(file_path):
    with open(file_path, 'r') as f:
        lines = f.readlines()

    warnings = []
    current_file = None

    for line in lines:
        if line.startswith("\u26a0"):
            match = re.search(r"Replayed\s([\w.]+)", line)
            if match:
                current_file = match.group(1).replace(".", "/") + ".lean"
        elif "warning:" in line:
            match = re.search(r":(\d+):(\d+): Detected a `let` expression", line)
            if match and current_file:
                warnings.append((current_file, int(match.group(1)), int(match.group(2))))

    return warnings

def validate_and_replace(file, line, col):
    with open(file, 'r') as f:
        lines = f.readlines()

    # Use the provided line and column indices directly
    line_idx = line - 1
    col_idx = col

    if line_idx >= len(lines):
        print(f"Line index {line_idx} is out of range for file {file}")
        return False

    target_line = lines[line_idx]

    # Check if the column index is valid
    if col_idx < 0 or col_idx + 4 > len(target_line):
        print(f"Column index {col_idx} is out of range for line {line_idx + 1} in file {file}")
        return False

    # Check for `let ` (with a trailing space) at the specified position
    if target_line[col_idx:col_idx + 4] == "let ":
        # Replace `let ` with `let_fun `
        updated_line = target_line[:col_idx] + "let_fun " + target_line[col_idx + 4:]
        lines[line_idx] = updated_line

        # Write the updated lines back to the file
        with open(file, 'w') as f:
            f.writelines(lines)

        return True
    else:
        # Print the actual four characters found for debugging
        actual_chars = target_line[col_idx:col_idx + 4]
        print(f"`let ` not found at line {line}, column {col} in file {file}. Line content: '{target_line.strip()}'. Expected 'let ' but found '{actual_chars}'")
        return False

def run_lake_build(file, original_content):
    # Convert file path to module format
    module_name = file.replace("/", ".").replace(".lean", "")
    cmd = ["lake", "build", module_name]
    print(f"Running build command: {' '.join(cmd)}")
    result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if result.returncode != 0:
        print(f"Build failed for {file}. Output:\n{result.stdout.decode()}{result.stderr.decode()}")
        # Revert file changes
        with open(file, 'w') as f:
            f.writelines(original_content)
        print(f"Reverted changes for {file}")
    return result.returncode == 0

def main(input_file):
    # Read exceptions from exceptions.txt
    with open("exceptions.txt", 'r') as f:
        exceptions = {line.strip() for line in f.readlines()}

    warnings = process_warnings(input_file)
    failed_builds = []

    for file, line, col in warnings:
        if file in exceptions:
            print(f"Skipping {file} as it is in exceptions.txt")
            continue

        with open(file, 'r') as f:
            original_content = f.readlines()

        if validate_and_replace(file, line, col):
            print(f"Modified {file} at line {line}, column {col}")
            if not run_lake_build(file, original_content):
                print(f"Build failed for {file}")
                failed_builds.append(file)
            else:
                print(f"Build succeeded for {file}")
        else:
            print(f"Validation failed for {file} at line {line}, column {col}")

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
