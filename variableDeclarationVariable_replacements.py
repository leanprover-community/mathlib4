def process_file_in_place(file_path, line_numbers):
    with open(file_path, 'r') as infile:
        lines = infile.readlines()

    # Process each line number in the input
    for line_number in line_numbers:
        # Convert to zero-indexed for Python list
        index = line_number - 1

        # Check if the line is within the file range
        if 0 <= index < len(lines):
            # First, find the first "variable" line before the current line
            before_index = None
            for i in range(index - 1, -1, -1):
                if "variable" in lines[i]:
                    before_index = i
                    break

            # Then, find the first "variable" line after the current line
            after_index = None
            for i in range(index + 1, len(lines)):
                if "variable" in lines[i]:
                    after_index = i
                    break

            # Modify the "variable" line before the input line (if found)
            if before_index is not None:
                lines[before_index] = lines[before_index].strip() + " in\n"

            # Remove the "variable" line after the input line (if found)
            if after_index is not None:
                lines[after_index] = None

    # Write the modified content back to the file
    with open(file_path, 'w') as outfile:
        # Filter out any None values (which represent deleted lines)
        outfile.writelines([line for line in lines if line is not None])

    print(f"File '{file_path}' has been modified in place.")

# Example usage
line_numbers = [186, 232]  # Example line numbers
process_file_in_place("Mathlib/Algebra/ContinuedFractions/Basic.lean", line_numbers)

# code -r -g  ././././Mathlib/Algebra/ContinuedFractions/Basic.lean:186
# code -r -g  ././././Mathlib/Algebra/ContinuedFractions/Basic.lean:232
