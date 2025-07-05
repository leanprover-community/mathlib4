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
                if lines[i] is not None and "variable" in lines[i]:
                    before_index = i
                    break

            # Then, find the first "variable" line after the current line
            after_index = None
            for i in range(index + 1, len(lines)):
                if lines[i] is not None and "variable" in lines[i]:
                    after_index = i
                    break

            # Modify the "variable" line before the input line (if found)
            if before_index is not None:
                # Append " in" to the line
                lines[before_index] = lines[before_index].strip() + " in\n"

                # Remove the "variable" line after the current one (if found)
                if after_index is not None:
                    lines[after_index] = None  # Mark for removal

                # Handle the empty lines: ensure exactly one empty line before the modified "variable" line
                # Remove all empty lines that precede the modified "variable" line
                while before_index - 1 >= 0 and lines[before_index - 1] and lines[before_index - 1].strip() == '':
                    lines[before_index - 1] = None  # Remove preceding empty lines
                    before_index -= 1

                # Ensure exactly one empty line before the "variable in" line
                if before_index - 1 >= 0 and lines[before_index - 1] and lines[before_index - 1].strip() != '':
                    lines.insert(before_index, '\n')  # Insert a single empty line before it

                # Remove all empty lines after the modified "variable in" line
                next_index = before_index + 3
                while next_index < len(lines) and (lines[next_index] is None or lines[next_index].strip() == ''):
                    lines[next_index] = None  # Remove empty lines after the "variable in" line
                    next_index += 1

                # Remove all empty lines after the removed "variable" line
                next_index = after_index+1
                #print(next_index)
                #print(lines[next_index])
                while next_index < len(lines) and (lines[next_index] is None or lines[next_index].strip() == ''):
                    lines[next_index] = None  # Remove empty lines after the "variable in" line
                    next_index += 1

    # Write the modified content back to the file
    with open(file_path, 'w') as outfile:
        for line in lines:
            # Avoid writing None lines (those marked for removal)
            if line is not None:
                outfile.write(line)

    print(f"File '{file_path}' has been modified in place.")

# Example usage
#line_numbers = [186, 234]  # Example line numbers
#process_file_in_place("Mathlib/Algebra/ContinuedFractions/Basic.lean", line_numbers)
