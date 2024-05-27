def add_question_mark(file_path, output_path, positions):
    def insert_question_mark(line, col_index):
        char_index = 0
        code_point_count = 0
        while code_point_count < col_index and char_index < len(line):
            code_point_count += 1
            char_index += len(line[char_index]) #.encode('utf-8'))
        return line[:char_index] + '?' + line[char_index:]

    with open(file_path, 'r', encoding='utf-8') as file:
        text_lines = file.readlines()

    for zo, line0, col in positions:
        line = line0 - 1
        if 0 <= line < len(text_lines):
            if zo == 0:
                text_lines[line] = insert_question_mark(text_lines[line], col)
            else:
              text_lines[line] = text_lines[line][:col+6] + text_lines[line][col+7:]

    with open(output_path, 'w', encoding='utf-8') as file:
        file.writelines(text_lines)

# Example usage:
input_file = 'Mathlib/Order/Ideal.lean'
output_file = 'output.lean'
# (0 for (+?) or 1 for (-'), line number, code point index)
positions = [(0, 466, 26), (1, 466, 6)]

add_question_mark(input_file, output_file, positions)
