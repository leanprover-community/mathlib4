import os

def add_question_mark(input_file, output_file, positions):
    with open(input_file, 'r') as file:
        content = file.read()

    # Convert the string to a list for easier manipulation
    chars = list(content)

    # Insert question marks at the specified positions
    for zo, pos in sorted(positions):
        if 0 <= pos <= len(chars):
            if zo == 0:
                chars.insert(pos, '?')
            else:
                chars = chars[:pos+6] + chars[pos+7:]

    # Join the list back into a single string
    modified_content = ''.join(chars)

    with open(output_file, 'w') as file:
        file.write(modified_content)

# Example usage:
input_file = 'Mathlib/Data/Set/Pointwise/Basic.lean'
output_file = 'output.lean'
positions = [(1, 38106), (0, 38150), (0, 38168)]  # positions where to add the question marks

#add_question_mark(input_file, output_file, positions)


def merge_strings(withLB1, withQM1):
    final = ""
    charLx = 0
    charRx = 0
    withLB = withLB1 #.encode('utf-8')
    withQM = withQM1 #.encode('utf-8')
    for char in range(0, len(withLB) + len(withQM)):
        if len(withLB) < charLx + 20000:
            return final + withQM[charRx:]
        elif len(withQM) < charRx + 20000:
            return final + withLB[charLx:]
        else:
            lx = withLB[charLx]
            rx = withQM[charRx]
            if lx == rx:
                final += lx
                charLx += 1
                charRx += 1
            elif lx == "\n":
                final += lx
                charLx += 1
            elif rx == "?":
                final += rx
                charRx += 1
    return final

left  = "refine _\n  i continue _ _ _\n  ⟨_ _ _⟩"
right = "refine ?_  i continue _ ?_ _  ⟨?_ _ ?_ _ ?_⟩"

print(merge_strings(left, right))

#def count_smaller_than(array, tgLine, threshold):
#    count = 0
#    for zo, line, col in array:
#        if zo == 0 and line == tgLine and col < threshold:
#            count += 1
#        #if zo == 1 and line == tgLine and col < threshold-6:
#        #    count -= 1
#    return count
#
#def add_question_mark(file_path, output_path, positions):
#    def insert_question_mark(line, col_index):
#        char_index = 0
#        code_point_count = 0
#        while code_point_count < col_index and char_index < len(line):
#            code_point_count += 1
#            char_index += len(line[char_index]) #.encode('utf-8'))
#        return line[:char_index] + '?' + line[char_index:]
#
#    with open(file_path, 'r', encoding='utf-8') as file:
#        text_lines = file.readlines()
#
#    for zo, line0, col0 in positions:
#        line = line0 - 1
#        col = col0 + count_smaller_than(positions, line0, col0)
#        if 0 <= line < len(text_lines):
#            if zo == 0:
#                text_lines[line] = insert_question_mark(text_lines[line], col)
#            else:
#              text_lines[line] = text_lines[line][:col+6] + text_lines[line][col+7:]
#
#    with open(output_path, 'w', encoding='utf-8') as file:
#        file.writelines(text_lines)
#
