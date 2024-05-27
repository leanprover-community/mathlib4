# def add_question_mark(text, lines_columns):
#     text_lines = text.split('\n')
#     for line, col in lines_columns:
#         if 0 <= line < len(text_lines) and 0 <= col <= len(text_lines[line]):
#             text_lines[line] = text_lines[line][:col] + '?' + text_lines[line][col:]
#     return '\n'.join(text_lines)
#
# # Example usage:
# text = """This is line 1
# This is line 2
# This is line 3"""
#
# lines_columns = [(0, 4), (1, 8), (2, 10)]
#
# new_text = add_question_mark(text, lines_columns)
# print(new_text)

import os

def count_smaller_than(array, tgLine, threshold):
    count = 0
    for zo, line, col in array:
        if zo == 0 and line == tgLine and col < threshold:
            count += 1
        if zo == 1 and line == tgLine and col < threshold-6:
            count -= 1
    return count

#def count_primes(array, tgLine, threshold):
#    count = 0
#    for _, line, col in array:
#        if line == tgLine and col < threshold:
#            count += 1
#    return count

def add_question_mark(file_path, output_path, lines_columns):
    with open(file_path, 'r') as file:
        text_lines = file.readlines()

    for tf, line0, col0 in lines_columns:
        line = line0 - 1
        col = col0 + 0*count_smaller_than(lines_columns, line0, col0)
        if 0 <= line < len(text_lines) and 0 <= col <= len(text_lines[line]):
            if tf == 0:
              text_lines[line] = text_lines[line][:col] + '?' + text_lines[line][col:]
            else:
              text_lines[line] = text_lines[line][:col+6] + text_lines[line][col+7:]

    with open(output_path, 'w') as file:
        file.writelines(text_lines)

# Example usage:
#input_file = 'Mathlib/Algebra/Group/Pi/Lemmas.lean'
#output_file = 'output.lean'
#lines_columns = [(0, 369, 23), (0, 369, 20), (1, 369, 2), (0, 376, 56), (1, 376, 6)]

#lines_columns = [(0, 609, 38), (1, 609, 6), (0, 1370, 20), (1, 1370, 4), (0, 1374, 35), (1, 1374, 4), (0, 1502, 73), (1, 1502, 2), (0, 1510, 70), (1, 1510, 2), (0, 1532, 64), (1, 1532, 2), (0, 1535, 44), (1, 1535, 2), (0, 1848, 74), (1, 1848, 2), (0, 2021, 46), (1, 2021, 2)]
#add_question_mark(input_file, output_file, lines_columns)
#
#os.rename(output_file, input_file)


#input_file = 'Mathlib/SetTheory/Ordinal/FixedPoint.lean'
#output_file = 'output.lean'
#lines_columns = [(1, 204, 7), (1, 123, 25), (0, 130, 20), (0, 130, 34), (0, 192, 41), (0, 204, 30), (0, 210, 35), (0, 234, 26), (0, 234, 11), (0, 303, 43), (0, 329, 20), (0, 329, 37), (0, 378, 45), (0, 387, 58), (0, 398, 90), (0, 426, 38), (0, 426, 57), (0, 581, 20), (0, 581, 32), (0, 599, 25), (0, 599, 11), (0, 634, 43), (0, 677, 34), (0, 677, 22), (0, 683, 60), (0, 718, 11), (0, 718, 25)]
##
#add_question_mark(input_file, output_file, lines_columns)
#

#[(130, 20), (130, 34), (192, 41), (204, 30), (210, 35), (234, 26), (234, 11), (303, 43), (329, 20), (329, 37), (378, 45), (387, 58), (398, 90), (426, 38), (426, 57), (581, 20), (581, 32), (599, 25), (599, 11), (634, 43), (677, 34), (677, 22), (683, 60), (718, 11), (718, 25)]
