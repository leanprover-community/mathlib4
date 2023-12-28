
import os
import re
import subprocess


def module_name_from_filename(filename):
    return ".".join(filename[:-5].split("/"))

# Determines if a change to a tactic call still builds and doesn't change the proof state
# If so, it replaces it and returns True
# Otherwise, it leaves the file as is and returns False
def try_alternate_tactic_call(filename, alternate_line, line_no):

    module_name = module_name_from_filename(filename)
    # Get number of spaces at start of alternate_line
    num_spaces = len(alternate_line) - len(alternate_line.lstrip(' '))

    #  Extract the file as a list of lines
    with open(filename, "r") as f:
        lines = list(f)

    assert(lines[line_no] != alternate_line)

    initial_lines = lines.copy()

    # insert a trace state
    lines.insert(line_no+1, " " * num_spaces + "trace_state\n")

    # Run once to get trace state
    print("Running lake build")
    out_current = str(subprocess.check_output(["lake", "build", module_name]))
    # out_current, err = proc.communicate()
    err = ("error" in out_current)
    print(out_current)
    assert(err == False)

    lines[line_no] = alternate_line

    # Write the modified lines to the file
    with open(filename, "w") as f:
        f.writelines(lines)

    # Run again
    try:
        out_alternate = str(subprocess.check_output(["lake", "build", module_name]))
    except subprocess.CalledProcessError as e:
        out_alternate = str(e.output)

    # out_alternate, err = proc.communicate()
    err = ("error" in out_alternate)

    if err:
        print("Failed to build")
        with open(filename, "w") as f:
            f.writelines(initial_lines)
        return False

    if out_current != out_alternate:
        print("Outputs are different")
        with open(filename, "w") as f:
            f.writelines(initial_lines)
        return False

    # Write the modified lines to the file
    print("Success")
    # Remove the trace state
    lines.pop(line_no+1)
    with open(filename, "w") as f:
        f.writelines(lines)

    # print("a", out_current)
    # print("b", out_alternate)
    # quit()
    return True


def remove_lemma_from_simp_only(filename):

    print(f"Removing unnecessary lemmas from simp only calls in {filename}")

    module_name = module_name_from_filename(filename)
    print(f"Building file and deps: lake build {module_name} > /dev/null")
    exit_code = os.system(f"lake build {module_name} > /dev/null")
    assert(exit_code == 0)

    #  Represent the file as a list of lines
    with open(filename, "r") as f:
        lines = list(f)

    i = 0
    # Find first line with a simp_only
    while i < len(list(lines)):
        line = lines[i]
        # If there's no simp, move on
        if "simp" not in line:
            i += 1
            continue
        # If the number of spaces starting this line is the same as the next, this is not terminal
        # Therefore, move on
        if len(line) - len(line.lstrip(' ')) == len(lines[i+1]) - len(lines[i+1].lstrip(' ')):
            i += 1
            continue

        print(f"At index {i}, found `simp` line: {line}")

        # simp_only_start = line.find("simp only")
        lemmas_start = line.find("[") + 1
        lemmas_end = line.find("]")
        # If there is no close bracket, the simp only call is multiple lines. Ignore this for now
        if lemmas_end == -1:
            i += 1
            continue
        lemmas = line[lemmas_start:lemmas_end].split(", ")
        print("Lemmas found:", lemmas)

        removable_lemma = None
        # For each lemma see if it can be removed
        for lemma in lemmas:
            assert("," not in lemma)

            other_lemmas = list(lemmas)
            other_lemmas.remove(lemma)
            new_line = line[:lemmas_start] + \
                ", ".join(other_lemmas) + line[lemmas_end:]

            print(f"Trying removal of lemma {lemma}")

            try_alternate_tactic_call(filename, new_line, i)

        if removable_lemma != None:
            lines[i] = new_line

        i += 1


    # write whatever the current version of the lines is to file
    with open(filename, "w") as f:
        f.writelines(lines)

filelist = []

for root, dirs, files in os.walk("Mathlib/Algebra"):
	for file in files:
        #append the file name to the listb in v in vw411
		filelist.append(os.path.join(root,file))

for filename in filelist:
    print(filename)
    if filename.endswith(".lean"):
        remove_lemma_from_simp_only(filename)
