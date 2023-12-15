
import os
import re

def extract_simp_rw_from_simp_only(filename):

    lines = list(open(filename, "r"))

    # Find first line with a simp_only
    for line in list(lines):
        if "simp only" in line:
            break

    print(f"Bot found line {line}")

    simp_only_start = line.find("simp only")
    lemmas_start = line.find("[") + 1
    lemmas_end = line.find("]")
    lemmas = line[lemmas_start:lemmas_end].split(", ")
    print("Lemmas found:", lemmas)
    for lemma in lemmas:
        assert("," not in lemma)
        other_lemmas = list(lemmas)
        other_lemmas.remove(lemma)
        new_line = line[:simp_only_start] + \
            f"simp_rw [{lemma}], " + \
            f"simp only [" + ", ".join(other_lemmas) + line[lemmas_end:]
        new_lines = list(lines)
        new_lines[lines.index(line)] = new_line

        f = open(filename, "w")
        f.writelines(new_lines)
        f.close()
        exit_code = os.system(f"lean --make {filename} > /dev/null")
        if exit_code != 0:
            f = open(filename, "w")
            f.writelines(lines)
            f.close()
        else:
            break


def remove_lemma_from_simp_only(filename):

    print(f"Removing unnecessary lemmas from simp only in {filename}")

    print("Building file and deps")
    module_name = ".".join(filename[:-5].split("/"))
    exit_code = os.system(f"lake build {module_name} > /dev/null")
    assert(exit_code == 0)

    #  Represent the file as a list of lines
    with open(filename, "r") as f:
        lines = list(f)

    i = 0
    # Find first line with a simp_only
    while i < len(list(lines)):
        line = lines[i]
        if "simp only" not in line:
            i += 1
            continue

        print(f"At index {i}, found `simp only` line: {line}")

        simp_only_start = line.find("simp only")
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
            new_line = line[:simp_only_start] + \
                f"simp only [" + ", ".join(other_lemmas) + line[lemmas_end:]
            new_lines = list(lines)
            # print("A", new_lines[i])
            # print("B", lines[i])
            # print("C", new_line)
            # print("D", line)
            assert("simp only" in new_lines[i])
            new_lines[i] = new_line

            print(f"Testing removal of lemma {lemma}")

            # Write the modified lines to the file
            with open(filename, "w") as f:
                f.writelines(new_lines)
            # Get the code for the runtime
            exit_code = os.system(f"lake build {module_name} > /dev/null")

            if exit_code == 0:
                print(f"Found removable lemma {lemma}")
                lines = new_lines
                removable_lemma = lemma
                break

        if removable_lemma != None:
            lines[i] = new_line

        i += 1


    # write whatever the current version of the lines is to file
    with open(filename, "w") as f:
        f.writelines(lines)

filelist = []

for root, dirs, files in os.walk("Mathlib/Data/Finsupp"):
	for file in files:
        #append the file name to the list
		filelist.append(os.path.join(root,file))

for filename in filelist:
    print(filename)
    if filename.endswith(".lean"):
        remove_lemma_from_simp_only(filename)
