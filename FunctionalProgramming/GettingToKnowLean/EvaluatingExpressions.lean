-- https://ideal-trout-55j7v6qwr434r55.github.dev/

-- 1.1. Evaluating Expressions

#eval 1 + 2

#eval 1 + 2 * 5

#eval String.append "Hello, " "Lean!"

#eval String.append "great " (String.append "oak " "tree")

#eval String.append "it is " (if 1 > 2 then "yes" else "no")

-- 1.1.2. Exercises

-- What are the values of the following expressions? Work them out by hand,
-- then enter them into Lean to check your work.

#eval 42 + 19

#eval String.append "A" (String.append "B" "C")

#eval String.append (String.append "A" "B") "C"

#eval if 3 == 3 then 5 else 7

#eval if 3 == 4 then "equal" else "not equal"
