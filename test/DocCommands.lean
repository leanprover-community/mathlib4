import Mathlib.Tactic.DocCommands

/--
This is my amazing docstring.
-/
def hi (x: Nat) := x + 1

def one : Nat := 2 + 3
def two (x : Nat) : Nat := x + 8
def three : Nat := 10

copy_doc_string hi → one two

#print one   -- we see a docstring
#print two   -- we see a docstring
#print three -- no docstring
