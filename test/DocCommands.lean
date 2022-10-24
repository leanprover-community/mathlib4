import Mathlib.Tactic.DocCommands
open Lean

/--This is my amazing docstring.-/
def hi (x: Nat) := x + 1

def one : Nat := 2 + 3
def two (x : Nat) : Nat := x + 8
def three : Nat := 10

copy_doc_string hi → one two

#eval show MetaM _ from do
  guard ((← findDocString? (← getEnv) `one) == some "This is my amazing docstring.")
  guard ((← findDocString? (← getEnv) `two) == some "This is my amazing docstring.")
  guard ((← findDocString? (← getEnv) `three) == none)


def four := 4
def five := 5

/--Doc string for four.-/
add_decl_doc four

#eval show MetaM _ from do
  guard ((← findDocString? (← getEnv) `four) == some "Doc string for four.")
  guard ((← findDocString? (← getEnv) `five) == none)
