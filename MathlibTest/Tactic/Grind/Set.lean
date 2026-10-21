module

public import Mathlib

@[expose] public section

example (h : ({[], ['a']} : Set (List Char)) = {[], ['a'], ['b']}) : False := by grind
