import LeanReducer.Command
import Mathlib.Logic.Basic

def f := 42

def g := f

def h := g

/-- info: 42 -/
#preserve_this in
#eval (g : ℕ)
