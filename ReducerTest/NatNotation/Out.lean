-- [✓] remove import Lean.Compiler.NoncomputableAttr

import Lean
import Init
import LeanReducer.Command

-- removed ././././Mathlib/Data/Nat/Notation.lean:L9:0,

@[inherit_doc] notation "ℕ" => Nat

def f := 42

def g := f

-- removed Mathlib/ReducerTest.lean:L8:0,

/-- info: 42 -/
#preserve_this in
#eval (g : ℕ)
