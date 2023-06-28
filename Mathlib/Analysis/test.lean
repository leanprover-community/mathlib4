import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.Rewrites

axiom K : Type
@[instance] axiom K.field : Field K

def foo : K → K := sorry

def bar : K := sorry

example : foo x = 1 ↔ ∃ k : ℤ, x = 2 * bar * k + bar / 2 := by
  rw?
