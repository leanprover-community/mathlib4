import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Rewrites

axiom K : Type
@[instance] axiom K.ring : Ring K

def foo : K → K := sorry

example : foo x = 1 ↔ ∃ k : ℤ, x = k := by
  rw?
