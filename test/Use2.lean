import Mathlib.RingTheory.Ideal.Operations

example {R : Type*} [CommRing R] {I J : Ideal R} {x : R} (hx : x ∈ I • J) :
      ∃ n: ℕ, True := by
   let P : R → Prop := fun x ↦ ∃ n : ℕ, True
   apply Submodule.smul_induction_on (p := P) hx
   intro a ha b hb
   use 1
