import Mathlib.LinearAlgebra.LinearIndependent

set_option pp.unicode.fun true

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] {s : Set V} {x : V}
  (hs : LinearIndependent K (fun b => b : s → V))
  (hs' : LinearIndependent K (Subtype.val : s → V))

/-- info: hs : LinearIndependent K fun (b : ↑s) ↦ ↑b -/
#guard_msgs in #check hs

/-- info: hs' : LinearIndependent (ι := { x // x ∈ s }) K Subtype.val -/
#guard_msgs in #check hs'
