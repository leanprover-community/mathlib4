import Mathlib.Analysis.LocallyConvex.Separation

open Set

section Real

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {s t : Set E} {x : E}

example (hs : Convex ℝ s) (ht : Convex ℝ t) (hst : Disjoint (interior s) t)
    (hsint : (interior s).Nonempty) (htne : t.Nonempty) :
    ∃ (f : StrongDual ℝ E) (u : ℝ), f ≠ 0 ∧ (∀ a ∈ s, f a ≤ u) ∧ ∀ b ∈ t, u ≤ f b :=
  geometric_hahn_banach_of_nonempty_interior hs ht hst hsint htne

example (hs : Convex ℝ s) (hx : x ∉ interior s) (hsint : (interior s).Nonempty) :
    ∃ f : StrongDual ℝ E, f ≠ 0 ∧ ∀ a ∈ s, f a ≤ f x :=
  geometric_hahn_banach_of_nonempty_interior_point hs hx hsint

end Real

section RCLike

variable {𝕜 E : Type*} [RCLike 𝕜] [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  {s : Set E} {x : E}

example (hs : Convex ℝ s) (hx : x ∉ interior s) (hsint : (interior s).Nonempty) :
    ∃ f : StrongDual 𝕜 E, f ≠ 0 ∧ ∀ a ∈ s, RCLike.re (f a) ≤ RCLike.re (f x) :=
  RCLike.geometric_hahn_banach_of_nonempty_interior_point (𝕜 := 𝕜) hs hx hsint

end RCLike
