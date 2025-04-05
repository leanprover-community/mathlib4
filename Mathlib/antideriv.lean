import Mathlib.Analysis.Calculus.ParametricIntegral

open Set Function MeasureTheory AffineMap
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem Convex.exists_hasFDerivWithin_of_symmetric {s : Set E} (hs : Convex ℝ s)
    {f' : E → E →L[ℝ] F} {f'' : E → E →L[ℝ] E →L[ℝ] F}
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f' (f'' x) s x)
    (hf'' : ∀ x ∈ s, ∀ u ∈ tangentConeAt ℝ s x, ∀ v ∈ tangentConeAt ℝ s x,
      f'' x u v = f'' x v u) :
    ∃ f : E → F, ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  · let f : E → F := fun x ↦ ∫ t in (0)..1, f' (lineMap x a t) (x - a)
    refine ⟨f, fun x hx ↦ ?_⟩
    
    
  
