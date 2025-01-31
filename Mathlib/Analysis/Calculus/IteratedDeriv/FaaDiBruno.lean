import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

open Function Set
open scoped ContDiff

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section scomp

variable {g : E → F} {f : 𝕜 → E} {s : Set 𝕜} {t : Set E} {x : 𝕜} {n : WithTop ℕ∞} {i : ℕ}

theorem iteratedDerivWithin_scomp_eq_sum_orderedFinpartition
    (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (hst : MapsTo f s t) (hi : i ≤ n) :
    iteratedDerivWithin i (g ∘ f) s x =
      ∑ c : OrderedFinpartition i, iteratedFDerivWithin 𝕜 c.length g t (f x) fun j ↦
        iteratedDerivWithin (c.partSize j) f s x := by
  simp only [iteratedDerivWithin, iteratedFDerivWithin_comp hg hf ht hs hx hst hi]
  simp [FormalMultilinearSeries.taylorComp, ftaylorSeriesWithin,
    OrderedFinpartition.applyOrderedFinpartition_apply, comp_def]

theorem iteratedDerivWithin_scomp_two
    (hg : ContDiffWithinAt 𝕜 2 g t (f x)) (hf : ContDiffWithinAt 𝕜 2 f s x)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (hst : MapsTo f s t) :
    iteratedDerivWithin 2 (g ∘ f) s x =
      iteratedFDerivWithin 𝕜 2 g t (f x) (fun _ ↦ derivWithin f s x) +
      fderivWithin 𝕜 g t (f x) (iteratedDerivWithin 2 f s x) := by
  rw [iteratedDerivWithin_scomp_eq_sum_orderedFinpartition hg hf ht hs hx hst le_rfl]
  -- TODO: add `Fintype.sum_sigma`
  simp only [← (OrderedFinpartition.extendEquiv 1).sum_comp, ← Finset.univ_sigma_univ,
    Finset.sum_sigma, Fintype.sum_unique]
  simp [OrderedFinpartition.extendEquiv, OrderedFinpartition.extend,
    OrderedFinpartition.extendLeft, OrderedFinpartition.extendMiddle, ht _ (hst hx),
    OrderedFinpartition.atomic, ← Matrix.vecCons_const (n := 1)]
  

end scomp
