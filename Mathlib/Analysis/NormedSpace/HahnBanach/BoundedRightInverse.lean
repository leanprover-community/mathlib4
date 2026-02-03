/-
Copyright (c) 2026 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Analysis.Normed.Module.Complemented
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-! # Continuous linear maps with a bounded right inverse

This file defines continuous linear maps which admit a bounded right inverse.

We prove that this class of maps
* is closed under products,
* is closed under composition
* contains linear equivalences and (in the future) Fredholm operators

as well as various weakenings: for instance, an surjective linear map on a finite-dimensional space
always admits a bounded right inverse.

This concept is used to give a conceptual definition of submersions between Banach manifolds.

**TODO**. Find a better location for this file; the HahnBanach parent folder was emptied!

-/

public section

open Function Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E E' F F' G : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

noncomputable section

/-- A continuous linear map `f : E → F` **splits** iff it is injective, has closed range and
its image has a closed complement. -/
@[expose] protected def ContinuousLinearMap.HasBoundedRightInverse (f : E →L[𝕜] F) : Prop :=
  ∃ g : F →L[𝕜] E, RightInverse f g
  --Injective f ∧ IsClosed (Set.range f) ∧ Submodule.ClosedComplemented (f.range)

namespace ContinuousLinearMap.HasBoundedRightInverse

variable {f : E →L[𝕜] F}

/-- Choice of right inverse for `f` -/
def rightInverse (h : f.HasBoundedRightInverse) : F →L[𝕜] E := Classical.choose h

lemma rightInverse_rightInverse (h : f.HasBoundedRightInverse) : RightInverse f h.rightInverse :=
  Classical.choose_spec h

example (h : f.HasBoundedRightInverse) (x : E) : h.rightInverse (f x) = x :=
  h.rightInverse_rightInverse x

lemma congr {g : E →L[𝕜] F} (hf : f.HasBoundedRightInverse) (hfg : g = f) :
    g.HasBoundedRightInverse :=
  hfg ▸ hf

variable (hf : f.HasBoundedRightInverse) (x : E) in
#check hf.rightInverse_rightInverse x
/-- A continuous linear equivalence splits. -/
lemma _root_.ContinuousLinearEquiv.splits (f : E ≃L[𝕜] F) :
    f.toContinuousLinearMap.HasBoundedRightInverse :=
  ⟨f.symm, rightInverse_of_comp f.coe_symm_comp_coe⟩

/-- An invertible continuous linear map splits. -/
lemma of_isInvertible (hf : IsInvertible f) : f.HasBoundedRightInverse := by
  obtain ⟨e, rfl⟩ := hf
  exact e.splits

-- FUTURE (once mathlib has a notion of Fredholm operators):
-- If `E` and `F` are Banach and `f : E → F` is Fredholm, then `f` has a bounded right inverse.

/-- If `f` and `g` split, then so does `f × g`. -/
lemma prodMap {g : E' →L[𝕜] F'} (hf : f.HasBoundedRightInverse) (hg : g.HasBoundedRightInverse) :
    (f.prodMap g).HasBoundedRightInverse := by
  sorry -- left for Samantha

-- Th next results may or may not require additional completeness hypotheses.
lemma comp {g : F →L[𝕜] G} (hg : g.HasBoundedRightInverse) (hf : f.HasBoundedRightInverse) :
    (g.comp f).HasBoundedRightInverse := by
  sorry

lemma of_comp {g : F →L[𝕜] G}
    (hg : g.HasBoundedRightInverse) (hfg : (g.comp f).HasBoundedRightInverse) :
    f.HasBoundedRightInverse := by
  sorry

lemma of_comp_iff {g : F →L[𝕜] G} (hg : g.HasBoundedRightInverse) :
    (g.comp f).HasBoundedRightInverse ↔ f.HasBoundedRightInverse :=
  ⟨fun hfg ↦ hg.of_comp hfg, fun hf ↦ hg.comp hf⟩

lemma compCLE_left [CompleteSpace F'] {f₀ : F' ≃L[𝕜] E} (hf : f.HasBoundedRightInverse) :
    (f.comp f₀.toContinuousLinearMap).HasBoundedRightInverse :=
  hf.comp f₀.splits

lemma compCLE_right [CompleteSpace F'] {g : F ≃L[𝕜] F'} (hf : f.HasBoundedRightInverse) :
    (g.toContinuousLinearMap.comp f).HasBoundedRightInverse :=
  g.splits.comp hf

/-- If `f : E → F` is surjective and `F` is finite-dimensional, `f` has a bounded right inverse. -/
lemma of_surjective_of_finiteDimensional [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
    (hf : Surjective f) :
    f.HasBoundedRightInverse := by
  -- a surjective linear map has a linear inverse
  -- it is continuous because its domain is
  obtain ⟨g, hg⟩ :=
    f.toLinearMap.exists_rightInverse_of_surjective (f.range_eq_top_of_surjective hf)
  use ⟨g, LinearMap.continuous_of_finiteDimensional _⟩
  intro x; simp
  sorry -- hg seems to be going the wrong way...

end ContinuousLinearMap.HasBoundedRightInverse

end
