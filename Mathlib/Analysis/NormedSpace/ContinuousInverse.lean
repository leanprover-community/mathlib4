/-
Copyright (c) 2026 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Analysis.Normed.Module.Complemented
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-! # Continuous linear maps with a continuous left/right inverse

This file defines continuous linear maps which admit a continuous left/right inverse.

We prove that both of these classes of maps are closed under products, composition and contain
linear equivalences, and a sufficient criterion in finite dimension: a surjective linear map on a
finite-dimensional space always admits a continuous right inverse; an injective linear map on a
finite-dimensional space always admits a continuous left inverse.

This concept is used to give an equivalent definition of immersions and submersions of manifolds.

## Main definitions and results

* `ContinuousLinearMap.HasBoundedRightInverse`: a continuous linear map admits a right inverse
  which is a continuous linear map itself
* `ContinuousLinearEquiv.hasBoundedRightInverse`: a continuous linear equivalence
  admits a continuous right inverse
* `ContinuousLinearEquiv.HasBoundedRightInverse.comp`: if `f : E → F` and `g : F → G` both admit
  a continuous right inverse, so does `g.comp f`.
* `ContinuousLinearEquiv.HasBoundedRightInverse.of_comp`: if `f : E → F` and `g : F → G` are
  continuous linear maps such that `g.comp f : E → G` admits a continuous right inverse,
  then so does `g`.
* `ContinuousLinearMap.HasBoundedRightInverse.continuousLinearMap_fst`:
  `ContinuousLinearMap.fst` has a continuous right inverse; similar for `snd`
* `ContinuousLinearMap.HasBoundedRightInverse.of_surjective_of_finiteDimensional`:
  if `f : E → F` is surjective and `F` is finite-dimensional, `f` has a continuous right inverse.

## TODO
* `ContinuousLinearEquiv.HasBoundedRightInverse.prodMap`: having a continuous right inverse
  is closed under taking products
* If `E` and `F` are Banach and `f : E → F` is surject and Fredholm,
  `f` has a continuous right inverse.
* is "split epimorphism/split surjection" a better term?

-/

public section

open Function Set

variable {R : Type*} [Semiring R] {E E' F F' G : Type*}
  [TopologicalSpace E] [AddCommMonoid E] [Module R E]
  [TopologicalSpace E'] [AddCommMonoid E'] [Module R E']
  [TopologicalSpace F] [AddCommMonoid F] [Module R F]
  [TopologicalSpace F'] [AddCommMonoid F'] [Module R F']

noncomputable section

/-- A continuous linear map admits a right inverse which is a continuous linear map itself. -/
@[expose] protected def ContinuousLinearMap.HasBoundedRightInverse (f : E →L[R] F) : Prop :=
  ∃ g : F →L[R] E, RightInverse g f

namespace ContinuousLinearMap.HasBoundedRightInverse

variable {f : E →L[R] F}

/-- Choice of right inverse for `f` -/
def rightInverse (h : f.HasBoundedRightInverse) : F →L[R] E := Classical.choose h

lemma rightInverse_rightInverse (h : f.HasBoundedRightInverse) : RightInverse h.rightInverse f :=
  Classical.choose_spec h

lemma surjective (h : f.HasBoundedRightInverse) : Surjective f :=
  h.rightInverse_rightInverse.surjective

example (h : f.HasBoundedRightInverse) (x : F) : f (h.rightInverse x) = x :=
  h.rightInverse_rightInverse x

lemma congr {g : E →L[R] F} (hf : f.HasBoundedRightInverse) (hfg : g = f) :
    g.HasBoundedRightInverse :=
  hfg ▸ hf

/-- A continuous linear equivalence has a continuous right inverse. -/
lemma _root_.ContinuousLinearEquiv.hasBoundedRightInverse (f : E ≃L[R] F) :
    f.toContinuousLinearMap.HasBoundedRightInverse :=
  ⟨f.symm, rightInverse_of_comp (by simp)⟩

/-- An invertible continuous linear map splits. -/
lemma of_isInvertible (hf : IsInvertible f) : f.HasBoundedRightInverse := by
  obtain ⟨e, rfl⟩ := hf
  exact e.hasBoundedRightInverse

/-- If `f` and `g` split, then so does `f × g`. -/
lemma prodMap {g : E' →L[R] F'} (hf : f.HasBoundedRightInverse) (hg : g.HasBoundedRightInverse) :
    (f.prodMap g).HasBoundedRightInverse := by
  obtain ⟨finv, hfinv⟩ := hf
  obtain ⟨ginv, hginv⟩ := hg
  use finv.prodMap ginv
  simp [hfinv, hginv]

variable [TopologicalSpace G] [AddCommMonoid G] [Module R G]

lemma comp {g : F →L[R] G} (hg : g.HasBoundedRightInverse) (hf : f.HasBoundedRightInverse) :
    (g.comp f).HasBoundedRightInverse := by
  obtain ⟨finv, hfinv⟩ := hf
  obtain ⟨ginv, hginv⟩ := hg
  refine ⟨finv.comp ginv, fun x ↦ ?_⟩
  simp only [coe_comp', Function.comp_apply]
  rw [hfinv, hginv]

lemma of_comp {g : F →L[R] G} (hfg : (g.comp f).HasBoundedRightInverse) :
    g.HasBoundedRightInverse := by
  obtain ⟨fginv, hfginv⟩ := hfg
  exact ⟨f.comp fginv, fun y ↦ by simpa using hfginv y⟩

lemma compCLE_left {f₀ : F' ≃L[R] E} (hf : f.HasBoundedRightInverse) :
    (f.comp f₀.toContinuousLinearMap).HasBoundedRightInverse :=
  hf.comp f₀.hasBoundedRightInverse

lemma compCLE_right {g : F ≃L[R] F'} (hf : f.HasBoundedRightInverse) :
    (g.toContinuousLinearMap.comp f).HasBoundedRightInverse :=
  g.hasBoundedRightInverse.comp hf

/-- `ContinuousLinearMap.fst` has a continuous right inverse. -/
lemma continuousLinearMap_fst : (ContinuousLinearMap.fst R F G).HasBoundedRightInverse := by
  use (ContinuousLinearMap.id _ _).prod 0
  intro x
  simp

/-- `ContinuousLinearMap.snd` has a continuous right inverse. -/
lemma continuousLinearMap_snd : (ContinuousLinearMap.snd R F G).HasBoundedRightInverse := by
  use ContinuousLinearMap.prod 0 (.id R G)
  intro x
  simp

section NontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E E' F F' G : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {f : E →L[𝕜] F}

/-- If `f : E → F` is surjective and `F` is finite-dimensional,
`f` has a continuous right inverse. -/
lemma of_surjective_of_finiteDimensional [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
    (hf : Surjective f) :
    f.HasBoundedRightInverse := by
  -- A surjective linear map has a linear inverse. It is continuous because its domain is.
  obtain ⟨g, hg⟩ :=
    f.toLinearMap.exists_rightInverse_of_surjective (f.range_eq_top_of_surjective hf)
  exact ⟨⟨g, g.continuous_of_finiteDimensional⟩, fun x ↦ congr($hg x)⟩

end NontriviallyNormedField

end ContinuousLinearMap.HasBoundedRightInverse

end
