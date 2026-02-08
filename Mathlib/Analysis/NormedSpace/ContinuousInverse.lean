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
* `ContinuousLinearMap.HasBoundedRightInverse.comp`: if `f : E → F` and `g : F → G` both admit
  a continuous right inverse, so does `g.comp f`.
* `ContinuousLinearMap.HasBoundedRightInverse.of_comp`: if `f : E → F` and `g : F → G` are
  continuous linear maps such that `g.comp f : E → G` admits a continuous right inverse,
  then so does `g`.
* `ContinuousLinearMap.HasBoundedRightInverse.prodMap`: having a continuous right inverse
  is closed under taking products
* `ContinuousLinearMap.HasBoundedRightInverse.continuousLinearMap_fst`:
  `ContinuousLinearMap.fst` has a continuous right inverse; similar for `snd`
* `ContinuousLinearMap.HasBoundedRightInverse.of_surjective_of_finiteDimensional`:
  if `f : E → F` is surjective and `F` is finite-dimensional, `f` has a continuous right inverse.

## TODO

* Suppose `E` and `F` are Banach and `f : E → F` is Fredholm.
  If `f` is surjective, it has a continuous right inverse.
  If `f` is injective, it has a continuout left inverse.
* Are "split monomorphism/split injection" resp. "split epimorphism/split surjection" better terms?

-/

public section

open Function Set

variable {R : Type*} [Semiring R] {E E' F F' G : Type*}
  [TopologicalSpace E] [AddCommMonoid E] [Module R E]
  [TopologicalSpace E'] [AddCommMonoid E'] [Module R E']
  [TopologicalSpace F] [AddCommMonoid F] [Module R F]
  [TopologicalSpace F'] [AddCommMonoid F'] [Module R F']

noncomputable section

/-- A continuous linear map admits a left inverse which is a continuous linear map itself. -/
@[expose] protected def ContinuousLinearMap.HasBoundedLeftInverse (f : E →L[R] F) : Prop :=
  ∃ g : F →L[R] E, LeftInverse g f

/-- A continuous linear map admits a right inverse which is a continuous linear map itself. -/
@[expose] protected def ContinuousLinearMap.HasBoundedRightInverse (f : E →L[R] F) : Prop :=
  ∃ g : F →L[R] E, RightInverse g f

namespace ContinuousLinearMap

namespace HasBoundedLeftInverse

variable {f : E →L[R] F}

/-- Choice of left inverse for `f` -/
def leftInverse (h : f.HasBoundedLeftInverse) : F →L[R] E := Classical.choose h

lemma leftInverse_leftInverse (h : f.HasBoundedLeftInverse) : LeftInverse h.leftInverse f :=
  Classical.choose_spec h

lemma injective (h : f.HasBoundedLeftInverse) : Injective f :=
  h.leftInverse_leftInverse.injective

example (h : f.HasBoundedLeftInverse) (x : E) : h.leftInverse (f x) = x :=
  h.leftInverse_leftInverse x

lemma congr {g : E →L[R] F} (hf : f.HasBoundedLeftInverse) (hfg : g = f) :
    g.HasBoundedLeftInverse :=
  hfg ▸ hf

/-- A continuous linear equivalence has a continuous left inverse. -/
lemma _root_.ContinuousLinearEquiv.hasBoundedLeftInverse (f : E ≃L[R] F) :
    f.toContinuousLinearMap.HasBoundedLeftInverse :=
  ⟨f.symm, rightInverse_of_comp (by simp)⟩

/-- An invertible continuous linear map has a continuous left inverse. -/
lemma of_isInvertible (hf : IsInvertible f) : f.HasBoundedLeftInverse := by
  obtain ⟨e, rfl⟩ := hf
  exact e.hasBoundedLeftInverse

/-- If `f` and `g` admit continuous left inverses, so does `f × g`. -/
lemma prodMap {g : E' →L[R] F'} (hf : f.HasBoundedLeftInverse) (hg : g.HasBoundedLeftInverse) :
    (f.prodMap g).HasBoundedLeftInverse := by
  obtain ⟨finv, hfinv⟩ := hf
  obtain ⟨ginv, hginv⟩ := hg
  use finv.prodMap ginv
  simp [hfinv, hginv]

variable [TopologicalSpace G] [AddCommMonoid G] [Module R G]

lemma comp {g : F →L[R] G} (hg : g.HasBoundedLeftInverse) (hf : f.HasBoundedLeftInverse) :
    (g.comp f).HasBoundedLeftInverse := by
  obtain ⟨finv, hfinv⟩ := hf
  obtain ⟨ginv, hginv⟩ := hg
  refine ⟨finv.comp ginv, fun x ↦ ?_⟩
  simp only [coe_comp', Function.comp_apply]
  rw [hginv, hfinv]

lemma of_comp {g : F →L[R] G} (hfg : (g.comp f).HasBoundedLeftInverse) :
    f.HasBoundedLeftInverse := by
  obtain ⟨fginv, hfginv⟩ := hfg
  refine ⟨fginv.comp g, fun y ↦ ?_⟩
  simp only [coe_comp', Function.comp_apply]
  exact hfginv y

lemma compCLE_left {f₀ : F' ≃L[R] E} (hf : f.HasBoundedLeftInverse) :
    (f.comp f₀.toContinuousLinearMap).HasBoundedLeftInverse :=
  hf.comp f₀.hasBoundedLeftInverse

lemma compCLE_right {g : F ≃L[R] F'} (hf : f.HasBoundedLeftInverse) :
    (g.toContinuousLinearMap.comp f).HasBoundedLeftInverse :=
  g.hasBoundedLeftInverse.comp hf

/-- `ContinuousLinearMap.inl` has a continuous left inverse. -/
lemma continuousLinearMap_inl : (ContinuousLinearMap.inl R F G).HasBoundedLeftInverse := by
  use ContinuousLinearMap.fst _ _ _
  intro x
  simp

/-- `ContinuousLinearMap.inr` has a continuous left inverse. -/
lemma continuousLinearMap_inr : (ContinuousLinearMap.inr R F G).HasBoundedLeftInverse := by
  use ContinuousLinearMap.snd _ _ _
  intro x
  simp

section NontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]
  [T2Space F] {f : E →L[𝕜] F}

/-- If `f : E → F` is injective and `E` is finite-dimensional,
`f` has a continuous left inverse. -/
lemma of_injective_of_finiteDimensional [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
    (hf : Injective f) :
    f.HasBoundedLeftInverse := by
  -- A surjective linear map has a linear inverse. It is continuous because its domain is.
  obtain ⟨g, hg⟩ :=
    f.toLinearMap.exists_leftInverse_of_injective (f.ker_eq_bot_of_injective hf)
  exact ⟨⟨g, LinearMap.continuous_of_finiteDimensional _⟩, fun x ↦ congr($hg x)⟩

end NontriviallyNormedField

end HasBoundedLeftInverse

namespace HasBoundedRightInverse

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

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]
  [T2Space F] {f : E →L[𝕜] F}

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

end HasBoundedRightInverse

end ContinuousLinearMap

end
