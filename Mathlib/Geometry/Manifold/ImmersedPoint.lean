/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Analysis.Normed.Module.ContinuousInverse

/-! # Immersed points of differentiable maps

Given a map `f : M → N` between manifolds, we call `x` and *immersed point* of `f` if and only if
the `mfderiv` of `f` at `x` *splits*, i.e. admits a continuous left inverse. (If `M` is
finite-dimensional, this is equivalent to injectivity of the the `mfderiv`.)

A future PR will show that `x` is an immersed point of `x` if and only if `f` is an immersion
at `x`: the composition property of immersed can be used to prove that immersions compose.


## Main definitions and results

* `IsImmersedPoint`: `x` is an *immersed point* of `f` iff `mfderiv I J f x` has a continuous left
  inverse
* `IsLocalDiffeomorphAt.isImmersedPoint`: if `f` is a local diffeomorphism at `x`, then `x` is an
  immersed point of `f`
* `IsImmersedPoint.comp`: if `x` is an immersed point of `f` and `f x` is an immersed point of `g`,
  then `x` is an immersed point of `g ∘ f`
* `IsImmersedPoint.of_comp`: if `g ∘ f` has immersed point `x`, then (assuming `f` and `g` are
  differentiable at `x` resp. `f x`), then `x` also an immersed point of `f`.
* `IsImmersedPoint.of_injective_of_finiteDimensional`: if `f : M → N` has injective `mfderiv` at `x`
  and `N` is finite-dimensional, then `x` is an immersed point of `f`.

## TODO
* `IsImmersedPoint.prodMap`: if `x` is an immersed point of `f` and `y` is an immersed point of `g`,
  then `(x, y)` is an immersed point of `f × g`.

-/

open Function Set Topology

public section

universe u
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F F' G : Type*} {E' : Type u}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {G : Type*} [TopologicalSpace G] {G' : Type*} [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {J : ModelWithCorners 𝕜 F G} {J' : ModelWithCorners 𝕜 F G'}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  {n : WithTop ℕ∞} [IsManifold I n M] [IsManifold I' n M']
variable {f : M → M'} {x : M} {n : WithTop ℕ∞}

-- TODO: move to the right place!
/-- If `f : E → F` has injective differential at `x`, it is differentiable at `x`. -/
lemma differentiableAt_of_fderiv_injective {f : E → F} {x : E} (hf : Injective (fderiv 𝕜 f x)) :
    DifferentiableAt 𝕜 f x := by
  replace hf : LinearMap.ker (fderiv 𝕜 f x).toLinearMap = ⊥ := by
    rw [LinearMap.ker_eq_bot]; exact hf
  by_cases h: Subsingleton E
  · exact differentiable_of_subsingleton.differentiableAt
  · by_contra h'
    have : (⊥ : Submodule 𝕜 E) = ⊤ := by
      simp [fderiv_zero_of_not_differentiableAt h', ← hf]
    have : Subsingleton (Submodule 𝕜 E) := subsingleton_of_bot_eq_top this
    simp_all only [Submodule.subsingleton_iff]

-- TODO: move to e.g. ContMDiff.Basic
/-- If `f : M → M'` has injective differential at `x`, it is `MDifferentiable` at `x`. -/
lemma mdifferentiableAt_of_mfderiv_injective {f : M → M'} (hf : Injective (mfderiv I I' f x)) :
    MDifferentiableAt I I' f x := by
  replace hf : LinearMap.ker (mfderiv I I' f x).toLinearMap = ⊥ := by
    rw [LinearMap.ker_eq_bot]; exact hf
  by_cases h: Subsingleton E
  · exact mdifferentiable_of_subsingleton.mdifferentiableAt
  · by_contra h'
    have : (⊥ : Submodule 𝕜 (TangentSpace I x)) = ⊤ := by
      simp [mfderiv_zero_of_not_mdifferentiableAt h', ← hf]
    have : Subsingleton (Submodule 𝕜 E) := subsingleton_of_bot_eq_top this
    simp_all only [Submodule.subsingleton_iff]

variable (I I' f x) in
/-- We say a map `f : M → M` splits at `x` if `mfderiv I I' f x` splits,
i.e. has a continuous left inverse. -/
def IsImmersedPoint (f : M → M') (x : M) : Prop :=
  mfderiv I I' f x |>.HasLeftInverse

lemma isImmersedPoint_iff : IsImmersedPoint I I' f x ↔ (mfderiv I I' f x).HasLeftInverse := by rfl

namespace IsImmersedPoint

variable {f g : M → M'} {x : M}

open IsManifold in
lemma mfderiv_injective (hf : IsImmersedPoint I I' f x) : Injective (mfderiv I I' f x) :=
  hf.injective

lemma mdifferentiableAt (hf : IsImmersedPoint I I' f x) : MDifferentiableAt I I' f x :=
  mdifferentiableAt_of_mfderiv_injective hf.mfderiv_injective

lemma continuousAt (hf : IsImmersedPoint I I' f x) : ContinuousAt f x :=
  hf.mdifferentiableAt.continuousAt

lemma congr (hf : IsImmersedPoint I I' f x) (hfg : g =ᶠ[𝓝 x] f) : IsImmersedPoint I I' g x := by
  rwa [isImmersedPoint_iff, hfg.mfderiv_eq]

-- This proof requires further lemmas relating the tangent bundles of `M`, `M'` and `M × M'`.
proof_wanted prodMap {y : N} (hf : IsImmersedPoint I I' f x) {g : N → N'}
    (hg : IsImmersedPoint J J' g y) : IsImmersedPoint (I.prod J) (I'.prod J') (Prod.map f g) (x, y)

lemma of_mfderiv_isInvertible (hf : (mfderiv I I' f x).IsInvertible) :
    IsImmersedPoint I I' f x := by
  rw [isImmersedPoint_iff]
  exact ContinuousLinearMap.HasLeftInverse.of_isInvertible hf

/-- If `x` is an immersed point of `f`, then `f` is a local diffeomorphism at `x`. -/
lemma _root_.IsLocalDiffeomorphAt.isImmersedPoint
    (hf : IsLocalDiffeomorphAt I I' n f x) (hn : n ≠ 0) : IsImmersedPoint I I' f x :=
  of_mfderiv_isInvertible (hf.isInvertible_mfderiv hn)

/-- If `x` is an immersed point of `x` and `f x` is an immersed point of `g`, then `x` is an
immersed point of `g ∘ f`. -/
lemma comp {g : M' → N} (hg : IsImmersedPoint I' J g (f x)) (hf : IsImmersedPoint I I' f x) :
    IsImmersedPoint I J (g ∘ f) x := by
  rw [isImmersedPoint_iff, mfderiv_comp x hg.mdifferentiableAt hf.mdifferentiableAt]
  rw [isImmersedPoint_iff] at hf hg
  exact hg.comp hf

lemma of_comp {g : M' → N} (hf : MDifferentiableAt I I' f x) (hg : MDifferentiableAt I' J g (f x))
    (hfg : IsImmersedPoint I J (g ∘ f) x) : IsImmersedPoint I I' f x := by
  rw [isImmersedPoint_iff, mfderiv_comp x hg hf] at hfg
  exact ContinuousLinearMap.HasLeftInverse.of_comp hfg

lemma comp_isLocalDiffeomorphAt_left (hf : IsImmersedPoint I I' f x)
    {f₀ : N → M} {y : N} (hxy : f₀ y = x) (hf₀ : IsLocalDiffeomorphAt J I n f₀ y) (hn : n ≠ 0) :
    IsImmersedPoint J I' (f ∘ f₀) y :=
  (hxy ▸ hf).comp (hf₀.isImmersedPoint hn)

lemma comp_isLocalDiffeomorphAt_left_iff {f₀ : N → M} {y : N} (hxy : f₀ y = x)
    (hf₀ : IsLocalDiffeomorphAt J I n f₀ y) (hn : n ≠ 0) :
    IsImmersedPoint I I' f x ↔ IsImmersedPoint J I' (f ∘ f₀) y := by
  refine ⟨fun hf ↦ hf.comp_isLocalDiffeomorphAt_left hxy hf₀ hn,
    fun h ↦ ?_⟩
  have := (hxy ▸ hf₀.localInverse_left_inv hf₀.localInverse_mem_target)
  apply (h.comp_isLocalDiffeomorphAt_left this
    (hxy ▸ hf₀.localInverse_isLocalDiffeomorphAt) hn).congr
  exact (hxy ▸ hf₀.localInverse_eventuallyEq_right.symm).fun_comp f

lemma comp_isLocalDiffeomorphAt_right (hf : IsImmersedPoint I I' f x)
    {g : M' → N} (hg : IsLocalDiffeomorphAt I' J n g (f x)) (hn : n ≠ 0) :
    IsImmersedPoint I J (g ∘ f) x :=
  (hg.isImmersedPoint hn).comp hf

lemma comp_isLocalDiffeomorphAt_right_iff (hf : ContinuousAt f x)
    {g : M' → N} (hg : IsLocalDiffeomorphAt I' J n g (f x)) (hn : n ≠ 0) :
    IsImmersedPoint I I' f x ↔  IsImmersedPoint I J (g ∘ f) x := by
  refine ⟨fun hf ↦ hf.comp_isLocalDiffeomorphAt_right hg hn, fun h ↦ ?_⟩
  apply (h.comp_isLocalDiffeomorphAt_right hg.localInverse_isLocalDiffeomorphAt hn).congr
  symm
  exact Filter.eventuallyEq_of_mem (hf hg.localInverse_eventuallyEq_left) (by intro; simp)

/-- If `mfderiv I J f x` is injective and `N` is finite-dimensional,
`x` is an immersed point of `f`. -/
lemma of_injective_of_finiteDimensional [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E']
    (hf' : Injective (mfderiv I I' f x)) : IsImmersedPoint I I' f x := by
  have : FiniteDimensional 𝕜 (TangentSpace I' (f x)) := inferInstanceAs (FiniteDimensional 𝕜 E')
  exact ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hf'

end IsImmersedPoint

end
