/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.Notation
public import Mathlib.Analysis.Normed.Module.ContinuousInverse

/-! # Immersed points of differentiable maps

Given a map `f : M → N` between manifolds, we call `x` and *immersed point* of `f` if and only if
the `mfderiv` of `f` at `x` *splits*, i.e. admits a continuous left inverse. (If `M` is
finite-dimensional, this is equivalent to injectivity of the `mfderiv`.)
Under (relatively mild) conditions, this is equivalent to being an immersion at `x` (which is why we
call this notation `IsDiffImmersionAt f x`: "f is an immersion at the level of differentials").
This will be shown in a future PR.

`IsDiffImmersionAt` always behaves nicely under composition: future PRs will use the above
equivalence to prove that immersions compose (in nice situations).

## Main definitions and results

* `IsDiffImmersionAt`: `x` is an *immersed point* of `f` iff `mfderiv I J f x` has a continuous left
  inverse
* `IsLocalDiffeomorphAt.isDiffImmersionAt`: if `f` is a local diffeomorphism at `x`, then `x` is an
  immersed point of `f`
* `IsDiffImmersionAt.comp`: if `x` is an immersed point of `f` and `f x` is an immersed point of `g`,
  then `x` is an immersed point of `g ∘ f`
* `IsDiffImmersionAt.of_comp`: if `g ∘ f` has immersed point `x`, then (assuming `f` and `g` are
  differentiable at `x` resp. `f x`), then `x` also an immersed point of `f`.
* `IsDiffImmersionAt.of_injective_of_finiteDimensional`: if `f : M → N` has injective `mfderiv` at `x`
  and `N` is finite-dimensional, then `x` is an immersed point of `f`.

## TODO
* `IsDiffImmersionAt.prodMap`: if `x` is an immersed point of `f` and `y` is an immersed point of `g`,
  then `(x, y)` is an immersed point of `f × g`.

-/

open Function Topology
open scoped Manifold

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

variable (I I' f x) in
/-- We say a map `f : M → M` splits at `x` if `mfderiv I I' f x` splits,
i.e. has a continuous left inverse. -/
def IsDiffImmersionAt (f : M → M') (x : M) : Prop := mfderiv% f x |>.HasLeftInverse

lemma isDiffImmersionAt_iff : IsDiffImmersionAt I I' f x ↔ (mfderiv% f x).HasLeftInverse := by rfl

namespace IsDiffImmersionAt

variable {f g : M → M'} {x : M}

lemma mfderiv_injective (hf : IsDiffImmersionAt I I' f x) : Injective (mfderiv% f x) :=
  hf.injective

lemma mdifferentiableAt (hf : IsDiffImmersionAt I I' f x) : MDiffAt f x :=
  mdifferentiableAt_of_mfderiv_injective hf.mfderiv_injective

lemma continuousAt (hf : IsDiffImmersionAt I I' f x) : ContinuousAt f x :=
  hf.mdifferentiableAt.continuousAt

lemma congr (hf : IsDiffImmersionAt I I' f x) (hfg : g =ᶠ[𝓝 x] f) : IsDiffImmersionAt I I' g x := by
  rwa [isDiffImmersionAt_iff, hfg.mfderiv_eq]

-- This proof requires further lemmas relating the tangent bundles of `M`, `M'` and `M × M'`.
proof_wanted prodMap {y : N} (hf : IsDiffImmersionAt I I' f x) {g : N → N'}
    (hg : IsDiffImmersionAt J J' g y) :
    IsDiffImmersionAt (I.prod J) (I'.prod J') (Prod.map f g) (x, y)

lemma of_mfderiv_isInvertible (hf : (mfderiv% f x).IsInvertible) : IsDiffImmersionAt I I' f x := by
  rw [isDiffImmersionAt_iff]
  exact ContinuousLinearMap.HasLeftInverse.of_isInvertible hf

/-- If `f` is a local diffeomorphism at `x`, then `x` is an immersed point of `f`. -/
lemma _root_.IsLocalDiffeomorphAt.isDiffImmersionAt
    (hf : IsLocalDiffeomorphAt I I' n f x) (hn : n ≠ 0) : IsDiffImmersionAt I I' f x :=
  of_mfderiv_isInvertible (hf.isInvertible_mfderiv hn)

/-- Every point is an immersed point of a continuous linear equivalence. -/
lemma _root_.ContinuousLinearEquiv.isDiffImmersionAt (f : E ≃L[𝕜] F) {x : E} :
    IsDiffImmersionAt 𝓘(𝕜, E) 𝓘(𝕜, F) f x :=
  (f.toDiffeomorph.isLocalDiffeomorph _).isDiffImmersionAt (by simp)

/-- If `x` is an immersed point of `x` and `f x` is an immersed point of `g`, then `x` is an
immersed point of `g ∘ f`. -/
lemma comp {g : M' → N} (hg : IsDiffImmersionAt I' J g (f x)) (hf : IsDiffImmersionAt I I' f x) :
    IsDiffImmersionAt I J (g ∘ f) x := by
  rw [isDiffImmersionAt_iff, mfderiv_comp x hg.mdifferentiableAt hf.mdifferentiableAt]
  rw [isDiffImmersionAt_iff] at hf hg
  exact hg.comp hf

/-- If `x` is an immersed point of `g ∘ f`, then `x` is an immersed point of `x`
provided `f` and `g` are differentiable at `x` and `f x`, respectively. -/
lemma of_comp {g : M' → N} (hf : MDiffAt f x) (hg : MDiffAt g (f x))
    (hfg : IsDiffImmersionAt I J (g ∘ f) x) : IsDiffImmersionAt I I' f x := by
  rw [isDiffImmersionAt_iff, mfderiv_comp x hg hf] at hfg
  exact ContinuousLinearMap.HasLeftInverse.of_comp hfg

lemma comp_isInvertible_mfderiv_left (hf : IsDiffImmersionAt I I' f x)
    {f₀ : N → M} {y : N} (hxy : f₀ y = x) (hf₀ : (mfderiv% f₀ y) |>.IsInvertible) :
    IsDiffImmersionAt J I' (f ∘ f₀) y :=
  (hxy ▸ hf).comp (.of_mfderiv_isInvertible hf₀)

lemma comp_isLocalDiffeomorphAt_left (hf : IsDiffImmersionAt I I' f x)
    {f₀ : N → M} {y : N} (hxy : f₀ y = x) (hf₀ : IsLocalDiffeomorphAt J I n f₀ y) (hn : n ≠ 0) :
    IsDiffImmersionAt J I' (f ∘ f₀) y :=
  (hxy ▸ hf).comp (hf₀.isDiffImmersionAt hn)

lemma comp_isLocalDiffeomorphAt_left_iff {f₀ : N → M} {y : N} (hxy : f₀ y = x)
    (hf₀ : IsLocalDiffeomorphAt J I n f₀ y) (hn : n ≠ 0) :
    IsDiffImmersionAt I I' f x ↔ IsDiffImmersionAt J I' (f ∘ f₀) y := by
  refine ⟨fun hf ↦ hf.comp_isLocalDiffeomorphAt_left hxy hf₀ hn,
    fun h ↦ ?_⟩
  have := (hxy ▸ hf₀.localInverse_left_inv hf₀.localInverse_mem_target)
  apply (h.comp_isLocalDiffeomorphAt_left this
    (hxy ▸ hf₀.localInverse_isLocalDiffeomorphAt) hn).congr
  exact (hxy ▸ hf₀.localInverse_eventuallyEq_right.symm).fun_comp f

lemma comp_isInvertible_mfderiv_right (hf : IsDiffImmersionAt I I' f x)
    {g : M' → N} (hg : (mfderiv% g (f x)).IsInvertible) :
    IsDiffImmersionAt I J (g ∘ f) x :=
  (IsDiffImmersionAt.of_mfderiv_isInvertible hg).comp hf

lemma comp_isLocalDiffeomorphAt_right (hf : IsDiffImmersionAt I I' f x)
    {g : M' → N} (hg : IsLocalDiffeomorphAt I' J n g (f x)) (hn : n ≠ 0) :
    IsDiffImmersionAt I J (g ∘ f) x :=
  (hg.isDiffImmersionAt hn).comp hf

lemma comp_isLocalDiffeomorphAt_right_iff (hf : ContinuousAt f x)
    {g : M' → N} (hg : IsLocalDiffeomorphAt I' J n g (f x)) (hn : n ≠ 0) :
    IsDiffImmersionAt I I' f x ↔  IsDiffImmersionAt I J (g ∘ f) x := by
  refine ⟨fun hf ↦ hf.comp_isLocalDiffeomorphAt_right hg hn, fun h ↦ ?_⟩
  apply (h.comp_isLocalDiffeomorphAt_right hg.localInverse_isLocalDiffeomorphAt hn).congr
  symm
  exact Filter.eventuallyEq_of_mem (hf hg.localInverse_eventuallyEq_left) (by intro; simp)

/-- If `mfderiv I J f x` is injective and `N` is finite-dimensional,
`x` is an immersed point of `f`. -/
lemma of_injective_of_finiteDimensional [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E']
    (hf' : Injective (mfderiv% f x)) : IsDiffImmersionAt I I' f x := by
  have : FiniteDimensional 𝕜 (TangentSpace I' (f x)) := inferInstanceAs (FiniteDimensional 𝕜 E')
  have : T2Space (TangentSpace% (f x)) := inferInstanceAs (T2Space E')
  exact ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hf'

end IsDiffImmersionAt

end
