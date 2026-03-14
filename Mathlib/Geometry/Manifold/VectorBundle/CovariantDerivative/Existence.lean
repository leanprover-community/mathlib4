/-
Copyright (c) 2026 Robin Gieseke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Gieseke
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Existence of covariant derivatives

This file proves that covariant derivatives (connections) exist on any smooth vector bundle
over a smooth manifold with σ-compact Hausdorff topology, using a partition of unity argument.

## Main results

* `Bundle.Trivialization.trivialCov`: the flat covariant derivative induced by a trivialization.
* `Bundle.Trivialization.isCovariantDerivativeOn_trivialCov`: the flat covariant derivative is
  indeed a covariant derivative on the base set of the trivialization.
* `CovariantDerivative.exists`: covariant derivatives always exist on smooth vector bundles
  over smooth σ-compact Hausdorff manifolds.

## Implementation notes

The flat covariant derivative decomposes as `e.symmL ∘ mfderiv (e.secToFun σ)`: it reads
a section through a trivialization via `secToFun`, takes the manifold derivative, and maps the
result back to the fiber via `symmL` (the inverse of the trivialization's linear equivalence).
-/

open Bundle NormedSpace
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle 1 F V I]

@[expose] public noncomputable section

/-! ## Flat covariant derivative in a trivialization -/

namespace Bundle.Trivialization

/-- The flat covariant derivative induced by a trivialization `e`. This reads a section `σ`
through `e` via `secToFun`, takes the manifold derivative, and maps the result back to the
fiber via `e.symmL`. Outside `e.baseSet` this is zero since `e.symmL` is zero there. -/
def trivialCov (e : Trivialization F (π F V)) [e.IsLinear ℝ]
    (σ : Π x : M, V x) (x : M) : TangentSpace I x →L[ℝ] V x :=
  e.symmL ℝ x ∘L mfderiv I 𝓘(ℝ, F) (e.secToFun σ) x

variable {F}

/-- The flat covariant derivative induced by a trivialization is a covariant derivative
on its base set. -/
theorem isCovariantDerivativeOn_trivialCov
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e] :
    IsCovariantDerivativeOn F (e.trivialCov (I := I) F) e.baseSet where
  add {σ σ'} {x} hσ hσ' hx := by
    unfold trivialCov Trivialization.secToFun
    have heq : (fun y ↦ (e ⟨y, (σ + σ') y⟩).2) =ᶠ[𝓝 x]
        ((fun y ↦ (e ⟨y, σ y⟩).2) + (fun y ↦ (e ⟨y, σ' y⟩).2)) :=
      e.secToFun_add_eventuallyEq (R := ℝ) σ σ' hx
    rw [heq.mfderiv_eq.trans (HasMFDerivAt.mfderiv
      (((e.mdifferentiableAt_section_iff I σ hx).mp hσ).hasMFDerivAt.add
        ((e.mdifferentiableAt_section_iff I σ' hx).mp hσ').hasMFDerivAt)),
      ContinuousLinearMap.comp_add]
  leibniz {σ g} {x} hσ hg hx := by
    unfold trivialCov Trivialization.secToFun
    have heq : (fun y ↦ (e ⟨y, (g • σ) y⟩).2) =ᶠ[𝓝 x]
        (g • (fun y ↦ (e ⟨y, σ y⟩).2)) :=
      e.secToFun_smul_eventuallyEq (R := ℝ) g σ hx
    rw [heq.mfderiv_eq]; ext v
    have := congr_arg (e.symmL ℝ x) (fromTangentSpace_mfderiv_smul_apply (V := F) hg
      ((e.mdifferentiableAt_section_iff I σ hx).mp hσ) v)
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
      map_add, map_smul, symmL_apply, symm_apply_apply_mk _ hx] using this

end Bundle.Trivialization

/-! ## Existence of covariant derivatives -/

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

-- TODO: `[IsManifold I ∞ M]` should be `[IsManifold I k M]` for suitable `k`: a C^k partition
-- of unity suffices. Blocked on mathlib lacking C^k partitions of unity.
/-- Every smooth vector bundle over a smooth σ-compact Hausdorff manifold admits a covariant
derivative. -/
theorem CovariantDerivative.exists : Nonempty (CovariantDerivative I F V) := by
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := I) isClosed_univ
    (fun x ↦ (trivializationAt F V x).baseSet)
    (fun x ↦ (trivializationAt F V x).open_baseSet)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, FiberBundle.mem_baseSet_trivializationAt' x⟩)
  exact ⟨⟨_, .finsum_affine_combination
    (fun i ↦ (trivializationAt F V i).isCovariantDerivativeOn_trivialCov (I := I))
    (fun x ↦ ρ.sum_eq_one (Set.mem_univ x)) ρ.locallyFinite hρ⟩⟩

end
