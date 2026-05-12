/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WeakDual
public import Mathlib.Analysis.RCLike.Extend
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Hahn-Banach theorem for locally convex spaces

In this file we prove the analytic Hahn-Banach theorem for locally convex spaces. For any continuous
linear function on a subspace, we can extend it to a function on the entire space.

We prove
* `Real.exists_extension`: Hahn-Banach theorem for continuous linear functions on locally convex
  spaces over `ℝ`.
* `exists_extension`: Hahn-Banach theorem for continuous linear functions on locally convex spaces
  over `ℝ` or `ℂ`.

-/

public section

open scoped ComplexOrder
open Module Topology RCLike

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
variable {F : Type*} [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F]

/-- **Hahn-Banach theorem** for linear functions dominated by a seminorm on locally convex spaces
over `ℝ`. -/
theorem LinearMap.exists_real_extension [Module ℝ E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] (S : Subspace ℝ E) (f : S →ₗ[ℝ] ℝ) {p : Seminorm ℝ E}
    (hp_cont : Continuous p) (hp : ∀ x, f x ≤ p x) :
    ∃ g : StrongDual ℝ E, (∀ x : S, g x = f x) ∧ ∀ x, g x ≤ p x := by
  obtain ⟨g, hg, hl⟩ := by
    refine exists_extension_of_le_sublinear ⟨S, f⟩ p (fun _ hc _ => ?_) ?_ hp
    · simp [map_smul_eq_mul, abs_of_nonneg hc.le]
    · exact fun x y => map_add_le_add p x y
  exact ⟨⟨g, (PolynormableSpace.withSeminorms ℝ E).continuous_real_rng g
    ⟨{⟨p, hp_cont⟩}, 1, fun x ↦ by simpa using hl x⟩⟩, hg, hl⟩

/-- **Hahn-Banach theorem** for continuous linear functions on locally convex spaces over `ℝ`. -/
theorem StrongDual.exists_real_extension [Module ℝ E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    (S : Subspace ℝ E) (f : StrongDual ℝ S) :
    ∃ g : StrongDual ℝ E, ∀ x : S, g x = f x := by
  have : PolynormableSpace ℝ E := LocallyConvexSpace.toPolynormableSpace
  obtain ⟨q, hq_cont, hq⟩ := PolynormableSpace.exists_continuous_seminorm_le (f := S.subtype)
    (p := f.toSeminorm) f.continuous.norm IsInducing.subtypeVal
  obtain ⟨g, hg, hl⟩ := by
    refine f.toLinearMap.exists_real_extension S hq_cont fun x => ?_
    calc
      _ ≤ f.toSeminorm x := by simp [le_abs_self]
      _ ≤ q x := hq x
  exact ⟨g, hg⟩

variable [Module 𝕜 E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace 𝕜 E]

/-- **Hahn-Banach theorem** for continuous linear functions on locally convex spaces over an
`RCLike` field. -/
theorem StrongDual.exists_extension (S : Submodule 𝕜 E) (f : StrongDual 𝕜 S) :
    ∃ g : StrongDual 𝕜 E, ∀ x : S, g x = f x := by
  letI : Module ℝ E := .restrictScalars ℝ 𝕜 E
  letI : IsScalarTower ℝ 𝕜 E := .restrictScalars _ _ _
  letI : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  letI : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms 𝕜 E).toLocallyConvexSpace
  let fr := reCLM.comp (f.restrictScalars ℝ)
  obtain ⟨g, (hg : ∀ x : S, g x = fr x)⟩ := exists_real_extension (S.restrictScalars ℝ) fr
  refine ⟨g.extendRCLike, fun x ↦ ?_⟩
  rw [g.extendRCLike_apply, ← Submodule.coe_smul, hg, hg]
  simp [fr, RCLike.algebraMap_eq_ofReal, mul_comm I]

variable [Module 𝕜 F] [ContinuousSMul 𝕜 F] [T2Space F]

/-- Corollary of the locally convex **Hahn-Banach theorem**: if `f : S → F` is a continuous
linear map with finite-dimensional range, then `f` extends to a continuous linear map on the whole
space. -/
lemma ContinuousLinearMap.exist_extension_of_finiteDimensional_range {S : Submodule 𝕜 E}
    (f : S →L[𝕜] F) [FiniteDimensional 𝕜 f.range] :
    ∃ g : E →L[𝕜] F, f = g.comp S.subtypeL := by
  let b := Module.finBasis 𝕜 f.range
  let e := b.equivFunL
  let fi := fun i ↦ (LinearMap.toContinuousLinearMap (b.coord i)).comp
    (f.codRestrict _ <| LinearMap.mem_range_self _)
  choose gi hgf using fun i ↦ StrongDual.exists_extension S (fi i)
  use f.range.subtypeL.comp <| e.symm.toContinuousLinearMap.comp (.pi gi)
  ext x
  simp [fi, e, hgf]

/-- A finite-dimensional submodule over `ℝ` or `ℂ` is `Submodule.ClosedComplemented`. -/
lemma Submodule.ClosedComplemented.of_finiteDimensional [LocallyConvexSpace 𝕜 F] (S : Submodule 𝕜 F)
    [FiniteDimensional 𝕜 S] : S.ClosedComplemented := by
  let ⟨g, hg⟩ := (ContinuousLinearMap.id 𝕜 S).exist_extension_of_finiteDimensional_range
  exact ⟨g, DFunLike.congr_fun hg.symm⟩
