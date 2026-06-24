/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WeakDual
public import Mathlib.Analysis.Normed.Module.RCLike.Extend
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Hahn-Banach theorem for polynormable spaces

In this file, we prove the analytic Hahn-Banach theorem for polynormable spaces over a field
satisfying `IsRCLikeNormedField`. For any continuous linear functional on a subspace, we can extend
it to the entire space. Note that we cannot use `LocallyConvexSpace` because an
`IsRCLikeNormedField` has no order structure.

We prove
* `Module.Dual.exists_continuous_extension_of_le_seminorm`: Hahn-Banach theorem for linear
  functionals dominated by a continuous seminorm on polynormable spaces over a field satisfying
  `IsRCLikeNormedField`.
* `StrongDual.exists_extension`: Hahn-Banach theorem for continuous linear functionals on
  polynormable spaces over fields satisfying `IsRCLikeNormedField`.

-/

public section

open Module Topology RCLike

open scoped ComplexConjugate

variable {𝕜 E : Type*} [AddCommGroup E]

theorem Module.Dual.exists_extension_of_le_seminorm_real [Module ℝ E]
    (S : Subspace ℝ E) (f : Dual ℝ S)
    {p : Seminorm ℝ E} (hp : ∀ x, f x ≤ p x) :
    ∃ g : Dual ℝ E, (∀ x : S, g x = f x) ∧ ∀ x, |g x| ≤ p x := by
  obtain ⟨g, hg, hl⟩ := by
    refine exists_extension_of_le_sublinear ⟨S, f⟩ p (fun _ hc _ => ?_) ?_ hp
    · simp [map_smul_eq_mul, abs_of_nonneg hc.le]
    · exact fun x y => map_add_le_add p x y
  exact ⟨g, hg, p.abs_le_of_le hl⟩

variable [NormedField 𝕜] [IsRCLikeNormedField 𝕜]

theorem Module.Dual.exists_extension_of_le_seminorm [Module 𝕜 E] (S : Submodule 𝕜 E) (f : Dual 𝕜 S)
    {p : Seminorm 𝕜 E} (hp : ∀ x, ‖f x‖ ≤ p x) :
    ∃ g : Dual 𝕜 E, (∀ x : S, g x = f x) ∧ ∀ x, ‖g x‖ ≤ p x := by
  letI : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  letI : Module ℝ E := .restrictScalars ℝ 𝕜 E
  letI : IsScalarTower ℝ 𝕜 E := .restrictScalars _ _ _
  let fr : Dual ℝ S := reLm.comp (f.restrictScalars ℝ)
  obtain ⟨g, (hg : ∀ x : S, g x = fr x), hgp⟩ :=
    fr.exists_extension_of_le_seminorm_real (S.restrictScalars ℝ) (p := p.restrictScalars ℝ)
      fun x ↦ (re_le_norm (f x)).trans (hp x)
  refine ⟨g.extendRCLike, fun x ↦ ?_, fun x ↦ ?_⟩
  · rw [g.extendRCLike_apply, ← Submodule.coe_smul, hg, hg]
    simp [fr, mul_comm I]
  · apply norm_extendRCLike_le_seminorm
    exact hgp

variable [TopologicalSpace E]

/-- **Hahn-Banach theorem** for linear functionals dominated by a continuous seminorm on
polynormable spaces over `ℝ`. -/
theorem Module.Dual.exists_continuous_extension_of_le_seminorm_real
    [Module ℝ E] [ContinuousSMul ℝ E] [PolynormableSpace ℝ E] (S : Subspace ℝ E) (f : Dual ℝ S)
    {p : Seminorm ℝ E} (hp_cont : Continuous p) (hp : ∀ x, f x ≤ p x) :
    ∃ g : StrongDual ℝ E, (∀ x : S, g x = f x) ∧ ∀ x, |g x| ≤ p x := by
  obtain ⟨g, hg, hl⟩ := f.exists_extension_of_le_seminorm_real S hp
  exact ⟨⟨g, (PolynormableSpace.withSeminorms ℝ E).continuous_real_rng g
    ⟨{⟨p, hp_cont⟩}, 1, fun x ↦ by simpa using (le_abs_self _).trans (hl x)⟩⟩, hg, hl⟩

variable [Module 𝕜 E] [PolynormableSpace 𝕜 E]

/-- **Hahn-Banach theorem** for linear functionals dominated by a continuous seminorm on
polynormable spaces over fields satisfying `IsRCLikeNormedField`. -/
theorem Module.Dual.exists_continuous_extension_of_le_seminorm (S : Submodule 𝕜 E) (f : Dual 𝕜 S)
    {p : Seminorm 𝕜 E} (hp_cont : Continuous p) (hp : ∀ x, ‖f x‖ ≤ p x) :
    ∃ g : StrongDual 𝕜 E, (∀ x : S, g x = f x) ∧ ∀ x, ‖g x‖ ≤ p x := by
  obtain ⟨g, hg, hle⟩ := Dual.exists_extension_of_le_seminorm S f hp
  refine ⟨⟨g, (PolynormableSpace.withSeminorms 𝕜 E).continuous_normedSpace_rng 𝕜 g ?_⟩, hg, hle⟩
  exact ⟨{⟨p, hp_cont⟩}, 1, by simpa⟩

/-- **Hahn-Banach theorem** for continuous linear functionals on polynormable spaces over a field
satisfying `IsRCLikeNormedField`. -/
theorem StrongDual.exists_extension {𝕜} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [Module 𝕜 E] [PolynormableSpace 𝕜 E] (S : Submodule 𝕜 E) (f : StrongDual 𝕜 S) :
    ∃ g : StrongDual 𝕜 E, ∀ x : S, g x = f x := by
  obtain ⟨q, hq_cont, hq⟩ := Seminorm.exists_le_comp_of_isInducing (f := S.subtype)
    (p := f.toSeminorm) f.continuous.norm IsInducing.subtypeVal
  obtain ⟨g, hg, _⟩ := Dual.exists_continuous_extension_of_le_seminorm S f.toLinearMap hq_cont hq
  exact ⟨g, hg⟩

variable {F : Type*} [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [Module 𝕜 F]
  [ContinuousSMul 𝕜 F] [T2Space F]

/-- Corollary of the polynormable **Hahn-Banach theorem**: if `f : S → F` is a continuous
linear map with finite-dimensional range, then `f` extends to a continuous linear map on the whole
space. -/
lemma ContinuousLinearMap.exist_extension_of_finiteDimensional_range {S : Submodule 𝕜 E}
    (f : S →L[𝕜] F) [FiniteDimensional 𝕜 f.range] :
    ∃ g : E →L[𝕜] F, f = g.comp S.subtypeL := by
  letI : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let b := Module.finBasis 𝕜 f.range
  let e := b.equivFunL
  let fi := fun i ↦ (LinearMap.toContinuousLinearMap (b.coord i)).comp
    (f.codRestrict _ <| LinearMap.mem_range_self _)
  choose gi hgf using fun i ↦ StrongDual.exists_extension S (fi i)
  use f.range.subtypeL.comp <| e.symm.toContinuousLinearMap.comp (.pi gi)
  ext x
  simp [fi, e, hgf]

/-- A finite-dimensional submodule of a polynormable space over a field satisfying
`IsRCLikeNormedField` is `Submodule.ClosedComplemented`. -/
lemma Submodule.ClosedComplemented.of_finiteDimensional [PolynormableSpace 𝕜 F] (S : Submodule 𝕜 F)
    [FiniteDimensional 𝕜 S] : S.ClosedComplemented := by
  let ⟨g, hg⟩ := (ContinuousLinearMap.id 𝕜 S).exist_extension_of_finiteDimensional_range
  exact ⟨g, DFunLike.congr_fun hg.symm⟩
