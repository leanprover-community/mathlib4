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

For the general `IsRCLikeNormedField` version, we state the topology hypothesis using
`PolynormableSpace`, the seminorm-family formulation of local convexity. Note that we cannot use
`LocallyConvexSpace` because an `IsRCLikeNormedField` has no order structure.

We prove
* `LinearMap.exists_extension`: Hahn-Banach theorem for linear functionals dominated by a continuous
  seminorm on polynormable spaces over fields satisfying `IsRCLikeNormedField`.
* `StrongDual.exists_extension`: Hahn-Banach theorem for continuous linear functionals on
  polynormable spaces over fields satisfying `IsRCLikeNormedField`.

-/

public section

open Module Topology RCLike

open scoped ComplexConjugate

variable {𝕜 E : Type*} [AddCommGroup E]

/-- If a real-linear functional is bounded by a `𝕜`-seminorm, then its `𝕜`-linear extension
is bounded by the same seminorm. -/
theorem Module.Dual.norm_extendRCLike_le_seminorm [RCLike 𝕜] [Module 𝕜 E] [Module ℝ E]
    [IsScalarTower ℝ 𝕜 E] (fr : Dual ℝ E) {p : Seminorm 𝕜 E} (hp : ∀ x, |fr x| ≤ p x) (x : E) :
    ‖(fr.extendRCLike x : 𝕜)‖ ≤ p x := by
  by_cases hx : fr.extendRCLike (𝕜 := 𝕜) x = 0
  · simp [hx]
  have hsq : ‖fr.extendRCLike (𝕜 := 𝕜) x‖ ^ 2 ≤ ‖fr.extendRCLike (𝕜 := 𝕜) x‖ * p x := calc
    _ = fr (conj (fr.extendRCLike x) • x) := fr.norm_extendRCLike_apply_sq x
    _ ≤ |fr (conj (fr.extendRCLike x) • x)| := le_abs_self _
    _ ≤ p (conj (fr.extendRCLike x) • x) := hp _
    _ = ‖conj (fr.extendRCLike x)‖ * p x := map_smul_eq_mul _ _ _
    _ = ‖(fr.extendRCLike x)‖ * p x := by rw [norm_conj]
  exact (mul_le_mul_iff_left₀ (norm_pos_iff.2 hx)).1 <| by simpa [pow_two, mul_comm] using hsq

theorem Module.Dual.exists_extension_of_le_seminorm_real [Module ℝ E]
    (S : Subspace ℝ E) (f : Dual ℝ S)
    {p : Seminorm ℝ E} (hp : ∀ x, f x ≤ p x) :
    ∃ g : Dual ℝ E, (∀ x : S, g x = f x) ∧ ∀ x, |g x| ≤ p x := by
  obtain ⟨g, hg, hl⟩ := by
    refine exists_extension_of_le_sublinear ⟨S, f⟩ p (fun _ hc _ => ?_) ?_ hp
    · simp [map_smul_eq_mul, abs_of_nonneg hc.le]
    · exact fun x y => map_add_le_add p x y
  exact ⟨g, hg, p.abs_le_of_le hl⟩

variable [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]

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

/-- **Hahn-Banach theorem** for linear functionals dominated by a continuous seminorm on locally
convex spaces over `ℝ`. -/
theorem Module.Dual.exists_continuous_extension_of_le_seminorm_real [IsTopologicalAddGroup E]
    [Module ℝ E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] (S : Subspace ℝ E) (f : Dual ℝ S)
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
theorem StrongDual.exists_extension (S : Submodule 𝕜 E) (f : StrongDual 𝕜 S) :
    ∃ g : StrongDual 𝕜 E, ∀ x : S, g x = f x := by
  obtain ⟨q, hq_cont, hq⟩ := PolynormableSpace.exists_continuous_seminorm_le (f := S.subtype)
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
