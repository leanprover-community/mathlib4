/-
Copyright (c) 2023 Sébastien Gouëzel All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.LinearAlgebra.Dual

/-!
# Spaces with separating dual

We introduce a typeclass `SeparatingDual R V`, registering that the points of the topological
module `V` over `R` can be separated by continuous linear forms.

This property is satisfied for normed spaces over `ℝ` or `ℂ` (by the analytic Hahn-Banach theorem)
and for locally convex topological spaces over `ℝ` (by the geometric Hahn-Banach theorem).

Under the assumption `SeparatingDual R V`, we show in
`SeparatingDual.exists_continuousLinearMap_apply_eq` that the group of continuous linear
equivalences acts transitively on the set of nonzero vectors.
-/

/-- When `E` is a topological module over a topological ring `R`, the class `SeparatingDual R E`
registers that continuous linear forms on `E` separate points of `E`. -/
@[mk_iff separatingDual_def]
class SeparatingDual (R V : Type*) [Ring R] [AddCommGroup V] [TopologicalSpace V]
    [TopologicalSpace R] [Module R V] : Prop :=
  /-- Any nonzero vector can be mapped by a continuous linear map to a nonzero scalar. -/
  exists_ne_zero' : ∀ (x : V), x ≠ 0 → ∃ f : V →L[R] R, f x ≠ 0

instance {E : Type*} [TopologicalSpace E] [AddCommGroup E] [TopologicalAddGroup E]
    [Module ℝ E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T1Space E] : SeparatingDual ℝ E :=
  ⟨fun x hx ↦ by
    rcases geometric_hahn_banach_point_point hx.symm with ⟨f, hf⟩
    simp only [map_zero] at hf
    exact ⟨f, hf.ne'⟩⟩

instance {E 𝕜 : Type*} [IsROrC 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] : SeparatingDual 𝕜 E :=
  ⟨fun x hx ↦ by
    rcases exists_dual_vector 𝕜 x hx with ⟨f, -, hf⟩
    refine ⟨f, ?_⟩
    simpa [hf] using hx⟩

namespace SeparatingDual

section Ring

variable {R V : Type*} [Ring R] [AddCommGroup V] [TopologicalSpace V]
  [TopologicalSpace R] [Module R V] [SeparatingDual R V]

lemma exists_ne_zero {x : V} (hx : x ≠ 0) :
    ∃ f : V →L[R] R, f x ≠ 0 :=
  exists_ne_zero' x hx

theorem exists_separating_of_ne {x y : V} (h : x ≠ y) :
    ∃ f : V →L[R] R, f x ≠ f y := by
  rcases exists_ne_zero (R := R) (sub_ne_zero_of_ne h) with ⟨f, hf⟩
  exact ⟨f, by simpa [sub_ne_zero] using hf⟩

protected theorem t1Space [T1Space R] : T1Space V := by
  apply t1Space_iff_exists_open.2 (fun x y hxy ↦ ?_)
  rcases exists_separating_of_ne (R := R) hxy with ⟨f, hf⟩
  exact ⟨f ⁻¹' {f y}ᶜ, isOpen_compl_singleton.preimage f.continuous, hf, by simp⟩

protected theorem t2Space [T2Space R] : T2Space V := by
  apply (t2Space_iff _).2 (fun {x} {y} hxy ↦ ?_)
  rcases exists_separating_of_ne (R := R) hxy with ⟨f, hf⟩
  exact separated_by_continuous f.continuous hf

end Ring

section Field

variable {R V : Type*} [Field R] [AddCommGroup V] [TopologicalSpace R] [TopologicalSpace V]
  [TopologicalRing R] [TopologicalAddGroup V] [Module R V] [SeparatingDual R V]

-- TODO (@alreadydone): this could generalize to CommRing R if we were to add a section
theorem _root_.separatingDual_iff_injective : SeparatingDual R V ↔
    Function.Injective (ContinuousLinearMap.coeLM (R := R) R (M := V) (N₃ := R)).flip := by
  simp_rw [separatingDual_def, Ne, injective_iff_map_eq_zero]
  congrm ∀ v, ?_
  rw [not_imp_comm, LinearMap.ext_iff]
  push_neg; rfl

open Function in
/-- Given a finite-dimensional subspace `W` of a space `V` with separating dual, any
  linear functional on `W` extends to a continuous linear functional on `V`.
  This is stated more generally for an injective linear map from `W` to `V`. -/
theorem dualMap_surjective_iff {W} [AddCommGroup W] [Module R W] [FiniteDimensional R W]
    {f : W →ₗ[R] V} : Surjective (f.dualMap ∘ ContinuousLinearMap.toLinearMap) ↔ Injective f := by
  constructor <;> intro hf
  · exact LinearMap.dualMap_surjective_iff.mp hf.of_comp
  have := (separatingDual_iff_injective.mp ‹_›).comp hf
  rw [← LinearMap.coe_comp] at this
  exact LinearMap.flip_surjective_iff₁.mpr this

lemma exists_eq_one {x : V} (hx : x ≠ 0) :
    ∃ f : V →L[R] R, f x = 1 := by
  rcases exists_ne_zero (R := R) hx with ⟨f, hf⟩
  exact ⟨(f x)⁻¹ • f, inv_mul_cancel hf⟩

theorem exists_eq_one_ne_zero_of_ne_zero_pair {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ f : V →L[R] R, f x = 1 ∧ f y ≠ 0 := by
  obtain ⟨u, ux⟩ : ∃ u : V →L[R] R, u x = 1 := exists_eq_one hx
  rcases ne_or_eq (u y) 0 with uy|uy
  · exact ⟨u, ux, uy⟩
  obtain ⟨v, vy⟩ : ∃ v : V →L[R] R, v y = 1 := exists_eq_one hy
  rcases ne_or_eq (v x) 0 with vx|vx
  · exact ⟨(v x)⁻¹ • v, inv_mul_cancel vx, show (v x)⁻¹ * v y ≠ 0 by simp [vx, vy]⟩
  · exact ⟨u + v, by simp [ux, vx], by simp [uy, vy]⟩

/-- In a topological vector space with separating dual, the group of continuous linear equivalences
acts transitively on the set of nonzero vectors: given two nonzero vectors `x` and `y`, there
exists `A : V ≃L[R] V` mapping `x` to `y`. -/
theorem exists_continuousLinearEquiv_apply_eq [ContinuousSMul R V]
    {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ A : V ≃L[R] V, A x = y := by
  obtain ⟨G, Gx, Gy⟩ : ∃ G : V →L[R] R, G x = 1 ∧ G y ≠ 0 :=
    exists_eq_one_ne_zero_of_ne_zero_pair hx hy
  let A : V ≃L[R] V :=
  { toFun := fun z ↦ z + G z • (y - x)
    invFun := fun z ↦ z + ((G y) ⁻¹ * G z) • (x - y)
    map_add' := fun a b ↦ by simp [add_smul]; abel
    map_smul' := by simp [smul_smul]
    left_inv := fun z ↦ by
      simp only [id_eq, eq_mpr_eq_cast, RingHom.id_apply, smul_eq_mul, AddHom.toFun_eq_coe,
        -- Note: #8386 had to change `map_smulₛₗ` into `map_smulₛₗ _`
        AddHom.coe_mk, map_add, map_smulₛₗ _, map_sub, Gx, mul_sub, mul_one, add_sub_cancel]
      rw [mul_comm (G z), ← mul_assoc, inv_mul_cancel Gy]
      simp only [smul_sub, one_mul]
      abel
    right_inv := fun z ↦ by
        -- Note: #8386 had to change `map_smulₛₗ` into `map_smulₛₗ _`
      simp only [map_add, map_smulₛₗ _, map_mul, map_inv₀, RingHom.id_apply, map_sub, Gx,
        smul_eq_mul, mul_sub, mul_one]
      rw [mul_comm _ (G y), ← mul_assoc, mul_inv_cancel Gy]
      simp only [smul_sub, one_mul, add_sub_cancel]
      abel
    continuous_toFun := continuous_id.add (G.continuous.smul continuous_const)
    continuous_invFun :=
      continuous_id.add ((continuous_const.mul G.continuous).smul continuous_const) }
  exact ⟨A, show x + G x • (y - x) = y by simp [Gx]⟩

end Field


open scoped NNReal

lemma _root_.LipschitzWith.cauchySeq_image {α β : Type*} [MetricSpace α] [MetricSpace β] {K : ℝ≥0} {f : α → β}
    (hf : LipschitzWith K f) {u : ℕ → α} (hu : CauchySeq u) :
    CauchySeq (f ∘ u) := by
  rcases cauchySeq_iff_le_tendsto_0.1 hu with ⟨b, b_nonneg, hb, blim⟩
  refine cauchySeq_iff_le_tendsto_0.2 ⟨fun n ↦ K * b n, ?_, ?_, ?_⟩
  · exact fun n ↦ mul_nonneg (by positivity) (b_nonneg n)
  · exact fun n m N hn hm ↦ hf.dist_le_mul_of_le (hb n m N hn hm)
  · rw [← mul_zero (K : ℝ)]
    exact blim.const_mul _


section

#check LipschitzWith

open Filter

open scoped Topology

lemma glou {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace 𝕜] [SeparatingDual 𝕜 E]
    [CompleteSpace (E →L[𝕜] F)] [Nontrivial E] : CompleteSpace F := by
  obtain ⟨v, hv⟩ : ∃ (v : E), v ≠ 0 := exists_ne 0
  obtain ⟨φ, hφ⟩ : ∃ φ : E →L[𝕜] 𝕜, φ v ≠ 0 := exists_ne_zero hv
  refine' Metric.complete_of_cauchySeq_tendsto fun f hf => _
  let g : ℕ → (E →L[𝕜] F) := fun n ↦ ContinuousLinearMap.smulRightL 𝕜 E F φ (f n)
  have : CauchySeq g := (ContinuousLinearMap.smulRightL 𝕜 E F φ).lipschitz.cauchySeq_image hf
  obtain ⟨a, ha⟩ : ∃ a, Tendsto g atTop (𝓝 a) := cauchy_iff_exists_le_nhds.mp this
  have : Tendsto (fun n ↦ g n v) atTop (𝓝 (a v)) := by
    have : Continuous (fun (i : E →L[𝕜] F) ↦ i v) := by exact?





end

end SeparatingDual
