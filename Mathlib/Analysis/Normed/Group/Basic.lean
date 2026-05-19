/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
module

public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Data.NNReal.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.MetricSpace.Basic

/-!
# (Semi)normed groups: basic theory

We prove basic properties of (semi)normed groups.

## Tags

normed group
-/

@[expose] public section


variable {𝓕 α ι κ E F G : Type*}

open Filter Function Metric Bornology
open ENNReal Filter NNReal Uniformity Pointwise Topology

section SeminormedGroup

variable [SeminormedGroup E] [SeminormedGroup F] [SeminormedGroup G] {s : Set E}
  {a a₁ a₂ b c d : E} {r r₁ r₂ : ℝ}

@[to_additive]
theorem dist_eq_norm_inv_mul (a b : E) : dist a b = ‖a⁻¹ * b‖ :=
  IsNormedGroup.dist_eq _ _

@[to_additive]
theorem dist_eq_norm_inv_mul' (a b : E) : dist a b = ‖b⁻¹ * a‖ := by
  rw [dist_comm, dist_eq_norm_inv_mul]

@[to_additive of_forall_le_norm]
lemma DiscreteTopology.of_forall_le_norm' (hpos : 0 < r) (hr : ∀ x : E, x ≠ 1 → r ≤ ‖x‖) :
    DiscreteTopology E :=
  .of_forall_le_dist hpos fun x y hne ↦ by
    simp only [dist_eq_norm_inv_mul]
    exact hr _ (by simpa [inv_mul_eq_one] using hne)

@[to_additive (attr := simp)]
theorem dist_one_right (a : E) : dist a 1 = ‖a‖ := by rw [dist_eq_norm_inv_mul', inv_one, one_mul]

@[to_additive]
theorem inseparable_one_iff_norm {a : E} : Inseparable a 1 ↔ ‖a‖ = 0 := by
  rw [Metric.inseparable_iff, dist_one_right]

@[to_additive]
lemma dist_one_left (a : E) : dist 1 a = ‖a‖ := by rw [dist_comm, dist_one_right]

@[to_additive (attr := simp)]
lemma dist_one : dist (1 : E) = norm := funext dist_one_left

@[to_additive]
theorem norm_div_rev (a b : E) : ‖a / b‖ = ‖b / a‖ := by
  rw [← dist_one, dist_eq_norm_inv_mul, dist_eq_norm_inv_mul']
  simp

@[to_additive (attr := simp) norm_neg]
theorem norm_inv' (a : E) : ‖a⁻¹‖ = ‖a‖ := by simpa using norm_div_rev 1 a

@[to_additive (attr := simp) norm_abs_zsmul]
theorem norm_zpow_abs (a : E) (n : ℤ) : ‖a ^ |n|‖ = ‖a ^ n‖ := by
  rcases le_total 0 n with hn | hn <;> simp [hn, abs_of_nonneg, abs_of_nonpos]

@[to_additive (attr := simp) norm_natAbs_smul]
theorem norm_pow_natAbs (a : E) (n : ℤ) : ‖a ^ n.natAbs‖ = ‖a ^ n‖ := by
  rw [← zpow_natCast, ← Int.abs_eq_natAbs, norm_zpow_abs]

@[to_additive norm_isUnit_zsmul]
theorem norm_zpow_isUnit (a : E) {n : ℤ} (hn : IsUnit n) : ‖a ^ n‖ = ‖a‖ := by
  rw [← norm_pow_natAbs, Int.isUnit_iff_natAbs_eq.mp hn, pow_one]

@[simp]
theorem norm_units_zsmul {E : Type*} [SeminormedAddGroup E] (n : ℤˣ) (a : E) : ‖n • a‖ = ‖a‖ :=
  norm_isUnit_zsmul a n.isUnit

open scoped symmDiff in
@[to_additive]
theorem dist_mulIndicator (s t : Set α) (f : α → E) (x : α) :
    dist (s.mulIndicator f x) (t.mulIndicator f x) = ‖(s ∆ t).mulIndicator f x‖ := by
  rw [dist_eq_norm_inv_mul, Set.apply_mulIndicator_symmDiff norm_inv']
  simp only [Set.mulIndicator, mul_ite, mul_one]
  split_ifs <;> simp

/-- **Triangle inequality** for the norm. -/
@[to_additive norm_add_le /-- **Triangle inequality** for the norm. -/]
theorem norm_mul_le' (a b : E) : ‖a * b‖ ≤ ‖a‖ + ‖b‖ := by
  simpa [dist_eq_norm_inv_mul] using dist_triangle a⁻¹ 1 b

/-- **Triangle inequality** for the norm. -/
@[to_additive norm_add_le_of_le /-- **Triangle inequality** for the norm. -/]
theorem norm_mul_le_of_le' (h₁ : ‖a₁‖ ≤ r₁) (h₂ : ‖a₂‖ ≤ r₂) : ‖a₁ * a₂‖ ≤ r₁ + r₂ :=
  (norm_mul_le' a₁ a₂).trans <| add_le_add h₁ h₂

/-- **Triangle inequality** for the norm. -/
@[to_additive norm_add₃_le /-- **Triangle inequality** for the norm. -/]
lemma norm_mul₃_le' : ‖a * b * c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := norm_mul_le_of_le' (norm_mul_le' _ _) le_rfl

/-- **Triangle inequality** for the norm. -/
@[to_additive norm_add₄_le /-- **Triangle inequality** for the norm. -/]
lemma norm_mul₄_le' : ‖a * b * c * d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ :=
  norm_mul_le_of_le' norm_mul₃_le' le_rfl

@[to_additive]
lemma norm_div_le_norm_div_add_norm_div (a b c : E) : ‖a / c‖ ≤ ‖a / b‖ + ‖b / c‖ := by
  simpa using norm_mul_le' (a / b) (b / c)

@[to_additive]
lemma norm_le_norm_div_add (a b : E) : ‖a‖ ≤ ‖a / b‖ + ‖b‖ := by
  simpa only [div_one] using norm_div_le_norm_div_add_norm_div a b 1

@[to_additive (attr := simp) norm_nonneg]
theorem norm_nonneg' (a : E) : 0 ≤ ‖a‖ := by
  rw [← dist_one_right]
  exact dist_nonneg

attribute [bound] norm_nonneg
attribute [grind .] norm_nonneg

@[to_additive (attr := simp) abs_norm]
theorem abs_norm' (z : E) : |‖z‖| = ‖z‖ := abs_of_nonneg <| norm_nonneg' _

@[to_additive (attr := simp) norm_zero]
theorem norm_one' : ‖(1 : E)‖ = 0 := by rw [← dist_one_right, dist_self]

@[to_additive]
theorem ne_one_of_norm_ne_zero : ‖a‖ ≠ 0 → a ≠ 1 :=
  mt <| by
    rintro rfl
    exact norm_one'

@[to_additive (attr := nontriviality) norm_of_subsingleton]
theorem norm_of_subsingleton' [Subsingleton E] (a : E) : ‖a‖ = 0 := by
  rw [Subsingleton.elim a 1, norm_one']

@[to_additive zero_lt_one_add_norm_sq]
theorem zero_lt_one_add_norm_sq' (x : E) : 0 < 1 + ‖x‖ ^ 2 := by
  positivity

@[to_additive]
theorem norm_div_le (a b : E) : ‖a / b‖ ≤ ‖a‖ + ‖b‖ := by
  simpa [div_eq_mul_inv] using norm_mul_le' a b⁻¹

attribute [bound] norm_sub_le

@[to_additive]
theorem norm_div_le_of_le {r₁ r₂ : ℝ} (H₁ : ‖a₁‖ ≤ r₁) (H₂ : ‖a₂‖ ≤ r₂) : ‖a₁ / a₂‖ ≤ r₁ + r₂ :=
  (norm_div_le a₁ a₂).trans <| add_le_add H₁ H₂

@[to_additive dist_le_norm_add_norm]
theorem dist_le_norm_add_norm' (a b : E) : dist a b ≤ ‖a‖ + ‖b‖ := by
  simpa [dist_eq_norm_inv_mul] using norm_mul_le' a⁻¹ b

@[to_additive]
theorem abs_norm_sub_norm_le_norm_inv_mul (a b : E) : |‖a‖ - ‖b‖| ≤ ‖a⁻¹ * b‖ := by
  simpa [dist_eq_norm_inv_mul] using abs_dist_sub_le a b 1

@[to_additive]
theorem norm_sub_norm_le_norm_inv_mul (a b : E) : ‖a‖ - ‖b‖ ≤ ‖a⁻¹ * b‖ :=
  (le_abs_self _).trans (abs_norm_sub_norm_le_norm_inv_mul a b)

@[to_additive (attr := bound)]
theorem norm_sub_le_norm_mul (a b : E) : ‖a‖ - ‖b‖ ≤ ‖a * b‖ := by
  simpa using norm_mul_le' (a * b) (b⁻¹)

@[to_additive]
theorem dist_norm_norm_le_norm_inv_mul (a b : E) : dist ‖a‖ ‖b‖ ≤ ‖a⁻¹ * b‖ :=
  abs_norm_sub_norm_le_norm_inv_mul a b

@[to_additive]
theorem norm_le_norm_add_norm_div' (u v : E) : ‖u‖ ≤ ‖v‖ + ‖u / v‖ := by
  rw [add_comm]
  refine (norm_mul_le' _ _).trans_eq' ?_
  rw [div_mul_cancel]

@[to_additive]
theorem norm_le_norm_add_norm_inv_mul (u v : E) : ‖u‖ ≤ ‖v‖ + ‖u⁻¹ * v‖ := by
  rw [add_comm, ← norm_inv' v, ← norm_inv' u]
  refine (norm_mul_le' _ _).trans_eq' ?_
  group

@[to_additive]
theorem norm_le_norm_add_norm_div (u v : E) : ‖v‖ ≤ ‖u‖ + ‖u / v‖ := by
  rw [norm_div_rev]
  exact norm_le_norm_add_norm_div' v u

alias norm_le_insert' := norm_le_norm_add_norm_sub'
alias norm_le_insert := norm_le_norm_add_norm_sub

@[to_additive]
theorem norm_le_mul_norm_add (u v : E) : ‖u‖ ≤ ‖u * v‖ + ‖v‖ :=
  calc
    ‖u‖ = ‖u * v / v‖ := by rw [mul_div_cancel_right]
    _ ≤ ‖u * v‖ + ‖v‖ := norm_div_le _ _

/-- An analogue of `norm_le_mul_norm_add` for the multiplication from the left. -/
@[to_additive /-- An analogue of `norm_le_add_norm_add` for the addition from the left. -/]
theorem norm_le_mul_norm_add' (u v : E) : ‖v‖ ≤ ‖u * v‖ + ‖u‖ :=
  calc
    ‖v‖ = ‖u⁻¹ * (u * v)‖ := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    _ ≤ ‖u⁻¹‖ + ‖u * v‖ := norm_mul_le' u⁻¹ (u * v)
    _ = ‖u * v‖ + ‖u‖ := by rw [norm_inv', add_comm]

@[to_additive]
lemma norm_mul_eq_norm_right {x : E} (y : E) (h : ‖x‖ = 0) : ‖x * y‖ = ‖y‖ := by
  apply le_antisymm ?_ ?_
  · simpa [h] using norm_mul_le' x y
  · simpa [h] using norm_le_mul_norm_add' x y

@[to_additive]
lemma norm_mul_eq_norm_left (x : E) {y : E} (h : ‖y‖ = 0) : ‖x * y‖ = ‖x‖ := by
  apply le_antisymm ?_ ?_
  · simpa [h] using norm_mul_le' x y
  · simpa [h] using norm_le_mul_norm_add x y

@[to_additive]
lemma norm_div_eq_norm_right {x : E} (y : E) (h : ‖x‖ = 0) : ‖x / y‖ = ‖y‖ := by
  rw [div_eq_mul_inv, norm_mul_eq_norm_right _ h, norm_inv']

@[to_additive]
lemma norm_div_eq_norm_left (x : E) {y : E} (h : ‖y‖ = 0) : ‖x / y‖ = ‖x‖ := by
  rw [div_eq_mul_inv, norm_mul_eq_norm_left]
  rwa [norm_inv']

@[to_additive]
theorem ball_eq_norm_inv_mul_lt (y : E) (ε : ℝ) : ball y ε = { x | ‖x⁻¹ * y‖ < ε } :=
  Set.ext fun a => by simp [dist_eq_norm_inv_mul]

@[to_additive]
theorem ball_one_eq (r : ℝ) : ball (1 : E) r = { x | ‖x‖ < r } :=
  Set.ext fun a => by simp

@[to_additive]
theorem mem_ball_iff_norm_inv_mul_lt : b ∈ ball a r ↔ ‖b⁻¹ * a‖ < r := by
  rw [mem_ball, dist_eq_norm_inv_mul]

@[to_additive]
theorem mem_ball_iff_norm_inv_mul_lt' : b ∈ ball a r ↔ ‖a⁻¹ * b‖ < r := by
  rw [mem_ball', dist_eq_norm_inv_mul]

@[to_additive]
theorem mem_ball_one_iff : a ∈ ball (1 : E) r ↔ ‖a‖ < r := by rw [mem_ball, dist_one_right]

@[to_additive]
theorem mem_closedBall_iff_norm_inv_mul_le : b ∈ closedBall a r ↔ ‖b⁻¹ * a‖ ≤ r := by
  rw [mem_closedBall, dist_eq_norm_inv_mul]

@[to_additive]
theorem mem_closedBall_one_iff : a ∈ closedBall (1 : E) r ↔ ‖a‖ ≤ r := by
  rw [mem_closedBall, dist_one_right]

@[to_additive]
theorem mem_closedBall_iff_norm_inv_mul_le' : b ∈ closedBall a r ↔ ‖a⁻¹ * b‖ ≤ r := by
  rw [mem_closedBall', dist_eq_norm_inv_mul]

@[to_additive norm_le_of_mem_closedBall]
theorem norm_le_of_mem_closedBall' (h : b ∈ closedBall a r) : ‖b‖ ≤ ‖a‖ + r :=
  (norm_le_norm_add_norm_inv_mul b a).trans (by simp [mem_closedBall_iff_norm_inv_mul_le.1 h])

@[to_additive norm_le_norm_add_const_of_dist_le]
theorem norm_le_norm_add_const_of_dist_le' : dist a b ≤ r → ‖a‖ ≤ ‖b‖ + r :=
  norm_le_of_mem_closedBall'

@[to_additive norm_lt_of_mem_ball]
theorem norm_lt_of_mem_ball' (h : b ∈ ball a r) : ‖b‖ < ‖a‖ + r :=
  (norm_le_norm_add_norm_inv_mul b a).trans_lt (by simp [mem_ball_iff_norm_inv_mul_lt.1 h])

@[to_additive]
theorem norm_div_sub_norm_div_le_norm_div (u v w : E) : ‖u / w‖ - ‖v / w‖ ≤ ‖u / v‖ := by
  simpa using norm_mul_le' (u / v) (v / w)

@[to_additive norm_add_sub_norm_sub_le_two_mul]
lemma norm_mul_sub_norm_div_le_two_mul {E : Type*} [SeminormedGroup E] (u v : E) :
    ‖u * v‖ - ‖u / v‖ ≤ 2 * ‖v‖ := by
  simpa [-tsub_le_iff_right, tsub_le_iff_left, two_mul, add_assoc]
    using norm_mul₃_le' (a := (u / v)) (b := v) (c := v)

@[to_additive norm_add_sub_norm_sub_le_two_mul_min]
lemma norm_mul_sub_norm_div_le_two_mul_min {E : Type*} [SeminormedCommGroup E] (u v : E) :
    ‖u * v‖ - ‖u / v‖ ≤ 2 * min ‖u‖ ‖v‖ := by
  rw [mul_min_of_nonneg _ _ (by positivity)]
  refine le_min ?_ (norm_mul_sub_norm_div_le_two_mul u v)
  rw [norm_div_rev, mul_comm]
  exact norm_mul_sub_norm_div_le_two_mul _ _

-- Higher priority to fire before `mem_sphere`.
@[to_additive]
theorem mem_sphere_iff_norm_inv_mul_eq : b ∈ sphere a r ↔ ‖b⁻¹ * a‖ = r := by
  simp [dist_eq_norm_inv_mul]

@[to_additive] -- `simp` can prove this
theorem mem_sphere_one_iff_norm : a ∈ sphere (1 : E) r ↔ ‖a‖ = r := by simp

@[to_additive (attr := simp) norm_eq_of_mem_sphere]
theorem norm_eq_of_mem_sphere' (x : sphere (1 : E) r) : ‖(x : E)‖ = r :=
  mem_sphere_one_iff_norm.mp x.2

@[to_additive]
theorem ne_one_of_mem_sphere (hr : r ≠ 0) (x : sphere (1 : E) r) : (x : E) ≠ 1 :=
  ne_one_of_norm_ne_zero <| by rwa [norm_eq_of_mem_sphere' x]

@[to_additive ne_zero_of_mem_unit_sphere]
theorem ne_one_of_mem_unit_sphere (x : sphere (1 : E) 1) : (x : E) ≠ 1 :=
  ne_one_of_mem_sphere one_ne_zero _

variable (E)

/-- The norm of a seminormed group as a group seminorm. -/
@[to_additive /-- The norm of a seminormed group as an additive group seminorm. -/]
def normGroupSeminorm : GroupSeminorm E :=
  ⟨norm, norm_one', norm_mul_le', norm_inv'⟩

@[to_additive (attr := simp)]
theorem coe_normGroupSeminorm : ⇑(normGroupSeminorm E) = norm :=
  rfl

variable {E}

@[to_additive]
theorem NormedGroup.tendsto_nhds_one {f : α → E} {l : Filter α} :
    Tendsto f l (𝓝 1) ↔ ∀ ε > 0, ∀ᶠ x in l, ‖f x‖ < ε :=
  Metric.tendsto_nhds.trans <| by simp only [dist_one_right]

@[deprecated (since := "2026-02-17")]
alias NormedCommGroup.tendsto_nhds_one := NormedGroup.tendsto_nhds_one

@[deprecated (since := "2026-02-17")]
alias NormedAddCommGroup.tendsto_nhds_zero := NormedAddGroup.tendsto_nhds_zero

@[to_additive]
theorem NormedGroup.tendsto_nhds_nhds {f : E → F} {x : E} {y : F} :
    Tendsto f (𝓝 x) (𝓝 y) ↔ ∀ ε > 0, ∃ δ > 0, ∀ x', ‖x'⁻¹ * x‖ < δ → ‖(f x')⁻¹ * y‖ < ε := by
  simp_rw [Metric.tendsto_nhds_nhds, dist_eq_norm_inv_mul]

@[to_additive]
theorem NormedGroup.nhds_basis_norm_lt (x : E) :
    (𝓝 x).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { y | ‖y⁻¹ * x‖ < ε } := by
  simp_rw [← ball_eq_norm_inv_mul_lt]
  exact Metric.nhds_basis_ball

@[to_additive]
theorem NormedGroup.nhds_one_basis_norm_lt :
    (𝓝 (1 : E)).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { y | ‖y‖ < ε } := by
  convert NormedGroup.nhds_basis_norm_lt (1 : E) using 1
  simp

@[deprecated (since := "2026-02-17")]
alias NormedCommGroup.nhds_one_basis_norm_lt := NormedGroup.nhds_one_basis_norm_lt

@[deprecated (since := "2026-02-17")]
alias NormedAddCommGroup.nhds_zero_basis_norm_lt := NormedAddGroup.nhds_zero_basis_norm_lt

@[to_additive]
theorem NormedGroup.uniformity_basis_dist :
    (𝓤 E).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { p : E × E | ‖p.fst⁻¹ * p.snd‖ < ε } := by
  convert Metric.uniformity_basis_dist (α := E) using 1
  simp [dist_eq_norm_inv_mul]

open Finset

variable [FunLike 𝓕 E F]

section NNNorm

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) SeminormedGroup.toNNNorm : NNNorm E :=
  ⟨fun a => .mk ‖a‖ (norm_nonneg' a)⟩

@[to_additive (attr := simp, norm_cast) coe_nnnorm]
theorem coe_nnnorm' (a : E) : (‖a‖₊ : ℝ) = ‖a‖ := rfl

@[to_additive (attr := simp) coe_comp_nnnorm]
theorem coe_comp_nnnorm' : (toReal : ℝ≥0 → ℝ) ∘ (nnnorm : E → ℝ≥0) = norm :=
  rfl

@[to_additive (attr := simp) norm_toNNReal]
theorem norm_toNNReal' : ‖a‖.toNNReal = ‖a‖₊ :=
  @Real.toNNReal_coe ‖a‖₊

@[to_additive (attr := simp) toReal_enorm]
lemma toReal_enorm' (x : E) : ‖x‖ₑ.toReal = ‖x‖ := by simp [enorm]

@[to_additive (attr := simp) ofReal_norm]
lemma ofReal_norm' (x : E) : .ofReal ‖x‖ = ‖x‖ₑ := by
  simp [enorm, ENNReal.ofReal, Real.toNNReal, nnnorm]

@[to_additive enorm_eq_iff_norm_eq]
theorem enorm'_eq_iff_norm_eq {x : E} {y : F} : ‖x‖ₑ = ‖y‖ₑ ↔ ‖x‖ = ‖y‖ := by
  simp only [← ofReal_norm']
  refine ⟨fun h ↦ ?_, fun h ↦ by congr⟩
  exact (Real.toNNReal_eq_toNNReal_iff (norm_nonneg' _) (norm_nonneg' _)).mp (ENNReal.coe_inj.mp h)

@[to_additive enorm_le_iff_norm_le]
theorem enorm'_le_iff_norm_le {x : E} {y : F} : ‖x‖ₑ ≤ ‖y‖ₑ ↔ ‖x‖ ≤ ‖y‖ := by
  simp only [← ofReal_norm']
  refine ⟨fun h ↦ ?_, fun h ↦ by gcongr⟩
  rw [ENNReal.ofReal_le_ofReal_iff (norm_nonneg' _)] at h
  exact h

@[to_additive]
theorem nndist_eq_nnnorm_inv_mul (a b : E) : nndist a b = ‖a⁻¹ * b‖₊ :=
  NNReal.eq <| dist_eq_norm_inv_mul _ _

@[to_additive (attr := simp) nnnorm_neg]
theorem nnnorm_inv' (a : E) : ‖a⁻¹‖₊ = ‖a‖₊ :=
  NNReal.eq <| norm_inv' a

@[to_additive (attr := simp)]
theorem nndist_one_right (a : E) : nndist a 1 = ‖a‖₊ := by
  simp [nndist_eq_nnnorm_inv_mul]

@[to_additive (attr := simp)]
lemma edist_one_right (a : E) : edist a 1 = ‖a‖ₑ := by simp [edist_nndist, nndist_one_right, enorm]

@[to_additive (attr := simp) nnnorm_zero]
theorem nnnorm_one' : ‖(1 : E)‖₊ = 0 := NNReal.eq norm_one'

@[to_additive]
theorem ne_one_of_nnnorm_ne_zero {a : E} : ‖a‖₊ ≠ 0 → a ≠ 1 :=
  mt <| by
    rintro rfl
    exact nnnorm_one'

@[to_additive nnnorm_add_le]
theorem nnnorm_mul_le' (a b : E) : ‖a * b‖₊ ≤ ‖a‖₊ + ‖b‖₊ :=
  NNReal.coe_le_coe.1 <| norm_mul_le' a b

@[to_additive norm_nsmul_le]
lemma norm_pow_le_mul_norm : ∀ {n : ℕ}, ‖a ^ n‖ ≤ n * ‖a‖
  | 0 => by simp
  | n + 1 => by simpa [pow_succ, add_mul] using norm_mul_le_of_le' norm_pow_le_mul_norm le_rfl

@[to_additive nnnorm_nsmul_le]
lemma nnnorm_pow_le_mul_norm {n : ℕ} : ‖a ^ n‖₊ ≤ n * ‖a‖₊ := by
  simpa only [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_natCast] using norm_pow_le_mul_norm

@[to_additive (attr := simp) nnnorm_abs_zsmul]
theorem nnnorm_zpow_abs (a : E) (n : ℤ) : ‖a ^ |n|‖₊ = ‖a ^ n‖₊ :=
  NNReal.eq <| norm_zpow_abs a n

@[to_additive (attr := simp) nnnorm_natAbs_smul]
theorem nnnorm_pow_natAbs (a : E) (n : ℤ) : ‖a ^ n.natAbs‖₊ = ‖a ^ n‖₊ :=
  NNReal.eq <| norm_pow_natAbs a n

@[to_additive nnnorm_isUnit_zsmul]
theorem nnnorm_zpow_isUnit (a : E) {n : ℤ} (hn : IsUnit n) : ‖a ^ n‖₊ = ‖a‖₊ :=
  NNReal.eq <| norm_zpow_isUnit a hn

@[simp]
theorem nnnorm_units_zsmul {E : Type*} [SeminormedAddGroup E] (n : ℤˣ) (a : E) : ‖n • a‖₊ = ‖a‖₊ :=
  NNReal.eq <| norm_isUnit_zsmul a n.isUnit

@[to_additive (attr := simp)]
theorem nndist_one_left (a : E) : nndist 1 a = ‖a‖₊ := by simp [nndist_eq_nnnorm_inv_mul]

@[to_additive (attr := simp)]
theorem edist_one_left (a : E) : edist 1 a = ‖a‖₊ := by
  rw [edist_nndist, nndist_one_left]

open scoped symmDiff in
@[to_additive]
theorem nndist_mulIndicator (s t : Set α) (f : α → E) (x : α) :
    nndist (s.mulIndicator f x) (t.mulIndicator f x) = ‖(s ∆ t).mulIndicator f x‖₊ :=
  NNReal.eq <| dist_mulIndicator s t f x

@[to_additive]
theorem nnnorm_div_le (a b : E) : ‖a / b‖₊ ≤ ‖a‖₊ + ‖b‖₊ :=
  NNReal.coe_le_coe.1 <| norm_div_le _ _

@[to_additive]
lemma enorm_div_le : ‖a / b‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ := by
  simpa [enorm, ← ENNReal.coe_add] using nnnorm_div_le a b

@[to_additive]
theorem nndist_nnnorm_nnnorm_le_nnnorm_inv_mul (a b : E) : nndist ‖a‖₊ ‖b‖₊ ≤ ‖a⁻¹ * b‖₊ :=
  NNReal.coe_le_coe.1 <| dist_norm_norm_le_norm_inv_mul a b

@[to_additive]
theorem nnnorm_le_nnnorm_add_nnnorm_div (a b : E) : ‖b‖₊ ≤ ‖a‖₊ + ‖a / b‖₊ :=
  norm_le_norm_add_norm_div _ _

@[to_additive]
theorem nnnorm_le_nnnorm_add_nnnorm_div' (a b : E) : ‖a‖₊ ≤ ‖b‖₊ + ‖a / b‖₊ :=
  norm_le_norm_add_norm_div' _ _

alias nnnorm_le_insert' := nnnorm_le_nnnorm_add_nnnorm_sub'

alias nnnorm_le_insert := nnnorm_le_nnnorm_add_nnnorm_sub

@[to_additive]
theorem nnnorm_le_mul_nnnorm_add (a b : E) : ‖a‖₊ ≤ ‖a * b‖₊ + ‖b‖₊ :=
  norm_le_mul_norm_add _ _

/-- An analogue of `nnnorm_le_mul_nnnorm_add` for the multiplication from the left. -/
@[to_additive /-- An analogue of `nnnorm_le_add_nnnorm_add` for the addition from the left. -/]
theorem nnnorm_le_mul_nnnorm_add' (a b : E) : ‖b‖₊ ≤ ‖a * b‖₊ + ‖a‖₊ :=
  norm_le_mul_norm_add' _ _

@[to_additive]
lemma nnnorm_mul_eq_nnnorm_right {x : E} (y : E) (h : ‖x‖₊ = 0) : ‖x * y‖₊ = ‖y‖₊ :=
  NNReal.eq <| norm_mul_eq_norm_right _ <| congr_arg NNReal.toReal h

@[to_additive]
lemma nnnorm_mul_eq_nnnorm_left (x : E) {y : E} (h : ‖y‖₊ = 0) : ‖x * y‖₊ = ‖x‖₊ :=
  NNReal.eq <| norm_mul_eq_norm_left _ <| congr_arg NNReal.toReal h

@[to_additive]
lemma nnnorm_div_eq_nnnorm_right {x : E} (y : E) (h : ‖x‖₊ = 0) : ‖x / y‖₊ = ‖y‖₊ :=
  NNReal.eq <| norm_div_eq_norm_right _ <| congr_arg NNReal.toReal h

@[to_additive]
lemma nnnorm_div_eq_nnnorm_left (x : E) {y : E} (h : ‖y‖₊ = 0) : ‖x / y‖₊ = ‖x‖₊ :=
  NNReal.eq <| norm_div_eq_norm_left _ <| congr_arg NNReal.toReal h

/-- The nonnegative norm seen as an `ENNReal` and then as a `Real` is equal to the norm. -/
@[to_additive toReal_coe_nnnorm /-- The nonnegative norm seen as an `ENNReal` and
then as a `Real` is equal to the norm. -/]
theorem toReal_coe_nnnorm' (a : E) : (‖a‖₊ : ℝ≥0∞).toReal = ‖a‖ := rfl

open scoped symmDiff in
@[to_additive]
theorem edist_mulIndicator (s t : Set α) (f : α → E) (x : α) :
    edist (s.mulIndicator f x) (t.mulIndicator f x) = ‖(s ∆ t).mulIndicator f x‖₊ := by
  rw [edist_nndist, nndist_mulIndicator]

@[to_additive nontrivialTopology_iff_exists_nnnorm_ne_zero]
theorem nontrivialTopology_iff_exists_nnnorm_ne_zero' :
    NontrivialTopology E ↔ ∃ x : E, ‖x‖₊ ≠ 0 := by
  simp_rw [TopologicalSpace.nontrivial_iff_exists_not_inseparable, Metric.inseparable_iff_nndist,
    nndist_eq_nnnorm_inv_mul]
  exact ⟨fun ⟨x, y, hxy⟩ => ⟨_, hxy⟩, fun ⟨x, hx⟩ => ⟨x, 1, by simpa using hx⟩⟩

@[to_additive indiscreteTopology_iff_forall_nnnorm_eq_zero]
theorem indiscreteTopology_iff_forall_nnnorm_eq_zero' :
    IndiscreteTopology E ↔ ∀ x : E, ‖x‖₊ = 0 := by
  simpa using nontrivialTopology_iff_exists_nnnorm_ne_zero' (E := E).not

variable (E) in
@[to_additive exists_nnnorm_ne_zero]
theorem exists_nnnorm_ne_zero' [NontrivialTopology E] : ∃ x : E, ‖x‖₊ ≠ 0 :=
  nontrivialTopology_iff_exists_nnnorm_ne_zero'.1 ‹_›

@[to_additive (attr := nontriviality) nnnorm_eq_zero]
theorem IndiscreteTopology.nnnorm_eq_zero' [IndiscreteTopology E] : ∀ x : E, ‖x‖₊ = 0 :=
  indiscreteTopology_iff_forall_nnnorm_eq_zero'.1 ‹_›

alias ⟨_, NontrivialTopology.of_exists_nnnorm_ne_zero'⟩ :=
  nontrivialTopology_iff_exists_nnnorm_ne_zero'
alias ⟨_, NontrivialTopology.of_exists_nnnorm_ne_zero⟩ :=
  nontrivialTopology_iff_exists_nnnorm_ne_zero
attribute [to_additive existing NontrivialTopology.of_exists_nnnorm_ne_zero]
  NontrivialTopology.of_exists_nnnorm_ne_zero'

alias ⟨_, IndiscreteTopology.of_forall_nnnorm_eq_zero'⟩ :=
  indiscreteTopology_iff_forall_nnnorm_eq_zero'
alias ⟨_, IndiscreteTopology.of_forall_nnnorm_eq_zero⟩ :=
  indiscreteTopology_iff_forall_nnnorm_eq_zero
attribute [to_additive existing IndiscreteTopology.of_forall_nnnorm_eq_zero]
  IndiscreteTopology.of_forall_nnnorm_eq_zero'

@[to_additive nontrivialTopology_iff_exists_norm_ne_zero]
theorem nontrivialTopology_iff_exists_norm_ne_zero' :
    NontrivialTopology E ↔ ∃ x : E, ‖x‖ ≠ 0 := by
  simp [nontrivialTopology_iff_exists_nnnorm_ne_zero', ← NNReal.ne_iff]

@[to_additive indiscreteTopology_iff_forall_norm_eq_zero]
theorem indiscreteTopology_iff_forall_norm_eq_zero' :
    IndiscreteTopology E ↔ ∀ x : E, ‖x‖ = 0 := by
  simpa using nontrivialTopology_iff_exists_norm_ne_zero' (E := E).not

variable (E) in
@[to_additive exists_norm_ne_zero]
theorem exists_norm_ne_zero' [NontrivialTopology E] : ∃ x : E, ‖x‖ ≠ 0 :=
  nontrivialTopology_iff_exists_norm_ne_zero'.1 ‹_›

@[to_additive (attr := nontriviality) IndiscreteTopology.norm_eq_zero]
theorem IndiscreteTopology.norm_eq_zero' [IndiscreteTopology E] : ∀ x : E, ‖x‖ = 0 :=
  indiscreteTopology_iff_forall_norm_eq_zero'.1 ‹_›

alias ⟨_, NontrivialTopology.of_exists_norm_ne_zero'⟩ :=
  nontrivialTopology_iff_exists_norm_ne_zero'
alias ⟨_, NontrivialTopology.of_exists_norm_ne_zero⟩ :=
  nontrivialTopology_iff_exists_norm_ne_zero
attribute [to_additive existing NontrivialTopology.of_exists_norm_ne_zero]
  NontrivialTopology.of_exists_norm_ne_zero'

alias ⟨_, IndiscreteTopology.of_forall_norm_eq_zero'⟩ :=
  indiscreteTopology_iff_forall_norm_eq_zero'
alias ⟨_, IndiscreteTopology.of_forall_norm_eq_zero⟩ :=
  indiscreteTopology_iff_forall_norm_eq_zero
attribute [to_additive existing IndiscreteTopology.of_forall_norm_eq_zero]
  IndiscreteTopology.of_forall_norm_eq_zero'

end NNNorm

section ENorm

@[to_additive (attr := simp) enorm_zero]
lemma enorm_one' {E : Type*} [TopologicalSpace E] [ESeminormedMonoid E] : ‖(1 : E)‖ₑ = 0 := by
  rw [IsESeminormedMonoid.enorm_zero]

@[to_additive exists_enorm_lt]
lemma exists_enorm_lt' (E : Type*) [TopologicalSpace E] [ESeminormedMonoid E]
    [hbot : NeBot (𝓝[≠] (1 : E))] {c : ℝ≥0∞} (hc : c ≠ 0) : ∃ x ≠ (1 : E), ‖x‖ₑ < c :=
  frequently_iff_neBot.mpr hbot |>.and_eventually
    (ContinuousENorm.continuous_enorm.tendsto' 1 0 (by simp) |>.eventually_lt_const hc.bot_lt)
    |>.exists

@[to_additive (attr := simp) enorm_neg]
lemma enorm_inv' (a : E) : ‖a⁻¹‖ₑ = ‖a‖ₑ := by simp [enorm]

@[to_additive ofReal_norm_eq_enorm]
lemma ofReal_norm_eq_enorm' (a : E) : .ofReal ‖a‖ = ‖a‖ₑ := ENNReal.ofReal_eq_coe_nnreal _

@[to_additive]
theorem edist_eq_enorm_inv_mul (a b : E) : edist a b = ‖a⁻¹ * b‖ₑ := by
  rw [edist_dist, dist_eq_norm_inv_mul, ofReal_norm_eq_enorm']

@[deprecated (since := "2026-02-11")] alias edist_one_eq_enorm := edist_one_right

@[deprecated (since := "2026-02-11")] alias edist_zero_eq_enorm := edist_zero_right

@[to_additive]
lemma enorm_div_rev {E : Type*} [SeminormedGroup E] (a b : E) : ‖a / b‖ₑ = ‖b / a‖ₑ := by
  rw [← enorm_inv', inv_div]

@[to_additive]
theorem mem_eball_one_iff {r : ℝ≥0∞} : a ∈ eball 1 r ↔ ‖a‖ₑ < r := by
  rw [Metric.mem_eball, edist_one_right]

@[deprecated (since := "2026-01-24")]
alias mem_emetric_ball_zero_iff := mem_eball_zero_iff

@[to_additive existing, deprecated (since := "2026-01-24")]
alias mem_emetric_ball_one_iff := mem_eball_one_iff

end ENorm

section ESeminormedMonoid

variable {E : Type*} [TopologicalSpace E] [ESeminormedMonoid E]

@[to_additive enorm_add_le]
lemma enorm_mul_le' (a b : E) : ‖a * b‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ := IsESeminormedMonoid.enorm_mul_le a b

@[to_additive enorm_add_le_of_le]
theorem enorm_mul_le_of_le' {r₁ r₂ : ℝ≥0∞} {a₁ a₂ : E}
    (h₁ : ‖a₁‖ₑ ≤ r₁) (h₂ : ‖a₂‖ₑ ≤ r₂) : ‖a₁ * a₂‖ₑ ≤ r₁ + r₂ :=
  (enorm_mul_le' a₁ a₂).trans <| add_le_add h₁ h₂

@[to_additive enorm_add₃_le]
lemma enorm_mul₃_le' {a b c : E} : ‖a * b * c‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ + ‖c‖ₑ :=
  enorm_mul_le_of_le' (enorm_mul_le' _ _) le_rfl

@[to_additive enorm_add₄_le]
lemma enorm_mul₄_le' {a b c d : E} : ‖a * b * c * d‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ + ‖c‖ₑ + ‖d‖ₑ :=
  enorm_mul_le_of_le' enorm_mul₃_le' le_rfl

end ESeminormedMonoid

section ENormedMonoid

variable {E : Type*} [TopologicalSpace E] [ENormedMonoid E]

@[to_additive (attr := simp) enorm_eq_zero]
lemma enorm_eq_zero' {a : E} : ‖a‖ₑ = 0 ↔ a = 1 := by
  simp [IsENormedMonoid.enorm_eq_zero]

@[to_additive enorm_ne_zero]
lemma enorm_ne_zero' {a : E} : ‖a‖ₑ ≠ 0 ↔ a ≠ 1 :=
  enorm_eq_zero'.ne

@[to_additive (attr := simp) enorm_pos]
lemma enorm_pos' {a : E} : 0 < ‖a‖ₑ ↔ a ≠ 1 :=
  pos_iff_ne_zero.trans enorm_ne_zero'

end ENormedMonoid

open Set in
@[to_additive]
lemma SeminormedGroup.disjoint_nhds (x : E) (f : Filter E) :
    Disjoint (𝓝 x) f ↔ ∃ δ > 0, ∀ᶠ y in f, δ ≤ ‖y⁻¹ * x‖ := by
  simp [NormedGroup.nhds_basis_norm_lt x |>.disjoint_iff_left, compl_setOf, eventually_iff]

@[to_additive]
lemma SeminormedGroup.disjoint_nhds_one (f : Filter E) :
    Disjoint (𝓝 1) f ↔ ∃ δ > 0, ∀ᶠ y in f, δ ≤ ‖y‖ := by
  simpa using disjoint_nhds 1 f

end SeminormedGroup

section Induced

variable (E F)

/-- missing doc -/
abbrev NormPseudoMetric.induced [NormPseudoMetric F] (f : E → F) :
    NormPseudoMetric E where
  norm := fun x => ‖f x‖
  toPseudoMetricSpace := .induced f toPseudoMetricSpace

/-- missing doc -/
abbrev NormMetric.induced [NormMetric F] (f : E → F) (hf : Injective f) :
    NormMetric E where
  norm := fun x => ‖f x‖
  toMetricSpace := .induced f hf toMetricSpace

variable [FunLike 𝓕 E F]

@[to_additive]
lemma IsNormedGroup.induced [Group E] [SeminormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕) :
    letI : NormPseudoMetric E := .induced E F f
    IsNormedGroup E :=
  letI : NormPseudoMetric E := .induced E F f
  { dist_eq x y := by simp +instances only [norm, map_mul, map_inv, ← dist_eq_norm_inv_mul]; rfl }

end Induced

namespace Subtype

variable {p : α → Prop}

instance [Norm α] : Norm (Subtype p) where
  norm x := ‖(x : α)‖

@[simp]
theorem coe_norm [Norm α] (x : Subtype p) : ‖x‖ = ‖(x : α)‖ :=
  rfl

@[norm_cast]
theorem norm_coe [Norm α] (x : Subtype p) : ‖(x : α)‖ = ‖x‖ :=
  rfl

instance [NormPseudoMetric α] : NormPseudoMetric (Subtype p) where
instance [NormMetric α] : NormMetric (Subtype p) where

end Subtype

section SeminormedCommGroup

variable [SeminormedCommGroup E] [SeminormedCommGroup F] {a b : E} {r : ℝ}
variable {ε : Type*} [TopologicalSpace ε] [ESeminormedCommMonoid ε]

@[to_additive]
theorem dist_eq_norm_div (a b : E) : dist a b = ‖a / b‖ := by
  rw [dist_eq_norm_inv_mul', div_eq_inv_mul]

@[to_additive]
theorem dist_eq_norm_div' (a b : E) : dist a b = ‖b / a‖ := by
  rw [dist_eq_norm_inv_mul, div_eq_inv_mul]

alias dist_eq_norm := dist_eq_norm_sub

alias dist_eq_norm' := dist_eq_norm_sub'

@[to_additive]
theorem norm_inv_mul (a b : E) : ‖a⁻¹ * b‖ = ‖a / b‖ := by
  rw [← dist_eq_norm_inv_mul, dist_eq_norm_div]

@[to_additive abs_norm_sub_norm_le]
theorem abs_norm_sub_norm_le' (a b : E) : |‖a‖ - ‖b‖| ≤ ‖a / b‖ :=
  (abs_norm_sub_norm_le_norm_inv_mul a b).trans_eq (norm_inv_mul a b)

@[to_additive norm_sub_norm_le]
theorem norm_sub_norm_le' (a b : E) : ‖a‖ - ‖b‖ ≤ ‖a / b‖ :=
  (le_abs_self _).trans (abs_norm_sub_norm_le' a b)

@[to_additive dist_norm_norm_le]
theorem dist_norm_norm_le' (a b : E) : dist ‖a‖ ‖b‖ ≤ ‖a / b‖ :=
  abs_norm_sub_norm_le' a b

@[to_additive nndist_nnnorm_nnnorm_le]
theorem nndist_nnnorm_nnnorm_le' (a b : E) : nndist ‖a‖₊ ‖b‖₊ ≤ ‖a / b‖₊ :=
  NNReal.coe_le_coe.1 <| dist_norm_norm_le' a b

@[to_additive]
theorem nndist_eq_nnnorm_div (a b : E) : nndist a b = ‖a / b‖₊ :=
  NNReal.eq <| dist_eq_norm_div _ _

alias nndist_eq_nnnorm := nndist_eq_nnnorm_sub

@[to_additive]
theorem edist_eq_enorm_div (a b : E) : edist a b = ‖a / b‖ₑ := by
  rw [edist_dist, dist_eq_norm_div, ofReal_norm_eq_enorm']

@[to_additive]
theorem dist_inv (x y : E) : dist x⁻¹ y = dist x y⁻¹ := by
  simp_rw [dist_eq_norm_inv_mul, ← norm_inv' (x⁻¹ * y⁻¹), mul_inv, inv_inv]

theorem norm_multiset_sum_le {E} [SeminormedAddCommGroup E] (m : Multiset E) :
    ‖m.sum‖ ≤ (m.map fun x => ‖x‖).sum :=
  m.le_sum_of_subadditive norm norm_zero.le norm_add_le

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddCommMonoid ε] in
theorem enorm_multisetSum_le (m : Multiset ε) :
    ‖m.sum‖ₑ ≤ (m.map fun x => ‖x‖ₑ).sum :=
  m.le_sum_of_subadditive enorm enorm_zero.le enorm_add_le

@[to_additive existing]
theorem norm_multiset_prod_le (m : Multiset E) : ‖m.prod‖ ≤ (m.map fun x => ‖x‖).sum :=
  m.apply_prod_le_sum_map _ norm_one'.le norm_mul_le'

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedCommMonoid ε] in
@[to_additive existing]
theorem enorm_multisetProd_le (m : Multiset ε) :
    ‖m.prod‖ₑ ≤ (m.map fun x => ‖x‖ₑ).sum :=
  m.apply_prod_le_sum_map _ enorm_one'.le enorm_mul_le'

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddCommMonoid ε] in
@[bound]
theorem enorm_sum_le (s : Finset ι) (f : ι → ε) :
    ‖∑ i ∈ s, f i‖ₑ ≤ ∑ i ∈ s, ‖f i‖ₑ :=
  s.le_sum_of_subadditive enorm enorm_zero.le enorm_add_le f

@[bound]
theorem norm_sum_le {E} [SeminormedAddCommGroup E] (s : Finset ι) (f : ι → E) :
    ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ :=
  s.le_sum_of_subadditive norm norm_zero.le norm_add_le f

@[to_additive existing]
theorem enorm_prod_le (s : Finset ι) (f : ι → ε) : ‖∏ i ∈ s, f i‖ₑ ≤ ∑ i ∈ s, ‖f i‖ₑ :=
  s.apply_prod_le_sum_apply _ enorm_one'.le enorm_mul_le'

@[to_additive existing]
theorem norm_prod_le (s : Finset ι) (f : ι → E) : ‖∏ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ :=
  s.apply_prod_le_sum_apply _ norm_one'.le norm_mul_le'

@[to_additive]
theorem enorm_prod_le_of_le (s : Finset ι) {f : ι → ε} {n : ι → ℝ≥0∞} (h : ∀ b ∈ s, ‖f b‖ₑ ≤ n b) :
    ‖∏ b ∈ s, f b‖ₑ ≤ ∑ b ∈ s, n b :=
  (enorm_prod_le s f).trans <| Finset.sum_le_sum h

@[to_additive]
theorem norm_prod_le_of_le (s : Finset ι) {f : ι → E} {n : ι → ℝ} (h : ∀ b ∈ s, ‖f b‖ ≤ n b) :
    ‖∏ b ∈ s, f b‖ ≤ ∑ b ∈ s, n b :=
  (norm_prod_le s f).trans <| Finset.sum_le_sum h

@[to_additive]
theorem dist_prod_prod_le_of_le (s : Finset ι) {f a : ι → E} {d : ι → ℝ}
    (h : ∀ b ∈ s, dist (f b) (a b) ≤ d b) :
    dist (∏ b ∈ s, f b) (∏ b ∈ s, a b) ≤ ∑ b ∈ s, d b := by
  simp_rw [dist_eq_norm_inv_mul] at h
  rw [dist_eq_norm_inv_mul, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  exact norm_prod_le_of_le s h

@[to_additive]
theorem dist_prod_prod_le (s : Finset ι) (f a : ι → E) :
    dist (∏ b ∈ s, f b) (∏ b ∈ s, a b) ≤ ∑ b ∈ s, dist (f b) (a b) :=
  dist_prod_prod_le_of_le s fun _ _ => le_rfl

@[to_additive ball_eq]
theorem ball_eq' (y : E) (ε : ℝ) : ball y ε = { x | ‖x / y‖ < ε } := by
  simp_rw [ball_eq_norm_inv_mul_lt, norm_inv_mul]

@[to_additive mem_ball_iff_norm]
theorem mem_ball_iff_norm'' : b ∈ ball a r ↔ ‖b / a‖ < r := by
  rw [mem_ball, dist_eq_norm_div]

@[to_additive mem_ball_iff_norm']
theorem mem_ball_iff_norm''' : b ∈ ball a r ↔ ‖a / b‖ < r := by
  rw [mem_ball', dist_eq_norm_div]

@[to_additive mem_closedBall_iff_norm]
theorem mem_closedBall_iff_norm'' : b ∈ closedBall a r ↔ ‖b / a‖ ≤ r := by
  rw [mem_closedBall, dist_eq_norm_div]

@[to_additive mem_closedBall_iff_norm']
theorem mem_closedBall_iff_norm''' : b ∈ closedBall a r ↔ ‖a / b‖ ≤ r := by
  rw [mem_closedBall', dist_eq_norm_div]

-- Higher priority to fire before `mem_sphere`.
@[to_additive (attr := simp high) mem_sphere_iff_norm]
theorem mem_sphere_iff_norm' : b ∈ sphere a r ↔ ‖b / a‖ = r := by simp [dist_eq_norm_div]

@[to_additive]
theorem mul_mem_ball_iff_norm : a * b ∈ ball a r ↔ ‖b‖ < r := by
  rw [mem_ball_iff_norm'']
  simp

@[to_additive]
theorem mul_mem_closedBall_iff_norm : a * b ∈ closedBall a r ↔ ‖b‖ ≤ r := by
  rw [mem_closedBall_iff_norm'']
  simp

-- Higher priority to apply this before the equivalent lemma `Metric.preimage_mul_left_ball`.
@[to_additive (attr := simp high)]
theorem preimage_mul_ball (a b : E) (r : ℝ) : (b * ·) ⁻¹' ball a r = ball (a / b) r := by
  ext c
  simp [dist_eq_norm_inv_mul, Set.mem_preimage, mem_ball, div_eq_mul_inv, mul_comm, mul_assoc]

-- Higher priority to apply this before the equivalent lemma `Metric.preimage_mul_left_closedBall`.
@[to_additive (attr := simp high)]
theorem preimage_mul_closedBall (a b : E) (r : ℝ) :
    (b * ·) ⁻¹' closedBall a r = closedBall (a / b) r := by
  ext c
  simp [dist_eq_norm_inv_mul, Set.mem_preimage, mem_closedBall, div_eq_mul_inv, mul_comm, mul_assoc]

@[to_additive (attr := simp)]
theorem preimage_mul_sphere (a b : E) (r : ℝ) : (b * ·) ⁻¹' sphere a r = sphere (a / b) r := by
  ext c
  simp only [Set.mem_preimage, mem_sphere_iff_norm', div_div_eq_mul_div, mul_comm]

@[to_additive]
theorem pow_mem_closedBall {n : ℕ} (h : a ∈ closedBall b r) :
    a ^ n ∈ closedBall (b ^ n) (n • r) := by
  simp only [mem_closedBall, dist_eq_norm_inv_mul, ← inv_pow, ← mul_pow] at h ⊢
  refine norm_pow_le_mul_norm.trans ?_
  simpa only [nsmul_eq_mul] using mul_le_mul_of_nonneg_left h n.cast_nonneg

@[to_additive]
theorem pow_mem_ball {n : ℕ} (hn : 0 < n) (h : a ∈ ball b r) : a ^ n ∈ ball (b ^ n) (n • r) := by
  simp only [mem_ball, dist_eq_norm_inv_mul, ← inv_pow, ← mul_pow] at h ⊢
  refine lt_of_le_of_lt norm_pow_le_mul_norm ?_
  replace hn : 0 < (n : ℝ) := by norm_cast
  rw [nsmul_eq_mul]
  nlinarith

@[to_additive]
theorem mul_mem_closedBall_mul_iff {c : E} : a * c ∈ closedBall (b * c) r ↔ a ∈ closedBall b r := by
  simp only [mem_closedBall, dist_eq_norm_inv_mul, mul_comm _ (b * c), mul_comm a⁻¹ b]
  simp

@[to_additive]
theorem mul_mem_ball_mul_iff {c : E} : a * c ∈ ball (b * c) r ↔ a ∈ ball b r := by
  simp only [mem_ball, dist_eq_norm_inv_mul, mul_comm _ (b * c), mul_comm a⁻¹ b]
  simp

@[to_additive]
theorem smul_closedBall'' : a • closedBall b r = closedBall (a • b) r := by
  ext
  simp [mem_closedBall, Set.mem_smul_set, dist_eq_norm_inv_mul, ← eq_inv_mul_iff_mul_eq, mul_assoc]

@[to_additive]
theorem smul_ball'' : a • ball b r = ball (a • b) r := by
  ext
  simp [mem_ball, Set.mem_smul_set, dist_eq_norm_inv_mul, ← eq_inv_mul_iff_mul_eq, mul_assoc]

@[to_additive]
theorem nnnorm_multiset_prod_le (m : Multiset E) : ‖m.prod‖₊ ≤ (m.map fun x => ‖x‖₊).sum :=
  NNReal.coe_le_coe.1 <| by
    push_cast
    rw [Multiset.map_map]
    exact norm_multiset_prod_le _

@[to_additive]
theorem nnnorm_prod_le (s : Finset ι) (f : ι → E) : ‖∏ a ∈ s, f a‖₊ ≤ ∑ a ∈ s, ‖f a‖₊ :=
  NNReal.coe_le_coe.1 <| by
    push_cast
    exact norm_prod_le _ _

@[to_additive]
theorem nnnorm_prod_le_of_le (s : Finset ι) {f : ι → E} {n : ι → ℝ≥0} (h : ∀ b ∈ s, ‖f b‖₊ ≤ n b) :
    ‖∏ b ∈ s, f b‖₊ ≤ ∑ b ∈ s, n b :=
  (norm_prod_le_of_le s h).trans_eq (NNReal.coe_sum ..).symm

@[to_additive]
theorem NormedCommGroup.tendsto_nhds_nhds {f : E → F} {x : E} {y : F} :
    Tendsto f (𝓝 x) (𝓝 y) ↔ ∀ ε > 0, ∃ δ > 0, ∀ x', ‖x' / x‖ < δ → ‖f x' / y‖ < ε := by
  simpa [norm_inv_mul] using NormedGroup.tendsto_nhds_nhds (f := f) (x := x) (y := y)

@[to_additive]
theorem NormedCommGroup.nhds_basis_norm_lt (x : E) :
    (𝓝 x).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { y | ‖y / x‖ < ε } := by
  simpa [norm_inv_mul] using NormedGroup.nhds_basis_norm_lt x

@[to_additive]
theorem NormedCommGroup.uniformity_basis_dist :
    (𝓤 E).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { p : E × E | ‖p.fst / p.snd‖ < ε } := by
  simpa [norm_inv_mul] using NormedGroup.uniformity_basis_dist (E := E)

end SeminormedCommGroup

section NormedGroup

variable [NormedGroup E] {a b : E}

@[to_additive (attr := simp) norm_le_zero_iff]
lemma norm_le_zero_iff' : ‖a‖ ≤ 0 ↔ a = 1 := by rw [← dist_one_right, dist_le_zero]

@[to_additive (attr := simp) norm_pos_iff]
lemma norm_pos_iff' : 0 < ‖a‖ ↔ a ≠ 1 := by rw [← not_le, norm_le_zero_iff']

@[to_additive (attr := simp) norm_eq_zero]
lemma norm_eq_zero' : ‖a‖ = 0 ↔ a = 1 := (norm_nonneg' a).ge_iff_eq'.symm.trans norm_le_zero_iff'

@[to_additive norm_ne_zero_iff]
lemma norm_ne_zero_iff' : ‖a‖ ≠ 0 ↔ a ≠ 1 := norm_eq_zero'.not

@[to_additive]
theorem norm_div_eq_zero_iff : ‖a / b‖ = 0 ↔ a = b := by rw [norm_eq_zero', div_eq_one]

@[to_additive]
theorem norm_div_pos_iff : 0 < ‖a / b‖ ↔ a ≠ b := by
  rw [(norm_nonneg' _).lt_iff_ne, ne_comm]
  exact norm_div_eq_zero_iff.not

@[to_additive eq_of_norm_sub_le_zero]
theorem eq_of_norm_div_le_zero (h : ‖a / b‖ ≤ 0) : a = b := by
  rwa [← div_eq_one, ← norm_le_zero_iff']

alias ⟨eq_of_norm_div_eq_zero, _⟩ := norm_div_eq_zero_iff

attribute [to_additive] eq_of_norm_div_eq_zero

@[to_additive]
theorem eq_one_or_norm_pos (a : E) : a = 1 ∨ 0 < ‖a‖ := by
  simpa [eq_comm] using (norm_nonneg' a).eq_or_lt

@[to_additive]
theorem eq_one_or_nnnorm_pos (a : E) : a = 1 ∨ 0 < ‖a‖₊ :=
  eq_one_or_norm_pos a

@[to_additive (attr := simp) nnnorm_eq_zero]
theorem nnnorm_eq_zero' : ‖a‖₊ = 0 ↔ a = 1 := by
  rw [← NNReal.coe_eq_zero, coe_nnnorm', norm_eq_zero']

@[to_additive nnnorm_ne_zero_iff]
theorem nnnorm_ne_zero_iff' : ‖a‖₊ ≠ 0 ↔ a ≠ 1 :=
  nnnorm_eq_zero'.not

@[to_additive (attr := simp) nnnorm_pos]
lemma nnnorm_pos' : 0 < ‖a‖₊ ↔ a ≠ 1 := pos_iff_ne_zero.trans nnnorm_ne_zero_iff'

variable (E)

/-- The norm of a normed group as a group norm. -/
@[to_additive /-- The norm of a normed group as an additive group norm. -/]
def normGroupNorm : GroupNorm E :=
  { normGroupSeminorm _ with eq_one_of_map_eq_zero' := fun _ => norm_eq_zero'.1 }

@[simp]
theorem coe_normGroupNorm : ⇑(normGroupNorm E) = norm :=
  rfl

end NormedGroup

section NormedAddGroup

variable [NormedAddGroup E] [TopologicalSpace α] {f : α → E}

/-! Some relations with `HasCompactSupport` -/

theorem hasCompactSupport_norm_iff : (HasCompactSupport fun x => ‖f x‖) ↔ HasCompactSupport f :=
  hasCompactSupport_comp_left norm_eq_zero

alias ⟨_, HasCompactSupport.norm⟩ := hasCompactSupport_norm_iff

end NormedAddGroup

/-! ### `positivity` extensions -/

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

/-- Extension for the `positivity` tactic: multiplicative norms are always nonnegative, and positive
on non-one inputs. -/
@[positivity ‖_‖]
meta def evalMulNorm : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@Norm.norm $E $_n $a) =>
    let _group_E ← synthInstanceQ q(Group $E)
    let _normPseudoMetric_E ← synthInstanceQ q(NormPseudoMetric $E)
    let _isNormedGroup_E ← synthInstanceQ q(IsNormedGroup $E)
    assertInstancesCommute
    -- Check whether we are in a normed group and whether the context contains a `a ≠ 1` assumption
    let o : Option (Q(NormMetric $E) × Q($a ≠ 1)) := ← do
      let .some normMetric_E ← trySynthInstanceQ q(NormMetric $E) | return none
      let some pa ← findLocalDeclWithTypeQ? q($a ≠ 1) | return none
      return some (normMetric_E, pa)
    match o with
    -- If so, return a proof of `0 < ‖a‖`
    | some (_normedGroup_E, pa) =>
      assertInstancesCommute
      return .positive q(norm_pos_iff'.2 $pa)
    -- Else, return a proof of `0 ≤ ‖a‖`
    | none => return .nonnegative q(norm_nonneg' $a)
  | _, _, _ => throwError "not `‖·‖`"

/-- Extension for the `positivity` tactic: additive norms are always nonnegative, and positive
on non-zero inputs. -/
@[positivity ‖_‖]
meta def evalAddNorm : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@Norm.norm $E $_n $a) =>
    let _addGroup_E ← synthInstanceQ q(AddGroup $E)
    let _normPseudoMetric_E ← synthInstanceQ q(NormPseudoMetric $E)
    let _isNormedAddGroup_E ← synthInstanceQ q(IsNormedAddGroup $E)
    assertInstancesCommute
    -- Check whether we are in a normed group and whether the context contains a `a ≠ 0` assumption
    let o : Option (Q(NormMetric $E) × Q($a ≠ 0)) := ← do
      let .some normMetric_E ← trySynthInstanceQ q(NormMetric $E) | return none
      let some pa ← findLocalDeclWithTypeQ? q($a ≠ 0) | return none
      return some (normMetric_E, pa)
    match o with
    -- If so, return a proof of `0 < ‖a‖`
    | some (_normedAddGroup_E, pa) =>
      assertInstancesCommute
      return .positive q(norm_pos_iff.2 $pa)
    -- Else, return a proof of `0 ≤ ‖a‖`
    | none => return .nonnegative q(norm_nonneg $a)
  | _, _, _ => throwError "not `‖·‖`"

end Mathlib.Meta.Positivity
