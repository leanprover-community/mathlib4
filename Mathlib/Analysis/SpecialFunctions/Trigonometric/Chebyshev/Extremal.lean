/-
Copyright (c) 2025 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
-/
module

public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Chebyshev polynomials over the reals: some extremal properties

<<<<<<< HEAD
* Chebyshev polynomials have largest leading coefficient,
  following proof in https://math.stackexchange.com/a/978145/1277
* Chebyshev polynomials maximize iterated derivatives at 1 and beyond

## Main statements

* `leadingCoeff_le_of_bounded`: If P is a degree n polynomial and |P(x)|≤1 for all |x|≤1 then
  the leading coefficient of P is at most 2^(n-1)
* `leadingCoeff_eq_iff_of_bounded`: If P is a degree n polynomial and |P(x)|≤1 for all |x|≤1 then
  the leading coefficient of P equals 2^(n-1) iff P = T_n, the n'th Chebyshev polynomial
* `eval_iterate_derivative_le_of_bounded`: If P is a degree n polynomial and |P(x)|≤1 for all |x|≤1
  then for all x≥1 and all 0≠k≤n, P^(k)(x) ≤ T_n^(k)(x)
* `eval_iterate_derivative_eq_iff_of_bounded`: If P is a degree n polynomial and |P(x)|≤1 for all
  |x|≤1 then for all 0≠k≤n, P^(k)(x) = T_n^(k)(x) iff P = T_n
=======
Chebyshev polynomials have largest leading coefficient,
following proof in https://math.stackexchange.com/a/978145/1277

## Main statements

* leadingCoeff_le_of_bounded: If `P` is a real polynomial of degree at most `n` and `|P (x)| ≤ 1`
  for all `|x| ≤ 1` then the leading coefficient of `P` is at most `2 ^ (n-1)`
* leadingCoeff_eq_iff_of_bounded: When `n ≥ 2`, equality holds iff `P = T_n`

## Implementation

By monotonicity of `2 ^ (n-1)`, we can assume that `P` has degree exactly `n`.
Using Lagrange interpolation, we can give a formula for the leading coefficient of `P`
as a linear combination of the values of `P` on the Chebyshev nodes (leadingCoeff_eq_sum_node).
The Chebyshev polynomial `T_n` has value `±1` on the nodes, with the same signs as the
coefficients of the linear combination (leadingCoeff_eq_sum_node_coeff_pos).
Since `|P (x)| ≤ 1` on the nodes, this implies that the leading coefficient of `P` is bounded
by that of `T_n`, which is known to equal `2 ^ (n-1)`.
Moreover, equality holds iff `P` and `T_n` agree on the nodes, which implies that they coincide.
>>>>>>> ChebyshevExtremalLC
-/
@[expose] public section
namespace Polynomial.Chebyshev

open Polynomial Real

<<<<<<< HEAD
/-- For n ≠ 0 and i ≤ n, `chebyshevNode n i` is one of the extremal points of the Chebyhsev T
polynomial over the interval [-1, 1]. -/
noncomputable abbrev chebyshevNode (n i : ℕ) : ℝ := cos (i * π / n)

lemma chebyshevNode_eq_one {n : ℕ} : chebyshevNode n 0 = 1 := by simp [chebyshevNode]

lemma chebyshevNode_eq_neg_one {n : ℕ} (hn : n ≠ 0) : chebyshevNode n n = -1 := by
  have : n * π / n = π := by aesop
  simp [chebyshevNode, this]

lemma chebyshevNode_mem_Icc {n i : ℕ} : chebyshevNode n i ∈ Set.Icc (-1) 1 :=
  Set.mem_Icc.mpr ⟨neg_one_le_cos _, cos_le_one _⟩

lemma eval_T_real_chebyshevNode {n i : ℕ} (hn : n ≠ 0) :
    (T ℝ n).eval (chebyshevNode n i) = (-1) ^ i := by
  have : (n : ℤ) * (i * π / n) = i * π := by norm_cast; field
  rw [T_real_cos, this, cos_nat_mul_pi]

lemma strictAntiOn_chebyshevNode (n : ℕ) :
    StrictAntiOn (chebyshevNode n ·) (Finset.range (n + 1)) := by
=======
/-- For `n ≠ 0` and `i ≤ n`, node n i is one of the extremal points of the Chebyhsev T
polynomial over the interval `[-1, 1]`. -/
noncomputable def node (n i : ℕ) : ℝ := cos (i * π / n)

lemma node_eq_one {n : ℕ} : node n 0 = 1 := by simp [node]

lemma node_eq_neg_one {n : ℕ} (hn : n ≠ 0) : node n n = -1 := by
  have : n * π / n = π := by aesop
  simp [node, this]

lemma node_mem_Icc {n i : ℕ} : node n i ∈ Set.Icc (-1) 1 :=
  Set.mem_Icc.mpr ⟨neg_one_le_cos _, cos_le_one _⟩

lemma eval_T_real_node {n i : ℕ} (hn : n ≠ 0) :
    (T ℝ n).eval (node n i) = (-1) ^ i := by
  have : (n : ℤ) * (i * π / n) = i * π := by norm_cast; field
  rw [node, T_real_cos, this, cos_nat_mul_pi]

lemma strictAntiOn_node (n : ℕ) :
    StrictAntiOn (node n ·) (Finset.range (n + 1)) := by
>>>>>>> ChebyshevExtremalLC
  wlog! hn : n ≠ 0
  · simp [hn]
  refine strictAntiOn_cos.comp_strictMonoOn ?_ (fun x hx => Set.mem_Icc.mpr ⟨by positivity, ?_⟩)
  · apply StrictMono.strictMonoOn
    exact StrictMono.mul_const
      (StrictMono.mul_const Nat.strictMono_cast (by positivity)) (by positivity)
  rw [Finset.mem_coe, Finset.mem_range_succ_iff] at hx
  rw [mul_div_assoc]
  nth_rewrite 2 [← mul_div_cancel₀ π (Nat.cast_ne_zero.mpr hn)]
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hx) (by positivity)

<<<<<<< HEAD
lemma chebyshevNode_lt {n i j : ℕ} (hi : i ≤ n) (hj : j ≤ n) (hij : i < j) :
    chebyshevNode n j < chebyshevNode n i :=
  (strictAntiOn_chebyshevNode n) (Finset.mem_coe.mpr (Finset.mem_range_succ_iff.mpr hi))
    (Finset.mem_coe.mpr (Finset.mem_range_succ_iff.mpr hj)) hij

lemma zero_lt_prod_chebyshevNode_sub_chebyshevNode {n i : ℕ} (hi : i ≤ n) :
    0 < (-1) ^ i * ∏ j ∈ (Finset.range (n + 1)).erase i, (chebyshevNode n i - chebyshevNode n j) :=
=======
lemma node_lt {n i j : ℕ} (hj : j ≤ n) (hij : i < j) :
    node n j < node n i :=
  (strictAntiOn_node n) (Finset.mem_coe.mpr (Finset.mem_range_succ_iff.mpr (by grind)))
    (Finset.mem_coe.mpr (Finset.mem_range_succ_iff.mpr hj)) hij

lemma zero_lt_prod_node_sub_node {n i : ℕ} (hi : i ≤ n) :
    0 < (-1) ^ i * ∏ j ∈ (Finset.range (n + 1)).erase i, (node n i - node n j) :=
>>>>>>> ChebyshevExtremalLC
    by
  wlog! hn : n ≠ 0
  · replace hi : i = 0 := Nat.le_zero.mp (le_of_le_of_eq hi hn)
    simp [hn, hi]
<<<<<<< HEAD
  have h₁ : 0 < ∏ j ∈ Finset.range i, ((-1) * (chebyshevNode n i - chebyshevNode n j)) :=
    Finset.prod_pos (fun j hj => mul_pos_of_neg_of_neg neg_one_lt_zero <| sub_neg.mpr <|
    chebyshevNode_lt (le_trans (le_of_lt <| Finset.mem_range.mp hj) hi) hi
    (Finset.mem_range.mp hj))
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range] at h₁
  have h₂ : 0 < ∏ j ∈ Finset.Ioc i n, (chebyshevNode n i - chebyshevNode n j) :=
    Finset.prod_pos (fun j hj => sub_pos.mpr <|
      chebyshevNode_lt hi (Finset.mem_Ioc.mp hj).2 (Finset.mem_Ioc.mp hj).1)
=======
  have h₁ : 0 < ∏ j ∈ Finset.range i, ((-1) * (node n i - node n j)) :=
    Finset.prod_pos (fun j hj => mul_pos_of_neg_of_neg neg_one_lt_zero <| sub_neg.mpr <|
    node_lt hi (Finset.mem_range.mp hj))
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range] at h₁
  have h₂ : 0 < ∏ j ∈ Finset.Ioc i n, (node n i - node n j) :=
    Finset.prod_pos (fun j hj => sub_pos.mpr <|
      node_lt (Finset.mem_Ioc.mp hj).2 (Finset.mem_Ioc.mp hj).1)
>>>>>>> ChebyshevExtremalLC
  have union : (Finset.range (n + 1)).erase i = (Finset.range i) ∪ Finset.Ioc i n := by grind
  have disjoint : Disjoint (Finset.range i) (Finset.Ioc i n) := by grind [Finset.disjoint_iff_ne]
  rw [union, Finset.prod_union disjoint, ← mul_assoc]
  exact mul_pos h₁ h₂

private lemma negOnePow_mul_negOnePow_mul_cancel {α β : ℝ} {i : ℕ} :
    ((-1) ^ i * α) * ((-1) ^ i * β) = α * β := calc
  _ = ((-1) ^ i * (-1) ^ i) * α * β := by ring
  _ = α * β := by simp [← mul_pow]

private lemma negOnePow_mul_le {α : ℝ} {i : ℕ} (hα : α ∈ Set.Icc (-1) 1) : (-1) ^ i * α ≤ 1 := by
  apply le_of_abs_le
  rw [abs_mul, abs_neg_one_pow, one_mul]
  exact abs_le.mpr hα

<<<<<<< HEAD
theorem apply_le_apply_T_real {n : ℕ} {param : ℝ[X] → ℝ} {c : ℕ → ℝ}
    (hparam : (P : ℝ[X]) → P.degree = n → param P = ∑ i ≤ n, P.eval (chebyshevNode n i) * (c i))
    (hcnonneg : ∀ i ≤ n, 0 ≤ (-1) ^ i * (c i))
    {P : ℝ[X]} (hPdeg : P.degree = n) (hPbnd : ∀ x ∈ Set.Icc (-1) 1, P.eval x ∈ Set.Icc (-1) 1) :
    param P ≤ param (T ℝ n) := by
  wlog! hn : n ≠ 0
  · rw [hparam P hPdeg, hparam (T ℝ n) (degree_T ℝ n), hn, show Finset.Iic 0 = {0} by rfl,
      Nat.cast_zero, T_zero, Finset.sum_singleton, Finset.sum_singleton, chebyshevNode_eq_one,
      eval_one]
    exact mul_le_mul_of_nonneg_right (hPbnd 1 (by simp) |> Set.mem_Icc.mp).2
      (le_of_le_of_eq (hcnonneg 0 n.zero_le) (one_mul _))
  calc
    param P = ∑ i ≤ n, P.eval (chebyshevNode n i) * (c i) := hparam P hPdeg
    _ ≤ ∑ i ≤ n, (T ℝ n).eval (chebyshevNode n i) * (c i) := by
      refine Finset.sum_le_sum (fun i hi => ?_)
      calc
        P.eval (chebyshevNode n i) * (c i) =
          ((-1) ^ i * P.eval (chebyshevNode n i)) * ((-1) ^ i * (c i)) :=
          negOnePow_mul_negOnePow_mul_cancel.symm
        _ ≤ 1 * ((-1) ^ i * (c i)) :=
          mul_le_mul_of_nonneg_right (negOnePow_mul_le (hPbnd _ chebyshevNode_mem_Icc))
          (hcnonneg i (Finset.mem_Iic.mp hi))
        _ = (T ℝ n).eval (chebyshevNode n i) * (c i) := by
          rw [eval_T_real_chebyshevNode hn, one_mul]
    _ = param (T ℝ n) := (hparam (T ℝ n) (degree_T ℝ n)).symm

theorem apply_eq_apply_T_real_iff {n : ℕ} {param : ℝ[X] → ℝ} {c : ℕ → ℝ}
    (hparam : (P : ℝ[X]) → P.degree = n → param P = ∑ i ≤ n, P.eval (chebyshevNode n i) * (c i))
    (hcpos : ∀ i ≤ n, 0 < (-1) ^ i * (c i))
    {P : ℝ[X]} (hPdeg : P.degree = n) (hPbnd : ∀ x ∈ Set.Icc (-1) 1, P.eval x ∈ Set.Icc (-1) 1) :
    (param P = param (T ℝ n)) ↔ P = T ℝ n := by
  refine ⟨fun h => ?_, by intro h; rw [h]⟩
  wlog! hn : n ≠ 0
  · rw [hparam P hPdeg, hparam (T ℝ n) (degree_T ℝ n), hn, show Finset.Iic 0 = {0} by rfl,
      Nat.cast_zero, T_zero, Finset.sum_singleton, Finset.sum_singleton, chebyshevNode_eq_one,
      eval_one, one_mul] at h
=======
/-- For a polynomial P and coefficient function c, param n c P is a linear combination of
P evaluated at the n'th order Chebyshev nodes, with coefficients taken from c. -/
noncomputable def param (n : ℕ) (c : ℕ → ℝ) (P : ℝ[X]) := ∑ i ≤ n, P.eval (node n i) * (c i)

theorem apply_le_apply_T_real {n : ℕ} {c : ℕ → ℝ}
    (hcnonneg : ∀ i ≤ n, 0 ≤ (-1) ^ i * (c i))
    {P : ℝ[X]} (hPbnd : ∀ x ∈ Set.Icc (-1) 1, P.eval x ∈ Set.Icc (-1) 1) :
    param n c P ≤ param n c (T ℝ n) := by
  rw [param, param]
  wlog! hn : n ≠ 0
  · rw [hn, show Finset.Iic 0 = {0} by rfl, Nat.cast_zero, T_zero,
      Finset.sum_singleton, Finset.sum_singleton, node_eq_one, eval_one]
    exact mul_le_mul_of_nonneg_right (hPbnd 1 (by simp) |> Set.mem_Icc.mp).2
      (le_of_le_of_eq (hcnonneg 0 n.zero_le) (one_mul _))
  calc
    ∑ i ≤ n, P.eval (node n i) * (c i) ≤ ∑ i ≤ n, (T ℝ n).eval (node n i) * (c i) := by
      refine Finset.sum_le_sum (fun i hi => ?_)
      calc
        P.eval (node n i) * (c i) =
          ((-1) ^ i * P.eval (node n i)) * ((-1) ^ i * (c i)) :=
          negOnePow_mul_negOnePow_mul_cancel.symm
        _ ≤ 1 * ((-1) ^ i * (c i)) :=
          mul_le_mul_of_nonneg_right (negOnePow_mul_le (hPbnd _ node_mem_Icc))
          (hcnonneg i (Finset.mem_Iic.mp hi))
        _ = (T ℝ n).eval (node n i) * (c i) := by
          rw [eval_T_real_node hn, one_mul]

theorem apply_eq_apply_T_real_iff {n : ℕ} {c : ℕ → ℝ}
    (hcpos : ∀ i ≤ n, 0 < (-1) ^ i * (c i))
    {P : ℝ[X]} (hPdeg : P.degree = n) (hPbnd : ∀ x ∈ Set.Icc (-1) 1, P.eval x ∈ Set.Icc (-1) 1) :
    (param n c P = param n c (T ℝ n)) ↔ P = T ℝ n := by
  refine ⟨fun h => ?_, by intro h; rw [h]⟩
  rw [param, param] at h
  wlog! hn : n ≠ 0
  · rw [hn, show Finset.Iic 0 = {0} by rfl, Nat.cast_zero, T_zero, Finset.sum_singleton,
      Finset.sum_singleton, node_eq_one, eval_one, one_mul] at h
>>>>>>> ChebyshevExtremalLC
    rw [hn, Nat.cast_zero] at hPdeg
    rw [hn, Nat.cast_zero, T_zero]
    have eval_P_one : P.eval 1 = 1 :=
      (mul_eq_right₀ (ne_of_lt <| lt_of_lt_of_eq (hcpos 0 n.zero_le) (one_mul _)).symm).mp h
    rw [eq_C_of_degree_eq_zero hPdeg, eval_C] at eval_P_one
    rw [eq_C_of_degree_eq_zero hPdeg, eval_P_one, C_1]
<<<<<<< HEAD
  apply eq_of_degrees_lt_of_eval_finset_eq ((Finset.range (n + 1)).image (chebyshevNode n ·))
  · rw [hPdeg, Nat.cast_lt, Finset.card_image_of_injOn (strictAntiOn_chebyshevNode n).injOn,
      Finset.card_range, Nat.lt_succ_iff]
  · rw [degree_T, Int.natAbs_natCast, Nat.cast_lt,
      Finset.card_image_of_injOn (strictAntiOn_chebyshevNode n).injOn,
      Finset.card_range, Nat.lt_succ_iff]
  rw [hparam P hPdeg, hparam (T ℝ n) (degree_T ℝ n)] at h
=======
  apply eq_of_degrees_lt_of_eval_finset_eq ((Finset.range (n + 1)).image (node n ·))
  · rw [hPdeg, Nat.cast_lt, Finset.card_image_of_injOn (strictAntiOn_node n).injOn,
      Finset.card_range, Nat.lt_succ_iff]
  · rw [degree_T, Int.natAbs_natCast, Nat.cast_lt,
      Finset.card_image_of_injOn (strictAntiOn_node n).injOn,
      Finset.card_range, Nat.lt_succ_iff]
>>>>>>> ChebyshevExtremalLC
  replace h := ge_of_eq h
  contrapose! h
  obtain ⟨x, hx, hPx⟩ := h
  obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
  replace hi := Finset.mem_Iic.mpr (Finset.mem_range_succ_iff.mp hi)
<<<<<<< HEAD
  suffices  ∑ i ≤ n, ((-1) ^ i * P.eval (chebyshevNode n i)) * ((-1) ^ i * c i) <
    ∑ i≤ n, ((-1) ^ i * (T ℝ n).eval (chebyshevNode n i)) * ((-1) ^ i * c i) by
    simp_rw [negOnePow_mul_negOnePow_mul_cancel] at this
    exact this
  have h_le {i : ℕ} (hi : i ∈ Finset.Iic n) :
    (-1) ^ i * P.eval (chebyshevNode n i) * ((-1) ^ i * c i) ≤
    (-1) ^ i * (T ℝ n).eval (chebyshevNode n i)  * ((-1) ^ i * c i) := by
    refine mul_le_mul_of_nonneg_right ?_ (le_of_lt (hcpos i (Finset.mem_Iic.mp hi)))
    rw [eval_T_real_chebyshevNode hn, ← neg_pow', neg_neg, one_pow]
    exact negOnePow_mul_le (hPbnd _ chebyshevNode_mem_Icc)
=======
  suffices  ∑ i ≤ n, ((-1) ^ i * P.eval (node n i)) * ((-1) ^ i * c i) <
    ∑ i≤ n, ((-1) ^ i * (T ℝ n).eval (node n i)) * ((-1) ^ i * c i) by
    simp_rw [negOnePow_mul_negOnePow_mul_cancel] at this
    exact this
  have h_le {i : ℕ} (hi : i ∈ Finset.Iic n) :
    (-1) ^ i * P.eval (node n i) * ((-1) ^ i * c i) ≤
    (-1) ^ i * (T ℝ n).eval (node n i)  * ((-1) ^ i * c i) := by
    refine mul_le_mul_of_nonneg_right ?_ (le_of_lt (hcpos i (Finset.mem_Iic.mp hi)))
    rw [eval_T_real_node hn, ← neg_pow', neg_neg, one_pow]
    exact negOnePow_mul_le (hPbnd _ node_mem_Icc)
>>>>>>> ChebyshevExtremalLC
  refine Finset.sum_lt_sum (fun i hi => h_le hi) ⟨i, hi, lt_of_le_of_ne (h_le hi) ?_⟩
  have := ne_of_lt (hcpos i (Finset.mem_Iic.mp hi))
  grind => ring

<<<<<<< HEAD
theorem leadingCoeff_eq_sum_chebyshevNode (n : ℕ) (P : ℝ[X]) (hP : P.degree = n) :
    P.leadingCoeff = ∑ i ≤ n, (P.eval (chebyshevNode n i)) *
    (∏ j ∈ (Finset.range (n + 1)).erase i, (chebyshevNode n i - chebyshevNode n j))⁻¹ := by
  rw [Lagrange.leadingCoeff_eq_sum (strictAntiOn_chebyshevNode n).injOn (by simp [hP]),
    show Finset.range (n + 1) = Finset.Iic n by grind]
  rfl

theorem leadingCoeff_eq_sum_chebyshevNode_coeff_pos {n i : ℕ} (hi : i ≤ n) :
    0 < (-1) ^ i *
    (∏ j ∈ (Finset.range (n + 1)).erase i, (chebyshevNode n i - chebyshevNode n j))⁻¹ := by
  have := inv_pos_of_pos <| zero_lt_prod_chebyshevNode_sub_chebyshevNode hi
  rwa [mul_inv, ← inv_pow, inv_neg_one] at this

theorem leadingCoeff_le_of_bounded {n : ℕ} {P : ℝ[X]}
    (hPdeg : P.degree = n) (hPbnd : ∀ x ∈ Set.Icc (-1) 1, P.eval x ∈ Set.Icc (-1) 1) :
    P.leadingCoeff ≤ 2 ^ (n - 1) := by
  convert apply_le_apply_T_real (leadingCoeff_eq_sum_chebyshevNode n)
    (fun i hi => le_of_lt <| leadingCoeff_eq_sum_chebyshevNode_coeff_pos hi) hPdeg hPbnd
  simp

theorem leadingCoeff_eq_iff_of_bounded {n : ℕ} {P : ℝ[X]}
    (hPdeg : P.degree = n) (hPbnd : ∀ x ∈ Set.Icc (-1) 1, P.eval x ∈ Set.Icc (-1) 1) :
    P.leadingCoeff = 2 ^ (n - 1) ↔ P = T ℝ n := by
  convert apply_eq_apply_T_real_iff (leadingCoeff_eq_sum_chebyshevNode n)
    (fun i hi => leadingCoeff_eq_sum_chebyshevNode_coeff_pos hi) hPdeg hPbnd
  simp

theorem eval_iterate_derivative_eq_sum_chebyshevNode {n k : ℕ} (hk : k ≤ n) (x : ℝ)
    (P : ℝ[X]) (hP : P.degree = n) :
    (derivative^[k] P).eval x =
      ∑ i ≤ n, P.eval (chebyshevNode n i) *
        (k.factorial *
        (∏ j ∈ (Finset.range (n + 1)).erase i, ((chebyshevNode n i) - (chebyshevNode n j)))⁻¹ *
        ∑ t ∈ ((Finset.range (n + 1)).erase i).powersetCard (n - k),
        ∏ a ∈ t, (x - chebyshevNode n a)) := by
  rw [Lagrange.eval_iterate_derivative_eq_sum (strictAntiOn_chebyshevNode n).injOn (by simp [hP])
    (le_of_le_of_eq (Nat.cast_le.mpr hk) hP.symm) x, Finset.mul_sum, Finset.card_range,
    Nat.add_sub_add_right, show Finset.range (n + 1) = Finset.Iic n by grind]
  congr! 1 with i hi
  ring

theorem eval_iterate_derivative_eq_sum_chebyshevNode_coeff_pos
    {n k i : ℕ} (hk₁ : 0 < k) (hk₂ : k ≤ n) (hi : i ≤ n) {x : ℝ} (hx : 1 ≤ x) :
    0 < (-1) ^ i *
      (k.factorial *
      (∏ j ∈ (Finset.range (n + 1)).erase i, ((chebyshevNode n i) - (chebyshevNode n j)))⁻¹ *
      ∑ t ∈ ((Finset.range (n + 1)).erase i).powersetCard (n - k),
      ∏ a ∈ t, (x - chebyshevNode n a)) := by
  rw [← mul_assoc]
  refine mul_pos ?_ (Finset.sum_pos' ?_ ?_)
  · rw [← mul_assoc, mul_comm (a := (-1) ^ i), mul_assoc]
    exact mul_pos (Nat.cast_pos.mpr <| Nat.factorial_pos k)
      (leadingCoeff_eq_sum_chebyshevNode_coeff_pos hi)
  · refine fun t _ => Finset.prod_nonneg (fun a _ => ?_)
    have : chebyshevNode n a ≤ 1 := cos_le_one _
    linarith
  · have : ∃ s ⊆ (Finset.range (n + 1)).erase i, s.card = n - k ∧ 0 ∉ s := by
      by_cases 1 ≤ i ∧ i ≤ n - k
      case neg => exact ⟨Finset.Icc 1 (n - k), by grind, by grind [Nat.card_Icc], by simp⟩
      case pos => exact ⟨(Finset.Icc 1 (n - k + 1)).erase i, by grind, by grind [Nat.card_Icc],
        by simp⟩
    obtain ⟨s, hs, hscard, hsn⟩ := this
    refine ⟨s, by simp [hs, hscard], Finset.prod_pos (fun a ha => ?_)⟩
    have : chebyshevNode n a < 1 := by
      rw [← chebyshevNode_eq_one (n := n)]
      apply chebyshevNode_lt (Nat.zero_le _) (by grind) (by grind)
    linarith

theorem eval_iterate_derivative_le_of_bounded {n : ℕ} {P : ℝ[X]}
    {k : ℕ} (hk₁ : 0 < k) (hk₂ : k ≤ n) {x : ℝ} (hx : 1 ≤ x)
    (hPdeg : P.degree = n) (hPbnd : ∀ x ∈ Set.Icc (-1) 1, P.eval x ∈ Set.Icc (-1) 1) :
    (derivative^[k] P).eval x ≤ (derivative^[k] (T ℝ n)).eval x :=
  apply_le_apply_T_real (eval_iterate_derivative_eq_sum_chebyshevNode hk₂ x)
    (fun _ hi => le_of_lt <| eval_iterate_derivative_eq_sum_chebyshevNode_coeff_pos hk₁ hk₂ hi hx)
    hPdeg hPbnd

theorem eval_iterate_derivative_eq_iff_of_bounded {n : ℕ} {P : ℝ[X]}
    {k : ℕ} (hk₁ : 0 < k) (hk₂ : k ≤ n) {x : ℝ} (hx : 1 ≤ x)
    (hPdeg : P.degree = n) (hPbnd : ∀ x ∈ Set.Icc (-1) 1, P.eval x ∈ Set.Icc (-1) 1) :
    (derivative^[k] P).eval x = (derivative^[k] (T ℝ n)).eval x ↔ P = T ℝ n :=
  apply_eq_apply_T_real_iff (eval_iterate_derivative_eq_sum_chebyshevNode hk₂ x)
    (fun _ hi => eval_iterate_derivative_eq_sum_chebyshevNode_coeff_pos hk₁ hk₂ hi hx)
    hPdeg hPbnd
=======
/-- Coefficients use to reproduce the leading coefficient of a polynomial given its values on the
Chebyshev nodes. -/
private noncomputable def leadingCoeff_c (n i : ℕ) :=
    (∏ j ∈ (Finset.range (n + 1)).erase i, (node n i - node n j))⁻¹

private theorem leadingCoeff_eq_sum_node {n : ℕ} {P : ℝ[X]} (hP : P.degree = n) :
    param n (leadingCoeff_c n) P = P.leadingCoeff := by
  simp_rw [param, leadingCoeff_c]
  rw [Lagrange.leadingCoeff_eq_sum (strictAntiOn_node n).injOn (by simp [hP]),
    show Finset.range (n + 1) = Finset.Iic n by grind]
  rfl

private theorem leadingCoeff_eq_sum_node_coeff_pos {n i : ℕ} (hi : i ≤ n) :
    0 < (-1) ^ i * leadingCoeff_c n i := by
  have := inv_pos_of_pos <| zero_lt_prod_node_sub_node hi
  rwa [mul_inv, ← inv_pow, inv_neg_one] at this

theorem leadingCoeff_le_of_bounded' {n : ℕ} {P : ℝ[X]}
    (hPdeg : P.degree = n) (hPbnd : ∀ x ∈ Set.Icc (-1) 1, P.eval x ∈ Set.Icc (-1) 1) :
    P.leadingCoeff ≤ 2 ^ (n - 1) := by
  rw [← leadingCoeff_eq_sum_node hPdeg]
  convert apply_le_apply_T_real
    (fun i hi => le_of_lt <| leadingCoeff_eq_sum_node_coeff_pos hi) hPbnd
  simp [leadingCoeff_eq_sum_node]

theorem leadingCoeff_le_of_bounded {n : ℕ} {P : ℝ[X]}
    (hPdeg : P.degree ≤ n) (hPbnd : ∀ x ∈ Set.Icc (-1) 1, P.eval x ∈ Set.Icc (-1) 1) :
    P.leadingCoeff ≤ 2 ^ (n - 1) := by
  by_cases P = 0
  case pos hP => simp [hP]
  case neg hP =>
    lift P.degree to ℕ using degree_ne_bot.mpr hP with d hd
    replace hPdeg : d ≤ n := (WithBot.coe_le rfl).mp hPdeg
    calc P.leadingCoeff ≤ 2 ^ (d - 1) := leadingCoeff_le_of_bounded' hd.symm hPbnd
      _ ≤ 2 ^ (n - 1) := by gcongr; norm_num

theorem leadingCoeff_eq_iff_of_bounded' {n : ℕ} {P : ℝ[X]}
    (hPdeg : P.degree = n) (hPbnd : ∀ x ∈ Set.Icc (-1) 1, P.eval x ∈ Set.Icc (-1) 1) :
    P.leadingCoeff = 2 ^ (n - 1) ↔ P = T ℝ n := by
  rw [← leadingCoeff_eq_sum_node hPdeg]
  convert apply_eq_apply_T_real_iff (fun i hi => leadingCoeff_eq_sum_node_coeff_pos hi) hPdeg hPbnd
  simp [leadingCoeff_eq_sum_node]

theorem leadingCoeff_eq_iff_of_bounded {n : ℕ} {P : ℝ[X]} (hn : 2 ≤ n)
    (hPdeg : P.degree ≤ n) (hPbnd : ∀ x ∈ Set.Icc (-1) 1, P.eval x ∈ Set.Icc (-1) 1) :
    P.leadingCoeff = 2 ^ (n - 1) ↔ P = T ℝ n := by
  refine ⟨fun hP => ?_, fun hP => by simp [hP]⟩
  lift P.degree to ℕ with d hd
  · contrapose! hP
    rw [degree_eq_bot.mp hP, leadingCoeff_zero]
    positivity
  suffices n ≤ P.degree from (leadingCoeff_eq_iff_of_bounded' (by grind) hPbnd).mp hP
  replace hP := ge_of_eq hP
  contrapose! hP
  have : d - 1 < n - 1 := by grind [Nat.cast_withBot, WithBot.coe_le_coe, WithBot.coe_lt_coe]
  calc P.leadingCoeff ≤ 2 ^ (d - 1) := leadingCoeff_le_of_bounded' hd.symm hPbnd
  _ < 2 ^ (n - 1) := by gcongr; norm_num
>>>>>>> ChebyshevExtremalLC

end Polynomial.Chebyshev
