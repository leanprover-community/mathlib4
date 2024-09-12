/-
Copyright (c) 2024 Edward Watine and Alvan Caleb Arulandu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edward Watine and Alvan Caleb Arulandu
-/

import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.InfiniteSum
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Finset.NoncommProd
import Mathlib.Topology.Algebra.Algebra


variable {𝕂 : Type*} (𝔸 : Type*) [Field 𝕂] [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸]
  [TopologicalRing 𝔸]

open Nat

/-- `expSeries 𝕂 𝔸` is the `FormalMultilinearSeries` whose `n`-th term is the map
`(xᵢ) : 𝔸ⁿ ↦ (1/n! : 𝕂) • ∏ xᵢ`. Its sum is the exponential map `NormedSpace.exp 𝕂 : 𝔸 → 𝔸`. -/
def expSeries : FormalMultilinearSeries 𝕂 𝔸 𝔸 := fun n =>
  (n !⁻¹ : 𝕂) • ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 n 𝔸

noncomputable def gaussianHypergeometricSeries (a b c : 𝕂) : FormalMultilinearSeries 𝕂 𝔸 𝔸 :=
  fun n => ((n !⁻¹ : 𝕂) * (ascPochhammer 𝕂 n).eval a * (ascPochhammer 𝕂 n).eval b *
    ((ascPochhammer 𝕂 n).eval c)⁻¹ ) • ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 n 𝔸

variable {𝔸} (a b c : 𝕂)

noncomputable def gaussianHypergeometric (x : 𝔸) : 𝔸 :=
  (gaussianHypergeometricSeries 𝔸 a b c).sum x

@[inherit_doc]
notation "₂F₁" => gaussianHypergeometric

theorem gaussianHypergeometricSeries_apply_eq (x : 𝔸) (n : ℕ) :
    (gaussianHypergeometricSeries 𝔸 a b c n fun _ => x) =
    ((n !⁻¹ : 𝕂) * (ascPochhammer 𝕂 n).eval a * (ascPochhammer 𝕂 n).eval b *
    ((ascPochhammer 𝕂 n).eval c)⁻¹ ) • x ^ n :=
  by simp [gaussianHypergeometricSeries]

theorem gaussianHypergeometricSeries_apply_eq' (x : 𝔸) :
    (fun n => gaussianHypergeometricSeries 𝔸 a b c n fun _ => x) =
    fun n => ((n !⁻¹ : 𝕂) * (ascPochhammer 𝕂 n).eval a * (ascPochhammer 𝕂 n).eval b *
    ((ascPochhammer 𝕂 n).eval c)⁻¹ ) • x ^ n :=
  by simp [gaussianHypergeometricSeries]

theorem gaussianHypergeometric_sum_eq (x : 𝔸) : (gaussianHypergeometricSeries 𝔸 a b c).sum x =
    ∑' n : ℕ, ((n !⁻¹ : 𝕂) * (ascPochhammer 𝕂 n).eval a * (ascPochhammer 𝕂 n).eval b *
    ((ascPochhammer 𝕂 n).eval c)⁻¹ ) • x ^ n :=
  tsum_congr fun n => gaussianHypergeometricSeries_apply_eq a b c x n

theorem gaussianHypergeometric_eq_tsum : ₂F₁ a b c =
    fun (x : 𝔸) => ∑' n : ℕ, ((n !⁻¹ : 𝕂) * (ascPochhammer 𝕂 n).eval a *
    (ascPochhammer 𝕂 n).eval b * ((ascPochhammer 𝕂 n).eval c)⁻¹ ) • x ^ n :=
  funext (gaussianHypergeometric_sum_eq a b c)

theorem gaussianHypergeometricSeries_apply_zero (n : ℕ) :
    (gaussianHypergeometricSeries 𝔸 a b c n fun _ => (0:𝔸)) =
    Pi.single (f := fun _ => 𝔸) 0 1 n := by
  rw [gaussianHypergeometricSeries_apply_eq]
  cases n <;> simp

@[simp]
theorem gaussianHypergeometric_zero : ₂F₁ a b c (0 : 𝔸) = 1 := by
  simp [gaussianHypergeometric_eq_tsum, ←gaussianHypergeometricSeries_apply_eq,
    gaussianHypergeometricSeries_apply_zero]

@[simp]
theorem gaussianHypergeometric_op [T2Space 𝔸] (x : 𝔸) :
    ₂F₁ a b c (MulOpposite.op x) = MulOpposite.op (₂F₁ a b c x) := by
  simp [gaussianHypergeometric, gaussianHypergeometric_sum_eq, ←MulOpposite.op_pow,
     ←MulOpposite.op_smul, tsum_op]

@[simp]
theorem gaussianHypergeometric_unop [T2Space 𝔸] (x : 𝔸ᵐᵒᵖ) :
    ₂F₁ a b c (MulOpposite.unop x) = MulOpposite.unop (₂F₁ a b c x) := by
  simp [gaussianHypergeometric, gaussianHypergeometric_sum_eq, ←MulOpposite.unop_pow,
     ←MulOpposite.unop_smul, tsum_unop]

theorem gaussianHypergeometricSeries_symm :
    gaussianHypergeometricSeries 𝔸 a b c = gaussianHypergeometricSeries 𝔸 b a c := by
    ext
    simp [gaussianHypergeometricSeries]
    nth_rewrite 2 [mul_assoc]
    nth_rewrite 3 [mul_comm]
    rw [←mul_assoc]

private def negativeInts := {(k : 𝕂) | ∃ kn : ℤ, kn ≤ 0 ∧ k = kn}

theorem ascPochhammer_eq_zero_iff (n : ℕ) (k : 𝕂) :
    (ascPochhammer 𝕂 n).eval k = 0 ↔ ∃ kn : ℤ, kn ≤ 0 ∧ k = kn ∧ n ≥ 1 - kn := by
  induction n with
  | zero =>
    simp only [ascPochhammer_zero, Polynomial.eval_one, one_ne_zero, CharP.cast_eq_zero, ge_iff_le,
      Left.neg_nonpos_iff, false_iff, not_exists, not_and, not_le]
    by_contra! hx
    let ⟨x, hx, _, hx'⟩ := hx
    linarith
  | succ n ih =>
    rewrite [ascPochhammer_succ_eval]
    constructor
    · intro zero
      simp only [_root_.mul_eq_zero] at zero
      cases zero with
      | inl h =>
        have ⟨kn, hkn, kkn⟩ := ih.1 h
        exact ⟨kn, hkn, kkn.1, le_trans kkn.2 <| cast_le.2 <| Nat.le_succ n ⟩
      | inr h =>
        refine ⟨-n, by linarith, ?_, (by simp; linarith)⟩
        simpa only [Int.cast_neg, Int.cast_natCast, eq_neg_iff_add_eq_zero]
    · intro ⟨kn, hkn, kkn⟩
      rewrite [_root_.mul_eq_zero, or_iff_not_imp_left]
      intro np
      have hp := not_exists.1 <| (not_iff_not.2 ih).1 np
      push_neg at hp
      have hnx' := hp kn hkn kkn.1
      rewrite [Nat.cast_add_one] at kkn
      have : kn = -n := by linarith
      rw [kkn.1, this]
      simp

lemma gaussianHypergeometricSeries_eq_zero_of_nonpos_int (n : ℕ)
    (habc : ∃ kn : ℤ, kn ≤ 0 ∧ (a = kn ∨ b = kn ∨ c = kn) ∧ n ≥ 1 - kn) :
    gaussianHypergeometricSeries 𝔸 a b c n = 0 := by
  rewrite [gaussianHypergeometricSeries]
  have ⟨kn, hkn, kkn, hn⟩ := habc
  repeat
    try cases' kkn with h kkn
    ext
    simp [(ascPochhammer_eq_zero_iff n _).2 ⟨kn, hkn, h, hn⟩]
  ext
  simp [(ascPochhammer_eq_zero_iff n _).2 ⟨kn, hkn, kkn, hn⟩]


variable {𝕂 : Type*} (𝔸 𝔹 : Type*) [RCLike 𝕂] [NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸]
    [NormOneClass 𝔸] (a b c : 𝕂)

open Asymptotics Filter Real Set

#check 𝕂

lemma gaussianHypergeometricSeries_succ_norm_div_norm (n : ℕ)
    (ha : ¬∃ kn : ℤ, kn ≤ 0 ∧ a = kn ∧ n ≥ 1 - kn) (hb : ¬∃ kn : ℤ, kn ≤ 0 ∧ b = kn ∧ n ≥ 1 - kn)
    (hc : ¬∃ kn : ℤ, kn ≤ 0 ∧ c = kn ∧ n ≥ 1 - kn) : ‖gaussianHypergeometricSeries 𝔸 a b c (n+1)‖ /
    ‖gaussianHypergeometricSeries 𝔸 a b c n‖ = ‖a + n‖ * ‖b + n‖ * ‖c + n‖⁻¹ * ‖1 + (n : 𝕂)‖⁻¹ := by
  simp [gaussianHypergeometricSeries, factorial_succ, ascPochhammer_succ_eval]
  rewrite [norm_smul (x:=ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 (n + 1) 𝔸),
    norm_smul (x:=ContinuousMultilinearMap.mkPiAlgebraFin 𝕂 n 𝔸)]
  simp only [norm_mul, norm_inv, ContinuousMultilinearMap.norm_mkPiAlgebraFin, mul_one]
  ring_nf
  simp only [inv_inv]
  have : ‖(n ! : 𝕂)‖⁻¹ * ‖1 + (n : 𝕂)‖⁻¹ * ‖Polynomial.eval a (ascPochhammer 𝕂 n)‖ * ‖↑n + a‖ *
    ‖Polynomial.eval b (ascPochhammer 𝕂 n)‖ * ‖↑n + b‖ * ‖↑n + c‖⁻¹ *
    ‖Polynomial.eval c (ascPochhammer 𝕂 n)‖⁻¹ * ‖(n ! : 𝕂)‖ *
    ‖Polynomial.eval a (ascPochhammer 𝕂 n)‖⁻¹ *
    ‖Polynomial.eval b (ascPochhammer 𝕂 n)‖⁻¹ * ‖Polynomial.eval c (ascPochhammer 𝕂 n)‖ =
    ‖(n ! : 𝕂)‖ * ‖(n ! : 𝕂)‖⁻¹ * ‖Polynomial.eval a (ascPochhammer 𝕂 n)‖ *
    ‖Polynomial.eval a (ascPochhammer 𝕂 n)‖⁻¹ * ‖Polynomial.eval b (ascPochhammer 𝕂 n)‖ *
    ‖Polynomial.eval b (ascPochhammer 𝕂 n)‖⁻¹ * ‖Polynomial.eval c (ascPochhammer 𝕂 n)‖ *
    ‖Polynomial.eval c (ascPochhammer 𝕂 n)‖⁻¹ * ‖↑n + a‖ * ‖↑n + b‖ * ‖↑n + c‖⁻¹ *
    ‖1 + (n : 𝕂)‖⁻¹ := by ring
  rewrite [this]
  repeat rewrite [DivisionRing.mul_inv_cancel, one_mul]
  ring
  all_goals rewrite [norm_ne_zero_iff]
  any_goals
    apply (not_iff_not.2 <| ascPochhammer_eq_zero_iff n _).2
    first | exact ha | exact hb | exact hc
  rw [cast_ne_zero]
  exact factorial_ne_zero n

theorem gaussianHypergeometric_nonpos_int_radius_top₁ (ha : a ∈ negativeInts) :
    (gaussianHypergeometricSeries 𝔸 a b c).radius = ⊤ := by
  have ⟨an, ha'⟩ := ha
  apply FormalMultilinearSeries.radius_eq_top_of_forall_image_add_eq_zero _ <| Int.toNat (1-an)
  intro m
  apply gaussianHypergeometricSeries_eq_zero_of_nonpos_int
  refine ⟨an, ha'.1, Or.inl ha'.2, ?_⟩
  rewrite [Nat.cast_add, Int.toNat_of_nonneg]
  all_goals linarith

theorem gaussianHypergeometric_nonpos_int_radius_top₂ (hb : b ∈ negativeInts) :
    (gaussianHypergeometricSeries 𝔸 a b c).radius = ⊤ := by
  rewrite [gaussianHypergeometricSeries_symm]
  exact gaussianHypergeometric_nonpos_int_radius_top₁ 𝔸 b a c hb

theorem gaussianHypergeometric_nonpos_int_radius_top₃ (hc : c ∈ negativeInts) :
    (gaussianHypergeometricSeries 𝔸 a b c).radius = ⊤ := by
  have ⟨cn, hc'⟩ := hc
  apply FormalMultilinearSeries.radius_eq_top_of_forall_image_add_eq_zero _ <| Int.toNat (1-cn)
  intro m
  apply gaussianHypergeometricSeries_eq_zero_of_nonpos_int
  refine ⟨cn, hc'.1, Or.inr <| Or.inr hc'.2, ?_⟩
  rewrite [Nat.cast_add, Int.toNat_of_nonneg]
  all_goals linarith


theorem gaussianHypergeometric_radius_eq_one :
    (gaussianHypergeometricSeries 𝔸 a b c).radius = 1 := by
  apply le_antisymm
  · refine ENNReal.le_of_forall_nnreal_lt (fun r hr ↦ ?_)
    rw [← ENNReal.coe_one, ENNReal.coe_le_coe]
    sorry
  · refine ENNReal.le_of_forall_nnreal_lt (fun r hr ↦ ?_)
    rw [← Nat.cast_one, ENNReal.coe_lt_natCast, Nat.cast_one] at hr
    apply FormalMultilinearSeries.le_radius_of_summable
    apply summable_of_ratio_norm_eventually_le
    · trivial
    · apply Filter.eventually_atTop.2 -- uses hr for the r here when it should be anything
      ring_nf
      use 1 -- need to choose large enough n and figure out the asymptotics of the ratio
      intro n hn
      simp
      rw [← mul_assoc, mul_assoc, mul_comm]
      have hr_pos : r ≠ 0 := by sorry
      norm_cast -- cancel terms
      sorry
