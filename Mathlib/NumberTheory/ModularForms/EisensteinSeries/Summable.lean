/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Analysis.NormedSpace.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Order.Interval.Finset.Box
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Uniform convergence of Eisenstein series

We show that the sum of `eisSummand` converges locally uniformly on `ℍ` to the Eisenstein series
of weight `k` and level `Γ(N)` with congruence condition `a : Fin 2 → ZMod N`.

## Outline of argument

The key lemma `r_mul_max_le` shows that, for `z ∈ ℍ` and `c, d ∈ ℤ` (not both zero),
`|c z + d|` is bounded below by `r z * max (|c|, |d|)`, where `r z` is an explicit function of `z`
(independent of `c, d`) satisfying `0 < r z < 1` for all `z`.

We then show in `summable_one_div_rpow_max` that the sum of `max (|c|, |d|) ^ (-k)` over
`(c, d) ∈ ℤ × ℤ` is convergent for `2 < k`. This is proved by decomposing `ℤ × ℤ` using the
`Finset.box` lemmas.
-/

noncomputable section

open Complex UpperHalfPlane Set Finset CongruenceSubgroup Topology Filter Asymptotics

open scoped UpperHalfPlane Topology BigOperators Nat


variable (z : ℍ)

namespace EisensteinSeries

lemma norm_eq_max_natAbs (x : Fin 2 → ℤ) : ‖x‖ = max (x 0).natAbs (x 1).natAbs := by
  rw [← coe_nnnorm, ← NNReal.coe_natCast, NNReal.coe_inj, Nat.cast_max]
  refine eq_of_forall_ge_iff fun c ↦ ?_
  simp only [pi_nnnorm_le_iff, Fin.forall_fin_two, max_le_iff, NNReal.natCast_natAbs]

lemma norm_symm (x y : ℤ) : ‖![x, y]‖ = ‖![y, x]‖ := by
  simp [EisensteinSeries.norm_eq_max_natAbs, max_comm]

theorem abs_le_left_of_norm (m n : ℤ) : |n| ≤ ‖![n, m]‖ := by
  simp only [EisensteinSeries.norm_eq_max_natAbs, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Nat.cast_max, le_sup_iff]
  left
  rw [Int.abs_eq_natAbs]
  rfl

theorem le_left_of_norm (m n : ℤ) : n ≤ ‖![n, m]‖ := by
  apply le_trans _ (abs_le_left_of_norm m n)
  norm_cast
  exact le_abs_self n

theorem abs_le_right_of_norm (m n : ℤ) : |m| ≤ ‖![n, m]‖ := by
  simp only [EisensteinSeries.norm_eq_max_natAbs, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Nat.cast_max, le_sup_iff]
  right
  rw [Int.abs_eq_natAbs]
  rfl

theorem le_right_of_norm (m n : ℤ) : m ≤ ‖![n, m]‖ := by
  apply le_trans _ (abs_le_right_of_norm m n)
  norm_cast
  exact le_abs_self m

section bounding_functions

/-- Auxiliary function used for bounding Eisenstein series, defined as
  `z.im ^ 2 / (z.re ^ 2 + z.im ^ 2)`. -/
def r1 : ℝ := z.im ^ 2 / (z.re ^ 2 + z.im ^ 2)

lemma r1_eq : r1 z = 1 / ((z.re / z.im) ^ 2 + 1) := by
  rw [div_pow, div_add_one (by positivity), one_div_div, r1]

lemma r1_pos : 0 < r1 z := by
  dsimp only [r1]
  positivity

/-- For `c, d ∈ ℝ` with `1 ≤ d ^ 2`, we have `r1 z ≤ |c * z + d| ^ 2`. -/
lemma r1_aux_bound (c : ℝ) {d : ℝ} (hd : 1 ≤ d ^ 2) :
    r1 z ≤ (c * z.re + d) ^ 2 + (c * z.im) ^ 2 := by
  have H1 : (c * z.re + d) ^ 2 + (c * z.im) ^ 2 =
    c ^ 2 * (z.re ^ 2 + z.im ^ 2) + d * 2 * c * z.re + d ^ 2 := by ring
  have H2 : (c ^ 2 * (z.re ^ 2 + z.im ^ 2) + d * 2 * c * z.re + d ^ 2) * (z.re ^ 2 + z.im ^ 2)
    - z.im ^ 2 = (c * (z.re ^ 2 + z.im ^ 2) + d * z.re) ^ 2 + (d ^ 2 - 1) * z.im ^ 2 := by ring
  rw [r1, H1, div_le_iff₀ (by positivity), ← sub_nonneg, H2]
  exact add_nonneg (sq_nonneg _) (mul_nonneg (sub_nonneg.mpr hd) (sq_nonneg _))

/-- This function is used to give an upper bound on the summands in Eisenstein series; it is
defined by `z ↦ min z.im √(z.im ^ 2 / (z.re ^ 2 + z.im ^ 2))`. -/
def r : ℝ := min z.im √(r1 z)

lemma r_pos : 0 < r z := by
  simp only [r, lt_min_iff, im_pos, Real.sqrt_pos, r1_pos, and_self]

lemma r_lower_bound_on_verticalStrip {A B : ℝ} (h : 0 < B) (hz : z ∈ verticalStrip A B) :
    r ⟨⟨A, B⟩, h⟩ ≤ r z := by
  apply min_le_min hz.2
  rw [Real.sqrt_le_sqrt_iff (by apply (r1_pos z).le)]
  simp only [r1_eq, div_pow, one_div]
  rw [inv_le_inv₀ (by positivity) (by positivity), add_le_add_iff_right, ← even_two.pow_abs]
  gcongr
  exacts [hz.1, hz.2]

lemma auxbound1 {c : ℝ} (d : ℝ) (hc : 1 ≤ c ^ 2) : r z ≤ ‖c * (z : ℂ) + d‖ := by
  rcases z with ⟨z, hz⟩
  have H1 : z.im ≤ √((c * z.re + d) ^ 2 + (c * z).im ^ 2) := by
    rw [Real.le_sqrt' hz, im_ofReal_mul, mul_pow]
    exact (le_mul_of_one_le_left (sq_nonneg _) hc).trans <| le_add_of_nonneg_left (sq_nonneg _)
  simpa only [r, norm_def, normSq_apply, add_re, re_ofReal_mul, coe_re, ← pow_two, add_im, mul_im,
    coe_im, ofReal_im, zero_mul, add_zero, min_le_iff] using Or.inl H1

lemma auxbound2 (c : ℝ) {d : ℝ} (hd : 1 ≤ d ^ 2) : r z ≤ ‖c * (z : ℂ) + d‖ := by
  have H1 : √(r1 z) ≤ √((c * z.re + d) ^ 2 + (c * z.im) ^ 2) :=
    (Real.sqrt_le_sqrt_iff (by positivity)).mpr (r1_aux_bound _ _ hd)
  simpa only [r, norm_def, normSq_apply, add_re, re_ofReal_mul, coe_re, ofReal_re, ← pow_two,
    add_im, im_ofReal_mul, coe_im, ofReal_im, add_zero, min_le_iff] using Or.inr H1

lemma div_max_sq_ge_one (x : Fin 2 → ℤ) (hx : x ≠ 0) :
    1 ≤ (x 0 / ‖x‖) ^ 2 ∨ 1 ≤ (x 1 / ‖x‖) ^ 2 := by
  refine (max_choice (x 0).natAbs (x 1).natAbs).imp (fun H0 ↦ ?_) (fun H1 ↦ ?_)
  · have : x 0 ≠ 0 := by
      rwa [← norm_ne_zero_iff, norm_eq_max_natAbs, H0, Nat.cast_ne_zero, Int.natAbs_ne_zero] at hx
    simp only [norm_eq_max_natAbs, H0, Int.cast_natAbs, Int.cast_abs, div_pow, sq_abs, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, Int.cast_eq_zero, this, div_self,
      le_refl]
  · have : x 1 ≠ 0 := by
      rwa [← norm_ne_zero_iff, norm_eq_max_natAbs, H1, Nat.cast_ne_zero, Int.natAbs_ne_zero] at hx
    simp only [norm_eq_max_natAbs, H1, Int.cast_natAbs, Int.cast_abs, div_pow, sq_abs, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, Int.cast_eq_zero, this, div_self,
      le_refl]

lemma r_mul_max_le {x : Fin 2 → ℤ} (hx : x ≠ 0) : r z * ‖x‖ ≤ ‖x 0 * (z : ℂ) + x 1‖ := by
  have hn0 : ‖x‖ ≠ 0 := by rwa [norm_ne_zero_iff]
  have h11 : x 0 * (z : ℂ) + x 1 = (x 0 / ‖x‖ * z + x 1 / ‖x‖) * ‖x‖ := by
    rw [div_mul_eq_mul_div, ← add_div, div_mul_cancel₀ _ (mod_cast hn0)]
  rw [norm_eq_max_natAbs, h11, norm_mul, norm_real, norm_norm, norm_eq_max_natAbs]
  gcongr
  · rcases div_max_sq_ge_one x hx with H1 | H2
    · simpa only [norm_eq_max_natAbs, ofReal_div, ofReal_intCast] using auxbound1 z (x 1 / ‖x‖) H1
    · simpa only [norm_eq_max_natAbs, ofReal_div, ofReal_intCast] using auxbound2 z (x 0 / ‖x‖) H2

/-- Upper bound for the summand `|c * z + d| ^ (-k)`, as a product of a function of `z` and a
function of `c, d`. -/
lemma summand_bound {k : ℝ} (hk : 0 ≤ k) (x : Fin 2 → ℤ) :
    ‖x 0 * (z : ℂ) + x 1‖ ^ (-k) ≤ (r z) ^ (-k) * ‖x‖ ^ (-k) := by
  by_cases hx : x = 0
  · simp only [hx, Pi.zero_apply, Int.cast_zero, zero_mul, add_zero, norm_zero]
    by_cases h : -k = 0
    · rw [h, Real.rpow_zero, Real.rpow_zero, one_mul]
    · rw [Real.zero_rpow h, mul_zero]
  · rw [← Real.mul_rpow (r_pos _).le (norm_nonneg _)]
    exact Real.rpow_le_rpow_of_nonpos (mul_pos (r_pos _) (norm_pos_iff.mpr hx)) (r_mul_max_le z hx)
      (neg_nonpos.mpr hk)

variable {z} in
lemma summand_bound_of_mem_verticalStrip {k : ℝ} (hk : 0 ≤ k) (x : Fin 2 → ℤ)
    {A B : ℝ} (hB : 0 < B) (hz : z ∈ verticalStrip A B) :
    ‖x 0 * (z : ℂ) + x 1‖ ^ (-k) ≤ r ⟨⟨A, B⟩, hB⟩ ^ (-k) * ‖x‖ ^ (-k) := by
  refine (summand_bound z hk x).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact Real.rpow_le_rpow_of_nonpos (r_pos _) (r_lower_bound_on_verticalStrip z hB hz)
    (neg_nonpos.mpr hk)

lemma linear_isBigO_r_right (c : ℤ) (z : ℍ) : (fun (d : ℤ) ↦ ((c : ℂ) * z + d)⁻¹) =O[cofinite]
    (fun d ↦ ((r z * ‖![c, d]‖))⁻¹) := by
    rw [Asymptotics.isBigO_iff']
    refine ⟨1, Real.zero_lt_one, ?_⟩
    filter_upwards with d
    simpa only [norm_inv, Nat.succ_eq_add_one, Nat.reduceAdd, mul_inv_rev, mul_comm, norm_mul,
      Real.norm_eq_abs, abs_eq_self.mpr (r_pos z).le, abs_norm, one_mul, ge_iff_le, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Real.rpow_neg_one] using
      EisensteinSeries.summand_bound z (k := 1) (by norm_num) ![c, d]

lemma linear_isBigO_r_left (d : ℤ) (z : ℍ) : (fun (c : ℤ) ↦ ((c : ℂ) * z + d)⁻¹) =O[cofinite]
    (fun c ↦ ((r z * ‖![c, d]‖))⁻¹) := by
    rw [Asymptotics.isBigO_iff']
    refine ⟨1, Real.zero_lt_one, ?_⟩
    filter_upwards with c
    simpa only [norm_inv, Nat.succ_eq_add_one, Nat.reduceAdd, mul_inv_rev, mul_comm, norm_mul,
      Real.norm_eq_abs, abs_eq_self.mpr (r_pos z).le, abs_norm, one_mul, ge_iff_le, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Real.rpow_neg_one] using
      EisensteinSeries.summand_bound z (k := 1) (by norm_num) ![c, d]

lemma linear_isBigO_right (c : ℤ) (z : ℍ) : (fun (d : ℤ) => ((c : ℂ) * z + d)⁻¹) =O[cofinite]
    fun n => ((n : ℝ)⁻¹) := by
  apply Asymptotics.IsBigO.trans (linear_isBigO_r_right c z)
  simp_rw [Asymptotics.isBigO_iff', eventually_iff_exists_mem]
  refine ⟨|(r z)|⁻¹, by simp [ne_of_gt (r_pos z)], {0}ᶜ,
    Set.Finite.compl_mem_cofinite (Set.finite_singleton 0), ?_⟩
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Nat.succ_eq_add_one, Nat.reduceAdd,
    mul_inv_rev, norm_mul, norm_inv, norm_norm, Real.norm_eq_abs, abs_norm, mul_comm]
  intro d _
  gcongr
  simpa using abs_le_right_of_norm d c

  lemma linear_isBigO_left (d : ℤ) (z : ℍ) : (fun (c : ℤ) => ((c : ℂ) * z + d)⁻¹) =O[cofinite]
    fun n => ((n : ℝ)⁻¹) := by
  apply Asymptotics.IsBigO.trans (linear_isBigO_r_left d z)
  simp_rw [Asymptotics.isBigO_iff', eventually_iff_exists_mem]
  refine ⟨|(r z)|⁻¹, by simp [ne_of_gt (r_pos z)], {0}ᶜ,
    Set.Finite.compl_mem_cofinite (Set.finite_singleton 0), ?_⟩
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Nat.succ_eq_add_one, Nat.reduceAdd,
    mul_inv_rev, norm_mul, norm_inv, norm_norm, Real.norm_eq_abs, abs_norm, mul_comm]
  intro c _
  gcongr
  simpa using abs_le_left_of_norm d c

end bounding_functions

/-- The function `ℤ ^ 2 → ℝ` given by `x ↦ ‖x‖ ^ (-k)` is summable if `2 < k`. We prove this by
splitting into boxes using `Finset.box`. -/
lemma summable_one_div_norm_rpow {k : ℝ} (hk : 2 < k) :
    Summable fun (x : Fin 2 → ℤ) ↦ ‖x‖ ^ (-k) := by
  rw [← (finTwoArrowEquiv _).symm.summable_iff, summable_partition _ Int.existsUnique_mem_box]
  · simp only [finTwoArrowEquiv_symm_apply, Function.comp_def]
    refine ⟨fun n ↦ (hasSum_fintype (β := box (α := ℤ × ℤ) n) _).summable, ?_⟩
    suffices Summable fun n : ℕ ↦ ∑' (_ : box (α := ℤ × ℤ) n), (n : ℝ) ^ (-k) by
      refine this.congr fun n ↦ tsum_congr fun p ↦ ?_
      simp only [← Int.mem_box.mp p.2, Nat.cast_max, norm_eq_max_natAbs, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons]
    simp only [tsum_fintype, univ_eq_attach, sum_const, card_attach, nsmul_eq_mul]
    apply ((Real.summable_nat_rpow.mpr (by linarith : 1 - k < -1)).mul_left
      8).of_norm_bounded_eventually_nat
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    rw [Int.card_box hn.ne', Real.norm_of_nonneg (by positivity), sub_eq_add_neg,
      Real.rpow_add (Nat.cast_pos.mpr hn), Real.rpow_one, Nat.cast_mul, Nat.cast_ofNat, mul_assoc]
  · exact fun n ↦ Real.rpow_nonneg (norm_nonneg _) _

lemma summable_of_inv_isBigO_riemannZeta {α : Type} [NormedField α] [CompleteSpace α]
    {f  : ℤ → α} {a : ℝ} (hab : 1 < a)
    (hf : (fun n => (f n)⁻¹) =O[cofinite] fun n => (|(n : ℝ)| ^ a)⁻¹) :
    Summable fun n => (f n)⁻¹ :=
    summable_of_isBigO
      (Summable.congr (Real.summable_abs_int_rpow hab) fun b ↦ Real.rpow_neg (abs_nonneg ↑b) a) hf

/-- This says that for `z : ℍ` the function `d : ℤ ↦ ((c z + d) ^ k)⁻¹ is Summable for `2 ≤ k`. -/
lemma linear_right_summable (z : ℍ) (c k : ℤ) (hk : 2 ≤ k) :
    Summable fun d : ℤ ↦ (((c : ℂ) * z + d) ^ k)⁻¹ := by
  apply summable_of_inv_isBigO_riemannZeta (a := k) (by norm_cast)
  lift k to ℕ using (by linarith)
  simp only [zpow_natCast, Int.cast_natCast, Real.rpow_natCast, ← inv_pow, ← abs_inv]
  apply Asymptotics.IsBigO.pow (Asymptotics.IsBigO.abs_right (linear_isBigO_right c z))

lemma linear_left_summable (z : ℍ) (d k : ℤ) (hk : 2 ≤ k) :
  Summable fun c : ℤ ↦ (((c : ℂ) * z + d) ^ k)⁻¹ := by
  apply ((linear_right_summable
    ⟨-1 /z, by simpa using UpperHalfPlane.pnat_div 1 z⟩ (-d) k hk).mul_left ((z : ℂ)^k)⁻¹).congr
  intro b
  rw [← mul_inv, ← mul_zpow]
  field_simp [UpperHalfPlane.ne_zero z, add_comm]

lemma summable_diff (z : ℍ) (c₁ c₂ : ℤ) :
    Summable fun (n : ℤ) => ((c₁ * (z : ℂ) - n) * (c₂ * z + n))⁻¹  := by
  apply summable_of_inv_isBigO_riemannZeta (a := 2) (by norm_cast)
  simp only [Real.rpow_two, sq_abs, abs_mul_abs_self, ← mul_inv, pow_two]
  simpa [sub_eq_add_neg] using Asymptotics.IsBigO.mul (linear_isBigO_right c₂ z)
    (linear_isBigO_right c₁ z).of_neg_int

end EisensteinSeries
