/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Mathlib.Algebra.Polynomial.Identities
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.MetricSpace.CauSeqFilter

/-!
# Hensel's lemma on ℤ_p

This file proves Hensel's lemma on ℤ_p, roughly following Keith Conrad's writeup:
<http://www.math.uconn.edu/~kconrad/blurbs/gradnumthy/hensel.pdf>

Hensel's lemma gives a simple condition for the existence of a root of a polynomial.

The proof and motivation are described in the paper
[R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019].

## References

* <http://www.math.uconn.edu/~kconrad/blurbs/gradnumthy/hensel.pdf>
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/Hensel%27s_lemma>

## Tags

p-adic, p adic, padic, p-adic integer
-/


noncomputable section

open Topology

-- We begin with some general lemmas that are used below in the computation.
theorem padic_polynomial_dist {p : ℕ} [Fact p.Prime] (F : Polynomial ℤ_[p]) (x y : ℤ_[p]) :
    ‖F.eval x - F.eval y‖ ≤ ‖x - y‖ :=
  let ⟨z, hz⟩ := F.evalSubFactor x y
  calc
    ‖F.eval x - F.eval y‖ = ‖z‖ * ‖x - y‖ := by simp [hz]
    _ ≤ 1 * ‖x - y‖ := by gcongr; apply PadicInt.norm_le_one
    _ = ‖x - y‖ := by simp

open Filter Metric

private theorem comp_tendsto_lim {p : ℕ} [Fact p.Prime] {F : Polynomial ℤ_[p]}
    (ncs : CauSeq ℤ_[p] norm) : Tendsto (fun i => F.eval (ncs i)) atTop (𝓝 (F.eval ncs.lim)) :=
  Filter.Tendsto.comp (@Polynomial.continuousAt _ _ _ _ F _) ncs.tendsto_limit

section

variable {p : ℕ} [Fact p.Prime] {ncs : CauSeq ℤ_[p] norm} {F : Polynomial ℤ_[p]}
  {a : ℤ_[p]} (ncs_der_val : ∀ n, ‖F.derivative.eval (ncs n)‖ = ‖F.derivative.eval a‖)

private theorem ncs_tendsto_lim :
    Tendsto (fun i => ‖F.derivative.eval (ncs i)‖) atTop (𝓝 ‖F.derivative.eval ncs.lim‖) :=
  Tendsto.comp (continuous_iff_continuousAt.1 continuous_norm _) (comp_tendsto_lim _)

include ncs_der_val

private theorem ncs_tendsto_const :
    Tendsto (fun i => ‖F.derivative.eval (ncs i)‖) atTop (𝓝 ‖F.derivative.eval a‖) := by
  convert @tendsto_const_nhds ℝ _ ℕ _ _; rw [ncs_der_val]

private theorem norm_deriv_eq : ‖F.derivative.eval ncs.lim‖ = ‖F.derivative.eval a‖ :=
  tendsto_nhds_unique ncs_tendsto_lim (ncs_tendsto_const ncs_der_val)

end

section


variable {p : ℕ} [Fact p.Prime] {ncs : CauSeq ℤ_[p] norm} {F : Polynomial ℤ_[p]}
  (hnorm : Tendsto (fun i => ‖F.eval (ncs i)‖) atTop (𝓝 0))
include hnorm

private theorem tendsto_zero_of_norm_tendsto_zero : Tendsto (fun i => F.eval (ncs i)) atTop (𝓝 0) :=
  tendsto_iff_norm_sub_tendsto_zero.2 (by simpa using hnorm)

theorem limit_zero_of_norm_tendsto_zero : F.eval ncs.lim = 0 :=
  tendsto_nhds_unique (comp_tendsto_lim _) (tendsto_zero_of_norm_tendsto_zero hnorm)

end

section Hensel

open Nat

variable (p : ℕ) [Fact p.Prime] (F : Polynomial ℤ_[p]) (a : ℤ_[p])

/-- `T` is an auxiliary value that is used to control the behavior of the polynomial `F`. -/
private def T_gen : ℝ := ‖F.eval a / ((F.derivative.eval a ^ 2 : ℤ_[p]) : ℚ_[p])‖

local notation "T" => @T_gen p _ F a

variable {p F a}

private theorem T_def : T = ‖F.eval a‖ / ‖F.derivative.eval a‖ ^ 2 := by
  simp [T_gen]

private theorem T_nonneg : 0 ≤ T := norm_nonneg _

private theorem T_pow_nonneg (n : ℕ) : 0 ≤ T ^ n := pow_nonneg T_nonneg _

variable (hnorm : ‖F.eval a‖ < ‖F.derivative.eval a‖ ^ 2)
include hnorm

private theorem deriv_sq_norm_pos : 0 < ‖F.derivative.eval a‖ ^ 2 :=
  lt_of_le_of_lt (norm_nonneg _) hnorm

private theorem deriv_sq_norm_ne_zero : ‖F.derivative.eval a‖ ^ 2 ≠ 0 :=
  ne_of_gt (deriv_sq_norm_pos hnorm)

private theorem deriv_norm_ne_zero : ‖F.derivative.eval a‖ ≠ 0 := fun h =>
  deriv_sq_norm_ne_zero hnorm (by simp [*, sq])

private theorem deriv_norm_pos : 0 < ‖F.derivative.eval a‖ :=
  lt_of_le_of_ne (norm_nonneg _) (Ne.symm (deriv_norm_ne_zero hnorm))

private theorem deriv_ne_zero : F.derivative.eval a ≠ 0 :=
  mt norm_eq_zero.2 (deriv_norm_ne_zero hnorm)


private theorem T_lt_one : T < 1 := by
  have h := (div_lt_one (deriv_sq_norm_pos hnorm)).2 hnorm
  rw [T_def]; exact h

private theorem T_pow {n : ℕ} (hn : n ≠ 0) : T ^ n < 1 := pow_lt_one₀ T_nonneg (T_lt_one hnorm) hn

private theorem T_pow' (n : ℕ) : T ^ 2 ^ n < 1 := T_pow hnorm (pow_ne_zero _ two_ne_zero)

/-- We will construct a sequence of elements of ℤ_p satisfying successive values of `ih`. -/
private def ih_gen (n : ℕ) (z : ℤ_[p]) : Prop :=
  ‖F.derivative.eval z‖ = ‖F.derivative.eval a‖ ∧ ‖F.eval z‖ ≤ ‖F.derivative.eval a‖ ^ 2 * T ^ 2 ^ n

local notation "ih" => @ih_gen p _ F a

private theorem ih_0 : ih 0 a :=
  ⟨rfl, by simp [T_def, mul_div_cancel₀ _ (ne_of_gt (deriv_sq_norm_pos hnorm))]⟩

private theorem calc_norm_le_one {n : ℕ} {z : ℤ_[p]} (hz : ih n z) :
    ‖(↑(F.eval z) : ℚ_[p]) / ↑(F.derivative.eval z)‖ ≤ 1 :=
  calc
    ‖(↑(F.eval z) : ℚ_[p]) / ↑(F.derivative.eval z)‖ =
        ‖(↑(F.eval z) : ℚ_[p])‖ / ‖(↑(F.derivative.eval z) : ℚ_[p])‖ :=
      norm_div _ _
    _ = ‖F.eval z‖ / ‖F.derivative.eval a‖ := by simp [hz.1]
    _ ≤ ‖F.derivative.eval a‖ ^ 2 * T ^ 2 ^ n / ‖F.derivative.eval a‖ := by
      gcongr
      apply hz.2
    _ = ‖F.derivative.eval a‖ * T ^ 2 ^ n := div_sq_cancel _ _
    _ ≤ 1 := mul_le_one₀ (PadicInt.norm_le_one _) (T_pow_nonneg _) (le_of_lt (T_pow' hnorm _))


private theorem calc_deriv_dist {z z' z1 : ℤ_[p]} (hz' : z' = z - z1)
    (hz1 : ‖z1‖ = ‖F.eval z‖ / ‖F.derivative.eval a‖) {n} (hz : ih n z) :
    ‖F.derivative.eval z' - F.derivative.eval z‖ < ‖F.derivative.eval a‖ :=
  calc
    ‖F.derivative.eval z' - F.derivative.eval z‖ ≤ ‖z' - z‖ := padic_polynomial_dist _ _ _
    _ = ‖z1‖ := by simp only [sub_eq_add_neg, add_assoc, hz', add_add_neg_cancel'_right, norm_neg]
    _ = ‖F.eval z‖ / ‖F.derivative.eval a‖ := hz1
    _ ≤ ‖F.derivative.eval a‖ ^ 2 * T ^ 2 ^ n / ‖F.derivative.eval a‖ := by
      gcongr
      apply hz.2
    _ = ‖F.derivative.eval a‖ * T ^ 2 ^ n := div_sq_cancel _ _
    _ < ‖F.derivative.eval a‖ := (mul_lt_iff_lt_one_right (deriv_norm_pos hnorm)).2
      (T_pow' hnorm _)


private def calc_eval_z' {z z' z1 : ℤ_[p]} (hz' : z' = z - z1) {n} (hz : ih n z)
    (h1 : ‖(↑(F.eval z) : ℚ_[p]) / ↑(F.derivative.eval z)‖ ≤ 1) (hzeq : z1 = ⟨_, h1⟩) :
    { q : ℤ_[p] // F.eval z' = q * z1 ^ 2 } := by
  have hdzne : F.derivative.eval z ≠ 0 :=
    mt norm_eq_zero.2 (by rw [hz.1]; apply deriv_norm_ne_zero; assumption)
  have hdzne' : (↑(F.derivative.eval z) : ℚ_[p]) ≠ 0 := fun h => hdzne (Subtype.ext_iff_val.2 h)
  obtain ⟨q, hq⟩ := F.binomExpansion z (-z1)
  have : ‖(↑(F.derivative.eval z) * (↑(F.eval z) / ↑(F.derivative.eval z)) : ℚ_[p])‖ ≤ 1 := by
    rw [padicNormE.mul]
    exact mul_le_one₀ (PadicInt.norm_le_one _) (norm_nonneg _) h1
  have : F.derivative.eval z * -z1 = -F.eval z := by
    calc
      F.derivative.eval z * -z1 =
          F.derivative.eval z * -⟨↑(F.eval z) / ↑(F.derivative.eval z), h1⟩ := by rw [hzeq]
      _ = -(F.derivative.eval z * ⟨↑(F.eval z) / ↑(F.derivative.eval z), h1⟩) := mul_neg _ _
      _ = -⟨F.derivative.eval z * (F.eval z / (F.derivative.eval z : ℤ_[p]) : ℚ_[p]), this⟩ :=
        (Subtype.ext <| by simp only [PadicInt.coe_neg, PadicInt.coe_mul])
      _ = -F.eval z := by simp only [mul_div_cancel₀ _ hdzne', Subtype.coe_eta]
  exact ⟨q, by simpa only [sub_eq_add_neg, this, hz', add_neg_cancel, neg_sq, zero_add] using hq⟩

private def calc_eval_z'_norm {z z' z1 : ℤ_[p]} {n} (hz : ih n z) {q} (heq : F.eval z' = q * z1 ^ 2)
    (h1 : ‖(↑(F.eval z) : ℚ_[p]) / ↑(F.derivative.eval z)‖ ≤ 1) (hzeq : z1 = ⟨_, h1⟩) :
    ‖F.eval z'‖ ≤ ‖F.derivative.eval a‖ ^ 2 * T ^ 2 ^ (n + 1) := by
  calc
    ‖F.eval z'‖ = ‖q‖ * ‖z1‖ ^ 2 := by simp [heq]
    _ ≤ 1 * ‖z1‖ ^ 2 := by gcongr; apply PadicInt.norm_le_one
    _ = ‖F.eval z‖ ^ 2 / ‖F.derivative.eval a‖ ^ 2 := by simp [hzeq, hz.1, div_pow]
    _ ≤ (‖F.derivative.eval a‖ ^ 2 * T ^ 2 ^ n) ^ 2 / ‖F.derivative.eval a‖ ^ 2 := by
      gcongr
      exact hz.2
    _ = (‖F.derivative.eval a‖ ^ 2) ^ 2 * (T ^ 2 ^ n) ^ 2 / ‖F.derivative.eval a‖ ^ 2 := by
      simp only [mul_pow]
    _ = ‖F.derivative.eval a‖ ^ 2 * (T ^ 2 ^ n) ^ 2 := div_sq_cancel _ _
    _ = ‖F.derivative.eval a‖ ^ 2 * T ^ 2 ^ (n + 1) := by rw [← pow_mul, pow_succ 2]


/-- Given `z : ℤ_[p]` satisfying `ih n z`, construct `z' : ℤ_[p]` satisfying `ih (n+1) z'`. We need
the hypothesis `ih n z`, since otherwise `z'` is not necessarily an integer. -/
private def ih_n {n : ℕ} {z : ℤ_[p]} (hz : ih n z) : { z' : ℤ_[p] // ih (n + 1) z' } :=
  have h1 : ‖(↑(F.eval z) : ℚ_[p]) / ↑(F.derivative.eval z)‖ ≤ 1 := calc_norm_le_one hnorm hz
  let z1 : ℤ_[p] := ⟨_, h1⟩
  let z' : ℤ_[p] := z - z1
  ⟨z',
    have hdist : ‖F.derivative.eval z' - F.derivative.eval z‖ < ‖F.derivative.eval a‖ :=
      calc_deriv_dist hnorm rfl (by simp [z1, hz.1]) hz
    have hfeq : ‖F.derivative.eval z'‖ = ‖F.derivative.eval a‖ := by
      rw [sub_eq_add_neg, ← hz.1, ← norm_neg (F.derivative.eval z)] at hdist
      have := PadicInt.norm_eq_of_norm_add_lt_right hdist
      rwa [norm_neg, hz.1] at this
    let ⟨_, heq⟩ := calc_eval_z' hnorm rfl hz h1 rfl
    have hnle : ‖F.eval z'‖ ≤ ‖F.derivative.eval a‖ ^ 2 * T ^ 2 ^ (n + 1) :=
      calc_eval_z'_norm hz heq h1 rfl
    ⟨hfeq, hnle⟩⟩

private def newton_seq_aux : ∀ n : ℕ, { z : ℤ_[p] // ih n z }
  | 0 => ⟨a, ih_0 hnorm⟩
  | k + 1 => ih_n hnorm (newton_seq_aux k).2

private def newton_seq_gen (n : ℕ) : ℤ_[p] :=
  (newton_seq_aux hnorm n).1

local notation "newton_seq" => newton_seq_gen hnorm

private theorem newton_seq_deriv_norm (n : ℕ) :
    ‖F.derivative.eval (newton_seq n)‖ = ‖F.derivative.eval a‖ :=
  (newton_seq_aux hnorm n).2.1

private theorem newton_seq_norm_le (n : ℕ) :
    ‖F.eval (newton_seq n)‖ ≤ ‖F.derivative.eval a‖ ^ 2 * T ^ 2 ^ n :=
  (newton_seq_aux hnorm n).2.2

private theorem newton_seq_norm_eq (n : ℕ) :
    ‖newton_seq (n + 1) - newton_seq n‖ =
    ‖F.eval (newton_seq n)‖ / ‖F.derivative.eval (newton_seq n)‖ := by
  rw [newton_seq_gen, newton_seq_gen, newton_seq_aux, ih_n]
  simp [sub_eq_add_neg, add_comm]

private theorem newton_seq_succ_dist (n : ℕ) :
    ‖newton_seq (n + 1) - newton_seq n‖ ≤ ‖F.derivative.eval a‖ * T ^ 2 ^ n :=
  calc
    ‖newton_seq (n + 1) - newton_seq n‖ =
        ‖F.eval (newton_seq n)‖ / ‖F.derivative.eval (newton_seq n)‖ :=
      newton_seq_norm_eq hnorm _
    _ = ‖F.eval (newton_seq n)‖ / ‖F.derivative.eval a‖ := by rw [newton_seq_deriv_norm]
    _ ≤ ‖F.derivative.eval a‖ ^ 2 * T ^ 2 ^ n / ‖F.derivative.eval a‖ := by
      gcongr
      apply newton_seq_norm_le
    _ = ‖F.derivative.eval a‖ * T ^ 2 ^ n := div_sq_cancel _ _

private theorem newton_seq_dist_aux (n : ℕ) :
    ∀ k : ℕ, ‖newton_seq (n + k) - newton_seq n‖ ≤ ‖F.derivative.eval a‖ * T ^ 2 ^ n
  | 0 => by simp [T_pow_nonneg, mul_nonneg]
  | k + 1 =>
    have : 2 ^ n ≤ 2 ^ (n + k) := by
      apply pow_right_mono₀
      · norm_num
      · apply Nat.le_add_right
    calc
      ‖newton_seq (n + (k + 1)) - newton_seq n‖ = ‖newton_seq (n + k + 1) - newton_seq n‖ := by
        rw [add_assoc]
      _ = ‖newton_seq (n + k + 1) - newton_seq (n + k) + (newton_seq (n + k) - newton_seq n)‖ := by
        rw [← sub_add_sub_cancel]
      _ ≤ max ‖newton_seq (n + k + 1) - newton_seq (n + k)‖ ‖newton_seq (n + k) - newton_seq n‖ :=
        (PadicInt.nonarchimedean _ _)
      _ ≤ max (‖F.derivative.eval a‖ * T ^ 2 ^ (n + k)) (‖F.derivative.eval a‖ * T ^ 2 ^ n) :=
        (max_le_max (newton_seq_succ_dist _ _) (newton_seq_dist_aux _ _))
      _ = ‖F.derivative.eval a‖ * T ^ 2 ^ n :=
        max_eq_right <|
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (norm_nonneg _)
            (le_of_lt (T_lt_one hnorm)) this) (norm_nonneg _)

private theorem newton_seq_dist {n k : ℕ} (hnk : n ≤ k) :
    ‖newton_seq k - newton_seq n‖ ≤ ‖F.derivative.eval a‖ * T ^ 2 ^ n := by
  have hex : ∃ m, k = n + m := Nat.exists_eq_add_of_le hnk
  let ⟨_, hex'⟩ := hex
  rw [hex']; apply newton_seq_dist_aux

private theorem bound' : Tendsto (fun n : ℕ => ‖F.derivative.eval a‖ * T ^ 2 ^ n) atTop (𝓝 0) := by
  rw [← mul_zero ‖F.derivative.eval a‖]
  exact
    tendsto_const_nhds.mul
      (Tendsto.comp (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (T_lt_one hnorm))
        (Nat.tendsto_pow_atTop_atTop_of_one_lt (by simp)))

private theorem bound :
    ∀ {ε}, ε > 0 → ∃ N : ℕ, ∀ {n}, n ≥ N → ‖F.derivative.eval a‖ * T ^ 2 ^ n < ε := fun hε ↦
  eventually_atTop.1 <| (bound' hnorm).eventually <| gt_mem_nhds hε

private theorem bound'_sq :
    Tendsto (fun n : ℕ => ‖F.derivative.eval a‖ ^ 2 * T ^ 2 ^ n) atTop (𝓝 0) := by
  rw [← mul_zero ‖F.derivative.eval a‖, sq]
  simp only [mul_assoc]
  apply Tendsto.mul
  · apply tendsto_const_nhds
  · apply bound'
    assumption

private theorem newton_seq_is_cauchy : IsCauSeq norm newton_seq := fun _ε hε ↦
  (bound hnorm hε).imp fun _N hN _j hj ↦ (newton_seq_dist hnorm hj).trans_lt <| hN le_rfl

private def newton_cau_seq : CauSeq ℤ_[p] norm := ⟨_, newton_seq_is_cauchy hnorm⟩

private def soln_gen : ℤ_[p] := (newton_cau_seq hnorm).lim

local notation "soln" => soln_gen hnorm

private theorem soln_spec {ε : ℝ} (hε : ε > 0) :
    ∃ N : ℕ, ∀ {i : ℕ}, i ≥ N → ‖soln - newton_cau_seq hnorm i‖ < ε :=
  Setoid.symm (CauSeq.equiv_lim (newton_cau_seq hnorm)) _ hε

private theorem soln_deriv_norm : ‖F.derivative.eval soln‖ = ‖F.derivative.eval a‖ :=
  norm_deriv_eq (newton_seq_deriv_norm hnorm)

private theorem newton_seq_norm_tendsto_zero :
    Tendsto (fun i => ‖F.eval (newton_cau_seq hnorm i)‖) atTop (𝓝 0) :=
  squeeze_zero (fun _ => norm_nonneg _) (newton_seq_norm_le hnorm) (bound'_sq hnorm)

private theorem newton_seq_dist_tendsto' :
    Tendsto (fun n => ‖newton_cau_seq hnorm n - a‖) atTop (𝓝 ‖soln - a‖) :=
  (continuous_norm.tendsto _).comp ((newton_cau_seq hnorm).tendsto_limit.sub tendsto_const_nhds)

private theorem eval_soln : F.eval soln = 0 :=
  limit_zero_of_norm_tendsto_zero (newton_seq_norm_tendsto_zero hnorm)

variable (hnsol : F.eval a ≠ 0)
include hnsol

private theorem T_pos : T > 0 := by
  rw [T_def]
  exact div_pos (norm_pos_iff.2 hnsol) (deriv_sq_norm_pos hnorm)

private theorem newton_seq_succ_dist_weak (n : ℕ) :
    ‖newton_seq (n + 2) - newton_seq (n + 1)‖ < ‖F.eval a‖ / ‖F.derivative.eval a‖ :=
  have : 2 ≤ 2 ^ (n + 1) := by
    have := pow_right_mono₀ (by simp : 1 ≤ 2) (Nat.le_add_left _ _ : 1 ≤ n + 1)
    simpa using this
  calc
    ‖newton_seq (n + 2) - newton_seq (n + 1)‖ ≤ ‖F.derivative.eval a‖ * T ^ 2 ^ (n + 1) :=
      newton_seq_succ_dist hnorm _
    _ ≤ ‖F.derivative.eval a‖ * T ^ 2 :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (norm_nonneg _)
        (le_of_lt (T_lt_one hnorm)) this) (norm_nonneg _))
    _ < ‖F.derivative.eval a‖ * T ^ 1 :=
      (mul_lt_mul_of_pos_left (pow_lt_pow_right_of_lt_one₀ (T_pos hnorm hnsol)
        (T_lt_one hnorm) (by simp)) (deriv_norm_pos hnorm))
    _ = ‖F.eval a‖ / ‖F.derivative.eval a‖ := by
      rw [T_gen, sq, pow_one, norm_div, ← mul_div_assoc, PadicInt.padic_norm_e_of_padicInt,
        PadicInt.coe_mul, padicNormE.mul]
      apply mul_div_mul_left
      apply deriv_norm_ne_zero; assumption

private theorem newton_seq_dist_to_a :
    ∀ n : ℕ, 0 < n → ‖newton_seq n - a‖ = ‖F.eval a‖ / ‖F.derivative.eval a‖
  | 1, _h => by simp [sub_eq_add_neg, add_assoc, newton_seq_gen, newton_seq_aux, ih_n]
  | k + 2, _h =>
    have hlt : ‖newton_seq (k + 2) - newton_seq (k + 1)‖ < ‖newton_seq (k + 1) - a‖ := by
      rw [newton_seq_dist_to_a (k + 1) (succ_pos _)]; apply newton_seq_succ_dist_weak
      assumption
    have hne' : ‖newton_seq (k + 2) - newton_seq (k + 1)‖ ≠ ‖newton_seq (k + 1) - a‖ := ne_of_lt hlt
    calc
      ‖newton_seq (k + 2) - a‖ =
          ‖newton_seq (k + 2) - newton_seq (k + 1) + (newton_seq (k + 1) - a)‖ := by
        rw [← sub_add_sub_cancel]
      _ = max ‖newton_seq (k + 2) - newton_seq (k + 1)‖ ‖newton_seq (k + 1) - a‖ :=
        (PadicInt.norm_add_eq_max_of_ne hne')
      _ = ‖newton_seq (k + 1) - a‖ := max_eq_right_of_lt hlt
      _ = ‖Polynomial.eval a F‖ / ‖Polynomial.eval a (Polynomial.derivative F)‖ :=
        newton_seq_dist_to_a (k + 1) (succ_pos _)

private theorem newton_seq_dist_tendsto :
    Tendsto (fun n => ‖newton_cau_seq hnorm n - a‖)
    atTop (𝓝 (‖F.eval a‖ / ‖F.derivative.eval a‖)) :=
  tendsto_const_nhds.congr' (eventually_atTop.2
    ⟨1, fun _ hx => (newton_seq_dist_to_a hnorm hnsol _ hx).symm⟩)

private theorem soln_dist_to_a : ‖soln - a‖ = ‖F.eval a‖ / ‖F.derivative.eval a‖ :=
  tendsto_nhds_unique (newton_seq_dist_tendsto' hnorm) (newton_seq_dist_tendsto hnorm hnsol)

private theorem soln_dist_to_a_lt_deriv : ‖soln - a‖ < ‖F.derivative.eval a‖ := by
  rw [soln_dist_to_a, div_lt_iff₀ (deriv_norm_pos _), ← sq] <;> assumption

private theorem soln_unique (z : ℤ_[p]) (hev : F.eval z = 0)
    (hnlt : ‖z - a‖ < ‖F.derivative.eval a‖) : z = soln :=
  have soln_dist : ‖z - soln‖ < ‖F.derivative.eval a‖ :=
    calc
      ‖z - soln‖ = ‖z - a + (a - soln)‖ := by rw [sub_add_sub_cancel]
      _ ≤ max ‖z - a‖ ‖a - soln‖ := PadicInt.nonarchimedean _ _
      _ < ‖F.derivative.eval a‖ :=
        max_lt hnlt ((norm_sub_rev soln a ▸ (soln_dist_to_a_lt_deriv hnorm)) hnsol)
  let h := z - soln
  let ⟨q, hq⟩ := F.binomExpansion soln h
  have : (F.derivative.eval soln + q * h) * h = 0 :=
    Eq.symm
      (calc
        0 = F.eval (soln + h) := by simp [h, hev]
        _ = F.derivative.eval soln * h + q * h ^ 2 := by rw [hq, eval_soln, zero_add]
        _ = (F.derivative.eval soln + q * h) * h := by rw [sq, right_distrib, mul_assoc]
        )
  have : h = 0 :=
    by_contra fun hne =>
      have : F.derivative.eval soln + q * h = 0 :=
        (eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_right hne
      have : F.derivative.eval soln = -q * h := by simpa using eq_neg_of_add_eq_zero_left this
      lt_irrefl ‖F.derivative.eval soln‖
        (calc
          ‖F.derivative.eval soln‖ = ‖-q * h‖ := by rw [this]
          _ ≤ 1 * ‖h‖ := by
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_right (PadicInt.norm_le_one _) (norm_nonneg _)
          _ = ‖z - soln‖ := by simp [h]
          _ < ‖F.derivative.eval soln‖ := by rw [soln_deriv_norm]; apply soln_dist
          )
  eq_of_sub_eq_zero (by rw [← this])

end Hensel

variable {p : ℕ} [Fact p.Prime] {F : Polynomial ℤ_[p]} {a : ℤ_[p]}

private theorem a_soln_is_unique (ha : F.eval a = 0) (z' : ℤ_[p]) (hz' : F.eval z' = 0)
    (hnormz' : ‖z' - a‖ < ‖F.derivative.eval a‖) : z' = a :=
  let h := z' - a
  let ⟨q, hq⟩ := F.binomExpansion a h
  have : (F.derivative.eval a + q * h) * h = 0 :=
    Eq.symm
      (calc
        0 = F.eval (a + h) := show 0 = F.eval (a + (z' - a)) by rw [add_comm]; simp [hz']
        _ = F.derivative.eval a * h + q * h ^ 2 := by rw [hq, ha, zero_add]
        _ = (F.derivative.eval a + q * h) * h := by rw [sq, right_distrib, mul_assoc]
        )
  have : h = 0 :=
    by_contra fun hne =>
      have : F.derivative.eval a + q * h = 0 :=
        (eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_right hne
      have : F.derivative.eval a = -q * h := by simpa using eq_neg_of_add_eq_zero_left this
      lt_irrefl ‖F.derivative.eval a‖
        (calc
          ‖F.derivative.eval a‖ = ‖q‖ * ‖h‖ := by simp [this]
          _ ≤ 1 * ‖h‖ := by gcongr; apply PadicInt.norm_le_one
          _ < ‖F.derivative.eval a‖ := by simpa
          )
  eq_of_sub_eq_zero (by rw [← this])

variable (hnorm : ‖F.eval a‖ < ‖F.derivative.eval a‖ ^ 2)
include hnorm

private theorem a_is_soln (ha : F.eval a = 0) :
    F.eval a = 0 ∧
      ‖a - a‖ < ‖F.derivative.eval a‖ ∧
        ‖F.derivative.eval a‖ = ‖F.derivative.eval a‖ ∧
          ∀ z', F.eval z' = 0 → ‖z' - a‖ < ‖F.derivative.eval a‖ → z' = a :=
  ⟨ha, by simp [deriv_ne_zero hnorm], rfl, a_soln_is_unique ha⟩

theorem hensels_lemma :
    ∃ z : ℤ_[p],
      F.eval z = 0 ∧
        ‖z - a‖ < ‖F.derivative.eval a‖ ∧
          ‖F.derivative.eval z‖ = ‖F.derivative.eval a‖ ∧
            ∀ z', F.eval z' = 0 → ‖z' - a‖ < ‖F.derivative.eval a‖ → z' = z := by
  classical
  exact if ha : F.eval a = 0 then ⟨a, a_is_soln hnorm ha⟩
  else by
    exact ⟨soln_gen hnorm, eval_soln hnorm,
      soln_dist_to_a_lt_deriv hnorm ha, soln_deriv_norm hnorm, fun z => soln_unique hnorm ha z⟩
