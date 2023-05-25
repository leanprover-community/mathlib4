/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis

! This file was ported from Lean 3 source module number_theory.padics.hensel
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecificLimits.Basic
import Mathbin.Data.Polynomial.Identities
import Mathbin.NumberTheory.Padics.PadicIntegers
import Mathbin.Topology.Algebra.Polynomial
import Mathbin.Topology.MetricSpace.CauSeqFilter

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

open Classical Topology

-- We begin with some general lemmas that are used below in the computation.
theorem padic_polynomial_dist {p : ℕ} [Fact p.Prime] (F : Polynomial ℤ_[p]) (x y : ℤ_[p]) :
    ‖F.eval x - F.eval y‖ ≤ ‖x - y‖ :=
  let ⟨z, hz⟩ := F.evalSubFactor x y
  calc
    ‖F.eval x - F.eval y‖ = ‖z‖ * ‖x - y‖ := by simp [hz]
    _ ≤ 1 * ‖x - y‖ := (mul_le_mul_of_nonneg_right (PadicInt.norm_le_one _) (norm_nonneg _))
    _ = ‖x - y‖ := by simp
    
#align padic_polynomial_dist padic_polynomial_dist

open Filter Metric

private theorem comp_tendsto_lim {p : ℕ} [Fact p.Prime] {F : Polynomial ℤ_[p]}
    (ncs : CauSeq ℤ_[p] norm) : Tendsto (fun i => F.eval (ncs i)) atTop (𝓝 (F.eval ncs.limUnder)) :=
  F.ContinuousAt.Tendsto.comp ncs.tendsto_limit
#align comp_tendsto_lim comp_tendsto_lim

section

parameter
  {p :
    ℕ}[Fact
      p.Prime]{ncs :
    CauSeq ℤ_[p]
      norm}{F :
    Polynomial
      ℤ_[p]}{a : ℤ_[p]}(ncs_der_val : ∀ n, ‖F.derivative.eval (ncs n)‖ = ‖F.derivative.eval a‖)

include ncs_der_val

private theorem ncs_tendsto_const :
    Tendsto (fun i => ‖F.derivative.eval (ncs i)‖) atTop (𝓝 ‖F.derivative.eval a‖) := by
  convert tendsto_const_nhds <;> ext <;> rw [ncs_der_val]
#align ncs_tendsto_const ncs_tendsto_const

private theorem ncs_tendsto_lim :
    Tendsto (fun i => ‖F.derivative.eval (ncs i)‖) atTop (𝓝 ‖F.derivative.eval ncs.limUnder‖) :=
  Tendsto.comp (continuous_iff_continuousAt.1 continuous_norm _) (comp_tendsto_lim _)
#align ncs_tendsto_lim ncs_tendsto_lim

private theorem norm_deriv_eq : ‖F.derivative.eval ncs.limUnder‖ = ‖F.derivative.eval a‖ :=
  tendsto_nhds_unique ncs_tendsto_lim ncs_tendsto_const
#align norm_deriv_eq norm_deriv_eq

end

section

parameter
  {p :
    ℕ}[Fact
      p.Prime]{ncs :
    CauSeq ℤ_[p]
      norm}{F : Polynomial ℤ_[p]}(hnorm : Tendsto (fun i => ‖F.eval (ncs i)‖) atTop (𝓝 0))

include hnorm

private theorem tendsto_zero_of_norm_tendsto_zero : Tendsto (fun i => F.eval (ncs i)) atTop (𝓝 0) :=
  tendsto_iff_norm_tendsto_zero.2 (by simpa using hnorm)
#align tendsto_zero_of_norm_tendsto_zero tendsto_zero_of_norm_tendsto_zero

theorem limit_zero_of_norm_tendsto_zero : F.eval ncs.limUnder = 0 :=
  tendsto_nhds_unique (comp_tendsto_lim _) tendsto_zero_of_norm_tendsto_zero
#align limit_zero_of_norm_tendsto_zero limit_zero_of_norm_tendsto_zero

end

section Hensel

open Nat

parameter
  {p :
    ℕ}[Fact
      p.Prime]{F :
    Polynomial
      ℤ_[p]}{a : ℤ_[p]}(hnorm : ‖F.eval a‖ < ‖F.derivative.eval a‖ ^ 2)(hnsol : F.eval a ≠ 0)

include hnorm

/-- `T` is an auxiliary value that is used to control the behavior of the polynomial `F`. -/
private def T : ℝ :=
  ‖(F.eval a / F.derivative.eval a ^ 2 : ℚ_[p])‖
#align T T

private theorem deriv_sq_norm_pos : 0 < ‖F.derivative.eval a‖ ^ 2 :=
  lt_of_le_of_lt (norm_nonneg _) hnorm
#align deriv_sq_norm_pos deriv_sq_norm_pos

private theorem deriv_sq_norm_ne_zero : ‖F.derivative.eval a‖ ^ 2 ≠ 0 :=
  ne_of_gt deriv_sq_norm_pos
#align deriv_sq_norm_ne_zero deriv_sq_norm_ne_zero

private theorem deriv_norm_ne_zero : ‖F.derivative.eval a‖ ≠ 0 := fun h =>
  deriv_sq_norm_ne_zero (by simp [*, sq])
#align deriv_norm_ne_zero deriv_norm_ne_zero

private theorem deriv_norm_pos : 0 < ‖F.derivative.eval a‖ :=
  lt_of_le_of_ne (norm_nonneg _) (Ne.symm deriv_norm_ne_zero)
#align deriv_norm_pos deriv_norm_pos

private theorem deriv_ne_zero : F.derivative.eval a ≠ 0 :=
  mt norm_eq_zero.2 deriv_norm_ne_zero
#align deriv_ne_zero deriv_ne_zero

private theorem T_def : T = ‖F.eval a‖ / ‖F.derivative.eval a‖ ^ 2 := by
  simp [T, ← PadicInt.norm_def]
#align T_def T_def

private theorem T_lt_one : T < 1 :=
  by
  let h := (div_lt_one deriv_sq_norm_pos).2 hnorm
  rw [T_def] <;> apply h
#align T_lt_one T_lt_one

private theorem T_nonneg : 0 ≤ T :=
  norm_nonneg _
#align T_nonneg T_nonneg

private theorem T_pow_nonneg (n : ℕ) : 0 ≤ T ^ n :=
  pow_nonneg T_nonneg _
#align T_pow_nonneg T_pow_nonneg

private theorem T_pow {n : ℕ} (hn : n ≠ 0) : T ^ n < 1 :=
  pow_lt_one T_nonneg T_lt_one hn
#align T_pow T_pow

private theorem T_pow' (n : ℕ) : T ^ 2 ^ n < 1 :=
  T_pow (pow_ne_zero _ two_ne_zero)
#align T_pow' T_pow'

/-- We will construct a sequence of elements of ℤ_p satisfying successive values of `ih`. -/
private def ih (n : ℕ) (z : ℤ_[p]) : Prop :=
  ‖F.derivative.eval z‖ = ‖F.derivative.eval a‖ ∧ ‖F.eval z‖ ≤ ‖F.derivative.eval a‖ ^ 2 * T ^ 2 ^ n
#align ih ih

private theorem ih_0 : ih 0 a :=
  ⟨rfl, by simp [T_def, mul_div_cancel' _ (ne_of_gt (deriv_sq_norm_pos hnorm))]⟩
#align ih_0 ih_0

private theorem calc_norm_le_one {n : ℕ} {z : ℤ_[p]} (hz : ih n z) :
    ‖(↑(F.eval z) : ℚ_[p]) / ↑(F.derivative.eval z)‖ ≤ 1 :=
  calc
    ‖(↑(F.eval z) : ℚ_[p]) / ↑(F.derivative.eval z)‖ =
        ‖(↑(F.eval z) : ℚ_[p])‖ / ‖(↑(F.derivative.eval z) : ℚ_[p])‖ :=
      norm_div _ _
    _ = ‖F.eval z‖ / ‖F.derivative.eval a‖ := by simp [hz.1]
    _ ≤ ‖F.derivative.eval a‖ ^ 2 * T ^ 2 ^ n / ‖F.derivative.eval a‖ :=
      ((div_le_div_right deriv_norm_pos).2 hz.2)
    _ = ‖F.derivative.eval a‖ * T ^ 2 ^ n := (div_sq_cancel _ _)
    _ ≤ 1 := mul_le_one (PadicInt.norm_le_one _) (T_pow_nonneg _) (le_of_lt (T_pow' _))
    
#align calc_norm_le_one calc_norm_le_one

private theorem calc_deriv_dist {z z' z1 : ℤ_[p]} (hz' : z' = z - z1)
    (hz1 : ‖z1‖ = ‖F.eval z‖ / ‖F.derivative.eval a‖) {n} (hz : ih n z) :
    ‖F.derivative.eval z' - F.derivative.eval z‖ < ‖F.derivative.eval a‖ :=
  calc
    ‖F.derivative.eval z' - F.derivative.eval z‖ ≤ ‖z' - z‖ := padic_polynomial_dist _ _ _
    _ = ‖z1‖ := by simp only [sub_eq_add_neg, add_assoc, hz', add_add_neg_cancel'_right, norm_neg]
    _ = ‖F.eval z‖ / ‖F.derivative.eval a‖ := hz1
    _ ≤ ‖F.derivative.eval a‖ ^ 2 * T ^ 2 ^ n / ‖F.derivative.eval a‖ :=
      ((div_le_div_right deriv_norm_pos).2 hz.2)
    _ = ‖F.derivative.eval a‖ * T ^ 2 ^ n := (div_sq_cancel _ _)
    _ < ‖F.derivative.eval a‖ := (mul_lt_iff_lt_one_right deriv_norm_pos).2 (T_pow' _)
    
#align calc_deriv_dist calc_deriv_dist

private def calc_eval_z' {z z' z1 : ℤ_[p]} (hz' : z' = z - z1) {n} (hz : ih n z)
    (h1 : ‖(↑(F.eval z) : ℚ_[p]) / ↑(F.derivative.eval z)‖ ≤ 1) (hzeq : z1 = ⟨_, h1⟩) :
    { q : ℤ_[p] // F.eval z' = q * z1 ^ 2 } :=
  by
  have hdzne : F.derivative.eval z ≠ 0 :=
    mt norm_eq_zero.2 (by rw [hz.1] <;> apply deriv_norm_ne_zero <;> assumption)
  have hdzne' : (↑(F.derivative.eval z) : ℚ_[p]) ≠ 0 := fun h => hdzne (Subtype.ext_iff_val.2 h)
  obtain ⟨q, hq⟩ := F.binom_expansion z (-z1)
  have : ‖(↑(F.derivative.eval z) * (↑(F.eval z) / ↑(F.derivative.eval z)) : ℚ_[p])‖ ≤ 1 :=
    by
    rw [padicNormE.mul]
    exact mul_le_one (PadicInt.norm_le_one _) (norm_nonneg _) h1
  have : F.derivative.eval z * -z1 = -F.eval z := by
    calc
      F.derivative.eval z * -z1 =
          F.derivative.eval z * -⟨↑(F.eval z) / ↑(F.derivative.eval z), h1⟩ :=
        by rw [hzeq]
      _ = -(F.derivative.eval z * ⟨↑(F.eval z) / ↑(F.derivative.eval z), h1⟩) := (mul_neg _ _)
      _ = -⟨↑(F.derivative.eval z) * (↑(F.eval z) / ↑(F.derivative.eval z)), this⟩ :=
        (Subtype.ext <| by simp only [PadicInt.coe_neg, PadicInt.coe_mul, Subtype.coe_mk])
      _ = -F.eval z := by simp only [mul_div_cancel' _ hdzne', Subtype.coe_eta]
      
  exact ⟨q, by simpa only [sub_eq_add_neg, this, hz', add_right_neg, neg_sq, zero_add] using hq⟩
#align calc_eval_z' calc_eval_z'

private def calc_eval_z'_norm {z z' z1 : ℤ_[p]} {n} (hz : ih n z) {q} (heq : F.eval z' = q * z1 ^ 2)
    (h1 : ‖(↑(F.eval z) : ℚ_[p]) / ↑(F.derivative.eval z)‖ ≤ 1) (hzeq : z1 = ⟨_, h1⟩) :
    ‖F.eval z'‖ ≤ ‖F.derivative.eval a‖ ^ 2 * T ^ 2 ^ (n + 1) :=
  calc
    ‖F.eval z'‖ = ‖q‖ * ‖z1‖ ^ 2 := by simp [HEq]
    _ ≤ 1 * ‖z1‖ ^ 2 :=
      (mul_le_mul_of_nonneg_right (PadicInt.norm_le_one _) (pow_nonneg (norm_nonneg _) _))
    _ = ‖F.eval z‖ ^ 2 / ‖F.derivative.eval a‖ ^ 2 := by simp [hzeq, hz.1, div_pow]
    _ ≤ (‖F.derivative.eval a‖ ^ 2 * T ^ 2 ^ n) ^ 2 / ‖F.derivative.eval a‖ ^ 2 :=
      ((div_le_div_right deriv_sq_norm_pos).2 (pow_le_pow_of_le_left (norm_nonneg _) hz.2 _))
    _ = (‖F.derivative.eval a‖ ^ 2) ^ 2 * (T ^ 2 ^ n) ^ 2 / ‖F.derivative.eval a‖ ^ 2 := by
      simp only [mul_pow]
    _ = ‖F.derivative.eval a‖ ^ 2 * (T ^ 2 ^ n) ^ 2 := (div_sq_cancel _ _)
    _ = ‖F.derivative.eval a‖ ^ 2 * T ^ 2 ^ (n + 1) := by rw [← pow_mul, pow_succ' 2]
    
#align calc_eval_z'_norm calc_eval_z'_norm

/- ./././Mathport/Syntax/Translate/Basic.lean:334:40: warning: unsupported option eqn_compiler.zeta -/
set_option eqn_compiler.zeta true

/-- Given `z : ℤ_[p]` satisfying `ih n z`, construct `z' : ℤ_[p]` satisfying `ih (n+1) z'`. We need
the hypothesis `ih n z`, since otherwise `z'` is not necessarily an integer. -/
private def ih_n {n : ℕ} {z : ℤ_[p]} (hz : ih n z) : { z' : ℤ_[p] // ih (n + 1) z' } :=
  have h1 : ‖(↑(F.eval z) : ℚ_[p]) / ↑(F.derivative.eval z)‖ ≤ 1 := calc_norm_le_one hz
  let z1 : ℤ_[p] := ⟨_, h1⟩
  let z' : ℤ_[p] := z - z1
  ⟨z',
    have hdist : ‖F.derivative.eval z' - F.derivative.eval z‖ < ‖F.derivative.eval a‖ :=
      calc_deriv_dist rfl (by simp [z1, hz.1]) hz
    have hfeq : ‖F.derivative.eval z'‖ = ‖F.derivative.eval a‖ :=
      by
      rw [sub_eq_add_neg, ← hz.1, ← norm_neg (F.derivative.eval z)] at hdist
      have := PadicInt.norm_eq_of_norm_add_lt_right hdist
      rwa [norm_neg, hz.1] at this
    let ⟨q, HEq⟩ := calc_eval_z' rfl hz h1 rfl
    have hnle : ‖F.eval z'‖ ≤ ‖F.derivative.eval a‖ ^ 2 * T ^ 2 ^ (n + 1) :=
      calc_eval_z'_norm hz HEq h1 rfl
    ⟨hfeq, hnle⟩⟩
#align ih_n ih_n

/- ./././Mathport/Syntax/Translate/Basic.lean:334:40: warning: unsupported option eqn_compiler.zeta -/
set_option eqn_compiler.zeta false

-- why doesn't "noncomputable theory" stick here?
private noncomputable def newton_seq_aux : ∀ n : ℕ, { z : ℤ_[p] // ih n z }
  | 0 => ⟨a, ih_0⟩
  | k + 1 => ih_n (newton_seq_aux k).2
#align newton_seq_aux newton_seq_aux

private def newton_seq (n : ℕ) : ℤ_[p] :=
  (newton_seq_aux n).1
#align newton_seq newton_seq

private theorem newton_seq_deriv_norm (n : ℕ) :
    ‖F.derivative.eval (newton_seq n)‖ = ‖F.derivative.eval a‖ :=
  (newton_seq_aux n).2.1
#align newton_seq_deriv_norm newton_seq_deriv_norm

private theorem newton_seq_norm_le (n : ℕ) :
    ‖F.eval (newton_seq n)‖ ≤ ‖F.derivative.eval a‖ ^ 2 * T ^ 2 ^ n :=
  (newton_seq_aux n).2.2
#align newton_seq_norm_le newton_seq_norm_le

private theorem newton_seq_norm_eq (n : ℕ) :
    ‖newton_seq (n + 1) - newton_seq n‖ =
      ‖F.eval (newton_seq n)‖ / ‖F.derivative.eval (newton_seq n)‖ :=
  by simp [newton_seq, newton_seq_aux, ih_n, sub_eq_add_neg, add_comm]
#align newton_seq_norm_eq newton_seq_norm_eq

private theorem newton_seq_succ_dist (n : ℕ) :
    ‖newton_seq (n + 1) - newton_seq n‖ ≤ ‖F.derivative.eval a‖ * T ^ 2 ^ n :=
  calc
    ‖newton_seq (n + 1) - newton_seq n‖ =
        ‖F.eval (newton_seq n)‖ / ‖F.derivative.eval (newton_seq n)‖ :=
      newton_seq_norm_eq _
    _ = ‖F.eval (newton_seq n)‖ / ‖F.derivative.eval a‖ := by rw [newton_seq_deriv_norm]
    _ ≤ ‖F.derivative.eval a‖ ^ 2 * T ^ 2 ^ n / ‖F.derivative.eval a‖ :=
      ((div_le_div_right deriv_norm_pos).2 (newton_seq_norm_le _))
    _ = ‖F.derivative.eval a‖ * T ^ 2 ^ n := div_sq_cancel _ _
    
#align newton_seq_succ_dist newton_seq_succ_dist

include hnsol

private theorem T_pos : T > 0 := by
  rw [T_def]
  exact div_pos (norm_pos_iff.2 hnsol) (deriv_sq_norm_pos hnorm)
#align T_pos T_pos

private theorem newton_seq_succ_dist_weak (n : ℕ) :
    ‖newton_seq (n + 2) - newton_seq (n + 1)‖ < ‖F.eval a‖ / ‖F.derivative.eval a‖ :=
  have : 2 ≤ 2 ^ (n + 1) :=
    by
    have := pow_le_pow (by norm_num : 1 ≤ 2) (Nat.le_add_left _ _ : 1 ≤ n + 1)
    simpa using this
  calc
    ‖newton_seq (n + 2) - newton_seq (n + 1)‖ ≤ ‖F.derivative.eval a‖ * T ^ 2 ^ (n + 1) :=
      newton_seq_succ_dist _
    _ ≤ ‖F.derivative.eval a‖ * T ^ 2 :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt T_lt_one) this)
        (norm_nonneg _))
    _ < ‖F.derivative.eval a‖ * T ^ 1 :=
      (mul_lt_mul_of_pos_left (pow_lt_pow_of_lt_one T_pos T_lt_one (by norm_num)) deriv_norm_pos)
    _ = ‖F.eval a‖ / ‖F.derivative.eval a‖ :=
      by
      rw [T, sq, pow_one, norm_div, ← mul_div_assoc, padicNormE.mul]
      apply mul_div_mul_left
      apply deriv_norm_ne_zero <;> assumption
    
#align newton_seq_succ_dist_weak newton_seq_succ_dist_weak

private theorem newton_seq_dist_aux (n : ℕ) :
    ∀ k : ℕ, ‖newton_seq (n + k) - newton_seq n‖ ≤ ‖F.derivative.eval a‖ * T ^ 2 ^ n
  | 0 => by simp [T_pow_nonneg hnorm, mul_nonneg]
  | k + 1 =>
    have : 2 ^ n ≤ 2 ^ (n + k) := by
      apply pow_le_pow
      norm_num
      apply Nat.le_add_right
    calc
      ‖newton_seq (n + (k + 1)) - newton_seq n‖ = ‖newton_seq (n + k + 1) - newton_seq n‖ := by
        rw [add_assoc]
      _ = ‖newton_seq (n + k + 1) - newton_seq (n + k) + (newton_seq (n + k) - newton_seq n)‖ := by
        rw [← sub_add_sub_cancel]
      _ ≤ max ‖newton_seq (n + k + 1) - newton_seq (n + k)‖ ‖newton_seq (n + k) - newton_seq n‖ :=
        (PadicInt.nonarchimedean _ _)
      _ ≤ max (‖F.derivative.eval a‖ * T ^ 2 ^ (n + k)) (‖F.derivative.eval a‖ * T ^ 2 ^ n) :=
        (max_le_max (newton_seq_succ_dist _) (newton_seq_dist_aux _))
      _ = ‖F.derivative.eval a‖ * T ^ 2 ^ n :=
        max_eq_right <|
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt T_lt_one) this)
            (norm_nonneg _)
      
#align newton_seq_dist_aux newton_seq_dist_aux

private theorem newton_seq_dist {n k : ℕ} (hnk : n ≤ k) :
    ‖newton_seq k - newton_seq n‖ ≤ ‖F.derivative.eval a‖ * T ^ 2 ^ n :=
  by
  have hex : ∃ m, k = n + m := exists_eq_add_of_le hnk
  let ⟨_, hex'⟩ := hex
  rw [hex'] <;> apply newton_seq_dist_aux <;> assumption
#align newton_seq_dist newton_seq_dist

private theorem newton_seq_dist_to_a :
    ∀ n : ℕ, 0 < n → ‖newton_seq n - a‖ = ‖F.eval a‖ / ‖F.derivative.eval a‖
  | 1, h => by simp [sub_eq_add_neg, add_assoc, newton_seq, newton_seq_aux, ih_n]
  | k + 2, h =>
    have hlt : ‖newton_seq (k + 2) - newton_seq (k + 1)‖ < ‖newton_seq (k + 1) - a‖ := by
      rw [newton_seq_dist_to_a (k + 1) (succ_pos _)] <;> apply newton_seq_succ_dist_weak <;>
        assumption
    have hne' : ‖newton_seq (k + 2) - newton_seq (k + 1)‖ ≠ ‖newton_seq (k + 1) - a‖ := ne_of_lt hlt
    calc
      ‖newton_seq (k + 2) - a‖ =
          ‖newton_seq (k + 2) - newton_seq (k + 1) + (newton_seq (k + 1) - a)‖ :=
        by rw [← sub_add_sub_cancel]
      _ = max ‖newton_seq (k + 2) - newton_seq (k + 1)‖ ‖newton_seq (k + 1) - a‖ :=
        (PadicInt.norm_add_eq_max_of_ne hne')
      _ = ‖newton_seq (k + 1) - a‖ := (max_eq_right_of_lt hlt)
      _ = ‖Polynomial.eval a F‖ / ‖Polynomial.eval a (Polynomial.derivative F)‖ :=
        newton_seq_dist_to_a (k + 1) (succ_pos _)
      
#align newton_seq_dist_to_a newton_seq_dist_to_a

private theorem bound' : Tendsto (fun n : ℕ => ‖F.derivative.eval a‖ * T ^ 2 ^ n) atTop (𝓝 0) :=
  by
  rw [← MulZeroClass.mul_zero ‖F.derivative.eval a‖]
  exact
    tendsto_const_nhds.mul
      (tendsto.comp (tendsto_pow_atTop_nhds_0_of_lt_1 (norm_nonneg _) (T_lt_one hnorm))
        (Nat.tendsto_pow_atTop_atTop_of_one_lt (by norm_num)))
#align bound' bound'

private theorem bound :
    ∀ {ε}, ε > 0 → ∃ N : ℕ, ∀ {n}, n ≥ N → ‖F.derivative.eval a‖ * T ^ 2 ^ n < ε :=
  by
  have := bound' hnorm hnsol
  simp [tendsto, nhds] at this
  intro ε hε
  cases' this (ball 0 ε) (mem_ball_self hε) is_open_ball with N hN
  exists N; intro n hn
  simpa [abs_of_nonneg (T_nonneg _)] using hN _ hn
#align bound bound

private theorem bound'_sq :
    Tendsto (fun n : ℕ => ‖F.derivative.eval a‖ ^ 2 * T ^ 2 ^ n) atTop (𝓝 0) :=
  by
  rw [← MulZeroClass.mul_zero ‖F.derivative.eval a‖, sq]
  simp only [mul_assoc]
  apply tendsto.mul
  · apply tendsto_const_nhds
  · apply bound'
    assumption
#align bound'_sq bound'_sq

private theorem newton_seq_is_cauchy : IsCauSeq norm newton_seq :=
  by
  intro ε hε
  cases' bound hnorm hnsol hε with N hN
  exists N
  intro j hj
  apply lt_of_le_of_lt
  · apply newton_seq_dist _ _ hj
    assumption
  · apply hN
    exact le_rfl
#align newton_seq_is_cauchy newton_seq_is_cauchy

private def newton_cau_seq : CauSeq ℤ_[p] norm :=
  ⟨_, newton_seq_is_cauchy⟩
#align newton_cau_seq newton_cau_seq

private def soln : ℤ_[p] :=
  newton_cau_seq.limUnder
#align soln soln

private theorem soln_spec {ε : ℝ} (hε : ε > 0) :
    ∃ N : ℕ, ∀ {i : ℕ}, i ≥ N → ‖soln - newton_cau_seq i‖ < ε :=
  Setoid.symm (CauSeq.equiv_lim newton_cau_seq) _ hε
#align soln_spec soln_spec

private theorem soln_deriv_norm : ‖F.derivative.eval soln‖ = ‖F.derivative.eval a‖ :=
  norm_deriv_eq newton_seq_deriv_norm
#align soln_deriv_norm soln_deriv_norm

private theorem newton_seq_norm_tendsto_zero :
    Tendsto (fun i => ‖F.eval (newton_cau_seq i)‖) atTop (𝓝 0) :=
  squeeze_zero (fun _ => norm_nonneg _) newton_seq_norm_le bound'_sq
#align newton_seq_norm_tendsto_zero newton_seq_norm_tendsto_zero

private theorem newton_seq_dist_tendsto :
    Tendsto (fun n => ‖newton_cau_seq n - a‖) atTop (𝓝 (‖F.eval a‖ / ‖F.derivative.eval a‖)) :=
  tendsto_const_nhds.congr' <| eventually_atTop.2 ⟨1, fun _ hx => (newton_seq_dist_to_a _ hx).symm⟩
#align newton_seq_dist_tendsto newton_seq_dist_tendsto

private theorem newton_seq_dist_tendsto' :
    Tendsto (fun n => ‖newton_cau_seq n - a‖) atTop (𝓝 ‖soln - a‖) :=
  (continuous_norm.Tendsto _).comp (newton_cau_seq.tendsto_limit.sub tendsto_const_nhds)
#align newton_seq_dist_tendsto' newton_seq_dist_tendsto'

private theorem soln_dist_to_a : ‖soln - a‖ = ‖F.eval a‖ / ‖F.derivative.eval a‖ :=
  tendsto_nhds_unique newton_seq_dist_tendsto' newton_seq_dist_tendsto
#align soln_dist_to_a soln_dist_to_a

private theorem soln_dist_to_a_lt_deriv : ‖soln - a‖ < ‖F.derivative.eval a‖ :=
  by
  rw [soln_dist_to_a, div_lt_iff]
  · rwa [sq] at hnorm
  · apply deriv_norm_pos
    assumption
#align soln_dist_to_a_lt_deriv soln_dist_to_a_lt_deriv

private theorem eval_soln : F.eval soln = 0 :=
  limit_zero_of_norm_tendsto_zero newton_seq_norm_tendsto_zero
#align eval_soln eval_soln

private theorem soln_unique (z : ℤ_[p]) (hev : F.eval z = 0)
    (hnlt : ‖z - a‖ < ‖F.derivative.eval a‖) : z = soln :=
  have soln_dist : ‖z - soln‖ < ‖F.derivative.eval a‖ :=
    calc
      ‖z - soln‖ = ‖z - a + (a - soln)‖ := by rw [sub_add_sub_cancel]
      _ ≤ max ‖z - a‖ ‖a - soln‖ := (PadicInt.nonarchimedean _ _)
      _ < ‖F.derivative.eval a‖ := max_lt hnlt (norm_sub_rev soln a ▸ soln_dist_to_a_lt_deriv)
      
  let h := z - soln
  let ⟨q, hq⟩ := F.binomExpansion soln h
  have : (F.derivative.eval soln + q * h) * h = 0 :=
    Eq.symm
      (calc
        0 = F.eval (soln + h) := by simp [hev, h]
        _ = F.derivative.eval soln * h + q * h ^ 2 := by rw [hq, eval_soln, zero_add]
        _ = (F.derivative.eval soln + q * h) * h := by rw [sq, right_distrib, mul_assoc]
        )
  have : h = 0 :=
    by_contradiction fun hne =>
      have : F.derivative.eval soln + q * h = 0 :=
        (eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_right hne
      have : F.derivative.eval soln = -q * h := by simpa using eq_neg_of_add_eq_zero_left this
      lt_irrefl ‖F.derivative.eval soln‖
        (calc
          ‖F.derivative.eval soln‖ = ‖-q * h‖ := by rw [this]
          _ ≤ 1 * ‖h‖ := by
            rw [PadicInt.norm_mul]
            exact mul_le_mul_of_nonneg_right (PadicInt.norm_le_one _) (norm_nonneg _)
          _ = ‖z - soln‖ := by simp [h]
          _ < ‖F.derivative.eval soln‖ := by rw [soln_deriv_norm] <;> apply soln_dist
          )
  eq_of_sub_eq_zero (by rw [← this] <;> rfl)
#align soln_unique soln_unique

end Hensel

variable {p : ℕ} [Fact p.Prime] {F : Polynomial ℤ_[p]} {a : ℤ_[p]}

private theorem a_soln_is_unique (ha : F.eval a = 0) (z' : ℤ_[p]) (hz' : F.eval z' = 0)
    (hnormz' : ‖z' - a‖ < ‖F.derivative.eval a‖) : z' = a :=
  let h := z' - a
  let ⟨q, hq⟩ := F.binomExpansion a h
  have : (F.derivative.eval a + q * h) * h = 0 :=
    Eq.symm
      (calc
        0 = F.eval (a + h) := show 0 = F.eval (a + (z' - a)) by rw [add_comm] <;> simp [hz']
        _ = F.derivative.eval a * h + q * h ^ 2 := by rw [hq, ha, zero_add]
        _ = (F.derivative.eval a + q * h) * h := by rw [sq, right_distrib, mul_assoc]
        )
  have : h = 0 :=
    by_contradiction fun hne =>
      have : F.derivative.eval a + q * h = 0 :=
        (eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_right hne
      have : F.derivative.eval a = -q * h := by simpa using eq_neg_of_add_eq_zero_left this
      lt_irrefl ‖F.derivative.eval a‖
        (calc
          ‖F.derivative.eval a‖ = ‖q‖ * ‖h‖ := by simp [this]
          _ ≤ 1 * ‖h‖ := (mul_le_mul_of_nonneg_right (PadicInt.norm_le_one _) (norm_nonneg _))
          _ < ‖F.derivative.eval a‖ := by simpa [h]
          )
  eq_of_sub_eq_zero (by rw [← this] <;> rfl)
#align a_soln_is_unique a_soln_is_unique

variable (hnorm : ‖F.eval a‖ < ‖F.derivative.eval a‖ ^ 2)

include hnorm

private theorem a_is_soln (ha : F.eval a = 0) :
    F.eval a = 0 ∧
      ‖a - a‖ < ‖F.derivative.eval a‖ ∧
        ‖F.derivative.eval a‖ = ‖F.derivative.eval a‖ ∧
          ∀ z', F.eval z' = 0 → ‖z' - a‖ < ‖F.derivative.eval a‖ → z' = a :=
  ⟨ha, by simp [deriv_ne_zero hnorm], rfl, a_soln_is_unique ha⟩
#align a_is_soln a_is_soln

theorem hensels_lemma :
    ∃ z : ℤ_[p],
      F.eval z = 0 ∧
        ‖z - a‖ < ‖F.derivative.eval a‖ ∧
          ‖F.derivative.eval z‖ = ‖F.derivative.eval a‖ ∧
            ∀ z', F.eval z' = 0 → ‖z' - a‖ < ‖F.derivative.eval a‖ → z' = z :=
  if ha : F.eval a = 0 then ⟨a, a_is_soln hnorm ha⟩
  else by
    refine'
        ⟨soln _ _, eval_soln _ _, soln_dist_to_a_lt_deriv _ _, soln_deriv_norm _ _,
          soln_unique _ _⟩ <;>
      assumption
#align hensels_lemma hensels_lemma

