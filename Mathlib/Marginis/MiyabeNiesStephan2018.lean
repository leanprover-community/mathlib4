/-
Copyright (c) 2024 Bjørn Kjos-Hanssen· All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!

Marginis:
Miyabe, Nies, Stephan, `Randomness and Solovay degrees`, JLA, 2018, page 3 says:

`We sometimes identify a real α with its binary expansion X ∈ 2^ω`
`and the corresponding set X = {n ∈ ℕ : X (n) = 1 }`

Here we prove the well known fact that this representation is not unique.

We also show that consequently, if we use `Mathlib`'s current definition of
the pullback measure as of June 23, 2024 as a basis for a measure on Cantor space,
the Cantor space gets measure 0.
 -/

open MeasureTheory

/-- The natural "binary expansion" map from Cantor space to ℝ. -/
noncomputable def real_of_cantor : (ℕ → Bool) → ℝ :=
  fun x ↦ tsum (fun n : ℕ ↦ ite (x n = true) ((1 / 2) ^ (n+1)) 0)

/--  The classic geometric series summing to 1. -/
lemma geom_value : ∑' (n : ℕ), ((1:ℝ) / 2 ^ n.succ)  = 1 := by
  have E := tsum_geometric_two' 1
  nth_rewrite 2 [← E]
  apply tsum_congr
  intro b
  rw [Nat.succ_eq_add_one]
  ring_nf

/-- A minor variant of the geometric series is summable. -/
lemma geom_summable: Summable (fun n : ℕ ↦ (1:ℝ) / 2^n.succ) := by
  have h₀ : (fun i ↦ (1:ℝ) / 2^(i+1)) = (fun n ↦ (1/2)^(n) * (1/2)) := by
    apply funext;intro x;ring_nf
  have h₁ := @summable_mul_right_iff ℕ ℝ _ _ _ (fun x ↦ (1 / 2)^x) (1/2) (by simp)
  rw [h₀, h₁]
  exact NormedRing.summable_geometric_of_norm_lt_one
    (1/2) (by simp only [one_div, norm_inv, Real.norm_ofNat]; exact two_inv_lt_one)


/-- The sequence .0111... -/
def halfminus := fun n ↦ ite (n=0) false true

/-- The sequence .1000... -/
def halfplus  := fun n ↦ ite (n=0) true false

/-- In Cantor space, .0111... ≠ .1000... -/
lemma halfplus_ne_halfminus : halfplus ≠ halfminus := by
  intro hc
  have : true = false := calc
    true = halfplus 0  := rfl
    _    = halfminus 0 := by rw [hc];
    _    = false       := rfl
  tauto


/-- The binary number .0111... is equal to 1/2. -/
theorem real_of_cantor_halfminus : real_of_cantor halfminus = 1 / 2 :=
  add_left_cancel (by
    show  1/2 + real_of_cantor halfminus = 1/2 + 1/2
    unfold real_of_cantor halfminus
    simp only [Bool.if_true_right, Bool.or_false, Bool.not_eq_true', decide_eq_false_iff_not,
      inv_pow, ite_not]
    simp_rw [div_pow, one_pow]
    have t := pow_one (2:ℝ) ▸ tsum_eq_add_tsum_ite geom_summable 0
    rw [← t]
    rw [geom_value]
    exact (add_halves 1).symm)

/-- The natural map from Cantor space to ℝ is not injective. -/
lemma real_of_cantor_noninjective : real_of_cantor halfminus = real_of_cantor halfplus := by
  calc _ = 1/2 := real_of_cantor_halfminus
       _ = _   := by unfold real_of_cantor halfplus; simp_all

/-- Trying to define a measure on [0,1] in ℝ.  -/
noncomputable def CantorLebesgueMeasure₀ := Measure.comap real_of_cantor volume

/-- An undesired result, similar to 1/0=0. -/
lemma because_real_of_cantor_not_injective : CantorLebesgueMeasure₀ Set.univ = 0 := by
  unfold CantorLebesgueMeasure₀
  unfold Measure.comap
  split_ifs with H
  · simp
    exfalso
    let Q := H.1 real_of_cantor_noninjective
    exact halfplus_ne_halfminus Q.symm
  · contrapose H
    simp
    simp at H
