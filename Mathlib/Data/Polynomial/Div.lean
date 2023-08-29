/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import Mathlib.Data.Polynomial.AlgebraMap
import Mathlib.Data.Polynomial.Inductions
import Mathlib.Data.Polynomial.Monic
import Mathlib.RingTheory.Multiplicity

#align_import data.polynomial.div from "leanprover-community/mathlib"@"e1e7190efdcefc925cb36f257a8362ef22944204"

/-!
# Division of univariate polynomials

The main defs are `divByMonic` and `modByMonic`.
The compatibility between these is given by `modByMonic_add_div`.
We also define `rootMultiplicity`.
-/


noncomputable section

open Classical BigOperators Polynomial

open Finset

namespace Polynomial

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

section CommSemiring

variable [CommSemiring R]

theorem X_dvd_iff {f : R[X]} : X ∣ f ↔ f.coeff 0 = 0 :=
  ⟨fun ⟨g, hfg⟩ => by rw [hfg, mul_comm, coeff_mul_X_zero], fun hf =>
                      -- 🎉 no goals
    ⟨f.divX, by rw [mul_comm, ← add_zero (f.divX * X), ← C_0, ← hf, divX_mul_X_add]⟩⟩
                -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.X_dvd_iff Polynomial.X_dvd_iff

theorem X_pow_dvd_iff {f : R[X]} {n : ℕ} : X ^ n ∣ f ↔ ∀ d < n, f.coeff d = 0 :=
  ⟨fun ⟨g, hgf⟩ d hd => by
    simp only [hgf, coeff_X_pow_mul', ite_eq_right_iff, not_le_of_lt hd, IsEmpty.forall_iff],
    -- 🎉 no goals
    fun hd => by
    induction' n with n hn
    -- ⊢ X ^ Nat.zero ∣ f
    · simp [pow_zero, one_dvd]
      -- 🎉 no goals
    · obtain ⟨g, hgf⟩ := hn fun d : ℕ => fun H : d < n => hd _ (Nat.lt_succ_of_lt H)
      -- ⊢ X ^ Nat.succ n ∣ f
      have := coeff_X_pow_mul g n 0
      -- ⊢ X ^ Nat.succ n ∣ f
      rw [zero_add, ← hgf, hd n (Nat.lt_succ_self n)] at this
      -- ⊢ X ^ Nat.succ n ∣ f
      obtain ⟨k, hgk⟩ := Polynomial.X_dvd_iff.mpr this.symm
      -- ⊢ X ^ Nat.succ n ∣ f
      use k
      -- ⊢ f = X ^ Nat.succ n * k
      rwa [pow_succ, mul_comm X _, mul_assoc, ← hgk]⟩
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.X_pow_dvd_iff Polynomial.X_pow_dvd_iff

end CommSemiring

section CommSemiring

variable [CommSemiring R] {p q : R[X]}

theorem multiplicity_finite_of_degree_pos_of_monic (hp : (0 : WithBot ℕ) < degree p) (hmp : Monic p)
    (hq : q ≠ 0) : multiplicity.Finite p q :=
  have zn0 : (0 : R) ≠ 1 :=
    haveI := Nontrivial.of_polynomial_ne hq
    zero_ne_one
  ⟨natDegree q, fun ⟨r, hr⟩ => by
    have hp0 : p ≠ 0 := fun hp0 => by simp [hp0] at hp
    -- ⊢ False
    have hr0 : r ≠ 0 := fun hr0 => by subst hr0; simp [hq] at hr
    -- ⊢ False
    have hpn1 : leadingCoeff p ^ (natDegree q + 1) = 1 := by simp [show _ = _ from hmp]
    -- ⊢ False
    have hpn0' : leadingCoeff p ^ (natDegree q + 1) ≠ 0 := hpn1.symm ▸ zn0.symm
    -- ⊢ False
    have hpnr0 : leadingCoeff (p ^ (natDegree q + 1)) * leadingCoeff r ≠ 0 := by
      simp only [leadingCoeff_pow' hpn0', leadingCoeff_eq_zero, hpn1, one_pow, one_mul, Ne.def,
          hr0]
    have hnp : 0 < natDegree p := by
      rw [← WithBot.coe_lt_coe, ← Nat.cast_withBot, ← Nat.cast_withBot,
        ← degree_eq_natDegree hp0]; exact hp
    have := congr_arg natDegree hr
    -- ⊢ False
    rw [natDegree_mul' hpnr0, natDegree_pow' hpn0', add_mul, add_assoc] at this
    -- ⊢ False
    exact
      ne_of_lt
        (lt_add_of_le_of_pos (le_mul_of_one_le_right (Nat.zero_le _) hnp)
          (add_pos_of_pos_of_nonneg (by rwa [one_mul]) (Nat.zero_le _)))
        this⟩
#align polynomial.multiplicity_finite_of_degree_pos_of_monic Polynomial.multiplicity_finite_of_degree_pos_of_monic

end CommSemiring

section Ring

variable [Ring R] {p q : R[X]}

theorem div_wf_lemma (h : degree q ≤ degree p ∧ p ≠ 0) (hq : Monic q) :
    degree (p - C (leadingCoeff p) * X ^ (natDegree p - natDegree q) * q) < degree p :=
  have hp : leadingCoeff p ≠ 0 := mt leadingCoeff_eq_zero.1 h.2
  have hq0 : q ≠ 0 := hq.ne_zero_of_polynomial_ne h.2
  have hlt : natDegree q ≤ natDegree p :=
    WithBot.coe_le_coe.1
      (by rw [← Nat.cast_withBot, ← Nat.cast_withBot, ← degree_eq_natDegree h.2,
        ← degree_eq_natDegree hq0]; exact h.1)
                                    -- 🎉 no goals
  degree_sub_lt
    (by
      rw [hq.degree_mul, degree_C_mul_X_pow _ hp, degree_eq_natDegree h.2,
        degree_eq_natDegree hq0, ← Nat.cast_add, tsub_add_cancel_of_le hlt])
    h.2 (by rw [leadingCoeff_mul_monic hq, leadingCoeff_mul_X_pow, leadingCoeff_C])
            -- 🎉 no goals
#align polynomial.div_wf_lemma Polynomial.div_wf_lemma

/-- See `divByMonic`. -/
noncomputable def divModByMonicAux : ∀ (_p : R[X]) {q : R[X]}, Monic q → R[X] × R[X]
  | p, q, hq =>
    if h : degree q ≤ degree p ∧ p ≠ 0 then
      let z := C (leadingCoeff p) * X ^ (natDegree p - natDegree q)
      have _wf := div_wf_lemma h hq
      let dm := divModByMonicAux (p - z * q) hq
      ⟨z + dm.1, dm.2⟩
    else ⟨0, p⟩
  termination_by divModByMonicAux p q hq => p
#align polynomial.div_mod_by_monic_aux Polynomial.divModByMonicAux

/-- `divByMonic` gives the quotient of `p` by a monic polynomial `q`. -/
def divByMonic (p q : R[X]) : R[X] :=
  if hq : Monic q then (divModByMonicAux p hq).1 else 0
#align polynomial.div_by_monic Polynomial.divByMonic

/-- `modByMonic` gives the remainder of `p` by a monic polynomial `q`. -/
def modByMonic (p q : R[X]) : R[X] :=
  if hq : Monic q then (divModByMonicAux p hq).2 else p
#align polynomial.mod_by_monic Polynomial.modByMonic

@[inherit_doc]
infixl:70 " /ₘ " => divByMonic

@[inherit_doc]
infixl:70 " %ₘ " => modByMonic

theorem degree_modByMonic_lt [Nontrivial R] :
    ∀ (p : R[X]) {q : R[X]} (_hq : Monic q), degree (p %ₘ q) < degree q
  | p, q, hq =>
    if h : degree q ≤ degree p ∧ p ≠ 0 then by
      have _wf := div_wf_lemma ⟨h.1, h.2⟩ hq
      -- ⊢ degree (p %ₘ q) < degree q
      have :
        degree ((p - C (leadingCoeff p) * X ^ (natDegree p - natDegree q) * q) %ₘ q) < degree q :=
        degree_modByMonic_lt (p - C (leadingCoeff p) * X ^ (natDegree p - natDegree q) * q) hq
      unfold modByMonic at this ⊢
      -- ⊢ degree (if hq : Monic q then (divModByMonicAux p hq).snd else p) < degree q
      unfold divModByMonicAux
      -- ⊢ degree
      dsimp
      -- ⊢ degree (if h : Monic q then (if degree q ≤ degree p ∧ ¬p = 0 then (↑C (leadi …
      rw [dif_pos hq] at this ⊢
      -- ⊢ degree (if degree q ≤ degree p ∧ ¬p = 0 then (↑C (leadingCoeff p) * X ^ (nat …
      rw [if_pos h]
      -- ⊢ degree (↑C (leadingCoeff p) * X ^ (natDegree p - natDegree q) + (divModByMon …
      exact this
      -- 🎉 no goals
    else
      Or.casesOn (not_and_or.1 h)
        (by
          unfold modByMonic divModByMonicAux
          -- ⊢ ¬degree q ≤ degree p →
          dsimp
          -- ⊢ ¬degree q ≤ degree p → degree (if h : Monic q then (if degree q ≤ degree p ∧ …
          rw [dif_pos hq, if_neg h]
          -- ⊢ ¬degree q ≤ degree p → degree (0, p).snd < degree q
          exact lt_of_not_ge)
          -- 🎉 no goals
        (by
          intro hp
          -- ⊢ degree (p %ₘ q) < degree q
          unfold modByMonic divModByMonicAux
          -- ⊢ degree
          dsimp
          -- ⊢ degree (if h : Monic q then (if degree q ≤ degree p ∧ ¬p = 0 then (↑C (leadi …
          rw [dif_pos hq, if_neg h, Classical.not_not.1 hp]
          -- ⊢ degree (0, 0).snd < degree q
          exact lt_of_le_of_ne bot_le (Ne.symm (mt degree_eq_bot.1 hq.ne_zero)))
          -- 🎉 no goals
  termination_by degree_modByMonic_lt p q hq => p
#align polynomial.degree_mod_by_monic_lt Polynomial.degree_modByMonic_lt

@[simp]
theorem zero_modByMonic (p : R[X]) : 0 %ₘ p = 0 := by
  unfold modByMonic divModByMonicAux
  -- ⊢ (if h : Monic p then
  dsimp
  -- ⊢ (if h : Monic p then (if degree p ≤ ⊥ ∧ ¬0 = 0 then (↑C 0 * X ^ (0 - natDegr …
  by_cases hp : Monic p
  -- ⊢ (if h : Monic p then (if degree p ≤ ⊥ ∧ ¬0 = 0 then (↑C 0 * X ^ (0 - natDegr …
  · rw [dif_pos hp, if_neg (mt And.right (not_not_intro rfl))]
    -- 🎉 no goals
  · rw [dif_neg hp]
    -- 🎉 no goals
#align polynomial.zero_mod_by_monic Polynomial.zero_modByMonic

@[simp]
theorem zero_divByMonic (p : R[X]) : 0 /ₘ p = 0 := by
  unfold divByMonic divModByMonicAux
  -- ⊢ (if h : Monic p then
  dsimp
  -- ⊢ (if h : Monic p then (if degree p ≤ ⊥ ∧ ¬0 = 0 then (↑C 0 * X ^ (0 - natDegr …
  by_cases hp : Monic p
  -- ⊢ (if h : Monic p then (if degree p ≤ ⊥ ∧ ¬0 = 0 then (↑C 0 * X ^ (0 - natDegr …
  · rw [dif_pos hp, if_neg (mt And.right (not_not_intro rfl))]
    -- 🎉 no goals
  · rw [dif_neg hp]
    -- 🎉 no goals
#align polynomial.zero_div_by_monic Polynomial.zero_divByMonic

@[simp]
theorem modByMonic_zero (p : R[X]) : p %ₘ 0 = p :=
  if h : Monic (0 : R[X]) then by
    haveI := monic_zero_iff_subsingleton.mp h
    -- ⊢ p %ₘ 0 = p
    simp
    -- 🎉 no goals
  else by unfold modByMonic divModByMonicAux; rw [dif_neg h]
          -- ⊢ (if h : Monic 0 then
                                              -- 🎉 no goals
#align polynomial.mod_by_monic_zero Polynomial.modByMonic_zero

@[simp]
theorem divByMonic_zero (p : R[X]) : p /ₘ 0 = 0 :=
  if h : Monic (0 : R[X]) then by
    haveI := monic_zero_iff_subsingleton.mp h
    -- ⊢ p /ₘ 0 = 0
    simp
    -- 🎉 no goals
  else by unfold divByMonic divModByMonicAux; rw [dif_neg h]
          -- ⊢ (if h : Monic 0 then
                                              -- 🎉 no goals
#align polynomial.div_by_monic_zero Polynomial.divByMonic_zero

theorem divByMonic_eq_of_not_monic (p : R[X]) (hq : ¬Monic q) : p /ₘ q = 0 :=
  dif_neg hq
#align polynomial.div_by_monic_eq_of_not_monic Polynomial.divByMonic_eq_of_not_monic

theorem modByMonic_eq_of_not_monic (p : R[X]) (hq : ¬Monic q) : p %ₘ q = p :=
  dif_neg hq
#align polynomial.mod_by_monic_eq_of_not_monic Polynomial.modByMonic_eq_of_not_monic

theorem modByMonic_eq_self_iff [Nontrivial R] (hq : Monic q) : p %ₘ q = p ↔ degree p < degree q :=
  ⟨fun h => h ▸ degree_modByMonic_lt _ hq, fun h => by
    have : ¬degree q ≤ degree p := not_le_of_gt h
    -- ⊢ p %ₘ q = p
    unfold modByMonic divModByMonicAux; dsimp; rw [dif_pos hq, if_neg (mt And.left this)]⟩
    -- ⊢ (if h : Monic q then
                                        -- ⊢ (if h : Monic q then (if degree q ≤ degree p ∧ ¬p = 0 then (↑C (leadingCoeff …
                                               -- 🎉 no goals
#align polynomial.mod_by_monic_eq_self_iff Polynomial.modByMonic_eq_self_iff

theorem degree_modByMonic_le (p : R[X]) {q : R[X]} (hq : Monic q) : degree (p %ₘ q) ≤ degree q := by
  nontriviality R
  -- ⊢ degree (p %ₘ q) ≤ degree q
  exact (degree_modByMonic_lt _ hq).le
  -- 🎉 no goals
#align polynomial.degree_mod_by_monic_le Polynomial.degree_modByMonic_le

end Ring

section CommRing

variable [CommRing R] {p q : R[X]}

theorem modByMonic_eq_sub_mul_div :
    ∀ (p : R[X]) {q : R[X]} (_hq : Monic q), p %ₘ q = p - q * (p /ₘ q)
  | p, q, hq =>
    if h : degree q ≤ degree p ∧ p ≠ 0 then by
      have _wf := div_wf_lemma h hq
      -- ⊢ p %ₘ q = p - q * (p /ₘ q)
      have ih :=
        modByMonic_eq_sub_mul_div (p - C (leadingCoeff p) * X ^ (natDegree p - natDegree q) * q) hq
      unfold modByMonic divByMonic divModByMonicAux
      -- ⊢ (if h : Monic q then
      dsimp
      -- ⊢ (if h : Monic q then (if degree q ≤ degree p ∧ ¬p = 0 then (↑C (leadingCoeff …
      rw [dif_pos hq, if_pos h]
      -- ⊢ (↑C (leadingCoeff p) * X ^ (natDegree p - natDegree q) + (divModByMonicAux ( …
      rw [modByMonic, dif_pos hq] at ih
      -- ⊢ (↑C (leadingCoeff p) * X ^ (natDegree p - natDegree q) + (divModByMonicAux ( …
      refine' ih.trans _
      -- ⊢ p - ↑C (leadingCoeff p) * X ^ (natDegree p - natDegree q) * q - q * ((p - ↑C …
      unfold divByMonic
      -- ⊢ (p - ↑C (leadingCoeff p) * X ^ (natDegree p - natDegree q) * q - q * if hq : …
      rw [dif_pos hq, dif_pos hq, if_pos h, mul_add, sub_add_eq_sub_sub, mul_comm]
      -- 🎉 no goals
    else by
      unfold modByMonic divByMonic divModByMonicAux
      -- ⊢ (if h : Monic q then
      dsimp
      -- ⊢ (if h : Monic q then (if degree q ≤ degree p ∧ ¬p = 0 then (↑C (leadingCoeff …
      rw [dif_pos hq, if_neg h, dif_pos hq, if_neg h, mul_zero, sub_zero]
      -- 🎉 no goals
  termination_by modByMonic_eq_sub_mul_div p q hq => p
#align polynomial.mod_by_monic_eq_sub_mul_div Polynomial.modByMonic_eq_sub_mul_div

theorem modByMonic_add_div (p : R[X]) {q : R[X]} (hq : Monic q) : p %ₘ q + q * (p /ₘ q) = p :=
  eq_sub_iff_add_eq.1 (modByMonic_eq_sub_mul_div p hq)
#align polynomial.mod_by_monic_add_div Polynomial.modByMonic_add_div

theorem divByMonic_eq_zero_iff [Nontrivial R] (hq : Monic q) : p /ₘ q = 0 ↔ degree p < degree q :=
  ⟨fun h => by
    have := modByMonic_add_div p hq;
    -- ⊢ degree p < degree q
      rwa [h, mul_zero, add_zero, modByMonic_eq_self_iff hq] at this,
      -- 🎉 no goals
    fun h => by
    have : ¬degree q ≤ degree p := not_le_of_gt h
    -- ⊢ p /ₘ q = 0
    unfold divByMonic divModByMonicAux; dsimp; rw [dif_pos hq, if_neg (mt And.left this)]⟩
    -- ⊢ (if h : Monic q then
                                        -- ⊢ (if h : Monic q then (if degree q ≤ degree p ∧ ¬p = 0 then (↑C (leadingCoeff …
                                               -- 🎉 no goals
#align polynomial.div_by_monic_eq_zero_iff Polynomial.divByMonic_eq_zero_iff

theorem degree_add_divByMonic (hq : Monic q) (h : degree q ≤ degree p) :
    degree q + degree (p /ₘ q) = degree p := by
  nontriviality R
  -- ⊢ degree q + degree (p /ₘ q) = degree p
  have hdiv0 : p /ₘ q ≠ 0 := by rwa [Ne.def, divByMonic_eq_zero_iff hq, not_lt]
  -- ⊢ degree q + degree (p /ₘ q) = degree p
  have hlc : leadingCoeff q * leadingCoeff (p /ₘ q) ≠ 0 := by
    rwa [Monic.def.1 hq, one_mul, Ne.def, leadingCoeff_eq_zero]
  have hmod : degree (p %ₘ q) < degree (q * (p /ₘ q)) :=
    calc
      degree (p %ₘ q) < degree q := degree_modByMonic_lt _ hq
      _ ≤ _ := by
        rw [degree_mul' hlc, degree_eq_natDegree hq.ne_zero, degree_eq_natDegree hdiv0, ←
            Nat.cast_add, Nat.cast_withBot, Nat.cast_withBot, WithBot.coe_le_coe]
        exact Nat.le_add_right _ _
  calc
    degree q + degree (p /ₘ q) = degree (q * (p /ₘ q)) := Eq.symm (degree_mul' hlc)
    _ = degree (p %ₘ q + q * (p /ₘ q)) := (degree_add_eq_right_of_degree_lt hmod).symm
    _ = _ := congr_arg _ (modByMonic_add_div _ hq)
#align polynomial.degree_add_div_by_monic Polynomial.degree_add_divByMonic

theorem degree_divByMonic_le (p q : R[X]) : degree (p /ₘ q) ≤ degree p :=
  if hp0 : p = 0 then by simp only [hp0, zero_divByMonic, le_refl]
                         -- 🎉 no goals
  else
    if hq : Monic q then
      if h : degree q ≤ degree p then by
        haveI := Nontrivial.of_polynomial_ne hp0;
        -- ⊢ degree (p /ₘ q) ≤ degree p
            rw [← degree_add_divByMonic hq h, degree_eq_natDegree hq.ne_zero,
              degree_eq_natDegree (mt (divByMonic_eq_zero_iff hq).1 (not_lt.2 h))];
          exact WithBot.coe_le_coe.2 (Nat.le_add_left _ _)
          -- 🎉 no goals
      else by
        unfold divByMonic divModByMonicAux;
        -- ⊢ degree
          simp [dif_pos hq, h, false_and_iff, if_false, degree_zero, bot_le]
          -- 🎉 no goals
    else (divByMonic_eq_of_not_monic p hq).symm ▸ bot_le
#align polynomial.degree_div_by_monic_le Polynomial.degree_divByMonic_le

theorem degree_divByMonic_lt (p : R[X]) {q : R[X]} (hq : Monic q) (hp0 : p ≠ 0)
    (h0q : 0 < degree q) : degree (p /ₘ q) < degree p :=
  if hpq : degree p < degree q then by
    haveI := Nontrivial.of_polynomial_ne hp0
    -- ⊢ degree (p /ₘ q) < degree p
    rw [(divByMonic_eq_zero_iff hq).2 hpq, degree_eq_natDegree hp0]
    -- ⊢ degree 0 < ↑(natDegree p)
    exact WithBot.bot_lt_coe _
    -- 🎉 no goals
  else by
    haveI := Nontrivial.of_polynomial_ne hp0
    -- ⊢ degree (p /ₘ q) < degree p
    rw [← degree_add_divByMonic hq (not_lt.1 hpq), degree_eq_natDegree hq.ne_zero,
      degree_eq_natDegree (mt (divByMonic_eq_zero_iff hq).1 hpq)]
    exact
      WithBot.coe_lt_coe.2
        (Nat.lt_add_of_pos_left (WithBot.coe_lt_coe.1 <|
          by simpa [Nat.cast_withBot, degree_eq_natDegree hq.ne_zero] using h0q))
#align polynomial.degree_div_by_monic_lt Polynomial.degree_divByMonic_lt

theorem natDegree_divByMonic {R : Type u} [CommRing R] (f : R[X]) {g : R[X]} (hg : g.Monic) :
    natDegree (f /ₘ g) = natDegree f - natDegree g := by
  nontriviality R
  -- ⊢ natDegree (f /ₘ g) = natDegree f - natDegree g
  by_cases hfg : f /ₘ g = 0
  -- ⊢ natDegree (f /ₘ g) = natDegree f - natDegree g
  · rw [hfg, natDegree_zero]
    -- ⊢ 0 = natDegree f - natDegree g
    rw [divByMonic_eq_zero_iff hg] at hfg
    -- ⊢ 0 = natDegree f - natDegree g
    rw [tsub_eq_zero_iff_le.mpr (natDegree_le_natDegree <| le_of_lt hfg)]
    -- 🎉 no goals
  have hgf := hfg
  -- ⊢ natDegree (f /ₘ g) = natDegree f - natDegree g
  rw [divByMonic_eq_zero_iff hg] at hgf
  -- ⊢ natDegree (f /ₘ g) = natDegree f - natDegree g
  push_neg at hgf
  -- ⊢ natDegree (f /ₘ g) = natDegree f - natDegree g
  have := degree_add_divByMonic hg hgf
  -- ⊢ natDegree (f /ₘ g) = natDegree f - natDegree g
  have hf : f ≠ 0 := by
    intro hf
    apply hfg
    rw [hf, zero_divByMonic]
  rw [degree_eq_natDegree hf, degree_eq_natDegree hg.ne_zero, degree_eq_natDegree hfg,
    Nat.cast_withBot, Nat.cast_withBot, Nat.cast_withBot,
    ← WithBot.coe_add, WithBot.coe_eq_coe] at this
  rw [← this, add_tsub_cancel_left]
  -- 🎉 no goals
#align polynomial.nat_degree_div_by_monic Polynomial.natDegree_divByMonic

theorem div_modByMonic_unique {f g} (q r : R[X]) (hg : Monic g)
    (h : r + g * q = f ∧ degree r < degree g) : f /ₘ g = q ∧ f %ₘ g = r := by
  nontriviality R
  -- ⊢ f /ₘ g = q ∧ f %ₘ g = r
  have h₁ : r - f %ₘ g = -g * (q - f /ₘ g) :=
    eq_of_sub_eq_zero
      (by
        rw [← sub_eq_zero_of_eq (h.1.trans (modByMonic_add_div f hg).symm)]
        simp [mul_add, mul_comm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc])
  have h₂ : degree (r - f %ₘ g) = degree (g * (q - f /ₘ g)) := by simp [h₁]
  -- ⊢ f /ₘ g = q ∧ f %ₘ g = r
  have h₄ : degree (r - f %ₘ g) < degree g :=
    calc
      degree (r - f %ₘ g) ≤ max (degree r) (degree (f %ₘ g)) := degree_sub_le _ _
      _ < degree g := max_lt_iff.2 ⟨h.2, degree_modByMonic_lt _ hg⟩
  have h₅ : q - f /ₘ g = 0 :=
    _root_.by_contradiction fun hqf =>
      not_le_of_gt h₄ <|
        calc
          degree g ≤ degree g + degree (q - f /ₘ g) := by
            erw [degree_eq_natDegree hg.ne_zero, degree_eq_natDegree hqf, WithBot.coe_le_coe]
            exact Nat.le_add_right _ _
          _ = degree (r - f %ₘ g) := by rw [h₂, degree_mul']; simpa [Monic.def.1 hg]
  exact ⟨Eq.symm <| eq_of_sub_eq_zero h₅, Eq.symm <| eq_of_sub_eq_zero <| by simpa [h₅] using h₁⟩
  -- 🎉 no goals
#align polynomial.div_mod_by_monic_unique Polynomial.div_modByMonic_unique

theorem map_mod_divByMonic [CommRing S] (f : R →+* S) (hq : Monic q) :
    (p /ₘ q).map f = p.map f /ₘ q.map f ∧ (p %ₘ q).map f = p.map f %ₘ q.map f := by
  nontriviality S
  -- ⊢ map f (p /ₘ q) = map f p /ₘ map f q ∧ map f (p %ₘ q) = map f p %ₘ map f q
  haveI : Nontrivial R := f.domain_nontrivial
  -- ⊢ map f (p /ₘ q) = map f p /ₘ map f q ∧ map f (p %ₘ q) = map f p %ₘ map f q
  have : map f p /ₘ map f q = map f (p /ₘ q) ∧ map f p %ₘ map f q = map f (p %ₘ q) :=
    div_modByMonic_unique ((p /ₘ q).map f) _ (hq.map f)
      ⟨Eq.symm <| by rw [← Polynomial.map_mul, ← Polynomial.map_add, modByMonic_add_div _ hq],
        calc
          _ ≤ degree (p %ₘ q) := degree_map_le _ _
          _ < degree q := (degree_modByMonic_lt _ hq)
          _ = _ :=
            Eq.symm <|
              degree_map_eq_of_leadingCoeff_ne_zero _
                (by rw [Monic.def.1 hq, f.map_one]; exact one_ne_zero)⟩
  exact ⟨this.1.symm, this.2.symm⟩
  -- 🎉 no goals
#align polynomial.map_mod_div_by_monic Polynomial.map_mod_divByMonic

theorem map_divByMonic [CommRing S] (f : R →+* S) (hq : Monic q) :
    (p /ₘ q).map f = p.map f /ₘ q.map f :=
  (map_mod_divByMonic f hq).1
#align polynomial.map_div_by_monic Polynomial.map_divByMonic

theorem map_modByMonic [CommRing S] (f : R →+* S) (hq : Monic q) :
    (p %ₘ q).map f = p.map f %ₘ q.map f :=
  (map_mod_divByMonic f hq).2
#align polynomial.map_mod_by_monic Polynomial.map_modByMonic

theorem dvd_iff_modByMonic_eq_zero (hq : Monic q) : p %ₘ q = 0 ↔ q ∣ p :=
  ⟨fun h => by rw [← modByMonic_add_div p hq, h, zero_add]; exact dvd_mul_right _ _, fun h => by
               -- ⊢ q ∣ q * (p /ₘ q)
                                                            -- 🎉 no goals
    nontriviality R
    -- ⊢ p %ₘ q = 0
    obtain ⟨r, hr⟩ := exists_eq_mul_right_of_dvd h
    -- ⊢ p %ₘ q = 0
    by_contra hpq0
    -- ⊢ False
    have hmod : p %ₘ q = q * (r - p /ₘ q) := by rw [modByMonic_eq_sub_mul_div _ hq, mul_sub, ← hr]
    -- ⊢ False
    have : degree (q * (r - p /ₘ q)) < degree q := hmod ▸ degree_modByMonic_lt _ hq
    -- ⊢ False
    have hrpq0 : leadingCoeff (r - p /ₘ q) ≠ 0 := fun h =>
      hpq0 <|
        leadingCoeff_eq_zero.1
          (by rw [hmod, leadingCoeff_eq_zero.1 h, mul_zero, leadingCoeff_zero])
    have hlc : leadingCoeff q * leadingCoeff (r - p /ₘ q) ≠ 0 := by rwa [Monic.def.1 hq, one_mul]
    -- ⊢ False
    rw [degree_mul' hlc, degree_eq_natDegree hq.ne_zero,
      degree_eq_natDegree (mt leadingCoeff_eq_zero.2 hrpq0)] at this
    exact not_lt_of_ge (Nat.le_add_right _ _) (WithBot.some_lt_some.1 this)⟩
    -- 🎉 no goals
#align polynomial.dvd_iff_mod_by_monic_eq_zero Polynomial.dvd_iff_modByMonic_eq_zero

theorem map_dvd_map [CommRing S] (f : R →+* S) (hf : Function.Injective f) {x y : R[X]}
    (hx : x.Monic) : x.map f ∣ y.map f ↔ x ∣ y := by
  rw [← dvd_iff_modByMonic_eq_zero hx, ← dvd_iff_modByMonic_eq_zero (hx.map f), ←
    map_modByMonic f hx]
  exact
    ⟨fun H => map_injective f hf <| by rw [H, Polynomial.map_zero], fun H => by
      rw [H, Polynomial.map_zero]⟩
#align polynomial.map_dvd_map Polynomial.map_dvd_map

@[simp]
theorem modByMonic_one (p : R[X]) : p %ₘ 1 = 0 :=
  (dvd_iff_modByMonic_eq_zero (by convert monic_one (R := R))).2 (one_dvd _)
                                  -- 🎉 no goals
#align polynomial.mod_by_monic_one Polynomial.modByMonic_one

@[simp]
theorem divByMonic_one (p : R[X]) : p /ₘ 1 = p := by
  conv_rhs => rw [← modByMonic_add_div p monic_one]; simp
  -- 🎉 no goals
#align polynomial.div_by_monic_one Polynomial.divByMonic_one

@[simp]
theorem modByMonic_X_sub_C_eq_C_eval (p : R[X]) (a : R) : p %ₘ (X - C a) = C (p.eval a) := by
  nontriviality R
  -- ⊢ p %ₘ (X - ↑C a) = ↑C (eval a p)
  have h : (p %ₘ (X - C a)).eval a = p.eval a := by
    rw [modByMonic_eq_sub_mul_div _ (monic_X_sub_C a), eval_sub, eval_mul, eval_sub, eval_X,
      eval_C, sub_self, zero_mul, sub_zero]
  have : degree (p %ₘ (X - C a)) < 1 :=
    degree_X_sub_C a ▸ degree_modByMonic_lt p (monic_X_sub_C a)
  have : degree (p %ₘ (X - C a)) ≤ 0 := by
    revert this
    cases degree (p %ₘ (X - C a))
    · exact fun _ => bot_le
    · exact fun h => WithBot.some_le_some.2 (Nat.le_of_lt_succ (WithBot.some_lt_some.1 h))
  rw [eq_C_of_degree_le_zero this, eval_C] at h
  -- ⊢ p %ₘ (X - ↑C a) = ↑C (eval a p)
  rw [eq_C_of_degree_le_zero this, h]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.mod_by_monic_X_sub_C_eq_C_eval Polynomial.modByMonic_X_sub_C_eq_C_eval

theorem mul_divByMonic_eq_iff_isRoot : (X - C a) * (p /ₘ (X - C a)) = p ↔ IsRoot p a :=
  ⟨fun h => by
    rw [← h, IsRoot.def, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul],
    -- 🎉 no goals
    fun h : p.eval a = 0 => by
    conv_rhs =>
        rw [← modByMonic_add_div p (monic_X_sub_C a)]
        rw [modByMonic_X_sub_C_eq_C_eval, h, C_0, zero_add]⟩
#align polynomial.mul_div_by_monic_eq_iff_is_root Polynomial.mul_divByMonic_eq_iff_isRoot

theorem dvd_iff_isRoot : X - C a ∣ p ↔ IsRoot p a :=
  ⟨fun h => by
    rwa [← dvd_iff_modByMonic_eq_zero (monic_X_sub_C _), modByMonic_X_sub_C_eq_C_eval, ← C_0,
      C_inj] at h,
    fun h => ⟨p /ₘ (X - C a), by rw [mul_divByMonic_eq_iff_isRoot.2 h]⟩⟩
                                 -- 🎉 no goals
#align polynomial.dvd_iff_is_root Polynomial.dvd_iff_isRoot

theorem X_sub_C_dvd_sub_C_eval : X - C a ∣ p - C (p.eval a) := by
  rw [dvd_iff_isRoot, IsRoot, eval_sub, eval_C, sub_self]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.X_sub_C_dvd_sub_C_eval Polynomial.X_sub_C_dvd_sub_C_eval

theorem mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero {b : R[X]} {P : R[X][X]} :
    P ∈ Ideal.span {C (X - C a), X - C b} ↔ (P.eval b).eval a = 0 := by
  rw [Ideal.mem_span_pair]
  -- ⊢ (∃ a_1 b_1, a_1 * ↑C (X - ↑C a) + b_1 * (X - ↑C b) = P) ↔ eval a (eval b P)  …
  constructor <;> intro h
  -- ⊢ (∃ a_1 b_1, a_1 * ↑C (X - ↑C a) + b_1 * (X - ↑C b) = P) → eval a (eval b P)  …
                  -- ⊢ eval a (eval b P) = 0
                  -- ⊢ ∃ a_1 b_1, a_1 * ↑C (X - ↑C a) + b_1 * (X - ↑C b) = P
  · rcases h with ⟨_, _, rfl⟩
    -- ⊢ eval a (eval b (w✝¹ * ↑C (X - ↑C a) + w✝ * (X - ↑C b))) = 0
    simp only [eval_C, eval_X, eval_add, eval_sub, eval_mul, add_zero, mul_zero, sub_self]
    -- 🎉 no goals
  · rcases dvd_iff_isRoot.mpr h with ⟨p, hp⟩
    -- ⊢ ∃ a_1 b_1, a_1 * ↑C (X - ↑C a) + b_1 * (X - ↑C b) = P
    rcases @X_sub_C_dvd_sub_C_eval _ b _ P with ⟨q, hq⟩
    -- ⊢ ∃ a_1 b_1, a_1 * ↑C (X - ↑C a) + b_1 * (X - ↑C b) = P
    exact ⟨C p, q, by rw [mul_comm, mul_comm q, eq_add_of_sub_eq' hq, hp, C_mul]⟩
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero Polynomial.mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero

theorem modByMonic_X (p : R[X]) : p %ₘ X = C (p.eval 0) := by
  rw [← modByMonic_X_sub_C_eq_C_eval, C_0, sub_zero]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.mod_by_monic_X Polynomial.modByMonic_X

theorem eval₂_modByMonic_eq_self_of_root [CommRing S] {f : R →+* S} {p q : R[X]} (hq : q.Monic)
    {x : S} (hx : q.eval₂ f x = 0) : (p %ₘ q).eval₂ f x = p.eval₂ f x := by
  rw [modByMonic_eq_sub_mul_div p hq, eval₂_sub, eval₂_mul, hx, zero_mul, sub_zero]
  -- 🎉 no goals
#align polynomial.eval₂_mod_by_monic_eq_self_of_root Polynomial.eval₂_modByMonic_eq_self_of_root

theorem sum_modByMonic_coeff (hq : q.Monic) {n : ℕ} (hn : q.degree ≤ n) :
    (∑ i : Fin n, monomial i ((p %ₘ q).coeff i)) = p %ₘ q := by
  nontriviality R
  -- ⊢ ∑ i : Fin n, ↑(monomial ↑i) (coeff (p %ₘ q) ↑i) = p %ₘ q
  exact
    (sum_fin (fun i c => monomial i c) (by simp) ((degree_modByMonic_lt _ hq).trans_le hn)).trans
      (sum_monomial_eq _)
#align polynomial.sum_mod_by_monic_coeff Polynomial.sum_modByMonic_coeff

theorem sub_dvd_eval_sub (a b : R) (p : R[X]) : a - b ∣ p.eval a - p.eval b := by
  suffices X - C b ∣ p - C (p.eval b) by
    simpa only [coe_evalRingHom, eval_sub, eval_X, eval_C] using (evalRingHom a).map_dvd this
  simp [dvd_iff_isRoot]
  -- 🎉 no goals
#align polynomial.sub_dvd_eval_sub Polynomial.sub_dvd_eval_sub

theorem mul_div_mod_by_monic_cancel_left (p : R[X]) {q : R[X]} (hmo : q.Monic) :
    q * p /ₘ q = p := by
  nontriviality R
  -- ⊢ q * p /ₘ q = p
  refine' (div_modByMonic_unique _ 0 hmo ⟨by rw [zero_add], _⟩).1
  -- ⊢ degree 0 < degree q
  rw [degree_zero]
  -- ⊢ ⊥ < degree q
  exact Ne.bot_lt fun h => hmo.ne_zero (degree_eq_bot.1 h)
  -- 🎉 no goals
#align polynomial.mul_div_mod_by_monic_cancel_left Polynomial.mul_div_mod_by_monic_cancel_left

variable (R)

theorem not_isField : ¬IsField R[X] := by
  nontriviality R
  -- ⊢ ¬IsField R[X]
  rw [Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top]
  -- ⊢ ∃ I, ⊥ < I ∧ I < ⊤
  use Ideal.span {Polynomial.X}
  -- ⊢ ⊥ < Ideal.span {X} ∧ Ideal.span {X} < ⊤
  constructor
  -- ⊢ ⊥ < Ideal.span {X}
  · rw [bot_lt_iff_ne_bot, Ne.def, Ideal.span_singleton_eq_bot]
    -- ⊢ ¬X = 0
    exact Polynomial.X_ne_zero
    -- 🎉 no goals
  · rw [lt_top_iff_ne_top, Ne.def, Ideal.eq_top_iff_one, Ideal.mem_span_singleton,
      Polynomial.X_dvd_iff, Polynomial.coeff_one_zero]
    exact one_ne_zero
    -- 🎉 no goals
#align polynomial.not_is_field Polynomial.not_isField

variable {R}

theorem ker_evalRingHom (x : R) : RingHom.ker (evalRingHom x) = Ideal.span {X - C x} := by
  ext y
  -- ⊢ y ∈ RingHom.ker (evalRingHom x) ↔ y ∈ Ideal.span {X - ↑C x}
  simp [Ideal.mem_span_singleton, dvd_iff_isRoot, RingHom.mem_ker]
  -- 🎉 no goals
#align polynomial.ker_eval_ring_hom Polynomial.ker_evalRingHom

section multiplicity

/-- An algorithm for deciding polynomial divisibility.
The algorithm is "compute `p %ₘ q` and compare to `0`".
See `polynomial.modByMonic` for the algorithm that computes `%ₘ`.
-/
def decidableDvdMonic (p : R[X]) (hq : Monic q) : Decidable (q ∣ p) :=
  decidable_of_iff (p %ₘ q = 0) (dvd_iff_modByMonic_eq_zero hq)
#align polynomial.decidable_dvd_monic Polynomial.decidableDvdMonic

theorem multiplicity_X_sub_C_finite (a : R) (h0 : p ≠ 0) : multiplicity.Finite (X - C a) p := by
  haveI := Nontrivial.of_polynomial_ne h0
  -- ⊢ multiplicity.Finite (X - ↑C a) p
  refine' multiplicity_finite_of_degree_pos_of_monic _ (monic_X_sub_C _) h0
  -- ⊢ 0 < degree (X - ↑C a)
  rw [degree_X_sub_C]
  -- ⊢ 0 < 1
  decide
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.multiplicity_X_sub_C_finite Polynomial.multiplicity_X_sub_C_finite

/- Porting note: stripping out classical for decidability instance parameter might
make for better ergonomics -/
/-- The largest power of `X - C a` which divides `p`.
This is computable via the divisibility algorithm `Polynomial.decidableDvdMonic`. -/
def rootMultiplicity (a : R) (p : R[X]) : ℕ :=
  if h0 : p = 0 then 0
  else
    let _ : DecidablePred fun n : ℕ => ¬(X - C a) ^ (n + 1) ∣ p := fun n =>
      @Not.decidable _ (decidableDvdMonic p ((monic_X_sub_C a).pow (n + 1)))
    Nat.find (multiplicity_X_sub_C_finite a h0)
#align polynomial.root_multiplicity Polynomial.rootMultiplicity

/- Porting note: added the following due to diamond with decidableProp and
decidableDvdMonic see also [Zulip]
(https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/
non-defeq.20aliased.20instance) -/
theorem rootMultiplicity_eq_nat_find_of_nonzero {p : R[X]} (p0 : p ≠ 0) {a : R} :
    rootMultiplicity a p = Nat.find (multiplicity_X_sub_C_finite a p0) := by
  dsimp [rootMultiplicity]
  -- ⊢ (if h0 : p = 0 then 0 else Nat.find (_ : multiplicity.Finite (X - ↑C a) p))  …
  rw [dif_neg p0]
  -- ⊢ Nat.find (_ : multiplicity.Finite (X - ↑C a) p) = Nat.find (_ : multiplicity …
  convert rfl
  -- 🎉 no goals

theorem rootMultiplicity_eq_multiplicity (p : R[X]) (a : R) :
    rootMultiplicity a p =
      if h0 : p = 0 then 0 else (multiplicity (X - C a) p).get (multiplicity_X_sub_C_finite a h0) :=
  by simp [multiplicity, rootMultiplicity, Part.Dom]; congr; funext; congr
     -- ⊢ (if h : p = 0 then 0 else Nat.find (_ : multiplicity.Finite (X - ↑C a) p)) = …
                                                      -- ⊢ (fun h => Nat.find (_ : multiplicity.Finite (X - ↑C a) p)) = fun h => Nat.fi …
                                                             -- ⊢ Nat.find (_ : multiplicity.Finite (X - ↑C a) p) = Nat.find (_ : (PartENat.fi …
                                                                     -- 🎉 no goals
#align polynomial.root_multiplicity_eq_multiplicity Polynomial.rootMultiplicity_eq_multiplicity

@[simp]
theorem rootMultiplicity_zero {x : R} : rootMultiplicity x 0 = 0 :=
  dif_pos rfl
#align polynomial.root_multiplicity_zero Polynomial.rootMultiplicity_zero

@[simp]
theorem rootMultiplicity_eq_zero_iff {p : R[X]} {x : R} :
    rootMultiplicity x p = 0 ↔ IsRoot p x → p = 0 := by
  simp only [rootMultiplicity_eq_multiplicity, dite_eq_left_iff, PartENat.get_eq_iff_eq_coe,
    Nat.cast_zero, multiplicity.multiplicity_eq_zero, dvd_iff_isRoot, not_imp_not]
#align polynomial.root_multiplicity_eq_zero_iff Polynomial.rootMultiplicity_eq_zero_iff

theorem rootMultiplicity_eq_zero {p : R[X]} {x : R} (h : ¬IsRoot p x) : rootMultiplicity x p = 0 :=
  rootMultiplicity_eq_zero_iff.2 fun h' => (h h').elim
#align polynomial.root_multiplicity_eq_zero Polynomial.rootMultiplicity_eq_zero

@[simp]
theorem rootMultiplicity_pos' {p : R[X]} {x : R} : 0 < rootMultiplicity x p ↔ p ≠ 0 ∧ IsRoot p x :=
  by rw [pos_iff_ne_zero, Ne.def, rootMultiplicity_eq_zero_iff, not_imp, and_comm]
     -- 🎉 no goals
#align polynomial.root_multiplicity_pos' Polynomial.rootMultiplicity_pos'

theorem rootMultiplicity_pos {p : R[X]} (hp : p ≠ 0) {x : R} :
    0 < rootMultiplicity x p ↔ IsRoot p x :=
  rootMultiplicity_pos'.trans (and_iff_right hp)
#align polynomial.root_multiplicity_pos Polynomial.rootMultiplicity_pos

@[simp]
theorem rootMultiplicity_C (r a : R) : rootMultiplicity a (C r) = 0 := by
  simp only [rootMultiplicity_eq_zero_iff, IsRoot, eval_C, C_eq_zero, imp_self]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.root_multiplicity_C Polynomial.rootMultiplicity_C

theorem pow_rootMultiplicity_dvd (p : R[X]) (a : R) : (X - C a) ^ rootMultiplicity a p ∣ p :=
  if h : p = 0 then by simp [h]
                       -- 🎉 no goals
  else by
    rw [rootMultiplicity_eq_multiplicity, dif_neg h]; exact multiplicity.pow_multiplicity_dvd _
    -- ⊢ (X - ↑C a) ^ Part.get (multiplicity (X - ↑C a) p) (_ : multiplicity.Finite ( …
                                                      -- 🎉 no goals
#align polynomial.pow_root_multiplicity_dvd Polynomial.pow_rootMultiplicity_dvd

theorem divByMonic_mul_pow_rootMultiplicity_eq (p : R[X]) (a : R) :
    p /ₘ (X - C a) ^ rootMultiplicity a p * (X - C a) ^ rootMultiplicity a p = p := by
  have : Monic ((X - C a) ^ rootMultiplicity a p) := (monic_X_sub_C _).pow _
  -- ⊢ p /ₘ (X - ↑C a) ^ rootMultiplicity a p * (X - ↑C a) ^ rootMultiplicity a p = p
  conv_rhs =>
      rw [← modByMonic_add_div p this,
        (dvd_iff_modByMonic_eq_zero this).2 (pow_rootMultiplicity_dvd _ _)]
  simp [mul_comm]
  -- 🎉 no goals
#align polynomial.div_by_monic_mul_pow_root_multiplicity_eq Polynomial.divByMonic_mul_pow_rootMultiplicity_eq

theorem eval_divByMonic_pow_rootMultiplicity_ne_zero {p : R[X]} (a : R) (hp : p ≠ 0) :
    eval a (p /ₘ (X - C a) ^ rootMultiplicity a p) ≠ 0 := by
  haveI : Nontrivial R := Nontrivial.of_polynomial_ne hp
  -- ⊢ eval a (p /ₘ (X - ↑C a) ^ rootMultiplicity a p) ≠ 0
  rw [Ne.def, ← IsRoot.def, ← dvd_iff_isRoot]
  -- ⊢ ¬X - ↑C a ∣ p /ₘ (X - ↑C a) ^ rootMultiplicity a p
  rintro ⟨q, hq⟩
  -- ⊢ False
  have := divByMonic_mul_pow_rootMultiplicity_eq p a
  -- ⊢ False
  rw [mul_comm, hq, ← mul_assoc, ← pow_succ', rootMultiplicity_eq_multiplicity, dif_neg hp] at this
  -- ⊢ False
  exact
    multiplicity.is_greatest'
      (multiplicity_finite_of_degree_pos_of_monic
        (show (0 : WithBot ℕ) < degree (X - C a) by rw [degree_X_sub_C]; exact by decide)
        (monic_X_sub_C _) hp)
      (Nat.lt_succ_self _) (dvd_of_mul_right_eq _ this)
#align polynomial.eval_div_by_monic_pow_root_multiplicity_ne_zero Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero

end multiplicity

end CommRing

end Polynomial
