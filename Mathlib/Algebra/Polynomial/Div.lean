/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.RingTheory.Multiplicity
import Mathlib.RingTheory.Ideal.Maps

#align_import data.polynomial.div from "leanprover-community/mathlib"@"e1e7190efdcefc925cb36f257a8362ef22944204"

/-!
# Division of univariate polynomials

The main defs are `divByMonic` and `modByMonic`.
The compatibility between these is given by `modByMonic_add_div`.
We also define `rootMultiplicity`.
-/


noncomputable section

open Polynomial

open Finset

namespace Polynomial

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

section Semiring

variable [Semiring R]

theorem X_dvd_iff {f : R[X]} : X ∣ f ↔ f.coeff 0 = 0 :=
  ⟨fun ⟨g, hfg⟩ => by rw [hfg, coeff_X_mul_zero], fun hf =>
    ⟨f.divX, by rw [← add_zero (X * f.divX), ← C_0, ← hf, X_mul_divX_add]⟩⟩
set_option linter.uppercaseLean3 false in
#align polynomial.X_dvd_iff Polynomial.X_dvd_iff

theorem X_pow_dvd_iff {f : R[X]} {n : ℕ} : X ^ n ∣ f ↔ ∀ d < n, f.coeff d = 0 :=
  ⟨fun ⟨g, hgf⟩ d hd => by
    simp only [hgf, coeff_X_pow_mul', ite_eq_right_iff, not_le_of_lt hd, IsEmpty.forall_iff],
    fun hd => by
    induction' n with n hn
    · simp [pow_zero, one_dvd]
    · obtain ⟨g, hgf⟩ := hn fun d : ℕ => fun H : d < n => hd _ (Nat.lt_succ_of_lt H)
      have := coeff_X_pow_mul g n 0
      rw [zero_add, ← hgf, hd n (Nat.lt_succ_self n)] at this
      obtain ⟨k, hgk⟩ := Polynomial.X_dvd_iff.mpr this.symm
      use k
      rwa [pow_succ, mul_assoc, ← hgk]⟩
set_option linter.uppercaseLean3 false in
#align polynomial.X_pow_dvd_iff Polynomial.X_pow_dvd_iff

variable {p q : R[X]}

theorem multiplicity_finite_of_degree_pos_of_monic (hp : (0 : WithBot ℕ) < degree p) (hmp : Monic p)
    (hq : q ≠ 0) : multiplicity.Finite p q :=
  have zn0 : (0 : R) ≠ 1 :=
    haveI := Nontrivial.of_polynomial_ne hq
    zero_ne_one
  ⟨natDegree q, fun ⟨r, hr⟩ => by
    have hp0 : p ≠ 0 := fun hp0 => by simp [hp0] at hp
    have hr0 : r ≠ 0 := fun hr0 => by subst hr0; simp [hq] at hr
    have hpn1 : leadingCoeff p ^ (natDegree q + 1) = 1 := by simp [show _ = _ from hmp]
    have hpn0' : leadingCoeff p ^ (natDegree q + 1) ≠ 0 := hpn1.symm ▸ zn0.symm
    have hpnr0 : leadingCoeff (p ^ (natDegree q + 1)) * leadingCoeff r ≠ 0 := by
      simp only [leadingCoeff_pow' hpn0', leadingCoeff_eq_zero, hpn1, one_pow, one_mul, Ne,
          hr0, not_false_eq_true]
    have hnp : 0 < natDegree p := Nat.cast_lt.1 <| by
      rw [← degree_eq_natDegree hp0]; exact hp
    have := congr_arg natDegree hr
    rw [natDegree_mul' hpnr0, natDegree_pow' hpn0', add_mul, add_assoc] at this
    exact
      ne_of_lt
        (lt_add_of_le_of_pos (le_mul_of_one_le_right (Nat.zero_le _) hnp)
          (add_pos_of_pos_of_nonneg (by rwa [one_mul]) (Nat.zero_le _)))
        this⟩
#align polynomial.multiplicity_finite_of_degree_pos_of_monic Polynomial.multiplicity_finite_of_degree_pos_of_monic

end Semiring

section Ring

variable [Ring R] {p q : R[X]}

theorem div_wf_lemma (h : degree q ≤ degree p ∧ p ≠ 0) (hq : Monic q) :
    degree (p - q * (C (leadingCoeff p) * X ^ (natDegree p - natDegree q))) < degree p :=
  have hp : leadingCoeff p ≠ 0 := mt leadingCoeff_eq_zero.1 h.2
  have hq0 : q ≠ 0 := hq.ne_zero_of_polynomial_ne h.2
  have hlt : natDegree q ≤ natDegree p :=
    Nat.cast_le.1
      (by rw [← degree_eq_natDegree h.2, ← degree_eq_natDegree hq0]; exact h.1)
  degree_sub_lt
    (by
      rw [hq.degree_mul_comm, hq.degree_mul, degree_C_mul_X_pow _ hp, degree_eq_natDegree h.2,
        degree_eq_natDegree hq0, ← Nat.cast_add, tsub_add_cancel_of_le hlt])
    h.2 (by rw [leadingCoeff_monic_mul hq, leadingCoeff_mul_X_pow, leadingCoeff_C])
#align polynomial.div_wf_lemma Polynomial.div_wf_lemma

/-- See `divByMonic`. -/
noncomputable def divModByMonicAux : ∀ (_p : R[X]) {q : R[X]}, Monic q → R[X] × R[X]
  | p, q, hq =>
    letI := Classical.decEq R
    if h : degree q ≤ degree p ∧ p ≠ 0 then
      let z := C (leadingCoeff p) * X ^ (natDegree p - natDegree q)
      have _wf := div_wf_lemma h hq
      let dm := divModByMonicAux (p - q * z) hq
      ⟨z + dm.1, dm.2⟩
    else ⟨0, p⟩
  termination_by p => p
#align polynomial.div_mod_by_monic_aux Polynomial.divModByMonicAux

/-- `divByMonic` gives the quotient of `p` by a monic polynomial `q`. -/
def divByMonic (p q : R[X]) : R[X] :=
  letI := Classical.decEq R
  if hq : Monic q then (divModByMonicAux p hq).1 else 0
#align polynomial.div_by_monic Polynomial.divByMonic

/-- `modByMonic` gives the remainder of `p` by a monic polynomial `q`. -/
def modByMonic (p q : R[X]) : R[X] :=
  letI := Classical.decEq R
  if hq : Monic q then (divModByMonicAux p hq).2 else p
#align polynomial.mod_by_monic Polynomial.modByMonic

@[inherit_doc]
infixl:70 " /ₘ " => divByMonic

@[inherit_doc]
infixl:70 " %ₘ " => modByMonic

theorem degree_modByMonic_lt [Nontrivial R] :
    ∀ (p : R[X]) {q : R[X]} (_hq : Monic q), degree (p %ₘ q) < degree q
  | p, q, hq =>
    letI := Classical.decEq R
    if h : degree q ≤ degree p ∧ p ≠ 0 then by
      have _wf := div_wf_lemma ⟨h.1, h.2⟩ hq
      have :=
        degree_modByMonic_lt (p - q * (C (leadingCoeff p) * X ^ (natDegree p - natDegree q))) hq
      unfold modByMonic at this ⊢
      unfold divModByMonicAux
      dsimp
      rw [dif_pos hq] at this ⊢
      rw [if_pos h]
      exact this
    else
      Or.casesOn (not_and_or.1 h)
        (by
          unfold modByMonic divModByMonicAux
          dsimp
          rw [dif_pos hq, if_neg h]
          exact lt_of_not_ge)
        (by
          intro hp
          unfold modByMonic divModByMonicAux
          dsimp
          rw [dif_pos hq, if_neg h, Classical.not_not.1 hp]
          exact lt_of_le_of_ne bot_le (Ne.symm (mt degree_eq_bot.1 hq.ne_zero)))
  termination_by p => p
#align polynomial.degree_mod_by_monic_lt Polynomial.degree_modByMonic_lt

theorem natDegree_modByMonic_lt (p : R[X]) {q : R[X]} (hmq : Monic q) (hq : q ≠ 1) :
    natDegree (p %ₘ q) < q.natDegree := by
  by_cases hpq : p %ₘ q = 0
  · rw [hpq, natDegree_zero, Nat.pos_iff_ne_zero]
    contrapose! hq
    exact eq_one_of_monic_natDegree_zero hmq hq
  · haveI := Nontrivial.of_polynomial_ne hpq
    exact natDegree_lt_natDegree hpq (degree_modByMonic_lt p hmq)

@[simp]
theorem zero_modByMonic (p : R[X]) : 0 %ₘ p = 0 := by
  classical
  unfold modByMonic divModByMonicAux
  dsimp
  by_cases hp : Monic p
  · rw [dif_pos hp, if_neg (mt And.right (not_not_intro rfl))]
  · rw [dif_neg hp]
#align polynomial.zero_mod_by_monic Polynomial.zero_modByMonic

@[simp]
theorem zero_divByMonic (p : R[X]) : 0 /ₘ p = 0 := by
  classical
  unfold divByMonic divModByMonicAux
  dsimp
  by_cases hp : Monic p
  · rw [dif_pos hp, if_neg (mt And.right (not_not_intro rfl))]
  · rw [dif_neg hp]
#align polynomial.zero_div_by_monic Polynomial.zero_divByMonic

@[simp]
theorem modByMonic_zero (p : R[X]) : p %ₘ 0 = p :=
  letI := Classical.decEq R
  if h : Monic (0 : R[X]) then by
    haveI := monic_zero_iff_subsingleton.mp h
    simp [eq_iff_true_of_subsingleton]
  else by unfold modByMonic divModByMonicAux; rw [dif_neg h]
#align polynomial.mod_by_monic_zero Polynomial.modByMonic_zero

@[simp]
theorem divByMonic_zero (p : R[X]) : p /ₘ 0 = 0 :=
  letI := Classical.decEq R
  if h : Monic (0 : R[X]) then by
    haveI := monic_zero_iff_subsingleton.mp h
    simp [eq_iff_true_of_subsingleton]
  else by unfold divByMonic divModByMonicAux; rw [dif_neg h]
#align polynomial.div_by_monic_zero Polynomial.divByMonic_zero

theorem divByMonic_eq_of_not_monic (p : R[X]) (hq : ¬Monic q) : p /ₘ q = 0 :=
  dif_neg hq
#align polynomial.div_by_monic_eq_of_not_monic Polynomial.divByMonic_eq_of_not_monic

theorem modByMonic_eq_of_not_monic (p : R[X]) (hq : ¬Monic q) : p %ₘ q = p :=
  dif_neg hq
#align polynomial.mod_by_monic_eq_of_not_monic Polynomial.modByMonic_eq_of_not_monic

theorem modByMonic_eq_self_iff [Nontrivial R] (hq : Monic q) : p %ₘ q = p ↔ degree p < degree q :=
  ⟨fun h => h ▸ degree_modByMonic_lt _ hq, fun h => by
    classical
    have : ¬degree q ≤ degree p := not_le_of_gt h
    unfold modByMonic divModByMonicAux; dsimp; rw [dif_pos hq, if_neg (mt And.left this)]⟩
#align polynomial.mod_by_monic_eq_self_iff Polynomial.modByMonic_eq_self_iff

theorem degree_modByMonic_le (p : R[X]) {q : R[X]} (hq : Monic q) : degree (p %ₘ q) ≤ degree q := by
  nontriviality R
  exact (degree_modByMonic_lt _ hq).le
#align polynomial.degree_mod_by_monic_le Polynomial.degree_modByMonic_le

theorem natDegree_modByMonic_le (p : Polynomial R) {g : Polynomial R} (hg : g.Monic) :
    natDegree (p %ₘ g) ≤ g.natDegree :=
  natDegree_le_natDegree (degree_modByMonic_le p hg)

theorem X_dvd_sub_C : X ∣ p - C (p.coeff 0) := by
  simp [X_dvd_iff, coeff_C]

theorem modByMonic_eq_sub_mul_div :
    ∀ (p : R[X]) {q : R[X]} (_hq : Monic q), p %ₘ q = p - q * (p /ₘ q)
  | p, q, hq =>
    letI := Classical.decEq R
    if h : degree q ≤ degree p ∧ p ≠ 0 then by
      have _wf := div_wf_lemma h hq
      have ih := modByMonic_eq_sub_mul_div
        (p - q * (C (leadingCoeff p) * X ^ (natDegree p - natDegree q))) hq
      unfold modByMonic divByMonic divModByMonicAux
      dsimp
      rw [dif_pos hq, if_pos h]
      rw [modByMonic, dif_pos hq] at ih
      refine ih.trans ?_
      unfold divByMonic
      rw [dif_pos hq, dif_pos hq, if_pos h, mul_add, sub_add_eq_sub_sub]
    else by
      unfold modByMonic divByMonic divModByMonicAux
      dsimp
      rw [dif_pos hq, if_neg h, dif_pos hq, if_neg h, mul_zero, sub_zero]
  termination_by p => p
#align polynomial.mod_by_monic_eq_sub_mul_div Polynomial.modByMonic_eq_sub_mul_div

theorem modByMonic_add_div (p : R[X]) {q : R[X]} (hq : Monic q) : p %ₘ q + q * (p /ₘ q) = p :=
  eq_sub_iff_add_eq.1 (modByMonic_eq_sub_mul_div p hq)
#align polynomial.mod_by_monic_add_div Polynomial.modByMonic_add_div

theorem divByMonic_eq_zero_iff [Nontrivial R] (hq : Monic q) : p /ₘ q = 0 ↔ degree p < degree q :=
  ⟨fun h => by
    have := modByMonic_add_div p hq;
      rwa [h, mul_zero, add_zero, modByMonic_eq_self_iff hq] at this,
  fun h => by
    classical
    have : ¬degree q ≤ degree p := not_le_of_gt h
    unfold divByMonic divModByMonicAux; dsimp; rw [dif_pos hq, if_neg (mt And.left this)]⟩
#align polynomial.div_by_monic_eq_zero_iff Polynomial.divByMonic_eq_zero_iff

theorem degree_add_divByMonic (hq : Monic q) (h : degree q ≤ degree p) :
    degree q + degree (p /ₘ q) = degree p := by
  nontriviality R
  have hdiv0 : p /ₘ q ≠ 0 := by rwa [Ne, divByMonic_eq_zero_iff hq, not_lt]
  have hlc : leadingCoeff q * leadingCoeff (p /ₘ q) ≠ 0 := by
    rwa [Monic.def.1 hq, one_mul, Ne, leadingCoeff_eq_zero]
  have hmod : degree (p %ₘ q) < degree (q * (p /ₘ q)) :=
    calc
      degree (p %ₘ q) < degree q := degree_modByMonic_lt _ hq
      _ ≤ _ := by
        rw [degree_mul' hlc, degree_eq_natDegree hq.ne_zero, degree_eq_natDegree hdiv0, ←
            Nat.cast_add, Nat.cast_le]
        exact Nat.le_add_right _ _
  calc
    degree q + degree (p /ₘ q) = degree (q * (p /ₘ q)) := Eq.symm (degree_mul' hlc)
    _ = degree (p %ₘ q + q * (p /ₘ q)) := (degree_add_eq_right_of_degree_lt hmod).symm
    _ = _ := congr_arg _ (modByMonic_add_div _ hq)
#align polynomial.degree_add_div_by_monic Polynomial.degree_add_divByMonic

theorem degree_divByMonic_le (p q : R[X]) : degree (p /ₘ q) ≤ degree p :=
  letI := Classical.decEq R
  if hp0 : p = 0 then by simp only [hp0, zero_divByMonic, le_refl]
  else
    if hq : Monic q then
      if h : degree q ≤ degree p then by
        haveI := Nontrivial.of_polynomial_ne hp0;
            rw [← degree_add_divByMonic hq h, degree_eq_natDegree hq.ne_zero,
              degree_eq_natDegree (mt (divByMonic_eq_zero_iff hq).1 (not_lt.2 h))];
          exact WithBot.coe_le_coe.2 (Nat.le_add_left _ _)
      else by
        unfold divByMonic divModByMonicAux;
          simp [dif_pos hq, h, false_and_iff, if_false, degree_zero, bot_le]
    else (divByMonic_eq_of_not_monic p hq).symm ▸ bot_le
#align polynomial.degree_div_by_monic_le Polynomial.degree_divByMonic_le

theorem degree_divByMonic_lt (p : R[X]) {q : R[X]} (hq : Monic q) (hp0 : p ≠ 0)
    (h0q : 0 < degree q) : degree (p /ₘ q) < degree p :=
  if hpq : degree p < degree q then by
    haveI := Nontrivial.of_polynomial_ne hp0
    rw [(divByMonic_eq_zero_iff hq).2 hpq, degree_eq_natDegree hp0]
    exact WithBot.bot_lt_coe _
  else by
    haveI := Nontrivial.of_polynomial_ne hp0
    rw [← degree_add_divByMonic hq (not_lt.1 hpq), degree_eq_natDegree hq.ne_zero,
      degree_eq_natDegree (mt (divByMonic_eq_zero_iff hq).1 hpq)]
    exact
      Nat.cast_lt.2
        (Nat.lt_add_of_pos_left (Nat.cast_lt.1 <|
          by simpa [degree_eq_natDegree hq.ne_zero] using h0q))
#align polynomial.degree_div_by_monic_lt Polynomial.degree_divByMonic_lt

theorem natDegree_divByMonic (f : R[X]) {g : R[X]} (hg : g.Monic) :
    natDegree (f /ₘ g) = natDegree f - natDegree g := by
  nontriviality R
  by_cases hfg : f /ₘ g = 0
  · rw [hfg, natDegree_zero]
    rw [divByMonic_eq_zero_iff hg] at hfg
    rw [tsub_eq_zero_iff_le.mpr (natDegree_le_natDegree <| le_of_lt hfg)]
  have hgf := hfg
  rw [divByMonic_eq_zero_iff hg] at hgf
  push_neg at hgf
  have := degree_add_divByMonic hg hgf
  have hf : f ≠ 0 := by
    intro hf
    apply hfg
    rw [hf, zero_divByMonic]
  rw [degree_eq_natDegree hf, degree_eq_natDegree hg.ne_zero, degree_eq_natDegree hfg,
    ← Nat.cast_add, Nat.cast_inj] at this
  rw [← this, add_tsub_cancel_left]
#align polynomial.nat_degree_div_by_monic Polynomial.natDegree_divByMonic

theorem div_modByMonic_unique {f g} (q r : R[X]) (hg : Monic g)
    (h : r + g * q = f ∧ degree r < degree g) : f /ₘ g = q ∧ f %ₘ g = r := by
  nontriviality R
  have h₁ : r - f %ₘ g = -g * (q - f /ₘ g) :=
    eq_of_sub_eq_zero
      (by
        rw [← sub_eq_zero_of_eq (h.1.trans (modByMonic_add_div f hg).symm)]
        simp [mul_add, mul_comm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc])
  have h₂ : degree (r - f %ₘ g) = degree (g * (q - f /ₘ g)) := by simp [h₁]
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
#align polynomial.div_mod_by_monic_unique Polynomial.div_modByMonic_unique

theorem map_mod_divByMonic [Ring S] (f : R →+* S) (hq : Monic q) :
    (p /ₘ q).map f = p.map f /ₘ q.map f ∧ (p %ₘ q).map f = p.map f %ₘ q.map f := by
  nontriviality S
  haveI : Nontrivial R := f.domain_nontrivial
  have : map f p /ₘ map f q = map f (p /ₘ q) ∧ map f p %ₘ map f q = map f (p %ₘ q) :=
    div_modByMonic_unique ((p /ₘ q).map f) _ (hq.map f)
      ⟨Eq.symm <| by rw [← Polynomial.map_mul, ← Polynomial.map_add, modByMonic_add_div _ hq],
        calc
          _ ≤ degree (p %ₘ q) := degree_map_le _ _
          _ < degree q := degree_modByMonic_lt _ hq
          _ = _ :=
            Eq.symm <|
              degree_map_eq_of_leadingCoeff_ne_zero _
                (by rw [Monic.def.1 hq, f.map_one]; exact one_ne_zero)⟩
  exact ⟨this.1.symm, this.2.symm⟩
#align polynomial.map_mod_div_by_monic Polynomial.map_mod_divByMonic

theorem map_divByMonic [Ring S] (f : R →+* S) (hq : Monic q) :
    (p /ₘ q).map f = p.map f /ₘ q.map f :=
  (map_mod_divByMonic f hq).1
#align polynomial.map_div_by_monic Polynomial.map_divByMonic

theorem map_modByMonic [Ring S] (f : R →+* S) (hq : Monic q) :
    (p %ₘ q).map f = p.map f %ₘ q.map f :=
  (map_mod_divByMonic f hq).2
#align polynomial.map_mod_by_monic Polynomial.map_modByMonic

theorem modByMonic_eq_zero_iff_dvd (hq : Monic q) : p %ₘ q = 0 ↔ q ∣ p :=
  ⟨fun h => by rw [← modByMonic_add_div p hq, h, zero_add]; exact dvd_mul_right _ _, fun h => by
    nontriviality R
    obtain ⟨r, hr⟩ := exists_eq_mul_right_of_dvd h
    by_contra hpq0
    have hmod : p %ₘ q = q * (r - p /ₘ q) := by rw [modByMonic_eq_sub_mul_div _ hq, mul_sub, ← hr]
    have : degree (q * (r - p /ₘ q)) < degree q := hmod ▸ degree_modByMonic_lt _ hq
    have hrpq0 : leadingCoeff (r - p /ₘ q) ≠ 0 := fun h =>
      hpq0 <|
        leadingCoeff_eq_zero.1
          (by rw [hmod, leadingCoeff_eq_zero.1 h, mul_zero, leadingCoeff_zero])
    have hlc : leadingCoeff q * leadingCoeff (r - p /ₘ q) ≠ 0 := by rwa [Monic.def.1 hq, one_mul]
    rw [degree_mul' hlc, degree_eq_natDegree hq.ne_zero,
      degree_eq_natDegree (mt leadingCoeff_eq_zero.2 hrpq0)] at this
    exact not_lt_of_ge (Nat.le_add_right _ _) (WithBot.coe_lt_coe.1 this)⟩
#align polynomial.dvd_iff_mod_by_monic_eq_zero Polynomial.modByMonic_eq_zero_iff_dvd

@[deprecated] alias dvd_iff_modByMonic_eq_zero := modByMonic_eq_zero_iff_dvd -- 2024-03-23

/-- See `Polynomial.mul_left_modByMonic` for the other multiplication order. That version, unlike
this one, requires commutativity. -/
@[simp]
lemma self_mul_modByMonic (hq : q.Monic) : (q * p) %ₘ q = 0 := by
  rw [modByMonic_eq_zero_iff_dvd hq]
  exact dvd_mul_right q p

theorem map_dvd_map [Ring S] (f : R →+* S) (hf : Function.Injective f) {x y : R[X]}
    (hx : x.Monic) : x.map f ∣ y.map f ↔ x ∣ y := by
  rw [← modByMonic_eq_zero_iff_dvd hx, ← modByMonic_eq_zero_iff_dvd (hx.map f), ←
    map_modByMonic f hx]
  exact
    ⟨fun H => map_injective f hf <| by rw [H, Polynomial.map_zero], fun H => by
      rw [H, Polynomial.map_zero]⟩
#align polynomial.map_dvd_map Polynomial.map_dvd_map

@[simp]
theorem modByMonic_one (p : R[X]) : p %ₘ 1 = 0 :=
  (modByMonic_eq_zero_iff_dvd (by convert monic_one (R := R))).2 (one_dvd _)
#align polynomial.mod_by_monic_one Polynomial.modByMonic_one

@[simp]
theorem divByMonic_one (p : R[X]) : p /ₘ 1 = p := by
  conv_rhs => rw [← modByMonic_add_div p monic_one]; simp
#align polynomial.div_by_monic_one Polynomial.divByMonic_one

theorem sum_modByMonic_coeff (hq : q.Monic) {n : ℕ} (hn : q.degree ≤ n) :
    (∑ i : Fin n, monomial i ((p %ₘ q).coeff i)) = p %ₘ q := by
  nontriviality R
  exact
    (sum_fin (fun i c => monomial i c) (by simp) ((degree_modByMonic_lt _ hq).trans_le hn)).trans
      (sum_monomial_eq _)
#align polynomial.sum_mod_by_monic_coeff Polynomial.sum_modByMonic_coeff

theorem mul_div_mod_by_monic_cancel_left (p : R[X]) {q : R[X]} (hmo : q.Monic) :
    q * p /ₘ q = p := by
  nontriviality R
  refine (div_modByMonic_unique _ 0 hmo ⟨by rw [zero_add], ?_⟩).1
  rw [degree_zero]
  exact Ne.bot_lt fun h => hmo.ne_zero (degree_eq_bot.1 h)
#align polynomial.mul_div_mod_by_monic_cancel_left Polynomial.mul_div_mod_by_monic_cancel_left

lemma coeff_divByMonic_X_sub_C_rec (p : R[X]) (a : R) (n : ℕ) :
    (p /ₘ (X - C a)).coeff n = coeff p (n + 1) + a * (p /ₘ (X - C a)).coeff (n + 1) := by
  nontriviality R
  have := monic_X_sub_C a
  set q := p /ₘ (X - C a)
  rw [← p.modByMonic_add_div this]
  have : degree (p %ₘ (X - C a)) < ↑(n + 1) := degree_X_sub_C a ▸ p.degree_modByMonic_lt this
    |>.trans_le <| WithBot.coe_le_coe.mpr le_add_self
  simp [sub_mul, add_sub, coeff_eq_zero_of_degree_lt this]

theorem coeff_divByMonic_X_sub_C (p : R[X]) (a : R) (n : ℕ) :
    (p /ₘ (X - C a)).coeff n = ∑ i ∈ Icc (n + 1) p.natDegree, a ^ (i - (n + 1)) * p.coeff i := by
  wlog h : p.natDegree ≤ n generalizing n
  · refine Nat.decreasingInduction' (fun n hn _ ih ↦ ?_) (le_of_not_le h) ?_
    · rw [coeff_divByMonic_X_sub_C_rec, ih, eq_comm, Icc_eq_cons_Ioc (Nat.succ_le.mpr hn),
          sum_cons, Nat.sub_self, pow_zero, one_mul, mul_sum]
      congr 1; refine sum_congr ?_ fun i hi ↦ ?_
      · ext; simp [Nat.succ_le]
      rw [← mul_assoc, ← pow_succ', eq_comm, i.sub_succ', Nat.sub_add_cancel]
      apply Nat.le_sub_of_add_le
      rw [add_comm]; exact (mem_Icc.mp hi).1
    · exact this _ le_rfl
  rw [Icc_eq_empty (Nat.lt_succ.mpr h).not_le, sum_empty]
  nontriviality R
  by_cases hp : p.natDegree = 0
  · rw [(divByMonic_eq_zero_iff <| monic_X_sub_C a).mpr, coeff_zero]
    apply degree_lt_degree; rw [hp, natDegree_X_sub_C]; norm_num
  · apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_divByMonic p (monic_X_sub_C a), natDegree_X_sub_C]
    exact (Nat.pred_lt hp).trans_le h

variable (R) in
theorem not_isField : ¬IsField R[X] := by
  nontriviality R
  intro h
  letI := h.toField
  simpa using congr_arg natDegree (monic_X.eq_one_of_isUnit <| monic_X (R := R).ne_zero.isUnit)
#align polynomial.not_is_field Polynomial.not_isField

section multiplicity

/-- An algorithm for deciding polynomial divisibility.
The algorithm is "compute `p %ₘ q` and compare to `0`".
See `polynomial.modByMonic` for the algorithm that computes `%ₘ`.
-/
def decidableDvdMonic [DecidableEq R] (p : R[X]) (hq : Monic q) : Decidable (q ∣ p) :=
  decidable_of_iff (p %ₘ q = 0) (modByMonic_eq_zero_iff_dvd hq)
#align polynomial.decidable_dvd_monic Polynomial.decidableDvdMonic

theorem multiplicity_X_sub_C_finite (a : R) (h0 : p ≠ 0) : multiplicity.Finite (X - C a) p := by
  haveI := Nontrivial.of_polynomial_ne h0
  refine multiplicity_finite_of_degree_pos_of_monic ?_ (monic_X_sub_C _) h0
  rw [degree_X_sub_C]
  decide
set_option linter.uppercaseLean3 false in
#align polynomial.multiplicity_X_sub_C_finite Polynomial.multiplicity_X_sub_C_finite

/- Porting note: stripping out classical for decidability instance parameter might
make for better ergonomics -/
/-- The largest power of `X - C a` which divides `p`.
This *could be* computable via the divisibility algorithm `Polynomial.decidableDvdMonic`,
as shown by `Polynomial.rootMultiplicity_eq_nat_find_of_nonzero` which has a computable RHS. -/
def rootMultiplicity (a : R) (p : R[X]) : ℕ :=
  letI := Classical.decEq R
  if h0 : p = 0 then 0
  else
    let _ : DecidablePred fun n : ℕ => ¬(X - C a) ^ (n + 1) ∣ p := fun n =>
      @Not.decidable _ (decidableDvdMonic p ((monic_X_sub_C a).pow (n + 1)))
    Nat.find (multiplicity_X_sub_C_finite a h0)
#align polynomial.root_multiplicity Polynomial.rootMultiplicity

/- Porting note: added the following due to diamond with decidableProp and
decidableDvdMonic see also [Zulip]
(https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/non-defeq.20aliased.20instance) -/
theorem rootMultiplicity_eq_nat_find_of_nonzero [DecidableEq R] {p : R[X]} (p0 : p ≠ 0) {a : R} :
    letI : DecidablePred fun n : ℕ => ¬(X - C a) ^ (n + 1) ∣ p := fun n =>
      @Not.decidable _ (decidableDvdMonic p ((monic_X_sub_C a).pow (n + 1)))
    rootMultiplicity a p = Nat.find (multiplicity_X_sub_C_finite a p0) := by
  dsimp [rootMultiplicity]
  cases Subsingleton.elim ‹DecidableEq R› (Classical.decEq R)
  rw [dif_neg p0]

theorem rootMultiplicity_eq_multiplicity [DecidableEq R] [@DecidableRel R[X] (· ∣ ·)]
    (p : R[X]) (a : R) :
    rootMultiplicity a p =
      if h0 : p = 0 then 0 else (multiplicity (X - C a) p).get (multiplicity_X_sub_C_finite a h0) :=
  by simp [multiplicity, rootMultiplicity, Part.Dom]; congr; funext; congr
#align polynomial.root_multiplicity_eq_multiplicity Polynomial.rootMultiplicity_eq_multiplicity

@[simp]
theorem rootMultiplicity_zero {x : R} : rootMultiplicity x 0 = 0 :=
  dif_pos rfl
#align polynomial.root_multiplicity_zero Polynomial.rootMultiplicity_zero

@[simp]
theorem rootMultiplicity_C (r a : R) : rootMultiplicity a (C r) = 0 := by
  cases subsingleton_or_nontrivial R
  · rw [Subsingleton.elim (C r) 0, rootMultiplicity_zero]
  classical
  rw [rootMultiplicity_eq_multiplicity]
  split_ifs with hr
  · rfl
  have h : natDegree (C r) < natDegree (X - C a) := by simp
  simp_rw [multiplicity.multiplicity_eq_zero.mpr ((monic_X_sub_C a).not_dvd_of_natDegree_lt hr h),
    PartENat.get_zero]
set_option linter.uppercaseLean3 false in
#align polynomial.root_multiplicity_C Polynomial.rootMultiplicity_C

theorem pow_rootMultiplicity_dvd (p : R[X]) (a : R) : (X - C a) ^ rootMultiplicity a p ∣ p :=
  letI := Classical.decEq R
  if h : p = 0 then by simp [h]
  else by
    classical
    rw [rootMultiplicity_eq_multiplicity, dif_neg h]; exact multiplicity.pow_multiplicity_dvd _
#align polynomial.pow_root_multiplicity_dvd Polynomial.pow_rootMultiplicity_dvd

theorem pow_mul_divByMonic_rootMultiplicity_eq (p : R[X]) (a : R) :
    (X - C a) ^ rootMultiplicity a p * (p /ₘ (X - C a) ^ rootMultiplicity a p) = p := by
  have : Monic ((X - C a) ^ rootMultiplicity a p) := (monic_X_sub_C _).pow _
  conv_rhs =>
      rw [← modByMonic_add_div p this,
        (modByMonic_eq_zero_iff_dvd this).2 (pow_rootMultiplicity_dvd _ _)]
  simp
#align polynomial.div_by_monic_mul_pow_root_multiplicity_eq Polynomial.pow_mul_divByMonic_rootMultiplicity_eq

theorem exists_eq_pow_rootMultiplicity_mul_and_not_dvd (p : R[X]) (hp : p ≠ 0) (a : R) :
    ∃ q : R[X], p = (X - C a) ^ p.rootMultiplicity a * q ∧ ¬ (X - C a) ∣ q := by
  classical
  rw [rootMultiplicity_eq_multiplicity, dif_neg hp]
  apply multiplicity.exists_eq_pow_mul_and_not_dvd

end multiplicity

end Ring

section CommRing

variable [CommRing R] {p q : R[X]}

@[simp]
theorem modByMonic_X_sub_C_eq_C_eval (p : R[X]) (a : R) : p %ₘ (X - C a) = C (p.eval a) := by
  nontriviality R
  have h : (p %ₘ (X - C a)).eval a = p.eval a := by
    rw [modByMonic_eq_sub_mul_div _ (monic_X_sub_C a), eval_sub, eval_mul, eval_sub, eval_X,
      eval_C, sub_self, zero_mul, sub_zero]
  have : degree (p %ₘ (X - C a)) < 1 :=
    degree_X_sub_C a ▸ degree_modByMonic_lt p (monic_X_sub_C a)
  have : degree (p %ₘ (X - C a)) ≤ 0 := by
    revert this
    cases degree (p %ₘ (X - C a))
    · exact fun _ => bot_le
    · exact fun h => WithBot.coe_le_coe.2 (Nat.le_of_lt_succ (WithBot.coe_lt_coe.1 h))
  rw [eq_C_of_degree_le_zero this, eval_C] at h
  rw [eq_C_of_degree_le_zero this, h]
set_option linter.uppercaseLean3 false in
#align polynomial.mod_by_monic_X_sub_C_eq_C_eval Polynomial.modByMonic_X_sub_C_eq_C_eval

theorem mul_divByMonic_eq_iff_isRoot : (X - C a) * (p /ₘ (X - C a)) = p ↔ IsRoot p a :=
  .trans
    ⟨fun h => by rw [← h, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul],
    fun h => by
      conv_rhs =>
        rw [← modByMonic_add_div p (monic_X_sub_C a)]
        rw [modByMonic_X_sub_C_eq_C_eval, h, C_0, zero_add]⟩
    IsRoot.def.symm
#align polynomial.mul_div_by_monic_eq_iff_is_root Polynomial.mul_divByMonic_eq_iff_isRoot

theorem dvd_iff_isRoot : X - C a ∣ p ↔ IsRoot p a :=
  ⟨fun h => by
    rwa [← modByMonic_eq_zero_iff_dvd (monic_X_sub_C _), modByMonic_X_sub_C_eq_C_eval, ← C_0,
      C_inj] at h,
    fun h => ⟨p /ₘ (X - C a), by rw [mul_divByMonic_eq_iff_isRoot.2 h]⟩⟩
#align polynomial.dvd_iff_is_root Polynomial.dvd_iff_isRoot

theorem X_sub_C_dvd_sub_C_eval : X - C a ∣ p - C (p.eval a) := by
  rw [dvd_iff_isRoot, IsRoot, eval_sub, eval_C, sub_self]
set_option linter.uppercaseLean3 false in
#align polynomial.X_sub_C_dvd_sub_C_eval Polynomial.X_sub_C_dvd_sub_C_eval

theorem mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero {b : R[X]} {P : R[X][X]} :
    P ∈ Ideal.span {C (X - C a), X - C b} ↔ (P.eval b).eval a = 0 := by
  rw [Ideal.mem_span_pair]
  constructor <;> intro h
  · rcases h with ⟨_, _, rfl⟩
    simp only [eval_C, eval_X, eval_add, eval_sub, eval_mul, add_zero, mul_zero, sub_self]
  · rcases dvd_iff_isRoot.mpr h with ⟨p, hp⟩
    rcases @X_sub_C_dvd_sub_C_eval _ b _ P with ⟨q, hq⟩
    exact ⟨C p, q, by rw [mul_comm, mul_comm q, eq_add_of_sub_eq' hq, hp, C_mul]⟩
set_option linter.uppercaseLean3 false in
#align polynomial.mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero Polynomial.mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero

-- TODO: generalize this to Ring. In general, 0 can be replaced by any element in the center of R.
theorem modByMonic_X (p : R[X]) : p %ₘ X = C (p.eval 0) := by
  rw [← modByMonic_X_sub_C_eq_C_eval, C_0, sub_zero]
set_option linter.uppercaseLean3 false in
#align polynomial.mod_by_monic_X Polynomial.modByMonic_X

theorem eval₂_modByMonic_eq_self_of_root [CommRing S] {f : R →+* S} {p q : R[X]} (hq : q.Monic)
    {x : S} (hx : q.eval₂ f x = 0) : (p %ₘ q).eval₂ f x = p.eval₂ f x := by
  rw [modByMonic_eq_sub_mul_div p hq, eval₂_sub, eval₂_mul, hx, zero_mul, sub_zero]
#align polynomial.eval₂_mod_by_monic_eq_self_of_root Polynomial.eval₂_modByMonic_eq_self_of_root

theorem sub_dvd_eval_sub (a b : R) (p : R[X]) : a - b ∣ p.eval a - p.eval b := by
  suffices X - C b ∣ p - C (p.eval b) by
    simpa only [coe_evalRingHom, eval_sub, eval_X, eval_C] using (evalRingHom a).map_dvd this
  simp [dvd_iff_isRoot]
#align polynomial.sub_dvd_eval_sub Polynomial.sub_dvd_eval_sub

theorem ker_evalRingHom (x : R) : RingHom.ker (evalRingHom x) = Ideal.span {X - C x} := by
  ext y
  simp [Ideal.mem_span_singleton, dvd_iff_isRoot, RingHom.mem_ker]
#align polynomial.ker_eval_ring_hom Polynomial.ker_evalRingHom

@[simp]
theorem rootMultiplicity_eq_zero_iff {p : R[X]} {x : R} :
    rootMultiplicity x p = 0 ↔ IsRoot p x → p = 0 := by
  classical
  simp only [rootMultiplicity_eq_multiplicity, dite_eq_left_iff, PartENat.get_eq_iff_eq_coe,
    Nat.cast_zero, multiplicity.multiplicity_eq_zero, dvd_iff_isRoot, not_imp_not]
#align polynomial.root_multiplicity_eq_zero_iff Polynomial.rootMultiplicity_eq_zero_iff

theorem rootMultiplicity_eq_zero {p : R[X]} {x : R} (h : ¬IsRoot p x) : rootMultiplicity x p = 0 :=
  rootMultiplicity_eq_zero_iff.2 fun h' => (h h').elim
#align polynomial.root_multiplicity_eq_zero Polynomial.rootMultiplicity_eq_zero

@[simp]
theorem rootMultiplicity_pos' {p : R[X]} {x : R} :
    0 < rootMultiplicity x p ↔ p ≠ 0 ∧ IsRoot p x := by
  rw [pos_iff_ne_zero, Ne, rootMultiplicity_eq_zero_iff, Classical.not_imp, and_comm]
#align polynomial.root_multiplicity_pos' Polynomial.rootMultiplicity_pos'

theorem rootMultiplicity_pos {p : R[X]} (hp : p ≠ 0) {x : R} :
    0 < rootMultiplicity x p ↔ IsRoot p x :=
  rootMultiplicity_pos'.trans (and_iff_right hp)
#align polynomial.root_multiplicity_pos Polynomial.rootMultiplicity_pos

theorem eval_divByMonic_pow_rootMultiplicity_ne_zero {p : R[X]} (a : R) (hp : p ≠ 0) :
    eval a (p /ₘ (X - C a) ^ rootMultiplicity a p) ≠ 0 := by
  classical
  haveI : Nontrivial R := Nontrivial.of_polynomial_ne hp
  rw [Ne, ← IsRoot, ← dvd_iff_isRoot]
  rintro ⟨q, hq⟩
  have := pow_mul_divByMonic_rootMultiplicity_eq p a
  rw [hq, ← mul_assoc, ← pow_succ, rootMultiplicity_eq_multiplicity, dif_neg hp] at this
  exact
    multiplicity.is_greatest'
      (multiplicity_finite_of_degree_pos_of_monic
        (show (0 : WithBot ℕ) < degree (X - C a) by rw [degree_X_sub_C]; decide)
        (monic_X_sub_C _) hp)
      (Nat.lt_succ_self _) (dvd_of_mul_right_eq _ this)
#align polynomial.eval_div_by_monic_pow_root_multiplicity_ne_zero Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero

/-- See `Polynomial.mul_right_modByMonic` for the other multiplication order. This version, unlike
that one, requires commutativity. -/
@[simp]
lemma mul_self_modByMonic (hq : q.Monic) : (p * q) %ₘ q = 0 := by
  rw [modByMonic_eq_zero_iff_dvd hq]
  exact dvd_mul_left q p

end CommRing

end Polynomial
