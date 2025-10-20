/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.MonoidAlgebra.Degree
import Mathlib.Algebra.Order.Ring.WithTop
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Nat.Cast.WithTop
import Mathlib.Data.Nat.SuccPred
import Mathlib.Order.SuccPred.WithBot

/-!
# Degree of univariate polynomials

## Main definitions

* `Polynomial.degree`: the degree of a polynomial, where `0` has degree `⊥`
* `Polynomial.natDegree`: the degree of a polynomial, where `0` has degree `0`
* `Polynomial.leadingCoeff`: the leading coefficient of a polynomial
* `Polynomial.Monic`: a polynomial is monic if its leading coefficient is 0
* `Polynomial.nextCoeff`: the next coefficient after the leading coefficient

## Main results

* `Polynomial.degree_eq_natDegree`: the degree and natDegree coincide for nonzero polynomials
-/

noncomputable section

open Finsupp Finset

open Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

section Semiring

variable [Semiring R] {p q r : R[X]}

/-- `degree p` is the degree of the polynomial `p`, i.e. the largest `X`-exponent in `p`.
`degree p = some n` when `p ≠ 0` and `n` is the highest power of `X` that appears in `p`, otherwise
`degree 0 = ⊥`. -/
def degree (p : R[X]) : WithBot ℕ :=
  p.support.max

/-- `natDegree p` forces `degree p` to ℕ, by defining `natDegree 0 = 0`. -/
def natDegree (p : R[X]) : ℕ :=
  (degree p).unbotD 0

/-- `leadingCoeff p` gives the coefficient of the highest power of `X` in `p`. -/
def leadingCoeff (p : R[X]) : R :=
  coeff p (natDegree p)

/-- a polynomial is `Monic` if its leading coefficient is 1 -/
def Monic (p : R[X]) :=
  leadingCoeff p = (1 : R)

theorem Monic.def : Monic p ↔ leadingCoeff p = 1 :=
  Iff.rfl

instance Monic.decidable [DecidableEq R] : Decidable (Monic p) := by unfold Monic; infer_instance

@[simp]
theorem Monic.leadingCoeff {p : R[X]} (hp : p.Monic) : leadingCoeff p = 1 :=
  hp

theorem Monic.coeff_natDegree {p : R[X]} (hp : p.Monic) : p.coeff p.natDegree = 1 :=
  hp

@[simp]
theorem degree_zero : degree (0 : R[X]) = ⊥ :=
  rfl

@[simp]
theorem natDegree_zero : natDegree (0 : R[X]) = 0 :=
  rfl

@[simp]
theorem coeff_natDegree : coeff p (natDegree p) = leadingCoeff p :=
  rfl

@[simp]
theorem degree_eq_bot : degree p = ⊥ ↔ p = 0 :=
  ⟨fun h => support_eq_empty.1 (Finset.max_eq_bot.1 h), fun h => h.symm ▸ rfl⟩

theorem degree_ne_bot : degree p ≠ ⊥ ↔ p ≠ 0 := degree_eq_bot.not

theorem degree_eq_natDegree (hp : p ≠ 0) : degree p = (natDegree p : WithBot ℕ) := by
  let ⟨n, hn⟩ := not_forall.1 (mt Option.eq_none_iff_forall_not_mem.2 (mt degree_eq_bot.1 hp))
  have hn : degree p = some n := Classical.not_not.1 hn
  rw [natDegree, hn]; rfl

theorem degree_eq_iff_natDegree_eq {p : R[X]} {n : ℕ} (hp : p ≠ 0) :
    p.degree = n ↔ p.natDegree = n := by rw [degree_eq_natDegree hp]; exact WithBot.coe_eq_coe

theorem degree_eq_iff_natDegree_eq_of_pos {p : R[X]} {n : ℕ} (hn : 0 < n) :
    p.degree = n ↔ p.natDegree = n := by
  obtain rfl | h := eq_or_ne p 0
  · simp [hn.ne]
  · exact degree_eq_iff_natDegree_eq h

theorem natDegree_eq_of_degree_eq_some {p : R[X]} {n : ℕ} (h : degree p = n) : natDegree p = n := by
  rw [natDegree, h, Nat.cast_withBot, WithBot.unbotD_coe]

theorem degree_ne_of_natDegree_ne {n : ℕ} : p.natDegree ≠ n → degree p ≠ n :=
  mt natDegree_eq_of_degree_eq_some

@[simp]
theorem degree_le_natDegree : degree p ≤ natDegree p :=
  WithBot.giUnbotDBot.gc.le_u_l _

theorem natDegree_eq_of_degree_eq [Semiring S] {q : S[X]} (h : degree p = degree q) :
    natDegree p = natDegree q := by unfold natDegree; rw [h]

theorem le_degree_of_ne_zero (h : coeff p n ≠ 0) : (n : WithBot ℕ) ≤ degree p := by
  rw [Nat.cast_withBot]
  exact Finset.le_sup (mem_support_iff.2 h)

theorem degree_mono [Semiring S] {f : R[X]} {g : S[X]} (h : f.support ⊆ g.support) :
    f.degree ≤ g.degree :=
  Finset.sup_mono h

theorem degree_le_degree (h : coeff q (natDegree p) ≠ 0) : degree p ≤ degree q := by
  by_cases hp : p = 0
  · rw [hp, degree_zero]
    exact bot_le
  · rw [degree_eq_natDegree hp]
    exact le_degree_of_ne_zero h

theorem natDegree_le_iff_degree_le {n : ℕ} : natDegree p ≤ n ↔ degree p ≤ n :=
  WithBot.unbotD_le_iff (fun _ ↦ bot_le)

theorem natDegree_lt_iff_degree_lt (hp : p ≠ 0) : p.natDegree < n ↔ p.degree < ↑n :=
  WithBot.unbotD_lt_iff (absurd · (degree_eq_bot.not.mpr hp))

alias ⟨degree_le_of_natDegree_le, natDegree_le_of_degree_le⟩ := natDegree_le_iff_degree_le

theorem natDegree_le_natDegree [Semiring S] {q : S[X]} (hpq : p.degree ≤ q.degree) :
    p.natDegree ≤ q.natDegree :=
  WithBot.giUnbotDBot.gc.monotone_l hpq

@[simp]
theorem degree_C (ha : a ≠ 0) : degree (C a) = (0 : WithBot ℕ) := by
  rw [degree, ← monomial_zero_left, support_monomial 0 ha, max_eq_sup_coe, sup_singleton,
    WithBot.coe_zero]

theorem degree_C_le : degree (C a) ≤ 0 := by
  by_cases h : a = 0
  · rw [h, C_0]
    exact bot_le
  · rw [degree_C h]

theorem degree_C_lt : degree (C a) < 1 :=
  degree_C_le.trans_lt <| WithBot.coe_lt_coe.mpr zero_lt_one

theorem degree_one_le : degree (1 : R[X]) ≤ (0 : WithBot ℕ) := by rw [← C_1]; exact degree_C_le

@[simp]
theorem natDegree_C (a : R) : natDegree (C a) = 0 := by
  by_cases ha : a = 0
  · have : C a = 0 := by rw [ha, C_0]
    rw [natDegree, degree_eq_bot.2 this, WithBot.unbotD_bot]
  · rw [natDegree, degree_C ha, WithBot.unbotD_zero]

@[simp]
theorem natDegree_one : natDegree (1 : R[X]) = 0 :=
  natDegree_C 1

@[simp]
theorem natDegree_natCast (n : ℕ) : natDegree (n : R[X]) = 0 := by
  simp only [← C_eq_natCast, natDegree_C]

@[simp]
theorem natDegree_ofNat (n : ℕ) [Nat.AtLeastTwo n] :
    natDegree (ofNat(n) : R[X]) = 0 :=
  natDegree_natCast _

theorem degree_natCast_le (n : ℕ) : degree (n : R[X]) ≤ 0 := degree_le_of_natDegree_le (by simp)

@[simp]
theorem degree_monomial (n : ℕ) (ha : a ≠ 0) : degree (monomial n a) = n := by
  rw [degree, support_monomial n ha, max_singleton, Nat.cast_withBot]

@[simp]
theorem degree_C_mul_X_pow (n : ℕ) (ha : a ≠ 0) : degree (C a * X ^ n) = n := by
  rw [C_mul_X_pow_eq_monomial, degree_monomial n ha]

theorem degree_C_mul_X (ha : a ≠ 0) : degree (C a * X) = 1 := by
  simpa only [pow_one] using degree_C_mul_X_pow 1 ha

theorem degree_monomial_le (n : ℕ) (a : R) : degree (monomial n a) ≤ n :=
  letI := Classical.decEq R
  if h : a = 0 then by rw [h, (monomial n).map_zero, degree_zero]; exact bot_le
  else le_of_eq (degree_monomial n h)

theorem degree_C_mul_X_pow_le (n : ℕ) (a : R) : degree (C a * X ^ n) ≤ n := by
  rw [C_mul_X_pow_eq_monomial]
  apply degree_monomial_le

theorem degree_C_mul_X_le (a : R) : degree (C a * X) ≤ 1 := by
  simpa only [pow_one] using degree_C_mul_X_pow_le 1 a

@[simp]
theorem natDegree_C_mul_X_pow (n : ℕ) (a : R) (ha : a ≠ 0) : natDegree (C a * X ^ n) = n :=
  natDegree_eq_of_degree_eq_some (degree_C_mul_X_pow n ha)

@[simp]
theorem natDegree_C_mul_X (a : R) (ha : a ≠ 0) : natDegree (C a * X) = 1 := by
  simpa only [pow_one] using natDegree_C_mul_X_pow 1 a ha

@[simp]
theorem natDegree_monomial [DecidableEq R] (i : ℕ) (r : R) :
    natDegree (monomial i r) = if r = 0 then 0 else i := by
  split_ifs with hr
  · simp [hr]
  · rw [← C_mul_X_pow_eq_monomial, natDegree_C_mul_X_pow i r hr]

theorem natDegree_monomial_le (a : R) {m : ℕ} : (monomial m a).natDegree ≤ m := by
  classical
  rw [Polynomial.natDegree_monomial]
  split_ifs
  exacts [Nat.zero_le _, le_rfl]

theorem natDegree_monomial_eq (i : ℕ) {r : R} (r0 : r ≠ 0) : (monomial i r).natDegree = i :=
  letI := Classical.decEq R
  Eq.trans (natDegree_monomial _ _) (if_neg r0)

theorem coeff_ne_zero_of_eq_degree (hn : degree p = n) : coeff p n ≠ 0 := fun h =>
  mem_support_iff.mp (mem_of_max hn) h

theorem degree_X_pow_le (n : ℕ) : degree (X ^ n : R[X]) ≤ n := by
  simpa only [C_1, one_mul] using degree_C_mul_X_pow_le n (1 : R)

theorem degree_X_le : degree (X : R[X]) ≤ 1 :=
  degree_monomial_le _ _

theorem natDegree_X_le : (X : R[X]).natDegree ≤ 1 :=
  natDegree_le_of_degree_le degree_X_le

theorem withBotSucc_degree_eq_natDegree_add_one (h : p ≠ 0) : p.degree.succ = p.natDegree + 1 := by
  rw [degree_eq_natDegree h]
  exact WithBot.succ_coe p.natDegree

end Semiring

section NonzeroSemiring

variable [Semiring R] [Nontrivial R] {p q : R[X]}

@[simp]
theorem degree_one : degree (1 : R[X]) = (0 : WithBot ℕ) :=
  degree_C one_ne_zero

@[simp]
theorem degree_X : degree (X : R[X]) = 1 :=
  degree_monomial _ one_ne_zero

@[simp]
theorem natDegree_X : (X : R[X]).natDegree = 1 :=
  natDegree_eq_of_degree_eq_some degree_X

end NonzeroSemiring

section Ring

variable [Ring R]

@[simp]
theorem degree_neg (p : R[X]) : degree (-p) = degree p := by unfold degree; rw [support_neg]

theorem degree_neg_le_of_le {a : WithBot ℕ} {p : R[X]} (hp : degree p ≤ a) : degree (-p) ≤ a :=
  p.degree_neg.le.trans hp

@[simp]
theorem natDegree_neg (p : R[X]) : natDegree (-p) = natDegree p := by simp [natDegree]

theorem natDegree_neg_le_of_le {p : R[X]} (hp : natDegree p ≤ m) : natDegree (-p) ≤ m :=
  (natDegree_neg p).le.trans hp

@[simp]
theorem natDegree_intCast (n : ℤ) : natDegree (n : R[X]) = 0 := by
  rw [← C_eq_intCast, natDegree_C]

theorem degree_intCast_le (n : ℤ) : degree (n : R[X]) ≤ 0 := degree_le_of_natDegree_le (by simp)

@[simp]
theorem leadingCoeff_neg (p : R[X]) : (-p).leadingCoeff = -p.leadingCoeff := by
  rw [leadingCoeff, leadingCoeff, natDegree_neg, coeff_neg]

end Ring

section Semiring

variable [Semiring R] {p : R[X]}

/-- The second-highest coefficient, or 0 for constants -/
def nextCoeff (p : R[X]) : R :=
  if p.natDegree = 0 then 0 else p.coeff (p.natDegree - 1)

lemma nextCoeff_eq_zero :
    p.nextCoeff = 0 ↔ p.natDegree = 0 ∨ 0 < p.natDegree ∧ p.coeff (p.natDegree - 1) = 0 := by
  simp [nextCoeff, or_iff_not_imp_left, pos_iff_ne_zero]; simp_all

lemma nextCoeff_ne_zero : p.nextCoeff ≠ 0 ↔ p.natDegree ≠ 0 ∧ p.coeff (p.natDegree - 1) ≠ 0 := by
  simp [nextCoeff]

@[simp]
theorem nextCoeff_C_eq_zero (c : R) : nextCoeff (C c) = 0 := by
  rw [nextCoeff]
  simp

theorem nextCoeff_of_natDegree_pos (hp : 0 < p.natDegree) :
    nextCoeff p = p.coeff (p.natDegree - 1) := by
  rw [nextCoeff, if_neg]
  contrapose! hp
  simpa

variable {p q : R[X]} {ι : Type*}

theorem degree_add_le (p q : R[X]) : degree (p + q) ≤ max (degree p) (degree q) := by
  simpa only [degree, ← support_toFinsupp, toFinsupp_add]
    using AddMonoidAlgebra.sup_support_add_le _ _ _

theorem degree_add_le_of_degree_le {p q : R[X]} {n : ℕ} (hp : degree p ≤ n) (hq : degree q ≤ n) :
    degree (p + q) ≤ n :=
  (degree_add_le p q).trans <| max_le hp hq

theorem degree_add_le_of_le {a b : WithBot ℕ} (hp : degree p ≤ a) (hq : degree q ≤ b) :
    degree (p + q) ≤ max a b :=
  (p.degree_add_le q).trans <| max_le_max ‹_› ‹_›

theorem natDegree_add_le (p q : R[X]) : natDegree (p + q) ≤ max (natDegree p) (natDegree q) := by
  rcases le_max_iff.1 (degree_add_le p q) with h | h <;> simp [natDegree_le_natDegree h]

theorem natDegree_add_le_of_degree_le {p q : R[X]} {n : ℕ} (hp : natDegree p ≤ n)
    (hq : natDegree q ≤ n) : natDegree (p + q) ≤ n :=
  (natDegree_add_le p q).trans <| max_le hp hq

theorem natDegree_add_le_of_le (hp : natDegree p ≤ m) (hq : natDegree q ≤ n) :
    natDegree (p + q) ≤ max m n :=
  (p.natDegree_add_le q).trans <| max_le_max ‹_› ‹_›

@[simp]
theorem leadingCoeff_zero : leadingCoeff (0 : R[X]) = 0 :=
  rfl

@[simp]
theorem leadingCoeff_eq_zero : leadingCoeff p = 0 ↔ p = 0 :=
  ⟨fun h =>
    Classical.by_contradiction fun hp =>
      mt mem_support_iff.1 (Classical.not_not.2 h) (mem_of_max (degree_eq_natDegree hp)),
    fun h => h.symm ▸ leadingCoeff_zero⟩

theorem leadingCoeff_ne_zero : leadingCoeff p ≠ 0 ↔ p ≠ 0 := by rw [Ne, leadingCoeff_eq_zero]

theorem leadingCoeff_eq_zero_iff_deg_eq_bot : leadingCoeff p = 0 ↔ degree p = ⊥ := by
  rw [leadingCoeff_eq_zero, degree_eq_bot]

theorem natDegree_C_mul_X_pow_le (a : R) (n : ℕ) : natDegree (C a * X ^ n) ≤ n :=
  natDegree_le_iff_degree_le.2 <| degree_C_mul_X_pow_le _ _

theorem degree_erase_le (p : R[X]) (n : ℕ) : degree (p.erase n) ≤ degree p := by
  simp only [erase_def, degree, support]
  apply sup_mono
  rw [Finsupp.support_erase]
  apply Finset.erase_subset

theorem degree_erase_lt (hp : p ≠ 0) : degree (p.erase (natDegree p)) < degree p := by
  apply lt_of_le_of_ne (degree_erase_le _ _)
  rw [degree_eq_natDegree hp, degree, support_erase]
  exact fun h => notMem_erase _ _ (mem_of_max h)

theorem degree_update_le (p : R[X]) (n : ℕ) (a : R) : degree (p.update n a) ≤ max (degree p) n := by
  classical
  rw [degree, support_update]
  split_ifs
  · exact (Finset.max_mono (erase_subset _ _)).trans (le_max_left _ _)
  · rw [max_insert, max_comm]
    exact le_rfl

theorem degree_sum_le (s : Finset ι) (f : ι → R[X]) :
    degree (∑ i ∈ s, f i) ≤ s.sup fun b => degree (f b) :=
  Finset.cons_induction_on s (by simp only [sum_empty, sup_empty, degree_zero, le_refl])
    fun a s has ih =>
    calc
      degree (∑ i ∈ cons a s has, f i) ≤ max (degree (f a)) (degree (∑ i ∈ s, f i)) := by
        rw [Finset.sum_cons]; exact degree_add_le _ _
      _ ≤ _ := by rw [sup_cons]; exact max_le_max le_rfl ih

theorem degree_mul_le (p q : R[X]) : degree (p * q) ≤ degree p + degree q := by
  simpa [degree, ← support_toFinsupp] using AddMonoidAlgebra.sup_support_mul_le (by simp) ..

theorem degree_mul_le_of_le {a b : WithBot ℕ} (hp : degree p ≤ a) (hq : degree q ≤ b) :
    degree (p * q) ≤ a + b := by grw [degree_mul_le, hp, hq]

theorem degree_pow_le (p : R[X]) : ∀ n : ℕ, degree (p ^ n) ≤ n • degree p
  | 0 => by rw [pow_zero, zero_nsmul]; exact degree_one_le
  | n + 1 => by grw [pow_succ, succ_nsmul, degree_mul_le, degree_pow_le]

theorem degree_pow_le_of_le {a : WithBot ℕ} (b : ℕ) (hp : degree p ≤ a) :
    degree (p ^ b) ≤ b * a := by
  induction b with
  | zero => simp [degree_one_le]
  | succ n hn =>
      rw [Nat.cast_succ, add_mul, one_mul, pow_succ]
      exact degree_mul_le_of_le hn hp

@[simp]
theorem leadingCoeff_monomial (a : R) (n : ℕ) : leadingCoeff (monomial n a) = a := by
  classical
  by_cases ha : a = 0
  · simp only [ha, (monomial n).map_zero, leadingCoeff_zero]
  · rw [leadingCoeff, natDegree_monomial, if_neg ha, coeff_monomial]
    simp

theorem leadingCoeff_C_mul_X_pow (a : R) (n : ℕ) : leadingCoeff (C a * X ^ n) = a := by
  rw [C_mul_X_pow_eq_monomial, leadingCoeff_monomial]

theorem leadingCoeff_C_mul_X (a : R) : leadingCoeff (C a * X) = a := by
  simpa only [pow_one] using leadingCoeff_C_mul_X_pow a 1

@[simp]
theorem leadingCoeff_C (a : R) : leadingCoeff (C a) = a :=
  leadingCoeff_monomial a 0

theorem leadingCoeff_X_pow (n : ℕ) : leadingCoeff ((X : R[X]) ^ n) = 1 := by
  simpa only [C_1, one_mul] using leadingCoeff_C_mul_X_pow (1 : R) n

theorem leadingCoeff_X : leadingCoeff (X : R[X]) = 1 := by
  simpa only [pow_one] using @leadingCoeff_X_pow R _ 1

@[simp]
theorem monic_X_pow (n : ℕ) : Monic (X ^ n : R[X]) :=
  leadingCoeff_X_pow n

@[simp]
theorem monic_X : Monic (X : R[X]) :=
  leadingCoeff_X

theorem leadingCoeff_one : leadingCoeff (1 : R[X]) = 1 :=
  leadingCoeff_C 1

@[simp]
theorem monic_one : Monic (1 : R[X]) :=
  leadingCoeff_C _

theorem Monic.ne_zero [Nontrivial R] {p : R[X]} (hp : p.Monic) :
    p ≠ 0 := by
  rintro rfl
  simp [Monic] at hp

theorem Monic.ne_zero_of_ne (h : (0 : R) ≠ 1) {p : R[X]} (hp : p.Monic) : p ≠ 0 := by
  nontriviality R
  exact hp.ne_zero

lemma Monic.ne_zero_of_C [Nontrivial R] {c : R} (hc : Monic (C c)) : c ≠ 0 := by
  rintro rfl
  simp [Monic] at hc

theorem Monic.ne_zero_of_polynomial_ne {r} (hp : Monic p) (hne : q ≠ r) : p ≠ 0 :=
  haveI := Nontrivial.of_polynomial_ne hne
  hp.ne_zero

theorem natDegree_mul_le {p q : R[X]} : natDegree (p * q) ≤ natDegree p + natDegree q := by
  apply natDegree_le_of_degree_le
  apply le_trans (degree_mul_le p q)
  rw [Nat.cast_add]
  apply add_le_add <;> apply degree_le_natDegree

theorem natDegree_mul_le_of_le (hp : natDegree p ≤ m) (hg : natDegree q ≤ n) :
    natDegree (p * q) ≤ m + n :=
natDegree_mul_le.trans <| add_le_add ‹_› ‹_›

theorem natDegree_pow_le {p : R[X]} {n : ℕ} : (p ^ n).natDegree ≤ n * p.natDegree := by
  induction n with
  | zero => simp
  | succ i hi =>
    rw [pow_succ, Nat.succ_mul]
    apply le_trans natDegree_mul_le (add_le_add_right hi _)

theorem natDegree_pow_le_of_le (n : ℕ) (hp : natDegree p ≤ m) :
    natDegree (p ^ n) ≤ n * m :=
  natDegree_pow_le.trans (Nat.mul_le_mul le_rfl ‹_›)

theorem natDegree_eq_zero_iff_degree_le_zero : p.natDegree = 0 ↔ p.degree ≤ 0 := by
  rw [← nonpos_iff_eq_zero, natDegree_le_iff_degree_le, Nat.cast_zero]

theorem degree_zero_le : degree (0 : R[X]) ≤ 0 := natDegree_eq_zero_iff_degree_le_zero.mp rfl

theorem degree_le_iff_coeff_zero (f : R[X]) (n : WithBot ℕ) :
    degree f ≤ n ↔ ∀ m : ℕ, n < m → coeff f m = 0 := by
  simp only [degree, Finset.max, Finset.sup_le_iff, mem_support_iff, Ne, ← not_le,
    not_imp_comm, Nat.cast_withBot]

theorem degree_lt_iff_coeff_zero (f : R[X]) (n : ℕ) :
    degree f < n ↔ ∀ m : ℕ, n ≤ m → coeff f m = 0 := by
  simp only [degree, Finset.sup_lt_iff (WithBot.bot_lt_coe n), mem_support_iff,
    WithBot.coe_lt_coe, ← @not_le ℕ, max_eq_sup_coe, Nat.cast_withBot, Ne, not_imp_not]

theorem natDegree_pos_iff_degree_pos : 0 < natDegree p ↔ 0 < degree p :=
  lt_iff_lt_of_le_iff_le natDegree_le_iff_degree_le

end Semiring

section NontrivialSemiring

variable [Semiring R] [Nontrivial R] {p q : R[X]} (n : ℕ)

@[simp]
theorem degree_X_pow : degree ((X : R[X]) ^ n) = n := by
  rw [X_pow_eq_monomial, degree_monomial _ (one_ne_zero' R)]

@[simp]
theorem natDegree_X_pow : natDegree ((X : R[X]) ^ n) = n :=
  natDegree_eq_of_degree_eq_some (degree_X_pow n)

end NontrivialSemiring

section Ring

variable [Ring R] {p q : R[X]}

theorem degree_sub_le (p q : R[X]) : degree (p - q) ≤ max (degree p) (degree q) := by
  simpa only [degree_neg q] using degree_add_le p (-q)

theorem degree_sub_le_of_le {a b : WithBot ℕ} (hp : degree p ≤ a) (hq : degree q ≤ b) :
    degree (p - q) ≤ max a b :=
  (p.degree_sub_le q).trans <| max_le_max ‹_› ‹_›

theorem natDegree_sub_le (p q : R[X]) : natDegree (p - q) ≤ max (natDegree p) (natDegree q) := by
  simpa only [← natDegree_neg q] using natDegree_add_le p (-q)

theorem natDegree_sub_le_of_le (hp : natDegree p ≤ m) (hq : natDegree q ≤ n) :
    natDegree (p - q) ≤ max m n :=
  (p.natDegree_sub_le q).trans <| max_le_max ‹_› ‹_›

theorem degree_sub_lt (hd : degree p = degree q) (hp0 : p ≠ 0)
    (hlc : leadingCoeff p = leadingCoeff q) : degree (p - q) < degree p :=
  have hp : monomial (natDegree p) (leadingCoeff p) + p.erase (natDegree p) = p :=
    monomial_add_erase _ _
  have hq : monomial (natDegree q) (leadingCoeff q) + q.erase (natDegree q) = q :=
    monomial_add_erase _ _
  have hd' : natDegree p = natDegree q := by unfold natDegree; rw [hd]
  have hq0 : q ≠ 0 := mt degree_eq_bot.2 (hd ▸ mt degree_eq_bot.1 hp0)
  calc
    degree (p - q) = degree (erase (natDegree q) p + -erase (natDegree q) q) := by
      conv =>
        lhs
        rw [← hp, ← hq, hlc, hd', add_sub_add_left_eq_sub, sub_eq_add_neg]
    _ ≤ max (degree (erase (natDegree q) p)) (degree (erase (natDegree q) q)) :=
      (degree_neg (erase (natDegree q) q) ▸ degree_add_le _ _)
    _ < degree p := max_lt_iff.2 ⟨hd' ▸ degree_erase_lt hp0, hd.symm ▸ degree_erase_lt hq0⟩

theorem degree_X_sub_C_le (r : R) : (X - C r).degree ≤ 1 :=
  (degree_sub_le _ _).trans (max_le degree_X_le (degree_C_le.trans zero_le_one))

theorem natDegree_X_sub_C_le (r : R) : (X - C r).natDegree ≤ 1 :=
  natDegree_le_iff_degree_le.2 <| degree_X_sub_C_le r

end Ring

end Polynomial
