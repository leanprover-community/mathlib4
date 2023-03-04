/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker

! This file was ported from Lean 3 source module data.polynomial.degree.definitions
! leanprover-community/mathlib commit 808ea4ebfabeb599f21ec4ae87d6dc969597887f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.BigOperators
import Mathbin.Data.Nat.WithBot
import Mathbin.Data.Polynomial.Monomial
import Mathbin.Data.Polynomial.Coeff

/-!
# Theory of univariate polynomials

The definitions include
`degree`, `monic`, `leading_coeff`

Results include
- `degree_mul` : The degree of the product is the sum of degrees
- `leading_coeff_add_of_degree_eq` and `leading_coeff_add_of_degree_lt` :
    The leading_coefficient of a sum is determined by the leading coefficients and degrees
-/


noncomputable section

open Finsupp Finset

open BigOperators Classical Polynomial

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
#align polynomial.degree Polynomial.degree

theorem degree_lt_wf : WellFounded fun p q : R[X] => degree p < degree q :=
  InvImage.wf degree (WithBot.wellFounded_lt Nat.lt_wfRel)
#align polynomial.degree_lt_wf Polynomial.degree_lt_wf

instance : WellFoundedRelation R[X] :=
  ⟨_, degree_lt_wf⟩

/-- `nat_degree p` forces `degree p` to ℕ, by defining nat_degree 0 = 0. -/
def natDegree (p : R[X]) : ℕ :=
  (degree p).unbot' 0
#align polynomial.nat_degree Polynomial.natDegree

/-- `leading_coeff p` gives the coefficient of the highest power of `X` in `p`-/
def leadingCoeff (p : R[X]) : R :=
  coeff p (natDegree p)
#align polynomial.leading_coeff Polynomial.leadingCoeff

/-- a polynomial is `monic` if its leading coefficient is 1 -/
def Monic (p : R[X]) :=
  leadingCoeff p = (1 : R)
#align polynomial.monic Polynomial.Monic

@[nontriviality]
theorem monic_of_subsingleton [Subsingleton R] (p : R[X]) : Monic p :=
  Subsingleton.elim _ _
#align polynomial.monic_of_subsingleton Polynomial.monic_of_subsingleton

theorem Monic.def : Monic p ↔ leadingCoeff p = 1 :=
  Iff.rfl
#align polynomial.monic.def Polynomial.Monic.def

instance Monic.decidable [DecidableEq R] : Decidable (Monic p) := by unfold monic <;> infer_instance
#align polynomial.monic.decidable Polynomial.Monic.decidable

@[simp]
theorem Monic.leadingCoeff {p : R[X]} (hp : p.Monic) : leadingCoeff p = 1 :=
  hp
#align polynomial.monic.leading_coeff Polynomial.Monic.leadingCoeff

theorem Monic.coeff_natDegree {p : R[X]} (hp : p.Monic) : p.coeff p.natDegree = 1 :=
  hp
#align polynomial.monic.coeff_nat_degree Polynomial.Monic.coeff_natDegree

@[simp]
theorem degree_zero : degree (0 : R[X]) = ⊥ :=
  rfl
#align polynomial.degree_zero Polynomial.degree_zero

@[simp]
theorem natDegree_zero : natDegree (0 : R[X]) = 0 :=
  rfl
#align polynomial.nat_degree_zero Polynomial.natDegree_zero

@[simp]
theorem coeff_natDegree : coeff p (natDegree p) = leadingCoeff p :=
  rfl
#align polynomial.coeff_nat_degree Polynomial.coeff_natDegree

theorem degree_eq_bot : degree p = ⊥ ↔ p = 0 :=
  ⟨fun h => support_eq_empty.1 (Finset.max_eq_bot.1 h), fun h => h.symm ▸ rfl⟩
#align polynomial.degree_eq_bot Polynomial.degree_eq_bot

@[nontriviality]
theorem degree_of_subsingleton [Subsingleton R] : degree p = ⊥ := by
  rw [Subsingleton.elim p 0, degree_zero]
#align polynomial.degree_of_subsingleton Polynomial.degree_of_subsingleton

@[nontriviality]
theorem natDegree_of_subsingleton [Subsingleton R] : natDegree p = 0 := by
  rw [Subsingleton.elim p 0, nat_degree_zero]
#align polynomial.nat_degree_of_subsingleton Polynomial.natDegree_of_subsingleton

theorem degree_eq_natDegree (hp : p ≠ 0) : degree p = (natDegree p : WithBot ℕ) :=
  by
  let ⟨n, hn⟩ := not_forall.1 (mt Option.eq_none_iff_forall_not_mem.2 (mt degree_eq_bot.1 hp))
  have hn : degree p = some n := Classical.not_not.1 hn
  rw [nat_degree, hn] <;> rfl
#align polynomial.degree_eq_nat_degree Polynomial.degree_eq_natDegree

theorem degree_eq_iff_natDegree_eq {p : R[X]} {n : ℕ} (hp : p ≠ 0) :
    p.degree = n ↔ p.natDegree = n := by rw [degree_eq_nat_degree hp, WithBot.coe_eq_coe]
#align polynomial.degree_eq_iff_nat_degree_eq Polynomial.degree_eq_iff_natDegree_eq

theorem degree_eq_iff_natDegree_eq_of_pos {p : R[X]} {n : ℕ} (hn : 0 < n) :
    p.degree = n ↔ p.natDegree = n := by
  constructor
  · intro H
    rwa [← degree_eq_iff_nat_degree_eq]
    rintro rfl
    rw [degree_zero] at H
    exact Option.noConfusion H
  · intro H
    rwa [degree_eq_iff_nat_degree_eq]
    rintro rfl
    rw [nat_degree_zero] at H
    rw [H] at hn
    exact lt_irrefl _ hn
#align polynomial.degree_eq_iff_nat_degree_eq_of_pos Polynomial.degree_eq_iff_natDegree_eq_of_pos

theorem natDegree_eq_of_degree_eq_some {p : R[X]} {n : ℕ} (h : degree p = n) : natDegree p = n :=
  have hp0 : p ≠ 0 := fun hp0 => by rw [hp0] at h <;> exact Option.noConfusion h
  Option.some_inj.1 <| show (natDegree p : WithBot ℕ) = n by rwa [← degree_eq_nat_degree hp0]
#align polynomial.nat_degree_eq_of_degree_eq_some Polynomial.natDegree_eq_of_degree_eq_some

@[simp]
theorem degree_le_natDegree : degree p ≤ natDegree p :=
  WithBot.giUnbot'Bot.gc.le_u_l _
#align polynomial.degree_le_nat_degree Polynomial.degree_le_natDegree

theorem natDegree_eq_of_degree_eq [Semiring S] {q : S[X]} (h : degree p = degree q) :
    natDegree p = natDegree q := by unfold nat_degree <;> rw [h]
#align polynomial.nat_degree_eq_of_degree_eq Polynomial.natDegree_eq_of_degree_eq

theorem le_degree_of_ne_zero (h : coeff p n ≠ 0) : (n : WithBot ℕ) ≤ degree p :=
  show @LE.le (WithBot ℕ) _ (some n : WithBot ℕ) (p.support.sup some : WithBot ℕ) from
    Finset.le_sup (mem_support_iff.2 h)
#align polynomial.le_degree_of_ne_zero Polynomial.le_degree_of_ne_zero

theorem le_natDegree_of_ne_zero (h : coeff p n ≠ 0) : n ≤ natDegree p :=
  by
  rw [← WithBot.coe_le_coe, ← degree_eq_nat_degree]
  exact le_degree_of_ne_zero h
  · intro h
    subst h
    exact h rfl
#align polynomial.le_nat_degree_of_ne_zero Polynomial.le_natDegree_of_ne_zero

theorem le_natDegree_of_mem_supp (a : ℕ) : a ∈ p.support → a ≤ natDegree p :=
  le_natDegree_of_ne_zero ∘ mem_support_iff.mp
#align polynomial.le_nat_degree_of_mem_supp Polynomial.le_natDegree_of_mem_supp

theorem degree_eq_of_le_of_coeff_ne_zero (pn : p.degree ≤ n) (p1 : p.coeff n ≠ 0) : p.degree = n :=
  pn.antisymm (le_degree_of_ne_zero p1)
#align polynomial.degree_eq_of_le_of_coeff_ne_zero Polynomial.degree_eq_of_le_of_coeff_ne_zero

theorem natDegree_eq_of_le_of_coeff_ne_zero (pn : p.natDegree ≤ n) (p1 : p.coeff n ≠ 0) :
    p.natDegree = n :=
  pn.antisymm (le_natDegree_of_ne_zero p1)
#align polynomial.nat_degree_eq_of_le_of_coeff_ne_zero Polynomial.natDegree_eq_of_le_of_coeff_ne_zero

theorem degree_mono [Semiring S] {f : R[X]} {g : S[X]} (h : f.support ⊆ g.support) :
    f.degree ≤ g.degree :=
  Finset.sup_mono h
#align polynomial.degree_mono Polynomial.degree_mono

theorem supp_subset_range (h : natDegree p < m) : p.support ⊆ Finset.range m := fun n hn =>
  mem_range.2 <| (le_natDegree_of_mem_supp _ hn).trans_lt h
#align polynomial.supp_subset_range Polynomial.supp_subset_range

theorem supp_subset_range_natDegree_succ : p.support ⊆ Finset.range (natDegree p + 1) :=
  supp_subset_range (Nat.lt_succ_self _)
#align polynomial.supp_subset_range_nat_degree_succ Polynomial.supp_subset_range_natDegree_succ

theorem degree_le_degree (h : coeff q (natDegree p) ≠ 0) : degree p ≤ degree q :=
  by
  by_cases hp : p = 0
  · rw [hp]
    exact bot_le
  · rw [degree_eq_nat_degree hp]
    exact le_degree_of_ne_zero h
#align polynomial.degree_le_degree Polynomial.degree_le_degree

theorem degree_ne_of_natDegree_ne {n : ℕ} : p.natDegree ≠ n → degree p ≠ n :=
  mt fun h => by rw [nat_degree, h, WithBot.unbot'_coe]
#align polynomial.degree_ne_of_nat_degree_ne Polynomial.degree_ne_of_natDegree_ne

theorem natDegree_le_iff_degree_le {n : ℕ} : natDegree p ≤ n ↔ degree p ≤ n :=
  WithBot.unbot'_bot_le_iff
#align polynomial.nat_degree_le_iff_degree_le Polynomial.natDegree_le_iff_degree_le

theorem natDegree_lt_iff_degree_lt (hp : p ≠ 0) : p.natDegree < n ↔ p.degree < ↑n :=
  WithBot.unbot'_lt_iff <| degree_eq_bot.Not.mpr hp
#align polynomial.nat_degree_lt_iff_degree_lt Polynomial.natDegree_lt_iff_degree_lt

/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Alias.lean:29:6: warning: don't know how to generate #align statements for .. -/
alias nat_degree_le_iff_degree_le ↔ ..

theorem natDegree_le_natDegree [Semiring S] {q : S[X]} (hpq : p.degree ≤ q.degree) :
    p.natDegree ≤ q.natDegree :=
  WithBot.giUnbot'Bot.gc.monotone_l hpq
#align polynomial.nat_degree_le_nat_degree Polynomial.natDegree_le_natDegree

theorem natDegree_lt_natDegree {p q : R[X]} (hp : p ≠ 0) (hpq : p.degree < q.degree) :
    p.natDegree < q.natDegree := by
  by_cases hq : q = 0; · exact (not_lt_bot <| hq.subst hpq).elim
  rwa [degree_eq_nat_degree hp, degree_eq_nat_degree hq, WithBot.coe_lt_coe] at hpq
#align polynomial.nat_degree_lt_nat_degree Polynomial.natDegree_lt_natDegree

@[simp]
theorem degree_c (ha : a ≠ 0) : degree (c a) = (0 : WithBot ℕ) := by
  rw [degree, ← monomial_zero_left, support_monomial 0 ha, max_eq_sup_coe, sup_singleton,
    WithBot.coe_zero]
#align polynomial.degree_C Polynomial.degree_c

theorem degree_c_le : degree (c a) ≤ 0 :=
  by
  by_cases h : a = 0
  · rw [h, C_0]
    exact bot_le
  · rw [degree_C h]
    exact le_rfl
#align polynomial.degree_C_le Polynomial.degree_c_le

theorem degree_c_lt : degree (c a) < 1 :=
  degree_c_le.trans_lt <| WithBot.coe_lt_coe.mpr zero_lt_one
#align polynomial.degree_C_lt Polynomial.degree_c_lt

theorem degree_one_le : degree (1 : R[X]) ≤ (0 : WithBot ℕ) := by rw [← C_1] <;> exact degree_C_le
#align polynomial.degree_one_le Polynomial.degree_one_le

@[simp]
theorem natDegree_c (a : R) : natDegree (c a) = 0 :=
  by
  by_cases ha : a = 0
  · have : C a = 0 := by rw [ha, C_0]
    rw [nat_degree, degree_eq_bot.2 this]
    rfl
  · rw [nat_degree, degree_C ha]
    rfl
#align polynomial.nat_degree_C Polynomial.natDegree_c

@[simp]
theorem natDegree_one : natDegree (1 : R[X]) = 0 :=
  natDegree_c 1
#align polynomial.nat_degree_one Polynomial.natDegree_one

@[simp]
theorem natDegree_nat_cast (n : ℕ) : natDegree (n : R[X]) = 0 := by
  simp only [← C_eq_nat_cast, nat_degree_C]
#align polynomial.nat_degree_nat_cast Polynomial.natDegree_nat_cast

@[simp]
theorem degree_monomial (n : ℕ) (ha : a ≠ 0) : degree (monomial n a) = n := by
  rw [degree, support_monomial n ha] <;> rfl
#align polynomial.degree_monomial Polynomial.degree_monomial

@[simp]
theorem degree_c_mul_x_pow (n : ℕ) (ha : a ≠ 0) : degree (c a * x ^ n) = n := by
  rw [C_mul_X_pow_eq_monomial, degree_monomial n ha]
#align polynomial.degree_C_mul_X_pow Polynomial.degree_c_mul_x_pow

theorem degree_c_mul_x (ha : a ≠ 0) : degree (c a * x) = 1 := by
  simpa only [pow_one] using degree_C_mul_X_pow 1 ha
#align polynomial.degree_C_mul_X Polynomial.degree_c_mul_x

theorem degree_monomial_le (n : ℕ) (a : R) : degree (monomial n a) ≤ n :=
  if h : a = 0 then by rw [h, (monomial n).map_zero] <;> exact bot_le
  else le_of_eq (degree_monomial n h)
#align polynomial.degree_monomial_le Polynomial.degree_monomial_le

theorem degree_c_mul_x_pow_le (n : ℕ) (a : R) : degree (c a * x ^ n) ≤ n :=
  by
  rw [C_mul_X_pow_eq_monomial]
  apply degree_monomial_le
#align polynomial.degree_C_mul_X_pow_le Polynomial.degree_c_mul_x_pow_le

theorem degree_c_mul_x_le (a : R) : degree (c a * x) ≤ 1 := by
  simpa only [pow_one] using degree_C_mul_X_pow_le 1 a
#align polynomial.degree_C_mul_X_le Polynomial.degree_c_mul_x_le

@[simp]
theorem natDegree_c_mul_x_pow (n : ℕ) (a : R) (ha : a ≠ 0) : natDegree (c a * x ^ n) = n :=
  natDegree_eq_of_degree_eq_some (degree_c_mul_x_pow n ha)
#align polynomial.nat_degree_C_mul_X_pow Polynomial.natDegree_c_mul_x_pow

@[simp]
theorem natDegree_c_mul_x (a : R) (ha : a ≠ 0) : natDegree (c a * x) = 1 := by
  simpa only [pow_one] using nat_degree_C_mul_X_pow 1 a ha
#align polynomial.nat_degree_C_mul_X Polynomial.natDegree_c_mul_x

@[simp]
theorem natDegree_monomial [DecidableEq R] (i : ℕ) (r : R) :
    natDegree (monomial i r) = if r = 0 then 0 else i :=
  by
  split_ifs with hr
  · simp [hr]
  · rw [← C_mul_X_pow_eq_monomial, nat_degree_C_mul_X_pow i r hr]
#align polynomial.nat_degree_monomial Polynomial.natDegree_monomial

theorem natDegree_monomial_le (a : R) {m : ℕ} : (monomial m a).natDegree ≤ m :=
  by
  rw [Polynomial.natDegree_monomial]
  split_ifs
  exacts[Nat.zero_le _, rfl.le]
#align polynomial.nat_degree_monomial_le Polynomial.natDegree_monomial_le

theorem natDegree_monomial_eq (i : ℕ) {r : R} (r0 : r ≠ 0) : (monomial i r).natDegree = i :=
  Eq.trans (natDegree_monomial _ _) (if_neg r0)
#align polynomial.nat_degree_monomial_eq Polynomial.natDegree_monomial_eq

theorem coeff_eq_zero_of_degree_lt (h : degree p < n) : coeff p n = 0 :=
  Classical.not_not.1 (mt le_degree_of_ne_zero (not_le_of_gt h))
#align polynomial.coeff_eq_zero_of_degree_lt Polynomial.coeff_eq_zero_of_degree_lt

theorem coeff_eq_zero_of_natDegree_lt {p : R[X]} {n : ℕ} (h : p.natDegree < n) : p.coeff n = 0 :=
  by
  apply coeff_eq_zero_of_degree_lt
  by_cases hp : p = 0
  · subst hp
    exact WithBot.bot_lt_coe n
  · rwa [degree_eq_nat_degree hp, WithBot.coe_lt_coe]
#align polynomial.coeff_eq_zero_of_nat_degree_lt Polynomial.coeff_eq_zero_of_natDegree_lt

theorem ext_iff_natDegree_le {p q : R[X]} {n : ℕ} (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) :
    p = q ↔ ∀ i ≤ n, p.coeff i = q.coeff i :=
  by
  refine' Iff.trans Polynomial.ext_iff _
  refine' forall_congr' fun i => ⟨fun h _ => h, fun h => _⟩
  refine' (le_or_lt i n).elim h fun k => _
  refine'
    (coeff_eq_zero_of_nat_degree_lt (hp.trans_lt k)).trans
      (coeff_eq_zero_of_nat_degree_lt (hq.trans_lt k)).symm
#align polynomial.ext_iff_nat_degree_le Polynomial.ext_iff_natDegree_le

theorem ext_iff_degree_le {p q : R[X]} {n : ℕ} (hp : p.degree ≤ n) (hq : q.degree ≤ n) :
    p = q ↔ ∀ i ≤ n, p.coeff i = q.coeff i :=
  ext_iff_natDegree_le (natDegree_le_of_degree_le hp) (natDegree_le_of_degree_le hq)
#align polynomial.ext_iff_degree_le Polynomial.ext_iff_degree_le

@[simp]
theorem coeff_natDegree_succ_eq_zero {p : R[X]} : p.coeff (p.natDegree + 1) = 0 :=
  coeff_eq_zero_of_natDegree_lt (lt_add_one _)
#align polynomial.coeff_nat_degree_succ_eq_zero Polynomial.coeff_natDegree_succ_eq_zero

-- We need the explicit `decidable` argument here because an exotic one shows up in a moment!
theorem ite_le_natDegree_coeff (p : R[X]) (n : ℕ) (I : Decidable (n < 1 + natDegree p)) :
    @ite _ (n < 1 + natDegree p) I (coeff p n) 0 = coeff p n :=
  by
  split_ifs
  · rfl
  · exact (coeff_eq_zero_of_nat_degree_lt (not_le.1 fun w => h (Nat.lt_one_add_iff.2 w))).symm
#align polynomial.ite_le_nat_degree_coeff Polynomial.ite_le_natDegree_coeff

theorem as_sum_support (p : R[X]) : p = ∑ i in p.support, monomial i (p.coeff i) :=
  (sum_monomial_eq p).symm
#align polynomial.as_sum_support Polynomial.as_sum_support

theorem as_sum_support_c_mul_x_pow (p : R[X]) : p = ∑ i in p.support, c (p.coeff i) * x ^ i :=
  trans p.as_sum_support <| by simp only [C_mul_X_pow_eq_monomial]
#align polynomial.as_sum_support_C_mul_X_pow Polynomial.as_sum_support_c_mul_x_pow

/-- We can reexpress a sum over `p.support` as a sum over `range n`,
for any `n` satisfying `p.nat_degree < n`.
-/
theorem sum_over_range' [AddCommMonoid S] (p : R[X]) {f : ℕ → R → S} (h : ∀ n, f n 0 = 0) (n : ℕ)
    (w : p.natDegree < n) : p.Sum f = ∑ a : ℕ in range n, f a (coeff p a) :=
  by
  rcases p with ⟨⟩
  have := supp_subset_range w
  simp only [Polynomial.sum, support, coeff, nat_degree, degree] at this⊢
  exact Finsupp.sum_of_support_subset _ this _ fun n hn => h n
#align polynomial.sum_over_range' Polynomial.sum_over_range'

/-- We can reexpress a sum over `p.support` as a sum over `range (p.nat_degree + 1)`.
-/
theorem sum_over_range [AddCommMonoid S] (p : R[X]) {f : ℕ → R → S} (h : ∀ n, f n 0 = 0) :
    p.Sum f = ∑ a : ℕ in range (p.natDegree + 1), f a (coeff p a) :=
  sum_over_range' p h (p.natDegree + 1) (lt_add_one _)
#align polynomial.sum_over_range Polynomial.sum_over_range

-- TODO this is essentially a duplicate of `sum_over_range`, and should be removed.
theorem sum_fin [AddCommMonoid S] (f : ℕ → R → S) (hf : ∀ i, f i 0 = 0) {n : ℕ} {p : R[X]}
    (hn : p.degree < n) : (∑ i : Fin n, f i (p.coeff i)) = p.Sum f :=
  by
  by_cases hp : p = 0
  · rw [hp, sum_zero_index, Finset.sum_eq_zero]
    intro i _
    exact hf i
  rw [sum_over_range' _ hf n ((nat_degree_lt_iff_degree_lt hp).mpr hn),
    Fin.sum_univ_eq_sum_range fun i => f i (p.coeff i)]
#align polynomial.sum_fin Polynomial.sum_fin

theorem as_sum_range' (p : R[X]) (n : ℕ) (w : p.natDegree < n) :
    p = ∑ i in range n, monomial i (coeff p i) :=
  p.sum_monomial_eq.symm.trans <| p.sum_over_range' monomial_zero_right _ w
#align polynomial.as_sum_range' Polynomial.as_sum_range'

theorem as_sum_range (p : R[X]) : p = ∑ i in range (p.natDegree + 1), monomial i (coeff p i) :=
  p.sum_monomial_eq.symm.trans <| p.sum_over_range <| monomial_zero_right
#align polynomial.as_sum_range Polynomial.as_sum_range

theorem as_sum_range_c_mul_x_pow (p : R[X]) :
    p = ∑ i in range (p.natDegree + 1), c (coeff p i) * x ^ i :=
  p.as_sum_range.trans <| by simp only [C_mul_X_pow_eq_monomial]
#align polynomial.as_sum_range_C_mul_X_pow Polynomial.as_sum_range_c_mul_x_pow

theorem coeff_ne_zero_of_eq_degree (hn : degree p = n) : coeff p n ≠ 0 := fun h =>
  mem_support_iff.mp (mem_of_max hn) h
#align polynomial.coeff_ne_zero_of_eq_degree Polynomial.coeff_ne_zero_of_eq_degree

theorem eq_x_add_c_of_degree_le_one (h : degree p ≤ 1) : p = c (p.coeff 1) * x + c (p.coeff 0) :=
  ext fun n =>
    Nat.casesOn n (by simp) fun n =>
      Nat.casesOn n (by simp [coeff_C]) fun m =>
        by
        have : degree p < m.succ.succ := lt_of_le_of_lt h (by decide)
        simp [coeff_eq_zero_of_degree_lt this, coeff_C, Nat.succ_ne_zero, coeff_X, Nat.succ_inj',
          @eq_comm ℕ 0]
#align polynomial.eq_X_add_C_of_degree_le_one Polynomial.eq_x_add_c_of_degree_le_one

theorem eq_x_add_c_of_degree_eq_one (h : degree p = 1) : p = c p.leadingCoeff * x + c (p.coeff 0) :=
  (eq_x_add_c_of_degree_le_one (show degree p ≤ 1 from h ▸ le_rfl)).trans
    (by simp only [leading_coeff, nat_degree_eq_of_degree_eq_some h])
#align polynomial.eq_X_add_C_of_degree_eq_one Polynomial.eq_x_add_c_of_degree_eq_one

theorem eq_x_add_c_of_natDegree_le_one (h : natDegree p ≤ 1) :
    p = c (p.coeff 1) * x + c (p.coeff 0) :=
  eq_x_add_c_of_degree_le_one <| degree_le_of_natDegree_le h
#align polynomial.eq_X_add_C_of_nat_degree_le_one Polynomial.eq_x_add_c_of_natDegree_le_one

theorem Monic.eq_x_add_c (hm : p.Monic) (hnd : p.natDegree = 1) : p = x + c (p.coeff 0) := by
  rw [← one_mul X, ← C_1, ← hm.coeff_nat_degree, hnd, ← eq_X_add_C_of_nat_degree_le_one hnd.le]
#align polynomial.monic.eq_X_add_C Polynomial.Monic.eq_x_add_c

theorem exists_eq_x_add_c_of_natDegree_le_one (h : natDegree p ≤ 1) : ∃ a b, p = c a * x + c b :=
  ⟨p.coeff 1, p.coeff 0, eq_x_add_c_of_natDegree_le_one h⟩
#align polynomial.exists_eq_X_add_C_of_nat_degree_le_one Polynomial.exists_eq_x_add_c_of_natDegree_le_one

theorem degree_x_pow_le (n : ℕ) : degree (x ^ n : R[X]) ≤ n := by
  simpa only [C_1, one_mul] using degree_C_mul_X_pow_le n (1 : R)
#align polynomial.degree_X_pow_le Polynomial.degree_x_pow_le

theorem degree_x_le : degree (x : R[X]) ≤ 1 :=
  degree_monomial_le _ _
#align polynomial.degree_X_le Polynomial.degree_x_le

theorem natDegree_x_le : (x : R[X]).natDegree ≤ 1 :=
  natDegree_le_of_degree_le degree_x_le
#align polynomial.nat_degree_X_le Polynomial.natDegree_x_le

theorem mem_support_c_mul_x_pow {n a : ℕ} {c : R} (h : a ∈ (c c * x ^ n).support) : a = n :=
  mem_singleton.1 <| support_c_mul_x_pow' n c h
#align polynomial.mem_support_C_mul_X_pow Polynomial.mem_support_c_mul_x_pow

theorem card_support_c_mul_x_pow_le_one {c : R} {n : ℕ} : (c c * x ^ n).support.card ≤ 1 :=
  by
  rw [← card_singleton n]
  apply card_le_of_subset (support_C_mul_X_pow' n c)
#align polynomial.card_support_C_mul_X_pow_le_one Polynomial.card_support_c_mul_x_pow_le_one

theorem card_supp_le_succ_natDegree (p : R[X]) : p.support.card ≤ p.natDegree + 1 :=
  by
  rw [← Finset.card_range (p.nat_degree + 1)]
  exact Finset.card_le_of_subset supp_subset_range_nat_degree_succ
#align polynomial.card_supp_le_succ_nat_degree Polynomial.card_supp_le_succ_natDegree

theorem le_degree_of_mem_supp (a : ℕ) : a ∈ p.support → ↑a ≤ degree p :=
  le_degree_of_ne_zero ∘ mem_support_iff.mp
#align polynomial.le_degree_of_mem_supp Polynomial.le_degree_of_mem_supp

theorem nonempty_support_iff : p.support.Nonempty ↔ p ≠ 0 := by
  rw [Ne.def, nonempty_iff_ne_empty, Ne.def, ← support_eq_empty]
#align polynomial.nonempty_support_iff Polynomial.nonempty_support_iff

end Semiring

section NonzeroSemiring

variable [Semiring R] [Nontrivial R] {p q : R[X]}

@[simp]
theorem degree_one : degree (1 : R[X]) = (0 : WithBot ℕ) :=
  degree_c (show (1 : R) ≠ 0 from zero_ne_one.symm)
#align polynomial.degree_one Polynomial.degree_one

@[simp]
theorem degree_x : degree (x : R[X]) = 1 :=
  degree_monomial _ one_ne_zero
#align polynomial.degree_X Polynomial.degree_x

@[simp]
theorem natDegree_x : (x : R[X]).natDegree = 1 :=
  natDegree_eq_of_degree_eq_some degree_x
#align polynomial.nat_degree_X Polynomial.natDegree_x

end NonzeroSemiring

section Ring

variable [Ring R]

theorem coeff_mul_x_sub_c {p : R[X]} {r : R} {a : ℕ} :
    coeff (p * (x - c r)) (a + 1) = coeff p a - coeff p (a + 1) * r := by simp [mul_sub]
#align polynomial.coeff_mul_X_sub_C Polynomial.coeff_mul_x_sub_c

@[simp]
theorem degree_neg (p : R[X]) : degree (-p) = degree p := by unfold degree <;> rw [support_neg]
#align polynomial.degree_neg Polynomial.degree_neg

@[simp]
theorem natDegree_neg (p : R[X]) : natDegree (-p) = natDegree p := by simp [nat_degree]
#align polynomial.nat_degree_neg Polynomial.natDegree_neg

@[simp]
theorem natDegree_int_cast (n : ℤ) : natDegree (n : R[X]) = 0 := by
  rw [← C_eq_int_cast, nat_degree_C]
#align polynomial.nat_degree_int_cast Polynomial.natDegree_int_cast

@[simp]
theorem leadingCoeff_neg (p : R[X]) : (-p).leadingCoeff = -p.leadingCoeff := by
  rw [leading_coeff, leading_coeff, nat_degree_neg, coeff_neg]
#align polynomial.leading_coeff_neg Polynomial.leadingCoeff_neg

end Ring

section Semiring

variable [Semiring R]

/-- The second-highest coefficient, or 0 for constants -/
def nextCoeff (p : R[X]) : R :=
  if p.natDegree = 0 then 0 else p.coeff (p.natDegree - 1)
#align polynomial.next_coeff Polynomial.nextCoeff

@[simp]
theorem nextCoeff_c_eq_zero (c : R) : nextCoeff (c c) = 0 :=
  by
  rw [next_coeff]
  simp
#align polynomial.next_coeff_C_eq_zero Polynomial.nextCoeff_c_eq_zero

theorem nextCoeff_of_pos_natDegree (p : R[X]) (hp : 0 < p.natDegree) :
    nextCoeff p = p.coeff (p.natDegree - 1) :=
  by
  rw [next_coeff, if_neg]
  contrapose! hp
  simpa
#align polynomial.next_coeff_of_pos_nat_degree Polynomial.nextCoeff_of_pos_natDegree

variable {p q : R[X]} {ι : Type _}

theorem coeff_natDegree_eq_zero_of_degree_lt (h : degree p < degree q) :
    coeff p (natDegree q) = 0 :=
  coeff_eq_zero_of_degree_lt (lt_of_lt_of_le h degree_le_natDegree)
#align polynomial.coeff_nat_degree_eq_zero_of_degree_lt Polynomial.coeff_natDegree_eq_zero_of_degree_lt

theorem ne_zero_of_degree_gt {n : WithBot ℕ} (h : n < degree p) : p ≠ 0 :=
  mt degree_eq_bot.2 (Ne.symm (ne_of_lt (lt_of_le_of_lt bot_le h)))
#align polynomial.ne_zero_of_degree_gt Polynomial.ne_zero_of_degree_gt

theorem ne_zero_of_degree_ge_degree (hpq : p.degree ≤ q.degree) (hp : p ≠ 0) : q ≠ 0 :=
  Polynomial.ne_zero_of_degree_gt
    (lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr (by rwa [Ne.def, Polynomial.degree_eq_bot])) hpq :
      q.degree > ⊥)
#align polynomial.ne_zero_of_degree_ge_degree Polynomial.ne_zero_of_degree_ge_degree

theorem ne_zero_of_natDegree_gt {n : ℕ} (h : n < natDegree p) : p ≠ 0 := fun H => by
  simpa [H, Nat.not_lt_zero] using h
#align polynomial.ne_zero_of_nat_degree_gt Polynomial.ne_zero_of_natDegree_gt

theorem degree_lt_degree (h : natDegree p < natDegree q) : degree p < degree q :=
  by
  by_cases hp : p = 0
  · simp [hp]
    rw [bot_lt_iff_ne_bot]
    intro hq
    simpa [hp, degree_eq_bot.mp hq, lt_irrefl] using h
  · rw [degree_eq_nat_degree hp, degree_eq_nat_degree <| ne_zero_of_nat_degree_gt h]
    exact_mod_cast h
#align polynomial.degree_lt_degree Polynomial.degree_lt_degree

theorem natDegree_lt_natDegree_iff (hp : p ≠ 0) : natDegree p < natDegree q ↔ degree p < degree q :=
  ⟨degree_lt_degree, by
    intro h
    have hq : q ≠ 0 := ne_zero_of_degree_gt h
    rw [degree_eq_nat_degree hp, degree_eq_nat_degree hq] at h
    exact_mod_cast h⟩
#align polynomial.nat_degree_lt_nat_degree_iff Polynomial.natDegree_lt_natDegree_iff

theorem eq_c_of_degree_le_zero (h : degree p ≤ 0) : p = c (coeff p 0) :=
  by
  ext (_ | n); · simp
  rw [coeff_C, if_neg (Nat.succ_ne_zero _), coeff_eq_zero_of_degree_lt]
  exact h.trans_lt (WithBot.some_lt_some.2 n.succ_pos)
#align polynomial.eq_C_of_degree_le_zero Polynomial.eq_c_of_degree_le_zero

theorem eq_c_of_degree_eq_zero (h : degree p = 0) : p = c (coeff p 0) :=
  eq_c_of_degree_le_zero (h ▸ le_rfl)
#align polynomial.eq_C_of_degree_eq_zero Polynomial.eq_c_of_degree_eq_zero

theorem degree_le_zero_iff : degree p ≤ 0 ↔ p = c (coeff p 0) :=
  ⟨eq_c_of_degree_le_zero, fun h => h.symm ▸ degree_c_le⟩
#align polynomial.degree_le_zero_iff Polynomial.degree_le_zero_iff

theorem degree_add_le (p q : R[X]) : degree (p + q) ≤ max (degree p) (degree q) :=
  calc
    degree (p + q) = (p + q).support.sup some := rfl
    _ ≤ (p.support ∪ q.support).sup some := (sup_mono support_add)
    _ = p.support.sup some ⊔ q.support.sup some := sup_union
    
#align polynomial.degree_add_le Polynomial.degree_add_le

theorem degree_add_le_of_degree_le {p q : R[X]} {n : ℕ} (hp : degree p ≤ n) (hq : degree q ≤ n) :
    degree (p + q) ≤ n :=
  (degree_add_le p q).trans <| max_le hp hq
#align polynomial.degree_add_le_of_degree_le Polynomial.degree_add_le_of_degree_le

theorem natDegree_add_le (p q : R[X]) : natDegree (p + q) ≤ max (natDegree p) (natDegree q) := by
  cases le_max_iff.1 (degree_add_le p q) <;> simp [nat_degree_le_nat_degree h]
#align polynomial.nat_degree_add_le Polynomial.natDegree_add_le

theorem natDegree_add_le_of_degree_le {p q : R[X]} {n : ℕ} (hp : natDegree p ≤ n)
    (hq : natDegree q ≤ n) : natDegree (p + q) ≤ n :=
  (natDegree_add_le p q).trans <| max_le hp hq
#align polynomial.nat_degree_add_le_of_degree_le Polynomial.natDegree_add_le_of_degree_le

@[simp]
theorem leadingCoeff_zero : leadingCoeff (0 : R[X]) = 0 :=
  rfl
#align polynomial.leading_coeff_zero Polynomial.leadingCoeff_zero

@[simp]
theorem leadingCoeff_eq_zero : leadingCoeff p = 0 ↔ p = 0 :=
  ⟨fun h =>
    by_contradiction fun hp =>
      mt mem_support_iff.1 (Classical.not_not.2 h) (mem_of_max (degree_eq_natDegree hp)),
    fun h => h.symm ▸ leadingCoeff_zero⟩
#align polynomial.leading_coeff_eq_zero Polynomial.leadingCoeff_eq_zero

theorem leadingCoeff_ne_zero : leadingCoeff p ≠ 0 ↔ p ≠ 0 := by rw [Ne.def, leading_coeff_eq_zero]
#align polynomial.leading_coeff_ne_zero Polynomial.leadingCoeff_ne_zero

theorem leadingCoeff_eq_zero_iff_deg_eq_bot : leadingCoeff p = 0 ↔ degree p = ⊥ := by
  rw [leading_coeff_eq_zero, degree_eq_bot]
#align polynomial.leading_coeff_eq_zero_iff_deg_eq_bot Polynomial.leadingCoeff_eq_zero_iff_deg_eq_bot

theorem natDegree_mem_support_of_nonzero (H : p ≠ 0) : p.natDegree ∈ p.support :=
  by
  rw [mem_support_iff]
  exact (not_congr leading_coeff_eq_zero).mpr H
#align polynomial.nat_degree_mem_support_of_nonzero Polynomial.natDegree_mem_support_of_nonzero

theorem natDegree_eq_support_max' (h : p ≠ 0) :
    p.natDegree = p.support.max' (nonempty_support_iff.mpr h) :=
  (le_max' _ _ <| natDegree_mem_support_of_nonzero h).antisymm <|
    max'_le _ _ _ le_natDegree_of_mem_supp
#align polynomial.nat_degree_eq_support_max' Polynomial.natDegree_eq_support_max'

theorem natDegree_c_mul_x_pow_le (a : R) (n : ℕ) : natDegree (c a * x ^ n) ≤ n :=
  natDegree_le_iff_degree_le.2 <| degree_c_mul_x_pow_le _ _
#align polynomial.nat_degree_C_mul_X_pow_le Polynomial.natDegree_c_mul_x_pow_le

theorem degree_add_eq_left_of_degree_lt (h : degree q < degree p) : degree (p + q) = degree p :=
  le_antisymm (max_eq_left_of_lt h ▸ degree_add_le _ _) <|
    degree_le_degree <|
      by
      rw [coeff_add, coeff_nat_degree_eq_zero_of_degree_lt h, add_zero]
      exact mt leading_coeff_eq_zero.1 (ne_zero_of_degree_gt h)
#align polynomial.degree_add_eq_left_of_degree_lt Polynomial.degree_add_eq_left_of_degree_lt

theorem degree_add_eq_right_of_degree_lt (h : degree p < degree q) : degree (p + q) = degree q := by
  rw [add_comm, degree_add_eq_left_of_degree_lt h]
#align polynomial.degree_add_eq_right_of_degree_lt Polynomial.degree_add_eq_right_of_degree_lt

theorem natDegree_add_eq_left_of_natDegree_lt (h : natDegree q < natDegree p) :
    natDegree (p + q) = natDegree p :=
  natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt (degree_lt_degree h))
#align polynomial.nat_degree_add_eq_left_of_nat_degree_lt Polynomial.natDegree_add_eq_left_of_natDegree_lt

theorem natDegree_add_eq_right_of_natDegree_lt (h : natDegree p < natDegree q) :
    natDegree (p + q) = natDegree q :=
  natDegree_eq_of_degree_eq (degree_add_eq_right_of_degree_lt (degree_lt_degree h))
#align polynomial.nat_degree_add_eq_right_of_nat_degree_lt Polynomial.natDegree_add_eq_right_of_natDegree_lt

theorem degree_add_c (hp : 0 < degree p) : degree (p + c a) = degree p :=
  add_comm (c a) p ▸ degree_add_eq_right_of_degree_lt <| lt_of_le_of_lt degree_c_le hp
#align polynomial.degree_add_C Polynomial.degree_add_c

theorem degree_add_eq_of_leadingCoeff_add_ne_zero (h : leadingCoeff p + leadingCoeff q ≠ 0) :
    degree (p + q) = max p.degree q.degree :=
  le_antisymm (degree_add_le _ _) <|
    match lt_trichotomy (degree p) (degree q) with
    | Or.inl hlt => by
      rw [degree_add_eq_right_of_degree_lt hlt, max_eq_right_of_lt hlt] <;> exact le_rfl
    | Or.inr (Or.inl HEq) =>
      le_of_not_gt fun hlt : max (degree p) (degree q) > degree (p + q) =>
        h <|
          show leadingCoeff p + leadingCoeff q = 0
            by
            rw [HEq, max_self] at hlt
            rw [leading_coeff, leading_coeff, nat_degree_eq_of_degree_eq HEq, ← coeff_add]
            exact coeff_nat_degree_eq_zero_of_degree_lt hlt
    | Or.inr (Or.inr hlt) => by
      rw [degree_add_eq_left_of_degree_lt hlt, max_eq_left_of_lt hlt] <;> exact le_rfl
#align polynomial.degree_add_eq_of_leading_coeff_add_ne_zero Polynomial.degree_add_eq_of_leadingCoeff_add_ne_zero

theorem degree_erase_le (p : R[X]) (n : ℕ) : degree (p.eraseₓ n) ≤ degree p :=
  by
  rcases p with ⟨⟩
  simp only [erase, degree, coeff, support]
  convert sup_mono (erase_subset _ _)
#align polynomial.degree_erase_le Polynomial.degree_erase_le

theorem degree_erase_lt (hp : p ≠ 0) : degree (p.eraseₓ (natDegree p)) < degree p :=
  by
  apply lt_of_le_of_ne (degree_erase_le _ _)
  rw [degree_eq_nat_degree hp, degree, support_erase]
  exact fun h => not_mem_erase _ _ (mem_of_max h)
#align polynomial.degree_erase_lt Polynomial.degree_erase_lt

theorem degree_update_le (p : R[X]) (n : ℕ) (a : R) : degree (p.update n a) ≤ max (degree p) n :=
  by
  rw [degree, support_update]
  split_ifs
  · exact (Finset.max_mono (erase_subset _ _)).trans (le_max_left _ _)
  · rw [max_insert, max_comm]
    exact le_rfl
#align polynomial.degree_update_le Polynomial.degree_update_le

theorem degree_sum_le (s : Finset ι) (f : ι → R[X]) :
    degree (∑ i in s, f i) ≤ s.sup fun b => degree (f b) :=
  Finset.induction_on s (by simp only [sum_empty, sup_empty, degree_zero, le_refl])
    fun a s has ih =>
    calc
      degree (∑ i in insert a s, f i) ≤ max (degree (f a)) (degree (∑ i in s, f i)) := by
        rw [sum_insert has] <;> exact degree_add_le _ _
      _ ≤ _ := by rw [sup_insert, sup_eq_max] <;> exact max_le_max le_rfl ih
      
#align polynomial.degree_sum_le Polynomial.degree_sum_le

theorem degree_mul_le (p q : R[X]) : degree (p * q) ≤ degree p + degree q :=
  calc
    degree (p * q) ≤
        p.support.sup fun i => degree (sum q fun j a => c (coeff p i * a) * x ^ (i + j)) :=
      by
      simp only [← C_mul_X_pow_eq_monomial.symm]
      convert degree_sum_le _ _
      exact mul_eq_sum_sum
    _ ≤
        p.support.sup fun i =>
          q.support.sup fun j => degree (c (coeff p i * coeff q j) * x ^ (i + j)) :=
      (Finset.sup_mono_fun fun i hi => degree_sum_le _ _)
    _ ≤ degree p + degree q :=
      by
      refine'
        Finset.sup_le fun a ha => Finset.sup_le fun b hb => le_trans (degree_C_mul_X_pow_le _ _) _
      rw [WithBot.coe_add]
      rw [mem_support_iff] at ha hb
      exact add_le_add (le_degree_of_ne_zero ha) (le_degree_of_ne_zero hb)
    
#align polynomial.degree_mul_le Polynomial.degree_mul_le

theorem degree_pow_le (p : R[X]) : ∀ n : ℕ, degree (p ^ n) ≤ n • degree p
  | 0 => by rw [pow_zero, zero_nsmul] <;> exact degree_one_le
  | n + 1 =>
    calc
      degree (p ^ (n + 1)) ≤ degree p + degree (p ^ n) := by
        rw [pow_succ] <;> exact degree_mul_le _ _
      _ ≤ _ := by rw [succ_nsmul] <;> exact add_le_add le_rfl (degree_pow_le _)
      
#align polynomial.degree_pow_le Polynomial.degree_pow_le

@[simp]
theorem leadingCoeff_monomial (a : R) (n : ℕ) : leadingCoeff (monomial n a) = a :=
  by
  by_cases ha : a = 0
  · simp only [ha, (monomial n).map_zero, leading_coeff_zero]
  · rw [leading_coeff, nat_degree_monomial, if_neg ha, coeff_monomial]
    simp
#align polynomial.leading_coeff_monomial Polynomial.leadingCoeff_monomial

theorem leadingCoeff_c_mul_x_pow (a : R) (n : ℕ) : leadingCoeff (c a * x ^ n) = a := by
  rw [C_mul_X_pow_eq_monomial, leading_coeff_monomial]
#align polynomial.leading_coeff_C_mul_X_pow Polynomial.leadingCoeff_c_mul_x_pow

theorem leadingCoeff_c_mul_x (a : R) : leadingCoeff (c a * x) = a := by
  simpa only [pow_one] using leading_coeff_C_mul_X_pow a 1
#align polynomial.leading_coeff_C_mul_X Polynomial.leadingCoeff_c_mul_x

@[simp]
theorem leadingCoeff_c (a : R) : leadingCoeff (c a) = a :=
  leadingCoeff_monomial a 0
#align polynomial.leading_coeff_C Polynomial.leadingCoeff_c

@[simp]
theorem leadingCoeff_x_pow (n : ℕ) : leadingCoeff ((x : R[X]) ^ n) = 1 := by
  simpa only [C_1, one_mul] using leading_coeff_C_mul_X_pow (1 : R) n
#align polynomial.leading_coeff_X_pow Polynomial.leadingCoeff_x_pow

@[simp]
theorem leadingCoeff_x : leadingCoeff (x : R[X]) = 1 := by
  simpa only [pow_one] using @leading_coeff_X_pow R _ 1
#align polynomial.leading_coeff_X Polynomial.leadingCoeff_x

@[simp]
theorem monic_x_pow (n : ℕ) : Monic (x ^ n : R[X]) :=
  leadingCoeff_x_pow n
#align polynomial.monic_X_pow Polynomial.monic_x_pow

@[simp]
theorem monic_x : Monic (x : R[X]) :=
  leadingCoeff_x
#align polynomial.monic_X Polynomial.monic_x

@[simp]
theorem leadingCoeff_one : leadingCoeff (1 : R[X]) = 1 :=
  leadingCoeff_c 1
#align polynomial.leading_coeff_one Polynomial.leadingCoeff_one

@[simp]
theorem monic_one : Monic (1 : R[X]) :=
  leadingCoeff_c _
#align polynomial.monic_one Polynomial.monic_one

theorem Monic.ne_zero {R : Type _} [Semiring R] [Nontrivial R] {p : R[X]} (hp : p.Monic) : p ≠ 0 :=
  by
  rintro rfl
  simpa [monic] using hp
#align polynomial.monic.ne_zero Polynomial.Monic.ne_zero

theorem Monic.ne_zero_of_ne (h : (0 : R) ≠ 1) {p : R[X]} (hp : p.Monic) : p ≠ 0 :=
  by
  nontriviality R
  exact hp.ne_zero
#align polynomial.monic.ne_zero_of_ne Polynomial.Monic.ne_zero_of_ne

theorem monic_of_natDegree_le_of_coeff_eq_one (n : ℕ) (pn : p.natDegree ≤ n) (p1 : p.coeff n = 1) :
    Monic p := by
  nontriviality
  refine' (congr_arg _ <| nat_degree_eq_of_le_of_coeff_ne_zero pn _).trans p1
  exact ne_of_eq_of_ne p1 one_ne_zero
#align polynomial.monic_of_nat_degree_le_of_coeff_eq_one Polynomial.monic_of_natDegree_le_of_coeff_eq_one

theorem monic_of_degree_le_of_coeff_eq_one (n : ℕ) (pn : p.degree ≤ n) (p1 : p.coeff n = 1) :
    Monic p :=
  monic_of_natDegree_le_of_coeff_eq_one n (natDegree_le_of_degree_le pn) p1
#align polynomial.monic_of_degree_le_of_coeff_eq_one Polynomial.monic_of_degree_le_of_coeff_eq_one

theorem Monic.ne_zero_of_polynomial_ne {r} (hp : Monic p) (hne : q ≠ r) : p ≠ 0 :=
  haveI := nontrivial.of_polynomial_ne hne
  hp.ne_zero
#align polynomial.monic.ne_zero_of_polynomial_ne Polynomial.Monic.ne_zero_of_polynomial_ne

theorem leadingCoeff_add_of_degree_lt (h : degree p < degree q) :
    leadingCoeff (p + q) = leadingCoeff q :=
  by
  have : coeff p (natDegree q) = 0 := coeff_natDegree_eq_zero_of_degree_lt h
  simp only [leading_coeff, nat_degree_eq_of_degree_eq (degree_add_eq_right_of_degree_lt h), this,
    coeff_add, zero_add]
#align polynomial.leading_coeff_add_of_degree_lt Polynomial.leadingCoeff_add_of_degree_lt

theorem leadingCoeff_add_of_degree_eq (h : degree p = degree q)
    (hlc : leadingCoeff p + leadingCoeff q ≠ 0) :
    leadingCoeff (p + q) = leadingCoeff p + leadingCoeff q :=
  by
  have : natDegree (p + q) = natDegree p := by
    apply nat_degree_eq_of_degree_eq <;>
      rw [degree_add_eq_of_leading_coeff_add_ne_zero hlc, h, max_self]
  simp only [leading_coeff, this, nat_degree_eq_of_degree_eq h, coeff_add]
#align polynomial.leading_coeff_add_of_degree_eq Polynomial.leadingCoeff_add_of_degree_eq

@[simp]
theorem coeff_mul_degree_add_degree (p q : R[X]) :
    coeff (p * q) (natDegree p + natDegree q) = leadingCoeff p * leadingCoeff q :=
  calc
    coeff (p * q) (natDegree p + natDegree q) =
        ∑ x in Nat.antidiagonal (natDegree p + natDegree q), coeff p x.1 * coeff q x.2 :=
      coeff_mul _ _ _
    _ = coeff p (natDegree p) * coeff q (natDegree q) :=
      by
      refine' Finset.sum_eq_single (nat_degree p, nat_degree q) _ _
      · rintro ⟨i, j⟩ h₁ h₂
        rw [nat.mem_antidiagonal] at h₁
        by_cases H : nat_degree p < i
        ·
          rw [coeff_eq_zero_of_degree_lt
              (lt_of_le_of_lt degree_le_nat_degree (WithBot.coe_lt_coe.2 H)),
            zero_mul]
        · rw [not_lt_iff_eq_or_lt] at H
          cases H
          · subst H
            rw [add_left_cancel_iff] at h₁
            dsimp at h₁
            subst h₁
            exfalso
            exact h₂ rfl
          · suffices nat_degree q < j by
              rw [coeff_eq_zero_of_degree_lt
                  (lt_of_le_of_lt degree_le_nat_degree (WithBot.coe_lt_coe.2 this)),
                mul_zero]
            · by_contra H'
              rw [not_lt] at H'
              exact
                ne_of_lt (Nat.lt_of_lt_of_le (Nat.add_lt_add_right H j) (Nat.add_le_add_left H' _))
                  h₁
      · intro H
        exfalso
        apply H
        rw [nat.mem_antidiagonal]
    
#align polynomial.coeff_mul_degree_add_degree Polynomial.coeff_mul_degree_add_degree

theorem degree_mul' (h : leadingCoeff p * leadingCoeff q ≠ 0) :
    degree (p * q) = degree p + degree q :=
  have hp : p ≠ 0 := by refine' mt _ h <;> exact fun hp => by rw [hp, leading_coeff_zero, zero_mul]
  have hq : q ≠ 0 := by refine' mt _ h <;> exact fun hq => by rw [hq, leading_coeff_zero, mul_zero]
  le_antisymm (degree_mul_le _ _)
    (by
      rw [degree_eq_nat_degree hp, degree_eq_nat_degree hq]
      refine' le_degree_of_ne_zero _
      rwa [coeff_mul_degree_add_degree])
#align polynomial.degree_mul' Polynomial.degree_mul'

theorem Monic.degree_mul (hq : Monic q) : degree (p * q) = degree p + degree q :=
  if hp : p = 0 then by simp [hp]
  else degree_mul' <| by rwa [hq.leading_coeff, mul_one, Ne.def, leading_coeff_eq_zero]
#align polynomial.monic.degree_mul Polynomial.Monic.degree_mul

theorem natDegree_mul' (h : leadingCoeff p * leadingCoeff q ≠ 0) :
    natDegree (p * q) = natDegree p + natDegree q :=
  have hp : p ≠ 0 := mt leadingCoeff_eq_zero.2 fun h₁ => h <| by rw [h₁, zero_mul]
  have hq : q ≠ 0 := mt leadingCoeff_eq_zero.2 fun h₁ => h <| by rw [h₁, mul_zero]
  natDegree_eq_of_degree_eq_some <| by
    rw [degree_mul' h, WithBot.coe_add, degree_eq_nat_degree hp, degree_eq_nat_degree hq]
#align polynomial.nat_degree_mul' Polynomial.natDegree_mul'

theorem leadingCoeff_mul' (h : leadingCoeff p * leadingCoeff q ≠ 0) :
    leadingCoeff (p * q) = leadingCoeff p * leadingCoeff q :=
  by
  unfold leading_coeff
  rw [nat_degree_mul' h, coeff_mul_degree_add_degree]
  rfl
#align polynomial.leading_coeff_mul' Polynomial.leadingCoeff_mul'

theorem monomial_natDegree_leadingCoeff_eq_self (h : p.support.card ≤ 1) :
    monomial p.natDegree p.leadingCoeff = p :=
  by
  rcases card_support_le_one_iff_monomial.1 h with ⟨n, a, rfl⟩
  by_cases ha : a = 0 <;> simp [ha]
#align polynomial.monomial_nat_degree_leading_coeff_eq_self Polynomial.monomial_natDegree_leadingCoeff_eq_self

theorem c_mul_x_pow_eq_self (h : p.support.card ≤ 1) : c p.leadingCoeff * x ^ p.natDegree = p := by
  rw [C_mul_X_pow_eq_monomial, monomial_nat_degree_leading_coeff_eq_self h]
#align polynomial.C_mul_X_pow_eq_self Polynomial.c_mul_x_pow_eq_self

theorem leadingCoeff_pow' : leadingCoeff p ^ n ≠ 0 → leadingCoeff (p ^ n) = leadingCoeff p ^ n :=
  Nat.recOn n (by simp) fun n ih h =>
    by
    have h₁ : leadingCoeff p ^ n ≠ 0 := fun h₁ => h <| by rw [pow_succ, h₁, mul_zero]
    have h₂ : leadingCoeff p * leadingCoeff (p ^ n) ≠ 0 := by rwa [pow_succ, ← ih h₁] at h
    rw [pow_succ, pow_succ, leading_coeff_mul' h₂, ih h₁]
#align polynomial.leading_coeff_pow' Polynomial.leadingCoeff_pow'

theorem degree_pow' : ∀ {n : ℕ}, leadingCoeff p ^ n ≠ 0 → degree (p ^ n) = n • degree p
  | 0 => fun h => by rw [pow_zero, ← C_1] at * <;> rw [degree_C h, zero_nsmul]
  | n + 1 => fun h =>
    by
    have h₁ : leadingCoeff p ^ n ≠ 0 := fun h₁ => h <| by rw [pow_succ, h₁, mul_zero]
    have h₂ : leadingCoeff p * leadingCoeff (p ^ n) ≠ 0 := by
      rwa [pow_succ, ← leading_coeff_pow' h₁] at h
    rw [pow_succ, degree_mul' h₂, succ_nsmul, degree_pow' h₁]
#align polynomial.degree_pow' Polynomial.degree_pow'

theorem natDegree_pow' {n : ℕ} (h : leadingCoeff p ^ n ≠ 0) : natDegree (p ^ n) = n * natDegree p :=
  if hp0 : p = 0 then
    if hn0 : n = 0 then by simp [*] else by rw [hp0, zero_pow (Nat.pos_of_ne_zero hn0)] <;> simp
  else
    have hpn : p ^ n ≠ 0 := fun hpn0 => by
      have h1 := h
      rw [← leading_coeff_pow' h1, hpn0, leading_coeff_zero] at h <;> exact h rfl
    Option.some_inj.1 <|
      show (natDegree (p ^ n) : WithBot ℕ) = (n * natDegree p : ℕ) by
        rw [← degree_eq_nat_degree hpn, degree_pow' h, degree_eq_nat_degree hp0, ←
            WithBot.coe_nsmul] <;>
          simp
#align polynomial.nat_degree_pow' Polynomial.natDegree_pow'

theorem leadingCoeff_monic_mul {p q : R[X]} (hp : Monic p) :
    leadingCoeff (p * q) = leadingCoeff q :=
  by
  rcases eq_or_ne q 0 with (rfl | H)
  · simp
  · rw [leading_coeff_mul', hp.leading_coeff, one_mul]
    rwa [hp.leading_coeff, one_mul, Ne.def, leading_coeff_eq_zero]
#align polynomial.leading_coeff_monic_mul Polynomial.leadingCoeff_monic_mul

theorem leadingCoeff_mul_monic {p q : R[X]} (hq : Monic q) :
    leadingCoeff (p * q) = leadingCoeff p :=
  Decidable.byCases
    (fun H : leadingCoeff p = 0 => by
      rw [H, leading_coeff_eq_zero.1 H, zero_mul, leading_coeff_zero])
    fun H : leadingCoeff p ≠ 0 => by
    rw [leading_coeff_mul', hq.leading_coeff, mul_one] <;> rwa [hq.leading_coeff, mul_one]
#align polynomial.leading_coeff_mul_monic Polynomial.leadingCoeff_mul_monic

@[simp]
theorem leadingCoeff_mul_x_pow {p : R[X]} {n : ℕ} : leadingCoeff (p * x ^ n) = leadingCoeff p :=
  leadingCoeff_mul_monic (monic_x_pow n)
#align polynomial.leading_coeff_mul_X_pow Polynomial.leadingCoeff_mul_x_pow

@[simp]
theorem leadingCoeff_mul_x {p : R[X]} : leadingCoeff (p * x) = leadingCoeff p :=
  leadingCoeff_mul_monic monic_x
#align polynomial.leading_coeff_mul_X Polynomial.leadingCoeff_mul_x

theorem natDegree_mul_le {p q : R[X]} : natDegree (p * q) ≤ natDegree p + natDegree q :=
  by
  apply nat_degree_le_of_degree_le
  apply le_trans (degree_mul_le p q)
  rw [WithBot.coe_add]
  refine' add_le_add _ _ <;> apply degree_le_nat_degree
#align polynomial.nat_degree_mul_le Polynomial.natDegree_mul_le

theorem natDegree_pow_le {p : R[X]} {n : ℕ} : (p ^ n).natDegree ≤ n * p.natDegree :=
  by
  induction' n with i hi
  · simp
  · rw [pow_succ, Nat.succ_mul, add_comm]
    apply le_trans nat_degree_mul_le
    exact add_le_add_left hi _
#align polynomial.nat_degree_pow_le Polynomial.natDegree_pow_le

@[simp]
theorem coeff_pow_mul_natDegree (p : R[X]) (n : ℕ) :
    (p ^ n).coeff (n * p.natDegree) = p.leadingCoeff ^ n :=
  by
  induction' n with i hi
  · simp
  · rw [pow_succ', pow_succ', Nat.succ_mul]
    by_cases hp1 : p.leading_coeff ^ i = 0
    · rw [hp1, zero_mul]
      by_cases hp2 : p ^ i = 0
      · rw [hp2, zero_mul, coeff_zero]
      · apply coeff_eq_zero_of_nat_degree_lt
        have h1 : (p ^ i).natDegree < i * p.nat_degree :=
          by
          apply lt_of_le_of_ne nat_degree_pow_le fun h => hp2 _
          rw [← h, hp1] at hi
          exact leading_coeff_eq_zero.mp hi
        calc
          (p ^ i * p).natDegree ≤ (p ^ i).natDegree + p.nat_degree := nat_degree_mul_le
          _ < i * p.nat_degree + p.nat_degree := add_lt_add_right h1 _
          
    · rw [← nat_degree_pow' hp1, ← leading_coeff_pow' hp1]
      exact coeff_mul_degree_add_degree _ _
#align polynomial.coeff_pow_mul_nat_degree Polynomial.coeff_pow_mul_natDegree

theorem zero_le_degree_iff : 0 ≤ degree p ↔ p ≠ 0 := by
  rw [← not_lt, Nat.WithBot.lt_zero_iff, degree_eq_bot]
#align polynomial.zero_le_degree_iff Polynomial.zero_le_degree_iff

theorem natDegree_eq_zero_iff_degree_le_zero : p.natDegree = 0 ↔ p.degree ≤ 0 := by
  rw [← nonpos_iff_eq_zero, nat_degree_le_iff_degree_le, WithBot.coe_zero]
#align polynomial.nat_degree_eq_zero_iff_degree_le_zero Polynomial.natDegree_eq_zero_iff_degree_le_zero

theorem degree_le_iff_coeff_zero (f : R[X]) (n : WithBot ℕ) :
    degree f ≤ n ↔ ∀ m : ℕ, n < m → coeff f m = 0 := by
  simp only [degree, Finset.max, Finset.sup_le_iff, mem_support_iff, Ne.def, ← not_le, not_imp_comm]
#align polynomial.degree_le_iff_coeff_zero Polynomial.degree_le_iff_coeff_zero

theorem degree_lt_iff_coeff_zero (f : R[X]) (n : ℕ) :
    degree f < n ↔ ∀ m : ℕ, n ≤ m → coeff f m = 0 :=
  by
  refine'
    ⟨fun hf m hm => coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hf (WithBot.coe_le_coe.2 hm)), _⟩
  simp only [degree, Finset.sup_lt_iff (WithBot.bot_lt_coe n), mem_support_iff, WithBot.some_eq_coe,
    WithBot.coe_lt_coe, ← @not_le ℕ, max_eq_sup_coe]
  exact fun h m => mt (h m)
#align polynomial.degree_lt_iff_coeff_zero Polynomial.degree_lt_iff_coeff_zero

theorem degree_smul_le (a : R) (p : R[X]) : degree (a • p) ≤ degree p :=
  by
  apply (degree_le_iff_coeff_zero _ _).2 fun m hm => _
  rw [degree_lt_iff_coeff_zero] at hm
  simp [hm m le_rfl]
#align polynomial.degree_smul_le Polynomial.degree_smul_le

theorem natDegree_smul_le (a : R) (p : R[X]) : natDegree (a • p) ≤ natDegree p :=
  natDegree_le_natDegree (degree_smul_le a p)
#align polynomial.nat_degree_smul_le Polynomial.natDegree_smul_le

theorem degree_lt_degree_mul_x (hp : p ≠ 0) : p.degree < (p * x).degree :=
  haveI := nontrivial.of_polynomial_ne hp
  by
  have : leading_coeff p * leading_coeff X ≠ 0 := by simpa
  erw [degree_mul' this, degree_eq_nat_degree hp, degree_X, ← WithBot.coe_one, ← WithBot.coe_add,
      WithBot.coe_lt_coe] <;>
    exact Nat.lt_succ_self _
#align polynomial.degree_lt_degree_mul_X Polynomial.degree_lt_degree_mul_x

theorem natDegree_pos_iff_degree_pos : 0 < natDegree p ↔ 0 < degree p :=
  lt_iff_lt_of_le_iff_le natDegree_le_iff_degree_le
#align polynomial.nat_degree_pos_iff_degree_pos Polynomial.natDegree_pos_iff_degree_pos

theorem eq_c_of_natDegree_le_zero (h : natDegree p ≤ 0) : p = c (coeff p 0) :=
  eq_c_of_degree_le_zero <| degree_le_of_natDegree_le h
#align polynomial.eq_C_of_nat_degree_le_zero Polynomial.eq_c_of_natDegree_le_zero

theorem eq_c_of_natDegree_eq_zero (h : natDegree p = 0) : p = c (coeff p 0) :=
  eq_c_of_natDegree_le_zero h.le
#align polynomial.eq_C_of_nat_degree_eq_zero Polynomial.eq_c_of_natDegree_eq_zero

theorem ne_zero_of_coe_le_degree (hdeg : ↑n ≤ p.degree) : p ≠ 0 :=
  zero_le_degree_iff.mp <| (WithBot.coe_le_coe.mpr n.zero_le).trans hdeg
#align polynomial.ne_zero_of_coe_le_degree Polynomial.ne_zero_of_coe_le_degree

theorem le_natDegree_of_coe_le_degree (hdeg : ↑n ≤ p.degree) : n ≤ p.natDegree :=
  WithBot.coe_le_coe.mp ((degree_eq_natDegree <| ne_zero_of_coe_le_degree hdeg) ▸ hdeg)
#align polynomial.le_nat_degree_of_coe_le_degree Polynomial.le_natDegree_of_coe_le_degree

theorem degree_sum_fin_lt {n : ℕ} (f : Fin n → R) :
    degree (∑ i : Fin n, c (f i) * x ^ (i : ℕ)) < n :=
  (degree_sum_le _ _).trans_lt <|
    (Finset.sup_lt_iff <| WithBot.bot_lt_coe n).2 fun k hk =>
      (degree_c_mul_x_pow_le _ _).trans_lt <| WithBot.coe_lt_coe.2 k.is_lt
#align polynomial.degree_sum_fin_lt Polynomial.degree_sum_fin_lt

theorem degree_linear_le : degree (c a * x + c b) ≤ 1 :=
  degree_add_le_of_degree_le (degree_c_mul_x_le _) <| le_trans degree_c_le Nat.WithBot.coe_nonneg
#align polynomial.degree_linear_le Polynomial.degree_linear_le

theorem degree_linear_lt : degree (c a * x + c b) < 2 :=
  degree_linear_le.trans_lt <| WithBot.coe_lt_coe.mpr one_lt_two
#align polynomial.degree_linear_lt Polynomial.degree_linear_lt

theorem degree_c_lt_degree_c_mul_x (ha : a ≠ 0) : degree (c b) < degree (c a * x) := by
  simpa only [degree_C_mul_X ha] using degree_C_lt
#align polynomial.degree_C_lt_degree_C_mul_X Polynomial.degree_c_lt_degree_c_mul_x

@[simp]
theorem degree_linear (ha : a ≠ 0) : degree (c a * x + c b) = 1 := by
  rw [degree_add_eq_left_of_degree_lt <| degree_C_lt_degree_C_mul_X ha, degree_C_mul_X ha]
#align polynomial.degree_linear Polynomial.degree_linear

theorem natDegree_linear_le : natDegree (c a * x + c b) ≤ 1 :=
  natDegree_le_of_degree_le degree_linear_le
#align polynomial.nat_degree_linear_le Polynomial.natDegree_linear_le

@[simp]
theorem natDegree_linear (ha : a ≠ 0) : natDegree (c a * x + c b) = 1 :=
  natDegree_eq_of_degree_eq_some <| degree_linear ha
#align polynomial.nat_degree_linear Polynomial.natDegree_linear

@[simp]
theorem leadingCoeff_linear (ha : a ≠ 0) : leadingCoeff (c a * x + c b) = a := by
  rw [add_comm, leading_coeff_add_of_degree_lt (degree_C_lt_degree_C_mul_X ha),
    leading_coeff_C_mul_X]
#align polynomial.leading_coeff_linear Polynomial.leadingCoeff_linear

theorem degree_quadratic_le : degree (c a * x ^ 2 + c b * x + c c) ≤ 2 := by
  simpa only [add_assoc] using
    degree_add_le_of_degree_le (degree_C_mul_X_pow_le 2 a)
      (le_trans degree_linear_le <| with_bot.coe_le_coe.mpr one_le_two)
#align polynomial.degree_quadratic_le Polynomial.degree_quadratic_le

theorem degree_quadratic_lt : degree (c a * x ^ 2 + c b * x + c c) < 3 :=
  degree_quadratic_le.trans_lt <| WithBot.coe_lt_coe.mpr <| lt_add_one 2
#align polynomial.degree_quadratic_lt Polynomial.degree_quadratic_lt

theorem degree_linear_lt_degree_c_mul_x_sq (ha : a ≠ 0) :
    degree (c b * x + c c) < degree (c a * x ^ 2) := by
  simpa only [degree_C_mul_X_pow 2 ha] using degree_linear_lt
#align polynomial.degree_linear_lt_degree_C_mul_X_sq Polynomial.degree_linear_lt_degree_c_mul_x_sq

@[simp]
theorem degree_quadratic (ha : a ≠ 0) : degree (c a * x ^ 2 + c b * x + c c) = 2 :=
  by
  rw [add_assoc, degree_add_eq_left_of_degree_lt <| degree_linear_lt_degree_C_mul_X_sq ha,
    degree_C_mul_X_pow 2 ha]
  rfl
#align polynomial.degree_quadratic Polynomial.degree_quadratic

theorem natDegree_quadratic_le : natDegree (c a * x ^ 2 + c b * x + c c) ≤ 2 :=
  natDegree_le_of_degree_le degree_quadratic_le
#align polynomial.nat_degree_quadratic_le Polynomial.natDegree_quadratic_le

@[simp]
theorem natDegree_quadratic (ha : a ≠ 0) : natDegree (c a * x ^ 2 + c b * x + c c) = 2 :=
  natDegree_eq_of_degree_eq_some <| degree_quadratic ha
#align polynomial.nat_degree_quadratic Polynomial.natDegree_quadratic

@[simp]
theorem leadingCoeff_quadratic (ha : a ≠ 0) : leadingCoeff (c a * x ^ 2 + c b * x + c c) = a := by
  rw [add_assoc, add_comm, leading_coeff_add_of_degree_lt <| degree_linear_lt_degree_C_mul_X_sq ha,
    leading_coeff_C_mul_X_pow]
#align polynomial.leading_coeff_quadratic Polynomial.leadingCoeff_quadratic

theorem degree_cubic_le : degree (c a * x ^ 3 + c b * x ^ 2 + c c * x + c d) ≤ 3 := by
  simpa only [add_assoc] using
    degree_add_le_of_degree_le (degree_C_mul_X_pow_le 3 a)
      (le_trans degree_quadratic_le <| with_bot.coe_le_coe.mpr <| Nat.le_succ 2)
#align polynomial.degree_cubic_le Polynomial.degree_cubic_le

theorem degree_cubic_lt : degree (c a * x ^ 3 + c b * x ^ 2 + c c * x + c d) < 4 :=
  degree_cubic_le.trans_lt <| WithBot.coe_lt_coe.mpr <| lt_add_one 3
#align polynomial.degree_cubic_lt Polynomial.degree_cubic_lt

theorem degree_quadratic_lt_degree_c_mul_x_cb (ha : a ≠ 0) :
    degree (c b * x ^ 2 + c c * x + c d) < degree (c a * x ^ 3) := by
  simpa only [degree_C_mul_X_pow 3 ha] using degree_quadratic_lt
#align polynomial.degree_quadratic_lt_degree_C_mul_X_cb Polynomial.degree_quadratic_lt_degree_c_mul_x_cb

@[simp]
theorem degree_cubic (ha : a ≠ 0) : degree (c a * x ^ 3 + c b * x ^ 2 + c c * x + c d) = 3 :=
  by
  rw [add_assoc, add_assoc, ← add_assoc (C b * X ^ 2),
    degree_add_eq_left_of_degree_lt <| degree_quadratic_lt_degree_C_mul_X_cb ha,
    degree_C_mul_X_pow 3 ha]
  rfl
#align polynomial.degree_cubic Polynomial.degree_cubic

theorem natDegree_cubic_le : natDegree (c a * x ^ 3 + c b * x ^ 2 + c c * x + c d) ≤ 3 :=
  natDegree_le_of_degree_le degree_cubic_le
#align polynomial.nat_degree_cubic_le Polynomial.natDegree_cubic_le

@[simp]
theorem natDegree_cubic (ha : a ≠ 0) : natDegree (c a * x ^ 3 + c b * x ^ 2 + c c * x + c d) = 3 :=
  natDegree_eq_of_degree_eq_some <| degree_cubic ha
#align polynomial.nat_degree_cubic Polynomial.natDegree_cubic

@[simp]
theorem leadingCoeff_cubic (ha : a ≠ 0) :
    leadingCoeff (c a * x ^ 3 + c b * x ^ 2 + c c * x + c d) = a := by
  rw [add_assoc, add_assoc, ← add_assoc (C b * X ^ 2), add_comm,
    leading_coeff_add_of_degree_lt <| degree_quadratic_lt_degree_C_mul_X_cb ha,
    leading_coeff_C_mul_X_pow]
#align polynomial.leading_coeff_cubic Polynomial.leadingCoeff_cubic

end Semiring

section NontrivialSemiring

variable [Semiring R] [Nontrivial R] {p q : R[X]}

@[simp]
theorem degree_x_pow (n : ℕ) : degree ((x : R[X]) ^ n) = n := by
  rw [X_pow_eq_monomial, degree_monomial _ (one_ne_zero' R)]
#align polynomial.degree_X_pow Polynomial.degree_x_pow

@[simp]
theorem natDegree_x_pow (n : ℕ) : natDegree ((x : R[X]) ^ n) = n :=
  natDegree_eq_of_degree_eq_some (degree_x_pow n)
#align polynomial.nat_degree_X_pow Polynomial.natDegree_x_pow

--  This lemma explicitly does not require the `nontrivial R` assumption.
theorem natDegree_x_pow_le {R : Type _} [Semiring R] (n : ℕ) : (x ^ n : R[X]).natDegree ≤ n :=
  by
  nontriviality R
  rwa [Polynomial.natDegree_x_pow]
#align polynomial.nat_degree_X_pow_le Polynomial.natDegree_x_pow_le

theorem not_isUnit_x : ¬IsUnit (x : R[X]) := fun ⟨⟨_, g, hfg, hgf⟩, rfl⟩ =>
  zero_ne_one' R <| by
    change g * monomial 1 1 = 1 at hgf
    rw [← coeff_one_zero, ← hgf]
    simp
#align polynomial.not_is_unit_X Polynomial.not_isUnit_x

@[simp]
theorem degree_mul_x : degree (p * x) = degree p + 1 := by simp [monic_X.degree_mul]
#align polynomial.degree_mul_X Polynomial.degree_mul_x

@[simp]
theorem degree_mul_x_pow : degree (p * x ^ n) = degree p + n := by simp [(monic_X_pow n).degree_mul]
#align polynomial.degree_mul_X_pow Polynomial.degree_mul_x_pow

end NontrivialSemiring

section Ring

variable [Ring R] {p q : R[X]}

theorem degree_sub_le (p q : R[X]) : degree (p - q) ≤ max (degree p) (degree q) := by
  simpa only [degree_neg q] using degree_add_le p (-q)
#align polynomial.degree_sub_le Polynomial.degree_sub_le

theorem natDegree_sub_le (p q : R[X]) : natDegree (p - q) ≤ max (natDegree p) (natDegree q) := by
  simpa only [← nat_degree_neg q] using nat_degree_add_le p (-q)
#align polynomial.nat_degree_sub_le Polynomial.natDegree_sub_le

theorem degree_sub_lt (hd : degree p = degree q) (hp0 : p ≠ 0)
    (hlc : leadingCoeff p = leadingCoeff q) : degree (p - q) < degree p :=
  have hp : monomial (natDegree p) (leadingCoeff p) + p.eraseₓ (natDegree p) = p :=
    monomial_add_erase _ _
  have hq : monomial (natDegree q) (leadingCoeff q) + q.eraseₓ (natDegree q) = q :=
    monomial_add_erase _ _
  have hd' : natDegree p = natDegree q := by unfold nat_degree <;> rw [hd]
  have hq0 : q ≠ 0 := mt degree_eq_bot.2 (hd ▸ mt degree_eq_bot.1 hp0)
  calc
    degree (p - q) = degree (erase (natDegree q) p + -erase (natDegree q) q) := by
      conv =>
        lhs
        rw [← hp, ← hq, hlc, hd', add_sub_add_left_eq_sub, sub_eq_add_neg]
    _ ≤ max (degree (erase (natDegree q) p)) (degree (erase (natDegree q) q)) :=
      (degree_neg (erase (natDegree q) q) ▸ degree_add_le _ _)
    _ < degree p := max_lt_iff.2 ⟨hd' ▸ degree_erase_lt hp0, hd.symm ▸ degree_erase_lt hq0⟩
    
#align polynomial.degree_sub_lt Polynomial.degree_sub_lt

theorem degree_x_sub_c_le (r : R) : (x - c r).degree ≤ 1 :=
  (degree_sub_le _ _).trans (max_le degree_x_le (degree_c_le.trans zero_le_one))
#align polynomial.degree_X_sub_C_le Polynomial.degree_x_sub_c_le

theorem natDegree_x_sub_c_le (r : R) : (x - c r).natDegree ≤ 1 :=
  natDegree_le_iff_degree_le.2 <| degree_x_sub_c_le r
#align polynomial.nat_degree_X_sub_C_le Polynomial.natDegree_x_sub_c_le

theorem degree_sub_eq_left_of_degree_lt (h : degree q < degree p) : degree (p - q) = degree p :=
  by
  rw [← degree_neg q] at h
  rw [sub_eq_add_neg, degree_add_eq_left_of_degree_lt h]
#align polynomial.degree_sub_eq_left_of_degree_lt Polynomial.degree_sub_eq_left_of_degree_lt

theorem degree_sub_eq_right_of_degree_lt (h : degree p < degree q) : degree (p - q) = degree q :=
  by
  rw [← degree_neg q] at h
  rw [sub_eq_add_neg, degree_add_eq_right_of_degree_lt h, degree_neg]
#align polynomial.degree_sub_eq_right_of_degree_lt Polynomial.degree_sub_eq_right_of_degree_lt

theorem natDegree_sub_eq_left_of_natDegree_lt (h : natDegree q < natDegree p) :
    natDegree (p - q) = natDegree p :=
  natDegree_eq_of_degree_eq (degree_sub_eq_left_of_degree_lt (degree_lt_degree h))
#align polynomial.nat_degree_sub_eq_left_of_nat_degree_lt Polynomial.natDegree_sub_eq_left_of_natDegree_lt

theorem natDegree_sub_eq_right_of_natDegree_lt (h : natDegree p < natDegree q) :
    natDegree (p - q) = natDegree q :=
  natDegree_eq_of_degree_eq (degree_sub_eq_right_of_degree_lt (degree_lt_degree h))
#align polynomial.nat_degree_sub_eq_right_of_nat_degree_lt Polynomial.natDegree_sub_eq_right_of_natDegree_lt

end Ring

section NonzeroRing

variable [Nontrivial R]

section Semiring

variable [Semiring R]

@[simp]
theorem degree_x_add_c (a : R) : degree (x + c a) = 1 :=
  by
  have : degree (c a) < degree (x : R[X]) :=
    calc
      degree (c a) ≤ 0 := degree_c_le
      _ < 1 := (WithBot.some_lt_some.mpr zero_lt_one)
      _ = degree x := degree_x.symm
      
  rw [degree_add_eq_left_of_degree_lt this, degree_X]
#align polynomial.degree_X_add_C Polynomial.degree_x_add_c

@[simp]
theorem natDegree_x_add_c (x : R) : (x + c x).natDegree = 1 :=
  natDegree_eq_of_degree_eq_some <| degree_x_add_c x
#align polynomial.nat_degree_X_add_C Polynomial.natDegree_x_add_c

@[simp]
theorem nextCoeff_x_add_c [Semiring S] (c : S) : nextCoeff (x + c c) = c :=
  by
  nontriviality S
  simp [next_coeff_of_pos_nat_degree]
#align polynomial.next_coeff_X_add_C Polynomial.nextCoeff_x_add_c

theorem degree_x_pow_add_c {n : ℕ} (hn : 0 < n) (a : R) : degree ((x : R[X]) ^ n + c a) = n :=
  by
  have : degree (c a) < degree ((x : R[X]) ^ n) :=
    degree_c_le.trans_lt <| by rwa [degree_X_pow, WithBot.coe_pos]
  rw [degree_add_eq_left_of_degree_lt this, degree_X_pow]
#align polynomial.degree_X_pow_add_C Polynomial.degree_x_pow_add_c

theorem x_pow_add_c_ne_zero {n : ℕ} (hn : 0 < n) (a : R) : (x : R[X]) ^ n + c a ≠ 0 :=
  mt degree_eq_bot.2
    (show degree ((x : R[X]) ^ n + c a) ≠ ⊥ by rw [degree_X_pow_add_C hn a] <;> exact by decide)
#align polynomial.X_pow_add_C_ne_zero Polynomial.x_pow_add_c_ne_zero

theorem x_add_c_ne_zero (r : R) : x + c r ≠ 0 :=
  pow_one (x : R[X]) ▸ x_pow_add_c_ne_zero zero_lt_one r
#align polynomial.X_add_C_ne_zero Polynomial.x_add_c_ne_zero

theorem zero_nmem_multiset_map_x_add_c {α : Type _} (m : Multiset α) (f : α → R) :
    (0 : R[X]) ∉ m.map fun a => x + c (f a) := fun mem =>
  let ⟨a, _, ha⟩ := Multiset.mem_map.mp mem
  x_add_c_ne_zero _ ha
#align polynomial.zero_nmem_multiset_map_X_add_C Polynomial.zero_nmem_multiset_map_x_add_c

theorem natDegree_x_pow_add_c {n : ℕ} {r : R} : (x ^ n + c r).natDegree = n :=
  by
  by_cases hn : n = 0
  · rw [hn, pow_zero, ← C_1, ← RingHom.map_add, nat_degree_C]
  · exact nat_degree_eq_of_degree_eq_some (degree_X_pow_add_C (pos_iff_ne_zero.mpr hn) r)
#align polynomial.nat_degree_X_pow_add_C Polynomial.natDegree_x_pow_add_c

theorem x_pow_add_c_ne_one {n : ℕ} (hn : 0 < n) (a : R) : (x : R[X]) ^ n + c a ≠ 1 := fun h =>
  hn.ne' <| by simpa only [nat_degree_X_pow_add_C, nat_degree_one] using congr_arg nat_degree h
#align polynomial.X_pow_add_C_ne_one Polynomial.x_pow_add_c_ne_one

theorem x_add_c_ne_one (r : R) : x + c r ≠ 1 :=
  pow_one (x : R[X]) ▸ x_pow_add_c_ne_one zero_lt_one r
#align polynomial.X_add_C_ne_one Polynomial.x_add_c_ne_one

end Semiring

end NonzeroRing

section Semiring

variable [Semiring R]

@[simp]
theorem leadingCoeff_x_pow_add_c {n : ℕ} (hn : 0 < n) {r : R} : (x ^ n + c r).leadingCoeff = 1 :=
  by
  nontriviality R
  rw [leading_coeff, nat_degree_X_pow_add_C, coeff_add, coeff_X_pow_self, coeff_C,
    if_neg (pos_iff_ne_zero.mp hn), add_zero]
#align polynomial.leading_coeff_X_pow_add_C Polynomial.leadingCoeff_x_pow_add_c

@[simp]
theorem leadingCoeff_x_add_c [Semiring S] (r : S) : (x + c r).leadingCoeff = 1 := by
  rw [← pow_one (X : S[X]), leading_coeff_X_pow_add_C zero_lt_one]
#align polynomial.leading_coeff_X_add_C Polynomial.leadingCoeff_x_add_c

@[simp]
theorem leadingCoeff_x_pow_add_one {n : ℕ} (hn : 0 < n) : (x ^ n + 1 : R[X]).leadingCoeff = 1 :=
  leadingCoeff_x_pow_add_c hn
#align polynomial.leading_coeff_X_pow_add_one Polynomial.leadingCoeff_x_pow_add_one

@[simp]
theorem leadingCoeff_pow_x_add_c (r : R) (i : ℕ) : leadingCoeff ((x + c r) ^ i) = 1 :=
  by
  nontriviality
  rw [leading_coeff_pow'] <;> simp
#align polynomial.leading_coeff_pow_X_add_C Polynomial.leadingCoeff_pow_x_add_c

end Semiring

section Ring

variable [Ring R]

@[simp]
theorem leadingCoeff_x_pow_sub_c {n : ℕ} (hn : 0 < n) {r : R} : (x ^ n - c r).leadingCoeff = 1 := by
  rw [sub_eq_add_neg, ← map_neg C r, leading_coeff_X_pow_add_C hn] <;> infer_instance
#align polynomial.leading_coeff_X_pow_sub_C Polynomial.leadingCoeff_x_pow_sub_c

@[simp]
theorem leadingCoeff_x_pow_sub_one {n : ℕ} (hn : 0 < n) : (x ^ n - 1 : R[X]).leadingCoeff = 1 :=
  leadingCoeff_x_pow_sub_c hn
#align polynomial.leading_coeff_X_pow_sub_one Polynomial.leadingCoeff_x_pow_sub_one

variable [Nontrivial R]

@[simp]
theorem degree_x_sub_c (a : R) : degree (x - c a) = 1 := by
  rw [sub_eq_add_neg, ← map_neg C a, degree_X_add_C]
#align polynomial.degree_X_sub_C Polynomial.degree_x_sub_c

@[simp]
theorem natDegree_x_sub_c (x : R) : (x - c x).natDegree = 1 :=
  natDegree_eq_of_degree_eq_some <| degree_x_sub_c x
#align polynomial.nat_degree_X_sub_C Polynomial.natDegree_x_sub_c

@[simp]
theorem nextCoeff_x_sub_c [Ring S] (c : S) : nextCoeff (x - c c) = -c := by
  rw [sub_eq_add_neg, ← map_neg C c, next_coeff_X_add_C]
#align polynomial.next_coeff_X_sub_C Polynomial.nextCoeff_x_sub_c

theorem degree_x_pow_sub_c {n : ℕ} (hn : 0 < n) (a : R) : degree ((x : R[X]) ^ n - c a) = n := by
  rw [sub_eq_add_neg, ← map_neg C a, degree_X_pow_add_C hn] <;> infer_instance
#align polynomial.degree_X_pow_sub_C Polynomial.degree_x_pow_sub_c

theorem x_pow_sub_c_ne_zero {n : ℕ} (hn : 0 < n) (a : R) : (x : R[X]) ^ n - c a ≠ 0 :=
  by
  rw [sub_eq_add_neg, ← map_neg C a]
  exact X_pow_add_C_ne_zero hn _
#align polynomial.X_pow_sub_C_ne_zero Polynomial.x_pow_sub_c_ne_zero

theorem x_sub_c_ne_zero (r : R) : x - c r ≠ 0 :=
  pow_one (x : R[X]) ▸ x_pow_sub_c_ne_zero zero_lt_one r
#align polynomial.X_sub_C_ne_zero Polynomial.x_sub_c_ne_zero

theorem zero_nmem_multiset_map_x_sub_c {α : Type _} (m : Multiset α) (f : α → R) :
    (0 : R[X]) ∉ m.map fun a => x - c (f a) := fun mem =>
  let ⟨a, _, ha⟩ := Multiset.mem_map.mp mem
  x_sub_c_ne_zero _ ha
#align polynomial.zero_nmem_multiset_map_X_sub_C Polynomial.zero_nmem_multiset_map_x_sub_c

theorem natDegree_x_pow_sub_c {n : ℕ} {r : R} : (x ^ n - c r).natDegree = n := by
  rw [sub_eq_add_neg, ← map_neg C r, nat_degree_X_pow_add_C]
#align polynomial.nat_degree_X_pow_sub_C Polynomial.natDegree_x_pow_sub_c

@[simp]
theorem leadingCoeff_x_sub_c [Ring S] (r : S) : (x - c r).leadingCoeff = 1 := by
  rw [sub_eq_add_neg, ← map_neg C r, leading_coeff_X_add_C]
#align polynomial.leading_coeff_X_sub_C Polynomial.leadingCoeff_x_sub_c

end Ring

section NoZeroDivisors

variable [Semiring R] [NoZeroDivisors R] {p q : R[X]}

@[simp]
theorem degree_mul : degree (p * q) = degree p + degree q :=
  if hp0 : p = 0 then by simp only [hp0, degree_zero, zero_mul, WithBot.bot_add]
  else
    if hq0 : q = 0 then by simp only [hq0, degree_zero, mul_zero, WithBot.add_bot]
    else degree_mul' <| mul_ne_zero (mt leadingCoeff_eq_zero.1 hp0) (mt leadingCoeff_eq_zero.1 hq0)
#align polynomial.degree_mul Polynomial.degree_mul

/-- `degree` as a monoid homomorphism between `R[X]` and `multiplicative (with_bot ℕ)`.
  This is useful to prove results about multiplication and degree. -/
def degreeMonoidHom [Nontrivial R] : R[X] →* Multiplicative (WithBot ℕ)
    where
  toFun := degree
  map_one' := degree_one
  map_mul' _ _ := degree_mul
#align polynomial.degree_monoid_hom Polynomial.degreeMonoidHom

@[simp]
theorem degree_pow [Nontrivial R] (p : R[X]) (n : ℕ) : degree (p ^ n) = n • degree p :=
  map_pow (@degreeMonoidHom R _ _ _) _ _
#align polynomial.degree_pow Polynomial.degree_pow

@[simp]
theorem leadingCoeff_mul (p q : R[X]) : leadingCoeff (p * q) = leadingCoeff p * leadingCoeff q :=
  by
  by_cases hp : p = 0
  · simp only [hp, zero_mul, leading_coeff_zero]
  · by_cases hq : q = 0
    · simp only [hq, mul_zero, leading_coeff_zero]
    · rw [leading_coeff_mul']
      exact mul_ne_zero (mt leading_coeff_eq_zero.1 hp) (mt leading_coeff_eq_zero.1 hq)
#align polynomial.leading_coeff_mul Polynomial.leadingCoeff_mul

/-- `polynomial.leading_coeff` bundled as a `monoid_hom` when `R` has `no_zero_divisors`, and thus
  `leading_coeff` is multiplicative -/
def leadingCoeffHom : R[X] →* R where
  toFun := leadingCoeff
  map_one' := by simp
  map_mul' := leadingCoeff_mul
#align polynomial.leading_coeff_hom Polynomial.leadingCoeffHom

@[simp]
theorem leadingCoeffHom_apply (p : R[X]) : leadingCoeffHom p = leadingCoeff p :=
  rfl
#align polynomial.leading_coeff_hom_apply Polynomial.leadingCoeffHom_apply

@[simp]
theorem leadingCoeff_pow (p : R[X]) (n : ℕ) : leadingCoeff (p ^ n) = leadingCoeff p ^ n :=
  (leadingCoeffHom : R[X] →* R).map_pow p n
#align polynomial.leading_coeff_pow Polynomial.leadingCoeff_pow

end NoZeroDivisors

end Polynomial

