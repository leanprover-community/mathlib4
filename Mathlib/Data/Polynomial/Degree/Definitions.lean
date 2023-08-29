/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.MonoidAlgebra.Degree
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.WithBot
import Mathlib.Data.Polynomial.Monomial
import Mathlib.Data.Polynomial.Coeff
import Mathlib.Data.Nat.Cast.WithTop

#align_import data.polynomial.degree.definitions from "leanprover-community/mathlib"@"808ea4ebfabeb599f21ec4ae87d6dc969597887f"


/-!
# Theory of univariate polynomials

The definitions include
`degree`, `Monic`, `leadingCoeff`

Results include
- `degree_mul` : The degree of the product is the sum of degrees
- `leadingCoeff_add_of_degree_eq` and `leadingCoeff_add_of_degree_lt` :
    The leading_coefficient of a sum is determined by the leading coefficients and degrees
-/

set_option autoImplicit true

-- Porting note: `Mathlib.Data.Nat.Cast.WithTop` should be imported for `Nat.cast_withBot`.

set_option linter.uppercaseLean3 false

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
  InvImage.wf degree (WithBot.wellFounded_lt Nat.lt_wfRel.wf)
#align polynomial.degree_lt_wf Polynomial.degree_lt_wf

instance : WellFoundedRelation R[X] :=
  ⟨_, degree_lt_wf⟩

/-- `natDegree p` forces `degree p` to ℕ, by defining `natDegree 0 = 0`. -/
def natDegree (p : R[X]) : ℕ :=
  (degree p).unbot' 0
#align polynomial.nat_degree Polynomial.natDegree

/-- `leadingCoeff p` gives the coefficient of the highest power of `X` in `p`-/
def leadingCoeff (p : R[X]) : R :=
  coeff p (natDegree p)
#align polynomial.leading_coeff Polynomial.leadingCoeff

/-- a polynomial is `Monic` if its leading coefficient is 1 -/
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

instance Monic.decidable [DecidableEq R] : Decidable (Monic p) := by unfold Monic; infer_instance
                                                                     -- ⊢ Decidable (leadingCoeff p = 1)
                                                                                   -- 🎉 no goals
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

@[simp]
theorem degree_eq_bot : degree p = ⊥ ↔ p = 0 :=
  ⟨fun h => support_eq_empty.1 (Finset.max_eq_bot.1 h), fun h => h.symm ▸ rfl⟩
#align polynomial.degree_eq_bot Polynomial.degree_eq_bot

@[nontriviality]
theorem degree_of_subsingleton [Subsingleton R] : degree p = ⊥ := by
  rw [Subsingleton.elim p 0, degree_zero]
  -- 🎉 no goals
#align polynomial.degree_of_subsingleton Polynomial.degree_of_subsingleton

@[nontriviality]
theorem natDegree_of_subsingleton [Subsingleton R] : natDegree p = 0 := by
  rw [Subsingleton.elim p 0, natDegree_zero]
  -- 🎉 no goals
#align polynomial.nat_degree_of_subsingleton Polynomial.natDegree_of_subsingleton

theorem degree_eq_natDegree (hp : p ≠ 0) : degree p = (natDegree p : WithBot ℕ) := by
  let ⟨n, hn⟩ := not_forall.1 (mt Option.eq_none_iff_forall_not_mem.2 (mt degree_eq_bot.1 hp))
  -- ⊢ degree p = ↑(natDegree p)
  have hn : degree p = some n := Classical.not_not.1 hn
  -- ⊢ degree p = ↑(natDegree p)
  rw [natDegree, hn]; rfl
  -- ⊢ Option.some n = ↑(WithBot.unbot' 0 (Option.some n))
                      -- 🎉 no goals
#align polynomial.degree_eq_nat_degree Polynomial.degree_eq_natDegree

theorem degree_eq_iff_natDegree_eq {p : R[X]} {n : ℕ} (hp : p ≠ 0) :
    p.degree = n ↔ p.natDegree = n := by rw [degree_eq_natDegree hp]; exact WithBot.coe_eq_coe
                                         -- ⊢ ↑(natDegree p) = ↑n ↔ natDegree p = n
                                                                      -- 🎉 no goals
#align polynomial.degree_eq_iff_nat_degree_eq Polynomial.degree_eq_iff_natDegree_eq

theorem degree_eq_iff_natDegree_eq_of_pos {p : R[X]} {n : ℕ} (hn : 0 < n) :
    p.degree = n ↔ p.natDegree = n := by
  constructor
  -- ⊢ degree p = ↑n → natDegree p = n
  · intro H
    -- ⊢ natDegree p = n
    rwa [← degree_eq_iff_natDegree_eq]
    -- ⊢ p ≠ 0
    rintro rfl
    -- ⊢ False
    rw [degree_zero] at H
    -- ⊢ False
    exact Option.noConfusion H
    -- 🎉 no goals
  · intro H
    -- ⊢ degree p = ↑n
    rwa [degree_eq_iff_natDegree_eq]
    -- ⊢ p ≠ 0
    rintro rfl
    -- ⊢ False
    rw [natDegree_zero] at H
    -- ⊢ False
    rw [H] at hn
    -- ⊢ False
    exact lt_irrefl _ hn
    -- 🎉 no goals
#align polynomial.degree_eq_iff_nat_degree_eq_of_pos Polynomial.degree_eq_iff_natDegree_eq_of_pos

theorem natDegree_eq_of_degree_eq_some {p : R[X]} {n : ℕ} (h : degree p = n) : natDegree p = n := by
  -- Porting note: `Nat.cast_withBot` is required.
  rw [natDegree, h, Nat.cast_withBot, WithBot.unbot'_coe]
  -- 🎉 no goals
#align polynomial.nat_degree_eq_of_degree_eq_some Polynomial.natDegree_eq_of_degree_eq_some

theorem degree_ne_of_natDegree_ne {n : ℕ} : p.natDegree ≠ n → degree p ≠ n :=
  mt natDegree_eq_of_degree_eq_some
#align polynomial.degree_ne_of_nat_degree_ne Polynomial.degree_ne_of_natDegree_ne

@[simp]
theorem degree_le_natDegree : degree p ≤ natDegree p :=
  WithBot.giUnbot'Bot.gc.le_u_l _
#align polynomial.degree_le_nat_degree Polynomial.degree_le_natDegree

theorem natDegree_eq_of_degree_eq [Semiring S] {q : S[X]} (h : degree p = degree q) :
    natDegree p = natDegree q := by unfold natDegree; rw [h]
                                    -- ⊢ WithBot.unbot' 0 (degree p) = WithBot.unbot' 0 (degree q)
                                                      -- 🎉 no goals
#align polynomial.nat_degree_eq_of_degree_eq Polynomial.natDegree_eq_of_degree_eq

theorem le_degree_of_ne_zero (h : coeff p n ≠ 0) : (n : WithBot ℕ) ≤ degree p :=
  show @LE.le (WithBot ℕ) _ (some n : WithBot ℕ) (p.support.sup some : WithBot ℕ) from
    Finset.le_sup (mem_support_iff.2 h)
#align polynomial.le_degree_of_ne_zero Polynomial.le_degree_of_ne_zero

theorem le_natDegree_of_ne_zero (h : coeff p n ≠ 0) : n ≤ natDegree p := by
  rw [← Nat.cast_le (α := WithBot ℕ), ← degree_eq_natDegree]
  -- ⊢ ↑n ≤ degree p
  exact le_degree_of_ne_zero h
  -- ⊢ p ≠ 0
  · rintro rfl
    -- ⊢ False
    exact h rfl
    -- 🎉 no goals
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

theorem supp_subset_range (h : natDegree p < m) : p.support ⊆ Finset.range m := fun _n hn =>
  mem_range.2 <| (le_natDegree_of_mem_supp _ hn).trans_lt h
#align polynomial.supp_subset_range Polynomial.supp_subset_range

theorem supp_subset_range_natDegree_succ : p.support ⊆ Finset.range (natDegree p + 1) :=
  supp_subset_range (Nat.lt_succ_self _)
#align polynomial.supp_subset_range_nat_degree_succ Polynomial.supp_subset_range_natDegree_succ

theorem degree_le_degree (h : coeff q (natDegree p) ≠ 0) : degree p ≤ degree q := by
  by_cases hp : p = 0
  -- ⊢ degree p ≤ degree q
  · rw [hp]
    -- ⊢ degree 0 ≤ degree q
    exact bot_le
    -- 🎉 no goals
  · rw [degree_eq_natDegree hp]
    -- ⊢ ↑(natDegree p) ≤ degree q
    exact le_degree_of_ne_zero h
    -- 🎉 no goals
#align polynomial.degree_le_degree Polynomial.degree_le_degree

theorem natDegree_le_iff_degree_le {n : ℕ} : natDegree p ≤ n ↔ degree p ≤ n :=
  WithBot.unbot'_bot_le_iff
#align polynomial.nat_degree_le_iff_degree_le Polynomial.natDegree_le_iff_degree_le

theorem natDegree_lt_iff_degree_lt (hp : p ≠ 0) : p.natDegree < n ↔ p.degree < ↑n :=
  WithBot.unbot'_lt_iff <| degree_eq_bot.not.mpr hp
#align polynomial.nat_degree_lt_iff_degree_lt Polynomial.natDegree_lt_iff_degree_lt

alias ⟨degree_le_of_natDegree_le, natDegree_le_of_degree_le⟩ := natDegree_le_iff_degree_le
#align polynomial.degree_le_of_nat_degree_le Polynomial.degree_le_of_natDegree_le
#align polynomial.nat_degree_le_of_degree_le Polynomial.natDegree_le_of_degree_le

theorem natDegree_le_natDegree [Semiring S] {q : S[X]} (hpq : p.degree ≤ q.degree) :
    p.natDegree ≤ q.natDegree :=
  WithBot.giUnbot'Bot.gc.monotone_l hpq
#align polynomial.nat_degree_le_nat_degree Polynomial.natDegree_le_natDegree

theorem natDegree_lt_natDegree {p q : R[X]} (hp : p ≠ 0) (hpq : p.degree < q.degree) :
    p.natDegree < q.natDegree := by
  by_cases hq : q = 0
  -- ⊢ natDegree p < natDegree q
  · exact (not_lt_bot <| hq ▸ hpq).elim
    -- 🎉 no goals
  -- Porting note: `Nat.cast_withBot` is required.
  rwa [degree_eq_natDegree hp, degree_eq_natDegree hq, Nat.cast_lt] at hpq
  -- 🎉 no goals
#align polynomial.nat_degree_lt_nat_degree Polynomial.natDegree_lt_natDegree

@[simp]
theorem degree_C (ha : a ≠ 0) : degree (C a) = (0 : WithBot ℕ) := by
  rw [degree, ← monomial_zero_left, support_monomial 0 ha, max_eq_sup_coe, sup_singleton,
    WithBot.coe_zero]
#align polynomial.degree_C Polynomial.degree_C

theorem degree_C_le : degree (C a) ≤ 0 := by
  by_cases h : a = 0
  -- ⊢ degree (↑C a) ≤ 0
  · rw [h, C_0]
    -- ⊢ degree 0 ≤ 0
    exact bot_le
    -- 🎉 no goals
  · rw [degree_C h]
    -- 🎉 no goals
#align polynomial.degree_C_le Polynomial.degree_C_le

theorem degree_C_lt : degree (C a) < 1 :=
  degree_C_le.trans_lt <| WithBot.coe_lt_coe.mpr zero_lt_one
#align polynomial.degree_C_lt Polynomial.degree_C_lt

theorem degree_one_le : degree (1 : R[X]) ≤ (0 : WithBot ℕ) := by rw [← C_1]; exact degree_C_le
                                                                  -- ⊢ degree (↑C 1) ≤ 0
                                                                              -- 🎉 no goals
#align polynomial.degree_one_le Polynomial.degree_one_le

@[simp]
theorem natDegree_C (a : R) : natDegree (C a) = 0 := by
  by_cases ha : a = 0
  -- ⊢ natDegree (↑C a) = 0
  · have : C a = 0 := by rw [ha, C_0]
    -- ⊢ natDegree (↑C a) = 0
    rw [natDegree, degree_eq_bot.2 this]
    -- ⊢ WithBot.unbot' 0 ⊥ = 0
    rfl
    -- 🎉 no goals
  · rw [natDegree, degree_C ha]
    -- ⊢ WithBot.unbot' 0 0 = 0
    rfl
    -- 🎉 no goals
#align polynomial.nat_degree_C Polynomial.natDegree_C

@[simp]
theorem natDegree_one : natDegree (1 : R[X]) = 0 :=
  natDegree_C 1
#align polynomial.nat_degree_one Polynomial.natDegree_one

@[simp]
theorem natDegree_nat_cast (n : ℕ) : natDegree (n : R[X]) = 0 := by
  simp only [← C_eq_nat_cast, natDegree_C]
  -- 🎉 no goals
#align polynomial.nat_degree_nat_cast Polynomial.natDegree_nat_cast

theorem degree_nat_cast_le (n : ℕ) : degree (n : R[X]) ≤ 0 := degree_le_of_natDegree_le (by simp)
                                                                                            -- 🎉 no goals

@[simp]
theorem degree_monomial (n : ℕ) (ha : a ≠ 0) : degree (monomial n a) = n := by
  rw [degree, support_monomial n ha]; rfl
  -- ⊢ Finset.max {n} = ↑n
                                      -- 🎉 no goals
#align polynomial.degree_monomial Polynomial.degree_monomial

@[simp]
theorem degree_C_mul_X_pow (n : ℕ) (ha : a ≠ 0) : degree (C a * X ^ n) = n := by
  rw [C_mul_X_pow_eq_monomial, degree_monomial n ha]
  -- 🎉 no goals
#align polynomial.degree_C_mul_X_pow Polynomial.degree_C_mul_X_pow

theorem degree_C_mul_X (ha : a ≠ 0) : degree (C a * X) = 1 := by
  simpa only [pow_one] using degree_C_mul_X_pow 1 ha
  -- 🎉 no goals
#align polynomial.degree_C_mul_X Polynomial.degree_C_mul_X

theorem degree_monomial_le (n : ℕ) (a : R) : degree (monomial n a) ≤ n :=
  if h : a = 0 then by rw [h, (monomial n).map_zero]; exact bot_le
                       -- ⊢ degree 0 ≤ ↑n
                                                      -- 🎉 no goals
  else le_of_eq (degree_monomial n h)
#align polynomial.degree_monomial_le Polynomial.degree_monomial_le

theorem degree_C_mul_X_pow_le (n : ℕ) (a : R) : degree (C a * X ^ n) ≤ n := by
  rw [C_mul_X_pow_eq_monomial]
  -- ⊢ degree (↑(monomial n) a) ≤ ↑n
  apply degree_monomial_le
  -- 🎉 no goals
#align polynomial.degree_C_mul_X_pow_le Polynomial.degree_C_mul_X_pow_le

theorem degree_C_mul_X_le (a : R) : degree (C a * X) ≤ 1 := by
  simpa only [pow_one] using degree_C_mul_X_pow_le 1 a
  -- 🎉 no goals
#align polynomial.degree_C_mul_X_le Polynomial.degree_C_mul_X_le

@[simp]
theorem natDegree_C_mul_X_pow (n : ℕ) (a : R) (ha : a ≠ 0) : natDegree (C a * X ^ n) = n :=
  natDegree_eq_of_degree_eq_some (degree_C_mul_X_pow n ha)
#align polynomial.nat_degree_C_mul_X_pow Polynomial.natDegree_C_mul_X_pow

@[simp]
theorem natDegree_C_mul_X (a : R) (ha : a ≠ 0) : natDegree (C a * X) = 1 := by
  simpa only [pow_one] using natDegree_C_mul_X_pow 1 a ha
  -- 🎉 no goals
#align polynomial.nat_degree_C_mul_X Polynomial.natDegree_C_mul_X

@[simp]
theorem natDegree_monomial [DecidableEq R] (i : ℕ) (r : R) :
    natDegree (monomial i r) = if r = 0 then 0 else i := by
  split_ifs with hr
  -- ⊢ natDegree (↑(monomial i) r) = 0
  · simp [hr]
    -- 🎉 no goals
  · rw [← C_mul_X_pow_eq_monomial, natDegree_C_mul_X_pow i r hr]
    -- 🎉 no goals
#align polynomial.nat_degree_monomial Polynomial.natDegree_monomial

theorem natDegree_monomial_le (a : R) {m : ℕ} : (monomial m a).natDegree ≤ m := by
  rw [Polynomial.natDegree_monomial]
  -- ⊢ (if a = 0 then 0 else m) ≤ m
  split_ifs
  -- ⊢ 0 ≤ m
  exacts [Nat.zero_le _, rfl.le]
  -- 🎉 no goals
#align polynomial.nat_degree_monomial_le Polynomial.natDegree_monomial_le

theorem natDegree_monomial_eq (i : ℕ) {r : R} (r0 : r ≠ 0) : (monomial i r).natDegree = i :=
  Eq.trans (natDegree_monomial _ _) (if_neg r0)
#align polynomial.nat_degree_monomial_eq Polynomial.natDegree_monomial_eq

theorem coeff_eq_zero_of_degree_lt (h : degree p < n) : coeff p n = 0 :=
  Classical.not_not.1 (mt le_degree_of_ne_zero (not_le_of_gt h))
#align polynomial.coeff_eq_zero_of_degree_lt Polynomial.coeff_eq_zero_of_degree_lt

theorem coeff_eq_zero_of_natDegree_lt {p : R[X]} {n : ℕ} (h : p.natDegree < n) :
    p.coeff n = 0 := by
  apply coeff_eq_zero_of_degree_lt
  -- ⊢ degree p < ↑n
  by_cases hp : p = 0
  -- ⊢ degree p < ↑n
  · subst hp
    -- ⊢ degree 0 < ↑n
    exact WithBot.bot_lt_coe n
    -- 🎉 no goals
  · rwa [degree_eq_natDegree hp, Nat.cast_lt]
    -- 🎉 no goals
#align polynomial.coeff_eq_zero_of_nat_degree_lt Polynomial.coeff_eq_zero_of_natDegree_lt

theorem ext_iff_natDegree_le {p q : R[X]} {n : ℕ} (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) :
    p = q ↔ ∀ i ≤ n, p.coeff i = q.coeff i := by
  refine' Iff.trans Polynomial.ext_iff _
  -- ⊢ (∀ (n : ℕ), coeff p n = coeff q n) ↔ ∀ (i : ℕ), i ≤ n → coeff p i = coeff q i
  refine' forall_congr' fun i => ⟨fun h _ => h, fun h => _⟩
  -- ⊢ coeff p i = coeff q i
  refine' (le_or_lt i n).elim h fun k => _
  -- ⊢ coeff p i = coeff q i
  exact
    (coeff_eq_zero_of_natDegree_lt (hp.trans_lt k)).trans
      (coeff_eq_zero_of_natDegree_lt (hq.trans_lt k)).symm
#align polynomial.ext_iff_nat_degree_le Polynomial.ext_iff_natDegree_le

theorem ext_iff_degree_le {p q : R[X]} {n : ℕ} (hp : p.degree ≤ n) (hq : q.degree ≤ n) :
    p = q ↔ ∀ i ≤ n, p.coeff i = q.coeff i :=
  ext_iff_natDegree_le (natDegree_le_of_degree_le hp) (natDegree_le_of_degree_le hq)
#align polynomial.ext_iff_degree_le Polynomial.ext_iff_degree_le

@[simp]
theorem coeff_natDegree_succ_eq_zero {p : R[X]} : p.coeff (p.natDegree + 1) = 0 :=
  coeff_eq_zero_of_natDegree_lt (lt_add_one _)
#align polynomial.coeff_nat_degree_succ_eq_zero Polynomial.coeff_natDegree_succ_eq_zero

-- We need the explicit `Decidable` argument here because an exotic one shows up in a moment!
theorem ite_le_natDegree_coeff (p : R[X]) (n : ℕ) (I : Decidable (n < 1 + natDegree p)) :
    @ite _ (n < 1 + natDegree p) I (coeff p n) 0 = coeff p n := by
  split_ifs with h
  -- ⊢ coeff p n = coeff p n
  · rfl
    -- 🎉 no goals
  · exact (coeff_eq_zero_of_natDegree_lt (not_le.1 fun w => h (Nat.lt_one_add_iff.2 w))).symm
    -- 🎉 no goals
#align polynomial.ite_le_nat_degree_coeff Polynomial.ite_le_natDegree_coeff

theorem as_sum_support (p : R[X]) : p = ∑ i in p.support, monomial i (p.coeff i) :=
  (sum_monomial_eq p).symm
#align polynomial.as_sum_support Polynomial.as_sum_support

theorem as_sum_support_C_mul_X_pow (p : R[X]) : p = ∑ i in p.support, C (p.coeff i) * X ^ i :=
  _root_.trans p.as_sum_support <| by simp only [C_mul_X_pow_eq_monomial]
                                      -- 🎉 no goals
#align polynomial.as_sum_support_C_mul_X_pow Polynomial.as_sum_support_C_mul_X_pow

/-- We can reexpress a sum over `p.support` as a sum over `range n`,
for any `n` satisfying `p.natDegree < n`.
-/
theorem sum_over_range' [AddCommMonoid S] (p : R[X]) {f : ℕ → R → S} (h : ∀ n, f n 0 = 0) (n : ℕ)
    (w : p.natDegree < n) : p.sum f = ∑ a : ℕ in range n, f a (coeff p a) := by
  rcases p with ⟨⟩
  -- ⊢ sum { toFinsupp := toFinsupp✝ } f = ∑ a in range n, f a (coeff { toFinsupp : …
  have := supp_subset_range w
  -- ⊢ sum { toFinsupp := toFinsupp✝ } f = ∑ a in range n, f a (coeff { toFinsupp : …
  simp only [Polynomial.sum, support, coeff, natDegree, degree] at this ⊢
  -- ⊢ ∑ x in toFinsupp✝.support, f x (↑toFinsupp✝ x) = ∑ x in range n, f x (↑toFin …
  exact Finsupp.sum_of_support_subset _ this _ fun n _hn => h n
  -- 🎉 no goals
#align polynomial.sum_over_range' Polynomial.sum_over_range'

/-- We can reexpress a sum over `p.support` as a sum over `range (p.natDegree + 1)`.
-/
theorem sum_over_range [AddCommMonoid S] (p : R[X]) {f : ℕ → R → S} (h : ∀ n, f n 0 = 0) :
    p.sum f = ∑ a : ℕ in range (p.natDegree + 1), f a (coeff p a) :=
  sum_over_range' p h (p.natDegree + 1) (lt_add_one _)
#align polynomial.sum_over_range Polynomial.sum_over_range

-- TODO this is essentially a duplicate of `sum_over_range`, and should be removed.
theorem sum_fin [AddCommMonoid S] (f : ℕ → R → S) (hf : ∀ i, f i 0 = 0) {n : ℕ} {p : R[X]}
    (hn : p.degree < n) : (∑ i : Fin n, f i (p.coeff i)) = p.sum f := by
  by_cases hp : p = 0
  -- ⊢ ∑ i : Fin n, f (↑i) (coeff p ↑i) = sum p f
  · rw [hp, sum_zero_index, Finset.sum_eq_zero]
    -- ⊢ ∀ (x : Fin n), x ∈ univ → f (↑x) (coeff 0 ↑x) = 0
    intro i _
    -- ⊢ f (↑i) (coeff 0 ↑i) = 0
    exact hf i
    -- 🎉 no goals
  rw [sum_over_range' _ hf n ((natDegree_lt_iff_degree_lt hp).mpr hn),
    Fin.sum_univ_eq_sum_range fun i => f i (p.coeff i)]
#align polynomial.sum_fin Polynomial.sum_fin

theorem as_sum_range' (p : R[X]) (n : ℕ) (w : p.natDegree < n) :
    p = ∑ i in range n, monomial i (coeff p i) :=
  p.sum_monomial_eq.symm.trans <| p.sum_over_range' monomial_zero_right _ w
#align polynomial.as_sum_range' Polynomial.as_sum_range'

theorem as_sum_range (p : R[X]) : p = ∑ i in range (p.natDegree + 1), monomial i (coeff p i) :=
  p.sum_monomial_eq.symm.trans <| p.sum_over_range <| monomial_zero_right
#align polynomial.as_sum_range Polynomial.as_sum_range

theorem as_sum_range_C_mul_X_pow (p : R[X]) :
    p = ∑ i in range (p.natDegree + 1), C (coeff p i) * X ^ i :=
  p.as_sum_range.trans <| by simp only [C_mul_X_pow_eq_monomial]
                             -- 🎉 no goals
#align polynomial.as_sum_range_C_mul_X_pow Polynomial.as_sum_range_C_mul_X_pow

theorem coeff_ne_zero_of_eq_degree (hn : degree p = n) : coeff p n ≠ 0 := fun h =>
  mem_support_iff.mp (mem_of_max hn) h
#align polynomial.coeff_ne_zero_of_eq_degree Polynomial.coeff_ne_zero_of_eq_degree

theorem eq_X_add_C_of_degree_le_one (h : degree p ≤ 1) : p = C (p.coeff 1) * X + C (p.coeff 0) :=
  ext fun n =>
    Nat.casesOn n (by simp) fun n =>
                      -- 🎉 no goals
      Nat.casesOn n (by simp [coeff_C]) fun m => by
                        -- 🎉 no goals
        -- Porting note: `by decide` → `Iff.mpr ..`
        have : degree p < m.succ.succ := lt_of_le_of_lt h
          (Iff.mpr WithBot.coe_lt_coe <| Nat.succ_lt_succ <| Nat.zero_lt_succ m)
        simp [coeff_eq_zero_of_degree_lt this, coeff_C, Nat.succ_ne_zero, coeff_X, Nat.succ_inj',
          @eq_comm ℕ 0]
#align polynomial.eq_X_add_C_of_degree_le_one Polynomial.eq_X_add_C_of_degree_le_one

theorem eq_X_add_C_of_degree_eq_one (h : degree p = 1) :
    p = C p.leadingCoeff * X + C (p.coeff 0) :=
  (eq_X_add_C_of_degree_le_one (show degree p ≤ 1 from h ▸ le_rfl)).trans
    (by simp only [leadingCoeff, natDegree_eq_of_degree_eq_some h]; rfl)
        -- ⊢ ↑C (coeff p 1) * X + ↑C (coeff p 0) = ↑C (coeff p One.one) * X + ↑C (coeff p …
                                                                    -- 🎉 no goals
#align polynomial.eq_X_add_C_of_degree_eq_one Polynomial.eq_X_add_C_of_degree_eq_one

theorem eq_X_add_C_of_natDegree_le_one (h : natDegree p ≤ 1) :
    p = C (p.coeff 1) * X + C (p.coeff 0) :=
  eq_X_add_C_of_degree_le_one <| degree_le_of_natDegree_le h
#align polynomial.eq_X_add_C_of_nat_degree_le_one Polynomial.eq_X_add_C_of_natDegree_le_one

theorem Monic.eq_X_add_C (hm : p.Monic) (hnd : p.natDegree = 1) : p = X + C (p.coeff 0) := by
  rw [← one_mul X, ← C_1, ← hm.coeff_natDegree, hnd, ← eq_X_add_C_of_natDegree_le_one hnd.le]
  -- 🎉 no goals
#align polynomial.monic.eq_X_add_C Polynomial.Monic.eq_X_add_C

theorem exists_eq_X_add_C_of_natDegree_le_one (h : natDegree p ≤ 1) : ∃ a b, p = C a * X + C b :=
  ⟨p.coeff 1, p.coeff 0, eq_X_add_C_of_natDegree_le_one h⟩
#align polynomial.exists_eq_X_add_C_of_natDegree_le_one Polynomial.exists_eq_X_add_C_of_natDegree_le_one

theorem degree_X_pow_le (n : ℕ) : degree (X ^ n : R[X]) ≤ n := by
  simpa only [C_1, one_mul] using degree_C_mul_X_pow_le n (1 : R)
  -- 🎉 no goals
#align polynomial.degree_X_pow_le Polynomial.degree_X_pow_le

theorem degree_X_le : degree (X : R[X]) ≤ 1 :=
  degree_monomial_le _ _
#align polynomial.degree_X_le Polynomial.degree_X_le

theorem natDegree_X_le : (X : R[X]).natDegree ≤ 1 :=
  natDegree_le_of_degree_le degree_X_le
#align polynomial.nat_degree_X_le Polynomial.natDegree_X_le

theorem mem_support_C_mul_X_pow {n a : ℕ} {c : R} (h : a ∈ support (C c * X ^ n)) : a = n :=
  mem_singleton.1 <| support_C_mul_X_pow' n c h
#align polynomial.mem_support_C_mul_X_pow Polynomial.mem_support_C_mul_X_pow

theorem card_support_C_mul_X_pow_le_one {c : R} {n : ℕ} : card (support (C c * X ^ n)) ≤ 1 := by
  rw [← card_singleton n]
  -- ⊢ card (support (↑C c * X ^ n)) ≤ card {n}
  apply card_le_of_subset (support_C_mul_X_pow' n c)
  -- 🎉 no goals
#align polynomial.card_support_C_mul_X_pow_le_one Polynomial.card_support_C_mul_X_pow_le_one

theorem card_supp_le_succ_natDegree (p : R[X]) : p.support.card ≤ p.natDegree + 1 := by
  rw [← Finset.card_range (p.natDegree + 1)]
  -- ⊢ card (support p) ≤ card (range (natDegree p + 1))
  exact Finset.card_le_of_subset supp_subset_range_natDegree_succ
  -- 🎉 no goals
#align polynomial.card_supp_le_succ_nat_degree Polynomial.card_supp_le_succ_natDegree

theorem le_degree_of_mem_supp (a : ℕ) : a ∈ p.support → ↑a ≤ degree p :=
  le_degree_of_ne_zero ∘ mem_support_iff.mp
#align polynomial.le_degree_of_mem_supp Polynomial.le_degree_of_mem_supp

theorem nonempty_support_iff : p.support.Nonempty ↔ p ≠ 0 := by
  rw [Ne.def, nonempty_iff_ne_empty, Ne.def, ← support_eq_empty]
  -- 🎉 no goals
#align polynomial.nonempty_support_iff Polynomial.nonempty_support_iff

end Semiring

section NonzeroSemiring

variable [Semiring R] [Nontrivial R] {p q : R[X]}

@[simp]
theorem degree_one : degree (1 : R[X]) = (0 : WithBot ℕ) :=
  degree_C (show (1 : R) ≠ 0 from zero_ne_one.symm)
#align polynomial.degree_one Polynomial.degree_one

@[simp]
theorem degree_X : degree (X : R[X]) = 1 :=
  degree_monomial _ one_ne_zero
#align polynomial.degree_X Polynomial.degree_X

@[simp]
theorem natDegree_X : (X : R[X]).natDegree = 1 :=
  natDegree_eq_of_degree_eq_some degree_X
#align polynomial.nat_degree_X Polynomial.natDegree_X

end NonzeroSemiring

section Ring

variable [Ring R]

theorem coeff_mul_X_sub_C {p : R[X]} {r : R} {a : ℕ} :
    coeff (p * (X - C r)) (a + 1) = coeff p a - coeff p (a + 1) * r := by simp [mul_sub]
                                                                          -- 🎉 no goals
#align polynomial.coeff_mul_X_sub_C Polynomial.coeff_mul_X_sub_C

@[simp]
theorem degree_neg (p : R[X]) : degree (-p) = degree p := by unfold degree; rw [support_neg]
                                                             -- ⊢ Finset.max (support (-p)) = Finset.max (support p)
                                                                            -- 🎉 no goals
#align polynomial.degree_neg Polynomial.degree_neg

theorem degree_neg_le_of_le {a : WithBot ℕ} {p : R[X]} (hp : degree p ≤ a) : degree (-p) ≤ a :=
  p.degree_neg.le.trans hp

@[simp]
theorem natDegree_neg (p : R[X]) : natDegree (-p) = natDegree p := by simp [natDegree]
                                                                      -- 🎉 no goals
#align polynomial.nat_degree_neg Polynomial.natDegree_neg

theorem natDegree_neg_le_of_le {p : R[X]} (hp : natDegree p ≤ m) : natDegree (-p) ≤ m :=
  (natDegree_neg p).le.trans hp

@[simp]
theorem natDegree_int_cast (n : ℤ) : natDegree (n : R[X]) = 0 := by
  rw [← C_eq_int_cast, natDegree_C]
  -- 🎉 no goals
#align polynomial.nat_degree_int_cast Polynomial.natDegree_int_cast

theorem degree_int_cast_le (n : ℤ) : degree (n : R[X]) ≤ 0 := degree_le_of_natDegree_le (by simp)
                                                                                            -- 🎉 no goals

@[simp]
theorem leadingCoeff_neg (p : R[X]) : (-p).leadingCoeff = -p.leadingCoeff := by
  rw [leadingCoeff, leadingCoeff, natDegree_neg, coeff_neg]
  -- 🎉 no goals
#align polynomial.leading_coeff_neg Polynomial.leadingCoeff_neg

end Ring

section Semiring

variable [Semiring R]

/-- The second-highest coefficient, or 0 for constants -/
def nextCoeff (p : R[X]) : R :=
  if p.natDegree = 0 then 0 else p.coeff (p.natDegree - 1)
#align polynomial.next_coeff Polynomial.nextCoeff

@[simp]
theorem nextCoeff_C_eq_zero (c : R) : nextCoeff (C c) = 0 := by
  rw [nextCoeff]
  -- ⊢ (if natDegree (↑C c) = 0 then 0 else coeff (↑C c) (natDegree (↑C c) - 1)) = 0
  simp
  -- 🎉 no goals
#align polynomial.next_coeff_C_eq_zero Polynomial.nextCoeff_C_eq_zero

theorem nextCoeff_of_pos_natDegree (p : R[X]) (hp : 0 < p.natDegree) :
    nextCoeff p = p.coeff (p.natDegree - 1) := by
  rw [nextCoeff, if_neg]
  -- ⊢ ¬natDegree p = 0
  contrapose! hp
  -- ⊢ natDegree p ≤ 0
  simpa
  -- 🎉 no goals
#align polynomial.next_coeff_of_pos_nat_degree Polynomial.nextCoeff_of_pos_natDegree

variable {p q : R[X]} {ι : Type*}

theorem coeff_natDegree_eq_zero_of_degree_lt (h : degree p < degree q) :
    coeff p (natDegree q) = 0 :=
  coeff_eq_zero_of_degree_lt (lt_of_lt_of_le h degree_le_natDegree)
#align polynomial.coeff_nat_degree_eq_zero_of_degree_lt Polynomial.coeff_natDegree_eq_zero_of_degree_lt

theorem ne_zero_of_degree_gt {n : WithBot ℕ} (h : n < degree p) : p ≠ 0 :=
  mt degree_eq_bot.2 h.ne_bot
#align polynomial.ne_zero_of_degree_gt Polynomial.ne_zero_of_degree_gt

theorem ne_zero_of_degree_ge_degree (hpq : p.degree ≤ q.degree) (hp : p ≠ 0) : q ≠ 0 :=
  Polynomial.ne_zero_of_degree_gt
    (lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr (by rwa [Ne.def, Polynomial.degree_eq_bot])) hpq :
                                               -- 🎉 no goals
      q.degree > ⊥)
#align polynomial.ne_zero_of_degree_ge_degree Polynomial.ne_zero_of_degree_ge_degree

theorem ne_zero_of_natDegree_gt {n : ℕ} (h : n < natDegree p) : p ≠ 0 := fun H => by
  simp [H, Nat.not_lt_zero] at h
  -- 🎉 no goals
#align polynomial.ne_zero_of_nat_degree_gt Polynomial.ne_zero_of_natDegree_gt

theorem degree_lt_degree (h : natDegree p < natDegree q) : degree p < degree q := by
  by_cases hp : p = 0
  -- ⊢ degree p < degree q
  · simp [hp]
    -- ⊢ ⊥ < degree q
    rw [bot_lt_iff_ne_bot]
    -- ⊢ degree q ≠ ⊥
    intro hq
    -- ⊢ False
    simp [hp, degree_eq_bot.mp hq, lt_irrefl] at h
    -- 🎉 no goals
  · rwa [degree_eq_natDegree hp, degree_eq_natDegree <| ne_zero_of_natDegree_gt h, Nat.cast_lt]
    -- 🎉 no goals
#align polynomial.degree_lt_degree Polynomial.degree_lt_degree

theorem natDegree_lt_natDegree_iff (hp : p ≠ 0) : natDegree p < natDegree q ↔ degree p < degree q :=
  ⟨degree_lt_degree, fun h ↦ by
    have hq : q ≠ 0 := ne_zero_of_degree_gt h
    -- ⊢ natDegree p < natDegree q
    rwa [degree_eq_natDegree hp, degree_eq_natDegree hq, Nat.cast_lt] at h⟩
    -- 🎉 no goals
#align polynomial.nat_degree_lt_nat_degree_iff Polynomial.natDegree_lt_natDegree_iff

theorem eq_C_of_degree_le_zero (h : degree p ≤ 0) : p = C (coeff p 0) := by
  ext (_ | n)
  -- ⊢ coeff p Nat.zero = coeff (↑C (coeff p 0)) Nat.zero
  · simp
    -- 🎉 no goals
  rw [coeff_C, if_neg (Nat.succ_ne_zero _), coeff_eq_zero_of_degree_lt]
  -- ⊢ degree p < ↑(Nat.succ n)
  exact h.trans_lt (WithBot.some_lt_some.2 n.succ_pos)
  -- 🎉 no goals
#align polynomial.eq_C_of_degree_le_zero Polynomial.eq_C_of_degree_le_zero

theorem eq_C_of_degree_eq_zero (h : degree p = 0) : p = C (coeff p 0) :=
  eq_C_of_degree_le_zero h.le
#align polynomial.eq_C_of_degree_eq_zero Polynomial.eq_C_of_degree_eq_zero

theorem degree_le_zero_iff : degree p ≤ 0 ↔ p = C (coeff p 0) :=
  ⟨eq_C_of_degree_le_zero, fun h => h.symm ▸ degree_C_le⟩
#align polynomial.degree_le_zero_iff Polynomial.degree_le_zero_iff

theorem degree_add_le (p q : R[X]) : degree (p + q) ≤ max (degree p) (degree q) := by
  simpa only [degree, ←support_toFinsupp, toFinsupp_add]
    using AddMonoidAlgebra.sup_support_add_le _ _ _
#align polynomial.degree_add_le Polynomial.degree_add_le

theorem degree_add_le_of_degree_le {p q : R[X]} {n : ℕ} (hp : degree p ≤ n) (hq : degree q ≤ n) :
    degree (p + q) ≤ n :=
  (degree_add_le p q).trans <| max_le hp hq
#align polynomial.degree_add_le_of_degree_le Polynomial.degree_add_le_of_degree_le

theorem degree_add_le_of_le {a b : WithBot ℕ} (hp : degree p ≤ a) (hq : degree q ≤ b) :
    degree (p + q) ≤ max a b :=
  (p.degree_add_le q).trans <| max_le_max ‹_› ‹_›

theorem natDegree_add_le (p q : R[X]) : natDegree (p + q) ≤ max (natDegree p) (natDegree q) := by
  cases' le_max_iff.1 (degree_add_le p q) with h h <;> simp [natDegree_le_natDegree h]
  -- ⊢ natDegree (p + q) ≤ max (natDegree p) (natDegree q)
                                                       -- 🎉 no goals
                                                       -- 🎉 no goals
#align polynomial.nat_degree_add_le Polynomial.natDegree_add_le

theorem natDegree_add_le_of_degree_le {p q : R[X]} {n : ℕ} (hp : natDegree p ≤ n)
    (hq : natDegree q ≤ n) : natDegree (p + q) ≤ n :=
  (natDegree_add_le p q).trans <| max_le hp hq
#align polynomial.nat_degree_add_le_of_degree_le Polynomial.natDegree_add_le_of_degree_le

theorem natDegree_add_le_of_le (hp : natDegree p ≤ m) (hq : natDegree q ≤ n) :
    natDegree (p + q) ≤ max m n :=
  (p.natDegree_add_le q).trans <| max_le_max ‹_› ‹_›

@[simp]
theorem leadingCoeff_zero : leadingCoeff (0 : R[X]) = 0 :=
  rfl
#align polynomial.leading_coeff_zero Polynomial.leadingCoeff_zero

@[simp]
theorem leadingCoeff_eq_zero : leadingCoeff p = 0 ↔ p = 0 :=
  ⟨fun h =>
    Classical.by_contradiction fun hp =>
      mt mem_support_iff.1 (Classical.not_not.2 h) (mem_of_max (degree_eq_natDegree hp)),
    fun h => h.symm ▸ leadingCoeff_zero⟩
#align polynomial.leading_coeff_eq_zero Polynomial.leadingCoeff_eq_zero

theorem leadingCoeff_ne_zero : leadingCoeff p ≠ 0 ↔ p ≠ 0 := by rw [Ne.def, leadingCoeff_eq_zero]
                                                                -- 🎉 no goals
#align polynomial.leading_coeff_ne_zero Polynomial.leadingCoeff_ne_zero

theorem leadingCoeff_eq_zero_iff_deg_eq_bot : leadingCoeff p = 0 ↔ degree p = ⊥ := by
  rw [leadingCoeff_eq_zero, degree_eq_bot]
  -- 🎉 no goals
#align polynomial.leading_coeff_eq_zero_iff_deg_eq_bot Polynomial.leadingCoeff_eq_zero_iff_deg_eq_bot

theorem natDegree_mem_support_of_nonzero (H : p ≠ 0) : p.natDegree ∈ p.support := by
  rw [mem_support_iff]
  -- ⊢ coeff p (natDegree p) ≠ 0
  exact (not_congr leadingCoeff_eq_zero).mpr H
  -- 🎉 no goals
#align polynomial.nat_degree_mem_support_of_nonzero Polynomial.natDegree_mem_support_of_nonzero

theorem natDegree_eq_support_max' (h : p ≠ 0) :
    p.natDegree = p.support.max' (nonempty_support_iff.mpr h) :=
  (le_max' _ _ <| natDegree_mem_support_of_nonzero h).antisymm <|
    max'_le _ _ _ le_natDegree_of_mem_supp
#align polynomial.nat_degree_eq_support_max' Polynomial.natDegree_eq_support_max'

theorem natDegree_C_mul_X_pow_le (a : R) (n : ℕ) : natDegree (C a * X ^ n) ≤ n :=
  natDegree_le_iff_degree_le.2 <| degree_C_mul_X_pow_le _ _
#align polynomial.nat_degree_C_mul_X_pow_le Polynomial.natDegree_C_mul_X_pow_le

theorem degree_add_eq_left_of_degree_lt (h : degree q < degree p) : degree (p + q) = degree p :=
  le_antisymm (max_eq_left_of_lt h ▸ degree_add_le _ _) <|
    degree_le_degree <| by
      rw [coeff_add, coeff_natDegree_eq_zero_of_degree_lt h, add_zero]
      -- ⊢ coeff p (natDegree p) ≠ 0
      exact mt leadingCoeff_eq_zero.1 (ne_zero_of_degree_gt h)
      -- 🎉 no goals
#align polynomial.degree_add_eq_left_of_degree_lt Polynomial.degree_add_eq_left_of_degree_lt

theorem degree_add_eq_right_of_degree_lt (h : degree p < degree q) : degree (p + q) = degree q := by
  rw [add_comm, degree_add_eq_left_of_degree_lt h]
  -- 🎉 no goals
#align polynomial.degree_add_eq_right_of_degree_lt Polynomial.degree_add_eq_right_of_degree_lt

theorem natDegree_add_eq_left_of_natDegree_lt (h : natDegree q < natDegree p) :
    natDegree (p + q) = natDegree p :=
  natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt (degree_lt_degree h))
#align polynomial.nat_degree_add_eq_left_of_nat_degree_lt Polynomial.natDegree_add_eq_left_of_natDegree_lt

theorem natDegree_add_eq_right_of_natDegree_lt (h : natDegree p < natDegree q) :
    natDegree (p + q) = natDegree q :=
  natDegree_eq_of_degree_eq (degree_add_eq_right_of_degree_lt (degree_lt_degree h))
#align polynomial.nat_degree_add_eq_right_of_nat_degree_lt Polynomial.natDegree_add_eq_right_of_natDegree_lt

theorem degree_add_C (hp : 0 < degree p) : degree (p + C a) = degree p :=
  add_comm (C a) p ▸ degree_add_eq_right_of_degree_lt <| lt_of_le_of_lt degree_C_le hp
#align polynomial.degree_add_C Polynomial.degree_add_C

@[simp] theorem natDegree_add_C {a : R} : (p + C a).natDegree = p.natDegree := by
  rcases eq_or_ne p 0 with rfl | hp
  -- ⊢ natDegree (0 + ↑C a) = natDegree 0
  · simp
    -- 🎉 no goals
  by_cases hpd : p.degree ≤ 0
  -- ⊢ natDegree (p + ↑C a) = natDegree p
  · rw [eq_C_of_degree_le_zero hpd, ← C_add, natDegree_C, natDegree_C]
    -- 🎉 no goals
  · rw [not_le, degree_eq_natDegree hp, Nat.cast_pos, ← natDegree_C a] at hpd
    -- ⊢ natDegree (p + ↑C a) = natDegree p
    exact natDegree_add_eq_left_of_natDegree_lt hpd
    -- 🎉 no goals

@[simp] theorem natDegree_C_add {a : R} : (C a + p).natDegree = p.natDegree := by
  simp [add_comm _ p]
  -- 🎉 no goals

theorem degree_add_eq_of_leadingCoeff_add_ne_zero (h : leadingCoeff p + leadingCoeff q ≠ 0) :
    degree (p + q) = max p.degree q.degree :=
  le_antisymm (degree_add_le _ _) <|
    match lt_trichotomy (degree p) (degree q) with
    | Or.inl hlt => by
      rw [degree_add_eq_right_of_degree_lt hlt, max_eq_right_of_lt hlt]
      -- 🎉 no goals
    | Or.inr (Or.inl HEq) =>
      le_of_not_gt fun hlt : max (degree p) (degree q) > degree (p + q) =>
        h <|
          show leadingCoeff p + leadingCoeff q = 0 by
            rw [HEq, max_self] at hlt
            -- ⊢ leadingCoeff p + leadingCoeff q = 0
            rw [leadingCoeff, leadingCoeff, natDegree_eq_of_degree_eq HEq, ← coeff_add]
            -- ⊢ coeff (p + q) (natDegree q) = 0
            exact coeff_natDegree_eq_zero_of_degree_lt hlt
            -- 🎉 no goals
    | Or.inr (Or.inr hlt) => by
      rw [degree_add_eq_left_of_degree_lt hlt, max_eq_left_of_lt hlt]
      -- 🎉 no goals
#align polynomial.degree_add_eq_of_leading_coeff_add_ne_zero Polynomial.degree_add_eq_of_leadingCoeff_add_ne_zero

theorem degree_erase_le (p : R[X]) (n : ℕ) : degree (p.erase n) ≤ degree p := by
  rcases p with ⟨p⟩
  -- ⊢ degree (erase n { toFinsupp := p }) ≤ degree { toFinsupp := p }
  simp only [erase_def, degree, coeff, support]
  -- ⊢ Finset.max (Finsupp.erase n p).support ≤ Finset.max p.support
  -- Porting note: simpler convert-free proof to be explicit about definition unfolding
  apply sup_mono
  -- ⊢ (Finsupp.erase n p).support ⊆ p.support
  rw [Finsupp.support_erase]
  -- ⊢ Finset.erase p.support n ⊆ p.support
  apply Finset.erase_subset
  -- 🎉 no goals
#align polynomial.degree_erase_le Polynomial.degree_erase_le

theorem degree_erase_lt (hp : p ≠ 0) : degree (p.erase (natDegree p)) < degree p := by
  apply lt_of_le_of_ne (degree_erase_le _ _)
  -- ⊢ degree (erase (natDegree p) p) ≠ degree p
  rw [degree_eq_natDegree hp, degree, support_erase]
  -- ⊢ Finset.max (Finset.erase (support p) (natDegree p)) ≠ ↑(natDegree p)
  exact fun h => not_mem_erase _ _ (mem_of_max h)
  -- 🎉 no goals
#align polynomial.degree_erase_lt Polynomial.degree_erase_lt

theorem degree_update_le (p : R[X]) (n : ℕ) (a : R) : degree (p.update n a) ≤ max (degree p) n := by
  rw [degree, support_update]
  -- ⊢ Finset.max (if a = 0 then Finset.erase (support p) n else insert n (support  …
  split_ifs
  -- ⊢ Finset.max (Finset.erase (support p) n) ≤ max (degree p) ↑n
  · exact (Finset.max_mono (erase_subset _ _)).trans (le_max_left _ _)
    -- 🎉 no goals
  · rw [max_insert, max_comm]
    -- ⊢ max (Finset.max (support p)) ↑n ≤ max (degree p) ↑n
    exact le_rfl
    -- 🎉 no goals
#align polynomial.degree_update_le Polynomial.degree_update_le

theorem degree_sum_le (s : Finset ι) (f : ι → R[X]) :
    degree (∑ i in s, f i) ≤ s.sup fun b => degree (f b) :=
  Finset.induction_on s (by simp only [sum_empty, sup_empty, degree_zero, le_refl])
                            -- 🎉 no goals
    fun a s has ih =>
    calc
      degree (∑ i in insert a s, f i) ≤ max (degree (f a)) (degree (∑ i in s, f i)) := by
        rw [sum_insert has]; exact degree_add_le _ _
        -- ⊢ degree (f a + ∑ x in s, f x) ≤ max (degree (f a)) (degree (∑ i in s, f i))
                             -- 🎉 no goals
      _ ≤ _ := by rw [sup_insert, sup_eq_max]; exact max_le_max le_rfl ih
                  -- ⊢ max (degree (f a)) (degree (∑ i in s, f i)) ≤ max (degree (f a)) (sup s fun  …
                                               -- 🎉 no goals
#align polynomial.degree_sum_le Polynomial.degree_sum_le

theorem degree_mul_le (p q : R[X]) : degree (p * q) ≤ degree p + degree q := by
  simpa only [degree, ←support_toFinsupp, toFinsupp_mul]
    using AddMonoidAlgebra.sup_support_mul_le (WithBot.coe_add _ _).le _ _
#align polynomial.degree_mul_le Polynomial.degree_mul_le

theorem degree_mul_le_of_le {a b : WithBot ℕ} (hp : degree p ≤ a) (hq : degree q ≤ b) :
    degree (p * q) ≤ a + b :=
  (p.degree_mul_le _).trans <| add_le_add ‹_› ‹_›

theorem degree_pow_le (p : R[X]) : ∀ n : ℕ, degree (p ^ n) ≤ n • degree p
  | 0 => by rw [pow_zero, zero_nsmul]; exact degree_one_le
            -- ⊢ degree 1 ≤ 0
                                       -- 🎉 no goals
  | n + 1 =>
    calc
      degree (p ^ (n + 1)) ≤ degree p + degree (p ^ n) := by
        rw [pow_succ]; exact degree_mul_le _ _
        -- ⊢ degree (p * p ^ n) ≤ degree p + degree (p ^ n)
                       -- 🎉 no goals
      _ ≤ _ := by rw [succ_nsmul]; exact add_le_add le_rfl (degree_pow_le _ _)
                  -- ⊢ degree p + degree (p ^ n) ≤ degree p + n • degree p
                                   -- 🎉 no goals
#align polynomial.degree_pow_le Polynomial.degree_pow_le

theorem degree_pow_le_of_le {a : WithBot ℕ} (b : ℕ) (hp : degree p ≤ a) :
    degree (p ^ b) ≤ b * a := by
  induction b with
  | zero => simp [degree_one_le]
  | succ n hn =>
      rw [Nat.cast_succ, add_mul, one_mul, pow_succ']
      exact degree_mul_le_of_le hn hp

@[simp]
theorem leadingCoeff_monomial (a : R) (n : ℕ) : leadingCoeff (monomial n a) = a := by
  by_cases ha : a = 0
  -- ⊢ leadingCoeff (↑(monomial n) a) = a
  · simp only [ha, (monomial n).map_zero, leadingCoeff_zero]
    -- 🎉 no goals
  · rw [leadingCoeff, natDegree_monomial, if_neg ha, coeff_monomial]
    -- ⊢ (if n = n then a else 0) = a
    simp
    -- 🎉 no goals
#align polynomial.leading_coeff_monomial Polynomial.leadingCoeff_monomial

theorem leadingCoeff_C_mul_X_pow (a : R) (n : ℕ) : leadingCoeff (C a * X ^ n) = a := by
  rw [C_mul_X_pow_eq_monomial, leadingCoeff_monomial]
  -- 🎉 no goals
#align polynomial.leading_coeff_C_mul_X_pow Polynomial.leadingCoeff_C_mul_X_pow

theorem leadingCoeff_C_mul_X (a : R) : leadingCoeff (C a * X) = a := by
  simpa only [pow_one] using leadingCoeff_C_mul_X_pow a 1
  -- 🎉 no goals
#align polynomial.leading_coeff_C_mul_X Polynomial.leadingCoeff_C_mul_X

@[simp]
theorem leadingCoeff_C (a : R) : leadingCoeff (C a) = a :=
  leadingCoeff_monomial a 0
#align polynomial.leading_coeff_C Polynomial.leadingCoeff_C

-- @[simp] -- Porting note: simp can prove this
theorem leadingCoeff_X_pow (n : ℕ) : leadingCoeff ((X : R[X]) ^ n) = 1 := by
  simpa only [C_1, one_mul] using leadingCoeff_C_mul_X_pow (1 : R) n
  -- 🎉 no goals
#align polynomial.leading_coeff_X_pow Polynomial.leadingCoeff_X_pow

-- @[simp] -- Porting note: simp can prove this
theorem leadingCoeff_X : leadingCoeff (X : R[X]) = 1 := by
  simpa only [pow_one] using @leadingCoeff_X_pow R _ 1
  -- 🎉 no goals
#align polynomial.leading_coeff_X Polynomial.leadingCoeff_X

@[simp]
theorem monic_X_pow (n : ℕ) : Monic (X ^ n : R[X]) :=
  leadingCoeff_X_pow n
#align polynomial.monic_X_pow Polynomial.monic_X_pow

@[simp]
theorem monic_X : Monic (X : R[X]) :=
  leadingCoeff_X
#align polynomial.monic_X Polynomial.monic_X

-- @[simp] -- Porting note: simp can prove this
theorem leadingCoeff_one : leadingCoeff (1 : R[X]) = 1 :=
  leadingCoeff_C 1
#align polynomial.leading_coeff_one Polynomial.leadingCoeff_one

@[simp]
theorem monic_one : Monic (1 : R[X]) :=
  leadingCoeff_C _
#align polynomial.monic_one Polynomial.monic_one

theorem Monic.ne_zero {R : Type*} [Semiring R] [Nontrivial R] {p : R[X]} (hp : p.Monic) :
    p ≠ 0 := by
  rintro rfl
  -- ⊢ False
  simp [Monic] at hp
  -- 🎉 no goals
#align polynomial.monic.ne_zero Polynomial.Monic.ne_zero

theorem Monic.ne_zero_of_ne (h : (0 : R) ≠ 1) {p : R[X]} (hp : p.Monic) : p ≠ 0 := by
  nontriviality R
  -- ⊢ p ≠ 0
  exact hp.ne_zero
  -- 🎉 no goals
#align polynomial.monic.ne_zero_of_ne Polynomial.Monic.ne_zero_of_ne

theorem monic_of_natDegree_le_of_coeff_eq_one (n : ℕ) (pn : p.natDegree ≤ n) (p1 : p.coeff n = 1) :
    Monic p := by
  unfold Monic
  -- ⊢ leadingCoeff p = 1
  nontriviality
  -- ⊢ leadingCoeff p = 1
  refine' (congr_arg _ <| natDegree_eq_of_le_of_coeff_ne_zero pn _).trans p1
  -- ⊢ coeff p n ≠ 0
  exact ne_of_eq_of_ne p1 one_ne_zero
  -- 🎉 no goals
#align polynomial.monic_of_nat_degree_le_of_coeff_eq_one Polynomial.monic_of_natDegree_le_of_coeff_eq_one

theorem monic_of_degree_le_of_coeff_eq_one (n : ℕ) (pn : p.degree ≤ n) (p1 : p.coeff n = 1) :
    Monic p :=
  monic_of_natDegree_le_of_coeff_eq_one n (natDegree_le_of_degree_le pn) p1
#align polynomial.monic_of_degree_le_of_coeff_eq_one Polynomial.monic_of_degree_le_of_coeff_eq_one

theorem Monic.ne_zero_of_polynomial_ne {r} (hp : Monic p) (hne : q ≠ r) : p ≠ 0 :=
  haveI := Nontrivial.of_polynomial_ne hne
  hp.ne_zero
#align polynomial.monic.ne_zero_of_polynomial_ne Polynomial.Monic.ne_zero_of_polynomial_ne

theorem leadingCoeff_add_of_degree_lt (h : degree p < degree q) :
    leadingCoeff (p + q) = leadingCoeff q := by
  have : coeff p (natDegree q) = 0 := coeff_natDegree_eq_zero_of_degree_lt h
  -- ⊢ leadingCoeff (p + q) = leadingCoeff q
  simp only [leadingCoeff, natDegree_eq_of_degree_eq (degree_add_eq_right_of_degree_lt h), this,
    coeff_add, zero_add]
#align polynomial.leading_coeff_add_of_degree_lt Polynomial.leadingCoeff_add_of_degree_lt

theorem leadingCoeff_add_of_degree_lt' (h : degree q < degree p) :
    leadingCoeff (p + q) = leadingCoeff p := by
  rw [add_comm]
  -- ⊢ leadingCoeff (q + p) = leadingCoeff p
  exact leadingCoeff_add_of_degree_lt h
  -- 🎉 no goals

theorem leadingCoeff_add_of_degree_eq (h : degree p = degree q)
    (hlc : leadingCoeff p + leadingCoeff q ≠ 0) :
    leadingCoeff (p + q) = leadingCoeff p + leadingCoeff q := by
  have : natDegree (p + q) = natDegree p := by
    apply natDegree_eq_of_degree_eq
    rw [degree_add_eq_of_leadingCoeff_add_ne_zero hlc, h, max_self]
  simp only [leadingCoeff, this, natDegree_eq_of_degree_eq h, coeff_add]
  -- 🎉 no goals
#align polynomial.leading_coeff_add_of_degree_eq Polynomial.leadingCoeff_add_of_degree_eq

@[simp]
theorem coeff_mul_degree_add_degree (p q : R[X]) :
    coeff (p * q) (natDegree p + natDegree q) = leadingCoeff p * leadingCoeff q :=
  calc
    coeff (p * q) (natDegree p + natDegree q) =
        ∑ x in Nat.antidiagonal (natDegree p + natDegree q), coeff p x.1 * coeff q x.2 :=
      coeff_mul _ _ _
    _ = coeff p (natDegree p) * coeff q (natDegree q) := by
      refine' Finset.sum_eq_single (natDegree p, natDegree q) _ _
      -- ⊢ ∀ (b : ℕ × ℕ), b ∈ Nat.antidiagonal (natDegree p + natDegree q) → b ≠ (natDe …
      · rintro ⟨i, j⟩ h₁ h₂
        -- ⊢ coeff p (i, j).fst * coeff q (i, j).snd = 0
        rw [Nat.mem_antidiagonal] at h₁
        -- ⊢ coeff p (i, j).fst * coeff q (i, j).snd = 0
        by_cases H : natDegree p < i
        -- ⊢ coeff p (i, j).fst * coeff q (i, j).snd = 0
        · rw [coeff_eq_zero_of_degree_lt
              (lt_of_le_of_lt degree_le_natDegree (WithBot.coe_lt_coe.2 H)),
            zero_mul]
        · rw [not_lt_iff_eq_or_lt] at H
          -- ⊢ coeff p (i, j).fst * coeff q (i, j).snd = 0
          cases' H with H H
          -- ⊢ coeff p (i, j).fst * coeff q (i, j).snd = 0
          · subst H
            -- ⊢ coeff p (natDegree p, j).fst * coeff q (natDegree p, j).snd = 0
            rw [add_left_cancel_iff] at h₁
            -- ⊢ coeff p (natDegree p, j).fst * coeff q (natDegree p, j).snd = 0
            dsimp at h₁
            -- ⊢ coeff p (natDegree p, j).fst * coeff q (natDegree p, j).snd = 0
            subst h₁
            -- ⊢ coeff p (natDegree p, natDegree q).fst * coeff q (natDegree p, natDegree q). …
            exact (h₂ rfl).elim
            -- 🎉 no goals
          · suffices natDegree q < j by
              rw [coeff_eq_zero_of_degree_lt
                  (lt_of_le_of_lt degree_le_natDegree (WithBot.coe_lt_coe.2 this)),
                mul_zero]
            · by_contra' H'
              -- ⊢ False
              exact
                ne_of_lt (Nat.lt_of_lt_of_le (Nat.add_lt_add_right H j) (Nat.add_le_add_left H' _))
                  h₁
      · intro H
        -- ⊢ coeff p (natDegree p, natDegree q).fst * coeff q (natDegree p, natDegree q). …
        exfalso
        -- ⊢ False
        apply H
        -- ⊢ (natDegree p, natDegree q) ∈ Nat.antidiagonal (natDegree p + natDegree q)
        rw [Nat.mem_antidiagonal]
        -- 🎉 no goals
#align polynomial.coeff_mul_degree_add_degree Polynomial.coeff_mul_degree_add_degree

theorem degree_mul' (h : leadingCoeff p * leadingCoeff q ≠ 0) :
    degree (p * q) = degree p + degree q :=
  have hp : p ≠ 0 := by refine' mt _ h; exact fun hp => by rw [hp, leadingCoeff_zero, zero_mul]
                        -- ⊢ p = 0 → leadingCoeff p * leadingCoeff q = 0
                                        -- 🎉 no goals
  have hq : q ≠ 0 := by refine' mt _ h; exact fun hq => by rw [hq, leadingCoeff_zero, mul_zero]
                        -- ⊢ q = 0 → leadingCoeff p * leadingCoeff q = 0
                                        -- 🎉 no goals
  le_antisymm (degree_mul_le _ _)
    (by
      rw [degree_eq_natDegree hp, degree_eq_natDegree hq]
      -- ⊢ ↑(natDegree p) + ↑(natDegree q) ≤ degree (p * q)
      refine le_degree_of_ne_zero (n := natDegree p + natDegree q) ?_
      -- ⊢ coeff (p * q) (natDegree p + natDegree q) ≠ 0
      rwa [coeff_mul_degree_add_degree])
      -- 🎉 no goals
#align polynomial.degree_mul' Polynomial.degree_mul'

theorem Monic.degree_mul (hq : Monic q) : degree (p * q) = degree p + degree q :=
  if hp : p = 0 then by simp [hp]
                        -- 🎉 no goals
  else degree_mul' <| by rwa [hq.leadingCoeff, mul_one, Ne.def, leadingCoeff_eq_zero]
                         -- 🎉 no goals
#align polynomial.monic.degree_mul Polynomial.Monic.degree_mul

theorem natDegree_mul' (h : leadingCoeff p * leadingCoeff q ≠ 0) :
    natDegree (p * q) = natDegree p + natDegree q :=
  have hp : p ≠ 0 := mt leadingCoeff_eq_zero.2 fun h₁ => h <| by rw [h₁, zero_mul]
                                                                 -- 🎉 no goals
  have hq : q ≠ 0 := mt leadingCoeff_eq_zero.2 fun h₁ => h <| by rw [h₁, mul_zero]
                                                                 -- 🎉 no goals
  natDegree_eq_of_degree_eq_some <| by
    rw [degree_mul' h, Nat.cast_add, degree_eq_natDegree hp, degree_eq_natDegree hq]
    -- 🎉 no goals
#align polynomial.nat_degree_mul' Polynomial.natDegree_mul'

theorem leadingCoeff_mul' (h : leadingCoeff p * leadingCoeff q ≠ 0) :
    leadingCoeff (p * q) = leadingCoeff p * leadingCoeff q := by
  unfold leadingCoeff
  -- ⊢ coeff (p * q) (natDegree (p * q)) = coeff p (natDegree p) * coeff q (natDegr …
  rw [natDegree_mul' h, coeff_mul_degree_add_degree]
  -- ⊢ leadingCoeff p * leadingCoeff q = coeff p (natDegree p) * coeff q (natDegree …
  rfl
  -- 🎉 no goals
#align polynomial.leading_coeff_mul' Polynomial.leadingCoeff_mul'

theorem monomial_natDegree_leadingCoeff_eq_self (h : p.support.card ≤ 1) :
    monomial p.natDegree p.leadingCoeff = p := by
  rcases card_support_le_one_iff_monomial.1 h with ⟨n, a, rfl⟩
  -- ⊢ ↑(monomial (natDegree (↑(monomial n) a))) (leadingCoeff (↑(monomial n) a)) = …
  by_cases ha : a = 0 <;> simp [ha]
  -- ⊢ ↑(monomial (natDegree (↑(monomial n) a))) (leadingCoeff (↑(monomial n) a)) = …
                          -- 🎉 no goals
                          -- 🎉 no goals
#align polynomial.monomial_nat_degree_leading_coeff_eq_self Polynomial.monomial_natDegree_leadingCoeff_eq_self

theorem C_mul_X_pow_eq_self (h : p.support.card ≤ 1) : C p.leadingCoeff * X ^ p.natDegree = p := by
  rw [C_mul_X_pow_eq_monomial, monomial_natDegree_leadingCoeff_eq_self h]
  -- 🎉 no goals
#align polynomial.C_mul_X_pow_eq_self Polynomial.C_mul_X_pow_eq_self

theorem leadingCoeff_pow' : leadingCoeff p ^ n ≠ 0 → leadingCoeff (p ^ n) = leadingCoeff p ^ n :=
  Nat.recOn n (by simp) fun n ih h => by
                  -- 🎉 no goals
    have h₁ : leadingCoeff p ^ n ≠ 0 := fun h₁ => h <| by rw [pow_succ, h₁, mul_zero]
    -- ⊢ leadingCoeff (p ^ Nat.succ n) = leadingCoeff p ^ Nat.succ n
    have h₂ : leadingCoeff p * leadingCoeff (p ^ n) ≠ 0 := by rwa [pow_succ, ← ih h₁] at h
    -- ⊢ leadingCoeff (p ^ Nat.succ n) = leadingCoeff p ^ Nat.succ n
    rw [pow_succ, pow_succ, leadingCoeff_mul' h₂, ih h₁]
    -- 🎉 no goals
#align polynomial.leading_coeff_pow' Polynomial.leadingCoeff_pow'

theorem degree_pow' : ∀ {n : ℕ}, leadingCoeff p ^ n ≠ 0 → degree (p ^ n) = n • degree p
  | 0 => fun h => by rw [pow_zero, ← C_1] at *; rw [degree_C h, zero_nsmul]
                     -- ⊢ degree (↑C 1) = 0 • degree p
                                                -- 🎉 no goals
  | n + 1 => fun h => by
    have h₁ : leadingCoeff p ^ n ≠ 0 := fun h₁ => h <| by rw [pow_succ, h₁, mul_zero]
    -- ⊢ degree (p ^ (n + 1)) = (n + 1) • degree p
    have h₂ : leadingCoeff p * leadingCoeff (p ^ n) ≠ 0 := by
      rwa [pow_succ, ← leadingCoeff_pow' h₁] at h
    rw [pow_succ, degree_mul' h₂, succ_nsmul, degree_pow' h₁]
    -- 🎉 no goals
#align polynomial.degree_pow' Polynomial.degree_pow'

theorem natDegree_pow' {n : ℕ} (h : leadingCoeff p ^ n ≠ 0) : natDegree (p ^ n) = n * natDegree p :=
  if hp0 : p = 0 then
    if hn0 : n = 0 then by simp [*] else by rw [hp0, zero_pow (Nat.pos_of_ne_zero hn0)]; simp
                           -- 🎉 no goals
                                            -- ⊢ natDegree 0 = n * natDegree 0
                                                                                         -- 🎉 no goals
  else
    have hpn : p ^ n ≠ 0 := fun hpn0 => by
      have h1 := h
      -- ⊢ False
      rw [← leadingCoeff_pow' h1, hpn0, leadingCoeff_zero] at h; exact h rfl
      -- ⊢ False
                                                                 -- 🎉 no goals
    Option.some_inj.1 <|
      show (natDegree (p ^ n) : WithBot ℕ) = (n * natDegree p : ℕ) by
        rw [← degree_eq_natDegree hpn, degree_pow' h, degree_eq_natDegree hp0]; simp
        -- ⊢ n • ↑(natDegree p) = ↑(n * natDegree p)
                                                                                -- 🎉 no goals
#align polynomial.nat_degree_pow' Polynomial.natDegree_pow'

theorem leadingCoeff_monic_mul {p q : R[X]} (hp : Monic p) :
    leadingCoeff (p * q) = leadingCoeff q := by
  rcases eq_or_ne q 0 with (rfl | H)
  -- ⊢ leadingCoeff (p * 0) = leadingCoeff 0
  · simp
    -- 🎉 no goals
  · rw [leadingCoeff_mul', hp.leadingCoeff, one_mul]
    -- ⊢ leadingCoeff p * leadingCoeff q ≠ 0
    rwa [hp.leadingCoeff, one_mul, Ne.def, leadingCoeff_eq_zero]
    -- 🎉 no goals
#align polynomial.leading_coeff_monic_mul Polynomial.leadingCoeff_monic_mul

theorem leadingCoeff_mul_monic {p q : R[X]} (hq : Monic q) :
    leadingCoeff (p * q) = leadingCoeff p :=
  Decidable.byCases
    (fun H : leadingCoeff p = 0 => by
      rw [H, leadingCoeff_eq_zero.1 H, zero_mul, leadingCoeff_zero])
      -- 🎉 no goals
    fun H : leadingCoeff p ≠ 0 => by
      rw [leadingCoeff_mul', hq.leadingCoeff, mul_one]
      -- ⊢ leadingCoeff p * leadingCoeff q ≠ 0
      rwa [hq.leadingCoeff, mul_one]
      -- 🎉 no goals
#align polynomial.leading_coeff_mul_monic Polynomial.leadingCoeff_mul_monic

@[simp]
theorem leadingCoeff_mul_X_pow {p : R[X]} {n : ℕ} : leadingCoeff (p * X ^ n) = leadingCoeff p :=
  leadingCoeff_mul_monic (monic_X_pow n)
#align polynomial.leading_coeff_mul_X_pow Polynomial.leadingCoeff_mul_X_pow

@[simp]
theorem leadingCoeff_mul_X {p : R[X]} : leadingCoeff (p * X) = leadingCoeff p :=
  leadingCoeff_mul_monic monic_X
#align polynomial.leading_coeff_mul_X Polynomial.leadingCoeff_mul_X

theorem natDegree_mul_le {p q : R[X]} : natDegree (p * q) ≤ natDegree p + natDegree q := by
  apply natDegree_le_of_degree_le
  -- ⊢ degree (p * q) ≤ ↑(natDegree p + natDegree q)
  apply le_trans (degree_mul_le p q)
  -- ⊢ degree p + degree q ≤ ↑(natDegree p + natDegree q)
  rw [Nat.cast_add]
  -- ⊢ degree p + degree q ≤ ↑(natDegree p) + ↑(natDegree q)
  apply add_le_add <;> apply degree_le_natDegree
  -- ⊢ degree p ≤ ↑(natDegree p)
                       -- 🎉 no goals
                       -- 🎉 no goals
#align polynomial.nat_degree_mul_le Polynomial.natDegree_mul_le

theorem natDegree_mul_le_of_le (hp : natDegree p ≤ m) (hg : natDegree q ≤ n) :
    natDegree (p * q) ≤ m + n :=
natDegree_mul_le.trans <| add_le_add ‹_› ‹_›

theorem natDegree_pow_le {p : R[X]} {n : ℕ} : (p ^ n).natDegree ≤ n * p.natDegree := by
  induction' n with i hi
  -- ⊢ natDegree (p ^ Nat.zero) ≤ Nat.zero * natDegree p
  · simp
    -- 🎉 no goals
  · rw [pow_succ, Nat.succ_mul, add_comm]
    -- ⊢ natDegree (p * p ^ i) ≤ natDegree p + i * natDegree p
    apply le_trans natDegree_mul_le
    -- ⊢ natDegree p + natDegree (p ^ i) ≤ natDegree p + i * natDegree p
    exact add_le_add_left hi _
    -- 🎉 no goals
#align polynomial.nat_degree_pow_le Polynomial.natDegree_pow_le

theorem natDegree_pow_le_of_le (n : ℕ) (hp : natDegree p ≤ m) :
    natDegree (p ^ n) ≤ n * m :=
  natDegree_pow_le.trans (Nat.mul_le_mul le_rfl ‹_›)

@[simp]
theorem coeff_pow_mul_natDegree (p : R[X]) (n : ℕ) :
    (p ^ n).coeff (n * p.natDegree) = p.leadingCoeff ^ n := by
  induction' n with i hi
  -- ⊢ coeff (p ^ Nat.zero) (Nat.zero * natDegree p) = leadingCoeff p ^ Nat.zero
  · simp
    -- 🎉 no goals
  · rw [pow_succ', pow_succ', Nat.succ_mul]
    -- ⊢ coeff (p ^ i * p) (i * natDegree p + natDegree p) = leadingCoeff p ^ i * lea …
    by_cases hp1 : p.leadingCoeff ^ i = 0
    -- ⊢ coeff (p ^ i * p) (i * natDegree p + natDegree p) = leadingCoeff p ^ i * lea …
    · rw [hp1, zero_mul]
      -- ⊢ coeff (p ^ i * p) (i * natDegree p + natDegree p) = 0
      by_cases hp2 : p ^ i = 0
      -- ⊢ coeff (p ^ i * p) (i * natDegree p + natDegree p) = 0
      · rw [hp2, zero_mul, coeff_zero]
        -- 🎉 no goals
      · apply coeff_eq_zero_of_natDegree_lt
        -- ⊢ natDegree (p ^ i * p) < i * natDegree p + natDegree p
        have h1 : (p ^ i).natDegree < i * p.natDegree := by
          refine lt_of_le_of_ne natDegree_pow_le fun h => hp2 ?_
          rw [← h, hp1] at hi
          exact leadingCoeff_eq_zero.mp hi
        calc
          (p ^ i * p).natDegree ≤ (p ^ i).natDegree + p.natDegree := natDegree_mul_le
          _ < i * p.natDegree + p.natDegree := add_lt_add_right h1 _

    · rw [← natDegree_pow' hp1, ← leadingCoeff_pow' hp1]
      -- ⊢ coeff (p ^ i * p) (natDegree (p ^ i) + natDegree p) = leadingCoeff (p ^ i) * …
      exact coeff_mul_degree_add_degree _ _
      -- 🎉 no goals
#align polynomial.coeff_pow_mul_nat_degree Polynomial.coeff_pow_mul_natDegree

theorem coeff_mul_add_eq_of_natDegree_le {df dg : ℕ} {g : R[X]}
    (hdf : natDegree f ≤ df) (hdg : natDegree g ≤ dg) :
    (f * g).coeff (df + dg) = f.coeff df * g.coeff dg := by
  rw [coeff_mul, Finset.sum_eq_single_of_mem (df, dg)]
  -- ⊢ (df, dg) ∈ Nat.antidiagonal (df + dg)
  · rw [Finset.Nat.mem_antidiagonal]
    -- 🎉 no goals
  rintro ⟨df', dg'⟩ hmem hne
  -- ⊢ coeff f (df', dg').fst * coeff g (df', dg').snd = 0
  obtain h | hdf' := lt_or_le df df'
  -- ⊢ coeff f (df', dg').fst * coeff g (df', dg').snd = 0
  · rw [coeff_eq_zero_of_natDegree_lt (hdf.trans_lt h), zero_mul]
    -- 🎉 no goals
  obtain h | hdg' := lt_or_le dg dg'
  -- ⊢ coeff f (df', dg').fst * coeff g (df', dg').snd = 0
  · rw [coeff_eq_zero_of_natDegree_lt (hdg.trans_lt h), mul_zero]
    -- 🎉 no goals
  obtain ⟨rfl, rfl⟩ :=
    eq_and_eq_of_le_of_le_of_add_le hdf' hdg' (Finset.Nat.mem_antidiagonal.1 hmem).ge
  exact (hne rfl).elim
  -- 🎉 no goals

theorem zero_le_degree_iff : 0 ≤ degree p ↔ p ≠ 0 := by
  rw [← not_lt, Nat.WithBot.lt_zero_iff, degree_eq_bot]
  -- 🎉 no goals
#align polynomial.zero_le_degree_iff Polynomial.zero_le_degree_iff

theorem natDegree_eq_zero_iff_degree_le_zero : p.natDegree = 0 ↔ p.degree ≤ 0 := by
  rw [← nonpos_iff_eq_zero, natDegree_le_iff_degree_le, Nat.cast_zero]
  -- 🎉 no goals
#align polynomial.nat_degree_eq_zero_iff_degree_le_zero Polynomial.natDegree_eq_zero_iff_degree_le_zero

theorem degree_zero_le : degree (0 : R[X]) ≤ 0 := natDegree_eq_zero_iff_degree_le_zero.mp rfl

theorem degree_le_iff_coeff_zero (f : R[X]) (n : WithBot ℕ) :
    degree f ≤ n ↔ ∀ m : ℕ, n < m → coeff f m = 0 := by
  -- Porting note: `Nat.cast_withBot` is required.
  simp only [degree, Finset.max, Finset.sup_le_iff, mem_support_iff, Ne.def, ← not_le,
    not_imp_comm, Nat.cast_withBot]
#align polynomial.degree_le_iff_coeff_zero Polynomial.degree_le_iff_coeff_zero

theorem degree_lt_iff_coeff_zero (f : R[X]) (n : ℕ) :
    degree f < n ↔ ∀ m : ℕ, n ≤ m → coeff f m = 0 := by
  simp only [degree, Finset.sup_lt_iff (WithBot.bot_lt_coe n), mem_support_iff,
    WithBot.coe_lt_coe, ← @not_le ℕ, max_eq_sup_coe, Nat.cast_withBot, Ne.def, not_imp_not]
#align polynomial.degree_lt_iff_coeff_zero Polynomial.degree_lt_iff_coeff_zero

theorem degree_smul_le (a : R) (p : R[X]) : degree (a • p) ≤ degree p := by
  refine (degree_le_iff_coeff_zero _ _).2 fun m hm => ?_
  -- ⊢ coeff (a • p) m = 0
  rw [degree_lt_iff_coeff_zero] at hm
  -- ⊢ coeff (a • p) m = 0
  simp [hm m le_rfl]
  -- 🎉 no goals
#align polynomial.degree_smul_le Polynomial.degree_smul_le

theorem natDegree_smul_le (a : R) (p : R[X]) : natDegree (a • p) ≤ natDegree p :=
  natDegree_le_natDegree (degree_smul_le a p)
#align polynomial.nat_degree_smul_le Polynomial.natDegree_smul_le

theorem degree_lt_degree_mul_X (hp : p ≠ 0) : p.degree < (p * X).degree := by
  haveI := Nontrivial.of_polynomial_ne hp
  -- ⊢ degree p < degree (p * X)
  have : leadingCoeff p * leadingCoeff X ≠ 0 := by simpa
  -- ⊢ degree p < degree (p * X)
  erw [degree_mul' this, degree_eq_natDegree hp, degree_X, ← WithBot.coe_one,
    ← WithBot.coe_add, WithBot.coe_lt_coe]; exact Nat.lt_succ_self _
                                            -- 🎉 no goals
#align polynomial.degree_lt_degree_mul_X Polynomial.degree_lt_degree_mul_X

theorem natDegree_pos_iff_degree_pos : 0 < natDegree p ↔ 0 < degree p :=
  lt_iff_lt_of_le_iff_le natDegree_le_iff_degree_le
#align polynomial.nat_degree_pos_iff_degree_pos Polynomial.natDegree_pos_iff_degree_pos

theorem eq_C_of_natDegree_le_zero (h : natDegree p ≤ 0) : p = C (coeff p 0) :=
  eq_C_of_degree_le_zero <| degree_le_of_natDegree_le h
#align polynomial.eq_C_of_nat_degree_le_zero Polynomial.eq_C_of_natDegree_le_zero

theorem eq_C_of_natDegree_eq_zero (h : natDegree p = 0) : p = C (coeff p 0) :=
  eq_C_of_natDegree_le_zero h.le
#align polynomial.eq_C_of_nat_degree_eq_zero Polynomial.eq_C_of_natDegree_eq_zero

theorem eq_C_coeff_zero_iff_natDegree_eq_zero : p = C (p.coeff 0) ↔ p.natDegree = 0 :=
  ⟨fun h ↦ by rw [h, natDegree_C], eq_C_of_natDegree_eq_zero⟩
              -- 🎉 no goals

theorem ne_zero_of_coe_le_degree (hdeg : ↑n ≤ p.degree) : p ≠ 0 :=
  zero_le_degree_iff.mp <| (WithBot.coe_le_coe.mpr n.zero_le).trans hdeg
#align polynomial.ne_zero_of_coe_le_degree Polynomial.ne_zero_of_coe_le_degree

theorem le_natDegree_of_coe_le_degree (hdeg : ↑n ≤ p.degree) : n ≤ p.natDegree :=
  -- Porting note: `.. ▸ ..` → `rwa [..] at ..`
  WithBot.coe_le_coe.mp <| by
    rwa [degree_eq_natDegree <| ne_zero_of_coe_le_degree hdeg] at hdeg
    -- 🎉 no goals
#align polynomial.le_nat_degree_of_coe_le_degree Polynomial.le_natDegree_of_coe_le_degree

theorem degree_sum_fin_lt {n : ℕ} (f : Fin n → R) :
    degree (∑ i : Fin n, C (f i) * X ^ (i : ℕ)) < n :=
  (degree_sum_le _ _).trans_lt <|
    (Finset.sup_lt_iff <| WithBot.bot_lt_coe n).2 fun k _hk =>
      (degree_C_mul_X_pow_le _ _).trans_lt <| WithBot.coe_lt_coe.2 k.is_lt
#align polynomial.degree_sum_fin_lt Polynomial.degree_sum_fin_lt

theorem degree_linear_le : degree (C a * X + C b) ≤ 1 :=
  degree_add_le_of_degree_le (degree_C_mul_X_le _) <| le_trans degree_C_le Nat.WithBot.coe_nonneg
#align polynomial.degree_linear_le Polynomial.degree_linear_le

theorem degree_linear_lt : degree (C a * X + C b) < 2 :=
  degree_linear_le.trans_lt <| WithBot.coe_lt_coe.mpr one_lt_two
#align polynomial.degree_linear_lt Polynomial.degree_linear_lt

theorem degree_C_lt_degree_C_mul_X (ha : a ≠ 0) : degree (C b) < degree (C a * X) := by
  simpa only [degree_C_mul_X ha] using degree_C_lt
  -- 🎉 no goals
#align polynomial.degree_C_lt_degree_C_mul_X Polynomial.degree_C_lt_degree_C_mul_X

@[simp]
theorem degree_linear (ha : a ≠ 0) : degree (C a * X + C b) = 1 := by
  rw [degree_add_eq_left_of_degree_lt <| degree_C_lt_degree_C_mul_X ha, degree_C_mul_X ha]
  -- 🎉 no goals
#align polynomial.degree_linear Polynomial.degree_linear

theorem natDegree_linear_le : natDegree (C a * X + C b) ≤ 1 :=
  natDegree_le_of_degree_le degree_linear_le
#align polynomial.nat_degree_linear_le Polynomial.natDegree_linear_le

theorem natDegree_linear (ha : a ≠ 0) : natDegree (C a * X + C b) = 1 := by
  rw [natDegree_add_C, natDegree_C_mul_X a ha]
  -- 🎉 no goals
#align polynomial.nat_degree_linear Polynomial.natDegree_linear

@[simp]
theorem leadingCoeff_linear (ha : a ≠ 0) : leadingCoeff (C a * X + C b) = a := by
  rw [add_comm, leadingCoeff_add_of_degree_lt (degree_C_lt_degree_C_mul_X ha),
    leadingCoeff_C_mul_X]
#align polynomial.leading_coeff_linear Polynomial.leadingCoeff_linear

theorem degree_quadratic_le : degree (C a * X ^ 2 + C b * X + C c) ≤ 2 := by
  simpa only [add_assoc] using
    degree_add_le_of_degree_le (degree_C_mul_X_pow_le 2 a)
      (le_trans degree_linear_le <| WithBot.coe_le_coe.mpr one_le_two)
#align polynomial.degree_quadratic_le Polynomial.degree_quadratic_le

theorem degree_quadratic_lt : degree (C a * X ^ 2 + C b * X + C c) < 3 :=
  degree_quadratic_le.trans_lt <| WithBot.coe_lt_coe.mpr <| lt_add_one 2
#align polynomial.degree_quadratic_lt Polynomial.degree_quadratic_lt

theorem degree_linear_lt_degree_C_mul_X_sq (ha : a ≠ 0) :
    degree (C b * X + C c) < degree (C a * X ^ 2) := by
  simpa only [degree_C_mul_X_pow 2 ha] using degree_linear_lt
  -- 🎉 no goals
#align polynomial.degree_linear_lt_degree_C_mul_X_sq Polynomial.degree_linear_lt_degree_C_mul_X_sq

@[simp]
theorem degree_quadratic (ha : a ≠ 0) : degree (C a * X ^ 2 + C b * X + C c) = 2 := by
  rw [add_assoc, degree_add_eq_left_of_degree_lt <| degree_linear_lt_degree_C_mul_X_sq ha,
    degree_C_mul_X_pow 2 ha]
  rfl
  -- 🎉 no goals
#align polynomial.degree_quadratic Polynomial.degree_quadratic

theorem natDegree_quadratic_le : natDegree (C a * X ^ 2 + C b * X + C c) ≤ 2 :=
  natDegree_le_of_degree_le degree_quadratic_le
#align polynomial.nat_degree_quadratic_le Polynomial.natDegree_quadratic_le

theorem natDegree_quadratic (ha : a ≠ 0) : natDegree (C a * X ^ 2 + C b * X + C c) = 2 :=
  natDegree_eq_of_degree_eq_some <| degree_quadratic ha
#align polynomial.nat_degree_quadratic Polynomial.natDegree_quadratic

@[simp]
theorem leadingCoeff_quadratic (ha : a ≠ 0) : leadingCoeff (C a * X ^ 2 + C b * X + C c) = a := by
  rw [add_assoc, add_comm, leadingCoeff_add_of_degree_lt <| degree_linear_lt_degree_C_mul_X_sq ha,
    leadingCoeff_C_mul_X_pow]
#align polynomial.leading_coeff_quadratic Polynomial.leadingCoeff_quadratic

theorem degree_cubic_le : degree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) ≤ 3 := by
  simpa only [add_assoc] using
    degree_add_le_of_degree_le (degree_C_mul_X_pow_le 3 a)
      (le_trans degree_quadratic_le <| WithBot.coe_le_coe.mpr <| Nat.le_succ 2)
#align polynomial.degree_cubic_le Polynomial.degree_cubic_le

theorem degree_cubic_lt : degree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) < 4 :=
  degree_cubic_le.trans_lt <| WithBot.coe_lt_coe.mpr <| lt_add_one 3
#align polynomial.degree_cubic_lt Polynomial.degree_cubic_lt

theorem degree_quadratic_lt_degree_C_mul_X_cb (ha : a ≠ 0) :
    degree (C b * X ^ 2 + C c * X + C d) < degree (C a * X ^ 3) := by
  simpa only [degree_C_mul_X_pow 3 ha] using degree_quadratic_lt
  -- 🎉 no goals
#align polynomial.degree_quadratic_lt_degree_C_mul_X_cb Polynomial.degree_quadratic_lt_degree_C_mul_X_cb

@[simp]
theorem degree_cubic (ha : a ≠ 0) : degree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) = 3 := by
  rw [add_assoc, add_assoc, ← add_assoc (C b * X ^ 2),
    degree_add_eq_left_of_degree_lt <| degree_quadratic_lt_degree_C_mul_X_cb ha,
    degree_C_mul_X_pow 3 ha]
  rfl
  -- 🎉 no goals
#align polynomial.degree_cubic Polynomial.degree_cubic

theorem natDegree_cubic_le : natDegree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) ≤ 3 :=
  natDegree_le_of_degree_le degree_cubic_le
#align polynomial.nat_degree_cubic_le Polynomial.natDegree_cubic_le

theorem natDegree_cubic (ha : a ≠ 0) : natDegree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) = 3 :=
  natDegree_eq_of_degree_eq_some <| degree_cubic ha
#align polynomial.nat_degree_cubic Polynomial.natDegree_cubic

@[simp]
theorem leadingCoeff_cubic (ha : a ≠ 0) :
    leadingCoeff (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) = a := by
  rw [add_assoc, add_assoc, ← add_assoc (C b * X ^ 2), add_comm,
    leadingCoeff_add_of_degree_lt <| degree_quadratic_lt_degree_C_mul_X_cb ha,
    leadingCoeff_C_mul_X_pow]
#align polynomial.leading_coeff_cubic Polynomial.leadingCoeff_cubic

end Semiring

section NontrivialSemiring

variable [Semiring R] [Nontrivial R] {p q : R[X]} (n : ℕ)

@[simp]
theorem degree_X_pow : degree ((X : R[X]) ^ n) = n := by
  rw [X_pow_eq_monomial, degree_monomial _ (one_ne_zero' R)]
  -- 🎉 no goals
#align polynomial.degree_X_pow Polynomial.degree_X_pow

@[simp]
theorem natDegree_X_pow : natDegree ((X : R[X]) ^ n) = n :=
  natDegree_eq_of_degree_eq_some (degree_X_pow n)
#align polynomial.nat_degree_X_pow Polynomial.natDegree_X_pow

@[simp] lemma natDegree_mul_X (hp : p ≠ 0) : natDegree (p * X) = natDegree p + 1 := by
  rw [natDegree_mul' (by simpa), natDegree_X]
  -- 🎉 no goals

@[simp] lemma natDegree_X_mul (hp : p ≠ 0) : natDegree (X * p) = natDegree p + 1 := by
  rw [commute_X p, natDegree_mul_X hp]
  -- 🎉 no goals

@[simp] lemma natDegree_mul_X_pow (hp : p ≠ 0) : natDegree (p * X ^ n) = natDegree p + n := by
  rw [natDegree_mul' (by simpa), natDegree_X_pow]
  -- 🎉 no goals

@[simp] lemma natDegree_X_pow_mul (hp : p ≠ 0) : natDegree (X ^ n * p) = natDegree p + n := by
  rw [commute_X_pow, natDegree_mul_X_pow n hp]
  -- 🎉 no goals

--  This lemma explicitly does not require the `Nontrivial R` assumption.
theorem natDegree_X_pow_le {R : Type*} [Semiring R] (n : ℕ) : (X ^ n : R[X]).natDegree ≤ n := by
  nontriviality R
  -- ⊢ natDegree (X ^ n) ≤ n
  rw [Polynomial.natDegree_X_pow]
  -- 🎉 no goals
#align polynomial.nat_degree_X_pow_le Polynomial.natDegree_X_pow_le

theorem not_isUnit_X : ¬IsUnit (X : R[X]) := fun ⟨⟨_, g, _hfg, hgf⟩, rfl⟩ =>
  zero_ne_one' R <| by
    rw [← coeff_one_zero, ← hgf]
    -- ⊢ 0 = coeff (g * ↑(monomial 1) 1) 0
    simp
    -- 🎉 no goals
#align polynomial.not_is_unit_X Polynomial.not_isUnit_X

@[simp]
theorem degree_mul_X : degree (p * X) = degree p + 1 := by simp [monic_X.degree_mul]
                                                           -- 🎉 no goals
#align polynomial.degree_mul_X Polynomial.degree_mul_X

@[simp]
theorem degree_mul_X_pow : degree (p * X ^ n) = degree p + n := by simp [(monic_X_pow n).degree_mul]
                                                                   -- 🎉 no goals
#align polynomial.degree_mul_X_pow Polynomial.degree_mul_X_pow

end NontrivialSemiring

section Ring

variable [Ring R] {p q : R[X]}

theorem degree_sub_le (p q : R[X]) : degree (p - q) ≤ max (degree p) (degree q) := by
  simpa only [degree_neg q] using degree_add_le p (-q)
  -- 🎉 no goals
#align polynomial.degree_sub_le Polynomial.degree_sub_le

theorem degree_sub_le_of_le {a b : WithBot ℕ} (hp : degree p ≤ a) (hq : degree q ≤ b) :
    degree (p - q) ≤ max a b :=
  (p.degree_sub_le q).trans <| max_le_max ‹_› ‹_›

theorem leadingCoeff_sub_of_degree_lt (h : Polynomial.degree q < Polynomial.degree p) :
    (p - q).leadingCoeff = p.leadingCoeff := by
  rw [← q.degree_neg] at h
  -- ⊢ leadingCoeff (p - q) = leadingCoeff p
  rw [sub_eq_add_neg, leadingCoeff_add_of_degree_lt' h]
  -- 🎉 no goals

theorem leadingCoeff_sub_of_degree_lt' (h : Polynomial.degree p < Polynomial.degree q) :
    (p - q).leadingCoeff = -q.leadingCoeff := by
  rw [← q.degree_neg] at h
  -- ⊢ leadingCoeff (p - q) = -leadingCoeff q
  rw [sub_eq_add_neg, leadingCoeff_add_of_degree_lt h, leadingCoeff_neg]
  -- 🎉 no goals

theorem leadingCoeff_sub_of_degree_eq (h : degree p = degree q)
    (hlc : leadingCoeff p ≠ leadingCoeff q) :
    leadingCoeff (p - q) = leadingCoeff p - leadingCoeff q := by
  replace h : degree p = degree (-q) := by rwa [q.degree_neg]
  -- ⊢ leadingCoeff (p - q) = leadingCoeff p - leadingCoeff q
  replace hlc : leadingCoeff p + leadingCoeff (-q) ≠ 0 := by
    rwa [← sub_ne_zero, sub_eq_add_neg, ← q.leadingCoeff_neg] at hlc
  rw [sub_eq_add_neg, leadingCoeff_add_of_degree_eq h hlc, leadingCoeff_neg, sub_eq_add_neg]
  -- 🎉 no goals

theorem natDegree_sub_le (p q : R[X]) : natDegree (p - q) ≤ max (natDegree p) (natDegree q) := by
  simpa only [← natDegree_neg q] using natDegree_add_le p (-q)
  -- 🎉 no goals
#align polynomial.nat_degree_sub_le Polynomial.natDegree_sub_le

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
                                             -- ⊢ WithBot.unbot' 0 (degree p) = WithBot.unbot' 0 (degree q)
                                                               -- 🎉 no goals
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

theorem degree_X_sub_C_le (r : R) : (X - C r).degree ≤ 1 :=
  (degree_sub_le _ _).trans (max_le degree_X_le (degree_C_le.trans zero_le_one))
#align polynomial.degree_X_sub_C_le Polynomial.degree_X_sub_C_le

theorem natDegree_X_sub_C_le (r : R) : (X - C r).natDegree ≤ 1 :=
  natDegree_le_iff_degree_le.2 <| degree_X_sub_C_le r
#align polynomial.nat_degree_X_sub_C_le Polynomial.natDegree_X_sub_C_le

theorem degree_sub_eq_left_of_degree_lt (h : degree q < degree p) : degree (p - q) = degree p := by
  rw [← degree_neg q] at h
  -- ⊢ degree (p - q) = degree p
  rw [sub_eq_add_neg, degree_add_eq_left_of_degree_lt h]
  -- 🎉 no goals
#align polynomial.degree_sub_eq_left_of_degree_lt Polynomial.degree_sub_eq_left_of_degree_lt

theorem degree_sub_eq_right_of_degree_lt (h : degree p < degree q) : degree (p - q) = degree q := by
  rw [← degree_neg q] at h
  -- ⊢ degree (p - q) = degree q
  rw [sub_eq_add_neg, degree_add_eq_right_of_degree_lt h, degree_neg]
  -- 🎉 no goals
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
theorem degree_X_add_C (a : R) : degree (X + C a) = 1 := by
  have : degree (C a) < degree (X : R[X]) :=
    calc
      degree (C a) ≤ 0 := degree_C_le
      _ < 1 := (WithBot.some_lt_some.mpr zero_lt_one)
      _ = degree X := degree_X.symm
  rw [degree_add_eq_left_of_degree_lt this, degree_X]
  -- 🎉 no goals
#align polynomial.degree_X_add_C Polynomial.degree_X_add_C

theorem natDegree_X_add_C (x : R) : (X + C x).natDegree = 1 :=
  natDegree_eq_of_degree_eq_some <| degree_X_add_C x
#align polynomial.nat_degree_X_add_C Polynomial.natDegree_X_add_C

@[simp]
theorem nextCoeff_X_add_C [Semiring S] (c : S) : nextCoeff (X + C c) = c := by
  nontriviality S
  -- ⊢ nextCoeff (X + ↑C c) = c
  simp [nextCoeff_of_pos_natDegree]
  -- 🎉 no goals
#align polynomial.next_coeff_X_add_C Polynomial.nextCoeff_X_add_C

theorem degree_X_pow_add_C {n : ℕ} (hn : 0 < n) (a : R) : degree ((X : R[X]) ^ n + C a) = n := by
  have : degree (C a) < degree ((X : R[X]) ^ n) := degree_C_le.trans_lt <| by
    rwa [degree_X_pow, Nat.cast_pos]
  rw [degree_add_eq_left_of_degree_lt this, degree_X_pow]
  -- 🎉 no goals
#align polynomial.degree_X_pow_add_C Polynomial.degree_X_pow_add_C

theorem X_pow_add_C_ne_zero {n : ℕ} (hn : 0 < n) (a : R) : (X : R[X]) ^ n + C a ≠ 0 :=
  mt degree_eq_bot.2
    (show degree ((X : R[X]) ^ n + C a) ≠ ⊥ by
      rw [degree_X_pow_add_C hn a]; exact WithBot.coe_ne_bot)
      -- ⊢ ↑n ≠ ⊥
                                    -- 🎉 no goals
#align polynomial.X_pow_add_C_ne_zero Polynomial.X_pow_add_C_ne_zero

theorem X_add_C_ne_zero (r : R) : X + C r ≠ 0 :=
  pow_one (X : R[X]) ▸ X_pow_add_C_ne_zero zero_lt_one r
#align polynomial.X_add_C_ne_zero Polynomial.X_add_C_ne_zero

theorem zero_nmem_multiset_map_X_add_C {α : Type*} (m : Multiset α) (f : α → R) :
    (0 : R[X]) ∉ m.map fun a => X + C (f a) := fun mem =>
  let ⟨_a, _, ha⟩ := Multiset.mem_map.mp mem
  X_add_C_ne_zero _ ha
#align polynomial.zero_nmem_multiset_map_X_add_C Polynomial.zero_nmem_multiset_map_X_add_C

theorem natDegree_X_pow_add_C {n : ℕ} {r : R} : (X ^ n + C r).natDegree = n := by
  by_cases hn : n = 0
  -- ⊢ natDegree (X ^ n + ↑C r) = n
  · rw [hn, pow_zero, ← C_1, ← RingHom.map_add, natDegree_C]
    -- 🎉 no goals
  · exact natDegree_eq_of_degree_eq_some (degree_X_pow_add_C (pos_iff_ne_zero.mpr hn) r)
    -- 🎉 no goals
#align polynomial.nat_degree_X_pow_add_C Polynomial.natDegree_X_pow_add_C

theorem X_pow_add_C_ne_one {n : ℕ} (hn : 0 < n) (a : R) : (X : R[X]) ^ n + C a ≠ 1 := fun h =>
  hn.ne' <| by simpa only [natDegree_X_pow_add_C, natDegree_one] using congr_arg natDegree h
               -- 🎉 no goals
#align polynomial.X_pow_add_C_ne_one Polynomial.X_pow_add_C_ne_one

theorem X_add_C_ne_one (r : R) : X + C r ≠ 1 :=
  pow_one (X : R[X]) ▸ X_pow_add_C_ne_one zero_lt_one r
#align polynomial.X_add_C_ne_one Polynomial.X_add_C_ne_one

end Semiring

end NonzeroRing

section Semiring

variable [Semiring R]

@[simp]
theorem leadingCoeff_X_pow_add_C {n : ℕ} (hn : 0 < n) {r : R} :
    (X ^ n + C r).leadingCoeff = 1 := by
  nontriviality R
  -- ⊢ leadingCoeff (X ^ n + ↑C r) = 1
  rw [leadingCoeff, natDegree_X_pow_add_C, coeff_add, coeff_X_pow_self, coeff_C,
    if_neg (pos_iff_ne_zero.mp hn), add_zero]
#align polynomial.leading_coeff_X_pow_add_C Polynomial.leadingCoeff_X_pow_add_C

@[simp]
theorem leadingCoeff_X_add_C [Semiring S] (r : S) : (X + C r).leadingCoeff = 1 := by
  rw [← pow_one (X : S[X]), leadingCoeff_X_pow_add_C zero_lt_one]
  -- 🎉 no goals
#align polynomial.leading_coeff_X_add_C Polynomial.leadingCoeff_X_add_C

@[simp]
theorem leadingCoeff_X_pow_add_one {n : ℕ} (hn : 0 < n) : (X ^ n + 1 : R[X]).leadingCoeff = 1 :=
  leadingCoeff_X_pow_add_C hn
#align polynomial.leading_coeff_X_pow_add_one Polynomial.leadingCoeff_X_pow_add_one

@[simp]
theorem leadingCoeff_pow_X_add_C (r : R) (i : ℕ) : leadingCoeff ((X + C r) ^ i) = 1 := by
  nontriviality
  -- ⊢ leadingCoeff ((X + ↑C r) ^ i) = 1
  rw [leadingCoeff_pow'] <;> simp
  -- ⊢ leadingCoeff (X + ↑C r) ^ i = 1
                             -- 🎉 no goals
                             -- 🎉 no goals
#align polynomial.leading_coeff_pow_X_add_C Polynomial.leadingCoeff_pow_X_add_C

end Semiring

section Ring

variable [Ring R]

@[simp]
theorem leadingCoeff_X_pow_sub_C {n : ℕ} (hn : 0 < n) {r : R} :
    (X ^ n - C r).leadingCoeff = 1 := by
  rw [sub_eq_add_neg, ← map_neg C r, leadingCoeff_X_pow_add_C hn]
  -- 🎉 no goals
#align polynomial.leading_coeff_X_pow_sub_C Polynomial.leadingCoeff_X_pow_sub_C

@[simp]
theorem leadingCoeff_X_pow_sub_one {n : ℕ} (hn : 0 < n) : (X ^ n - 1 : R[X]).leadingCoeff = 1 :=
  leadingCoeff_X_pow_sub_C hn
#align polynomial.leading_coeff_X_pow_sub_one Polynomial.leadingCoeff_X_pow_sub_one

variable [Nontrivial R]

@[simp]
theorem degree_X_sub_C (a : R) : degree (X - C a) = 1 := by
  rw [sub_eq_add_neg, ← map_neg C a, degree_X_add_C]
  -- 🎉 no goals
#align polynomial.degree_X_sub_C Polynomial.degree_X_sub_C

@[simp]
theorem natDegree_X_sub_C (x : R) : (X - C x).natDegree = 1 :=
  natDegree_eq_of_degree_eq_some <| degree_X_sub_C x
#align polynomial.nat_degree_X_sub_C Polynomial.natDegree_X_sub_C

@[simp]
theorem nextCoeff_X_sub_C [Ring S] (c : S) : nextCoeff (X - C c) = -c := by
  rw [sub_eq_add_neg, ← map_neg C c, nextCoeff_X_add_C]
  -- 🎉 no goals
#align polynomial.next_coeff_X_sub_C Polynomial.nextCoeff_X_sub_C

theorem degree_X_pow_sub_C {n : ℕ} (hn : 0 < n) (a : R) : degree ((X : R[X]) ^ n - C a) = n := by
  rw [sub_eq_add_neg, ← map_neg C a, degree_X_pow_add_C hn]
  -- 🎉 no goals
#align polynomial.degree_X_pow_sub_C Polynomial.degree_X_pow_sub_C

theorem X_pow_sub_C_ne_zero {n : ℕ} (hn : 0 < n) (a : R) : (X : R[X]) ^ n - C a ≠ 0 := by
  rw [sub_eq_add_neg, ← map_neg C a]
  -- ⊢ X ^ n + ↑C (-a) ≠ 0
  exact X_pow_add_C_ne_zero hn _
  -- 🎉 no goals
#align polynomial.X_pow_sub_C_ne_zero Polynomial.X_pow_sub_C_ne_zero

theorem X_sub_C_ne_zero (r : R) : X - C r ≠ 0 :=
  pow_one (X : R[X]) ▸ X_pow_sub_C_ne_zero zero_lt_one r
#align polynomial.X_sub_C_ne_zero Polynomial.X_sub_C_ne_zero

theorem zero_nmem_multiset_map_X_sub_C {α : Type*} (m : Multiset α) (f : α → R) :
    (0 : R[X]) ∉ m.map fun a => X - C (f a) := fun mem =>
  let ⟨_a, _, ha⟩ := Multiset.mem_map.mp mem
  X_sub_C_ne_zero _ ha
#align polynomial.zero_nmem_multiset_map_X_sub_C Polynomial.zero_nmem_multiset_map_X_sub_C

theorem natDegree_X_pow_sub_C {n : ℕ} {r : R} : (X ^ n - C r).natDegree = n := by
  rw [sub_eq_add_neg, ← map_neg C r, natDegree_X_pow_add_C]
  -- 🎉 no goals
#align polynomial.nat_degree_X_pow_sub_C Polynomial.natDegree_X_pow_sub_C

@[simp]
theorem leadingCoeff_X_sub_C [Ring S] (r : S) : (X - C r).leadingCoeff = 1 := by
  rw [sub_eq_add_neg, ← map_neg C r, leadingCoeff_X_add_C]
  -- 🎉 no goals
#align polynomial.leading_coeff_X_sub_C Polynomial.leadingCoeff_X_sub_C

end Ring

section NoZeroDivisors

variable [Semiring R] [NoZeroDivisors R] {p q : R[X]}

@[simp]
theorem degree_mul : degree (p * q) = degree p + degree q :=
  if hp0 : p = 0 then by simp only [hp0, degree_zero, zero_mul, WithBot.bot_add]
                         -- 🎉 no goals
  else
    if hq0 : q = 0 then by simp only [hq0, degree_zero, mul_zero, WithBot.add_bot]
                           -- 🎉 no goals
    else degree_mul' <| mul_ne_zero (mt leadingCoeff_eq_zero.1 hp0) (mt leadingCoeff_eq_zero.1 hq0)
#align polynomial.degree_mul Polynomial.degree_mul

/-- `degree` as a monoid homomorphism between `R[X]` and `Multiplicative (WithBot ℕ)`.
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
theorem leadingCoeff_mul (p q : R[X]) : leadingCoeff (p * q) = leadingCoeff p * leadingCoeff q := by
  by_cases hp : p = 0
  -- ⊢ leadingCoeff (p * q) = leadingCoeff p * leadingCoeff q
  · simp only [hp, zero_mul, leadingCoeff_zero]
    -- 🎉 no goals
  · by_cases hq : q = 0
    -- ⊢ leadingCoeff (p * q) = leadingCoeff p * leadingCoeff q
    · simp only [hq, mul_zero, leadingCoeff_zero]
      -- 🎉 no goals
    · rw [leadingCoeff_mul']
      -- ⊢ leadingCoeff p * leadingCoeff q ≠ 0
      exact mul_ne_zero (mt leadingCoeff_eq_zero.1 hp) (mt leadingCoeff_eq_zero.1 hq)
      -- 🎉 no goals
#align polynomial.leading_coeff_mul Polynomial.leadingCoeff_mul

/-- `Polynomial.leadingCoeff` bundled as a `MonoidHom` when `R` has `NoZeroDivisors`, and thus
  `leadingCoeff` is multiplicative -/
def leadingCoeffHom : R[X] →* R where
  toFun := leadingCoeff
  map_one' := by simp
                 -- 🎉 no goals
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
