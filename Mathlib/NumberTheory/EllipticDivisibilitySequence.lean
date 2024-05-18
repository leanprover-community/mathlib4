/-
Copyright (c) 2024 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import Init.Data.Int.DivModLemmas
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Int.Parity
import Mathlib.GroupTheory.Perm.ClosureSwap
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Elliptic divisibility sequences

This file defines the type of an elliptic divisibility sequence (EDS) and a few examples.

## Mathematical background

Let $R$ be a commutative ring. An elliptic sequence is a sequence $W : \mathbb{Z} \to R$ satisfying
$$ W(m + n)W(m - n)W(r)^2 = W(m + r)W(m - r)W(n)^2 - W(n + r)W(n - r)W(m)^2, $$
for any $m, n, r \in \mathbb{Z}$. A divisibility sequence is a sequence $W : \mathbb{Z} \to R$
satisfying $W(m) \mid W(n)$ for any $m, n \in \mathbb{Z}$ such that $m \mid n$.

Some examples of EDSs include
 * the identity sequence,
 * certain terms of Lucas sequences, and
 * division polynomials of elliptic curves.

## Main definitions

 * `IsEllSequence`: a sequence indexed by integers is an elliptic sequence.
 * `IsDivSequence`: a sequence indexed by integers is a divisibility sequence.
 * `IsEllDivSequence`: a sequence indexed by integers is an EDS.
 * `preNormEDS'`: the auxiliary sequence for a normalised EDS indexed by `ℕ`.
 * `preNormEDS`: the auxiliary sequence for a normalised EDS indexed by `ℤ`.
 * `normEDS`: the canonical example of a normalised EDS indexed by `ℤ`.

## Main statements

 * `isEllDivSequence_normEDS`: `normEDS` satisfies `IsEllDivSequence`.
 * TODO: prove that a normalised sequence satisfying `IsEllDivSequence` can be given by `normEDS`,
   at least when `W 2` is not a zero divisor.

## Implementation notes

The normalised EDS `normEDS b c d n` is defined in terms of the auxiliary sequence
`preNormEDS (b ^ 4) c d n`, which are equal when `n` is odd, and which differ by a factor of `b`
when `n` is even. This coincides with the definition in the references since both agree for
`normEDS b c d 2` and for `normEDS b c d 4`, and the correct factors of `b` are removed in
`normEDS b c d (2 * (m + 2) + 1)` and in `normEDS b c d (2 * (m + 3))`.

One reason is to avoid the necessity for ring division by `b` in the inductive definition of
`normEDS b c d (2 * (m + 3))`. The idea is that, it can be shown that `normEDS b c d (2 * (m + 3))`
always contains a factor of `b`, so it is possible to remove a factor of `b` *a posteriori*, but
stating this lemma requires first defining `normEDS b c d (2 * (m + 3))`, which requires having this
factor of `b` *a priori*. Another reason is to allow the definition of univariate $n$-division
polynomials of elliptic curves, omitting a factor of the bivariate $2$-division polynomial.

## References

M Ward, *Memoir on Elliptic Divisibility Sequences*

## Tags

elliptic, divisibility, sequence
-/

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : ℤ → R)
variable {F} [FunLike F R S] [RingHomClass F R S] (f : F)

open scoped nonZeroDivisors

namespace EllSequence

/-- The expression `W((m+n)/2) * W((m-n)/2)`, intended to apply to integers `m` and `n`
have the same parity. -/
def addMulSub (m n : ℤ) : R := W ((m + n).div 2) * W ((m - n).div 2)
-- Implementation note: we use `Int.div _ 2` instead of `_ / 2` so that `(-m).div 2 = -(m.div 2)`
-- and lemmas like `addMulSub_neg₀` hold unconditionally, even though in the case we care about
-- (`m` and `n` both even or both odd) both are equal.

def rel₄ (a b c d : ℤ) : R :=
  addMulSub W a b * addMulSub W c d
    - addMulSub W a c * addMulSub W b d + addMulSub W a d * addMulSub W b c

lemma addMulSub_two_zero : addMulSub W 2 0 = W 1 ^ 2 := (sq _).symm
lemma addMulSub_three_one : addMulSub W 3 1 = W 2 * W 1 := rfl

lemma addMulSub_even (m n : ℤ) : addMulSub W (2 * m) (2 * n) = W (m + n) * W (m - n) := by
  simp_rw [addMulSub, ← left_distrib, ← mul_sub_left_distrib, Int.mul_div_cancel_left _ two_ne_zero]

lemma addMulSub_odd (m n : ℤ) :
    addMulSub W (2 * m + 1) (2 * n + 1) = W (m + n + 1) * W (m - n) := by
  have h k := Int.mul_div_cancel_left k two_ne_zero
  rw [addMulSub, ← h (m + n + 1), ← h (m - n)]; congr <;> ring

lemma addMulSub_same (zero : W 0 = 0) (m : ℤ) : addMulSub W m m = 0 := by
  rw [addMulSub, sub_self, Int.zero_div, zero, mul_zero]

lemma addMulSub_neg₀ (neg : ∀ k, W (-k) = -W k) (m n : ℤ) :
    addMulSub W (-m) n = addMulSub W m n := by
  simp_rw [addMulSub, ← neg_add', neg_add_eq_sub, ← neg_sub m, Int.neg_div, neg]; ring

lemma addMulSub_neg₁ (m n : ℤ) : addMulSub W m (-n) = addMulSub W m n := by
  rw [addMulSub, addMulSub, mul_comm]; abel_nf

lemma addMulSub_abs₁ (m n : ℤ) : addMulSub W m |n| = addMulSub W m n := by
  obtain h | h := abs_choice n <;> simp only [h, addMulSub_neg₁]

lemma addMulSub_swap (neg : ∀ k, W (-k) = -W k) (m n : ℤ) : addMulSub W m n = - addMulSub W n m := by
  rw [addMulSub, addMulSub, ← neg_sub, Int.neg_div, neg]; ring_nf

section transf

variable (a b c d e : ℤ)

/-- The first entry of the transformation of the quadruple (a,b,c,d). -/
def transf₁ : ℤ := (a + b + c - d) / 2
/-- The second entry of the transformation of the quadruple (a,b,c,d). -/
def transf₂ : ℤ := (a + b + d - c) / 2
/-- The third entry of the transformation of the quadruple (a,b,c,d). -/
def transf₃ : ℤ := (a + c + d - b) / 2
/-- The fourth entry of the transformation of the quadruple (a,b,c,d). -/
def transf₄ : ℤ := (b + c + d - a) / 2

def addMulSub₄ : R := W ((a + b).div 2) * W ((c - d).div 2)

lemma addMulSub₄_mul_addMulSub₄ :
    addMulSub₄ W a b c d * addMulSub₄ W c d a b = addMulSub W a b * addMulSub W c d := by
  simp_rw [addMulSub₄, addMulSub]; ring

def StrictAnti₄ : Prop := 0 ≤ d ∧ d < c ∧ c < b ∧ b < a

def HaveSameParity₄ : Prop :=
  a.negOnePow = b.negOnePow ∧ b.negOnePow = c.negOnePow ∧ c.negOnePow = d.negOnePow

namespace HaveSameParity₄
open Int

variable {a b c d} (same : HaveSameParity₄ a b c d)

lemma same₀₃ : a.negOnePow = d.negOnePow := by rw [same.1, same.2.1, same.2.2]

lemma six_le_of_strictAnti₄ (anti : StrictAnti₄ a b c d) : 6 ≤ a := by
  simp_rw [HaveSameParity₄, negOnePow_eq_iff] at same
  obtain ⟨hd, hdc, hcb, hba⟩ := anti
  rw [lt_iff_add_two_le_of_even_sub] at hdc hcb hba
  · linarith
  exacts [same.1, same.2.1, same.2.2]

lemma two_dvd :
    2 ∣ (a + b + c - d) ∧ 2 ∣ (a + b + d - c) ∧ 2 ∣ (a + c + d - b) ∧ 2 ∣ (b + c + d - a) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp_rw [← even_iff_two_dvd, ← negOnePow_eq_one_iff, negOnePow_sub, negOnePow_add,
    same.1, same.2.1, same.2.2, negOnePow_mul_negOnePow_self, one_mul, negOnePow_mul_negOnePow_self]

lemma addMulSub_transf :
    addMulSub W (transf₁ a b c d) (transf₂ a b c d) = addMulSub₄ W a b c d ∧
      addMulSub W (transf₁ a b c d) (transf₃ a b c d) = addMulSub₄ W a c b d ∧
      addMulSub W (transf₁ a b c d) |transf₄ a b c d| = addMulSub₄ W b c a d ∧
      addMulSub W (transf₂ a b c d) (transf₃ a b c d) = addMulSub₄ W a d b c ∧
      addMulSub W (transf₂ a b c d) |transf₄ a b c d| = addMulSub₄ W b d a c ∧
      addMulSub W (transf₃ a b c d) |transf₄ a b c d| = addMulSub₄ W c d a b := by
  simp_rw [transf₁, transf₂, transf₃, transf₄, addMulSub_abs₁, addMulSub, addMulSub₄]
  obtain ⟨-, h₂, h₃, h₄⟩ := two_dvd same
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [← add_ediv_of_dvd_right ‹_›, ← sub_ediv_of_dvd _ ‹_›]
    congr <;> apply Int.ediv_eq_of_eq_mul_left two_ne_zero <;> ring

theorem rel₄_transf :
    rel₄ W (transf₁ a b c d) (transf₂ a b c d) (transf₃ a b c d) |transf₄ a b c d| =
      rel₄ W a b c d := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := same.addMulSub_transf W
  simp_rw [rel₄, h₁, h₂, h₃, h₄, h₅, h₆, addMulSub₄_mul_addMulSub₄, mul_comm]

lemma transf_sub_adj :
    transf₁ a b c d - transf₂ a b c d = c - d ∧
      transf₂ a b c d - transf₃ a b c d = b - c ∧
      transf₃ a b c d - transf₄ a b c d = a - b := by
  obtain ⟨_, _, _, _⟩ := two_dvd same
  rw [transf₁, transf₂, transf₃, transf₄]
  refine ⟨?_, ?_, ?_⟩
  all_goals rw [← sub_ediv_of_dvd _ ‹_›]; apply Int.ediv_eq_of_eq_mul_left two_ne_zero; ring

lemma transf :
    HaveSameParity₄ (transf₁ a b c d) (transf₂ a b c d) (transf₃ a b c d) |transf₄ a b c d| := by
  obtain ⟨h₁, h₂, h₃⟩ := transf_sub_adj same
  simp_rw [HaveSameParity₄, negOnePow_abs, negOnePow_eq_iff, h₁, h₂, h₃, ← negOnePow_eq_iff]
  exact ⟨same.2.2, same.2.1, same.1⟩

lemma strictAnti₄_transf (anti : StrictAnti₄ a b c d) :
    StrictAnti₄ (transf₁ a b c d) (transf₂ a b c d) (transf₃ a b c d) |transf₄ a b c d| := by
  obtain ⟨hd, hdc, hcb, hba⟩ := anti
  obtain ⟨h₁, h₂, h₃⟩ := transf_sub_adj same
  refine ⟨abs_nonneg _, abs_lt.mpr ⟨?_, ?_⟩, ?_, ?_⟩ <;> rw [← sub_pos]
  · rw [sub_neg_eq_add, transf₃, transf₄, ← add_ediv_of_dvd_right (two_dvd same).2.2.1]
    exact (add_pos_of_pos_of_nonneg (hd.trans_lt hdc) hd).trans_eq
      (Int.ediv_eq_of_eq_mul_left two_ne_zero <| by ring).symm
  all_goals simp only [h₁, h₂, h₃, sub_pos, hba, hcb, hdc]

end HaveSameParity₄

end transf

def relFin4 (t : Fin 4 → ℤ) : R := rel₄ W (t 0) (t 1) (t 2) (t 3)

def rel₆ (k l a b c d : ℤ) : R := addMulSub W k l * rel₄ W a b c d

def Rel₃ (m n r : ℤ) : Prop :=
  W (m + n) * W (m - n) * W r ^ 2 =
    W (m + r) * W (m - r) * W n ^ 2 - W (n + r) * W (n - r) * W m ^ 2

lemma rel₃_iff₄ (m n r : ℤ) :
    Rel₃ W m n r ↔ rel₄ W (2 * m) (2 * n) (2 * r) 0 = 0 := by
  rw [rel₄, ← mul_zero 2, Rel₃]
  simp_rw [addMulSub_even, add_zero, sub_zero]
  convert sub_eq_zero.symm using 2; ring

lemma rel₆_eq₃ (c d m n r : ℤ) :
    rel₆ W c d m n r c = rel₆ W r c m n c d - rel₆ W n c m r c d + rel₆ W m c n r c d := by
  simp_rw [rel₆, rel₄]; ring

lemma rel₆_eq₃' (c d m n r : ℤ) :
    rel₆ W c d m n r d = rel₆ W r d m n c d - rel₆ W n d m r c d + rel₆ W m d n r c d := by
  simp_rw [rel₆, rel₄]; ring

theorem rel₆_eq₁₀ (c d m n r s : ℤ) :
    rel₆ W c d m n r s =
      rel₆ W n d m r s c - rel₆ W r d m n s c + rel₆ W s d m n r c
      + rel₆ W n c m r s d - rel₆ W r c m n s d + rel₆ W s c m n r d
      + rel₆ W n r m s c d - rel₆ W n s m r c d + rel₆ W r s m n c d
      - 2 * rel₆ W m d n r s c := by
  simp_rw [rel₆, rel₄]; ring

section recurrence

def OddRec (m : ℤ) : Prop :=
  W (2 * m + 1) * W 1 ^ 3 = W (m + 2) * W m ^ 3 - W (m - 1) * W (m + 1) ^ 3

def EvenRec (m : ℤ) : Prop :=
  W (2 * m) * W 2 * W 1 ^ 2 = W m * (W (m - 1) ^ 2 * W (m + 2) - W (m - 2) * W (m + 1) ^ 2)

lemma rel₃_iff_oddRec (m : ℤ) : Rel₃ W (m + 1) m 1 ↔ OddRec W m := by
  rw [Rel₃, OddRec]; ring_nf

lemma rel₃_iff_evenRec (m : ℤ) : Rel₃ W (m + 1) (m - 1) 1 ↔ EvenRec W m := by
  rw [Rel₃, EvenRec]; ring_nf

lemma rel₄_iff_evenRec (m : ℤ) : rel₄ W (2 * m + 1) (2 * m - 1) 3 1 = 0 ↔ EvenRec W m := by
  rw [iff_comm, EvenRec, ← sub_eq_zero, show 2 * m - 1 = 2 * (m - 1) + 1 by ring]
  convert_to _ ↔ rel₄ W _ _ (2 * 1 + 1) (2 * 0 + 1) = 0
  simp_rw [rel₄, addMulSub_odd]; ring_nf

def dMin (a : ℤ) : ℤ := if Even a then 0 else 1
def cMin (a : ℤ) : ℤ := dMin a + 2

lemma dMin_nonneg (a : ℤ) : 0 ≤ dMin a := by rw [dMin]; split_ifs <;> decide

lemma dMin_lt_cMin (a : ℤ) : dMin a < cMin a := lt_add_of_pos_right _ zero_lt_two

lemma negOnePow_cMin_eq_dMin (a : ℤ) : (cMin a).negOnePow = (dMin a).negOnePow := by
  rw [cMin, Int.negOnePow_add]; exact mul_one _

lemma negOnePow_dMin (a : ℤ) : (dMin a).negOnePow = a.negOnePow := by
  rw [dMin]; split_ifs with h <;> simp [h, Int.negOnePow_even, Int.negOnePow_odd]

lemma negOnePow_cMin (a : ℤ) : (cMin a).negOnePow = a.negOnePow := by
  rw [negOnePow_cMin_eq_dMin, negOnePow_dMin]

variable {W}
lemma addMulSub_mem_nonZeroDivisors (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰) (a : ℤ) :
    addMulSub W (cMin a) (dMin a) ∈ R⁰ := by
  rw [cMin, dMin]; split_ifs; exacts [mul_mem one one, mul_mem two one]

variable {a b : ℤ} (same : a.negOnePow = b.negOnePow)

lemma dMin_le (h : 0 ≤ b) : dMin a ≤ b := by
  rw [dMin]; split_ifs with odd
  exacts [h, h.lt_of_ne (by rintro rfl; exact odd (a.negOnePow_eq_one_iff.mp same))]

-- lemma cMin_le

end recurrence

open Int

section Rel₄OfValid

def Rel₄OfValid (a b c d : ℤ) : Prop :=
  HaveSameParity₄ a b c d → StrictAnti₄ a b c d → rel₄ W a b c d = 0

variable {W} {a c₀ d₀ : ℤ} (par : c₀.negOnePow = d₀.negOnePow) (le : 0 ≤ d₀) (lt : d₀ < c₀)
  (rel : ∀ {a' b}, a' ≤ a → Rel₄OfValid W a' b c₀ d₀) (mem : addMulSub W c₀ d₀ ∈ R⁰)

lemma rel₄_fix₁_of_fix₂ (b c : ℤ) :
    Rel₄OfValid W a b c c₀ ∧ (c₀ < c → Rel₄OfValid W a b c d₀) := by
  refine ⟨fun same anti ↦ mem _ ?_, fun hc same anti ↦ mem _ ?_⟩ <;> rw [mul_comm, ← rel₆]
  on_goal 1 => rw [rel₆_eq₃]; have hc := trivial
  on_goal 2 => rw [rel₆_eq₃']
  all_goals simp_rw [rel₆]; rw [rel le_rfl, rel le_rfl, rel anti.2.2.2.le]
  iterate 2
    simp_rw [mul_zero, add_zero, sub_zero]
    iterate 3
      simp only [HaveSameParity₄, par, same.1, same.2.1, same.2.2, true_and]
      refine ⟨le, lt, ?_, ?_⟩ <;> linarith only [hc, anti.2.1, anti.2.2.1, anti.2.2.2]

lemma rel₄_of_fix₂ (b c d : ℤ) (hc : c₀ < d) (par' : d.negOnePow = d₀.negOnePow) :
    Rel₄OfValid W a b c d := fun same ⟨_, hdc, hcb, hba⟩ ↦ mem _ <| by
  rw [mul_comm, ← rel₆, rel₆_eq₁₀]; simp_rw [rel₆]
  have fix₁ b c := (rel₄_fix₁_of_fix₂ par le lt rel mem b c).1
  have fix₂ {b c} := (rel₄_fix₁_of_fix₂ par le lt rel mem b c).2
  rw [fix₁, fix₁, fix₁, fix₂ hc, fix₂ hc, fix₂ (hc.trans hdc), rel le_rfl, rel le_rfl,
    rel le_rfl, (rel₄_fix₁_of_fix₂ par le lt (fun h ↦ rel <| h.trans hba.le) mem _ _).1]
  · simp_rw [mul_zero, add_zero, sub_zero]
  iterate 10
    simp only [HaveSameParity₄, par, par', same.1, same.2.1, same.2.2, true_and]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith only [hc, le, lt, hdc, hcb, hba]

theorem rel₄_of_min (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (rel : ∀ {a' b}, a' ≤ a → Rel₄OfValid W a' b (cMin a) (dMin a))
    (b c d : ℤ) : Rel₄OfValid W a b c d := fun same anti ↦ by
  obtain hc|hc := lt_or_le (cMin a) d
  · refine rel₄_of_fix₂ (negOnePow_cMin_eq_dMin a) (dMin_nonneg a) (dMin_lt_cMin a) rel
      (addMulSub_mem_nonZeroDivisors one two a) _ _ _ hc ?_ same anti
    rw [negOnePow_dMin, same.1, same.2.1, same.2.2]
  have fix := rel₄_fix₁_of_fix₂ (negOnePow_cMin_eq_dMin a) (dMin_nonneg a) (dMin_lt_cMin a) rel
    (addMulSub_mem_nonZeroDivisors one two a) b c
  obtain rfl|hc := hc.eq_or_lt
  · exact fix.1 same anti
  obtain rfl : dMin a = d := (dMin_le same.same₀₃ anti.1).antisymm <| by
    rwa [lt_iff_add_two_le_of_even_sub, cMin, add_le_add_iff_right] at hc
    rw [← negOnePow_eq_iff, negOnePow_cMin, same.same₀₃]
  obtain rfl|hc : cMin a = c ∨ _ := ((lt_iff_add_two_le_of_even_sub <| by
    rw [← negOnePow_eq_iff, negOnePow_dMin, same.1, same.2.1]).mp anti.2.1).eq_or_lt
  exacts [rel le_rfl same anti, fix.2 hc same anti]

end Rel₄OfValid

/-- The main inductive argument. -/
theorem rel₄_of_oddRec_evenRec (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (oddRec : ∀ m ≥ 2, OddRec W m) (evenRec : ∀ m ≥ 3, EvenRec W m) :
    ∀ a b c d : ℤ, Rel₄OfValid W a b c d :=
  -- apply induction on `a`
  strong_induction 6 -- if `a < 6` the conclusion holds vacuously
    (fun a ha b c d same anti ↦ ((same.six_le_of_strictAnti₄ anti).not_lt ha).elim)
    -- otherwise, it suffices to deal with the "minimal" case `c = cMin a` and `d = dMin a`
    fun a h6 ih ↦ rel₄_of_min one two fun {a' b} haa same anti ↦ by
  obtain ha'|ha' := haa.lt_or_eq
  · -- if `a' < a`, apply the inductive hypothesis
    exact ih _ ha' _ _ _ same anti
  obtain hba|rfl := lt_or_eq_of_le <| show b + 2 ≤ a' from
    (lt_iff_add_two_le_of_even_sub <| (negOnePow_eq_iff _ _).1 same.1).1 anti.2.2.2
  · -- if `b + 2 < a'`, apply `transf` and then the inductive hypothesis is applicable
    rw [← same.rel₄_transf]
    refine ih _ ?_ _ _ _ same.transf (same.strictAnti₄_transf anti)
    rw [transf₁, Int.ediv_lt_iff_lt_mul zero_lt_two, ← ha', cMin]
    linarith only [hba]
  obtain ⟨m, rfl|rfl⟩ := b.even_or_odd'
  -- the `b + 2 = a'` case is handled by oddRec or evenRec depending on the parity of `b`
  · have ea : Even a := by rw [← ha']; exact (even_two_mul _).add even_two
    simp_rw [cMin, dMin, if_pos ea]
    convert (rel₃_iff₄ W (m + 1) m 1).mp ((rel₃_iff_oddRec W m).mpr <| oddRec _ ?_) using 2
    · ring
    · linarith only [h6, ha']
  · have nea : ¬ Even a := by
      rw [← ha', ← Int.odd_iff_not_even]; convert odd_two_mul_add_one (m + 1) using 1; ring
    simp_rw [cMin, dMin, if_neg nea]
    convert (rel₄_iff_evenRec W (m + 1)).mpr (evenRec _ ?_) using 2
    on_goal 3 => linarith only [h6, ha']
    all_goals ring

section

variable (neg : ∀ k, W (-k) = -W k)

lemma rel₄_neg₀ (m n r s : ℤ) : rel₄ W (-m) n r s = rel₄ W m n r s := by
  simp_rw [rel₄, addMulSub_neg₀ W neg]

lemma rel₄_neg₁ (m n r s : ℤ) : rel₄ W m (-n) r s = rel₄ W m n r s := by
  simp_rw [rel₄, addMulSub_neg₀ W neg, addMulSub_neg₁]

lemma rel₄_neg₂ (m n r s : ℤ) : rel₄ W m n (-r) s = rel₄ W m n r s := by
  simp_rw [rel₄, addMulSub_neg₀ W neg, addMulSub_neg₁]

lemma rel₄_neg₃ (m n r s : ℤ) : rel₄ W m n r (-s) = rel₄ W m n r s := by
  simp_rw [rel₄, addMulSub_neg₁]

lemma rel₄_swap₀₁ (m n r s : ℤ) : rel₄ W m n r s = - rel₄ W n m r s := by
  simp_rw [rel₄, addMulSub_swap W neg n m]; ring

lemma rel₄_swap₁₂ (m n r s : ℤ) : rel₄ W m n r s = - rel₄ W m r n s := by
  simp_rw [rel₄, addMulSub_swap W neg r n]; ring

lemma rel₄_swap₂₃ (m n r s : ℤ) : rel₄ W m n r s = - rel₄ W m n s r := by
  simp_rw [rel₄, addMulSub_swap W neg s r]; ring

variable (zero : W 0 = 0)

lemma rel₄_same₀₁ (m r s : ℤ) : rel₄ W m m r s = 0 := by
  simp_rw [rel₄, addMulSub_same W zero]; ring

lemma rel₄_same₁₂ (m n s : ℤ) : rel₄ W m n n s = 0 := by
  simp_rw [rel₄, addMulSub_same W zero]; ring

lemma rel₄_same₂₃ (m n r : ℤ) : rel₄ W m n r r = 0 := by
  simp_rw [rel₄, addMulSub_same W zero]; ring

end

section Perm

open Equiv

lemma closure_swap₀₁_swap₁₂_swap₂₃ :
    Subgroup.closure {swap (0 : Fin 4) 1, swap 1 2, swap 2 3} = ⊤ := by
  apply closure_of_isSwap_of_isPretransitive

theorem rel₄_perm (t : Fin 4 → ℤ) (σ : Equiv.Perm (Fin 4)) :
    relFin4 W (t ∘ σ) = Equiv.Perm.sign σ • relFin4 W t := by
  _




end Perm

end EllSequence

open EllSequence

/-- The proposition that a sequence indexed by integers is an elliptic sequence. -/
def IsEllSequence : Prop :=
  ∀ m n r : ℤ, Rel₃ W m n r

/-- The proposition that a sequence indexed by integers is a divisibility sequence. -/
def IsDivSequence : Prop :=
  ∀ m n : ℕ, m ∣ n → W m ∣ W n

/-- The proposition that a sequence indexed by integers is an EDS. -/
def IsEllDivSequence : Prop :=
  IsEllSequence W ∧ IsDivSequence W

lemma IsEllSequence_id : IsEllSequence id :=
  fun _ _ _ => by simp only [Rel₃, id_eq]; ring1

lemma IsDivSequence_id : IsDivSequence id :=
  fun _ _ => Int.ofNat_dvd.mpr

/-- The identity sequence is an EDS. -/
theorem IsEllDivSequence_id : IsEllDivSequence id :=
  ⟨IsEllSequence_id, IsDivSequence_id⟩

lemma IsEllSequence_mul (x : R) {W : ℤ → R} (h : IsEllSequence W) : IsEllSequence (x • W) :=
  fun m n r => by linear_combination
    (norm := (simp only [Pi.smul_apply, smul_eq_mul]; ring1)) x ^ 4 * h m n r

lemma IsDivSequence_mul (x : R) {W : ℤ → R} (h : IsDivSequence W) : IsDivSequence (x • W) :=
  fun m n r => mul_dvd_mul_left x <| h m n r

lemma IsEllDivSequence_mul (x : R) {W : ℤ → R} (h : IsEllDivSequence W) :
    IsEllDivSequence (x • W) :=
  ⟨IsEllSequence_mul x h.left, IsDivSequence_mul x h.right⟩

lemma IsEllSequence.map {W : ℤ → R} (h : IsEllSequence W) : IsEllSequence (f ∘ W) := by
  simpa using (congr_arg f <| h · · ·)

lemma IsDivSequence.map {W : ℤ → R} (h : IsDivSequence W) : IsDivSequence (f ∘ W) :=
  (map_dvd f <| h · · ·)

lemma IsEllDivSequence.map {W : ℤ → R} (h : IsEllDivSequence W) : IsEllDivSequence (f ∘ W) :=
  ⟨h.1.map f, h.2.map f⟩

section recurrence

namespace IsEllSequence

open EllSequence

variable {W : ℤ → R} (h : IsEllSequence W)

lemma zero' [IsReduced R] : W 0 = 0 := by
  have := h 0 0 0
  simp_rw [Rel₃, add_zero, sub_self, mul_assoc, ← pow_succ'] at this
  exact IsReduced.eq_zero _ ⟨_, this⟩

lemma zero (m : ℤ) (mem : W (2 * m) ∈ R⁰) : W 0 = 0 := by
  have := h m m (2 * m)
  rw [Rel₃, add_comm, sub_self, sub_self, ← two_mul, mul_comm (W _)] at this
  exact mem _ (pow_mem mem 2 _ this)

lemma sub_add_neg_sub_mul_eq_zero (m n r : ℤ) :
    (W (m - n) + W (-(m - n))) * W (m + n) * W r ^ 2 = 0 := by
  have := congr($(h m n r) + $(h n m r))
  rw [add_comm n, ← right_distrib, ← left_distrib, mul_comm (W _)] at this
  convert this using 4 <;> ring_nf

lemma neg (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰) (m : ℤ) : W (-m) = - W m := by
  rw [eq_neg_iff_add_eq_zero]
  obtain ⟨m, rfl|rfl⟩ := m.even_or_odd'
  on_goal 1 => apply two
  on_goal 2 => apply one
  all_goals apply pow_mem one 2
  · convert sub_add_neg_sub_mul_eq_zero h (1 - m) (m + 1) 1 using 2; ring_nf
  · convert sub_add_neg_sub_mul_eq_zero h (-m) (m + 1) 1 using 2; ring_nf

theorem of_even_odd (zero : W 0 = 0) (neg : ∀ n : ℕ, W (-n) = - W n)
    (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (oddRec : ∀ n, OddRec (W ·) n) (evenRec : ∀ n, EvenRec (W ·) n) : IsEllSequence W := by
  sorry

/- need W 1 = 1 ...
lemma IsEllSequence.somos {W : ℤ → R} (h : IsEllSequence W) (n : ℤ) :
    W (n + 2) * W (n - 2) = W (n + 1) * W (n - 1) * W 2 ^ 2 - W n ^ 2 * W 3 := by
  simpa using h. -/

end IsEllSequence

end recurrence

/-- The auxiliary sequence for a normalised EDS `W : ℕ → R`,
with initial values `W(0) = 0`, `W(1) = 1`, `W(2) = 1`, `W(3) = c`, and `W(4) = d`. -/
def preNormEDS' (b c d : R) : ℕ → R
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => c
  | 4 => d
  | (n + 5) => let m := n / 2
    have h4 : m + 4 < n + 5 := Nat.lt_succ.mpr <| add_le_add_right (n.div_le_self 2) 4
    have h3 : m + 3 < n + 5 := (lt_add_one _).trans h4
    have h2 : m + 2 < n + 5 := (lt_add_one _).trans h3
    have h1 : m + 1 < n + 5 := (lt_add_one _).trans h2
    if hn : Even n then
      preNormEDS' b c d (m + 4) * preNormEDS' b c d (m + 2) ^ 3 * (if Even m then b else 1) -
        preNormEDS' b c d (m + 1) * preNormEDS' b c d (m + 3) ^ 3 * (if Even m then 1 else b)
    else
      have h5 : m + 5 < n + 5 := add_lt_add_right
        (Nat.div_lt_self (Nat.odd_iff_not_even.mpr hn).pos <| Nat.lt_succ_self 1) 5
      preNormEDS' b c d (m + 2) ^ 2 * preNormEDS' b c d (m + 3) * preNormEDS' b c d (m + 5) -
        preNormEDS' b c d (m + 1) * preNormEDS' b c d (m + 3) * preNormEDS' b c d (m + 4) ^ 2

variable (b c d : R)

@[simp]
lemma preNormEDS'_zero : preNormEDS' b c d 0 = 0 := by
  rw [preNormEDS']

@[simp]
lemma preNormEDS'_one : preNormEDS' b c d 1 = 1 := by
  rw [preNormEDS']

@[simp]
lemma preNormEDS'_two : preNormEDS' b c d 2 = 1 := by
  rw [preNormEDS']

@[simp]
lemma preNormEDS'_three : preNormEDS' b c d 3 = c := by
  rw [preNormEDS']

@[simp]
lemma preNormEDS'_four : preNormEDS' b c d 4 = d := by
  rw [preNormEDS']

lemma preNormEDS'_odd (m : ℕ) : preNormEDS' b c d (2 * (m + 2) + 1) =
    preNormEDS' b c d (m + 4) * preNormEDS' b c d (m + 2) ^ 3 * (if Even m then b else 1) -
      preNormEDS' b c d (m + 1) * preNormEDS' b c d (m + 3) ^ 3 * (if Even m then 1 else b) := by
  rw [show 2 * (m + 2) + 1 = 2 * m + 5 by rfl, preNormEDS', dif_pos <| even_two_mul _]
  simp only [m.mul_div_cancel_left two_pos]

lemma preNormEDS'_even (m : ℕ) : preNormEDS' b c d (2 * (m + 3)) =
    preNormEDS' b c d (m + 2) ^ 2 * preNormEDS' b c d (m + 3) * preNormEDS' b c d (m + 5) -
      preNormEDS' b c d (m + 1) * preNormEDS' b c d (m + 3) * preNormEDS' b c d (m + 4) ^ 2 := by
  rw [show 2 * (m + 3) = 2 * m + 1 + 5 by rfl, preNormEDS', dif_neg m.not_even_two_mul_add_one]
  simp only [Nat.mul_add_div two_pos]
  rfl

/-- The auxiliary sequence for a normalised EDS `W : ℤ → R`,
with initial values `W(0) = 0`, `W(1) = 1`, `W(2) = 1`, `W(3) = c`, and `W(4) = d`.

This extends `preNormEDS'` by defining its values at negative integers. -/
def preNormEDS (n : ℤ) : R :=
  n.sign * preNormEDS' b c d n.natAbs

@[simp]
lemma preNormEDS_ofNat (n : ℕ) : preNormEDS b c d n = preNormEDS' b c d n := by
  by_cases hn : n = 0
  · rw [hn, preNormEDS, Nat.cast_zero, Int.sign_zero, Int.cast_zero, zero_mul, preNormEDS'_zero]
  · rw [preNormEDS, Int.sign_natCast_of_ne_zero hn, Int.cast_one, one_mul, Int.natAbs_cast]

@[simp]
lemma preNormEDS_zero : preNormEDS b c d 0 = 0 := by
  erw [preNormEDS_ofNat, preNormEDS'_zero]

@[simp]
lemma preNormEDS_one : preNormEDS b c d 1 = 1 := by
  erw [preNormEDS_ofNat, preNormEDS'_one]

@[simp]
lemma preNormEDS_two : preNormEDS b c d 2 = 1 := by
  erw [preNormEDS_ofNat, preNormEDS'_two]

@[simp]
lemma preNormEDS_three : preNormEDS b c d 3 = c := by
  erw [preNormEDS_ofNat, preNormEDS'_three]

@[simp]
lemma preNormEDS_four : preNormEDS b c d 4 = d := by
  erw [preNormEDS_ofNat, preNormEDS'_four]

lemma preNormEDS_odd (m : ℕ) : preNormEDS b c d (2 * (m + 2) + 1) =
    preNormEDS b c d (m + 4) * preNormEDS b c d (m + 2) ^ 3 * (if Even m then b else 1) -
      preNormEDS b c d (m + 1) * preNormEDS b c d (m + 3) ^ 3 * (if Even m then 1 else b) := by
  repeat erw [preNormEDS_ofNat]
  exact preNormEDS'_odd ..

lemma preNormEDS_even (m : ℕ) : preNormEDS b c d (2 * (m + 3)) =
    preNormEDS b c d (m + 2) ^ 2 * preNormEDS b c d (m + 3) * preNormEDS b c d (m + 5) -
      preNormEDS b c d (m + 1) * preNormEDS b c d (m + 3) * preNormEDS b c d (m + 4) ^ 2 := by
  repeat erw [preNormEDS_ofNat]
  exact preNormEDS'_even ..

@[simp]
lemma preNormEDS_neg (n : ℤ) : preNormEDS b c d (-n) = -preNormEDS b c d n := by
  rw [preNormEDS, Int.sign_neg, Int.cast_neg, neg_mul, Int.natAbs_neg, preNormEDS]

/-- The canonical example of a normalised EDS `W : ℤ → R`,
with initial values `W(0) = 0`, `W(1) = 1`, `W(2) = b`, `W(3) = c`, and `W(4) = d * b`.

This is defined in terms of `preNormEDS` whose even terms differ by a factor of `b`. -/
def normEDS (n : ℤ) : R :=
  preNormEDS (b ^ 4) c d n * if Even n.natAbs then b else 1

@[simp]
lemma normEDS_ofNat (n : ℕ) :
    normEDS b c d n = preNormEDS' (b ^ 4) c d n * if Even n then b else 1 := by
  rw [normEDS, preNormEDS_ofNat, Int.natAbs_ofNat]

@[simp]
lemma normEDS_zero : normEDS b c d 0 = 0 := by
  erw [normEDS_ofNat, preNormEDS'_zero, zero_mul]

@[simp]
lemma normEDS_one : normEDS b c d 1 = 1 := by
  erw [normEDS_ofNat, preNormEDS'_one, one_mul, if_neg Nat.not_even_one]

@[simp]
lemma normEDS_two : normEDS b c d 2 = b := by
  erw [normEDS_ofNat, preNormEDS'_two, one_mul, if_pos even_two]

@[simp]
lemma normEDS_three : normEDS b c d 3 = c := by
  erw [normEDS_ofNat, preNormEDS'_three, if_neg <| by decide, mul_one]

@[simp]
lemma normEDS_four : normEDS b c d 4 = d * b := by
  erw [normEDS_ofNat, preNormEDS'_four, if_pos <| by decide]

lemma normEDS_odd (m : ℕ) : normEDS b c d (2 * (m + 2) + 1) =
    normEDS b c d (m + 4) * normEDS b c d (m + 2) ^ 3 -
      normEDS b c d (m + 1) * normEDS b c d (m + 3) ^ 3 := by
  repeat erw [normEDS_ofNat]
  simp only [preNormEDS'_odd, if_neg (m + 2).not_even_two_mul_add_one]
  by_cases hm : Even m
  · have hm1 : ¬Even (m + 1) := fun h => Nat.even_add_one.mp h hm
    have hm2 : Even (m + 2) := Nat.even_add_one.mpr hm1
    have hm3 : ¬Even (m + 3) := fun h => Nat.even_add_one.mp h hm2
    have hm4 : Even (m + 4) := Nat.even_add_one.mpr hm3
    rw [if_pos hm, if_pos hm, if_pos hm4, if_pos hm2, if_neg hm1, if_neg hm3]
    ring1
  · have hm1 : Even (m + 1) := Nat.even_add_one.mpr hm
    have hm2 : ¬Even (m + 2) := fun h => Nat.even_add_one.mp h hm1
    have hm3 : Even (m + 3) := Nat.even_add_one.mpr hm2
    have hm4 : ¬Even (m + 4) := fun h => Nat.even_add_one.mp h hm3
    rw [if_neg hm, if_neg hm, if_neg hm4, if_neg hm2, if_pos hm1, if_pos hm3]
    ring1

lemma normEDS_even (m : ℕ) : normEDS b c d (2 * (m + 3)) * b =
    normEDS b c d (m + 2) ^ 2 * normEDS b c d (m + 3) * normEDS b c d (m + 5) -
      normEDS b c d (m + 1) * normEDS b c d (m + 3) * normEDS b c d (m + 4) ^ 2 := by
  repeat erw [normEDS_ofNat]
  simp only [preNormEDS'_even, if_pos <| even_two_mul _]
  by_cases hm : Even m
  · have hm1 : ¬Even (m + 1) := fun h => Nat.even_add_one.mp h hm
    have hm2 : Even (m + 2) := Nat.even_add_one.mpr hm1
    have hm3 : ¬Even (m + 3) := fun h => Nat.even_add_one.mp h hm2
    have hm4 : Even (m + 4) := Nat.even_add_one.mpr hm3
    have hm5 : ¬Even (m + 5) := fun h => Nat.even_add_one.mp h hm4
    rw [if_pos hm2, if_neg hm3, if_neg hm5, if_neg hm1, if_pos hm4]
    ring1
  · have hm1 : Even (m + 1) := Nat.even_add_one.mpr hm
    have hm2 : ¬Even (m + 2) := fun h => Nat.even_add_one.mp h hm1
    have hm3 : Even (m + 3) := Nat.even_add_one.mpr hm2
    have hm4 : ¬Even (m + 4) := fun h => Nat.even_add_one.mp h hm3
    have hm5 : Even (m + 5) := Nat.even_add_one.mpr hm4
    rw [if_neg hm2, if_pos hm3, if_pos hm5, if_pos hm1, if_neg hm4]
    ring1

@[simp]
lemma normEDS_neg (n : ℕ) : normEDS b c d (-n) = -normEDS b c d n := by
  rw [normEDS, preNormEDS_neg, Int.natAbs_neg, neg_mul, normEDS]

section map

variable {b c d}

inductive Param : Type | B : Param | C : Param | D : Param

open Param in
open MvPolynomial (X) in
noncomputable def universalNormEDS : ℤ → MvPolynomial Param ℤ := normEDS (X B) (X C) (X D)

-- preNormEDS', preNormEDS too
lemma map_normEDS (n : ℤ) : f (normEDS b c d n) = normEDS (f b) (f c) (f d) n := by
  sorry

open MvPolynomial in
lemma normEDS_eq_aeval (n : ℤ) :
    normEDS b c d n = aeval (Param.rec b c d) (universalNormEDS n) := by
  simp_rw [universalNormEDS, map_normEDS, aeval_X]

end map

-- IsNormEDS predicate? satisfying W (-n) = - W n and W 0 = 0 (and W 1 = 1?)
-- W 1 = 1 is normalization; usually W 1 not being a zero divisor has the same effect (can prove the same things)
-- W 1 not a zero divisor + IsEllSequence probably imply W (-n) = - W n and W 0 = 0
-- prove Somos relation and relevant identities for the two cases
