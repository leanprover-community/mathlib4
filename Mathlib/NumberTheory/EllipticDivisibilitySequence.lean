/-
Copyright (c) 2024 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
module

public import Init.Data.Int.DivMod
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Nat.EvenOddRec
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Group.Int.Even

/-!
# Elliptic divisibility sequences

This file defines elliptic divisibility sequences (EDS)
and constructs normalised EDSs from initial terms.

## Mathematical background

Let `R` be a commutative ring. An elliptic sequence is a sequence `W : ℤ → R` satisfying
`W(m + n)W(m - n)W(r)² = W(m + r)W(m - r)W(n)² - W(n + r)W(n - r)W(m)²` for any `m, n, r ∈ ℤ`.
A divisibility sequence is a sequence `W : ℤ → R` satisfying `W(m) ∣ W(n)` for any `m, n ∈ ℤ` such
that `m ∣ n`. An elliptic divisibility sequence is simply a divisibility sequence that is elliptic.

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
* `complEDS₂`: the 2-complement sequence for a normalised EDS indexed by `ℕ`.
* `normEDS`: the canonical example of a normalised EDS indexed by `ℤ`.
* `complEDS'`: the complement sequence for a normalised EDS indexed by `ℕ`.
* `complEDS`: the complement sequence for a normalised EDS indexed by `ℤ`.

## Main statements

 * `isEllDivSequence_normEDS`: `normEDS` satisfies `IsEllDivSequence`.

## Implementation notes

The normalised EDS `normEDS b c d n` is defined in terms of the auxiliary sequence
`preNormEDS (b ^ 4) c d n`, which are equal when `n` is odd, and which differ by a factor of `b`
when `n` is even. This coincides with the definition in the references since both agree for
`normEDS b c d 2` and for `normEDS b c d 4`, and the correct factors of `b` are removed in
`normEDS b c d (2 * (m + 2) + 1)` and in `normEDS b c d (2 * (m + 3))`.

One reason is to avoid the necessity for ring division by `b` in the inductive definition of
`normEDS b c d (2 * (m + 3))`. The idea is that it can be shown that `normEDS b c d (2 * (m + 3))`
always contains a factor of `b`, so it is possible to remove a factor of `b` *a posteriori*, but
stating this lemma requires first defining `normEDS b c d (2 * (m + 3))`, which requires having this
factor of `b` *a priori*. Another reason is to allow the definition of univariate `n`-division
polynomials of elliptic curves, omitting a factor of the bivariate `2`-division polynomial.

## References

M Ward, *Memoir on Elliptic Divisibility Sequences*

## Tags

elliptic, divisibility, sequence
-/

@[expose] public section

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : ℤ → R)
variable {F} [FunLike F R S] [RingHomClass F R S] (f : F)

open scoped nonZeroDivisors

namespace EllSequence

/-- The expression `W((m+n)/2) * W((m-n)/2)` is the basic building block of elliptic relations,
where integers `m` and `n` should have the same parity. -/
def addMulSub (m n : ℤ) : R := W ((m + n).tdiv 2) * W ((m - n).tdiv 2)
-- Implementation note: we use `Int.tdiv _ 2` instead of `_ / 2` so that
-- `(-m).tdiv 2 = -(m.tdiv 2)`
-- and lemmas like `addMulSub_neg₀` hold unconditionally, even though in the case we care about
-- (`m` and `n` both even or both odd) both are equal.

/-- The four-index elliptic relation, defined in terms of `addMulSub`,
featuring the three partitions of four indices into two pairs.
Intended to apply to four integers of the same parity. -/
def rel₄ (a b c d : ℤ) : R :=
  addMulSub W a b * addMulSub W c d
    - addMulSub W a c * addMulSub W b d + addMulSub W a d * addMulSub W b c

/-- The defining property of Stange's elliptic nets,
equivalent to a suitable valid (same-parity indices) `rel₄` relation,
but here only the first three indices enjoy symmetry under permutation,
while in `rel₄` all four indices can be freely permuted.

The order of the last two terms are changed and two signs are swapped compared to Stange's
paper to make the equivalence with elliptic relations unconditional (indepedent of W
being an odd function). This should also avoid peculiarities in characterstic 3. -/
def net (p q r s : ℤ) : R :=
  W (p + q + s) * W (p - q) * W (r + s) * W r
    - W (p + r + s) * W (p - r) * W (q + s) * W q
    + W (q + r + s) * W (q - r) * W (p + s) * W p

variable {W} in
lemma net_eq_rel₄ {p q r s : ℤ} :
    net W p q r s = rel₄ W (2 * p + s) (2 * q + s) (2 * r + s) s := by
  simp_rw [net, rel₄, addMulSub, add_add_add_comm _ s, add_sub_add_comm, sub_self, add_zero,
    add_assoc, ← two_mul, add_sub_cancel_right, ← left_distrib, ← mul_sub_left_distrib,
    Int.mul_tdiv_cancel_left _ two_ne_zero]
  ring

/-- The three-index elliptic relation, obtained by
specializing to `d = 0` in the four-index relation. -/
def Rel₃ (m n r : ℤ) : Prop :=
  W (m + n) * W (m - n) * W r ^ 2 =
    W (m + r) * W (m - r) * W n ^ 2 - W (n + r) * W (n - r) * W m ^ 2

/-- The proposition that a sequence indexed by integers is an elliptic sequence. -/
def _root_.IsEllSequence : Prop :=
  ∀ m n r : ℤ, Rel₃ W m n r

/-- The numerator of an invariant of an elliptic sequence, such that for each `s`,
`invarNum s n / invarDenom s n` is a constant independent of `n`. -/
def invarNum (s n : ℤ) : R :=
  (W (n + 2 * s) * W (n - s) ^ 2 + W (n + s) ^ 2 * W (n - 2 * s)) * W s ^ 2
    + W n ^ 3 * W (2 * s) ^ 2

/-- The denominator of an invariant of an elliptic sequence. -/
def invarDenom (s n : ℤ) : R := W (n + s) * W n * W (n - s)

theorem invar_of_net (net_eq_zero : ∀ p q r s, net W p q r s = 0) (s m n : ℤ) :
    invarNum W s m * invarDenom W s n = invarNum W s n * invarDenom W s m := by
  simp_rw [invarNum, invarDenom]
  linear_combination (norm := (simp_rw [net]; ring_nf; simp only [Nat.rawCast]))
    net_eq_zero m n s 0 * W m * W n * W (2 * s) ^ 2
      - (net_eq_zero m n s s * W (m - s) * W (n - s)
        + net_eq_zero (m - s) (n - s) s s * W (m + s) * W (n + s)
        - net_eq_zero (n + s) n (n - s) (m - n) * W (m - n) * W (2 * s)) * W s ^ 2

lemma net_add_sub_iff (m n : ℤ) :
    net W (m + n) m (m - n) n = 0 ↔
      W (2 * (m + n)) * W (m - n) * W m * W n =
        (W (2 * m + n) * W (2 * n) * W m - W (m + 2 * n) * W (2 * m) * W n) * W (m + n) := by
  rw [net]; conv_rhs => rw [← sub_eq_zero]
  ring_nf; simp only [Nat.rawCast]

lemma addMulSub_two_zero : addMulSub W 2 0 = W 1 ^ 2 := (sq _).symm
lemma addMulSub_three_one : addMulSub W 3 1 = W 2 * W 1 := rfl

lemma addMulSub_even (m n : ℤ) : addMulSub W (2 * m) (2 * n) = W (m + n) * W (m - n) := by
  simp_rw [addMulSub, ← left_distrib, ← mul_sub_left_distrib, Int.mul_tdiv_cancel_left _ two_ne_zero]

lemma addMulSub_odd (m n : ℤ) :
    addMulSub W (2 * m + 1) (2 * n + 1) = W (m + n + 1) * W (m - n) := by
  have h k := Int.mul_tdiv_cancel_left k two_ne_zero
  rw [addMulSub, ← h (m + n + 1), ← h (m - n)]; congr <;> ring

lemma addMulSub_same (zero : W 0 = 0) (m : ℤ) : addMulSub W m m = 0 := by
  rw [addMulSub, sub_self, Int.zero_tdiv, zero, mul_zero]

lemma addMulSub_neg₀ (neg : ∀ k, W (-k) = -W k) (m n : ℤ) :
    addMulSub W (-m) n = addMulSub W m n := by
  simp_rw [addMulSub, ← neg_add', neg_add_eq_sub, ← neg_sub m, Int.neg_tdiv, neg]; ring

lemma addMulSub_neg₁ (m n : ℤ) : addMulSub W m (-n) = addMulSub W m n := by
  rw [addMulSub, addMulSub, mul_comm]; abel_nf

lemma addMulSub_abs₀ (neg : ∀ k, W (-k) = -W k) (m n : ℤ) :
    addMulSub W |m| n = addMulSub W m n := by
  obtain h | h := abs_choice m <;> simp only [h, addMulSub_neg₀ W neg]

lemma addMulSub_abs₁ (m n : ℤ) : addMulSub W m |n| = addMulSub W m n := by
  obtain h | h := abs_choice n <;> simp only [h, addMulSub_neg₁]

lemma addMulSub_swap (neg : ∀ k, W (-k) = -W k) (m n : ℤ) :
    addMulSub W m n = - addMulSub W n m := by
  rw [addMulSub, addMulSub, ← neg_sub, Int.neg_tdiv, neg]; ring_nf

section transf

variable (a b c d : ℤ)

/-- The proposition that the four indices are all nonnegative and strictly decreasing. -/
def StrictAnti₄ : Prop := 0 ≤ d ∧ d < c ∧ c < b ∧ b < a

/-- The proposition that the four indices are of the same parity. -/
def HaveSameParity₄ : Prop :=
  a.negOnePow = b.negOnePow ∧ b.negOnePow = c.negOnePow ∧ c.negOnePow = d.negOnePow

/-- The average of four indices. -/
def avg₄ : ℤ := (a + b + c + d) / 2

namespace HaveSameParity₄
open Int Equiv

variable {W a b c d} (same : HaveSameParity₄ a b c d)
include same

lemma rel₄_eq_net : rel₄ W a b c d = net W ((a - d) / 2) ((b - d) / 2) ((c - d) / 2) d := by
  have h := @Int.two_mul_ediv_two_of_even
  rw [net_eq_rel₄, h, h, h]; · simp_rw [sub_add_cancel]
  all_goals rw [← negOnePow_eq_iff]
  exacts [same.1.trans (same.2.1.trans same.2.2), same.2.1.trans same.2.2, same.2.2]

lemma even_sum : Even (a + b + c + d) := by
  simp_rw [← negOnePow_eq_one_iff, negOnePow_add,
    same.1, same.2.1, same.2.2, units_mul_self, one_mul, units_mul_self]

lemma avg₄_add_avg₄ : avg₄ a b c d + avg₄ a b c d = a + b + c + d := by
  rw [← two_mul]; exact Int.mul_ediv_cancel' same.even_sum.two_dvd

lemma same₀₃ : a.negOnePow = d.negOnePow := by rw [same.1, same.2.1, same.2.2]

protected lemma abs : HaveSameParity₄ |a| |b| |c| |d| := by
  simpa only [HaveSameParity₄, negOnePow_abs] using same

lemma perm (σ : Perm (Fin 4)) :
    ∀ t : Fin 4 → ℤ, HaveSameParity₄ (t 0) (t 1) (t 2) (t 3) →
      HaveSameParity₄ (t (σ 0)) (t (σ 1)) (t (σ 2)) (t (σ 3)) := by
  have hmem := (Perm.mclosure_swap_castSucc_succ 3).symm ▸ Submonoid.mem_top σ
  refine Submonoid.closure_induction
    (motive := fun σ _ ↦ ∀ t : Fin 4 → ℤ, HaveSameParity₄ (t 0) (t 1) (t 2) (t 3) →
      HaveSameParity₄ (t (σ 0)) (t (σ 1)) (t (σ 2)) (t (σ 3)))
    ?_ (fun _ ↦ id) (fun σ τ _ _ hσ hτ t same ↦ ?_) hmem
  on_goal 2 => simp_rw [Perm.mul_apply]; exact hτ (t ∘ σ) (hσ _ same)
  rintro _ ⟨i, rfl⟩ t ⟨h₀₁, h₁₂, h₂₃⟩; fin_cases i
  exacts [⟨h₀₁.symm, h₀₁ ▸ h₁₂, h₂₃⟩, ⟨h₀₁ ▸ h₁₂, h₁₂.symm, h₁₂ ▸ h₂₃⟩, ⟨h₀₁, h₁₂ ▸ h₂₃, h₂₃.symm⟩]

lemma six_le_of_strictAnti₄ (anti : StrictAnti₄ a b c d) : 6 ≤ a := by
  simp_rw [HaveSameParity₄, negOnePow_eq_iff] at same
  obtain ⟨hd, hdc, hcb, hba⟩ := anti
  rw [← add_two_le_iff_lt_of_even_sub] at hdc hcb hba
  · linarith
  exacts [same.1, same.2.1, same.2.2]

variable (W) in
/-- A hybrid product formed by one factor from an `addMulSub` and one from another `addMulSub`. -/
def addMulSub₄ (a b c d : ℤ) : R := W ((a + b).tdiv 2) * W ((c - d).tdiv 2)

lemma addMulSub₄_mul_addMulSub₄ :
    addMulSub₄ W a b c d * addMulSub₄ W c d a b = addMulSub W a b * addMulSub W c d := by
  simp_rw [addMulSub₄, addMulSub]; ring

lemma addMulSub_transf :
    addMulSub W (avg₄ a b c d - d) (avg₄ a b c d - c) = addMulSub₄ W a b c d ∧
      addMulSub W (avg₄ a b c d - d) (avg₄ a b c d - b) = addMulSub₄ W a c b d ∧
      addMulSub W (avg₄ a b c d - d) |avg₄ a b c d - a| = addMulSub₄ W b c a d ∧
      addMulSub W (avg₄ a b c d - c) (avg₄ a b c d - b) = addMulSub₄ W a d b c ∧
      addMulSub W (avg₄ a b c d - c) |avg₄ a b c d - a| = addMulSub₄ W b d a c ∧
      addMulSub W (avg₄ a b c d - b) |avg₄ a b c d - a| = addMulSub₄ W c d a b := by
  simp_rw [addMulSub_abs₁, addMulSub, addMulSub₄, sub_add_sub_comm, same.avg₄_add_avg₄]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring_nf

theorem rel₄_transf :
    rel₄ W (avg₄ a b c d - d) (avg₄ a b c d - c) (avg₄ a b c d - b) |avg₄ a b c d - a| =
      rel₄ W a b c d := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := same.addMulSub_transf (W := W)
  simp_rw [rel₄, h₁, h₂, h₃, h₄, h₅, h₆, addMulSub₄_mul_addMulSub₄, mul_comm]

theorem transf : HaveSameParity₄
    (avg₄ a b c d - d) (avg₄ a b c d - c) (avg₄ a b c d - b) |avg₄ a b c d - a| := by
  simp_rw [HaveSameParity₄, negOnePow_abs, negOnePow_sub, same.1, same.2.1, same.2.2, true_and]

theorem strictAnti₄_transf (anti : StrictAnti₄ a b c d) :
    StrictAnti₄ (avg₄ a b c d - d) (avg₄ a b c d - c) (avg₄ a b c d - b) |avg₄ a b c d - a| := by
  obtain ⟨hd, hdc, hcb, hba⟩ := anti
  refine ⟨abs_nonneg _, abs_lt.mpr ⟨?_, ?_⟩, ?_, ?_⟩ <;> rw [← sub_pos]
  · rw [sub_neg_eq_add, sub_add_sub_comm, same.avg₄_add_avg₄]; linarith only [hd, hdc]
  all_goals linarith only [hdc, hcb, hba]

end HaveSameParity₄

end transf

/-- The four-index elliptic relation multiplied by a two-index "coefficient". -/
def rel₆ (k l a b c d : ℤ) : R := addMulSub W k l * rel₄ W a b c d

lemma rel₃_iff₄ (m n r : ℤ) :
    Rel₃ W m n r ↔ rel₄ W (2 * m) (2 * n) (2 * r) 0 = 0 := by
  rw [rel₄, ← mul_zero 2, Rel₃]
  simp_rw [addMulSub_even, add_zero, sub_zero]
  convert sub_eq_zero.symm using 2; ring

/-! In the following three key lemmas we use `m`, `n`, `r`, `s` to denote "free" indices and
`c`, `d` to denote "fixed" indices. -/

/-- A `rel₄` with a fixed index and three free indices can be expressed in terms of
three `rel₄`s with two fixed indices and two free indices that share one fixed index
(the larger one) and two free indices with the first `rel₄`.
The coefficient before the first `rel₄` is `addMulSub` applied to the two fixed indices. -/
lemma rel₆_eq₃ (c d m n r : ℤ) :
    rel₆ W c d m n r c = rel₆ W m c n r c d - rel₆ W n c m r c d + rel₆ W r c m n c d := by
  simp_rw [rel₆, rel₄]; ring

/-- A `rel₄` with a fixed index and three free indices can be expressed in terms of
three `rel₄`s with two fixed indices and two free indices that share one fixed index
(the smaller one) and two free indices with the first `rel₄`.
The coefficient before the first `rel₄` is `addMulSub` applied to the two fixed indices. -/
lemma rel₆_eq₃' (c d m n r : ℤ) :
    rel₆ W c d m n r d = rel₆ W m d n r c d - rel₆ W n d m r c d + rel₆ W r d m n c d := by
  simp_rw [rel₆, rel₄]; ring

/-- A `rel₄` with four free indices can be expressed in terms of ten `rel₄`s
with at least one index chosen from two possibilities (fixed indices) and
the other indices chosen from the indices of the first `rel₄`.
The coefficient before the first `rel₄` is `addMulSub` applied to the two fixed indices. -/
theorem rel₆_eq₁₀ (c d m n r s : ℤ) :
    rel₆ W c d m n r s =
      rel₆ W n d m r s c - rel₆ W r d m n s c + rel₆ W s d m n r c
      + rel₆ W n c m r s d - rel₆ W r c m n s d + rel₆ W s c m n r d
      + rel₆ W n r m s c d - rel₆ W n s m r c d + rel₆ W r s m n c d
      - 2 * rel₆ W m d n r s c := by
  simp_rw [rel₆, rel₄]; ring

theorem addMulSub_sq_mul_rel₄_eq₉ (c d m n r s : ℤ) :
    (addMulSub W c d) ^ 2 * rel₄ W m n r s =
      addMulSub W m c * (rel₆ W n d r s c d - rel₆ W r d n s c d + rel₆ W s d n r c d)
                    -- = rel₆ W c d n r s d ↑ by rel₆_eq₃'   = rel₆ W c d n r s c ↓ by rel₆_eq₃
      - addMulSub W m d * (rel₆ W n c r s c d - rel₆ W r c n s c d + rel₆ W s c n r c d)
      + addMulSub W c d * (rel₆ W n r m s c d - rel₆ W n s m r c d + rel₆ W r s m n c d) := by
                         -- the third row in RHS of rel₆_eq₁₀
  simp_rw [rel₆, rel₄]; ring

/-- The recurrence defining odd terms of an elliptic sequence,
a particular case of the elliptic relation according to `rel₃_iff_oddRec`. -/
def OddRec (m : ℤ) : Prop :=
  W (2 * m + 1) * W 1 ^ 3 = W (m + 2) * W m ^ 3 - W (m - 1) * W (m + 1) ^ 3

/-- The recurrence defining even terms of an elliptic sequence, a particular case
of the elliptic relation according to `rel₃_iff_evenRec` and `rel₄_iff_evenRec`. -/
def EvenRec (m : ℤ) : Prop :=
  W (2 * m) * W 2 * W 1 ^ 2 = W m * (W (m - 1) ^ 2 * W (m + 2) - W (m - 2) * W (m + 1) ^ 2)

lemma rel₃_iff_oddRec (m : ℤ) : Rel₃ W (m + 1) m 1 ↔ OddRec W m := by
  rw [Rel₃, OddRec]; ring_nf

lemma rel₃_iff_evenRec (m : ℤ) : Rel₃ W (m + 1) (m - 1) 1 ↔ EvenRec W m := by
  rw [Rel₃, EvenRec]; ring_nf; simp only [Nat.rawCast]

lemma rel₄_iff_evenRec (m : ℤ) : rel₄ W (2 * m + 1) (2 * m - 1) 3 1 = 0 ↔ EvenRec W m := by
  rw [iff_comm, EvenRec, ← sub_eq_zero, show 2 * m - 1 = 2 * (m - 1) + 1 by ring]
  convert_to _ ↔ rel₄ W _ _ (2 * 1 + 1) (2 * 0 + 1) = 0
  simp_rw [rel₄, addMulSub_odd]; ring_nf; simp only [Nat.rawCast]

/-- The minimal possible fourth index in the four-index elliptic relation given the first index. -/
def dMin (a : ℤ) : ℤ := if Even a then 0 else 1
/-- The minimal possible third index in the four-index elliptic relation given the first index. -/
def cMin (a : ℤ) : ℤ := dMin a + 2

lemma dMin_nonneg (a : ℤ) : 0 ≤ dMin a := by rw [dMin]; split_ifs <;> decide

lemma dMin_lt_cMin (a : ℤ) : dMin a < cMin a := lt_add_of_pos_right _ zero_lt_two

lemma negOnePow_cMin_eq_dMin (a : ℤ) : (cMin a).negOnePow = (dMin a).negOnePow := by
  rw [cMin, Int.negOnePow_add]; exact mul_one _

lemma negOnePow_dMin (a : ℤ) : (dMin a).negOnePow = a.negOnePow := by
  rw [dMin]; split_ifs with h
  · simp [Int.negOnePow_even, h]
  · simp [Int.negOnePow_odd, Int.not_even_iff_odd.mp h]

lemma negOnePow_cMin (a : ℤ) : (cMin a).negOnePow = a.negOnePow := by
  rw [negOnePow_cMin_eq_dMin, negOnePow_dMin]

variable {W}
lemma addMulSub_mem_nonZeroDivisors (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰) (a : ℤ) :
    addMulSub W (cMin a) (dMin a) ∈ R⁰ := by
  rw [cMin, dMin]; split_ifs; exacts [mul_mem one one, mul_mem two one]

lemma dMin_le {a b : ℤ} (same : a.negOnePow = b.negOnePow) (h : 0 ≤ b) : dMin a ≤ b := by
  rw [dMin]; split_ifs with odd
  exacts [h, h.lt_of_ne (by rintro rfl; exact odd (a.negOnePow_eq_one_iff.mp same))]

open Int

section Rel₄OfValid

variable (W) in
/-- The four-index elliptic relation restricted to the case where the four indices are
nonnegative, have the same parity and are strictly decreasing. -/
def Rel₄OfValid (a b c d : ℤ) : Prop :=
  HaveSameParity₄ a b c d → StrictAnti₄ a b c d → rel₄ W a b c d = 0

variable {a c₀ d₀ : ℤ} (par : c₀.negOnePow = d₀.negOnePow) (le : 0 ≤ d₀) (lt : d₀ < c₀)
  (rel : ∀ {a' b}, a' ≤ a → Rel₄OfValid W a' b c₀ d₀) (mem : addMulSub W c₀ d₀ ∈ R⁰)
include par le lt rel mem

/-- If `rel₄` holds for all quadruples of the form `(a', b, c₀, d₀)` for arbitrary `b` and
`a' < a`, then it holds for `(a, b, c, c₀)` and `(a, b, c, d₀)` for arbitrary `b` and `c`
(subject to some technical conditions). -/
lemma rel₄_fix₁_of_fix₂ (b c : ℤ) :
    Rel₄OfValid W a b c c₀ ∧ (c₀ < c → Rel₄OfValid W a b c d₀) := by
  refine ⟨fun same anti ↦ mem _ ?_, fun _hc same anti ↦ mem _ ?_⟩ <;> rw [mul_comm, ← rel₆]
  on_goal 1 => rw [rel₆_eq₃]; have _hc := trivial
  on_goal 2 => rw [rel₆_eq₃']
  all_goals simp_rw [rel₆]; rw [rel le_rfl, rel le_rfl, rel anti.2.2.2.le]
  iterate 2
    simp_rw [mul_zero, add_zero, sub_zero]
    iterate 3
      simp only [HaveSameParity₄, par, same.1, same.2.1, same.2.2, true_and]
      refine ⟨le, lt, ?_, ?_⟩ <;> linarith only [_hc, anti.2.1, anti.2.2.1, anti.2.2.2]

/-- If `rel₄` holds for all quadruples of the form `(a', b, c₀, d₀)` for arbitrary `b` and
`a' < a`, then it holds for `(a, b, c, d)` for arbitrary `b`, `c` and `d`
(subject to some technical conditions). -/
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

/-- Specialize previous lemmas to the case `c₀ = cMin a` and `d₀ = dMin a`,
and combine them to remove technical conditions about the relative order of the indices. -/
theorem rel₄_of_min₂ (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (rel : ∀ {a' b}, a' ≤ a → Rel₄OfValid W a' b (cMin a) (dMin a)) (b c d : ℤ) :
    Rel₄OfValid W a b c d := fun same anti ↦ by
  obtain hc|hc := lt_or_ge (cMin a) d
  · refine rel₄_of_fix₂ (negOnePow_cMin_eq_dMin a) (dMin_nonneg a) (dMin_lt_cMin a) rel
      (addMulSub_mem_nonZeroDivisors one two a) _ _ _ hc ?_ same anti
    rw [negOnePow_dMin, same.1, same.2.1, same.2.2]
  have fix := rel₄_fix₁_of_fix₂ (negOnePow_cMin_eq_dMin a) (dMin_nonneg a) (dMin_lt_cMin a) rel
    (addMulSub_mem_nonZeroDivisors one two a) b c
  obtain rfl|hc := hc.eq_or_lt
  · exact fix.1 same anti
  obtain rfl : dMin a = d := (dMin_le same.same₀₃ anti.1).antisymm <| by
    rwa [← add_two_le_iff_lt_of_even_sub, cMin, add_le_add_iff_right] at hc
    rw [← negOnePow_eq_iff, negOnePow_cMin, same.same₀₃]
  obtain rfl|hc : cMin a = c ∨ _ := ((add_two_le_iff_lt_of_even_sub <| by
    rw [← negOnePow_eq_iff, negOnePow_dMin, same.1, same.2.1]).mpr anti.2.1).eq_or_lt
  exacts [rel le_rfl same anti, fix.2 hc same anti]

-- The main inductive argument.
theorem rel₄_of_anti_oddRec_evenRec (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (oddRec : ∀ m ≥ 2, OddRec W m) (evenRec : ∀ m ≥ 3, EvenRec W m) :
    ∀ ⦃a b c d : ℤ⦄, Rel₄OfValid W a b c d :=
  -- apply induction on `a`
  Int.strongRec (m := 6) -- if `a < 6` the conclusion holds vacuously
    (fun a ha b c d same anti ↦ ((same.six_le_of_strictAnti₄ anti).not_lt ha).elim)
    -- otherwise, it suffices to deal with the "minimal" case `c = cMin a` and `d = dMin a`
    fun a h6 ih ↦ rel₄_of_min₂ one two fun {a' b} haa same anti ↦ by
  obtain ha'|ha' := haa.lt_or_eq
  · -- if a' < a, apply the inductive hypothesis
    exact ih _ ha' same anti
  obtain hba|rfl := lt_or_eq_of_le <| show b + 2 ≤ a' from
    (add_two_le_iff_lt_of_even_sub <| (negOnePow_eq_iff _ _).1 same.1).mpr anti.2.2.2
  · -- if b + 2 < a', apply `transf` and then the inductive hypothesis is applicable
    rw [← same.rel₄_transf]
    refine ih _ ?_ same.transf (same.strictAnti₄_transf anti)
    rw [avg₄, sub_lt_iff_lt_add, Int.ediv_lt_iff_lt_mul zero_lt_two, ← ha', cMin]
    linarith only [hba]
  obtain ⟨m, rfl|rfl⟩ := b.even_or_odd'
  -- the b + 2 = a' case is handled by oddRec or evenRec depending on the parity of `b`
  · have ea : Even a := by rw [← ha']; exact (even_two_mul _).add even_two
    simp_rw [cMin, dMin, if_pos ea]
    convert (rel₃_iff₄ W (m + 1) m 1).mp ((rel₃_iff_oddRec W m).mpr <| oddRec _ ?_) using 2
    · ring
    · linarith only [h6, ha']
  · have nea : ¬ Even a := by
      rw [← ha', ← Int.not_even_iff_odd]; convert odd_two_mul_add_one (m + 1) using 1; ring
    simp_rw [cMin, dMin, if_neg nea]
    convert (rel₄_iff_evenRec W (m + 1)).mpr (evenRec _ ?_) using 2
    on_goal 3 => linarith only [h6, ha']
    all_goals ring

end Rel₄OfValid

section Perm

variable (neg : ∀ k, W (-k) = -W k)
include neg

lemma rel₄_abs {m n r s : ℤ} : rel₄ W |m| |n| |r| |s| = rel₄ W m n r s := by
  simp_rw [rel₄, addMulSub_abs₀ W neg, addMulSub_abs₁]

lemma rel₄_swap₀₁ {m n r s : ℤ} : rel₄ W m n r s = - rel₄ W n m r s := by
  simp_rw [rel₄, addMulSub_swap W neg n m]; ring

lemma rel₄_swap₁₂ {m n r s : ℤ} : rel₄ W m n r s = - rel₄ W m r n s := by
  simp_rw [rel₄, addMulSub_swap W neg r n]; ring

lemma rel₄_swap₂₃ {m n r s : ℤ} : rel₄ W m n r s = - rel₄ W m n s r := by
  simp_rw [rel₄, addMulSub_swap W neg s r]; ring

open Equiv

variable (W) in
/-- The four-index elliptic relation with a tuple as input. -/
def relFin4 (t : Fin 4 → ℤ) : R := rel₄ W (t 0) (t 1) (t 2) (t 3)

/-- `rel₄` is invariant (up to sign) under permutation of the four indices. -/
theorem relFin4_perm (σ : Perm (Fin 4)) : ∀ t, relFin4 W (t ∘ σ) = Perm.sign σ • relFin4 W t := by
  have hmem := (Perm.mclosure_swap_castSucc_succ 3).symm ▸ Submonoid.mem_top σ
  refine Submonoid.closure_induction
    (motive := fun σ _ ↦ ∀ t, relFin4 W (t ∘ σ) = Perm.sign σ • relFin4 W t)
    ?_ (by simp) (fun σ τ _ _ hσ hτ t ↦ ?_) hmem
  · rintro _ ⟨i, rfl⟩ t; fin_cases i <;>
      rw [Perm.sign_swap (Fin.castSucc_lt_succ _).ne, Units.neg_smul, one_smul]
    exacts [rel₄_swap₀₁ neg, rel₄_swap₁₂ neg, rel₄_swap₂₃ neg]
  rw [Perm.coe_mul, ← Function.comp.assoc, hτ, hσ, map_mul, mul_comm, mul_smul]

lemma relFin4_perm' (σ : Perm (Fin 4)) (t) : Perm.sign σ • relFin4 W (t ∘ σ) = relFin4 W t := by
  rw [relFin4_perm neg, ← mul_smul, Int.units_mul_self, one_smul]

variable (zero : W 0 = 0)
include zero

/-! `rel₄` is trivial when two indices are equal. -/

lemma rel₄_same₀₁ (m r s : ℤ) : rel₄ W m m r s = 0 := by
  simp_rw [rel₄, addMulSub_same W zero]; ring

lemma rel₄_same₁₂ (m n s : ℤ) : rel₄ W m n n s = 0 := by
  simp_rw [rel₄, addMulSub_same W zero]; ring

lemma rel₄_same₂₃ (m n r : ℤ) : rel₄ W m n r r = 0 := by
  simp_rw [rel₄, addMulSub_same W zero]; ring

variable (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
  (oddRec : ∀ m ≥ 2, OddRec W m) (evenRec : ∀ m ≥ 3, EvenRec W m)
include one two oddRec evenRec

/-- The four-index `rel₄` relations follow from
the single-index `oddRec` and `evenRec` recursive relations. -/
theorem rel₄_of_oddRec_evenRec {a b c d : ℤ} (same : HaveSameParity₄ a b c d) :
    rel₄ W a b c d = 0 := by
  let t := ![|a|, |b|, |c|, |d|]
  have nonneg i : 0 ≤ t i := by fin_cases i <;> exact abs_nonneg _
  let σ := Fin.revPerm.trans (Tuple.sort t)
  have anti : Antitone (t ∘ σ) := by
    simp_rw [σ, coe_trans, ← Function.comp.assoc]
    exact (Tuple.monotone_sort t).comp_antitone fun _ _ ↦ Fin.rev_le_rev.mpr
  clear_value σ -- otherwise, unifying `t (σ i)` with `(t ∘ σ) i` is extremely slow
  rw [← rel₄_abs neg]; change relFin4 W t = 0
  rw [← relFin4_perm' neg σ, relFin4]; simp_rw [Function.comp]
  by_cases h₃₂ : t (σ 3) = t (σ 2); · rw [h₃₂, rel₄_same₂₃ zero, smul_zero]
  by_cases h₂₁ : t (σ 2) = t (σ 1); · rw [h₂₁, rel₄_same₁₂ zero, smul_zero]
  by_cases h₁₀ : t (σ 1) = t (σ 0); · rw [h₁₀, rel₄_same₀₁ zero, smul_zero]
  rw [rel₄_of_anti_oddRec_evenRec one two oddRec evenRec (same.abs.perm _ _), smul_zero]
  exact ⟨nonneg _, (anti <| by decide).lt_of_ne h₃₂,
    (anti <| by decide).lt_of_ne h₂₁, (anti <| by decide).lt_of_ne h₁₀⟩

/-- An ℕ-indexed sequence satisfying the even-odd recurrence, after extension to all integers
by symmetry (to make an odd function), is an elliptic sequence, provided its first two terms
are not zero divisors. -/
theorem _root_.IsEllSequence.of_oddRec_evenRec : IsEllSequence W := fun m n r ↦ by
  rw [rel₃_iff₄, rel₄_of_oddRec_evenRec neg zero one two oddRec evenRec]
  refine ⟨?_, ?_, ?_⟩ <;> simp only [negOnePow_two_mul, negOnePow_zero]

end Perm

end EllSequence

open EllSequence

/-- The proposition that a sequence indexed by integers is a divisibility sequence. -/
def IsDivSequence : Prop :=
  ∀ m n : ℤ, m ∣ n → W m ∣ W n

/-- The proposition that a sequence indexed by integers is an EDS. -/
def IsEllDivSequence : Prop :=
  IsEllSequence W ∧ IsDivSequence W

lemma isEllSequence_id : IsEllSequence id :=
  fun _ _ _ ↦ by simp only [Rel₃, id_eq]; ring1

lemma isDivSequence_id : IsDivSequence id :=
  fun _ _ ↦ id

/-- The identity sequence is an EDS. -/
theorem isEllDivSequence_id : IsEllDivSequence id :=
  ⟨isEllSequence_id, isDivSequence_id⟩

variable {W}

lemma IsEllSequence.smul (h : IsEllSequence W) (x : R) : IsEllSequence (x • W) :=
  fun m n r ↦ show _ = _ by linear_combination
    (norm := (simp only [Pi.smul_apply, smul_eq_mul]; ring1)) x ^ 4 * (show _ = _ from h m n r)

lemma IsDivSequence.smul (h : IsDivSequence W) (x : R) : IsDivSequence (x • W) :=
  (mul_dvd_mul_left x <| h · · ·)

lemma IsEllDivSequence.smul (h : IsEllDivSequence W) (x : R) : IsEllDivSequence (x • W) :=
  ⟨h.left.smul x, h.right.smul x⟩

lemma IsEllSequence.map (h : IsEllSequence W) : IsEllSequence (f ∘ W) := by
  simpa using (congr_arg f <| h · · ·)

lemma IsDivSequence.map (h : IsDivSequence W) : IsDivSequence (f ∘ W) :=
  (map_dvd f <| h · · ·)

lemma IsEllDivSequence.map (h : IsEllDivSequence W) : IsEllDivSequence (f ∘ W) :=
  ⟨h.1.map f, h.2.map f⟩

namespace IsEllSequence

open EllSequence

variable (ell : IsEllSequence W)
include ell

lemma oddRec (m : ℤ) : OddRec W m := (rel₃_iff_oddRec W m).mp (ell _ _ _)
lemma evenRec (m : ℤ) : EvenRec W m := (rel₃_iff_evenRec W m).mp (ell _ _ _)

lemma zero' [IsReduced R] : W 0 = 0 := by
  have := ell 0 0 0
  simp_rw [Rel₃, add_zero, sub_self, mul_assoc, ← pow_succ'] at this
  exact IsReduced.eq_zero _ ⟨_, this⟩

/-- The zeroth term of an elliptic sequence is zero,
provided some even term is not a zero divisor. -/
lemma zero (m : ℤ) (mem : W (2 * m) ∈ R⁰) : W 0 = 0 := by
  have := ell m m (2 * m)
  rw [Rel₃, add_comm, sub_self, sub_self, ← two_mul, mul_comm (W _)] at this
  exact mem _ (pow_mem mem 2 _ this)

lemma sub_add_neg_sub_mul_eq_zero (m n r : ℤ) :
    (W (m - n) + W (-(m - n))) * W (m + n) * W r ^ 2 = 0 := by
  have := congr($(ell m n r) + $(ell n m r))
  rw [add_comm n, ← right_distrib, ← left_distrib, mul_comm (W _)] at this
  convert this using 4 <;> ring_nf

variable (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
include one two

/-- An elliptic sequence is an odd function, provided its first two terms are not zero divisors. -/
lemma neg (m : ℤ) : W (-m) = - W m := by
  rw [eq_neg_iff_add_eq_zero]
  obtain ⟨m, rfl|rfl⟩ := m.even_or_odd'
  on_goal 1 => apply two
  on_goal 2 => apply one
  all_goals apply pow_mem one 2
  · convert sub_add_neg_sub_mul_eq_zero ell (1 - m) (m + 1) 1 using 2; ring_nf
  · convert sub_add_neg_sub_mul_eq_zero ell (-m) (m + 1) 1 using 2; ring_nf

protected lemma rel₄ {a b c d : ℤ} (same : HaveSameParity₄ a b c d) : rel₄ W a b c d = 0 :=
  rel₄_of_oddRec_evenRec (ell.neg one two) (ell.zero 1 two) one two
    (fun _ _ ↦ ell.oddRec _) (fun _ _ ↦ ell.evenRec _) same

protected lemma net (p q r s : ℤ) : net W p q r s = 0 := by
  rw [net_eq_rel₄]
  refine ell.rel₄ one two ?_
  simp_rw [HaveSameParity₄, Int.negOnePow_add, Int.negOnePow_two_mul, one_mul, true_and]

lemma invar (s m n : ℤ) : invarNum W s m * invarDenom W s n = invarNum W s n * invarDenom W s m :=
  invar_of_net _ (ell.net one two) _ _ _

end IsEllSequence

/-- The auxiliary sequence for a normalised EDS `W : ℕ → R`,
with initial values `W(0) = 0`, `W(1) = 1`, `W(2) = 1`, `W(3) = c`, and `W(4) = d`. -/
def preNormEDS' (b c d : R) : ℕ → R
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => c
  | 4 => d
  | (n + 5) => letI m := n / 2
    have h4 : m + 4 < n + 5 := Nat.lt_succ.mpr <| add_le_add_right (n.div_le_self 2) 4
    have h3 : m + 3 < n + 5 := (lt_add_one _).trans h4
    have h2 : m + 2 < n + 5 := (lt_add_one _).trans h3
    have h1 : m + 1 < n + 5 := (lt_add_one _).trans h2
    if hn : Even n then
      preNormEDS' (m + 4) * preNormEDS' (m + 2) ^ 3 * (if Even m then b else 1) -
        preNormEDS' (m + 1) * preNormEDS' (m + 3) ^ 3 * (if Even m then 1 else b)
    else
      have : m + 5 < n + 5 := by
        gcongr; exact Nat.div_lt_self (Nat.not_even_iff_odd.mp hn).pos one_lt_two
      preNormEDS' (m + 2) ^ 2 * preNormEDS' (m + 3) * preNormEDS' (m + 5) -
        preNormEDS' (m + 1) * preNormEDS' (m + 3) * preNormEDS' (m + 4) ^ 2

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

lemma preNormEDS'_even (m : ℕ) : preNormEDS' b c d (2 * (m + 3)) =
    preNormEDS' b c d (m + 2) ^ 2 * preNormEDS' b c d (m + 3) * preNormEDS' b c d (m + 5) -
      preNormEDS' b c d (m + 1) * preNormEDS' b c d (m + 3) * preNormEDS' b c d (m + 4) ^ 2 := by
  rw [show 2 * (m + 3) = 2 * m + 1 + 5 by rfl, preNormEDS', dif_neg m.not_even_two_mul_add_one]
  simpa only [Nat.mul_add_div two_pos] using by rfl

lemma preNormEDS'_odd (m : ℕ) : preNormEDS' b c d (2 * (m + 2) + 1) =
    preNormEDS' b c d (m + 4) * preNormEDS' b c d (m + 2) ^ 3 * (if Even m then b else 1) -
      preNormEDS' b c d (m + 1) * preNormEDS' b c d (m + 3) ^ 3 * (if Even m then 1 else b) := by
  rw [show 2 * (m + 2) + 1 = 2 * m + 5 by rfl, preNormEDS', dif_pos <| even_two_mul m,
    m.mul_div_cancel_left two_pos]

/-- The auxiliary sequence for a normalised EDS `W : ℤ → R`, with initial values
`W(0) = 0`, `W(1) = 1`, `W(2) = 1`, `W(3) = c`, and `W(4) = d` and extra parameter `b`.

This extends `preNormEDS'` by defining its values at negative integers. -/
def preNormEDS (n : ℤ) : R :=
  n.sign * preNormEDS' b c d n.natAbs

@[simp]
lemma preNormEDS_ofNat (n : ℕ) : preNormEDS b c d n = preNormEDS' b c d n := by
  by_cases hn : n = 0
  · simp [hn, preNormEDS]
  · simp [preNormEDS, Int.sign_natCast_of_ne_zero hn]

@[simp]
lemma preNormEDS_zero : preNormEDS b c d 0 = 0 := by
  simp [preNormEDS]

@[simp]
lemma preNormEDS_one : preNormEDS b c d 1 = 1 := by
  simp [preNormEDS]

@[simp]
lemma preNormEDS_two : preNormEDS b c d 2 = 1 := by
  simp [preNormEDS, Int.sign_eq_one_of_pos]

@[simp]
lemma preNormEDS_three : preNormEDS b c d 3 = c := by
  simp [preNormEDS, Int.sign_eq_one_of_pos]

@[simp]
lemma preNormEDS_four : preNormEDS b c d 4 = d := by
  simp [preNormEDS, Int.sign_eq_one_of_pos]

@[simp]
lemma preNormEDS_neg (n : ℤ) : preNormEDS b c d (-n) = -preNormEDS b c d n := by
  simp [preNormEDS]

lemma preNormEDS_even (m : ℤ) : preNormEDS b c d (2 * m) =
    preNormEDS b c d (m - 1) ^ 2 * preNormEDS b c d m * preNormEDS b c d (m + 2) -
      preNormEDS b c d (m - 2) * preNormEDS b c d m * preNormEDS b c d (m + 1) ^ 2 := by
  induction m using Int.negInduction with
  | nat m =>
    rcases m with _ | _ | _ | m
    iterate 3 simp
    simp_rw [Nat.cast_succ, Int.add_sub_cancel, show (m : ℤ) + 1 + 1 + 1 = m + 1 + 2 by rfl,
      Int.add_sub_cancel]
    norm_cast
    simpa only [preNormEDS_ofNat] using preNormEDS'_even ..
  | neg ih m =>
    simp_rw [mul_neg, ← sub_neg_eq_add, ← neg_sub', ← neg_add', preNormEDS_neg, ih]
    ring1

lemma preNormEDS_odd (m : ℤ) : preNormEDS b c d (2 * m + 1) =
    preNormEDS b c d (m + 2) * preNormEDS b c d m ^ 3 * (if Even m then b else 1) -
      preNormEDS b c d (m - 1) * preNormEDS b c d (m + 1) ^ 3 * (if Even m then 1 else b) := by
  induction m using Int.negInduction with
  | nat m =>
    rcases m with _ | _ | _
    iterate 2 simp
    simp_rw [Nat.cast_succ, Int.add_sub_cancel, Int.even_add_one, not_not, Int.even_coe_nat]
    norm_cast
    simpa only [preNormEDS_ofNat] using preNormEDS'_odd ..
  | neg ih m =>
    rcases m with _ | m
    · simp
    simp_rw [Nat.cast_succ, show 2 * -(m + 1 : ℤ) + 1 = -(2 * m + 1) by rfl,
      show -(m + 1 : ℤ) + 2 = -(m - 1) by ring1, show -(m + 1 : ℤ) - 1 = -(m + 2) by rfl,
      show -(m + 1 : ℤ) + 1 = -m by ring1, preNormEDS_neg, even_neg, Int.even_add_one, ite_not, ih]
    ring1

/-- The 2-complement sequence `Wᶜ₂ : ℤ → R` for a normalised EDS `W : ℤ → R` that witnesses
`W(k) ∣ W(2 * k)`. In other words, `W(k) * Wᶜ₂(k) = W(2 * k)` for any `k ∈ ℤ`.

This is defined in terms of `preNormEDS`. -/
def complEDS₂ (k : ℤ) : R :=
  (preNormEDS (b ^ 4) c d (k - 1) ^ 2 * preNormEDS (b ^ 4) c d (k + 2) -
    preNormEDS (b ^ 4) c d (k - 2) * preNormEDS (b ^ 4) c d (k + 1) ^ 2) * if Even k then 1 else b

@[simp]
lemma complEDS₂_zero : complEDS₂ b c d 0 = 2 := by
  simp [complEDS₂, one_add_one_eq_two]

@[simp]
lemma complEDS₂_one : complEDS₂ b c d 1 = b := by
  simp [complEDS₂]

@[simp]
lemma complEDS₂_two : complEDS₂ b c d 2 = d := by
  simp [complEDS₂]

@[simp]
lemma complEDS₂_three : complEDS₂ b c d 3 = preNormEDS (b ^ 4) c d 5 * b - d ^ 2 * b := by
  simp [complEDS₂, if_neg (by decide : ¬Even (3 : ℤ)), sub_mul]

@[simp]
lemma complEDS₂_four : complEDS₂ b c d 4 =
    c ^ 2 * preNormEDS (b ^ 4) c d 6 - preNormEDS (b ^ 4) c d 5 ^ 2 := by
  simp [complEDS₂, if_pos (by decide : Even (4 : ℤ))]

@[simp]
lemma complEDS₂_neg (k : ℤ) : complEDS₂ b c d (-k) = complEDS₂ b c d k := by
  simp_rw [complEDS₂, ← neg_add', ← sub_neg_eq_add, ← neg_sub', preNormEDS_neg, even_neg]
  ring1

lemma preNormEDS_mul_complEDS₂ (k : ℤ) : preNormEDS (b ^ 4) c d k * complEDS₂ b c d k =
    preNormEDS (b ^ 4) c d (2 * k) * if Even k then 1 else b := by
  rw [complEDS₂, preNormEDS_even]
  ring1

end PreNormEDS

section NormEDS

/-- The canonical example of a normalised EDS `W : ℤ → R`, with initial values
`W(0) = 0`, `W(1) = 1`, `W(2) = b`, `W(3) = c`, and `W(4) = d * b`.

This is defined in terms of `preNormEDS` whose even terms differ by a factor of `b`. -/
def normEDS (n : ℤ) : R :=
  preNormEDS (b ^ 4) c d n * if Even n then b else 1

lemma normEDS_def (n : ℤ) :
    normEDS b c d n = preNormEDS (b ^ 4) c d n * if Even n then b else 1 := rfl

@[simp]
lemma normEDS_ofNat (n : ℕ) :
    normEDS b c d n = preNormEDS' (b ^ 4) c d n * if Even n then b else 1 := by
  simp_rw [normEDS, preNormEDS_ofNat, Int.even_coe_nat]

@[simp]
lemma normEDS_zero : normEDS b c d 0 = 0 := by
  simp [normEDS]

@[simp]
lemma normEDS_one : normEDS b c d 1 = 1 := by
  simp [normEDS]

@[simp]
lemma normEDS_two : normEDS b c d 2 = b := by
  simp [normEDS]

@[simp]
lemma normEDS_three : normEDS b c d 3 = c := by
  simp [normEDS, show ¬Even (3 : ℤ) by decide]

@[simp]
lemma normEDS_four : normEDS b c d 4 = d * b := by
  simp [normEDS, show ¬Odd (4 : ℤ) by decide]

@[simp]
lemma normEDS_neg (n : ℤ) : normEDS b c d (-n) = -normEDS b c d n := by
  simp_rw [normEDS, preNormEDS_neg, neg_mul, even_neg]

lemma normEDS_mul_complEDS₂ (k : ℤ) :
    normEDS b c d k * complEDS₂ b c d k = normEDS b c d (2 * k) := by
  simp_rw [normEDS, mul_right_comm, preNormEDS_mul_complEDS₂, mul_assoc, apply_ite₂, one_mul,
    mul_one, ite_self, if_pos <| even_two_mul k]

lemma normEDS_dvd_normEDS_two_mul (k : ℤ) : normEDS b c d k ∣ normEDS b c d (2 * k) :=
  ⟨complEDS₂ .., (normEDS_mul_complEDS₂ ..).symm⟩

lemma complEDS₂_mul_b (k : ℤ) : complEDS₂ b c d k * b =
    normEDS b c d (k - 1) ^ 2 * normEDS b c d (k + 2) -
      normEDS b c d (k - 2) * normEDS b c d (k + 1) ^ 2 := by
  induction k using Int.negInduction with
  | nat k =>
    simp_rw [complEDS₂, normEDS, Int.even_add, Int.even_sub, even_two, iff_true, Int.not_even_one,
      iff_false]
    split_ifs <;> ring1
  | neg ih =>
    simp_rw [complEDS₂_neg, ← sub_neg_eq_add, ← neg_sub', ← neg_add', normEDS_neg, ih]
    ring1

lemma normEDS_even (m : ℤ) : normEDS b c d (2 * m) * b =
    normEDS b c d (m - 1) ^ 2 * normEDS b c d m * normEDS b c d (m + 2) -
      normEDS b c d (m - 2) * normEDS b c d m * normEDS b c d (m + 1) ^ 2 := by
  rw [← normEDS_mul_complEDS₂, mul_assoc, complEDS₂_mul_b]
  ring1

lemma normEDS_odd (m : ℤ) : normEDS b c d (2 * m + 1) =
    normEDS b c d (m + 2) * normEDS b c d m ^ 3 -
      normEDS b c d (m - 1) * normEDS b c d (m + 1) ^ 3 := by
  simp_rw [normEDS, preNormEDS_odd, if_neg m.not_even_two_mul_add_one, Int.even_add, Int.even_sub,
    even_two, iff_true, Int.not_even_one, iff_false]
  split_ifs <;> ring1

/- superseded by `IsEllSequence.normEDS` which doesn't require `hb`. -/
private theorem IsEllSequence.normEDS_of_mem_nonZeroDivisors (hb : b ∈ R⁰) :
    IsEllSequence (normEDS b c d) := by
  refine IsEllSequence.of_oddRec_evenRec (normEDS_neg _ _ _) (normEDS_zero _ _ _)
    (by rw [normEDS_one]; exact one_mem _) (by rwa [normEDS_two]) ?_ ?_ <;>
    intro m hm <;> rw [GE.ge, ← sub_nonneg] at hm
  · lift m - 2 to ℕ using hm with k hk
    rw [← eq_sub_iff_add_eq.mp hk, OddRec, normEDS_one, one_pow, mul_one, ← add_sub]
    exact normEDS_odd _ _ _ k
  · lift m - 3 to ℕ using hm with k hk
    rw [← eq_sub_iff_add_eq.mp hk, EvenRec, normEDS_one, normEDS_two, one_pow, mul_one]
    convert normEDS_even _ _ _ k using 1; ring_nf

lemma invarNum_normEDS (n : ℤ) : letI W := normEDS b c d
    invarNum W 1 n = W (n + 2) * W (n - 1) ^ 2 + W (n + 1) ^ 2 * W (n - 2) + W n ^ 3 * b ^ 2 := by
  simp [invarNum]

lemma invarNum_normEDS_two : invarNum (normEDS b c d) 1 2 = (d + b ^ 4) * b := by
  simp [invarNum, right_distrib, ← pow_succ, ← pow_add]

lemma invarDenom_normEDS_two : invarDenom (normEDS b c d) 1 2 = c * b := by simp [invarDenom]

/-- Strong recursion principle for a normalised EDS indexed by `ℕ`: if we have
 * `P 0`, `P 1`, `P 2`, `P 3`, and `P 4`,
 * for all `m : ℕ` we can prove `P (2 * (m + 3))` from `P k` for all `k < 2 * (m + 3)`, and
 * for all `m : ℕ` we can prove `P (2 * (m + 2) + 1)` from `P k` for all `k < 2 * (m + 2) + 1`,
then we have `P n` for all `n : ℕ`. -/
@[elab_as_elim]
noncomputable def normEDSRec' {P : ℕ → Sort u}
    (zero : P 0) (one : P 1) (two : P 2) (three : P 3) (four : P 4)
    (even : ∀ m : ℕ, (∀ k < 2 * (m + 3), P k) → P (2 * (m + 3)))
    (odd : ∀ m : ℕ, (∀ k < 2 * (m + 2) + 1, P k) → P (2 * (m + 2) + 1)) (n : ℕ) : P n :=
  n.evenOddStrongRec (by rintro (_ | _ | _ | _) h; exacts [zero, two, four, even _ h])
    (by rintro (_ | _ | _) h; exacts [one, three, odd _ h])

/-- Recursion principle for a normalised EDS: if we have
* `P 0`, `P 1`, `P 2`, `P 3`, and `P 4`,
* for all `m : ℕ` we can prove `P (2 * (m + 3))` from `P (m + 1)`, `P (m + 2)`, `P (m + 3)`,
  `P (m + 4)`, and `P (m + 5)`, and
* for all `m : ℕ` we can prove `P (2 * (m + 2) + 1)` from `P (m + 1)`, `P (m + 2)`, `P (m + 3)`,
  and `P (m + 4)`,
then we have `P n` for all `n : ℕ`. -/
@[elab_as_elim]
noncomputable def normEDSRec {P : ℕ → Sort u}
    (zero : P 0) (one : P 1) (two : P 2) (three : P 3) (four : P 4)
    (even : ∀ m : ℕ, P (m + 1) → P (m + 2) → P (m + 3) → P (m + 4) → P (m + 5) → P (2 * (m + 3)))
    (odd : ∀ m : ℕ, P (m + 1) → P (m + 2) → P (m + 3) → P (m + 4) → P (2 * (m + 2) + 1)) (n : ℕ) :
    P n :=
  normEDSRec' zero one two three four (fun _ ih => by apply even <;> exact ih _ <| by linarith only)
    (fun _ ih => by apply odd <;> exact ih _ <| by linarith only) n

section Complement

variable (b c d : R) (m : ℤ)

/-- An auxiliary expression that appears in the definition of the numerator of
the reduced invariant and in the definition of the `ω` family of division polynomials. -/
def compl₂EDSAux : R :=
  preNormEDS (b ^ 4) c d (m - 2) * preNormEDS (b ^ 4) c d (m + 1) ^ 2 * if Even m then 1 else b

@[simp] lemma compl₂EDSAux_zero : compl₂EDSAux b c d 0 = -1 := by simp [compl₂EDSAux]
@[simp] lemma compl₂EDSAux_one : compl₂EDSAux b c d 1 = -b := by simp [compl₂EDSAux]
@[simp] lemma compl₂EDSAux_neg_one : compl₂EDSAux b c d (-1) = 0 := by simp [compl₂EDSAux]
@[simp] lemma compl₂EDSAux_two : compl₂EDSAux b c d 2 = 0 := by simp [compl₂EDSAux]
@[simp] lemma compl₂EDSAux_neg_two : compl₂EDSAux b c d (-2) = -d := by simp [compl₂EDSAux]

lemma compl₂EDSAux_mul_b :
    compl₂EDSAux b c d m * b = normEDS b c d (m - 2) * normEDS b c d (m + 1) ^ 2 := by
  simp_rw [compl₂EDSAux, normEDS, Int.even_add, Int.even_sub, Int.not_even_one, even_two,
    iff_false, iff_true]; split_ifs <;> ring

/-- The "complement" of W(m) in W(2m) for a normalised EDS W is the witness of W(m) ∣ W(2m). -/
def compl₂EDS : R :=
  letI p := preNormEDS (b ^ 4) c d
  (p (m - 1) ^ 2 * p (m + 2) - p (m - 2) * p (m + 1) ^ 2) * if Even m then 1 else b

lemma compl₂EDSAux_neg : compl₂EDSAux b c d (-m) = -compl₂EDS b c d m - compl₂EDSAux b c d m := by
  simp_rw [compl₂EDSAux, compl₂EDS, neg_sub_left, neg_add_eq_sub, ← neg_sub m,
    preNormEDS_neg, even_neg]; ring_nf

@[simp] lemma compl₂EDS_zero : compl₂EDS b c d 0 = 2 := by simp [compl₂EDS, one_add_one_eq_two]
@[simp] lemma compl₂EDS_one : compl₂EDS b c d 1 = b := by simp [compl₂EDS]
@[simp] lemma compl₂EDS_two : compl₂EDS b c d 2 = d := by simp [compl₂EDS]

@[simp] lemma compl₂EDS_neg : compl₂EDS b c d (-m) = compl₂EDS b c d m := by
  simp_rw [compl₂EDS, neg_sub_left, neg_add_eq_sub, ← neg_sub m, preNormEDS_neg, even_neg]; ring_nf

lemma normEDS_mul_compl₂EDS :
    normEDS b c d m * compl₂EDS b c d m = normEDS b c d (2 * m) := by
  induction m using Int.negInduction with
  | nat m =>
    obtain _|_|_|m := m
    iterate 3 simp [mul_comm]
    simp_rw [show m + 1 + 1 + 1 = m + 3 by rfl, normEDS, compl₂EDS,
      if_pos (even_two_mul _), Nat.cast_add, Nat.cast_ofNat, preNormEDS_even]
    rw [mul_mul_mul_comm]; congr
    · ring_nf
    · split_ifs <;> simp only [one_mul, mul_one]
  | neg m hm => simp_rw [mul_neg, normEDS_neg, compl₂EDS_neg, neg_mul, hm]

lemma normEDS_dvd_two_mul : normEDS b c d m ∣ normEDS b c d (2 * m) :=
  ⟨_, (normEDS_mul_compl₂EDS b c d m).symm⟩

lemma compl₂EDS_mul_b : letI W := normEDS b c d
    compl₂EDS b c d m * b = W (m - 1) ^ 2 * W (m + 2) - W (m - 2) * W (m + 1) ^ 2 := by
  induction m using Int.negInduction with
  | nat m =>
    simp_rw [compl₂EDS, normEDS, Int.even_sub, Int.even_add,
      Int.not_even_one, even_two, iff_false, iff_true]
    split_ifs <;> ring
  | neg m hm =>
    simp_rw [← neg_add', neg_add_eq_sub, ← neg_sub (m : ℤ), normEDS_neg, compl₂EDS_neg]
    convert hm using 1; ring

lemma normEDS_six_eq_mul : normEDS b c d 6 = (normEDS b c d 5 - d ^ 2) * b * c := by
  rw [show (6 : ℤ) = 2 * 3 by rfl, ← normEDS_mul_compl₂EDS, compl₂EDS, if_neg (by decide)]
  simp_rw [Int.reduceAdd, Int.reduceSub, normEDS_three, normEDS]
  rw [preNormEDS_one, preNormEDS_two, preNormEDS_four, if_neg (by decide)]
  ring

namespace EllSequence

variable (W₁ compl₂ : ℤ → R) (m : ℤ)

/-- Given two sequences representing `W(m)/W(1)` and `W(2m)/W(m)` respectively,
we construct the sequence representing `W(n*m)/W(m)` in a division-free way. -/
def compl' : ℕ → R
  | 0 => 0
  | 1 => 1
  | (n + 2) => letI k := n / 2 + 1
    have : k < n + 2 := Nat.lt_succ.mpr <| add_le_add_right (n.div_le_self 2) 1
    if hn : Even n
      then compl₂ (k * m) * compl' k
      else
        have : k + 1 < n + 2 := add_lt_add_right
          (Nat.div_lt_self (Nat.odd_iff_not_even.mpr hn).pos <| Nat.lt_succ_self 1) 2
        W₁ ((k + 1) * m + 1) * W₁ ((k + 1) * m - 1) * compl' k ^ 2
      - W₁ (k * m + 1) * W₁ (k * m - 1) * compl' (k + 1) ^ 2

/-- `W(n*m)/W(m)` with `n : ℤ`. -/
def compl (n : ℤ) : R := n.sign * compl' W₁ compl₂ m n.natAbs

lemma compl_ofNat (n : ℕ) : compl W₁ compl₂ m n = compl' W₁ compl₂ m n := by
  obtain _|n := n; · simp [compl, compl']
  rw [compl, Int.natAbs_cast]; simp

lemma compl_neg (n : ℤ) : compl W₁ compl₂ m (-n) = -compl W₁ compl₂ m n := by simp [compl]

/-- `W(n*m)/W(m)` for `W` a normalised EDS. -/
def complEDS := compl (normEDS b c d) (compl₂EDS b c d) m

end EllSequence

end Complement

section Map

variable {b c d}

lemma map_preNormEDS' (n : ℕ) : f (preNormEDS' b c d n) = preNormEDS' (f b) (f c) (f d) n := by
  induction n using normEDSRec' with
  | zero => rw [preNormEDS'_zero, map_zero, preNormEDS'_zero]
  | one => rw [preNormEDS'_one, map_one, preNormEDS'_one]
  | two => rw [preNormEDS'_two, map_one, preNormEDS'_two]
  | three => rw [preNormEDS'_three, preNormEDS'_three]
  | four => rw [preNormEDS'_four, preNormEDS'_four]
  | _ _ ih =>
    simp only [preNormEDS'_odd, preNormEDS'_even, map_one, map_sub, map_mul, map_pow, apply_ite f]
    repeat rw [ih _ <| by linarith only]

lemma map_preNormEDS (n : ℤ) : f (preNormEDS b c d n) = preNormEDS (f b) (f c) (f d) n := by
  rw [preNormEDS, map_mul, map_intCast, map_preNormEDS', preNormEDS]

lemma map_normEDS (n : ℤ) : f (normEDS b c d n) = normEDS (f b) (f c) (f d) n := by
  rw [normEDS, map_mul, map_preNormEDS, map_pow, apply_ite f, map_one, normEDS]

lemma map_compl₂EDS (n : ℤ) : f (compl₂EDS b c d n) = compl₂EDS (f b) (f c) (f d) n := by
  simp only [compl₂EDS, map_sub, map_mul, map_pow, map_preNormEDS, apply_ite f, map_one]

lemma EllSequence.map_compl' (W₁ compl₂ : ℤ → R) (m : ℤ) (n : ℕ) :
    f (compl' W₁ compl₂ m n) = compl' (f ∘ W₁) (f ∘ compl₂) m n := by
  refine n.strong_induction_on fun n ih ↦ ?_
  obtain _|_|n := n
  iterate 2 simp [compl']
  rw [compl']; conv_rhs => rw [compl']
  split_ifs with hn
  · rw [map_mul, ih _ (by omega)]; rfl
  simp_rw [map_sub, map_mul, map_pow]
  rw [ih _ (by omega), ih]; · rfl
  exact add_lt_add_right (Nat.div_lt_self (Nat.odd_iff_not_even.mpr hn).pos <| Nat.lt_succ_self 1) 2

lemma EllSequence.map_compl (W₁ compl₂ : ℤ → R) (m n : ℤ) :
    f (compl W₁ compl₂ m n) = compl (f ∘ W₁) (f ∘ compl₂) m n := by
  simp [compl, map_compl']

lemma map_complEDS (m n : ℤ) : f (complEDS b c d m n) = complEDS (f b) (f c) (f d) m n := by
  simp_rw [complEDS, map_compl, Function.comp, map_normEDS, map_compl₂EDS]

lemma map_addMulSub (m n : ℤ) : f (addMulSub W m n) = addMulSub (f ∘ W) m n := by
  simp_rw [addMulSub, map_mul, Function.comp]

lemma map_rel₄ (p q r s : ℤ) : f (rel₄ W p q r s) = rel₄ (f ∘ W) p q r s := by
  simp_rw [rel₄, map_add, map_sub, map_mul, map_addMulSub]

lemma map_net (p q r s : ℤ) : f (net W p q r s) = net (f ∘ W) p q r s := by
  simp_rw [net_eq_rel₄, map_rel₄]

lemma map_invarNum (s m : ℤ) : f (invarNum W s m) = invarNum (f ∘ W) s m := by
  simp only [invarNum, map_add, map_mul, map_pow, Function.comp]

lemma map_invarDenom (s m : ℤ) : f (invarDenom W s m) = invarDenom (f ∘ W) s m := by
  simp_rw [invarDenom, map_mul, Function.comp]

/-- A type of three elements corresponding to the three parameters of a normalised EDS. -/
inductive Param : Type | B : Param | C : Param | D : Param

open Param MvPolynomial
/-- The universal normalised EDS, from which every normalised EDS can be obtained by
composing with a ring homomorphism, which allows us to reduce equalities between
expressions involving terms of a normalised EDS to the universal case.
It takes values in a domain, and all nonzero terms are nonzero and therefore
are not zero divisors, a condition required to apply certain lemmas. -/
noncomputable def universalNormEDS : ℤ → MvPolynomial Param ℤ := normEDS (X B) (X C) (X D)

lemma normEDS_eq_aeval : normEDS b c d = (aeval (Param.rec b c d) <| universalNormEDS ·) := by
  simp_rw [universalNormEDS, map_normEDS, aeval_X]

lemma compl₂EDS_eq_aeval :
    compl₂EDS b c d =
      (aeval (Param.rec b c d) <| compl₂EDS (X (R := ℤ) B) (X C) (X D) ·) := by
  simp_rw [map_compl₂EDS, aeval_X]

lemma complEDS_eq_aeval :
    complEDS b c d =
      (aeval (Param.rec b c d) <| complEDS (X (R := ℤ) B) (X C) (X D) · ·) := by
  simp_rw [map_complEDS, aeval_X]

end Map

section

variable {b c d} {U : ℤ → R} (ellW : IsEllSequence W) (ellU : IsEllSequence U)
include ellW ellU
open MvPolynomial

/-- A normalised EDS is in fact an elliptic sequenc. -/
protected lemma IsEllSequence.normEDS : IsEllSequence (normEDS b c d) := by
  rw [normEDS_eq_aeval]
  exact map _ (normEDS_of_mem_nonZeroDivisors _ _ _ (mem_nonZeroDivisors_of_ne_zero <| X_ne_zero _))

/-- Two elliptic sequences are equal if their first four terms are equal,
provided the first two terms are not zero divisors. -/
protected lemma IsEllSequence.ext (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (h1 : W 1 = U 1) (h2 : W 2 = U 2) (h3 : W 3 = U 3) (h4 : W 4 = U 4) : W = U :=
  funext fun n ↦ by
    induction n using Int.negInduction with
    | nat n =>
      refine normEDSRec ?_ h1 h2 h3 h4 (fun m h₁ h₂ h₃ h₄ h₅ ↦ ?_) (fun m h₁ h₂ h₃ h₄ ↦ ?_) n
      · rw [Nat.cast_zero, ellW.zero 1 two, ellU.zero 1 (h2 ▸ two)]
      · erw [← mul_cancel_right_mem_nonZeroDivisors (mul_mem two <| pow_mem one 2), ← mul_assoc,
          ← mul_assoc, Nat.cast_mul, Nat.cast_add, ellW.evenRec, h1, h2, ellU.evenRec]
        convert congr($h₃ * ($h₂ ^ 2 * $h₅ - $h₁ * $h₄ ^ 2)) <;> abel
      · rw [← mul_cancel_right_mem_nonZeroDivisors (pow_mem one 3)]
        erw [Nat.cast_add, Nat.cast_mul, Nat.cast_add, ellW.oddRec, h1, ellU.oddRec]
        convert congr($h₄ * $h₂ ^ 3 - $h₁ * $h₃ ^ 3) <;> abel
    | neg n hn =>
      rw [ellW.neg one two, ellU.neg (h1 ▸ one) (h2 ▸ two), hn]

lemma normEDS_two_three_two : normEDS 2 3 2 = id := by
  apply IsEllSequence.normEDS.ext isEllSequence_id <;>
    simp only [normEDS_one, normEDS_two, normEDS_three, normEDS_four]
  exacts [mem_nonZeroDivisors_of_ne_zero one_ne_zero,
    mem_nonZeroDivisors_of_ne_zero two_ne_zero, rfl, rfl, rfl, rfl]

lemma compl₂EDS_two_three_two (n : ℤ) : compl₂EDS (2 : ℤ) 3 2 n = 2 := by
  obtain rfl | hn := eq_or_ne n 0
  · exact compl₂EDS_zero ..
  · have := normEDS_mul_compl₂EDS (2 : ℤ) 3 2 n
    rwa [normEDS_two_three_two, id, id, mul_comm,
      mul_cancel_right_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hn)] at this

lemma universalNormEDS_ne_zero {n : ℤ} (hn : n ≠ 0) : universalNormEDS n ≠ 0 :=
  fun h ↦ hn <| by
    apply_fun aeval (Param.rec (2 : ℤ) 3 2) at h
    simpa [universalNormEDS, map_normEDS, normEDS_two_three_two] using h

lemma universalNormEDS_mem_nonZeroDivisors {n : ℤ} (hn : n ≠ 0) :
    universalNormEDS n ∈ (MvPolynomial Param ℤ)⁰ :=
  mem_nonZeroDivisors_of_ne_zero (universalNormEDS_ne_zero hn)

section Divisibility

variable (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
  (dvd₁₂ : W 1 ∣ W 2) (dvd₁₃ : W 1 ∣ W 3) (dvd₂₄ : W 2 ∣ W 4)
include one two dvd₁₂ dvd₁₃ dvd₂₄

theorem IsEllSequence.eq_normEDS_of_dvd : ∃ b c d, W = (W 1 * normEDS b c d ·) :=
  have ⟨b, h₁₂⟩ := dvd₁₂; have ⟨c, h₁₃⟩ := dvd₁₃; have ⟨d, h₂₄⟩ := dvd₂₄
  ⟨b, c, d, ellW.ext (IsEllSequence.normEDS.smul _)
    one two (by simp) (by simp [h₁₂]) (by simp [h₁₃]) (by rw [h₂₄, h₁₂, normEDS_four]; ring)⟩

/-- An EDS whose first two terms are not zero divisors
is a constant multiple of a normalised EDS. -/
theorem IsEllDivSequence.eq_normEDS (h : IsEllDivSequence W) :
    ∃ b c d, W = (W 1 * normEDS b c d ·) :=
  h.1.eq_normEDS_of_dvd one two (h.2 _ _ ⟨2, rfl⟩) (h.2 _ _ ⟨3, rfl⟩) (h.2 _ _ ⟨2, rfl⟩)

section Complement

variable (W₁ compl₂ : ℤ → R)
  (h₁ : ∀ m, W 1 * W₁ m = W m) (h₂ : ∀ m, W m * compl₂ m = W (2 * m)) (m n : ℤ)

/-- If `W` is an elliptic sequence whose first two terms are not zero divisors,
the sequence constructed above indeed gives `W(n*m)` when multiplied by `W(m)`.
The condition `mem` is actually redundant because `W` is a multiple of a normalised EDS
by the other assumptions, so we can conclude using `normEDS_mul_compl` below. -/
lemma IsEllSequence.mul_compl_eq_apply_mul_of_mem_nonZeroDivisors (mem : W m ∈ R⁰) :
    W m * compl W₁ compl₂ m n = W (n * m) := by
  induction n using Int.negInduction with
  | nat n =>
    refine n.strong_induction_on fun n ih ↦ ?_
    cases' n with n; · simp [EllSequence.compl, ellW.zero 1 two]
    cases' n with n; · simp [EllSequence.compl, compl']
    rw [EllSequence.compl, Int.sign_eq_one_of_pos (by omega),
      Int.natAbs_cast, compl', Int.cast_one, one_mul]
    obtain ⟨k, rfl|rfl⟩ := n.even_or_odd'
    · rw [dif_pos (even_two_mul _), k.mul_div_cancel_left zero_lt_two, mul_comm (compl₂ _),
        ← mul_assoc, ← compl_ofNat, ih _ (by omega), h₂, ← mul_assoc, add_assoc, ← two_mul,
        ← left_distrib, Nat.cast_mul]; rfl
    simp_rw [dif_neg (Nat.not_even_two_mul_add_one _), show (2 * k + 1) / 2 = k by omega]
    rw [← mul_cancel_right_mem_nonZeroDivisors (mul_mem mem <| pow_mem one 2)]
    have := (ellW ((k + 1 + 1) * m) ((k + 1) * m) 1).symm
    simp_rw [← right_distrib, ← mul_sub_right_distrib, add_sub_cancel_left,
      ← h₁ (_ + 1), ← h₁ (_ - 1), ← Nat.cast_one (R := ℤ), ← Nat.cast_add] at this
    rw [← ih _ (by omega), ← ih _ (by omega)] at this
    simp_rw [compl_ofNat, Nat.cast_add] at this ⊢
    convert this using 1
    · ring_nf
    rw [Nat.cast_mul]; ring_nf
  | neg n hn => rw [neg_mul, ellW.neg one two, compl_neg, mul_neg, hn]

lemma normEDS_mul_complEDS (m n : ℤ) :
    normEDS b c d m * complEDS b c d m n = normEDS b c d (n * m) := by
  obtain rfl|hm := eq_or_ne m 0; · simp
  rw [normEDS_eq_aeval, universalNormEDS, complEDS_eq_aeval, ← map_mul]; congr 1
  have := @universalNormEDS_mem_nonZeroDivisors
  exact IsEllSequence.normEDS.mul_compl_eq_apply_mul_of_mem_nonZeroDivisors (this one_ne_zero)
    (this two_ne_zero) _ _ (fun _ ↦ by simp) (fun _ ↦ normEDS_mul_compl₂EDS _ _ _ _) _ _ (this hm)

lemma normEDS_mul_complEDS_div (hm : m ≠ 0) (n : ℤ) (dvd : m ∣ n) :
    normEDS b c d m * complEDS b c d m (n / m) = normEDS b c d n := by
  obtain ⟨n, rfl⟩ := dvd
  rw [Int.mul_ediv_cancel_left _ hm, normEDS_mul_complEDS, mul_comm]

namespace EllSequence

variable (b c d)

/-- The numerator of the reduced invariant expression `(W(m-1)²W(m+2)+W(m-2)W(m+1)²+W₂²W(m)³)/W₂`
for a normalised EDS W, obtained by cancelling `W₃W₂ = b*c` from `invarNum`. -/
def redInvarNum : R :=
  compl₂EDS b c d m + normEDS b c d m ^ 3 * b + 2 * compl₂EDSAux b c d m

lemma compl₂EDS_eq_redInvarNum_sub :
    compl₂EDS b c d m =
      redInvarNum b c d m - normEDS b c d m ^ 3 * b - 2 * compl₂EDSAux b c d m := by
  rw [redInvarNum]; ring

lemma invarNum_eq_redInvarNum_mul : invarNum (normEDS b c d) 1 m = redInvarNum b c d m * b := by
  simp_rw [redInvarNum, right_distrib, compl₂EDS_mul_b, mul_assoc 2 _ b,
    compl₂EDSAux_mul_b, invarNum_normEDS]; ring

/-- The expression `W(m+1)W(m)W(m-1)/W₃W₂` for a normalised EDS. -/
def redInvarDenom : R :=
  letI C := complEDS b c d
  letI W := normEDS b c d
  letI r₆ := normEDS b c d 5 - d ^ 2 -- W₆/W₃W₂
  if m % 6 = 0 then r₆ * C 6 (m / 6) * W (m + 1) * W (m - 1) else
  if m % 6 = 1 then r₆ * C 6 ((m - 1) / 6) * W (m + 1) * W m else
  if m % 6 = 5 then r₆ * C 6 ((m + 1) / 6) * W m * W (m - 1) else
  if m % 6 = 2 then C 3 ((m + 1) / 3) * C 2 (m / 2) * W (m - 1) else
  if m % 6 = 4 then C 3 ((m - 1) / 3) * C 2 (m / 2) * W (m + 1) else
  if m % 6 = 3 then C 3 (m / 3) * C 2 ((m - 1) / 2) * W (m + 1) else 0

lemma invarDenom_eq_redInvarDenom_mul :
    invarDenom (normEDS b c d) 1 m = redInvarDenom b c d m * b * c := by
  have h6 : (6 : ℤ) ≠ 0 := by decide
  have h3 : (3 : ℤ) ≠ 0 := by decide
  have hd k m dvd eq :=
    (Int.dvd_iff_emod_eq_zero k m).mpr ((@Int.emod_emod_of_dvd m k 6 dvd).symm.trans eq)
  have hd2 {m} := hd 2 m ⟨3, rfl⟩
  have hd3 {m} := hd 3 m ⟨2, rfl⟩
  have mul_eq := @normEDS_mul_complEDS_div _ _ b c d
  rw [invarDenom, redInvarDenom]; split_ifs with h h h h h h -- slow
  · rw [← mul_eq _ h6 _ (Int.dvd_of_emod_eq_zero h), normEDS_six_eq_mul]; ring
  · rw [← mul_eq _ h6 _ (Int.dvd_sub_of_emod_eq h), normEDS_six_eq_mul]; ring
  · rw [show m + 1 = m + 6 - 5 by abel, ← mul_eq _ h6, normEDS_six_eq_mul]; ring
    exact Int.dvd_sub_of_emod_eq (Int.add_emod_self.trans h)
  on_goal 1 => rw [← mul_eq _ h3 _ (hd3 <| by simp [h, Int.add_emod]),
    ← mul_eq _ two_ne_zero m (hd2 <| by simp [h])]
  on_goal 2 => rw [← mul_eq _ h3 (m - 1) (hd3 <| by simp [h, Int.sub_emod]),
    ← mul_eq _ two_ne_zero m (hd2 <| by simp [h])]
  on_goal 3 => rw [← mul_eq _ h3 m (hd3 <| by simp [h]),
    ← mul_eq _ two_ne_zero (m - 1) (hd2 <| by simp [h, Int.sub_emod])]
  on_goal 4 =>
    have h0 := Int.emod_nonneg m h6
    have lt := Int.emod_lt_of_pos m (show 0 < 6 by decide)
    interval_cases m % 6 <;> contradiction
  all_goals rw [normEDS_three, normEDS_two]; ring

@[simp] lemma redInvarDenom_zero : redInvarDenom b c d 0 = 0 := by
  simp [redInvarDenom, complEDS, compl', compl]

@[simp] lemma redInvarDenom_one : redInvarDenom b c d 1 = 0 := by
  simp [redInvarDenom, complEDS, compl', compl]

@[simp] lemma redInvarDenom_two : redInvarDenom b c d 2 = 1 := by
  simp [redInvarDenom, complEDS, compl', compl]

lemma map_compl₂EDSAux : f (compl₂EDSAux b c d m) = compl₂EDSAux (f b) (f c) (f d) m := by
  simp [compl₂EDSAux, apply_ite f, map_preNormEDS]

lemma map_redInvarNum : f (redInvarNum b c d m) = redInvarNum (f b) (f c) (f d) m := by
  simp [redInvarNum, map_compl₂EDS, map_normEDS, map_compl₂EDSAux]

lemma map_redInvarDenom : f (redInvarDenom b c d m) = redInvarDenom (f b) (f c) (f d) m := by
  simp [redInvarDenom, apply_ite f, map_normEDS, map_complEDS]

end EllSequence

end Complement

/-- A normalised EDS is in fact a divisibility sequence. -/
protected theorem IsDivSequence.normEDS : IsDivSequence (normEDS b c d) := by
  rintro m _ ⟨n, rfl⟩
  rw [mul_comm, ← normEDS_mul_complEDS]
  exact dvd_mul_right _ _

/-- A normalised EDS is in fact an EDS. -/
protected theorem IsEllDivSequence.normEDS : IsEllDivSequence (normEDS b c d) :=
  ⟨IsEllSequence.normEDS, IsDivSequence.normEDS⟩

/-- An elliptic sequence is a divisibility sequence if it satisfies three base cases
of the divisibility condition, provided its first two terms are not zero divisors. -/
lemma IsEllSequence.isDivSequence_of_dvd : IsDivSequence W := by
  obtain ⟨b, c, d, h⟩ := ellW.eq_normEDS_of_dvd one two dvd₁₂ dvd₁₃ dvd₂₄
  rw [h]; exact IsDivSequence.normEDS.smul _

lemma IsEllSequence.isEllDivSequence_of_dvd : IsEllDivSequence W :=
  ⟨ellW, ellW.isDivSequence_of_dvd one two dvd₁₂ dvd₁₃ dvd₂₄⟩

end Divisibility

section

lemma net_normEDS (p q r s : ℤ) : net (normEDS b c d) p q r s = 0 := by
  rw [normEDS_eq_aeval, ← Function.comp, ← map_net,
    universalNormEDS, IsEllSequence.normEDS.net, map_zero] <;>
  apply mem_nonZeroDivisors_of_ne_zero <;> simp only [normEDS_one, normEDS_two]
  exacts [one_ne_zero, MvPolynomial.X_ne_zero _]

lemma rel₄_normEDS (p q r s : ℤ) (same : HaveSameParity₄ p q r s) :
    rel₄ (normEDS b c d) p q r s = 0 := by
  rw [same.rel₄_eq_net, net_normEDS]

lemma invar_normEDS (s m n : ℤ) :
    invarNum (normEDS b c d) s m * invarDenom (normEDS b c d) s n =
      invarNum (normEDS b c d) s n * invarDenom (normEDS b c d) s m :=
  invar_of_net _ net_normEDS _ _ _

private lemma invar₂_normEDS_of_mem_nonZeroDivisors (hb : b ∈ R⁰) (m : ℤ) :
    invarNum (normEDS b c d) 1 m * c = invarDenom (normEDS b c d) 1 m * (d + b ^ 4) := by
  rw [← mul_cancel_right_mem_nonZeroDivisors hb, mul_assoc, mul_assoc, mul_comm (invarDenom _ _ _)]
  convert invar_normEDS 1 m 2 <;> simp only [invarNum_normEDS_two, invarDenom_normEDS_two]

open MvPolynomial Param in
lemma invar₂_normEDS {m : ℤ} :
    invarNum (normEDS b c d) 1 m * c = invarDenom (normEDS b c d) 1 m * (d + b ^ 4) := by
  have := congr(aeval (Param.rec b c d) $(invar₂_normEDS_of_mem_nonZeroDivisors
    (c := X Param.C) (d := X D) (mem_nonZeroDivisors_of_ne_zero <| X_ne_zero (R := ℤ) B) m))
  rw [← universalNormEDS] at this
  simpa only [map_mul, map_invarNum, map_invarDenom,
    Function.comp, ← normEDS_eq_aeval, map_add, map_pow, aeval_X] using this

private lemma redInvar_normEDS_of_mem_nonZeroDivisors (hb : b ∈ R⁰) (hc : c ∈ R⁰) (m : ℤ) :
    redInvarNum b c d m = redInvarDenom b c d m * (d + b ^ 4) := by
  rw [← mul_cancel_right_mem_nonZeroDivisors hb, ← mul_cancel_right_mem_nonZeroDivisors hc,
    ← invarNum_eq_redInvarNum_mul, invar₂_normEDS, invarDenom_eq_redInvarDenom_mul]
  ring

open MvPolynomial Param in
lemma redInvar_normEDS (m : ℤ) :
    redInvarNum b c d m = redInvarDenom b c d m * (d + b ^ 4) := by
  have := congr(aeval (Param.rec b c d) $(redInvar_normEDS_of_mem_nonZeroDivisors
    (b := X (R := ℤ) B) (c := X Param.C) (d := X D) ?_ ?_ m))
  · simpa only [map_redInvarNum, map_mul, map_add, map_pow, map_redInvarDenom, aeval_X] using this
  all_goals exact mem_nonZeroDivisors_of_ne_zero (X_ne_zero _)

end

end NormEDS

section ComplEDS

variable (k : ℤ)

/-- The complement sequence `Wᶜ : ℤ × ℕ → R` for a normalised EDS `W : ℤ → R` that witnesses
`W(k) ∣ W(n * k)`. In other words, `W(k) * Wᶜ(k, n) = W(n * k)` for any `k, n ∈ ℤ`.

This is defined in terms of `normEDS` and agrees with `complEDS₂` when `n = 2`. -/
def complEDS' : ℕ → R
  | 0 => 0
  | 1 => 1
  | (n + 2) => let m := n / 2 + 1
    if hn : Even n then complEDS' m * complEDS₂ b c d (m * k) else
      have : m + 1 < n + 2 :=
        add_lt_add_left (Nat.div_lt_self (Nat.not_even_iff_odd.mp hn).pos one_lt_two) 2
      complEDS' m ^ 2 * normEDS b c d ((m + 1) * k + 1) * normEDS b c d ((m + 1) * k - 1) -
        complEDS' (m + 1) ^ 2 * normEDS b c d (m * k + 1) * normEDS b c d (m * k - 1)

@[simp]
lemma complEDS'_zero : complEDS' b c d k 0 = 0 := by
  rw [complEDS']

@[simp]
lemma complEDS'_one : complEDS' b c d k 1 = 1 := by
  rw [complEDS']

lemma complEDS'_even (m : ℕ) : complEDS' b c d k (2 * (m + 1)) =
    complEDS' b c d k (m + 1) * complEDS₂ b c d ((m + 1) * k) := by
  rw [show 2 * (m + 1) = 2 * m + 2 by rfl, complEDS', dif_pos <| even_two_mul m,
    m.mul_div_cancel_left two_pos, Nat.cast_succ]

lemma complEDS'_odd (m : ℕ) : complEDS' b c d k (2 * (m + 1) + 1) =
    complEDS' b c d k (m + 1) ^ 2
        * normEDS b c d ((m + 2) * k + 1) * normEDS b c d ((m + 2) * k - 1) -
      complEDS' b c d k (m + 2) ^ 2
          * normEDS b c d ((m + 1) * k + 1) * normEDS b c d ((m + 1) * k - 1) := by
  rw [show 2 * (m + 1) + 1 = 2 * m + 3 by rfl, complEDS', dif_neg m.not_even_two_mul_add_one]
  simpa only [Nat.mul_add_div two_pos] using by rfl

/-- The complement sequence `Wᶜ : ℤ × ℤ → R` for a normalised EDS `W : ℤ → R` that witnesses
`W(k) ∣ W(n * k)`. In other words, `W(k) * Wᶜ(k, n) = W(n * k)` for any `k, n ∈ ℤ`.

This extends `complEDS'` by defining its values at negative integers. -/
def complEDS (n : ℤ) : R :=
  n.sign * complEDS' b c d k n.natAbs

@[simp]
lemma complEDS_ofNat (n : ℕ) : complEDS b c d k n = complEDS' b c d k n := by
  by_cases hn : n = 0
  · simp [hn, complEDS]
  · simp [complEDS, Int.sign_natCast_of_ne_zero hn]

@[simp]
lemma complEDS_zero : complEDS b c d k 0 = 0 := by
  simp [complEDS]

@[simp]
lemma complEDS_one : complEDS b c d k 1 = 1 := by
  simp [complEDS]

@[simp]
lemma complEDS_neg (n : ℤ) : complEDS b c d k (-n) = -complEDS b c d k n := by
  simp [complEDS]

lemma complEDS_even (m : ℤ) :
    complEDS b c d k (2 * m) = complEDS b c d k m * complEDS₂ b c d (m * k) := by
  induction m using Int.negInduction with
  | nat m =>
    rcases m with _ | _
    · simp
    norm_cast
    simpa only [complEDS_ofNat] using complEDS'_even ..
  | neg ih => simp_rw [mul_neg, complEDS_neg, ih, neg_mul, complEDS₂_neg]

lemma complEDS_odd (m : ℤ) : complEDS b c d k (2 * m + 1) =
    complEDS b c d k m ^ 2 * normEDS b c d ((m + 1) * k + 1) * normEDS b c d ((m + 1) * k - 1) -
      complEDS b c d k (m + 1) ^ 2 * normEDS b c d (m * k + 1) * normEDS b c d (m * k - 1) := by
  induction m using Int.negInduction with
  | nat m =>
    rcases m with _ | _
    · simp
    norm_cast
    simpa only [complEDS_ofNat] using complEDS'_odd ..
  | neg ih m =>
    rcases m with _ | m
    · simp
    simp_rw [Nat.cast_succ, show 2 * -(m + 1 : ℤ) + 1 = -(2 * m + 1) by rfl,
      show (-(m + 1 : ℤ) + 1) = -m by ring1, neg_mul, ← sub_neg_eq_add, ← neg_sub', sub_neg_eq_add,
      ← neg_add', complEDS_neg, normEDS_neg, ih]
    ring1

/-- Strong recursion principle for the complement sequence for a normalised EDS: if we have
* `P 0`, `P 1`,
* for all `m : ℕ` we can prove `P (2 * (m + 3))` from `P k` for all `k < 2 * (m + 3)`, and
* for all `m : ℕ` we can prove `P (2 * (m + 2) + 1)` from `P k` for all `k < 2 * (m + 2) + 1`,
then we have `P n` for all `n : ℕ`. -/
@[elab_as_elim]
noncomputable def complEDSRec' {P : ℕ → Sort u} (zero : P 0) (one : P 1)
    (even : ∀ m : ℕ, (∀ k < 2 * (m + 1), P k) → P (2 * (m + 1)))
    (odd : ∀ m : ℕ, (∀ k < 2 * (m + 1) + 1, P k) → P (2 * (m + 1) + 1)) (n : ℕ) : P n :=
  n.evenOddStrongRec (by rintro (_ | _) h; exacts [zero, even _ h])
    (by rintro (_ | _) h; exacts [one, odd _ h])

/-- Recursion principle for the complement sequence for a normalised EDS: if we have
* `P 0`, `P 1`,
* for all `m : ℕ` we can prove `P (2 * (m + 3))` from `P (m + 1)`, `P (m + 2)`, `P (m + 3)`,
  `P (m + 4)`, and `P (m + 5)`, and
* for all `m : ℕ` we can prove `P (2 * (m + 2) + 1)` from `P (m + 1)`, `P (m + 2)`, `P (m + 3)`,
  and `P (m + 4)`,
then we have `P n` for all `n : ℕ`. -/
@[elab_as_elim]
noncomputable def complEDSRec {P : ℕ → Sort u} (zero : P 0) (one : P 1)
    (even : ∀ m : ℕ, P (m + 1) → P (2 * (m + 1)))
    (odd : ∀ m : ℕ, P (m + 1) → P (m + 2) → P (2 * (m + 1) + 1)) (n : ℕ) : P n :=
  complEDSRec' zero one (fun _ ih => even _ <| ih _ <| by linarith only)
    (fun _ ih => odd _ (ih _ <| by linarith only) <| ih _ <| by linarith only) n

end ComplEDS

section Map

variable {S : Type v} [CommRing S] (f : R →+* S)

@[simp]
lemma map_preNormEDS' (n : ℕ) : f (preNormEDS' b c d n) = preNormEDS' (f b) (f c) (f d) n := by
  induction n using normEDSRec' with
  | zero => simp
  | one => simp
  | two => simp
  | three => simp
  | four => simp
  | _ _ ih =>
    simp only [preNormEDS'_even, preNormEDS'_odd, apply_ite f, map_pow, map_mul, map_sub, map_one]
    repeat rw [ih _ <| by linarith only]

@[simp]
lemma map_preNormEDS (n : ℤ) : f (preNormEDS b c d n) = preNormEDS (f b) (f c) (f d) n := by
  simp [preNormEDS]

@[simp]
lemma map_complEDS₂ (n : ℤ) : f (complEDS₂ b c d n) = complEDS₂ (f b) (f c) (f d) n := by
  simp [complEDS₂, apply_ite f]

@[simp]
lemma map_normEDS (n : ℤ) : f (normEDS b c d n) = normEDS (f b) (f c) (f d) n := by
  simp [normEDS, apply_ite f]

@[simp]
lemma map_complEDS' (k : ℤ) (n : ℕ) :
    f (complEDS' b c d k n) = complEDS' (f b) (f c) (f d) k n := by
  induction n using complEDSRec' with
  | zero => simp
  | one => simp
  | _ _ ih =>
    simp only [complEDS'_even, complEDS'_odd, map_normEDS, map_complEDS₂, map_pow, map_mul, map_sub]
    repeat rw [ih _ <| by linarith only]

@[simp]
lemma map_complEDS (k n : ℤ) : f (complEDS b c d k n) = complEDS (f b) (f c) (f d) k n := by
  simp [complEDS]

end Map
