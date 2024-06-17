/-
Copyright (c) 2024 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Init.Data.Int.DivModLemmas
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Nat.EvenOddRec
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.Data.Nat.EvenOddRec
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Elliptic divisibility sequences

This file defines elliptic divisibility sequences (EDS)
and constructs normalised EDSs from initial terms.

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

 * TODO: prove that `normEDS` satisfies `IsEllDivSequence`.
 * TODO: prove that a normalised sequence satisfying `IsEllDivSequence` can be given by `normEDS`.

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

/-- The expression `W((m+n)/2) * W((m-n)/2)` is the basic building block of elliptic relations,
where integers `m` and `n` should have the same parity. -/
def addMulSub (m n : ℤ) : R := W ((m + n).div 2) * W ((m - n).div 2)
/- Implementation note: we use `Int.div _ 2` instead of `_ / 2` so that `(-m).div 2 = -(m.div 2)`
and lemmas like `addMulSub_neg₀` hold unconditionally, even though in the case we care about
(`m` and `n` both even or both odd) both are equal. -/

/-- The four-index elliptic relation, defined in terms of `addMulSub`,
featuring the three partitions of four indices into two pairs.
Intended to apply to four integers of the same parity. -/
def rel₄ (a b c d : ℤ) : R :=
  addMulSub W a b * addMulSub W c d
    - addMulSub W a c * addMulSub W b d
    + addMulSub W a d * addMulSub W b c

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
    Int.mul_div_cancel_left _ two_ne_zero]
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
  linear_combination (norm := (simp_rw [net]; ring_nf))
    net_eq_zero m n s 0 * W m * W n * W (2 * s) ^ 2
      - (net_eq_zero m n s s * W (m - s) * W (n - s)
        + net_eq_zero (m - s) (n - s) s s * W (m + s) * W (n + s)
        - net_eq_zero (n + s) n (n - s) (m - n) * W (m - n) * W (2 * s)) * W s ^ 2

lemma net_add_sub_iff (m n : ℤ) :
    net W (m + n) m (m - n) n = 0 ↔
      W (2 * (m + n)) * W (m - n) * W m * W n =
        (W (2 * m + n) * W (2 * n) * W m - W (m + 2 * n) * W (2 * m) * W n) * W (m + n) := by
  rw [net]; conv_rhs => rw [← sub_eq_zero]
  ring_nf

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

lemma addMulSub_abs₀ (neg : ∀ k, W (-k) = -W k) (m n : ℤ) :
    addMulSub W |m| n = addMulSub W m n := by
  obtain h | h := abs_choice m <;> simp only [h, addMulSub_neg₀ W neg]

lemma addMulSub_abs₁ (m n : ℤ) : addMulSub W m |n| = addMulSub W m n := by
  obtain h | h := abs_choice n <;> simp only [h, addMulSub_neg₁]

lemma addMulSub_swap (neg : ∀ k, W (-k) = -W k) (m n : ℤ) :
    addMulSub W m n = - addMulSub W n m := by
  rw [addMulSub, addMulSub, ← neg_sub, Int.neg_div, neg]; ring_nf

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

lemma rel₄_eq_net : rel₄ W a b c d = net W ((a - d) / 2) ((b - d) / 2) ((c - d) / 2) d := by
  have h := @Int.two_mul_ediv_two_of_even
  rw [net_eq_rel₄, h, h, h]; · simp_rw [sub_add_cancel]
  all_goals simp only [← negOnePow_eq_iff, same.1, same.2.1, same.2.2]

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
  have := (Perm.mclosure_swap_castSucc_succ 3).symm ▸ Submonoid.mem_top σ
  refine Submonoid.closure_induction this ?_ (fun _ ↦ id) fun σ τ hσ hτ t same ↦ ?_
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
def addMulSub₄ (a b c d : ℤ) : R := W ((a + b).div 2) * W ((c - d).div 2)

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
  rw [Rel₃, EvenRec]; ring_nf

lemma rel₄_iff_evenRec (m : ℤ) : rel₄ W (2 * m + 1) (2 * m - 1) 3 1 = 0 ↔ EvenRec W m := by
  rw [iff_comm, EvenRec, ← sub_eq_zero, show 2 * m - 1 = 2 * (m - 1) + 1 by ring]
  convert_to _ ↔ rel₄ W _ _ (2 * 1 + 1) (2 * 0 + 1) = 0
  simp_rw [rel₄, addMulSub_odd]; ring_nf

/-- The minimal possible fourth index in the four-index elliptic relation given the first index. -/
def dMin (a : ℤ) : ℤ := if Even a then 0 else 1
/-- The minimal possible third index in the four-index elliptic relation given the first index. -/
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
  obtain hc|hc := lt_or_le (cMin a) d
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
  · -- if `a' < a`, apply the inductive hypothesis
    exact ih _ ha' same anti
  obtain hba|rfl := lt_or_eq_of_le <| show b + 2 ≤ a' from
    (add_two_le_iff_lt_of_even_sub <| (negOnePow_eq_iff _ _).1 same.1).mpr anti.2.2.2
  · -- if `b + 2 < a'`, apply `transf` and then the inductive hypothesis is applicable
    rw [← same.rel₄_transf]
    refine ih _ ?_ same.transf (same.strictAnti₄_transf anti)
    rw [avg₄, sub_lt_iff_lt_add, Int.ediv_lt_iff_lt_mul zero_lt_two, ← ha', cMin]
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

end Rel₄OfValid

section Perm

variable (neg : ∀ k, W (-k) = -W k)

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
  have := (Perm.mclosure_swap_castSucc_succ 3).symm ▸ Submonoid.mem_top σ
  refine Submonoid.closure_induction this ?_ (by simp) fun σ τ hσ hτ t ↦ ?_
  · rintro _ ⟨i, rfl⟩ t; fin_cases i <;>
      rw [Perm.sign_swap (Fin.castSucc_lt_succ _).ne, Units.neg_smul, one_smul]
    exacts [rel₄_swap₀₁ neg, rel₄_swap₁₂ neg, rel₄_swap₂₃ neg]
  rw [Perm.coe_mul, ← Function.comp.assoc, hτ, hσ, map_mul, mul_comm, mul_smul]

lemma relFin4_perm' (σ : Perm (Fin 4)) (t) : Perm.sign σ • relFin4 W (t ∘ σ) = relFin4 W t := by
  rw [relFin4_perm neg, ← mul_smul, Int.units_mul_self, one_smul]

variable (zero : W 0 = 0)

/-! `rel₄` is trivial when two indices are equal. -/

lemma rel₄_same₀₁ (m r s : ℤ) : rel₄ W m m r s = 0 := by
  simp_rw [rel₄, addMulSub_same W zero]; ring

lemma rel₄_same₁₂ (m n s : ℤ) : rel₄ W m n n s = 0 := by
  simp_rw [rel₄, addMulSub_same W zero]; ring

lemma rel₄_same₂₃ (m n r : ℤ) : rel₄ W m n r r = 0 := by
  simp_rw [rel₄, addMulSub_same W zero]; ring

variable (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
  (oddRec : ∀ m ≥ 2, OddRec W m) (evenRec : ∀ m ≥ 3, EvenRec W m)

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

/-- An ℕ-indexed sequence defined recursively by the even-odd recurrence, after extension to
all integers by symmetry (to make an odd function), is an elliptic sequence, provided its
first two terms are not zero divisors. -/
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
  simp_rw [preNormEDS'_odd, if_neg (m + 2).not_even_two_mul_add_one, Nat.even_add_one, ite_not]
  split_ifs <;> ring1

lemma normEDS_even (m : ℕ) : normEDS b c d (2 * (m + 3)) * b =
    normEDS b c d (m + 2) ^ 2 * normEDS b c d (m + 3) * normEDS b c d (m + 5) -
      normEDS b c d (m + 1) * normEDS b c d (m + 3) * normEDS b c d (m + 4) ^ 2 := by
  repeat erw [normEDS_ofNat]
  simp only [preNormEDS'_even, if_pos <| even_two_mul _, Nat.even_add_one, ite_not]
  split_ifs <;> ring1

@[simp]
lemma normEDS_neg (n : ℤ) : normEDS b c d (-n) = -normEDS b c d n := by
  rw [normEDS, preNormEDS_neg, Int.natAbs_neg, neg_mul, normEDS]

/-- Strong recursion principle for a normalised EDS: if we have
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
  normEDSRec' zero one two three four
    (fun _ ih => by apply even <;> exact ih _ <| by linarith only)
    (fun _ ih => by apply odd <;> exact ih _ <| by linarith only) n
