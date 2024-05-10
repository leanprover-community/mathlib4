/-
Copyright (c) 2024 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import Mathlib.Data.Nat.Parity
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
 * `normEDS'`: the canonical example of a normalised EDS indexed by `ℕ`.
 * `normEDS`: the canonical example of a normalised EDS indexed by `ℤ`.

## Main statements

 * TODO: prove that `normEDS` satisfies `IsEllDivSequence`.
 * TODO: prove that a normalised sequence satisfying `IsEllDivSequence` can be given by `normEDS`.

## Implementation notes

`IsEllDivSequence' b c d n` is defined in terms of the private `IsEllDivSequence'' b c d n`,
which are equal when `n` is odd and differ by a factor of `b` when `n` is even. This coincides with
the reference since both agree for `IsEllDivSequence' b c d 2` and for `IsEllDivSequence' b c d 4`,
and the correct factors of `b` are removed in `IsEllDivSequence' b c d (2 * (m + 2) + 1)` and in
`IsEllDivSequence' b c d (2 * (m + 3))`. This is done to avoid the necessity for ring division by
`b` in the inductive definition of `IsEllDivSequence' b c d (2 * (m + 3))`. The idea is that, an
easy lemma shows that `IsEllDivSequence' b c d (2 * (m + 3))` always contains a factor of `b`, so it
is possible to remove a factor of `b` a posteriori, but stating this lemma requires first defining
`IsEllDivSequence' b c d (2 * (m + 3))`, which requires having this factor of `b` a priori.

## References

M Ward, *Memoir on Elliptic Divisibility Sequences*

## Tags

elliptic, divisibility, sequence
-/

universe u v w

variable {R : Type u} [CommRing R]

/-- The proposition that a sequence indexed by integers is an elliptic sequence. -/
def IsEllSequence (W : ℤ → R) : Prop :=
  ∀ m n r : ℤ, W (m + n) * W (m - n) * W r ^ 2 =
    W (m + r) * W (m - r) * W n ^ 2 - W (n + r) * W (n - r) * W m ^ 2

/-- The proposition that a sequence indexed by integers is a divisibility sequence. -/
def IsDivSequence (W : ℤ → R) : Prop :=
  ∀ m n : ℕ, m ∣ n → W m ∣ W n

/-- The proposition that a sequence indexed by integers is an EDS. -/
def IsEllDivSequence (W : ℤ → R) : Prop :=
  IsEllSequence W ∧ IsDivSequence W

lemma IsEllSequence_id : IsEllSequence id :=
  fun _ _ _ => by simp only [id_eq]; ring1

lemma IsDivSequence_id : IsDivSequence id :=
  fun _ _ => Int.ofNat_dvd.mpr

/-- The identity sequence is an EDS. -/
theorem IsEllDivSequence_id : IsEllDivSequence id :=
  ⟨IsEllSequence_id, IsDivSequence_id⟩

lemma IsEllSequence_mul (x : R) {W : ℤ → R} (h : IsEllSequence W) : IsEllSequence (x • W) :=
  fun m n r => by
    linear_combination (norm := (simp only [Pi.smul_apply, smul_eq_mul]; ring1)) x ^ 4 * h m n r

lemma IsDivSequence_mul (x : R) {W : ℤ → R} (h : IsDivSequence W) : IsDivSequence (x • W) :=
  fun m n r => mul_dvd_mul_left x <| h m n r

lemma IsEllDivSequence_mul (x : R) {W : ℤ → R} (h : IsEllDivSequence W) :
    IsEllDivSequence (x • W) :=
  ⟨IsEllSequence_mul x h.left, IsDivSequence_mul x h.right⟩

private def normEDS'' (b c d : R) : ℕ → R
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
      normEDS'' b c d (m + 4) * normEDS'' b c d (m + 2) ^ 3 * (if Even m then b ^ 4 else 1) -
        normEDS'' b c d (m + 1) * normEDS'' b c d (m + 3) ^ 3 * (if Even m then 1 else b ^ 4)
    else
      have h5 : m + 5 < n + 5 := add_lt_add_right
        (Nat.div_lt_self (Nat.odd_iff_not_even.mpr hn).pos <| Nat.lt_succ_self 1) 5
      normEDS'' b c d (m + 2) ^ 2 * normEDS'' b c d (m + 3) * normEDS'' b c d (m + 5) -
        normEDS'' b c d (m + 1) * normEDS'' b c d (m + 3) * normEDS'' b c d (m + 4) ^ 2

variable (b c d : R)

/-- The canonical example of a normalised EDS `W : ℕ → R`,
with initial values `W(0) = 0`, `W(1) = 1`, `W(2) = b`, `W(3) = c`, and `W(4) = b * d`.

This is defined in terms of a truncated sequence whose even terms differ by a factor of `b`. -/
def normEDS' (n : ℕ) : R :=
  normEDS'' b c d n * if Even n then b else 1

@[simp]
lemma normEDS'_zero : normEDS' b c d 0 = 0 := by
  rw [normEDS', normEDS'', zero_mul]

@[simp]
lemma normEDS'_one : normEDS' b c d 1 = 1 := by
  rw [normEDS', normEDS'', one_mul, if_neg Nat.not_even_one]

@[simp]
lemma normEDS'_two : normEDS' b c d 2 = b := by
  rw [normEDS', normEDS'', one_mul, if_pos even_two]

@[simp]
lemma normEDS'_three : normEDS' b c d 3 = c := by
  rw [normEDS', normEDS'', if_neg <| by decide, mul_one]

@[simp]
lemma normEDS'_four : normEDS' b c d 4 = d * b := by
  rw [normEDS', normEDS'', if_pos <| by decide]

lemma normEDS'_odd (m : ℕ) : normEDS' b c d (2 * (m + 2) + 1) =
    normEDS' b c d (m + 4) * normEDS' b c d (m + 2) ^ 3 -
      normEDS' b c d (m + 1) * normEDS' b c d (m + 3) ^ 3 := by
  rw [normEDS', if_neg <| fun h => Nat.even_add_one.mp h <| even_two_mul _,
    show 2 * (m + 2) + 1 = 2 * m + 5 by rfl, normEDS'', dif_pos <| even_two_mul m]
  simp only [normEDS', Nat.mul_div_right _ zero_lt_two]
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

lemma normEDS'_even (m : ℕ) : normEDS' b c d (2 * (m + 3)) * b =
    normEDS' b c d (m + 2) ^ 2 * normEDS' b c d (m + 3) * normEDS' b c d (m + 5) -
      normEDS' b c d (m + 1) * normEDS' b c d (m + 3) * normEDS' b c d (m + 4) ^ 2 := by
  rw [normEDS', if_pos <| even_two_mul _, show 2 * (m + 3) = 2 * m + 1 + 5 by rfl,
    normEDS'', dif_neg <| fun h => Nat.even_add_one.mp h <| even_two_mul _]
  simp only [normEDS', Nat.mul_add_div two_pos, show 1 / 2 = 0 by rfl]
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

/-- The canonical example of a normalised EDS `W : ℤ → R`,
with initial values `W(0) = 0`, `W(1) = 1`, `W(2) = b`, `W(3) = c`, and `W(4) = b * d`.

This extends `normEDS'` by defining its values at negative integers. -/
def normEDS (n : ℤ) : R := n.sign * normEDS' b c d n.natAbs

@[simp]
lemma normEDS_zero : normEDS b c d 0 = 0 := by
  erw [normEDS, Int.cast_zero, zero_mul]

@[simp]
lemma normEDS_one : normEDS b c d 1 = 1 := by
  erw [normEDS, Int.cast_one, one_mul, normEDS'_one]

@[simp]
lemma normEDS_two : normEDS b c d 2 = b := by
  erw [normEDS, Int.cast_one, one_mul, normEDS'_two]

@[simp]
lemma normEDS_three : normEDS b c d 3 = c := by
  erw [normEDS, Int.cast_one, one_mul, normEDS'_three]

@[simp]
lemma normEDS_four : normEDS b c d 4 = d * b := by
  erw [normEDS, Int.cast_one, one_mul, normEDS'_four]

lemma normEDS_odd (m : ℕ) : normEDS b c d (2 * (m + 2) + 1) =
    normEDS b c d (m + 4) * normEDS b c d (m + 2) ^ 3 -
      normEDS b c d (m + 1) * normEDS b c d (m + 3) ^ 3 := by
  repeat erw [normEDS, Int.cast_one, one_mul]
  exact normEDS'_odd b c d m

lemma normEDS_even (m : ℕ) : normEDS b c d (2 * (m + 3)) * b =
    normEDS b c d (m + 2) ^ 2 * normEDS b c d (m + 3) * normEDS b c d (m + 5) -
      normEDS b c d (m + 1) * normEDS b c d (m + 3) * normEDS b c d (m + 4) ^ 2 := by
  repeat erw [normEDS, Int.cast_one, one_mul]
  exact normEDS'_even b c d m

@[simp]
lemma normEDS_neg (n : ℕ) : normEDS b c d (-n) = -normEDS b c d n := by
  simp [normEDS]
