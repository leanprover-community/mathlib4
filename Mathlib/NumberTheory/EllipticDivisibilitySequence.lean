/-
Copyright (c) 2024 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import Mathlib.Data.Nat.Parity
import Mathlib.Tactic.Linarith

/-!
# Elliptic divisibility sequences

This file defines the type of elliptic divisibility sequences and a few examples.

## Mathematical background

Let $R$ be a commutative ring. An elliptic sequence is a sequence $h : \mathbb{Z} \to R$ satisfying
$$ h(m + n)h(m - n)h(r)^2 = h(m + r)h(m - r)h(n)^2 - h(n + r)h(n - r)h(m)^2, $$
for any $m, n, r \in \mathbb{Z}$. A divisibility sequence is a sequence $h : \mathbb{Z} \to R$
satisfying $h(m) \mid h(n)$ for any $m, n \in \mathbb{Z}$ such that $m \mid n$.

Some examples of elliptic divisibility sequences include
 * the integers $\mathbb{Z}$,
 * certain terms of Lucas sequences, and
 * division polynomials of elliptic curves.

## Main definitions

 * `isEllSequence`: a sequence indexed by integers is an elliptic sequence.
 * `isDivSequence`: a sequence indexed by integers is a divisibility sequence.
 * `isEllDivSequence`: a sequence indexed by integers is an elliptic divisibility sequence.
 * `EllDivSequence'`: a canonical example of an elliptic divisibility sequence indexed by naturals.
 * `EllDivSequence`: a canonical example of an elliptic divisibility sequence indexed by integers.

## Main statements

 * TODO: prove that `EllDivSequence` is an elliptic divisibility sequence.
 * TODO: prove that a general elliptic divisibility sequence can be given by `EllDivSequence`.

## References

M Ward, *Memoir on Elliptic Divisibility Sequences*

## Tags

elliptic, divisibility, sequence
-/

universe u v w

variable {R : Type u} [CommRing R]

/-- The proposition that a sequence indexed by integers is an elliptic sequence. -/
def isEllSequence (h : ℤ → R) : Prop :=
  ∀ m n r : ℤ, h (m + n) * h (m - n) * h r ^ 2 =
    h (m + r) * h (m - r) * h n ^ 2 - h (n + r) * h (n - r) * h m ^ 2

/-- The proposition that a sequence indexed by integers is a divisibility sequence. -/
def isDivSequence (h : ℤ → R) : Prop :=
  ∀ m n : ℕ, m ∣ n → h m ∣ h n

/-- The proposition that a sequence indexed by integers is an elliptic divisibility sequence. -/
def isEllDivSequence (h : ℤ → R) : Prop :=
  isEllSequence h ∧ isDivSequence h

/-- The integers form an elliptic divisibility sequence. -/
lemma Int.isEllDivSequence : isEllDivSequence id :=
  ⟨fun _ _ _ => by simp only [id_eq]; ring1, fun _ _ => Int.ofNat_dvd.mpr⟩

private def EllDivSequence'' (b c d : R) : ℕ → R
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => c
  | 4 => d
  | (n + 5) =>
    if hn : Even n then
      let m := n / 2
      have h4 : m + 4 < n + 5 :=
        by linarith only [show n = 2 * m by exact (Nat.two_mul_div_two_of_even hn).symm]
      have h3 : m + 3 < n + 5 := (lt_add_one _).trans h4
      have h2 : m + 2 < n + 5 := (lt_add_one _).trans h3
      have h1 : m + 1 < n + 5 := (lt_add_one _).trans h2
      EllDivSequence'' b c d (m + 4) * EllDivSequence'' b c d (m + 2) ^ 3 *
          (if Even m then b ^ 4 else 1) -
        EllDivSequence'' b c d (m + 1) * EllDivSequence'' b c d (m + 3) ^ 3 *
            (if Even m then 1 else b ^ 4)
    else
      let m := n / 2
      have h5 : m + 5 < n + 5 := by
        linarith only [show n = 2 * m + 1
          by exact (Nat.two_mul_div_two_add_one_of_odd <| Nat.odd_iff_not_even.mpr hn).symm]
      have h4 : m + 4 < n + 5 := (lt_add_one _).trans h5
      have h3 : m + 3 < n + 5 := (lt_add_one _).trans h4
      have h2 : m + 2 < n + 5 := (lt_add_one _).trans h3
      have h1 : m + 1 < n + 5 := (lt_add_one _).trans h2
      EllDivSequence'' b c d (m + 2) ^ 2 * EllDivSequence'' b c d (m + 3) *
          EllDivSequence'' b c d (m + 5) -
        EllDivSequence'' b c d (m + 1) * EllDivSequence'' b c d (m + 3) *
            EllDivSequence'' b c d (m + 4) ^ 2

variable (b c d : R)

/-- The canonical example of an elliptic divisibility sequence `h : ℕ → R`,
with initial values `h(2) = b`, `h(3) = c`, and `h(4) = d`.

This is defined in terms of a truncated sequence whose even terms differ by a factor of `b`. -/
def EllDivSequence' (n : ℕ) : R :=
  EllDivSequence'' b c d n * if Even n then b else 1

@[simp]
lemma EllDivSequence'_zero : EllDivSequence' b c d 0 = 0 := by
  rw [EllDivSequence', EllDivSequence'', zero_mul]

@[simp]
lemma EllDivSequence'_one : EllDivSequence' b c d 1 = 1 := by
  rw [EllDivSequence', EllDivSequence'', one_mul, if_neg Nat.not_even_one]

@[simp]
lemma EllDivSequence'_two : EllDivSequence' b c d 2 = b := by
  rw [EllDivSequence', EllDivSequence'', one_mul, if_pos even_two]

@[simp]
lemma EllDivSequence'_three : EllDivSequence' b c d 3 = c := by
  rw [EllDivSequence', EllDivSequence'', if_neg <| by decide, mul_one]

@[simp]
lemma EllDivSequence'_four : EllDivSequence' b c d 4 = d * b := by
  rw [EllDivSequence', EllDivSequence'', if_pos <| by decide]

lemma EllDivSequence'_odd (m : ℕ) : EllDivSequence' b c d (2 * (m + 2) + 1) =
    EllDivSequence' b c d (m + 4) * EllDivSequence' b c d (m + 2) ^ 3 -
      EllDivSequence' b c d (m + 1) * EllDivSequence' b c d (m + 3) ^ 3 := by
  rw [EllDivSequence', if_neg <| fun h => Nat.even_add_one.mp h <| even_two_mul _,
    show 2 * (m + 2) + 1 = 2 * m + 5 by rfl, EllDivSequence'', dif_pos <| even_two_mul m]
  simp only [EllDivSequence', Nat.mul_div_right _ zero_lt_two]
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

lemma EllDivSequence'_even (m : ℕ) : EllDivSequence' b c d (2 * (m + 3)) * b =
    EllDivSequence' b c d (m + 2) ^ 2 * EllDivSequence' b c d (m + 3) *
        EllDivSequence' b c d (m + 5) -
      EllDivSequence' b c d (m + 1) * EllDivSequence' b c d (m + 3) *
          EllDivSequence' b c d (m + 4) ^ 2 := by
  rw [EllDivSequence', if_pos <| even_two_mul _, show 2 * (m + 3) = 2 * m + 1 + 5 by rfl,
    EllDivSequence'', dif_neg <| fun h => Nat.even_add_one.mp h <| even_two_mul _]
  simp only [EllDivSequence', Nat.mul_add_div two_pos, show 1 / 2 = 0 by rfl]
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

/-- The canonical example of an elliptic divisibility sequence `h : ℤ → R`,
with initial values `h(2) = b`, `h(3) = c`, and `h(4) = d`.

This extends `EllDivSequence'` by defining its values at negative integers. -/
def EllDivSequence : ℤ → R
  | Int.ofNat n => EllDivSequence' b c d n
  | Int.negSucc n => -EllDivSequence' b c d (n + 1)

@[simp]
lemma EllDivSequence_zero : EllDivSequence b c d 0 = 0 :=
  EllDivSequence'_zero b c d

@[simp]
lemma EllDivSequence_one : EllDivSequence b c d 1 = 1 :=
  EllDivSequence'_one b c d

@[simp]
lemma EllDivSequence_two : EllDivSequence b c d 2 = b :=
  EllDivSequence'_two b c d

@[simp]
lemma EllDivSequence_three : EllDivSequence b c d 3 = c :=
  EllDivSequence'_three b c d

@[simp]
lemma EllDivSequence_four : EllDivSequence b c d 4 = d * b :=
  EllDivSequence'_four b c d

@[simp]
lemma EllDivSequence_odd (m : ℕ) : EllDivSequence b c d (2 * (m + 2) + 1) =
    EllDivSequence b c d (m + 4) * EllDivSequence b c d (m + 2) ^ 3 -
      EllDivSequence b c d (m + 1) * EllDivSequence b c d (m + 3) ^ 3 :=
  EllDivSequence'_odd b c d m

@[simp]
lemma EllDivSequence_even (m : ℕ) : EllDivSequence b c d (2 * (m + 3)) * b =
    EllDivSequence b c d (m + 2) ^ 2 * EllDivSequence b c d (m + 3) * EllDivSequence b c d (m + 5) -
      EllDivSequence b c d (m + 1) * EllDivSequence b c d (m + 3) *
        EllDivSequence b c d (m + 4) ^ 2 :=
  EllDivSequence'_even b c d m

@[simp]
lemma EllDivSequence_neg (n : ℕ) : EllDivSequence b c d (-n) = -EllDivSequence b c d n := by
  induction n
  erw [EllDivSequence_zero, neg_zero]
  rfl
