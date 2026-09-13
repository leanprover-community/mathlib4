/-
Copyright (c) 2026 Tomaz Mascarenhas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Mascarenhas
-/
module

public import Mathlib.Data.List.Destutter
public import Mathlib.Basic.Sign.Basic

/-!
# Sign variations of a list

This files defines `List.signVariations`, for counting the number of changes of sign in a list
after all zeroes were removed. For example, `[1, 0, -2, 3, 3]` has two sign variations, and so
does `[1, -2, 3]`.

This is the counting device behind Descartes' rule of signs (applied to the list of coefficients
of the polynomial) and Sturm's theorem (applied to the values of a Sturm sequence at a
point, or to its leading coefficients for the count at infinity).

## Main definitions

* `List.signVariations l`: the number of sign variations of `l`.

## Main results

* `List.signVariations_cons_cons_of_ne_zero`: the recursion for a list starting with two nonzero
  entries: prepending `a` to `b :: l` adds one variation exactly when `sign a ≠ sign b`.
* `List.signVariations_zero_cons`, `List.signVariations_cons_zero_cons`: zero entries are ignored.
* `List.signVariations_map`: `signVariations` only depends on the signs of the entries, so it is
  invariant under any map preserving signs (for instance the cast `ℚ → ℝ`, or `SignType.sign`
  itself).
-/

@[expose] public section

open SignType

namespace List

variable {α : Type*} [Zero α] [LinearOrder α]

/-- The number of sign variations of a list: the number of adjacent pairs of opposite sign once
all zero entries have been removed. -/
def signVariations (l : List α) : ℕ :=
  letI signs := l.map SignType.sign
  letI nonzero_signs := signs.filter (· ≠ 0)
  (nonzero_signs.destutter (· ≠ ·)).length - 1

@[simp]
lemma signVariations_nil :
    signVariations ([] : List α) = 0 := by
  trivial

@[simp]
lemma signVariations_singleton : ∀ (a : α), signVariations [a] = 0 := by
  intro a
  rcases eq_or_ne a 0 with ha | ha <;> simp [signVariations, ha]

/-- A leading zero entry does not change the sign variations. -/
@[simp]
lemma signVariations_zero_cons : ∀ (b : α) (as : List α),
    signVariations (0 :: b :: as) = signVariations (b :: as) := by
  simp [signVariations]

/-- A zero entry in second position does not change the sign variations. -/
@[simp]
lemma signVariations_cons_zero_cons : ∀ (a : α) (as : List α),
    signVariations (a :: 0 :: as) = signVariations (a :: as) := by
  simp [signVariations, filter]

/-- Prepending a nonzero entry `a` to a list starting with a nonzero entry `b` adds one sign
variation exactly when `a` and `b` have opposite signs. -/
lemma signVariations_cons_cons_of_ne_zero : ∀ (a b : α) (as : List α),
    a ≠ 0 → b ≠ 0 →
      signVariations (a :: b :: as) =
        (if sign a = sign b then 0 else 1) + signVariations (b :: as) := by
  intros a b as ha hb
  have ha' : sign a ≠ 0 := by rwa [ne_eq, sign_eq_zero_iff]
  have hb' : sign b ≠ 0 := by rwa [ne_eq, sign_eq_zero_iff]
  have hf1 :
      ((a :: b :: as).map sign).filter (· ≠ 0) =
      sign a :: sign b :: (as.map sign).filter (· ≠ 0) := by
    simp [ha', hb']
  have hf2 : ((b :: as).map sign).filter (· ≠ 0) = sign b :: (as.map sign).filter (· ≠ 0) := by
    simp [hb']
  have hne : ((sign b :: (as.map sign).filter (· ≠ 0)).destutter (· ≠ ·)).length ≠ 0 := by
    rw [ne_eq, length_eq_zero_iff, destutter_eq_nil]
    simp
  simp only [signVariations, hf1, hf2, destutter_cons_cons, ← destutter_cons']
  by_cases h : sign a = sign b
  · rw [ite_eq_right (not_not.mpr h), ite_eq_left h, h, zero_add]
  · rw [ite_eq_left h, ite_eq_right h, length_cons]
    omega

/-- `signVariations` only depends on the signs of the entries, so it is invariant under any
map that preserves signs (e.g. casts, or `sign` itself). -/
lemma signVariations_map {β : Type*} [Zero β] [LinearOrder β] {f : α → β}
    (hf : ∀ x, sign (f x) = sign x) (l : List α) :
    signVariations (l.map f) = signVariations l := by
  have : (l.map f).map sign = l.map sign := by
    rw [map_map]
    exact map_congr_left fun x _ => hf x
  simp only [signVariations, this]

/-- A run of zero entries after the head does not change the sign variations. -/
@[simp]
lemma signVariations_cons_replicate_zero_append (a : α) (n : ℕ) (l : List α) :
    signVariations (a :: (replicate n 0 ++ l)) = signVariations (a :: l) := by
  have h : ((replicate n (0 : α) ++ l).map sign).filter (· ≠ 0) = (l.map sign).filter (· ≠ 0) := by
    simp [filter_append]
  simp only [signVariations, map_cons, filter_cons, h]

/-- `signVariations` is invariant under any map that negates signs (e.g. negation). -/
lemma signVariations_map_of_sign_eq_neg {β : Type*} [Zero β] [LinearOrder β] {f : α → β}
    (hf : ∀ x, sign (f x) = -sign x) (l : List α) :
    signVariations (l.map f) = signVariations l := by
  have h1 : (l.map f).map sign = (l.map sign).map (- ·) := by
    rw [map_map, map_map]
    exact map_congr_left fun x _ => hf x
  have h2 : ((l.map sign).map (- ·)).filter (· ≠ 0) = ((l.map sign).filter (· ≠ 0)).map (- ·) := by
    rw [filter_map]
    congr 2
    funext s
    simp
  simp only [signVariations, h1, h2, ← map_destutter_ne _ neg_injective, length_map]

end List
