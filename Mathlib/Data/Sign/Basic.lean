/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Sign.Defs

/-!
# Sign function

This file defines the sign function for types with zero and a decidable less-than relation, and
proves some basic theorems about it.
-/

universe u
variable {α : Type u}

namespace SignType

/-- Casting `SignType → ℤ → α` is the same as casting directly `SignType → α`. -/
@[simp, norm_cast]
lemma intCast_cast {α : Type*} [AddGroupWithOne α] (s : SignType) : ((s : ℤ) : α) = s :=
  map_cast' _ Int.cast_one Int.cast_zero (@Int.cast_one α _ ▸ Int.cast_neg 1) _

theorem pow_odd (s : SignType) {n : ℕ} (hn : Odd n) : s ^ n = s := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_add, pow_one, pow_mul, sq]
  cases s <;> simp

theorem zpow_odd (s : SignType) {z : ℤ} (hz : Odd z) : s ^ z = s := by
  obtain rfl | hs := eq_or_ne s 0
  · rw [zero_zpow]
    rintro rfl
    simp at hz
  obtain ⟨k, rfl⟩ := hz
  rw [zpow_add₀ hs, zpow_one, zpow_mul, zpow_two]
  cases s <;> simp

lemma pow_even (s : SignType) {n : ℕ} (hn : Even n) (hs : s ≠ 0) :
    s ^ n = 1 := by
  cases s <;> simp_all

lemma zpow_even (s : SignType) {z : ℤ} (hz : Even z) (hs : s ≠ 0) :
    s ^ z = 1 := by
  cases s <;> simp_all [Even.neg_one_zpow]

/-- `SignType.cast` as a `MulWithZeroHom`. -/
@[simps]
def castHom {α} [MulZeroOneClass α] [HasDistribNeg α] : SignType →*₀ α where
  toFun := cast
  map_zero' := rfl
  map_one' := rfl
  map_mul' x y := by cases x <;> cases y <;> simp [zero_eq_zero, pos_eq_one, neg_eq_neg_one]

theorem univ_eq : (Finset.univ : Finset SignType) = {0, -1, 1} := by
  decide

theorem range_eq {α} (f : SignType → α) : Set.range f = {f zero, f neg, f pos} := by
  classical rw [← Fintype.coe_image_univ, univ_eq]
  classical simp [Finset.coe_insert]

@[simp, norm_cast] lemma coe_mul {α} [MulZeroOneClass α] [HasDistribNeg α] (a b : SignType) :
    ↑(a * b) = (a : α) * b :=
  map_mul SignType.castHom _ _

@[simp, norm_cast] lemma coe_pow {α} [MonoidWithZero α] [HasDistribNeg α] (a : SignType) (k : ℕ) :
    ↑(a ^ k) = (a : α) ^ k :=
  map_pow SignType.castHom _ _

@[simp, norm_cast] lemma coe_zpow {α} [GroupWithZero α] [HasDistribNeg α] (a : SignType) (k : ℤ) :
    ↑(a ^ k) = (a : α) ^ k :=
  map_zpow₀ SignType.castHom _ _

end SignType

open SignType

section OrderedRing

@[simp]
lemma sign_intCast {α : Type*} [Ring α] [PartialOrder α] [IsOrderedRing α]
    [Nontrivial α] [DecidableLT α] (n : ℤ) :
    sign (n : α) = sign n := by
  simp only [sign_apply, Int.cast_pos, Int.cast_lt_zero]

end OrderedRing

section LinearOrderedRing

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α]

theorem sign_mul (x y : α) : sign (x * y) = sign x * sign y := by
  rcases lt_trichotomy x 0 with (hx | hx | hx) <;> rcases lt_trichotomy y 0 with (hy | hy | hy) <;>
    simp [hx, hy, mul_pos_of_neg_of_neg, mul_neg_of_neg_of_pos, mul_neg_of_pos_of_neg]

@[simp] theorem sign_mul_abs (x : α) : (sign x * |x| : α) = x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;> simp [*, abs_of_pos, abs_of_neg]

@[simp] theorem abs_mul_sign (x : α) : (|x| * sign x : α) = x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;> simp [*, abs_of_pos, abs_of_neg]

@[simp]
theorem sign_mul_self (x : α) : sign x * x = |x| := by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;> simp [*, abs_of_pos, abs_of_neg]

@[simp]
theorem self_mul_sign (x : α) : x * sign x = |x| := by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;> simp [*, abs_of_pos, abs_of_neg]

/-- `SignType.sign` as a `MonoidWithZeroHom` for a nontrivial ordered semiring. Note that linearity
is required; consider ℂ with the order `z ≤ w` iff they have the same imaginary part and
`z - w ≤ 0` in the reals; then `1 + I` and `1 - I` are incomparable to zero, and thus we have:
`0 * 0 = SignType.sign (1 + I) * SignType.sign (1 - I) ≠ SignType.sign 2 = 1`.
(`Complex.orderedCommRing`) -/
def signHom : α →*₀ SignType where
  toFun := sign
  map_zero' := sign_zero
  map_one' := sign_one
  map_mul' := sign_mul

theorem sign_pow (x : α) (n : ℕ) : sign (x ^ n) = sign x ^ n := map_pow signHom x n

end LinearOrderedRing

section LinearOrderedAddCommGroup

variable [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

theorem sign_sum {ι : Type*} {s : Finset ι} {f : ι → α} (hs : s.Nonempty) (t : SignType)
    (h : ∀ i ∈ s, sign (f i) = t) : sign (∑ i ∈ s, f i) = t := by
  cases t
  · simp_rw [zero_eq_zero, sign_eq_zero_iff] at h ⊢
    exact Finset.sum_eq_zero h
  · simp_rw [neg_eq_neg_one, sign_eq_neg_one_iff] at h ⊢
    exact Finset.sum_neg h hs
  · simp_rw [pos_eq_one, sign_eq_one_iff] at h ⊢
    exact Finset.sum_pos h hs

end LinearOrderedAddCommGroup

open Finset Nat

section exists_signed_sum

/-!
In this section we explicitly handle universe variables,
because Lean creates a fresh universe variable for the type whose existence is asserted.
But we want the type to live in the same universe as the input type.
-/

private theorem exists_signed_sum_aux [DecidableEq α] (s : Finset α) (f : α → ℤ) :
    ∃ (β : Type u) (t : Finset β) (sgn : β → SignType) (g : β → α),
      (∀ b, g b ∈ s) ∧
        (#t = ∑ a ∈ s, (f a).natAbs) ∧
          ∀ a ∈ s, (∑ b ∈ t, if g b = a then (sgn b : ℤ) else 0) = f a := by
  refine
    ⟨(Σ _ : { x // x ∈ s }, ℕ), Finset.univ.sigma fun a => range (f a).natAbs,
      fun a => sign (f a.1), fun a => a.1, fun a => a.1.2, ?_, ?_⟩
  · simp [sum_attach (f := fun a => (f a).natAbs)]
  · intro x hx
    simp [sum_sigma, hx, ← Int.sign_eq_sign, Int.sign_mul_abs, mul_comm |f _|,
      sum_attach (s := s) (f := fun y => if y = x then f y else 0)]

/-- We can decompose a sum of absolute value `n` into a sum of `n` signs. -/
theorem exists_signed_sum [DecidableEq α] (s : Finset α) (f : α → ℤ) :
    ∃ (β : Type u) (_ : Fintype β) (sgn : β → SignType) (g : β → α),
      (∀ b, g b ∈ s) ∧
        (Fintype.card β = ∑ a ∈ s, (f a).natAbs) ∧
          ∀ a ∈ s, (∑ b, if g b = a then (sgn b : ℤ) else 0) = f a :=
  let ⟨β, t, sgn, g, hg, ht, hf⟩ := exists_signed_sum_aux s f
  ⟨t, inferInstance, fun b => sgn b, fun b => g b, fun b => hg b, by simp [ht], fun a ha =>
    (sum_attach t fun b ↦ ite (g b = a) (sgn b : ℤ) 0).trans <| hf _ ha⟩

/-- We can decompose a sum of absolute value less than `n` into a sum of at most `n` signs. -/
theorem exists_signed_sum' [Nonempty α] [DecidableEq α] (s : Finset α) (f : α → ℤ)
    (n : ℕ) (h : (∑ i ∈ s, (f i).natAbs) ≤ n) :
    ∃ (β : Type u) (_ : Fintype β) (sgn : β → SignType) (g : β → α),
      (∀ b, g b ∉ s → sgn b = 0) ∧
        Fintype.card β = n ∧ ∀ a ∈ s, (∑ i, if g i = a then (sgn i : ℤ) else 0) = f a := by
  obtain ⟨β, _, sgn, g, hg, hβ, hf⟩ := exists_signed_sum s f
  refine
    ⟨β ⊕ (Fin (n - ∑ i ∈ s, (f i).natAbs)), inferInstance, Sum.elim sgn 0,
      Sum.elim g (Classical.arbitrary (Fin (n - Finset.sum s fun i => Int.natAbs (f i)) → α)),
        ?_, by simp [hβ, h], fun a ha => by simp [hf _ ha]⟩
  rintro (b | b) hb
  · cases hb (hg _)
  · rfl

end exists_signed_sum
