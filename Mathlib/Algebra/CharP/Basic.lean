/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Joey van Langen, Casper Putz
-/
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Ring.ULift
import Mathlib.Algebra.Ring.Opposite
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Cast.Prod
import Mathlib.Data.ULift
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Algebra.Ring.GrindInstances

/-!
# Characteristic of semirings

This file collects some fundamental results on the characteristic of rings that don't need the extra
imports of `CharP/Lemmas.lean`.

As such, we can probably reorganize and find a better home for most of these lemmas.
-/

assert_not_exists Finset TwoSidedIdeal

open Set

variable (R : Type*)

namespace CharP
section AddMonoidWithOne
variable [AddMonoidWithOne R] (p : ℕ)

variable [CharP R p] {a b : ℕ}

lemma natCast_eq_natCast' (h : a ≡ b [MOD p]) : (a : R) = b := by
  wlog hle : a ≤ b
  · exact (this R p h.symm (le_of_not_ge hle)).symm
  rw [Nat.modEq_iff_dvd' hle] at h
  rw [← Nat.sub_add_cancel hle, Nat.cast_add, (cast_eq_zero_iff R p _).mpr h, zero_add]

lemma natCast_eq_natCast_mod (a : ℕ) : (a : R) = a % p :=
  natCast_eq_natCast' R p (Nat.mod_modEq a p).symm

variable [IsRightCancelAdd R]

lemma natCast_eq_natCast : (a : R) = b ↔ a ≡ b [MOD p] := by
  wlog hle : a ≤ b
  · rw [eq_comm, this R p (le_of_not_ge hle), Nat.ModEq.comm]
  rw [Nat.modEq_iff_dvd' hle, ← cast_eq_zero_iff R p (b - a),
    ← add_right_cancel_iff (G := R) (a := a) (b := b - a), zero_add, ← Nat.cast_add,
    Nat.sub_add_cancel hle, eq_comm]

lemma natCast_injOn_Iio : (Set.Iio p).InjOn ((↑) : ℕ → R) :=
  fun _a ha _b hb hab ↦ ((natCast_eq_natCast _ _).1 hab).eq_of_lt_of_lt ha hb

end AddMonoidWithOne

section AddGroupWithOne
variable [AddGroupWithOne R] (p : ℕ) [CharP R p] {a b : ℤ}

lemma intCast_eq_intCast : (a : R) = b ↔ a ≡ b [ZMOD p] := by
  rw [eq_comm, ← sub_eq_zero, ← Int.cast_sub, CharP.intCast_eq_zero_iff R p, Int.modEq_iff_dvd]

lemma intCast_eq_intCast_mod : (a : R) = a % (p : ℤ) :=
  (CharP.intCast_eq_intCast R p).mpr (Int.mod_modEq a p).symm

lemma intCast_injOn_Ico [IsRightCancelAdd R] : InjOn (Int.cast : ℤ → R) (Ico 0 p) := by
  rintro a ⟨ha₀, ha⟩ b ⟨hb₀, hb⟩ hab
  lift a to ℕ using ha₀
  lift b to ℕ using hb₀
  norm_cast at *
  exact natCast_injOn_Iio _ _ ha hb hab

end AddGroupWithOne
end CharP

namespace CharP

section NonAssocSemiring

variable {R} [NonAssocSemiring R]

variable (R) in
/-- If a ring `R` is of characteristic `p`, then for any prime number `q` different from `p`,
it is not zero in `R`. -/
lemma cast_ne_zero_of_ne_of_prime [Nontrivial R]
    {p q : ℕ} [CharP R p] (hq : q.Prime) (hneq : p ≠ q) : (q : R) ≠ 0 := fun h ↦ by
  rw [cast_eq_zero_iff R p q] at h
  rcases hq.eq_one_or_self_of_dvd _ h with h | h
  · subst h
    exact false_of_nontrivial_of_char_one (R := R)
  · exact hneq h

lemma ringChar_of_prime_eq_zero [Nontrivial R] {p : ℕ} (hprime : Nat.Prime p)
    (hp0 : (p : R) = 0) : ringChar R = p :=
  Or.resolve_left ((Nat.dvd_prime hprime).1 (ringChar.dvd hp0)) ringChar_ne_one

lemma charP_iff_prime_eq_zero [Nontrivial R] {p : ℕ} (hp : p.Prime) :
    CharP R p ↔ (p : R) = 0 :=
  ⟨fun _ => cast_eq_zero R p,
   fun hp0 => (ringChar_of_prime_eq_zero hp hp0) ▸ inferInstance⟩

end NonAssocSemiring
end CharP

section

/-- We have `2 ≠ 0` in a nontrivial ring whose characteristic is not `2`. -/
protected lemma Ring.two_ne_zero {R : Type*} [NonAssocSemiring R] [Nontrivial R]
    (hR : ringChar R ≠ 2) : (2 : R) ≠ 0 := by
  rw [Ne, (by norm_cast : (2 : R) = (2 : ℕ)), ringChar.spec, Nat.dvd_prime Nat.prime_two]
  exact mt (or_iff_left hR).mp CharP.ringChar_ne_one

-- We have `CharP.neg_one_ne_one`, which assumes `[Ring R] (p : ℕ) [CharP R p] [Fact (2 < p)]`.
-- This is a version using `ringChar` instead.
/-- Characteristic `≠ 2` and nontrivial implies that `-1 ≠ 1`. -/
lemma Ring.neg_one_ne_one_of_char_ne_two {R : Type*} [NonAssocRing R] [Nontrivial R]
    (hR : ringChar R ≠ 2) : (-1 : R) ≠ 1 := fun h =>
  Ring.two_ne_zero hR (one_add_one_eq_two (R := R) ▸ neg_eq_iff_add_eq_zero.mp h)

/-- Characteristic `≠ 2` in a domain implies that `-a = a` iff `a = 0`. -/
lemma Ring.eq_self_iff_eq_zero_of_char_ne_two {R : Type*} [NonAssocRing R] [Nontrivial R]
    [NoZeroDivisors R] (hR : ringChar R ≠ 2) {a : R} : -a = a ↔ a = 0 :=
  ⟨fun h =>
    (mul_eq_zero.mp <| (two_mul a).trans <| neg_eq_iff_add_eq_zero.mp h).resolve_left
      (Ring.two_ne_zero hR),
    fun h => ((congr_arg (fun x => -x) h).trans neg_zero).trans h.symm⟩

end

section Prod
variable (S : Type*) [AddMonoidWithOne R] [AddMonoidWithOne S] (p q : ℕ) [CharP R p]

/-- The characteristic of the product of rings is the least common multiple of the
characteristics of the two rings. -/
instance Nat.lcm.charP [CharP S q] : CharP (R × S) (Nat.lcm p q) where
  cast_eq_zero_iff := by
    simp [Prod.ext_iff, CharP.cast_eq_zero_iff R p, CharP.cast_eq_zero_iff S q, Nat.lcm_dvd_iff]

/-- The characteristic of the product of two rings of the same characteristic
  is the same as the characteristic of the rings -/
instance Prod.charP [CharP S p] : CharP (R × S) p := by
  convert Nat.lcm.charP R S p p; simp

instance Prod.charZero_of_left [CharZero R] : CharZero (R × S) where
  cast_injective _ _ h := CharZero.cast_injective congr(Prod.fst $h)

instance Prod.charZero_of_right [CharZero S] : CharZero (R × S) where
  cast_injective _ _ h := CharZero.cast_injective congr(Prod.snd $h)

end Prod

instance ULift.charP [AddMonoidWithOne R] (p : ℕ) [CharP R p] : CharP (ULift R) p where
  cast_eq_zero_iff n := Iff.trans ULift.ext_iff <| CharP.cast_eq_zero_iff R p n

instance MulOpposite.charP [AddMonoidWithOne R] (p : ℕ) [CharP R p] : CharP Rᵐᵒᵖ p where
  cast_eq_zero_iff n := MulOpposite.unop_inj.symm.trans <| CharP.cast_eq_zero_iff R p n

section

/-- If two integers from `{0, 1, -1}` result in equal elements in a ring `R`
that is nontrivial and of characteristic not `2`, then they are equal. -/
lemma Int.cast_injOn_of_ringChar_ne_two {R : Type*} [NonAssocRing R] [Nontrivial R]
    (hR : ringChar R ≠ 2) : ({0, 1, -1} : Set ℤ).InjOn ((↑) : ℤ → R) := by
  rintro _ (rfl | rfl | rfl) _ (rfl | rfl | rfl) h <;>
  simp only
    [cast_neg, cast_one, cast_zero, neg_eq_zero, one_ne_zero, zero_ne_one, zero_eq_neg] at h ⊢
  · exact ((Ring.neg_one_ne_one_of_char_ne_two hR).symm h).elim
  · exact ((Ring.neg_one_ne_one_of_char_ne_two hR) h).elim

end

namespace CharZero

lemma charZero_iff_forall_prime_ne_zero [NonAssocRing R] [NoZeroDivisors R] [Nontrivial R] :
    CharZero R ↔ ∀ p : ℕ, p.Prime → (p : R) ≠ 0 := by
  refine ⟨fun h p hp => by simp [hp.ne_zero], fun h => ?_⟩
  let p := ringChar R
  cases CharP.char_is_prime_or_zero R p with
  | inl hp => simpa using h p hp
  | inr h => have : CharP R 0 := h ▸ inferInstance; exact CharP.charP_to_charZero R

end CharZero

namespace Fin

open Fin.NatCast

/-- The characteristic of `F_p` is `p`. -/
@[stacks 09FS "First part. We don't require `p` to be a prime in mathlib."]
instance charP (n : ℕ) [NeZero n] : CharP (Fin n) n where cast_eq_zero_iff _ := natCast_eq_zero

end Fin

section AddMonoidWithOne
variable [AddMonoidWithOne R]

instance (S : Type*) [Semiring S] (p) [ExpChar R p] [ExpChar S p] : ExpChar (R × S) p := by
  obtain hp | ⟨hp⟩ := ‹ExpChar R p›
  · constructor
  obtain _ | _ := ‹ExpChar S p›
  · exact (Nat.not_prime_one hp).elim
  · have := Prod.charP R S p; exact .prime hp

end AddMonoidWithOne

section CommRing

instance (α : Type*) [Semiring α] [IsLeftCancelAdd α] (n : ℕ) [CharP α n] :
    Lean.Grind.IsCharP α n where
  ofNat_ext_iff {a b} := by
    rw [Lean.Grind.Semiring.ofNat_eq_natCast, Lean.Grind.Semiring.ofNat_eq_natCast]
    exact CharP.cast_eq_iff_mod_eq α n

end CommRing
