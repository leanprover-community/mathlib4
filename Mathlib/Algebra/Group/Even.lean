/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Squares and even elements

This file defines square and even elements in a monoid.

## Main declarations

* `IsSquare a` means that there is some `r` such that `a = r * r`
* `Even a` means that there is some `r` such that `a = r + r`

## TODO

* Try to generalize `IsSquare/Even` lemmas further. For example, there are still a few lemmas in
  `Algebra.Ring.Parity` whose `Semiring` assumptions I (DT) am not convinced are necessary.
* The "old" definition of `Even a` asked for the existence of an element `c` such that `a = 2 * c`.
  For this reason, several fixes introduce an extra `two_mul` or `← two_mul`.
  It might be the case that by making a careful choice of `simp` lemma, this can be avoided.

## See also

`Mathlib.Algebra.Ring.Parity` for the definition of odd elements.
-/

assert_not_exists MonoidWithZero DenselyOrdered

open MulOpposite

variable {F α β : Type*}

section Mul
variable [Mul α]

/-- An element `a` of a type `α` with multiplication satisfies `IsSquare a` if `a = r * r`,
for some `r : α`. -/
@[to_additive "An element `a` of a type `α` with addition satisfies `Even a` if `a = r + r`,
for some `r : α`."]
def IsSquare (a : α) : Prop := ∃ r, a = r * r

@[to_additive]
lemma isSquare_iff_exists_mul_self (a : α) : IsSquare a ↔ ∃ r, a = r * r := Iff.rfl

alias ⟨IsSquare.exists_mul_self, _⟩ := isSquare_iff_exists_mul_self
attribute [to_additive] IsSquare.exists_mul_self

@[to_additive (attr := simp)] lemma IsSquare.mul_self (r : α) : IsSquare (r * r) := ⟨r, rfl⟩

@[to_additive, deprecated (since := "2024-08-27")] alias isSquare_mul_self := IsSquare.mul_self

@[to_additive]
lemma isSquare_op_iff {a : α} : IsSquare (op a) ↔ IsSquare a :=
  ⟨fun ⟨r, hr⟩ ↦ ⟨unop r, congr_arg unop hr⟩, fun ⟨r, hr⟩ ↦ ⟨op r, congr_arg op hr⟩⟩

@[to_additive]
lemma isSquare_unop_iff {a : αᵐᵒᵖ} : IsSquare (unop a) ↔ IsSquare a := isSquare_op_iff.symm

@[to_additive]
instance [DecidablePred (IsSquare : α → Prop)] : DecidablePred (IsSquare : αᵐᵒᵖ → Prop) :=
  fun _ ↦ decidable_of_iff _ isSquare_unop_iff

@[simp]
lemma even_ofMul_iff {a : α} : Even (Additive.ofMul a) ↔ IsSquare a := Iff.rfl

@[simp]
lemma isSquare_toMul_iff {a : Additive α} : IsSquare (a.toMul) ↔ Even a := Iff.rfl

instance Additive.instDecidablePredEven [DecidablePred (IsSquare : α → Prop)] :
    DecidablePred (Even : Additive α → Prop) :=
  fun _ ↦ decidable_of_iff _ isSquare_toMul_iff

end Mul

section Add
variable [Add α]

@[simp] lemma isSquare_ofAdd_iff {a : α} : IsSquare (Multiplicative.ofAdd a) ↔ Even a := Iff.rfl

@[simp]
lemma even_toAdd_iff {a : Multiplicative α} : Even a.toAdd ↔ IsSquare a := Iff.rfl

instance Multiplicative.instDecidablePredIsSquare [DecidablePred (Even : α → Prop)] :
    DecidablePred (IsSquare : Multiplicative α → Prop) :=
  fun _ ↦ decidable_of_iff _ even_toAdd_iff

end Add

@[to_additive (attr := simp)]
lemma IsSquare.one [MulOneClass α] : IsSquare (1 : α) := ⟨1, (mul_one _).symm⟩

@[to_additive, deprecated (since := "2024-12-27")] alias isSquare_one := IsSquare.one

section MonoidHom
variable [MulOneClass α] [MulOneClass β] [FunLike F α β] [MonoidHomClass F α β]

@[to_additive]
lemma IsSquare.map {a : α} (f : F) : IsSquare a → IsSquare (f a) :=
  fun ⟨r, _⟩ => ⟨f r, by simp_all⟩

@[to_additive]
lemma exists_apply_eq_and_isSquare {b : β} {f : F} (hf : Function.Surjective f) :
    IsSquare b → ∃ a, f a = b ∧ IsSquare a := fun ⟨s, _⟩ => by
  rcases hf s with ⟨r, rfl⟩
  use r * r; simp_all

end MonoidHom

section Monoid
variable [Monoid α] {n : ℕ} {a : α}

@[to_additive even_iff_exists_two_nsmul]
lemma isSquare_iff_exists_sq (a : α): IsSquare a ↔ ∃ r, a = r ^ 2 := by simp [IsSquare, pow_two]

alias ⟨IsSquare.exists_sq, _⟩ := isSquare_iff_exists_sq
attribute [to_additive Even.exists_two_nsmul
  "Alias of the forwards direction of `even_iff_exists_two_nsmul`."] IsSquare.exists_sq

@[to_additive (attr := simp) Even.two_nsmul]
lemma IsSquare.sq (r : α) : IsSquare (r ^ 2) := ⟨r, pow_two _⟩

@[deprecated (since := "2024-12-27")] alias even_two_nsmul := Even.two_nsmul
@[deprecated (since := "2024-12-27")] alias IsSquare_sq := IsSquare.sq

@[to_additive] lemma IsSquare.pow (n : ℕ) : IsSquare a → IsSquare (a ^ n) := by
  rintro ⟨r, rfl⟩; exact ⟨r ^ n, (Commute.refl _).mul_pow _⟩

@[to_additive] lemma Even.isSquare_pow : Even n → ∀ a : α, IsSquare (a ^ n) := by
  rintro ⟨m, rfl⟩ a; exact ⟨a ^ m, pow_add _ _ _⟩

@[deprecated (since := "2024-01-07")] alias Even.nsmul' := Even.even_nsmul

end Monoid

@[to_additive]
lemma IsSquare.mul [CommSemigroup α] {a b : α} : IsSquare a → IsSquare b → IsSquare (a * b) :=
  fun ⟨r, _⟩ ⟨s, _⟩ => ⟨r * s, by simp_all [mul_mul_mul_comm]⟩

section DivisionMonoid
variable [DivisionMonoid α] {a : α}

@[to_additive (attr := simp)] lemma isSquare_inv : IsSquare a⁻¹ ↔ IsSquare a := by
  constructor <;> exact fun h => by simpa using (isSquare_op_iff.mpr h).map (MulEquiv.inv' α).symm

alias ⟨_, IsSquare.inv⟩ := isSquare_inv
attribute [to_additive] IsSquare.inv

@[to_additive] lemma IsSquare.zpow (n : ℤ) : IsSquare a → IsSquare (a ^ n) := by
  rintro ⟨r, rfl⟩; exact ⟨r ^ n, (Commute.refl _).mul_zpow _⟩

end DivisionMonoid

@[to_additive]
lemma IsSquare.div [DivisionCommMonoid α] {a b : α} (ha : IsSquare a) (hb : IsSquare b) :
    IsSquare (a / b) := by rw [div_eq_mul_inv]; exact ha.mul hb.inv

@[to_additive]
lemma Even.isSquare_zpow [Group α] {n : ℤ} : Even n → ∀ a : α, IsSquare (a ^ n) := by
  rintro ⟨m, rfl⟩ a; exact ⟨a ^ m, zpow_add _ _ _⟩

@[deprecated (since := "2024-01-07")] alias Even.zsmul' := Even.even_zsmul
