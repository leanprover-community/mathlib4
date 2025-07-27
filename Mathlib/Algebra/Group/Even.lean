/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Equiv.Opposite
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.Set.Operations

/-!
# Squares and even elements

This file defines square and even elements in a monoid.

## Main declarations

* `IsSquare a` means that there is some `r` such that `a = r * r`
* `Even a` means that there is some `r` such that `a = r + r`

## Note

* Many lemmas about `Even` / `IsSquare`, including important `simp` lemmas,
  are in `Mathlib/Algebra/Ring/Parity.lean`.

## TODO

* Try to generalize `IsSquare/Even` lemmas further. For example, there are still a few lemmas in
  `Algebra.Ring.Parity` whose `Semiring` assumptions I (DT) am not convinced are necessary.
* The "old" definition of `Even a` asked for the existence of an element `c` such that `a = 2 * c`.
  For this reason, several fixes introduce an extra `two_mul` or `← two_mul`.
  It might be the case that by making a careful choice of `simp` lemma, this can be avoided.

## See also

`Mathlib/Algebra/Ring/Parity.lean` for the definition of odd elements as well as facts about
`Even` / `IsSquare` in rings.
-/

assert_not_exists MonoidWithZero DenselyOrdered

open MulOpposite

variable {F α β : Type*}

section Mul
variable [Mul α]

/-- An element `a` of a type `α` with multiplication satisfies `IsSquare a` if `a = r * r`,
for some root `r : α`. -/
@[to_additive "An element `a` of a type `α` with addition satisfies `Even a` if `a = r + r`,
for some `r : α`."]
def IsSquare (a : α) : Prop := ∃ r, a = r * r

@[to_additive]
lemma isSquare_iff_exists_mul_self (a : α) : IsSquare a ↔ ∃ r, a = r * r := .rfl

alias ⟨IsSquare.exists_mul_self, _⟩ := isSquare_iff_exists_mul_self
attribute [to_additive (attr := aesop unsafe 5% forward)] IsSquare.exists_mul_self

@[to_additive (attr := simp, aesop safe)]
lemma IsSquare.mul_self (r : α) : IsSquare (r * r) := ⟨r, rfl⟩

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

@[to_additive (attr := simp, grind)]
lemma IsSquare.one [MulOneClass α] : IsSquare (1 : α) := ⟨1, (mul_one _).symm⟩

@[deprecated (since := "2024-12-27")] alias isSquare_one := IsSquare.one
@[deprecated (since := "2024-12-27")] alias even_zero := Even.zero

section MonoidHom
variable [MulOneClass α] [MulOneClass β] [FunLike F α β] [MonoidHomClass F α β]

@[to_additive (attr := aesop unsafe 90%)]
lemma IsSquare.map {a : α} (f : F) : IsSquare a → IsSquare (f a) :=
  fun ⟨r, _⟩ => ⟨f r, by simp [*]⟩

@[to_additive]
lemma isSquare_subset_image_isSquare {f : F} (hf : Function.Surjective f) :
    {b | IsSquare b} ⊆ f '' {a | IsSquare a} := fun b ⟨s, _⟩ => by
  rcases hf s with ⟨r, rfl⟩
  exact ⟨r * r, by simp [*]⟩

end MonoidHom

section Monoid
variable [Monoid α] {n : ℕ} {a : α}

@[to_additive even_iff_exists_two_nsmul]
lemma isSquare_iff_exists_sq (a : α) : IsSquare a ↔ ∃ r, a = r ^ 2 := by simp [IsSquare, pow_two]

@[to_additive Even.exists_two_nsmul
  "Alias of the forwards direction of `even_iff_exists_two_nsmul`."]
alias ⟨IsSquare.exists_sq, _⟩ := isSquare_iff_exists_sq

-- provable by simp in `Algebra.Ring.Parity`
@[to_additive (attr := aesop safe) Even.two_nsmul]
lemma IsSquare.sq (r : α) : IsSquare (r ^ 2) := ⟨r, pow_two _⟩

@[deprecated (since := "2024-12-27")] alias IsSquare_sq := IsSquare.sq
@[deprecated (since := "2024-12-27")] alias even_two_nsmul := Even.two_nsmul

@[to_additive (attr := aesop unsafe 80%) Even.nsmul_right]
lemma IsSquare.pow (n : ℕ) (ha : IsSquare a) : IsSquare (a ^ n) := by
  aesop (add simp Commute.mul_pow)

@[deprecated (since := "2025-01-19")] alias Even.nsmul := Even.nsmul_right

@[to_additive (attr := aesop unsafe 90%) Even.nsmul_left]
lemma Even.isSquare_pow (hn : Even n) : ∀ a : α, IsSquare (a ^ n) := by aesop (add simp pow_add)

@[deprecated (since := "2025-01-19")] alias Even.nsmul' := Even.nsmul_left

end Monoid

@[to_additive (attr := aesop unsafe 90%)]
lemma IsSquare.mul [CommSemigroup α] {a b : α} : IsSquare a → IsSquare b → IsSquare (a * b) :=
  fun ⟨r, _⟩ ⟨s, _⟩ => ⟨r * s, by simp_all [mul_mul_mul_comm]⟩

section DivisionMonoid
variable [DivisionMonoid α] {a : α}

@[to_additive (attr := simp)] lemma isSquare_inv : IsSquare a⁻¹ ↔ IsSquare a := by
  constructor <;> intro h <;> simpa using (isSquare_op_iff.mpr h).map (MulEquiv.inv' α).symm

@[to_additive] alias ⟨_, IsSquare.inv⟩ := isSquare_inv

@[to_additive (attr := aesop unsafe 80%) Even.zsmul_right]
lemma IsSquare.zpow (n : ℤ) : IsSquare a → IsSquare (a ^ n) := by
  aesop (add simp Commute.mul_zpow)

end DivisionMonoid

@[to_additive (attr := aesop unsafe 90%)]
lemma IsSquare.div [DivisionCommMonoid α] {a b : α} (ha : IsSquare a) (hb : IsSquare b) :
    IsSquare (a / b) := by aesop (add simp div_eq_mul_inv)

@[to_additive (attr := simp, aesop unsafe 90%) Even.zsmul_left]
lemma Even.isSquare_zpow [Group α] {n : ℤ} : Even n → ∀ a : α, IsSquare (a ^ n) := by
  aesop (add simp zpow_add)

example {G : Type*} [CommGroup G] {a b c d e : G} (ha : IsSquare a) {n : ℕ} {k : ℤ} (hk : Even k) :
    IsSquare <| a * (b * b) / (c ^ 2) * (d ^ k) * (e ^ (n + n)) := by aesop

example {G : Type*} [AddCommGroup G] {a b c d e : G} (ha : Even a) {n : ℕ} {k : ℤ} (hk : Even k) :
    Even <| a + (b + b) - 2 • c + k • d + (n + n) • e := by aesop
