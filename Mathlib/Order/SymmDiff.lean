/-
Copyright (c) 2021 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Bryan Gin-ge Chen, Yaël Dillies
-/
import Mathlib.Order.BooleanAlgebra
import Mathlib.Logic.Equiv.Basic

/-!
# Symmetric difference and bi-implication

This file defines the symmetric difference and bi-implication operators in (co-)Heyting algebras.

## Examples

Some examples are
* The symmetric difference of two sets is the set of elements that are in either but not both.
* The symmetric difference on propositions is `Xor'`.
* The symmetric difference on `Bool` is `Bool.xor`.
* The equivalence of propositions. Two propositions are equivalent if they imply each other.
* The symmetric difference translates to addition when considering a Boolean algebra as a Boolean
  ring.

## Main declarations

* `symmDiff`: The symmetric difference operator, defined as `(a \ b) ⊔ (b \ a)`
* `bihimp`: The bi-implication operator, defined as `(b ⇨ a) ⊓ (a ⇨ b)`

In generalized Boolean algebras, the symmetric difference operator is:

* `symmDiff_comm`: commutative, and
* `symmDiff_assoc`: associative.

## Notations

* `a ∆ b`: `symmDiff a b`
* `a ⇔ b`: `bihimp a b`

## References

The proof of associativity follows the note "Associativity of the Symmetric Difference of Sets: A
Proof from the Book" by John McCuan:

* <https://people.math.gatech.edu/~mccuan/courses/4317/symmetricdifference.pdf>

## Tags

boolean ring, generalized boolean algebra, boolean algebra, symmetric difference, bi-implication,
Heyting
-/

assert_not_exists RelIso

open Function OrderDual

variable {ι α β : Type*} {π : ι → Type*}

/-- The symmetric difference operator on a type with `⊔` and `\` is `(A \ B) ⊔ (B \ A)`. -/
def symmDiff [Max α] [SDiff α] (a b : α) : α :=
  a \ b ⊔ b \ a

/-- The Heyting bi-implication is `(b ⇨ a) ⊓ (a ⇨ b)`. This generalizes equivalence of
propositions. -/
def bihimp [Min α] [HImp α] (a b : α) : α :=
  (b ⇨ a) ⊓ (a ⇨ b)

/-- Notation for symmDiff -/
scoped[symmDiff] infixl:100 " ∆ " => symmDiff

/-- Notation for bihimp -/
scoped[symmDiff] infixl:100 " ⇔ " => bihimp

open scoped symmDiff

theorem symmDiff_def [Max α] [SDiff α] (a b : α) : a ∆ b = a \ b ⊔ b \ a :=
  rfl

theorem bihimp_def [Min α] [HImp α] (a b : α) : a ⇔ b = (b ⇨ a) ⊓ (a ⇨ b) :=
  rfl

theorem symmDiff_eq_Xor' (p q : Prop) : p ∆ q = Xor' p q :=
  rfl

@[simp]
theorem bihimp_iff_iff {p q : Prop} : p ⇔ q ↔ (p ↔ q) :=
  iff_iff_implies_and_implies.symm.trans Iff.comm

@[simp]
theorem Bool.symmDiff_eq_xor : ∀ p q : Bool, p ∆ q = xor p q := by decide

section GeneralizedCoheytingAlgebra

variable [GeneralizedCoheytingAlgebra α] (a b c : α)

@[simp]
theorem toDual_symmDiff : toDual (a ∆ b) = toDual a ⇔ toDual b :=
  rfl

@[simp]
theorem ofDual_bihimp (a b : αᵒᵈ) : ofDual (a ⇔ b) = ofDual a ∆ ofDual b :=
  rfl

theorem symmDiff_comm : a ∆ b = b ∆ a := by simp only [symmDiff, sup_comm]

instance symmDiff_isCommutative : Std.Commutative (α := α) (· ∆ ·) :=
  ⟨symmDiff_comm⟩

@[simp]
theorem symmDiff_self : a ∆ a = ⊥ := by rw [symmDiff, sup_idem, sdiff_self]

@[simp]
theorem symmDiff_bot : a ∆ ⊥ = a := by rw [symmDiff, sdiff_bot, bot_sdiff, sup_bot_eq]

@[simp]
theorem bot_symmDiff : ⊥ ∆ a = a := by rw [symmDiff_comm, symmDiff_bot]

@[simp]
theorem symmDiff_eq_bot {a b : α} : a ∆ b = ⊥ ↔ a = b := by
  simp_rw [symmDiff, sup_eq_bot_iff, sdiff_eq_bot_iff, le_antisymm_iff]

theorem symmDiff_of_le {a b : α} (h : a ≤ b) : a ∆ b = b \ a := by
  rw [symmDiff, sdiff_eq_bot_iff.2 h, bot_sup_eq]

theorem symmDiff_of_ge {a b : α} (h : b ≤ a) : a ∆ b = a \ b := by
  rw [symmDiff, sdiff_eq_bot_iff.2 h, sup_bot_eq]

theorem symmDiff_le {a b c : α} (ha : a ≤ b ⊔ c) (hb : b ≤ a ⊔ c) : a ∆ b ≤ c :=
  sup_le (sdiff_le_iff.2 ha) <| sdiff_le_iff.2 hb

theorem symmDiff_le_iff {a b c : α} : a ∆ b ≤ c ↔ a ≤ b ⊔ c ∧ b ≤ a ⊔ c := by
  simp_rw [symmDiff, sup_le_iff, sdiff_le_iff]

@[simp]
theorem symmDiff_le_sup {a b : α} : a ∆ b ≤ a ⊔ b :=
  sup_le_sup sdiff_le sdiff_le

theorem symmDiff_eq_sup_sdiff_inf : a ∆ b = (a ⊔ b) \ (a ⊓ b) := by simp [sup_sdiff, symmDiff]

theorem Disjoint.symmDiff_eq_sup {a b : α} (h : Disjoint a b) : a ∆ b = a ⊔ b := by
  rw [symmDiff, h.sdiff_eq_left, h.sdiff_eq_right]

theorem symmDiff_sdiff : a ∆ b \ c = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) := by
  rw [symmDiff, sup_sdiff_distrib, sdiff_sdiff_left, sdiff_sdiff_left]

@[simp]
theorem symmDiff_sdiff_inf : a ∆ b \ (a ⊓ b) = a ∆ b := by
  rw [symmDiff_sdiff]
  simp [symmDiff]

@[simp]
theorem symmDiff_sdiff_eq_sup : a ∆ (b \ a) = a ⊔ b := by
  rw [symmDiff, sdiff_idem]
  exact
    le_antisymm (sup_le_sup sdiff_le sdiff_le)
      (sup_le le_sdiff_sup <| le_sdiff_sup.trans <| sup_le le_sup_right le_sdiff_sup)

@[simp]
theorem sdiff_symmDiff_eq_sup : (a \ b) ∆ b = a ⊔ b := by
  rw [symmDiff_comm, symmDiff_sdiff_eq_sup, sup_comm]

@[simp]
theorem symmDiff_sup_inf : a ∆ b ⊔ a ⊓ b = a ⊔ b := by
  refine le_antisymm (sup_le symmDiff_le_sup inf_le_sup) ?_
  rw [sup_inf_left, symmDiff]
  refine sup_le (le_inf le_sup_right ?_) (le_inf ?_ le_sup_right)
  · rw [sup_right_comm]
    exact le_sup_of_le_left le_sdiff_sup
  · rw [sup_assoc]
    exact le_sup_of_le_right le_sdiff_sup

@[simp]
theorem inf_sup_symmDiff : a ⊓ b ⊔ a ∆ b = a ⊔ b := by rw [sup_comm, symmDiff_sup_inf]

@[simp]
theorem symmDiff_symmDiff_inf : a ∆ b ∆ (a ⊓ b) = a ⊔ b := by
  rw [← symmDiff_sdiff_inf a, sdiff_symmDiff_eq_sup, symmDiff_sup_inf]

@[simp]
theorem inf_symmDiff_symmDiff : (a ⊓ b) ∆ (a ∆ b) = a ⊔ b := by
  rw [symmDiff_comm, symmDiff_symmDiff_inf]

theorem symmDiff_triangle : a ∆ c ≤ a ∆ b ⊔ b ∆ c := by
  refine (sup_le_sup (sdiff_triangle a b c) <| sdiff_triangle _ b _).trans_eq ?_
  rw [sup_comm (c \ b), sup_sup_sup_comm, symmDiff, symmDiff]

theorem le_symmDiff_sup_right (a b : α) : a ≤ (a ∆ b) ⊔ b := by
  convert symmDiff_triangle a b ⊥ <;> rw [symmDiff_bot]

theorem le_symmDiff_sup_left (a b : α) : b ≤ (a ∆ b) ⊔ a :=
  symmDiff_comm a b ▸ le_symmDiff_sup_right ..

end GeneralizedCoheytingAlgebra

section GeneralizedHeytingAlgebra

variable [GeneralizedHeytingAlgebra α] (a b c : α)

@[simp]
theorem toDual_bihimp : toDual (a ⇔ b) = toDual a ∆ toDual b :=
  rfl

@[simp]
theorem ofDual_symmDiff (a b : αᵒᵈ) : ofDual (a ∆ b) = ofDual a ⇔ ofDual b :=
  rfl

theorem bihimp_comm : a ⇔ b = b ⇔ a := by simp only [(· ⇔ ·), inf_comm]

instance bihimp_isCommutative : Std.Commutative (α := α) (· ⇔ ·) :=
  ⟨bihimp_comm⟩

@[simp]
theorem bihimp_self : a ⇔ a = ⊤ := by rw [bihimp, inf_idem, himp_self]

@[simp]
theorem bihimp_top : a ⇔ ⊤ = a := by rw [bihimp, himp_top, top_himp, inf_top_eq]

@[simp]
theorem top_bihimp : ⊤ ⇔ a = a := by rw [bihimp_comm, bihimp_top]

@[simp]
theorem bihimp_eq_top {a b : α} : a ⇔ b = ⊤ ↔ a = b :=
  @symmDiff_eq_bot αᵒᵈ _ _ _

theorem bihimp_of_le {a b : α} (h : a ≤ b) : a ⇔ b = b ⇨ a := by
  rw [bihimp, himp_eq_top_iff.2 h, inf_top_eq]

theorem bihimp_of_ge {a b : α} (h : b ≤ a) : a ⇔ b = a ⇨ b := by
  rw [bihimp, himp_eq_top_iff.2 h, top_inf_eq]

theorem le_bihimp {a b c : α} (hb : a ⊓ b ≤ c) (hc : a ⊓ c ≤ b) : a ≤ b ⇔ c :=
  le_inf (le_himp_iff.2 hc) <| le_himp_iff.2 hb

theorem le_bihimp_iff {a b c : α} : a ≤ b ⇔ c ↔ a ⊓ b ≤ c ∧ a ⊓ c ≤ b := by
  simp_rw [bihimp, le_inf_iff, le_himp_iff, and_comm]

@[simp]
theorem inf_le_bihimp {a b : α} : a ⊓ b ≤ a ⇔ b :=
  inf_le_inf le_himp le_himp

theorem bihimp_eq_sup_himp_inf : a ⇔ b = a ⊔ b ⇨ a ⊓ b := by simp [himp_inf_distrib, bihimp]

@[deprecated (since := "2025-06-05")] alias bihimp_eq_inf_himp_inf := bihimp_eq_sup_himp_inf

theorem Codisjoint.bihimp_eq_inf {a b : α} (h : Codisjoint a b) : a ⇔ b = a ⊓ b := by
  rw [bihimp, h.himp_eq_left, h.himp_eq_right]

theorem himp_bihimp : a ⇨ b ⇔ c = (a ⊓ c ⇨ b) ⊓ (a ⊓ b ⇨ c) := by
  rw [bihimp, himp_inf_distrib, himp_himp, himp_himp]

@[simp]
theorem sup_himp_bihimp : a ⊔ b ⇨ a ⇔ b = a ⇔ b := by
  rw [himp_bihimp]
  simp [bihimp]

@[simp]
theorem bihimp_himp_eq_inf : a ⇔ (a ⇨ b) = a ⊓ b :=
  @symmDiff_sdiff_eq_sup αᵒᵈ _ _ _

@[simp]
theorem himp_bihimp_eq_inf : (b ⇨ a) ⇔ b = a ⊓ b :=
  @sdiff_symmDiff_eq_sup αᵒᵈ _ _ _

@[simp]
theorem bihimp_inf_sup : a ⇔ b ⊓ (a ⊔ b) = a ⊓ b :=
  @symmDiff_sup_inf αᵒᵈ _ _ _

@[simp]
theorem sup_inf_bihimp : (a ⊔ b) ⊓ a ⇔ b = a ⊓ b :=
  @inf_sup_symmDiff αᵒᵈ _ _ _

@[simp]
theorem bihimp_bihimp_sup : a ⇔ b ⇔ (a ⊔ b) = a ⊓ b :=
  @symmDiff_symmDiff_inf αᵒᵈ _ _ _

@[simp]
theorem sup_bihimp_bihimp : (a ⊔ b) ⇔ (a ⇔ b) = a ⊓ b :=
  @inf_symmDiff_symmDiff αᵒᵈ _ _ _

theorem bihimp_triangle : a ⇔ b ⊓ b ⇔ c ≤ a ⇔ c :=
  @symmDiff_triangle αᵒᵈ _ _ _ _

end GeneralizedHeytingAlgebra

section CoheytingAlgebra

variable [CoheytingAlgebra α] (a : α)

@[simp]
theorem symmDiff_top' : a ∆ ⊤ = ￢a := by simp [symmDiff]

@[simp]
theorem top_symmDiff' : ⊤ ∆ a = ￢a := by simp [symmDiff]

@[simp]
theorem hnot_symmDiff_self : (￢a) ∆ a = ⊤ := by
  rw [eq_top_iff, symmDiff, hnot_sdiff, sup_sdiff_self]
  exact Codisjoint.top_le codisjoint_hnot_left

@[simp]
theorem symmDiff_hnot_self : a ∆ (￢a) = ⊤ := by rw [symmDiff_comm, hnot_symmDiff_self]

theorem IsCompl.symmDiff_eq_top {a b : α} (h : IsCompl a b) : a ∆ b = ⊤ := by
  rw [h.eq_hnot, hnot_symmDiff_self]

end CoheytingAlgebra

section HeytingAlgebra

variable [HeytingAlgebra α] (a : α)

@[simp]
theorem bihimp_bot : a ⇔ ⊥ = aᶜ := by simp [bihimp]

@[simp]
theorem bot_bihimp : ⊥ ⇔ a = aᶜ := by simp [bihimp]

@[simp]
theorem compl_bihimp_self : aᶜ ⇔ a = ⊥ :=
  @hnot_symmDiff_self αᵒᵈ _ _

@[simp]
theorem bihimp_hnot_self : a ⇔ aᶜ = ⊥ :=
  @symmDiff_hnot_self αᵒᵈ _ _

theorem IsCompl.bihimp_eq_bot {a b : α} (h : IsCompl a b) : a ⇔ b = ⊥ := by
  rw [h.eq_compl, compl_bihimp_self]

end HeytingAlgebra

section GeneralizedBooleanAlgebra

variable [GeneralizedBooleanAlgebra α] (a b c d : α)

@[simp]
theorem sup_sdiff_symmDiff : (a ⊔ b) \ a ∆ b = a ⊓ b :=
  sdiff_eq_symm inf_le_sup (by rw [symmDiff_eq_sup_sdiff_inf])

theorem disjoint_symmDiff_inf : Disjoint (a ∆ b) (a ⊓ b) := by
  rw [symmDiff_eq_sup_sdiff_inf]
  exact disjoint_sdiff_self_left

theorem inf_symmDiff_distrib_left : a ⊓ b ∆ c = (a ⊓ b) ∆ (a ⊓ c) := by
  rw [symmDiff_eq_sup_sdiff_inf, inf_sdiff_distrib_left, inf_sup_left, inf_inf_distrib_left,
    symmDiff_eq_sup_sdiff_inf]

theorem inf_symmDiff_distrib_right : a ∆ b ⊓ c = (a ⊓ c) ∆ (b ⊓ c) := by
  simp_rw [inf_comm _ c, inf_symmDiff_distrib_left]

theorem sdiff_symmDiff : c \ a ∆ b = c ⊓ a ⊓ b ⊔ c \ a ⊓ c \ b := by
  simp only [(· ∆ ·), sdiff_sdiff_sup_sdiff']

theorem sdiff_symmDiff' : c \ a ∆ b = c ⊓ a ⊓ b ⊔ c \ (a ⊔ b) := by
  rw [sdiff_symmDiff, sdiff_sup]

@[simp]
theorem symmDiff_sdiff_left : a ∆ b \ a = b \ a := by
  rw [symmDiff_def, sup_sdiff, sdiff_idem, sdiff_sdiff_self, bot_sup_eq]

@[simp]
theorem symmDiff_sdiff_right : a ∆ b \ b = a \ b := by rw [symmDiff_comm, symmDiff_sdiff_left]

@[simp]
theorem sdiff_symmDiff_left : a \ a ∆ b = a ⊓ b := by simp [sdiff_symmDiff]

@[simp]
theorem sdiff_symmDiff_right : b \ a ∆ b = a ⊓ b := by
  rw [symmDiff_comm, inf_comm, sdiff_symmDiff_left]

theorem symmDiff_eq_sup : a ∆ b = a ⊔ b ↔ Disjoint a b := by
  refine ⟨fun h => ?_, Disjoint.symmDiff_eq_sup⟩
  rw [symmDiff_eq_sup_sdiff_inf, sdiff_eq_self_iff_disjoint] at h
  exact h.of_disjoint_inf_of_le le_sup_left

@[simp]
theorem le_symmDiff_iff_left : a ≤ a ∆ b ↔ Disjoint a b := by
  refine ⟨fun h => ?_, fun h => h.symmDiff_eq_sup.symm ▸ le_sup_left⟩
  rw [symmDiff_eq_sup_sdiff_inf] at h
  exact disjoint_iff_inf_le.mpr (le_sdiff_right.1 <| inf_le_of_left_le h).le

@[simp]
theorem le_symmDiff_iff_right : b ≤ a ∆ b ↔ Disjoint a b := by
  rw [symmDiff_comm, le_symmDiff_iff_left, disjoint_comm]

theorem symmDiff_symmDiff_left :
    a ∆ b ∆ c = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ c \ (a ⊔ b) ⊔ a ⊓ b ⊓ c :=
  calc
    a ∆ b ∆ c = a ∆ b \ c ⊔ c \ a ∆ b := symmDiff_def _ _
    _ = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ (c \ (a ⊔ b) ⊔ c ⊓ a ⊓ b) := by
        { rw [sdiff_symmDiff', sup_comm (c ⊓ a ⊓ b), symmDiff_sdiff] }
    _ = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ c \ (a ⊔ b) ⊔ a ⊓ b ⊓ c := by ac_rfl

theorem symmDiff_symmDiff_right :
    a ∆ (b ∆ c) = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ c \ (a ⊔ b) ⊔ a ⊓ b ⊓ c :=
  calc
    a ∆ (b ∆ c) = a \ b ∆ c ⊔ b ∆ c \ a := symmDiff_def _ _
    _ = a \ (b ⊔ c) ⊔ a ⊓ b ⊓ c ⊔ (b \ (c ⊔ a) ⊔ c \ (b ⊔ a)) := by
        { rw [sdiff_symmDiff', sup_comm (a ⊓ b ⊓ c), symmDiff_sdiff] }
    _ = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ c \ (a ⊔ b) ⊔ a ⊓ b ⊓ c := by ac_rfl

theorem symmDiff_assoc : a ∆ b ∆ c = a ∆ (b ∆ c) := by
  rw [symmDiff_symmDiff_left, symmDiff_symmDiff_right]

instance symmDiff_isAssociative : Std.Associative (α := α) (· ∆ ·) :=
  ⟨symmDiff_assoc⟩

theorem symmDiff_left_comm : a ∆ (b ∆ c) = b ∆ (a ∆ c) := by
  simp_rw [← symmDiff_assoc, symmDiff_comm]

theorem symmDiff_right_comm : a ∆ b ∆ c = a ∆ c ∆ b := by simp_rw [symmDiff_assoc, symmDiff_comm]

theorem symmDiff_symmDiff_symmDiff_comm : a ∆ b ∆ (c ∆ d) = a ∆ c ∆ (b ∆ d) := by
  simp_rw [symmDiff_assoc, symmDiff_left_comm]

@[simp]
theorem symmDiff_symmDiff_cancel_left : a ∆ (a ∆ b) = b := by simp [← symmDiff_assoc]

@[simp]
theorem symmDiff_symmDiff_cancel_right : b ∆ a ∆ a = b := by simp [symmDiff_assoc]

@[simp]
theorem symmDiff_symmDiff_self' : a ∆ b ∆ a = b := by
  rw [symmDiff_comm, symmDiff_symmDiff_cancel_left]

theorem symmDiff_left_involutive (a : α) : Involutive (· ∆ a) :=
  symmDiff_symmDiff_cancel_right _

theorem symmDiff_right_involutive (a : α) : Involutive (a ∆ ·) :=
  symmDiff_symmDiff_cancel_left _

theorem symmDiff_left_injective (a : α) : Injective (· ∆ a) :=
  Function.Involutive.injective (symmDiff_left_involutive a)

theorem symmDiff_right_injective (a : α) : Injective (a ∆ ·) :=
  Function.Involutive.injective (symmDiff_right_involutive _)

theorem symmDiff_left_surjective (a : α) : Surjective (· ∆ a) :=
  Function.Involutive.surjective (symmDiff_left_involutive _)

theorem symmDiff_right_surjective (a : α) : Surjective (a ∆ ·) :=
  Function.Involutive.surjective (symmDiff_right_involutive _)

variable {a b c}

@[simp]
theorem symmDiff_left_inj : a ∆ b = c ∆ b ↔ a = c :=
  (symmDiff_left_injective _).eq_iff

@[simp]
theorem symmDiff_right_inj : a ∆ b = a ∆ c ↔ b = c :=
  (symmDiff_right_injective _).eq_iff

@[simp]
theorem symmDiff_eq_left : a ∆ b = a ↔ b = ⊥ :=
  calc
    a ∆ b = a ↔ a ∆ b = a ∆ ⊥ := by rw [symmDiff_bot]
    _ ↔ b = ⊥ := by rw [symmDiff_right_inj]

@[simp]
theorem symmDiff_eq_right : a ∆ b = b ↔ a = ⊥ := by rw [symmDiff_comm, symmDiff_eq_left]

protected theorem Disjoint.symmDiff_left (ha : Disjoint a c) (hb : Disjoint b c) :
    Disjoint (a ∆ b) c := by
  rw [symmDiff_eq_sup_sdiff_inf]
  exact (ha.sup_left hb).disjoint_sdiff_left

protected theorem Disjoint.symmDiff_right (ha : Disjoint a b) (hb : Disjoint a c) :
    Disjoint a (b ∆ c) :=
  (ha.symm.symmDiff_left hb.symm).symm

theorem symmDiff_eq_iff_sdiff_eq (ha : a ≤ c) : a ∆ b = c ↔ c \ a = b := by
  rw [← symmDiff_of_le ha]
  exact ((symmDiff_right_involutive a).toPerm _).apply_eq_iff_eq_symm_apply.trans eq_comm

end GeneralizedBooleanAlgebra

section BooleanAlgebra

variable [BooleanAlgebra α] (a b c d : α)

/-! `CogeneralizedBooleanAlgebra` isn't actually a typeclass, but the lemmas in here are dual to
the `GeneralizedBooleanAlgebra` ones -/
section CogeneralizedBooleanAlgebra

@[simp]
theorem inf_himp_bihimp : a ⇔ b ⇨ a ⊓ b = a ⊔ b :=
  @sup_sdiff_symmDiff αᵒᵈ _ _ _

theorem codisjoint_bihimp_sup : Codisjoint (a ⇔ b) (a ⊔ b) :=
  @disjoint_symmDiff_inf αᵒᵈ _ _ _

@[simp]
theorem himp_bihimp_left : a ⇨ a ⇔ b = a ⇨ b :=
  @symmDiff_sdiff_left αᵒᵈ _ _ _

@[simp]
theorem himp_bihimp_right : b ⇨ a ⇔ b = b ⇨ a :=
  @symmDiff_sdiff_right αᵒᵈ _ _ _

@[simp]
theorem bihimp_himp_left : a ⇔ b ⇨ a = a ⊔ b :=
  @sdiff_symmDiff_left αᵒᵈ _ _ _

@[simp]
theorem bihimp_himp_right : a ⇔ b ⇨ b = a ⊔ b :=
  @sdiff_symmDiff_right αᵒᵈ _ _ _

@[simp]
theorem bihimp_eq_inf : a ⇔ b = a ⊓ b ↔ Codisjoint a b :=
  @symmDiff_eq_sup αᵒᵈ _ _ _

@[simp]
theorem bihimp_le_iff_left : a ⇔ b ≤ a ↔ Codisjoint a b :=
  @le_symmDiff_iff_left αᵒᵈ _ _ _

@[simp]
theorem bihimp_le_iff_right : a ⇔ b ≤ b ↔ Codisjoint a b :=
  @le_symmDiff_iff_right αᵒᵈ _ _ _

theorem bihimp_assoc : a ⇔ b ⇔ c = a ⇔ (b ⇔ c) :=
  @symmDiff_assoc αᵒᵈ _ _ _ _

instance bihimp_isAssociative : Std.Associative (α := α) (· ⇔ ·) :=
  ⟨bihimp_assoc⟩

theorem bihimp_left_comm : a ⇔ (b ⇔ c) = b ⇔ (a ⇔ c) := by simp_rw [← bihimp_assoc, bihimp_comm]

theorem bihimp_right_comm : a ⇔ b ⇔ c = a ⇔ c ⇔ b := by simp_rw [bihimp_assoc, bihimp_comm]

theorem bihimp_bihimp_bihimp_comm : a ⇔ b ⇔ (c ⇔ d) = a ⇔ c ⇔ (b ⇔ d) := by
  simp_rw [bihimp_assoc, bihimp_left_comm]

@[simp]
theorem bihimp_bihimp_cancel_left : a ⇔ (a ⇔ b) = b := by simp [← bihimp_assoc]

@[simp]
theorem bihimp_bihimp_cancel_right : b ⇔ a ⇔ a = b := by simp [bihimp_assoc]

@[simp]
theorem bihimp_bihimp_self : a ⇔ b ⇔ a = b := by rw [bihimp_comm, bihimp_bihimp_cancel_left]

theorem bihimp_left_involutive (a : α) : Involutive (· ⇔ a) :=
  bihimp_bihimp_cancel_right _

theorem bihimp_right_involutive (a : α) : Involutive (a ⇔ ·) :=
  bihimp_bihimp_cancel_left _

theorem bihimp_left_injective (a : α) : Injective (· ⇔ a) :=
  @symmDiff_left_injective αᵒᵈ _ _

theorem bihimp_right_injective (a : α) : Injective (a ⇔ ·) :=
  @symmDiff_right_injective αᵒᵈ _ _

theorem bihimp_left_surjective (a : α) : Surjective (· ⇔ a) :=
  @symmDiff_left_surjective αᵒᵈ _ _

theorem bihimp_right_surjective (a : α) : Surjective (a ⇔ ·) :=
  @symmDiff_right_surjective αᵒᵈ _ _

variable {a b c}

@[simp]
theorem bihimp_left_inj : a ⇔ b = c ⇔ b ↔ a = c :=
  (bihimp_left_injective _).eq_iff

@[simp]
theorem bihimp_right_inj : a ⇔ b = a ⇔ c ↔ b = c :=
  (bihimp_right_injective _).eq_iff

@[simp]
theorem bihimp_eq_left : a ⇔ b = a ↔ b = ⊤ :=
  @symmDiff_eq_left αᵒᵈ _ _ _

@[simp]
theorem bihimp_eq_right : a ⇔ b = b ↔ a = ⊤ :=
  @symmDiff_eq_right αᵒᵈ _ _ _

protected theorem Codisjoint.bihimp_left (ha : Codisjoint a c) (hb : Codisjoint b c) :
    Codisjoint (a ⇔ b) c :=
  (ha.inf_left hb).mono_left inf_le_bihimp

protected theorem Codisjoint.bihimp_right (ha : Codisjoint a b) (hb : Codisjoint a c) :
    Codisjoint a (b ⇔ c) :=
  (ha.inf_right hb).mono_right inf_le_bihimp

end CogeneralizedBooleanAlgebra

theorem symmDiff_eq : a ∆ b = a ⊓ bᶜ ⊔ b ⊓ aᶜ := by simp only [(· ∆ ·), sdiff_eq]

theorem bihimp_eq : a ⇔ b = (a ⊔ bᶜ) ⊓ (b ⊔ aᶜ) := by simp only [(· ⇔ ·), himp_eq]

theorem symmDiff_eq' : a ∆ b = (a ⊔ b) ⊓ (aᶜ ⊔ bᶜ) := by
  rw [symmDiff_eq_sup_sdiff_inf, sdiff_eq, compl_inf]

theorem bihimp_eq' : a ⇔ b = a ⊓ b ⊔ aᶜ ⊓ bᶜ :=
  @symmDiff_eq' αᵒᵈ _ _ _

theorem symmDiff_top : a ∆ ⊤ = aᶜ :=
  symmDiff_top' _

theorem top_symmDiff : ⊤ ∆ a = aᶜ :=
  top_symmDiff' _

@[simp]
theorem compl_symmDiff : (a ∆ b)ᶜ = a ⇔ b := by
  simp_rw [symmDiff, compl_sup_distrib, compl_sdiff, bihimp, inf_comm]

@[simp]
theorem compl_bihimp : (a ⇔ b)ᶜ = a ∆ b :=
  @compl_symmDiff αᵒᵈ _ _ _

@[simp]
theorem compl_symmDiff_compl : aᶜ ∆ bᶜ = a ∆ b :=
  (sup_comm _ _).trans <| by simp_rw [compl_sdiff_compl, sdiff_eq, symmDiff_eq]

@[simp]
theorem compl_bihimp_compl : aᶜ ⇔ bᶜ = a ⇔ b :=
  @compl_symmDiff_compl αᵒᵈ _ _ _

@[simp]
theorem symmDiff_eq_top : a ∆ b = ⊤ ↔ IsCompl a b := by
  rw [symmDiff_eq', ← compl_inf, inf_eq_top_iff, compl_eq_top, isCompl_iff, disjoint_iff,
    codisjoint_iff, and_comm]

@[simp]
theorem bihimp_eq_bot : a ⇔ b = ⊥ ↔ IsCompl a b := by
  rw [bihimp_eq', ← compl_sup, sup_eq_bot_iff, compl_eq_bot, isCompl_iff, disjoint_iff,
    codisjoint_iff]

@[simp]
theorem compl_symmDiff_self : aᶜ ∆ a = ⊤ :=
  hnot_symmDiff_self _

@[simp]
theorem symmDiff_compl_self : a ∆ aᶜ = ⊤ :=
  symmDiff_hnot_self _

theorem symmDiff_symmDiff_right' :
    a ∆ (b ∆ c) = a ⊓ b ⊓ c ⊔ a ⊓ bᶜ ⊓ cᶜ ⊔ aᶜ ⊓ b ⊓ cᶜ ⊔ aᶜ ⊓ bᶜ ⊓ c :=
  calc
    a ∆ (b ∆ c) = a ⊓ (b ⊓ c ⊔ bᶜ ⊓ cᶜ) ⊔ (b ⊓ cᶜ ⊔ c ⊓ bᶜ) ⊓ aᶜ := by
        { rw [symmDiff_eq, compl_symmDiff, bihimp_eq', symmDiff_eq] }
    _ = a ⊓ b ⊓ c ⊔ a ⊓ bᶜ ⊓ cᶜ ⊔ b ⊓ cᶜ ⊓ aᶜ ⊔ c ⊓ bᶜ ⊓ aᶜ := by
        { rw [inf_sup_left, inf_sup_right, ← sup_assoc, ← inf_assoc, ← inf_assoc] }
    _ = a ⊓ b ⊓ c ⊔ a ⊓ bᶜ ⊓ cᶜ ⊔ aᶜ ⊓ b ⊓ cᶜ ⊔ aᶜ ⊓ bᶜ ⊓ c := (by
      congr 1
      · congr 1
        rw [inf_comm, inf_assoc]
      · apply inf_left_right_swap)

variable {a b c}

theorem Disjoint.le_symmDiff_sup_symmDiff_left (h : Disjoint a b) : c ≤ a ∆ c ⊔ b ∆ c := by
  trans c \ (a ⊓ b)
  · rw [h.eq_bot, sdiff_bot]
  · rw [sdiff_inf]
    exact sup_le_sup le_sup_right le_sup_right

theorem Disjoint.le_symmDiff_sup_symmDiff_right (h : Disjoint b c) : a ≤ a ∆ b ⊔ a ∆ c := by
  simp_rw [symmDiff_comm a]
  exact h.le_symmDiff_sup_symmDiff_left

theorem Codisjoint.bihimp_inf_bihimp_le_left (h : Codisjoint a b) : a ⇔ c ⊓ b ⇔ c ≤ c :=
  h.dual.le_symmDiff_sup_symmDiff_left

theorem Codisjoint.bihimp_inf_bihimp_le_right (h : Codisjoint b c) : a ⇔ b ⊓ a ⇔ c ≤ a :=
  h.dual.le_symmDiff_sup_symmDiff_right

end BooleanAlgebra

/-! ### Prod -/


section Prod

@[simp]
theorem symmDiff_fst [GeneralizedCoheytingAlgebra α] [GeneralizedCoheytingAlgebra β]
    (a b : α × β) : (a ∆ b).1 = a.1 ∆ b.1 :=
  rfl

@[simp]
theorem symmDiff_snd [GeneralizedCoheytingAlgebra α] [GeneralizedCoheytingAlgebra β]
    (a b : α × β) : (a ∆ b).2 = a.2 ∆ b.2 :=
  rfl

@[simp]
theorem bihimp_fst [GeneralizedHeytingAlgebra α] [GeneralizedHeytingAlgebra β] (a b : α × β) :
    (a ⇔ b).1 = a.1 ⇔ b.1 :=
  rfl

@[simp]
theorem bihimp_snd [GeneralizedHeytingAlgebra α] [GeneralizedHeytingAlgebra β] (a b : α × β) :
    (a ⇔ b).2 = a.2 ⇔ b.2 :=
  rfl

end Prod

/-! ### Pi -/


namespace Pi

theorem symmDiff_def [∀ i, GeneralizedCoheytingAlgebra (π i)] (a b : ∀ i, π i) :
    a ∆ b = fun i => a i ∆ b i :=
  rfl

theorem bihimp_def [∀ i, GeneralizedHeytingAlgebra (π i)] (a b : ∀ i, π i) :
    a ⇔ b = fun i => a i ⇔ b i :=
  rfl

@[simp]
theorem symmDiff_apply [∀ i, GeneralizedCoheytingAlgebra (π i)] (a b : ∀ i, π i) (i : ι) :
    (a ∆ b) i = a i ∆ b i :=
  rfl

@[simp]
theorem bihimp_apply [∀ i, GeneralizedHeytingAlgebra (π i)] (a b : ∀ i, π i) (i : ι) :
    (a ⇔ b) i = a i ⇔ b i :=
  rfl

end Pi
