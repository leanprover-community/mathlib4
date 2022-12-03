/-
Copyright (c) 2021 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Bryan Gin-ge Chen, Yaël Dillies
-/
import Mathbin.Order.BooleanAlgebra
import Mathbin.Logic.Equiv.Basic

/-!
# Symmetric difference and bi-implication

This file defines the symmetric difference and bi-implication operators in (co-)Heyting algebras.

## Examples

Some examples are
* The symmetric difference of two sets is the set of elements that are in either but not both.
* The symmetric difference on propositions is `xor`.
* The symmetric difference on `bool` is `bxor`.
* The equivalence of propositions. Two propositions are equivalent if they imply each other.
* The symmetric difference translates to addition when considering a Boolean algebra as a Boolean
  ring.

## Main declarations

* `symm_diff`: The symmetric difference operator, defined as `(a \ b) ⊔ (b \ a)`
* `bihimp`: The bi-implication operator, defined as `(b ⇨ a) ⊓ (a ⇨ b)`

In generalized Boolean algebras, the symmetric difference operator is:

* `symm_diff_comm`: commutative, and
* `symm_diff_assoc`: associative.

## Notations

* `a ∆ b`: `symm_diff a b`
* `a ⇔ b`: `bihimp a b`

## References

The proof of associativity follows the note "Associativity of the Symmetric Difference of Sets: A
Proof from the Book" by John McCuan:

* <https://people.math.gatech.edu/~mccuan/courses/4317/symmetricdifference.pdf>

## Tags

boolean ring, generalized boolean algebra, boolean algebra, symmetric difference, bi-implication,
Heyting
-/


open Function OrderDual

variable {ι α β : Type _} {π : ι → Type _}

/-- The symmetric difference operator on a type with `⊔` and `\` is `(A \ B) ⊔ (B \ A)`. -/
def symmDiff [HasSup α] [SDiff α] (a b : α) : α :=
  a \ b ⊔ b \ a
#align symm_diff symmDiff

/-- The Heyting bi-implication is `(b ⇨ a) ⊓ (a ⇨ b)`. This generalizes equivalence of
propositions. -/
def bihimp [HasInf α] [HasHimp α] (a b : α) : α :=
  (b ⇨ a) ⊓ (a ⇨ b)
#align bihimp bihimp

-- mathport name: «expr ∆ »
infixl:100
  " ∆ " =>/- This notation might conflict with the Laplacian once we have it. Feel free to put it in locale
  `order` or `symm_diff` if that happens. -/
  symmDiff

-- mathport name: «expr ⇔ »
infixl:100 " ⇔ " => bihimp

theorem symm_diff_def [HasSup α] [SDiff α] (a b : α) : a ∆ b = a \ b ⊔ b \ a :=
  rfl
#align symm_diff_def symm_diff_def

theorem bihimp_def [HasInf α] [HasHimp α] (a b : α) : a ⇔ b = (b ⇨ a) ⊓ (a ⇨ b) :=
  rfl
#align bihimp_def bihimp_def

theorem symm_diff_eq_xor (p q : Prop) : p ∆ q = Xor' p q :=
  rfl
#align symm_diff_eq_xor symm_diff_eq_xor

@[simp]
theorem bihimp_iff_iff {p q : Prop} : p ⇔ q ↔ (p ↔ q) :=
  (iff_iff_implies_and_implies _ _).symm.trans Iff.comm
#align bihimp_iff_iff bihimp_iff_iff

@[simp]
theorem Bool.symm_diff_eq_bxor : ∀ p q : Bool, p ∆ q = xor p q := by decide
#align bool.symm_diff_eq_bxor Bool.symm_diff_eq_bxor

section GeneralizedCoheytingAlgebra

variable [GeneralizedCoheytingAlgebra α] (a b c d : α)

@[simp]
theorem to_dual_symm_diff : toDual (a ∆ b) = toDual a ⇔ toDual b :=
  rfl
#align to_dual_symm_diff to_dual_symm_diff

@[simp]
theorem of_dual_bihimp (a b : αᵒᵈ) : ofDual (a ⇔ b) = ofDual a ∆ ofDual b :=
  rfl
#align of_dual_bihimp of_dual_bihimp

theorem symm_diff_comm : a ∆ b = b ∆ a := by simp only [(· ∆ ·), sup_comm]
#align symm_diff_comm symm_diff_comm

instance symm_diff_is_comm : IsCommutative α (· ∆ ·) :=
  ⟨symm_diff_comm⟩
#align symm_diff_is_comm symm_diff_is_comm

@[simp]
theorem symm_diff_self : a ∆ a = ⊥ := by rw [(· ∆ ·), sup_idem, sdiff_self]
#align symm_diff_self symm_diff_self

@[simp]
theorem symm_diff_bot : a ∆ ⊥ = a := by rw [(· ∆ ·), sdiff_bot, bot_sdiff, sup_bot_eq]
#align symm_diff_bot symm_diff_bot

@[simp]
theorem bot_symm_diff : ⊥ ∆ a = a := by rw [symm_diff_comm, symm_diff_bot]
#align bot_symm_diff bot_symm_diff

@[simp]
theorem symm_diff_eq_bot {a b : α} : a ∆ b = ⊥ ↔ a = b := by
  simp_rw [symmDiff, sup_eq_bot_iff, sdiff_eq_bot_iff, le_antisymm_iff]
#align symm_diff_eq_bot symm_diff_eq_bot

theorem symm_diff_of_le {a b : α} (h : a ≤ b) : a ∆ b = b \ a := by
  rw [symmDiff, sdiff_eq_bot_iff.2 h, bot_sup_eq]
#align symm_diff_of_le symm_diff_of_le

theorem symm_diff_of_ge {a b : α} (h : b ≤ a) : a ∆ b = a \ b := by
  rw [symmDiff, sdiff_eq_bot_iff.2 h, sup_bot_eq]
#align symm_diff_of_ge symm_diff_of_ge

theorem symm_diff_le {a b c : α} (ha : a ≤ b ⊔ c) (hb : b ≤ a ⊔ c) : a ∆ b ≤ c :=
  sup_le (sdiff_le_iff.2 ha) <| sdiff_le_iff.2 hb
#align symm_diff_le symm_diff_le

theorem symm_diff_le_iff {a b c : α} : a ∆ b ≤ c ↔ a ≤ b ⊔ c ∧ b ≤ a ⊔ c := by
  simp_rw [symmDiff, sup_le_iff, sdiff_le_iff]
#align symm_diff_le_iff symm_diff_le_iff

@[simp]
theorem symm_diff_le_sup {a b : α} : a ∆ b ≤ a ⊔ b :=
  sup_le_sup sdiff_le sdiff_le
#align symm_diff_le_sup symm_diff_le_sup

theorem symm_diff_eq_sup_sdiff_inf : a ∆ b = (a ⊔ b) \ (a ⊓ b) := by simp [sup_sdiff, symmDiff]
#align symm_diff_eq_sup_sdiff_inf symm_diff_eq_sup_sdiff_inf

theorem Disjoint.symm_diff_eq_sup {a b : α} (h : Disjoint a b) : a ∆ b = a ⊔ b := by
  rw [(· ∆ ·), h.sdiff_eq_left, h.sdiff_eq_right]
#align disjoint.symm_diff_eq_sup Disjoint.symm_diff_eq_sup

theorem symm_diff_sdiff : a ∆ b \ c = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) := by
  rw [symmDiff, sup_sdiff_distrib, sdiff_sdiff_left, sdiff_sdiff_left]
#align symm_diff_sdiff symm_diff_sdiff

@[simp]
theorem symm_diff_sdiff_inf : a ∆ b \ (a ⊓ b) = a ∆ b := by
  rw [symm_diff_sdiff]
  simp [symmDiff]
#align symm_diff_sdiff_inf symm_diff_sdiff_inf

@[simp]
theorem symm_diff_sdiff_eq_sup : a ∆ (b \ a) = a ⊔ b := by
  rw [symmDiff, sdiff_idem]
  exact
    le_antisymm (sup_le_sup sdiff_le sdiff_le)
      (sup_le le_sdiff_sup <| le_sdiff_sup.trans <| sup_le le_sup_right le_sdiff_sup)
#align symm_diff_sdiff_eq_sup symm_diff_sdiff_eq_sup

@[simp]
theorem sdiff_symm_diff_eq_sup : (a \ b) ∆ b = a ⊔ b := by
  rw [symm_diff_comm, symm_diff_sdiff_eq_sup, sup_comm]
#align sdiff_symm_diff_eq_sup sdiff_symm_diff_eq_sup

@[simp]
theorem symm_diff_sup_inf : a ∆ b ⊔ a ⊓ b = a ⊔ b := by
  refine' le_antisymm (sup_le symm_diff_le_sup inf_le_sup) _
  rw [sup_inf_left, symmDiff]
  refine' sup_le (le_inf le_sup_right _) (le_inf _ le_sup_right)
  · rw [sup_right_comm]
    exact le_sup_of_le_left le_sdiff_sup
  · rw [sup_assoc]
    exact le_sup_of_le_right le_sdiff_sup
#align symm_diff_sup_inf symm_diff_sup_inf

@[simp]
theorem inf_sup_symm_diff : a ⊓ b ⊔ a ∆ b = a ⊔ b := by rw [sup_comm, symm_diff_sup_inf]
#align inf_sup_symm_diff inf_sup_symm_diff

@[simp]
theorem symm_diff_symm_diff_inf : a ∆ b ∆ (a ⊓ b) = a ⊔ b := by
  rw [← symm_diff_sdiff_inf a, sdiff_symm_diff_eq_sup, symm_diff_sup_inf]
#align symm_diff_symm_diff_inf symm_diff_symm_diff_inf

@[simp]
theorem inf_symm_diff_symm_diff : (a ⊓ b) ∆ (a ∆ b) = a ⊔ b := by
  rw [symm_diff_comm, symm_diff_symm_diff_inf]
#align inf_symm_diff_symm_diff inf_symm_diff_symm_diff

theorem symm_diff_triangle : a ∆ c ≤ a ∆ b ⊔ b ∆ c := by
  refine' (sup_le_sup (sdiff_triangle a b c) <| sdiff_triangle _ b _).trans_eq _
  rw [@sup_comm _ _ (c \ b), sup_sup_sup_comm, symmDiff, symmDiff]
#align symm_diff_triangle symm_diff_triangle

end GeneralizedCoheytingAlgebra

section GeneralizedHeytingAlgebra

variable [GeneralizedHeytingAlgebra α] (a b c d : α)

@[simp]
theorem to_dual_bihimp : toDual (a ⇔ b) = toDual a ∆ toDual b :=
  rfl
#align to_dual_bihimp to_dual_bihimp

@[simp]
theorem of_dual_symm_diff (a b : αᵒᵈ) : ofDual (a ∆ b) = ofDual a ⇔ ofDual b :=
  rfl
#align of_dual_symm_diff of_dual_symm_diff

theorem bihimp_comm : a ⇔ b = b ⇔ a := by simp only [(· ⇔ ·), inf_comm]
#align bihimp_comm bihimp_comm

instance bihimp_is_comm : IsCommutative α (· ⇔ ·) :=
  ⟨bihimp_comm⟩
#align bihimp_is_comm bihimp_is_comm

@[simp]
theorem bihimp_self : a ⇔ a = ⊤ := by rw [(· ⇔ ·), inf_idem, himp_self]
#align bihimp_self bihimp_self

@[simp]
theorem bihimp_top : a ⇔ ⊤ = a := by rw [(· ⇔ ·), himp_top, top_himp, inf_top_eq]
#align bihimp_top bihimp_top

@[simp]
theorem top_bihimp : ⊤ ⇔ a = a := by rw [bihimp_comm, bihimp_top]
#align top_bihimp top_bihimp

@[simp]
theorem bihimp_eq_top {a b : α} : a ⇔ b = ⊤ ↔ a = b :=
  @symm_diff_eq_bot αᵒᵈ _ _ _
#align bihimp_eq_top bihimp_eq_top

theorem bihimp_of_le {a b : α} (h : a ≤ b) : a ⇔ b = b ⇨ a := by
  rw [bihimp, himp_eq_top_iff.2 h, inf_top_eq]
#align bihimp_of_le bihimp_of_le

theorem bihimp_of_ge {a b : α} (h : b ≤ a) : a ⇔ b = a ⇨ b := by
  rw [bihimp, himp_eq_top_iff.2 h, top_inf_eq]
#align bihimp_of_ge bihimp_of_ge

theorem le_bihimp {a b c : α} (hb : a ⊓ b ≤ c) (hc : a ⊓ c ≤ b) : a ≤ b ⇔ c :=
  le_inf (le_himp_iff.2 hc) <| le_himp_iff.2 hb
#align le_bihimp le_bihimp

theorem le_bihimp_iff {a b c : α} : a ≤ b ⇔ c ↔ a ⊓ b ≤ c ∧ a ⊓ c ≤ b := by
  simp_rw [bihimp, le_inf_iff, le_himp_iff, and_comm]
#align le_bihimp_iff le_bihimp_iff

@[simp]
theorem inf_le_bihimp {a b : α} : a ⊓ b ≤ a ⇔ b :=
  inf_le_inf le_himp le_himp
#align inf_le_bihimp inf_le_bihimp

theorem bihimp_eq_inf_himp_inf : a ⇔ b = a ⊔ b ⇨ a ⊓ b := by simp [himp_inf_distrib, bihimp]
#align bihimp_eq_inf_himp_inf bihimp_eq_inf_himp_inf

theorem Codisjoint.bihimp_eq_inf {a b : α} (h : Codisjoint a b) : a ⇔ b = a ⊓ b := by
  rw [(· ⇔ ·), h.himp_eq_left, h.himp_eq_right]
#align codisjoint.bihimp_eq_inf Codisjoint.bihimp_eq_inf

theorem himp_bihimp : a ⇨ b ⇔ c = (a ⊓ c ⇨ b) ⊓ (a ⊓ b ⇨ c) := by
  rw [bihimp, himp_inf_distrib, himp_himp, himp_himp]
#align himp_bihimp himp_bihimp

@[simp]
theorem sup_himp_bihimp : a ⊔ b ⇨ a ⇔ b = a ⇔ b := by
  rw [himp_bihimp]
  simp [bihimp]
#align sup_himp_bihimp sup_himp_bihimp

@[simp]
theorem bihimp_himp_eq_inf : a ⇔ (a ⇨ b) = a ⊓ b :=
  @symm_diff_sdiff_eq_sup αᵒᵈ _ _ _
#align bihimp_himp_eq_inf bihimp_himp_eq_inf

@[simp]
theorem himp_bihimp_eq_inf : (b ⇨ a) ⇔ b = a ⊓ b :=
  @sdiff_symm_diff_eq_sup αᵒᵈ _ _ _
#align himp_bihimp_eq_inf himp_bihimp_eq_inf

@[simp]
theorem bihimp_inf_sup : a ⇔ b ⊓ (a ⊔ b) = a ⊓ b :=
  @symm_diff_sup_inf αᵒᵈ _ _ _
#align bihimp_inf_sup bihimp_inf_sup

@[simp]
theorem sup_inf_bihimp : (a ⊔ b) ⊓ a ⇔ b = a ⊓ b :=
  @inf_sup_symm_diff αᵒᵈ _ _ _
#align sup_inf_bihimp sup_inf_bihimp

@[simp]
theorem bihimp_bihimp_sup : a ⇔ b ⇔ (a ⊔ b) = a ⊓ b :=
  @symm_diff_symm_diff_inf αᵒᵈ _ _ _
#align bihimp_bihimp_sup bihimp_bihimp_sup

@[simp]
theorem sup_bihimp_bihimp : (a ⊔ b) ⇔ (a ⇔ b) = a ⊓ b :=
  @inf_symm_diff_symm_diff αᵒᵈ _ _ _
#align sup_bihimp_bihimp sup_bihimp_bihimp

theorem bihimp_triangle : a ⇔ b ⊓ b ⇔ c ≤ a ⇔ c :=
  @symm_diff_triangle αᵒᵈ _ _ _ _
#align bihimp_triangle bihimp_triangle

end GeneralizedHeytingAlgebra

section CoheytingAlgebra

variable [CoheytingAlgebra α] (a : α)

@[simp]
theorem symm_diff_top' : a ∆ ⊤ = ￢a := by simp [symmDiff]
#align symm_diff_top' symm_diff_top'

@[simp]
theorem top_symm_diff' : ⊤ ∆ a = ￢a := by simp [symmDiff]
#align top_symm_diff' top_symm_diff'

@[simp]
theorem hnot_symm_diff_self : (￢a) ∆ a = ⊤ := by
  rw [eq_top_iff, symmDiff, hnot_sdiff, sup_sdiff_self]
  exact Codisjoint.top_le codisjoint_hnot_left
#align hnot_symm_diff_self hnot_symm_diff_self

@[simp]
theorem symm_diff_hnot_self : a ∆ (￢a) = ⊤ := by rw [symm_diff_comm, hnot_symm_diff_self]
#align symm_diff_hnot_self symm_diff_hnot_self

theorem IsCompl.symm_diff_eq_top {a b : α} (h : IsCompl a b) : a ∆ b = ⊤ := by
  rw [h.eq_hnot, hnot_symm_diff_self]
#align is_compl.symm_diff_eq_top IsCompl.symm_diff_eq_top

end CoheytingAlgebra

section HeytingAlgebra

variable [HeytingAlgebra α] (a : α)

@[simp]
theorem bihimp_bot : a ⇔ ⊥ = aᶜ := by simp [bihimp]
#align bihimp_bot bihimp_bot

@[simp]
theorem bot_bihimp : ⊥ ⇔ a = aᶜ := by simp [bihimp]
#align bot_bihimp bot_bihimp

@[simp]
theorem compl_bihimp_self : aᶜ ⇔ a = ⊥ :=
  @hnot_symm_diff_self αᵒᵈ _ _
#align compl_bihimp_self compl_bihimp_self

@[simp]
theorem bihimp_hnot_self : a ⇔ aᶜ = ⊥ :=
  @symm_diff_hnot_self αᵒᵈ _ _
#align bihimp_hnot_self bihimp_hnot_self

theorem IsCompl.bihimp_eq_bot {a b : α} (h : IsCompl a b) : a ⇔ b = ⊥ := by
  rw [h.eq_compl, compl_bihimp_self]
#align is_compl.bihimp_eq_bot IsCompl.bihimp_eq_bot

end HeytingAlgebra

section GeneralizedBooleanAlgebra

variable [GeneralizedBooleanAlgebra α] (a b c d : α)

@[simp]
theorem sup_sdiff_symm_diff : (a ⊔ b) \ a ∆ b = a ⊓ b :=
  sdiff_eq_symm inf_le_sup (by rw [symm_diff_eq_sup_sdiff_inf])
#align sup_sdiff_symm_diff sup_sdiff_symm_diff

theorem disjoint_symm_diff_inf : Disjoint (a ∆ b) (a ⊓ b) := by
  rw [symm_diff_eq_sup_sdiff_inf]
  exact disjoint_sdiff_self_left
#align disjoint_symm_diff_inf disjoint_symm_diff_inf

theorem inf_symm_diff_distrib_left : a ⊓ b ∆ c = (a ⊓ b) ∆ (a ⊓ c) := by
  rw [symm_diff_eq_sup_sdiff_inf, inf_sdiff_distrib_left, inf_sup_left, inf_inf_distrib_left,
    symm_diff_eq_sup_sdiff_inf]
#align inf_symm_diff_distrib_left inf_symm_diff_distrib_left

theorem inf_symm_diff_distrib_right : a ∆ b ⊓ c = (a ⊓ c) ∆ (b ⊓ c) := by
  simp_rw [@inf_comm _ _ _ c, inf_symm_diff_distrib_left]
#align inf_symm_diff_distrib_right inf_symm_diff_distrib_right

theorem sdiff_symm_diff : c \ a ∆ b = c ⊓ a ⊓ b ⊔ c \ a ⊓ c \ b := by
  simp only [(· ∆ ·), sdiff_sdiff_sup_sdiff']
#align sdiff_symm_diff sdiff_symm_diff

theorem sdiff_symm_diff' : c \ a ∆ b = c ⊓ a ⊓ b ⊔ c \ (a ⊔ b) := by
  rw [sdiff_symm_diff, sdiff_sup, sup_comm]
#align sdiff_symm_diff' sdiff_symm_diff'

@[simp]
theorem symm_diff_sdiff_left : a ∆ b \ a = b \ a := by
  rw [symm_diff_def, sup_sdiff, sdiff_idem, sdiff_sdiff_self, bot_sup_eq]
#align symm_diff_sdiff_left symm_diff_sdiff_left

@[simp]
theorem symm_diff_sdiff_right : a ∆ b \ b = a \ b := by rw [symm_diff_comm, symm_diff_sdiff_left]
#align symm_diff_sdiff_right symm_diff_sdiff_right

@[simp]
theorem sdiff_symm_diff_left : a \ a ∆ b = a ⊓ b := by simp [sdiff_symm_diff]
#align sdiff_symm_diff_left sdiff_symm_diff_left

@[simp]
theorem sdiff_symm_diff_right : b \ a ∆ b = a ⊓ b := by
  rw [symm_diff_comm, inf_comm, sdiff_symm_diff_left]
#align sdiff_symm_diff_right sdiff_symm_diff_right

theorem symm_diff_eq_sup : a ∆ b = a ⊔ b ↔ Disjoint a b := by
  refine' ⟨fun h => _, Disjoint.symm_diff_eq_sup⟩
  rw [symm_diff_eq_sup_sdiff_inf, sdiff_eq_self_iff_disjoint] at h
  exact h.of_disjoint_inf_of_le le_sup_left
#align symm_diff_eq_sup symm_diff_eq_sup

@[simp]
theorem le_symm_diff_iff_left : a ≤ a ∆ b ↔ Disjoint a b := by
  refine' ⟨fun h => _, fun h => h.symm_diff_eq_sup.symm ▸ le_sup_left⟩
  rw [symm_diff_eq_sup_sdiff_inf] at h
  exact disjoint_iff_inf_le.mpr (le_sdiff_iff.1 <| inf_le_of_left_le h).le
#align le_symm_diff_iff_left le_symm_diff_iff_left

@[simp]
theorem le_symm_diff_iff_right : b ≤ a ∆ b ↔ Disjoint a b := by
  rw [symm_diff_comm, le_symm_diff_iff_left, Disjoint.comm]
#align le_symm_diff_iff_right le_symm_diff_iff_right

theorem symm_diff_symm_diff_left :
    a ∆ b ∆ c = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ c \ (a ⊔ b) ⊔ a ⊓ b ⊓ c :=
  calc
    a ∆ b ∆ c = a ∆ b \ c ⊔ c \ a ∆ b := symm_diff_def _ _
    _ = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ (c \ (a ⊔ b) ⊔ c ⊓ a ⊓ b) := by
      rw [sdiff_symm_diff', @sup_comm _ _ (c ⊓ a ⊓ b), symm_diff_sdiff]
    _ = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ c \ (a ⊔ b) ⊔ a ⊓ b ⊓ c := by ac_rfl
    
#align symm_diff_symm_diff_left symm_diff_symm_diff_left

theorem symm_diff_symm_diff_right :
    a ∆ (b ∆ c) = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ c \ (a ⊔ b) ⊔ a ⊓ b ⊓ c :=
  calc
    a ∆ (b ∆ c) = a \ b ∆ c ⊔ b ∆ c \ a := symm_diff_def _ _
    _ = a \ (b ⊔ c) ⊔ a ⊓ b ⊓ c ⊔ (b \ (c ⊔ a) ⊔ c \ (b ⊔ a)) := by
      rw [sdiff_symm_diff', @sup_comm _ _ (a ⊓ b ⊓ c), symm_diff_sdiff]
    _ = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ c \ (a ⊔ b) ⊔ a ⊓ b ⊓ c := by ac_rfl
    
#align symm_diff_symm_diff_right symm_diff_symm_diff_right

theorem symm_diff_assoc : a ∆ b ∆ c = a ∆ (b ∆ c) := by
  rw [symm_diff_symm_diff_left, symm_diff_symm_diff_right]
#align symm_diff_assoc symm_diff_assoc

instance symm_diff_is_assoc : IsAssociative α (· ∆ ·) :=
  ⟨symm_diff_assoc⟩
#align symm_diff_is_assoc symm_diff_is_assoc

theorem symm_diff_left_comm : a ∆ (b ∆ c) = b ∆ (a ∆ c) := by
  simp_rw [← symm_diff_assoc, symm_diff_comm]
#align symm_diff_left_comm symm_diff_left_comm

theorem symm_diff_right_comm : a ∆ b ∆ c = a ∆ c ∆ b := by simp_rw [symm_diff_assoc, symm_diff_comm]
#align symm_diff_right_comm symm_diff_right_comm

theorem symm_diff_symm_diff_symm_diff_comm : a ∆ b ∆ (c ∆ d) = a ∆ c ∆ (b ∆ d) := by
  simp_rw [symm_diff_assoc, symm_diff_left_comm]
#align symm_diff_symm_diff_symm_diff_comm symm_diff_symm_diff_symm_diff_comm

@[simp]
theorem symm_diff_symm_diff_cancel_left : a ∆ (a ∆ b) = b := by simp [← symm_diff_assoc]
#align symm_diff_symm_diff_cancel_left symm_diff_symm_diff_cancel_left

@[simp]
theorem symm_diff_symm_diff_cancel_right : b ∆ a ∆ a = b := by simp [symm_diff_assoc]
#align symm_diff_symm_diff_cancel_right symm_diff_symm_diff_cancel_right

@[simp]
theorem symm_diff_symm_diff_self' : a ∆ b ∆ a = b := by
  rw [symm_diff_comm, symm_diff_symm_diff_cancel_left]
#align symm_diff_symm_diff_self' symm_diff_symm_diff_self'

theorem symm_diff_left_involutive (a : α) : Involutive (· ∆ a) :=
  symm_diff_symm_diff_cancel_right _
#align symm_diff_left_involutive symm_diff_left_involutive

theorem symm_diff_right_involutive (a : α) : Involutive ((· ∆ ·) a) :=
  symm_diff_symm_diff_cancel_left _
#align symm_diff_right_involutive symm_diff_right_involutive

theorem symm_diff_left_injective (a : α) : Injective (· ∆ a) :=
  (symm_diff_left_involutive _).Injective
#align symm_diff_left_injective symm_diff_left_injective

theorem symm_diff_right_injective (a : α) : Injective ((· ∆ ·) a) :=
  (symm_diff_right_involutive _).Injective
#align symm_diff_right_injective symm_diff_right_injective

theorem symm_diff_left_surjective (a : α) : Surjective (· ∆ a) :=
  (symm_diff_left_involutive _).Surjective
#align symm_diff_left_surjective symm_diff_left_surjective

theorem symm_diff_right_surjective (a : α) : Surjective ((· ∆ ·) a) :=
  (symm_diff_right_involutive _).Surjective
#align symm_diff_right_surjective symm_diff_right_surjective

variable {a b c}

@[simp]
theorem symm_diff_left_inj : a ∆ b = c ∆ b ↔ a = c :=
  (symm_diff_left_injective _).eq_iff
#align symm_diff_left_inj symm_diff_left_inj

@[simp]
theorem symm_diff_right_inj : a ∆ b = a ∆ c ↔ b = c :=
  (symm_diff_right_injective _).eq_iff
#align symm_diff_right_inj symm_diff_right_inj

@[simp]
theorem symm_diff_eq_left : a ∆ b = a ↔ b = ⊥ :=
  calc
    a ∆ b = a ↔ a ∆ b = a ∆ ⊥ := by rw [symm_diff_bot]
    _ ↔ b = ⊥ := by rw [symm_diff_right_inj]
    
#align symm_diff_eq_left symm_diff_eq_left

@[simp]
theorem symm_diff_eq_right : a ∆ b = b ↔ a = ⊥ := by rw [symm_diff_comm, symm_diff_eq_left]
#align symm_diff_eq_right symm_diff_eq_right

protected theorem Disjoint.symm_diff_left (ha : Disjoint a c) (hb : Disjoint b c) :
    Disjoint (a ∆ b) c := by 
  rw [symm_diff_eq_sup_sdiff_inf]
  exact (ha.sup_left hb).disjoint_sdiff_left
#align disjoint.symm_diff_left Disjoint.symm_diff_left

protected theorem Disjoint.symm_diff_right (ha : Disjoint a b) (hb : Disjoint a c) :
    Disjoint a (b ∆ c) :=
  (ha.symm.symm_diff_left hb.symm).symm
#align disjoint.symm_diff_right Disjoint.symm_diff_right

theorem symm_diff_eq_iff_sdiff_eq (ha : a ≤ c) : a ∆ b = c ↔ c \ a = b := by
  rw [← symm_diff_of_le ha]
  exact ((symm_diff_right_involutive a).toPerm _).apply_eq_iff_eq_symm_apply.trans eq_comm
#align symm_diff_eq_iff_sdiff_eq symm_diff_eq_iff_sdiff_eq

end GeneralizedBooleanAlgebra

section BooleanAlgebra

variable [BooleanAlgebra α] (a b c d : α)

/- `cogeneralized_boolean_algebra` isn't actually a typeclass, but the lemmas in here are dual to
the `generalized_boolean_algebra` ones -/
section CogeneralizedBooleanAlgebra

@[simp]
theorem inf_himp_bihimp : a ⇔ b ⇨ a ⊓ b = a ⊔ b :=
  @sup_sdiff_symm_diff αᵒᵈ _ _ _
#align inf_himp_bihimp inf_himp_bihimp

theorem codisjoint_bihimp_sup : Codisjoint (a ⇔ b) (a ⊔ b) :=
  @disjoint_symm_diff_inf αᵒᵈ _ _ _
#align codisjoint_bihimp_sup codisjoint_bihimp_sup

@[simp]
theorem himp_bihimp_left : a ⇨ a ⇔ b = a ⇨ b :=
  @symm_diff_sdiff_left αᵒᵈ _ _ _
#align himp_bihimp_left himp_bihimp_left

@[simp]
theorem himp_bihimp_right : b ⇨ a ⇔ b = b ⇨ a :=
  @symm_diff_sdiff_right αᵒᵈ _ _ _
#align himp_bihimp_right himp_bihimp_right

@[simp]
theorem bihimp_himp_left : a ⇔ b ⇨ a = a ⊔ b :=
  @sdiff_symm_diff_left αᵒᵈ _ _ _
#align bihimp_himp_left bihimp_himp_left

@[simp]
theorem bihimp_himp_right : a ⇔ b ⇨ b = a ⊔ b :=
  @sdiff_symm_diff_right αᵒᵈ _ _ _
#align bihimp_himp_right bihimp_himp_right

@[simp]
theorem bihimp_eq_inf : a ⇔ b = a ⊓ b ↔ Codisjoint a b :=
  @symm_diff_eq_sup αᵒᵈ _ _ _
#align bihimp_eq_inf bihimp_eq_inf

@[simp]
theorem bihimp_le_iff_left : a ⇔ b ≤ a ↔ Codisjoint a b :=
  @le_symm_diff_iff_left αᵒᵈ _ _ _
#align bihimp_le_iff_left bihimp_le_iff_left

@[simp]
theorem bihimp_le_iff_right : a ⇔ b ≤ b ↔ Codisjoint a b :=
  @le_symm_diff_iff_right αᵒᵈ _ _ _
#align bihimp_le_iff_right bihimp_le_iff_right

theorem bihimp_assoc : a ⇔ b ⇔ c = a ⇔ (b ⇔ c) :=
  @symm_diff_assoc αᵒᵈ _ _ _ _
#align bihimp_assoc bihimp_assoc

instance bihimp_is_assoc : IsAssociative α (· ⇔ ·) :=
  ⟨bihimp_assoc⟩
#align bihimp_is_assoc bihimp_is_assoc

theorem bihimp_left_comm : a ⇔ (b ⇔ c) = b ⇔ (a ⇔ c) := by simp_rw [← bihimp_assoc, bihimp_comm]
#align bihimp_left_comm bihimp_left_comm

theorem bihimp_right_comm : a ⇔ b ⇔ c = a ⇔ c ⇔ b := by simp_rw [bihimp_assoc, bihimp_comm]
#align bihimp_right_comm bihimp_right_comm

theorem bihimp_bihimp_bihimp_comm : a ⇔ b ⇔ (c ⇔ d) = a ⇔ c ⇔ (b ⇔ d) := by
  simp_rw [bihimp_assoc, bihimp_left_comm]
#align bihimp_bihimp_bihimp_comm bihimp_bihimp_bihimp_comm

@[simp]
theorem bihimp_bihimp_cancel_left : a ⇔ (a ⇔ b) = b := by simp [← bihimp_assoc]
#align bihimp_bihimp_cancel_left bihimp_bihimp_cancel_left

@[simp]
theorem bihimp_bihimp_cancel_right : b ⇔ a ⇔ a = b := by simp [bihimp_assoc]
#align bihimp_bihimp_cancel_right bihimp_bihimp_cancel_right

@[simp]
theorem bihimp_bihimp_self : a ⇔ b ⇔ a = b := by rw [bihimp_comm, bihimp_bihimp_cancel_left]
#align bihimp_bihimp_self bihimp_bihimp_self

theorem bihimp_left_involutive (a : α) : Involutive (· ⇔ a) :=
  bihimp_bihimp_cancel_right _
#align bihimp_left_involutive bihimp_left_involutive

theorem bihimp_right_involutive (a : α) : Involutive ((· ⇔ ·) a) :=
  bihimp_bihimp_cancel_left _
#align bihimp_right_involutive bihimp_right_involutive

theorem bihimp_left_injective (a : α) : Injective (· ⇔ a) :=
  @symm_diff_left_injective αᵒᵈ _ _
#align bihimp_left_injective bihimp_left_injective

theorem bihimp_right_injective (a : α) : Injective ((· ⇔ ·) a) :=
  @symm_diff_right_injective αᵒᵈ _ _
#align bihimp_right_injective bihimp_right_injective

theorem bihimp_left_surjective (a : α) : Surjective (· ⇔ a) :=
  @symm_diff_left_surjective αᵒᵈ _ _
#align bihimp_left_surjective bihimp_left_surjective

theorem bihimp_right_surjective (a : α) : Surjective ((· ⇔ ·) a) :=
  @symm_diff_right_surjective αᵒᵈ _ _
#align bihimp_right_surjective bihimp_right_surjective

variable {a b c}

@[simp]
theorem bihimp_left_inj : a ⇔ b = c ⇔ b ↔ a = c :=
  (bihimp_left_injective _).eq_iff
#align bihimp_left_inj bihimp_left_inj

@[simp]
theorem bihimp_right_inj : a ⇔ b = a ⇔ c ↔ b = c :=
  (bihimp_right_injective _).eq_iff
#align bihimp_right_inj bihimp_right_inj

@[simp]
theorem bihimp_eq_left : a ⇔ b = a ↔ b = ⊤ :=
  @symm_diff_eq_left αᵒᵈ _ _ _
#align bihimp_eq_left bihimp_eq_left

@[simp]
theorem bihimp_eq_right : a ⇔ b = b ↔ a = ⊤ :=
  @symm_diff_eq_right αᵒᵈ _ _ _
#align bihimp_eq_right bihimp_eq_right

protected theorem Codisjoint.bihimp_left (ha : Codisjoint a c) (hb : Codisjoint b c) :
    Codisjoint (a ⇔ b) c :=
  (ha.inf_left hb).mono_left inf_le_bihimp
#align codisjoint.bihimp_left Codisjoint.bihimp_left

protected theorem Codisjoint.bihimp_right (ha : Codisjoint a b) (hb : Codisjoint a c) :
    Codisjoint a (b ⇔ c) :=
  (ha.inf_right hb).mono_right inf_le_bihimp
#align codisjoint.bihimp_right Codisjoint.bihimp_right

end CogeneralizedBooleanAlgebra

theorem symm_diff_eq : a ∆ b = a ⊓ bᶜ ⊔ b ⊓ aᶜ := by simp only [(· ∆ ·), sdiff_eq]
#align symm_diff_eq symm_diff_eq

theorem bihimp_eq : a ⇔ b = (a ⊔ bᶜ) ⊓ (b ⊔ aᶜ) := by simp only [(· ⇔ ·), himp_eq]
#align bihimp_eq bihimp_eq

theorem symm_diff_eq' : a ∆ b = (a ⊔ b) ⊓ (aᶜ ⊔ bᶜ) := by
  rw [symm_diff_eq_sup_sdiff_inf, sdiff_eq, compl_inf]
#align symm_diff_eq' symm_diff_eq'

theorem bihimp_eq' : a ⇔ b = a ⊓ b ⊔ aᶜ ⊓ bᶜ :=
  @symm_diff_eq' αᵒᵈ _ _ _
#align bihimp_eq' bihimp_eq'

theorem symm_diff_top : a ∆ ⊤ = aᶜ :=
  symm_diff_top' _
#align symm_diff_top symm_diff_top

theorem top_symm_diff : ⊤ ∆ a = aᶜ :=
  top_symm_diff' _
#align top_symm_diff top_symm_diff

@[simp]
theorem compl_symm_diff : (a ∆ b)ᶜ = a ⇔ b := by
  simp_rw [symmDiff, compl_sup_distrib, compl_sdiff, bihimp, inf_comm]
#align compl_symm_diff compl_symm_diff

@[simp]
theorem compl_bihimp : (a ⇔ b)ᶜ = a ∆ b :=
  @compl_symm_diff αᵒᵈ _ _ _
#align compl_bihimp compl_bihimp

@[simp]
theorem compl_symm_diff_compl : aᶜ ∆ bᶜ = a ∆ b :=
  sup_comm.trans <| by simp_rw [compl_sdiff_compl, sdiff_eq, symm_diff_eq]
#align compl_symm_diff_compl compl_symm_diff_compl

@[simp]
theorem compl_bihimp_compl : aᶜ ⇔ bᶜ = a ⇔ b :=
  @compl_symm_diff_compl αᵒᵈ _ _ _
#align compl_bihimp_compl compl_bihimp_compl

@[simp]
theorem symm_diff_eq_top : a ∆ b = ⊤ ↔ IsCompl a b := by
  rw [symm_diff_eq', ← compl_inf, inf_eq_top_iff, compl_eq_top, isCompl_iff, disjoint_iff,
    codisjoint_iff, and_comm]
#align symm_diff_eq_top symm_diff_eq_top

@[simp]
theorem bihimp_eq_bot : a ⇔ b = ⊥ ↔ IsCompl a b := by
  rw [bihimp_eq', ← compl_sup, sup_eq_bot_iff, compl_eq_bot, isCompl_iff, disjoint_iff,
    codisjoint_iff]
#align bihimp_eq_bot bihimp_eq_bot

@[simp]
theorem compl_symm_diff_self : aᶜ ∆ a = ⊤ :=
  hnot_symm_diff_self _
#align compl_symm_diff_self compl_symm_diff_self

@[simp]
theorem symm_diff_compl_self : a ∆ aᶜ = ⊤ :=
  symm_diff_hnot_self _
#align symm_diff_compl_self symm_diff_compl_self

theorem symm_diff_symm_diff_right' :
    a ∆ (b ∆ c) = a ⊓ b ⊓ c ⊔ a ⊓ bᶜ ⊓ cᶜ ⊔ aᶜ ⊓ b ⊓ cᶜ ⊔ aᶜ ⊓ bᶜ ⊓ c :=
  calc
    a ∆ (b ∆ c) = a ⊓ (b ⊓ c ⊔ bᶜ ⊓ cᶜ) ⊔ (b ⊓ cᶜ ⊔ c ⊓ bᶜ) ⊓ aᶜ := by
      rw [symm_diff_eq, compl_symm_diff, bihimp_eq', symm_diff_eq]
    _ = a ⊓ b ⊓ c ⊔ a ⊓ bᶜ ⊓ cᶜ ⊔ b ⊓ cᶜ ⊓ aᶜ ⊔ c ⊓ bᶜ ⊓ aᶜ := by
      rw [inf_sup_left, inf_sup_right, ← sup_assoc, ← inf_assoc, ← inf_assoc]
    _ = a ⊓ b ⊓ c ⊔ a ⊓ bᶜ ⊓ cᶜ ⊔ aᶜ ⊓ b ⊓ cᶜ ⊔ aᶜ ⊓ bᶜ ⊓ c := by
      congr 1
      · congr 1
        rw [inf_comm, inf_assoc]
      · apply inf_left_right_swap
    
#align symm_diff_symm_diff_right' symm_diff_symm_diff_right'

variable {a b c}

theorem Disjoint.le_symm_diff_sup_symm_diff_left (h : Disjoint a b) : c ≤ a ∆ c ⊔ b ∆ c := by
  trans c \ (a ⊓ b)
  · rw [h.eq_bot, sdiff_bot]
  · rw [sdiff_inf]
    exact sup_le_sup le_sup_right le_sup_right
#align disjoint.le_symm_diff_sup_symm_diff_left Disjoint.le_symm_diff_sup_symm_diff_left

theorem Disjoint.le_symm_diff_sup_symm_diff_right (h : Disjoint b c) : a ≤ a ∆ b ⊔ a ∆ c := by
  simp_rw [symm_diff_comm a]
  exact h.le_symm_diff_sup_symm_diff_left
#align disjoint.le_symm_diff_sup_symm_diff_right Disjoint.le_symm_diff_sup_symm_diff_right

theorem Codisjoint.bihimp_inf_bihimp_le_left (h : Codisjoint a b) : a ⇔ c ⊓ b ⇔ c ≤ c :=
  h.dual.le_symm_diff_sup_symm_diff_left
#align codisjoint.bihimp_inf_bihimp_le_left Codisjoint.bihimp_inf_bihimp_le_left

theorem Codisjoint.bihimp_inf_bihimp_le_right (h : Codisjoint b c) : a ⇔ b ⊓ a ⇔ c ≤ a :=
  h.dual.le_symm_diff_sup_symm_diff_right
#align codisjoint.bihimp_inf_bihimp_le_right Codisjoint.bihimp_inf_bihimp_le_right

end BooleanAlgebra

/-! ### Prod -/


section Prod

@[simp]
theorem symm_diff_fst [GeneralizedCoheytingAlgebra α] [GeneralizedCoheytingAlgebra β]
    (a b : α × β) : (a ∆ b).1 = a.1 ∆ b.1 :=
  rfl
#align symm_diff_fst symm_diff_fst

@[simp]
theorem symm_diff_snd [GeneralizedCoheytingAlgebra α] [GeneralizedCoheytingAlgebra β]
    (a b : α × β) : (a ∆ b).2 = a.2 ∆ b.2 :=
  rfl
#align symm_diff_snd symm_diff_snd

@[simp]
theorem bihimp_fst [GeneralizedHeytingAlgebra α] [GeneralizedHeytingAlgebra β] (a b : α × β) :
    (a ⇔ b).1 = a.1 ⇔ b.1 :=
  rfl
#align bihimp_fst bihimp_fst

@[simp]
theorem bihimp_snd [GeneralizedHeytingAlgebra α] [GeneralizedHeytingAlgebra β] (a b : α × β) :
    (a ⇔ b).2 = a.2 ⇔ b.2 :=
  rfl
#align bihimp_snd bihimp_snd

end Prod

/-! ### Pi -/


namespace Pi

theorem symm_diff_def [∀ i, GeneralizedCoheytingAlgebra (π i)] (a b : ∀ i, π i) :
    a ∆ b = fun i => a i ∆ b i :=
  rfl
#align pi.symm_diff_def Pi.symm_diff_def

theorem bihimp_def [∀ i, GeneralizedHeytingAlgebra (π i)] (a b : ∀ i, π i) :
    a ⇔ b = fun i => a i ⇔ b i :=
  rfl
#align pi.bihimp_def Pi.bihimp_def

@[simp]
theorem symm_diff_apply [∀ i, GeneralizedCoheytingAlgebra (π i)] (a b : ∀ i, π i) (i : ι) :
    (a ∆ b) i = a i ∆ b i :=
  rfl
#align pi.symm_diff_apply Pi.symm_diff_apply

@[simp]
theorem bihimp_apply [∀ i, GeneralizedHeytingAlgebra (π i)] (a b : ∀ i, π i) (i : ι) :
    (a ⇔ b) i = a i ⇔ b i :=
  rfl
#align pi.bihimp_apply Pi.bihimp_apply

end Pi

