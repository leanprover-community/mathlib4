/-
Copyright (c) 2021 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Bryan Gin-ge Chen, Yaël Dillies
-/
import Mathlib.Order.BooleanAlgebra
import Mathlib.Logic.Equiv.Basic

#align_import order.symm_diff from "leanprover-community/mathlib"@"6eb334bd8f3433d5b08ba156b8ec3e6af47e1904"

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


open Function OrderDual

variable {ι α β : Type*} {π : ι → Type*}

/-- The symmetric difference operator on a type with `⊔` and `\` is `(A \ B) ⊔ (B \ A)`. -/
def symmDiff [Sup α] [SDiff α] (a b : α) : α :=
  a \ b ⊔ b \ a
#align symm_diff symmDiff

/-- The Heyting bi-implication is `(b ⇨ a) ⊓ (a ⇨ b)`. This generalizes equivalence of
propositions. -/
def bihimp [Inf α] [HImp α] (a b : α) : α :=
  (b ⇨ a) ⊓ (a ⇨ b)
#align bihimp bihimp

/- This notation might conflict with the Laplacian once we have it. Feel free to put it in locale
  `order` or `symmDiff` if that happens. -/
/-- Notation for symmDiff -/
infixl:100 " ∆ " => symmDiff

/-- Notation for bihimp -/
infixl:100 " ⇔ " => bihimp

theorem symmDiff_def [Sup α] [SDiff α] (a b : α) : a ∆ b = a \ b ⊔ b \ a :=
  rfl
#align symm_diff_def symmDiff_def

theorem bihimp_def [Inf α] [HImp α] (a b : α) : a ⇔ b = (b ⇨ a) ⊓ (a ⇨ b) :=
  rfl
#align bihimp_def bihimp_def

theorem symmDiff_eq_Xor' (p q : Prop) : p ∆ q = Xor' p q :=
  rfl
#align symm_diff_eq_xor symmDiff_eq_Xor'

@[simp]
theorem bihimp_iff_iff {p q : Prop} : p ⇔ q ↔ (p ↔ q) :=
  (iff_iff_implies_and_implies _ _).symm.trans Iff.comm
#align bihimp_iff_iff bihimp_iff_iff

@[simp]
theorem Bool.symmDiff_eq_xor : ∀ p q : Bool, p ∆ q = xor p q := by decide
                                                                   -- 🎉 no goals
#align bool.symm_diff_eq_bxor Bool.symmDiff_eq_xor

section GeneralizedCoheytingAlgebra

variable [GeneralizedCoheytingAlgebra α] (a b c d : α)

@[simp]
theorem toDual_symmDiff : toDual (a ∆ b) = toDual a ⇔ toDual b :=
  rfl
#align to_dual_symm_diff toDual_symmDiff

@[simp]
theorem ofDual_bihimp (a b : αᵒᵈ) : ofDual (a ⇔ b) = ofDual a ∆ ofDual b :=
  rfl
#align of_dual_bihimp ofDual_bihimp

theorem symmDiff_comm : a ∆ b = b ∆ a := by simp only [symmDiff, sup_comm]
                                            -- 🎉 no goals
#align symm_diff_comm symmDiff_comm

instance symmDiff_isCommutative : IsCommutative α (· ∆ ·) :=
  ⟨symmDiff_comm⟩
#align symm_diff_is_comm symmDiff_isCommutative

@[simp]
theorem symmDiff_self : a ∆ a = ⊥ := by rw [symmDiff, sup_idem, sdiff_self]
                                        -- 🎉 no goals
#align symm_diff_self symmDiff_self

@[simp]
theorem symmDiff_bot : a ∆ ⊥ = a := by rw [symmDiff, sdiff_bot, bot_sdiff, sup_bot_eq]
                                       -- 🎉 no goals
#align symm_diff_bot symmDiff_bot

@[simp]
theorem bot_symmDiff : ⊥ ∆ a = a := by rw [symmDiff_comm, symmDiff_bot]
                                       -- 🎉 no goals
#align bot_symm_diff bot_symmDiff

@[simp]
theorem symmDiff_eq_bot {a b : α} : a ∆ b = ⊥ ↔ a = b := by
  simp_rw [symmDiff, sup_eq_bot_iff, sdiff_eq_bot_iff, le_antisymm_iff]
  -- 🎉 no goals
#align symm_diff_eq_bot symmDiff_eq_bot

theorem symmDiff_of_le {a b : α} (h : a ≤ b) : a ∆ b = b \ a := by
  rw [symmDiff, sdiff_eq_bot_iff.2 h, bot_sup_eq]
  -- 🎉 no goals
#align symm_diff_of_le symmDiff_of_le

theorem symmDiff_of_ge {a b : α} (h : b ≤ a) : a ∆ b = a \ b := by
  rw [symmDiff, sdiff_eq_bot_iff.2 h, sup_bot_eq]
  -- 🎉 no goals
#align symm_diff_of_ge symmDiff_of_ge

theorem symmDiff_le {a b c : α} (ha : a ≤ b ⊔ c) (hb : b ≤ a ⊔ c) : a ∆ b ≤ c :=
  sup_le (sdiff_le_iff.2 ha) <| sdiff_le_iff.2 hb
#align symm_diff_le symmDiff_le

theorem symmDiff_le_iff {a b c : α} : a ∆ b ≤ c ↔ a ≤ b ⊔ c ∧ b ≤ a ⊔ c := by
  simp_rw [symmDiff, sup_le_iff, sdiff_le_iff]
  -- 🎉 no goals
#align symm_diff_le_iff symmDiff_le_iff

@[simp]
theorem symmDiff_le_sup {a b : α} : a ∆ b ≤ a ⊔ b :=
  sup_le_sup sdiff_le sdiff_le
#align symm_diff_le_sup symmDiff_le_sup

theorem symmDiff_eq_sup_sdiff_inf : a ∆ b = (a ⊔ b) \ (a ⊓ b) := by simp [sup_sdiff, symmDiff]
                                                                    -- 🎉 no goals
#align symm_diff_eq_sup_sdiff_inf symmDiff_eq_sup_sdiff_inf

theorem Disjoint.symmDiff_eq_sup {a b : α} (h : Disjoint a b) : a ∆ b = a ⊔ b := by
  rw [symmDiff, h.sdiff_eq_left, h.sdiff_eq_right]
  -- 🎉 no goals
#align disjoint.symm_diff_eq_sup Disjoint.symmDiff_eq_sup

theorem symmDiff_sdiff : a ∆ b \ c = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) := by
  rw [symmDiff, sup_sdiff_distrib, sdiff_sdiff_left, sdiff_sdiff_left]
  -- 🎉 no goals
#align symm_diff_sdiff symmDiff_sdiff

@[simp]
theorem symmDiff_sdiff_inf : a ∆ b \ (a ⊓ b) = a ∆ b := by
  rw [symmDiff_sdiff]
  -- ⊢ a \ (b ⊔ a ⊓ b) ⊔ b \ (a ⊔ a ⊓ b) = a ∆ b
  simp [symmDiff]
  -- 🎉 no goals
#align symm_diff_sdiff_inf symmDiff_sdiff_inf

@[simp]
theorem symmDiff_sdiff_eq_sup : a ∆ (b \ a) = a ⊔ b := by
  rw [symmDiff, sdiff_idem]
  -- ⊢ a \ (b \ a) ⊔ b \ a = a ⊔ b
  exact
    le_antisymm (sup_le_sup sdiff_le sdiff_le)
      (sup_le le_sdiff_sup <| le_sdiff_sup.trans <| sup_le le_sup_right le_sdiff_sup)
#align symm_diff_sdiff_eq_sup symmDiff_sdiff_eq_sup

@[simp]
theorem sdiff_symmDiff_eq_sup : (a \ b) ∆ b = a ⊔ b := by
  rw [symmDiff_comm, symmDiff_sdiff_eq_sup, sup_comm]
  -- 🎉 no goals
#align sdiff_symm_diff_eq_sup sdiff_symmDiff_eq_sup

@[simp]
theorem symmDiff_sup_inf : a ∆ b ⊔ a ⊓ b = a ⊔ b := by
  refine' le_antisymm (sup_le symmDiff_le_sup inf_le_sup) _
  -- ⊢ a ⊔ b ≤ a ∆ b ⊔ a ⊓ b
  rw [sup_inf_left, symmDiff]
  -- ⊢ a ⊔ b ≤ (a \ b ⊔ b \ a ⊔ a) ⊓ (a \ b ⊔ b \ a ⊔ b)
  refine' sup_le (le_inf le_sup_right _) (le_inf _ le_sup_right)
  -- ⊢ a ≤ a \ b ⊔ b \ a ⊔ b
  · rw [sup_right_comm]
    -- ⊢ a ≤ a \ b ⊔ b ⊔ b \ a
    exact le_sup_of_le_left le_sdiff_sup
    -- 🎉 no goals
  · rw [sup_assoc]
    -- ⊢ b ≤ a \ b ⊔ (b \ a ⊔ a)
    exact le_sup_of_le_right le_sdiff_sup
    -- 🎉 no goals
#align symm_diff_sup_inf symmDiff_sup_inf

@[simp]
theorem inf_sup_symmDiff : a ⊓ b ⊔ a ∆ b = a ⊔ b := by rw [sup_comm, symmDiff_sup_inf]
                                                       -- 🎉 no goals
#align inf_sup_symm_diff inf_sup_symmDiff

@[simp]
theorem symmDiff_symmDiff_inf : a ∆ b ∆ (a ⊓ b) = a ⊔ b := by
  rw [← symmDiff_sdiff_inf a, sdiff_symmDiff_eq_sup, symmDiff_sup_inf]
  -- 🎉 no goals
#align symm_diff_symm_diff_inf symmDiff_symmDiff_inf

@[simp]
theorem inf_symmDiff_symmDiff : (a ⊓ b) ∆ (a ∆ b) = a ⊔ b := by
  rw [symmDiff_comm, symmDiff_symmDiff_inf]
  -- 🎉 no goals
#align inf_symm_diff_symm_diff inf_symmDiff_symmDiff

theorem symmDiff_triangle : a ∆ c ≤ a ∆ b ⊔ b ∆ c := by
  refine' (sup_le_sup (sdiff_triangle a b c) <| sdiff_triangle _ b _).trans_eq _
  -- ⊢ a \ b ⊔ b \ c ⊔ (c \ b ⊔ b \ a) = a ∆ b ⊔ b ∆ c
  rw [@sup_comm _ _ (c \ b), sup_sup_sup_comm, symmDiff, symmDiff]
  -- 🎉 no goals
#align symm_diff_triangle symmDiff_triangle

end GeneralizedCoheytingAlgebra

section GeneralizedHeytingAlgebra

variable [GeneralizedHeytingAlgebra α] (a b c d : α)

@[simp]
theorem toDual_bihimp : toDual (a ⇔ b) = toDual a ∆ toDual b :=
  rfl
#align to_dual_bihimp toDual_bihimp

@[simp]
theorem ofDual_symmDiff (a b : αᵒᵈ) : ofDual (a ∆ b) = ofDual a ⇔ ofDual b :=
  rfl
#align of_dual_symm_diff ofDual_symmDiff

theorem bihimp_comm : a ⇔ b = b ⇔ a := by simp only [(· ⇔ ·), inf_comm]
                                          -- 🎉 no goals
#align bihimp_comm bihimp_comm

instance bihimp_isCommutative : IsCommutative α (· ⇔ ·) :=
  ⟨bihimp_comm⟩
#align bihimp_is_comm bihimp_isCommutative

@[simp]
theorem bihimp_self : a ⇔ a = ⊤ := by rw [bihimp, inf_idem, himp_self]
                                      -- 🎉 no goals
#align bihimp_self bihimp_self

@[simp]
theorem bihimp_top : a ⇔ ⊤ = a := by rw [bihimp, himp_top, top_himp, inf_top_eq]
                                     -- 🎉 no goals
#align bihimp_top bihimp_top

@[simp]
theorem top_bihimp : ⊤ ⇔ a = a := by rw [bihimp_comm, bihimp_top]
                                     -- 🎉 no goals
#align top_bihimp top_bihimp

@[simp]
theorem bihimp_eq_top {a b : α} : a ⇔ b = ⊤ ↔ a = b :=
  @symmDiff_eq_bot αᵒᵈ _ _ _
#align bihimp_eq_top bihimp_eq_top

theorem bihimp_of_le {a b : α} (h : a ≤ b) : a ⇔ b = b ⇨ a := by
  rw [bihimp, himp_eq_top_iff.2 h, inf_top_eq]
  -- 🎉 no goals
#align bihimp_of_le bihimp_of_le

theorem bihimp_of_ge {a b : α} (h : b ≤ a) : a ⇔ b = a ⇨ b := by
  rw [bihimp, himp_eq_top_iff.2 h, top_inf_eq]
  -- 🎉 no goals
#align bihimp_of_ge bihimp_of_ge

theorem le_bihimp {a b c : α} (hb : a ⊓ b ≤ c) (hc : a ⊓ c ≤ b) : a ≤ b ⇔ c :=
  le_inf (le_himp_iff.2 hc) <| le_himp_iff.2 hb
#align le_bihimp le_bihimp

theorem le_bihimp_iff {a b c : α} : a ≤ b ⇔ c ↔ a ⊓ b ≤ c ∧ a ⊓ c ≤ b := by
  simp_rw [bihimp, le_inf_iff, le_himp_iff, and_comm]
  -- 🎉 no goals
#align le_bihimp_iff le_bihimp_iff

@[simp]
theorem inf_le_bihimp {a b : α} : a ⊓ b ≤ a ⇔ b :=
  inf_le_inf le_himp le_himp
#align inf_le_bihimp inf_le_bihimp

theorem bihimp_eq_inf_himp_inf : a ⇔ b = a ⊔ b ⇨ a ⊓ b := by simp [himp_inf_distrib, bihimp]
                                                             -- 🎉 no goals
#align bihimp_eq_inf_himp_inf bihimp_eq_inf_himp_inf

theorem Codisjoint.bihimp_eq_inf {a b : α} (h : Codisjoint a b) : a ⇔ b = a ⊓ b := by
  rw [bihimp, h.himp_eq_left, h.himp_eq_right]
  -- 🎉 no goals
#align codisjoint.bihimp_eq_inf Codisjoint.bihimp_eq_inf

theorem himp_bihimp : a ⇨ b ⇔ c = (a ⊓ c ⇨ b) ⊓ (a ⊓ b ⇨ c) := by
  rw [bihimp, himp_inf_distrib, himp_himp, himp_himp]
  -- 🎉 no goals
#align himp_bihimp himp_bihimp

@[simp]
theorem sup_himp_bihimp : a ⊔ b ⇨ a ⇔ b = a ⇔ b := by
  rw [himp_bihimp]
  -- ⊢ ((a ⊔ b) ⊓ b ⇨ a) ⊓ ((a ⊔ b) ⊓ a ⇨ b) = a ⇔ b
  simp [bihimp]
  -- 🎉 no goals
#align sup_himp_bihimp sup_himp_bihimp

@[simp]
theorem bihimp_himp_eq_inf : a ⇔ (a ⇨ b) = a ⊓ b :=
  @symmDiff_sdiff_eq_sup αᵒᵈ _ _ _
#align bihimp_himp_eq_inf bihimp_himp_eq_inf

@[simp]
theorem himp_bihimp_eq_inf : (b ⇨ a) ⇔ b = a ⊓ b :=
  @sdiff_symmDiff_eq_sup αᵒᵈ _ _ _
#align himp_bihimp_eq_inf himp_bihimp_eq_inf

@[simp]
theorem bihimp_inf_sup : a ⇔ b ⊓ (a ⊔ b) = a ⊓ b :=
  @symmDiff_sup_inf αᵒᵈ _ _ _
#align bihimp_inf_sup bihimp_inf_sup

@[simp]
theorem sup_inf_bihimp : (a ⊔ b) ⊓ a ⇔ b = a ⊓ b :=
  @inf_sup_symmDiff αᵒᵈ _ _ _
#align sup_inf_bihimp sup_inf_bihimp

@[simp]
theorem bihimp_bihimp_sup : a ⇔ b ⇔ (a ⊔ b) = a ⊓ b :=
  @symmDiff_symmDiff_inf αᵒᵈ _ _ _
#align bihimp_bihimp_sup bihimp_bihimp_sup

@[simp]
theorem sup_bihimp_bihimp : (a ⊔ b) ⇔ (a ⇔ b) = a ⊓ b :=
  @inf_symmDiff_symmDiff αᵒᵈ _ _ _
#align sup_bihimp_bihimp sup_bihimp_bihimp

theorem bihimp_triangle : a ⇔ b ⊓ b ⇔ c ≤ a ⇔ c :=
  @symmDiff_triangle αᵒᵈ _ _ _ _
#align bihimp_triangle bihimp_triangle

end GeneralizedHeytingAlgebra

section CoheytingAlgebra

variable [CoheytingAlgebra α] (a : α)

@[simp]
theorem symmDiff_top' : a ∆ ⊤ = ￢a := by simp [symmDiff]
                                         -- 🎉 no goals
#align symm_diff_top' symmDiff_top'

@[simp]
theorem top_symmDiff' : ⊤ ∆ a = ￢a := by simp [symmDiff]
                                         -- 🎉 no goals
#align top_symm_diff' top_symmDiff'

@[simp]
theorem hnot_symmDiff_self : (￢a) ∆ a = ⊤ := by
  rw [eq_top_iff, symmDiff, hnot_sdiff, sup_sdiff_self]
  -- ⊢ ⊤ ≤ ￢a ⊔ a
  exact Codisjoint.top_le codisjoint_hnot_left
  -- 🎉 no goals
#align hnot_symm_diff_self hnot_symmDiff_self

@[simp]
theorem symmDiff_hnot_self : a ∆ (￢a) = ⊤ := by rw [symmDiff_comm, hnot_symmDiff_self]
                                                -- 🎉 no goals
#align symm_diff_hnot_self symmDiff_hnot_self

theorem IsCompl.symmDiff_eq_top {a b : α} (h : IsCompl a b) : a ∆ b = ⊤ := by
  rw [h.eq_hnot, hnot_symmDiff_self]
  -- 🎉 no goals
#align is_compl.symm_diff_eq_top IsCompl.symmDiff_eq_top

end CoheytingAlgebra

section HeytingAlgebra

variable [HeytingAlgebra α] (a : α)

@[simp]
theorem bihimp_bot : a ⇔ ⊥ = aᶜ := by simp [bihimp]
                                      -- 🎉 no goals
#align bihimp_bot bihimp_bot

@[simp]
theorem bot_bihimp : ⊥ ⇔ a = aᶜ := by simp [bihimp]
                                      -- 🎉 no goals
#align bot_bihimp bot_bihimp

@[simp]
theorem compl_bihimp_self : aᶜ ⇔ a = ⊥ :=
  @hnot_symmDiff_self αᵒᵈ _ _
#align compl_bihimp_self compl_bihimp_self

@[simp]
theorem bihimp_hnot_self : a ⇔ aᶜ = ⊥ :=
  @symmDiff_hnot_self αᵒᵈ _ _
#align bihimp_hnot_self bihimp_hnot_self

theorem IsCompl.bihimp_eq_bot {a b : α} (h : IsCompl a b) : a ⇔ b = ⊥ := by
  rw [h.eq_compl, compl_bihimp_self]
  -- 🎉 no goals
#align is_compl.bihimp_eq_bot IsCompl.bihimp_eq_bot

end HeytingAlgebra

section GeneralizedBooleanAlgebra

variable [GeneralizedBooleanAlgebra α] (a b c d : α)

@[simp]
theorem sup_sdiff_symmDiff : (a ⊔ b) \ a ∆ b = a ⊓ b :=
  sdiff_eq_symm inf_le_sup (by rw [symmDiff_eq_sup_sdiff_inf])
                               -- 🎉 no goals
#align sup_sdiff_symm_diff sup_sdiff_symmDiff

theorem disjoint_symmDiff_inf : Disjoint (a ∆ b) (a ⊓ b) := by
  rw [symmDiff_eq_sup_sdiff_inf]
  -- ⊢ Disjoint ((a ⊔ b) \ (a ⊓ b)) (a ⊓ b)
  exact disjoint_sdiff_self_left
  -- 🎉 no goals
#align disjoint_symm_diff_inf disjoint_symmDiff_inf

theorem inf_symmDiff_distrib_left : a ⊓ b ∆ c = (a ⊓ b) ∆ (a ⊓ c) := by
  rw [symmDiff_eq_sup_sdiff_inf, inf_sdiff_distrib_left, inf_sup_left, inf_inf_distrib_left,
    symmDiff_eq_sup_sdiff_inf]
#align inf_symm_diff_distrib_left inf_symmDiff_distrib_left

theorem inf_symmDiff_distrib_right : a ∆ b ⊓ c = (a ⊓ c) ∆ (b ⊓ c) := by
  simp_rw [@inf_comm _ _ _ c, inf_symmDiff_distrib_left]
  -- 🎉 no goals
#align inf_symm_diff_distrib_right inf_symmDiff_distrib_right

theorem sdiff_symmDiff : c \ a ∆ b = c ⊓ a ⊓ b ⊔ c \ a ⊓ c \ b := by
  simp only [(· ∆ ·), sdiff_sdiff_sup_sdiff']
  -- 🎉 no goals
#align sdiff_symm_diff sdiff_symmDiff

theorem sdiff_symmDiff' : c \ a ∆ b = c ⊓ a ⊓ b ⊔ c \ (a ⊔ b) := by
  rw [sdiff_symmDiff, sdiff_sup, sup_comm]
  -- 🎉 no goals
#align sdiff_symm_diff' sdiff_symmDiff'

@[simp]
theorem symmDiff_sdiff_left : a ∆ b \ a = b \ a := by
  rw [symmDiff_def, sup_sdiff, sdiff_idem, sdiff_sdiff_self, bot_sup_eq]
  -- 🎉 no goals
#align symm_diff_sdiff_left symmDiff_sdiff_left

@[simp]
theorem symmDiff_sdiff_right : a ∆ b \ b = a \ b := by rw [symmDiff_comm, symmDiff_sdiff_left]
                                                       -- 🎉 no goals
#align symm_diff_sdiff_right symmDiff_sdiff_right

@[simp]
theorem sdiff_symmDiff_left : a \ a ∆ b = a ⊓ b := by simp [sdiff_symmDiff]
                                                      -- 🎉 no goals
#align sdiff_symm_diff_left sdiff_symmDiff_left

@[simp]
theorem sdiff_symmDiff_right : b \ a ∆ b = a ⊓ b := by
  rw [symmDiff_comm, inf_comm, sdiff_symmDiff_left]
  -- 🎉 no goals
#align sdiff_symm_diff_right sdiff_symmDiff_right

theorem symmDiff_eq_sup : a ∆ b = a ⊔ b ↔ Disjoint a b := by
  refine' ⟨fun h => _, Disjoint.symmDiff_eq_sup⟩
  -- ⊢ Disjoint a b
  rw [symmDiff_eq_sup_sdiff_inf, sdiff_eq_self_iff_disjoint] at h
  -- ⊢ Disjoint a b
  exact h.of_disjoint_inf_of_le le_sup_left
  -- 🎉 no goals
#align symm_diff_eq_sup symmDiff_eq_sup

@[simp]
theorem le_symmDiff_iff_left : a ≤ a ∆ b ↔ Disjoint a b := by
  refine' ⟨fun h => _, fun h => h.symmDiff_eq_sup.symm ▸ le_sup_left⟩
  -- ⊢ Disjoint a b
  rw [symmDiff_eq_sup_sdiff_inf] at h
  -- ⊢ Disjoint a b
  exact disjoint_iff_inf_le.mpr (le_sdiff_iff.1 <| inf_le_of_left_le h).le
  -- 🎉 no goals
#align le_symm_diff_iff_left le_symmDiff_iff_left

@[simp]
theorem le_symmDiff_iff_right : b ≤ a ∆ b ↔ Disjoint a b := by
  rw [symmDiff_comm, le_symmDiff_iff_left, disjoint_comm]
  -- 🎉 no goals
#align le_symm_diff_iff_right le_symmDiff_iff_right

theorem symmDiff_symmDiff_left :
    a ∆ b ∆ c = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ c \ (a ⊔ b) ⊔ a ⊓ b ⊓ c :=
  calc
    a ∆ b ∆ c = a ∆ b \ c ⊔ c \ a ∆ b := symmDiff_def _ _
    _ = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ (c \ (a ⊔ b) ⊔ c ⊓ a ⊓ b) := by
        { rw [sdiff_symmDiff', @sup_comm _ _ (c ⊓ a ⊓ b), symmDiff_sdiff] }
        -- 🎉 no goals
    _ = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ c \ (a ⊔ b) ⊔ a ⊓ b ⊓ c := by ac_rfl
                                                                  -- 🎉 no goals
#align symm_diff_symm_diff_left symmDiff_symmDiff_left

theorem symmDiff_symmDiff_right :
    a ∆ (b ∆ c) = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ c \ (a ⊔ b) ⊔ a ⊓ b ⊓ c :=
  calc
    a ∆ (b ∆ c) = a \ b ∆ c ⊔ b ∆ c \ a := symmDiff_def _ _
    _ = a \ (b ⊔ c) ⊔ a ⊓ b ⊓ c ⊔ (b \ (c ⊔ a) ⊔ c \ (b ⊔ a)) := by
        { rw [sdiff_symmDiff', @sup_comm _ _ (a ⊓ b ⊓ c), symmDiff_sdiff] }
        -- 🎉 no goals
    _ = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) ⊔ c \ (a ⊔ b) ⊔ a ⊓ b ⊓ c := by ac_rfl
                                                                  -- 🎉 no goals
#align symm_diff_symm_diff_right symmDiff_symmDiff_right

theorem symmDiff_assoc : a ∆ b ∆ c = a ∆ (b ∆ c) := by
  rw [symmDiff_symmDiff_left, symmDiff_symmDiff_right]
  -- 🎉 no goals
#align symm_diff_assoc symmDiff_assoc

instance symmDiff_isAssociative : IsAssociative α (· ∆ ·) :=
  ⟨symmDiff_assoc⟩
#align symm_diff_is_assoc symmDiff_isAssociative

theorem symmDiff_left_comm : a ∆ (b ∆ c) = b ∆ (a ∆ c) := by
  simp_rw [← symmDiff_assoc, symmDiff_comm]
  -- 🎉 no goals
#align symm_diff_left_comm symmDiff_left_comm

theorem symmDiff_right_comm : a ∆ b ∆ c = a ∆ c ∆ b := by simp_rw [symmDiff_assoc, symmDiff_comm]
                                                          -- 🎉 no goals
#align symm_diff_right_comm symmDiff_right_comm

theorem symmDiff_symmDiff_symmDiff_comm : a ∆ b ∆ (c ∆ d) = a ∆ c ∆ (b ∆ d) := by
  simp_rw [symmDiff_assoc, symmDiff_left_comm]
  -- 🎉 no goals
#align symm_diff_symm_diff_symm_diff_comm symmDiff_symmDiff_symmDiff_comm

@[simp]
theorem symmDiff_symmDiff_cancel_left : a ∆ (a ∆ b) = b := by simp [← symmDiff_assoc]
                                                              -- 🎉 no goals
#align symm_diff_symm_diff_cancel_left symmDiff_symmDiff_cancel_left

@[simp]
theorem symmDiff_symmDiff_cancel_right : b ∆ a ∆ a = b := by simp [symmDiff_assoc]
                                                             -- 🎉 no goals
#align symm_diff_symm_diff_cancel_right symmDiff_symmDiff_cancel_right

@[simp]
theorem symmDiff_symmDiff_self' : a ∆ b ∆ a = b := by
  rw [symmDiff_comm, symmDiff_symmDiff_cancel_left]
  -- 🎉 no goals
#align symm_diff_symm_diff_self' symmDiff_symmDiff_self'

theorem symmDiff_left_involutive (a : α) : Involutive (· ∆ a) :=
  symmDiff_symmDiff_cancel_right _
#align symm_diff_left_involutive symmDiff_left_involutive

theorem symmDiff_right_involutive (a : α) : Involutive ((· ∆ ·) a) :=
  symmDiff_symmDiff_cancel_left _
#align symm_diff_right_involutive symmDiff_right_involutive

theorem symmDiff_left_injective (a : α) : Injective (· ∆ a) :=
  Function.Involutive.injective (symmDiff_left_involutive a)
#align symm_diff_left_injective symmDiff_left_injective

theorem symmDiff_right_injective (a : α) : Injective ((· ∆ ·) a) :=
  Function.Involutive.injective (symmDiff_right_involutive _)
#align symm_diff_right_injective symmDiff_right_injective

theorem symmDiff_left_surjective (a : α) : Surjective (· ∆ a) :=
  Function.Involutive.surjective (symmDiff_left_involutive _)
#align symm_diff_left_surjective symmDiff_left_surjective

theorem symmDiff_right_surjective (a : α) : Surjective ((· ∆ ·) a) :=
  Function.Involutive.surjective (symmDiff_right_involutive _)
#align symm_diff_right_surjective symmDiff_right_surjective

variable {a b c}

@[simp]
theorem symmDiff_left_inj : a ∆ b = c ∆ b ↔ a = c :=
  (symmDiff_left_injective _).eq_iff
#align symm_diff_left_inj symmDiff_left_inj

@[simp]
theorem symmDiff_right_inj : a ∆ b = a ∆ c ↔ b = c :=
  (symmDiff_right_injective _).eq_iff
#align symm_diff_right_inj symmDiff_right_inj

@[simp]
theorem symmDiff_eq_left : a ∆ b = a ↔ b = ⊥ :=
  calc
    a ∆ b = a ↔ a ∆ b = a ∆ ⊥ := by rw [symmDiff_bot]
                                    -- 🎉 no goals
    _ ↔ b = ⊥ := by rw [symmDiff_right_inj]
                    -- 🎉 no goals
#align symm_diff_eq_left symmDiff_eq_left

@[simp]
theorem symmDiff_eq_right : a ∆ b = b ↔ a = ⊥ := by rw [symmDiff_comm, symmDiff_eq_left]
                                                    -- 🎉 no goals
#align symm_diff_eq_right symmDiff_eq_right

protected theorem Disjoint.symmDiff_left (ha : Disjoint a c) (hb : Disjoint b c) :
    Disjoint (a ∆ b) c := by
  rw [symmDiff_eq_sup_sdiff_inf]
  -- ⊢ Disjoint ((a ⊔ b) \ (a ⊓ b)) c
  exact (ha.sup_left hb).disjoint_sdiff_left
  -- 🎉 no goals
#align disjoint.symm_diff_left Disjoint.symmDiff_left

protected theorem Disjoint.symmDiff_right (ha : Disjoint a b) (hb : Disjoint a c) :
    Disjoint a (b ∆ c) :=
  (ha.symm.symmDiff_left hb.symm).symm
#align disjoint.symm_diff_right Disjoint.symmDiff_right

theorem symmDiff_eq_iff_sdiff_eq (ha : a ≤ c) : a ∆ b = c ↔ c \ a = b := by
  rw [← symmDiff_of_le ha]
  -- ⊢ a ∆ b = c ↔ a ∆ c = b
  exact ((symmDiff_right_involutive a).toPerm _).apply_eq_iff_eq_symm_apply.trans eq_comm
  -- 🎉 no goals
#align symm_diff_eq_iff_sdiff_eq symmDiff_eq_iff_sdiff_eq

end GeneralizedBooleanAlgebra

section BooleanAlgebra

variable [BooleanAlgebra α] (a b c d : α)

/- `CogeneralizedBooleanAlgebra` isn't actually a typeclass, but the lemmas in here are dual to
the `GeneralizedBooleanAlgebra` ones -/
section CogeneralizedBooleanAlgebra

@[simp]
theorem inf_himp_bihimp : a ⇔ b ⇨ a ⊓ b = a ⊔ b :=
  @sup_sdiff_symmDiff αᵒᵈ _ _ _
#align inf_himp_bihimp inf_himp_bihimp

theorem codisjoint_bihimp_sup : Codisjoint (a ⇔ b) (a ⊔ b) :=
  @disjoint_symmDiff_inf αᵒᵈ _ _ _
#align codisjoint_bihimp_sup codisjoint_bihimp_sup

@[simp]
theorem himp_bihimp_left : a ⇨ a ⇔ b = a ⇨ b :=
  @symmDiff_sdiff_left αᵒᵈ _ _ _
#align himp_bihimp_left himp_bihimp_left

@[simp]
theorem himp_bihimp_right : b ⇨ a ⇔ b = b ⇨ a :=
  @symmDiff_sdiff_right αᵒᵈ _ _ _
#align himp_bihimp_right himp_bihimp_right

@[simp]
theorem bihimp_himp_left : a ⇔ b ⇨ a = a ⊔ b :=
  @sdiff_symmDiff_left αᵒᵈ _ _ _
#align bihimp_himp_left bihimp_himp_left

@[simp]
theorem bihimp_himp_right : a ⇔ b ⇨ b = a ⊔ b :=
  @sdiff_symmDiff_right αᵒᵈ _ _ _
#align bihimp_himp_right bihimp_himp_right

@[simp]
theorem bihimp_eq_inf : a ⇔ b = a ⊓ b ↔ Codisjoint a b :=
  @symmDiff_eq_sup αᵒᵈ _ _ _
#align bihimp_eq_inf bihimp_eq_inf

@[simp]
theorem bihimp_le_iff_left : a ⇔ b ≤ a ↔ Codisjoint a b :=
  @le_symmDiff_iff_left αᵒᵈ _ _ _
#align bihimp_le_iff_left bihimp_le_iff_left

@[simp]
theorem bihimp_le_iff_right : a ⇔ b ≤ b ↔ Codisjoint a b :=
  @le_symmDiff_iff_right αᵒᵈ _ _ _
#align bihimp_le_iff_right bihimp_le_iff_right

theorem bihimp_assoc : a ⇔ b ⇔ c = a ⇔ (b ⇔ c) :=
  @symmDiff_assoc αᵒᵈ _ _ _ _
#align bihimp_assoc bihimp_assoc

instance bihimp_isAssociative : IsAssociative α (· ⇔ ·) :=
  ⟨bihimp_assoc⟩
#align bihimp_is_assoc bihimp_isAssociative

theorem bihimp_left_comm : a ⇔ (b ⇔ c) = b ⇔ (a ⇔ c) := by simp_rw [← bihimp_assoc, bihimp_comm]
                                                           -- 🎉 no goals
#align bihimp_left_comm bihimp_left_comm

theorem bihimp_right_comm : a ⇔ b ⇔ c = a ⇔ c ⇔ b := by simp_rw [bihimp_assoc, bihimp_comm]
                                                        -- 🎉 no goals
#align bihimp_right_comm bihimp_right_comm

theorem bihimp_bihimp_bihimp_comm : a ⇔ b ⇔ (c ⇔ d) = a ⇔ c ⇔ (b ⇔ d) := by
  simp_rw [bihimp_assoc, bihimp_left_comm]
  -- 🎉 no goals
#align bihimp_bihimp_bihimp_comm bihimp_bihimp_bihimp_comm

@[simp]
theorem bihimp_bihimp_cancel_left : a ⇔ (a ⇔ b) = b := by simp [← bihimp_assoc]
                                                          -- 🎉 no goals
#align bihimp_bihimp_cancel_left bihimp_bihimp_cancel_left

@[simp]
theorem bihimp_bihimp_cancel_right : b ⇔ a ⇔ a = b := by simp [bihimp_assoc]
                                                         -- 🎉 no goals
#align bihimp_bihimp_cancel_right bihimp_bihimp_cancel_right

@[simp]
theorem bihimp_bihimp_self : a ⇔ b ⇔ a = b := by rw [bihimp_comm, bihimp_bihimp_cancel_left]
                                                 -- 🎉 no goals
#align bihimp_bihimp_self bihimp_bihimp_self

theorem bihimp_left_involutive (a : α) : Involutive (· ⇔ a) :=
  bihimp_bihimp_cancel_right _
#align bihimp_left_involutive bihimp_left_involutive

theorem bihimp_right_involutive (a : α) : Involutive ((· ⇔ ·) a) :=
  bihimp_bihimp_cancel_left _
#align bihimp_right_involutive bihimp_right_involutive

theorem bihimp_left_injective (a : α) : Injective (· ⇔ a) :=
  @symmDiff_left_injective αᵒᵈ _ _
#align bihimp_left_injective bihimp_left_injective

theorem bihimp_right_injective (a : α) : Injective ((· ⇔ ·) a) :=
  @symmDiff_right_injective αᵒᵈ _ _
#align bihimp_right_injective bihimp_right_injective

theorem bihimp_left_surjective (a : α) : Surjective (· ⇔ a) :=
  @symmDiff_left_surjective αᵒᵈ _ _
#align bihimp_left_surjective bihimp_left_surjective

theorem bihimp_right_surjective (a : α) : Surjective ((· ⇔ ·) a) :=
  @symmDiff_right_surjective αᵒᵈ _ _
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
  @symmDiff_eq_left αᵒᵈ _ _ _
#align bihimp_eq_left bihimp_eq_left

@[simp]
theorem bihimp_eq_right : a ⇔ b = b ↔ a = ⊤ :=
  @symmDiff_eq_right αᵒᵈ _ _ _
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

theorem symmDiff_eq : a ∆ b = a ⊓ bᶜ ⊔ b ⊓ aᶜ := by simp only [(· ∆ ·), sdiff_eq]
                                                    -- 🎉 no goals
#align symm_diff_eq symmDiff_eq

theorem bihimp_eq : a ⇔ b = (a ⊔ bᶜ) ⊓ (b ⊔ aᶜ) := by simp only [(· ⇔ ·), himp_eq]
                                                      -- 🎉 no goals
#align bihimp_eq bihimp_eq

theorem symmDiff_eq' : a ∆ b = (a ⊔ b) ⊓ (aᶜ ⊔ bᶜ) := by
  rw [symmDiff_eq_sup_sdiff_inf, sdiff_eq, compl_inf]
  -- 🎉 no goals
#align symm_diff_eq' symmDiff_eq'

theorem bihimp_eq' : a ⇔ b = a ⊓ b ⊔ aᶜ ⊓ bᶜ :=
  @symmDiff_eq' αᵒᵈ _ _ _
#align bihimp_eq' bihimp_eq'

theorem symmDiff_top : a ∆ ⊤ = aᶜ :=
  symmDiff_top' _
#align symm_diff_top symmDiff_top

theorem top_symmDiff : ⊤ ∆ a = aᶜ :=
  top_symmDiff' _
#align top_symm_diff top_symmDiff

@[simp]
theorem compl_symmDiff : (a ∆ b)ᶜ = a ⇔ b := by
  simp_rw [symmDiff, compl_sup_distrib, compl_sdiff, bihimp, inf_comm]
  -- 🎉 no goals
#align compl_symm_diff compl_symmDiff

@[simp]
theorem compl_bihimp : (a ⇔ b)ᶜ = a ∆ b :=
  @compl_symmDiff αᵒᵈ _ _ _
#align compl_bihimp compl_bihimp

@[simp]
theorem compl_symmDiff_compl : aᶜ ∆ bᶜ = a ∆ b :=
  sup_comm.trans <| by simp_rw [compl_sdiff_compl, sdiff_eq, symmDiff_eq]
                       -- 🎉 no goals
#align compl_symm_diff_compl compl_symmDiff_compl

@[simp]
theorem compl_bihimp_compl : aᶜ ⇔ bᶜ = a ⇔ b :=
  @compl_symmDiff_compl αᵒᵈ _ _ _
#align compl_bihimp_compl compl_bihimp_compl

@[simp]
theorem symmDiff_eq_top : a ∆ b = ⊤ ↔ IsCompl a b := by
  rw [symmDiff_eq', ← compl_inf, inf_eq_top_iff, compl_eq_top, isCompl_iff, disjoint_iff,
    codisjoint_iff, and_comm]
#align symm_diff_eq_top symmDiff_eq_top

@[simp]
theorem bihimp_eq_bot : a ⇔ b = ⊥ ↔ IsCompl a b := by
  rw [bihimp_eq', ← compl_sup, sup_eq_bot_iff, compl_eq_bot, isCompl_iff, disjoint_iff,
    codisjoint_iff]
#align bihimp_eq_bot bihimp_eq_bot

@[simp]
theorem compl_symmDiff_self : aᶜ ∆ a = ⊤ :=
  hnot_symmDiff_self _
#align compl_symm_diff_self compl_symmDiff_self

@[simp]
theorem symmDiff_compl_self : a ∆ aᶜ = ⊤ :=
  symmDiff_hnot_self _
#align symm_diff_compl_self symmDiff_compl_self

theorem symmDiff_symmDiff_right' :
    a ∆ (b ∆ c) = a ⊓ b ⊓ c ⊔ a ⊓ bᶜ ⊓ cᶜ ⊔ aᶜ ⊓ b ⊓ cᶜ ⊔ aᶜ ⊓ bᶜ ⊓ c :=
  calc
    a ∆ (b ∆ c) = a ⊓ (b ⊓ c ⊔ bᶜ ⊓ cᶜ) ⊔ (b ⊓ cᶜ ⊔ c ⊓ bᶜ) ⊓ aᶜ := by
        { rw [symmDiff_eq, compl_symmDiff, bihimp_eq', symmDiff_eq] }
        -- 🎉 no goals
    _ = a ⊓ b ⊓ c ⊔ a ⊓ bᶜ ⊓ cᶜ ⊔ b ⊓ cᶜ ⊓ aᶜ ⊔ c ⊓ bᶜ ⊓ aᶜ := by
        { rw [inf_sup_left, inf_sup_right, ← sup_assoc, ← inf_assoc, ← inf_assoc] }
        -- 🎉 no goals
    _ = a ⊓ b ⊓ c ⊔ a ⊓ bᶜ ⊓ cᶜ ⊔ aᶜ ⊓ b ⊓ cᶜ ⊔ aᶜ ⊓ bᶜ ⊓ c := (by
      congr 1
      -- ⊢ a ⊓ b ⊓ c ⊔ a ⊓ bᶜ ⊓ cᶜ ⊔ b ⊓ cᶜ ⊓ aᶜ = a ⊓ b ⊓ c ⊔ a ⊓ bᶜ ⊓ cᶜ ⊔ aᶜ ⊓ b ⊓ cᶜ
      · congr 1
        -- ⊢ b ⊓ cᶜ ⊓ aᶜ = aᶜ ⊓ b ⊓ cᶜ
        rw [inf_comm, inf_assoc]
        -- 🎉 no goals
      · apply inf_left_right_swap)
        -- 🎉 no goals
#align symm_diff_symm_diff_right' symmDiff_symmDiff_right'

variable {a b c}

theorem Disjoint.le_symmDiff_sup_symmDiff_left (h : Disjoint a b) : c ≤ a ∆ c ⊔ b ∆ c := by
  trans c \ (a ⊓ b)
  -- ⊢ c ≤ c \ (a ⊓ b)
  · rw [h.eq_bot, sdiff_bot]
    -- 🎉 no goals
  · rw [sdiff_inf]
    -- ⊢ c \ a ⊔ c \ b ≤ a ∆ c ⊔ b ∆ c
    exact sup_le_sup le_sup_right le_sup_right
    -- 🎉 no goals
#align disjoint.le_symm_diff_sup_symm_diff_left Disjoint.le_symmDiff_sup_symmDiff_left

theorem Disjoint.le_symmDiff_sup_symmDiff_right (h : Disjoint b c) : a ≤ a ∆ b ⊔ a ∆ c := by
  simp_rw [symmDiff_comm a]
  -- ⊢ a ≤ b ∆ a ⊔ c ∆ a
  exact h.le_symmDiff_sup_symmDiff_left
  -- 🎉 no goals
#align disjoint.le_symm_diff_sup_symm_diff_right Disjoint.le_symmDiff_sup_symmDiff_right

theorem Codisjoint.bihimp_inf_bihimp_le_left (h : Codisjoint a b) : a ⇔ c ⊓ b ⇔ c ≤ c :=
  h.dual.le_symmDiff_sup_symmDiff_left
#align codisjoint.bihimp_inf_bihimp_le_left Codisjoint.bihimp_inf_bihimp_le_left

theorem Codisjoint.bihimp_inf_bihimp_le_right (h : Codisjoint b c) : a ⇔ b ⊓ a ⇔ c ≤ a :=
  h.dual.le_symmDiff_sup_symmDiff_right
#align codisjoint.bihimp_inf_bihimp_le_right Codisjoint.bihimp_inf_bihimp_le_right

end BooleanAlgebra

/-! ### Prod -/


section Prod

@[simp]
theorem symmDiff_fst [GeneralizedCoheytingAlgebra α] [GeneralizedCoheytingAlgebra β]
    (a b : α × β) : (a ∆ b).1 = a.1 ∆ b.1 :=
  rfl
#align symm_diff_fst symmDiff_fst

@[simp]
theorem symmDiff_snd [GeneralizedCoheytingAlgebra α] [GeneralizedCoheytingAlgebra β]
    (a b : α × β) : (a ∆ b).2 = a.2 ∆ b.2 :=
  rfl
#align symm_diff_snd symmDiff_snd

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

theorem symmDiff_def [∀ i, GeneralizedCoheytingAlgebra (π i)] (a b : ∀ i, π i) :
    a ∆ b = fun i => a i ∆ b i :=
  rfl
#align pi.symm_diff_def Pi.symmDiff_def

theorem bihimp_def [∀ i, GeneralizedHeytingAlgebra (π i)] (a b : ∀ i, π i) :
    a ⇔ b = fun i => a i ⇔ b i :=
  rfl
#align pi.bihimp_def Pi.bihimp_def

@[simp]
theorem symmDiff_apply [∀ i, GeneralizedCoheytingAlgebra (π i)] (a b : ∀ i, π i) (i : ι) :
    (a ∆ b) i = a i ∆ b i :=
  rfl
#align pi.symm_diff_apply Pi.symmDiff_apply

@[simp]
theorem bihimp_apply [∀ i, GeneralizedHeytingAlgebra (π i)] (a b : ∀ i, π i) (i : ι) :
    (a ⇔ b) i = a i ⇔ b i :=
  rfl
#align pi.bihimp_apply Pi.bihimp_apply

end Pi
