/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.GroupTheory.MonoidLocalization.Basic

/-!
# Ordered structures on localizations of commutative monoids

-/

open Function

namespace Localization

variable {α : Type*}

section OrderedCancelCommMonoid

variable [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α] {s : Submonoid α}
  {a₁ b₁ : α} {a₂ b₂ : s}

@[to_additive]
instance le : LE (Localization s) :=
  ⟨fun a b =>
    Localization.liftOn₂ a b (fun a₁ a₂ b₁ b₂ => ↑b₂ * a₁ ≤ a₂ * b₁)
      fun {a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂} hab hcd => propext <| by
        obtain ⟨e, he⟩ := r_iff_exists.1 hab
        obtain ⟨f, hf⟩ := r_iff_exists.1 hcd
        simp only [mul_right_inj] at he hf
        dsimp
        rw [← mul_le_mul_iff_right, mul_right_comm, ← hf, mul_right_comm, mul_right_comm (a₂ : α),
          mul_le_mul_iff_right, ← mul_le_mul_iff_left, mul_left_comm, he, mul_left_comm,
          mul_left_comm (b₂ : α), mul_le_mul_iff_left]⟩

@[to_additive]
instance lt : LT (Localization s) :=
  ⟨fun a b =>
    Localization.liftOn₂ a b (fun a₁ a₂ b₁ b₂ => ↑b₂ * a₁ < a₂ * b₁)
      fun {a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂} hab hcd => propext <| by
        obtain ⟨e, he⟩ := r_iff_exists.1 hab
        obtain ⟨f, hf⟩ := r_iff_exists.1 hcd
        simp only [mul_right_inj] at he hf
        dsimp
        rw [← mul_lt_mul_iff_right, mul_right_comm, ← hf, mul_right_comm, mul_right_comm (a₂ : α),
          mul_lt_mul_iff_right, ← mul_lt_mul_iff_left, mul_left_comm, he, mul_left_comm,
          mul_left_comm (b₂ : α), mul_lt_mul_iff_left]⟩

@[to_additive]
theorem mk_le_mk : mk a₁ a₂ ≤ mk b₁ b₂ ↔ ↑b₂ * a₁ ≤ a₂ * b₁ :=
  Iff.rfl

@[to_additive]
theorem mk_lt_mk : mk a₁ a₂ < mk b₁ b₂ ↔ ↑b₂ * a₁ < a₂ * b₁ :=
  Iff.rfl

-- declaring this separately to the instance below makes things faster
@[to_additive]
instance partialOrder : PartialOrder (Localization s) where
  le_refl a := Localization.induction_on a fun _ => le_rfl
  le_trans a b c :=
    Localization.induction_on₃ a b c fun a b c hab hbc => by
      simp only [mk_le_mk] at hab hbc ⊢
      apply le_of_mul_le_mul_left' _
      · exact ↑b.2
      grw [mul_left_comm, hab]
      rwa [mul_left_comm, mul_left_comm (b.2 : α), mul_le_mul_iff_left]
  le_antisymm a b := by
    induction a using Localization.rec
    on_goal 1 =>
      induction b using Localization.rec
      · simp_rw [mk_le_mk, mk_eq_mk_iff, r_iff_exists]
        exact fun hab hba => ⟨1, by rw [hab.antisymm hba]⟩
    all_goals rfl
  lt_iff_le_not_ge a b := Localization.induction_on₂ a b fun _ _ => lt_iff_le_not_ge

@[to_additive]
instance isOrderedCancelMonoid : IsOrderedCancelMonoid (Localization s) where
  mul_le_mul_left := fun a b =>
    Localization.induction_on₂ a b fun a b hab c =>
      Localization.induction_on c fun c => by
        simp only [mk_mul, mk_le_mk, Submonoid.coe_mul, mul_mul_mul_comm _ _ c.1] at hab ⊢
        exact mul_le_mul_left' hab _
  le_of_mul_le_mul_left := fun a b c =>
    Localization.induction_on₃ a b c fun a b c hab => by
      simp only [mk_mul, mk_le_mk, Submonoid.coe_mul, mul_mul_mul_comm _ _ a.1] at hab ⊢
      exact le_of_mul_le_mul_left' hab

@[to_additive]
instance decidableLE [DecidableLE α] : DecidableLE (Localization s) := fun a b =>
  Localization.recOnSubsingleton₂ a b fun _ _ _ _ => decidable_of_iff' _ mk_le_mk

@[to_additive]
instance decidableLT [DecidableLT α] : DecidableLT (Localization s) := fun a b =>
  Localization.recOnSubsingleton₂ a b fun _ _ _ _ => decidable_of_iff' _ mk_lt_mk

/-- An ordered cancellative monoid injects into its localization by sending `a` to `a / b`. -/
@[to_additive (attr := simps!) /-- An ordered cancellative monoid injects into its localization by
sending `a` to `a - b`. -/]
def mkOrderEmbedding (b : s) : α ↪o Localization s where
  toFun a := mk a b
  inj' := mk_left_injective _
  map_rel_iff' {a b} := by simp [mk_le_mk]

end OrderedCancelCommMonoid

@[to_additive]
instance [CommMonoid α] [LinearOrder α] [IsOrderedCancelMonoid α] {s : Submonoid α} :
    LinearOrder (Localization s) :=
  { le_total := fun a b =>
      Localization.induction_on₂ a b fun _ _ => by
        simp_rw [mk_le_mk]
        exact le_total _ _
    toDecidableLE := Localization.decidableLE
    toDecidableLT := Localization.decidableLT
    toDecidableEq := Localization.decidableEq }

end Localization
