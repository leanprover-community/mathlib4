import Mathlib.Logic.Nontrivial.Basic
import Mathlib.Order.BoundedOrder
import Mathlib.Order.TypeTags
import Mathlib.Data.Option.NAry
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Lift
import Mathlib.Data.Option.Basic


variable {α β γ δ : Type*}

namespace WithBot

variable {a b : α}

@[simp, norm_cast]
theorem coe_inj : (a : WithBot α) = b ↔ a = b :=
  Option.some_inj

@[simp]
theorem bot_ne_coe : ⊥ ≠ (a : WithBot α) :=
  nofun

section LE

variable [LE α]

instance (priority := 10) le : LE (WithBot α) :=
  ⟨fun o₁ o₂ => ∀ a : α, o₁ = ↑a → ∃ b : α, o₂ = ↑b ∧ a ≤ b⟩

@[simp, norm_cast]
theorem coe_le_coe : (a : WithBot α) ≤ b ↔ a ≤ b := by
  simp [LE.le]

instance orderBot : OrderBot (WithBot α) where
  bot_le _ := fun _ h => Option.noConfusion h

theorem le_coe_iff : ∀ {x : WithBot α}, x ≤ b ↔ ∀ a : α, x = ↑a → a ≤ b
  | (b : α) => by simp
  | ⊥ => by simp

end LE

section LT

variable [LT α]

instance (priority := 10) lt : LT (WithBot α) :=
  ⟨fun o₁ o₂ : WithBot α => ∃ b : α, o₂ = ↑b ∧ ∀ a : α, o₁ = ↑a → a < b⟩

@[simp, norm_cast]
theorem coe_lt_coe : (a : WithBot α) < b ↔ a < b := by
  simp [LT.lt]

end LT

instance preorder [Preorder α] : Preorder (WithBot α) where
  le := (· ≤ ·)
  lt := (· < ·)
  lt_iff_le_not_le := sorry
  le_refl _ a ha := sorry
  le_trans _ _ _ h₁ h₂ a ha := sorry

end WithBot

namespace WithBot

open OrderDual

/--
error: mod_cast has type
  ∀ (z : α), ↑x < ↑z → ↑y ≤ ↑z : Prop
but is expected to have type
  ∀ (a : α), x < a → y ≤ a : Prop
-/
#guard_msgs in
lemma le_of_forall_lt_iff_le [LinearOrder α] [DenselyOrdered α]
    {x y : WithBot α} : (∀ z : α, x < z → y ≤ z) ↔ y ≤ x := by
  refine ⟨fun h ↦ ?_, fun h z x_z ↦ h.trans x_z.le⟩
  induction x with
  | bot => sorry
  | coe x =>
    rw [le_coe_iff]
    rintro y rfl
    exact le_of_forall_le_of_dense (by exact_mod_cast h)

end WithBot
