/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Minchao Wu
-/
import Mathlib.Data.Sigma.Lex
import Mathlib.Order.BoundedOrder
import Mathlib.Mathport.Notation
import Init.NotationExtra

#align_import data.psigma.order from "leanprover-community/mathlib"@"62a5626868683c104774de8d85b9855234ac807c"

/-!
# Lexicographic order on a sigma type
This file defines the lexicographic order on `Σₗ' i, α i`. `a` is less than `b` if its summand is
strictly less than the summand of `b` or they are in the same summand and `a` is less than `b`
there.
## Notation
* `Σₗ' i, α i`: Sigma type equipped with the lexicographic order. A type synonym of `Σ' i, α i`.
## See also
Related files are:
* `Data.Finset.Colex`: Colexicographic order on finite sets.
* `Data.List.Lex`: Lexicographic order on lists.
* `Data.Pi.Lex`: Lexicographic order on `Πₗ i, α i`.
* `Data.Sigma.Order`: Lexicographic order on `Σₗ i, α i`. Basically a twin of this file.
* `Data.Prod.Lex`: Lexicographic order on `α × β`.
## TODO
Define the disjoint order on `Σ' i, α i`, where `x ≤ y` only if `x.fst = y.fst`.
Prove that a sigma type is a `NoMaxOrder`, `NoMinOrder`, `DenselyOrdered` when its summands
are.
-/


variable {ι : Type*} {α : ι → Type*}

namespace PSigma

/-- The notation `Σₗ' i, α i` refers to a sigma type which is locally equipped with the
lexicographic order.-/
notation3 "Σₗ' "(...)", "r:(scoped p => _root_.Lex (PSigma p)) => r

namespace Lex

/-- The lexicographical `≤` on a sigma type. -/
instance le [LT ι] [∀ i, LE (α i)] : LE (Σₗ' i, α i) :=
  ⟨Lex (· < ·) fun _ => (· ≤ ·)⟩
#align psigma.lex.has_le PSigma.Lex.le

/-- The lexicographical `<` on a sigma type. -/
instance lt [LT ι] [∀ i, LT (α i)] : LT (Σₗ' i, α i) :=
  ⟨Lex (· < ·) fun _ => (· < ·)⟩
#align psigma.lex.has_lt PSigma.Lex.lt

instance preorder [Preorder ι] [∀ i, Preorder (α i)] : Preorder (Σₗ' i, α i) :=
  { Lex.le, Lex.lt with
    le_refl := fun ⟨i, a⟩ => Lex.right _ le_rfl,
    le_trans := by
      rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ ⟨a₃, b₃⟩ ⟨h₁r⟩ ⟨h₂r⟩
      · left
        -- ⊢ a₁ < a₃
        apply lt_trans
        repeat' assumption
        -- 🎉 no goals
      · left
        -- ⊢ a₁ < a₂
        assumption
        -- 🎉 no goals
      · left
        -- ⊢ a₁ < a₃
        assumption
        -- 🎉 no goals
      · right
        -- ⊢ b₁ ≤ b₂✝
        apply le_trans
        repeat' assumption,
        -- 🎉 no goals
    lt_iff_le_not_le := by
      refine' fun a b => ⟨fun hab => ⟨hab.mono_right fun i a b => le_of_lt, _⟩, _⟩
      -- ⊢ ¬b ≤ a
      · rintro (⟨i, a, hji⟩ | ⟨i, hba⟩) <;> obtain ⟨_, _, hij⟩ | ⟨_, hab⟩ := hab
        -- ⊢ False
                                            -- ⊢ False
                                            -- ⊢ False
        · exact hij.not_lt hji
          -- 🎉 no goals
        · exact lt_irrefl _ hji
          -- 🎉 no goals
        · exact lt_irrefl _ hij
          -- 🎉 no goals
        · exact hab.not_le hba
          -- 🎉 no goals
      · rintro ⟨⟨j, b, hij⟩ | ⟨i, hab⟩, hba⟩
        -- ⊢ { fst := a₁✝, snd := j } < { fst := a₂✝, snd := b }
        · exact Lex.left _ _ hij
          -- 🎉 no goals
        · exact Lex.right _ (hab.lt_of_not_le fun h => hba <| Lex.right _ h) }
          -- 🎉 no goals
#align psigma.lex.preorder PSigma.Lex.preorder

/-- Dictionary / lexicographic partial_order for dependent pairs. -/
instance partialOrder [PartialOrder ι] [∀ i, PartialOrder (α i)] : PartialOrder (Σₗ' i, α i) :=
  { Lex.preorder with
    le_antisymm := by
      rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ (⟨_, _, hlt₁⟩ | ⟨_, hlt₁⟩) (⟨_, _, hlt₂⟩ | ⟨_, hlt₂⟩)
      · exact (lt_irrefl a₁ <| hlt₁.trans hlt₂).elim
        -- 🎉 no goals
      · exact (lt_irrefl a₁ hlt₁).elim
        -- 🎉 no goals
      · exact (lt_irrefl a₁ hlt₂).elim
        -- 🎉 no goals
      · rw [hlt₁.antisymm hlt₂] }
        -- 🎉 no goals
#align psigma.lex.partial_order PSigma.Lex.partialOrder

/-- Dictionary / lexicographic linear_order for pairs. -/
instance linearOrder [LinearOrder ι] [∀ i, LinearOrder (α i)] : LinearOrder (Σₗ' i, α i) :=
  { Lex.partialOrder with
    le_total := by
      rintro ⟨i, a⟩ ⟨j, b⟩
      -- ⊢ { fst := i, snd := a } ≤ { fst := j, snd := b } ∨ { fst := j, snd := b } ≤ { …
      obtain hij | rfl | hji := lt_trichotomy i j
      · exact Or.inl (Lex.left _ _ hij)
        -- 🎉 no goals
      · obtain hab | hba := le_total a b
        -- ⊢ { fst := i, snd := a } ≤ { fst := i, snd := b } ∨ { fst := i, snd := b } ≤ { …
        · exact Or.inl (Lex.right _ hab)
          -- 🎉 no goals
        · exact Or.inr (Lex.right _ hba)
          -- 🎉 no goals
      · exact Or.inr (Lex.left _ _ hji),
        -- 🎉 no goals
    decidableEq := PSigma.decidableEq, decidableLE := Lex.decidable _ _,
    decidableLT := Lex.decidable _ _ }
#align psigma.lex.linear_order PSigma.Lex.linearOrder

/-- The lexicographical linear order on a sigma type. -/
instance orderBot [PartialOrder ι] [OrderBot ι] [∀ i, Preorder (α i)] [OrderBot (α ⊥)] :
    OrderBot (Σₗ' i, α i) where
  bot := ⟨⊥, ⊥⟩
  bot_le := fun ⟨a, b⟩ => by
    obtain rfl | ha := eq_bot_or_bot_lt a
    -- ⊢ ⊥ ≤ { fst := ⊥, snd := b }
    · exact Lex.right _ bot_le
      -- 🎉 no goals
    · exact Lex.left _ _ ha
      -- 🎉 no goals
#align psigma.lex.order_bot PSigma.Lex.orderBot

/-- The lexicographical linear order on a sigma type. -/
instance orderTop [PartialOrder ι] [OrderTop ι] [∀ i, Preorder (α i)] [OrderTop (α ⊤)] :
    OrderTop (Σₗ' i, α i) where
  top := ⟨⊤, ⊤⟩
  le_top := fun ⟨a, b⟩ => by
    obtain rfl | ha := eq_top_or_lt_top a
    -- ⊢ { fst := ⊤, snd := b } ≤ ⊤
    · exact Lex.right _ le_top
      -- 🎉 no goals
    · exact Lex.left _ _ ha
      -- 🎉 no goals
#align psigma.lex.order_top PSigma.Lex.orderTop

/-- The lexicographical linear order on a sigma type. -/
instance boundedOrder [PartialOrder ι] [BoundedOrder ι] [∀ i, Preorder (α i)] [OrderBot (α ⊥)]
    [OrderTop (α ⊤)] : BoundedOrder (Σₗ' i, α i) :=
  { Lex.orderBot, Lex.orderTop with }
#align psigma.lex.bounded_order PSigma.Lex.boundedOrder

instance denselyOrdered [Preorder ι] [DenselyOrdered ι] [∀ i, Nonempty (α i)] [∀ i, Preorder (α i)]
    [∀ i, DenselyOrdered (α i)] : DenselyOrdered (Σₗ' i, α i) :=
  ⟨by
    rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | @⟨_, _, b, h⟩)
    -- ⊢ ∃ a_1, { fst := i, snd := a } < a_1 ∧ a_1 < { fst := j, snd := b }
    · obtain ⟨k, hi, hj⟩ := exists_between h
      -- ⊢ ∃ a_1, { fst := i, snd := a } < a_1 ∧ a_1 < { fst := j, snd := b }
      obtain ⟨c⟩ : Nonempty (α k) := inferInstance
      -- ⊢ ∃ a_1, { fst := i, snd := a } < a_1 ∧ a_1 < { fst := j, snd := b }
      exact ⟨⟨k, c⟩, left _ _ hi, left _ _ hj⟩
      -- 🎉 no goals
    · obtain ⟨c, ha, hb⟩ := exists_between h
      -- ⊢ ∃ a_1, { fst := i, snd := a } < a_1 ∧ a_1 < { fst := i, snd := b }
      exact ⟨⟨i, c⟩, right _ ha, right _ hb⟩⟩
      -- 🎉 no goals
#align psigma.lex.densely_ordered PSigma.Lex.denselyOrdered

instance denselyOrdered_of_noMaxOrder [Preorder ι] [∀ i, Preorder (α i)]
    [∀ i, DenselyOrdered (α i)] [∀ i, NoMaxOrder (α i)] : DenselyOrdered (Σₗ' i, α i) :=
  ⟨by
    rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | @⟨_, _, b, h⟩)
    -- ⊢ ∃ a_1, { fst := i, snd := a } < a_1 ∧ a_1 < { fst := j, snd := b }
    · obtain ⟨c, ha⟩ := exists_gt a
      -- ⊢ ∃ a_1, { fst := i, snd := a } < a_1 ∧ a_1 < { fst := j, snd := b }
      exact ⟨⟨i, c⟩, right _ ha, left _ _ h⟩
      -- 🎉 no goals
    · obtain ⟨c, ha, hb⟩ := exists_between h
      -- ⊢ ∃ a_1, { fst := i, snd := a } < a_1 ∧ a_1 < { fst := i, snd := b }
      exact ⟨⟨i, c⟩, right _ ha, right _ hb⟩⟩
      -- 🎉 no goals
#align psigma.lex.densely_ordered_of_no_max_order PSigma.Lex.denselyOrdered_of_noMaxOrder

instance densely_ordered_of_noMinOrder [Preorder ι] [∀ i, Preorder (α i)]
    [∀ i, DenselyOrdered (α i)] [∀ i, NoMinOrder (α i)] : DenselyOrdered (Σₗ' i, α i) :=
  ⟨by
    rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | @⟨_, _, b, h⟩)
    -- ⊢ ∃ a_1, { fst := i, snd := a } < a_1 ∧ a_1 < { fst := j, snd := b }
    · obtain ⟨c, hb⟩ := exists_lt b
      -- ⊢ ∃ a_1, { fst := i, snd := a } < a_1 ∧ a_1 < { fst := j, snd := b }
      exact ⟨⟨j, c⟩, left _ _ h, right _ hb⟩
      -- 🎉 no goals
    · obtain ⟨c, ha, hb⟩ := exists_between h
      -- ⊢ ∃ a_1, { fst := i, snd := a } < a_1 ∧ a_1 < { fst := i, snd := b }
      exact ⟨⟨i, c⟩, right _ ha, right _ hb⟩⟩
      -- 🎉 no goals
#align psigma.lex.densely_ordered_of_no_min_order PSigma.Lex.densely_ordered_of_noMinOrder

instance noMaxOrder_of_nonempty [Preorder ι] [∀ i, Preorder (α i)] [NoMaxOrder ι]
    [∀ i, Nonempty (α i)] : NoMaxOrder (Σₗ' i, α i) :=
  ⟨by
    rintro ⟨i, a⟩
    -- ⊢ ∃ b, { fst := i, snd := a } < b
    obtain ⟨j, h⟩ := exists_gt i
    -- ⊢ ∃ b, { fst := i, snd := a } < b
    obtain ⟨b⟩ : Nonempty (α j) := inferInstance
    -- ⊢ ∃ b, { fst := i, snd := a } < b
    exact ⟨⟨j, b⟩, left _ _ h⟩⟩
    -- 🎉 no goals
#align psigma.lex.no_max_order_of_nonempty PSigma.Lex.noMaxOrder_of_nonempty

-- porting note: this statement was incorrect in mathlib3, hence the `#noalign`.
instance noMinOrder_of_nonempty [Preorder ι] [∀ i, Preorder (α i)] [NoMinOrder ι]
    [∀ i, Nonempty (α i)] : NoMinOrder (Σₗ' i, α i) :=
  ⟨by
    rintro ⟨i, a⟩
    -- ⊢ ∃ b, b < { fst := i, snd := a }
    obtain ⟨j, h⟩ := exists_lt i
    -- ⊢ ∃ b, b < { fst := i, snd := a }
    obtain ⟨b⟩ : Nonempty (α j) := inferInstance
    -- ⊢ ∃ b, b < { fst := i, snd := a }
    exact ⟨⟨j, b⟩, left _ _ h⟩⟩
    -- 🎉 no goals
#noalign psigma.lex.no_min_order_of_nonempty

instance noMaxOrder [Preorder ι] [∀ i, Preorder (α i)] [∀ i, NoMaxOrder (α i)] :
    NoMaxOrder (Σₗ' i, α i) :=
  ⟨by
    rintro ⟨i, a⟩
    -- ⊢ ∃ b, { fst := i, snd := a } < b
    obtain ⟨b, h⟩ := exists_gt a
    -- ⊢ ∃ b, { fst := i, snd := a } < b
    exact ⟨⟨i, b⟩, right _ h⟩⟩
    -- 🎉 no goals
#align psigma.lex.no_max_order PSigma.Lex.noMaxOrder

instance noMinOrder [Preorder ι] [∀ i, Preorder (α i)] [∀ i, NoMinOrder (α i)] :
    NoMinOrder (Σₗ' i, α i) :=
  ⟨by
    rintro ⟨i, a⟩
    -- ⊢ ∃ b, b < { fst := i, snd := a }
    obtain ⟨b, h⟩ := exists_lt a
    -- ⊢ ∃ b, b < { fst := i, snd := a }
    exact ⟨⟨i, b⟩, right _ h⟩⟩
    -- 🎉 no goals
#align psigma.lex.no_min_order PSigma.Lex.noMinOrder

end Lex

end PSigma
