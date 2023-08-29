/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Sigma.Lex
import Mathlib.Order.BoundedOrder
import Mathlib.Mathport.Notation

#align_import data.sigma.order from "leanprover-community/mathlib"@"1fc36cc9c8264e6e81253f88be7fb2cb6c92d76a"

/-!
# Orders on a sigma type

This file defines two orders on a sigma type:
* The disjoint sum of orders. `a` is less `b` iff `a` and `b` are in the same summand and `a` is
  less than `b` there.
* The lexicographical order. `a` is less than `b` if its summand is strictly less than the summand
  of `b` or they are in the same summand and `a` is less than `b` there.

We make the disjoint sum of orders the default set of instances. The lexicographic order goes on a
type synonym.

## Notation

* `_root_.Lex (Sigma α)`: Sigma type equipped with the lexicographic order.
Type synonym of `Σ i, α i`.

## See also

Related files are:
* `Data.Finset.CoLex`: Colexicographic order on finite sets.
* `Data.List.Lex`: Lexicographic order on lists.
* `Data.Pi.Lex`: Lexicographic order on `Πₗ i, α i`.
* `Data.PSigma.Order`: Lexicographic order on `Σₗ' i, α i`. Basically a twin of this file.
* `Data.Prod.Lex`: Lexicographic order on `α × β`.

## TODO

Upgrade `Equiv.sigma_congr_left`, `Equiv.sigma_congr`, `Equiv.sigma_assoc`,
`Equiv.sigma_prod_of_equiv`, `Equiv.sigma_equiv_prod`, ... to order isomorphisms.
-/


namespace Sigma

variable {ι : Type*} {α : ι → Type*}

/-! ### Disjoint sum of orders on `Sigma` -/

-- porting note: I made this `le` instead of `LE` because the output type is `Prop`
/-- Disjoint sum of orders. `⟨i, a⟩ ≤ ⟨j, b⟩` iff `i = j` and `a ≤ b`. -/
protected inductive le [∀ i, LE (α i)] : ∀ _a _b : Σ i, α i, Prop
  | fiber (i : ι) (a b : α i) : a ≤ b → Sigma.le ⟨i, a⟩ ⟨i, b⟩
#align sigma.le Sigma.le

/-- Disjoint sum of orders. `⟨i, a⟩ < ⟨j, b⟩` iff `i = j` and `a < b`. -/
protected inductive lt [∀ i, LT (α i)] : ∀ _a _b : Σi, α i, Prop
  | fiber (i : ι) (a b : α i) : a < b → Sigma.lt ⟨i, a⟩ ⟨i, b⟩
#align sigma.lt Sigma.lt

protected instance LE [∀ i, LE (α i)] : LE (Σi, α i) where
  le := Sigma.le

protected instance LT [∀ i, LT (α i)] : LT (Σi, α i) where
  lt := Sigma.lt

@[simp]
theorem mk_le_mk_iff [∀ i, LE (α i)] {i : ι} {a b : α i} : (⟨i, a⟩ : Sigma α) ≤ ⟨i, b⟩ ↔ a ≤ b :=
  ⟨fun ⟨_, _, _, h⟩ => h, Sigma.le.fiber _ _ _⟩
#align sigma.mk_le_mk_iff Sigma.mk_le_mk_iff

@[simp]
theorem mk_lt_mk_iff [∀ i, LT (α i)] {i : ι} {a b : α i} : (⟨i, a⟩ : Sigma α) < ⟨i, b⟩ ↔ a < b :=
  ⟨fun ⟨_, _, _, h⟩ => h, Sigma.lt.fiber _ _ _⟩
#align sigma.mk_lt_mk_iff Sigma.mk_lt_mk_iff

theorem le_def [∀ i, LE (α i)] {a b : Σi, α i} : a ≤ b ↔ ∃ h : a.1 = b.1, h.rec a.2 ≤ b.2 := by
  constructor
  -- ⊢ a ≤ b → ∃ h, h ▸ a.snd ≤ b.snd
  · rintro ⟨i, a, b, h⟩
    -- ⊢ ∃ h, h ▸ { fst := i, snd := a }.snd ≤ { fst := i, snd := b }.snd
    exact ⟨rfl, h⟩
    -- 🎉 no goals
  · obtain ⟨i, a⟩ := a
    -- ⊢ (∃ h, h ▸ { fst := i, snd := a }.snd ≤ b.snd) → { fst := i, snd := a } ≤ b
    obtain ⟨j, b⟩ := b
    -- ⊢ (∃ h, h ▸ { fst := i, snd := a }.snd ≤ { fst := j, snd := b }.snd) → { fst : …
    rintro ⟨rfl : i = j, h⟩
    -- ⊢ { fst := i, snd := a } ≤ { fst := i, snd := b }
    exact le.fiber _ _ _ h
    -- 🎉 no goals
#align sigma.le_def Sigma.le_def

theorem lt_def [∀ i, LT (α i)] {a b : Σi, α i} : a < b ↔ ∃ h : a.1 = b.1, h.rec a.2 < b.2 := by
  constructor
  -- ⊢ a < b → ∃ h, h ▸ a.snd < b.snd
  · rintro ⟨i, a, b, h⟩
    -- ⊢ ∃ h, h ▸ { fst := i, snd := a }.snd < { fst := i, snd := b }.snd
    exact ⟨rfl, h⟩
    -- 🎉 no goals
  · obtain ⟨i, a⟩ := a
    -- ⊢ (∃ h, h ▸ { fst := i, snd := a }.snd < b.snd) → { fst := i, snd := a } < b
    obtain ⟨j, b⟩ := b
    -- ⊢ (∃ h, h ▸ { fst := i, snd := a }.snd < { fst := j, snd := b }.snd) → { fst : …
    rintro ⟨rfl : i = j, h⟩
    -- ⊢ { fst := i, snd := a } < { fst := i, snd := b }
    exact lt.fiber _ _ _ h
    -- 🎉 no goals
#align sigma.lt_def Sigma.lt_def

protected instance preorder [∀ i, Preorder (α i)] : Preorder (Σi, α i) :=
  { Sigma.LE, Sigma.LT with
    le_refl := fun ⟨i, a⟩ => Sigma.le.fiber i a a le_rfl,
    le_trans := by
      rintro _ _ _ ⟨i, a, b, hab⟩ ⟨_, _, c, hbc⟩
      -- ⊢ { fst := i, snd := a } ≤ { fst := i, snd := c }
      exact le.fiber i a c (hab.trans hbc),
      -- 🎉 no goals
    lt_iff_le_not_le := fun _ _ => by
      constructor
      -- ⊢ x✝¹ < x✝ → x✝¹ ≤ x✝ ∧ ¬x✝ ≤ x✝¹
      · rintro ⟨i, a, b, hab⟩
        -- ⊢ { fst := i, snd := a } ≤ { fst := i, snd := b } ∧ ¬{ fst := i, snd := b } ≤  …
        rwa [mk_le_mk_iff, mk_le_mk_iff, ← lt_iff_le_not_le]
        -- 🎉 no goals
      · rintro ⟨⟨i, a, b, hab⟩, h⟩
        -- ⊢ { fst := i, snd := a } < { fst := i, snd := b }
        rw [mk_le_mk_iff] at h
        -- ⊢ { fst := i, snd := a } < { fst := i, snd := b }
        exact mk_lt_mk_iff.2 (hab.lt_of_not_le h) }
        -- 🎉 no goals

instance [∀ i, PartialOrder (α i)] : PartialOrder (Σi, α i) :=
  { Sigma.preorder with
    le_antisymm := by
      rintro _ _ ⟨i, a, b, hab⟩ ⟨_, _, _, hba⟩
      -- ⊢ { fst := i, snd := a } = { fst := i, snd := b }
      exact ext rfl (heq_of_eq <| hab.antisymm hba) }
      -- 🎉 no goals

instance [∀ i, Preorder (α i)] [∀ i, DenselyOrdered (α i)] : DenselyOrdered (Σi, α i) where
  dense := by
    rintro ⟨i, a⟩ ⟨_, _⟩ ⟨_, _, b, h⟩
    -- ⊢ ∃ a_1, { fst := i, snd := a } < a_1 ∧ a_1 < { fst := i, snd := b }
    obtain ⟨c, ha, hb⟩ := exists_between h
    -- ⊢ ∃ a_1, { fst := i, snd := a } < a_1 ∧ a_1 < { fst := i, snd := b }
    exact ⟨⟨i, c⟩, lt.fiber i a c ha, lt.fiber i c b hb⟩
    -- 🎉 no goals

/-! ### Lexicographical order on `Sigma` -/


namespace Lex
-- mathport name: «exprΣₗ , »
/-- The notation `Σₗ i, α i` refers to a sigma type equipped with the lexicographic order. -/
notation3 "Σₗ "(...)", "r:(scoped p => _root_.Lex (Sigma p)) => r

/-- The lexicographical `≤` on a sigma type. -/
protected instance LE [LT ι] [∀ i, LE (α i)] : LE (Σₗ i, α i) where
  le := Lex (· < ·) fun _ => (· ≤ ·)
#align sigma.lex.has_le Sigma.Lex.LE

/-- The lexicographical `<` on a sigma type. -/
protected instance LT [LT ι] [∀ i, LT (α i)] : LT (Σₗ i, α i) where
  lt := Lex (· < ·) fun _ => (· < ·)
#align sigma.lex.has_lt Sigma.Lex.LT

theorem le_def [LT ι] [∀ i, LE (α i)] {a b : Σₗ i, α i} :
    a ≤ b ↔ a.1 < b.1 ∨ ∃ h : a.1 = b.1, h.rec a.2 ≤ b.2 :=
  Sigma.lex_iff
#align sigma.lex.le_def Sigma.Lex.le_def

theorem lt_def [LT ι] [∀ i, LT (α i)] {a b : Σₗ i, α i} :
    a < b ↔ a.1 < b.1 ∨ ∃ h : a.1 = b.1, h.rec a.2 < b.2 :=
  Sigma.lex_iff
#align sigma.lex.lt_def Sigma.Lex.lt_def

/-- The lexicographical preorder on a sigma type. -/
instance preorder [Preorder ι] [∀ i, Preorder (α i)] : Preorder (Σₗ i, α i) :=
  { Sigma.Lex.LE, Sigma.Lex.LT with
    le_refl := fun ⟨i, a⟩ => Lex.right a a le_rfl,
    le_trans := fun _ _ _ => trans_of ((Lex (· < ·)) fun _ => (· ≤ ·)),
    lt_iff_le_not_le := by
      refine' fun a b => ⟨fun hab => ⟨hab.mono_right fun i a b => le_of_lt, _⟩, _⟩
      -- ⊢ ¬b ≤ a
      · rintro (⟨b, a, hji⟩ | ⟨b, a, hba⟩) <;> obtain ⟨_, _, hij⟩ | ⟨_, _, hab⟩ := hab
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
      · rintro ⟨⟨a, b, hij⟩ | ⟨a, b, hab⟩, hba⟩
        -- ⊢ { fst := i✝, snd := a } < { fst := j✝, snd := b }
        · exact Sigma.Lex.left _ _ hij
          -- 🎉 no goals
        · exact Sigma.Lex.right _ _ (hab.lt_of_not_le fun h => hba <| Sigma.Lex.right _ _ h) }
          -- 🎉 no goals
#align sigma.lex.preorder Sigma.Lex.preorder

/-- The lexicographical partial order on a sigma type. -/
instance partialOrder [Preorder ι] [∀ i, PartialOrder (α i)] :
    PartialOrder (Σₗ i, α i) :=
  { Lex.preorder with
    le_antisymm := fun _ _ => antisymm_of ((Lex (· < ·)) fun _ => (· ≤ ·)) }
#align sigma.lex.partial_order Sigma.Lex.partialOrder



/-- The lexicographical linear order on a sigma type. -/
instance linearOrder [LinearOrder ι] [∀ i, LinearOrder (α i)] :
    LinearOrder (Σₗ i, α i) :=
  { Lex.partialOrder with
    le_total := total_of ((Lex (· < ·)) fun _ => (· ≤ ·)),
    decidableEq := Sigma.instDecidableEqSigma,
    decidableLE := Lex.decidable _ _ }
#align sigma.lex.linear_order Sigma.Lex.linearOrder

/-- The lexicographical linear order on a sigma type. -/
instance orderBot [PartialOrder ι] [OrderBot ι] [∀ i, Preorder (α i)] [OrderBot (α ⊥)] :
    OrderBot (Σₗ i, α i) where
  bot := ⟨⊥, ⊥⟩
  bot_le := fun ⟨a, b⟩ => by
    obtain rfl | ha := eq_bot_or_bot_lt a
    -- ⊢ ⊥ ≤ { fst := ⊥, snd := b }
    · exact Lex.right _ _ bot_le
      -- 🎉 no goals
    · exact Lex.left _ _ ha
      -- 🎉 no goals
#align sigma.lex.order_bot Sigma.Lex.orderBot

/-- The lexicographical linear order on a sigma type. -/
instance orderTop [PartialOrder ι] [OrderTop ι] [∀ i, Preorder (α i)] [OrderTop (α ⊤)] :
    OrderTop (Σₗ i, α i) where
  top := ⟨⊤, ⊤⟩
  le_top := fun ⟨a, b⟩ => by
    obtain rfl | ha := eq_top_or_lt_top a
    -- ⊢ { fst := ⊤, snd := b } ≤ ⊤
    · exact Lex.right _ _ le_top
      -- 🎉 no goals
    · exact Lex.left _ _ ha
      -- 🎉 no goals
#align sigma.lex.order_top Sigma.Lex.orderTop

/-- The lexicographical linear order on a sigma type. -/
instance boundedOrder [PartialOrder ι] [BoundedOrder ι] [∀ i, Preorder (α i)] [OrderBot (α ⊥)]
    [OrderTop (α ⊤)] : BoundedOrder (Σₗ i, α i) :=
  { Lex.orderBot, Lex.orderTop with }
#align sigma.lex.bounded_order Sigma.Lex.boundedOrder

instance denselyOrdered [Preorder ι] [DenselyOrdered ι] [∀ i, Nonempty (α i)] [∀ i, Preorder (α i)]
    [∀ i, DenselyOrdered (α i)] : DenselyOrdered (Σₗ i, α i) where
  dense := by
    rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | ⟨_, b, h⟩)
    -- ⊢ ∃ a_1, { fst := i, snd := a } < a_1 ∧ a_1 < { fst := j, snd := b }
    · obtain ⟨k, hi, hj⟩ := exists_between h
      -- ⊢ ∃ a_1, { fst := i, snd := a } < a_1 ∧ a_1 < { fst := j, snd := b }
      obtain ⟨c⟩ : Nonempty (α k) := inferInstance
      -- ⊢ ∃ a_1, { fst := i, snd := a } < a_1 ∧ a_1 < { fst := j, snd := b }
      exact ⟨⟨k, c⟩, left _ _ hi, left _ _ hj⟩
      -- 🎉 no goals
    · obtain ⟨c, ha, hb⟩ := exists_between h
      -- ⊢ ∃ a_1, { fst := i, snd := a } < a_1 ∧ a_1 < { fst := i, snd := b }
      exact ⟨⟨i, c⟩, right _ _ ha, right _ _ hb⟩
      -- 🎉 no goals
#align sigma.lex.densely_ordered Sigma.Lex.denselyOrdered

instance denselyOrdered_of_noMaxOrder [Preorder ι] [∀ i, Preorder (α i)]
    [∀ i, DenselyOrdered (α i)] [∀ i, NoMaxOrder (α i)] :
    DenselyOrdered (Σₗ i, α i) where
  dense := by
    rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | ⟨_, b, h⟩)
    -- ⊢ ∃ a_1, { fst := i, snd := a } < a_1 ∧ a_1 < { fst := j, snd := b }
    · obtain ⟨c, ha⟩ := exists_gt a
      -- ⊢ ∃ a_1, { fst := i, snd := a } < a_1 ∧ a_1 < { fst := j, snd := b }
      exact ⟨⟨i, c⟩, right _ _ ha, left _ _ h⟩
      -- 🎉 no goals
    · obtain ⟨c, ha, hb⟩ := exists_between h
      -- ⊢ ∃ a_1, { fst := i, snd := a } < a_1 ∧ a_1 < { fst := i, snd := b }
      exact ⟨⟨i, c⟩, right _ _ ha, right _ _ hb⟩
      -- 🎉 no goals
#align sigma.lex.densely_ordered_of_no_max_order Sigma.Lex.denselyOrdered_of_noMaxOrder

instance denselyOrdered_of_noMinOrder [Preorder ι] [∀ i, Preorder (α i)]
    [∀ i, DenselyOrdered (α i)] [∀ i, NoMinOrder (α i)] :
    DenselyOrdered (Σₗ i, α i) where
  dense := by
    rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | ⟨_, b, h⟩)
    -- ⊢ ∃ a_1, { fst := i, snd := a } < a_1 ∧ a_1 < { fst := j, snd := b }
    · obtain ⟨c, hb⟩ := exists_lt b
      -- ⊢ ∃ a_1, { fst := i, snd := a } < a_1 ∧ a_1 < { fst := j, snd := b }
      exact ⟨⟨j, c⟩, left _ _ h, right _ _ hb⟩
      -- 🎉 no goals
    · obtain ⟨c, ha, hb⟩ := exists_between h
      -- ⊢ ∃ a_1, { fst := i, snd := a } < a_1 ∧ a_1 < { fst := i, snd := b }
      exact ⟨⟨i, c⟩, right _ _ ha, right _ _ hb⟩
      -- 🎉 no goals
#align sigma.lex.densely_ordered_of_no_min_order Sigma.Lex.denselyOrdered_of_noMinOrder

instance noMaxOrder_of_nonempty [Preorder ι] [∀ i, Preorder (α i)] [NoMaxOrder ι]
    [∀ i, Nonempty (α i)] : NoMaxOrder (Σₗ i, α i) where
  exists_gt := by
    rintro ⟨i, a⟩
    -- ⊢ ∃ b, { fst := i, snd := a } < b
    obtain ⟨j, h⟩ := exists_gt i
    -- ⊢ ∃ b, { fst := i, snd := a } < b
    obtain ⟨b⟩ : Nonempty (α j) := inferInstance
    -- ⊢ ∃ b, { fst := i, snd := a } < b
    exact ⟨⟨j, b⟩, left _ _ h⟩
    -- 🎉 no goals
#align sigma.lex.no_max_order_of_nonempty Sigma.Lex.noMaxOrder_of_nonempty

-- porting note: this statement was incorrect in mathlib3, hence the `#noalign`.
instance noMinOrder_of_nonempty [Preorder ι] [∀ i, Preorder (α i)] [NoMinOrder ι]
    [∀ i, Nonempty (α i)] : NoMinOrder (Σₗ i, α i) where
  exists_lt := by
    rintro ⟨i, a⟩
    -- ⊢ ∃ b, b < { fst := i, snd := a }
    obtain ⟨j, h⟩ := exists_lt i
    -- ⊢ ∃ b, b < { fst := i, snd := a }
    obtain ⟨b⟩ : Nonempty (α j) := inferInstance
    -- ⊢ ∃ b, b < { fst := i, snd := a }
    exact ⟨⟨j, b⟩, left _ _ h⟩
    -- 🎉 no goals
#noalign sigma.lex.no_min_order_of_nonempty

instance noMaxOrder [Preorder ι] [∀ i, Preorder (α i)] [∀ i, NoMaxOrder (α i)] :
    NoMaxOrder (Σₗ i, α i) where
  exists_gt := by
    rintro ⟨i, a⟩
    -- ⊢ ∃ b, { fst := i, snd := a } < b
    obtain ⟨b, h⟩ := exists_gt a
    -- ⊢ ∃ b, { fst := i, snd := a } < b
    exact ⟨⟨i, b⟩, right _ _ h⟩
    -- 🎉 no goals
#align sigma.lex.no_max_order Sigma.Lex.noMaxOrder

instance noMinOrder [Preorder ι] [∀ i, Preorder (α i)] [∀ i, NoMinOrder (α i)] :
    NoMinOrder (Σₗ i, α i) where
  exists_lt := by
    rintro ⟨i, a⟩
    -- ⊢ ∃ b, b < { fst := i, snd := a }
    obtain ⟨b, h⟩ := exists_lt a
    -- ⊢ ∃ b, b < { fst := i, snd := a }
    exact ⟨⟨i, b⟩, right _ _ h⟩
    -- 🎉 no goals
#align sigma.lex.no_min_order Sigma.Lex.noMinOrder

end Lex

end Sigma
