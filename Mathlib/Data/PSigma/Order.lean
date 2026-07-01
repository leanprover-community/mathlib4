/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Minchao Wu
-/
module

public import Mathlib.Data.Sigma.Lex
public import Mathlib.Data.Sigma.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.Lex

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

public section


variable {ι : Type*} {α : ι → Type*}

namespace PSigma

/-- The notation `Σₗ' i, α i` refers to a sigma type which is locally equipped with the
lexicographic order. -/
-- TODO: make `Lex` be `Sort u -> Sort u` so we can remove `.{_+1, _+1}`
notation3 "Σₗ' " (...) ", " r:(scoped p => _root_.Lex (PSigma.{_ + 1, _ + 1} p)) => r

namespace Lex

/-- The lexicographical `≤` on a sigma type. -/
instance le [LT ι] [∀ i, LE (α i)] : LE (Σₗ' i, α i) :=
  ⟨Lex (· < ·) fun _ => (· ≤ ·)⟩

/-- The lexicographical `<` on a sigma type. -/
instance lt [LT ι] [∀ i, LT (α i)] : LT (Σₗ' i, α i) :=
  ⟨Lex (· < ·) fun _ => (· < ·)⟩

instance preorder [Preorder ι] [∀ i, Preorder (α i)] : Preorder (Σₗ' i, α i) :=
  { Lex.le, Lex.lt with
    le_refl := fun ⟨_, _⟩ => Lex.right _ le_rfl,
    le_trans := by
      rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ ⟨a₃, b₃⟩ ⟨h₁r⟩ ⟨h₂r⟩
      · left
        apply lt_trans
        repeat' assumption
      · left
        assumption
      · left
        assumption
      · right
        apply le_trans
        repeat' assumption,
    lt_iff_le_not_ge := by
      refine fun a b => ⟨fun hab => ⟨hab.mono_right fun i a b => le_of_lt, ?_⟩, ?_⟩
      · rintro (⟨i, a, hji⟩ | ⟨i, hba⟩) <;> obtain ⟨_, _, hij⟩ | ⟨_, hab⟩ := hab
        · exact hij.not_gt hji
        · exact lt_irrefl _ hji
        · exact lt_irrefl _ hij
        · exact hab.not_ge hba
      · rintro ⟨⟨j, b, hij⟩ | ⟨i, hab⟩, hba⟩
        · exact Lex.left _ _ hij
        · exact Lex.right _ (hab.lt_of_not_ge fun h => hba <| Lex.right _ h) }

/-- Dictionary / lexicographic `PartialOrder` for dependent pairs. -/
instance partialOrder [PartialOrder ι] [∀ i, PartialOrder (α i)] : PartialOrder (Σₗ' i, α i) :=
  { Lex.preorder with
    le_antisymm := by
      rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ (⟨_, _, hlt₁⟩ | ⟨_, hlt₁⟩) (⟨_, _, hlt₂⟩ | ⟨_, hlt₂⟩)
      · exact (lt_irrefl a₁ <| hlt₁.trans hlt₂).elim
      · exact (lt_irrefl a₁ hlt₁).elim
      · exact (lt_irrefl a₁ hlt₂).elim
      · rw [hlt₁.antisymm hlt₂] }

/-- Dictionary / lexicographic `LinearOrder` for pairs. -/
instance linearOrder [LinearOrder ι] [∀ i, LinearOrder (α i)] : LinearOrder (Σₗ' i, α i) :=
  { Lex.partialOrder with
    le_total := by
      rintro ⟨i, a⟩ ⟨j, b⟩
      obtain hij | rfl | hji := lt_trichotomy i j
      · exact Or.inl (Lex.left _ _ hij)
      · obtain hab | hba := le_total a b
        · exact Or.inl (Lex.right _ hab)
        · exact Or.inr (Lex.right _ hba)
      · exact Or.inr (Lex.left _ _ hji),
    toDecidableEq := PSigma.decidableEq, toDecidableLE := Lex.decidable _ _,
    toDecidableLT := Lex.decidable _ _ }

/-- The lexicographical linear order on a sigma type. -/
instance orderBot [PartialOrder ι] [OrderBot ι] [∀ i, Preorder (α i)] [OrderBot (α ⊥)] :
    OrderBot (Σₗ' i, α i) where
  bot := ⟨⊥, ⊥⟩
  bot_le := fun ⟨a, b⟩ => by
    obtain rfl | ha := eq_bot_or_bot_lt a
    · exact Lex.right _ bot_le
    · exact Lex.left _ _ ha

/-- The lexicographical linear order on a sigma type. -/
instance orderTop [PartialOrder ι] [OrderTop ι] [∀ i, Preorder (α i)] [OrderTop (α ⊤)] :
    OrderTop (Σₗ' i, α i) where
  top := ⟨⊤, ⊤⟩
  le_top := fun ⟨a, b⟩ => by
    obtain rfl | ha := eq_top_or_lt_top a
    · exact Lex.right _ le_top
    · exact Lex.left _ _ ha

/-- The lexicographical linear order on a sigma type. -/
instance boundedOrder [PartialOrder ι] [BoundedOrder ι] [∀ i, Preorder (α i)] [OrderBot (α ⊥)]
    [OrderTop (α ⊤)] : BoundedOrder (Σₗ' i, α i) :=
  { Lex.orderBot, Lex.orderTop with }

instance denselyOrdered [Preorder ι] [DenselyOrdered ι] [∀ i, Nonempty (α i)] [∀ i, Preorder (α i)]
    [∀ i, DenselyOrdered (α i)] : DenselyOrdered (Σₗ' i, α i) :=
  ⟨by
    rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | @⟨_, _, b, h⟩)
    · obtain ⟨k, hi, hj⟩ := exists_between h
      obtain ⟨c⟩ : Nonempty (α k) := inferInstance
      exact ⟨⟨k, c⟩, left _ _ hi, left _ _ hj⟩
    · obtain ⟨c, ha, hb⟩ := exists_between h
      exact ⟨⟨i, c⟩, right _ ha, right _ hb⟩⟩

instance denselyOrdered_of_noMaxOrder [Preorder ι] [∀ i, Preorder (α i)]
    [∀ i, DenselyOrdered (α i)] [∀ i, NoMaxOrder (α i)] : DenselyOrdered (Σₗ' i, α i) :=
  ⟨by
    rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | @⟨_, _, b, h⟩)
    · obtain ⟨c, ha⟩ := exists_gt a
      exact ⟨⟨i, c⟩, right _ ha, left _ _ h⟩
    · obtain ⟨c, ha, hb⟩ := exists_between h
      exact ⟨⟨i, c⟩, right _ ha, right _ hb⟩⟩

instance denselyOrdered_of_noMinOrder [Preorder ι] [∀ i, Preorder (α i)]
    [∀ i, DenselyOrdered (α i)] [∀ i, NoMinOrder (α i)] : DenselyOrdered (Σₗ' i, α i) :=
  ⟨by
    rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | @⟨_, _, b, h⟩)
    · obtain ⟨c, hb⟩ := exists_lt b
      exact ⟨⟨j, c⟩, left _ _ h, right _ hb⟩
    · obtain ⟨c, ha, hb⟩ := exists_between h
      exact ⟨⟨i, c⟩, right _ ha, right _ hb⟩⟩

instance noMaxOrder_of_nonempty [Preorder ι] [∀ i, Preorder (α i)] [NoMaxOrder ι]
    [∀ i, Nonempty (α i)] : NoMaxOrder (Σₗ' i, α i) :=
  ⟨by
    rintro ⟨i, a⟩
    obtain ⟨j, h⟩ := exists_gt i
    obtain ⟨b⟩ : Nonempty (α j) := inferInstance
    exact ⟨⟨j, b⟩, left _ _ h⟩⟩

instance noMinOrder_of_nonempty [Preorder ι] [∀ i, Preorder (α i)] [NoMinOrder ι]
    [∀ i, Nonempty (α i)] : NoMinOrder (Σₗ' i, α i) :=
  ⟨by
    rintro ⟨i, a⟩
    obtain ⟨j, h⟩ := exists_lt i
    obtain ⟨b⟩ : Nonempty (α j) := inferInstance
    exact ⟨⟨j, b⟩, left _ _ h⟩⟩

instance noMaxOrder [Preorder ι] [∀ i, Preorder (α i)] [∀ i, NoMaxOrder (α i)] :
    NoMaxOrder (Σₗ' i, α i) :=
  ⟨by
    rintro ⟨i, a⟩
    obtain ⟨b, h⟩ := exists_gt a
    exact ⟨⟨i, b⟩, right _ h⟩⟩

instance noMinOrder [Preorder ι] [∀ i, Preorder (α i)] [∀ i, NoMinOrder (α i)] :
    NoMinOrder (Σₗ' i, α i) :=
  ⟨by
    rintro ⟨i, a⟩
    obtain ⟨b, h⟩ := exists_lt a
    exact ⟨⟨i, b⟩, right _ h⟩⟩

end Lex

end PSigma
