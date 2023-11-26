import Mathlib.Order.RelClasses
import Mathlib.Order.RelIso.Set
import Mathlib.Order.InitialSeg
import Mathlib.Order.Bounds.Basic
import Mathlib.Init.Data.Subtype.Basic
import Mathlib.Data.Sum.Order

universe u v

/--
A forest is a poset in which every down set is a WellOrder
-/
class IsForest (α : Type u) extends PartialOrder α where
  toWellFoundedLT : WellFoundedLT α
  downset_trichot : ∀ (x y a : α), x < a → y < a → x < y ∨ x = y ∨ x > y

attribute [instance] IsForest.toWellFoundedLT

instance (α : Type u) [IsForest α] (a : α) :
    IsTrichotomous { x // x < a } (. < .) where
  trichotomous := fun ⟨x, hx⟩ ⟨y, hy⟩ =>
    (IsForest.downset_trichot x y a hx hy).imp3 id Subtype.ext id

instance {α : Type u} [IsForest α] (a : α) :
    IsWellOrder { x // x < a } (. < .) where

instance {α : Type u} [DecidableEq α] [IsForest α] (a : α) :
    IsWellOrder { x // x ≤ a } (. < .) where
  trichotomous := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    by_cases h : x = a <;> by_cases h' : y = a
    . subst x; subst y; right; left; rfl
    . replace h' := @Subtype.ne_of_val_ne α (. ≤ a) ⟨y, hy⟩ ⟨a, le_refl a⟩ h'
      subst x; right; right; exact lt_of_le_of_ne hy h'
    . replace h := @Subtype.ne_of_val_ne α (. ≤ a) ⟨x, hx⟩ ⟨a, le_refl a⟩ h
      subst y; left; exact lt_of_le_of_ne hx h
    . have := IsForest.downset_trichot x y a (lt_of_le_of_ne hx h)
                                             (lt_of_le_of_ne hy h')
      simp only [Subrel, Order.Preimage, Subtype.mk.injEq] at this ⊢
      exact this

/--
A tree is a forest equipped with a minimum element.
-/
class IsTree (α : Type u) extends IsForest α, OrderBot α

instance {α} [LinearOrder α] [OrderBot α] [WellFoundedLT α] : IsTree α where
  toWellFoundedLT := inferInstance
  downset_trichot x y _ _ _ := IsTrichotomous.trichotomous x y

instance {α : Type u} [IsForest α] : IsTree (WithBot α) where
  toWellFoundedLT := inferInstance
  downset_trichot := by
    intro x y a hx hy
    cases' x with x <;> cases' y with y
    . simp only [lt_self_iff_false, or_false, or_true]
    . simp only [Subtype.mk_lt_mk, Subtype.mk.injEq, WithBot.not_lt_none, or_self, or_false]
      apply WithBot.none_lt_some
    . simp only [Subtype.mk_lt_mk, WithBot.not_lt_none, Subtype.mk.injEq, false_or]
      apply WithBot.none_lt_some
    . cases' a with a
      . exfalso; exact WithBot.not_lt_none _ hx
      simp only [WithBot.some_lt_some] at hx hy
      have := IsForest.downset_trichot x y a hx hy
      simp only [Subtype.mk_lt_mk, WithBot.some_lt_some, Subtype.mk.injEq] at this ⊢
      rw [Option.some_inj]
      exact this

instance {α : Type u} {β : Type v} [IsForest α] [IsForest β]
    : IsForest (α ⊕ β) where
  -- should extract both of these to somewhere else
  toWellFoundedLT := by
    constructor; constructor; rintro (x | x)
    <;> (induction x using WellFounded.induction;
         exact IsForest.toWellFoundedLT.wf)
    <;> constructor
    <;> intro _ h <;> cases h
    <;> apply_assumption
    <;> assumption
  downset_trichot := by
    intros x y a; revert x y; rcases a with (x | x)
    <;> intro s t hs ht
    <;> cases' hs with s _ hs s _ hs <;> cases' ht with t _ ht t _ ht
    <;> simp only [Subtype.mk_lt_mk, Subtype.mk.injEq, Sum.inl_lt_inl_iff,
                   Sum.inl.injEq, Sum.inr_lt_inr_iff, Sum.inr.injEq]
    <;> have := IsForest.downset_trichot s t x hs ht
    <;> simp only [Subtype.mk_lt_mk, WithBot.some_lt_some, Subtype.mk.injEq] at this
    <;> exact this
