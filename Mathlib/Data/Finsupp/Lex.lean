/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.DFinsupp.Lex
import Mathlib.Data.Finsupp.ToDFinsupp

#align_import data.finsupp.lex from "leanprover-community/mathlib"@"dc6c365e751e34d100e80fe6e314c3c3e0fd2988"

/-!
# Lexicographic order on finitely supported functions

This file defines the lexicographic order on `Finsupp`.
-/


variable {α N : Type*}

namespace Finsupp

section NHasZero

variable [Zero N]

/-- `Finsupp.Lex r s` is the lexicographic relation on `α →₀ N`, where `α` is ordered by `r`,
and `N` is ordered by `s`.

The type synonym `Lex (α →₀ N)` has an order given by `Finsupp.Lex (· < ·) (· < ·)`.
-/
protected def Lex (r : α → α → Prop) (s : N → N → Prop) (x y : α →₀ N) : Prop :=
  Pi.Lex r s x y
#align finsupp.lex Finsupp.Lex

-- Porting note: Added `_root_` to better align with Lean 3.
theorem _root_.Pi.lex_eq_finsupp_lex {r : α → α → Prop} {s : N → N → Prop} (a b : α →₀ N) :
    Pi.Lex r s a b = Finsupp.Lex r s a b :=
  rfl
#align pi.lex_eq_finsupp_lex Pi.lex_eq_finsupp_lex

theorem lex_def {r : α → α → Prop} {s : N → N → Prop} {a b : α →₀ N} :
    Finsupp.Lex r s a b ↔ ∃ j, (∀ d, r d j → a d = b d) ∧ s (a j) (b j) :=
  Iff.rfl
#align finsupp.lex_def Finsupp.lex_def

theorem lex_eq_invImage_dfinsupp_lex (r : α → α → Prop) (s : N → N → Prop) :
    Finsupp.Lex r s = InvImage (DFinsupp.Lex r fun _ ↦ s) toDFinsupp :=
  rfl
#align finsupp.lex_eq_inv_image_dfinsupp_lex Finsupp.lex_eq_invImage_dfinsupp_lex

instance [LT α] [LT N] : LT (Lex (α →₀ N)) :=
  ⟨fun f g ↦ Finsupp.Lex (· < ·) (· < ·) (ofLex f) (ofLex g)⟩

theorem lex_lt_of_lt_of_preorder [Preorder N] (r) [IsStrictOrder α r] {x y : α →₀ N} (hlt : x < y) :
    ∃ i, (∀ j, r j i → x j ≤ y j ∧ y j ≤ x j) ∧ x i < y i :=
  DFinsupp.lex_lt_of_lt_of_preorder r (id hlt : x.toDFinsupp < y.toDFinsupp)
#align finsupp.lex_lt_of_lt_of_preorder Finsupp.lex_lt_of_lt_of_preorder

theorem lex_lt_of_lt [PartialOrder N] (r) [IsStrictOrder α r] {x y : α →₀ N} (hlt : x < y) :
    Pi.Lex r (· < ·) x y :=
  DFinsupp.lex_lt_of_lt r (id hlt : x.toDFinsupp < y.toDFinsupp)
#align finsupp.lex_lt_of_lt Finsupp.lex_lt_of_lt

instance Lex.isStrictOrder [LinearOrder α] [PartialOrder N] :
    IsStrictOrder (Lex (α →₀ N)) (· < ·) :=
  let i : IsStrictOrder (Lex (α → N)) (· < ·) := Pi.Lex.isStrictOrder
  { irrefl := toLex.surjective.forall.2 fun _ ↦ @irrefl _ _ i.toIsIrrefl _
    trans := toLex.surjective.forall₃.2 fun _ _ _ ↦ @trans _ _ i.toIsTrans _ _ _ }
#align finsupp.lex.is_strict_order Finsupp.Lex.isStrictOrder

variable [LinearOrder α]

/-- The partial order on `Finsupp`s obtained by the lexicographic ordering.
See `Finsupp.Lex.linearOrder` for a proof that this partial order is in fact linear. -/
instance Lex.partialOrder [PartialOrder N] : PartialOrder (Lex (α →₀ N)) where
  lt := (· < ·)
  le x y := ⇑(ofLex x) = ⇑(ofLex y) ∨ x < y
  __ := PartialOrder.lift (fun x : Lex (α →₀ N) ↦ toLex (⇑(ofLex x)))
    (DFunLike.coe_injective (F := Finsupp α N))
#align finsupp.lex.partial_order Finsupp.Lex.partialOrder

/-- The linear order on `Finsupp`s obtained by the lexicographic ordering. -/
instance Lex.linearOrder [LinearOrder N] : LinearOrder (Lex (α →₀ N)) where
  lt := (· < ·)
  le := (· ≤ ·)
  __ := LinearOrder.lift' (toLex ∘ toDFinsupp ∘ ofLex) finsuppEquivDFinsupp.injective
#align finsupp.lex.linear_order Finsupp.Lex.linearOrder

variable [PartialOrder N]

theorem toLex_monotone : Monotone (@toLex (α →₀ N)) :=
  fun a b h ↦ DFinsupp.toLex_monotone (id h : ∀ i, ofLex (toDFinsupp a) i ≤ ofLex (toDFinsupp b) i)
#align finsupp.to_lex_monotone Finsupp.toLex_monotone

theorem lt_of_forall_lt_of_lt (a b : Lex (α →₀ N)) (i : α) :
    (∀ j < i, ofLex a j = ofLex b j) → ofLex a i < ofLex b i → a < b :=
  fun h1 h2 ↦ ⟨i, h1, h2⟩
#align finsupp.lt_of_forall_lt_of_lt Finsupp.lt_of_forall_lt_of_lt

end NHasZero

section Covariants

variable [LinearOrder α] [AddMonoid N] [LinearOrder N]

/-!  We are about to sneak in a hypothesis that might appear to be too strong.
We assume `CovariantClass` with *strict* inequality `<` also when proving the one with the
*weak* inequality `≤`.  This is actually necessary: addition on `Lex (α →₀ N)` may fail to be
monotone, when it is "just" monotone on `N`.

See `Counterexamples/ZeroDivisorsInAddMonoidAlgebras.lean` for a counterexample. -/


section Left

variable [CovariantClass N N (· + ·) (· < ·)]

instance Lex.covariantClass_lt_left :
    CovariantClass (Lex (α →₀ N)) (Lex (α →₀ N)) (· + ·) (· < ·) :=
  ⟨fun _ _ _ ⟨a, lta, ha⟩ ↦ ⟨a, fun j ja ↦ congr_arg _ (lta j ja), add_lt_add_left ha _⟩⟩
#align finsupp.lex.covariant_class_lt_left Finsupp.Lex.covariantClass_lt_left

instance Lex.covariantClass_le_left :
    CovariantClass (Lex (α →₀ N)) (Lex (α →₀ N)) (· + ·) (· ≤ ·) :=
  covariantClass_le_of_lt _ _ _
#align finsupp.lex.covariant_class_le_left Finsupp.Lex.covariantClass_le_left

end Left

section Right

variable [CovariantClass N N (Function.swap (· + ·)) (· < ·)]

instance Lex.covariantClass_lt_right :
    CovariantClass (Lex (α →₀ N)) (Lex (α →₀ N)) (Function.swap (· + ·)) (· < ·) :=
  ⟨fun f _ _ ⟨a, lta, ha⟩ ↦
    ⟨a, fun j ja ↦ congr_arg (· + ofLex f j) (lta j ja), add_lt_add_right ha _⟩⟩
#align finsupp.lex.covariant_class_lt_right Finsupp.Lex.covariantClass_lt_right

instance Lex.covariantClass_le_right :
    CovariantClass (Lex (α →₀ N)) (Lex (α →₀ N)) (Function.swap (· + ·)) (· ≤ ·) :=
  covariantClass_le_of_lt _ _ _
#align finsupp.lex.covariant_class_le_right Finsupp.Lex.covariantClass_le_right

end Right

end Covariants

section OrderedAddMonoid

variable [LinearOrder α]

instance Lex.orderBot [CanonicallyOrderedAddCommMonoid N] : OrderBot (Lex (α →₀ N)) where
  bot := 0
  bot_le _ := Finsupp.toLex_monotone bot_le

noncomputable instance Lex.orderedAddCancelCommMonoid [OrderedCancelAddCommMonoid N] :
    OrderedCancelAddCommMonoid (Lex (α →₀ N)) where
  add_le_add_left _ _ h _ := add_le_add_left (α := Lex (α → N)) h _
  le_of_add_le_add_left _ _ _ := le_of_add_le_add_left (α := Lex (α → N))

noncomputable instance Lex.orderedAddCommGroup [OrderedAddCommGroup N] :
    OrderedAddCommGroup (Lex (α →₀ N)) where
  add_le_add_left _ _ := add_le_add_left

noncomputable instance Lex.linearOrderedCancelAddCommMonoid [LinearOrderedCancelAddCommMonoid N] :
    LinearOrderedCancelAddCommMonoid (Lex (α →₀ N)) where
  __ : LinearOrder (Lex (α →₀ N)) := inferInstance
  __ : OrderedCancelAddCommMonoid (Lex (α →₀ N)) := inferInstance

noncomputable instance Lex.linearOrderedAddCommGroup [LinearOrderedAddCommGroup N] :
    LinearOrderedAddCommGroup (Lex (α →₀ N)) where
  __ : LinearOrder (Lex (α →₀ N)) := inferInstance
  add_le_add_left _ _ := add_le_add_left

end OrderedAddMonoid

end Finsupp
