/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.Monoid.Defs

/-!
# Ordered AddTorsors
This file defines ordered vector addition and proves some properties.  A motivating example is given
by the additive action of `ℤ` on subsets of reals that are closed under integer translation.  The
order compatibility allows for a treatment of the `R((z))`-module structure on `(z ^ s) V((z))` for
an `R`-module `V`, using the formalism of Hahn series.

## Implementation notes

We write our conditions as `Prop`-valued mixins.

## Definitions
* OrderedVAdd : inequalities are preserved by translation.
* CancelVAdd : the vector addition version of cancellative addition
* OrderedCancelVAdd : inequalities are preserved and reflected by translation.

## Instances
* OrderedAddCommMonoid.toOrderedVAdd
* OrderedVAdd.toCovariantClassLeft
* OrderedCancelVAdd.toCancelVAdd
* OrderedCancelAddCommMonoid.toOrderedCancelVAdd
* OrderedCancelVAdd.toContravariantClassLeft

## TODO
* `OrderedAddTorsor `: An additive torsor over an additive commutative group with compatible order.
* `Set.vAddAntidiagonal`
* (lex) prod instances
* Pi instances
* `vAddAntidiagonal.finite_of_isPWO`
* `Finset.vAddAntidiagonal`

-/

open Function

variable {G P : Type*}

/-- An ordered vector addition is a bi-monotone vector addition. -/
class OrderedVAdd (G P : Type*) [LE G] [LE P] [VAdd G P] : Prop where
  protected vadd_le_vadd_left : ∀ a b : P, a ≤ b → ∀ c : G, c +ᵥ a ≤ c +ᵥ b
  protected vadd_le_vadd_right : ∀ c d : G, c ≤ d → ∀ a : P, c +ᵥ a ≤ d +ᵥ a

instance OrderedAddCommMonoid.toOrderedVAdd [OrderedAddCommMonoid G] : OrderedVAdd G G where
  vadd_le_vadd_left _ _ := add_le_add_left
  vadd_le_vadd_right _ _ h a := add_le_add_right h a

instance OrderedVAdd.toCovariantClassLeft [LE G] [LE P] [VAdd G P] [OrderedVAdd G P] :
    CovariantClass G P (· +ᵥ ·) (· ≤ ·) where
  elim := fun a _ _ bc ↦ OrderedVAdd.vadd_le_vadd_left _ _ bc a

/-- A vector addition is cancellative if it is pointwise injective on the left and right. -/
class CancelVAdd (G P : Type*) [LE G] [LE P] [VAdd G P] : Prop where
  protected left_cancel : ∀ (a : G) (b c : P), a +ᵥ b = a +ᵥ c → b = c
  protected right_cancel : ∀ (a b : G) (c : P), a +ᵥ c = b +ᵥ c → a = b

/-- An ordered cancellative vector addition is an ordered vector addition that is cancellative. -/
class OrderedCancelVAdd (G P : Type*) [LE G] [LE P] [VAdd G P] extends OrderedVAdd G P : Prop where
  protected le_of_vadd_le_vadd_left : ∀ (a : G) (b c : P), a +ᵥ b ≤ a +ᵥ c → b ≤ c
  protected le_of_vadd_le_vadd_right : ∀ (a b : G) (c : P), a +ᵥ c ≤ b +ᵥ c → a ≤ b

instance OrderedCancelVAdd.toCancelVAdd [PartialOrder G] [PartialOrder P] [VAdd G P]
    [OrderedCancelVAdd G P] : CancelVAdd G P where
  left_cancel a b c h := (OrderedCancelVAdd.le_of_vadd_le_vadd_left a b c h.le).antisymm
    (OrderedCancelVAdd.le_of_vadd_le_vadd_left a c b h.ge)
  right_cancel a b c h := by
    refine (OrderedCancelVAdd.le_of_vadd_le_vadd_right a b c h.le).antisymm ?_
    exact (OrderedCancelVAdd.le_of_vadd_le_vadd_right b a c h.ge)

instance OrderedCancelAddCommMonoid.toOrderedCancelVAdd [OrderedCancelAddCommMonoid G] :
    OrderedCancelVAdd G G where
  le_of_vadd_le_vadd_left _ _ _ := le_of_add_le_add_left
  le_of_vadd_le_vadd_right _ _ _ := le_of_add_le_add_right

namespace VAdd

theorem vadd_lt_vadd_of_le_of_lt [LE G] [Preorder P] [VAdd G P] [OrderedCancelVAdd G P]
    {a b : G} {c d : P} (h₁ : a ≤ b) (h₂ : c < d) :
    a +ᵥ c < b +ᵥ d := by
  refine lt_of_le_of_lt (OrderedVAdd.vadd_le_vadd_right a b h₁ c) ?_
  refine lt_of_le_not_le (OrderedVAdd.vadd_le_vadd_left c d (le_of_lt h₂) b) ?_
  by_contra hbdc
  have h : d ≤ c := OrderedCancelVAdd.le_of_vadd_le_vadd_left b d c hbdc
  rw [@lt_iff_le_not_le] at h₂
  simp_all only [not_true_eq_false, and_false]

theorem vadd_lt_vadd_of_lt_of_le [Preorder G] [Preorder P] [VAdd G P] [OrderedCancelVAdd G P]
    {a b : G} {c d : P} (h₁ : a < b) (h₂ : c ≤ d) :
    a +ᵥ c < b +ᵥ d := by
  refine lt_of_le_of_lt (OrderedVAdd.vadd_le_vadd_left c d h₂ a) ?_
  refine lt_of_le_not_le (OrderedVAdd.vadd_le_vadd_right a b (le_of_lt h₁) d) ?_
  by_contra hbad
  have h : b ≤ a := OrderedCancelVAdd.le_of_vadd_le_vadd_right b a d hbad
  rw [@lt_iff_le_not_le] at h₁
  simp_all only [not_true_eq_false, and_false]

end VAdd

instance (priority := 200) OrderedCancelVAdd.toContravariantClassLeLeft [LE G]
    [LE P] [VAdd G P] [OrderedCancelVAdd G P] : ContravariantClass G P (· +ᵥ ·) (· ≤ ·) :=
  ⟨OrderedCancelVAdd.le_of_vadd_le_vadd_left⟩
