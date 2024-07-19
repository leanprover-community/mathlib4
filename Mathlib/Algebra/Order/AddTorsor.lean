/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.Monoid.Defs

/-!
# Ordered scalar multiplication and vector addition
This file defines ordered scalar multiplication and vector addition, and proves some properties.
In the additive case, a motivating example is given by the additive action of `ℤ` on subsets of
reals that are closed under integer translation.  The order compatibility allows for a treatment of
the `R((z))`-module structure on `(z ^ s) V((z))` for an `R`-module `V`, using the formalism of Hahn
series.  In the multiplicative case, a standard example is the action of non-negative rationals on
an ordered field.

## Implementation notes

* Beause these classes mix the algebra and order hierarchies, we write them as `Prop`-valued mixins.
* Despite the file name, Ordered AddTorsors are not defined as a separate class.  To implement them,
  combine `[AddTorsor G P]` with `[IsOrderedCancelVAdd G P]`

## Definitions
* IsOrderedSMul : inequalities are preserved by scalar multiplication.
* IsOrderedVAdd : inequalities are preserved by translation.
* IsCancelSMul : the scalar multiplication version of cancellative multiplication
* IsCancelVAdd : the vector addition version of cancellative addition
* IsOrderedCancelSMul : inequalities are preserved and reflected by scalar multiplication.
* IsOrderedCancelVAdd : inequalities are preserved and reflected by translation.
* SMul.antidiagonal : Set-valued antidiagonal for SMul.
* VAdd.antidiagonal : Set-valued antidiagonal for VAdd.
* Finset.SMulAntidiagonal : Finset antidiagonal for PWO inputs.
* Finset.VAddAntidiagonal : Finset antidiagonal for PWO inputs.

## Instances
* OrderedCommMonoid.toIsOrderedSMul
* OrderedAddCommMonoid.toIsOrderedVAdd
* IsOrderedSMul.toCovariantClassLeft
* IsOrderedVAdd.toCovariantClassLeft
* IsOrderedCancelSMul.toCancelSMul
* IsOrderedCancelVAdd.toCancelVAdd
* OrderedCancelCommMonoid.toIsOrderedCancelSMul
* OrderedCancelAddCommMonoid.toIsOrderedCancelVAdd
* IsOrderedCancelSMul.toContravariantClassLeft
* IsOrderedCancelVAdd.toContravariantClassLeft

## TODO
* (lex) prod instances
* Pi instances
* WithTop

-/

open Function

variable {G P : Type*}

/-- An ordered vector addition is a bi-monotone vector addition. -/
class IsOrderedVAdd (G P : Type*) [LE G] [LE P] [VAdd G P] : Prop where
  protected vadd_le_vadd_left : ∀ a b : P, a ≤ b → ∀ c : G, c +ᵥ a ≤ c +ᵥ b
  protected vadd_le_vadd_right : ∀ c d : G, c ≤ d → ∀ a : P, c +ᵥ a ≤ d +ᵥ a

@[deprecated (since := "2024-07-15")] alias OrderedVAdd := IsOrderedVAdd

/-- An ordered scalar multiplication is a bi-monotone scalar multiplication. Note that this is
different from `OrderedSMul`, which uses strict inequality, requires `G` to be a semiring, and the
defining conditions are restricted to positive elements of `G`. -/
@[to_additive]
class IsOrderedSMul (G P : Type*) [LE G] [LE P] [SMul G P] : Prop where
  protected smul_le_smul_left : ∀ a b : P, a ≤ b → ∀ c : G, c • a ≤ c • b
  protected smul_le_smul_right : ∀ c d : G, c ≤ d → ∀ a : P, c • a ≤ d • a

@[to_additive]
instance [LE G] [LE P] [SMul G P] [IsOrderedSMul G P] : CovariantClass G P (· • ·) (· ≤ ·) where
  elim := fun a _ _ bc ↦ IsOrderedSMul.smul_le_smul_left _ _ bc a

@[to_additive]
instance [OrderedCommMonoid G] : IsOrderedSMul G G where
  smul_le_smul_left _ _ := mul_le_mul_left'
  smul_le_smul_right _ _ := mul_le_mul_right'

@[to_additive]
theorem IsOrderedSMul.smul_le_smul [Preorder G] [Preorder P] [SMul G P] [IsOrderedSMul G P]
    {a b : G} {c d : P} (hab : a ≤ b) (hcd : c ≤ d) : a • c ≤ b • d :=
  (IsOrderedSMul.smul_le_smul_left _ _ hcd _).trans (IsOrderedSMul.smul_le_smul_right _ _ hab _)

/-- A vector addition is cancellative if it is pointwise injective on the left and right. -/
class IsCancelVAdd (G P : Type*) [VAdd G P] : Prop where
  protected left_cancel : ∀ (a : G) (b c : P), a +ᵥ b = a +ᵥ c → b = c
  protected right_cancel : ∀ (a b : G) (c : P), a +ᵥ c = b +ᵥ c → a = b

@[deprecated (since := "2024-07-15")] alias CancelVAdd := IsCancelVAdd

/-- A scalar multiplication is cancellative if it is pointwise injective on the left and right. -/
@[to_additive]
class IsCancelSMul (G P : Type*) [SMul G P] : Prop where
  protected left_cancel : ∀ (a : G) (b c : P), a • b = a • c → b = c
  protected right_cancel : ∀ (a b : G) (c : P), a • c = b • c → a = b

/-- An ordered cancellative vector addition is an ordered vector addition that is cancellative. -/
class IsOrderedCancelVAdd (G P : Type*) [LE G] [LE P] [VAdd G P] extends
    IsOrderedVAdd G P : Prop where
  protected le_of_vadd_le_vadd_left : ∀ (a : G) (b c : P), a +ᵥ b ≤ a +ᵥ c → b ≤ c
  protected le_of_vadd_le_vadd_right : ∀ (a b : G) (c : P), a +ᵥ c ≤ b +ᵥ c → a ≤ b

@[deprecated (since := "2024-07-15")] alias OrderedCancelVAdd := IsOrderedCancelVAdd

/-- An ordered cancellative scalar multiplication is an ordered scalar multiplication that is
  cancellative. -/
@[to_additive]
class IsOrderedCancelSMul (G P : Type*) [LE G] [LE P] [SMul G P] extends
    IsOrderedSMul G P : Prop where
  protected le_of_smul_le_smul_left : ∀ (a : G) (b c : P), a • b ≤ a • c → b ≤ c
  protected le_of_smul_le_smul_right : ∀ (a b : G) (c : P), a • c ≤ b • c → a ≤ b

@[to_additive]
instance [PartialOrder G] [PartialOrder P] [SMul G P] [IsOrderedCancelSMul G P] :
    IsCancelSMul G P where
  left_cancel a b c h := (IsOrderedCancelSMul.le_of_smul_le_smul_left a b c h.le).antisymm
    (IsOrderedCancelSMul.le_of_smul_le_smul_left a c b h.ge)
  right_cancel a b c h := (IsOrderedCancelSMul.le_of_smul_le_smul_right a b c h.le).antisymm
    (IsOrderedCancelSMul.le_of_smul_le_smul_right b a c h.ge)

@[to_additive]
instance [OrderedCancelCommMonoid G] : IsOrderedCancelSMul G G where
  le_of_smul_le_smul_left _ _ _ := le_of_mul_le_mul_left'
  le_of_smul_le_smul_right _ _ _ := le_of_mul_le_mul_right'

@[to_additive]
instance (priority := 200) [LE G] [LE P] [SMul G P] [IsOrderedCancelSMul G P] :
    ContravariantClass G P (· • ·) (· ≤ ·) :=
  ⟨IsOrderedCancelSMul.le_of_smul_le_smul_left⟩

/-- The vector sum of two monotone functions is monotone. -/
@[to_additive]
theorem Monotone.SMul {γ : Type*} [Preorder G] [Preorder P] [Preorder γ] [SMul G P]
    [IsOrderedSMul G P] {f : γ → G} {g : γ → P} (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x • g x :=
  fun _ _ hab => (IsOrderedSMul.smul_le_smul_left _ _ (hg hab) _).trans
    (IsOrderedSMul.smul_le_smul_right _ _ (hf hab) _)
