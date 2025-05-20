/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Data.Prod.RevLex

/-!
# Ordered scalar multiplication and vector addition
This file defines ordered scalar multiplication and vector addition, and proves some properties.
In the additive case, a motivating example is given by the additive action of `ℤ` on subsets of
reals that are closed under integer translation.  The order compatibility allows for a treatment of
the `R((z))`-module structure on `(z ^ s) V((z))` for an `R`-module `V`, using the formalism of Hahn
series.  In the multiplicative case, a standard example is the action of non-negative rationals on
an ordered field.

## Implementation notes
* Because these classes mix the algebra and order hierarchies, we write them as `Prop`-valued
  mixins.
* Despite the file name, Ordered AddTorsors are not defined as a separate class.  To implement them,
  combine `[AddTorsor G P]` with `[IsOrderedCancelVAdd G P]`

## Definitions
* IsOrderedSMul : inequalities are preserved by scalar multiplication.
* IsOrderedVAdd : inequalities are preserved by translation.
* IsCancelSMul : the scalar multiplication version of cancellative multiplication
* IsCancelVAdd : the vector addition version of cancellative addition
* IsOrderedCancelSMul : inequalities are preserved and reflected by scalar multiplication.
* IsOrderedCancelVAdd : inequalities are preserved and reflected by translation.

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
* WithTop (in a different file?)
-/

open Function

variable {G P : Type*}

/-- An ordered vector addition is a bi-monotone vector addition. -/
class IsOrderedVAdd (G P : Type*) [LE G] [LE P] [VAdd G P] : Prop where
  protected vadd_le_vadd_left : ∀ a b : P, a ≤ b → ∀ c : G, c +ᵥ a ≤ c +ᵥ b
  protected vadd_le_vadd_right : ∀ c d : G, c ≤ d → ∀ a : P, c +ᵥ a ≤ d +ᵥ a

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
instance [CommMonoid G] [PartialOrder G] [IsOrderedMonoid G] : IsOrderedSMul G G where
  smul_le_smul_left _ _ := mul_le_mul_left'
  smul_le_smul_right _ _ := mul_le_mul_right'

@[to_additive]
theorem IsOrderedSMul.smul_le_smul [LE G] [Preorder P] [SMul G P] [IsOrderedSMul G P]
    {a b : G} {c d : P} (hab : a ≤ b) (hcd : c ≤ d) : a • c ≤ b • d :=
  (IsOrderedSMul.smul_le_smul_left _ _ hcd _).trans (IsOrderedSMul.smul_le_smul_right _ _ hab _)

@[to_additive]
theorem Monotone.smul {G : Type*} [Preorder G] [Preorder P] [SMul G P]
    [IsOrderedSMul G P] {f : G → G} {g : G → P} (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x • g x :=
  fun _ _ hab => (IsOrderedSMul.smul_le_smul_left _ _ (hg hab) _).trans
    (IsOrderedSMul.smul_le_smul_right _ _ (hf hab) _)

/-- A vector addition is cancellative if it is pointwise injective on the left and right. -/
class IsCancelVAdd (G P : Type*) [VAdd G P] : Prop where
  protected left_cancel : ∀ (a : G) (b c : P), a +ᵥ b = a +ᵥ c → b = c
  protected right_cancel : ∀ (a b : G) (c : P), a +ᵥ c = b +ᵥ c → a = b

/-- A scalar multiplication is cancellative if it is pointwise injective on the left and right. -/
@[to_additive]
class IsCancelSMul (G P : Type*) [SMul G P] : Prop where
  protected left_cancel : ∀ (a : G) (b c : P), a • b = a • c → b = c
  protected right_cancel : ∀ (a b : G) (c : P), a • c = b • c → a = b

/-- An ordered cancellative vector addition is an ordered vector addition that is cancellative. -/
class IsOrderedCancelVAdd (G P : Type*) [LE G] [LE P] [VAdd G P] : Prop
    extends IsOrderedVAdd G P where
  protected le_of_vadd_le_vadd_left : ∀ (a : G) (b c : P), a +ᵥ b ≤ a +ᵥ c → b ≤ c
  protected le_of_vadd_le_vadd_right : ∀ (a b : G) (c : P), a +ᵥ c ≤ b +ᵥ c → a ≤ b

/-- An ordered cancellative scalar multiplication is an ordered scalar multiplication that is
  cancellative. -/
@[to_additive]
class IsOrderedCancelSMul (G P : Type*) [LE G] [LE P] [SMul G P] : Prop
    extends IsOrderedSMul G P where
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
instance [CommMonoid G] [PartialOrder G] [IsOrderedCancelMonoid G] : IsOrderedCancelSMul G G where
  le_of_smul_le_smul_left _ _ _ := le_of_mul_le_mul_left'
  le_of_smul_le_smul_right _ _ _ := le_of_mul_le_mul_right'

@[to_additive]
instance (priority := 200) [LE G] [LE P] [SMul G P] [IsOrderedCancelSMul G P] :
    ContravariantClass G P (· • ·) (· ≤ ·) :=
  ⟨IsOrderedCancelSMul.le_of_smul_le_smul_left⟩

namespace SMul

@[to_additive]
theorem smul_lt_smul_of_le_of_lt [LE G] [Preorder P] [SMul G P] [IsOrderedCancelSMul G P]
    {a b : G} {c d : P} (h₁ : a ≤ b) (h₂ : c < d) :
  a • c < b • d := by
  refine lt_of_le_of_lt (IsOrderedSMul.smul_le_smul_right a b h₁ c) ?_
  refine lt_of_le_not_le (IsOrderedSMul.smul_le_smul_left c d (le_of_lt h₂) b) ?_
  by_contra hbdc
  have h : d ≤ c := IsOrderedCancelSMul.le_of_smul_le_smul_left b d c hbdc
  rw [@lt_iff_le_not_le] at h₂
  simp_all only [not_true_eq_false, and_false]

@[to_additive]
theorem smul_lt_smul_of_lt_of_le [Preorder G] [Preorder P] [SMul G P] [IsOrderedCancelSMul G P]
    {a b : G} {c d : P} (h₁ : a < b) (h₂ : c ≤ d) : a • c < b • d := by
  refine lt_of_le_of_lt (IsOrderedSMul.smul_le_smul_left c d h₂ a) ?_
  refine lt_of_le_not_le (IsOrderedSMul.smul_le_smul_right a b (le_of_lt h₁) d) ?_
  by_contra hbad
  have h : b ≤ a := IsOrderedCancelSMul.le_of_smul_le_smul_right b a d hbad
  rw [@lt_iff_le_not_le] at h₁
  simp_all only [not_true_eq_false, and_false]

@[to_additive]
theorem lt_of_smul_lt_smul_left [PartialOrder G] [PartialOrder P] [SMul G P]
    [IsOrderedCancelSMul G P] {a : G} {b c : P} (h₁ : a • b < a • c) :
    b < c := by
  refine lt_of_le_of_ne (IsOrderedCancelSMul.le_of_smul_le_smul_left a b c (le_of_lt h₁)) ?_
  contrapose! h₁
  rw [h₁]
  exact gt_irrefl (a • c)

@[to_additive]
theorem lt_of_smul_lt_smul_right [PartialOrder G] [PartialOrder P] [SMul G P]
    [IsOrderedCancelSMul G P] {a b : G} {c : P} (h₁ : a • c < b • c) : a < b := by
  refine lt_of_le_of_ne (IsOrderedCancelSMul.le_of_smul_le_smul_right a b c (le_of_lt h₁)) ?_
  contrapose! h₁
  rw [h₁]
  exact gt_irrefl (b • c)

end SMul

namespace Prod.Lex

variable {G G₁ P₁ P₂ : Type*}

instance [VAdd G P₁] [VAdd G₁ P₂] : VAdd (G ×ₗ G₁) (P₁ ×ₗ P₂) where
  vadd g h := toLex ((ofLex g).1 +ᵥ (ofLex h).1, (ofLex g).2 +ᵥ (ofLex h).2)

theorem vadd_eq [VAdd G P₁] [VAdd G₁ P₂] (g : G ×ₗ G₁) (h : P₁ ×ₗ P₂) :
    g +ᵥ h = toLex ((ofLex g).1 +ᵥ (ofLex h).1, (ofLex g).2 +ᵥ (ofLex h).2) := rfl

instance [AddMonoid G] [AddMonoid G₁] [AddAction G P₁] [AddAction G₁ P₂] :
    AddAction (G ×ₗ G₁) (P₁ ×ₗ P₂) where
  zero_vadd x := by simp [vadd_eq]
  add_vadd x y z := by simp [vadd_eq, add_vadd]

instance [PartialOrder G] [PartialOrder G₁] [PartialOrder P₁] [VAdd G P₁]
    [IsOrderedCancelVAdd G P₁] [PartialOrder P₂] [VAdd G₁ P₂] [IsOrderedCancelVAdd G₁ P₂] :
    IsOrderedCancelVAdd (G ×ₗ G₁) (P₁ ×ₗ P₂) where
  vadd_le_vadd_left a b h c := by
    obtain h₁ | ⟨h₂, h₃⟩ := Prod.Lex.le_iff.mp h
    · exact Prod.Lex.le_iff.mpr <| Or.inl <|
        by simpa using (VAdd.vadd_lt_vadd_of_le_of_lt (Preorder.le_refl (ofLex c).1) h₁)
    · refine Prod.Lex.le_iff.mpr <| Or.inr <| ⟨?_, ?_⟩
      · simpa using (congrArg (HVAdd.hVAdd (ofLex c).1) h₂)
      · simpa using (IsOrderedVAdd.vadd_le_vadd_left (ofLex a).2 (ofLex b).2 h₃ (ofLex c).2)
  vadd_le_vadd_right a b h c := by
    obtain h₁ | ⟨h₂, h₃⟩ := Prod.Lex.le_iff.mp h
    · exact Prod.Lex.le_iff.mpr <| Or.inl <|
        by simpa using (VAdd.vadd_lt_vadd_of_lt_of_le h₁ (Preorder.le_refl (ofLex c).1))
    · refine Prod.Lex.le_iff.mpr <| Or.inr <| ⟨?_, ?_⟩
      · simpa using congrFun (congrArg HVAdd.hVAdd h₂) (ofLex c).1
      · simpa using (IsOrderedVAdd.vadd_le_vadd_right (ofLex a).2 (ofLex b).2 h₃ (ofLex c).2)
  le_of_vadd_le_vadd_left a b c h := by
    obtain h₁ | ⟨h₂, h₃⟩ := Prod.Lex.le_iff.mp h
    · exact Prod.Lex.le_iff.mpr <| Or.inl <| VAdd.lt_of_vadd_lt_vadd_left h₁
    · refine Prod.Lex.le_iff.mpr <| Or.inr <| ⟨IsCancelVAdd.left_cancel _ _ _ h₂, ?_⟩
      exact IsOrderedCancelVAdd.le_of_vadd_le_vadd_left (ofLex a).2 (ofLex b).2 (ofLex c).2 h₃
  le_of_vadd_le_vadd_right a b c h := by
    obtain h₁ | ⟨h₂, h₃⟩ := Prod.Lex.le_iff.mp h
    · refine Prod.Lex.le_iff.mpr <| Or.inl <| VAdd.lt_of_vadd_lt_vadd_right h₁
    · refine Prod.Lex.le_iff.mpr <| Or.inr <| ⟨IsCancelVAdd.right_cancel _ _ _ h₂, ?_⟩
      exact IsOrderedCancelVAdd.le_of_vadd_le_vadd_right (ofLex a).2 (ofLex b).2 (ofLex c).2 h₃

end Prod.Lex

namespace Prod.RevLex

variable {G G₁ P₁ P₂ : Type*}

instance [VAdd G P₁] [VAdd G₁ P₂] : VAdd (G ×ᵣ G₁) (P₁ ×ᵣ P₂) where
  vadd g h := toRevLex ((ofRevLex g).1 +ᵥ (ofRevLex h).1, (ofRevLex g).2 +ᵥ (ofRevLex h).2)

theorem vadd_eq [VAdd G P₁] [VAdd G₁ P₂] (g : G ×ᵣ G₁) (h : P₁ ×ᵣ P₂) :
    g +ᵥ h = toRevLex ((ofRevLex g).1 +ᵥ (ofRevLex h).1, (ofRevLex g).2 +ᵥ (ofRevLex h).2) := rfl

instance [AddMonoid G] [AddMonoid G₁] [AddAction G P₁] [AddAction G₁ P₂] :
    AddAction (G ×ᵣ G₁) (P₁ ×ᵣ P₂) where
  zero_vadd x := by simp [vadd_eq]
  add_vadd x y z := by simp [vadd_eq, add_vadd]

instance [PartialOrder G] [PartialOrder G₁] [PartialOrder P₁] [VAdd G P₁]
    [IsOrderedCancelVAdd G P₁] [PartialOrder P₂] [VAdd G₁ P₂] [IsOrderedCancelVAdd G₁ P₂] :
    IsOrderedCancelVAdd (G ×ᵣ G₁) (P₁ ×ᵣ P₂) where
  vadd_le_vadd_left a b h c := by
    obtain h₁ | ⟨h₂, h₃⟩ := Prod.RevLex.le_iff.mp h
    · refine Prod.RevLex.le_iff.mpr <| Or.inl <| by simpa using (VAdd.vadd_lt_vadd_of_le_of_lt
        (Preorder.le_refl (ofRevLex c).2) h₁)
    · refine Prod.RevLex.le_iff.mpr <| Or.inr <| ⟨?_, ?_⟩
      · simpa using (congrArg (HVAdd.hVAdd (ofRevLex c).2) h₂)
      · simpa using (IsOrderedVAdd.vadd_le_vadd_left
          (ofRevLex a).1 (ofRevLex b).1 h₃ (ofRevLex c).1)
  vadd_le_vadd_right a b h c := by
    obtain h₁ | ⟨h₂, h₃⟩ := Prod.RevLex.le_iff.mp h
    · exact Prod.RevLex.le_iff.mpr <| Or.inl <|
        by simpa using (VAdd.vadd_lt_vadd_of_lt_of_le h₁ (Preorder.le_refl (ofRevLex c).2))
    · refine Prod.RevLex.le_iff.mpr <| Or.inr <| ⟨?_, ?_⟩
      · simpa using congrFun (congrArg HVAdd.hVAdd h₂) (ofRevLex c).2
      · simpa using (IsOrderedVAdd.vadd_le_vadd_right
          (ofRevLex a).1 (ofRevLex b).1 h₃ (ofRevLex c).1)
  le_of_vadd_le_vadd_left a b c h := by
    obtain h₁ | ⟨h₂, h₃⟩ := Prod.RevLex.le_iff.mp h
    · exact Prod.RevLex.le_iff.mpr <| Or.inl <| VAdd.lt_of_vadd_lt_vadd_left h₁
    · refine Prod.RevLex.le_iff.mpr <| Or.inr <| ⟨IsCancelVAdd.left_cancel _ _ _ h₂, ?_⟩
      exact IsOrderedCancelVAdd.le_of_vadd_le_vadd_left
          (ofRevLex a).1 (ofRevLex b).1 (ofRevLex c).1 h₃
  le_of_vadd_le_vadd_right a b c h := by
    obtain h₁ | ⟨h₂, h₃⟩ := Prod.RevLex.le_iff.mp h
    · refine Prod.RevLex.le_iff.mpr <| Or.inl <| VAdd.lt_of_vadd_lt_vadd_right h₁
    · refine Prod.RevLex.le_iff.mpr <| Or.inr <| ⟨IsCancelVAdd.right_cancel _ _ _ h₂, ?_⟩
      exact IsOrderedCancelVAdd.le_of_vadd_le_vadd_right
        (ofRevLex a).1 (ofRevLex b).1 (ofRevLex c).1 h₃

theorem lexEquiv_vadd [PartialOrder G] [PartialOrder G₁] [PartialOrder P₁] [VAdd G P₁]
    [PartialOrder P₂] [VAdd G₁ P₂] (x : Lex (G × G₁)) (y : Lex (P₁ × P₂)) :
    (Prod.RevLex.lexEquiv P₁ P₂) (x +ᵥ y) =
      (Prod.RevLex.lexEquiv G G₁) x +ᵥ (Prod.RevLex.lexEquiv P₁ P₂) y := by
  simp [lexEquiv, vadd_eq, Prod.Lex.vadd_eq]

end Prod.RevLex
