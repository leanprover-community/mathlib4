/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Data.Prod.RevLex
import Mathlib.GroupTheory.GroupAction.Hom

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
  refine lt_of_le_not_ge (IsOrderedSMul.smul_le_smul_left c d (le_of_lt h₂) b) ?_
  by_contra hbdc
  have h : d ≤ c := IsOrderedCancelSMul.le_of_smul_le_smul_left b d c hbdc
  rw [@lt_iff_le_not_ge] at h₂
  simp_all only [not_true_eq_false, and_false]

@[to_additive]
theorem smul_lt_smul_of_lt_of_le [Preorder G] [Preorder P] [SMul G P] [IsOrderedCancelSMul G P]
    {a b : G} {c d : P} (h₁ : a < b) (h₂ : c ≤ d) : a • c < b • d := by
  refine lt_of_le_of_lt (IsOrderedSMul.smul_le_smul_left c d h₂ a) ?_
  refine lt_of_le_not_ge (IsOrderedSMul.smul_le_smul_right a b (le_of_lt h₁) d) ?_
  by_contra hbad
  have h : b ≤ a := IsOrderedCancelSMul.le_of_smul_le_smul_right b a d hbad
  rw [@lt_iff_le_not_ge] at h₁
  simp_all only [not_true_eq_false, and_false]

@[to_additive]
theorem lt_of_smul_lt_smul_left [PartialOrder G] [PartialOrder P] [SMul G P]
    [IsOrderedCancelSMul G P] {a : G} {b c : P} (h₁ : a • b < a • c) :
    b < c := by
  refine lt_of_le_of_ne (IsOrderedCancelSMul.le_of_smul_le_smul_left a b c (le_of_lt h₁)) ?_
  contrapose! h₁
  rw [h₁]
  exact lt_irrefl (a • c)

@[to_additive]
theorem lt_of_smul_lt_smul_right [PartialOrder G] [PartialOrder P] [SMul G P]
    [IsOrderedCancelSMul G P] {a b : G} {c : P} (h₁ : a • c < b • c) : a < b := by
  refine lt_of_le_of_ne (IsOrderedCancelSMul.le_of_smul_le_smul_right a b c (le_of_lt h₁)) ?_
  contrapose! h₁
  rw [h₁]
  exact lt_irrefl (b • c)

end SMul


section MulActionEquiv

variable {M' : Type*}
variable {M : Type*} {N : Type*} {P : Type*}
variable (φ : M ≃ N) (ψ : N ≃ P) (χ : M ≃ P)
variable (X : Type*) [LE X] [SMul M X] [SMul M' X]
variable (Y : Type*) [LE Y] [SMul N Y] [SMul M' Y]
variable (Z : Type*) [LE Z] [SMul P Z]

/-- Equivariant functions :
When `φ : M ≃ N` is an equivalence, and types `X` and `Y` are endowed with additive actions
of `M` and `N`, an equivalence `f : X ≃ Y` is `φ`-equivariant if `f (m +ᵥ x) = (φ m) +ᵥ (f x)`. -/
structure OrderedAddActionEquiv (φ : M ≃ N) (X : Type*) [LE X] [VAdd M X] (Y : Type*) [LE Y]
    [VAdd N Y] where
  /-- The underlying function. -/
  protected toEquiv : X ≃o Y
  /-- The proposition that the function commutes with the additive actions. -/
  protected map_vadd' : ∀ (m : M) (x : X), toEquiv (m +ᵥ x) = (φ m) +ᵥ toEquiv x

/-- Equivariant functions :
When `φ : M ≃ N` is an equivalence, and types `X` and `Y` are endowed with actions of `M` and `N`,
an ordered equivalence `f : X ≃ Y` is `φ`-equivariant if `f (m • x) = (φ m) • (f x)`. -/
@[to_additive]
structure OrderedMulActionEquiv where
  /-- The underlying function. -/
  protected toEquiv : X ≃o Y
  /-- The proposition that the function commutes with the actions. -/
  protected map_smul' : ∀ (m : M) (x : X), toEquiv (m • x) = (φ m) • toEquiv x

/- Porting note: local notation given a name, conflict with Algebra.Hom.GroupAction
see https://github.com/leanprover/lean4/issues/2000 -/
/-- Ordered `φ`-equivariant equivalences `X ≃ Y`,
where `φ : M ≃ N`, where `M` and `N` act on `X` and `Y` respectively. -/
notation:25 (name := «OrderedMulActionEquivLocal≺») X " ≃oₑ[" φ:25 "] " Y:0 =>
  OrderedMulActionEquiv φ X Y

/-- Ordered `M`-equivariant equivalences `X ≃ Y` with respect to the action of `M`.
This is the same as `X ≃oₑ[Equiv.refl M] Y`. -/
notation:25 (name := «OrderedMulActionEquivIdLocal≺») X " ≃o[" M:25 "] " Y:0 =>
  OrderedMulActionEquiv (Equiv.refl M) X Y

/-- Ordered `φ`-equivariant equivalences `X ≃ Y`,
where `φ : M ≃ N`, where `M` and `N` act additively on `X` and `Y` respectively

We use the same notation as for multiplicative actions, as conflicts are unlikely. -/
notation:25 (name := «OrderedAddActionEquivLocal≺») X " ≃oₑ[" φ:25 "] " Y:0 =>
  OrderedAddActionEquiv φ X Y

/-- Ordered `M`-equivariant equivalences `X ≃ Y` with respect to the additive action of `M`.
This is the same as `X ≃oₑ[Equiv.refl M] Y`.

We use the same notation as for multiplicative actions, as conflicts are unlikely. -/
notation:25 (name := «OrderedAddActionEquivIdLocal≺») X " ≃o[" M:25 "] " Y:0 =>
  OrderedAddActionEquiv (Equiv.refl M) X Y

/-- `OrderedAddActionSemiEquivClass F φ X Y` states that
  `F` is a type of order ismorphisms which are `φ`-equivariant.

You should extend this class when you extend `AddActionEquiv`. -/
class OrderedAddActionSemiEquivClass (F : Type*) {M N : outParam Type*} (φ : outParam (M ≃ N))
    (X Y : outParam Type*) [LE X] [VAdd M X] [LE Y] [VAdd N Y] [EquivLike F X Y]
    [OrderIsoClass F X Y] : Prop where
  /-- The proposition that the function preserves the action. -/
  map_vaddₛₗ : ∀ (f : F) (c : M) (x : X), f (c +ᵥ x) = (φ c) +ᵥ (f x)

/-- `OrderedMulActionSemiEquivClass F φ X Y` states that
  `F` is a type of order isomorphisms which are `φ`-equivariant.

You should extend this class when you extend `OrderedMulActionEquiv`. -/
@[to_additive]
class OrderedMulActionSemiEquivClass (F : Type*) {M N : outParam Type*} (φ : outParam (M ≃ N))
    (X Y : outParam Type*) [LE X] [SMul M X] [LE Y] [SMul N Y] [EquivLike F X Y]
    [OrderIsoClass F X Y] : Prop where
  /-- The proposition that the function preserves the action. -/
  map_smulₛₗ : ∀ (f : F) (c : M) (x : X), f (c • x) = (φ c) • (f x)

export OrderedMulActionSemiEquivClass (map_smulₛₗ)
export OrderedAddActionSemiEquivClass (map_vaddₛₗ)

@[to_additive]
instance (F : Type*) [SMul M X] [SMul N Y] [EquivLike F X Y] [OrderIsoClass F X Y]
    [OrderedMulActionSemiEquivClass F φ X Y] : MulActionSemiHomClass F φ X Y where
  map_smulₛₗ := OrderedMulActionSemiEquivClass.map_smulₛₗ

/-- `OrderedMulActionEquivClass F M X Y` states that `F` is a type of order
isomorphisms which are equivariant with respect to actions of `M`
This is an abbreviation of `OrderedMulActionSemiEquivClass`. -/
@[to_additive "`OrderedMulActionEquivClass F M X Y` states that `F` is a type of
isomorphisms which are equivariant with respect to actions of `M`
This is an abbreviation of `OrderedMulActionSemiEquivClass`."]
abbrev OrderedMulActionEquivClass (F : Type*) (M : outParam Type*)
    (X Y : outParam Type*) [LE X] [SMul M X] [LE Y] [SMul M Y] [EquivLike F X Y]
    [OrderIsoClass F X Y] :=
  OrderedMulActionSemiEquivClass F (Equiv.refl M) X Y

@[to_additive] instance : EquivLike (OrderedMulActionEquiv φ X Y) X Y where
  coe f := OrderedMulActionEquiv.toEquiv f
  inv f := (OrderedMulActionEquiv.toEquiv f).symm
  left_inv f x := by simp
  right_inv f x := by simp
  coe_injective' f g h hs := by
    cases f
    cases g
    simp only [OrderedMulActionEquiv.mk.injEq]
    ext
    simp [h]

@[to_additive] instance : OrderIsoClass (X ≃oₑ[φ] Y) X Y where
  map_le_map_iff f := f.toEquiv.map_rel_iff'

@[to_additive]
instance : OrderedMulActionSemiEquivClass (X ≃oₑ[φ] Y) φ X Y where
  map_smulₛₗ := OrderedMulActionEquiv.map_smul'

initialize_simps_projections OrderedMulActionEquiv (toEquiv → apply)
initialize_simps_projections OrderedAddActionEquiv (toEquiv → apply)

end MulActionEquiv

namespace Prod.Lex

variable {G G₁ P₁ P₂ : Type*}

@[to_additive]
instance [SMul G P₁] [SMul G₁ P₂] : SMul (G ×ₗ G₁) (P₁ ×ₗ P₂) where
  smul g h := toLex ((ofLex g).1 • (ofLex h).1, (ofLex g).2 • (ofLex h).2)

@[to_additive]
theorem smul_eq [SMul G P₁] [SMul G₁ P₂] (g : G ×ₗ G₁) (h : P₁ ×ₗ P₂) :
    g • h = toLex ((ofLex g).1 • (ofLex h).1, (ofLex g).2 • (ofLex h).2) :=
  rfl

@[to_additive]
instance [Monoid G] [Monoid G₁] [MulAction G P₁] [MulAction G₁ P₂] :
    MulAction (G ×ₗ G₁) (P₁ ×ₗ P₂) where
  one_smul x := by simp [smul_eq]
  mul_smul x y z := by simp [smul_eq, mul_smul]

@[to_additive]
instance [PartialOrder G] [PartialOrder G₁] [PartialOrder P₁] [SMul G P₁]
    [IsOrderedCancelSMul G P₁] [PartialOrder P₂] [SMul G₁ P₂] [IsOrderedCancelSMul G₁ P₂] :
    IsOrderedCancelSMul (G ×ₗ G₁) (P₁ ×ₗ P₂) where
  smul_le_smul_left a b h c := by
    obtain h₁ | ⟨h₂, h₃⟩ := Prod.Lex.le_iff.mp h
    · exact Prod.Lex.le_iff.mpr <| Or.inl <|
        by simpa using (SMul.smul_lt_smul_of_le_of_lt (Preorder.le_refl (ofLex c).1) h₁)
    · refine Prod.Lex.le_iff.mpr <| Or.inr <| ⟨?_, ?_⟩
      · simpa using (congrArg (HSMul.hSMul (ofLex c).1) h₂)
      · simpa using (IsOrderedSMul.smul_le_smul_left (ofLex a).2 (ofLex b).2 h₃ (ofLex c).2)
  smul_le_smul_right a b h c := by
    obtain h₁ | ⟨h₂, h₃⟩ := Prod.Lex.le_iff.mp h
    · exact Prod.Lex.le_iff.mpr <| Or.inl <|
        by simpa using (SMul.smul_lt_smul_of_lt_of_le h₁ (Preorder.le_refl (ofLex c).1))
    · refine Prod.Lex.le_iff.mpr <| Or.inr <| ⟨?_, ?_⟩
      · simpa using congrFun (congrArg HSMul.hSMul h₂) (ofLex c).1
      · simpa using (IsOrderedSMul.smul_le_smul_right (ofLex a).2 (ofLex b).2 h₃ (ofLex c).2)
  le_of_smul_le_smul_left a b c h := by
    obtain h₁ | ⟨h₂, h₃⟩ := Prod.Lex.le_iff.mp h
    · exact Prod.Lex.le_iff.mpr <| Or.inl <| SMul.lt_of_smul_lt_smul_left h₁
    · refine Prod.Lex.le_iff.mpr <| Or.inr <| ⟨IsCancelSMul.left_cancel _ _ _ h₂, ?_⟩
      exact IsOrderedCancelSMul.le_of_smul_le_smul_left (ofLex a).2 (ofLex b).2 (ofLex c).2 h₃
  le_of_smul_le_smul_right a b c h := by
    obtain h₁ | ⟨h₂, h₃⟩ := Prod.Lex.le_iff.mp h
    · refine Prod.Lex.le_iff.mpr <| Or.inl <| SMul.lt_of_smul_lt_smul_right h₁
    · refine Prod.Lex.le_iff.mpr <| Or.inr <| ⟨IsCancelSMul.right_cancel _ _ _ h₂, ?_⟩
      exact IsOrderedCancelSMul.le_of_smul_le_smul_right (ofLex a).2 (ofLex b).2 (ofLex c).2 h₃

end Prod.Lex

namespace Prod.RevLex

variable {G G₁ P₁ P₂ : Type*}

@[to_additive]
instance [SMul G P₁] [SMul G₁ P₂] : SMul (G ×ᵣ G₁) (P₁ ×ᵣ P₂) where
  smul g h := toRevLex ((ofRevLex g).1 • (ofRevLex h).1, (ofRevLex g).2 • (ofRevLex h).2)

@[to_additive]
theorem smul_eq [SMul G P₁] [SMul G₁ P₂] (g : G ×ᵣ G₁) (h : P₁ ×ᵣ P₂) :
    g • h = toRevLex ((ofRevLex g).1 • (ofRevLex h).1, (ofRevLex g).2 • (ofRevLex h).2) := rfl

@[to_additive]
instance [Monoid G] [Monoid G₁] [MulAction G P₁] [MulAction G₁ P₂] :
    MulAction (G ×ᵣ G₁) (P₁ ×ᵣ P₂) where
  one_smul x := by simp [smul_eq]
  mul_smul x y z := by simp [smul_eq, mul_smul]

@[to_additive]
instance [PartialOrder G] [PartialOrder G₁] [PartialOrder P₁] [SMul G P₁]
    [IsOrderedCancelSMul G P₁] [PartialOrder P₂] [SMul G₁ P₂] [IsOrderedCancelSMul G₁ P₂] :
    IsOrderedCancelSMul (G ×ᵣ G₁) (P₁ ×ᵣ P₂) where
  smul_le_smul_left a b h c := by
    obtain h₁ | ⟨h₂, h₃⟩ := Prod.RevLex.le_iff.mp h
    · refine Prod.RevLex.le_iff.mpr <| Or.inl <| by simpa using (SMul.smul_lt_smul_of_le_of_lt
        (Preorder.le_refl (ofRevLex c).2) h₁)
    · refine Prod.RevLex.le_iff.mpr <| Or.inr <| ⟨?_, ?_⟩
      · simpa using (congrArg (HSMul.hSMul (ofRevLex c).2) h₂)
      · simpa using (IsOrderedSMul.smul_le_smul_left
          (ofRevLex a).1 (ofRevLex b).1 h₃ (ofRevLex c).1)
  smul_le_smul_right a b h c := by
    obtain h₁ | ⟨h₂, h₃⟩ := Prod.RevLex.le_iff.mp h
    · exact Prod.RevLex.le_iff.mpr <| Or.inl <|
        by simpa using (SMul.smul_lt_smul_of_lt_of_le h₁ (Preorder.le_refl (ofRevLex c).2))
    · refine Prod.RevLex.le_iff.mpr <| Or.inr <| ⟨?_, ?_⟩
      · simpa using congrFun (congrArg HSMul.hSMul h₂) (ofRevLex c).2
      · simpa using (IsOrderedSMul.smul_le_smul_right
          (ofRevLex a).1 (ofRevLex b).1 h₃ (ofRevLex c).1)
  le_of_smul_le_smul_left a b c h := by
    obtain h₁ | ⟨h₂, h₃⟩ := Prod.RevLex.le_iff.mp h
    · exact Prod.RevLex.le_iff.mpr <| Or.inl <| SMul.lt_of_smul_lt_smul_left h₁
    · refine Prod.RevLex.le_iff.mpr <| Or.inr <| ⟨IsCancelSMul.left_cancel _ _ _ h₂, ?_⟩
      exact IsOrderedCancelSMul.le_of_smul_le_smul_left
          (ofRevLex a).1 (ofRevLex b).1 (ofRevLex c).1 h₃
  le_of_smul_le_smul_right a b c h := by
    obtain h₁ | ⟨h₂, h₃⟩ := Prod.RevLex.le_iff.mp h
    · refine Prod.RevLex.le_iff.mpr <| Or.inl <| SMul.lt_of_smul_lt_smul_right h₁
    · refine Prod.RevLex.le_iff.mpr <| Or.inr <| ⟨IsCancelSMul.right_cancel _ _ _ h₂, ?_⟩
      exact IsOrderedCancelSMul.le_of_smul_le_smul_right
        (ofRevLex a).1 (ofRevLex b).1 (ofRevLex c).1 h₃

/-- An ordered equivariant isomorphism given by `lexEquiv`. -/
@[to_additive "An ordered additive-equivariant isomorphism given by `lexEquiv`."]
def lexEquivSMul (G G₁ P₁ P₂) [PartialOrder G] [PartialOrder G₁] [PartialOrder P₁] [SMul G P₁]
    [PartialOrder P₂] [SMul G₁ P₂] :
    (P₁ ×ₗ P₂) ≃oₑ[(Prod.RevLex.lexEquiv G G₁).toEquiv] (P₂ ×ᵣ P₁) where
  toEquiv := Prod.RevLex.lexEquiv P₁ P₂
  map_smul' g p := by simp [lexEquiv, smul_eq, Prod.Lex.smul_eq]

end Prod.RevLex
