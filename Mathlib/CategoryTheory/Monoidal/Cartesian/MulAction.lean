/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon_
public import Mathlib.GroupTheory.GroupAction.Hom

/-!
# Action objects in cartesian monoidal categories

Given a monoid object `M` in a cartesian monoidal category `C`, we define the notion of a
multiplicative action of `M` on an object `X` of `C`.

## Main definitions

- `CategoryTheory.MulActionObj`: A multiplicative action of a monoid object on an object.
- `CategoryTheory.IsMulActionHom`: Equivariant morphisms under monoid actions.
- `CategoryTheory.Hom.mulAction`: If `M` acts on `X`, morphisms into `M` act on morphism into `X`.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory CartesianMonoidalCategory MonObj AddMonObj

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]

/-- An additive action of an additive monoid object `M` on an object `X`
in a cartesian monoidal category. -/
@[ext]
class AddActionObj (M : C) [AddMonObj M] (X : C) where
  /-- The additive action morphism. -/
  vadd : M ⊗ X ⟶ X
  /-- Acting by the zero element is the identity. -/
  zero_vadd (M X) : ζ ▷ X ≫ vadd = (λ_ X).hom := by cat_disch
  /-- The action is compatible with addition. -/
  add_vadd (M X) : (σ ▷ X) ≫ vadd = (α_ _ _ _).hom ≫ (M ◁ vadd) ≫ vadd := by cat_disch

/-- A multiplicative action of a monoid object `M` on an object `X`
in a cartesian monoidal category. -/
@[to_additive (attr := ext)]
class MulActionObj (M : C) [MonObj M] (X : C) where
  /-- The scalar multiplication morphism. -/
  smul : M ⊗ X ⟶ X
  /-- Acting by the unit element is the identity. -/
  one_smul (M X) : η ▷ X ≫ smul = (λ_ X).hom := by cat_disch
  /-- The action is compatible with multiplication. -/
  mul_smul (M X) : (μ ▷ X) ≫ smul = (α_ _ _ _).hom ≫ (M ◁ smul) ≫ smul := by cat_disch

variable {M : C} [MonObj M] {X : C} [MulActionObj M X]

namespace MulActionObj

attribute [to_additive existing (attr := reassoc), simp] one_smul
attribute [to_additive existing (attr := simp)] one_smul_assoc
attribute [to_additive existing (attr := reassoc)] mul_smul
attribute [to_additive existing] mul_smul_assoc

/-- Every monoid object acts on itself by left multiplication. -/
@[to_additive /-- Every additive monoid object acts on itself by left addition. -/]
instance : MulActionObj M M where
  smul := mul

variable (M) in
/-- The trivial action of `M` on `X`, given by projection to the second factor. -/
@[to_additive (attr := simps!, implicit_reducible)
/-- The trivial action of `M` on `X`, given by projection to the second factor. -/]
def trivial (X : C) : MulActionObj M X where
  smul := snd _ _
  one_smul := by simp [leftUnitor_hom]

/-- Transfer a `MulActionObj` along isomorphisms. -/
@[to_additive (attr := implicit_reducible)
  /-- Transfer an `AddActionObj` along isomorphisms. -/]
def ofIso {N : C} [MonObj N] (e₁ : M ≅ N) [IsMonHom e₁.hom] {Y : C} (e₂ : X ≅ Y) :
    MulActionObj N Y where
  smul := (e₁.inv ⊗ₘ e₂.inv) ≫ smul ≫ e₂.hom
  one_smul := by
    have : η ▷ Y ≫ (e₁.inv ⊗ₘ e₂.inv) = _ ◁ e₂.inv ≫ (η ≫ e₁.inv) ▷ X := by
      rw [tensorHom_def', comp_whiskerRight, whisker_exchange_assoc]
    simp [reassoc_of% this]
  mul_smul := by
    have : μ[N] ▷ Y ≫ (e₁.inv ⊗ₘ e₂.inv) =
        ((e₁.inv ⊗ₘ e₁.inv) ⊗ₘ e₂.inv) ≫ μ[M] ▷ X := by
      rw [tensorHom_def', whisker_exchange, ← comp_whiskerRight_assoc, IsMonHom.mul_hom,
        comp_whiskerRight, Category.assoc, ← whisker_exchange]
      nth_rw 2 [tensorHom_def', whisker_exchange]
      simp
    rw [reassoc_of% this]
    have : (α_ N M X).inv ≫ e₁.inv ▷ M ▷ X ≫ (α_ M M X).hom ≫ M ◁ smul =
        N ◁ smul ≫ e₁.inv ▷ X := by
      rw [associator_naturality_left_assoc, whisker_exchange]
      simp
    simp [tensorHom_def', mul_smul_assoc, reassoc_of% this]

variable (M) in
@[to_additive (attr := reassoc)]
theorem mul_smul_flip :
    M ◁ smul ≫ smul = (α_ M M X).inv ≫ (μ ▷ X) ≫ smul := by
  simp [MulActionObj.mul_smul]

@[to_additive (attr := reassoc (attr := simp))]
theorem one_smul_hom {Z : C} (f : Z ⟶ X) :
    (η[M] ⊗ₘ f) ≫ smul = (λ_ Z).hom ≫ f := by
  rw [tensorHom_def'_assoc, one_smul, leftUnitor_naturality]

end MulActionObj

variable {N O : C} [MonObj N] [MonObj O] {Y Z : C} [MulActionObj N Y] [MulActionObj O Z]

/-- If `φ : M ⟶ N` is a morphism of additive monoid objects and `X` and `Y` are equipped with
actions of `M` and `N`, a morphism `f : X ⟶ Y` is `φ`-equivariant if the actions commute with
`f` and `φ`. -/
class IsAddActionHom {M : C} [AddMonObj M] {X : C} [AddActionObj M X] {N : C} [AddMonObj N]
    {Y : C} [AddActionObj N Y] (φ : M ⟶ N) (f : X ⟶ Y) : Prop where
  vadd_hom (f) : AddActionObj.vadd ≫ f = (φ ⊗ₘ f) ≫ AddActionObj.vadd

/-- If `φ : M ⟶ N` is a morphism of monoid objects and `X` and `Y` are equipped with actions of
`M` and `N`, a morphism `f : X ⟶ Y` is `φ`-equivariant if the actions commute with `f` and `φ`. -/
@[to_additive existing]
class IsMulActionHom (φ : M ⟶ N) (f : X ⟶ Y) : Prop where
  smul_hom (φ f) : MulActionObj.smul ≫ f = (φ ⊗ₘ f) ≫ MulActionObj.smul := by cat_disch

namespace IsMulActionHom

-- `attribute [to_additive (attr := reassoc)] IsMulActionHom.smul_hom` is not sufficient
attribute [reassoc] IsMulActionHom.smul_hom
attribute [to_additive] IsMulActionHom.smul_hom_assoc

variable [MulActionObj M Y] [MulActionObj M Z] in
@[to_additive (attr := reassoc (attr := simp))]
lemma smul_hom_id (f : X ⟶ Y) [IsMulActionHom (𝟙 M) f] :
    MulActionObj.smul ≫ f = M ◁ f ≫ MulActionObj.smul := by
  simp [smul_hom (𝟙 M)]

-- Without this, the proof of `IsMulActionHom (𝟙 M) (f ≫ g)` breaks below.
set_option linter.existingAttributeWarning false in
attribute [to_additive existing] IsMulActionHom.smul_hom_id_assoc

@[to_additive]
instance : IsMulActionHom (𝟙 M) (𝟙 X) where

@[to_additive]
instance (φ : M ⟶ N) (ψ : N ⟶ O) (f : X ⟶ Y) (g : Y ⟶ Z) [IsMulActionHom φ f] [IsMulActionHom ψ g] :
    IsMulActionHom (φ ≫ ψ) (f ≫ g) where
  smul_hom := by simp [smul_hom_assoc φ, smul_hom ψ]

variable [MulActionObj M Y] [MulActionObj M Z] in
@[to_additive]
instance (f : X ⟶ Y) (g : Y ⟶ Z) [IsMulActionHom (𝟙 M) f] [IsMulActionHom (𝟙 M) g] :
    IsMulActionHom (𝟙 M) (f ≫ g) where

end IsMulActionHom

namespace Hom

variable (M X) in
/-- Morphisms `Y ⟶ M` act on morphisms `Y ⟶ X` via the internal scalar multiplication. -/
@[to_additive /-- Morphisms `Y ⟶ M` act on morphisms `Y ⟶ X` via the internal additive action. -/]
instance (Y : C) : SMul (Y ⟶ M) (Y ⟶ X) where
  smul m x := lift m x ≫ MulActionObj.smul

@[to_additive]
lemma smul_def {Y : C} (m : Y ⟶ M) (x : Y ⟶ X) : m • x = lift m x ≫ MulActionObj.smul :=
  rfl

/-- If `M` is a monoid object acting on `X`, then morphisms into `M` act on
morphisms into `X`. -/
@[to_additive /-- If `M` is an additive monoid object acting on `X`, then morphisms into `M` act on
morphisms into `X`. -/]
instance mulAction (Y : C) : MulAction (Y ⟶ M) (Y ⟶ X) where
  smul m x := lift m x ≫ MulActionObj.smul
  one_smul x := by
    rw [one_def, smul_def, ← lift_whiskerRight, Category.assoc]
    simp
  mul_smul m n x := by
    rw [mul_def, smul_def, ← lift_whiskerRight, Category.assoc]
    simp [smul_def, MulActionObj.mul_smul]

@[to_additive]
lemma map_smul (φ : M ⟶ N) (f : X ⟶ Y) [IsMulActionHom φ f] {Z : C} (m : Z ⟶ M) (x : Z ⟶ X) :
    (m • x) ≫ f = m ≫ φ • x ≫ f := by
  simp [smul_def, Category.assoc, IsMulActionHom.smul_hom φ]

/-- A `φ`-equivariant morphism induces an equivariant morphism on hom types. -/
@[to_additive /-- A `φ`-equivariant morphism induces an equivariant morphism on hom types. -/]
def mulActionHom (φ : M ⟶ N) (f : X ⟶ Y) [IsMulActionHom φ f] (Z : C) :
    MulActionHom (· ≫ φ : (Z ⟶ M) → _) (Z ⟶ X) (Z ⟶ Y) where
  toFun := (· ≫ f)
  map_smul' := map_smul φ f

end Hom

end CategoryTheory
