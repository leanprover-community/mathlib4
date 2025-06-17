/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Paul Lezeau, Robin Carlier
-/
import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.CategoryTheory.Monoidal.Action.Basic

/-!
# The category of module objects over a monoid object.
-/

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory Mon_Class

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]

/-- A module object for a monoid object, all internal to some monoidal category. -/
structure Mod_ (A : Mon_ C) where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  /-- The action morphism of the module object -/
  smul : A.X ⊗ X ⟶ X
  one_smul : η ▷ X ≫ smul = (λ_ X).hom := by aesop_cat
  assoc : μ ▷ X ≫ smul = (α_ A.X A.X X).hom ≫ A.X ◁ smul ≫ smul := by aesop_cat

attribute [reassoc (attr := simp)] Mod_.one_smul Mod_.assoc

namespace Mod_

variable {A : Mon_ C} (M : Mod_ A)

theorem assoc_flip :
    A.X ◁ M.smul ≫ M.smul = (α_ A.X A.X M.X).inv ≫ μ ▷ M.X ≫ M.smul := by simp

/-- A morphism of module objects. -/
@[ext]
structure Hom (M N : Mod_ A) where
  /-- The underlying morphism -/
  hom : M.X ⟶ N.X
  smul_hom : M.smul ≫ hom = A.X ◁ hom ≫ N.smul := by aesop_cat

attribute [reassoc (attr := simp)] Hom.smul_hom

/-- The identity morphism on a module object. -/
@[simps]
def id (M : Mod_ A) : Hom M M where hom := 𝟙 M.X

instance homInhabited (M : Mod_ A) : Inhabited (Hom M M) :=
  ⟨id M⟩

/-- Composition of module object morphisms. -/
@[simps]
def comp {M N O : Mod_ A} (f : Hom M N) (g : Hom N O) : Hom M O where hom := f.hom ≫ g.hom

instance : Category (Mod_ A) where
  Hom M N := Hom M N
  id := id
  comp f g := comp f g

@[ext]
lemma hom_ext {M N : Mod_ A} (f₁ f₂ : M ⟶ N) (h : f₁.hom = f₂.hom) : f₁ = f₂ :=
  Hom.ext h

@[simp]
theorem id_hom' (M : Mod_ A) : (𝟙 M : M ⟶ M).hom = 𝟙 M.X := by
  rfl

@[simp]
theorem comp_hom' {M N K : Mod_ A} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

variable (A)

/-- A monoid object as a module over itself. -/
@[simps]
def regular : Mod_ A where
  X := A.X
  smul := μ

instance : Inhabited (Mod_ A) :=
  ⟨regular A⟩

/-- The forgetful functor from module objects to the ambient category. -/
def forget : Mod_ A ⥤ C where
  obj A := A.X
  map f := f.hom

#adaptation_note /-- https://github.com/leanprover/lean4/pull/6053
we needed to increase the `maxHeartbeats` limit if we didn't write an explicit proof for
`map_id` and `map_comp`.

This may indicate a configuration problem in Aesop. -/
/-- A morphism of monoid objects induces a "restriction" or "comap" functor
between the categories of module objects.
-/
@[simps]
def comap {A B : Mon_ C} (f : A ⟶ B) : Mod_ B ⥤ Mod_ A where
  obj M :=
    { X := M.X
      smul := f.hom ▷ M.X ≫ M.smul
      one_smul := by
        slice_lhs 1 2 => rw [← comp_whiskerRight]
        rw [IsMon_Hom.one_hom, one_smul]
      assoc := by
        -- oh, for homotopy.io in a widget!
        slice_rhs 2 3 => rw [whisker_exchange]
        simp only [whiskerRight_tensor, MonoidalCategory.whiskerLeft_comp, Category.assoc,
          Iso.hom_inv_id_assoc]
        slice_rhs 4 5 => rw [Mod_.assoc_flip]
        slice_rhs 3 4 => rw [associator_inv_naturality_middle]
        slice_rhs 2 4 => rw [Iso.hom_inv_id_assoc]
        slice_rhs 1 2 => rw [← MonoidalCategory.comp_whiskerRight, ← whisker_exchange]
        slice_rhs 1 2 => rw [← MonoidalCategory.comp_whiskerRight, ← tensorHom_def',
          ← IsMon_Hom.mul_hom]
        rw [comp_whiskerRight, Category.assoc] }
  map g :=
    { hom := g.hom
      smul_hom := by
        dsimp
        slice_rhs 1 2 => rw [whisker_exchange]
        slice_rhs 2 3 => rw [← g.smul_hom]
        rw [Category.assoc] }

-- Lots more could be said about `comap`, e.g. how it interacts with
-- identities, compositions, and equalities of monoid object morphisms.
end Mod_


section Mod_Class

open Mon_Class

variable (M : C) [Mon_Class M]

open scoped MonoidalLeftAction
/-- Given an action of a monoidal category `C` on a category `D`,
an action of a monoid object `M` in `C` on an object `X` in `D` is the data of a
map `smul : M ⊙ X ⟶ X` that satisfies unitality and associativity with
multiplication.

See `MulAction` for the non-categorical version. -/
class Mod_Class (X : D) where
  /-- The action map -/
  smul : M ⊙ₗ X ⟶ X
  /-- The identity acts trivially. -/
  one_smul' (X) : η ⊵ₗ X ≫ smul = (λₗ X).hom := by aesop_cat
  /-- The action map is compatible with multiplication. -/
  mul_smul' (X) : μ ⊵ₗ X ≫ smul = (αₗ M M X).hom ≫ M ⊴ₗ smul ≫ smul := by aesop_cat

attribute [reassoc] Mod_Class.mul_smul' Mod_Class.one_smul'

@[inherit_doc] scoped[Mon_Class] notation "γ" => Mod_Class.smul
@[inherit_doc] scoped[Mon_Class] notation "γ["Y"]" => Mod_Class.smul (X := Y)
@[inherit_doc] scoped[Mon_Class] notation "γ["N","Y"]" =>
  Mod_Class.smul (M := N) (X := Y)

variable {M}

namespace Mod_Class

@[reassoc (attr := simp)]
theorem one_smul (X : D) [Mod_Class M X] :
    η ⊵ₗ X ≫ γ[M,X] = (λₗ[C] X).hom :=
  Mod_Class.one_smul' X

@[reassoc (attr := simp)]
theorem mul_smul (X : D) [Mod_Class M X] :
    μ ⊵ₗ X ≫ γ = (αₗ M M X).hom ≫ M ⊴ₗ γ ≫ γ := Mod_Class.mul_smul' X

theorem assoc_flip (X : D) [Mod_Class M X] : M ⊴ₗ γ ≫ γ =
    (αₗ M M X).inv ≫ μ[M] ⊵ₗ X ≫ γ := by
  simp

variable (M) in
/-- The action of a monoid object on itself. -/
-- See note [reducible non instances]
abbrev regular : Mod_Class M M where
  smul := μ

/-- If `C` acts monoidally on `D`, then every object of `D` is canonically a
module over the trivial monoid. -/
@[simps]
instance (X : D) : Mod_Class (𝟙_ C) X where
  smul := λₗ _|>.hom

@[ext]
theorem ext {X : C} (h₁ h₂ : Mod_Class M X) (H : h₁.smul = h₂.smul) :
    h₁ = h₂ := by
  cases h₁
  cases h₂
  subst H
  rfl

end Mod_Class

end Mod_Class

open scoped Mod_Class MonoidalLeftAction

variable (A : C) [Mon_Class A]
/-- A morphism in `D` is a morphism of `A`-module objects if it commutes with
the action maps -/
class IsMod_Hom {M N : D} [Mod_Class A M] [Mod_Class A N] (f : M ⟶ N) where
  smul_hom : γ[M] ≫ f = A ⊴ₗ f ≫ γ[N] := by aesop_cat

attribute [reassoc (attr := simp)] IsMod_Hom.smul_hom

variable {M N O: D} [Mod_Class A M] [Mod_Class A N] [Mod_Class A O]

instance : IsMod_Hom A (𝟙 M) where

instance (f : M ⟶ N) (g : N ⟶ O) [IsMod_Hom A f] [IsMod_Hom A g] :
    IsMod_Hom A (f ≫ g) where

instance (f : M ≅ N) [IsMod_Hom A f.hom] :
   IsMod_Hom A f.inv where
  smul_hom := by simp [Iso.comp_inv_eq]

variable (D) in
/-- A (bundled) module object for a monoid object in a monoidal category acting
on the ambient category. -/
structure Mod_ (A : C) [Mon_Class A] where
  /-- The underlying object in the ambient category -/
  X : D
  [mod : Mod_Class A X]

attribute [instance] Mod_.mod

namespace Mod_

variable {A : C} [Mon_Class A] (M : Mod_ D A)

theorem assoc_flip : A ⊴ₗ γ ≫ γ = (αₗ A A M.X).inv ≫ μ ⊵ₗ M.X ≫ γ := by simp

/-- A morphism of monoid objects. -/
@[ext]
structure Hom (M N : Mod_ D A) where
  /-- The underlying morphism -/
  hom : M.X ⟶ N.X
  [isMod_Hom : IsMod_Hom A hom]


attribute [instance] Hom.isMod_Hom

/-- An alternative constructor for `Hom`,
taking a morphism without a [isMod_Hom] instance, as well as the relevant
equality to put such an instance. -/
@[simps!]
def Hom.mk' {M N : Mod_ D A} (f : M.X ⟶ N.X)
    (smul_hom : γ[M.X] ≫ f = A ⊴ₗ f ≫ γ[N.X] := by aesop_cat) : Hom M N :=
  letI : IsMod_Hom A f := ⟨smul_hom⟩
  ⟨f⟩

/-- An alternative constructor for `Hom`,
taking a morphism without a [isMod_Hom] instance, between objects with
a `Mod_Class` instance (rather than bundled as `Mod_`),
as well as the relevant equality to put such an instance. -/
@[simps!]
def Hom.mk'' {M N : D} [Mod_Class A M] [Mod_Class A N] (f : M ⟶ N)
    (smul_hom : γ[M] ≫ f = A ⊴ₗ f ≫ γ[N] := by aesop_cat) :
    Hom (.mk (A := A) M) (.mk (A := A) N) :=
  letI : IsMod_Hom A f := ⟨smul_hom⟩
  ⟨f⟩

/-- The identity morphism on a module object. -/
@[simps]
def id (M : Mod_ D A) : Hom M M where hom := 𝟙 M.X

instance homInhabited (M : Mod_ D A) : Inhabited (Hom M M) :=
  ⟨id M⟩

/-- Composition of module object morphisms. -/
@[simps]
def comp {M N O : Mod_ D A} (f : Hom M N) (g : Hom N O) :
    Hom M O where
  hom := f.hom ≫ g.hom

instance : Category (Mod_ D A) where
  Hom M N := Hom M N
  id := id
  comp f g := comp f g

@[ext]
lemma hom_ext {M N : Mod_ D A} (f₁ f₂ : M ⟶ N) (h : f₁.hom = f₂.hom) :
    f₁ = f₂ :=
  Hom.ext h

@[simp]
theorem id_hom' (M : Mod_ D A) : (𝟙 M : M ⟶ M).hom = 𝟙 M.X := by
  rfl

@[simp]
theorem comp_hom' {M N K : Mod_ D A} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

variable (A)

/-- A monoid object as a module over itself. -/
@[simps]
def regular : Mod_ C A :=
  letI : Mod_Class A A := .regular A
  ⟨A⟩

instance : Inhabited (Mod_ C A) :=
  ⟨regular A⟩

/-- The forgetful functor from module objects to the ambient category. -/
@[simps]
def forget : Mod_ D A ⥤ D where
  obj A := A.X
  map f := f.hom

section comap

variable {A B : C} [Mon_Class A] [Mon_Class B] (f : A ⟶ B) [IsMon_Hom f]

open MonoidalLeftAction in
/-- When `M` is a `B`-module in `D` and `f : A ⟶ B` is a morphism of internal
monoid objects, `M` inherits an `A`-module structure via
"restriction of scalars", i.e `γ[A, M] = f.hom ⊵ M ≫ γ[B, M]`. -/
@[simps!]
def scalarRestriction (M : D) [Mod_Class B M] : Mod_Class A M where
  smul := f ⊵ₗ M ≫ γ[B, M]
  one_smul' := by
    rw [← comp_actionHomLeft_assoc]
    rw [IsMon_Hom.one_hom, Mod_Class.one_smul]
  mul_smul' := by
    -- oh, for homotopy.io in a widget!
    slice_rhs 2 3 => rw [action_exchange]
    simp only [actionHomLeft_action_assoc, Category.assoc, Iso.hom_inv_id_assoc,
      actionHomRight_comp]
    slice_rhs 4 6 => rw [Mod_Class.assoc_flip]
    slice_rhs 2 4 => rw [← whiskerLeft_actionHomLeft]
    slice_rhs 1 2 => rw [← comp_actionHomLeft]
    rw [← comp_actionHomLeft, Category.assoc, ← comp_actionHomLeft_assoc,
      IsMon_Hom.mul_hom, tensorHom_def, Category.assoc]

open MonoidalLeftAction in
/-- If `g : M ⟶ N` is a `B`-linear morphisms of `B`-modules, then it induces an
`A`-linear morphism when `M` and `N` have an `A`-module structure obtained
by restricting scalars along a monoid morphism `A ⟶ B`. -/
@[simps!]
lemma scalarRestriction_isMod_Hom
    (M N : D) [Mod_Class B M] [Mod_Class B N] (g : M ⟶ N) [IsMod_Hom B g] :
    letI := scalarRestriction f M
    letI := scalarRestriction f N
    IsMod_Hom A g :=
  letI := scalarRestriction f M
  letI := scalarRestriction f N
  { smul_hom := by
      dsimp
      slice_rhs 1 2 => rw [action_exchange]
      slice_rhs 2 3 => rw [← IsMod_Hom.smul_hom]
      rw [Category.assoc] }

/-- A morphism of monoid objects induces a "restriction" or "comap" functor
between the categories of module objects.
-/
@[simps]
def comap {A B : C} [Mon_Class A] [Mon_Class B] (f : A ⟶ B) [IsMon_Hom f] :
    Mod_ D B ⥤ Mod_ D A where
  obj M :=
    letI := scalarRestriction f M.X
    ⟨M.X⟩
  map {M N} g :=
    letI := scalarRestriction_isMod_Hom f M.X N.X g.hom
    ⟨g.hom⟩

-- Lots more could be said about `comap`, e.g. how it interacts with
-- identities, compositions, and equalities of monoid object morphisms.

end comap

end Mod_
