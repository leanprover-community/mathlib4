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

open CategoryTheory MonoidalCategory MonObj

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalLeftAction C D]

section ModObj

open MonObj

variable (M : C) [MonObj M]

open scoped MonoidalLeftAction
/-- Given an action of a monoidal category `C` on a category `D`,
an action of a monoid object `M` in `C` on an object `X` in `D` is the data of a
map `smul : M ⊙ₗ X ⟶ X` that satisfies unitality and associativity with
multiplication.

See `MulAction` for the non-categorical version. -/
class ModObj (X : D) where
  /-- The action map -/
  smul : M ⊙ₗ X ⟶ X
  /-- The identity acts trivially. -/
  one_smul' (X) : η ⊵ₗ X ≫ smul = (λₗ X).hom := by cat_disch
  /-- The action map is compatible with multiplication. -/
  mul_smul' (X) : μ ⊵ₗ X ≫ smul = (αₗ M M X).hom ≫ M ⊴ₗ smul ≫ smul := by cat_disch

@[deprecated (since := "2025-09-14")] alias Mod_Class := ModObj

attribute [reassoc] ModObj.mul_smul' ModObj.one_smul'

@[inherit_doc] scoped[MonObj] notation "γ" => ModObj.smul
@[inherit_doc] scoped[MonObj] notation "γ["Y"]" => ModObj.smul (X := Y)
@[inherit_doc] scoped[MonObj] notation "γ["N","Y"]" =>
  ModObj.smul (M := N) (X := Y)

variable {M}

namespace ModObj

@[reassoc (attr := simp)]
theorem one_smul (X : D) [ModObj M X] :
    η ⊵ₗ X ≫ γ[M,X] = (λₗ[C] X).hom :=
  ModObj.one_smul' X

@[reassoc (attr := simp)]
theorem mul_smul (X : D) [ModObj M X] :
    μ ⊵ₗ X ≫ γ = (αₗ M M X).hom ≫ M ⊴ₗ γ ≫ γ := ModObj.mul_smul' X

theorem assoc_flip (X : D) [ModObj M X] : M ⊴ₗ γ ≫ γ =
    (αₗ M M X).inv ≫ μ[M] ⊵ₗ X ≫ γ := by
  simp

variable (M) in
/-- The action of a monoid object on itself. -/
-- See note [reducible non-instances]
abbrev regular : ModObj M M where
  smul := μ

attribute [local instance] regular in
@[simp] lemma smul_eq_mul (M : C) [MonObj M] : γ[M, M] = μ[M] := rfl

/-- If `C` acts monoidally on `D`, then every object of `D` is canonically a
module over the trivial monoid. -/
@[simps]
instance (X : D) : ModObj (𝟙_ C) X where
  smul := (λₗ _).hom

@[ext]
theorem ext {X : C} (h₁ h₂ : ModObj M X) (H : h₁.smul = h₂.smul) :
    h₁ = h₂ := by
  cases h₁
  cases h₂
  subst H
  rfl

end ModObj

end ModObj

open scoped ModObj MonoidalLeftAction

variable (A : C) [MonObj A]
/-- A morphism in `D` is a morphism of `A`-module objects if it commutes with
the action maps -/
class IsMod_Hom {M N : D} [ModObj A M] [ModObj A N] (f : M ⟶ N) where
  smul_hom : γ[M] ≫ f = A ⊴ₗ f ≫ γ[N] := by cat_disch

attribute [reassoc (attr := simp)] IsMod_Hom.smul_hom

variable {M N O : D} [ModObj A M] [ModObj A N] [ModObj A O]

instance : IsMod_Hom A (𝟙 M) where

instance (f : M ⟶ N) (g : N ⟶ O) [IsMod_Hom A f] [IsMod_Hom A g] :
    IsMod_Hom A (f ≫ g) where

instance (f : M ≅ N) [IsMod_Hom A f.hom] :
    IsMod_Hom A f.inv where
  smul_hom := by simp [Iso.comp_inv_eq]

variable (D) in
/-- A module object for a monoid object in a monoidal category acting on the
ambient category. -/
structure Mod_ (A : C) [MonObj A] where
  /-- The underlying object in the ambient category -/
  X : D
  [mod : ModObj A X]

attribute [instance] Mod_.mod

namespace Mod_

variable {A : C} [MonObj A] (M : Mod_ D A)

theorem assoc_flip : A ⊴ₗ γ ≫ γ = (αₗ A A M.X).inv ≫ μ ⊵ₗ M.X ≫ γ := by simp

/-- A morphism of module objects. -/
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
    (smul_hom : γ[M.X] ≫ f = A ⊴ₗ f ≫ γ[N.X] := by cat_disch) : Hom M N :=
  letI : IsMod_Hom A f := ⟨smul_hom⟩
  ⟨f⟩

/-- An alternative constructor for `Hom`,
taking a morphism without a [isMod_Hom] instance, between objects with
a `ModObj` instance (rather than bundled as `Mod_`),
as well as the relevant equality to put such an instance. -/
@[simps!]
def Hom.mk'' {M N : D} [ModObj A M] [ModObj A N] (f : M ⟶ N)
    (smul_hom : γ[M] ≫ f = A ⊴ₗ f ≫ γ[N] := by cat_disch) :
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
theorem id_hom' (M : Mod_ D A) : (𝟙 M : M ⟶ M).hom = 𝟙 M.X := rfl

@[simp]
theorem comp_hom' {M N K : Mod_ D A} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

variable (A)

/-- A monoid object as a module over itself. -/
@[simps]
def regular : Mod_ C A :=
  letI : ModObj A A := .regular A
  ⟨A⟩

instance : Inhabited (Mod_ C A) :=
  ⟨regular A⟩

/-- The forgetful functor from module objects to the ambient category. -/
@[simps]
def forget : Mod_ D A ⥤ D where
  obj A := A.X
  map f := f.hom

section comap

variable {A B : C} [MonObj A] [MonObj B] (f : A ⟶ B) [IsMonHom f]

open MonoidalLeftAction in
/-- When `M` is a `B`-module in `D` and `f : A ⟶ B` is a morphism of internal
monoid objects, `M` inherits an `A`-module structure via
"restriction of scalars", i.e `γ[A, M] = f.hom ⊵ₗ M ≫ γ[B, M]`. -/
@[simps!]
def scalarRestriction (M : D) [ModObj B M] : ModObj A M where
  smul := f ⊵ₗ M ≫ γ[B, M]
  one_smul' := by
    rw [← comp_actionHomLeft_assoc]
    rw [IsMonHom.one_hom, ModObj.one_smul]
  mul_smul' := by
    -- oh, for homotopy.io in a widget!
    slice_rhs 2 3 => rw [action_exchange]
    simp only [actionHomLeft_action_assoc, Category.assoc, Iso.hom_inv_id_assoc,
      actionHomRight_comp]
    slice_rhs 4 6 => rw [ModObj.assoc_flip]
    slice_rhs 2 4 => rw [← whiskerLeft_actionHomLeft]
    slice_rhs 1 2 => rw [← comp_actionHomLeft]
    rw [← comp_actionHomLeft, Category.assoc, ← comp_actionHomLeft_assoc,
      IsMonHom.mul_hom, tensorHom_def, Category.assoc]

open MonoidalLeftAction in
/-- If `g : M ⟶ N` is a `B`-linear morphisms of `B`-modules, then it induces an
`A`-linear morphism when `M` and `N` have an `A`-module structure obtained
by restricting scalars along a monoid morphism `A ⟶ B`. -/
lemma scalarRestriction_hom
    (M N : D) [ModObj B M] [ModObj B N] (g : M ⟶ N) [IsMod_Hom B g] :
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
def comap {A B : C} [MonObj A] [MonObj B] (f : A ⟶ B) [IsMonHom f] :
    Mod_ D B ⥤ Mod_ D A where
  obj M :=
    letI := scalarRestriction f M.X
    ⟨M.X⟩
  map {M N} g :=
    letI := scalarRestriction_hom f M.X N.X g.hom
    ⟨g.hom⟩

-- Lots more could be said about `comap`, e.g. how it interacts with
-- identities, compositions, and equalities of monoid object morphisms.

end comap

end Mod_
