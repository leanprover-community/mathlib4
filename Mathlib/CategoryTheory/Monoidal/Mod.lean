/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Paul Lezeau, Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Monoidal.Action.Basic

/-!
# The category of module objects over a monoid object.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory MonObj

namespace CategoryTheory
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalLeftAction C D]

section ModObj

open MonObj AddMonObj

open scoped MonoidalLeftAction

section

variable (M : C) [AddMonObj M]

/-- Given an action of a monoidal category `C` on a category `D`,
an action of an additive monoid object `M` in `C` on an object `X` in `D` is the data of a
map `vadd : M ⊙ₗ X ⟶ X` that satisfies zero-additivity and associativity with addition.

See `AddAction` for the non-categorical version. -/
class AddModObj (X : D) where
  /-- The action map -/
  vadd : M ⊙ₗ X ⟶ X
  /-- The zero acts trivially. -/
  zero_vadd (X) : ζ ⊵ₗ X ≫ vadd = (λₗ X).hom := by cat_disch
  /-- The action map is compatible with addition. -/
  add_vadd (X) : σ ⊵ₗ X ≫ vadd = (αₗ M M X).hom ≫ M ⊴ₗ vadd ≫ vadd := by cat_disch

end

variable (M : C) [MonObj M]

/-- Given an action of a monoidal category `C` on a category `D`,
an action of a monoid object `M` in `C` on an object `X` in `D` is the data of a
map `smul : M ⊙ₗ X ⟶ X` that satisfies unitality and associativity with
multiplication.

See `MulAction` for the non-categorical version. -/
@[to_additive]
class ModObj (X : D) where
  /-- The action map -/
  smul : M ⊙ₗ X ⟶ X
  /-- The identity acts trivially. -/
  one_smul (X) : η ⊵ₗ X ≫ smul = (λₗ X).hom := by cat_disch
  /-- The action map is compatible with multiplication. -/
  mul_smul (X) : μ ⊵ₗ X ≫ smul = (αₗ M M X).hom ≫ M ⊴ₗ smul ≫ smul := by cat_disch

attribute [to_additive existing (attr := reassoc (attr := simp))] ModObj.mul_smul ModObj.one_smul

namespace AddModObj

@[inherit_doc] scoped[CategoryTheory.MonObj] notation "δ" => AddModObj.vadd
@[inherit_doc] scoped[CategoryTheory.MonObj] notation "δ[" Y "]" => AddModObj.vadd (X := Y)
@[inherit_doc] scoped[CategoryTheory.MonObj] notation "δ[" N "," Y "]" =>
  AddModObj.vadd (M := N) (X := Y)

end AddModObj

namespace MonObj

@[inherit_doc] scoped notation "γ" => ModObj.smul
@[inherit_doc] scoped notation "γ[" Y "]" => ModObj.smul (X := Y)
@[inherit_doc] scoped notation "γ[" N "," Y "]" =>
  ModObj.smul (M := N) (X := Y)

end MonObj

variable {M}

namespace ModObj

@[to_additive]
theorem assoc_flip (X : D) [ModObj M X] : M ⊴ₗ γ ≫ γ =
    (αₗ M M X).inv ≫ μ[M] ⊵ₗ X ≫ γ := by
  simp

variable (M) in
/-- The action of a monoid object on itself. -/
-- See note [reducible non-instances]
@[to_additive]
abbrev regular : ModObj M M where
  smul := μ

attribute [local instance] regular in
@[to_additive, simp]
lemma smul_eq_mul (M : C) [MonObj M] : γ[M,M] = μ[M] := rfl

/-- If `C` acts monoidally on `D`, then every object of `D` is canonically a
module over the trivial monoid. -/
@[to_additive (attr := simps)]
instance (X : D) : ModObj (𝟙_ C) X where
  smul := (λₗ _).hom

@[to_additive (attr := ext)]
theorem ext {X : C} (h₁ h₂ : ModObj M X) (H : h₁.smul = h₂.smul) :
    h₁ = h₂ := by
  cases h₁
  cases h₂
  subst H
  rfl

end ModObj

end ModObj

open scoped ModObj MonoidalLeftAction

variable {M' N' O' : D}

open AddModObj in
/-- A morphism in `D` is a morphism of `A`-additive module objects if it commutes with
the action maps -/
class IsAddModHom (A : C) [AddMonObj A] [AddModObj A M'] [AddModObj A N'] (f : M' ⟶ N') where
  vadd_hom : δ[M'] ≫ f = A ⊴ₗ f ≫ δ[N'] := by cat_disch

variable (A : C) [MonObj A]
/-- A morphism in `D` is a morphism of `A`-module objects if it commutes with
the action maps -/
@[to_additive]
class IsModHom {M N : D} [ModObj A M] [ModObj A N] (f : M ⟶ N) where
  smul_hom : γ[M] ≫ f = A ⊴ₗ f ≫ γ[N] := by cat_disch

@[deprecated (since := "2026-04-21")]
alias IsMod_Hom := IsModHom

@[deprecated (since := "2026-04-21")]
alias IsMod_Hom.smul_hom := IsModHom.smul_hom

attribute [to_additive existing (attr := reassoc (attr := simp))] IsModHom.smul_hom

set_option linter.existingAttributeWarning false in
attribute [to_additive existing] IsModHom.smul_hom_assoc

variable {M N O : D} [ModObj A M] [ModObj A N] [ModObj A O]

@[to_additive]
instance instIsModHomId : IsModHom A (𝟙 M) where

@[to_additive]
instance instIsModHomComp (f : M ⟶ N) (g : N ⟶ O) [IsModHom A f] [IsModHom A g] :
    IsModHom A (f ≫ g) where

@[to_additive]
instance instIsModHomIso (f : M ≅ N) [IsModHom A f.hom] :
    IsModHom A f.inv where
  smul_hom := by simp [Iso.comp_inv_eq]

variable (D) in
/-- An additive module object for an additive monoid object in a monoidal category acting on the
ambient category. -/
structure AddMod (A : C) [AddMonObj A] where
  /-- The underlying object in the ambient category -/
  X : D
  [addMod : AddModObj A X]

attribute [instance] AddMod.addMod

variable (D) in
/-- A module object for a monoid object in a monoidal category acting on the
ambient category. -/
@[to_additive AddMod]
structure Mod (A : C) [MonObj A] where
  /-- The underlying object in the ambient category -/
  X : D
  [mod : ModObj A X]

@[deprecated (since := "2026-04-21")]
alias Mod_ := Mod

@[deprecated (since := "2026-04-21")]
alias Mod_.mod := Mod.mod

attribute [instance] Mod.mod

namespace AddMod

variable {A : C} [AddMonObj A] (M : AddMod D A)

/-- A morphism of additive module objects. -/
@[ext]
structure Hom (M N : AddMod D A) where
  /-- The underlying morphism -/
  hom : M.X ⟶ N.X
  [isAddModHom : IsAddModHom A hom]

attribute [instance] Hom.isAddModHom

end AddMod

namespace Mod

variable {A : C} [MonObj A] (M : Mod D A)

@[to_additive]
theorem assoc_flip : A ⊴ₗ γ ≫ γ = (αₗ A A M.X).inv ≫ μ ⊵ₗ M.X ≫ γ := by simp

/-- A morphism of module objects. -/
@[ext, to_additive existing]
structure Hom (M N : Mod D A) where
  /-- The underlying morphism -/
  hom : M.X ⟶ N.X
  [isModHom : IsModHom A hom]

attribute [instance] Hom.isModHom
attribute [to_additive existing (attr := instance)] Hom.isModHom

/-- An alternative constructor for `Hom`,
taking a morphism without a `[IsModHom]` instance, as well as the relevant
equality to put such an instance. -/
@[to_additive (attr := simps)]
def Hom.mk' {M N : Mod D A} (f : M.X ⟶ N.X)
    (smul_hom : γ[M.X] ≫ f = A ⊴ₗ f ≫ γ[N.X] := by cat_disch) : Hom M N :=
  letI : IsModHom A f := ⟨smul_hom⟩
  ⟨f⟩

/-- An alternative constructor for `Hom`,
taking a morphism without a `[IsModHom]` instance, between objects with
a `ModObj` instance (rather than bundled as `Mod`),
as well as the relevant equality to put such an instance. -/
@[to_additive (attr := simps)]
def Hom.mk'' {M N : D} [ModObj A M] [ModObj A N] (f : M ⟶ N)
    (smul_hom : γ[M] ≫ f = A ⊴ₗ f ≫ γ[N] := by cat_disch) :
    Hom (.mk (A := A) M) (.mk (A := A) N) :=
  letI : IsModHom A f := ⟨smul_hom⟩
  ⟨f⟩

/-- The identity morphism on a module object. -/
@[to_additive (attr := simps)]
def id (M : Mod D A) : Hom M M where hom := 𝟙 M.X

@[to_additive]
instance homInhabited (M : Mod D A) : Inhabited (Hom M M) :=
  ⟨id M⟩

/-- Composition of module object morphisms. -/
@[to_additive (attr := simps)]
def comp {M N O : Mod D A} (f : Hom M N) (g : Hom N O) :
    Hom M O where
  hom := f.hom ≫ g.hom

@[to_additive]
instance : Category (Mod D A) where
  Hom M N := Hom M N
  id := id
  comp f g := comp f g

@[to_additive (attr := ext)]
lemma hom_ext {M N : Mod D A} (f₁ f₂ : M ⟶ N) (h : f₁.hom = f₂.hom) :
    f₁ = f₂ :=
  Hom.ext h

@[to_additive (attr := simp)]
theorem id_hom' (M : Mod D A) : (𝟙 M : M ⟶ M).hom = 𝟙 M.X := by
  rfl

@[to_additive (attr := simp)]
theorem comp_hom' {M N K : Mod D A} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

variable (A)

/-- A monoid object as a module over itself. -/
@[to_additive (attr := simps)]
def regular : Mod C A :=
  letI : ModObj A A := .regular A
  ⟨A⟩

@[to_additive (attr := simps)]
instance : Inhabited (Mod C A) :=
  ⟨regular A⟩

/-- The forgetful functor from module objects to the ambient category. -/
@[to_additive (attr := simps)]
def forget : Mod D A ⥤ D where
  obj A := A.X
  map f := f.hom

section comap

variable {A B : C} [MonObj A] [MonObj B] (f : A ⟶ B) [IsMonHom f]

open MonoidalLeftAction in
/-- When `M` is a `B`-module in `D` and `f : A ⟶ B` is a morphism of internal
monoid objects, `M` inherits an `A`-module structure via
"restriction of scalars", i.e `γ[A, M] = f ⊵ₗ M ≫ γ[B, M]`. -/
@[to_additive (attr := simps, implicit_reducible)]
def scalarRestriction (M : D) [ModObj B M] : ModObj A M where
  smul := f ⊵ₗ M ≫ γ[B,M]
  one_smul := by
    rw [← comp_actionHomLeft_assoc]
    rw [IsMonHom.one_hom, ModObj.one_smul]
  mul_smul := by
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
@[to_additive]
lemma scalarRestriction_hom
    (M N : D) [ModObj B M] [ModObj B N] (g : M ⟶ N) [IsModHom B g] :
    letI := scalarRestriction f M
    letI := scalarRestriction f N
    IsModHom A g :=
  letI := scalarRestriction f M
  letI := scalarRestriction f N
  { smul_hom := by
      simpa using (action_exchange_assoc f g γ).symm }

/-- A morphism of monoid objects induces a "restriction" or "comap" functor
between the categories of module objects.
-/
@[to_additive (attr := simps)]
def comap {A B : C} [MonObj A] [MonObj B] (f : A ⟶ B) [IsMonHom f] :
    Mod D B ⥤ Mod D A where
  obj M :=
    letI := scalarRestriction f M.X
    ⟨M.X⟩
  map {M N} g :=
    letI := scalarRestriction_hom f M.X N.X g.hom
    ⟨g.hom⟩

-- Lots more could be said about `comap`, e.g. how it interacts with
-- identities, compositions, and equalities of monoid object morphisms.

end comap

end Mod

namespace Mod_

@[deprecated (since := "2026-04-21")] alias assoc_flip := Mod.assoc_flip

@[deprecated (since := "2026-04-21")] alias Hom := Mod.Hom

@[deprecated (since := "2026-04-21")] alias Hom.mk' := Mod.Hom.mk'

@[deprecated (since := "2026-04-21")] alias Hom.mk'' := Mod.Hom.mk''

@[deprecated (since := "2026-04-21")] alias id := Mod.id

@[deprecated (since := "2026-04-21")] alias comp := Mod.comp

@[deprecated (since := "2026-04-21")] alias hom_ext := Mod.hom_ext

@[deprecated (since := "2026-04-21")] alias id_hom' := Mod.id_hom'

@[deprecated (since := "2026-04-21")] alias comp_hom' := Mod.comp_hom'

@[deprecated (since := "2026-04-21")] alias regular := Mod.regular

@[deprecated (since := "2026-04-21")] alias forget := Mod.forget

@[deprecated (since := "2026-04-21")] alias scalarRestriction := Mod.scalarRestriction

@[deprecated (since := "2026-04-21")] alias scalarRestriction_hom := Mod.scalarRestriction_hom

@[deprecated (since := "2026-04-21")] alias comap := Mod.comap

end Mod_

end CategoryTheory
