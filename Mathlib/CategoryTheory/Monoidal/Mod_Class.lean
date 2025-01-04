/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Mon_Class

/-!
# The category of module objects over a monoid object.
-/


universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C]
variable {C}

open scoped Mon_Class

/-- A module object for a monoid object, all internal to some monoidal category. -/
class Mod_Class (A : C) [Mon_Class A] (X : C) where
  act : A ⊗ X ⟶ X
  one_act : (η ▷ X) ≫ act = (λ_ X).hom := by aesop_cat
  assoc : (μ ▷ X) ≫ act = (α_ A A X).hom ≫ (A ◁ act) ≫ act := by aesop_cat

attribute [reassoc (attr := simp)] Mod_Class.one_act Mod_Class.assoc

namespace Mod_Class

scoped notation "↷" => Mod_Class.act

variable {A M : C} [Mon_Class A] [Mod_Class A M]


theorem assoc_flip :
    (A ◁ act) ≫ act = (α_ A A M).inv ≫ (μ ▷ M) ≫ act := by
  simp

/-- A morphism of module objects. -/
@[ext]
structure Hom (A M N : C) [Mon_Class A] [Mod_Class A M] [Mod_Class A N] where
  hom : M ⟶ N
  act_hom : act ≫ hom = (A ◁ hom) ≫ act := by aesop_cat

attribute [reassoc (attr := simp)] Hom.act_hom

/-- The identity morphism on a module object. -/
@[simps]
def id (A M : C) [Mon_Class A] [Mod_Class A M] : Hom A M M where hom := 𝟙 M

instance homInhabited : Inhabited (Hom A M M) :=
  ⟨id A M⟩

/-- Composition of module object morphisms. -/
@[simps]
def comp {M N O : C} [Mod_Class A M] [Mod_Class A N] [Mod_Class A O]
    (f : Hom A M N) (g : Hom A N O) :
    Hom A M O where
  hom := f.hom ≫ g.hom

end Mod_Class

structure Mod_Cat (A : C) [Mon_Class A] where
  X : C
  [isMod : Mod_Class A X]

attribute [instance] Mod_Cat.isMod

-- namespace Mod_Cat

variable {A : C} [Mon_Class A]

instance : Category (Mod_Cat A) where
  Hom M N := Mod_Class.Hom A M.X N.X
  id M := Mod_Class.id A M.X
  comp f g := Mod_Class.comp f g

namespace Mod_Cat

-- namespace Mod_Class

@[simp]
theorem mk_X (X : C) [Mod_Class A X] : (⟨X⟩ : Mod_Cat A).X = X := rfl

abbrev of (A X : C) [Mon_Class A] [Mod_Class A X] : Mod_Cat A := .mk X

theorem of_X (A X : C) [Mon_Class A] [Mod_Class A X] : (Mod_Cat.of A X).X = X := rfl

-- Porting note (#5229): added because `Hom.ext` is not triggered automatically
@[ext]
lemma hom_ext {M N : Mod_Cat A} (f₁ f₂ : M ⟶ N) (h : f₁.hom = f₂.hom) : f₁ = f₂ :=
  Mod_Class.Hom.ext h

@[simp]
theorem id_hom' (M : Mod_Cat A) : (𝟙 M : M ⟶ M).hom = 𝟙 M.X := by
  rfl

@[simp]
theorem comp_hom' {M N K : Mod_Cat A} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

end Mod_Cat

namespace Mod_Class

variable (A)

/-- A monoid object as a module over itself. -/
@[simps]
instance regular : Mod_Class A A where
  act := μ

instance : Inhabited (Mod_Class A A) :=
  ⟨regular A⟩

@[simps]
def comap {A B : C} [Mon_Class A] [Mon_Class B] (f : Mon_ClassHom A B) (M : C) [Mod_Class B M] :
    Mod_Class A M where
  act := (f.hom ▷ M) ≫ act
  one_act := by
    slice_lhs 1 2 => rw [← comp_whiskerRight]
    rw [f.one_hom, one_act]
  assoc := by
    -- oh, for homotopy.io in a widget!
    slice_rhs 2 3 => rw [whisker_exchange]
    simp only [whiskerRight_tensor, MonoidalCategory.whiskerLeft_comp, Category.assoc,
      Iso.hom_inv_id_assoc]
    slice_rhs 4 5 => rw [Mod_Class.assoc_flip]
    slice_rhs 3 4 => rw [associator_inv_naturality_middle]
    slice_rhs 2 4 => rw [Iso.hom_inv_id_assoc]
    slice_rhs 1 2 => rw [← MonoidalCategory.comp_whiskerRight, ← whisker_exchange]
    slice_rhs 1 2 => rw [← MonoidalCategory.comp_whiskerRight, ← tensorHom_def', ← f.mul_hom]
    rw [comp_whiskerRight, Category.assoc]

end Mod_Class

namespace Mod_Cat

/-- The forgetful functor from module objects to the ambient category. -/
def forget : Mod_Cat A ⥤ C where
  obj A := A.X
  map f := f.hom

open CategoryTheory.MonoidalCategory

/-- A morphism of monoid objects induces a "restriction" or "comap" functor
between the categories of module objects.
-/
@[simps]
def comap {A B : C} [Mon_Class A] [Mon_Class B] (f : Mon_ClassHom A B) : Mod_Cat B ⥤ Mod_Cat A where
  obj M :=
    { X := M.X
      isMod := Mod_Class.comap f M.X }
  map g :=
    { hom := g.hom
      act_hom := by
        dsimp
        slice_rhs 1 2 => rw [whisker_exchange]
        slice_rhs 2 3 => rw [← g.act_hom]
        rw [Category.assoc] }

-- Lots more could be said about `comap`, e.g. how it interacts with
-- identities, compositions, and equalities of monoid object morphisms.
end Mod_Cat
