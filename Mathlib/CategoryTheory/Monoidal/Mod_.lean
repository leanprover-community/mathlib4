/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Paul Lezeau
-/
import Mathlib.CategoryTheory.Monoidal.Mon_

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

/-- An action of a monoid object `M` on an object `X` is the data of a map `smul : M ⊗ X ⟶ X` that
satisfies unitality and associativity with multiplication.

See `MulAction` for the non-categorical version. -/
class Mod_Class (X : C) where
  /-- The action map -/
  smul : M ⊗ X ⟶ X
  /-- The identity acts trivially. -/
  one_smul (X) : η ▷ X ≫ smul = (λ_ X).hom := by aesop_cat
  /-- The action map is compatible with multiplication. -/
  mul_smul (X) : μ ▷ X ≫ smul = (α_ M M X).hom ≫ M ◁ smul ≫ smul := by aesop_cat

attribute [reassoc (attr := simp)] Mod_Class.mul_smul Mod_Class.one_smul

@[inherit_doc] scoped[Mon_Class] notation "γ" => Mod_Class.smul
@[inherit_doc] scoped[Mon_Class] notation "γ["X"]" => Mod_Class.smul (X := X)

namespace Mod_Class

theorem assoc_flip (X : C) [Mod_Class M X] : M ◁ γ ≫ γ[X] = (α_ M M X).inv ≫ μ[M] ▷ X ≫ γ := by
  simp

/-- The action of a monoid object on itself. -/
-- See note [reducible non instances]
abbrev regular : Mod_Class M M where smul := μ

instance {A : Mon_ C} (M : Mod_ A) : Mod_Class A.X M.X where
  smul := M.smul
  one_smul := M.one_smul
  mul_smul := M.assoc

end Mod_Class

/-- Construct an object of `Mod_ (Mon_.mk' M)` from an object `X : C` and a
`Mod_Class M X` instance. -/
@[simps]
def Mod_.mk' (X : C) [Mod_Class M X] : Mod_ (.mk M) where
  X := X
  smul := γ[M]

end Mod_Class
