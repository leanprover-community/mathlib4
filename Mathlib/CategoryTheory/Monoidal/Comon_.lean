/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# The category of comonoids in a monoidal category.

We define comonoids in a monoidal category `C`.

## TODO
* `Comon_ C ≌ Mon_ (Cᵒᵖ)`
* An oplax monoidal functor takes comonoid objects to comonoid objects.
  That is, a oplax monoidal functor `F : C ⥤ D` induces a functor `Comon_ C ⥤ Comon_ D`.
* Comonoid objects in `C` are "just"
  oplax monoidal functors from the trivial monoidal category to `C`.
* The category of comonoids in a braided monoidal category is monoidal.
  (It may suffice to transfer this across the equivalent to monoids in the opposite category.)

-/

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C]

/-- A comonoid object internal to a monoidal category.

When the monoidal category is preadditive, this is also sometimes called a "coalgebra object".
-/
structure Comon_ where
  /-- The underlying object of a comonoid object. -/
  X : C
  /-- The counit of a comonoid object. -/
  counit : X ⟶ 𝟙_ C
  /-- The comultiplication morphism of a comonoid object. -/
  comul : X ⟶ X ⊗ X
  counit_comul : comul ≫ (counit ▷ X) = (λ_ X).inv := by aesop_cat
  comul_counit : comul ≫ (X ◁ counit) = (ρ_ X).inv := by aesop_cat
  comul_assoc : comul ≫ (X ◁ comul) ≫ (α_ X X X).inv = comul ≫ (comul ▷ X) := by aesop_cat

attribute [reassoc] Comon_.counit_comul Comon_.comul_counit

attribute [reassoc (attr := simp)] Comon_.comul_assoc

namespace Comon_

/-- The trivial comonoid object. We later show this is terminal in `Comon_ C`.
-/
@[simps]
def trivial : Comon_ C where
  X := 𝟙_ C
  counit := 𝟙 _
  comul := (λ_ _).inv
  comul_assoc := by coherence
  counit_comul := by coherence
  comul_counit := by coherence

instance : Inhabited (Comon_ C) :=
  ⟨trivial C⟩

variable {C}
variable {M : Comon_ C}

@[reassoc (attr := simp)]
theorem counit_comul_hom {Z : C} (f : M.X ⟶ Z) : M.comul ≫ (M.counit ⊗ f) = f ≫ (λ_ Z).inv := by
  rw [leftUnitor_inv_naturality, tensorHom_def, counit_comul_assoc]

@[reassoc (attr := simp)]
theorem comul_counit_hom {Z : C} (f : M.X ⟶ Z) : M.comul ≫ (f ⊗ M.counit) = f ≫ (ρ_ Z).inv := by
  rw [rightUnitor_inv_naturality, tensorHom_def', comul_counit_assoc]

@[reassoc (attr := simp)] theorem comul_assoc_flip :
    M.comul ≫ (M.comul ▷ M.X) ≫ (α_ M.X M.X M.X).hom = M.comul ≫ (M.X ◁ M.comul) := by
  simp [← comul_assoc_assoc]

/-- A morphism of comonoid objects. -/
@[ext]
structure Hom (M N : Comon_ C) where
  /-- The underlying morphism of a morphism of comonoid objects. -/
  hom : M.X ⟶ N.X
  hom_counit : hom ≫ N.counit = M.counit := by aesop_cat
  hom_comul : hom ≫ N.comul = M.comul ≫ (hom ⊗ hom) := by aesop_cat

attribute [reassoc (attr := simp)] Hom.hom_counit Hom.hom_comul

/-- The identity morphism on a comonoid object. -/
@[simps]
def id (M : Comon_ C) : Hom M M where
  hom := 𝟙 M.X

instance homInhabited (M : Comon_ C) : Inhabited (Hom M M) :=
  ⟨id M⟩

/-- Composition of morphisms of monoid objects. -/
@[simps]
def comp {M N O : Comon_ C} (f : Hom M N) (g : Hom N O) : Hom M O where
  hom := f.hom ≫ g.hom

instance : Category (Comon_ C) where
  Hom M N := Hom M N
  id := id
  comp f g := comp f g

@[ext] lemma ext {X Y : Comon_ C} {f g : X ⟶ Y} (w : f.hom = g.hom) : f = g := Hom.ext _ _ w

@[simp] theorem id_hom' (M : Comon_ C) : (𝟙 M : Hom M M).hom = 𝟙 M.X := rfl

@[simp]
theorem comp_hom' {M N K : Comon_ C} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

section

variable (C)

/-- The forgetful functor from comonoid objects to the ambient category. -/
@[simps]
def forget : Comon_ C ⥤ C where
  obj A := A.X
  map f := f.hom

end

instance forget_faithful : (@forget C _ _).Faithful where

instance {A B : Comon_ C} (f : A ⟶ B) [e : IsIso ((forget C).map f)] : IsIso f.hom := e

/-- The forgetful functor from comonoid objects to the ambient category reflects isomorphisms. -/
instance : (forget C).ReflectsIsomorphisms where
  reflects f e :=
    ⟨⟨{ hom := inv f.hom }, by aesop_cat⟩⟩

/-- Construct an isomorphism of monoids by giving an isomorphism between the underlying objects
and checking compatibility with unit and multiplication only in the forward direction.
-/
@[simps]
def mkIso {M N : Comon_ C} (f : M.X ≅ N.X) (f_counit : f.hom ≫ N.counit = M.counit)
    (f_comul : f.hom ≫ N.comul = M.comul ≫ (f.hom ⊗ f.hom)) : M ≅ N where
  hom :=
    { hom := f.hom
      hom_counit := f_counit
      hom_comul := f_comul }
  inv :=
    { hom := f.inv
      hom_counit := by rw [← f_counit]; simp
      hom_comul := by
        rw [← cancel_epi f.hom]
        slice_rhs 1 2 => rw [f_comul]
        simp }

instance uniqueHomToTrivial (A : Comon_ C) : Unique (A ⟶ trivial C) where
  default :=
    { hom := A.counit
      hom_counit := by dsimp; simp
      hom_comul := by dsimp; simp [A.comul_counit, unitors_inv_equal] }
  uniq f := by
    ext; simp
    rw [← Category.comp_id f.hom]
    erw [f.hom_counit]

open CategoryTheory.Limits

instance : HasTerminal (Comon_ C) :=
  hasTerminal_of_unique (trivial C)

end Comon_
