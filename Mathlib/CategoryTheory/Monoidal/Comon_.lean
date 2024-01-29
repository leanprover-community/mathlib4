/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.CategoryTheory.Monoidal.Opposite

/-!
# The category of comonoids in a monoidal category.

We define comonoids in a monoidal category `C`,
and show that they are equivalently monoid objects in the opposite category.

## TODO
* An oplax monoidal functor takes comonoid objects to comonoid objects.
  That is, a oplax monoidal functor `F : C ⥤ D` induces a functor `Comon_ C ⥤ Comon_ D`.
* Comonoid objects in `C` are "just"
  oplax monoidal functors from the trivial monoidal category to `C`.
* The category of comonoids in a braided monoidal category is monoidal.
  (It may suffice to transfer this across the equivalent to monoids in the opposite category.)

-/

set_option linter.uppercaseLean3 false

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
  counit_comul : comul ≫ (counit ⊗ 𝟙 X) = (λ_ X).inv := by aesop_cat
  comul_counit : comul ≫ (𝟙 X ⊗ counit) = (ρ_ X).inv := by aesop_cat
  comul_assoc : comul ≫ (comul ⊗ 𝟙 X) = comul ≫ (𝟙 X ⊗ comul) ≫ (α_ X X X).inv := by aesop_cat

attribute [reassoc] Comon_.counit_comul Comon_.comul_counit

-- We prove a more general `@[simp]` lemma below.
attribute [reassoc (attr := simp)] Comon_.comul_assoc

namespace Comon_

/-- The trivial comonoid object. We later show this is initial in `Comon_ C`.
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

@[simp]
theorem counit_comul_hom {Z : C} (f : M.X ⟶ Z) : M.comul ≫ (M.counit ⊗ f) = f ≫ (λ_ Z).inv := by
  rw [← tensor_id_comp_id_tensor, ← Category.assoc, M.counit_comul, leftUnitor_inv_naturality]

@[simp]
theorem mul_one_hom {Z : C} (f : M.X ⟶ Z) : M.comul ≫ (f ⊗ M.counit) = f ≫ (ρ_ Z).inv := by
  rw [← id_tensor_comp_tensor_id, ← Category.assoc, M.comul_counit, rightUnitor_inv_naturality]

theorem assoc_flip :
    M.comul ≫ (𝟙 M.X ⊗ M.comul) = M.comul ≫ (M.comul ⊗ 𝟙 M.X) ≫ (α_ M.X M.X M.X).hom := by simp

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
theorem comp_hom' {M N K : Comon_ C} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : Hom M K).hom = f.hom ≫ g.hom :=
  rfl

section

variable (C)

/-- The forgetful functor from comonoid objects to the ambient category. -/
@[simps]
def forget : Comon_ C ⥤ C where
  obj A := A.X
  map f := f.hom

end

instance forget_faithful : Faithful (@forget C _ _) where

instance {A B : Comon_ C} (f : A ⟶ B) [e : IsIso ((forget C).map f)] : IsIso f.hom := e

/-- The forgetful functor from comonoid objects to the ambient category reflects isomorphisms. -/
instance : ReflectsIsomorphisms (forget C) where
  reflects f e :=
    ⟨⟨{ hom := inv f.hom }, by aesop_cat⟩⟩

/-- Construct an isomorphism of monoids by giving an isomorphism between the underlying objects
and checking compatibility with unit and multiplication only in the forward direction.
-/
def isoOfIso {M N : Comon_ C} (f : M.X ≅ N.X) (f_counit : f.hom ≫ N.counit = M.counit)
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

open Opposite

variable (C)

/--
Turn a comonoid object into a monoid object in the opposite category.
-/
@[simps] def Comon_to_Mon_op_op_obj (A : Comon_ C) : Mon_ (Cᵒᵖ) where
  X := op A.X
  one := A.counit.op
  mul := A.comul.op
  one_mul := by
    rw [op_leftUnitor]
    dsimp
    rw [← A.counit_comul, op_comp, op_tensorHom]
    rfl
  mul_one := by
    rw [op_rightUnitor]
    dsimp
    rw [← A.comul_counit, op_comp, op_tensorHom]
    rfl
  mul_assoc := by
    rw [op_associator]
    dsimp
    rw [← op_id, op_tensor_op, op_tensor_op, ← op_comp, ← op_comp, ← op_comp]
    rw [Category.assoc, ← A.comul_assoc]

/--
The contravariant functor turning comonoid objects into monoid objects in the opposite category.
-/
def Comon_to_Mon_op_op : Comon_ C ⥤ (Mon_ (Cᵒᵖ))ᵒᵖ where
  obj A := op (Comon_to_Mon_op_op_obj C A)
  map := fun f => op <|
    { hom := f.hom.op
      one_hom := by apply Quiver.Hom.unop_inj; simp
      mul_hom := by apply Quiver.Hom.unop_inj; simp [op_tensorHom] }

/--
Turn a monoid object in the opposite category into a comonoid object.
-/
@[simps] def Mon_op_op_to_Comon_obj (A : (Mon_ (Cᵒᵖ))) : Comon_ C where
  X := unop A.X
  counit := A.one.unop
  comul := A.mul.unop
  counit_comul := by
    rw [← unop_id, unop_tensor_unop, ← unop_comp, A.one_mul]
    rfl
  comul_counit := by
    rw [← unop_id, unop_tensor_unop, ← unop_comp, A.mul_one]
    rfl
  comul_assoc := by
    rw [← unop_id, unop_tensor_unop, unop_tensor_unop, ← unop_comp, A.mul_assoc,
      op_associator]
    simp

/--
The contravariant functor turning monoid objects in the opposite category into comonoid objects.
-/
def Mon_op_op_to_Comon : (Mon_ (Cᵒᵖ))ᵒᵖ ⥤ Comon_ C where
  obj A := Mon_op_op_to_Comon_obj C (unop A)
  map := fun f =>
    { hom := f.unop.hom.unop
      hom_counit := by apply Quiver.Hom.op_inj; simp
      hom_comul := by apply Quiver.Hom.op_inj; simp [op_tensorHom] }

/--
Comonoid objects are contravariantly equivalent to monoid objects in the opposite category.
-/
def Comon_equiv_Mon_op_op : Comon_ C ≌ (Mon_ (Cᵒᵖ))ᵒᵖ :=
  { functor := Comon_to_Mon_op_op C
    inverse := Mon_op_op_to_Comon C
    unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
    counitIso := NatIso.ofComponents (fun _ => Iso.refl _) }

end Comon_
