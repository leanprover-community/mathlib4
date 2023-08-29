/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Data.Int.Basic
import Mathlib.CategoryTheory.Shift.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Basic

#align_import category_theory.differential_object from "leanprover-community/mathlib"@"6876fa15e3158ff3e4a4e2af1fb6e1945c6e8803"

/-!
# Differential objects in a category.

A differential object in a category with zero morphisms and a shift is
an object `X` equipped with
a morphism `d : obj ⟶ obj⟦1⟧`, such that `d^2 = 0`.

We build the category of differential objects, and some basic constructions
such as the forgetful functor, zero morphisms and zero objects, and the shift functor
on differential objects.
-/


open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable (S : Type*) [AddMonoidWithOne S] (C : Type u) [Category.{v} C]

variable [HasZeroMorphisms C] [HasShift C S]

/-- A differential object in a category with zero morphisms and a shift is
an object `obj` equipped with
a morphism `d : obj ⟶ obj⟦1⟧`, such that `d^2 = 0`. -/
-- Porting note: Removed `@[nolint has_nonempty_instance]`
structure DifferentialObject where
  /-- The underlying object of a differential object. -/
  obj : C
  /-- The differential of a differential object. -/
  d : obj ⟶ obj⟦(1 : S)⟧
  /-- The differential `d` satisfies that `d² = 0`. -/
  d_squared : d ≫ d⟦(1 : S)⟧' = 0 := by aesop_cat
#align category_theory.differential_object CategoryTheory.DifferentialObject
set_option linter.uppercaseLean3 false in
#align category_theory.differential_object.X CategoryTheory.DifferentialObject.obj

attribute [reassoc (attr := simp)] DifferentialObject.d_squared

variable {S C}

namespace DifferentialObject

/-- A morphism of differential objects is a morphism commuting with the differentials. -/
@[ext] -- Porting note: Removed `nolint has_nonempty_instance`
structure Hom (X Y : DifferentialObject S C) where
  /-- The morphism between underlying objects of the two differentiable objects. -/
  f : X.obj ⟶ Y.obj
  comm : X.d ≫ f⟦1⟧' = f ≫ Y.d := by aesop_cat
#align category_theory.differential_object.hom CategoryTheory.DifferentialObject.Hom

attribute [reassoc (attr := simp)] Hom.comm

namespace Hom

/-- The identity morphism of a differential object. -/
@[simps]
def id (X : DifferentialObject S C) : Hom X X where
  f := 𝟙 X.obj
#align category_theory.differential_object.hom.id CategoryTheory.DifferentialObject.Hom.id

/-- The composition of morphisms of differential objects. -/
@[simps]
def comp {X Y Z : DifferentialObject S C} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  f := f.f ≫ g.f
#align category_theory.differential_object.hom.comp CategoryTheory.DifferentialObject.Hom.comp

end Hom

instance categoryOfDifferentialObjects : Category (DifferentialObject S C) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp f g
#align category_theory.differential_object.category_of_differential_objects CategoryTheory.DifferentialObject.categoryOfDifferentialObjects

-- Porting note: added
@[ext]
theorem ext {A B : DifferentialObject S C} {f g : A ⟶ B} (w : f.f = g.f := by aesop_cat) : f = g :=
  Hom.ext _ _ w

@[simp]
theorem id_f (X : DifferentialObject S C) : (𝟙 X : X ⟶ X).f = 𝟙 X.obj := rfl
#align category_theory.differential_object.id_f CategoryTheory.DifferentialObject.id_f

@[simp]
theorem comp_f {X Y Z : DifferentialObject S C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).f = f.f ≫ g.f :=
  rfl
#align category_theory.differential_object.comp_f CategoryTheory.DifferentialObject.comp_f

@[simp]
theorem eqToHom_f {X Y : DifferentialObject S C} (h : X = Y) :
    Hom.f (eqToHom h) = eqToHom (congr_arg _ h) := by
  subst h
  -- ⊢ (eqToHom (_ : X = X)).f = eqToHom (_ : X.obj = X.obj)
  rw [eqToHom_refl, eqToHom_refl]
  -- ⊢ (𝟙 X).f = 𝟙 X.obj
  rfl
  -- 🎉 no goals
#align category_theory.differential_object.eq_to_hom_f CategoryTheory.DifferentialObject.eqToHom_f

variable (S C)

/-- The forgetful functor taking a differential object to its underlying object. -/
def forget : DifferentialObject S C ⥤ C where
  obj X := X.obj
  map f := f.f
#align category_theory.differential_object.forget CategoryTheory.DifferentialObject.forget

instance forget_faithful : Faithful (forget S C) where
#align category_theory.differential_object.forget_faithful CategoryTheory.DifferentialObject.forget_faithful

variable [(shiftFunctor C (1 : S)).PreservesZeroMorphisms]

instance {X Y : DifferentialObject S C} : Zero (X ⟶ Y) := ⟨{f := 0}⟩

variable {S C}

@[simp]
theorem zero_f (P Q : DifferentialObject S C) : (0 : P ⟶ Q).f = 0 := rfl
#align category_theory.differential_object.zero_f CategoryTheory.DifferentialObject.zero_f

instance hasZeroMorphisms : HasZeroMorphisms (DifferentialObject S C) where
#align category_theory.differential_object.has_zero_morphisms CategoryTheory.DifferentialObject.hasZeroMorphisms

/-- An isomorphism of differential objects gives an isomorphism of the underlying objects. -/
@[simps]
def isoApp {X Y : DifferentialObject S C} (f : X ≅ Y) : X.obj ≅ Y.obj where
  hom := f.hom.f
  inv := f.inv.f
  hom_inv_id := by rw [← comp_f, Iso.hom_inv_id, id_f]
                   -- 🎉 no goals
  inv_hom_id := by rw [← comp_f, Iso.inv_hom_id, id_f]
                   -- 🎉 no goals
#align category_theory.differential_object.iso_app CategoryTheory.DifferentialObject.isoApp

@[simp]
theorem isoApp_refl (X : DifferentialObject S C) : isoApp (Iso.refl X) = Iso.refl X.obj := rfl
#align category_theory.differential_object.iso_app_refl CategoryTheory.DifferentialObject.isoApp_refl

@[simp]
theorem isoApp_symm {X Y : DifferentialObject S C} (f : X ≅ Y) : isoApp f.symm = (isoApp f).symm :=
  rfl
#align category_theory.differential_object.iso_app_symm CategoryTheory.DifferentialObject.isoApp_symm

@[simp]
theorem isoApp_trans {X Y Z : DifferentialObject S C} (f : X ≅ Y) (g : Y ≅ Z) :
    isoApp (f ≪≫ g) = isoApp f ≪≫ isoApp g := rfl
#align category_theory.differential_object.iso_app_trans CategoryTheory.DifferentialObject.isoApp_trans

/-- An isomorphism of differential objects can be constructed
from an isomorphism of the underlying objects that commutes with the differentials. -/
@[simps]
def mkIso {X Y : DifferentialObject S C} (f : X.obj ≅ Y.obj) (hf : X.d ≫ f.hom⟦1⟧' = f.hom ≫ Y.d) :
    X ≅ Y where
  hom := ⟨f.hom, hf⟩
  inv := ⟨f.inv, by
    rw [← Functor.mapIso_inv, Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, Functor.mapIso_hom,
      hf]⟩
  hom_inv_id := by ext1; dsimp; exact f.hom_inv_id
                   -- ⊢ autoParam ((Hom.mk f.hom ≫ Hom.mk f.inv).f = (𝟙 X).f) _auto✝
                         -- ⊢ autoParam (f.hom ≫ f.inv = 𝟙 X.obj) _auto✝
                                -- 🎉 no goals
  inv_hom_id := by ext1; dsimp; exact f.inv_hom_id
                   -- ⊢ autoParam ((Hom.mk f.inv ≫ Hom.mk f.hom).f = (𝟙 Y).f) _auto✝
                         -- ⊢ autoParam (f.inv ≫ f.hom = 𝟙 Y.obj) _auto✝
                                -- 🎉 no goals
#align category_theory.differential_object.mk_iso CategoryTheory.DifferentialObject.mkIso

end DifferentialObject

namespace Functor

universe v' u'

variable (D : Type u') [Category.{v'} D]

variable [HasZeroMorphisms D] [HasShift D S]

/-- A functor `F : C ⥤ D` which commutes with shift functors on `C` and `D` and preserves zero
morphisms can be lifted to a functor `DifferentialObject S C ⥤ DifferentialObject S D`. -/
@[simps]
def mapDifferentialObject (F : C ⥤ D)
    (η : (shiftFunctor C (1 : S)).comp F ⟶ F.comp (shiftFunctor D (1 : S)))
    (hF : ∀ c c', F.map (0 : c ⟶ c') = 0) : DifferentialObject S C ⥤ DifferentialObject S D where
  obj X :=
    { obj := F.obj X.obj
      d := F.map X.d ≫ η.app X.obj
      d_squared := by
        rw [Functor.map_comp, ← Functor.comp_map F (shiftFunctor D (1 : S))]
        -- ⊢ (F.map X.d ≫ NatTrans.app η X.obj) ≫ (F ⋙ shiftFunctor D 1).map X.d ≫ (shift …
        slice_lhs 2 3 => rw [← η.naturality X.d]
        -- ⊢ F.map X.d ≫ ((shiftFunctor C 1 ⋙ F).map X.d ≫ NatTrans.app η ((shiftFunctor  …
        rw [Functor.comp_map]
        -- ⊢ F.map X.d ≫ (F.map ((shiftFunctor C 1).map X.d) ≫ NatTrans.app η ((shiftFunc …
        slice_lhs 1 2 => rw [← F.map_comp, X.d_squared, hF]
        -- ⊢ (0 ≫ NatTrans.app η ((shiftFunctor C 1).obj X.obj)) ≫ (shiftFunctor D 1).map …
        rw [zero_comp, zero_comp] }
        -- 🎉 no goals
  map f :=
    { f := F.map f.f
      comm := by
        dsimp
        -- ⊢ (F.map X✝.d ≫ NatTrans.app η X✝.obj) ≫ (shiftFunctor D 1).map (F.map f.f) =  …
        slice_lhs 2 3 => rw [← Functor.comp_map F (shiftFunctor D (1 : S)), ← η.naturality f.f]
        -- ⊢ F.map X✝.d ≫ (shiftFunctor C 1 ⋙ F).map f.f ≫ NatTrans.app η Y✝.obj = F.map  …
        slice_lhs 1 2 => rw [Functor.comp_map, ← F.map_comp, f.comm, F.map_comp]
        -- ⊢ (F.map f.f ≫ F.map Y✝.d) ≫ NatTrans.app η Y✝.obj = F.map f.f ≫ F.map Y✝.d ≫  …
        rw [Category.assoc] }
        -- 🎉 no goals
  map_id := by intros; ext; simp
               -- ⊢ { obj := fun X => DifferentialObject.mk (F.obj X.obj) (F.map X.d ≫ NatTrans. …
                       -- ⊢ autoParam (({ obj := fun X => DifferentialObject.mk (F.obj X.obj) (F.map X.d …
                            -- 🎉 no goals
  map_comp := by intros; ext; simp
                 -- ⊢ { obj := fun X => DifferentialObject.mk (F.obj X.obj) (F.map X.d ≫ NatTrans. …
                         -- ⊢ autoParam (({ obj := fun X => DifferentialObject.mk (F.obj X.obj) (F.map X.d …
                              -- 🎉 no goals
#align category_theory.functor.map_differential_object CategoryTheory.Functor.mapDifferentialObject

end Functor

end CategoryTheory

namespace CategoryTheory

namespace DifferentialObject

variable (S : Type*) [AddMonoidWithOne S] (C : Type u) [Category.{v} C]

variable [HasZeroObject C] [HasZeroMorphisms C] [HasShift C S]
variable [(shiftFunctor C (1 : S)).PreservesZeroMorphisms]

open scoped ZeroObject

instance hasZeroObject : HasZeroObject (DifferentialObject S C) := by
  -- Porting note(https://github.com/leanprover-community/mathlib4/issues/4998): added `aesop_cat`
  -- Porting note: added `simp only [eq_iff_true_of_subsingleton]`
  refine' ⟨⟨⟨0, 0, by aesop_cat⟩, fun X => ⟨⟨⟨⟨0, by aesop_cat⟩⟩, fun f => _⟩⟩,
    fun X => ⟨⟨⟨⟨0, by aesop_cat⟩⟩, fun f => _⟩⟩⟩⟩ <;> ext <;>
                                                       -- ⊢ autoParam (f.f = default.f) _auto✝
                                                       -- ⊢ autoParam (f.f = default.f) _auto✝
    simp only [eq_iff_true_of_subsingleton]
    -- 🎉 no goals
    -- 🎉 no goals
#align category_theory.differential_object.has_zero_object CategoryTheory.DifferentialObject.hasZeroObject

end DifferentialObject

namespace DifferentialObject

variable (S : Type*) [AddMonoidWithOne S]
variable (C : Type (u + 1)) [LargeCategory C] [ConcreteCategory C] [HasZeroMorphisms C]
variable [HasShift C S]

instance concreteCategoryOfDifferentialObjects : ConcreteCategory (DifferentialObject S C) where
  forget := forget S C ⋙ CategoryTheory.forget C
#align category_theory.differential_object.concrete_category_of_differential_objects CategoryTheory.DifferentialObject.concreteCategoryOfDifferentialObjects

instance : HasForget₂ (DifferentialObject S C) C where
  forget₂ := forget S C

end DifferentialObject

/-! The category of differential objects itself has a shift functor. -/


namespace DifferentialObject

variable {S : Type*} [AddCommGroupWithOne S] (C : Type u) [Category.{v} C]

variable [HasZeroMorphisms C] [HasShift C S]

noncomputable section

/-- The shift functor on `DifferentialObject S C`. -/
@[simps]
def shiftFunctor (n : S) : DifferentialObject S C ⥤ DifferentialObject S C where
  obj X :=
    { obj := X.obj⟦n⟧
      d := X.d⟦n⟧' ≫ (shiftComm _ _ _).hom
      d_squared := by
        rw [Functor.map_comp, Category.assoc, shiftComm_hom_comp_assoc, ← Functor.map_comp_assoc,
          X.d_squared, Functor.map_zero, zero_comp] }
  map f :=
    { f := f.f⟦n⟧'
      comm := by
        dsimp
        -- ⊢ ((CategoryTheory.shiftFunctor C n).map X✝.d ≫ NatTrans.app (shiftFunctorComm …
        erw [Category.assoc, shiftComm_hom_comp, ← Functor.map_comp_assoc, f.comm,
          Functor.map_comp_assoc]
        rfl }
        -- 🎉 no goals
  map_id X := by ext1; dsimp; rw [Functor.map_id]
                 -- ⊢ autoParam (({ obj := fun X => mk ((CategoryTheory.shiftFunctor C n).obj X.ob …
                       -- ⊢ autoParam ((CategoryTheory.shiftFunctor C n).map (𝟙 X.obj) = 𝟙 ((CategoryThe …
                              -- 🎉 no goals
  map_comp f g := by ext1; dsimp; rw [Functor.map_comp]
                     -- ⊢ autoParam (({ obj := fun X => mk ((CategoryTheory.shiftFunctor C n).obj X.ob …
                           -- ⊢ autoParam ((CategoryTheory.shiftFunctor C n).map (f.f ≫ g.f) = (CategoryTheo …
                                  -- 🎉 no goals
#align category_theory.differential_object.shift_functor CategoryTheory.DifferentialObject.shiftFunctor

/-- The shift functor on `DifferentialObject S C` is additive. -/
@[simps!]
nonrec def shiftFunctorAdd (m n : S) :
    shiftFunctor C (m + n) ≅ shiftFunctor C m ⋙ shiftFunctor C n := by
  refine' NatIso.ofComponents (fun X => mkIso (shiftAdd X.obj _ _) _) (fun f => _)
  -- ⊢ ((shiftFunctor C (m + n)).obj X).d ≫ (CategoryTheory.shiftFunctor C 1).map ( …
  · dsimp
    -- ⊢ ((CategoryTheory.shiftFunctor C (m + n)).map X.d ≫ NatTrans.app (shiftFuncto …
    rw [← cancel_epi ((shiftFunctorAdd C m n).inv.app X.obj)]
    -- ⊢ NatTrans.app (CategoryTheory.shiftFunctorAdd C m n).inv X.obj ≫ ((CategoryTh …
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    -- ⊢ NatTrans.app (CategoryTheory.shiftFunctorAdd C m n).inv X.obj ≫ (CategoryThe …
    erw [← NatTrans.naturality_assoc]
    -- ⊢ (CategoryTheory.shiftFunctor C m ⋙ CategoryTheory.shiftFunctor C n).map X.d  …
    dsimp
    -- ⊢ (CategoryTheory.shiftFunctor C n).map ((CategoryTheory.shiftFunctor C m).map …
    simp only [Functor.map_comp, Category.assoc,
      shiftFunctorComm_hom_app_comp_shift_shiftFunctorAdd_hom_app 1 m n X.obj,
      Iso.inv_hom_id_app_assoc]
  · ext; dsimp; exact NatTrans.naturality _ _
    -- ⊢ autoParam (((shiftFunctor C (m + n)).map f ≫ ((fun X => mkIso (shiftAdd X.ob …
         -- ⊢ autoParam ((CategoryTheory.shiftFunctor C (m + n)).map f.f ≫ NatTrans.app (C …
                -- 🎉 no goals
#align category_theory.differential_object.shift_functor_add CategoryTheory.DifferentialObject.shiftFunctorAdd

section

/-- The shift by zero is naturally isomorphic to the identity. -/
@[simps!]
def shiftZero : shiftFunctor C (0 : S) ≅ 𝟭 (DifferentialObject S C) := by
  refine' NatIso.ofComponents (fun X => mkIso ((shiftFunctorZero C S).app X.obj) _) (fun f => _)
  -- ⊢ ((shiftFunctor C 0).obj X).d ≫ (CategoryTheory.shiftFunctor C 1).map ((shift …
  · erw [← NatTrans.naturality]
    -- ⊢ ((shiftFunctor C 0).obj X).d ≫ (CategoryTheory.shiftFunctor C 1).map ((shift …
    dsimp
    -- ⊢ ((CategoryTheory.shiftFunctor C 0).map X.d ≫ NatTrans.app (shiftFunctorComm  …
    simp only [shiftFunctorZero_hom_app_shift, Category.assoc]
    -- 🎉 no goals
  · aesop_cat
    -- 🎉 no goals
#align category_theory.differential_object.shift_zero CategoryTheory.DifferentialObject.shiftZero

end

instance : HasShift (DifferentialObject S C) S :=
  hasShiftMk _ _
    { F := shiftFunctor C
      zero := shiftZero C
      add := shiftFunctorAdd C
      assoc_hom_app := fun m₁ m₂ m₃ X => by
        ext1
        -- ⊢ autoParam ((NatTrans.app (shiftFunctorAdd C (m₁ + m₂) m₃).hom X ≫ (shiftFunc …
        convert shiftFunctorAdd_assoc_hom_app m₁ m₂ m₃ X.obj
        -- ⊢ (eqToHom (_ : (shiftFunctor C (m₁ + m₂ + m₃)).obj X = (shiftFunctor C (m₁ +  …
        dsimp [shiftFunctorAdd']
        -- ⊢ (eqToHom (_ : (shiftFunctor C (m₁ + m₂ + m₃)).obj X = (shiftFunctor C (m₁ +  …
        simp
        -- 🎉 no goals
      zero_add_hom_app := fun n X => by
        ext1
        -- ⊢ autoParam ((NatTrans.app (shiftFunctorAdd C 0 n).hom X).f = (eqToHom (_ : (s …
        convert shiftFunctorAdd_zero_add_hom_app n X.obj
        -- ⊢ (eqToHom (_ : (shiftFunctor C (0 + n)).obj X = (shiftFunctor C n).obj ((𝟭 (D …
        simp
        -- 🎉 no goals
      add_zero_hom_app := fun n X => by
        ext1
        -- ⊢ autoParam ((NatTrans.app (shiftFunctorAdd C n 0).hom X).f = (eqToHom (_ : (s …
        convert shiftFunctorAdd_add_zero_hom_app n X.obj
        -- ⊢ (eqToHom (_ : (shiftFunctor C (n + 0)).obj X = (𝟭 (DifferentialObject S C)). …
        simp }
        -- 🎉 no goals

end

end DifferentialObject

end CategoryTheory
