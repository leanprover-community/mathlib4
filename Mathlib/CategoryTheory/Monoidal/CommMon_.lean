/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Mon_

/-!
# The category of commutative monoids in a braided monoidal category.
-/


universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C] [BraidedCategory.{v₁} C]

/-- A commutative monoid object internal to a monoidal category.
-/
structure CommMon_ extends Mon_ C where
  mul_comm : (β_ _ _).hom ≫ mul = mul := by aesop_cat

attribute [reassoc (attr := simp)] CommMon_.mul_comm

namespace CommMon_

/-- The trivial commutative monoid object. We later show this is initial in `CommMon_ C`.
-/
@[simps!]
def trivial : CommMon_ C :=
  { Mon_.trivial C with mul_comm := by dsimp; rw [braiding_leftUnitor, unitors_equal] }

instance : Inhabited (CommMon_ C) :=
  ⟨trivial C⟩

variable {C}
variable {M : CommMon_ C}

instance : Category (CommMon_ C) :=
  InducedCategory.category CommMon_.toMon_

@[simp]
theorem id_hom (A : CommMon_ C) : Mon_.Hom.hom (𝟙 A) = 𝟙 A.X :=
  rfl

@[simp]
theorem comp_hom {R S T : CommMon_ C} (f : R ⟶ S) (g : S ⟶ T) :
    Mon_.Hom.hom (f ≫ g) = f.hom ≫ g.hom :=
  rfl

@[ext]
lemma hom_ext {A B : CommMon_ C} (f g : A ⟶ B) (h : f.hom = g.hom) : f = g :=
  Mon_.Hom.ext h

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/10688): the following two lemmas `id'` and `comp'`
-- have been added to ease automation;
@[simp]
lemma id' (A : CommMon_ C) : (𝟙 A : A.toMon_ ⟶ A.toMon_) = 𝟙 (A.toMon_) := rfl

@[simp]
lemma comp' {A₁ A₂ A₃ : CommMon_ C} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) :
    ((f ≫ g : A₁ ⟶ A₃) : A₁.toMon_ ⟶ A₃.toMon_) = @CategoryStruct.comp (Mon_ C) _ _ _ _ f g := rfl

section

variable (C)

/-- The forgetful functor from commutative monoid objects to monoid objects. -/
def forget₂Mon_ : CommMon_ C ⥤ Mon_ C :=
  inducedFunctor CommMon_.toMon_

/-- The forgetful functor from commutative monoid objects to monoid objects
is fully faithful. -/
def fullyFaithfulForget₂Mon_ : (forget₂Mon_ C).FullyFaithful :=
  fullyFaithfulInducedFunctor _
-- The `Full, Faithful` instances should be constructed by a deriving handler.
-- https://github.com/leanprover-community/mathlib4/issues/380

instance : (forget₂Mon_ C).Full := InducedCategory.full _
instance : (forget₂Mon_ C).Faithful := InducedCategory.faithful _

@[simp]
theorem forget₂Mon_obj_one (A : CommMon_ C) : ((forget₂Mon_ C).obj A).one = A.one :=
  rfl

@[simp]
theorem forget₂Mon_obj_mul (A : CommMon_ C) : ((forget₂Mon_ C).obj A).mul = A.mul :=
  rfl

@[simp]
theorem forget₂Mon_map_hom {A B : CommMon_ C} (f : A ⟶ B) : ((forget₂Mon_ C).map f).hom = f.hom :=
  rfl

@[deprecated (since := "2025-02-07")] alias forget₂_Mon_obj_one := forget₂Mon_obj_one
@[deprecated (since := "2025-02-07")] alias forget₂_Mon_obj_mul := forget₂Mon_obj_mul
@[deprecated (since := "2025-02-07")] alias forget₂_Mon_map_hom := forget₂Mon_map_hom

/-- The forgetful functor from commutative monoid objects to the ambient category. -/
@[simps!]
def forget : CommMon_ C ⥤ C :=
  forget₂Mon_ C ⋙ Mon_.forget C

instance : (forget C).Faithful where

@[simp]
theorem forget₂Mon_comp_forget : forget₂Mon_ C ⋙ Mon_.forget C = forget C := rfl

end

section

variable {M N : CommMon_ C} (f : M.X ≅ N.X) (one_f : M.one ≫ f.hom = N.one := by aesop_cat)
  (mul_f : M.mul ≫ f.hom = (f.hom ⊗ f.hom) ≫ N.mul := by aesop_cat)

/-- Constructor for isomorphisms in the category `CommMon_ C`. -/
def mkIso : M ≅ N :=
  (fullyFaithfulForget₂Mon_ C).preimageIso (Mon_.mkIso f one_f mul_f)

@[simp] lemma mkIso_hom_hom : (mkIso f one_f mul_f).hom.hom = f.hom := rfl
@[simp] lemma mkIso_inv_hom : (mkIso f one_f mul_f).inv.hom = f.inv := rfl

end

instance uniqueHomFromTrivial (A : CommMon_ C) : Unique (trivial C ⟶ A) :=
  Mon_.uniqueHomFromTrivial A.toMon_

open CategoryTheory.Limits

instance : HasInitial (CommMon_ C) :=
  hasInitial_of_unique (trivial C)

end CommMon_

namespace CategoryTheory.Functor

variable {C} {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D] [BraidedCategory.{v₂} D]

/-- A lax braided functor takes commutative monoid objects to commutative monoid objects.

That is, a lax braided functor `F : C ⥤ D` induces a functor `CommMon_ C ⥤ CommMon_ D`.
-/
@[simps!]
def mapCommMon (F : C ⥤ D) [F.LaxBraided] : CommMon_ C ⥤ CommMon_ D where
  obj A :=
    { F.mapMon.obj A.toMon_ with
      mul_comm := by
        dsimp
        rw [← Functor.LaxBraided.braided_assoc, ← Functor.map_comp, A.mul_comm] }
  map f := F.mapMon.map f

variable (C) (D)

/-- `mapCommMon` is functorial in the lax braided functor. -/
@[simps]
def mapCommMonFunctor : LaxBraidedFunctor C D ⥤ CommMon_ C ⥤ CommMon_ D where
  obj F := F.mapCommMon
  map α := { app := fun A => { hom := α.hom.app A.X } }
  map_comp _ _ := rfl

end CategoryTheory.Functor

namespace CommMon_

open CategoryTheory.LaxBraidedFunctor

namespace EquivLaxBraidedFunctorPUnit

/-- Implementation of `CommMon_.equivLaxBraidedFunctorPUnit`. -/
@[simps]
def laxBraidedToCommMon : LaxBraidedFunctor (Discrete PUnit.{u + 1}) C ⥤ CommMon_ C where
  obj F := (F.mapCommMon : CommMon_ _ ⥤ CommMon_ C).obj (trivial (Discrete PUnit.{u+1}))
  map α := ((Functor.mapCommMonFunctor (Discrete PUnit) C).map α).app _

variable {C}

/-- Implementation of `CommMon_.equivLaxBraidedFunctorPUnit`. -/
@[simps!]
def commMonToLaxBraidedObj (A : CommMon_ C) :
    Discrete PUnit.{u + 1} ⥤ C := (Functor.const _).obj A.X

instance (A : CommMon_ C) : (commMonToLaxBraidedObj A).LaxMonoidal where
  ε' := A.one
  μ' := fun _ _ => A.mul

open Functor.LaxMonoidal

@[simp]
lemma commMonToLaxBraidedObj_ε (A : CommMon_ C) :
    ε (commMonToLaxBraidedObj A) = A.one := rfl

@[simp]
lemma commMonToLaxBraidedObj_μ (A : CommMon_ C) (X Y) :
    μ (commMonToLaxBraidedObj A) X Y = A.mul := rfl

instance (A : CommMon_ C) : (commMonToLaxBraidedObj A).LaxBraided where

variable (C)
/-- Implementation of `CommMon_.equivLaxBraidedFunctorPUnit`. -/
@[simps]
def commMonToLaxBraided : CommMon_ C ⥤ LaxBraidedFunctor (Discrete PUnit.{u + 1}) C where
  obj A := LaxBraidedFunctor.of (commMonToLaxBraidedObj A)
  map f :=
    { hom := { app := fun _ => f.hom }
      isMonoidal := { } }

/-- Implementation of `CommMon_.equivLaxBraidedFunctorPUnit`. -/
@[simps!]
def unitIso :
    𝟭 (LaxBraidedFunctor (Discrete PUnit.{u + 1}) C) ≅
        laxBraidedToCommMon C ⋙ commMonToLaxBraided C :=
  NatIso.ofComponents
    (fun F ↦ LaxBraidedFunctor.isoOfComponents (fun _ ↦ F.mapIso (eqToIso (by ext))))
    (fun f ↦ by ext ⟨⟨⟩⟩; dsimp; simp)

/-- Implementation of `CommMon_.equivLaxBraidedFunctorPUnit`. -/
@[simps!]
def counitIso : commMonToLaxBraided C ⋙ laxBraidedToCommMon C ≅ 𝟭 (CommMon_ C) :=
  NatIso.ofComponents (fun F ↦ mkIso (Iso.refl _))

end EquivLaxBraidedFunctorPUnit

open EquivLaxBraidedFunctorPUnit

/-- Commutative monoid objects in `C` are "just" braided lax monoidal functors from the trivial
braided monoidal category to `C`.
-/
@[simps]
def equivLaxBraidedFunctorPUnit : LaxBraidedFunctor (Discrete PUnit.{u + 1}) C ≌ CommMon_ C where
  functor := laxBraidedToCommMon C
  inverse := commMonToLaxBraided C
  unitIso := unitIso C
  counitIso := counitIso C

end CommMon_

namespace CommMon_

variable {C}

/-- Construct an object of `CommMon_ C` from an object `X : C` a `Mon_Class X` instance
and a `IsCommMon X` insance. -/
def mk' (X : C) [Mon_Class X] [IsCommMon X] : CommMon_ C where
  __ := Mon_.mk' X
  mul_comm := IsCommMon.mul_comm X

instance (X : CommMon_ C) : IsCommMon X.X where
  mul_comm' := X.mul_comm

end CommMon_
