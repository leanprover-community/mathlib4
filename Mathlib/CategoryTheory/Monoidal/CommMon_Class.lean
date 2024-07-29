/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Mon_Class

/-!
# The category of commutative monoids in a braided monoidal category.
-/


universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory

open scoped Mon_

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C] [BraidedCategory.{v₁} C]

/-- A commutative monoid object internal to a monoidal category.
-/
class CommMon_ (M : C) extends Mon_ M where
  mul_comm' : (β_ M M).hom ≫ μ = μ := by aesop_cat

namespace CommMon_

@[reassoc (attr := simp)]
theorem mul_comm (M : C) [CommMon_ M] : (β_ M M).hom ≫ μ = μ :=
  CommMon_.mul_comm'

/-- The trivial commutative monoid object. We later show this is initial in `CommMon_Cat C`.
-/
@[simps!]
instance trivial : CommMon_ (𝟙_ C) :=
  { Mon_.trivial C with mul_comm' := by dsimp; rw [braiding_leftUnitor, unitors_equal] }

instance : Inhabited (CommMon_ (𝟙_ C)) :=
  ⟨trivial⟩

end CommMon_

variable (C) in
-- variable {M : C} [CommMon_ M]

structure CommMon_Cat where
  (X : C)
  [isCommMon_ : CommMon_ X]

attribute [instance] CommMon_Cat.isCommMon_

@[simps]
def CommMon_Cat.toMon_Cat (M : CommMon_Cat C) : Mon_Cat C :=
  { X := M.X, isMon_ := M.isCommMon_.toMon_ }

instance : Category (CommMon_Cat C) :=
  InducedCategory.category CommMon_Cat.toMon_Cat

@[simp]
theorem id_hom (A : CommMon_Cat C) : Mon_.Hom.hom (𝟙 A) = 𝟙 A.X :=
  rfl

@[simp]
theorem comp_hom {R S T : CommMon_Cat C} (f : R ⟶ S) (g : S ⟶ T) :
    Mon_.Hom.hom (f ≫ g) = f.hom ≫ g.hom :=
  rfl

-- Porting note (#5229): added because `Mon_.Hom.ext` is not triggered automatically
-- for morphisms in `CommMon_Cat C`
@[ext]
lemma hom_ext {A B : CommMon_Cat C} (f g : A ⟶ B) (h : f.hom = g.hom) : f = g :=
  Mon_.Hom.ext _ _ h

-- Porting note (#10688): the following two lemmas `id'` and `comp'`
-- have been added to ease automation;
@[simp]
lemma id' (A : CommMon_Cat C) : (𝟙 A : A.toMon_Cat ⟶ A.toMon_Cat) = 𝟙 (A.toMon_Cat) := rfl

@[simp]
lemma comp' {A₁ A₂ A₃ : CommMon_Cat C} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) :
    ((f ≫ g : A₁ ⟶ A₃) : A₁.toMon_Cat ⟶ A₃.toMon_Cat) =
      CategoryStruct.comp (obj := Mon_Cat C) f g := rfl

namespace CommMon_Cat

section

variable (C)

/-- The forgetful functor from commutative monoid objects to monoid objects. -/
def forget₂Mon_Cat : CommMon_Cat C ⥤ Mon_Cat C :=
  inducedFunctor CommMon_Cat.toMon_Cat

-- Porting note: no delta derive handler, see https://github.com/leanprover-community/mathlib4/issues/5020
instance : (forget₂Mon_Cat C).Full := InducedCategory.full _
instance : (forget₂Mon_Cat C).Faithful := InducedCategory.faithful _

@[simp]
theorem forget₂_Mon_obj_one (A : CommMon_Cat C) :
    (η : _ ⟶ ((forget₂Mon_Cat C).obj A).X) = (η : _ ⟶ A.X) :=
  rfl

@[simp]
theorem forget₂_Mon_obj_mul (A : CommMon_Cat C) :
    (μ : _ ⟶ ((forget₂Mon_Cat C).obj A).X) = (μ : _ ⟶ A.X) :=
  rfl

@[simp]
theorem forget₂_Mon_map_hom {A B : CommMon_Cat C} (f : A ⟶ B) :
    ((forget₂Mon_Cat C).map f).hom = f.hom :=
  rfl

end

instance uniqueHomFromTrivial (A : CommMon_Cat C) : Unique (CommMon_Cat.mk (𝟙_ C) ⟶ A) :=
  Mon_Cat.uniqueHomFromTrivial A.toMon_Cat

open CategoryTheory.Limits

instance : HasInitial (CommMon_Cat C) :=
  hasInitial_of_unique (mk (𝟙_ C))

end CommMon_Cat

namespace CategoryTheory.LaxBraidedFunctor

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D] [BraidedCategory.{v₂} D]

/-- A lax braided functor takes commutative monoid objects to commutative monoid objects.

That is, a lax braided functor `F : C ⥤ D` induces a functor `CommMon_Cat C ⥤ CommMon_ D`.
-/
@[simps!?]
instance (F : LaxBraidedFunctor C D) {A : C} [CommMon_ A] : CommMon_ (F.obj A) where
  mul_comm' := by
    dsimp
    have := F.braided
    slice_lhs 1 2 => rw [← this]
    slice_lhs 2 3 => rw [← CategoryTheory.Functor.map_comp, CommMon_.mul_comm]

/-- A lax braided functor takes commutative monoid objects to commutative monoid objects.

That is, a lax braided functor `F : C ⥤ D` induces a functor `CommMon_Cat C ⥤ CommMon_ D`.
-/
@[simps!?]
def mapCommMon (F : LaxBraidedFunctor C D) : CommMon_Cat C ⥤ CommMon_Cat D where
  obj A := CommMon_Cat.mk (F.obj A.X)
  map f := Mon_Cat.mkHom <| F.toLaxMonoidalFunctor.mapMon.map f

variable (C) (D)

-- Porting note (#10688): added @[simps] to ease automation
/-- `mapCommMon` is functorial in the lax braided functor. -/
@[simps]
def mapCommMonFunctor : LaxBraidedFunctor C D ⥤ CommMon_Cat C ⥤ CommMon_Cat D where
  obj := mapCommMon
  map α :=
    { app := fun A => { hom := α.app A.X } }

end CategoryTheory.LaxBraidedFunctor

namespace CommMon_

open CategoryTheory.LaxBraidedFunctor

namespace EquivLaxBraidedFunctorPUnit

variable (C)

/-- Implementation of `CommMon_.equivLaxBraidedFunctorPUnit`. -/
@[simps]
def laxBraidedToCommMon : LaxBraidedFunctor (Discrete PUnit.{u + 1}) C ⥤ CommMon_Cat C where
  obj F := (F.mapCommMon : CommMon_Cat _ ⥤ CommMon_Cat C).obj (.mk (𝟙_ (Discrete PUnit.{u+1})))
  map α := ((mapCommMonFunctor (Discrete PUnit.{u+1}) C).map α).app _

/-- Implementation of `CommMon_.equivLaxBraidedFunctorPunit`. -/
@[simps?]
def commMonToLaxBraided : CommMon_Cat C ⥤ LaxBraidedFunctor (Discrete PUnit.{u + 1}) C where
  obj A :=
    { obj := fun _ => A.X
      map := fun _ => 𝟙 _
      ε := η
      «μ» := fun _ _ => μ
      map_id := fun _ => rfl
      map_comp := fun _ _ => (Category.id_comp (𝟙 A.X)).symm }
  map f :=
    { app := fun _ => f.hom
      naturality := fun _ _ _ => by dsimp; rw [Category.id_comp, Category.comp_id]
      unit := Mon_.Hom.one_hom f
      tensor := fun _ _ => Mon_.Hom.mul_hom f }

/-- Implementation of `CommMon_.equivLaxBraidedFunctorPUnit`. -/
@[simps!]
def unitIso :
    𝟭 (LaxBraidedFunctor (Discrete PUnit.{u + 1}) C) ≅
      laxBraidedToCommMon C ⋙ commMonToLaxBraided C :=
  NatIso.ofComponents
    (fun F =>
      LaxBraidedFunctor.mkIso
        (MonoidalNatIso.ofComponents
          (fun _ => F.toLaxMonoidalFunctor.toFunctor.mapIso (eqToIso (by ext)))
          (by rintro ⟨⟩ ⟨⟩ f; aesop_cat) (by aesop_cat) (by aesop_cat)))

attribute [-simp] commMonToLaxBraided_obj_obj in
/-- Implementation of `CommMon_.equivLaxBraidedFunctorPUnit`. -/
@[simps!]
def counitIso : commMonToLaxBraided C ⋙ laxBraidedToCommMon C ≅ 𝟭 (CommMon_Cat C) :=
  NatIso.ofComponents
    (fun F =>
      { hom := { hom := 𝟙 _ }
        inv := { hom := 𝟙 _ } })

end EquivLaxBraidedFunctorPUnit

open EquivLaxBraidedFunctorPUnit

/-- Commutative monoid objects in `C` are "just" braided lax monoidal functors from the trivial
braided monoidal category to `C`.
-/
@[simps]
def equivLaxBraidedFunctorPUnit : LaxBraidedFunctor (Discrete PUnit.{u + 1}) C ≌ CommMon_Cat C where
  functor := laxBraidedToCommMon C
  inverse := commMonToLaxBraided C
  unitIso := unitIso C
  counitIso := counitIso C

end CommMon_
