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

open CategoryTheory MonoidalCategory Mon_Class

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C] [BraidedCategory.{v₁} C]

/-- A commutative monoid object internal to a monoidal category.
-/
structure CommMon_ extends Mon_ C where
  mul_comm : (β_ X X).hom ≫ μ = μ := by aesop_cat

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
theorem id_hom (A : CommMon_ C) : Mon_Hom.hom (𝟙 A) = 𝟙 A.X :=
  rfl

@[simp]
theorem comp_hom {R S T : CommMon_ C} (f : R ⟶ S) (g : S ⟶ T) :
    Mon_Hom.hom (f ≫ g) = f.hom ≫ g.hom :=
  rfl

@[ext]
lemma hom_ext {A B : CommMon_ C} (f g : A ⟶ B) (h : f.hom = g.hom) : f = g :=
  Mon_Hom.ext h

-- Porting note (#10688): the following two lemmas `id'` and `comp'`
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

instance (A : CommMon_ C) : Mon_Class ((forget₂Mon_ C).obj A).X :=
  inferInstanceAs <| Mon_Class A.X

-- Porting note: no delta derive handler, see https://github.com/leanprover-community/mathlib4/issues/5020
instance : (forget₂Mon_ C).Full := InducedCategory.full _
instance : (forget₂Mon_ C).Faithful := InducedCategory.faithful _

@[simp]
theorem forget₂_Mon_obj_one (A : CommMon_ C) : η[((forget₂Mon_ C).obj A).X] = η[A.X] :=
  rfl

@[simp]
theorem forget₂_Mon_obj_mul (A : CommMon_ C) : μ[((forget₂Mon_ C).obj A).X] = μ[A.X] :=
  rfl

@[simp]
theorem forget₂_Mon_map_hom {A B : CommMon_ C} (f : A ⟶ B) : ((forget₂Mon_ C).map f).hom = f.hom :=
  rfl

end

instance uniqueHomFromTrivial (A : CommMon_ C) : Unique (trivial C ⟶ A) :=
  Mon_.uniqueHomFromTrivial A.toMon_

open CategoryTheory.Limits

instance : HasInitial (CommMon_ C) :=
  hasInitial_of_unique (trivial C)

end CommMon_

namespace CategoryTheory.LaxBraidedFunctor

variable {C} {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D] [BraidedCategory.{v₂} D]

/-- A lax braided functor takes commutative monoid objects to commutative monoid objects.

That is, a lax braided functor `F : C ⥤ D` induces a functor `CommMon_ C ⥤ CommMon_ D`.
-/
@[simps!]
def mapCommMon (F : LaxBraidedFunctor C D) : CommMon_ C ⥤ CommMon_ D where
  obj A :=
    { F.toLaxMonoidalFunctor.mapMon.obj A.toMon_ with
      mul_comm := by
        dsimp
        have := F.braided
        slice_lhs 1 2 => rw [← this]
        slice_lhs 2 3 => rw [← CategoryTheory.Functor.map_comp, A.mul_comm] }
  map f := F.toLaxMonoidalFunctor.mapMon.map f

variable (C) (D)

-- Porting note (#10688): added @[simps] to ease automation
/-- `mapCommMon` is functorial in the lax braided functor. -/
@[simps]
def mapCommMonFunctor : LaxBraidedFunctor C D ⥤ CommMon_ C ⥤ CommMon_ D where
  obj := mapCommMon
  map α :=
    { app := fun A => { hom := α.app A.X }
      naturality := by intros; ext; simp }

end CategoryTheory.LaxBraidedFunctor

namespace CommMon_

open CategoryTheory.LaxBraidedFunctor

namespace EquivLaxBraidedFunctorPUnit

/-- Implementation of `CommMon_.equivLaxBraidedFunctorPUnit`. -/
@[simps]
def laxBraidedToCommMon : LaxBraidedFunctor (Discrete PUnit.{u + 1}) C ⥤ CommMon_ C where
  obj F := (F.mapCommMon : CommMon_ _ ⥤ CommMon_ C).obj (trivial (Discrete PUnit.{u+1}))
  map α := ((mapCommMonFunctor (Discrete PUnit.{u+1}) C).map α).app _

/-- Implementation of `CommMon_.equivLaxBraidedFunctorPunit`. -/
@[simps]
def commMonToLaxBraided : CommMon_ C ⥤ LaxBraidedFunctor (Discrete PUnit.{u + 1}) C where
  obj A :=
    { obj := fun _ => A.X
      map := fun _ => 𝟙 _
      «ε» := η
      «μ» := fun _ _ => μ
      map_id := fun _ => rfl
      map_comp := fun _ _ => (Category.id_comp (𝟙 A.X)).symm }
  map f :=
    { app := fun _ => f.hom
      naturality := fun _ _ _ => by dsimp; rw [Category.id_comp, Category.comp_id]
      unit := Mon_Hom.one_hom f
      tensor := fun _ _ => Mon_Hom.mul_hom f }

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

theorem counitIso_one (F : CommMon_ C) :
    η[((commMonToLaxBraided C ⋙ laxBraidedToCommMon C).obj F).X] = η ≫ 𝟙 F.X := rfl

theorem counitIso_one_mul (F : CommMon_ C) :
    μ[((commMonToLaxBraided C ⋙ laxBraidedToCommMon C).obj F).X] = μ ≫ 𝟙 F.X := rfl

attribute [local simp] counitIso_one counitIso_one_mul in
/-- Implementation of `CommMon_.equivLaxBraidedFunctorPUnit`. -/
@[simps!]
def counitIso : commMonToLaxBraided C ⋙ laxBraidedToCommMon C ≅ 𝟭 (CommMon_ C) :=
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
def equivLaxBraidedFunctorPUnit : LaxBraidedFunctor (Discrete PUnit.{u + 1}) C ≌ CommMon_ C where
  functor := laxBraidedToCommMon C
  inverse := commMonToLaxBraided C
  unitIso := unitIso C
  counitIso := counitIso C

end CommMon_
