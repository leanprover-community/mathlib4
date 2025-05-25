/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Monoidal.Grp_
import Mathlib.CategoryTheory.Monoidal.CommMon_

/-!
# The category of commutative groups in a cartesian monoidal category
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory Category Limits MonoidalCategory CartesianMonoidalCategory Mon_ Grp_ CommMon_

variable (C : Type u₁) [Category.{v₁} C] [CartesianMonoidalCategory.{v₁} C] [BraidedCategory C]

/-- A commutative group object internal to a cartesian monoidal category. -/
structure CommGrp_ extends Grp_ C, CommMon_ C where

/-- Turn a commutative group object into a commutative monoid object. -/
add_decl_doc CommGrp_.toCommMon_

attribute [reassoc (attr := simp)] CommGrp_.mul_comm

namespace CommGrp_

/-- The trivial commutative group object. -/
@[simps!]
def trivial : CommGrp_ C :=
  { Grp_.trivial C with mul_comm := by simpa using unitors_equal.symm }

instance : Inhabited (CommGrp_ C) where
  default := trivial C

variable {C}

instance : Category (CommGrp_ C) :=
  InducedCategory.category CommGrp_.toGrp_

omit [BraidedCategory C] in
@[simp]
theorem id_hom (A : Grp_ C) : Mon_.Hom.hom (𝟙 A) = 𝟙 A.X :=
  rfl

@[simp]
theorem comp_hom {R S T : CommGrp_ C} (f : R ⟶ S) (g : S ⟶ T) :
    Mon_.Hom.hom (f ≫ g) = f.hom ≫ g.hom :=
  rfl

@[ext]
theorem hom_ext {A B : CommGrp_ C} (f g : A ⟶ B) (h : f.hom = g.hom) : f = g :=
  Mon_.Hom.ext h

@[simp]
lemma id' (A : CommGrp_ C) : (𝟙 A : A.toMon_ ⟶ A.toMon_) = 𝟙 (A.toMon_) := rfl

@[simp]
lemma comp' {A₁ A₂ A₃ : CommGrp_ C} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) :
    ((f ≫ g : A₁ ⟶ A₃) : A₁.toMon_ ⟶ A₃.toMon_) = @CategoryStruct.comp (Mon_ C) _ _ _ _ f g := rfl

section

variable (C)

/-- The forgetful functor from commutative group objects to group objects. -/
def forget₂Grp_ : CommGrp_ C ⥤ Grp_ C :=
  inducedFunctor CommGrp_.toGrp_

/-- The forgetful functor from commutative group objects to group objects is fully faithful. -/
def fullyFaithfulForget₂Grp_ : (forget₂Grp_ C).FullyFaithful :=
    fullyFaithfulInducedFunctor _

instance : (forget₂Grp_ C).Full := InducedCategory.full _
instance : (forget₂Grp_ C).Faithful := InducedCategory.faithful _

@[simp]
theorem forget₂Grp_obj_one (A : CommGrp_ C) : ((forget₂Grp_ C).obj A).one = A.one :=
  rfl

@[simp]
theorem forget₂Grp_obj_mul (A : CommGrp_ C) : ((forget₂Grp_ C).obj A).mul = A.mul :=
  rfl

@[simp]
theorem forget₂Grp_map_hom {A B : CommGrp_ C} (f : A ⟶ B) : ((forget₂Grp_ C).map f).hom = f.hom :=
  rfl

/-- The forgetful functor from commutative group objects to commutative monoid objects. -/
def forget₂CommMon_ : CommGrp_ C ⥤ CommMon_ C :=
  inducedFunctor CommGrp_.toCommMon_

/-- The forgetful functor from commutative group objects to commutative monoid objects is fully
faithful. -/
def fullyFaithfulForget₂CommMon_ : (forget₂CommMon_ C).FullyFaithful :=
    fullyFaithfulInducedFunctor _

instance : (forget₂CommMon_ C).Full := InducedCategory.full _
instance : (forget₂CommMon_ C).Faithful := InducedCategory.faithful _

@[simp]
theorem forget₂CommMon_obj_one (A : CommGrp_ C) : ((forget₂CommMon_ C).obj A).one = A.one :=
  rfl

@[simp]
theorem forget₂CommMon_obj_mul (A : CommGrp_ C) : ((forget₂CommMon_ C).obj A).mul = A.mul :=
  rfl

@[simp]
theorem forget₂CommMon_map_hom {A B : CommGrp_ C} (f : A ⟶ B) :
    ((forget₂CommMon_ C).map f).hom = f.hom :=
  rfl

/-- The forgetful functor from commutative group objects to the ambient category. -/
@[simps!]
def forget : CommGrp_ C ⥤ C :=
  forget₂Grp_ C ⋙ Grp_.forget C

instance : (forget C).Faithful where

@[simp]
theorem forget₂Grp_comp_forget : forget₂Grp_ C ⋙ Grp_.forget C = forget C := rfl

@[simp]
theorem forget₂CommMon_comp_forget : forget₂CommMon_ C ⋙ CommMon_.forget C = forget C := rfl

end

section

variable {M N : CommGrp_ C} (f : M.X ≅ N.X) (one_f : M.one ≫ f.hom = N.one := by aesop_cat)
  (mul_f : M.mul ≫ f.hom = (f.hom ⊗ f.hom) ≫ N.mul := by aesop_cat)

/-- Constructor for isomorphisms in the category `Grp_ C`. -/
def mkIso : M ≅ N :=
  (fullyFaithfulForget₂Grp_ C).preimageIso (Grp_.mkIso f one_f mul_f)

@[simp] lemma mkIso_hom_hom : (mkIso f one_f mul_f).hom.hom = f.hom := rfl
@[simp] lemma mkIso_inv_hom : (mkIso f one_f mul_f).inv.hom = f.inv := rfl

end

instance uniqueHomFromTrivial (A : CommGrp_ C) : Unique (trivial C ⟶ A) :=
  Mon_.uniqueHomFromTrivial A.toMon_

instance : HasInitial (CommGrp_ C) :=
  hasInitial_of_unique (trivial C)

end CommGrp_

namespace CategoryTheory
variable {C}
  {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D] [BraidedCategory D]
  {E : Type u₃} [Category.{v₃} E] [CartesianMonoidalCategory E] [BraidedCategory E]

namespace Functor
variable {F F' : C ⥤ D} [F.Braided] [F'.Braided] {G : D ⥤ E} [G.Braided]

open Monoidal

variable (F) in
/-- A finite-product-preserving functor takes commutative group objects to commutative group
objects. -/
@[simps!]
noncomputable def mapCommGrp : CommGrp_ C ⥤ CommGrp_ D where
  obj A :=
    { F.mapGrp.obj A.toGrp_ with
      mul_comm := by
        dsimp
        rw [← Functor.LaxBraided.braided_assoc, ← Functor.map_comp, A.mul_comm] }
  map f := F.mapMon.map f

/-- The identity functor is also the identity on commutative group objects. -/
@[simps!]
noncomputable def mapCommGrpIdIso : mapCommGrp (𝟭 C) ≅ 𝟭 (CommGrp_ C) :=
  NatIso.ofComponents (fun X ↦ CommGrp_.mkIso (.refl _) (by simp [ε_of_cartesianMonoidalCategory])
    (by simp [μ_of_cartesianMonoidalCategory]))

/-- The composition functor is also the composition on commutative group objects. -/
@[simps!]
noncomputable def mapCommGrpCompIso : (F ⋙ G).mapCommGrp ≅ F.mapCommGrp ⋙ G.mapCommGrp :=
  NatIso.ofComponents (fun X ↦ CommGrp_.mkIso (.refl _) (by simp [ε_of_cartesianMonoidalCategory])
    (by simp [μ_of_cartesianMonoidalCategory]))

/-- Natural transformations between functors lift to commutative group objects. -/
@[simps!]
noncomputable def mapCommGrpNatTrans (f : F ⟶ F') : F.mapCommGrp ⟶ F'.mapCommGrp where
  app X := .mk (f.app _)

/-- Natural isomorphisms between functors lift to commutative group objects. -/
@[simps!]
noncomputable def mapCommGrpNatIso (e : F ≅ F') : F.mapCommGrp ≅ F'.mapCommGrp :=
  NatIso.ofComponents fun X ↦ CommGrp_.mkIso (e.app _)

attribute [local instance] Functor.Braided.ofChosenFiniteProducts in
/-- `mapCommGrp` is functorial in the left-exact functor. -/
@[simps]
noncomputable def mapCommGrpFunctor : (C ⥤ₗ D) ⥤ CommGrp_ C ⥤ CommGrp_ D where
  obj F := F.1.mapCommGrp
  map {F G} α := { app := fun A => { hom := α.app A.X } }

end Functor

open Functor

namespace Adjunction
variable {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) [F.Braided] [G.Braided]

/-- An adjunction of braided functors lifts to an adjunction of their lifts to commutative group
objects. -/
@[simps] noncomputable def mapCommGrp : F.mapCommGrp ⊣ G.mapCommGrp where
  unit := mapCommGrpIdIso.inv ≫ mapCommGrpNatTrans a.unit ≫ mapCommGrpCompIso.hom
  counit := mapCommGrpCompIso.inv ≫ mapCommGrpNatTrans a.counit ≫ mapCommGrpIdIso.hom

end Adjunction

namespace Equivalence
variable (e : C ≌ D) [e.functor.Braided] [e.inverse.Braided]

/-- An equivalence of categories lifts to an equivalence of their commutative group objects. -/
@[simps] noncomputable def mapCommGrp : CommGrp_ C ≌ CommGrp_ D where
  functor := e.functor.mapCommGrp
  inverse := e.inverse.mapCommGrp
  unitIso := mapCommGrpIdIso.symm ≪≫ mapCommGrpNatIso e.unitIso ≪≫ mapCommGrpCompIso
  counitIso := mapCommGrpCompIso.symm ≪≫ mapCommGrpNatIso e.counitIso ≪≫ mapCommGrpIdIso

end CategoryTheory.Equivalence
