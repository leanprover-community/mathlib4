/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.homology.homotopy_category
! leanprover-community/mathlib commit 13ff898b0eee75d3cc75d1c06a491720eaaf911d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Homology.Homotopy
import Mathbin.CategoryTheory.Quotient

/-!
# The homotopy category

`homotopy_category V c` gives the category of chain complexes of shape `c` in `V`,
with chain maps identified when they are homotopic.
-/


universe v u

open Classical

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {ι : Type _}

variable (V : Type u) [Category.{v} V] [Preadditive V]

variable (c : ComplexShape ι)

/-- The congruence on `homological_complex V c` given by the existence of a homotopy.
-/
def homotopic : HomRel (HomologicalComplex V c) := fun C D f g => Nonempty (Homotopy f g)
#align homotopic homotopic

instance homotopy_congruence : Congruence (homotopic V c)
    where
  IsEquiv C D :=
    { refl := fun C => ⟨Homotopy.refl C⟩
      symm := fun f g ⟨w⟩ => ⟨w.symm⟩
      trans := fun f g h ⟨w₁⟩ ⟨w₂⟩ => ⟨w₁.trans w₂⟩ }
  compLeft := fun E F G m₁ m₂ g ⟨i⟩ => ⟨i.compLeft _⟩
  compRight := fun E F G f m₁ m₂ ⟨i⟩ => ⟨i.compRight _⟩
#align homotopy_congruence homotopy_congruence

/-- `homotopy_category V c` is the category of chain complexes of shape `c` in `V`,
with chain maps identified when they are homotopic. -/
def HomotopyCategory :=
  CategoryTheory.Quotient (homotopic V c)deriving Category
#align homotopy_category HomotopyCategory

-- TODO the homotopy_category is preadditive
namespace HomotopyCategory

/-- The quotient functor from complexes to the homotopy category. -/
def quotient : HomologicalComplex V c ⥤ HomotopyCategory V c :=
  CategoryTheory.Quotient.functor _
#align homotopy_category.quotient HomotopyCategory.quotient

open ZeroObject

-- TODO upgrade this to `has_zero_object`, presumably for any `quotient`.
instance [HasZeroObject V] : Inhabited (HomotopyCategory V c) :=
  ⟨(quotient V c).obj 0⟩

variable {V c}

@[simp]
theorem quotient_obj_as (C : HomologicalComplex V c) : ((quotient V c).obj C).as = C :=
  rfl
#align homotopy_category.quotient_obj_as HomotopyCategory.quotient_obj_as

@[simp]
theorem quotient_map_out {C D : HomotopyCategory V c} (f : C ⟶ D) : (quotient V c).map f.out = f :=
  Quot.out_eq _
#align homotopy_category.quotient_map_out HomotopyCategory.quotient_map_out

theorem eq_of_homotopy {C D : HomologicalComplex V c} (f g : C ⟶ D) (h : Homotopy f g) :
    (quotient V c).map f = (quotient V c).map g :=
  CategoryTheory.Quotient.sound _ ⟨h⟩
#align homotopy_category.eq_of_homotopy HomotopyCategory.eq_of_homotopy

/-- If two chain maps become equal in the homotopy category, then they are homotopic. -/
def homotopyOfEq {C D : HomologicalComplex V c} (f g : C ⟶ D)
    (w : (quotient V c).map f = (quotient V c).map g) : Homotopy f g :=
  ((Quotient.functor_map_eq_iff _ _ _).mp w).some
#align homotopy_category.homotopy_of_eq HomotopyCategory.homotopyOfEq

/-- An arbitrarily chosen representation of the image of a chain map in the homotopy category
is homotopic to the original chain map.
-/
def homotopyOutMap {C D : HomologicalComplex V c} (f : C ⟶ D) :
    Homotopy ((quotient V c).map f).out f :=
  by
  apply homotopy_of_eq
  simp
#align homotopy_category.homotopy_out_map HomotopyCategory.homotopyOutMap

@[simp]
theorem quotient_map_out_comp_out {C D E : HomotopyCategory V c} (f : C ⟶ D) (g : D ⟶ E) :
    (quotient V c).map (Quot.out f ≫ Quot.out g) = f ≫ g := by
  conv_rhs => erw [← quotient_map_out f, ← quotient_map_out g, ← (Quotient V c).map_comp]
#align homotopy_category.quotient_map_out_comp_out HomotopyCategory.quotient_map_out_comp_out

/-- Homotopy equivalent complexes become isomorphic in the homotopy category. -/
@[simps]
def isoOfHomotopyEquiv {C D : HomologicalComplex V c} (f : HomotopyEquiv C D) :
    (quotient V c).obj C ≅ (quotient V c).obj D
    where
  Hom := (quotient V c).map f.Hom
  inv := (quotient V c).map f.inv
  hom_inv_id' := by
    rw [← (Quotient V c).map_comp, ← (Quotient V c).map_id]
    exact eq_of_homotopy _ _ f.homotopy_hom_inv_id
  inv_hom_id' := by
    rw [← (Quotient V c).map_comp, ← (Quotient V c).map_id]
    exact eq_of_homotopy _ _ f.homotopy_inv_hom_id
#align homotopy_category.iso_of_homotopy_equiv HomotopyCategory.isoOfHomotopyEquiv

/-- If two complexes become isomorphic in the homotopy category,
  then they were homotopy equivalent. -/
def homotopyEquivOfIso {C D : HomologicalComplex V c}
    (i : (quotient V c).obj C ≅ (quotient V c).obj D) : HomotopyEquiv C D
    where
  Hom := Quot.out i.Hom
  inv := Quot.out i.inv
  homotopyHomInvId :=
    homotopyOfEq _ _
      (by
        simp
        rfl)
  homotopyInvHomId :=
    homotopyOfEq _ _
      (by
        simp
        rfl)
#align homotopy_category.homotopy_equiv_of_iso HomotopyCategory.homotopyEquivOfIso

variable (V c) [HasEqualizers V] [HasImages V] [HasImageMaps V] [HasCokernels V]

/-- The `i`-th homology, as a functor from the homotopy category. -/
def homologyFunctor (i : ι) : HomotopyCategory V c ⥤ V :=
  CategoryTheory.Quotient.lift _ (homologyFunctor V c i) fun C D f g ⟨h⟩ =>
    homology_map_eq_of_homotopy h i
#align homotopy_category.homology_functor HomotopyCategory.homologyFunctor

/-- The homology functor on the homotopy category is just the usual homology functor. -/
def homologyFactors (i : ι) : quotient V c ⋙ homologyFunctor V c i ≅ homologyFunctor V c i :=
  CategoryTheory.Quotient.lift.isLift _ _ _
#align homotopy_category.homology_factors HomotopyCategory.homologyFactors

@[simp]
theorem homologyFactors_hom_app (i : ι) (C : HomologicalComplex V c) :
    (homologyFactors V c i).Hom.app C = 𝟙 _ :=
  rfl
#align homotopy_category.homology_factors_hom_app HomotopyCategory.homologyFactors_hom_app

@[simp]
theorem homologyFactors_inv_app (i : ι) (C : HomologicalComplex V c) :
    (homologyFactors V c i).inv.app C = 𝟙 _ :=
  rfl
#align homotopy_category.homology_factors_inv_app HomotopyCategory.homologyFactors_inv_app

theorem homologyFunctor_map_factors (i : ι) {C D : HomologicalComplex V c} (f : C ⟶ D) :
    (homologyFunctor V c i).map f = ((homologyFunctor V c i).map ((quotient V c).map f) : _) :=
  (CategoryTheory.Quotient.lift_map_functor_map _ (homologyFunctor V c i) _ f).symm
#align homotopy_category.homology_functor_map_factors HomotopyCategory.homologyFunctor_map_factors

end HomotopyCategory

namespace CategoryTheory

variable {V} {W : Type _} [Category W] [Preadditive W]

/-- An additive functor induces a functor between homotopy categories. -/
@[simps]
def Functor.mapHomotopyCategory (c : ComplexShape ι) (F : V ⥤ W) [F.Additive] :
    HomotopyCategory V c ⥤ HomotopyCategory W c
    where
  obj C := (HomotopyCategory.quotient W c).obj ((F.mapHomologicalComplex c).obj C.as)
  map C D f := (HomotopyCategory.quotient W c).map ((F.mapHomologicalComplex c).map (Quot.out f))
  map_id' C := by
    rw [← (HomotopyCategory.quotient W c).map_id]
    apply HomotopyCategory.eq_of_homotopy
    rw [← (F.map_homological_complex c).map_id]
    apply F.map_homotopy
    apply HomotopyCategory.homotopyOfEq
    exact Quot.out_eq _
  map_comp' C D E f g := by
    rw [← (HomotopyCategory.quotient W c).map_comp]
    apply HomotopyCategory.eq_of_homotopy
    rw [← (F.map_homological_complex c).map_comp]
    apply F.map_homotopy
    apply HomotopyCategory.homotopyOfEq
    convert Quot.out_eq _
    exact HomotopyCategory.quotient_map_out_comp_out _ _
#align category_theory.functor.map_homotopy_category CategoryTheory.Functor.mapHomotopyCategory

-- TODO `F.map_homotopy_category c` is additive (and linear when `F` is linear).
/-- A natural transformation induces a natural transformation between
  the induced functors on the homotopy category. -/
@[simps]
def NatTrans.mapHomotopyCategory {F G : V ⥤ W} [F.Additive] [G.Additive] (α : F ⟶ G)
    (c : ComplexShape ι) : F.mapHomotopyCategory c ⟶ G.mapHomotopyCategory c
    where
  app C := (HomotopyCategory.quotient W c).map ((NatTrans.mapHomologicalComplex α c).app C.as)
  naturality' C D f := by
    dsimp
    simp only [← functor.map_comp]
    congr 1
    ext
    dsimp
    simp
#align category_theory.nat_trans.map_homotopy_category CategoryTheory.NatTrans.mapHomotopyCategory

@[simp]
theorem NatTrans.mapHomotopyCategory_id (c : ComplexShape ι) (F : V ⥤ W) [F.Additive] :
    NatTrans.mapHomotopyCategory (𝟙 F) c = 𝟙 (F.mapHomotopyCategory c) := by tidy
#align category_theory.nat_trans.map_homotopy_category_id CategoryTheory.NatTrans.mapHomotopyCategory_id

@[simp]
theorem NatTrans.mapHomotopyCategory_comp (c : ComplexShape ι) {F G H : V ⥤ W} [F.Additive]
    [G.Additive] [H.Additive] (α : F ⟶ G) (β : G ⟶ H) :
    NatTrans.mapHomotopyCategory (α ≫ β) c =
      NatTrans.mapHomotopyCategory α c ≫ NatTrans.mapHomotopyCategory β c :=
  by tidy
#align category_theory.nat_trans.map_homotopy_category_comp CategoryTheory.NatTrans.mapHomotopyCategory_comp

end CategoryTheory

