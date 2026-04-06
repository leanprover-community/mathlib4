/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.CategoryTheory.MorphismProperty.IsInvertedBy
public import Mathlib.CategoryTheory.Quotient.Linear
public import Mathlib.CategoryTheory.Quotient.Preadditive

/-!
# The homotopy category

`HomotopyCategory V c` gives the category of chain complexes of shape `c` in `V`,
with chain maps identified when they are homotopic.
-/

@[expose] public section

universe v u

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {R : Type*} [Semiring R]
  {ι : Type*} (V : Type u) [Category.{v} V] [Preadditive V] (c : ComplexShape ι)

/-- The congruence on `HomologicalComplex V c` given by the existence of a homotopy.
-/
def homotopic : HomRel (HomologicalComplex V c) := fun _ _ f g => Nonempty (Homotopy f g)

instance homotopy_congruence : Congruence (homotopic V c) where
  equivalence :=
    { refl := fun C => ⟨Homotopy.refl C⟩
      symm := fun ⟨w⟩ => ⟨w.symm⟩
      trans := fun ⟨w₁⟩ ⟨w₂⟩ => ⟨w₁.trans w₂⟩ }
  comp_left := fun _ _ _ ⟨i⟩ => ⟨i.compLeft _⟩
  comp_right := fun _ ⟨i⟩ => ⟨i.compRight _⟩

/-- `HomotopyCategory V c` is the category of chain complexes of shape `c` in `V`,
with chain maps identified when they are homotopic. -/
def HomotopyCategory :=
  CategoryTheory.Quotient (homotopic V c)

instance : Category (HomotopyCategory V c) :=
  inferInstanceAs <| Category (CategoryTheory.Quotient (homotopic V c))

namespace HomotopyCategory

instance : Preadditive (CategoryTheory.Quotient (homotopic V c)) :=
  Quotient.preadditive _ (by
    rintro _ _ _ _ _ _ ⟨h⟩ ⟨h'⟩
    exact ⟨Homotopy.add h h'⟩)

instance : Preadditive (HomotopyCategory V c) :=
  inferInstanceAs <| Preadditive (CategoryTheory.Quotient (homotopic V c))

/-- The quotient functor from complexes to the homotopy category. -/
def quotient : HomologicalComplex V c ⥤ HomotopyCategory V c :=
  CategoryTheory.Quotient.functor _

instance : (quotient V c).Full := Quotient.full_functor _

instance : (quotient V c).EssSurj := Quotient.essSurj_functor _

instance : (quotient V c).Additive where

instance : Functor.Additive (Quotient.functor (homotopic V c)) where

instance [Linear R V] : Linear R (HomotopyCategory V c) :=
  Quotient.linear R (homotopic V c) (fun _ _ _ _ _ h => ⟨h.some.smul _⟩)

instance [Linear R V] : Functor.Linear R (quotient V c) :=
  Quotient.linear_functor _ (homotopic V c) _

open ZeroObject

instance [HasZeroObject V] : Inhabited (HomotopyCategory V c) :=
  ⟨(quotient V c).obj 0⟩

instance [HasZeroObject V] : HasZeroObject (HomotopyCategory V c) :=
  ⟨(quotient V c).obj 0, by
    rw [IsZero.iff_id_eq_zero, ← (quotient V c).map_id, id_zero, Functor.map_zero]⟩

instance {D : Type*} [Category* D] : ((Functor.whiskeringLeft _ _ D).obj (quotient V c)).Full :=
  Quotient.full_whiskeringLeft_functor _ _

instance {D : Type*} [Category* D] : ((Functor.whiskeringLeft _ _ D).obj (quotient V c)).Faithful :=
  Quotient.faithful_whiskeringLeft_functor _ _

variable {V c}

lemma quotient_obj_surjective (X : HomotopyCategory V c) :
    ∃ (K : HomologicalComplex V c), (quotient _ _).obj K = X :=
  ⟨_, rfl⟩

-- Not `@[simp]` because it hinders the automatic application of the more useful `quotient_map_out`
theorem quotient_obj_as (C : HomologicalComplex V c) : ((quotient V c).obj C).as = C :=
  rfl

@[simp]
theorem quotient_map_out {C D : HomotopyCategory V c} (f : C ⟶ D) : (quotient V c).map f.out = f :=
  Quot.out_eq _

theorem quot_mk_eq_quotient_map {C D : HomologicalComplex V c} (f : C ⟶ D) :
    Quot.mk _ f = (quotient V c).map f := rfl

theorem eq_of_homotopy {C D : HomologicalComplex V c} (f g : C ⟶ D) (h : Homotopy f g) :
    (quotient V c).map f = (quotient V c).map g :=
  CategoryTheory.Quotient.sound _ ⟨h⟩

/-- If two chain maps become equal in the homotopy category, then they are homotopic. -/
def homotopyOfEq {C D : HomologicalComplex V c} (f g : C ⟶ D)
    (w : (quotient V c).map f = (quotient V c).map g) : Homotopy f g :=
  ((Quotient.functor_map_eq_iff _ _ _).mp w).some

lemma quotient_map_eq_zero_iff {C D : HomologicalComplex V c} (f : C ⟶ D) :
    (quotient V c).map f = 0 ↔ Nonempty (Homotopy f 0) :=
  ⟨fun h ↦ ⟨homotopyOfEq _ _ (by simpa using h)⟩,
    fun ⟨h⟩ ↦ by simpa using eq_of_homotopy _ _ h⟩

set_option backward.isDefEq.respectTransparency false in
/-- An arbitrarily chosen representation of the image of a chain map in the homotopy category
is homotopic to the original chain map.
-/
def homotopyOutMap {C D : HomologicalComplex V c} (f : C ⟶ D) :
    Homotopy ((quotient V c).map f).out f := by
  apply homotopyOfEq
  simp

set_option backward.isDefEq.respectTransparency false in
theorem quotient_map_out_comp_out {C D E : HomotopyCategory V c} (f : C ⟶ D) (g : D ⟶ E) :
    (quotient V c).map (Quot.out f ≫ Quot.out g) = f ≫ g := by simp

/-- Homotopy equivalent complexes become isomorphic in the homotopy category. -/
@[simps]
def isoOfHomotopyEquiv {C D : HomologicalComplex V c} (f : HomotopyEquiv C D) :
    (quotient V c).obj C ≅ (quotient V c).obj D where
  hom := (quotient V c).map f.hom
  inv := (quotient V c).map f.inv
  hom_inv_id := by
    rw [← (quotient V c).map_comp, ← (quotient V c).map_id]
    exact eq_of_homotopy _ _ f.homotopyHomInvId
  inv_hom_id := by
    rw [← (quotient V c).map_comp, ← (quotient V c).map_id]
    exact eq_of_homotopy _ _ f.homotopyInvHomId

set_option backward.isDefEq.respectTransparency false in
/-- If two complexes become isomorphic in the homotopy category,
  then they were homotopy equivalent. -/
def homotopyEquivOfIso {C D : HomologicalComplex V c}
    (i : (quotient V c).obj C ≅ (quotient V c).obj D) : HomotopyEquiv C D where
  hom := Quot.out i.hom
  inv := Quot.out i.inv
  homotopyHomInvId :=
    homotopyOfEq _ _
      (by rw [quotient_map_out_comp_out, i.hom_inv_id, (quotient V c).map_id])
  homotopyInvHomId :=
    homotopyOfEq _ _
      (by rw [quotient_map_out_comp_out, i.inv_hom_id, (quotient V c).map_id])

variable (V c) in
lemma quotient_inverts_homotopyEquivalences :
    (HomologicalComplex.homotopyEquivalences V c).IsInvertedBy (quotient V c) := by
  rintro K L _ ⟨e, rfl⟩
  change IsIso (isoOfHomotopyEquiv e).hom
  infer_instance

lemma isZero_quotient_obj_iff (C : HomologicalComplex V c) :
    IsZero ((quotient _ _).obj C) ↔ Nonempty (Homotopy (𝟙 C) 0) := by
  rw [IsZero.iff_id_eq_zero]
  constructor
  · intro h
    exact ⟨(homotopyOfEq _ _ (by simp [h]))⟩
  · rintro ⟨h⟩
    simpa using (eq_of_homotopy _ _ h)

variable (V c)

section

variable [CategoryWithHomology V]

open Classical in
/-- The `i`-th homology, as a functor from the homotopy category. -/
noncomputable def homologyFunctor (i : ι) : HomotopyCategory V c ⥤ V :=
  CategoryTheory.Quotient.lift _ (HomologicalComplex.homologyFunctor V c i) (by
    rintro K L f g ⟨h⟩
    exact h.homologyMap_eq i)

/-- The homology functor on the homotopy category is induced by
the homology functor on homological complexes. -/
noncomputable def homologyFunctorFactors (i : ι) :
    quotient V c ⋙ homologyFunctor V c i ≅
      HomologicalComplex.homologyFunctor V c i :=
  Quotient.lift.isLift _ _ _

-- this is to prevent any abuse of defeq
attribute [irreducible] homologyFunctor homologyFunctorFactors

instance (i : ι) : (homologyFunctor V c i).Additive := by
  have := Functor.additive_of_iso (homologyFunctorFactors V c i).symm
  exact Functor.additive_of_full_essSurj_comp (quotient V c) _

end

end HomotopyCategory

namespace CategoryTheory

variable {V} {W : Type*} [Category* W] [Preadditive W]

/-- An additive functor induces a functor between homotopy categories. -/
@[simps! obj]
def Functor.mapHomotopyCategory (F : V ⥤ W) [F.Additive] (c : ComplexShape ι) :
    HomotopyCategory V c ⥤ HomotopyCategory W c :=
  CategoryTheory.Quotient.lift _ (F.mapHomologicalComplex c ⋙ HomotopyCategory.quotient W c)
    (fun _ _ _ _ ⟨h⟩ => HomotopyCategory.eq_of_homotopy _ _ (F.mapHomotopy h))

@[simp]
lemma Functor.mapHomotopyCategory_map (F : V ⥤ W) [F.Additive] {c : ComplexShape ι}
    {K L : HomologicalComplex V c} (f : K ⟶ L) :
    (F.mapHomotopyCategory c).map ((HomotopyCategory.quotient V c).map f) =
      (HomotopyCategory.quotient W c).map ((F.mapHomologicalComplex c).map f) :=
  rfl

/-- The obvious isomorphism between
`HomotopyCategory.quotient V c ⋙ F.mapHomotopyCategory c` and
`F.mapHomologicalComplex c ⋙ HomotopyCategory.quotient W c` when `F : V ⥤ W` is
an additive functor. -/
def Functor.mapHomotopyCategoryFactors (F : V ⥤ W) [F.Additive] (c : ComplexShape ι) :
    HomotopyCategory.quotient V c ⋙ F.mapHomotopyCategory c ≅
      F.mapHomologicalComplex c ⋙ HomotopyCategory.quotient W c :=
  CategoryTheory.Quotient.lift.isLift _ _ _

set_option backward.isDefEq.respectTransparency false in
-- TODO develop lifting of natural transformations for general quotient categories so that
-- `NatTrans.mapHomotopyCategory` become a particular case of it
/-- A natural transformation induces a natural transformation between
  the induced functors on the homotopy category. -/
@[simps]
def NatTrans.mapHomotopyCategory {F G : V ⥤ W} [F.Additive] [G.Additive] (α : F ⟶ G)
    (c : ComplexShape ι) : F.mapHomotopyCategory c ⟶ G.mapHomotopyCategory c where
  app C := (HomotopyCategory.quotient W c).map ((NatTrans.mapHomologicalComplex α c).app C.as)
  naturality := by
    rintro ⟨C⟩ ⟨D⟩ ⟨f : C ⟶ D⟩
    simp only [HomotopyCategory.quot_mk_eq_quotient_map, Functor.mapHomotopyCategory_map,
      ← Functor.map_comp, NatTrans.naturality]

@[simp]
theorem NatTrans.mapHomotopyCategory_id (c : ComplexShape ι) (F : V ⥤ W) [F.Additive] :
    NatTrans.mapHomotopyCategory (𝟙 F) c = 𝟙 (F.mapHomotopyCategory c) := by cat_disch

@[simp]
theorem NatTrans.mapHomotopyCategory_comp (c : ComplexShape ι) {F G H : V ⥤ W} [F.Additive]
    [G.Additive] [H.Additive] (α : F ⟶ G) (β : G ⟶ H) :
    NatTrans.mapHomotopyCategory (α ≫ β) c =
      NatTrans.mapHomotopyCategory α c ≫ NatTrans.mapHomotopyCategory β c := by cat_disch

instance (F : V ⥤ W) [F.Additive] (c : ComplexShape ι) :
    (F.mapHomotopyCategory c).Additive :=
  have := Functor.additive_of_iso (F.mapHomotopyCategoryFactors c).symm
  (HomotopyCategory.quotient V c).additive_of_full_essSurj_comp (F.mapHomotopyCategory c)

instance (F : V ⥤ W) [F.Additive] (c : ComplexShape ι) [Linear R V] [Linear R W] [F.Linear R] :
    Functor.Linear R (F.mapHomotopyCategory c) :=
  have := Functor.linear_of_iso R (F.mapHomotopyCategoryFactors c).symm
  (HomotopyCategory.quotient V c).linear_of_full_essSurj_comp (F.mapHomotopyCategory c)

end CategoryTheory
