import Mathlib.CategoryTheory.GradedObject

namespace CategoryTheory

open Limits

variable {C D : Type*} [Category C] [Category D]

namespace GradedObject

section

variable {I J : Type*} (X Y Z : GradedObject I C) (φ : X ⟶ Y) (e : X ≅ Y) (ψ : Y ⟶ Z) (p : I → J)

variable [X.HasMap p] [Y.HasMap p] [Z.HasMap p]

attribute [local ext] mapObj_ext

@[simps]
noncomputable def isColimitCoconeMapObj (j : J) : IsColimit (X.cofanMapObj p j) where
  desc s := descMapObj _ _ (fun i hi => s.ι.app ⟨⟨i, hi⟩⟩)
  fac s := fun ⟨i, hi⟩ => by simp
  uniq s m hm := by
    apply mapObj_ext
    intro i hi
    simpa using hm ⟨i, hi⟩


variable (C)

abbrev HasMapFunctor := ∀ (j : J), HasColimitsOfShape (Discrete (p ⁻¹' {j})) C

end

section

variable {I J K : Type*} (X Y : GradedObject I C) (p : I → J) (q : J → K) (r : I → K)
  (hpqr : ∀ i, r i = q (p i))
  [X.HasMap p] [(X.mapObj p).HasMap q] [X.HasMap r]

attribute [local ext] mapObj_ext

@[simps]
noncomputable def mapObjMapObjIso : (X.mapObj p).mapObj q ≅ X.mapObj r where
  hom k := descMapObj _ _ (fun j hj => descMapObj _ _
    (fun i hi => X.ιMapObj r i k (by rw [hpqr, hi, hj])))
  inv k := descMapObj _ _
    (fun i hi => X.ιMapObj p i (p i) rfl ≫ (X.mapObj p).ιMapObj q (p i) k (by rw [← hi, hpqr]))

end

@[simps]
def applyFunctorsObj {I : Type*} (F : GradedObject I (C ⥤ D)) :
    GradedObject I C ⥤ GradedObject I D where
  obj X i := (F i).obj (X i)
  map {X Y} φ i := (F i).map (φ i)

variable (C D)

@[simps]
def applyFunctors (I : Type*) :
    GradedObject I (C ⥤ D) ⥤ GradedObject I C ⥤ GradedObject I D where
  obj F := F.applyFunctorsObj
  map {F F'} φ :=
    { app := fun X i => (φ i).app (X i) }

section

variable {C D}
variable {I J : Type*} (F : GradedObject J (C ⥤ D)) (p : I → J) (X : GradedObject I C)
  [X.HasMap p]

abbrev PreservesMap := ∀ (j : J), PreservesColimit
  (Discrete.functor (fun (i : (p ⁻¹' {j})) => X i)) (F j)

noncomputable def comapObjApplyFunctorsObjObjMapObj
    [HasMap ((applyFunctorsObj ((comap (C ⥤ D) p).obj F)).obj X) p] :
    (((comap _ p).obj F).applyFunctorsObj.obj X).mapObj p ⟶
        F.applyFunctorsObj.obj (X.mapObj p) := fun j =>
  descMapObj _ _ (by
    rintro i rfl
    exact (F (p i)).map (X.ιMapObj p i _ rfl))

@[reassoc (attr := simp)]
lemma ι_comapObjApplyFunctorsObjObjMapObj (i : I)
    [HasMap ((applyFunctorsObj ((comap (C ⥤ D) p).obj F)).obj X) p] :
    ιMapObj _ p i _ rfl ≫ comapObjApplyFunctorsObjObjMapObj F p X (p i) =
      (F (p i)).map (X.ιMapObj p i _ rfl) := by
  apply ι_descMapObj

@[reassoc (attr := simp)]
lemma ι_comapObjApplyFunctorsObjObjMapObj' (i : I) (j : J) (hi : p i = j)
    [HasMap ((applyFunctorsObj ((comap (C ⥤ D) p).obj F)).obj X) p] :
    ((applyFunctorsObj ((comap (C ⥤ D) p).obj F)).obj X).ιMapObj p i j hi ≫
      comapObjApplyFunctorsObjObjMapObj F p X j =
        eqToHom (by subst hi; rfl) ≫ (F j).map (X.ιMapObj p i j hi) := by
  subst hi
  simp

variable [X.HasMap p]

/-noncomputable def mapCoconeMapObj (j : J) := (F j).mapCocone (X.coconeMapObj p j)

noncomputable def isColimitMapCoconeMapObj [F.PreservesMap p X] (j : J) :
    IsColimit (F.mapCoconeMapObj p X j) :=
  isColimitOfPreserves (F j) (X.isColimitCoconeMapObj p j)

instance [F.PreservesMap p X] :
    HasMap ((applyFunctorsObj ((comap (C ⥤ D) p).obj F)).obj X) p := by
  intro j
  have : HasColimit _ := ⟨_, F.isColimitMapCoconeMapObj p X j⟩
  let e : Discrete.functor (fun (i : (p ⁻¹' {j})) => (F (p i)).obj (X i)) ≅
    Discrete.functor (fun (i : (p ⁻¹' {j})) => X i) ⋙ F j :=
      Discrete.natIso (fun ⟨i⟩ => eqToIso (by
        obtain ⟨i, rfl⟩ := i
        rfl))
  exact hasColimitOfIso e

noncomputable def coconeMapObjApplyFunctors (j : J)
    [HasMap ((applyFunctorsObj ((comap (C ⥤ D) p).obj F)).obj X) p] :=
  (((comap _ p).obj F).applyFunctorsObj.obj X).coconeMapObj p j

noncomputable def isColimitCoconeMapObjApplyFunctors (j : J)
    [HasMap ((applyFunctorsObj ((comap (C ⥤ D) p).obj F)).obj X) p] :
    IsColimit (F.coconeMapObjApplyFunctors p X j) := by
  apply isColimitCoconeMapObj

noncomputable def mapCoconeMapObj' (j : J) : Cocone (Discrete.functor (fun (i : (p ⁻¹' {j})) => (F (p i)).obj (X i))) :=
  (Cocones.precompose ((Discrete.natIso (fun ⟨i⟩ => eqToIso (by obtain ⟨i, rfl⟩ := i; rfl))).hom)).obj (F.mapCoconeMapObj p X j)

variable [F.PreservesMap p X]

noncomputable def isColimitMapCoconeMapObj' (j : J) : IsColimit (F.mapCoconeMapObj' p X j) :=
  (IsColimit.precomposeHomEquiv _ _).symm (F.isColimitMapCoconeMapObj p X j)

instance (j : J) : IsIso (F.comapObjApplyFunctorsObjObjMapObj p X j) := by
  suffices F.comapObjApplyFunctorsObjObjMapObj p X j =
      (IsColimit.coconePointUniqueUpToIso (F.isColimitCoconeMapObjApplyFunctors p X j)
        (F.isColimitMapCoconeMapObj' p X j)).hom by
    rw [this]
    infer_instance
  apply mapObj_ext
  rintro i hi
  rw [ι_comapObjApplyFunctorsObjObjMapObj']
  erw [IsColimit.comp_coconePointUniqueUpToIso_hom]
  rfl

instance : IsIso (F.comapObjApplyFunctorsObjObjMapObj p X) :=
  isIso_of_isIso_apply _ (fun _ => inferInstance)

@[simps! hom]
noncomputable def comapObjApplyFunctorsObjObjMapObjIso :
    (((comap _ p).obj F).applyFunctorsObj.obj X).mapObj p ≅
        F.applyFunctorsObj.obj (X.mapObj p) :=
  asIso (F.comapObjApplyFunctorsObjObjMapObj p X)

lemma applyFunctorsObjObjMapObj_ext (j : J) {A : D}
    (f g : F.applyFunctorsObj.obj (X.mapObj p) j ⟶ A)
    (h : ∀ (i : I) (hi : p i = j), (F j).map (X.ιMapObj p i j hi) ≫ f = (F j).map (X.ιMapObj p i j hi) ≫ g) :
    f = g := by
  rw [← cancel_epi ((eval j).mapIso (F.comapObjApplyFunctorsObjObjMapObjIso p X)).hom]
  apply mapObj_ext
  intro i hi
  simp [h]-/

end

end GradedObject

end CategoryTheory
