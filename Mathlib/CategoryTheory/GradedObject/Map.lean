import Mathlib.CategoryTheory.GradedObject

namespace CategoryTheory

open Limits

variable {C D : Type*} [Category C] [Category D]

namespace GradedObject

section

@[simps]
def isoMk {I : Type*} (X Y : GradedObject I C) (e : ∀ i, X i ≅ Y i) : X ≅ Y where
  hom i := (e i).hom
  inv i := (e i).inv

lemma isIso_of_isIso_apply {I : Type*} {X Y : GradedObject I C} (f : X ⟶ Y)
    (h : ∀ i, IsIso (f i)) : IsIso f := by
  change IsIso (isoMk X Y (fun i => asIso (f i))).hom
  infer_instance

end

section

variable {I J : Type*} (X Y Z : GradedObject I C) (φ : X ⟶ Y) (ψ : Y ⟶ Z) (p : I → J)

abbrev HasMap : Prop := ∀ (j : J), HasCoproduct (fun (i : (p ⁻¹' {j})) => X i)

variable [X.HasMap p] [Y.HasMap p] [Z.HasMap p]

noncomputable def mapObj : GradedObject J C := fun j => ∐ (fun (i : (p ⁻¹' {j})) => X i)

noncomputable def ιMapObj (i : I) (j : J) (hij : p i = j) : X i ⟶ X.mapObj p j :=
  Sigma.ι (fun (i' : (p ⁻¹' {j})) => X i') ⟨i, hij⟩

@[simps]
noncomputable def coconeMapObj (j : J) : Cocone (Discrete.functor (fun (i : (p ⁻¹' {j})) => X i)) where
  pt := X.mapObj p j
  ι := Discrete.natTrans (fun ⟨i⟩ => X.ιMapObj p i.1 j i.2)

lemma mapObj_ext {A : C} {j : J} (f g : X.mapObj p j ⟶ A)
    (hfg : ∀ (i : I) (hij : p i = j), X.ιMapObj p i j hij ≫ f = X.ιMapObj p i j hij ≫ g) :
    f = g := by
  apply Limits.Sigma.hom_ext
  rintro ⟨i, hij⟩
  exact hfg i hij

attribute [local ext] mapObj_ext

noncomputable def descMapObj {A : C} {j : J} (φ : ∀ (i : I) (_ : p i = j), X i ⟶ A) :
    X.mapObj p j ⟶ A :=
  Limits.Sigma.desc (fun x => φ x.1 x.2)

@[reassoc (attr := simp)]
lemma ι_descMapObj {A : C} {j : J} (φ : ∀ (i : I) (_ : p i = j), X i ⟶ A) (i : I) (hi : p i = j) :
    X.ιMapObj p i j hi ≫ X.descMapObj p φ = φ i hi := by
  simp [descMapObj, ιMapObj]

@[simps]
noncomputable def isColimitCoconeMapObj (j : J) : IsColimit (X.coconeMapObj p j) where
  desc s := descMapObj _ _ (fun i hi => s.ι.app ⟨⟨i, hi⟩⟩)
  fac s := fun ⟨i, hi⟩ => by simp
  uniq s m hm := by
    apply mapObj_ext
    intro i hi
    simpa using hm ⟨i, hi⟩

variable {X Y}

noncomputable def mapMap : X.mapObj p ⟶ Y.mapObj p := fun _ => Limits.Sigma.map (fun i => φ i)

@[reassoc (attr := simp)]
lemma ι_mapMap (i : I) (j : J) (hij : p i = j) :
    X.ιMapObj p i j hij ≫ mapMap φ p j = φ i ≫ Y.ιMapObj p i j hij := by
  simp [ιMapObj, mapMap]

lemma congr_mapMap (φ₁ φ₂ : X ⟶ Y) (h : φ₁ = φ₂) : mapMap φ₁ p = mapMap φ₂ p := by
  subst h
  rfl

variable (X)

@[simp]
lemma mapMap_id : mapMap (𝟙 X) p = 𝟙 _ := by aesop_cat

variable {X Z}

@[simp]
lemma mapMap_comp : mapMap (φ ≫ ψ) p = mapMap φ p ≫ mapMap ψ p := by aesop_cat

variable (C)

abbrev HasMapFunctor := ∀ (j : J), HasColimitsOfShape (Discrete (p ⁻¹' {j})) C

noncomputable def map [HasMapFunctor C p] : GradedObject I C ⥤ GradedObject J C where
  obj X := X.mapObj p
  map φ := mapMap φ p

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

noncomputable def mapCoconeMapObj (j : J) := (F j).mapCocone (X.coconeMapObj p j)

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
  simp [h]

end

end GradedObject

end CategoryTheory
