import Mathlib.CategoryTheory.GradedObject

namespace CategoryTheory

open Category Limits

variable {C D : Type*} [Category C] [Category D]

def Cofan.IsColimit.desc {I : Type*} {F : I → C} {c : Cofan F} (hc : IsColimit c) {A : C}
    (f : ∀ i, F i ⟶ A) : c.pt ⟶ A :=
  hc.desc (Cofan.mk A f)

@[reassoc (attr := simp)]
lemma Cofan.IsColimit.fac {I : Type*} {F : I → C} {c : Cofan F} (hc : IsColimit c) {A : C}
    (f : ∀ i, F i ⟶ A) (i : I) :
    c.proj i ≫ Cofan.IsColimit.desc hc f = f i :=
  hc.fac (Cofan.mk A f) ⟨i⟩

lemma Cofan.IsColimit.hom_ext {I : Type*} {F : I → C} {c : Cofan F} (hc : IsColimit c) {A : C}
    (f g : c.pt ⟶ A) (h : ∀ i, c.proj i ≫ f = c.proj i ≫ g): f = g :=
  hc.hom_ext (fun ⟨i⟩ => h i)

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

@[reassoc (attr := simp)]
lemma iso_hom_inv_id_apply {I : Type*} {X Y : GradedObject I C} (e : X ≅ Y) (i : I) :
    e.hom i ≫ e.inv i = 𝟙 _ :=
  congr_fun e.hom_inv_id i

@[reassoc (attr := simp)]
lemma iso_inv_hom_id_apply {I : Type*} {X Y : GradedObject I C} (e : X ≅ Y) (i : I) :
    e.inv i ≫ e.hom i = 𝟙 _ :=
  congr_fun e.inv_hom_id i

instance {I : Type*} {X Y : GradedObject I C} (f : X ⟶ Y) [IsIso f] (i : I) : IsIso (f i) := by
  change IsIso ((eval i).map f)
  infer_instance

end

section

variable {I J : Type*} (X Y Z : GradedObject I C) (φ : X ⟶ Y) (e : X ≅ Y) (ψ : Y ⟶ Z) (p : I → J)

@[simp]
abbrev mapObjFun (j : J) := (fun (i : (p ⁻¹' {j})) => X i)

variable (j : J)

abbrev HasMap : Prop := ∀ (j : J), HasCoproduct (X.mapObjFun p j)

variable [X.HasMap p] [Y.HasMap p] [Z.HasMap p]

noncomputable def mapObj : GradedObject J C := fun j => ∐ (X.mapObjFun p j)

noncomputable def ιMapObj (i : I) (j : J) (hij : p i = j) : X i ⟶ X.mapObj p j :=
  Sigma.ι (fun (i' : (p ⁻¹' {j})) => X i') ⟨i, hij⟩

abbrev CofanMapObjFun (j : J) := Cofan (X.mapObjFun p j)

@[simp]
def CofanMapObjFun.mk (j : J) (pt : C) (ι' : ∀ (i : I) (_ : p i = j), X i ⟶ pt) : CofanMapObjFun X p j :=
  Cofan.mk pt (fun ⟨i, hi⟩ => ι' i hi)

@[simps!]
noncomputable def cofanMapObj (j : J) : CofanMapObjFun X p j :=
  CofanMapObjFun.mk X p j (X.mapObj p j) (fun i hi => X.ιMapObj p i j hi)

@[ext]
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
noncomputable def isColimitCofanMapObj (j : J) : IsColimit (X.cofanMapObj p j) where
  desc s := descMapObj _ _ (fun i hi => s.ι.app ⟨⟨i, hi⟩⟩)
  fac s := fun ⟨i, hi⟩ => by simp
  uniq s m hm := by
    apply mapObj_ext
    intro i hi
    simpa using hm ⟨i, hi⟩

namespace CofanMapObjFun

lemma hasMap (c : ∀ j, CofanMapObjFun X p j) (hc : ∀ j, IsColimit (c j)) :
    X.HasMap p := fun j => ⟨_, hc j⟩

variable {j X p}
  (c : CofanMapObjFun X p j) (hc : IsColimit c) [X.HasMap p]

noncomputable def iso : c.pt ≅ X.mapObj p j :=
  IsColimit.coconePointUniqueUpToIso hc (X.isColimitCofanMapObj p j)

@[reassoc (attr := simp)]
lemma proj_iso_hom (i : I) (hi : p i = j) :
    c.proj ⟨i, hi⟩ ≫ (c.iso hc).hom = X.ιMapObj p i j hi := by
  apply IsColimit.comp_coconePointUniqueUpToIso_hom

@[reassoc (attr := simp)]
lemma ιMapObj_iso_inv (i : I) (hi : p i = j) :
    X.ιMapObj p i j hi ≫ (c.iso hc).inv = c.proj ⟨i, hi⟩ := by
  apply IsColimit.comp_coconePointUniqueUpToIso_inv

end CofanMapObjFun

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

@[simps]
noncomputable def mapIso : X.mapObj p ≅ Y.mapObj p where
  hom := mapMap e.hom p
  inv := mapMap e.inv p
  hom_inv_id := by rw [← mapMap_comp, e.hom_inv_id, mapMap_id]
  inv_hom_id := by rw [← mapMap_comp, e.inv_hom_id, mapMap_id]

variable (C)

@[simps]
noncomputable def map [∀ (j : J), HasColimitsOfShape (Discrete (p ⁻¹' {j})) C] :
    GradedObject I C ⥤ GradedObject J C where
  obj X := X.mapObj p
  map φ := mapMap φ p

end

section

variable {I J K : Type*} (X Y : GradedObject I C) (p : I → J) (q : J → K) (r : I → K)
  (hpqr : ∀ i, r i = q (p i))

section

variable (k : K) (c : ∀ (j : J) (_ : q j = k), X.CofanMapObjFun p j)
  (hc : ∀ j hj, IsColimit (c j hj))
  (c' : Cofan (fun (j : q ⁻¹' {k}) => (c j.1 j.2).pt))
  (hc' : IsColimit c')

@[simp]
def cofanMapObjComp : X.CofanMapObjFun r k :=
  CofanMapObjFun.mk _ _ _ c'.pt (fun i hi =>
    (c (p i) (by rw [← hpqr, hi])).proj ⟨i, rfl⟩ ≫ c'.proj (⟨p i, by
      rw [Set.mem_preimage, Set.mem_singleton_iff, ← hpqr, hi]⟩))

@[simp]
def isColimitCofanMapObjComp :
    IsColimit (cofanMapObjComp X p q r hpqr k c c') :=
  mkCofanColimit _
    (fun s => Cofan.IsColimit.desc hc'
      (fun ⟨j, (hj : q j = k)⟩ => Cofan.IsColimit.desc (hc j hj)
        (fun ⟨i, (hi : p i = j)⟩ => s.proj ⟨i, by
          simp only [Set.mem_preimage, Set.mem_singleton_iff, hpqr, hi, hj]⟩)))
    (fun s ⟨i, (hi : r i = k)⟩ => by simp)
    (fun s m hm => by
      apply Cofan.IsColimit.hom_ext hc'
      rintro ⟨j, rfl : q j = k⟩
      apply Cofan.IsColimit.hom_ext (hc j rfl)
      rintro ⟨i, rfl : p i = j⟩
      dsimp
      rw [Cofan.IsColimit.fac, Cofan.IsColimit.fac, ← hm]
      dsimp
      rw [assoc])

lemma hasMap_comp [X.HasMap p] [(X.mapObj p).HasMap q] : X.HasMap r :=
  fun k => ⟨_, isColimitCofanMapObjComp X p q r hpqr k _
    (fun j _ => X.isColimitCofanMapObj p j) _ ((X.mapObj p).isColimitCofanMapObj q k)⟩

end

variable [X.HasMap p] [(X.mapObj p).HasMap q] [X.HasMap r]

noncomputable def mapObjMapObjIso : (X.mapObj p).mapObj q ≅ X.mapObj r :=
  isoMk _ _ (fun k => CofanMapObjFun.iso _ (isColimitCofanMapObjComp X p q r hpqr k _
      (fun j _ => X.isColimitCofanMapObj p j) _ ((X.mapObj p).isColimitCofanMapObj q k)))

@[simp]
lemma mapObjMapObjIso_hom (k : K) :
    (mapObjMapObjIso X p q r hpqr).hom k =
      descMapObj _ _ (fun j hj =>
        descMapObj _ _ (fun i hi => X.ιMapObj r i k (by rw [hpqr, hi, hj]))) := rfl

@[simp]
lemma mapObjMapObjIso_inv (k : K) :
    (mapObjMapObjIso X p q r hpqr).inv k =
      descMapObj _ _ (fun i hi => X.ιMapObj p i (p i) rfl ≫
        (X.mapObj p).ιMapObj q (p i) k (by rw [← hi, hpqr])) := rfl

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
  (Discrete.functor (X.mapObjFun p j)) (F j)

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

noncomputable def mapCofanMapObj (j : J) := (F j).mapCocone (X.cofanMapObj p j)

noncomputable def isColimitMapCofanMapObj [F.PreservesMap p X] (j : J) :
    IsColimit (F.mapCofanMapObj p X j) :=
  isColimitOfPreserves (F j) (X.isColimitCofanMapObj p j)

instance [F.PreservesMap p X] :
    HasMap ((applyFunctorsObj ((comap (C ⥤ D) p).obj F)).obj X) p := by
  intro j
  have : HasColimit _ := ⟨_, F.isColimitMapCofanMapObj p X j⟩
  let e : Discrete.functor (fun (i : (p ⁻¹' {j})) => (F (p i)).obj (X i)) ≅
    Discrete.functor (fun (i : (p ⁻¹' {j})) => X i) ⋙ F j :=
      Discrete.natIso (fun ⟨i⟩ => eqToIso (by
        obtain ⟨i, rfl⟩ := i
        rfl))
  exact hasColimitOfIso e

noncomputable def coconeMapObjApplyFunctors (j : J)
    [HasMap ((applyFunctorsObj ((comap (C ⥤ D) p).obj F)).obj X) p] :=
  (((comap _ p).obj F).applyFunctorsObj.obj X).cofanMapObj p j

noncomputable def isColimitCofanMapObjApplyFunctors (j : J)
    [HasMap ((applyFunctorsObj ((comap (C ⥤ D) p).obj F)).obj X) p] :
    IsColimit (F.coconeMapObjApplyFunctors p X j) := by
  apply isColimitCofanMapObj

noncomputable def mapCofanMapObj' (j : J) : Cocone (Discrete.functor (fun (i : (p ⁻¹' {j})) => (F (p i)).obj (X i))) :=
  (Cocones.precompose ((Discrete.natIso (fun ⟨i⟩ => eqToIso (by obtain ⟨i, rfl⟩ := i; rfl))).hom)).obj (F.mapCofanMapObj p X j)

variable [F.PreservesMap p X]

noncomputable def isColimitMapCofanMapObj' (j : J) : IsColimit (F.mapCofanMapObj' p X j) :=
  (IsColimit.precomposeHomEquiv _ _).symm (F.isColimitMapCofanMapObj p X j)

instance (j : J) : IsIso (F.comapObjApplyFunctorsObjObjMapObj p X j) := by
  suffices F.comapObjApplyFunctorsObjObjMapObj p X j =
      (IsColimit.coconePointUniqueUpToIso (F.isColimitCofanMapObjApplyFunctors p X j)
        (F.isColimitMapCofanMapObj' p X j)).hom by
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
