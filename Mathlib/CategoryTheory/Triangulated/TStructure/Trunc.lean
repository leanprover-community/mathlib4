import Mathlib.CategoryTheory.Triangulated.TStructure.Basic

namespace CategoryTheory

open Category Limits Pretriangulated ZeroObject Preadditive

namespace Triangulated

variable {C : Type _} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  (t : TStructure C)

namespace TStructure

lemma triangle_map_ext' (a b : ℤ) (hab : a ≤ b) {T T' : Triangle C} (f₁ f₂ : T ⟶ T')
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C)
    (h₀ : t.IsLE T.obj₁ a) (h₁ : t.IsGE T'.obj₃ b)
    (H : f₁.hom₂ = f₂.hom₂) : f₁ = f₂ := by
  suffices ∀ (f : T ⟶ T') (_ : f.hom₂ = 0), f = 0 by
    rw [← sub_eq_zero]
    apply this
    dsimp
    rw [H, sub_self]
  intro f hf
  ext
  . obtain ⟨g, hg⟩ := covariant_yoneda_exact₂ _ (inv_rot_of_dist_triangle _ hT') f.hom₁ (by
      have eq := f.comm₁
      dsimp at eq ⊢
      rw [← eq, hf, comp_zero])
    have hg' : g = 0 := t.zero_of_isLE_of_isGE g a (b+1) (by linarith) h₀
      (t.isGE_shift T'.obj₃ b (-1) (b+1) (by linarith))
    rw [instAddCommGroupTriangleHom_zero_hom₁, hg, hg', zero_comp]
  . rw [hf, instAddCommGroupTriangleHom_zero_hom₂]
  . obtain ⟨g, hg⟩ := contravariant_yoneda_exact₃ _ hT f.hom₃ (by rw [f.comm₂, hf, zero_comp])
    have hg' : g = 0 := t.zero_of_isLE_of_isGE g (a-1) b (by linarith)
      (t.isLE_shift _ a 1 (a-1) (by linarith)) inferInstance
    rw [instAddCommGroupTriangleHom_zero_hom₃, hg, hg', comp_zero]

lemma triangle_map_exists (n₀ n₁ : ℤ) (h : n₀ < n₁) (T T' : Triangle C)
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C)
    (φ : T.obj₂ ⟶ T'.obj₂)
    (h₀ : t.IsLE T.obj₁ n₀)
    (h₁' : t.IsGE T'.obj₃ n₁) :
    ∃ (f : T ⟶ T'), f.hom₂ = φ := by
  obtain ⟨a, comm₁⟩ := covariant_yoneda_exact₂ _ hT' (T.mor₁ ≫ φ) (t.zero _ n₀ n₁ h)
  obtain ⟨c, ⟨comm₂, comm₃⟩⟩ := complete_distinguished_triangle_morphism _ _ hT hT' a φ comm₁
  exact ⟨
    { hom₁ := a
      hom₂ := φ
      hom₃ := c
      comm₁ := comm₁
      comm₂ := comm₂
      comm₃ := comm₃ }, rfl⟩

lemma triangle_iso_exists (n₀ n₁ : ℤ) (h : n₀ < n₁) (T T' : Triangle C)
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C)
    (e : T.obj₂ ≅ T'.obj₂)
    (h₀ : t.IsLE T.obj₁ n₀) (h₁ : t.IsGE T.obj₃ n₁)
    (h₀' : t.IsLE T'.obj₁ n₀) (h₁' : t.IsGE T'.obj₃ n₁) :
    ∃ (e' : T ≅ T'), e'.hom.hom₂ = e.hom := by
  obtain ⟨hom, hhom⟩ := triangle_map_exists t _ _ h _ _ hT hT' e.hom h₀ h₁'
  obtain ⟨inv, hinv⟩ := triangle_map_exists t _ _ h _ _ hT' hT e.inv h₀' h₁
  refine' ⟨
    { hom := hom
      inv := inv
      hom_inv_id := triangle_map_ext' t n₀ n₁ (by linarith) _ _ hT hT h₀ h₁
        (by simp only [comp_hom₂, id_hom₂, hhom, hinv, e.hom_inv_id])
      inv_hom_id := triangle_map_ext' t n₀ n₁ (by linarith) _ _ hT' hT' h₀' h₁'
        (by simp only [comp_hom₂, id_hom₂, hhom, hinv, e.inv_hom_id]) }, hhom⟩

namespace TruncAux

variable (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (A : C)

noncomputable def triangle : Triangle C :=
  Triangle.mk
    (t.exists_triangle A n₀ n₁ h).choose_spec.choose_spec.choose_spec.choose_spec.choose
    (t.exists_triangle A n₀ n₁
      h).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
    (t.exists_triangle A n₀ n₁
      h).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose

lemma triangle_distinguished :
    triangle t n₀ n₁ h A ∈ distTriang C :=
  (t.exists_triangle A n₀ n₁
      h).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec

instance triangle_obj₁_isLE :
    t.IsLE (triangle t n₀ n₁ h A).obj₁ n₀ :=
  ⟨(t.exists_triangle A n₀ n₁ h).choose_spec.choose_spec.choose⟩

@[simp]
lemma triangle_obj₂ :
    (triangle t n₀ n₁ h A).obj₂ = A := by rfl

instance triangle_obj₃_isGE :
    t.IsGE (triangle t n₀ n₁ h A).obj₃ n₁ :=
  ⟨(t.exists_triangle A n₀ n₁ h).choose_spec.choose_spec.choose_spec.choose⟩

variable {A}
variable {B : C} (φ : A ⟶ B)

lemma triangle_map_ext (f₁ f₂ : triangle t n₀ n₁ h A ⟶ triangle t n₀ n₁ h B)
    (H : f₁.hom₂ = f₂.hom₂) : f₁ = f₂ :=
  triangle_map_ext' t n₀ n₁ (by linarith) _ _
    (triangle_distinguished t n₀ n₁ h A) (triangle_distinguished t n₀ n₁ h B)
    inferInstance inferInstance H

noncomputable def triangle_map : triangle t n₀ n₁ h A ⟶ triangle t n₀ n₁ h B :=
  have H := triangle_map_exists t n₀ n₁ (by linarith) _ _ (triangle_distinguished t n₀ n₁ h A)
    (triangle_distinguished t n₀ n₁ h B) φ inferInstance inferInstance
  { hom₁ := H.choose.hom₁
    hom₂ := φ
    hom₃ := H.choose.hom₃
    comm₁ := by rw [← H.choose.comm₁, H.choose_spec]
    comm₂ := by rw [H.choose.comm₂, H.choose_spec]
    comm₃ := H.choose.comm₃ }

noncomputable def triangleFunctor : C ⥤ Triangle C where
  obj := triangle t n₀ n₁ h
  map φ := triangle_map t n₀ n₁ h φ
  map_id _ := triangle_map_ext t n₀ n₁ h _ _ rfl
  map_comp _ _ := triangle_map_ext t n₀ n₁ h _ _ rfl

lemma triangleFunctor_obj_distinguished (A : C) :
  (triangleFunctor t n₀ n₁ h).obj A ∈ distTriang C :=
    triangle_distinguished t n₀ n₁ h A

variable (A)

@[simp]
lemma triangleFunctor_obj_obj₂ : ((triangleFunctor t n₀ n₁ h).obj A).obj₂ = A := rfl

variable {A}

@[simp]
lemma triangleFunctor_map_hom₂ : ((triangleFunctor t n₀ n₁ h).map φ).hom₂ = φ := rfl

instance triangleFunctor_obj_obj₁_mem_setLE :
    t.IsLE ((triangleFunctor t n₀ n₁ h).obj A).obj₁ n₀ := by
  dsimp [triangleFunctor]
  infer_instance

lemma triangleFunctor_obj_obj₃_mem_setGE :
    t.IsGE ((triangleFunctor t n₀ n₁ h).obj A).obj₃ n₁ := by
  dsimp [triangleFunctor]
  infer_instance

noncomputable def congrTriangleFunctor (n₀ n₁ n₀' n₁' : ℤ) (h : n₀ + 1 = n₁) (h' : n₀' + 1 = n₁')
  (eq : n₀ = n₀') :
    triangleFunctor t n₀ n₁ h ≅ triangleFunctor t n₀' n₁' h' := eqToIso (by
  subst eq
  obtain rfl : n₁ = n₁' := by linarith
  rfl)

end TruncAux

noncomputable def truncLE (n : ℤ) : C ⥤ C :=
  TruncAux.triangleFunctor t n (n+1) rfl ⋙ Triangle.π₁

noncomputable def truncLEι (n : ℤ) : t.truncLE n ⟶ 𝟭 _ :=
  whiskerLeft (TruncAux.triangleFunctor t n (n+1) rfl) Triangle.π₁Toπ₂

noncomputable def truncGE (n : ℤ) : C ⥤ C :=
  TruncAux.triangleFunctor t (n-1) n (by linarith) ⋙ Triangle.π₃

noncomputable def truncGEπ (n : ℤ) : 𝟭 _ ⟶ t.truncGE n  :=
  whiskerLeft (TruncAux.triangleFunctor t (n-1) n (by linarith)) Triangle.π₂Toπ₃

instance (X : C) (n : ℤ) : t.IsLE ((t.truncLE n).obj X) n := by
  dsimp [truncLE]
  infer_instance

instance (X : C) (n : ℤ) : t.IsGE ((t.truncGE n).obj X) n := by
  dsimp [truncGE, TruncAux.triangleFunctor]
  infer_instance

noncomputable def truncGEδLE (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
  t.truncGE n₁ ⟶ t.truncLE n₀ ⋙ shiftFunctor C (1 : ℤ) := by
    refine' _ ≫ whiskerLeft (TruncAux.triangleFunctor t n₀ (n₀+1) rfl) Triangle.π₃Toπ₁
    dsimp only [truncGE]
    exact whiskerRight (((TruncAux.congrTriangleFunctor t (n₁ - 1) n₁ n₀ (n₀ + 1)
      (by linarith) rfl (by linarith))).hom) Triangle.π₃

@[simps!]
noncomputable def truncTriangleLESelfGEFunctor (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) : C ⥤ Triangle C :=
  Triangle.functorMk (t.truncLEι n₀) (t.truncGEπ n₁) (t.truncGEδLE n₀ n₁ h)

@[simp]
lemma truncTriangleLESelfGEFunctor_comp_π₁ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    t.truncTriangleLESelfGEFunctor n₀ n₁ h ⋙ Triangle.π₁ = t.truncLE n₀ := rfl

@[simp]
lemma truncTriangleLESelfGEFunctor_comp_π₂ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    t.truncTriangleLESelfGEFunctor n₀ n₁ h ⋙ Triangle.π₂ = 𝟭 _ := rfl

@[simp]
lemma truncTriangleLESelfGEFunctor_comp_π₃ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    t.truncTriangleLESelfGEFunctor n₀ n₁ h ⋙ Triangle.π₃ = t.truncGE n₁ := rfl

@[simp]
lemma truncTriangleLESelfGEFunctor_π₁Toπ₂ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    whiskerLeft (t.truncTriangleLESelfGEFunctor n₀ n₁ h) Triangle.π₁Toπ₂ =
      t.truncLEι n₀ := rfl

@[simp]
lemma truncTriangleLESelfGEFunctor_π₂Toπ₃ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    whiskerLeft (t.truncTriangleLESelfGEFunctor n₀ n₁ h) Triangle.π₂Toπ₃ =
      t.truncGEπ n₁ := rfl

@[simp]
lemma truncTriangleLESelfGEFunctor_π₃Toπ₁ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    whiskerLeft (t.truncTriangleLESelfGEFunctor n₀ n₁ h) Triangle.π₃Toπ₁ =
      t.truncGEδLE n₀ n₁ h := rfl

lemma truncTriangleLESelfGE_distinguished (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) :
    (t.truncTriangleLESelfGEFunctor n₀ n₁ h).obj X ∈ distTriang C := by
  let e := TruncAux.congrTriangleFunctor t n₀ (n₀ + 1) (n₁ - 1) n₁ rfl (by linarith) (by linarith)
  let e' := TruncAux.congrTriangleFunctor t (n₁-1) n₁ n₀ (n₀ + 1) (by linarith) rfl (by linarith)
  have e'' : t.truncTriangleLESelfGEFunctor n₀ n₁ h ≅
      TruncAux.triangleFunctor t (n₁-1) n₁ (by linarith) := by
    refine' Triangle.functorIsoMk _ _ (isoWhiskerRight e Triangle.π₁) (Iso.refl _)
      (Iso.refl _) _ _ _
    . ext X
      dsimp [truncLEι]
      rw [← (e.hom.app X).comm₁, comp_id]
      dsimp [TruncAux.congrTriangleFunctor]
      rw [eqToHom_app, Triangle.eqToHom_hom₂, eqToHom_refl]
      erw [comp_id]
    . obtain rfl : n₀ = n₁ - 1 := by linarith
      dsimp
      rw [id_comp, comp_id]
      rfl
    . ext X
      dsimp [truncGEδLE]
      rw [assoc, id_comp, ← reassoc_of% ((e'.hom.app X).comm₃), ← Functor.map_comp]
      dsimp [TruncAux.congrTriangleFunctor]
      simp only [eqToHom_app, Triangle.eqToHom_hom₁, eqToHom_trans, eqToHom_refl,
        Functor.map_id, comp_id]
  refine' isomorphic_distinguished _
    (TruncAux.triangleFunctor_obj_distinguished t (n₁-1) n₁ (by linarith) X) _ _
  exact ((evaluation _ _).obj X).mapIso e''

attribute [irreducible] truncLE truncGE truncLEι truncGEπ truncGEδLE

lemma isZero_truncLE_obj_zero (n : ℤ) : IsZero ((t.truncLE n).obj 0) := by
  let δ := (t.truncGEδLE n (n+1) rfl).app 0
  have : IsIso δ := (isIso₃_iff _ ((t.truncTriangleLESelfGE_distinguished n (n+1) rfl 0))).2
      ⟨(isZero_zero C).eq_of_tgt _ _, (isZero_zero C).eq_of_src _ _⟩
  have : t.IsLE ((t.truncLE n ⋙ shiftFunctor C (1 : ℤ)).obj 0) (n-1) :=
    t.isLE_shift _ n 1 (n-1) (by linarith)
  have hδ := t.zero_of_isLE_of_isGE δ (n-1) (n+1) (by linarith)
    (t.isLE_of_iso (asIso δ).symm _) (t.isGE_of_iso (asIso δ) _)
  rw [IsZero.iff_id_eq_zero]
  apply (shiftFunctor C (1 : ℤ)).map_injective
  rw [Functor.map_id, Functor.map_zero, ← cancel_epi δ, comp_zero, hδ, zero_comp]

lemma isZero_truncGE_obj_zero (n : ℤ) : IsZero ((t.truncGE n).obj 0) := by
  apply (isIso₁_iff_isZero₃ _ (t.truncTriangleLESelfGE_distinguished (n-1) n (by linarith) 0)).1
  exact ⟨⟨0, (isZero_truncLE_obj_zero t (n-1)).eq_of_src _ _, (isZero_zero _).eq_of_src _ _⟩⟩

instance (n : ℤ) : t.IsLE (0 : C) n := t.isLE_of_iso (t.isZero_truncLE_obj_zero n).isoZero n
instance (n : ℤ) : t.IsGE (0 : C) n := t.isGE_of_iso (t.isZero_truncGE_obj_zero n).isoZero n

lemma isLE_iff_isIso_truncLEι_app (n : ℤ) (X : C) :
    t.IsLE X n ↔ IsIso ((t.truncLEι n).app X) := by
  constructor
  . intro
    obtain ⟨e, he⟩ := t.triangle_iso_exists n (n+1) (by linarith) _ _
      (contractible_distinguished X)
      (t.truncTriangleLESelfGE_distinguished n (n+1) rfl X) (Iso.refl X) (by dsimp ; infer_instance)
      (by dsimp ; infer_instance) (by dsimp ; infer_instance) (by dsimp ; infer_instance)
    dsimp at he
    have : (truncLEι t n).app X = e.inv.hom₁ := by
      have he' : e.inv.hom₂ = 𝟙 X := by
        rw [← cancel_mono e.hom.hom₂, ← comp_hom₂, e.inv_hom_id, he]
        dsimp
        rw [id_comp]
      simpa [he'] using e.inv.comm₁
    rw [this]
    infer_instance
  . intro
    exact t.isLE_of_iso (asIso ((truncLEι t n).app X)) n

lemma isGE_iff_isIso_truncGEπ_app (n : ℤ) (X : C) :
    t.IsGE X n ↔ IsIso ((t.truncGEπ n).app X) := by
  constructor
  . intro h
    obtain ⟨e, he⟩ := t.triangle_iso_exists (n-1) n (by linarith) _ _
      (inv_rot_of_dist_triangle _ (contractible_distinguished X))
      (t.truncTriangleLESelfGE_distinguished (n-1) n (by linarith) X)
      (Iso.refl X)
        (t.isLE_of_iso (shiftFunctor C (-1 : ℤ)).mapZeroObject.symm _)
        (by dsimp ; infer_instance) (by dsimp ; infer_instance) (by dsimp ; infer_instance)
    dsimp at he
    have : (truncGEπ t n).app X = e.hom.hom₃ := by
      have eq := e.hom.comm₂
      dsimp at eq
      rw [← cancel_epi e.hom.hom₂, ← eq, he]
    rw [this]
    infer_instance
  . intro
    exact t.isGE_of_iso (asIso ((truncGEπ t n).app X)).symm n

instance (X : C) (n : ℤ) [t.IsLE X n] : IsIso ((t.truncLEι n).app X) := by
  rw [← isLE_iff_isIso_truncLEι_app ]
  infer_instance

instance (X : C) (n : ℤ) [t.IsGE X n] : IsIso ((t.truncGEπ n).app X) := by
  rw [← isGE_iff_isIso_truncGEπ_app ]
  infer_instance

lemma isLE_iff_isZero_truncGE_obj (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) :
    t.IsLE X n₀ ↔ IsZero ((t.truncGE n₁).obj X) := by
  rw [t.isLE_iff_isIso_truncLEι_app n₀ X]
  exact isIso₁_iff_isZero₃ _ (t.truncTriangleLESelfGE_distinguished n₀ n₁ h X)

lemma isGE_iff_isZero_truncLE_obj (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) :
    t.IsGE X n₁ ↔ IsZero ((t.truncLE n₀).obj X) := by
  rw [t.isGE_iff_isIso_truncGEπ_app n₁ X]
  exact isIso₂_iff_isZero₁ _ (t.truncTriangleLESelfGE_distinguished n₀ n₁ h X)

lemma isZero_truncGE_obj_of_isLE (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) [t.IsLE X n₀] :
    IsZero ((t.truncGE n₁).obj X) := by
  rw [← t.isLE_iff_isZero_truncGE_obj _ _ h X]
  infer_instance

lemma isZero_truncLE_obj_of_isGE (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) [t.IsGE X n₁] :
    IsZero ((t.truncLE n₀).obj X) := by
  rw [← t.isGE_iff_isZero_truncLE_obj _ _ h X]
  infer_instance

lemma from_truncGE_obj_ext (n : ℤ) (X : C) {Y : C}
    (f₁ f₂ : (t.truncGE n).obj X ⟶ Y) (h : (t.truncGEπ n).app X ≫ f₁ = (t.truncGEπ n).app X ≫ f₂)
    [t.IsGE Y n] :
    f₁ = f₂ := by
  suffices ∀ (f : (t.truncGE n).obj X ⟶ Y) (_ : (t.truncGEπ n).app X ≫ f = 0), f = 0 by
    rw [← sub_eq_zero, this (f₁ - f₂) (by rw [comp_sub, sub_eq_zero, h])]
  intro f hf
  obtain ⟨g, hg⟩ := contravariant_yoneda_exact₃ _
    (t.truncTriangleLESelfGE_distinguished (n-1) n (by linarith) X) f hf
  have hg' := t.zero_of_isLE_of_isGE g (n-2) n (by linarith)
    (by dsimp ; exact t.isLE_shift _ (n-1) 1 (n-2) (by linarith)) (by dsimp ; infer_instance)
  rw [hg, hg', comp_zero]

lemma to_truncLE_obj_ext (n : ℤ) (Y : C) {X : C}
    (f₁ f₂ : Y ⟶ (t.truncLE n).obj X) (h : f₁ ≫ (t.truncLEι n).app X = f₂ ≫ (t.truncLEι n).app X)
    [t.IsLE Y n] :
    f₁ = f₂ := by
  suffices ∀ (f : Y ⟶ (t.truncLE n).obj X) (_ : f ≫ (t.truncLEι n).app X = 0), f = 0 by
    rw [← sub_eq_zero, this (f₁ - f₂) (by rw [sub_comp, sub_eq_zero, h])]
  intro f hf
  obtain ⟨g, hg⟩ := covariant_yoneda_exact₂ _ (inv_rot_of_dist_triangle _
    (t.truncTriangleLESelfGE_distinguished n (n+1) rfl X)) f hf
  have hg' := t.zero_of_isLE_of_isGE g n (n+2) (by linarith) (by dsimp ; infer_instance)
    (by dsimp ; apply (t.isGE_shift _ (n+1) (-1) (n+2) (by linarith)))
  rw [hg, hg', zero_comp]

lemma liftTruncLE' {X Y : C} (f : X ⟶ Y) (n : ℤ) [t.IsLE X n] :
    ∃ (f' : X ⟶ (t.truncLE n).obj Y), f = f' ≫ (t.truncLEι n).app Y :=
  covariant_yoneda_exact₂ _ (t.truncTriangleLESelfGE_distinguished n (n+1) rfl Y) f
    (t.zero_of_isLE_of_isGE  _ n (n+1) (by linarith) inferInstance (by dsimp ; infer_instance))

noncomputable def liftTruncLE {X Y : C} (f : X ⟶ Y) (n : ℤ) [t.IsLE X n] :
    X ⟶ (t.truncLE n).obj Y := (t.liftTruncLE' f n).choose

@[reassoc (attr := simp)]
lemma liftTruncLE_ι {X Y : C} (f : X ⟶ Y) (n : ℤ) [t.IsLE X n] :
    t.liftTruncLE f n ≫ (t.truncLEι n).app Y = f :=
  (t.liftTruncLE' f n).choose_spec.symm

lemma descTruncGE' {X Y : C} (f : X ⟶ Y) (n : ℤ) [t.IsGE Y n] :
  ∃ (f' : (t.truncGE n).obj X ⟶ Y), f = (t.truncGEπ n).app X ≫ f' :=
  contravariant_yoneda_exact₂ _ (t.truncTriangleLESelfGE_distinguished (n-1) n (by linarith) X) f
    (t.zero_of_isLE_of_isGE _ (n-1)  n (by linarith) (by dsimp ; infer_instance) inferInstance)

noncomputable def descTruncGE {X Y : C} (f : X ⟶ Y) (n : ℤ) [t.IsGE Y n] :
    (t.truncGE n).obj X ⟶ Y := (t.descTruncGE' f n).choose

@[reassoc (attr := simp)]
lemma π_descTruncGE {X Y : C} (f : X ⟶ Y) (n : ℤ) [t.IsGE Y n] :
    (t.truncGEπ n).app X ≫ t.descTruncGE f n  = f :=
  (t.descTruncGE' f n).choose_spec.symm

lemma isLE_iff_orthogonal (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) :
    t.IsLE X n₀ ↔ ∀ (Y : C) (f : X ⟶ Y) (_ : t.IsGE Y n₁), f = 0 := by
  constructor
  . intro _ Y f _
    exact t.zero f n₀ n₁ (by linarith)
  . intro hX
    rw [isLE_iff_isZero_truncGE_obj t n₀ n₁ h, IsZero.iff_id_eq_zero]
    apply t.from_truncGE_obj_ext n₁
    rw [comp_zero, comp_id]
    exact hX _ _ inferInstance

lemma isGE_iff_orthogonal (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) :
    t.IsGE X n₁ ↔ ∀ (Y : C) (f : Y ⟶ X) (_ : t.IsLE Y n₀), f = 0 := by
  constructor
  . intro _ Y f _
    exact t.zero f n₀ n₁ (by linarith)
  . intro hX
    rw [isGE_iff_isZero_truncLE_obj t n₀ n₁ h, IsZero.iff_id_eq_zero]
    apply t.to_truncLE_obj_ext n₀
    rw [zero_comp, id_comp]
    exact hX _ _ inferInstance

lemma isLE₂ (T : Triangle C) (hT : T ∈ distTriang C) (n : ℤ) (h₁ : t.IsLE T.obj₁ n)
    (h₃ : t.IsLE T.obj₃ n) : t.IsLE T.obj₂ n := by
  rw [t.isLE_iff_orthogonal n (n+1) rfl]
  intro Y f hY
  obtain ⟨f', hf'⟩ := contravariant_yoneda_exact₂ _ hT f
    (t.zero _ n (n+1) (by linarith) )
  rw [hf', t.zero f' n (n+1) (by linarith), comp_zero]

lemma isGE₂ (T : Triangle C) (hT : T ∈ distTriang C) (n : ℤ) (h₁ : t.IsGE T.obj₁ n)
    (h₃ : t.IsGE T.obj₃ n) : t.IsGE T.obj₂ n := by
  rw [t.isGE_iff_orthogonal (n-1) n (by linarith)]
  intro Y f hY
  obtain ⟨f', hf'⟩ := covariant_yoneda_exact₂ _ hT f (t.zero _ (n-1) n (by linarith))
  rw [hf', t.zero f' (n-1) n (by linarith), zero_comp]

def minus : Triangulated.Subcategory C where
  set X := ∃ (n : ℤ), t.IsLE X n
  zero := ⟨0, inferInstance⟩
  shift := by
    rintro X n ⟨i, hX⟩
    exact ⟨i - n, t.isLE_shift _ i n (i - n) (by linarith)⟩
  ext₂ := by
    rintro T hT ⟨i₁, hi₁⟩ ⟨i₃, hi₃⟩
    exact ⟨max i₁ i₃, t.isLE₂ T hT _ (t.isLE_of_LE _ _ _ (le_max_left i₁ i₃))
      (t.isLE_of_LE _ _ _ (le_max_right i₁ i₃))⟩

def plus : Triangulated.Subcategory C where
  set X := ∃ (n : ℤ), t.IsGE X n
  zero := ⟨0, inferInstance⟩
  shift := by
    rintro X n ⟨i, hX⟩
    exact ⟨i - n, t.isGE_shift _ i n (i - n) (by linarith)⟩
  ext₂ := by
    rintro T hT ⟨i₁, hi₁⟩ ⟨i₃, hi₃⟩
    exact ⟨min i₁ i₃, t.isGE₂ T hT _ (t.isGE_of_GE _ _ _ (min_le_left i₁ i₃))
      (t.isGE_of_GE _ _ _ (min_le_right i₁ i₃))⟩

def bounded : Triangulated.Subcategory C := t.plus ⊓ t.minus

noncomputable def natTransTruncLEOfLE (n₀ n₁ : ℤ) (h : n₀ ≤ n₁) :
    t.truncLE n₀ ⟶ t.truncLE n₁ := by
  have : ∀ (X : C), t.IsLE ((truncLE t n₀).obj X) n₁ := fun _ => t.isLE_of_LE  _ n₀ n₁ h
  exact
  { app := fun X => t.liftTruncLE ((t.truncLEι n₀).app X) n₁
    naturality := fun _ _ _ => by
      apply to_truncLE_obj_ext
      dsimp
      simp }

-- false positive of unusedHavesSuffices
@[reassoc (attr := simp, nolint unusedHavesSuffices)]
lemma natTransTruncLEOfLE_ι_app (n₀ n₁ : ℤ) (h : n₀ ≤ n₁) (X : C) :
    (t.natTransTruncLEOfLE n₀ n₁ h).app X ≫ (t.truncLEι n₁).app X =
      (t.truncLEι n₀).app X := by
  have : IsLE t ((truncLE t n₀).obj X) n₁ := t.isLE_of_LE  _ n₀ n₁ h
  dsimp [natTransTruncLEOfLE]
  rw [t.liftTruncLE_ι]

@[reassoc (attr := simp)]
lemma natTransTruncLEOfLE_ι (a b : ℤ) (h : a ≤ b) :
    t.natTransTruncLEOfLE a b h ≫ t.truncLEι b = t.truncLEι a := by aesop_cat

noncomputable def natTransTruncGEOfGE (n₀ n₁ : ℤ) (h : n₀ ≤ n₁) :
    t.truncGE n₀ ⟶ t.truncGE n₁ := by
  have : ∀ (X : C), IsGE t ((truncGE t n₁).obj X) n₀ := fun _ => t.isGE_of_GE  _ n₀ n₁ h
  exact
  { app := fun X => t.descTruncGE ((t.truncGEπ n₁).app X) n₀
    naturality := fun _ _ _ => by
      apply from_truncGE_obj_ext
      dsimp
      simp only [π_descTruncGE_assoc, ← NatTrans.naturality, ← NatTrans.naturality_assoc,
        π_descTruncGE] }

-- false positive of unusedHavesSuffices
@[reassoc (attr := simp, nolint unusedHavesSuffices)]
lemma π_natTransTruncGEOfGE_app (n₀ n₁ : ℤ) (h : n₀ ≤ n₁) (X : C) :
    (t.truncGEπ n₀).app X ≫ (t.natTransTruncGEOfGE n₀ n₁ h).app X  =
      (t.truncGEπ n₁).app X := by
  have : IsGE t ((truncGE t n₁).obj X) n₀ := t.isGE_of_GE  _ n₀ n₁ h
  dsimp [natTransTruncGEOfGE]
  rw [t.π_descTruncGE]

lemma isIso_truncLEmap_iff {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) :
    IsIso ((t.truncLE n₀).map f) ↔
      ∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ ((t.truncLE n₀).obj X)⟦1⟧)
        (_ : Triangle.mk ((t.truncLEι n₀).app X ≫ f) g h ∈ distTriang _), t.IsGE Z n₁ := by
  constructor
  . intro hf
    refine' ⟨(t.truncGE n₁).obj Y, (t.truncGEπ n₁).app Y,
      (t.truncGEδLE n₀ n₁ hn₁).app Y ≫ (inv ((t.truncLE n₀).map f))⟦1⟧',
      isomorphic_distinguished _ (t.truncTriangleLESelfGE_distinguished n₀ n₁ hn₁ Y) _ _,
      inferInstance⟩
    refine' Triangle.isoMk _ _ (asIso ((t.truncLE n₀).map f)) (Iso.refl _) (Iso.refl _) _ _ _
    all_goals aesop_cat
  . rintro ⟨Z, g, h, mem, _⟩
    obtain ⟨e, he⟩ := t.triangle_iso_exists n₀ n₁ (by linarith)  _ _ mem
      (t.truncTriangleLESelfGE_distinguished n₀ n₁ hn₁ Y) (Iso.refl _)
      (by dsimp ; infer_instance) (by dsimp ; infer_instance)
      (by dsimp ; infer_instance) (by dsimp ; infer_instance)
    suffices ((t.truncLE n₀).map f) = e.hom.hom₁ by
      rw [this]
      infer_instance
    apply to_truncLE_obj_ext
    refine' Eq.trans _ e.hom.comm₁
    aesop_cat

lemma isIso_truncGEmap_iff {Y Z : C} (g : Y ⟶ Z) (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) :
    IsIso ((t.truncGE n₁).map g) ↔
      ∃ (X : C) (f : X ⟶ Y) (h : ((t.truncGE n₁).obj Z) ⟶ X⟦(1 : ℤ)⟧)
        (_ : Triangle.mk f (g ≫ (t.truncGEπ n₁).app Z) h ∈ distTriang _), t.IsLE X n₀ := by
  constructor
  . intro hf
    refine' ⟨(t.truncLE n₀).obj Y, (t.truncLEι n₀).app Y,
      inv ((t.truncGE n₁).map g) ≫ (t.truncGEδLE n₀ n₁ hn₁).app Y,
      isomorphic_distinguished _ (t.truncTriangleLESelfGE_distinguished n₀ n₁ hn₁ Y) _ _,
      inferInstance⟩

    refine' Iso.symm (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
      (asIso ((truncGE t n₁).map g)) _ _ _)
    . aesop_cat
    . dsimp
      rw [id_comp]
      exact ((t.truncGEπ n₁).naturality g).symm
    . aesop_cat
  . rintro ⟨X, f, h, mem, _⟩
    obtain ⟨e, he⟩ := t.triangle_iso_exists n₀ n₁ (by linarith) _ _
      (t.truncTriangleLESelfGE_distinguished n₀ n₁ hn₁ Y) mem (Iso.refl _)
      (by dsimp ; infer_instance) (by dsimp ; infer_instance)
      (by dsimp ; infer_instance) (by dsimp ; infer_instance)
    suffices ((t.truncGE n₁).map g) = e.hom.hom₃ by
      rw [this]
      infer_instance
    apply from_truncGE_obj_ext
    refine' Eq.trans _ e.hom.comm₂.symm
    dsimp at he ⊢
    rw [he, id_comp]
    exact ((t.truncGEπ n₁).naturality g).symm

instance (X : C) (a b : ℤ) [t.IsLE X b] : t.IsLE ((t.truncLE a).obj X) b := by
  by_cases a ≤ b
  . exact t.isLE_of_LE _ _ _ h
  . simp only [not_le] at h
    have : t.IsLE X a := t.isLE_of_LE X b a (by linarith)
    apply t.isLE_of_iso (show X ≅ _ from (asIso ((t.truncLEι a).app X)).symm)

instance (X : C) (a b : ℤ) [t.IsGE X a] : t.IsGE ((t.truncGE b).obj X) a := by
  by_cases a ≤ b
  . exact t.isGE_of_GE _ _ _ h
  . simp only [not_le] at h
    have : t.IsGE X b := t.isGE_of_GE X b a (by linarith)
    apply t.isGE_of_iso (show X ≅ _ from asIso ((t.truncGEπ b).app X))

/- Now, we need the octahedron axiom -/

variable [IsTriangulated C]

lemma isIso₁_truncLEmap_of_GE (T : Triangle C) (hT : T ∈ distTriang C)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (h₃ : t.IsGE T.obj₃ n₁) :
    IsIso ((t.truncLE n₀).map T.mor₁) := by
  rw [isIso_truncLEmap_iff _ _ _ _ h]
  obtain ⟨Z, g, k, mem⟩ := distinguished_cocone_triangle ((t.truncLEι n₀).app T.obj₁ ≫ T.mor₁)
  refine' ⟨_, _, _, mem, _⟩
  have H := someOctahedron rfl (t.truncTriangleLESelfGE_distinguished n₀ n₁ h T.obj₁) hT mem
  exact t.isGE₂ _ H.mem n₁ (by dsimp ; infer_instance) (by dsimp ; infer_instance)

lemma isIso₂_truncGEmap_of_LE (T : Triangle C) (hT : T ∈ distTriang C)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (h₁ : t.IsLE T.obj₁ n₀) :
    IsIso ((t.truncGE n₁).map T.mor₂) := by
  rw [isIso_truncGEmap_iff _ _ _ _ h]
  obtain ⟨X, f, k, mem⟩ := distinguished_cocone_triangle₁ (T.mor₂ ≫ (t.truncGEπ n₁).app T.obj₃)
  refine' ⟨_, _, _, mem, _⟩
  have H := someOctahedron rfl (rot_of_dist_triangle _ hT)
    (rot_of_dist_triangle _ (t.truncTriangleLESelfGE_distinguished n₀ n₁ h T.obj₃))
    (rot_of_dist_triangle _ mem)
  have : t.IsLE (X⟦(1 : ℤ)⟧) (n₀-1) := t.isLE₂ _ H.mem (n₀-1)
    (t.isLE_shift T.obj₁ n₀ 1 (n₀-1) (by linarith))
    (t.isLE_shift ((t.truncLE n₀).obj T.obj₃) n₀ 1 (n₀-1) (by linarith))
  exact t.isLE_of_shift X n₀ 1 (n₀-1) (by linarith)

instance (X : C) (a b : ℤ) [t.IsGE X a] : t.IsGE ((t.truncLE b).obj X) a := by
  rw [t.isGE_iff_isZero_truncLE_obj (a-1) a (by linarith)]
  have := t.isIso₁_truncLEmap_of_GE _ ((t.truncTriangleLESelfGE_distinguished b (b+1) rfl X))
    (a-1) a (by linarith) (by dsimp ; infer_instance)
  dsimp at this
  exact IsZero.of_iso (t.isZero_truncLE_obj_of_isGE (a-1) a (by linarith) X)
    (asIso ((t.truncLE (a - 1)).map ((t.truncLEι b).app X)))

instance (X : C) (a b : ℤ) [t.IsLE X b] : t.IsLE ((t.truncGE a).obj X) b := by
  rw [t.isLE_iff_isZero_truncGE_obj b (b+1) rfl]
  have := t.isIso₂_truncGEmap_of_LE _ ((t.truncTriangleLESelfGE_distinguished (a-1) a (by linarith) X))
    b (b+1) rfl (by dsimp ; infer_instance)
  dsimp at this
  exact IsZero.of_iso (t.isZero_truncGE_obj_of_isLE b (b+1) rfl X)
    (asIso ((t.truncGE (b+1)).map ((t.truncGEπ  a).app X))).symm

noncomputable def truncLELEIsoTruncLE₁ (a b : ℤ) (h : a ≤ b) :
    t.truncLE b ⋙ t.truncLE a ≅ t.truncLE a :=
  have : ∀ (X : C), IsIso ((t.truncLE a).map ((t.truncLEι b).app X)) := fun X =>
    t.isIso₁_truncLEmap_of_GE _ (t.truncTriangleLESelfGE_distinguished b (b+1) rfl X) a _ rfl
      (by dsimp ;exact t.isGE_of_GE _ (a+1) (b+1) (by linarith))
  NatIso.ofComponents (fun X => asIso ((t.truncLE a).map ((t.truncLEι b).app X))) (fun f => by
    dsimp
    rw [← Functor.map_comp, ← Functor.map_comp, NatTrans.naturality, Functor.id_map])

@[simp]
lemma truncLELEIsoTruncLE₁_hom_app (a b : ℤ) (h : a ≤ b) (X : C) :
    (t.truncLELEIsoTruncLE₁ a b h).hom.app X =
      (t.truncLE a).map ((t.truncLEι b).app X) := rfl

noncomputable def truncLT (b : ℤ) : C ⥤ C := t.truncLE (b-1)

noncomputable def truncLTIsoTruncLE (a b : ℤ) (h : a + 1 = b) : t.truncLT b ≅ t.truncLE a :=
  eqToIso (by dsimp only [truncLT] ; congr 1 ; linarith)

noncomputable def truncLTι (n : ℤ) : t.truncLT n ⟶ 𝟭 _ := t.truncLEι _

@[reassoc (attr := simp)]
lemma truncLTIsoTruncLE_hom_ι (a b : ℤ) (h : a + 1 = b) :
    (t.truncLTIsoTruncLE a b h).hom ≫ t.truncLEι a = t.truncLTι b := by
  obtain rfl : a = b - 1 := by linarith
  apply id_comp

@[reassoc (attr := simp)]
lemma truncLTIsoTruncLE_inv_ι (a b : ℤ) (h : a + 1 = b) :
    (t.truncLTIsoTruncLE a b h).inv ≫ t.truncLTι b = t.truncLEι a := by
  obtain rfl : a = b - 1 := by linarith
  apply id_comp

noncomputable def natTransTruncLTLEOfLE (a b : ℤ) (h : a-1 ≤ b) :
    t.truncLT a ⟶ t.truncLE b := t.natTransTruncLEOfLE _ _ h

@[reassoc (attr := simp)]
lemma natTransTruncLTLEOfLE_ι_app (a b : ℤ) (h : a-1 ≤ b) (X : C) :
    (t.natTransTruncLTLEOfLE a b h).app X ≫ (t.truncLEι b).app X = (t.truncLTι a).app X :=
  t.natTransTruncLEOfLE_ι_app _ _ h X

@[reassoc (attr := simp)]
lemma natTransTruncLTLEOfLE_ι (a b : ℤ) (h : a-1 ≤ b) :
    t.natTransTruncLTLEOfLE a b h ≫ t.truncLEι b = t.truncLTι a :=
  t.natTransTruncLEOfLE_ι _ _ h

noncomputable def truncGT (a : ℤ) : C ⥤ C := t.truncGE (a+1)

instance (a : ℤ) (X : C) : t.IsGE ((t.truncGT a).obj X) (a+1) := by
  dsimp [truncGT]
  infer_instance

instance (a : ℤ) (X : C) : t.IsGE ((t.truncGT (a-1)).obj X) a :=
  t.isGE_of_GE _ a (a-1+1) (by linarith)

instance (a b : ℤ) (X : C) [t.IsLE X b] : t.IsLE ((t.truncGT a).obj X) b := by
  dsimp [truncGT]
  infer_instance

noncomputable def truncGTIsoTruncGE (a b : ℤ) (h : a + 1 = b) : t.truncGT a ≅ t.truncGE b :=
  eqToIso (by dsimp only [truncGT] ; congr 1)

noncomputable def truncGTπ (n : ℤ) : 𝟭 _ ⟶ t.truncGT n := t.truncGEπ _

@[reassoc (attr := simp)]
lemma truncGTπ_comp_truncGTIsoTruncGE_hom (a b : ℤ) (h : a + 1 = b) :
    t.truncGTπ a ≫ (t.truncGTIsoTruncGE a b h).hom = t.truncGEπ b := by
  subst h
  apply comp_id

@[reassoc (attr := simp)]
lemma truncGEπ_comp_truncGTIsoTruncGE_inv (a b : ℤ) (h : a + 1 = b) :
    t.truncGEπ b ≫ (t.truncGTIsoTruncGE a b h).inv = t.truncGTπ a := by
  subst h
  apply comp_id

noncomputable def truncGTδLE (n : ℤ) :
    t.truncGT n ⟶ t.truncLE n ⋙ shiftFunctor C (1 : ℤ) := t.truncGEδLE _ _ rfl

@[reassoc (attr := simp)]
lemma truncGTIsoTruncGE_hom_comp_truncLEδGE (a b : ℤ) (h : a + 1 = b) :
    (t.truncGTIsoTruncGE a b h).hom ≫ t.truncGEδLE a b h = t.truncGTδLE a := by
  subst h
  apply id_comp

@[reassoc (attr := simp)]
lemma truncGTIsoTruncGE_inv_comp_truncLEδGT (a b : ℤ) (h : a + 1 = b) :
    (t.truncGTIsoTruncGE a b h).inv ≫ t.truncGTδLE a = t.truncGEδLE a b h := by
  subst h
  apply id_comp

noncomputable def truncTriangleLESelfGTFunctor (n : ℤ) : C ⥤ Triangle C :=
  Triangle.functorMk (t.truncLEι n) (t.truncGTπ n) (t.truncGTδLE n)

@[simp]
lemma truncTriangleLESelfGTFunctor_comp_π₁ (n : ℤ) :
    t.truncTriangleLESelfGTFunctor n ⋙ Triangle.π₁ = t.truncLE n := rfl

@[simp]
lemma truncTriangleLESelfGTFunctor_comp_π₂ (n : ℤ) :
    t.truncTriangleLESelfGTFunctor n ⋙ Triangle.π₂ = 𝟭 _ := rfl

@[simp]
lemma truncTriangleLESelfGTFunctor_comp_π₃ (n : ℤ) :
    t.truncTriangleLESelfGTFunctor n ⋙ Triangle.π₃ = t.truncGT n := rfl

noncomputable def truncTriangleLESelfGTFunctorIsoTruncTriangleLESelfGEFunctor
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    t.truncTriangleLESelfGTFunctor n₀ ≅ t.truncTriangleLESelfGEFunctor n₀ n₁ h := by
  refine' Triangle.functorIsoMk' (Iso.refl _) (Iso.refl _) (t.truncGTIsoTruncGE _ _ h) _ _ _
  all_goals aesop_cat

lemma truncTriangleLESelfGT_distinguished (n : ℤ) (X : C) :
    (t.truncTriangleLESelfGTFunctor n).obj X ∈ distTriang C := by
  refine' isomorphic_distinguished _ (t.truncTriangleLESelfGE_distinguished n (n+1) rfl X) _ _
  exact ((evaluation _ _).obj X).mapIso
    (t.truncTriangleLESelfGTFunctorIsoTruncTriangleLESelfGEFunctor n (n+1) rfl)

noncomputable def truncGEδLT (n : ℤ) :
    t.truncGE n ⟶ t.truncLT n ⋙ shiftFunctor C (1 : ℤ) :=
  t.truncGEδLE (n-1) n (by linarith) ≫
    whiskerRight ((t.truncLTIsoTruncLE (n-1) n (by linarith)).inv) _

lemma truncGEδLT_eq (a b : ℤ) (h : a + 1 = b) :
    t.truncGEδLT b = t.truncGEδLE a b h ≫
      whiskerRight ((t.truncLTIsoTruncLE a b h).inv) _ := by
  obtain rfl : a = b-1 := by linarith
  rfl

@[simp]
lemma truncGEδLT_comp_whiskerRight_truncLTIsoTruncLE_hom (a b : ℤ) (h : a + 1 = b) :
    t.truncGEδLT b ≫ whiskerRight ((t.truncLTIsoTruncLE a b h).hom) _= t.truncGEδLE a b h := by
  simp only [t.truncGEδLT_eq a b h, assoc, ← whiskerRight_comp, Iso.inv_hom_id,
    whiskerRight_id', comp_id]

noncomputable def truncTriangleLTSelfGEFunctor (n : ℤ) : C ⥤ Triangle C :=
  Triangle.functorMk (t.truncLTι n) (t.truncGEπ n) (t.truncGEδLT n)

noncomputable def truncTriangleLTSelfGEFunctorIsoTruncTriangleLESelfGEFunctor
    (a b : ℤ) (h : a + 1 = b) :
    t.truncTriangleLTSelfGEFunctor b ≅ t.truncTriangleLESelfGEFunctor a b h := by
  refine' Triangle.functorIsoMk' (t.truncLTIsoTruncLE _ _ h) (Iso.refl _) (Iso.refl _) _ _ _
  all_goals aesop_cat

lemma truncTriangleLTSelfGE_distinguished (n : ℤ) (X : C) :
    (t.truncTriangleLTSelfGEFunctor n).obj X ∈ distTriang C := by
  refine' isomorphic_distinguished _
    (t.truncTriangleLESelfGE_distinguished (n-1) n (by linarith) X) _ _
  exact ((evaluation _ _).obj X).mapIso
    (t.truncTriangleLTSelfGEFunctorIsoTruncTriangleLESelfGEFunctor (n-1) n (by linarith))


noncomputable def truncGELE (a b : ℤ) : C ⥤ C := t.truncLE b ⋙ t.truncGE a

instance (a b : ℤ) (X : C) : t.IsLE ((t.truncGELE a b).obj X) b := by
  dsimp [truncGELE]
  infer_instance

instance (a b : ℤ) (X : C) : t.IsGE ((t.truncGELE a b).obj X) a := by
  dsimp [truncGELE]
  infer_instance

noncomputable def truncLEπGELE (a b : ℤ) : t.truncLE b ⟶ t.truncGELE a b :=
  whiskerLeft (t.truncLE b) (t.truncGEπ a)

noncomputable def truncGTLE (a b : ℤ) : C ⥤ C := t.truncLE b ⋙ t.truncGT a

noncomputable def truncGTLEIsotruncGELE (a b a' : ℤ) (h : a + 1 = a') :
    t.truncGTLE a b ≅ t.truncGELE a' b :=
  isoWhiskerLeft (t.truncLE b) (t.truncGTIsoTruncGE a a' h)

instance (a b : ℤ) (X : C) : t.IsLE ((t.truncGTLE a b).obj X) b := by
  dsimp [truncGTLE]
  infer_instance

noncomputable def truncLEπGTLE (a b : ℤ) : t.truncLE b ⟶ t.truncGTLE a b :=
  whiskerLeft (t.truncLE b) (t.truncGTπ a)

noncomputable def truncGTLEδLE (a b : ℤ) :
    t.truncGTLE a b ⟶ t.truncLE a ⋙ shiftFunctor C (1 : ℤ) :=
  whiskerRight (t.truncLEι b) (t.truncGT a) ≫ t.truncGTδLE a

noncomputable def truncTriangleLELEGTLEFunctor (a b : ℤ) (h : a ≤ b) : C ⥤ Triangle C :=
  Triangle.functorMk (t.natTransTruncLEOfLE a b h) (t.truncLEπGTLE a b) (t.truncGTLEδLE a b)

@[simp]
lemma truncTriangleLELEGTLEFunctor_comp_π₁ (a b : ℤ) (h : a ≤ b) :
    t.truncTriangleLELEGTLEFunctor a b h ⋙ Triangle.π₁ = t.truncLE a := rfl

@[simp]
lemma truncTriangleLELEGTLEFunctor_comp_π₂ (a b : ℤ) (h : a ≤ b) :
    t.truncTriangleLELEGTLEFunctor a b h ⋙ Triangle.π₂ = t.truncLE b := rfl

@[simp]
lemma truncTriangleLELEGTLEFunctor_comp_π₃ (a b : ℤ) (h : a ≤ b) :
    t.truncTriangleLELEGTLEFunctor a b h ⋙ Triangle.π₃ = t.truncGTLE a b := rfl

@[simp]
lemma truncTriangleLELEGTLEFunctor_π₁Toπ₂ (a b : ℤ) (h : a ≤ b) :
    whiskerLeft (t.truncTriangleLELEGTLEFunctor a b h) Triangle.π₁Toπ₂ =
      t.natTransTruncLEOfLE a b h := rfl

@[simp]
lemma truncTriangleLELEGTLEFunctor_π₂Toπ₃ (a b : ℤ) (h : a ≤ b) :
    whiskerLeft (t.truncTriangleLELEGTLEFunctor a b h) Triangle.π₂Toπ₃ = t.truncLEπGTLE a b := rfl

@[simp]
lemma truncTriangleLELEGTLEFunctor_π₃Toπ₁ (a b : ℤ) (h : a ≤ b) :
    whiskerLeft (t.truncTriangleLELEGTLEFunctor a b h) Triangle.π₃Toπ₁ =
      t.truncGTLEδLE a b := rfl

noncomputable def truncTriangleLELEGTLEFunctorIsoTruncTriangleLESelfGTFunctor
    (a b : ℤ) (h : a ≤ b) : t.truncTriangleLELEGTLEFunctor a b h ≅
    t.truncLE b ⋙ t.truncTriangleLESelfGTFunctor a := by
  apply Iso.symm
  refine' Triangle.functorIsoMk _ _ (t.truncLELEIsoTruncLE₁ a b h) (Iso.refl _) (Iso.refl _)
    _ _ _
  . ext X
    dsimp [truncTriangleLESelfGTFunctor]
    apply t.to_truncLE_obj_ext
    simp only [Functor.id_obj, comp_id, NatTrans.naturality, assoc, Functor.id_map,
      natTransTruncLEOfLE_ι_app_assoc]
  . dsimp only [Iso.refl]
    rw [id_comp, comp_id]
    rfl
  . ext X
    dsimp [truncTriangleLESelfGTFunctor, truncGTLEδLE, truncGT, truncGTδLE]
    simp only [id_comp, NatTrans.naturality, Functor.comp_map]

noncomputable def truncTriangleLELEGTLE_distinguished (a b : ℤ) (h : a ≤ b) (X : C) :
    (t.truncTriangleLELEGTLEFunctor a b h).obj X ∈ distTriang C := by
  refine' isomorphic_distinguished _
    (t.truncTriangleLESelfGT_distinguished a ((t.truncLE b).obj X)) _ _
  exact ((evaluation _ _).obj X).mapIso
    (t.truncTriangleLELEGTLEFunctorIsoTruncTriangleLESelfGTFunctor a b h)

noncomputable def truncGTLEδLT (a b : ℤ) :
    t.truncGELE a b ⟶ t.truncLT a ⋙ shiftFunctor C (1 : ℤ) :=
  (t.truncGTLEIsotruncGELE (a-1) b a (by linarith)).inv ≫ t.truncGTLEδLE (a-1) b ≫
    whiskerRight ((t.truncLTIsoTruncLE (a-1) a (by linarith)).inv) _

noncomputable def truncTriangleLTLEGELEFunctor (a b : ℤ) (h : a-1 ≤ b) : C ⥤ Triangle C :=
  Triangle.functorMk (t.natTransTruncLTLEOfLE a b h) (t.truncLEπGELE a b) (t.truncGTLEδLT a b)

@[simp]
lemma truncTriangleLTLEGELEFunctor_comp_π₁ (a b : ℤ) (h : a-1 ≤ b) :
    t.truncTriangleLTLEGELEFunctor a b h ⋙ Triangle.π₁ = t.truncLT a := rfl

@[simp]
lemma truncTriangleLTLEGELEFunctor_comp_π₂ (a b : ℤ) (h : a-1 ≤ b) :
    t.truncTriangleLTLEGELEFunctor a b h ⋙ Triangle.π₂ = t.truncLE b := rfl

@[simp]
lemma truncTriangleLTLEGELEFunctor_comp_π₃ (a b : ℤ) (h : a-1 ≤ b) :
    t.truncTriangleLTLEGELEFunctor a b h ⋙ Triangle.π₃ = t.truncGELE a b := rfl

@[simp]
lemma truncTriangleLTLEGELEFunctor_π₁Toπ₂ (a b : ℤ) (h : a-1 ≤ b) :
    whiskerLeft (t.truncTriangleLTLEGELEFunctor a b h) Triangle.π₁Toπ₂ =
      t.natTransTruncLTLEOfLE a b h := rfl

@[simp]
lemma truncTriangleLTLEGELEFunctor_π₂Toπ₃ (a b : ℤ) (h : a-1 ≤ b) :
    whiskerLeft (t.truncTriangleLTLEGELEFunctor a b h) Triangle.π₂Toπ₃ =
      t.truncLEπGELE a b := rfl

@[simp]
lemma truncTriangleLTLEGELEFunctor_π₃Toπ₁ (a b : ℤ) (h : a-1 ≤ b) :
    whiskerLeft (t.truncTriangleLTLEGELEFunctor a b h) Triangle.π₃Toπ₁ =
      t.truncGTLEδLT a b := rfl


/-noncomputable def truncTriangleLTLEGELEFunctorIsoTruncTriangleLELEGTLEFunctor
    (a b a' : ℤ) (h : a - 1 ≤ b) (ha' : a' + 1 = a)  : t.truncTriangleLTLEGELEFunctor a b h ≅
    t.truncTriangleLELEGTLEFunctor a' b
      (by simpa only [← ha', add_sub_cancel] using h) := by
  refine' Triangle.functorIsoMk _ _ _ _ _ _ _ _
  . exact t.truncLTIsoTruncLE _ _ ha'
  . exact Iso.refl _
  . exact (t.truncGTLEIsotruncGELE a' b a ha').symm
  . dsimp
    rw [comp_id]
    sorry
  . dsimp
    rw [id_comp]
    sorry
  . dsimp
    sorry

noncomputable def truncTriangleLTLEGELE_distinguished (a b : ℤ) (h : a - 1 ≤ b) (X : C) :
    (t.truncTriangleLTLEGELEFunctor a b h).obj X ∈ distTriang C := by
  refine' isomorphic_distinguished _
    (t.truncTriangleLELEGTLE_distinguished (a-1) b (by linarith) X) _ _
  exact ((evaluation _ _).obj X).mapIso
    (t.truncTriangleLTLEGELEFunctorIsoTruncTriangleLELEGTLEFunctor a b (a-1) h (by linarith))

-- this one should be for internal use only as it is isomorphic to `truncGELE`,
-- see `truncGELEIsoTruncLEGE` below
noncomputable def truncLEGE (a b : ℤ) : C ⥤ C := t.truncGE a ⋙ t.truncLE b

instance (a b : ℤ) (X : C) : t.IsLE ((t.truncLEGE a b).obj X) b := by
  dsimp [truncLEGE]
  infer_instance

instance (a b : ℤ) (X : C) : t.IsGE ((t.truncLEGE a b).obj X) a := by
  dsimp [truncLEGE]
  infer_instance

noncomputable def natTransTruncGELETruncLEGE (a b : ℤ) :
    t.truncGELE a b ⟶ t.truncLEGE a b where
  app X := t.liftTruncLE (t.descTruncGE ((t.truncLEι b).app X ≫ (t.truncGEπ a).app X) a) b
  naturality X Y f := by
    dsimp [truncLEGE, truncGELE]
    apply t.to_truncLE_obj_ext
    dsimp
    apply t.from_truncGE_obj_ext
    simp only [assoc, liftTruncLE_ι, NatTrans.naturality, liftTruncLE_ι_assoc, Functor.id_map,
      Functor.id_obj, π_descTruncGE_assoc, ← NatTrans.naturality_assoc, π_descTruncGE]
    rw [← NatTrans.naturality, NatTrans.naturality_assoc]

@[reassoc (attr := simp)]
lemma natTransTruncGELETruncLEGE_app_pentagon (a b : ℤ) (X : C) :
  (t.truncGEπ a).app _ ≫ (t.natTransTruncGELETruncLEGE a b).app X ≫ (t.truncLEι b).app _ =
    (t.truncLEι b).app X ≫ (t.truncGEπ a).app X := by simp [natTransTruncGELETruncLEGE]

instance (a b : ℤ) (X : C) : IsIso ((t.natTransTruncGELETruncLEGE a b).app X) := by
  by_cases a - 1 ≤ b
  . let u₁₂ := (t.natTransTruncLTLEOfLE a b h).app X
    let u₂₃ : (t.truncLE b).obj X ⟶ X := (t.truncLEι _).app X
    let u₁₃ : _ ⟶ X := (t.truncLTι a).app X
    have eq : u₁₂ ≫ u₂₃ = u₁₃ := by simp
    have H := someOctahedron eq (t.truncTriangleLTLEGELE_distinguished a b h X)
      (t.truncTriangleLESelfGT_distinguished b X)
      (t.truncTriangleLTSelfGE_distinguished a X)
    let m₁ : (t.truncGELE a b).obj _ ⟶ _ := H.m₁
    have := t.isIso₁_truncLEmap_of_GE _ H.mem b _ rfl (by dsimp ; infer_instance)
    dsimp at this
    have eq' : t.liftTruncLE m₁ b = (t.natTransTruncGELETruncLEGE a b).app X := by
      apply t.to_truncLE_obj_ext
      dsimp
      apply t.from_truncGE_obj_ext
      rw [t.liftTruncLE_ι]
      rw [t.natTransTruncGELETruncLEGE_app_pentagon a b X]
      exact H.comm₁
    rw [← eq']
    have fac : (t.truncLEι b).app ((t.truncGE a).obj
        ((t.truncLE b).obj X)) ≫ t.liftTruncLE m₁ b = (t.truncLE b).map H.m₁ :=
      t.to_truncLE_obj_ext _ _ _ _ (by simp)
    exact IsIso.of_isIso_fac_left fac
  . refine' ⟨0, _, _⟩
    all_goals
      apply IsZero.eq_of_src
      exact t.isZero _ b a (by linarith)

instance (a b : ℤ) : IsIso (t.natTransTruncGELETruncLEGE a b) := NatIso.isIso_of_isIso_app _

noncomputable def truncGELEIsoTruncLEGE (a b : ℤ) :
    t.truncGELE a b ≅ t.truncLEGE a b := asIso (t.natTransTruncGELETruncLEGE a b)-/


/-
noncomputable def truncGELEIsoTruncLEGE (a b : ℤ) :
    t.truncLE b ⋙ t.truncGE a ≅ t.truncGE a ⋙ t.truncLE b :=
  NatIso.ofComponents (fun X => asIso (t.truncGELEIsoTruncLEGE_hom_app a b X)) (fun {X Y} f => by
    dsimp [asIso]
    apply from_truncGE_obj_ext
    dsimp
    apply to_truncLE_obj_ext
    rw [assoc, assoc, assoc, assoc, NatTrans.naturality,
      truncGELEIsoTruncLEGE_hom_app_pentagon_assoc, Functor.id_map,
      ← NatTrans.naturality_assoc,
      truncGELEIsoTruncLEGE_hom_app_pentagon,
      Functor.id_map, ← NatTrans.naturality, Functor.id_map,
      NatTrans.naturality_assoc, Functor.id_map])


noncomputable def homology (n : ℤ) : C ⥤ t.Heart :=
  FullSubcategory.lift _ (t.truncGELE n n ⋙ shiftFunctor C n)
    (fun _ => (t.mem_heart_iff _).2 ⟨t.isLE_shift _ n n 0 (add_zero n),
      t.isGE_shift _ n n 0 (add_zero n)⟩)


noncomputable def truncGELT (a b : ℤ) : C ⥤ C := t.truncLT b ⋙ t.truncGE a

noncomputable def truncGELTIsoTruncGELE (a b b' : ℤ) (hb' : b + 1 = b') :
    t.truncGELT a b' ≅ t.truncLE b ⋙ t.truncGE a :=
  isoWhiskerRight (t.truncLTIsoTruncLE b b' hb') _

noncomputable def natTransTruncLTOfLE (a b : ℤ) (h : a ≤ b) :
    t.truncLT a ⟶ t.truncLT b :=
  t.natTransTruncLEOfLE (a-1) (b-1) (by linarith)

noncomputable def truncGELTδ (a b : ℤ) (h : a ≤ b) :
    t.truncGELT a b ⟶ t.truncLT a ⋙ shiftFunctor C (1 : ℤ) :=
  (t.truncGELTIsoTruncGELE a (b-1) b (by linarith)).hom ≫
    whiskerLeft (t.truncLEFiltrationTriangle (a-1) (b-1) (by linarith) a (by linarith))
      Triangle.π₃Toπ₁ ≫
    whiskerRight (t.truncLTIsoTruncLE (a-1) a (by linarith)).inv (shiftFunctor C (1 : ℤ))

noncomputable def truncLTFiltrationTriangle (a b : ℤ) (h : a ≤ b) : C ⥤ Triangle C where
  obj X := Triangle.mk ((t.natTransTruncLTOfLE a b h).app X)
    ((t.truncGEπ a).app ((t.truncLT b).obj X)) ((t.truncGELTδ a b h).app X)
  map φ :=
    { hom₁ := (t.truncLT a).map φ
      hom₂ := (t.truncLT b).map φ
      hom₃ := (t.truncGELT a b).map φ
      comm₂ := by
        dsimp
        erw [← NatTrans.naturality]
        rfl }-/

end TStructure

end Triangulated

end CategoryTheory
