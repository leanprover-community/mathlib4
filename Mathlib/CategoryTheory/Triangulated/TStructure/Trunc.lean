import Mathlib.CategoryTheory.Triangulated.TStructure.Basic
import Mathlib.CategoryTheory.Triangulated.TStructure.AbstractSpectralObject
import Mathlib.Algebra.Homology.SpectralSequence.ZTilde

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

variable (n : ℤ) (A : C)

noncomputable def triangle : Triangle C :=
  Triangle.mk
    (t.exists_triangle A (n-1) n
      (by linarith)).choose_spec.choose_spec.choose_spec.choose_spec.choose
    (t.exists_triangle A (n-1) n
      (by linarith)).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
    (t.exists_triangle A (n-1) n
      (by linarith)).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose

lemma triangle_distinguished :
    triangle t n A ∈ distTriang C :=
  (t.exists_triangle A (n-1) n (by linarith)
    ).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec

instance triangle_obj₁_isLE (n : ℤ) :
    t.IsLE (triangle t n A).obj₁ (n-1) := by
  exact ⟨(t.exists_triangle A (n-1) n (by linarith)).choose_spec.choose_spec.choose⟩

@[simp]
lemma triangle_obj₂ :
    (triangle t n A).obj₂ = A := by rfl

instance triangle_obj₃_isGE :
    t.IsGE (triangle t n A).obj₃ n :=
  ⟨(t.exists_triangle A (n-1) n (by linarith)).choose_spec.choose_spec.choose_spec.choose⟩

variable {A}
variable {B : C} (φ : A ⟶ B)

lemma triangle_map_ext (f₁ f₂ : triangle t n A ⟶ triangle t n B)
    (H : f₁.hom₂ = f₂.hom₂) : f₁ = f₂ :=
  triangle_map_ext' t (n-1) n (by linarith) _ _
    (triangle_distinguished t n A) (triangle_distinguished t n B)
    inferInstance inferInstance H

noncomputable def triangleMap : triangle t n A ⟶ triangle t n B :=
  have H := triangle_map_exists t (n-1) n (by linarith) _ _ (triangle_distinguished t n A)
    (triangle_distinguished t n B) φ inferInstance inferInstance
  { hom₁ := H.choose.hom₁
    hom₂ := φ
    hom₃ := H.choose.hom₃
    comm₁ := by rw [← H.choose.comm₁, H.choose_spec]
    comm₂ := by rw [H.choose.comm₂, H.choose_spec]
    comm₃ := H.choose.comm₃ }

noncomputable def triangleFunctor : C ⥤ Triangle C where
  obj := triangle t n
  map φ := triangleMap t n φ
  map_id _ := triangle_map_ext t n _ _ rfl
  map_comp _ _ := triangle_map_ext t n _ _ rfl

variable (A)

lemma triangleFunctor_obj_distinguished :
  (triangleFunctor t n).obj A ∈ distTriang C :=
    triangle_distinguished t n A

@[simp]
lemma triangleFunctor_obj_obj₂ : ((triangleFunctor t n).obj A).obj₂ = A := rfl

@[simp]
lemma triangleFunctor_map_hom₂ : ((triangleFunctor t n).map φ).hom₂ = φ := rfl

instance isLE_triangleFunctor_obj_obj₁ :
    t.IsLE ((triangleFunctor t n).obj A).obj₁ (n-1) := by
  dsimp [triangleFunctor]
  infer_instance

instance isGE_triangleFunctor_obj_obj₃ :
    t.IsGE ((triangleFunctor t n).obj A).obj₃ n := by
  dsimp [triangleFunctor]
  infer_instance

noncomputable def triangleMapOfLE (a b : ℤ) (h : a ≤ b) : triangle t a A ⟶ triangle t b A :=
  have H := triangle_map_exists t (a-1) b (by linarith) _ _ (triangle_distinguished t a A)
    (triangle_distinguished t b A) (𝟙 _) inferInstance inferInstance
  { hom₁ := H.choose.hom₁
    hom₂ := 𝟙 _
    hom₃ := H.choose.hom₃
    comm₁ := by rw [← H.choose.comm₁, H.choose_spec]
    comm₂ := by rw [H.choose.comm₂, H.choose_spec]
    comm₃ := H.choose.comm₃ }

noncomputable def triangleFunctorNatTransOfLE (a b : ℤ) (h : a ≤ b) :
    triangleFunctor t a ⟶ triangleFunctor t b where
  app X := triangleMapOfLE t X a b h
  naturality {X₁ X₂} φ := by
    refine' triangle_map_ext' t (a-1) b (by linarith) _ _
      (triangleFunctor_obj_distinguished t a X₁) (triangleFunctor_obj_distinguished t b X₂)
      inferInstance inferInstance _
    dsimp [triangleMapOfLE]
    rw [id_comp, comp_id]

@[simp]
lemma triangleFunctorNatTransOfLE_app_hom₂ (a b : ℤ) (h : a ≤ b) (X : C) :
    ((triangleFunctorNatTransOfLE t a b h).app X).hom₂ = 𝟙 X := rfl

lemma triangleFunctorNatTransOfLE_trans (a b c : ℤ) (hab : a ≤ b) (hbc : b ≤ c) :
    triangleFunctorNatTransOfLE t a b hab ≫ triangleFunctorNatTransOfLE t b c hbc =
      triangleFunctorNatTransOfLE t a c (hab.trans hbc) := by
  apply NatTrans.ext
  ext1 X
  exact triangle_map_ext' t (a-1) c (by linarith) _ _
    (triangleFunctor_obj_distinguished t a X) (triangleFunctor_obj_distinguished t c X)
    inferInstance inferInstance (by aesop_cat)

lemma triangleFunctorNatTransOfLE_refl (a : ℤ) :
    triangleFunctorNatTransOfLE t a a (by rfl) = 𝟙 _ := by
  apply NatTrans.ext
  ext1 X
  exact triangle_map_ext' t (a-1) a (by linarith) _ _
    (triangleFunctor_obj_distinguished t a X) (triangleFunctor_obj_distinguished t a X)
    inferInstance inferInstance (by aesop_cat)

end TruncAux

noncomputable def truncLT (n : ℤ) : C ⥤ C :=
  TruncAux.triangleFunctor t n ⋙ Triangle.π₁

noncomputable def truncLTι (n : ℤ) : t.truncLT n ⟶ 𝟭 _ :=
  whiskerLeft (TruncAux.triangleFunctor t n) Triangle.π₁Toπ₂

noncomputable def truncGE (n : ℤ) : C ⥤ C :=
  TruncAux.triangleFunctor t n ⋙ Triangle.π₃

noncomputable def truncGEπ (n : ℤ) : 𝟭 _ ⟶ t.truncGE n :=
  whiskerLeft (TruncAux.triangleFunctor t n) Triangle.π₂Toπ₃

instance (X : C) (n : ℤ) : t.IsLE ((t.truncLT n).obj X) (n-1) := by
  dsimp [truncLT]
  infer_instance

instance (X : C) (n : ℤ) : t.IsGE ((t.truncGE n).obj X) n := by
  dsimp [truncGE]
  infer_instance

noncomputable def truncGEδLT (n : ℤ) :
  t.truncGE n ⟶ t.truncLT n ⋙ shiftFunctor C (1 : ℤ) :=
    whiskerLeft (TruncAux.triangleFunctor t n) Triangle.π₃Toπ₁

@[simps!]
noncomputable def triangleLTGE (n : ℤ) : C ⥤ Triangle C :=
  Triangle.functorMk (t.truncLTι n) (t.truncGEπ n) (t.truncGEδLT n)

lemma triangleLTGE_distinguished (n : ℤ) (X : C) :
    (t.triangleLTGE n).obj X ∈ distTriang C :=
  TruncAux.triangleFunctor_obj_distinguished t n X

@[reassoc (attr := simp)]
lemma truncLTι_comp_truncGEπ_app (n : ℤ) (X : C) :
    (t.truncLTι n).app X ≫ (t.truncGEπ n).app X = 0 :=
  comp_dist_triangle_mor_zero₁₂ _ ((t.triangleLTGE_distinguished n X))

@[reassoc (attr := simp)]
lemma truncGEπ_comp_truncGEδLT_app (n : ℤ) (X : C) :
    (t.truncGEπ n).app X ≫ (t.truncGEδLT n).app X = 0 :=
  comp_dist_triangle_mor_zero₂₃ _ ((t.triangleLTGE_distinguished n X))

@[reassoc (attr := simp)]
lemma truncGEδLT_comp_truncLTι_app (n : ℤ) (X : C) :
    (t.truncGEδLT n).app X ≫ ((t.truncLTι n).app X)⟦(1 : ℤ)⟧' = 0 :=
  comp_dist_triangle_mor_zero₃₁ _ ((t.triangleLTGE_distinguished n X))

@[reassoc (attr := simp)]
lemma truncLTι_comp_truncGEπ (n : ℤ) :
    t.truncLTι n ≫ t.truncGEπ n = 0 := by aesop_cat

@[reassoc (attr := simp)]
lemma truncGEπ_comp_truncGEδLT (n : ℤ) :
    t.truncGEπ n ≫ t.truncGEδLT n = 0 := by aesop_cat

@[reassoc (attr := simp)]
lemma truncGEδLT_comp_truncLTι (n : ℤ) :
    t.truncGEδLT n ≫ whiskerRight (t.truncLTι n) (shiftFunctor C (1 : ℤ)) = 0 := by aesop_cat

noncomputable def natTransTruncLTOfLE (a b : ℤ) (h : a ≤ b) :
    t.truncLT a ⟶ t.truncLT b :=
  whiskerRight (TruncAux.triangleFunctorNatTransOfLE t a b h) Triangle.π₁

noncomputable def natTransTruncGEOfLE (a b : ℤ) (h : a ≤ b) :
    t.truncGE a ⟶ t.truncGE b :=
  whiskerRight (TruncAux.triangleFunctorNatTransOfLE t a b h) Triangle.π₃

@[reassoc (attr := simp)]
lemma natTransTruncLTOfLE_ι_app (a b : ℤ) (h : a ≤ b) (X : C):
    (t.natTransTruncLTOfLE a b h).app X ≫ (t.truncLTι b).app X = (t.truncLTι a).app X := by
  simpa only [TruncAux.triangleFunctorNatTransOfLE_app_hom₂,
    TruncAux.triangleFunctor_obj_obj₂, comp_id]
    using ((TruncAux.triangleFunctorNatTransOfLE t a b h).app X).comm₁.symm

@[reassoc (attr := simp)]
lemma natTransTruncLTOfLE_ι (a b : ℤ) (h : a ≤ b) :
    t.natTransTruncLTOfLE a b h ≫ t.truncLTι b = t.truncLTι a := by aesop_cat

@[reassoc (attr := simp)]
lemma π_natTransTruncGEOfLE_app (a b : ℤ) (h : a ≤ b) (X : C) :
    (t.truncGEπ a).app X ≫ (t.natTransTruncGEOfLE a b h).app X = (t.truncGEπ b).app X := by
  simpa only [TruncAux.triangleFunctorNatTransOfLE_app_hom₂,
    TruncAux.triangleFunctor_obj_obj₂, id_comp]
    using ((TruncAux.triangleFunctorNatTransOfLE t a b h).app X).comm₂

@[reassoc (attr := simp)]
lemma π_natTransTruncGEOfLE (a b : ℤ) (h : a ≤ b) :
    t.truncGEπ a ≫ t.natTransTruncGEOfLE a b h = t.truncGEπ b := by aesop_cat

@[reassoc]
lemma truncGEδLT_comp_natTransTruncLTOfLE_app (a b : ℤ) (h : a ≤ b) (X : C) :
  (t.truncGEδLT a).app X ≫ ((natTransTruncLTOfLE t a b h).app X)⟦(1 :ℤ)⟧' =
    (t.natTransTruncGEOfLE a b h).app X ≫ (t.truncGEδLT b).app X :=
  ((TruncAux.triangleFunctorNatTransOfLE t a b h).app X).comm₃

@[reassoc]
lemma truncGEδLT_comp_whiskerRight_natTransTruncLTOfLE (a b : ℤ) (h : a ≤ b) :
  t.truncGEδLT a ≫ whiskerRight (natTransTruncLTOfLE t a b h) (shiftFunctor C (1 : ℤ)) =
    t.natTransTruncGEOfLE a b h ≫ t.truncGEδLT b := by
  ext X
  exact t.truncGEδLT_comp_natTransTruncLTOfLE_app a b h X

noncomputable def natTransTriangleLTGEOfLE (a b : ℤ) (h : a ≤ b) :
    t.triangleLTGE a ⟶ t.triangleLTGE b := by
  refine' Triangle.functorHomMk' (t.natTransTruncLTOfLE a b h) (𝟙 _)
    ((t.natTransTruncGEOfLE a b h)) _ _ _
  . dsimp
    simp
  . dsimp
    simp
  . exact t.truncGEδLT_comp_whiskerRight_natTransTruncLTOfLE a b h

@[simp]
lemma natTransTriangleLTGEOfLE_refl (a : ℤ) :
    t.natTransTriangleLTGEOfLE a a (by rfl) = 𝟙 _ :=
  TruncAux.triangleFunctorNatTransOfLE_refl t a

set_option maxHeartbeats 400000 in
lemma natTransTriangleLTGEOfLE_trans (a b c : ℤ) (hab : a ≤ b) (hbc : b ≤ c):
    t.natTransTriangleLTGEOfLE a b hab ≫ t.natTransTriangleLTGEOfLE b c hbc =
      t.natTransTriangleLTGEOfLE a c (hab.trans hbc) :=
  TruncAux.triangleFunctorNatTransOfLE_trans t a b c hab hbc

@[simp]
lemma natTransTruncLTOfLE_refl (a : ℤ) :
    t.natTransTruncLTOfLE a a (by rfl) = 𝟙 _ :=
  congr_arg (fun x => whiskerRight x (Triangle.π₁)) (t.natTransTriangleLTGEOfLE_refl a)

set_option maxHeartbeats 400000 in
@[simp]
lemma natTransTruncLTOfLE_trans (a b c : ℤ) (hab : a ≤ b) (hbc : b ≤ c) :
    t.natTransTruncLTOfLE a b hab ≫ t.natTransTruncLTOfLE b c hbc =
      t.natTransTruncLTOfLE a c (hab.trans hbc) :=
  congr_arg (fun x => whiskerRight x Triangle.π₁)
    (t.natTransTriangleLTGEOfLE_trans a b c hab hbc)

@[simp]
lemma natTransTruncLTOfLE_refl_app (a : ℤ) (X : C) :
    (t.natTransTruncLTOfLE a a (by rfl)).app X = 𝟙 _ :=
  congr_app (t.natTransTruncLTOfLE_refl a) X

@[reassoc (attr := simp)]
lemma natTransTruncLTOfLE_trans_app (a b c : ℤ) (hab : a ≤ b) (hbc : b ≤ c) (X : C) :
    (t.natTransTruncLTOfLE a b hab).app X ≫ (t.natTransTruncLTOfLE b c hbc).app X =
      (t.natTransTruncLTOfLE a c (hab.trans hbc)).app X :=
  congr_app (t.natTransTruncLTOfLE_trans a b c hab hbc) X

@[simp]
lemma natTransTruncGEOfLE_refl (a : ℤ) :
    t.natTransTruncGEOfLE a a (by rfl) = 𝟙 _ :=
  congr_arg (fun x => whiskerRight x (Triangle.π₃)) (t.natTransTriangleLTGEOfLE_refl a)

set_option maxHeartbeats 400000 in
@[simp]
lemma natTransTruncGEOfLE_trans (a b c : ℤ) (hab : a ≤ b) (hbc : b ≤ c) :
    t.natTransTruncGEOfLE a b hab ≫ t.natTransTruncGEOfLE b c hbc =
      t.natTransTruncGEOfLE a c (hab.trans hbc) :=
  congr_arg (fun x => whiskerRight x Triangle.π₃)
    (t.natTransTriangleLTGEOfLE_trans a b c hab hbc)

@[simp]
lemma natTransTruncGEOfLE_refl_app (a : ℤ) (X : C) :
    (t.natTransTruncGEOfLE a a (by rfl)).app X = 𝟙 _ :=
  congr_app (t.natTransTruncGEOfLE_refl a) X

@[reassoc (attr := simp)]
lemma natTransTruncGEOfLE_trans_app (a b c : ℤ) (hab : a ≤ b) (hbc : b ≤ c) (X : C) :
    (t.natTransTruncGEOfLE a b hab).app X ≫ (t.natTransTruncGEOfLE b c hbc).app X =
      (t.natTransTruncGEOfLE a c (hab.trans hbc)).app X :=
  congr_app (t.natTransTruncGEOfLE_trans a b c hab hbc) X


attribute [irreducible] truncLT truncGE truncLTι truncGEπ truncGEδLT
  natTransTruncLTOfLE natTransTruncGEOfLE

noncomputable def truncLE (n : ℤ) : C ⥤ C := t.truncLT (n+1)

instance (n : ℤ) (X : C) : t.IsLE ((t.truncLE n).obj X) n := by
  have : t.IsLE ((t.truncLE n).obj X) (n+1-1) := by
    dsimp [truncLE]
    infer_instance
  exact t.isLE_of_LE _ (n+1-1) n (by linarith)

noncomputable def truncGT (n : ℤ) : C ⥤ C := t.truncGE (n+1)

instance (n : ℤ) (X : C) : t.IsGE ((t.truncGT n).obj X) (n+1) := by
  dsimp [truncGT]
  infer_instance

instance (n : ℤ) (X : C) : t.IsGE ((t.truncGT (n-1)).obj X) n :=
  t.isGE_of_GE _ n (n-1+1) (by linarith)

noncomputable def truncLEIsoTruncLT (a b : ℤ) (h : a + 1 = b) : t.truncLE a ≅ t.truncLT b :=
  eqToIso (congr_arg t.truncLT h)

noncomputable def truncGTIsoTruncGE (a b : ℤ) (h : a + 1 = b) : t.truncGT a ≅ t.truncGE b :=
  eqToIso (congr_arg t.truncGE h)

noncomputable def truncLEι (n : ℤ) : t.truncLE n ⟶ 𝟭 C := t.truncLTι (n + 1)

@[reassoc (attr := simp)]
lemma truncLEIsoTruncLT_hom_ι (a b : ℤ) (h : a + 1 = b) :
    (t.truncLEIsoTruncLT a b h).hom ≫ t.truncLTι b = t.truncLEι a := by
  subst h
  dsimp [truncLEIsoTruncLT, truncLEι]
  rw [id_comp]

@[reassoc (attr := simp)]
lemma truncLEIsoTruncLT_hom_ι_app (a b : ℤ) (h : a + 1 = b) (X : C) :
    (t.truncLEIsoTruncLT a b h).hom.app X ≫ (t.truncLTι b).app X = (t.truncLEι a).app X :=
  congr_app (t.truncLEIsoTruncLT_hom_ι a b h) X

@[reassoc (attr := simp)]
lemma truncLEIsoTruncLT_inv_ι (a b : ℤ) (h : a + 1 = b) :
    (t.truncLEIsoTruncLT a b h).inv ≫ t.truncLEι a = t.truncLTι b := by
  subst h
  dsimp [truncLEIsoTruncLT, truncLEι, truncLE]
  rw [id_comp]

@[reassoc (attr := simp)]
lemma truncLEIsoTruncLT_inv_ι_app (a b : ℤ) (h : a + 1 = b) (X : C) :
    (t.truncLEIsoTruncLT a b h).inv.app X ≫ (t.truncLEι a).app X = (t.truncLTι b).app X :=
  congr_app (t.truncLEIsoTruncLT_inv_ι a b h) X

noncomputable def truncGTπ (n : ℤ) : 𝟭 C ⟶ t.truncGT n := t.truncGEπ (n + 1)

@[reassoc (attr := simp)]
lemma π_truncGTIsoTruncGE_hom (a b : ℤ) (h : a + 1 = b) :
    t.truncGTπ a ≫ (t.truncGTIsoTruncGE a b h).hom = t.truncGEπ b := by
  subst h
  dsimp [truncGTIsoTruncGE, truncGTπ]
  rw [comp_id]

@[reassoc (attr := simp)]
lemma π_truncGTIsoTruncGE_hom_ι_app (a b : ℤ) (h : a + 1 = b) (X : C) :
    (t.truncGTπ a).app X ≫ (t.truncGTIsoTruncGE a b h).hom.app X = (t.truncGEπ b).app X :=
  congr_app (t.π_truncGTIsoTruncGE_hom a b h) X

@[reassoc (attr := simp)]
lemma π_truncGTIsoTruncGE_inv (a b : ℤ) (h : a + 1 = b) :
    t.truncGEπ b ≫ (t.truncGTIsoTruncGE a b h).inv = t.truncGTπ a := by
  subst h
  dsimp [truncGTIsoTruncGE, truncGTπ, truncGT]
  rw [comp_id]

@[reassoc (attr := simp)]
lemma π_truncGTIsoTruncGE_inv_ι_app (a b : ℤ) (h : a + 1 = b) (X : C) :
    (t.truncGEπ b).app X ≫ (t.truncGTIsoTruncGE a b h).inv.app X = (t.truncGTπ a).app X :=
  congr_app (t.π_truncGTIsoTruncGE_inv a b h) X

noncomputable def truncGEδLE (a b : ℤ) (h : a + 1 = b) :
    t.truncGE b ⟶ t.truncLE a ⋙ shiftFunctor C (1 : ℤ) :=
  t.truncGEδLT b ≫ whiskerRight (t.truncLEIsoTruncLT a b h).inv (shiftFunctor C (1 : ℤ))

@[simps!]
noncomputable def triangleLEGE (a b : ℤ) (h : a + 1 = b) : C ⥤ Triangle C :=
  Triangle.functorMk (t.truncLEι a) (t.truncGEπ b) (t.truncGEδLE a b h)

noncomputable def triangleLEGEIsoTriangleLTGE (a b : ℤ) (h : a + 1 = b) :
    t.triangleLEGE a b h ≅ t.triangleLTGE b := by
  refine' Triangle.functorIsoMk _ _ (t.truncLEIsoTruncLT a b h) (Iso.refl _) (Iso.refl _) _ _ _
  . aesop_cat
  . aesop_cat
  . ext
    dsimp [truncGEδLE]
    simp only [assoc, id_comp, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id, comp_id]

lemma triangleLEGE_distinguished (a b : ℤ) (h : a + 1 = b) (X : C) :
    (t.triangleLEGE a b h).obj X ∈ distTriang C :=
  isomorphic_distinguished _ (t.triangleLTGE_distinguished b X) _
    ((t.triangleLEGEIsoTriangleLTGE a b h).app X)

noncomputable def truncGTδLE (n : ℤ) :
    t.truncGT n ⟶ t.truncLE n ⋙ shiftFunctor C (1 : ℤ) :=
  (t.truncGTIsoTruncGE n (n+1) rfl).hom ≫ t.truncGEδLE n (n+1) (by linarith)

@[simps!]
noncomputable def triangleLEGT (n : ℤ) : C ⥤ Triangle C :=
  Triangle.functorMk (t.truncLEι n) (t.truncGTπ n) (t.truncGTδLE n)

noncomputable def triangleLEGTIsoTriangleLEGE (a b : ℤ) (h : a + 1 = b) :
    t.triangleLEGT a ≅ t.triangleLEGE a b h := by
  refine' Triangle.functorIsoMk _ _ (Iso.refl _) (Iso.refl _) (t.truncGTIsoTruncGE a b h) _ _ _
  . aesop_cat
  . aesop_cat
  . ext
    dsimp [truncGTδLE]
    subst h
    simp only [Functor.map_id, comp_id]

lemma triangleLEGT_distinguished (n : ℤ) (X : C) :
    (t.triangleLEGT n).obj X ∈ distTriang C :=
  isomorphic_distinguished _ (t.triangleLEGE_distinguished n (n+1) rfl X) _
    ((t.triangleLEGTIsoTriangleLEGE n (n+1) rfl).app X)

namespace TruncLTt

noncomputable def obj : ℤt → C ⥤ C
  | some none => 0
  | some (some a) => t.truncLT a
  | none => 𝟭 C

noncomputable def map : ∀ {x y : ℤt}, (x ⟶ y) → (obj t x ⟶ obj t y)
  | some none, some none => fun _ => 𝟙 _
  | some none, some (some b) => fun _ => 0
  | some none, none => fun _ => 0
  | some (some a), some none  => fun _ => 0
  | some (some a), some (some b) =>
      fun hab => t.natTransTruncLTOfLE a b (by simpa using (leOfHom hab))
  | some (some a), none => fun _ => t.truncLTι  a
  | none, some none  => fun _ => 0
  | none, some (some b) => fun _ => 0
  | none, none => fun _ => 𝟙 _

end TruncLTt

noncomputable def truncLTt : ℤt ⥤ C ⥤ C where
  obj := TruncLTt.obj t
  map φ := TruncLTt.map t φ
  map_id := by
    rintro (_|_|_)
    . rfl
    . rfl
    . dsimp [TruncLTt.map]
      rw [t.natTransTruncLTOfLE_refl]
      rfl
  map_comp {a b c} hab hbc := by
    replace hab := leOfHom hab
    replace hbc := leOfHom hbc
    obtain (_|_|_) := a <;> obtain (_|_|_) := b <;> obtain (_|_|_) := c
    all_goals simp at hbc hab <;> dsimp [TruncLTt.map] <;> simp

namespace TruncGEt

noncomputable def obj : ℤt → C ⥤ C
  | some none => 𝟭 C
  | some (some a) => t.truncGE a
  | none => 0

noncomputable def map : ∀ {x y : ℤt}, (x ⟶ y) → (obj t x ⟶ obj t y)
  | some none, some none => fun _ => 𝟙 _
  | some none, some (some b) => fun _ => t.truncGEπ b
  | some none, none => fun _ => 0
  | some (some a), some none  => fun _ => 0
  | some (some a), some (some b) =>
      fun hab => t.natTransTruncGEOfLE a b (by simpa using (leOfHom hab))
  | some (some a), none => fun _ => 0
  | none, some none  => fun _ => 0
  | none, some (some b) => fun _ => 0
  | none, none => fun _ => 𝟙 _

end TruncGEt

noncomputable def truncGEt : ℤt ⥤ C ⥤ C where
  obj := TruncGEt.obj t
  map φ := TruncGEt.map t φ
  map_id := by
    rintro (_|a|_)
    . rfl
    . rfl
    . dsimp [TruncGEt.map]
      rw [natTransTruncGEOfLE_refl]
      rfl
  map_comp {a b c} hab hbc := by
    replace hab := leOfHom hab
    replace hbc := leOfHom hbc
    obtain (_|_|_) := a <;> obtain (_|_|_) := b <;> obtain (_|_|_) := c
    all_goals simp at hbc hab <;> dsimp [TruncGEt.map] <;> simp

@[simp]
lemma truncGEt_bot :
    t.truncGEt.obj ⊥ = 𝟭 _ := rfl

@[simp]
lemma truncGEt_top :
    t.truncGEt.obj ⊤ = 0 := rfl

namespace TruncGEtδLTt

noncomputable def app : ∀ (a : ℤt), t.truncGEt.obj a ⟶ t.truncLTt.obj a ⋙ shiftFunctor C (1 : ℤ)
  | some none => 0
  | some (some a) => t.truncGEδLT a
  | none => 0

end TruncGEtδLTt

noncomputable def truncGEtδLTt :
    t.truncGEt ⟶ t.truncLTt ⋙ ((whiskeringRight C C C).obj (shiftFunctor C (1 : ℤ))) where
  app a := TruncGEtδLTt.app t a
  naturality {a b} hab := by
    replace hab := leOfHom hab
    obtain (_|_|a) := a
    . apply IsZero.eq_of_src
      exact isZero_zero _
    all_goals obtain (_|_|b) := b <;> simp at hab <;>
      dsimp [TruncGEtδLTt.app, truncGEt, truncLTt, TruncGEt.map, TruncLTt.map] <;>
      simp [t.truncGEδLT_comp_whiskerRight_natTransTruncLTOfLE]

@[simp]
lemma truncGEtδLTt_mk (n : ℤ) :
    t.truncGEtδLTt.app (ℤt.mk n) = t.truncGEδLT n := rfl

@[simps]
noncomputable def abstractSpectralObject : SpectralObject.AbstractSpectralObject C ℤt where
  truncLT := t.truncLTt
  truncGE := t.truncGEt
  truncLTObjTopIso' := Iso.refl _
  truncGEObjBotIso' := Iso.refl _
  truncGEδLT := t.truncGEtδLTt


namespace AbstractSpectralObject

open SpectralObject

@[simp]
lemma truncGELT_eq (g : Arrow ℤt) :
  (abstractSpectralObject t).truncGELT.obj g =
    t.truncLTt.obj g.right ⋙ t.truncGEt.obj g.left := rfl

noncomputable def isZero_truncGE_obj_top_obj (X : C) :
    IsZero ((t.abstractSpectralObject.truncGE.obj ⊤).obj X) :=
  IsZero.obj (isZero_zero _) _

noncomputable def isZero_truncLT_obj_bot_obj (X : C) :
    IsZero ((t.abstractSpectralObject.truncLT.obj ⊥).obj X) :=
  IsZero.obj (isZero_zero _) _

@[simp]
lemma truncLEι_mk (n : ℤ) :
    t.abstractSpectralObject.truncLTι (ℤt.mk n) = t.truncLTι n :=
  comp_id _

@[simp]
lemma truncGEπ_mk (n : ℤ) :
    t.abstractSpectralObject.truncGEπ (ℤt.mk n) = t.truncGEπ n :=
  id_comp _

@[simp]
lemma truncGEδLT_mk (n : ℤ) :
    t.abstractSpectralObject.truncGEδLT.app (ℤt.mk n) =
      t.truncGEδLT n := rfl

lemma triangleLTGEIso (n : ℤ) (X : C) :
    (t.abstractSpectralObject.triangleLTGE.obj (ℤt.mk n)).obj X ≅
      (t.triangleLTGE n).obj X := by
  refine' Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) _ _ _
  all_goals aesop_cat

@[simp]
lemma truncLTι_top_app (X : C) :
    (t.abstractSpectralObject.truncLTι ⊤).app X = 𝟙 X := by
  dsimp [AbstractSpectralObject.truncLTι]
  erw [Functor.map_id]
  simp only [NatTrans.id_app, id_comp]
  rfl

@[simp]
lemma truncGEπ_bot_app (X : C) :
    (t.abstractSpectralObject.truncGEπ ⊥).app X = 𝟙 X := by
  dsimp [AbstractSpectralObject.truncGEπ]
  erw [Functor.map_id]
  simp only [NatTrans.id_app]
  erw [comp_id]
  rfl

lemma triangleLTGETopIso (X : C) :
  (t.abstractSpectralObject.triangleLTGE.obj ⊤).obj X ≅
    Pretriangulated.contractibleTriangle X := by
  refine' Triangle.isoMk _ _ (((abstractSpectralObject t).truncLTObjTopIso).app X)
    (Iso.refl _) (isZero_truncLT_obj_bot_obj t X).isoZero _ _ _
  . dsimp
    rw [truncLTι_top_app]
    rfl
  . exact IsZero.eq_of_tgt (isZero_zero _) _ _
  . refine' IsZero.eq_of_src _ _ _
    exact IsZero.obj (isZero_zero _) _

lemma triangleLTGEBotIso (X : C) :
  (t.abstractSpectralObject.triangleLTGE.obj ⊥).obj X ≅
    (Pretriangulated.contractibleTriangle X).invRotate := by
  refine' Triangle.isoMk _ _ ((isZero_truncLT_obj_bot_obj t X).isoZero ≪≫
    (shiftFunctor C (-1 : ℤ)).mapZeroObject.symm)
    (((abstractSpectralObject t).truncLTObjTopIso).app X) (Iso.refl _) _ _ _
  . apply IsZero.eq_of_src
    apply isZero_truncLT_obj_bot_obj
  . dsimp
    rw [truncGEπ_bot_app]
    rfl
  . apply IsZero.eq_of_tgt _
    dsimp
    rw [IsZero.iff_id_eq_zero, ← Functor.map_id, ← Functor.map_id, id_zero,
      Functor.map_zero, Functor.map_zero]

lemma distinguished (n : ℤt) (X : C) :
  (t.abstractSpectralObject.triangleLTGE.obj n).obj X ∈ distTriang C := by
  obtain (_|_|n) := n
  . exact isomorphic_distinguished _ (contractible_distinguished X) _
      (triangleLTGETopIso t X)
  . exact isomorphic_distinguished _
      (inv_rot_of_dist_triangle _ (contractible_distinguished X)) _
      (triangleLTGEBotIso t X)
  . exact isomorphic_distinguished _ (t.triangleLTGE_distinguished n X) _
      (triangleLTGEIso t n X)

end AbstractSpectralObject

instance : t.abstractSpectralObject.IsCompatible where
  distinguished := AbstractSpectralObject.distinguished t
  isIso_truncGEToTruncGEGE := sorry
  isIso_truncLTLTToTruncLT := sorry
  isIso_truncLTGELTSelfToTruncLTGE := sorry
  isIso_truncLTGELTSelfToTruncGELT := sorry
  truncGEπ_compatibility' := sorry
  truncLTι_compatibility' := sorry

@[simps!]
noncomputable def spectralObject (X : C) : SpectralObject C ℤt :=
  t.abstractSpectralObject.spectralObject X

lemma isZero_truncLE_obj_zero (n : ℤ) : IsZero ((t.truncLE n).obj 0) := by
  let δ := (t.truncGEδLE n (n+1) rfl).app 0
  have : IsIso δ := (isIso₃_iff _ (t.triangleLEGE_distinguished n (n+1) rfl 0)).2
    ⟨(isZero_zero C).eq_of_tgt _ _, (isZero_zero C).eq_of_src _ _⟩
  have : t.IsLE ((t.truncLE n ⋙ shiftFunctor C (1 : ℤ)).obj 0) (n-1) :=
    t.isLE_shift _ n 1 (n-1) (by linarith)
  have hδ := t.zero_of_isLE_of_isGE δ (n-1) (n+1) (by linarith)
    (t.isLE_of_iso (asIso δ).symm _) (t.isGE_of_iso (asIso δ) _)
  rw [IsZero.iff_id_eq_zero]
  apply (shiftFunctor C (1 : ℤ)).map_injective
  rw [Functor.map_id, Functor.map_zero, ← cancel_epi δ, comp_zero, hδ, zero_comp]

lemma isZero_truncGE_obj_zero (n : ℤ) : IsZero ((t.truncGE n).obj 0) := by
  apply (isIso₁_iff_isZero₃ _ (t.triangleLEGE_distinguished (n-1) n (by linarith) 0)).1
  exact ⟨⟨0, (isZero_truncLE_obj_zero t (n-1)).eq_of_src _ _, (isZero_zero _).eq_of_src _ _⟩⟩

instance (n : ℤ) : t.IsLE (0 : C) n := t.isLE_of_iso (t.isZero_truncLE_obj_zero n).isoZero n
instance (n : ℤ) : t.IsGE (0 : C) n := t.isGE_of_iso (t.isZero_truncGE_obj_zero n).isoZero n

lemma isLE_of_isZero (X : C) (hX : IsZero X) (n : ℤ) : t.IsLE X n :=
  t.isLE_of_iso hX.isoZero.symm n

lemma isGE_of_isZero (X : C) (hX : IsZero X) (n : ℤ) : t.IsGE X n :=
  t.isGE_of_iso hX.isoZero.symm n

lemma isLE_iff_isIso_truncLEι_app (n : ℤ) (X : C) :
    t.IsLE X n ↔ IsIso ((t.truncLEι n).app X) := by
  constructor
  . intro
    obtain ⟨e, he⟩ := t.triangle_iso_exists n (n+1) (by linarith) _ _
      (contractible_distinguished X) (t.triangleLEGT_distinguished n X)
      (Iso.refl X) (by dsimp ; infer_instance)
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
      (t.triangleLTGE_distinguished n X) (Iso.refl X)
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

lemma isLE_iff_isZero_truncGT_obj (n : ℤ) (X : C) :
    t.IsLE X n ↔ IsZero ((t.truncGT n).obj X) := by
  rw [t.isLE_iff_isIso_truncLEι_app n X]
  exact isIso₁_iff_isZero₃ _ (t.triangleLEGT_distinguished n X)

lemma isGE_iff_isZero_truncLT_obj (n : ℤ) (X : C) :
    t.IsGE X n ↔ IsZero ((t.truncLT n).obj X) := by
  rw [t.isGE_iff_isIso_truncGEπ_app n X]
  exact isIso₂_iff_isZero₁ _ (t.triangleLTGE_distinguished n X)

lemma isLE_iff_isZero_truncGE_obj (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) :
    t.IsLE X n₀ ↔ IsZero ((t.truncGE n₁).obj X) := by
  rw [t.isLE_iff_isIso_truncLEι_app n₀ X]
  exact isIso₁_iff_isZero₃ _ (t.triangleLEGE_distinguished n₀ n₁ h X)

lemma isGE_iff_isZero_truncLE_obj (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) :
    t.IsGE X n₁ ↔ IsZero ((t.truncLE n₀).obj X) := by
  rw [t.isGE_iff_isIso_truncGEπ_app n₁ X]
  exact isIso₂_iff_isZero₁ _ (t.triangleLEGE_distinguished n₀ n₁ h X)

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
    (t.triangleLTGE_distinguished n X) f hf
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
    (t.triangleLEGT_distinguished n X)) f hf
  have hg' := t.zero_of_isLE_of_isGE g n (n+2) (by linarith) (by dsimp ; infer_instance)
    (by dsimp ; apply (t.isGE_shift _ (n+1) (-1) (n+2) (by linarith)))
  rw [hg, hg', zero_comp]

lemma to_truncLT_obj_ext (n : ℤ) (Y : C) {X : C}
    (f₁ f₂ : Y ⟶ (t.truncLT n).obj X) (h : f₁ ≫ (t.truncLTι n).app X = f₂ ≫ (t.truncLTι n).app X)
    [t.IsLE Y (n-1)] :
    f₁ = f₂ := by
  rw [← cancel_mono ((t.truncLEIsoTruncLT (n-1) n (by linarith)).inv.app X)]
  apply to_truncLE_obj_ext
  simpa only [Functor.id_obj, assoc, truncLEIsoTruncLT_inv_ι_app] using h

lemma liftTruncLE' {X Y : C} (f : X ⟶ Y) (n : ℤ) [t.IsLE X n] :
    ∃ (f' : X ⟶ (t.truncLE n).obj Y), f = f' ≫ (t.truncLEι n).app Y :=
  covariant_yoneda_exact₂ _ (t.triangleLEGT_distinguished n Y) f
    (t.zero_of_isLE_of_isGE  _ n (n+1) (by linarith) inferInstance (by dsimp ; infer_instance))

noncomputable def liftTruncLE {X Y : C} (f : X ⟶ Y) (n : ℤ) [t.IsLE X n] :
    X ⟶ (t.truncLE n).obj Y := (t.liftTruncLE' f n).choose

@[reassoc (attr := simp)]
lemma liftTruncLE_ι {X Y : C} (f : X ⟶ Y) (n : ℤ) [t.IsLE X n] :
    t.liftTruncLE f n ≫ (t.truncLEι n).app Y = f :=
  (t.liftTruncLE' f n).choose_spec.symm

lemma descTruncGE' {X Y : C} (f : X ⟶ Y) (n : ℤ) [t.IsGE Y n] :
  ∃ (f' : (t.truncGE n).obj X ⟶ Y), f = (t.truncGEπ n).app X ≫ f' :=
  contravariant_yoneda_exact₂ _ (t.triangleLTGE_distinguished n X) f
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

noncomputable def natTransTruncLEOfLE (a b : ℤ) (h : a ≤ b) :
    t.truncLE a ⟶ t.truncLE b :=
  t.natTransTruncLTOfLE (a+1) (b+1) (by linarith)

@[reassoc (attr := simp)]
lemma natTransTruncLEOfLE_ι_app (n₀ n₁ : ℤ) (h : n₀ ≤ n₁) (X : C) :
    (t.natTransTruncLEOfLE n₀ n₁ h).app X ≫ (t.truncLEι n₁).app X =
      (t.truncLEι n₀).app X :=
  t.natTransTruncLTOfLE_ι_app _ _ _ _

@[reassoc (attr := simp)]
lemma natTransTruncLEOfLE_ι (a b : ℤ) (h : a ≤ b) :
    t.natTransTruncLEOfLE a b h ≫ t.truncLEι b = t.truncLEι a := by aesop_cat

@[simp]
lemma natTransTruncLEOfLE_refl (a : ℤ) :
    t.natTransTruncLEOfLE a a (by rfl) = 𝟙 _ :=
  t.natTransTruncLTOfLE_refl _

@[simp]
lemma natTransTruncLEOfLE_trans (a b c : ℤ) (hab : a ≤ b) (hbc : b ≤ c) :
    t.natTransTruncLEOfLE a b hab ≫ t.natTransTruncLEOfLE b c hbc =
      t.natTransTruncLEOfLE a c (hab.trans hbc) :=
  t.natTransTruncLTOfLE_trans _ _ _ _ _

@[simp]
lemma natTransTruncLEOfLE_refl_app (a : ℤ) (X : C) :
    (t.natTransTruncLEOfLE a a (by rfl)).app X = 𝟙 _ :=
  congr_app (t.natTransTruncLEOfLE_refl a) X

@[reassoc (attr := simp)]
lemma natTransTruncLEOfLE_trans_app (a b c : ℤ) (hab : a ≤ b) (hbc : b ≤ c) (X : C) :
    (t.natTransTruncLEOfLE a b hab).app X ≫ (t.natTransTruncLEOfLE b c hbc).app X =
      (t.natTransTruncLEOfLE a c (hab.trans hbc)).app X :=
  congr_app (t.natTransTruncLEOfLE_trans a b c hab hbc) X

lemma isIso_truncLTmap_iff {X Y : C} (f : X ⟶ Y) (n : ℤ) :
    IsIso ((t.truncLT n).map f) ↔
      ∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ ((t.truncLT n).obj X)⟦1⟧)
        (_ : Triangle.mk ((t.truncLTι n).app X ≫ f) g h ∈ distTriang _), t.IsGE Z n := by
  constructor
  . intro hf
    refine' ⟨(t.truncGE n).obj Y, (t.truncGEπ n).app Y,
      (t.truncGEδLT n).app Y ≫ (inv ((t.truncLT n).map f))⟦1⟧',
      isomorphic_distinguished _ (t.triangleLTGE_distinguished n Y) _ _, inferInstance⟩
    refine' Triangle.isoMk _ _ (asIso ((t.truncLT n).map f)) (Iso.refl _) (Iso.refl _) _ _ _
    all_goals aesop_cat
  . rintro ⟨Z, g, h, mem, _⟩
    obtain ⟨e, he⟩ := t.triangle_iso_exists (n-1) n (by linarith)  _ _ mem
      (t.triangleLTGE_distinguished n Y) (Iso.refl _)
      (by dsimp ; infer_instance) (by dsimp ; infer_instance)
      (by dsimp ; infer_instance) (by dsimp ; infer_instance)
    suffices ((t.truncLT n).map f) = e.hom.hom₁ by
      rw [this]
      infer_instance
    apply to_truncLT_obj_ext
    refine' Eq.trans _ e.hom.comm₁
    aesop_cat

lemma isIso_truncLEmap_iff {X Y : C} (f : X ⟶ Y) (a b : ℤ) (h : a + 1 = b) :
    IsIso ((t.truncLE a).map f) ↔
      ∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ ((t.truncLE a).obj X)⟦1⟧)
        (_ : Triangle.mk ((t.truncLEι a).app X ≫ f) g h ∈ distTriang _), t.IsGE Z b := by
  subst h
  apply isIso_truncLTmap_iff

lemma isIso_truncGEmap_iff {Y Z : C} (g : Y ⟶ Z) (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) :
    IsIso ((t.truncGE n₁).map g) ↔
      ∃ (X : C) (f : X ⟶ Y) (h : ((t.truncGE n₁).obj Z) ⟶ X⟦(1 : ℤ)⟧)
        (_ : Triangle.mk f (g ≫ (t.truncGEπ n₁).app Z) h ∈ distTriang _), t.IsLE X n₀ := by
  constructor
  . intro hf
    refine' ⟨(t.truncLE n₀).obj Y, (t.truncLEι n₀).app Y,
      inv ((t.truncGE n₁).map g) ≫ (t.truncGEδLE n₀ n₁ hn₁).app Y,
      isomorphic_distinguished _ (t.triangleLEGE_distinguished n₀ n₁ hn₁ Y) _ _,
      inferInstance⟩
    refine' Iso.symm (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
      (asIso ((t.truncGE n₁).map g)) _ _ _)
    . aesop_cat
    . dsimp
      rw [id_comp]
      exact ((t.truncGEπ n₁).naturality g).symm
    . aesop_cat
  . rintro ⟨X, f, h, mem, _⟩
    obtain ⟨e, he⟩ := t.triangle_iso_exists n₀ n₁ (by linarith) _ _
      (t.triangleLEGE_distinguished n₀ n₁ hn₁ Y) mem (Iso.refl _)
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

lemma isIso_truncGTmap_iff {Y Z : C} (g : Y ⟶ Z) (n : ℤ) :
    IsIso ((t.truncGT n).map g) ↔
      ∃ (X : C) (f : X ⟶ Y) (h : ((t.truncGT n).obj Z) ⟶ X⟦(1 : ℤ)⟧)
        (_ : Triangle.mk f (g ≫ (t.truncGTπ n).app Z) h ∈ distTriang _), t.IsLE X n :=
  t.isIso_truncGEmap_iff g n (n+1) rfl

instance (X : C) (a b : ℤ) [t.IsLE X b] : t.IsLE ((t.truncLE a).obj X) b := by
  by_cases a ≤ b
  . exact t.isLE_of_LE _ _ _ h
  . simp only [not_le] at h
    have : t.IsLE X a := t.isLE_of_LE X b a (by linarith)
    apply t.isLE_of_iso (show X ≅ _ from (asIso ((t.truncLEι a).app X)).symm)

instance (X : C) (a b : ℤ) [t.IsLE X b] : t.IsLE ((t.truncLT a).obj X) b :=
  t.isLE_of_iso ((t.truncLEIsoTruncLT (a-1) a (by linarith)).app X) b

instance (X : C) (a b : ℤ) [t.IsGE X a] : t.IsGE ((t.truncGE b).obj X) a := by
  by_cases a ≤ b
  . exact t.isGE_of_GE _ _ _ h
  . simp only [not_le] at h
    have : t.IsGE X b := t.isGE_of_GE X b a (by linarith)
    apply t.isGE_of_iso (show X ≅ _ from asIso ((t.truncGEπ b).app X))

instance (X : C) (a b : ℤ) [t.IsGE X a] : t.IsGE ((t.truncGT b).obj X) a :=
  t.isGE_of_iso ((t.truncGTIsoTruncGE b (b+1) (by linarith)).symm.app X) a

noncomputable def truncGELT (a b : ℤ) : C ⥤ C := t.truncLT b ⋙ t.truncGE a

noncomputable def truncGELE (a b : ℤ) : C ⥤ C := t.truncLE b ⋙ t.truncGE a

noncomputable def truncGELEIsoTruncGELT (a b b' : ℤ) (hb' : b + 1 = b') :
    t.truncGELE a b ≅ t.truncGELT a b' :=
  isoWhiskerRight (t.truncLEIsoTruncLT b b' hb') _

instance (X : C) (a b : ℤ) : t.IsGE ((t.truncGELE a b).obj X) a := by
  dsimp [truncGELE]
  infer_instance

instance (X : C) (a b : ℤ) : t.IsLE ((t.truncGELE a b).obj X) b := by
  sorry -- see below

instance (i : ℤt) : (t.truncGEt.obj i).Additive := sorry

@[simp]
lemma truncGEt_obj_mk (n : ℤ) : t.truncGEt.obj (ℤt.mk n) = t.truncGE n := rfl

lemma isZero_truncLTt_obj_obj (X : C) (n : ℤ) [t.IsGE X n] (j : ℤt) (hj : j ≤ ℤt.mk n) :
  IsZero ((t.truncLTt.obj j).obj X) := sorry

lemma truncGEt_obj_obj_isGE (n : ℤ) (i : ℤt) (h : ℤt.mk n ≤ i) (X : C) :
    t.IsGE ((t.truncGEt.obj i).obj X) n := by
  obtain (rfl|⟨i, rfl⟩|rfl) := i.three_cases
  . simp at h
  . simp at h
    dsimp
    exact t.isGE_of_GE  _ _ _ h
  . dsimp
    apply t.isGE_of_isZero
    apply Functor.zero_obj


noncomputable def homology' (n : ℤ) : C ⥤ C := t.truncGELE n n ⋙ shiftFunctor C n

instance (X : C) : t.IsLE ((t.homology' n).obj X) 0 :=
  t.isLE_shift _ n n 0 (add_zero n)

instance (X : C) : t.IsGE ((t.homology' n).obj X) 0 :=
  t.isGE_shift _ n n 0 (add_zero n)

lemma homology'_obj_mem_heart (n : ℤ) (X : C) : (t.homology' n).obj X ∈ t.heart := by
  rw [mem_heart_iff]
  exact ⟨inferInstance, inferInstance⟩

noncomputable def homology (n : ℤ) : C ⥤ t.Heart :=
  FullSubcategory.lift _ (t.truncGELE n n ⋙ shiftFunctor C n) (t.homology'_obj_mem_heart n)

noncomputable def homologyCompιHeart (n : ℤ) :
  t.homology n ⋙ t.ιHeart ≅ t.truncGELE n n ⋙ shiftFunctor C n :=
    FullSubcategory.lift_comp_inclusion _ _ _

noncomputable def homologyCompιHeartDegreeIsoHomology' (q : ℤ) :
    t.homology q ⋙ t.ιHeartDegree q ≅ t.truncGELE q q :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (t.homologyCompιHeart q) _ ≪≫ Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _  (shiftFunctorCompIsoId C q (-q) (add_right_neg q)) ≪≫
    Functor.rightUnitor _

/-noncomputable def spectralObjectω₁IsoHomologyιHeartDegree (X : C) (q q' : ℤ) (hq' : q + 1 = q') :
    (t.spectralObject X).ω₁.obj (ιℤt.mapArrow.obj (Arrow.mkOfLE q q')) ≅
      (t.homology q ⋙ t.ιHeartDegree q).obj X :=
  (t.truncGELEIsoTruncGELT q q q' hq').symm.app X ≪≫
    (t.homologyCompιHeartDegreeIsoHomology' q).symm.app X-/

noncomputable def shiftSpectralObjectω₁IsoHomologyιHeart (X : C) (q q' : ℤ) (hq' : q + 1 = q') :
    ((t.spectralObject X).ω₁ ⋙ shiftFunctor C q).obj (ιℤt.mapArrow.obj (Arrow.mkOfLE q q')) ≅
      (t.homology q ⋙ t.ιHeart).obj X :=
  (shiftFunctor C q).mapIso ((t.truncGELEIsoTruncGELT q q q' hq').symm.app X) ≪≫
    (t.homologyCompιHeart q).symm.app X

/- Now, we need the octahedron axiom -/

/-variable [IsTriangulated C]

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

@[reassoc (attr := simp)]
lemma truncLTIsoTruncLE_hom_comp_natTransTruncLEOfLE (a a' b : ℤ) (ha' : a' + 1 = a) (h : a' ≤ b):
  (t.truncLTIsoTruncLE a' a ha').hom ≫ t.natTransTruncLEOfLE a' b h =
    t.natTransTruncLTLEOfLE a b (by simpa only [← ha', add_sub_cancel] using h) := by
  obtain rfl : a' = a - 1 := by linarith
  apply id_comp

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

@[reassoc (attr := simp)]
lemma truncGEπ_comp_truncGEδLT (n : ℤ) :
    t.truncGEπ n ≫ t.truncGEδLT n = 0 := by
  ext X
  exact comp_dist_triangle_mor_zero₂₃ _ (t.truncTriangleLTSelfGE_distinguished n X)

@[reassoc (attr := simp)]
lemma truncGEδLT_comp_truncLTι (n : ℤ) :
    t.truncGEδLT n ≫ whiskerRight (t.truncLTι n) (shiftFunctor C (1 : ℤ)) = 0 := by
  ext X
  exact comp_dist_triangle_mor_zero₃₁ _ (t.truncTriangleLTSelfGE_distinguished n X)

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

noncomputable def truncGTLEIsoTruncGELE (a b a' : ℤ) (h : a + 1 = a') :
    t.truncGTLE a b ≅ t.truncGELE a' b :=
  isoWhiskerLeft (t.truncLE b) (t.truncGTIsoTruncGE a a' h)

instance (a b : ℤ) (X : C) : t.IsLE ((t.truncGTLE a b).obj X) b := by
  dsimp [truncGTLE]
  infer_instance

noncomputable def truncLEπGTLE (a b : ℤ) : t.truncLE b ⟶ t.truncGTLE a b :=
  whiskerLeft (t.truncLE b) (t.truncGTπ a)

@[reassoc (attr := simp)]
lemma truncLEπGELE_comp_truncGTLEIsoTruncGELE_inv (a b a' : ℤ) (h : a' + 1 = a) :
    t.truncLEπGELE a b ≫ (t.truncGTLEIsoTruncGELE a' b a h).inv = t.truncLEπGTLE a' b := by
  subst h
  apply comp_id

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

noncomputable def truncGELEδLT (a b : ℤ) :
    t.truncGELE a b ⟶ t.truncLT a ⋙ shiftFunctor C (1 : ℤ) :=
  (t.truncGTLEIsoTruncGELE (a-1) b a (by linarith)).inv ≫ t.truncGTLEδLE (a-1) b ≫
    whiskerRight ((t.truncLTIsoTruncLE (a-1) a (by linarith)).inv) _

@[reassoc (attr := simp)]
lemma truncGELEδLT_comp_truncLTIsoTruncLE_hom (a a' b : ℤ) (ha' : a' + 1 = a) :
    t.truncGELEδLT a b ≫
      whiskerRight (t.truncLTIsoTruncLE a' a ha').hom (shiftFunctor C (1 : ℤ)) =
        (t.truncGTLEIsoTruncGELE a' b a ha').inv ≫ t.truncGTLEδLE a' b := by
  obtain rfl : a' = a - 1 := by linarith
  dsimp only [truncGELEδLT]
  simp only [assoc, ← whiskerRight_comp, Iso.inv_hom_id, whiskerRight_id', comp_id]

noncomputable def truncTriangleLTLEGELEFunctor (a b : ℤ) (h : a-1 ≤ b) : C ⥤ Triangle C :=
  Triangle.functorMk (t.natTransTruncLTLEOfLE a b h) (t.truncLEπGELE a b) (t.truncGELEδLT a b)

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
      t.truncGELEδLT a b := rfl

noncomputable def truncTriangleLTLEGELEFunctorIsoTruncTriangleLELEGTLEFunctor
    (a b a' : ℤ) (h : a - 1 ≤ b) (ha' : a' + 1 = a)  : t.truncTriangleLTLEGELEFunctor a b h ≅
    t.truncTriangleLELEGTLEFunctor a' b
      (by simpa only [← ha', add_sub_cancel] using h) := by
  refine' Triangle.functorIsoMk _ _ (t.truncLTIsoTruncLE _ _ ha') (Iso.refl _)
    ((t.truncGTLEIsoTruncGELE a' b a ha').symm) _ _ _
  all_goals aesop_cat

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
      t.to_truncLE_obj_ext _ _ _ _ (by simp [truncGELE])
    exact IsIso.of_isIso_fac_left fac
  . refine' ⟨0, _, _⟩
    all_goals
      apply IsZero.eq_of_src
      exact t.isZero _ b a (by linarith)

instance (a b : ℤ) : IsIso (t.natTransTruncGELETruncLEGE a b) := NatIso.isIso_of_isIso_app _

noncomputable def truncGELEIsoTruncLEGE (a b : ℤ) :
    t.truncGELE a b ≅ t.truncLEGE a b := asIso (t.natTransTruncGELETruncLEGE a b)


noncomputable def truncGELT (a b : ℤ) : C ⥤ C := t.truncLT b ⋙ t.truncGE a

noncomputable def truncGELTIsoTruncGELE (a b b' : ℤ) (hb' : b + 1 = b') :
    t.truncGELT a b' ≅ t.truncLE b ⋙ t.truncGE a :=
  isoWhiskerRight (t.truncLTIsoTruncLE b b' hb') (t.truncGE a)

noncomputable def natTransTruncLTOfLE (a b : ℤ) (h : a ≤ b) :
    t.truncLT a ⟶ t.truncLT b :=
  t.natTransTruncLEOfLE (a-1) (b-1) (by linarith)

@[simp]
lemma natTransTruncLTOfLE_eq_id (n : ℤ) :
    t.natTransTruncLTOfLE n n (by rfl) = 𝟙 _ :=
  t.natTransTruncLEOfLE_eq_id (n-1)

@[reassoc (attr := simp)]
lemma natTransTruncLTOfLE_comp (a b c : ℤ) (hab : a ≤ b) (hbc : b ≤ c) :
    t.natTransTruncLTOfLE a b hab ≫ t.natTransTruncLTOfLE b c hbc =
      t.natTransTruncLTOfLE a c (hab.trans hbc) :=
  t.natTransTruncLEOfLE_comp (a-1) (b-1) (c-1) (by linarith) (by linarith)

@[reassoc (attr := simp)]
lemma natTransTruncLTOfLE_ι (a b : ℤ) (h : a ≤ b) :
    t.natTransTruncLTOfLE a b h ≫ t.truncLTι b = t.truncLTι a :=
  t.natTransTruncLEOfLE_ι (a-1) (b-1) (by linarith)

@[reassoc (attr := simp)]
lemma natTransTruncLTOfLE_comp_truncLTIsoTruncLE_hom (a b b' : ℤ) (h : a ≤ b) (hb' : b' + 1 = b) :
    t.natTransTruncLTOfLE a b h ≫ (t.truncLTIsoTruncLE b' b hb').hom =
      t.natTransTruncLTLEOfLE a b' ((Int.sub_le_sub_right h 1).trans
        (by simp only [← hb', add_sub_cancel, le_refl])) := by
  obtain rfl : b' = b - 1 := by linarith
  apply comp_id

noncomputable def truncLTπGELT (a b : ℤ) :
    t.truncLT b ⟶ t.truncGELT a b :=
  whiskerLeft (t.truncLT b) (t.truncGEπ a)

@[reassoc (attr := simp)]
lemma truncLTπGELT_comp_truncGELTIsoTruncGELE_hom (a b b' : ℤ) (hb' : b' + 1 = b) :
    t.truncLTπGELT a b ≫ (t.truncGELTIsoTruncGELE a b' b hb').hom =
      (t.truncLTIsoTruncLE b' b hb').hom ≫ t.truncLEπGELE a b' := by
  obtain rfl : b' = b - 1 := by linarith
  dsimp only [truncLTπGELT, truncGELTIsoTruncGELE, truncLTIsoTruncLE, truncLEπGELE, truncLT]
  simp only [eqToIso_refl, isoWhiskerRight_hom, Iso.refl_hom, whiskerRight_id', id_comp]
  apply comp_id

noncomputable def truncGELTδLT (a b : ℤ) :
    t.truncGELT a b ⟶ t.truncLT a ⋙ shiftFunctor C (1 : ℤ) :=
  t.truncGELEδLT a (b-1)

@[reassoc (attr := simp)]
lemma truncGELTIsoTruncGELE_hom_comp_truncGELEδLT (a b b' : ℤ) (hb' : b' + 1 = b) :
    (t.truncGELTIsoTruncGELE a b' b hb').hom ≫ t.truncGELEδLT a b' =
      t.truncGELTδLT a b := by
  obtain rfl : b' = b - 1 := by linarith
  dsimp only [truncGELTδLT, truncGELTIsoTruncGELE, truncLTIsoTruncLE]
  simp only [eqToIso_refl, isoWhiskerRight_hom, Iso.refl_hom, whiskerRight_id']
  apply id_comp

noncomputable def truncTriangleLTLTGELTFunctor (a b : ℤ) (h : a ≤ b) : C ⥤ Triangle C :=
  Triangle.functorMk (t.natTransTruncLTOfLE a b h) (t.truncLTπGELT a b) (t.truncGELTδLT a b)

lemma truncTriangleLTLTGELTFunctor_comp_π₁ (a b : ℤ) (h : a ≤ b) :
    t.truncTriangleLTLTGELTFunctor a b h ⋙ Triangle.π₁ = t.truncLT a := rfl

@[simps! hom inv]
noncomputable def truncTriangleLTLTGELTFunctorCompπ₁Iso (a b : ℤ) (h : a ≤ b) :
    t.truncTriangleLTLTGELTFunctor a b h ⋙ Triangle.π₁ ≅ t.truncLT a := Iso.refl _

@[simp]
lemma truncTriangleLTLTGELTFunctor_comp_π₂ (a b : ℤ) (h : a ≤ b) :
    t.truncTriangleLTLTGELTFunctor a b h ⋙ Triangle.π₂ = t.truncLT b := rfl

@[simp]
lemma truncTriangleLTLTGELTFunctor_comp_π₃ (a b : ℤ) (h : a ≤ b) :
    t.truncTriangleLTLTGELTFunctor a b h ⋙ Triangle.π₃ = t.truncGELT a b := rfl

@[simp]
lemma truncTriangleLTLTGELTFunctor_π₁Toπ₂ (a b : ℤ) (h : a ≤ b) :
    whiskerLeft (t.truncTriangleLTLTGELTFunctor a b h) Triangle.π₁Toπ₂ =
      t.natTransTruncLTOfLE a b h := rfl

@[simp]
lemma truncTriangleLTLTGELTFunctor_π₂Toπ₃ (a b : ℤ) (h : a ≤ b) :
    whiskerLeft (t.truncTriangleLTLTGELTFunctor a b h) Triangle.π₂Toπ₃ =
      t.truncLTπGELT a b := rfl

@[simp]
lemma truncTriangleLTLTGELTFunctor_π₃Toπ₁ (a b : ℤ) (h : a ≤ b) :
    whiskerLeft (t.truncTriangleLTLTGELTFunctor a b h) Triangle.π₃Toπ₁ =
      t.truncGELTδLT a b := rfl

noncomputable def truncTriangleLTLTGELTFunctorIsoTruncTriangleLTLEGELEFunctor
    (a b : ℤ) (h : a ≤ b) (b' : ℤ) (hb' : b' + 1 = b) :
  t.truncTriangleLTLTGELTFunctor a b h ≅
    t.truncTriangleLTLEGELEFunctor a b'
      ((Int.sub_le_sub_right h 1).trans (by simp only [← hb', add_sub_cancel, le_refl])) := by
  refine' Triangle.functorIsoMk _ _ (t.truncTriangleLTLTGELTFunctorCompπ₁Iso a b h)
    (t.truncLTIsoTruncLE b' b hb') (t.truncGELTIsoTruncGELE a b' b hb') _ _ _
  . dsimp
    simp
  . dsimp
    simp
  . dsimp
    simp only [whiskerRight_id', truncGELTIsoTruncGELE_hom_comp_truncGELEδLT]
    apply comp_id

noncomputable def truncTriangleLTLTGELT_distinguished (a b : ℤ) (h : a ≤ b) (X : C) :
    (t.truncTriangleLTLTGELTFunctor a b h).obj X ∈ distTriang C := by
  refine' isomorphic_distinguished _
    (t.truncTriangleLTLEGELE_distinguished a (b-1) (by linarith) X) _ _
  exact ((evaluation _ _).obj X).mapIso
    (t.truncTriangleLTLTGELTFunctorIsoTruncTriangleLTLEGELEFunctor a b h (b-1) (by linarith))

-/

end TStructure

end Triangulated

end CategoryTheory
