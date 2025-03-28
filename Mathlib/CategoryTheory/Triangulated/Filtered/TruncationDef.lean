/-
Copyright (c) 2021 Luke Kershaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Kershaw, Joël Riou
-/
import Mathlib.CategoryTheory.Triangulated.Filtered.Basic

/-!
# Filtered Triangulated Categories

-/

namespace CategoryTheory

open Category Limits Pretriangulated ZeroObject Preadditive

namespace Triangulated

variable {C : Type _} [Category C] [HasZeroObject C]  [Preadditive C] [HasShift C (ℤ × ℤ)]
  [∀ p : ℤ × ℤ, Functor.Additive (CategoryTheory.shiftFunctor C p)]
  [hC : Pretriangulated C] [hP : FilteredTriangulated C]

namespace FilteredTriangulated

lemma triangle_map_ext' (a b : ℤ) (hab : a < b) {T T' : Triangle C} (f₁ f₂ : T ⟶ T')
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C)
    (h₀ : hP.IsGE T.obj₁ b) (h₁ : hP.IsLE T'.obj₃ a)
    (H : f₁.hom₂ = f₂.hom₂) : f₁ = f₂ := by
  suffices ∀ (f : T ⟶ T') (_ : f.hom₂ = 0), f = (0 : T ⟶ T') by
    rw [← sub_eq_zero]
    apply this
    dsimp
    rw [H, sub_self]
  intro f hf
  ext
  · obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _ hT') f.hom₁ (by
      have eq := f.comm₁
      dsimp at eq ⊢
      rw [← eq, hf, comp_zero])
    have hg' : g = 0 := hP.zero_of_isGE_of_isLE g a b hab h₀
      (hP.shift_isLE_of_isLE T'.obj₃ a (-1))
    simp [hg, hg']
  · simp [hf]
  · obtain ⟨g, hg⟩ := T.yoneda_exact₃ hT f.hom₃ (by rw [f.comm₂, hf, zero_comp])
    have hg' : g = 0 := hP.zero_of_isGE_of_isLE g a b hab
      (hP.shift_isGE_of_isGE T.obj₁ b 1) h₁
    simp [hg, hg']

lemma triangle_map_exists (n₀ n₁ : ℤ) (h : n₀ < n₁) (T T' : Triangle C)
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C)
    (φ : T.obj₂ ⟶ T'.obj₂)
    (h₀ : hP.IsGE T.obj₁ n₁)
    (h₁ : hP.IsLE T'.obj₃ n₀) :
    ∃ (f : T ⟶ T'), f.hom₂ = φ := by
  obtain ⟨a, comm₁⟩ := T'.coyoneda_exact₂ hT' (T.mor₁ ≫ φ) (hP.zero _ n₀ n₁ h)
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
    (h₀ : hP.IsGE T.obj₁ n₁) (h₁ : hP.IsLE T.obj₃ n₀)
    (h₀' : hP.IsGE T'.obj₁ n₁) (h₁' : hP.IsLE T'.obj₃ n₀) :
    ∃ (e' : T ≅ T'), e'.hom.hom₂ = e.hom := by
  obtain ⟨hom, hhom⟩ := triangle_map_exists _ _ h _ _ hT hT' e.hom h₀ h₁'
  obtain ⟨inv, hinv⟩ := triangle_map_exists _ _ h _ _ hT' hT e.inv h₀' h₁
  refine ⟨
    { hom := hom
      inv := inv
      hom_inv_id := triangle_map_ext' n₀ n₁ (by linarith) _ _ hT hT h₀ h₁
        (by simp only [comp_hom₂, id_hom₂, hhom, hinv, e.hom_inv_id])
      inv_hom_id := triangle_map_ext' n₀ n₁ (by linarith) _ _ hT' hT' h₀' h₁'
        (by simp only [comp_hom₂, id_hom₂, hhom, hinv, e.inv_hom_id]) }, hhom⟩

namespace TruncAux

variable (n : ℤ) (A : C)

noncomputable def triangle : Triangle C :=
  Triangle.mk
    (hP.exists_triangle A (n-1) n
      (by linarith)).choose_spec.choose_spec.choose_spec.choose_spec.choose
    (hP.exists_triangle A (n-1) n
      (by linarith)).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
    (hP.exists_triangle A (n-1) n
      (by linarith)).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose

lemma triangle_distinguished :
    triangle n A ∈ distTriang C :=
  (hP.exists_triangle A (n-1) n (by linarith)
    ).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec

instance triangle_obj₁_isGE (n : ℤ) :
    hP.IsGE (triangle n A).obj₁ n := by
  exact ⟨(hP.exists_triangle A (n-1) n (by linarith)).choose_spec.choose_spec.choose⟩

@[simp]
lemma triangle_obj₂ :
    (triangle n A).obj₂ = A := by rfl

instance triangle_obj₃_isLE :
    hP.IsLE (triangle n A).obj₃ (n-1) :=
  ⟨(hP.exists_triangle A (n-1) n (by linarith)).choose_spec.choose_spec.choose_spec.choose⟩

variable {A}
variable {B : C} (φ : A ⟶ B)

lemma triangle_map_ext (f₁ f₂ : triangle n A ⟶ triangle n B)
    (H : f₁.hom₂ = f₂.hom₂) : f₁ = f₂ :=
  triangle_map_ext' (n-1) n (by linarith) _ _
    (triangle_distinguished n A) (triangle_distinguished n B)
    inferInstance inferInstance H

noncomputable def triangleMap : triangle n A ⟶ triangle n B :=
  have H := triangle_map_exists (n-1) n (by linarith) _ _ (triangle_distinguished n A)
    (triangle_distinguished n B) φ inferInstance inferInstance
  { hom₁ := H.choose.hom₁
    hom₂ := φ
    hom₃ := H.choose.hom₃
    comm₁ := by rw [← H.choose.comm₁, H.choose_spec]
    comm₂ := by rw [H.choose.comm₂, H.choose_spec]
    comm₃ := H.choose.comm₃ }

noncomputable def triangleFunctor : C ⥤ Triangle C where
  obj := triangle n
  map φ := triangleMap n φ
  map_id _ := triangle_map_ext n _ _ rfl
  map_comp _ _ := triangle_map_ext n _ _ rfl

variable (A)

lemma triangleFunctor_obj_distinguished :
  (triangleFunctor n).obj A ∈ distTriang C :=
    triangle_distinguished n A

@[simp]
lemma triangleFunctor_obj_obj₂ : ((triangleFunctor n).obj A).obj₂ = A := rfl

@[simp]
lemma triangleFunctor_map_hom₂ : ((triangleFunctor n).map φ).hom₂ = φ := rfl

instance isGE_triangleFunctor_obj_obj₁ :
    hP.IsGE ((triangleFunctor n).obj A).obj₁ n := by
  dsimp [triangleFunctor]
  infer_instance

instance isLE_triangleFunctor_obj_obj₃ :
    hP.IsLE ((triangleFunctor n).obj A).obj₃ (n-1) := by
  dsimp [triangleFunctor]
  infer_instance

noncomputable def triangleMapOfGE (a b : ℤ) (h : b ≤ a) : triangle a A ⟶ triangle b A :=
  have H := triangle_map_exists (b-1) a (by linarith) _ _ (triangle_distinguished a A)
    (triangle_distinguished b A) (𝟙 _) inferInstance inferInstance
  { hom₁ := H.choose.hom₁
    hom₂ := 𝟙 _
    hom₃ := H.choose.hom₃
    comm₁ := by rw [← H.choose.comm₁, H.choose_spec]
    comm₂ := by rw [H.choose.comm₂, H.choose_spec]
    comm₃ := H.choose.comm₃ }

noncomputable def triangleFunctorNatTransOfGE (a b : ℤ) (h : b ≤ a) :
    triangleFunctor a ⟶ triangleFunctor (hP := hP) b where
  app X := triangleMapOfGE X a b h
  naturality {X₁ X₂} φ := by
    refine triangle_map_ext' (b-1) a (by linarith) _ _
      (triangleFunctor_obj_distinguished a X₁) (triangleFunctor_obj_distinguished b X₂)
      inferInstance inferInstance ?_
    dsimp [triangleMapOfGE]
    rw [id_comp, comp_id]

@[simp]
lemma triangleFunctorNatTransOfGE_app_hom₂ (a b : ℤ) (h : b ≤ a) (X : C) :
    ((triangleFunctorNatTransOfGE a b h).app X).hom₂ = 𝟙 X := rfl

lemma triangleFunctorNatTransOfGE_trans (a b c : ℤ) (hab : b ≤ a) (hbc : c ≤ b) :
    triangleFunctorNatTransOfGE a b hab ≫ triangleFunctorNatTransOfGE b c hbc =
      triangleFunctorNatTransOfGE a c (hbc.trans hab) (hP := hP) := by
  apply NatTrans.ext
  ext1 X
  exact triangle_map_ext' (c-1) a (by linarith) _ _
    (triangleFunctor_obj_distinguished a X) (triangleFunctor_obj_distinguished c X)
    inferInstance inferInstance (by aesop_cat)

lemma triangleFunctorNatTransOfGE_refl (a : ℤ) :
    triangleFunctorNatTransOfGE (hP := hP) a a (by rfl) = 𝟙 _ := by
  apply NatTrans.ext
  ext1 X
  exact triangle_map_ext' (a-1) a (by linarith) _ _
    (triangleFunctor_obj_distinguished a X) (triangleFunctor_obj_distinguished a X)
    inferInstance inferInstance (by aesop_cat)

instance : (triangleFunctor (hP := hP) n).Additive where
  map_add := triangle_map_ext n  _ _ rfl

end TruncAux

noncomputable def truncLT (n : ℤ) : C ⥤ C :=
  TruncAux.triangleFunctor n ⋙ Triangle.π₃

instance (n : ℤ) : (truncLT (hP := hP) n).Additive where
  map_add {_ _ f g} := by
    dsimp only [truncLT, Functor.comp_map]
    rw [Functor.map_add]
    rfl

noncomputable def truncLTπ (n : ℤ) : 𝟭 _ ⟶ truncLT (hP := hP) n:=
  whiskerLeft (TruncAux.triangleFunctor n) Triangle.π₂Toπ₃

lemma truncLTπ_app (n : ℤ) (X : C) :
    (truncLTπ n).app X = ((TruncAux.triangleFunctor n).obj X).mor₂ := by
  dsimp [truncLTπ]

noncomputable def truncGE (n : ℤ) : C ⥤ C :=
  TruncAux.triangleFunctor n ⋙ Triangle.π₁

instance (n : ℤ) : (truncGE (hP := hP) n).Additive where
  map_add {_ _ f g} := by
    dsimp only [truncGE, Functor.comp_map]
    rw [Functor.map_add]
    rfl

noncomputable def truncGEι (n : ℤ) : truncGE (hP := hP) n ⟶ 𝟭 _ :=
  whiskerLeft (TruncAux.triangleFunctor n) Triangle.π₁Toπ₂

instance (X : C) (n : ℤ) : hP.IsLE ((truncLT n).obj X) (n-1) := by
  dsimp [truncLT]
  infer_instance

instance (X : C) (n : ℤ) : hP.IsGE ((truncGE n).obj X) n := by
  dsimp [truncGE]
  infer_instance

noncomputable def truncLTδGE (n : ℤ) :
  truncLT n ⟶ truncGE n ⋙ shiftFunctor C (1 : ℤ) :=
    whiskerLeft (TruncAux.triangleFunctor n) Triangle.π₃Toπ₁

@[simps!]
noncomputable def triangleGELT (n : ℤ) : C ⥤ Triangle C :=
  Triangle.functorMk (truncGEι n) (truncLTπ n) (truncLTδGE n)

lemma triangleGELT_distinguished (n : ℤ) (X : C) :
    (triangleGELT n).obj X ∈ distTriang C :=
  TruncAux.triangleFunctor_obj_distinguished n X

noncomputable def truncLT_iso_triangleGELT_comp_π₃ (n : ℤ) :
  triangleGELT n ⋙ Triangle.π₃ ≅ truncLT (C := C) n := by
  refine NatIso.ofComponents (fun A ↦ Iso.refl _) ?_
  intro A B f
  simp only [Functor.comp_obj, Triangle.π₃_obj, triangleGELT_obj_obj₃, Iso.refl_hom, comp_id,
    Functor.comp_map, Triangle.π₃_map, triangleGELT_map_hom₃, id_comp]

noncomputable def truncGE_iso_triangleGELT_comp_π₁ (n : ℤ) :
  triangleGELT n ⋙ Triangle.π₁ ≅ truncGE (C := C) n := by
  refine NatIso.ofComponents (fun A ↦ Iso.refl _) ?_
  intro A B f
  simp only [Functor.comp_obj, Triangle.π₁_obj, triangleGELT_obj_obj₁, Functor.comp_map,
    Triangle.π₁_map, triangleGELT_map_hom₁, Iso.refl_hom, comp_id, id_comp]

@[reassoc (attr := simp)]
lemma truncGEι_comp_truncLTπ_app (n : ℤ) (X : C) :
    (truncGEι n).app X ≫ (truncLTπ n).app X = 0 :=
  comp_distTriang_mor_zero₁₂ _ ((triangleGELT_distinguished n X))

@[reassoc (attr := simp)]
lemma truncLTπ_comp_truncLTδGE_app (n : ℤ) (X : C) :
    (truncLTπ n).app X ≫ (truncLTδGE n).app X = 0 :=
  comp_distTriang_mor_zero₂₃ _ ((triangleGELT_distinguished n X))

@[reassoc (attr := simp)]
lemma truncLTδGE_comp_truncGEι_app (n : ℤ) (X : C) :
    (truncLTδGE n).app X ≫ ((truncGEι n).app X)⟦(1 : ℤ)⟧' = 0 :=
  comp_distTriang_mor_zero₃₁ _ ((triangleGELT_distinguished n X))

@[reassoc (attr := simp)]
lemma truncGEι_comp_truncLTπ (n : ℤ) :
    truncGEι (hP := hP) n ≫ truncLTπ n = 0 := by aesop_cat

@[reassoc (attr := simp)]
lemma truncLTπ_comp_truncLTδGE (n : ℤ) :
    truncLTπ (hP := hP) n ≫ truncLTδGE n = 0 := by aesop_cat

@[reassoc (attr := simp)]
lemma truncLTδGE_comp_truncGEι (n : ℤ) :
    truncLTδGE n ≫ whiskerRight (truncGEι n) (shiftFunctor C (1 : ℤ)) = 0 := by aesop_cat

noncomputable def natTransTruncLTOfGE (a b : ℤ) (h : b ≤ a) :
    truncLT a ⟶ truncLT (hP := hP) b :=
  whiskerRight (TruncAux.triangleFunctorNatTransOfGE a b h) Triangle.π₃

noncomputable def natTransTruncGEOfGE (a b : ℤ) (h : b ≤ a) :
    truncGE a ⟶ truncGE (hP := hP) b :=
  whiskerRight (TruncAux.triangleFunctorNatTransOfGE a b h) Triangle.π₁

@[reassoc (attr := simp)]
lemma natTransTruncLTOfGE_π_app (a b : ℤ) (h : b ≤ a) (X : C):
    (truncLTπ a).app X ≫ (natTransTruncLTOfGE a b h).app X = (truncLTπ b).app X := by
  simpa only [TruncAux.triangleFunctorNatTransOfGE_app_hom₂,
    TruncAux.triangleFunctor_obj_obj₂, id_comp]
    using ((TruncAux.triangleFunctorNatTransOfGE a b h).app X).comm₂

@[reassoc (attr := simp)]
lemma natTransTruncLTOfGE_π (a b : ℤ) (h : b ≤ a) :
    truncLTπ a  ≫ natTransTruncLTOfGE a b h = truncLTπ (hP := hP) b := by aesop_cat

@[reassoc (attr := simp)]
lemma ι_natTransTruncGEOfGE_app (a b : ℤ) (h : b ≤ a) (X : C) :
    (natTransTruncGEOfGE a b h).app X ≫ (truncGEι b).app X = (truncGEι a).app X := by
  simpa only [TruncAux.triangleFunctorNatTransOfGE_app_hom₂,
    TruncAux.triangleFunctor_obj_obj₂, comp_id]
    using ((TruncAux.triangleFunctorNatTransOfGE a b h).app X).comm₁.symm

@[reassoc (attr := simp)]
lemma ι_natTransTruncGEOfGE (a b : ℤ) (h : b ≤ a) :
    natTransTruncGEOfGE (hP := hP) a b h ≫ truncGEι b = truncGEι a := by aesop_cat

@[reassoc]
lemma truncLTδGE_comp_natTransTruncGEOfGE_app (a b : ℤ) (h : b ≤ a) (X : C) :
  (truncLTδGE a).app X ≫ ((natTransTruncGEOfGE a b h).app X)⟦(1 :ℤ)⟧' =
    (natTransTruncLTOfGE a b h).app X ≫ (truncLTδGE b).app X :=
  ((TruncAux.triangleFunctorNatTransOfGE a b h).app X).comm₃

@[reassoc]
lemma truncLTδGE_comp_whiskerRight_natTransTruncGEOfGE (a b : ℤ) (h : b ≤ a) :
  truncLTδGE a ≫ whiskerRight (natTransTruncGEOfGE a b h) (shiftFunctor C (1 : ℤ)) =
    natTransTruncLTOfGE a b h ≫ truncLTδGE b := by
  ext X
  exact truncLTδGE_comp_natTransTruncGEOfGE_app a b h X

noncomputable def natTransTriangleGELTOfGE (a b : ℤ) (h : b ≤ a) :
    triangleGELT a ⟶ triangleGELT b (hP := hP) := by
  refine Triangle.functorHomMk' (natTransTruncGEOfGE a b h) (𝟙 _)
    ((natTransTruncLTOfGE a b h)) ?_ ?_ ?_
  · dsimp
    simp
  · dsimp
    simp
  · exact truncLTδGE_comp_whiskerRight_natTransTruncGEOfGE a b h

@[simp]
lemma natTransTriangleGELTOfGE_refl (a : ℤ) :
    natTransTriangleGELTOfGE (hP := hP) a a (by rfl) = 𝟙 _ :=
  TruncAux.triangleFunctorNatTransOfGE_refl a

set_option maxHeartbeats 400000 in
lemma natTransTriangleGELTOfGE_trans (a b c : ℤ) (hab : b ≤ a) (hbc : c ≤ b):
    natTransTriangleGELTOfGE a b hab ≫ natTransTriangleGELTOfGE b c hbc =
      natTransTriangleGELTOfGE (hP := hP) a c (hbc.trans hab) :=
  TruncAux.triangleFunctorNatTransOfGE_trans a b c hab hbc

@[simp]
lemma natTransTruncLTOfGE_refl (a : ℤ) :
    natTransTruncLTOfGE (hP := hP) a a (by rfl) = 𝟙 _ :=
  congr_arg (fun x => whiskerRight x (Triangle.π₃)) (natTransTriangleGELTOfGE_refl a)

set_option maxHeartbeats 400000 in
@[simp]
lemma natTransTruncLTOfGE_trans (a b c : ℤ) (hab : b ≤ a) (hbc : c ≤ b) :
    natTransTruncLTOfGE a b hab ≫ natTransTruncLTOfGE b c hbc =
      natTransTruncLTOfGE (hP := hP) a c (hbc.trans hab) :=
  congr_arg (fun x => whiskerRight x Triangle.π₃)
    (natTransTriangleGELTOfGE_trans a b c hab hbc)

lemma natTransTruncLTOfGE_refl_app (a : ℤ) (X : C) :
    (natTransTruncLTOfGE a a (by rfl)).app X = 𝟙 _ :=
  congr_app (natTransTruncLTOfGE_refl a) X

lemma natTransTruncLTOfGE_trans_app (a b c : ℤ) (hab : b ≤ a) (hbc : c ≤ b) (X : C) :
    (natTransTruncLTOfGE a b hab).app X ≫ (natTransTruncLTOfGE b c hbc).app X =
      (natTransTruncLTOfGE a c (hbc.trans hab)).app X :=
  congr_app (natTransTruncLTOfGE_trans a b c hab hbc) X

@[simp]
lemma natTransTruncGEOfGE_refl (a : ℤ) :
    natTransTruncGEOfGE (hP := hP) a a (by rfl) = 𝟙 _ :=
  congr_arg (fun x => whiskerRight x (Triangle.π₁)) (natTransTriangleGELTOfGE_refl a)

set_option maxHeartbeats 400000 in
@[simp]
lemma natTransTruncGEOfGE_trans (a b c : ℤ) (hab : b ≤ a) (hbc : c ≤ b) :
    natTransTruncGEOfGE a b hab ≫ natTransTruncGEOfGE b c hbc =
      natTransTruncGEOfGE (hP := hP) a c (hbc.trans hab) :=
  congr_arg (fun x => whiskerRight x Triangle.π₁)
    (natTransTriangleGELTOfGE_trans a b c hab hbc)

lemma natTransTruncGEOfGE_refl_app (a : ℤ) (X : C) :
    (natTransTruncGEOfGE a a (by rfl)).app X = 𝟙 _ :=
  congr_app (natTransTruncGEOfGE_refl a) X

lemma natTransTruncGEOfGE_trans_app (a b c : ℤ) (hab : b ≤ a) (hbc : c ≤ b) (X : C) :
    (natTransTruncGEOfGE a b hab).app X ≫ (natTransTruncGEOfGE b c hbc).app X =
      (natTransTruncGEOfGE a c (hbc.trans hab)).app X :=
  congr_app (natTransTruncGEOfGE_trans a b c hab hbc) X

attribute [irreducible] truncLT truncGE truncLTπ truncGEι truncLTδGE
  natTransTruncLTOfGE natTransTruncGEOfGE

noncomputable def truncLE (n : ℤ) : C ⥤ C := truncLT (n+1)

instance (n : ℤ) : (truncLE (hP := hP) n).Additive := by
  dsimp only [truncLE]
  infer_instance

instance (n : ℤ) (X : C) : hP.IsLE ((truncLE n).obj X) n := by
  have : hP.IsLE ((truncLE n).obj X) (n+1-1) := by
    dsimp [truncLE]
    infer_instance
  exact hP.isLE_of_LE _ (n+1-1) n (by linarith)

noncomputable def truncGT (n : ℤ) : C ⥤ C := truncGE (n+1)

instance (n : ℤ) : (truncGT (hP := hP) n).Additive := by
  dsimp only [truncGT]
  infer_instance

instance (n : ℤ) (X : C) : hP.IsGE ((truncGT n).obj X) (n+1) := by
  dsimp [truncGT]
  infer_instance

instance (n : ℤ) (X : C) : hP.IsGE ((truncGT (n-1)).obj X) n :=
  hP.isGE_of_GE _ n (n-1+1) (by linarith)

noncomputable def truncLEIsoTruncLT (a b : ℤ) (h : a + 1 = b) : hP.truncLE a ≅ truncLT b :=
  eqToIso (congr_arg truncLT h)

noncomputable def truncGTIsoTruncGE (a b : ℤ) (h : a + 1 = b) : hP.truncGT a ≅ truncGE b :=
  eqToIso (congr_arg truncGE h)

noncomputable def truncLEπ (n : ℤ) : 𝟭 C ⟶ truncLE n:= truncLTπ (n + 1)

lemma truncLEπ_app (n : ℤ) (X : C) :
    (truncLEπ n).app X = (truncLTπ (n + 1)).app X := by
  dsimp [truncLEπ]

@[reassoc (attr := simp)]
lemma π_truncLEIsoTruncLT_hom (a b : ℤ) (h : a + 1 = b) :
    truncLEπ a ≫ (hP.truncLEIsoTruncLT a b h).hom = truncLTπ b := by
  subst h
  dsimp [truncLEIsoTruncLT, truncLEπ]
  rw [comp_id]

@[reassoc (attr := simp)]
lemma π_truncLEIsoTruncLT_hom_app (a b : ℤ) (h : a + 1 = b) (X : C) :
    (truncLEπ a).app X ≫ (truncLEIsoTruncLT a b h).hom.app X = (truncLTπ b).app X :=
  congr_app (π_truncLEIsoTruncLT_hom a b h) X

@[reassoc (attr := simp)]
lemma π_truncLEIsoTruncLT_inv (a b : ℤ) (h : a + 1 = b) :
    truncLTπ b ≫ (hP.truncLEIsoTruncLT a b h).inv = truncLEπ a := by
  subst h
  dsimp [truncLEIsoTruncLT, truncLEπ, truncLE]
  rw [comp_id]

@[reassoc (attr := simp)]
lemma π_truncLEIsoTruncLT_inv_app (a b : ℤ) (h : a + 1 = b) (X : C) :
    (truncLTπ b).app X ≫ (truncLEIsoTruncLT a b h).inv.app X = (truncLEπ a).app X :=
  congr_app (π_truncLEIsoTruncLT_inv a b h) X

noncomputable def truncGTι (n : ℤ) : truncGT n ⟶ 𝟭 C := truncGEι (n + 1)

@[reassoc (attr := simp)]
lemma truncGTIsoTruncGE_hom_ι (a b : ℤ) (h : a + 1 = b) :
    (hP.truncGTIsoTruncGE a b h).hom ≫ truncGEι b = truncGTι a := by
  subst h
  dsimp [truncGTIsoTruncGE, truncGTι]
  rw [id_comp]

@[reassoc (attr := simp)]
lemma truncGTIsoTruncGE_hom_ι_app (a b : ℤ) (h : a + 1 = b) (X : C) :
    (truncGTIsoTruncGE a b h).hom.app X ≫ (truncGEι b).app X = (truncGTι a).app X :=
  congr_app (truncGTIsoTruncGE_hom_ι a b h) X

@[reassoc (attr := simp)]
lemma truncGTIsoTruncGE_inv_ι (a b : ℤ) (h : a + 1 = b) :
    (hP.truncGTIsoTruncGE a b h).inv ≫ truncGTι a = truncGEι b := by
  subst h
  dsimp [truncGTIsoTruncGE, truncGTι, truncGT]
  rw [id_comp]

@[reassoc (attr := simp)]
lemma truncGTIsoTruncGE_inv_ι_app (a b : ℤ) (h : a + 1 = b) (X : C) :
    (truncGTIsoTruncGE a b h).inv.app X ≫ (truncGTι a).app X = (truncGEι b).app X :=
  congr_app (truncGTIsoTruncGE_inv_ι a b h) X

noncomputable def truncLEδGE (a b : ℤ) (h : a + 1 = b) :
    truncLE a ⟶ truncGE b ⋙ shiftFunctor C (1 : ℤ) :=
  (truncLEIsoTruncLT a b h).hom ≫ truncLTδGE b

@[simps!]
noncomputable def triangleGELE (a b : ℤ) (h : a + 1 = b) : C ⥤ Triangle C :=
  Triangle.functorMk (truncGEι b) (truncLEπ a) (truncLEδGE a b h)

noncomputable def triangleGELEIsoTriangleGELT (a b : ℤ) (h : a + 1 = b) :
    hP.triangleGELE a b h ≅ triangleGELT b := by
  refine Triangle.functorIsoMk _ _ (Iso.refl _) (Iso.refl _) (truncLEIsoTruncLT a b h) ?_ ?_ ?_
  · aesop_cat
  · aesop_cat
  · ext
    dsimp [truncLEδGE]
    simp only [assoc, id_comp, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id, comp_id]

lemma triangleGELE_distinguished (a b : ℤ) (h : a + 1 = b) (X : C) :
    (triangleGELE a b h).obj X ∈ distTriang C :=
  isomorphic_distinguished _ (triangleGELT_distinguished b X) _
    ((triangleGELEIsoTriangleGELT a b h).app X)

noncomputable def truncLEδGT (n : ℤ) :
    truncLE n ⟶ truncGT n ⋙ shiftFunctor C (1 : ℤ) :=
  truncLEδGE n (n+1) (by linarith) ≫ whiskerRight (truncGTIsoTruncGE n (n+1) rfl).inv
  (shiftFunctor C 1)

@[simps!]
noncomputable def triangleGTLE (n : ℤ) : C ⥤ Triangle C :=
  Triangle.functorMk (truncGTι n) (truncLEπ n) (truncLEδGT n)

noncomputable def triangleGTLEIsoTriangleGELE (a b : ℤ) (h : a + 1 = b) :
    hP.triangleGTLE a ≅ triangleGELE a b h := by
  refine Triangle.functorIsoMk _ _ (truncGTIsoTruncGE a b h) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · aesop_cat
  · aesop_cat
  · ext
    dsimp [truncLEδGT]
    subst h
    simp only [assoc, id_comp, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id, comp_id]

lemma triangleGTLE_distinguished (n : ℤ) (X : C) :
    (triangleGTLE n).obj X ∈ distTriang C :=
  isomorphic_distinguished _ (triangleGELE_distinguished n (n+1) rfl X) _
    ((triangleGTLEIsoTriangleGELE n (n+1) rfl).app X)


section CommShift

variable (n : ℤ) (A : C)

noncomputable def triangleGELTIsoShift_exists (a : ℤ) :=
  triangle_iso_exists (n - 1) n (by linarith) _ _
      (triangleGELT_distinguished n (A⟦a⟧))
      (Triangle.shift_distinguished _ (triangleGELT_distinguished n A) a) (Iso.refl _)
      (by dsimp; infer_instance) (by dsimp; infer_instance)
      (by dsimp; exact shift_isGE_of_isGE _ n a)
      (by dsimp; exact shift_isLE_of_isLE _ (n - 1) a)

noncomputable def triangleGELTCommShiftIso (a : ℤ) :
    shiftFunctor C a ⋙ triangleGELT n ≅ triangleGELT n ⋙ shiftFunctor (Triangle C) a := by
  refine NatIso.ofComponents (fun A ↦ a.negOnePow • Classical.choose
    (triangleGELTIsoShift_exists n A a)) ?_
  intro A B f
  refine triangle_map_ext' (n - 1) n (by linarith) _ _ ?_ ?_ ?_ ?_ ?_
  · simp only [Functor.comp_obj]
    exact triangleGELT_distinguished _ _
  · simp only [Functor.comp_obj]
    exact Triangle.shift_distinguished _ (triangleGELT_distinguished _ _) _
  · simp only [Functor.comp_obj]
    dsimp; infer_instance
  · simp only [Triangle.shiftFunctor_eq, Functor.comp_obj, Triangle.shiftFunctor_obj,
    triangleGELT_obj_obj₁, triangleGELT_obj_obj₂, triangleGELT_obj_obj₃, triangleGELT_obj_mor₁,
    triangleGELT_obj_mor₂, triangleGELT_obj_mor₃, Triangle.mk_obj₃]
    exact shift_isLE_of_isLE _ (n - 1) a
  · dsimp
    erw [zsmul_comp, comp_zsmul]
    rw [Classical.choose_spec (triangleGELTIsoShift_exists n A a),
      Classical.choose_spec (triangleGELTIsoShift_exists n B a), Iso.refl_hom, Iso.refl_hom]
    erw [comp_id, id_comp]

lemma triangleGELTCommShiftIso_zero :
    triangleGELTCommShiftIso (C := C) n 0 = Functor.CommShift.isoZero (triangleGELT n) ℤ := by
  apply Iso.ext; apply NatTrans.ext; ext1 A
  refine triangle_map_ext' (n - 1) n (by linarith) _ _ ?_ ?_ ?_ ?_ ?_
  · exact triangleGELT_distinguished _ _
  · exact Triangle.shift_distinguished _ (triangleGELT_distinguished _ _) _
  · dsimp; infer_instance
  · dsimp; infer_instance
  · dsimp; simp only [triangleGELTCommShiftIso, Triangle.shiftFunctor_eq,
    Triangle.shiftFunctor_obj, triangleGELT_obj_obj₁, triangleGELT_obj_obj₂, triangleGELT_obj_obj₃,
    Int.negOnePow_zero, triangleGELT_obj_mor₁, triangleGELT_obj_mor₂, Functor.comp_obj,
    triangleGELT_obj_mor₃, Triangle.mk_obj₂, Iso.refl_hom, NatIso.ofComponents_hom_app,
    smul_iso_hom, one_smul, Functor.CommShift.isoZero_hom_app, Triangle.shiftFunctorZero_eq,
    triangleCategory_comp, TriangleMorphism.comp_hom₂, triangleGELT_map_hom₂,
    Triangle.shiftFunctorZero_inv_app_hom₂, Iso.hom_inv_id_app]
    rw [Classical.choose_spec (triangleGELTIsoShift_exists n A 0), Iso.refl_hom]; rfl

lemma triangleGELTCommShiftIso_add (a b : ℤ) :
    triangleGELTCommShiftIso (C := C) n (a + b) = Functor.CommShift.isoAdd
    (triangleGELTCommShiftIso n a) (triangleGELTCommShiftIso n b) := by
  apply Iso.ext; apply NatTrans.ext; ext1 A
  refine triangle_map_ext' (n - 1) n (by linarith) _ _ ?_ ?_ ?_ ?_ ?_
  · exact triangleGELT_distinguished _ _
  · simp only [Functor.comp_obj]
    exact Triangle.shift_distinguished _ (triangleGELT_distinguished _ _) _
  · dsimp; infer_instance
  · simp only [Triangle.shiftFunctor_eq, Functor.comp_obj, Triangle.shiftFunctor_obj,
    triangleGELT_obj_obj₁, triangleGELT_obj_obj₂, triangleGELT_obj_obj₃, triangleGELT_obj_mor₁,
    triangleGELT_obj_mor₂, triangleGELT_obj_mor₃, Triangle.mk_obj₃]
    exact shift_isLE_of_isLE _ (n - 1) _
  · simp only [NatIso.ofComponents_hom_app, Functor.CommShift.isoAdd_hom_app,
      triangleGELTCommShiftIso]
    rw [TriangleMorphism.smul_iso_hom, TriangleMorphism.smul_hom₂,
      Classical.choose_spec (triangleGELTIsoShift_exists n A (a + b)), Iso.refl_hom]
    simp only [comp_hom₂]
    rw [TriangleMorphism.smul_iso_hom, TriangleMorphism.smul_hom₂,
      Classical.choose_spec (triangleGELTIsoShift_exists n _ b), Iso.refl_hom, Linear.smul_comp,
      Linear.comp_smul]
    erw [id_comp, Triangle.shiftFunctor_map_hom₂]
    rw [TriangleMorphism.smul_iso_hom, TriangleMorphism.smul_hom₂,
      Classical.choose_spec (triangleGELTIsoShift_exists n A a), Iso.refl_hom,
      Functor.map_zsmul, zsmul_comp, comp_zsmul, Functor.map_id]
    erw [id_comp]
    dsimp
    rw [shiftFunctorAdd'_eq_shiftFunctorAdd, Iso.hom_inv_id_app, Int.negOnePow_add, Units.val_mul,
      smul_smul, mul_comm]


noncomputable instance : (triangleGELT (hP := hP) n).CommShift ℤ where
  iso := triangleGELTCommShiftIso n
  zero := triangleGELTCommShiftIso_zero n
  add := triangleGELTCommShiftIso_add n

lemma triangleGELT_commShiftIso_hom_eq (n a : ℤ) (X : C) :
    ((triangleGELT (hP := hP) n).commShiftIso a).hom.app X =
    a.negOnePow.1 • (triangleGELTIsoShift_exists n X a).choose.hom := rfl

noncomputable instance (n : ℤ) : (truncLT (hP := hP) n).CommShift ℤ :=
    Functor.CommShift.ofIso (truncLT_iso_triangleGELT_comp_π₃ n) ℤ

lemma truncLT_commShiftIso_hom_app (n a : ℤ) (X : C) :
    ((hP.truncLT n).commShiftIso a).hom.app X = a.negOnePow.1 •
    (triangleGELTIsoShift_exists n X a).choose.hom.hom₃ := by
  have := @NatTrans.shift_app_comm _ _ _ _ _ _ _ _ _ _ _ _ _
    (Functor.CommShift.ofIso_compatibility (truncLT_iso_triangleGELT_comp_π₃ n (C := C)) ℤ) a X
  simp only [Functor.comp_obj, Triangle.π₃_obj, triangleGELT_obj_obj₃,
    truncLT_iso_triangleGELT_comp_π₃, NatTrans.comp_app, whiskerRight_app,
    NatIso.ofComponents_hom_app, Iso.refl_hom, Functor.map_id, comp_id, whiskerLeft_app, id_comp]
    at this
  rw [← this, Functor.commShiftIso_comp_hom_app (triangleGELT n) Triangle.π₃ a X]
  rw [triangleGELT_commShiftIso_hom_eq, Triangle_π₃_commShiftIso_hom]
  erw [comp_id]
  simp only [Functor.comp_obj, Triangle.shiftFunctor_eq, Triangle.shiftFunctor_obj,
    triangleGELT_obj_obj₁, triangleGELT_obj_obj₂, triangleGELT_obj_obj₃, triangleGELT_obj_mor₁,
    triangleGELT_obj_mor₂, triangleGELT_obj_mor₃, Triangle.mk_obj₂, Iso.refl_hom, Triangle.π₃_map,
    instSMulHomTriangle_smul_hom₃, Triangle.mk_obj₃]

noncomputable instance (n : ℤ) : (truncGE (hP := hP) n).CommShift ℤ :=
    Functor.CommShift.ofIso (truncGE_iso_triangleGELT_comp_π₁ n) ℤ

lemma truncGE_commShiftIso_hom_app (n a : ℤ) (X : C) :
    ((hP.truncGE n).commShiftIso a).hom.app X = a.negOnePow.1 •
    (triangleGELTIsoShift_exists n X a).choose.hom.hom₁ := by
  have := @NatTrans.shift_app_comm _ _ _ _ _ _ _ _ _ _ _ _ _
    (Functor.CommShift.ofIso_compatibility (truncGE_iso_triangleGELT_comp_π₁ n (C := C)) ℤ) a X
  simp only [Functor.comp_obj, Triangle.π₁_obj, triangleGELT_obj_obj₁,
    truncGE_iso_triangleGELT_comp_π₁, NatTrans.comp_app, whiskerRight_app,
    NatIso.ofComponents_hom_app, Iso.refl_hom, Functor.map_id, comp_id, whiskerLeft_app, id_comp]
    at this
  rw [← this, Functor.commShiftIso_comp_hom_app (triangleGELT n) Triangle.π₁ a X]
  rw [triangleGELT_commShiftIso_hom_eq, Triangle_π₁_commShiftIso_hom]
  erw [comp_id]
  simp only [Functor.comp_obj, Triangle.shiftFunctor_eq, Triangle.shiftFunctor_obj,
    triangleGELT_obj_obj₁, triangleGELT_obj_obj₂, triangleGELT_obj_obj₃, triangleGELT_obj_mor₁,
    triangleGELT_obj_mor₂, triangleGELT_obj_mor₃, Triangle.mk_obj₂, Iso.refl_hom, Triangle.π₁_map,
    instSMulHomTriangle_smul_hom₁, Triangle.mk_obj₁]

noncomputable instance (n : ℤ) : (truncLE (hP := hP) n).CommShift ℤ := by
  dsimp only [truncLE]
  infer_instance

lemma truncLE_commShiftIso_hom_app (n a : ℤ) (X : C) :
    ((hP.truncLE n).commShiftIso a).hom.app X =
    ((hP.truncLT (n + 1)).commShiftIso a).hom.app X := by
  dsimp [truncLE]

noncomputable instance (n : ℤ) : (truncGT (hP := hP) n).CommShift ℤ := by
  dsimp only [truncGT]
  infer_instance

lemma truncGT_commShiftIso_hom_app (n a : ℤ) (X : C) :
    ((hP.truncGT n).commShiftIso a).hom.app X =
    ((hP.truncGE (n + 1)).commShiftIso a).hom.app X := by
  dsimp [truncGT]

lemma truncLTCommShift_comm (X : C) (n a : ℤ) :
    ((hP.truncLTπ n).app X)⟦a⟧' = (truncLTπ n).app (X⟦a⟧) ≫
    ((truncLT n).commShiftIso a).hom.app X := by
  rw [truncLT_commShiftIso_hom_app, comp_zsmul]
  simp only [Functor.id_obj, Functor.comp_obj, Triangle.shiftFunctor_eq, Triangle.shiftFunctor_obj,
    triangleGELT_obj_obj₁, triangleGELT_obj_obj₂, triangleGELT_obj_obj₃, triangleGELT_obj_mor₁,
    triangleGELT_obj_mor₂, triangleGELT_obj_mor₃, Triangle.mk_obj₂, Iso.refl_hom]
  have := (triangleGELTIsoShift_exists n X a).choose.hom.comm₂
  simp only [triangleGELT_obj_obj₂, Triangle.shiftFunctor_eq, Triangle.shiftFunctor_obj,
    triangleGELT_obj_obj₁, triangleGELT_obj_obj₃, triangleGELT_obj_mor₁, triangleGELT_obj_mor₂,
    Functor.comp_obj, triangleGELT_obj_mor₃, Triangle.mk_obj₃, Triangle.mk_obj₂, Iso.refl_hom,
    Triangle.mk_mor₂, Linear.comp_units_smul] at this
  rw [this, (triangleGELTIsoShift_exists n X a).choose_spec, Iso.refl_hom]
  change _ = a.negOnePow.1 • _
  erw [id_comp, smul_smul]; rw [← Units.val_mul, ← Int.negOnePow_sub]
  conv_rhs => congr; congr; rw [sub_self, Int.negOnePow_zero]
  erw [one_smul]

lemma truncLECommShift_comm (X : C) (n a : ℤ) :
    ((hP.truncLEπ n).app X)⟦a⟧' = (truncLEπ n).app (X⟦a⟧) ≫
    ((truncLE n).commShiftIso a).hom.app X := truncLTCommShift_comm _ _ _

lemma truncGECommShift_comm (X : C) (n a : ℤ) :
    ((truncGE n).commShiftIso a).inv.app X ≫ (truncGEι n).app
          ((shiftFunctor C a).obj X) = ((truncGEι n).app X)⟦a⟧' := by
  rw [← cancel_epi (((truncGE n).commShiftIso a).hom.app X)]
  simp only [Functor.comp_obj, Functor.id_obj, Iso.hom_inv_id_app_assoc]
  rw [truncGE_commShiftIso_hom_app, zsmul_comp]
  simp only [Triangle.shiftFunctor_eq, Triangle.shiftFunctor_obj, triangleGELT_obj_obj₁,
    triangleGELT_obj_obj₂, triangleGELT_obj_obj₃, triangleGELT_obj_mor₁, triangleGELT_obj_mor₂,
    Functor.comp_obj, triangleGELT_obj_mor₃, Triangle.mk_obj₂, Iso.refl_hom]
  have := (triangleGELTIsoShift_exists n X a).choose.hom.comm₁
  simp only [triangleGELT_obj_obj₁, Triangle.shiftFunctor_eq, Triangle.shiftFunctor_obj,
    triangleGELT_obj_obj₂, triangleGELT_obj_obj₃, triangleGELT_obj_mor₁, triangleGELT_obj_mor₂,
    Functor.comp_obj, triangleGELT_obj_mor₃, Triangle.mk_obj₂, Iso.refl_hom, Triangle.mk_obj₁,
    Triangle.mk_mor₁, Linear.comp_units_smul] at this
  erw [← this, (triangleGELTIsoShift_exists n X a).choose_spec, Iso.refl_hom]
  erw [comp_id]

lemma truncGTCommShift_comm (X : C) (n a : ℤ) :
    ((hP.truncLEπ n).app X)⟦a⟧' = (truncLEπ n).app (X⟦a⟧) ≫
    ((truncLE n).commShiftIso a).hom.app X := truncLTCommShift_comm _ _ _

end CommShift

lemma to_truncGE_obj_ext (n : ℤ) (X : C) {Y : C}
    (f₁ f₂ : X ⟶ (hP.truncGE n).obj Y) (h : f₁ ≫ (hP.truncGEι n).app Y =
    f₂ ≫ (hP.truncGEι n).app Y) [hP.IsGE X n] :
    f₁ = f₂ := by
  suffices ∀ (f : X ⟶ (hP.truncGE n).obj Y) (_ : f ≫ (hP.truncGEι n).app Y = 0), f = 0 by
    rw [← sub_eq_zero, this (f₁ - f₂) (by rw [sub_comp, sub_eq_zero, h])]
  intro f hf
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _
    (hP.triangleGELT_distinguished n Y)) f hf
  have hg' := zero_of_isGE_of_isLE g (n-1) n (by linarith) inferInstance
    (by simp only [Triangle.invRotate_obj₁, Int.reduceNeg, triangleGELT_obj_obj₃]
        exact shift_isLE_of_isLE _ _ _)
  rw [hg, hg', zero_comp]

lemma to_truncGT_obj_ext (n : ℤ) (X : C) {Y : C}
    (f₁ f₂ : X ⟶ (hP.truncGT n).obj Y) (h : f₁ ≫ (hP.truncGTι n).app Y =
    f₂ ≫ (hP.truncGTι n).app Y) [hP.IsGE X (n+1)] :
    f₁ = f₂ := by
  rw [← cancel_mono ((hP.truncGTIsoTruncGE n (n+1) (by linarith)).hom.app Y)]
  apply to_truncGE_obj_ext
  simpa only [Functor.id_obj, assoc, truncGTIsoTruncGE_hom_ι_app] using h

lemma from_truncLE_obj_ext (n : ℤ) (Y : C) {X : C}
    (f₁ f₂ : (hP.truncLE n).obj X ⟶ Y) (h : (hP.truncLEπ n).app X ≫ f₁ =
    (hP.truncLEπ n).app X ≫ f₂) [hP.IsLE Y n] :
    f₁ = f₂ := by
  suffices ∀ (f : (hP.truncLE n).obj X ⟶ Y) (_ : (hP.truncLEπ n).app X ≫ f = 0), f = 0 by
    rw [← sub_eq_zero, this (f₁ - f₂) (by rw [comp_sub, sub_eq_zero, h])]
  intro f hf
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _ (hP.triangleGTLE_distinguished n X) f hf
  have hg' := hP.zero_of_isGE_of_isLE g n (n+1) (by linarith)
    (by simp only [triangleGTLE_obj_obj₁]; exact shift_isGE_of_isGE _ _ _) inferInstance
  rw [hg, hg', comp_zero]

lemma from_truncLT_obj_ext (n : ℤ) (Y : C) {X : C}
    (f₁ f₂ : (hP.truncLT n).obj X ⟶ Y) (h : (hP.truncLTπ n).app X ≫ f₁ =
    (hP.truncLTπ n).app X ≫ f₂) [hP.IsLE Y (n-1)] :
    f₁ = f₂ := by
  rw [← cancel_epi ((hP.truncLEIsoTruncLT (n-1) n (by linarith)).hom.app X)]
  apply from_truncLE_obj_ext
  simpa only [Functor.id_obj, π_truncLEIsoTruncLT_hom_app_assoc] using h

lemma liftTruncGE' {X Y : C} (f : X ⟶ Y) (n : ℤ) [hP.IsGE X n] :
    ∃ (f' : X ⟶ (hP.truncGE n).obj Y), f = f' ≫ (hP.truncGEι n).app Y :=
  Triangle.coyoneda_exact₂ _ (hP.triangleGELT_distinguished n Y) f
    (hP.zero_of_isGE_of_isLE  _ (n - 1) n (by linarith)
    inferInstance (by dsimp; infer_instance))

noncomputable def liftTruncGE {X Y : C} (f : X ⟶ Y) (n : ℤ) [hP.IsGE X n] :
    X ⟶ (hP.truncGE n).obj Y := (hP.liftTruncGE' f n).choose

@[reassoc (attr := simp)]
lemma liftTruncGE_ι {X Y : C} (f : X ⟶ Y) (n : ℤ) [hP.IsGE X n] :
    hP.liftTruncGE f n ≫ (hP.truncGEι n).app Y = f :=
  (hP.liftTruncGE' f n).choose_spec.symm

noncomputable def liftTruncGT {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (h : n₁ + 1 = n₀) [hP.IsGE X n₀] :
    X ⟶ (hP.truncGT n₁).obj Y :=
  hP.liftTruncGE f n₀ ≫ (hP.truncGTIsoTruncGE _ _ h).inv.app Y

@[reassoc (attr := simp)]
lemma liftTruncGT_ι {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (h : n₁ + 1 = n₀) [hP.IsGE X n₀] :
    hP.liftTruncGT f n₀ n₁ h ≫ (hP.truncGTι n₁).app Y = f := by
  dsimp only [liftTruncGT]
  simp only [Functor.id_obj, assoc, truncGTIsoTruncGE_inv_ι_app, liftTruncGE_ι]

lemma descTruncLE' {X Y : C} (f : X ⟶ Y) (n : ℤ) [hP.IsLE Y n] :
  ∃ (f' : (hP.truncLE n).obj X ⟶ Y), f = (hP.truncLEπ n).app X ≫ f' :=
  Triangle.yoneda_exact₂ _ (hP.triangleGTLE_distinguished n X) f
    (hP.zero_of_isGE_of_isLE _ n (n + 1) (by linarith) (by dsimp; infer_instance) inferInstance)

noncomputable def descTruncLE {X Y : C} (f : X ⟶ Y) (n : ℤ) [hP.IsLE Y n] :
    (hP.truncLE n).obj X ⟶ Y := (hP.descTruncLE' f n).choose

@[reassoc (attr := simp)]
lemma π_descTruncLE {X Y : C} (f : X ⟶ Y) (n : ℤ) [hP.IsLE Y n] :
    (hP.truncLEπ n).app X ≫ hP.descTruncLE f n = f :=
  (hP.descTruncLE' f n).choose_spec.symm

noncomputable def descTruncLT {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) [hP.IsLE Y n₀] :
    (hP.truncLT n₁).obj X ⟶ Y := (hP.truncLEIsoTruncLT _ _ h).inv.app X ≫ hP.descTruncLE f n₀

@[reassoc (attr := simp)]
lemma π_descTruncLT {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) [hP.IsLE Y n₀] :
    (hP.truncLTπ n₁).app X ≫ hP.descTruncLT f n₀ n₁ h  = f := by
  dsimp only [descTruncLT]
  simp only [Functor.id_obj, π_truncLEIsoTruncLT_inv_app_assoc, π_descTruncLE]

variable [IsTriangulated C]

noncomputable instance (n : ℤ) : (hP.truncLT n).IsTriangulated where
  map_distinguished T hT := by
    obtain ⟨Z₁, Z₃, f, g, h, v₁, w₁, u₃, v₃, w₃, hZ, hGT, hLE, comm₁₂, comm₂₃, _, comm₃₁₂, _⟩ :=
      NineGrid' (hP.triangleGELT_distinguished n T.obj₁) (hP.triangleGELT_distinguished n
      T.obj₂) ((hP.truncGE n).map T.mor₁) T.mor₁ (by simp only [triangleGELT_obj_obj₁,
        triangleGELT_obj_obj₂, triangleGELT_obj_mor₁, NatTrans.naturality, Functor.id_obj,
        Functor.id_map]) T.mor₂ T.mor₃ hT
    have ex := triangle_iso_exists (n - 1) n (by linarith) _ _ hZ
      (hP.triangleGELT_distinguished n T.obj₃) (Iso.refl _)
      (by simp only [Triangle.mk_obj₁]
          refine hP.isGE₃ _ hGT ?_ ?_ (n := n)
          simp only [triangleGELT_obj_obj₁, Triangle.mk_obj₁]; infer_instance
          simp only [triangleGELT_obj_obj₁, Triangle.mk_obj₂]; infer_instance)
      (by simp only [Triangle.mk_obj₃]
          refine hP.isLE₃ _ hLE ?_ ?_ (n := n - 1)
          simp only [triangleGELT_obj_obj₃, Triangle.mk_obj₁]; infer_instance
          simp only [triangleGELT_obj_obj₃, Triangle.mk_obj₂]; infer_instance)
      (by simp only [triangleGELT_obj_obj₁]; infer_instance)
      (by simp only [triangleGELT_obj_obj₃]; infer_instance)
    set eZ := ex.choose
    set e : Triangle.mk u₃ v₃ w₃ ≅ (truncLT n).mapTriangle.obj T := by
      refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Triangle.π₃.mapIso eZ) ?_ ?_ ?_
      · simp only [triangleGELT_obj_obj₃, Triangle.mk_obj₁, Functor.mapTriangle_obj,
        Triangle.mk_obj₂, Triangle.mk_mor₁, Iso.refl_hom, comp_id, id_comp]
        have : IsLE ((triangleGELT n).obj T.obj₂).obj₃ (n - 1) := by
          simp only [triangleGELT_obj_obj₃]; infer_instance
        refine from_truncLT_obj_ext n _ _ _ ?_
        simp only [Functor.id_obj, triangleGELT_obj_obj₃]
        have := comm₁₂.2.1
        simp only [triangleGELT_obj_obj₂, triangleGELT_obj_obj₃, triangleGELT_obj_mor₂] at this
        rw [this]
        exact (truncLTπ n).naturality T.mor₁
      · simp only [triangleGELT_obj_obj₃, Triangle.mk_obj₂, Functor.mapTriangle_obj,
        Triangle.mk_obj₃, Triangle.mk_mor₂, Functor.mapIso_hom, Triangle.π₃_map, Iso.refl_hom,
        id_comp]
        refine from_truncLT_obj_ext n _ _ _ ?_
        have := comm₂₃.2.1
        simp only [triangleGELT_obj_obj₂, Triangle.mk_obj₃, triangleGELT_obj_obj₃,
          triangleGELT_obj_mor₂, Triangle.mk_obj₂, Triangle.mk_mor₂] at this
        rw [← assoc, this]
        have := eZ.hom.comm₂
        simp only [Triangle.mk_obj₂, triangleGELT_obj_obj₃, Triangle.mk_obj₃, Triangle.mk_mor₂,
          triangleGELT_obj_obj₂, triangleGELT_obj_mor₂] at this
        rw [assoc, this]
        have := (truncLTπ n).naturality T.mor₂
        simp only [Functor.id_obj, Functor.id_map] at this
        rw [← this, ex.choose_spec]
        simp only [Functor.id_obj, Triangle.mk_obj₂, triangleGTLE_obj_obj₂, Iso.refl_hom, id_comp]
      · simp only [triangleGELT_obj_obj₃, Triangle.mk_obj₃, Functor.mapTriangle_obj,
        Triangle.mk_obj₁, Triangle.mk_mor₃, Iso.refl_hom, Functor.map_id, comp_id,
        Functor.mapIso_hom, Triangle.π₃_map]
        rw [← cancel_epi eZ.inv.hom₃]
        have : IsLE ((((triangleGELT n).obj T.obj₁).obj₃)⟦(1 : ℤ)⟧) (n - 1) := by
          simp only [triangleGELT_obj_obj₃]
          exact shift_isLE_of_isLE _ _ _
        refine from_truncLT_obj_ext n _ _ _ ?_
        have := eZ.inv.comm₂
        simp only [triangleGELT_obj_obj₂, Triangle.mk_obj₃, triangleGELT_obj_obj₃,
          triangleGELT_obj_mor₂, Triangle.mk_obj₂, Triangle.mk_mor₂] at this
        rw [← assoc, this]
        rw [← cancel_epi eZ.hom.hom₂]
        conv_rhs => rw [ex.choose_spec]
        simp only [Triangle.mk_obj₂, triangleGELT_obj_obj₃, triangleGELT_obj_obj₂, Functor.id_obj,
          Triangle.mk_obj₃, assoc, Iso.hom_inv_id_triangle_hom₂_assoc, Iso.refl_hom,
          Iso.inv_hom_id_triangle_hom₃_assoc, id_comp]
        have := (truncLTπ n).naturality T.mor₃
        simp only [Functor.id_obj, Functor.id_map] at this
        rw [← assoc, ← this, ← comm₃₁₂]
        simp only [triangleGELT_obj_obj₂, triangleGELT_obj_obj₃, triangleGELT_obj_mor₂, assoc]
        rw [truncLTCommShift_comm]
    exact isomorphic_distinguished _ hLE _ e.symm

noncomputable instance (n : ℤ) : (hP.truncLE n).IsTriangulated := by
  dsimp [truncLE]; infer_instance

noncomputable instance (n : ℤ) : (hP.truncGE n).IsTriangulated where
  map_distinguished T hT := by
    obtain ⟨Z₁, Z₃, f, g, h, v₁, w₁, u₃, v₃, w₃, hZ, hGT, hLE, _, comm₂₃, comm₃₁₁, _, _⟩ :=
      NineGrid' (hP.triangleGELT_distinguished n T.obj₁) (hP.triangleGELT_distinguished n
      T.obj₂) ((hP.truncGE n).map T.mor₁) T.mor₁ (by simp only [triangleGELT_obj_obj₁,
        triangleGELT_obj_obj₂, triangleGELT_obj_mor₁, NatTrans.naturality, Functor.id_obj,
        Functor.id_map]) T.mor₂ T.mor₃ hT
    have ex := triangle_iso_exists (n - 1) n (by linarith) _ _ hZ
      (hP.triangleGELT_distinguished n T.obj₃) (Iso.refl _)
      (by simp only [Triangle.mk_obj₁]
          refine hP.isGE₃ _ hGT ?_ ?_ (n := n)
          simp only [triangleGELT_obj_obj₁, Triangle.mk_obj₁]; infer_instance
          simp only [triangleGELT_obj_obj₁, Triangle.mk_obj₂]; infer_instance)
      (by simp only [Triangle.mk_obj₃]
          refine hP.isLE₃ _ hLE ?_ ?_ (n := n - 1)
          simp only [triangleGELT_obj_obj₃, Triangle.mk_obj₁]; infer_instance
          simp only [triangleGELT_obj_obj₃, Triangle.mk_obj₂]; infer_instance)
      (by simp only [triangleGELT_obj_obj₁]; infer_instance)
      (by simp only [triangleGELT_obj_obj₃]; infer_instance)
    set eZ := ex.choose
    set e : Triangle.mk ((hP.truncGE n).map T.mor₁) v₁ w₁ ≅ (truncGE n).mapTriangle.obj T := by
      refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Triangle.π₁.mapIso eZ) ?_ ?_ ?_
      · simp only [Triangle.mk_obj₁, Functor.mapTriangle_obj, Triangle.mk_obj₂, Triangle.mk_mor₁,
        Iso.refl_hom, comp_id, id_comp]
      · simp only [Triangle.mk_obj₂, Functor.mapTriangle_obj, Triangle.mk_obj₃, Triangle.mk_mor₂,
        Functor.mapIso_hom, Triangle.π₁_map, Iso.refl_hom, id_comp]
        refine to_truncGE_obj_ext n _ _ _ ?_
        have := eZ.hom.comm₁
        simp only [Triangle.mk_obj₁, triangleGELT_obj_obj₂, Triangle.mk_obj₂, Triangle.mk_mor₁,
          triangleGELT_obj_obj₁, triangleGELT_obj_mor₁] at this
        conv_lhs => rw [assoc, ← this]
        have := comm₂₃.1
        simp only [triangleGELT_obj_obj₁, Triangle.mk_obj₂, triangleGELT_obj_obj₂,
          triangleGELT_obj_mor₁, Triangle.mk_obj₁, Triangle.mk_mor₁] at this
        conv_lhs => rw [← assoc, ← this]
        simp only [Functor.id_obj, Triangle.mk_obj₂, triangleGELT_obj_obj₂, Iso.refl_hom, assoc,
          NatTrans.naturality, Functor.id_map, eZ]
        rw [ex.choose_spec, Iso.refl_hom]; erw [comp_id]
      · simp only [Triangle.mk_obj₃, Functor.mapTriangle_obj, Triangle.mk_obj₁, Triangle.mk_mor₃,
        Iso.refl_hom, Functor.map_id, comp_id, Functor.mapIso_hom, Triangle.π₁_map]
        rw [← cancel_mono (((truncGE n).commShiftIso 1).inv.app T.obj₁)]
        simp only [Functor.comp_obj, assoc, Iso.hom_inv_id_app, comp_id]
        have : IsGE Z₁ n := by
          have := asIso eZ.hom.hom₁
          simp only [Triangle.mk_obj₁, triangleGELT_obj_obj₁] at this
          exact isGE_of_iso this.symm _
        refine to_truncGE_obj_ext n _ _ _ ?_
        simp only [Functor.id_obj, assoc, NatTrans.naturality, Functor.id_map]
        rw [truncGECommShift_comm]; erw [comm₃₁₁]
        have := eZ.hom.comm₁
        simp only [Triangle.mk_obj₁, triangleGELT_obj_obj₂, Triangle.mk_obj₂, Triangle.mk_mor₁,
          triangleGELT_obj_obj₁, triangleGELT_obj_mor₁] at this
        conv_rhs => rw [← assoc, ← this, ex.choose_spec, Iso.refl_hom]; erw [comp_id]
    exact isomorphic_distinguished _ hGT _ e.symm

noncomputable instance (n : ℤ) : (hP.truncGT n).IsTriangulated := by
  dsimp [truncGT]; infer_instance

end FilteredTriangulated

end Triangulated

end CategoryTheory
