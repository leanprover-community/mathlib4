/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.ETrunc
public import Mathlib.CategoryTheory.Triangulated.TStructure.Induced
public import Mathlib.CategoryTheory.Triangulated.TStructure.AbstractSpectralObject

/-!
# Truncations for a t-structure

-/

@[expose] public section

namespace CategoryTheory

open Category Limits Pretriangulated ZeroObject Preadditive

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Triangulated

namespace TStructure

variable (t : TStructure C)

@[simps]
noncomputable def abstractSpectralObject : SpectralObject.AbstractSpectralObject C EInt where
  truncLT := t.eTruncLT
  truncGE := t.eTruncGE
  truncLTObjTopIso' := Iso.refl _
  truncGEObjBotIso' := Iso.refl _
  truncGEδLT := t.eTruncGEδLTt

namespace AbstractSpectralObject

open SpectralObject

@[simp]
lemma truncGELT_eq (g : Arrow EInt) :
  (abstractSpectralObject t).truncGELT.obj g =
    t.eTruncLT.obj g.right ⋙ t.eTruncGE.obj g.left := rfl

lemma isZero_truncGE_obj_top_obj (X : C) :
    IsZero ((t.abstractSpectralObject.truncGE.obj ⊤).obj X) :=
  IsZero.obj (isZero_zero _) _

lemma isZero_truncLT_obj_bot_obj (X : C) :
    IsZero ((t.abstractSpectralObject.truncLT.obj ⊥).obj X) :=
  IsZero.obj (isZero_zero _) _

@[simp]
lemma truncLEι_mk (n : ℤ) :
    t.abstractSpectralObject.truncLTι (EInt.mk n) = t.truncLTι n :=
  comp_id _

@[simp]
lemma truncGEπ_mk (n : ℤ) :
    t.abstractSpectralObject.truncGEπ (EInt.mk n) = t.truncGEπ n :=
  id_comp _

@[simp]
lemma truncGEδLT_mk (n : ℤ) :
    t.abstractSpectralObject.truncGEδLT.app (EInt.mk n) =
      t.truncGEδLT n := rfl

noncomputable def triangleLTGEIso (n : ℤ) (X : C) :
    (t.abstractSpectralObject.triangleLTGE.obj (EInt.mk n)).obj X ≅
      (t.triangleLTGE n).obj X :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)

@[simp]
lemma truncLTObjTopIso : t.abstractSpectralObject.truncLTObjTopIso = Iso.refl _ := rfl

@[simp]
lemma truncGEObjBotIso : t.abstractSpectralObject.truncGEObjBotIso = Iso.refl _ := rfl

@[simp]
lemma truncLTι_top_app (X : C) :
    (t.abstractSpectralObject.truncLTι ⊤).app X = 𝟙 X := by
  dsimp [AbstractSpectralObject.truncLTι]
  erw [Functor.map_id]
  simp only [eTruncLT_obj_top, NatTrans.id_app, Functor.id_obj, comp_id]

@[simp]
lemma truncGEπ_bot_app (X : C) :
    (t.abstractSpectralObject.truncGEπ ⊥).app X = 𝟙 X := by
  dsimp [AbstractSpectralObject.truncGEπ]
  erw [Functor.map_id]
  simp only [eTruncGE_obj_bot, NatTrans.id_app, Functor.id_obj, comp_id]

noncomputable def triangleLTGETopIso (X : C) :
  (t.abstractSpectralObject.triangleLTGE.obj ⊤).obj X ≅
    Pretriangulated.contractibleTriangle X := by
  refine Triangle.isoMk _ _ (((abstractSpectralObject t).truncLTObjTopIso).app X)
    (Iso.refl _) (isZero_truncLT_obj_bot_obj t X).isoZero ?_ ?_ ?_
  · dsimp
    rw [truncLTι_top_app]
  · exact IsZero.eq_of_tgt (isZero_zero _) _ _
  · refine IsZero.eq_of_src ?_ _ _
    exact IsZero.obj (isZero_zero _) _

noncomputable def triangleLTGEBotIso (X : C) :
  (t.abstractSpectralObject.triangleLTGE.obj ⊥).obj X ≅
    (Pretriangulated.contractibleTriangle X).invRotate := by
  refine Triangle.isoMk _ _ ((isZero_truncLT_obj_bot_obj t X).isoZero ≪≫
    (shiftFunctor C (-1 : ℤ)).mapZeroObject.symm)
    (((abstractSpectralObject t).truncLTObjTopIso).app X) (Iso.refl _) ?_ ?_ ?_
  · apply IsZero.eq_of_src
    apply isZero_truncLT_obj_bot_obj
  · dsimp
    rw [truncGEπ_bot_app]
  · apply IsZero.eq_of_tgt _
    dsimp
    rw [IsZero.iff_id_eq_zero, ← Functor.map_id, ← Functor.map_id, id_zero,
      Functor.map_zero, Functor.map_zero]

lemma distinguished (n : EInt) (X : C) :
  (t.abstractSpectralObject.triangleLTGE.obj n).obj X ∈ distTriang C := by
  obtain (_|_|n) := n
  · exact isomorphic_distinguished _
      (inv_rot_of_distTriang _ (contractible_distinguished X)) _
      (triangleLTGEBotIso t X)
  · exact isomorphic_distinguished _ (contractible_distinguished X) _
      (triangleLTGETopIso t X)
  · exact isomorphic_distinguished _ (t.triangleLTGE_distinguished n X) _
      (triangleLTGEIso t n X)

end AbstractSpectralObject


/- Now, we need the octahedron axiom -/

variable [IsTriangulated C]

lemma isIso₁_truncLE_map_of_isGE (T : Triangle C) (hT : T ∈ distTriang C)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (h₃ : t.IsGE T.obj₃ n₁) :
    IsIso ((t.truncLE n₀).map T.mor₁) := by
  rw [isIso_truncLEmap_iff _ _ _ _ h]
  obtain ⟨Z, g, k, mem⟩ := distinguished_cocone_triangle ((t.truncLEι n₀).app T.obj₁ ≫ T.mor₁)
  refine ⟨_, _, _, mem, ?_⟩
  have H := someOctahedron rfl (t.triangleLEGE_distinguished n₀ n₁ h T.obj₁) hT mem
  exact t.isGE₂ _ H.mem n₁ (by dsimp; infer_instance) (by dsimp; infer_instance)

lemma isIso₁_truncLT_map_of_isGE (T : Triangle C) (hT : T ∈ distTriang C)
    (n : ℤ) (h₃ : t.IsGE T.obj₃ n) : IsIso ((t.truncLT n).map T.mor₁) := by
  rw [← NatIso.isIso_map_iff (t.truncLEIsoTruncLT (n-1) n (by lia))]
  exact t.isIso₁_truncLE_map_of_isGE T hT (n-1) n (by lia) h₃

lemma isIso₂_truncGE_map_of_LE (T : Triangle C) (hT : T ∈ distTriang C)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (h₁ : t.IsLE T.obj₁ n₀) :
    IsIso ((t.truncGE n₁).map T.mor₂) := by
  rw [isIso_truncGEmap_iff _ _ _ _ h]
  obtain ⟨X, f, k, mem⟩ := distinguished_cocone_triangle₁ (T.mor₂ ≫ (t.truncGEπ n₁).app T.obj₃)
  refine ⟨_, _, _, mem, ?_⟩
  have H := someOctahedron rfl (rot_of_distTriang _ hT)
    (rot_of_distTriang _ (t.triangleLEGE_distinguished n₀ n₁ h T.obj₃))
    (rot_of_distTriang _ mem)
  have : t.IsLE (X⟦(1 : ℤ)⟧) (n₀-1) := t.isLE₂ _ H.mem (n₀-1)
    (t.isLE_shift T.obj₁ n₀ 1 (n₀-1) (by lia))
    (t.isLE_shift ((t.truncLE n₀).obj T.obj₃) n₀ 1 (n₀-1) (by lia))
  exact t.isLE_of_shift X n₀ 1 (n₀-1) (by lia)

instance (X : C) (a b : ℤ) [t.IsGE X a] : t.IsGE ((t.truncLE b).obj X) a := by
  rw [t.isGE_iff_isZero_truncLE_obj (a-1) a (by lia)]
  have := t.isIso₁_truncLE_map_of_isGE _ ((t.triangleLEGE_distinguished b (b+1) rfl X))
    (a-1) a (by lia) (by dsimp; infer_instance)
  dsimp at this
  exact IsZero.of_iso (t.isZero_truncLE_obj_of_isGE (a-1) a (by lia) X)
    (asIso ((t.truncLE (a - 1)).map ((t.truncLEι b).app X)))

instance (X : C) (a b : ℤ) [t.IsGE X a] : t.IsGE ((t.truncLT b).obj X) a :=
  t.isGE_of_iso ((t.truncLEIsoTruncLT (b-1) b (by lia)).app X) a

instance (X : C) (a b : ℤ) [t.IsLE X b] : t.IsLE ((t.truncGE a).obj X) b := by
  rw [t.isLE_iff_isZero_truncGE_obj b (b+1) rfl]
  have := t.isIso₂_truncGE_map_of_LE _ ((t.triangleLEGE_distinguished (a-1) a (by lia) X))
    b (b+1) rfl (by dsimp; infer_instance)
  dsimp at this
  exact IsZero.of_iso (t.isZero_truncGE_obj_of_isLE b (b+1) rfl X)
    (asIso ((t.truncGE (b+1)).map ((t.truncGEπ  a).app X))).symm

instance (X : C) (a b : ℤ) : t.IsGE ((t.truncGELE a b).obj X) a := by
  dsimp [truncGELE]
  infer_instance

instance (X : C) (a b : ℤ) : t.IsLE ((t.truncGELE a b).obj X) b := by
  dsimp [truncGELE]
  infer_instance

instance (X : C) (a b : ℤ) : t.IsGE ((t.truncGELT a b).obj X) a := by
  dsimp [truncGELT]
  infer_instance

instance (X : C) (a b : ℤ) : t.IsLE ((t.truncGELT a b).obj X) (b-1) := by
  dsimp [truncGELT]
  infer_instance

instance (X : C) (a b : ℤ) : t.IsGE ((t.truncLTGE a b).obj X) a := by
  dsimp [truncLTGE]
  infer_instance

instance (X : C) (a b : ℤ) : t.IsLE ((t.truncLTGE a b).obj X) (b-1) := by
  dsimp [truncLTGE]
  infer_instance

instance (a b : ℤ) : (t.truncGELT a b).Additive := by
  dsimp only [truncGELT]
  infer_instance

instance (a b : ℤ) : (t.truncGELE a b).Additive := by
  dsimp only [truncGELE]
  infer_instance

instance (i : EInt) : (t.eTruncGE.obj i).Additive := by
  induction i <;> constructor <;> cat_disch

instance (i : EInt) : (t.eTruncLT.obj i).Additive := by
  induction i <;> constructor <;> cat_disch

omit [IsTriangulated C] in
lemma isZero_eTruncLT_obj_obj (X : C) (n : ℤ) [t.IsGE X n] (j : EInt) (hj : j ≤ EInt.mk n) :
    IsZero ((t.eTruncLT.obj j).obj X) := by
  induction j with
  | bot => simp
  | coe j =>
    dsimp
    rw [← t.isGE_iff_isZero_truncLT_obj]
    exact t.isGE_of_GE  _ _ _ (by simpa using hj)
  | top => simp at hj

omit [IsTriangulated C] in
lemma isZero_eTruncGE_obj_obj (X : C) (n : ℤ) [t.IsLE X n] (j : EInt) (hj : EInt.mk n < j) :
    IsZero ((t.eTruncGE.obj j).obj X) := by
  induction j with
  | bot => simp at hj
  | coe j =>
    simp only [EInt.coe_lt_coe_iff] at hj
    dsimp
    rw [← t.isLE_iff_isZero_truncGE_obj (j - 1) j (by simp)]
    exact t.isLE_of_LE X n (j - 1) (by lia)
  | top => simp

omit [IsTriangulated C] in
lemma eTruncGE_obj_obj_isGE (n : ℤ) (i : EInt) (h : EInt.mk n ≤ i) (X : C) :
    t.IsGE ((t.eTruncGE.obj i).obj X) n := by
  induction i with
  | bot => simp at h
  | coe i =>
    dsimp
    exact t.isGE_of_GE  _ _ _ (by simpa using h)
  | top => exact t.isGE_of_isZero (Functor.zero_obj _) _

omit [IsTriangulated C] in
lemma eTruncLT_obj_obj_isLE (n : ℤ) (i : EInt) (h : i ≤ EInt.mk (n + 1)) (X : C) :
    t.IsLE (((t.eTruncLT.obj i)).obj X) n := by
  induction i with
  | bot => exact t.isLE_of_isZero (by simp) _
  | coe i =>
    simp only [EInt.coe_le_coe_iff] at h
    dsimp
    exact t.isLE_of_LE _ (i - 1) n (by lia)
  | top => simp at h

lemma isIso_truncGE_map_truncGEπ_app (a b : ℤ) (h : a ≤ b) (X : C) :
    IsIso ((t.truncGE b).map ((t.truncGEπ a).app X)) :=
  t.isIso₂_truncGE_map_of_LE _
    (t.triangleLEGE_distinguished (a-1) a (by lia) X) (b-1) b (by lia)
      (t.isLE_of_LE ((t.truncLE (a-1)).obj X) (a-1) (b-1) (by lia))

lemma isIso_truncLT_map_truncLTι_app (a b : ℤ) (h : a ≤ b) (X : C) :
    IsIso ((t.truncLT a).map ((t.truncLTι b).app X)) :=
  t.isIso₁_truncLT_map_of_isGE _ (t.triangleLTGE_distinguished b X) a
    (t.isGE_of_GE ((t.truncGE b).obj X) a b (by lia))

lemma isIso_truncLE_map_truncLEι_app (a b : ℤ) (h : a ≤ b) (X : C) :
    IsIso ((t.truncLE a).map ((t.truncLEι b).app X)) := by
  apply isIso_truncLT_map_truncLTι_app
  lia

instance (X : C) (n : ℤ) : IsIso ((t.truncLE n).map ((t.truncLEι n).app X)) :=
  t.isIso_truncLE_map_truncLEι_app _ _ (by rfl) _

instance (X : C) (n : ℤ) : IsIso ((t.truncGE n).map ((t.truncGEπ n).app X)) :=
  t.isIso_truncGE_map_truncGEπ_app _ _ (by rfl) _

lemma isIso_eTruncGE_obj_map_truncGEπ_app (a b : EInt) (h : a ≤ b) (X : C) :
    IsIso ((t.eTruncGE.obj b).map ((t.abstractSpectralObject.truncGEπ a).app X)) := by
  induction b with
  | bot =>
    obtain rfl : a = ⊥ := by simpa using h
    dsimp
    simp only [AbstractSpectralObject.truncGEπ_bot_app]
    infer_instance
  | coe b =>
    induction a with
    | bot => dsimp; infer_instance
    | coe a =>
      simp only [EInt.coe_le_coe_iff] at h
      simp only [AbstractSpectralObject.truncGEπ_mk]
      exact t.isIso_truncGE_map_truncGEπ_app a b h X
    | top => simp at h
  | top => exact ⟨0, IsZero.eq_of_src (by simp) _ _, IsZero.eq_of_src (by simp) _ _⟩

lemma isIso_eTruncLT_obj_map_truncLTπ_app (a b : EInt) (h : a ≤ b) (X : C) :
    IsIso ((t.eTruncLT.obj a).map ((t.abstractSpectralObject.truncLTι b).app X)) := by
  induction a with
  | bot => exact ⟨0, IsZero.eq_of_src (by simp) _ _, IsZero.eq_of_src (by simp) _ _⟩
  | coe a =>
    induction b with
    | bot => simp at h
    | coe b =>
      simp only [EInt.coe_le_coe_iff] at h
      simp only [AbstractSpectralObject.truncLEι_mk]
      exact t.isIso_truncLT_map_truncLTι_app a b h X
    | top => dsimp; infer_instance
  | top =>
    obtain rfl : b = ⊤ := by simpa using h
    dsimp [AbstractSpectralObject.truncLTι_top_app]
    infer_instance

instance (D : Arrow EInt) (X : C) :
  IsIso ((t.abstractSpectralObject.truncGEToTruncGEGE.app D).app X) :=
    t.isIso_eTruncGE_obj_map_truncGEπ_app _ _ (leOfHom D.hom) X

instance (D : Arrow EInt) (X : C) :
  IsIso ((t.abstractSpectralObject.truncLTLTToTruncLT.app D).app X) :=
    t.isIso_eTruncLT_obj_map_truncLTπ_app _ _ (leOfHom D.hom) X

instance (D : Arrow EInt) : IsIso (t.abstractSpectralObject.truncGEToTruncGEGE.app D) :=
  NatIso.isIso_of_isIso_app _

instance (D : Arrow EInt) : IsIso (t.abstractSpectralObject.truncLTLTToTruncLT.app D) :=
  NatIso.isIso_of_isIso_app _

instance : IsIso (t.abstractSpectralObject.truncGEToTruncGEGE) := NatIso.isIso_of_isIso_app _

instance : IsIso (t.abstractSpectralObject.truncLTLTToTruncLT) := NatIso.isIso_of_isIso_app _

omit [IsTriangulated C] in
lemma truncGEπ_compatibility (a : EInt) (X : C) :
  (t.abstractSpectralObject.truncGE.obj a).map ((t.abstractSpectralObject.truncGEπ a).app X) =
    (t.abstractSpectralObject.truncGEπ a).app
      ((t.abstractSpectralObject.truncGE.obj a).obj X) := by
  induction a with
  | bot => simp
  | coe a =>
    simp only [abstractSpectralObject_truncGE, eTruncGE_obj_mk, Functor.id_obj,
      AbstractSpectralObject.truncGEπ_mk]
    exact t.from_truncGE_obj_ext ((t.truncGEπ a).naturality ((t.truncGEπ a).app X)).symm
  | top => exact IsZero.eq_of_src (by simp) _ _

omit [IsTriangulated C] in
lemma truncLTι_compatibility (a : EInt) (X : C) :
    (t.abstractSpectralObject.truncLT.obj a).map ((t.abstractSpectralObject.truncLTι a).app X) =
      (t.abstractSpectralObject.truncLTι a).app
        ((t.abstractSpectralObject.truncLT.obj a).obj X) := by
  induction a with
  | bot => exact IsZero.eq_of_src (by simp) _ _
  | coe a =>
    simp only [abstractSpectralObject_truncLT, eTruncLT_obj_mk, Functor.id_obj,
      AbstractSpectralObject.truncLEι_mk]
    exact t.to_truncLT_obj_ext ((t.truncLTι a).naturality ((t.truncLTι a).app X))
  | top => simp

lemma isIso_truncLTι_app_truncGELT_obj (a b : EInt) (h : a ≤ b) (X : C) :
    IsIso ((t.abstractSpectralObject.truncLTι b).app
      ((t.eTruncLT.obj b ⋙ t.eTruncGE.obj a).obj X)) := by
  induction b with
  | bot =>
    refine ⟨0, IsZero.eq_of_src (by simp) _ _, IsZero.eq_of_src ?_ _ _⟩
    dsimp
    exact IsZero.of_iso (isZero_zero _)
        (Functor.mapIso _ (IsZero.isoZero (Functor.zero_obj _)) ≪≫
          (t.eTruncGE.obj a).mapZeroObject)
  | coe b =>
    simp only [abstractSpectralObject_truncLT, eTruncLT_obj_mk, Functor.comp_obj,
      Functor.id_obj, AbstractSpectralObject.truncLEι_mk]
    rw [← t.isLE_iff_isIso_truncLTι_app (b-1) b (by lia)]
    induction a with
    | bot => dsimp; infer_instance
    | coe a => dsimp; infer_instance
    | top => exact t.isLE_of_isZero (by simp) _
  | top =>
    simp only [abstractSpectralObject_truncLT, eTruncLT_obj_top, Functor.comp_obj,
      Functor.id_obj, AbstractSpectralObject.truncLTι_top_app]
    infer_instance

instance (D : Arrow EInt) (X : C) :
    IsIso ((t.abstractSpectralObject.truncLTGELTSelfToTruncGELT.app D).app X) :=
  t.isIso_truncLTι_app_truncGELT_obj D.left D.right (leOfHom D.hom) X

instance (D : Arrow EInt) : IsIso (t.abstractSpectralObject.truncLTGELTSelfToTruncGELT.app D) :=
  NatIso.isIso_of_isIso_app _

instance : IsIso (t.abstractSpectralObject.truncLTGELTSelfToTruncGELT) :=
  NatIso.isIso_of_isIso_app _

instance (a b : ℤ) (X : C) : t.IsLE ((t.truncGELT a b).obj X) (b-1) := by
  dsimp [truncGELT]
  infer_instance

noncomputable def natTransTruncGELTTruncLTGE (a b : ℤ) :
    t.truncGELT a b ⟶ t.truncLTGE a b where
  app X := t.liftTruncLT (t.descTruncGE
    ((t.truncLTι b).app X ≫ (t.truncGEπ a).app X) a) (b-1) b (by lia)
  naturality X Y f := by
    dsimp [truncGELT, truncLTGE]
    apply t.to_truncLT_obj_ext
    dsimp
    apply t.from_truncGE_obj_ext
    simp only [Functor.id_obj, assoc, liftTruncLT_ι, NatTrans.naturality,
      Functor.id_map, liftTruncLT_ι_assoc, π_descTruncGE_assoc,
      ← NatTrans.naturality_assoc, π_descTruncGE]
    rw [← NatTrans.naturality, NatTrans.naturality_assoc]

@[reassoc (attr := simp)]
lemma natTransTruncGELETruncLEGE_app_pentagon (a b : ℤ) (X : C) :
    (t.truncGEπ a).app _ ≫ (t.natTransTruncGELTTruncLTGE a b).app X ≫ (t.truncLTι b).app _ =
      (t.truncLTι b).app X ≫ (t.truncGEπ a).app X := by simp [natTransTruncGELTTruncLTGE]

lemma natTransTruncGELETruncLEGE_app_pentagon_uniqueness (a b : ℤ) (X : C)
    (φ : (t.truncGELT a b).obj X ⟶ (t.truncLTGE a b).obj X)
    (hφ : (t.truncGEπ a).app _ ≫ φ ≫ (t.truncLTι b).app _ =
      (t.truncLTι b).app X ≫ (t.truncGEπ a).app X) :
    φ = (t.natTransTruncGELTTruncLTGE a b).app X := by
  apply t.to_truncLT_obj_ext
  dsimp
  apply t.from_truncGE_obj_ext
  rw [hφ, natTransTruncGELETruncLEGE_app_pentagon]

noncomputable def truncGELTδLT (a b : ℤ) :
    t.truncGELT a b ⟶ t.truncLT a ⋙ shiftFunctor C (1 : ℤ) :=
  Functor.whiskerLeft (t.truncLT b) (t.truncGEδLT a) ≫
    Functor.whiskerRight (t.truncLTι b) (t.truncLT a ⋙ shiftFunctor C (1 : ℤ))

@[simps!]
noncomputable def triangleLTLTGELT (a b : ℤ) (h : a ≤ b) : C ⥤ Triangle C :=
  Triangle.functorMk (t.natTransTruncLTOfLE a b h)
    (Functor.whiskerLeft (t.truncLT b) (t.truncGEπ a)) (t.truncGELTδLT a b)

lemma triangleLTLTGELT_distinguished (a b : ℤ) (h : a ≤ b) (X : C) :
    (t.triangleLTLTGELT a b h).obj X ∈ distTriang C := by
  have := t.isIso_truncLT_map_truncLTι_app a b h X
  refine isomorphic_distinguished _ (t.triangleLTGE_distinguished a ((t.truncLT b).obj X)) _ ?_
  refine Triangle.isoMk _ _ ((asIso ((t.truncLT a).map ((t.truncLTι b).app X))).symm)
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · dsimp
    simp only [comp_id, IsIso.eq_inv_comp]
    apply t.to_truncLT_obj_ext
    simp only [Functor.id_obj, NatTrans.naturality, assoc, Functor.id_map,
      natTransTruncLTOfLE_ι_app_assoc]
  · dsimp
    simp only [comp_id, id_comp]
  · dsimp [truncGELTδLT]
    simp only [Functor.map_inv, assoc, IsIso.hom_inv_id, comp_id, id_comp]

instance (a b : ℤ) (X : C) : IsIso ((t.natTransTruncGELTTruncLTGE a b).app X) := by
  by_cases h : a ≤ b
  · let u₁₂ := (t.natTransTruncLTOfLE a b h).app X
    let u₂₃ : (t.truncLT b).obj X ⟶ X := (t.truncLTι b).app X
    let u₁₃ : _ ⟶ X := (t.truncLTι a).app X
    have eq : u₁₂ ≫ u₂₃ = u₁₃ := by simp [u₁₂, u₂₃, u₁₃]
    have H := someOctahedron eq (t.triangleLTLTGELT_distinguished a b h X)
      (t.triangleLTGE_distinguished b X) (t.triangleLTGE_distinguished a X)
    let m₁ : (t.truncGELT a b).obj X ⟶  _ := H.m₁
    have := t.isIso₁_truncLT_map_of_isGE _ H.mem b (by dsimp; infer_instance)
    dsimp at this
    have eq' : t.liftTruncLT m₁ (b-1) b (by lia) =
        (t.natTransTruncGELTTruncLTGE a b).app X := by
      apply t.to_truncLT_obj_ext
      dsimp
      apply t.from_truncGE_obj_ext
      simp_rw [natTransTruncGELETruncLEGE_app_pentagon, liftTruncLT_ι]
      exact H.comm₁
    rw [← eq']
    have fac : (t.truncLTι b).app ((t.truncGE a).obj ((t.truncLT b).obj X)) ≫
        t.liftTruncLT m₁ (b-1) b (by lia) = (t.truncLT b).map m₁ :=
      t.to_truncLT_obj_ext (by simp [truncGELT])
    have : IsIso ((t.truncLTι b).app ((t.truncGE a).obj ((t.truncLT b).obj X))) := by
      rw [← t.isLE_iff_isIso_truncLTι_app (b-1) b (by lia)]
      infer_instance
    exact IsIso.of_isIso_fac_left fac
  · refine ⟨0, ?_, ?_⟩
    all_goals
      apply IsZero.eq_of_src
      exact t.isZero _ (b-1) a (by lia)

instance (a b : ℤ) : IsIso (t.natTransTruncGELTTruncLTGE a b) :=
  NatIso.isIso_of_isIso_app _

noncomputable def truncGELTIsoLTGE (a b : ℤ) : t.truncGELT a b ≅ t.truncLTGE a b :=
  asIso (t.natTransTruncGELTTruncLTGE a b)

noncomputable def truncGELEIsoLEGE (a b : ℤ) : t.truncGELE a b ≅ t.truncLEGE a b :=
  t.truncGELTIsoLTGE a (b + 1)

instance (a b : ℤ) (X : C) :
  IsIso ((t.truncLTι b).app ((t.truncGE a).obj ((t.truncLT b).obj X))) := by
    rw [← t.isLE_iff_isIso_truncLTι_app (b-1) b (by lia)]
    infer_instance

lemma truncLT_map_truncGE_map_truncLTι_app_fac (a b : ℤ) (X : C) :
    (t.truncLT b).map ((t.truncGE a).map ((t.truncLTι b).app X)) =
      (t.truncLTι b).app ((t.truncGE a).obj ((t.truncLT b).obj X)) ≫
        (t.natTransTruncGELTTruncLTGE a b).app X := by
  rw [← cancel_epi (inv ((t.truncLTι b).app ((t.truncGE a).obj ((t.truncLT b).obj X)))),
    IsIso.inv_hom_id_assoc]
  apply t.natTransTruncGELETruncLEGE_app_pentagon_uniqueness
  simp only [Functor.id_obj, assoc, NatTrans.naturality, Functor.id_map, IsIso.inv_hom_id_assoc]
  exact ((t.truncGEπ a).naturality ((t.truncLTι b).app X)).symm

lemma isIso_truncLT_map_truncGE_map_truncLTι_app (a b : ℤ) (X : C) :
    IsIso ((t.truncLT b).map ((t.truncGE a).map ((t.truncLTι b).app X))) := by
  rw [t.truncLT_map_truncGE_map_truncLTι_app_fac a b X]
  infer_instance

instance (D : Arrow EInt) (X : C) :
    IsIso ((t.abstractSpectralObject.truncLTGELTSelfToTruncLTGE.app D).app X) := by
  obtain ⟨a, b, f, rfl⟩ := Arrow.mk_surjective D
  have h : a ≤ b := leOfHom f
  induction b with
  | bot =>
    obtain rfl : a = ⊥ := by simpa using h
    exact ⟨0, IsZero.eq_of_src (Functor.zero_obj _) _ _,
      IsZero.eq_of_src (Functor.zero_obj _) _ _⟩
  | coe b =>
    dsimp [SpectralObject.AbstractSpectralObject.truncLTGELTSelfToTruncLTGE,
      SpectralObject.AbstractSpectralObject.truncLTGE]
    induction a with
    | bot =>
      simp only [AbstractSpectralObject.truncLEι_mk]
      exact t.isIso_truncLT_map_truncLTι_app b b (by rfl) X
    | coe a =>
      simp only [EInt.coe_le_coe_iff] at h
      simp only [eTruncGE_obj_mk, AbstractSpectralObject.truncLEι_mk]
      exact t.isIso_truncLT_map_truncGE_map_truncLTι_app a b X
    | top =>
      refine ⟨0, IsZero.eq_of_src ?_ _ _, IsZero.eq_of_src ?_ _ _⟩
      all_goals
        exact (isZero_zero _).of_iso
          ((t.truncLT b).mapIso ((Functor.zero_obj _).isoZero) ≪≫
            (t.truncLT b).mapZeroObject)
  | top =>
  · dsimp [SpectralObject.AbstractSpectralObject.truncLTGELTSelfToTruncLTGE]
    simp only [AbstractSpectralObject.truncLTι_top_app, Functor.map_id]
    infer_instance

instance (D : Arrow EInt) : IsIso (t.abstractSpectralObject.truncLTGELTSelfToTruncLTGE.app D) :=
  NatIso.isIso_of_isIso_app _

instance : IsIso (t.abstractSpectralObject.truncLTGELTSelfToTruncLTGE) :=
  NatIso.isIso_of_isIso_app _

instance : t.abstractSpectralObject.IsCompatible where
  distinguished := AbstractSpectralObject.distinguished t
  truncGEπ_compatibility' := t.truncGEπ_compatibility
  truncLTι_compatibility' := t.truncLTι_compatibility

@[simps!]
noncomputable def spectralObject (X : C) : SpectralObject C EInt :=
  t.abstractSpectralObject.spectralObject X

end TStructure

end Triangulated

namespace Triangulated

variable (t : TStructure C)

instance [IsTriangulated C] : t.plus.HasInducedTStructure t :=
  .mk' (by
    rintro X ⟨a, _⟩ n
    exact ⟨⟨a, inferInstance⟩, ⟨a, inferInstance⟩⟩)

instance [IsTriangulated C] : t.minus.HasInducedTStructure t :=
  .mk' (by
    rintro X ⟨a, _⟩ n
    exact ⟨⟨a, inferInstance⟩, ⟨a, inferInstance⟩⟩)

instance [IsTriangulated C] : t.bounded.HasInducedTStructure t := by
  dsimp [TStructure.bounded]
  infer_instance

namespace TStructure

instance [IsTriangulated C] (X : C) (n : ℤ) [t.IsGE X n] (i : EInt) :
    t.IsGE ((t.eTruncLT.obj i).obj X) n := by
  induction i with
  | bot => exact isGE_of_isZero _ (by simp) _
  | coe _ => dsimp; infer_instance
  | top => dsimp; infer_instance

instance [IsTriangulated C] (X : C) (n : ℤ) [t.IsLE X n] (i : EInt) :
    t.IsLE ((t.eTruncGE.obj i).obj X) n := by
  induction i with
  | bot => dsimp; infer_instance
  | coe _ => dsimp; infer_instance
  | top => exact isLE_of_isZero _ (by simp) _

end TStructure

end Triangulated

end CategoryTheory
