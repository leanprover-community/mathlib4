/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.Basic
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.CategoryTheory.Triangulated.TStructure.AbstractSpectralObject
public import Mathlib.Algebra.Homology.SpectralSequence.EInt

/-!
# Truncations for a t-structure

-/

@[expose] public section

namespace CategoryTheory

open Category Limits Pretriangulated ZeroObject Preadditive Functor

variable {C : Type _} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Triangulated

namespace TStructure

variable (t : TStructure C)

noncomputable def truncLE (n : ℤ) : C ⥤ C := t.truncLT (n+1)

instance (n : ℤ) : (t.truncLE n).Additive := by
  dsimp only [truncLE]
  infer_instance

instance (n : ℤ) (X : C) : t.IsLE ((t.truncLE n).obj X) n := by
  have : t.IsLE ((t.truncLE n).obj X) (n+1-1) := by
    dsimp [truncLE]
    infer_instance
  exact t.isLE_of_LE _ (n+1-1) n (by lia)

noncomputable def truncGT (n : ℤ) : C ⥤ C := t.truncGE (n+1)

instance (n : ℤ) : (t.truncGT n).Additive := by
  dsimp only [truncGT]
  infer_instance

instance (n : ℤ) (X : C) : t.IsGE ((t.truncGT n).obj X) (n+1) := by
  dsimp [truncGT]
  infer_instance

instance (n : ℤ) (X : C) : t.IsGE ((t.truncGT (n-1)).obj X) n :=
  t.isGE_of_GE _ n (n-1+1) (by lia)

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
  refine Triangle.functorIsoMk _ _ (t.truncLEIsoTruncLT a b h) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · aesop_cat
  · aesop_cat
  · ext
    dsimp [truncGEδLE]
    simp only [assoc, id_comp, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id, comp_id]

lemma triangleLEGE_distinguished (a b : ℤ) (h : a + 1 = b) (X : C) :
    (t.triangleLEGE a b h).obj X ∈ distTriang C :=
  isomorphic_distinguished _ (t.triangleLTGE_distinguished b X) _
    ((t.triangleLEGEIsoTriangleLTGE a b h).app X)

noncomputable def truncGTδLE (n : ℤ) :
    t.truncGT n ⟶ t.truncLE n ⋙ shiftFunctor C (1 : ℤ) :=
  (t.truncGTIsoTruncGE n (n+1) rfl).hom ≫ t.truncGEδLE n (n+1) (by lia)

@[simps!]
noncomputable def triangleLEGT (n : ℤ) : C ⥤ Triangle C :=
  Triangle.functorMk (t.truncLEι n) (t.truncGTπ n) (t.truncGTδLE n)

noncomputable def triangleLEGTIsoTriangleLEGE (a b : ℤ) (h : a + 1 = b) :
    t.triangleLEGT a ≅ t.triangleLEGE a b h := by
  refine Triangle.functorIsoMk _ _ (Iso.refl _) (Iso.refl _) (t.truncGTIsoTruncGE a b h) ?_ ?_ ?_
  · aesop_cat
  · aesop_cat
  · ext
    dsimp [truncGTδLE]
    subst h
    simp only [Functor.map_id, comp_id]

lemma triangleLEGT_distinguished (n : ℤ) (X : C) :
    (t.triangleLEGT n).obj X ∈ distTriang C :=
  isomorphic_distinguished _ (t.triangleLEGE_distinguished n (n+1) rfl X) _
    ((t.triangleLEGTIsoTriangleLEGE n (n+1) rfl).app X)

noncomputable def truncLTt : EInt ⥤ C ⥤ C where
  obj n := by
    induction n with
    | bot => exact 0
    | coe a => exact t.truncLT a
    | top => exact 𝟭 C
  map {x y} f := by
    induction x with
    | bot =>
      induction y with
      | bot => exact 𝟙 _
      | coe b => exact 0
      | top => exact 0
    | coe a =>
      induction y with
      | bot => exact 0
      | coe b => exact t.natTransTruncLTOfLE a b (by simpa using leOfHom f)
      | top => exact t.truncLTι a
    | top =>
      induction y with
      | bot => exact 0
      | coe b => exact 0
      | top => exact 𝟙 _
  map_id n := by induction n <;> simp
  map_comp {x y z} f g := by
    have f' := leOfHom f
    have g' := leOfHom g
    induction x <;> induction y <;> induction z <;> cat_disch

@[simp]
lemma truncLTt_obj_top : t.truncLTt.obj ⊤ = 𝟭 _ := rfl

@[simp]
lemma truncLTt_obj_bot : t.truncLTt.obj ⊥ = 0 := rfl

@[simp]
lemma truncLTt_obj_mk (n : ℤ) : t.truncLTt.obj (EInt.mk n) = t.truncLT n := rfl

@[simp]
lemma truncLTt_map_eq_truncLTι (n : ℤ) :
    t.truncLTt.map (homOfLE (show EInt.mk n ≤ ⊤ by simp)) = t.truncLTι n := rfl

noncomputable def truncGEt : EInt ⥤ C ⥤ C where
  obj n := by
    induction n with
    | bot => exact 𝟭 C
    | coe a => exact t.truncGE a
    | top => exact 0
  map {x y} f := by
    induction x with
    | bot =>
      induction y with
      | bot => exact 𝟙 _
      | coe b => exact t.truncGEπ b
      | top => exact 0
    | coe a =>
      induction y with
      | bot => exact 0
      | coe b => exact t.natTransTruncGEOfLE a b (by simpa using leOfHom f)
      | top => exact 0
    | top =>
      induction y with
      | bot => exact 0
      | coe b => exact 0
      | top => exact 𝟙 _
  map_id n := by induction n <;> simp
  map_comp {x y z} f g := by
    have f' := leOfHom f
    have g' := leOfHom g
    induction x <;> induction y <;> induction z <;> cat_disch

@[simp]
lemma truncGEt_obj_bot :
    t.truncGEt.obj ⊥ = 𝟭 _ := rfl

@[simp]
lemma truncGEt_obj_top :
    t.truncGEt.obj ⊤ = 0 := rfl

@[simp]
lemma truncGEt_obj_mk (n : ℤ) : t.truncGEt.obj (EInt.mk n) = t.truncGE n := rfl

noncomputable def truncGEtδLTt :
    t.truncGEt ⟶ t.truncLTt ⋙ ((whiskeringRight C C C).obj (shiftFunctor C (1 : ℤ))) where
  app a := by
    induction a with
    | bot => exact 0
    | coe a => exact t.truncGEδLT a
    | top => exact 0
  naturality {a b} hab := by
    replace hab := leOfHom hab
    induction a; rotate_right
    · apply (isZero_zero _).eq_of_src
    all_goals
      induction b <;> simp at hab <;>
        dsimp [truncGEt, truncLTt] <;>
        simp [t.truncGEδLT_comp_whiskerRight_natTransTruncLTOfLE]

@[simp]
lemma truncGEtδLTt_mk (n : ℤ) :
    t.truncGEtδLTt.app (EInt.mk n) = t.truncGEδLT n := rfl

@[simps]
noncomputable def abstractSpectralObject : SpectralObject.AbstractSpectralObject C EInt where
  truncLT := t.truncLTt
  truncGE := t.truncGEt
  truncLTObjTopIso' := Iso.refl _
  truncGEObjBotIso' := Iso.refl _
  truncGEδLT := t.truncGEtδLTt

namespace AbstractSpectralObject

open SpectralObject

@[simp]
lemma truncGELT_eq (g : Arrow EInt) :
  (abstractSpectralObject t).truncGELT.obj g =
    t.truncLTt.obj g.right ⋙ t.truncGEt.obj g.left := rfl

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
  simp only [truncLTt_obj_top, NatTrans.id_app, Functor.id_obj, comp_id]

@[simp]
lemma truncGEπ_bot_app (X : C) :
    (t.abstractSpectralObject.truncGEπ ⊥).app X = 𝟙 X := by
  dsimp [AbstractSpectralObject.truncGEπ]
  erw [Functor.map_id]
  simp only [truncGEt_obj_bot, NatTrans.id_app, Functor.id_obj, comp_id]

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

lemma isZero_truncLE_obj_zero (n : ℤ) : IsZero ((t.truncLE n).obj 0) := by
  let δ := (t.truncGEδLE n (n+1) rfl).app 0
  have : IsIso δ := by
    have h := (t.triangleLEGE_distinguished n (n+1) rfl 0)
    exact (Triangle.isZero₂_iff_isIso₃ _ h).1
      ((Triangle.isZero₂_iff _ (t.triangleLEGE_distinguished n (n+1) rfl 0)).2
        ⟨(isZero_zero C).eq_of_tgt _ _, (isZero_zero C).eq_of_src _ _⟩)
  have : t.IsLE ((t.truncLE n ⋙ shiftFunctor C (1 : ℤ)).obj 0) (n-1) :=
    t.isLE_shift _ n 1 (n-1) (by lia)
  have hδ := t.zero_of_isLE_of_isGE δ (n-1) (n+1) (by lia)
    (t.isLE_of_iso (asIso δ).symm _) (t.isGE_of_iso (asIso δ) _)
  rw [IsZero.iff_id_eq_zero]
  apply (shiftFunctor C (1 : ℤ)).map_injective
  rw [Functor.map_id, Functor.map_zero, ← cancel_epi δ, comp_zero, hδ, zero_comp]

lemma isZero_truncGE_obj_zero (n : ℤ) : IsZero ((t.truncGE n).obj 0) := by
  apply (Triangle.isZero₃_iff_isIso₁ _ (t.triangleLEGE_distinguished (n-1) n (by lia) 0)).2
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
  · intro
    obtain ⟨e, he⟩ := t.triangle_iso_exists
      (contractible_distinguished X) (t.triangleLEGT_distinguished n X)
      (Iso.refl X) n (n + 1)
      (by dsimp; infer_instance)
      (by dsimp; infer_instance)
      (by dsimp; infer_instance)
      (by dsimp; infer_instance)
    dsimp at he
    have : (truncLEι t n).app X = e.inv.hom₁ := by
      have he' : e.inv.hom₂ = 𝟙 X := by
        rw [← cancel_mono e.hom.hom₂, ← comp_hom₂, e.inv_hom_id, he]
        dsimp
        rw [id_comp]
      simpa [he'] using e.inv.comm₁
    rw [this]
    infer_instance
  · intro
    exact t.isLE_of_iso (asIso ((truncLEι t n).app X)) n

lemma isLE_iff_isIso_truncLTι_app (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) (X : C) :
    t.IsLE X n₀ ↔ IsIso (((t.truncLTι n₁)).app X) := by
  rw [isLE_iff_isIso_truncLEι_app]
  subst hn₁
  rfl

lemma isGE_iff_isIso_truncGEπ_app (n : ℤ) (X : C) :
    t.IsGE X n ↔ IsIso ((t.truncGEπ n).app X) := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := t.triangle_iso_exists
      (inv_rot_of_distTriang _ (contractible_distinguished X))
      (t.triangleLTGE_distinguished n X) (Iso.refl X) (n-1) n
      (t.isLE_of_iso (shiftFunctor C (-1 : ℤ)).mapZeroObject.symm _)
      (by dsimp; infer_instance) (by dsimp; infer_instance) (by dsimp; infer_instance)
    dsimp at he
    have : (truncGEπ t n).app X = e.hom.hom₃ := by
      have eq := e.hom.comm₂
      dsimp at eq
      rw [← cancel_epi e.hom.hom₂, ← eq, he]
    rw [this]
    infer_instance
  · intro
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
  exact (Triangle.isZero₃_iff_isIso₁ _ (t.triangleLEGT_distinguished n X)).symm

lemma isGE_iff_isZero_truncLT_obj (n : ℤ) (X : C) :
    t.IsGE X n ↔ IsZero ((t.truncLT n).obj X) := by
  rw [t.isGE_iff_isIso_truncGEπ_app n X]
  exact (Triangle.isZero₁_iff_isIso₂ _ (t.triangleLTGE_distinguished n X)).symm

lemma isLE_iff_isZero_truncGE_obj (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) :
    t.IsLE X n₀ ↔ IsZero ((t.truncGE n₁).obj X) := by
  rw [t.isLE_iff_isIso_truncLEι_app n₀ X]
  exact (Triangle.isZero₃_iff_isIso₁ _ (t.triangleLEGE_distinguished n₀ n₁ h X)).symm

lemma isGE_iff_isZero_truncLE_obj (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) :
    t.IsGE X n₁ ↔ IsZero ((t.truncLE n₀).obj X) := by
  rw [t.isGE_iff_isIso_truncGEπ_app n₁ X]
  exact (Triangle.isZero₁_iff_isIso₂ _ (t.triangleLEGE_distinguished n₀ n₁ h X)).symm

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
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _
    (t.triangleLTGE_distinguished n X) f hf
  have hg' := t.zero_of_isLE_of_isGE g (n-2) n (by lia)
    (by dsimp; exact t.isLE_shift _ (n-1) 1 (n-2) (by lia)) (by infer_instance)
  rw [hg, hg', comp_zero]

lemma to_truncLE_obj_ext (n : ℤ) (Y : C) {X : C}
    (f₁ f₂ : Y ⟶ (t.truncLE n).obj X) (h : f₁ ≫ (t.truncLEι n).app X = f₂ ≫ (t.truncLEι n).app X)
    [t.IsLE Y n] :
    f₁ = f₂ := by
  suffices ∀ (f : Y ⟶ (t.truncLE n).obj X) (_ : f ≫ (t.truncLEι n).app X = 0), f = 0 by
    rw [← sub_eq_zero, this (f₁ - f₂) (by rw [sub_comp, sub_eq_zero, h])]
  intro f hf
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _
    (t.triangleLEGT_distinguished n X)) f hf
  have hg' := t.zero_of_isLE_of_isGE g n (n+2) (by lia) (by infer_instance)
    (by dsimp; apply (t.isGE_shift _ (n+1) (-1) (n+2) (by lia)))
  rw [hg, hg', zero_comp]

lemma to_truncLT_obj_ext (n : ℤ) (Y : C) {X : C}
    (f₁ f₂ : Y ⟶ (t.truncLT n).obj X) (h : f₁ ≫ (t.truncLTι n).app X = f₂ ≫ (t.truncLTι n).app X)
    [t.IsLE Y (n - 1)] :
    f₁ = f₂ := by
  rw [← cancel_mono ((t.truncLEIsoTruncLT (n-1) n (by lia)).inv.app X)]
  apply to_truncLE_obj_ext
  simpa only [Functor.id_obj, assoc, truncLEIsoTruncLT_inv_ι_app] using h

/-- liftTruncLE' -/
lemma liftTruncLE' {X Y : C} (f : X ⟶ Y) (n : ℤ) [t.IsLE X n] :
    ∃ (f' : X ⟶ (t.truncLE n).obj Y), f = f' ≫ (t.truncLEι n).app Y :=
  Triangle.coyoneda_exact₂ _ (t.triangleLEGT_distinguished n Y) f
    (t.zero_of_isLE_of_isGE  _ n (n+1) (by lia) inferInstance (by dsimp; infer_instance))

noncomputable def liftTruncLE {X Y : C} (f : X ⟶ Y) (n : ℤ) [t.IsLE X n] :
    X ⟶ (t.truncLE n).obj Y := (t.liftTruncLE' f n).choose

@[reassoc (attr := simp)]
lemma liftTruncLE_ι {X Y : C} (f : X ⟶ Y) (n : ℤ) [t.IsLE X n] :
    t.liftTruncLE f n ≫ (t.truncLEι n).app Y = f :=
  (t.liftTruncLE' f n).choose_spec.symm

noncomputable def liftTruncLT {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) [t.IsLE X n₀] :
    X ⟶ (t.truncLT n₁).obj Y :=
  t.liftTruncLE f n₀ ≫ (t.truncLEIsoTruncLT _ _ h).hom.app Y

@[reassoc (attr := simp)]
lemma liftTruncLT_ι {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) [t.IsLE X n₀] :
    t.liftTruncLT f n₀ n₁ h ≫ (t.truncLTι n₁).app Y = f := by
  dsimp only [liftTruncLT]
  simp only [Functor.id_obj, assoc, truncLEIsoTruncLT_hom_ι_app, liftTruncLE_ι]

/-- descTruncGE' -/
lemma descTruncGE' {X Y : C} (f : X ⟶ Y) (n : ℤ) [t.IsGE Y n] :
  ∃ (f' : (t.truncGE n).obj X ⟶ Y), f = (t.truncGEπ n).app X ≫ f' :=
  Triangle.yoneda_exact₂ _ (t.triangleLTGE_distinguished n X) f
    (t.zero_of_isLE_of_isGE _ (n-1)  n (by lia) (by dsimp; infer_instance) inferInstance)

noncomputable def descTruncGE {X Y : C} (f : X ⟶ Y) (n : ℤ) [t.IsGE Y n] :
    (t.truncGE n).obj X ⟶ Y := (t.descTruncGE' f n).choose

@[reassoc (attr := simp)]
lemma π_descTruncGE {X Y : C} (f : X ⟶ Y) (n : ℤ) [t.IsGE Y n] :
    (t.truncGEπ n).app X ≫ t.descTruncGE f n  = f :=
  (t.descTruncGE' f n).choose_spec.symm

lemma isLE_iff_orthogonal (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) :
    t.IsLE X n₀ ↔ ∀ (Y : C) (f : X ⟶ Y) (_ : t.IsGE Y n₁), f = 0 := by
  constructor
  · intro _ Y f _
    exact t.zero f n₀ n₁ (by lia)
  · intro hX
    rw [isLE_iff_isZero_truncGE_obj t n₀ n₁ h, IsZero.iff_id_eq_zero]
    apply t.from_truncGE_obj_ext n₁
    rw [comp_zero, comp_id]
    exact hX _ _ inferInstance

lemma isGE_iff_orthogonal (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) :
    t.IsGE X n₁ ↔ ∀ (Y : C) (f : Y ⟶ X) (_ : t.IsLE Y n₀), f = 0 := by
  constructor
  · intro _ Y f _
    exact t.zero f n₀ n₁ (by lia)
  · intro hX
    rw [isGE_iff_isZero_truncLE_obj t n₀ n₁ h, IsZero.iff_id_eq_zero]
    apply t.to_truncLE_obj_ext n₀
    rw [zero_comp, id_comp]
    exact hX _ _ inferInstance

lemma isLE₂ (T : Triangle C) (hT : T ∈ distTriang C) (n : ℤ) (h₁ : t.IsLE T.obj₁ n)
    (h₃ : t.IsLE T.obj₃ n) : t.IsLE T.obj₂ n := by
  rw [t.isLE_iff_orthogonal n (n+1) rfl]
  intro Y f hY
  obtain ⟨f', hf'⟩ := Triangle.yoneda_exact₂ _ hT f
    (t.zero _ n (n+1) (by lia) )
  rw [hf', t.zero f' n (n+1) (by lia), comp_zero]

lemma isGE₂ (T : Triangle C) (hT : T ∈ distTriang C) (n : ℤ) (h₁ : t.IsGE T.obj₁ n)
    (h₃ : t.IsGE T.obj₃ n) : t.IsGE T.obj₂ n := by
  rw [t.isGE_iff_orthogonal (n-1) n (by lia)]
  intro Y f hY
  obtain ⟨f', hf'⟩ := Triangle.coyoneda_exact₂ _ hT f (t.zero _ (n-1) n (by lia))
  rw [hf', t.zero f' (n-1) n (by lia), zero_comp]

instance : t.minus.IsTriangulated where
  exists_zero := ⟨0, isZero_zero C, 0, inferInstance⟩
  toIsTriangulatedClosed₂ := .mk' (fun T hT ↦ by
    rintro ⟨i₁, hi₁⟩ ⟨i₃, hi₃⟩
    exact ⟨max i₁ i₃, t.isLE₂ T hT _ (t.isLE_of_LE _ _ _ (le_max_left i₁ i₃))
      (t.isLE_of_LE _ _ _ (le_max_right i₁ i₃))⟩)

instance : t.plus.IsTriangulated where
  exists_zero := ⟨0, isZero_zero C, 0, inferInstance⟩
  toIsTriangulatedClosed₂ := .mk' (fun T hT ↦ by
    rintro ⟨i₁, hi₁⟩ ⟨i₃, hi₃⟩
    exact ⟨min i₁ i₃, t.isGE₂ T hT _ (t.isGE_of_GE _ _ _ (min_le_left i₁ i₃))
      (t.isGE_of_GE _ _ _ (min_le_right i₁ i₃))⟩)

instance : t.bounded.IsTriangulated := by
  dsimp [bounded]
  infer_instance

noncomputable def natTransTruncLEOfLE (a b : ℤ) (h : a ≤ b) :
    t.truncLE a ⟶ t.truncLE b :=
  t.natTransTruncLTOfLE (a+1) (b+1) (by lia)

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
  · intro hf
    refine ⟨(t.truncGE n).obj Y, (t.truncGEπ n).app Y,
      (t.truncGEδLT n).app Y ≫ (inv ((t.truncLT n).map f))⟦1⟧',
      isomorphic_distinguished _ (t.triangleLTGE_distinguished n Y) _ ?_, inferInstance⟩
    exact Triangle.isoMk _ _ (asIso ((t.truncLT n).map f)) (Iso.refl _) (Iso.refl _)
  · rintro ⟨Z, g, h, mem, _⟩
    obtain ⟨e, he⟩ := t.triangle_iso_exists
      mem (t.triangleLTGE_distinguished n Y) (Iso.refl _) (n-1) n
      (by dsimp; infer_instance) (by dsimp; infer_instance)
      (by dsimp; infer_instance) (by dsimp; infer_instance)
    suffices ((t.truncLT n).map f) = e.hom.hom₁ by
      rw [this]
      infer_instance
    apply to_truncLT_obj_ext
    refine Eq.trans ?_ e.hom.comm₁
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
  · intro hf
    refine ⟨(t.truncLE n₀).obj Y, (t.truncLEι n₀).app Y,
      inv ((t.truncGE n₁).map g) ≫ (t.truncGEδLE n₀ n₁ hn₁).app Y,
      isomorphic_distinguished _ (t.triangleLEGE_distinguished n₀ n₁ hn₁ Y) _ ?_,
      inferInstance⟩
    refine Iso.symm (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
      (asIso ((t.truncGE n₁).map g)) ?_ ?_ ?_)
    · aesop_cat
    · dsimp
      rw [id_comp]
      exact ((t.truncGEπ n₁).naturality g).symm
    · aesop_cat
  · rintro ⟨X, f, h, mem, _⟩
    obtain ⟨e, he⟩ := t.triangle_iso_exists
      (t.triangleLEGE_distinguished n₀ n₁ hn₁ Y) mem (Iso.refl _) n₀ n₁
      (by dsimp; infer_instance) (by dsimp; infer_instance)
      (by dsimp; infer_instance) (by dsimp; infer_instance)
    suffices ((t.truncGE n₁).map g) = e.hom.hom₃ by
      rw [this]
      infer_instance
    apply from_truncGE_obj_ext
    refine Eq.trans ?_ e.hom.comm₂.symm
    dsimp at he ⊢
    rw [he, id_comp]
    exact ((t.truncGEπ n₁).naturality g).symm

lemma isIso_truncGTmap_iff {Y Z : C} (g : Y ⟶ Z) (n : ℤ) :
    IsIso ((t.truncGT n).map g) ↔
      ∃ (X : C) (f : X ⟶ Y) (h : ((t.truncGT n).obj Z) ⟶ X⟦(1 : ℤ)⟧)
        (_ : Triangle.mk f (g ≫ (t.truncGTπ n).app Z) h ∈ distTriang _), t.IsLE X n :=
  t.isIso_truncGEmap_iff g n (n+1) rfl

instance (X : C) (a b : ℤ) [t.IsLE X b] : t.IsLE ((t.truncLE a).obj X) b := by
  by_cases h : a ≤ b
  · exact t.isLE_of_LE _ _ _ h
  · simp only [not_le] at h
    have : t.IsLE X a := t.isLE_of_LE X b a (by lia)
    apply t.isLE_of_iso (show X ≅ _ from (asIso ((t.truncLEι a).app X)).symm)

instance (X : C) (a b : ℤ) [t.IsLE X b] : t.IsLE ((t.truncLT a).obj X) b :=
  t.isLE_of_iso ((t.truncLEIsoTruncLT (a-1) a (by lia)).app X) b

instance (X : C) (a b : ℤ) [t.IsGE X a] : t.IsGE ((t.truncGE b).obj X) a := by
  by_cases h : a ≤ b
  · exact t.isGE_of_GE _ _ _ h
  · simp only [not_le] at h
    have : t.IsGE X b := t.isGE_of_GE X b a (by lia)
    apply t.isGE_of_iso (show X ≅ _ from asIso ((t.truncGEπ b).app X))

instance (X : C) (a b : ℤ) [t.IsGE X a] : t.IsGE ((t.truncGT b).obj X) a :=
  t.isGE_of_iso ((t.truncGTIsoTruncGE b (b+1) (by lia)).symm.app X) a

noncomputable def truncGELT (a b : ℤ) : C ⥤ C := t.truncLT b ⋙ t.truncGE a

noncomputable def truncLTGE (a b : ℤ) : C ⥤ C := t.truncGE a ⋙ t.truncLT b

noncomputable def truncLEGE (a b : ℤ) : C ⥤ C := t.truncGE a ⋙ t.truncLE b

noncomputable def truncGELE (a b : ℤ) : C ⥤ C := t.truncLE b ⋙ t.truncGE a

noncomputable def truncGELEIsoTruncGELT (a b b' : ℤ) (hb' : b + 1 = b') :
    t.truncGELE a b ≅ t.truncGELT a b' :=
  isoWhiskerRight (t.truncLEIsoTruncLT b b' hb') _

/- Now, we need the octahedron axiom -/

variable [IsTriangulated C]

lemma isIso₁_truncLE_map_of_GE (T : Triangle C) (hT : T ∈ distTriang C)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (h₃ : t.IsGE T.obj₃ n₁) :
    IsIso ((t.truncLE n₀).map T.mor₁) := by
  rw [isIso_truncLEmap_iff _ _ _ _ h]
  obtain ⟨Z, g, k, mem⟩ := distinguished_cocone_triangle ((t.truncLEι n₀).app T.obj₁ ≫ T.mor₁)
  refine ⟨_, _, _, mem, ?_⟩
  have H := someOctahedron rfl (t.triangleLEGE_distinguished n₀ n₁ h T.obj₁) hT mem
  exact t.isGE₂ _ H.mem n₁ (by dsimp; infer_instance) (by dsimp; infer_instance)

lemma isIso₁_truncLT_map_of_GE (T : Triangle C) (hT : T ∈ distTriang C)
    (n : ℤ) (h₃ : t.IsGE T.obj₃ n) : IsIso ((t.truncLT n).map T.mor₁) := by
  rw [← NatIso.isIso_map_iff (t.truncLEIsoTruncLT (n-1) n (by lia))]
  exact t.isIso₁_truncLE_map_of_GE T hT (n-1) n (by lia) h₃

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
  have := t.isIso₁_truncLE_map_of_GE _ ((t.triangleLEGE_distinguished b (b+1) rfl X))
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

instance (i : EInt) : (t.truncGEt.obj i).Additive := by
  induction i <;> constructor <;> cat_disch

instance (i : EInt) : (t.truncLTt.obj i).Additive := by
  induction i <;> constructor <;> cat_disch

omit [IsTriangulated C] in
lemma isZero_truncLTt_obj_obj (X : C) (n : ℤ) [t.IsGE X n] (j : EInt) (hj : j ≤ EInt.mk n) :
    IsZero ((t.truncLTt.obj j).obj X) := by
  induction j with
  | bot => simp
  | coe j =>
    dsimp
    rw [← t.isGE_iff_isZero_truncLT_obj]
    exact t.isGE_of_GE  _ _ _ (by simpa using hj)
  | top => simp at hj

omit [IsTriangulated C] in
lemma isZero_truncGEt_obj_obj (X : C) (n : ℤ) [t.IsLE X n] (j : EInt) (hj : EInt.mk n < j) :
    IsZero ((t.truncGEt.obj j).obj X) := by
  induction j with
  | bot => simp at hj
  | coe j =>
    simp only [EInt.coe_lt_coe_iff] at hj
    dsimp
    rw [← t.isLE_iff_isZero_truncGE_obj (j - 1) j (by simp)]
    exact t.isLE_of_LE X n (j - 1) (by lia)
  | top => simp

omit [IsTriangulated C] in
lemma truncGEt_obj_obj_isGE (n : ℤ) (i : EInt) (h : EInt.mk n ≤ i) (X : C) :
    t.IsGE ((t.truncGEt.obj i).obj X) n := by
  induction i with
  | bot => simp at h
  | coe i =>
    dsimp
    exact t.isGE_of_GE  _ _ _ (by simpa using h)
  | top => exact t.isGE_of_isZero _ (Functor.zero_obj _) _

omit [IsTriangulated C] in
lemma truncLTt_obj_obj_isLE (n : ℤ) (i : EInt) (h : i ≤ EInt.mk (n + 1)) (X : C) :
    t.IsLE (((t.truncLTt.obj i)).obj X) n := by
  induction i with
  | bot => exact t.isLE_of_isZero _ (by simp) _
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
  t.isIso₁_truncLT_map_of_GE _ (t.triangleLTGE_distinguished b X) a
    (t.isGE_of_GE ((t.truncGE b).obj X) a b (by lia))

lemma isIso_truncLE_map_truncLEι_app (a b : ℤ) (h : a ≤ b) (X : C) :
    IsIso ((t.truncLE a).map ((t.truncLEι b).app X)) := by
  apply isIso_truncLT_map_truncLTι_app
  lia

instance (X : C) (n : ℤ) : IsIso ((t.truncLE n).map ((t.truncLEι n).app X)) :=
  t.isIso_truncLE_map_truncLEι_app _ _ (by rfl) _

instance (X : C) (n : ℤ) : IsIso ((t.truncGE n).map ((t.truncGEπ n).app X)) :=
  t.isIso_truncGE_map_truncGEπ_app _ _ (by rfl) _

lemma isIso_truncGEt_obj_map_truncGEπ_app (a b : EInt) (h : a ≤ b) (X : C) :
    IsIso ((t.truncGEt.obj b).map ((t.abstractSpectralObject.truncGEπ a).app X)) := by
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

lemma isIso_truncLTt_obj_map_truncLTπ_app (a b : EInt) (h : a ≤ b) (X : C) :
    IsIso ((t.truncLTt.obj a).map ((t.abstractSpectralObject.truncLTι b).app X)) := by
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
    t.isIso_truncGEt_obj_map_truncGEπ_app _ _ (leOfHom D.hom) X

instance (D : Arrow EInt) (X : C) :
  IsIso ((t.abstractSpectralObject.truncLTLTToTruncLT.app D).app X) :=
    t.isIso_truncLTt_obj_map_truncLTπ_app _ _ (leOfHom D.hom) X

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
    simp only [abstractSpectralObject_truncGE, truncGEt_obj_mk, id_obj,
      AbstractSpectralObject.truncGEπ_mk]
    apply from_truncGE_obj_ext
    exact ((t.truncGEπ a).naturality ((t.truncGEπ a).app X)).symm
  | top => exact IsZero.eq_of_src (by simp) _ _

omit [IsTriangulated C] in
lemma truncLTι_compatibility (a : EInt) (X : C) :
    (t.abstractSpectralObject.truncLT.obj a).map ((t.abstractSpectralObject.truncLTι a).app X) =
      (t.abstractSpectralObject.truncLTι a).app
        ((t.abstractSpectralObject.truncLT.obj a).obj X) := by
  induction a with
  | bot => exact IsZero.eq_of_src (by simp) _ _
  | coe a =>
    simp only [abstractSpectralObject_truncLT, truncLTt_obj_mk, id_obj,
      AbstractSpectralObject.truncLEι_mk]
    apply to_truncLT_obj_ext
    exact (t.truncLTι a).naturality ((t.truncLTι a).app X)
  | top => simp

lemma isIso_truncLTι_app_truncGELT_obj (a b : EInt) (h : a ≤ b) (X : C) :
    IsIso ((t.abstractSpectralObject.truncLTι b).app
      ((t.truncLTt.obj b ⋙ t.truncGEt.obj a).obj X)) := by
  induction b with
  | bot =>
    refine ⟨0, IsZero.eq_of_src (by simp) _ _, IsZero.eq_of_src ?_ _ _⟩
    dsimp
    exact IsZero.of_iso (isZero_zero _)
        (Functor.mapIso _ (IsZero.isoZero (Functor.zero_obj _)) ≪≫
          (t.truncGEt.obj a).mapZeroObject)
  | coe b =>
    simp only [abstractSpectralObject_truncLT, truncLTt_obj_mk, comp_obj, id_obj,
      AbstractSpectralObject.truncLEι_mk]
    rw [← t.isLE_iff_isIso_truncLTι_app (b-1) b (by lia)]
    induction a with
    | bot => dsimp; infer_instance
    | coe a => dsimp; infer_instance
    | top => exact t.isLE_of_isZero _ (by simp) _
  | top =>
    simp only [abstractSpectralObject_truncLT, truncLTt_obj_top, comp_obj, id_obj,
      AbstractSpectralObject.truncLTι_top_app]
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
  whiskerLeft (t.truncLT b) (t.truncGEδLT a) ≫
    whiskerRight (t.truncLTι b) (t.truncLT a ⋙ shiftFunctor C (1 : ℤ))

@[simps!]
noncomputable def triangleLTLTGELT (a b : ℤ) (h : a ≤ b) : C ⥤ Triangle C :=
  Triangle.functorMk (t.natTransTruncLTOfLE a b h)
    (whiskerLeft (t.truncLT b) (t.truncGEπ a)) (t.truncGELTδLT a b)

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
    have := t.isIso₁_truncLT_map_of_GE _ H.mem b (by dsimp; infer_instance)
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
      t.to_truncLT_obj_ext _ _ _ _ (by simp [truncGELT])
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
      simp only [truncGEt_obj_mk, AbstractSpectralObject.truncLEι_mk]
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

namespace ObjectProperty

open Triangulated

/-- Constructor for `HasInducedTStructure`. -/
lemma HasInducedTStructure.mk' {P : ObjectProperty C} [P.IsTriangulated] {t : TStructure C}
    (h : ∀ (X : C) (_ : P X) (n : ℤ), P ((t.truncLE n).obj X) ∧
      P ((t.truncGE n).obj X)) :
    P.HasInducedTStructure t where
  exists_triangle_zero_one X hX :=
      ⟨_, _, inferInstance, inferInstance, _, _, _,
        t.triangleLEGE_distinguished 0 1 (by omega) X,
          P.le_isoClosure _ ((h X hX _).1), P.le_isoClosure _ ((h X hX _).2)⟩

lemma mem_of_hasInductedTStructure (P : ObjectProperty C) [P.IsTriangulated] (t : TStructure C)
    [P.IsClosedUnderIsomorphisms] [P.HasInducedTStructure t]
    (T : Triangle C) (hT : T ∈ distTriang C)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (h₁ : t.IsLE T.obj₁ n₀) (h₂ : P T.obj₂)
    (h₃ : t.IsGE T.obj₃ n₁) :
    P T.obj₁ ∧ P T.obj₃ := by
  obtain ⟨e, _⟩ := t.triangle_iso_exists hT
    (P.ι.map_distinguished _ ((P.tStructure t).triangleLEGE_distinguished n₀ n₁ h ⟨_, h₂⟩))
    (Iso.refl _) n₀ n₁ inferInstance inferInstance (by
      dsimp [-ι_obj]
      rw [← P.tStructure_isLE_iff]
      infer_instance) (by
      dsimp [-ι_obj]
      rw [← P.tStructure_isGE_iff]
      infer_instance)
  exact ⟨(P.prop_iff_of_iso (Triangle.π₁.mapIso e)).2 (P.prop_ι_obj _),
    (P.prop_iff_of_iso (Triangle.π₃.mapIso e)).2 (P.prop_ι_obj _)⟩

instance (P P' : ObjectProperty C) [P.IsTriangulated] [P'.IsTriangulated] (t : TStructure C)
    [P.HasInducedTStructure t] [P'.HasInducedTStructure t]
    [P.IsClosedUnderIsomorphisms] [P'.IsClosedUnderIsomorphisms] :
    (P ⊓ P').HasInducedTStructure t :=
  .mk' (by
    rintro X ⟨hX, hX'⟩ n
    exact
      ⟨⟨(P.mem_of_hasInductedTStructure t _ (t.triangleLEGE_distinguished n _ rfl X) n _ rfl
        (by dsimp; infer_instance) hX (by dsimp; infer_instance)).1,
      (P'.mem_of_hasInductedTStructure t _ (t.triangleLEGE_distinguished n _ rfl X) n _ rfl
        (by dsimp; infer_instance) hX' (by dsimp; infer_instance)).1⟩,
        ⟨(P.mem_of_hasInductedTStructure t _ (t.triangleLEGE_distinguished (n - 1) n (by omega) X)
        (n - 1) n (by omega) (by dsimp; infer_instance) hX (by dsimp; infer_instance)).2,
      (P'.mem_of_hasInductedTStructure t _ (t.triangleLEGE_distinguished (n - 1) n (by omega) X)
        (n - 1) n (by omega) (by dsimp; infer_instance) hX' (by dsimp; infer_instance)).2⟩⟩)

end ObjectProperty

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

instance (X : C) (n : ℤ) [t.IsLE X n] (i : EInt) :
    t.IsLE ((t.truncLTt.obj i).obj X) n := by
  induction i with
  | bot => exact isLE_of_isZero _ _ (by simp) _
  | coe _ => dsimp; infer_instance
  | top => dsimp; infer_instance

instance [IsTriangulated C] (X : C) (n : ℤ) [t.IsGE X n] (i : EInt) :
    t.IsGE ((t.truncLTt.obj i).obj X) n := by
  induction i with
  | bot => exact isGE_of_isZero _ _ (by simp) _
  | coe _ => dsimp; infer_instance
  | top => dsimp; infer_instance

instance [IsTriangulated C] (X : C) (n : ℤ) [t.IsLE X n] (i : EInt) :
    t.IsLE ((t.truncGEt.obj i).obj X) n := by
  induction i with
  | bot => dsimp; infer_instance
  | coe _ => dsimp; infer_instance
  | top => exact isLE_of_isZero _ _ (by simp) _

instance (X : C) (n : ℤ) [t.IsGE X n] (i : EInt) :
    t.IsGE ((t.truncGEt.obj i).obj X) n := by
  induction i with
  | bot => dsimp; infer_instance
  | coe _ => dsimp; infer_instance
  | top => exact isGE_of_isZero _ _ (by simp) _

end TStructure

end Triangulated

end CategoryTheory
