/-
Copyright (c) 2021 Luke Kershaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Kershaw, Joël Riou
-/
import Mathlib.CategoryTheory.Triangulated.Filtered.TruncationDef

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

/-
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
  | some (some a), none => fun _ => t.truncLTι a
  | none, some none  => fun _ => 0
  | none, some (some b) => fun _ => 0
  | none, none => fun _ => 𝟙 _

end TruncLTt

noncomputable def truncLTt : ℤt ⥤ C ⥤ C where
  obj := TruncLTt.obj t
  map φ := TruncLTt.map t φ
  map_id := by
    rintro (_|_|_)
    · rfl
    · rfl
    · dsimp [TruncLTt.map]
      rw [t.natTransTruncLTOfLE_refl]
      rfl
  map_comp {a b c} hab hbc := by
    replace hab := leOfHom hab
    replace hbc := leOfHom hbc
    obtain (_|_|_) := a <;> obtain (_|_|_) := b <;> obtain (_|_|_) := c
    all_goals simp (config := {failIfUnchanged := false}) at hbc hab <;>
      dsimp [TruncLTt.map] <;> simp

@[simp]
lemma truncLTt_obj_top : t.truncLTt.obj ⊤ = 𝟭 _ := rfl

@[simp]
lemma truncLTt_obj_bot : t.truncLTt.obj ⊥ = 0 := rfl

@[simp]
lemma truncLTt_obj_mk (n : ℤ) : t.truncLTt.obj (ℤt.mk n) = t.truncLT n := rfl

@[simp]
lemma truncLTt_map_eq_truncLTι (n : ℤ) :
    t.truncLTt.map (homOfLE (show ℤt.mk n ≤ ⊤ by simp)) = t.truncLTι n := rfl

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
    · rfl
    · rfl
    · dsimp [TruncGEt.map]
      rw [natTransTruncGEOfLE_refl]
      rfl
  map_comp {a b c} hab hbc := by
    replace hab := leOfHom hab
    replace hbc := leOfHom hbc
    obtain (_|_|_) := a <;> obtain (_|_|_) := b <;> obtain (_|_|_) := c
    all_goals simp (config := {failIfUnchanged := false}) at hbc hab <;>
      dsimp [TruncGEt.map] <;> simp

@[simp]
lemma truncGEt_obj_bot :
    t.truncGEt.obj ⊥ = 𝟭 _ := rfl

@[simp]
lemma truncGEt_obj_top :
    t.truncGEt.obj ⊤ = 0 := rfl

@[simp]
lemma truncGEt_obj_mk (n : ℤ) : t.truncGEt.obj (ℤt.mk n) = t.truncGE n := rfl

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
    · apply IsZero.eq_of_src
      exact isZero_zero _
    all_goals obtain (_|_|b) := b <;> simp (config := {failIfUnchanged := false}) at hab <;>
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

noncomputable def triangleLTGEIso (n : ℤ) (X : C) :
    (t.abstractSpectralObject.triangleLTGE.obj (ℤt.mk n)).obj X ≅
      (t.triangleLTGE n).obj X := by
  refine' Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) _ _ _
  all_goals aesop_cat

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
  refine' Triangle.isoMk _ _ (((abstractSpectralObject t).truncLTObjTopIso).app X)
    (Iso.refl _) (isZero_truncLT_obj_bot_obj t X).isoZero _ _ _
  · dsimp
    rw [truncLTι_top_app]
  · exact IsZero.eq_of_tgt (isZero_zero _) _ _
  · refine' IsZero.eq_of_src _ _ _
    exact IsZero.obj (isZero_zero _) _

noncomputable def triangleLTGEBotIso (X : C) :
  (t.abstractSpectralObject.triangleLTGE.obj ⊥).obj X ≅
    (Pretriangulated.contractibleTriangle X).invRotate := by
  refine' Triangle.isoMk _ _ ((isZero_truncLT_obj_bot_obj t X).isoZero ≪≫
    (shiftFunctor C (-1 : ℤ)).mapZeroObject.symm)
    (((abstractSpectralObject t).truncLTObjTopIso).app X) (Iso.refl _) _ _ _
  · apply IsZero.eq_of_src
    apply isZero_truncLT_obj_bot_obj
  · dsimp
    rw [truncGEπ_bot_app]
  · apply IsZero.eq_of_tgt _
    dsimp
    rw [IsZero.iff_id_eq_zero, ← Functor.map_id, ← Functor.map_id, id_zero,
      Functor.map_zero, Functor.map_zero]

lemma distinguished (n : ℤt) (X : C) :
  (t.abstractSpectralObject.triangleLTGE.obj n).obj X ∈ distTriang C := by
  obtain (_|_|n) := n
  · exact isomorphic_distinguished _ (contractible_distinguished X) _
      (triangleLTGETopIso t X)
  · exact isomorphic_distinguished _
      (inv_rot_of_distTriang _ (contractible_distinguished X)) _
      (triangleLTGEBotIso t X)
  · exact isomorphic_distinguished _ (t.triangleLTGE_distinguished n X) _
      (triangleLTGEIso t n X)

end AbstractSpectralObject
-/

lemma isZero_truncLE_obj_zero (n : ℤ) : IsZero ((hP.truncLE n).obj 0) := by
  let δ := (hP.truncLEδGE n (n+1) rfl).app 0
  have : IsIso δ := by
    have h := (hP.triangleGELE_distinguished n (n+1) rfl 0)
    exact (Triangle.isZero₂_iff_isIso₃ _ h).1
      ((Triangle.isZero₂_iff _ (hP.triangleGELE_distinguished n (n+1) rfl 0)).2
        ⟨(isZero_zero C).eq_of_tgt _ _, (isZero_zero C).eq_of_src _ _⟩)
  have : IsGE ((truncGE (n + 1) ⋙ shiftFunctor C (1 : ℤ)).obj 0) (n + 1) := by
    simp only [Functor.comp_obj]
    exact shift_isGE_of_isGE _ _ _
  have hδ := hP.zero_of_isGE_of_isLE δ n (n+1) (by linarith)
    (hP.isGE_of_iso (asIso δ).symm _) (hP.isLE_of_iso (asIso δ) _)
  rw [IsZero.iff_id_eq_zero]
  rw [← cancel_mono δ, zero_comp, hδ, comp_zero]

lemma isZero_truncGE_obj_zero (n : ℤ) : IsZero ((hP.truncGE n).obj 0) := by
  apply (Triangle.isZero₁_iff_isIso₂ _ (hP.triangleGELE_distinguished (n-1) n (by linarith) 0)).2
  simp only [Int.reduceNeg, Int.rawCast, Int.cast_id, Nat.rawCast, Int.Nat.cast_ofNat_Int,
    Int.reduceAdd, Int.ofNat_eq_coe, Nat.cast_id, eq_mp_eq_cast, triangleGELE_obj_obj₂,
    triangleGELE_obj_obj₃, triangleGELE_obj_mor₂]
  refine ⟨0, by simp only [comp_zero, id_zero], ?_⟩
  rw [(Limits.IsZero.iff_id_eq_zero _).mp (hP.isZero_truncLE_obj_zero (n-1)), zero_comp]

instance (n : ℤ) : hP.IsLE (0 : C) n := hP.isLE_of_iso (hP.isZero_truncLE_obj_zero n).isoZero n
instance (n : ℤ) : hP.IsGE (0 : C) n := hP.isGE_of_iso (hP.isZero_truncGE_obj_zero n).isoZero n

lemma isLE_of_isZero (X : C) (hX : IsZero X) (n : ℤ) : hP.IsLE X n :=
  hP.isLE_of_iso hX.isoZero.symm n

lemma isGE_of_isZero (X : C) (hX : IsZero X) (n : ℤ) : hP.IsGE X n :=
  hP.isGE_of_iso hX.isoZero.symm n

lemma isLE_iff_isIso_truncLEπ_app (n : ℤ) (X : C) :
    hP.IsLE X n ↔ IsIso ((hP.truncLEπ n).app X) := by
  constructor
  · intro
    obtain ⟨e, he⟩ := hP.triangle_iso_exists n (n+1) (by linarith) _ _
      (contractible_distinguished₁ X) (hP.triangleGTLE_distinguished n X)
      (Iso.refl X) (by dsimp ; infer_instance)
      (by dsimp ; infer_instance) (by dsimp ; infer_instance) (by dsimp ; infer_instance)
    dsimp at he
    have : (truncLEπ n).app X = e.hom.hom₃ := by
      simpa [he] using e.hom.comm₂.symm
    rw [this]
    infer_instance
  · intro
    exact hP.isLE_of_iso (asIso ((truncLEπ n).app X)).symm n

lemma isLE_iff_isIso_truncLTπ_app (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) (X : C) :
    hP.IsLE X n₀ ↔ IsIso (((hP.truncLTπ n₁)).app X) := by
  rw [isLE_iff_isIso_truncLEπ_app]
  subst hn₁
  rfl

lemma isGE_iff_isIso_truncGEι_app (n : ℤ) (X : C) :
    hP.IsGE X n ↔ IsIso ((hP.truncGEι n).app X) := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := hP.triangle_iso_exists (n-1) n (by linarith) _ _
      (contractible_distinguished X)
      (hP.triangleGELT_distinguished n X) (Iso.refl X) h
      (by dsimp ; infer_instance) (by dsimp ; infer_instance) (by dsimp ; infer_instance)
    dsimp at he
    have : (truncGEι n).app X = e.inv.hom₁ := by
      have eq := e.inv.comm₁
      dsimp at eq
      apply_fun (fun x ↦ x ≫ e.hom.hom₂) at eq
      simp only [triangleGELT_obj_obj₂, contractibleTriangle_obj₂, assoc,
        Iso.inv_hom_id_triangle_hom₂, comp_id] at eq
      rw [eq, he, comp_id]
    rw [this]
    infer_instance
  · intro
    exact hP.isGE_of_iso (asIso ((truncGEι n).app X)) n

instance (X : C) (n : ℤ) [hP.IsLE X n] : IsIso ((hP.truncLEπ n).app X) := by
  rw [← isLE_iff_isIso_truncLEπ_app ]
  infer_instance

instance (X : C) (n : ℤ) [hP.IsGE X n] : IsIso ((hP.truncGEι n).app X) := by
  rw [← isGE_iff_isIso_truncGEι_app ]
  infer_instance

lemma isLE_iff_isZero_truncGT_obj (n : ℤ) (X : C) :
    hP.IsLE X n ↔ IsZero ((hP.truncGT n).obj X) := by
  rw [hP.isLE_iff_isIso_truncLEπ_app n X]
  exact (Triangle.isZero₁_iff_isIso₂ _ (hP.triangleGTLE_distinguished n X)).symm

lemma isGE_iff_isZero_truncLT_obj (n : ℤ) (X : C) :
    hP.IsGE X n ↔ IsZero ((hP.truncLT n).obj X) := by
  rw [hP.isGE_iff_isIso_truncGEι_app n X]
  exact (Triangle.isZero₃_iff_isIso₁ _ (hP.triangleGELT_distinguished n X)).symm

lemma isLE_iff_isZero_truncGE_obj (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) :
    hP.IsLE X n₀ ↔ IsZero ((hP.truncGE n₁).obj X) := by
  rw [hP.isLE_iff_isIso_truncLEπ_app n₀ X]
  exact (Triangle.isZero₁_iff_isIso₂ _ (hP.triangleGELE_distinguished n₀ n₁ h X)).symm

lemma isGE_iff_isZero_truncLE_obj (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) :
    hP.IsGE X n₁ ↔ IsZero ((hP.truncLE n₀).obj X) := by
  rw [hP.isGE_iff_isIso_truncGEι_app n₁ X]
  exact (Triangle.isZero₃_iff_isIso₁ _ (hP.triangleGELE_distinguished n₀ n₁ h X)).symm

lemma isZero_truncGE_obj_of_isLE (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) [hP.IsLE X n₀] :
    IsZero ((hP.truncGE n₁).obj X) := by
  rw [← hP.isLE_iff_isZero_truncGE_obj _ _ h X]
  infer_instance

lemma isZero_truncLE_obj_of_isGE (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) [hP.IsGE X n₁] :
    IsZero ((hP.truncLE n₀).obj X) := by
  rw [← hP.isGE_iff_isZero_truncLE_obj _ _ h X]
  infer_instance

lemma isLE_iff_orthogonal (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) :
    hP.IsLE X n₀ ↔ ∀ (Y : C) (f : Y ⟶ X) (_ : hP.IsGE Y n₁), f = 0 := by
  constructor
  · intro _ Y f _
    exact hP.zero f n₀ n₁ (by linarith)
  · intro hX
    rw [isLE_iff_isZero_truncGE_obj n₀ n₁ h, IsZero.iff_id_eq_zero]
    apply to_truncGE_obj_ext n₁
    rw [zero_comp, id_comp]
    exact hX _ _ inferInstance

lemma isGE_iff_orthogonal (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) :
    hP.IsGE X n₁ ↔ ∀ (Y : C) (f : X ⟶ Y) (_ : hP.IsLE Y n₀), f = 0 := by
  constructor
  · intro _ Y f _
    exact zero f n₀ n₁ (by linarith)
  · intro hX
    rw [isGE_iff_isZero_truncLE_obj n₀ n₁ h, IsZero.iff_id_eq_zero]
    apply from_truncLE_obj_ext n₀
    rw [comp_zero, comp_id]
    exact hX _ _ inferInstance

noncomputable def natTransTruncLEOfGE (a b : ℤ) (h : b ≤ a) :
    hP.truncLE a ⟶ hP.truncLE b :=
  natTransTruncLTOfGE (a+1) (b+1) (by linarith)

@[reassoc (attr := simp)]
lemma π_natTransTruncLEOfGE_app (n₀ n₁ : ℤ) (h : n₁ ≤ n₀) (X : C) :
    (truncLEπ n₀).app X ≫ (hP.natTransTruncLEOfGE n₀ n₁ h).app X =
      (truncLEπ n₁).app X :=
  natTransTruncLTOfGE_π_app _ _ _ _

@[reassoc (attr := simp)]
lemma π_natTransTruncLEOfGE (a b : ℤ) (h : b ≤ a) :
    truncLEπ a ≫ hP.natTransTruncLEOfGE a b h = truncLEπ b := by aesop_cat

@[simp]
lemma natTransTruncLEOfGE_refl (a : ℤ) :
    hP.natTransTruncLEOfGE a a (by rfl) = 𝟙 _ :=
  natTransTruncLTOfGE_refl _

@[simp]
lemma natTransTruncLEOfGE_trans (a b c : ℤ) (hab : b ≤ a) (hbc : c ≤ b) :
    hP.natTransTruncLEOfGE a b hab ≫ hP.natTransTruncLEOfGE b c hbc =
      hP.natTransTruncLEOfGE a c (hbc.trans hab) :=
  natTransTruncLTOfGE_trans _ _ _ _ _

@[simp]
lemma natTransTruncLEOfGE_refl_app (a : ℤ) (X : C) :
    (natTransTruncLEOfGE a a (by rfl)).app X = 𝟙 _ :=
  congr_app (natTransTruncLEOfGE_refl a) X

@[reassoc (attr := simp)]
lemma natTransTruncLEOfGE_trans_app (a b c : ℤ) (hab : b ≤ a) (hbc : c ≤ b) (X : C) :
    (natTransTruncLEOfGE a b hab).app X ≫ (natTransTruncLEOfGE b c hbc).app X =
      (natTransTruncLEOfGE a c (hbc.trans hab)).app X :=
  congr_app (natTransTruncLEOfGE_trans a b c hab hbc) X

lemma isIso_truncLTmap_iff {X Y : C} (g : X ⟶ Y) (n : ℤ) :
    IsIso ((truncLT n).map g) ↔
      ∃ (Z : C) (f : Z ⟶ X) (h : ((truncLT n).obj Y) ⟶ Z⟦(1 : ℤ)⟧)
        (_ : Triangle.mk f (g ≫ (truncLTπ n).app Y) h ∈ distTriang _), IsGE Z n := by
  constructor
  · intro hg
    refine ⟨(truncGE n).obj X, (truncGEι n).app X,
      inv ((truncLT n).map g) ≫ (truncLTδGE n).app X,
      isomorphic_distinguished _ (triangleGELT_distinguished n X) _ ?_, inferInstance⟩
    refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (asIso ((truncLT n).map g)).symm (by simp)
      ?_ (by simp)
    simp only [Triangle.mk_obj₂, triangleGELT_obj_obj₃, Triangle.mk_obj₃, Triangle.mk_mor₂,
      Iso.symm_hom, asIso_inv, assoc, triangleGELT_obj_obj₂, Iso.refl_hom, triangleGELT_obj_mor₂,
      id_comp]
    rw [← cancel_mono ((truncLT n).map g)]
    simp only [assoc, IsIso.inv_hom_id, comp_id]
    have := (truncLTπ n).naturality g
    simp only [Functor.id_obj, Functor.id_map] at this
    exact this
  · rintro ⟨Z, f, h, mem, _⟩
    obtain ⟨e, he⟩ := triangle_iso_exists (n-1) n (by linarith)  _ _ mem
      (triangleGELT_distinguished n X) (Iso.refl _)
      (by dsimp ; infer_instance) (by dsimp ; infer_instance)
      (by dsimp ; infer_instance) (by dsimp ; infer_instance)
    suffices ((truncLT n).map g) = e.inv.hom₃ by
      rw [this]
      infer_instance
    apply from_truncLT_obj_ext
    refine Eq.trans ?_ e.inv.comm₂.symm
    rw [← cancel_epi e.hom.hom₂]
    simp only [Triangle.mk_obj₂, triangleGELT_obj_obj₂, Functor.id_obj, Triangle.mk_obj₃,
      Triangle.mk_mor₂, Iso.hom_inv_id_triangle_hom₂_assoc]
    have := (truncLTπ n).naturality g
    simp only [Functor.id_obj, Functor.id_map] at this
    rw [← this, he, Iso.refl_hom]; erw [id_comp]

lemma isIso_truncLEmap_iff {X Y : C} (g : X ⟶ Y) (a b : ℤ) (h : a + 1 = b) :
    IsIso ((truncLE a).map g) ↔
      ∃ (Z : C) (f : Z ⟶ X) (h : ((truncLE a).obj Y) ⟶ Z⟦1⟧)
        (_ : Triangle.mk f (g ≫ (truncLEπ a).app Y) h ∈ distTriang _), IsGE Z b := by
  subst h
  apply isIso_truncLTmap_iff

lemma isIso_truncGEmap_iff {Y Z : C} (f : Y ⟶ Z) (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) :
    IsIso ((truncGE n₁).map f) ↔
      ∃ (X : C) (g : Z ⟶ X) (h : X ⟶ ((truncGE n₁).obj Y)⟦(1 : ℤ)⟧)
        (_ : Triangle.mk ((truncGEι n₁).app Y ≫ f) g h ∈ distTriang _), IsLE X n₀ := by
  constructor
  · intro hf
    refine ⟨(truncLE n₀).obj Z, (truncLEπ n₀).app Z,
      (truncLEδGE n₀ n₁ hn₁).app Z ≫ inv ((truncGE n₁).map f)⟦1⟧',
      isomorphic_distinguished _ (triangleGELE_distinguished n₀ n₁ hn₁ Z) _ ?_,
      inferInstance⟩
    exact Triangle.isoMk _ _ (asIso ((truncGE n₁).map f)) (Iso.refl _) (Iso.refl _) (by aesop_cat)
      (by aesop_cat) (by aesop_cat)
  · rintro ⟨X, g, h, mem, _⟩
    obtain ⟨e, he⟩ := triangle_iso_exists n₀ n₁ (by linarith) _ _ mem
      (triangleGELE_distinguished n₀ n₁ hn₁ Z) (Iso.refl _)
      (by dsimp ; infer_instance) (by dsimp ; infer_instance)
      (by dsimp ; infer_instance) (by dsimp ; infer_instance)
    suffices ((truncGE n₁).map f) = e.hom.hom₁ by
      rw [this]
      infer_instance
    apply to_truncGE_obj_ext
    refine Eq.trans ?_ e.hom.comm₁
    dsimp at he ⊢
    rw [he, comp_id]
    exact (truncGEι n₁).naturality f

lemma isIso_truncGTmap_iff {Y Z : C} (f : Y ⟶ Z) (n : ℤ) :
    IsIso ((truncGT n).map f) ↔
      ∃ (X : C) (g : Z ⟶ X) (h : X ⟶ ((truncGT n).obj Y)⟦(1 : ℤ)⟧)
        (_ : Triangle.mk ((truncGTι n).app Y ≫ f) g h ∈ distTriang _), IsLE X n :=
  isIso_truncGEmap_iff f n (n+1) rfl

instance (X : C) (a b : ℤ) [IsLE X b] : IsLE ((truncLE a).obj X) b := by
  by_cases h : a ≤ b
  · exact isLE_of_LE _ _ _ h
  · simp only [not_le] at h
    have : IsLE X a := isLE_of_LE X b a (by linarith)
    apply isLE_of_iso (show X ≅ _ from (asIso ((truncLEπ a).app X)))

instance (X : C) (a b : ℤ) [IsLE X b] : IsLE ((truncLT a).obj X) b :=
  isLE_of_iso ((truncLEIsoTruncLT (a-1) a (by linarith)).app X) b

instance (X : C) (a b : ℤ) [IsGE X a] : IsGE ((truncGE b).obj X) a := by
  by_cases h : a ≤ b
  · exact isGE_of_GE _ _ _ h
  · simp only [not_le] at h
    have : IsGE X b := isGE_of_GE X b a (by linarith)
    apply isGE_of_iso (show X ≅ _ from (asIso ((truncGEι b).app X)).symm)

instance (X : C) (a b : ℤ) [IsGE X a] : IsGE ((truncGT b).obj X) a :=
  isGE_of_iso ((truncGTIsoTruncGE b (b+1) (by linarith)).symm.app X) a

noncomputable def truncGELT (a b : ℤ) : C ⥤ C := truncLT b ⋙ truncGE a

noncomputable def truncLTGE (a b : ℤ) : C ⥤ C := truncGE a ⋙ truncLT b

noncomputable def truncLEGE (a b : ℤ) : C ⥤ C := truncGE a ⋙ truncLE b

noncomputable def truncGELE (a b : ℤ) : C ⥤ C := truncLE b ⋙ truncGE a

noncomputable def truncGELEIsoTruncGELT (a b b' : ℤ) (hb' : b + 1 = b') :
    truncGELE a b (C := C) ≅ truncGELT a b' :=
  isoWhiskerRight (truncLEIsoTruncLT b b' hb') _

/- Now, we need the octahedron axiom -/

variable [IsTriangulated C]

lemma isIso₁_truncGE_map_of_LE (T : Triangle C) (hT : T ∈ distTriang C)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (h₃ : IsLE T.obj₃ n₀) :
    IsIso ((truncGE n₁).map T.mor₁) := by
  change IsIso ((truncGE n₁).mapTriangle.obj T).mor₁
  rw [← Triangle.isZero₃_iff_isIso₁ _ ((truncGE n₁).map_distinguished _ hT)]
  simp only [Functor.mapTriangle_obj, Triangle.mk_obj₃]
  rw [← isLE_iff_isZero_truncGE_obj (h := h)]
  assumption

lemma isIso₁_truncGT_map_of_LE (T : Triangle C) (hT : T ∈ distTriang C)
    (n : ℤ) (h₃ : IsLE T.obj₃ n) : IsIso ((truncGT n).map T.mor₁) := by
  rw [← NatIso.isIso_map_iff (truncGTIsoTruncGE n (n + 1) (by linarith)).symm]
  exact isIso₁_truncGE_map_of_LE T hT n (n + 1) (by linarith) h₃

lemma isIso₂_truncLE_map_of_GE (T : Triangle C) (hT : T ∈ distTriang C)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (h₁ : IsGE T.obj₁ n₁) :
    IsIso ((truncLE n₀).map T.mor₂) := by
  change IsIso ((truncLE n₀).mapTriangle.obj T).mor₂
  rw [← Triangle.isZero₁_iff_isIso₂ _ ((truncLE n₀).map_distinguished _ hT)]
  simp only [Functor.mapTriangle_obj, Triangle.mk_obj₁]
  rw [← isGE_iff_isZero_truncLE_obj (h := h)]
  assumption

lemma isIso₂_truncLT_map_of_GE (T : Triangle C) (hT : T ∈ distTriang C)
    (n : ℤ) (h₁ : IsGE T.obj₁ n) :
    IsIso ((truncLT n).map T.mor₂) := by
  rw [← NatIso.isIso_map_iff (truncLEIsoTruncLT (n-1) n (by linarith))]
  exact isIso₂_truncLE_map_of_GE T hT (n-1) n (by linarith) h₁

instance (X : C) (a b : ℤ) [IsGE X a] : IsGE ((truncLE b).obj X) a := by
  rw [isGE_iff_isZero_truncLE_obj (a-1) a (by linarith)]
  have := isIso₂_truncLE_map_of_GE _ ((triangleGELE_distinguished b (b+1) rfl X))
    (a-1) a (by linarith) (by dsimp ; infer_instance)
  dsimp at this
  exact IsZero.of_iso (isZero_truncLE_obj_of_isGE (a-1) a (by linarith) X)
    (asIso ((truncLE (a - 1)).map ((truncLEπ b).app X))).symm

instance (X : C) (a b : ℤ) [IsGE X a] : IsGE ((truncLT b).obj X) a :=
  isGE_of_iso ((truncLEIsoTruncLT (b-1) b (by linarith)).app X) a

instance (X : C) (a b : ℤ) [IsLE X b] : IsLE ((truncGE a).obj X) b := by
  rw [isLE_iff_isZero_truncGE_obj b (b+1) rfl]
  have := isIso₁_truncGE_map_of_LE _ ((triangleGELE_distinguished (a-1) a (by linarith) X))
    b (b+1) rfl (by dsimp ; infer_instance)
  dsimp at this
  exact IsZero.of_iso (isZero_truncGE_obj_of_isLE b (b+1) rfl X)
    (asIso ((truncGE (b+1)).map ((truncGEι  a).app X)))

instance (X : C) (a b : ℤ) : IsGE ((truncGELE a b).obj X) a := by
  dsimp [truncGELE]
  infer_instance

instance (X : C) (a b : ℤ) : IsLE ((truncGELE a b).obj X) b := by
  dsimp [truncGELE]
  infer_instance

instance (X : C) (a b : ℤ) : IsGE ((truncGELT a b).obj X) a := by
  dsimp [truncGELT]
  infer_instance

instance (X : C) (a b : ℤ) : IsLE ((truncGELT a b).obj X) (b-1) := by
  dsimp [truncGELT]
  infer_instance

instance (X : C) (a b : ℤ) : IsGE ((truncLTGE a b).obj X) a := by
  dsimp [truncLTGE]
  infer_instance

instance (X : C) (a b : ℤ) : IsLE ((truncLTGE a b).obj X) (b-1) := by
  dsimp [truncLTGE]
  infer_instance

instance (a b : ℤ) : (hP.truncGELT a b).Additive := by
  dsimp only [truncGELT]
  infer_instance

instance (a b : ℤ) : (hP.truncGELE a b).Additive := by
  dsimp only [truncGELE]
  infer_instance

instance (a b : ℤ) : (hP.truncLTGE a b).Additive := by
  dsimp only [truncLTGE]
  infer_instance

instance (a b : ℤ) : (hP.truncLEGE a b).Additive := by
  dsimp only [truncLEGE]
  infer_instance

noncomputable instance (a b : ℤ) : (hP.truncGELT a b).CommShift ℤ := by
  dsimp only [truncGELT]
  infer_instance

noncomputable instance (a b : ℤ) : (hP.truncGELE a b).CommShift ℤ := by
  dsimp only [truncGELE]
  infer_instance

noncomputable instance (a b : ℤ) : (hP.truncLTGE a b).CommShift ℤ := by
  dsimp only [truncLTGE]
  infer_instance

noncomputable instance (a b : ℤ) : (hP.truncLEGE a b).CommShift ℤ := by
  dsimp only [truncLEGE]
  infer_instance

noncomputable instance (a b : ℤ) : (hP.truncGELT a b).IsTriangulated := by
  dsimp only [truncGELT]
  infer_instance

noncomputable instance (a b : ℤ) : (hP.truncGELE a b).IsTriangulated := by
  dsimp only [truncGELE]
  infer_instance

noncomputable instance (a b : ℤ) : (hP.truncLTGE a b).IsTriangulated := by
  dsimp only [truncLTGE]
  infer_instance

noncomputable instance (a b : ℤ) : (hP.truncLEGE a b).IsTriangulated := by
  dsimp only [truncLEGE]
  infer_instance

/-
instance (i : ℤt) : (t.truncGEt.obj i).Additive := by
  obtain (rfl|⟨i, rfl⟩|rfl) := i.three_cases
  · dsimp
    infer_instance
  · dsimp
    infer_instance
  · constructor
    aesop_cat

instance (i : ℤt) : (t.truncLTt.obj i).Additive := by
  obtain (rfl|⟨i, rfl⟩|rfl) := i.three_cases
  · constructor
    dsimp
    aesop_cat
  · dsimp
    infer_instance
  · dsimp
    infer_instance

lemma isZero_truncLTt_obj_obj (X : C) (n : ℤ) [t.IsGE X n] (j : ℤt) (hj : j ≤ ℤt.mk n) :
    IsZero ((t.truncLTt.obj j).obj X) := by
  obtain (rfl|⟨j, rfl⟩|rfl) := j.three_cases
  · apply Functor.zero_obj
  · simp at hj
    dsimp
    rw [← t.isGE_iff_isZero_truncLT_obj]
    exact t.isGE_of_GE  _ _ _ hj

  · simp at hj

lemma isZero_truncGEt_obj_obj (X : C) (n : ℤ) [t.IsLE X n] (j : ℤt) (hj : ℤt.mk n < j) :
    IsZero ((t.truncGEt.obj j).obj X) := by
  obtain (rfl|⟨j, rfl⟩|rfl) := j.three_cases
  · simp at hj
  · simp at hj
    dsimp
    rw [← t.isLE_iff_isZero_truncGE_obj (j - 1) j (by simp)]
    exact t.isLE_of_LE X n (j - 1) (by linarith)
  · apply Functor.zero_obj

lemma truncGEt_obj_obj_isGE (n : ℤ) (i : ℤt) (h : ℤt.mk n ≤ i) (X : C) :
    t.IsGE ((t.truncGEt.obj i).obj X) n := by
  obtain (rfl|⟨i, rfl⟩|rfl) := i.three_cases
  · simp at h
  · simp at h
    dsimp
    exact t.isGE_of_GE  _ _ _ h
  · dsimp
    apply t.isGE_of_isZero
    apply Functor.zero_obj

lemma truncLTt_obj_obj_isLE (n : ℤ) (i : ℤt) (h : i ≤ ℤt.mk (n + 1)) (X : C) :
    t.IsLE (((t.truncLTt.obj i)).obj X) n := by
  obtain (rfl|⟨i, rfl⟩|rfl) := i.three_cases
  · dsimp
    apply t.isLE_of_isZero
    apply Functor.zero_obj
  · simp at h
    dsimp
    exact t.isLE_of_LE _ (i - 1) n (by linarith)
  · simp at h
-/

noncomputable def Gr'' (n : ℤ) : C ⥤ C := truncGELE n n ⋙ @shiftFunctor C _ _ _ Shift₂ (-n)

variable (n : ℤ)

instance (n : ℤ) : Functor.Additive (hP.Gr'' n) := by
  dsimp [Gr'']; infer_instance

noncomputable instance (n : ℤ) : (hP.Gr'' n).CommShift ℤ := by
  dsimp [Gr'']; infer_instance

instance (n : ℤ) : Functor.IsTriangulated (hP.Gr'' n) := by
  dsimp [Gr'']
  have := hP.shift₂_triangle
  infer_instance

instance (X : C) (n : ℤ) : IsLE ((Gr'' n).obj X) 0 :=
  isLE_shift _ n (-n) 0 (neg_add_cancel _)

instance (X : C) (n : ℤ) : IsGE ((Gr'' n).obj X) 0 :=
  isGE_shift _ n (-n) 0 (neg_add_cancel _)

lemma Gr''_obj_mem_core (n : ℤ) (X : C) : hP.core ((Gr'' n).obj X) := by
  rw [mem_core_iff]
  exact ⟨inferInstance, inferInstance⟩

noncomputable def Gr' (n : ℤ) : C ⥤ hP.Core' :=
  FullSubcategory.lift _ (Gr'' n) (Gr''_obj_mem_core n)

noncomputable def GrCompιCore' (n : ℤ) :
  hP.Gr' n ⋙ ιCore' ≅ Gr'' n :=
    FullSubcategory.lift_comp_inclusion _ _ _

noncomputable def Gr₀CompιCore'IsoTruncGELE : hP.Gr' 0 ⋙ ιCore' ≅ truncGELE 0 0 :=
  GrCompιCore' 0 ≪≫ isoWhiskerLeft (truncGELE 0 0) (shiftFunctorZero C ℤ)

/-
noncomputable def homologyCompιHeartDegreeIsoHomology' (q : ℤ) :
    t.homology' q ⋙ t.ιHeartDegree q ≅ t.truncGELE q q :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (t.homologyCompιHeart' q) _ ≪≫ Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _  (shiftFunctorCompIsoId C q (-q) (add_right_neg q)) ≪≫
    Functor.rightUnitor _
-/

lemma isIso_truncGE_map_truncGEι_app (a b : ℤ) (h : a ≤ b) (X : C) :
    IsIso ((truncGE b).map ((truncGEι a).app X)) :=
  isIso₁_truncGE_map_of_LE _
    (triangleGELE_distinguished (a-1) a (by linarith) X) (b-1) b (by linarith)
      (isLE_of_LE ((truncLE (a-1)).obj X) (a-1) (b-1) (by linarith))

/-
lemma isIso_truncGE_map_truncGTι_app (a b : ℤ) (h : a ≤ b) (X : C) :
    IsIso ((truncGE b).map ((truncGTι a).app X)) := sorry
-/

lemma isIso_truncLT_map_truncLTπ_app (a b : ℤ) (h : a ≤ b) (X : C) :
    IsIso ((truncLT a).map ((truncLTπ b).app X)) :=
  isIso₂_truncLT_map_of_GE _ (triangleGELT_distinguished b X) a
    (isGE_of_GE ((truncGE b).obj X) a b (by linarith))

lemma isIso_truncLE_map_truncLEπ_app (a b : ℤ) (h : a ≤ b) (X : C) :
    IsIso ((truncLE a).map ((truncLEπ b).app X)) := by
  apply isIso_truncLT_map_truncLTπ_app
  linarith

instance (X : C) (n : ℤ) : IsIso ((truncLE n).map ((truncLEπ n).app X)) := by
  apply isIso_truncLE_map_truncLEπ_app
  rfl

instance (X : C) (n : ℤ) : IsIso ((truncGE n).map ((truncGEι n).app X)) := by
  apply isIso_truncGE_map_truncGEι_app
  rfl

/-
lemma isIso_truncGEt_obj_map_truncGEπ_app (a b : ℤt) (h : a ≤ b) (X : C) :
    IsIso ((t.truncGEt.obj b).map ((t.abstractSpectralObject.truncGEπ a).app X)) := by
  obtain (rfl|⟨b, rfl⟩|rfl) := b.three_cases
  · simp only [ℤt.le_bot_iff] at h
    subst h
    dsimp
    simp only [AbstractSpectralObject.truncGEπ_bot_app]
    infer_instance
  · obtain (rfl|⟨a, rfl⟩|rfl) := a.three_cases
    · dsimp
      infer_instance
    · simp only [ℤt.mk_le_mk_iff] at h
      dsimp
      simp only [AbstractSpectralObject.truncGEπ_mk]
      exact t.isIso_truncGE_map_truncGEπ_app a b h X
    · simp at h
  · refine' ⟨0, IsZero.eq_of_src _ _ _, IsZero.eq_of_src _ _ _⟩
    all_goals
      simp only [truncGEt_obj_top, Functor.zero_obj]

lemma isIso_truncLTt_obj_map_truncLTπ_app (a b : ℤt) (h : a ≤ b) (X : C) :
    IsIso ((t.truncLTt.obj a).map ((t.abstractSpectralObject.truncLTι b).app X)) := by
  obtain (rfl|⟨a, rfl⟩|rfl) := a.three_cases
  · refine' ⟨0, IsZero.eq_of_src _ _ _, IsZero.eq_of_src _ _ _⟩
    all_goals
      simp only [truncLTt_obj_bot, Functor.zero_obj]
  · obtain (rfl|⟨b, rfl⟩|rfl) := b.three_cases
    · simp at h
    · simp only [ℤt.mk_le_mk_iff] at h
      dsimp
      simp only [AbstractSpectralObject.truncLEι_mk]
      exact t.isIso_truncLT_map_truncLTι_app a b h X
    · dsimp
      infer_instance
  · simp only [ℤt.top_le_iff] at h
    subst h
    dsimp
    simp only [AbstractSpectralObject.truncLTι_top_app]
    infer_instance
-/

/-
instance (D : Arrow ℤt) (X : C) :
  IsIso ((t.abstractSpectralObject.truncGEToTruncGEGE.app D).app X) :=
    t.isIso_truncGEt_obj_map_truncGEπ_app _ _ (leOfHom D.hom) X

instance (D : Arrow ℤt) (X : C) :
  IsIso ((t.abstractSpectralObject.truncLTLTToTruncLT.app D).app X) :=
    t.isIso_truncLTt_obj_map_truncLTπ_app _ _ (leOfHom D.hom) X

instance (D : Arrow ℤt) : IsIso (t.abstractSpectralObject.truncGEToTruncGEGE.app D) :=
  NatIso.isIso_of_isIso_app _

instance (D : Arrow ℤt) : IsIso (t.abstractSpectralObject.truncLTLTToTruncLT.app D) :=
  NatIso.isIso_of_isIso_app _

instance : IsIso (t.abstractSpectralObject.truncGEToTruncGEGE) := NatIso.isIso_of_isIso_app _

instance : IsIso (t.abstractSpectralObject.truncLTLTToTruncLT) := NatIso.isIso_of_isIso_app _

lemma truncGEπ_compatibility (a : ℤt) (X : C) :
  (t.abstractSpectralObject.truncGE.obj a).map ((t.abstractSpectralObject.truncGEπ a).app X) =
    (t.abstractSpectralObject.truncGEπ a).app
      ((t.abstractSpectralObject.truncGE.obj a).obj X) := by
  obtain (rfl|⟨a, rfl⟩|rfl) := a.three_cases
  · rfl
  · dsimp
    simp only [AbstractSpectralObject.truncGEπ_mk]
    apply from_truncGE_obj_ext
    exact ((t.truncGEπ a).naturality ((t.truncGEπ a).app X)).symm
  · apply IsZero.eq_of_src
    dsimp
    simp

lemma truncLTι_compatibility (a : ℤt) (X : C) :
    (t.abstractSpectralObject.truncLT.obj a).map ((t.abstractSpectralObject.truncLTι a).app X) =
      (t.abstractSpectralObject.truncLTι a).app
        ((t.abstractSpectralObject.truncLT.obj a).obj X) := by
  obtain (rfl|⟨a, rfl⟩|rfl) := a.three_cases
  · apply IsZero.eq_of_src
    dsimp
    simp
  · dsimp
    simp only [AbstractSpectralObject.truncLEι_mk]
    apply to_truncLT_obj_ext
    exact ((t.truncLTι a).naturality ((t.truncLTι a).app X))
  · rfl

lemma isIso_truncLTι_app_truncGELT_obj (a b : ℤt) (h : a ≤ b) (X : C) :
    IsIso ((t.abstractSpectralObject.truncLTι b).app
      ((t.truncLTt.obj b ⋙ t.truncGEt.obj a).obj X)) := by
  obtain (rfl|⟨b, rfl⟩|rfl) := b.three_cases
  · refine' ⟨0, IsZero.eq_of_src _ _ _, IsZero.eq_of_src _ _ _⟩
    · dsimp
      simp
    · dsimp
      refine' IsZero.of_iso (isZero_zero _)
        (Functor.mapIso _ (IsZero.isoZero (Functor.zero_obj _)) ≪≫
          (t.truncGEt.obj a).mapZeroObject)
  · dsimp [SpectralObject.AbstractSpectralObject.truncLTι]
    simp only [comp_id]
    rw [← t.isLE_iff_isIso_truncLTι_app (b-1) b (by linarith)]
    obtain (rfl|⟨a, rfl⟩|rfl) := a.three_cases
    · dsimp
      infer_instance
    · dsimp
      infer_instance
    · dsimp
      apply t.isLE_of_isZero
      simp
  · dsimp [SpectralObject.AbstractSpectralObject.truncLTι]
    erw [comp_id, Functor.map_id]
    dsimp
    infer_instance

instance (D : Arrow ℤt) (X : C) :
    IsIso ((t.abstractSpectralObject.truncLTGELTSelfToTruncGELT.app D).app X) :=
  t.isIso_truncLTι_app_truncGELT_obj D.left D.right (leOfHom D.hom) X

instance (D : Arrow ℤt) : IsIso (t.abstractSpectralObject.truncLTGELTSelfToTruncGELT.app D) :=
  NatIso.isIso_of_isIso_app _

instance : IsIso (t.abstractSpectralObject.truncLTGELTSelfToTruncGELT) :=
  NatIso.isIso_of_isIso_app _
-/

instance (a b : ℤ) (X : C) : IsLE ((truncGELT a b).obj X) (b-1) := by
  dsimp [truncGELT]
  infer_instance

noncomputable def natTransTruncLTGETruncGELT (a b : ℤ) :
    truncLTGE (C := C) a b ⟶ truncGELT a b where
  app X := descTruncLT (liftTruncGE
    ((truncGEι a).app X ≫ (truncLTπ b).app X) a) (b-1) b (by linarith)
  naturality X Y f := by
    dsimp [truncGELT, truncLTGE]
    apply from_truncLT_obj_ext
    dsimp
    apply to_truncGE_obj_ext
    simp only [Functor.id_obj, ← NatTrans.naturality_assoc, Functor.id_map, π_descTruncLT, assoc,
      liftTruncGE_ι, π_descTruncLT_assoc, NatTrans.naturality, liftTruncGE_ι_assoc]
    rw [← NatTrans.naturality, NatTrans.naturality_assoc]

@[reassoc (attr := simp)]
lemma natTransTruncLEGETruncGELE_app_pentagon (a b : ℤ) (X : C) :
    (truncLTπ b).app _ ≫ (natTransTruncLTGETruncGELT a b).app X ≫ (truncGEι a).app _ =
      (truncGEι a).app X ≫ (truncLTπ b).app X := by simp [natTransTruncLTGETruncGELT]

lemma natTransTruncLEGETruncGELE_app_pentagon_uniqueness (a b : ℤ) (X : C)
    (φ : (truncLTGE a b).obj X ⟶ (truncGELT a b).obj X)
    (hφ : (truncLTπ b).app _ ≫ φ ≫ (truncGEι a).app _ =
      (truncGEι a).app X ≫ (truncLTπ b).app X) :
    φ = (natTransTruncLTGETruncGELT a b).app X := by
  apply from_truncLT_obj_ext
  dsimp
  apply to_truncGE_obj_ext
  rw [assoc, assoc, natTransTruncLEGETruncGELE_app_pentagon, hφ]

noncomputable def truncLTδGELE (a b : ℤ) :
    truncLT a ⟶ truncGELE a b ⋙ shiftFunctor C (1 : ℤ) :=
  whiskerRight (truncLEπ b) (truncLT a) ≫ whiskerLeft (truncLE b) (truncLTδGE a)

noncomputable def truncLTGEδGE (a b : ℤ) :
    truncLTGE a b ⟶ truncGE b ⋙ shiftFunctor C (1 : ℤ) :=
  whiskerLeft (truncGE a) (truncLTδGE b) ≫ whiskerRight (truncGEι a)
  (truncGE b ⋙ (shiftFunctor C (1 : ℤ)))

@[simps!]
noncomputable def triangleGELELTLE (a b : ℤ) (h : a ≤ b) : C ⥤ Triangle C :=
  Triangle.functorMk (whiskerLeft (truncLE b) (truncGEι a)) (natTransTruncLTOfGE (b + 1) a
  (by linarith)) (truncLTδGELE a b)

@[simps!]
noncomputable def triangleGEGELTGE (a b : ℤ) (h : a ≤ b) : C ⥤ Triangle C :=
  Triangle.functorMk (natTransTruncGEOfGE b a h) (whiskerLeft (truncGE a) (truncLTπ b))
    (truncLTGEδGE a b)

lemma triangleGELELTLE_distinguished (a b : ℤ) (h : a ≤ b) (X : C) :
    (triangleGELELTLE a b h).obj X ∈ distTriang C := by
  have := isIso_truncLT_map_truncLTπ_app a (b + 1) (by linarith) X
  refine isomorphic_distinguished _ (triangleGELT_distinguished a ((truncLE b).obj X)) _ ?_
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (asIso ((truncLT a).map
    ((truncLTπ (b + 1)).app X))) ?_ ?_ ?_
  · simp only [triangleGELELTLE_obj_obj₁, triangleGELT_obj_obj₂, triangleGELELTLE_obj_obj₂,
    triangleGELELTLE_obj_mor₁, Iso.refl_hom, comp_id, triangleGELT_obj_obj₁, triangleGELT_obj_mor₁,
    id_comp]
  · dsimp [truncLTδGELE]
    have : IsLE ((truncLT a).obj ((truncLE b).obj X)) (b + 1 - 1) := by
      have heq : b + 1 - 1 = b := Int.add_sub_cancel _ _
      rw [heq]; infer_instance
    apply from_truncLT_obj_ext
    simp only [Functor.id_obj, natTransTruncLTOfGE_π_app_assoc, id_comp]
    have := (truncLTπ a).naturality ((truncLTπ (b + 1)).app X)
    simp only [Functor.id_obj, Functor.id_map] at this
    exact this.symm
  · dsimp [truncLTδGELE]; simp only [NatTrans.naturality, Functor.comp_obj, Functor.comp_map,
    Functor.map_id, comp_id]; rfl

lemma triangleGEGELTGE_distinguished (a b : ℤ) (h : a ≤ b) (X : C) :
    (triangleGEGELTGE a b h).obj X ∈ distTriang C := by
  have := isIso_truncGE_map_truncGEι_app a b h X
  refine isomorphic_distinguished _ (triangleGELT_distinguished b ((truncGE a).obj X)) _ ?_
  refine Triangle.isoMk _ _ (asIso ((truncGE b).map ((truncGEι a).app X))).symm (Iso.refl _)
    (Iso.refl _) ?_ ?_ ?_
  · dsimp [truncLTGEδGE]; simp only [comp_id, IsIso.eq_inv_comp, NatTrans.naturality]
    apply to_truncGE_obj_ext
    simp only [Functor.id_obj, assoc, NatTrans.naturality, Functor.id_map,
      ι_natTransTruncGEOfGE_app_assoc]
  · simp only [triangleGEGELTGE_obj_obj₂, triangleGELT_obj_obj₃, triangleGEGELTGE_obj_obj₃,
    triangleGEGELTGE_obj_mor₂, Iso.refl_hom, comp_id, triangleGELT_obj_obj₂, triangleGELT_obj_mor₂,
    id_comp]
  · dsimp [truncLTGEδGE]; simp only [Functor.map_inv, assoc, IsIso.hom_inv_id, comp_id, id_comp]

instance (a b : ℤ) (X : C) : IsIso ((natTransTruncLTGETruncGELT a b).app X) := by
  by_cases h : a ≤ b
  · let u₁₂ := (natTransTruncGEOfGE b a h).app X
    let u₂₃ : (truncGE a).obj X ⟶ X := (truncGEι a).app X
    let u₁₃ : _ ⟶ X := (truncGEι b).app X
    have eq : u₁₂ ≫ u₂₃ = u₁₃ := by simp [u₁₂, u₂₃, u₁₃]
    have H := someOctahedron eq (triangleGEGELTGE_distinguished a b h X)
      (triangleGELT_distinguished a X) (triangleGELT_distinguished b X)
    let m₁ : (truncLTGE a b).obj X ⟶  _ := H.m₁
    have := isIso₁_truncGE_map_of_LE _ H.mem (a-1) a (by linarith) (by dsimp; infer_instance)
    dsimp at this
    have eq' : liftTruncGE m₁ a = (natTransTruncLTGETruncGELT a b).app X := by
      apply to_truncGE_obj_ext
      dsimp
      apply from_truncLT_obj_ext
      simp_rw [natTransTruncLEGETruncGELE_app_pentagon, liftTruncGE_ι]
      exact H.comm₁
    rw [← eq']
    have fac : (truncGEι a).app ((truncLT b).obj ((truncGE a).obj X)) ≫
        liftTruncGE m₁ a = (truncGE a).map m₁ := to_truncGE_obj_ext _ _ _ _ (by simp [truncLTGE])
    have : IsIso ((truncGEι a).app ((truncLT b).obj ((truncGE a).obj X))) := by
      rw [← isGE_iff_isIso_truncGEι_app a]
      infer_instance
    exact IsIso.of_isIso_fac_left fac
  · refine ⟨0, ?_, ?_⟩
    all_goals
      apply IsZero.eq_of_src
      refine isZero _ (b-1) a (by linarith)

instance (a b : ℤ) : IsIso (hP.natTransTruncLTGETruncGELT a b) :=
  NatIso.isIso_of_isIso_app _

noncomputable def truncLTGEIsoGELT (a b : ℤ) : hP.truncLTGE a b ≅ truncGELT a b :=
  asIso (natTransTruncLTGETruncGELT a b)

noncomputable def truncLEGEIsoGELE (a b : ℤ) : hP.truncLEGE a b ≅ truncGELE a b :=
  truncLTGEIsoGELT a (b + 1)

instance (a b : ℤ) (X : C) :
  IsIso ((truncGEι b).app ((truncLT a).obj ((truncGE b).obj X))) := by
    rw [← isGE_iff_isIso_truncGEι_app]
    infer_instance

lemma truncGE_map_truncLT_map_truncGEι_app_fac (a b : ℤ) (X : C) :
    (truncGE a).map ((truncLT b).map ((truncGEι a).app X)) =
      (truncGEι a).app ((truncLT b).obj ((truncGE a).obj X)) ≫
        (natTransTruncLTGETruncGELT a b).app X := by
  rw [← cancel_epi (inv ((truncGEι a).app ((truncLT b).obj ((truncGE a).obj X)))),
    IsIso.inv_hom_id_assoc]
  apply natTransTruncLEGETruncGELE_app_pentagon_uniqueness
  simp only [Functor.id_obj, assoc, NatTrans.naturality, Functor.id_map, IsIso.inv_hom_id_assoc]
  exact ((truncLTπ b).naturality ((truncGEι a).app X)).symm

lemma isIso_truncGE_map_truncLT_map_truncGEι_app (a b : ℤ) (X : C) :
    IsIso ((truncGE a).map ((truncLT b).map ((truncGEι a).app X))) := by
  rw [truncGE_map_truncLT_map_truncGEι_app_fac a b X]
  infer_instance

/-
instance (D : Arrow ℤt) (X : C) :
    IsIso ((t.abstractSpectralObject.truncLTGELTSelfToTruncLTGE.app D).app X) := by
  obtain ⟨a, b, f : a ⟶ b⟩ := D
  have h : a ≤ b := leOfHom f
  obtain (rfl|⟨b, rfl⟩|rfl) := b.three_cases
  · simp only [ℤt.le_bot_iff] at h
    subst h
    exact ⟨0, IsZero.eq_of_src (Functor.zero_obj _) _ _,
      IsZero.eq_of_src (Functor.zero_obj _) _ _⟩
  dsimp [SpectralObject.AbstractSpectralObject.truncLTGELTSelfToTruncLTGE,
      SpectralObject.AbstractSpectralObject.truncLTGE]
  · obtain (rfl|⟨a, rfl⟩|rfl) := a.three_cases
    · simp only [AbstractSpectralObject.truncLEι_mk]
      exact t.isIso_truncLT_map_truncLTι_app b b (by rfl) X
    · simp only [ℤt.mk_le_mk_iff] at h
      simp only [truncGEt_obj_mk, AbstractSpectralObject.truncLEι_mk]
      exact t.isIso_truncLT_map_truncGE_map_truncLTι_app a b X
    · refine' ⟨0, IsZero.eq_of_src _ _ _,
        IsZero.eq_of_src _ _ _⟩
      all_goals
        exact IsZero.of_iso (isZero_zero _)
          ((t.truncLT b).mapIso ((Functor.zero_obj _).isoZero) ≪≫
          (t.truncLT b).mapZeroObject)
  · dsimp [SpectralObject.AbstractSpectralObject.truncLTGELTSelfToTruncLTGE]
    simp only [AbstractSpectralObject.truncLTι_top_app, Functor.map_id]
    infer_instance

instance (D : Arrow ℤt) : IsIso (t.abstractSpectralObject.truncLTGELTSelfToTruncLTGE.app D) :=
  NatIso.isIso_of_isIso_app _

instance : IsIso (t.abstractSpectralObject.truncLTGELTSelfToTruncLTGE) :=
  NatIso.isIso_of_isIso_app _

instance : t.abstractSpectralObject.IsCompatible where
  distinguished := AbstractSpectralObject.distinguished t
  truncGEπ_compatibility' := t.truncGEπ_compatibility
  truncLTι_compatibility' := t.truncLTι_compatibility

@[simps!]
noncomputable def spectralObject (X : C) : SpectralObject C ℤt :=
  t.abstractSpectralObject.spectralObject X

noncomputable def shiftSpectralObjectω₁IsoHomologyιHeart' (X : C) (q q' : ℤ) (hq' : q + 1 = q') :
    ((t.spectralObject X).ω₁ ⋙ shiftFunctor C q).obj
      (ComposableArrows.mk₁ (homOfLE (by simp; linarith) : ℤt.mk q ⟶ ℤt.mk q')) ≅
      (t.homology' q ⋙ t.ιHeart').obj X :=
  (shiftFunctor C q).mapIso ((t.truncGELEIsoTruncGELT q q q' hq').symm.app X) ≪≫
    (t.homologyCompιHeart' q).symm.app X

noncomputable def homology₀CompιHeartIsoTruncLEGE : t.homology' 0 ⋙ t.ιHeart' ≅ t.truncLEGE 0 0 :=
  t.homology₀CompιHeart'IsoTruncGELE ≪≫ t.truncGELEIsoLEGE 0 0
-/

end FilteredTriangulated

namespace Subcategory

#exit

lemma HasInducedFiltration.mk' (S : Subcategory C) (hP : FilteredTriangulated C)
    (h : ∀ (X : C) (_ : S.P X) (n : ℤ), S.P ((hP.truncLE n).obj X) ∧
      (S.P ((hP.truncGE n).obj X))) :
    S.HasInducedTStructure t where  -- need also to talk about induced filtrations then
  exists_triangle_zero_one X hX := by
    refine' ⟨_, _, _, _, _, _, _,
      t.triangleLEGE_distinguished 0 1 (by linarith) X,
      ⟨⟨(t.truncLE 0).obj X, (h X hX 0).1⟩, ⟨Iso.refl _⟩⟩,
      ⟨⟨(t.truncGE 1).obj X, (h X hX 1).2⟩, ⟨Iso.refl _⟩⟩⟩
    exact TStructure.mem_of_isLE  _ _ _
    exact TStructure.mem_of_isGE  _ _ _

lemma mem_of_hasInductedTStructure (S : Subcategory C) (t : TStructure C)
    [ClosedUnderIsomorphisms S.P] [S.HasInducedTStructure t]
    (T : Triangle C) (hT : T ∈ distTriang C)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (h₁ : t.IsLE T.obj₁ n₀) (h₂ : S.P T.obj₂)
    (h₃ : t.IsGE T.obj₃ n₁) :
    S.P T.obj₁ ∧ S.P T.obj₃ := by
  obtain ⟨e, _⟩ := t.triangle_iso_exists n₀ n₁ (by omega) _ _ hT
    (S.ι.map_distinguished _ ((S.tStructure t).triangleLEGE_distinguished n₀ n₁ h ⟨_, h₂⟩))
    (Iso.refl _) inferInstance inferInstance (by
      dsimp
      rw [← S.tStructure_isLE_iff]
      infer_instance) (by
      dsimp
      rw [← S.tStructure_isGE_iff]
      infer_instance)
  exact ⟨(mem_iff_of_iso S.P (Triangle.π₁.mapIso e)).2 (S.ι_obj_mem _),
    (mem_iff_of_iso S.P (Triangle.π₃.mapIso e)).2 (S.ι_obj_mem _)⟩

instance (S S' : Subcategory C) (t : TStructure C) [S.HasInducedTStructure t]
    [S'.HasInducedTStructure t]
    [ClosedUnderIsomorphisms S.P] [ClosedUnderIsomorphisms S'.P] :
    (S.inter S').HasInducedTStructure t :=
  HasInducedTStructure.mk' _ _ (by
    rintro X ⟨hX, hX'⟩ n
    exact
      ⟨⟨(S.mem_of_hasInductedTStructure t _ (t.triangleLEGE_distinguished n _ rfl X) n _ rfl
        (by dsimp; infer_instance) hX (by dsimp; infer_instance)).1,
      (S'.mem_of_hasInductedTStructure t _ (t.triangleLEGE_distinguished n _ rfl X) n _ rfl
        (by dsimp; infer_instance) hX' (by dsimp; infer_instance)).1⟩,
        ⟨(S.mem_of_hasInductedTStructure t _ (t.triangleLEGE_distinguished (n - 1) n (by omega) X)
        (n - 1) n (by omega) (by dsimp; infer_instance) hX (by dsimp; infer_instance)).2,
      (S'.mem_of_hasInductedTStructure t _ (t.triangleLEGE_distinguished (n - 1) n (by omega) X)
        (n - 1) n (by omega) (by dsimp; infer_instance) hX' (by dsimp; infer_instance)).2⟩⟩)

end Subcategory

instance [IsTriangulated C] : t.plus.HasInducedTStructure t := by
  apply Subcategory.HasInducedTStructure.mk'
  rintro X ⟨a, _⟩ n
  exact ⟨⟨a, inferInstance⟩, ⟨a, inferInstance⟩⟩

instance [IsTriangulated C] : t.minus.HasInducedTStructure t := by
  apply Subcategory.HasInducedTStructure.mk'
  rintro X ⟨a, _⟩ n
  exact ⟨⟨a, inferInstance⟩, ⟨a, inferInstance⟩⟩

instance [IsTriangulated C] : t.bounded.HasInducedTStructure t := by
  dsimp [TStructure.bounded]
  infer_instance

namespace TStructure

instance (X : C) (n : ℤ) [t.IsLE X n] (i : ℤt) :
    t.IsLE ((t.truncLTt.obj i).obj X) n := by
  obtain rfl|⟨i, rfl⟩|rfl := ℤt.three_cases i
  · apply isLE_of_isZero
    simp
  · dsimp
    infer_instance
  · dsimp
    infer_instance

instance [IsTriangulated C] (X : C) (n : ℤ) [t.IsGE X n] (i : ℤt) :
    t.IsGE ((t.truncLTt.obj i).obj X) n := by
  obtain rfl|⟨i, rfl⟩|rfl := ℤt.three_cases i
  · apply isGE_of_isZero
    simp
  · dsimp
    infer_instance
  · dsimp
    infer_instance

instance [IsTriangulated C] (X : C) (n : ℤ) [t.IsLE X n] (i : ℤt) :
    t.IsLE ((t.truncGEt.obj i).obj X) n := by
  obtain rfl|⟨i, rfl⟩|rfl := ℤt.three_cases i
  · dsimp
    infer_instance
  · dsimp
    infer_instance
  · apply isLE_of_isZero
    simp

instance (X : C) (n : ℤ) [t.IsGE X n] (i : ℤt) :
    t.IsGE ((t.truncGEt.obj i).obj X) n := by
  obtain rfl|⟨i, rfl⟩|rfl := ℤt.three_cases i
  · dsimp
    infer_instance
  · dsimp
    infer_instance
  · apply isGE_of_isZero
    simp

end TStructure

end Triangulated

end CategoryTheory
