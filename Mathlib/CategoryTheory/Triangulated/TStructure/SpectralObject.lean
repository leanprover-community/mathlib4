/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.SpectralObject
public import Mathlib.CategoryTheory.Triangulated.TStructure.ETrunc

/-!
# Spectral objects attached t-structures

-/

@[expose] public section

-- This is a refactor of the construction in `Trunc.lean`
-- There are sorries in `ETrunc.lean`

namespace CategoryTheory

open Limits Pretriangulated ZeroObject Preadditive ComposableArrows

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Triangulated

namespace TStructure

variable (t : TStructure C) [IsTriangulated C]

@[simps]
noncomputable def ω₁ : ComposableArrows EInt 1 ⥤ C ⥤ C where
  obj D := t.eTruncLT.obj (D.obj 1) ⋙ t.eTruncGE.obj (D.obj 0)
  map φ := t.eTruncLT.map (φ.app 1) ◫ t.eTruncGE.map (φ.app 0)

section

variable (a b c : EInt) (hab : a ≤ b) (hbc : b ≤ c)

open Functor in
@[simps!]
noncomputable def ω₁δ :
    t.ω₁.obj (mk₁ (homOfLE hbc)) ⟶ t.ω₁.obj (mk₁ (homOfLE hab)) ⋙ shiftFunctor C (1 : ℤ) :=
  whiskerLeft _ (t.eTruncGEToGEGE a b) ≫ (associator _ _ _).inv ≫
      (t.ω₁.obj (mk₁ (homOfLE (hab.trans hbc)))).whiskerLeft (t.eTruncGEδLT.app b) ≫
      (associator _ _ _).inv ≫
      whiskerRight
        ((associator _ _ _).hom ≫ whiskerLeft _ (t.eTruncLTGEIsoLEGT a b).hom ≫
          (associator _ _ _).inv ≫ whiskerRight (t.eTruncLTLTToLT c b) _) _

attribute [local simp] Precomp.obj in
@[reassoc]
lemma ω₁δ_naturality (a' b' c' : EInt) (hab' : a' ≤ b') (hbc' : b' ≤ c')
    (φ : mk₂ (homOfLE hab) (homOfLE hbc) ⟶ mk₂ (homOfLE hab') (homOfLE hbc')) :
    t.ω₁.map (homMk₁ (φ.app 1) (φ.app 2)) ≫ t.ω₁δ a' b' c' hab' hbc' =
      t.ω₁δ a b c hab hbc ≫ Functor.whiskerRight (t.ω₁.map (homMk₁ (φ.app 0) (φ.app 1))) _ := by
  ext X
  simp only [Nat.reduceAdd, homOfLE_leOfHom, ω₁_obj, Fin.isValue, mk₁_obj, Mk₁.obj,
    Functor.comp_obj, ω₁_map, homMk₁_app, NatTrans.comp_app, NatTrans.hcomp_app, ω₁δ_app,
    ← Functor.map_comp, Category.assoc, NatTrans.naturality_assoc, Functor.comp_map,
    ← Functor.map_comp_assoc, NatTrans.naturality_app_assoc, Functor.whiskeringRight_obj_obj,
    Functor.whiskeringRight_obj_map, Functor.whiskerRight_app, NatTrans.naturality]
  congr 2
  have h₁ := t.eTruncLTGEIsoLEGT_naturality_app a b hab a' b' hab' (homMk₁ (φ.app 0) (φ.app 1))
  dsimp at h₁
  simp only [homOfLE_leOfHom, Fin.isValue, Functor.map_comp, Category.assoc, ← reassoc_of% h₁]
  erw [← NatTrans.naturality]
  dsimp
  --??
  have h₂ := (t.eTruncLTGEIsoLEGT a' b').hom.naturality ((t.eTruncLT.map (φ.app 2)).app X)
  dsimp at h₂
  have h₃ := t.eTruncLT_map_app_eTruncLTι_app (φ.app 2) X
  sorry

@[simps!]
noncomputable def triangleω₁δ : C ⥤ Triangle C :=
  Triangle.functorMk (t.ω₁.map (twoδ₂Toδ₁' a b c hab hbc))
    (t.ω₁.map (twoδ₁Toδ₀' a b c hab hbc)) (t.ω₁δ a b c hab hbc)

noncomputable def triangleω₁δObjIso (X : C) :
    (t.triangleω₁δ a b c hab hbc).obj X ≅
      (t.eTriangleLTGE.obj b).obj ((t.ω₁.obj (mk₁ (homOfLE (hab.trans hbc)))).obj X) := by
  refine Triangle.isoMk _ _
    ((t.eTruncGE.obj a).mapIso ((t.eTruncLTLTIsoLT c b hbc).symm.app X) ≪≫
      (t.eTruncLTGEIsoLEGT a b).symm.app _) (Iso.refl _) ((t.eTruncGEIsoGEGE a b hab).app _)
    ?_ ?_ ?_
  · dsimp
    simp only [triangleω₁δ_obj_mor₁, homOfLE_leOfHom, Category.comp_id, Category.assoc]
    rw [← cancel_epi ((t.eTruncGE.obj a).map ((t.eTruncLTLTIsoLT c b hbc).hom.app X)),
      ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id, Category.id_comp]
    rw [← cancel_epi ((t.eTruncLTGEIsoLEGT a b).hom.app ((t.eTruncLT.obj c).obj X)),
      Iso.hom_inv_id_app_assoc]
    sorry
  · sorry
  · simp [← Functor.map_comp_assoc, ← Functor.map_comp]

lemma triangleω₁δ_distinguished (X : C) :
    (t.triangleω₁δ a b c hab hbc).obj X ∈ distTriang _ :=
  isomorphic_distinguished _ (t.eTriangleLTGE_distinguished b _) _
    (t.triangleω₁δObjIso a b c hab hbc X)

end

@[simps ω₁]
noncomputable def newSpectralObject (X : C) : SpectralObject C EInt where
  ω₁ := t.ω₁ ⋙ (evaluation _ _).obj X
  δ'.app D := (t.ω₁δ (D.obj 0) (D.obj 1) (D.obj 2)
    (leOfHom (D.map' 0 1)) (leOfHom (D.map' 1 2))).app X
  δ'.naturality {D D'} φ := by
    obtain ⟨a, b, c, f, g, rfl⟩ := mk₂_surjective D
    obtain ⟨a', b', c', f', g', rfl⟩ := mk₂_surjective D'
    exact NatTrans.congr_app (t.ω₁δ_naturality a b c (leOfHom f) (leOfHom g)
      a' b' c' (leOfHom f') (leOfHom g') φ) X
  distinguished' D := by
    obtain ⟨a, b, c, f, g, rfl⟩ := mk₂_surjective D
    exact t.triangleω₁δ_distinguished a b c (leOfHom f) (leOfHom g) X

@[simp]
lemma newSpectralObject_δ (X : C) {a b c : EInt} (f : a ⟶ b) (g : b ⟶ c) :
    (t.newSpectralObject X).δ f g = (t.ω₁δ a b c (leOfHom f) (leOfHom g)).app X := rfl

@[simps]
noncomputable def spectralObjectFunctor : C ⥤ SpectralObject C EInt where
  obj := t.newSpectralObject
  map φ :=
    { hom := Functor.whiskerLeft _ ((evaluation _ _).map φ)
      comm f g := ((t.ω₁δ _ _ _ (leOfHom f) (leOfHom g)).naturality φ).symm }

end TStructure

end Triangulated

end CategoryTheory
