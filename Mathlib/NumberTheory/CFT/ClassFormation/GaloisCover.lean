/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Shapes.Connected
public import Mathlib.NumberTheory.CFT.ClassFormation.GaloisCategoryEquivalence
public import Mathlib.NumberTheory.CFT.ClassFormation.GaloisCategoryOver

/-!
# Galois covers in Galois categories

-/

@[expose] public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

open PreGaloisCategory

namespace GaloisCategory

/-- In a Galois category, a morphism `f : Y ⟶ X` is a Galois cover
if `X` is connected and `Over.mk f` is a Galois object in
the Galois category `Over X`. -/
abbrev IsGaloisCover [GaloisCategory C] {Y X : C} (f : Y ⟶ X)
    [PreGaloisCategory.IsConnected X] : Prop :=
  IsGalois (Over.mk f)

lemma isGaloisCover_def {Y X : C} (f : Y ⟶ X) [GaloisCategory C]
  [PreGaloisCategory.IsConnected X] :
  IsGaloisCover f ↔ IsGalois (Over.mk f) := Iff.rfl

lemma isConnected_of_isGaloisCover [GaloisCategory C] {Y X : C} (f : Y ⟶ X)
    [PreGaloisCategory.IsConnected X] [IsGaloisCover f] :
    PreGaloisCategory.IsConnected Y := by
  rw [← dsimp% isConnected_over_iff (Over.mk f)]
  infer_instance

lemma hom_ext_of_isConnected [GaloisCategory C]
    (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
    {Y X : C} [PreGaloisCategory.IsConnected Y]
    {f f' : Y ⟶ X} (y : F.obj Y) (h : F.map f y = F.map f' y) :
    f = f' :=
  F.map_injective (by
    ext z
    obtain ⟨g, rfl⟩ := (FiberFunctor.isPretransitive_of_isConnected F Y).exists_smul_eq y z
    simp only [mulAction_def, ← NatTrans.naturality_apply, h])

lemma isGaloisOver_of_isGalois [GaloisCategory C]
    {Y X : C} (f : Y ⟶ X) [PreGaloisCategory.IsConnected X]
    (hY : IsGalois Y := by infer_instance) :
    IsGaloisCover f := by
  have : PreGaloisCategory.IsConnected (Over.mk f).left := by
    dsimp
    infer_instance
  let F := getFiberFunctor C
  rw [isGaloisCover_def]
  let s : F.obj X := Classical.arbitrary _
  rw [isGalois_iff_pretransitive (fiberFunctorOver F X s),
    MulAction.isPretransitive_iff]
  rw [isGalois_iff_pretransitive F, MulAction.isPretransitive_iff] at hY
  intro ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨g, rfl⟩ := hY x y
  exact ⟨Over.isoMk g (hom_ext_of_isConnected F x (by cat_disch)), rfl⟩

lemma isGaloisCover_of_comp [GaloisCategory C]
    {Z Y X : C} (f : Z ⟶ Y) (g : Y ⟶ X) (fg : Z ⟶ X)
    [PreGaloisCategory.IsConnected Y]
    [PreGaloisCategory.IsConnected X]
    (h : f ≫ g = fg := by cat_disch)
    (hfg : IsGaloisCover fg := by infer_instance) :
    IsGaloisCover f := by
  subst h
  rw [isGaloisCover_def] at hfg ⊢
  have : PreGaloisCategory.IsConnected (Over.mk g).left := by
    assumption
  let e := Over.iteratedSliceEquiv (Over.mk g)
  let γ := e.inverse.obj (Over.mk f)
  change IsGalois γ.left at hfg
  have := isGaloisOver_of_isGalois γ.hom
  rw [isGaloisCover_def] at this
  rwa [← isGalois_iff_of_isEquivalence e.inverse (Over.mk f)]

lemma exists_isGaloisCover [GaloisCategory C]
    {Y X : C} (f : Y ⟶ X) [PreGaloisCategory.IsConnected Y]
      [PreGaloisCategory.IsConnected X] :
    ∃ (Z : C) (g : Z ⟶ Y), PreGaloisCategory.IsConnected Z ∧ IsGaloisCover (g ≫ f) := by
  obtain ⟨Z, g, _⟩ := exists_hom_from_galois_of_connected (Over.mk f)
  refine ⟨Z.left, g.left, ?_, by rwa [dsimp% g.w]⟩
  rw [← isConnected_over_iff]
  infer_instance

end GaloisCategory

end CategoryTheory
