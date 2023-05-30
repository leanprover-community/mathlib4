/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/

import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair

namespace CategoryTheory

open Limits

variable {C : Type _} [Category C]

def Sieve.EffectiveEpimorphic {X : C} (S : Sieve X) : Prop :=
  Nonempty (IsColimit (S : Presieve X).cocone)

abbrev Presieve.EffectiveEpimorphic {X : C} (S : Presieve X) : Prop :=
  (Sieve.generate S).EffectiveEpimorphic

inductive Sieve.generate_singleton_aux {X Y : C} (f : Y ⟶ X) : (Z : C) → (Z ⟶ X) → Prop where
  | mk (Z : C) (g : Z ⟶ Y) : Sieve.generate_singleton_aux _ _ (g ≫ f)

def Sieve.generate_singleton {X Y : C} (f : Y ⟶ X) : Sieve X where
  arrows Z g := ∃ (e : Z ⟶ Y), e ≫ f = g
  downward_closed := by
    rintro W Z g ⟨e,rfl⟩ q
    refine ⟨q ≫ e, by simp⟩

lemma Sieve.generate_singleton_eq {X Y : C} (f : Y ⟶ X) :
    Sieve.generate (Presieve.singleton f) = Sieve.generate_singleton f := by
  ext Z ; intro g
  constructor
  · rintro ⟨W,i,p,⟨⟩,rfl⟩
    exact ⟨i,rfl⟩
  · rintro ⟨g,h⟩
    exact ⟨Y,g,f,⟨⟩,h⟩

structure EffectiveEpiStruct {X Y : C} (f : Y ⟶ X) where
  desc : ∀ {W : C} (e : Y ⟶ W),
    (∀ {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e) → (X ⟶ W)
  fac : ∀ {W : C} (e : Y ⟶ W)
    (h : ∀ {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e),
    f ≫ desc e h = e
  uniq : ∀ {W : C} (e : Y ⟶ W)
    (h : ∀ {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e)
    (m : X ⟶ W), f ≫ m = e → m = desc e h

class EffectiveEpi {X Y : C} (f : Y ⟶ X) : Prop where
  cond : Nonempty (EffectiveEpiStruct f)

def isColimitOfEffectiveEpiStruct {X Y : C} (f : Y ⟶ X) (Hf : EffectiveEpiStruct f) :
    IsColimit (Sieve.generate_singleton f : Presieve X).cocone :=
  letI D := FullSubcategory fun T : Over X => Sieve.generate_singleton f T.hom
  letI F : D ⥤ _ := (Sieve.generate_singleton f).arrows.diagram
  { desc := fun S => Hf.desc (S.ι.app ⟨Over.mk f, ⟨𝟙 _, by simp⟩⟩) <| by
      intro Z g₁ g₂ h
      let Y' : D := ⟨Over.mk f, 𝟙 _, by simp⟩
      let Z' : D := ⟨Over.mk (g₁ ≫ f), g₁, rfl⟩
      let g₁' : Z' ⟶ Y' := Over.homMk g₁
      let g₂' : Z' ⟶ Y' := Over.homMk g₂ (by simp [h])
      change F.map g₁' ≫ _ = F.map g₂' ≫ _
      simp only [S.w]
    fac := by
      rintro S ⟨T,g,hT⟩
      dsimp
      nth_rewrite 1 [← hT, Category.assoc, Hf.fac]
      let y : D := ⟨Over.mk f, 𝟙 _, by simp⟩
      let x : D := ⟨Over.mk T.hom, g, hT⟩
      let g' : x ⟶ y := Over.homMk g
      change F.map g' ≫ _ = _
      rw [S.w]
      rfl
    uniq := by
      intro S m hm
      dsimp
      generalize_proofs h1 h2
      apply Hf.uniq _ h2
      exact hm ⟨Over.mk f, 𝟙 _, by simp⟩ }

noncomputable
def effectiveEpiStructOfIsColimit {X Y : C} (f : Y ⟶ X)
    (Hf : IsColimit (Sieve.generate_singleton f : Presieve X).cocone) :
    EffectiveEpiStruct f :=
  let aux {W : C} (e : Y ⟶ W)
    (h : ∀ {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e) :
    Cocone (Sieve.generate_singleton f).arrows.diagram :=
    { pt := W
      ι := {
        app := fun ⟨T,hT⟩ => hT.choose ≫ e
        naturality := by
          rintro ⟨A,hA⟩ ⟨B,hB⟩ (q : A ⟶ B)
          dsimp ; simp only [← Category.assoc, Category.comp_id]
          apply h
          rw [Category.assoc, hB.choose_spec, hA.choose_spec, Over.w] } }
  { desc := fun {W} e h => Hf.desc (aux e h)
    fac := by
      intro W e h
      dsimp
      have := Hf.fac (aux e h) ⟨Over.mk f, 𝟙 _, by simp⟩
      dsimp at this ; rw [this] ; clear this
      nth_rewrite 2 [← Category.id_comp e]
      apply h
      generalize_proofs hh
      rw [hh.choose_spec, Category.id_comp]
    uniq := by
      intro W e h m hm
      dsimp
      apply Hf.uniq (aux e h)
      rintro ⟨A,g,hA⟩
      dsimp
      nth_rewrite 1 [← hA, Category.assoc, hm]
      apply h
      generalize_proofs hh
      rwa [hh.choose_spec] }

theorem Sieve.effectiveEpimorphic_singleton {X Y : C} (f : Y ⟶ X) :
    (Presieve.singleton f).EffectiveEpimorphic ↔ (EffectiveEpi f) := by
  constructor
  · intro (h : Nonempty _)
    rw [Sieve.generate_singleton_eq] at h
    constructor
    apply Nonempty.map (effectiveEpiStructOfIsColimit _) h
  · rintro ⟨h⟩
    show Nonempty _
    rw [Sieve.generate_singleton_eq]
    apply Nonempty.map (isColimitOfEffectiveEpiStruct _) h

end CategoryTheory
