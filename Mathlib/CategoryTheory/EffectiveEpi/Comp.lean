/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.EffectiveEpi.Basic
/-!

# Composition of effective epimorphisms

This file provides `EffectiveEpi` instances for certain compositions.

-/

namespace CategoryTheory

open Limits

variable {C : Type*} [Category C]

/--
A split epi followed by an effective epi is an effective epi. This version takes an explicit section
to the split epi, and is mainly used to define `effectiveEpiStructCompOfEffectiveEpiSplitEpi`,
which takes a `IsSplitEpi` instance instead.
-/
noncomputable
def effectiveEpiStructCompOfEffectiveEpiSplitEpi' {B X Y : C} (f : X ⟶ B) (g : Y ⟶ X) (i : X ⟶ Y)
    (hi : i ≫ g = 𝟙 _) [EffectiveEpi f] : EffectiveEpiStruct (g ≫ f) where
  desc e w := EffectiveEpi.desc f (i ≫ e) fun g₁ g₂ _ ↦ (by
    simp only [← Category.assoc]
    apply w (g₁ ≫ i) (g₂ ≫ i)
    simpa [← Category.assoc, hi])
  fac e w := by
    simp only [Category.assoc, EffectiveEpi.fac]
    rw [← Category.id_comp e, ← Category.assoc, ← Category.assoc]
    apply w
    simp only [Category.comp_id, Category.id_comp, ← Category.assoc]
    aesop
  uniq _ _ _ hm := by
    apply EffectiveEpi.uniq f
    rw [← hm, ← Category.assoc, ← Category.assoc, hi, Category.id_comp]

/-- A split epi followed by an effective epi is an effective epi. -/
noncomputable
def effectiveEpiStructCompOfEffectiveEpiSplitEpi {B X Y : C} (f : X ⟶ B) (g : Y ⟶ X) [IsSplitEpi g]
    [EffectiveEpi f] : EffectiveEpiStruct (g ≫ f) :=
  effectiveEpiStructCompOfEffectiveEpiSplitEpi' f g
    (IsSplitEpi.exists_splitEpi (f := g)).some.section_
    (IsSplitEpi.exists_splitEpi (f := g)).some.id

instance {B X Y : C} (f : X ⟶ B) (g : Y ⟶ X) [IsSplitEpi g] [EffectiveEpi f] :
    EffectiveEpi (g ≫ f) := ⟨⟨effectiveEpiStructCompOfEffectiveEpiSplitEpi f g⟩⟩

section CompIso

variable {B B' : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B)) [EffectiveEpiFamily X π]
  (i : B ⟶ B') [IsIso i]

theorem effectiveEpiFamilyStructCompIso_aux
    {W : C} (e : (a : α) → X a ⟶ W)
    (h : ∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π a₁ ≫ i = g₂ ≫ π a₂ ≫ i → g₁ ≫ e a₁ = g₂ ≫ e a₂)
    {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂) (hg : g₁ ≫ π a₁ = g₂ ≫ π a₂) :
    g₁ ≫ e a₁ = g₂ ≫ e a₂ := by
  apply h
  rw [← Category.assoc, hg]
  simp

/-- An effective epi family followed by an iso is an effective epi family. -/
noncomputable
def effectiveEpiFamilyStructCompIso : EffectiveEpiFamilyStruct X (fun a ↦ π a ≫ i) where
  desc e h := inv i ≫ EffectiveEpiFamily.desc X π e (effectiveEpiFamilyStructCompIso_aux X π i e h)
  fac _ _ _ := by simp
  uniq e h m hm := by
    simp only [Category.assoc] at hm
    simp [← EffectiveEpiFamily.uniq X π e
      (effectiveEpiFamilyStructCompIso_aux X π i e h) (i ≫ m) hm]

instance : EffectiveEpiFamily X (fun a ↦ π a ≫ i) := ⟨⟨effectiveEpiFamilyStructCompIso X π i⟩⟩

end CompIso

section IsoComp

variable {B : C} {α : Type*} (X Y : α → C) (π : (a : α) → (X a ⟶ B)) [EffectiveEpiFamily X π]
  (i : (a : α) → Y a ⟶ X a) [∀ a, IsIso (i a)]

theorem effectiveEpiFamilyStructIsoComp_aux {W : C} (e : (a : α) → Y a ⟶ W)
    (h : ∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ Y a₁) (g₂ : Z ⟶ Y a₂),
      g₁ ≫ i a₁ ≫ π a₁ = g₂ ≫ i a₂ ≫ π a₂ → g₁ ≫ e a₁ = g₂ ≫ e a₂)
    {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂) (hg : g₁ ≫ π a₁ = g₂ ≫ π a₂) :
    g₁ ≫ (fun a ↦ inv (i a) ≫ e a) a₁ = g₂ ≫ (fun a ↦ inv (i a) ≫ e a) a₂ := by
  simp only [← Category.assoc]
  apply h
  simp [hg]

/-- An effective epi family preceded by a family of isos is an effective epi family. -/
noncomputable
def effectiveEpiFamilyStructIsoComp : EffectiveEpiFamilyStruct Y (fun a ↦ i a ≫ π a) where
  desc e h := EffectiveEpiFamily.desc X π (fun a ↦ inv (i a) ≫ e a)
    (effectiveEpiFamilyStructIsoComp_aux X Y π i e h)
  fac _ _ _ := by simp
  uniq e h m hm := by
    simp only [Category.assoc] at hm
    simp [← EffectiveEpiFamily.uniq X π (fun a ↦ inv (i a) ≫ e a)
      (effectiveEpiFamilyStructIsoComp_aux X Y π i e h) m fun a ↦ by simpa using hm a]

instance effectiveEpiFamilyIsoComp : EffectiveEpiFamily Y (fun a ↦ i a ≫ π a) :=
  ⟨⟨effectiveEpiFamilyStructIsoComp X Y π i⟩⟩

end IsoComp
