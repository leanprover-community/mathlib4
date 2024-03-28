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
An effective epi family precomposed by a family of split epis is effective epimorphic.
This version takes an explicit section to the split epis, and is mainly used to define
`effectiveEpiStructCompOfEffectiveEpiSplitEpi`,
which takes a `IsSplitEpi` instance instead.
-/
noncomputable
def effectiveEpiFamilyStructCompOfEffectiveEpiSplitEpi' {α : Type*} {B : C} {X Y : α → C}
    (f : (a : α) → X a ⟶ B) (g : (a : α) → Y a ⟶ X a) (i : (a : α) → X a ⟶ Y a)
    (hi : ∀ a, i a ≫ g a = 𝟙 _) [EffectiveEpiFamily _ f] :
    EffectiveEpiFamilyStruct _ (fun a ↦ g a ≫ f a) where
  desc e w := EffectiveEpiFamily.desc _ f (fun a ↦ i a ≫ e a) fun a₁ a₂ g₁ g₂ _ ↦ (by
    simp only [← Category.assoc]
    apply w _ _ (g₁ ≫ i a₁) (g₂ ≫ i a₂)
    simpa [← Category.assoc, hi])
  fac e w a := by
    simp only [Category.assoc, EffectiveEpiFamily.fac]
    rw [← Category.id_comp (e a), ← Category.assoc, ← Category.assoc]
    apply w
    simp only [Category.comp_id, Category.id_comp, ← Category.assoc]
    aesop
  uniq _ _ _ hm := by
    apply EffectiveEpiFamily.uniq _ f
    intro a
    rw [← hm a, ← Category.assoc, ← Category.assoc, hi, Category.id_comp]

/--
An effective epi family precomposed with a family of split epis is effective epimorphic.
-/
noncomputable
def effectiveEpiFamilyStructCompOfEffectiveEpiSplitEpi {α : Type*} {B : C} {X Y : α → C}
    (f : (a : α) → X a ⟶ B) (g : (a : α) → Y a ⟶ X a) [∀ a, IsSplitEpi (g a)]
    [EffectiveEpiFamily _ f] : EffectiveEpiFamilyStruct _ (fun a ↦ g a ≫ f a) :=
  effectiveEpiFamilyStructCompOfEffectiveEpiSplitEpi' f g
    (fun a ↦ section_ (g a))
    (fun a ↦ IsSplitEpi.id (g a))

instance {α : Type*} {B : C} {X Y : α → C}
    (f : (a : α) → X a ⟶ B) (g : (a : α) → Y a ⟶ X a) [∀ a, IsSplitEpi (g a)]
    [EffectiveEpiFamily _ f] : EffectiveEpiFamily _ (fun a ↦ g a ≫ f a) :=
  ⟨⟨effectiveEpiFamilyStructCompOfEffectiveEpiSplitEpi f g⟩⟩

example {B X Y : C} (f : X ⟶ B) (g : Y ⟶ X) [IsSplitEpi g] [EffectiveEpi f] :
    EffectiveEpi (g ≫ f) := inferInstance

instance IsSplitEpi.EffectiveEpi {B X : C} (f : X ⟶ B) [IsSplitEpi f] : EffectiveEpi f := by
  rw [← Category.comp_id f]
  infer_instance

/--
If a family of morphisms with fixed target, precomposed by a family of split epis is
effective epimorphic, then the original family is as well.
This version takes an explicit section to the split epis, and is mainly used to define
`effectiveEpiStructCompOfEffectiveEpiSplitEpi`,
which takes a `IsSplitEpi` instance instead.
-/
noncomputable
def effectiveEpiFamilyStructOfEffectiveEpiSplitEpiComp' {α : Type*} {B : C} {X Y : α → C}
    (f : (a : α) → X a ⟶ B) (g : (a : α) → Y a ⟶ X a) (i : (a : α) → X a ⟶ Y a)
    (hi : ∀ a, i a ≫ g a = 𝟙 _) [EffectiveEpiFamily _ (fun a ↦ g a ≫ f a)] :
    EffectiveEpiFamilyStruct _ f where
  desc e w := EffectiveEpiFamily.desc _ (fun a ↦ g a ≫ f a) (fun a ↦ g a ≫ e a) fun a₁ a₂ g₁ g₂ hg ↦
    (by
      simp only [← Category.assoc] at hg
      simpa using w a₁ a₂ (g₁ ≫ g a₁) (g₂ ≫ g a₂) hg)
  fac e w a := by
    have := EffectiveEpiFamily.fac _ (fun a ↦ g a ≫ f a) (fun a ↦ g a ≫ e a) fun a₁ a₂ g₁ g₂ hg ↦
      (by
        simp only [← Category.assoc] at hg
        simpa using w a₁ a₂ (g₁ ≫ g a₁) (g₂ ≫ g a₂) hg)
    have := congrArg (i a ≫ ·) (this a)
    simp only [← Category.assoc, hi a] at this
    simpa using this
  uniq _ _ _ hm := by
    apply EffectiveEpiFamily.uniq _ (fun a ↦ g a ≫ f a)
    intro a
    rw [← hm, ← Category.assoc]

/--
If a family of morphisms with fixed target, precomposed by a family of split epis is
effective epimorphic, then the original family is as well.
-/
noncomputable
def effectiveEpiFamilyStructOfEffectiveEpiSplitEpiComp {α : Type*} {B : C} {X Y : α → C}
    (f : (a : α) → X a ⟶ B) (g : (a : α) → Y a ⟶ X a) [∀ a, IsSplitEpi (g a)]
    [EffectiveEpiFamily _ (fun a ↦ g a ≫ f a)] : EffectiveEpiFamilyStruct _ f :=
  effectiveEpiFamilyStructOfEffectiveEpiSplitEpiComp' f g
    (fun a ↦ section_ (g a))
    (fun a ↦ IsSplitEpi.id (g a))

lemma effectiveEpiFamily_of_effectiveEpi_splitEpi_comp {α : Type*} {B : C} {X Y : α → C}
    (f : (a : α) → X a ⟶ B) (g : (a : α) → Y a ⟶ X a) [∀ a, IsSplitEpi (g a)]
    [EffectiveEpiFamily _ (fun a ↦ g a ≫ f a)] : EffectiveEpiFamily _ f :=
  ⟨⟨effectiveEpiFamilyStructOfEffectiveEpiSplitEpiComp f g⟩⟩

lemma effectiveEpi_of_effectiveEpi_splitEpi_comp {B X Y : C} (f : X ⟶ B) (g : Y ⟶ X)
    [IsSplitEpi g] [EffectiveEpi (g ≫ f)] : EffectiveEpi f :=
  have := (effectiveEpi_iff_effectiveEpiFamily (g ≫ f)).mp inferInstance
  have := effectiveEpiFamily_of_effectiveEpi_splitEpi_comp
    (X := fun () ↦ X) (Y := fun () ↦ Y) (fun () ↦ f) (fun () ↦ g)
  inferInstance

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

example : EffectiveEpiFamily Y (fun a ↦ i a ≫ π a) :=
  inferInstance

end IsoComp
