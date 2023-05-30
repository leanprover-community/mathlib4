/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/

import Mathlib.CategoryTheory.Sites.Coverage
import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic

/-!

# The Coherent Grothendieck Topology

This file defines the coherent Grothendieck topology (and coverage) on a category `C`.
The category `C` must satisfy a `Precoherent C` condition, which is essentially the minimal
requirement for the coherent coverage to exist.

In `isSheaf_coherent`, we characterize the sheaf condition for presheaves of types for the
coherent Grothendieck topology in terms of finite effective epimorphic families.

-/

namespace CategoryTheory

open Limits

variable (C : Type _) [Category C]

/--
The condition `Precoherent C` is essentially the minimal condition required to define the
coherent coverage on `C`.
-/
class Precoherent : Prop where
  cond {B₁ B₂ : C} (f : B₂ ⟶ B₁) :
    ∀ (α : Type) [Fintype α] (X₁ : α → C) (π₁ : (a : α) → (X₁ a ⟶ B₁)),
      (Presieve.ofArrows X₁ π₁).EffectiveEpimorphic →
    ∃ (β : Type) (_ : Fintype β) (X₂ : β → C) (π₂ : (b : β) → (X₂ b ⟶ B₂)),
      (Presieve.ofArrows X₂ π₂).EffectiveEpimorphic ∧
      ∃ (i : β → α) (ι : (b :  β) → (X₂ b ⟶ X₁ (i b))),
      ∀ (b : β), ι b ≫ π₁ _ = π₂ _ ≫ f
/--
The coherent coverage on a precoherent category `C`.
-/
def CoherentCoverage [Precoherent C] : Coverage C where
  covering B := { S | ∃ (α : Type) (_ : Fintype α) (X : α → C) (π : (a : α) → (X a ⟶ B)),
    S = Presieve.ofArrows X π ∧ (Sieve.generate S).EffectiveEpimorphic }
  pullback := by
    rintro B₁ B₂ f S ⟨α, _, X₁, π₁, rfl, hS⟩
    obtain ⟨β,_,X₂,π₂,h,i,ι,hh⟩ := Precoherent.cond f α X₁ π₁ hS
    refine ⟨Presieve.ofArrows X₂ π₂, ⟨β, inferInstance, X₂, π₂, rfl, h⟩, ?_⟩
    rintro _ _ ⟨b⟩
    refine ⟨(X₁ (i b)), ι _, π₁ _, ⟨_⟩, hh _⟩

/--
The coherent Grothendieck topology on a precoherent category `C`.
-/
def CoherentTopology [Precoherent C] : GrothendieckTopology C :=
  Coverage.toGrothendieck _ <| CoherentCoverage C

lemma isSheaf_coherent_aux [Precoherent C] (P : Cᵒᵖ ⥤ Type w) :
    Presieve.IsSheaf (CoherentTopology C) P ↔
    (∀ (B : C) (α : Type) [Fintype α] (X : α → C) (π : (a : α) → (X a ⟶ B)),
      (Presieve.ofArrows X π).EffectiveEpimorphic →
      (Presieve.ofArrows X π).IsSheafFor P) := by
  constructor
  · intro hP B α _ X π h
    dsimp only [CoherentTopology] at hP
    rw [Presieve.isSheaf_coverage] at hP
    apply hP
    dsimp only [CoherentCoverage]
    refine ⟨α, inferInstance, X, π, rfl, h⟩
  · intro h
    dsimp only [CoherentTopology]
    rw [Presieve.isSheaf_coverage]
    rintro B S ⟨α, _, X, π, rfl, hS⟩
    exact h _ _ _ _ hS

lemma isSheaf_coherent [Precoherent C] (P : Cᵒᵖ ⥤ Type w) :
    Presieve.IsSheaf (CoherentTopology C) P ↔
    (∀ (B : C) (α : Type) [Fintype α] (X : α → C) (π : (a : α) → (X a ⟶ B)),
      EffectiveEpiFamily X π → (Presieve.ofArrows X π).IsSheafFor P) := by
  simp [isSheaf_coherent_aux, Sieve.effectiveEpimorphic_family]

end CategoryTheory
