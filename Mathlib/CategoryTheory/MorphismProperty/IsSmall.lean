/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.Logic.Small.Basic

/-!
# Small classes of morphisms

A class of morphisms `W : MorphismProperty C` is `w`-small
if the corresponding set in `Set (Arrow C)` is.

-/

universe w t v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace MorphismProperty

variable (W : MorphismProperty C)

/-- A class of morphisms `W : MorphismProperty C` is `w`-small
if the corresponding set in `Set (Arrow C)` is. -/
@[pp_with_univ]
class IsSmall : Prop where
  small_toSet : Small.{w} W.toSet

attribute [instance] IsSmall.small_toSet

instance isSmall_ofHoms {ι : Type t} [Small.{w} ι] {A B : ι → C} (f : ∀ i, A i ⟶ B i) :
    IsSmall.{w} (ofHoms f) := by
  let φ (i : ι) : (ofHoms f).toSet := ⟨Arrow.mk (f i), ⟨i⟩⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨⟨_, _, f⟩, ⟨i⟩⟩
    exact ⟨i, rfl⟩
  exact ⟨small_of_surjective hφ⟩

lemma isSmall_iff_eq_ofHoms :
    IsSmall.{w} W ↔ ∃ (ι : Type w) (A B : ι → C) (f : ∀ i, A i ⟶ B i),
      W = ofHoms f := by
  constructor
  · intro
    refine ⟨Shrink.{w} W.toSet, _, _, fun i ↦ ((equivShrink _).symm i).1.hom, ?_⟩
    ext A B f
    rw [ofHoms_iff]
    constructor
    · intro hf
      exact ⟨equivShrink _ ⟨f, hf⟩, by simp⟩
    · rintro ⟨i, hi⟩
      simp only [← W.arrow_mk_mem_toSet_iff, hi, Arrow.mk_eq, Subtype.coe_prop]
  · rintro ⟨_, _, _, _, rfl⟩
    infer_instance

lemma iSup_ofHoms {α : Type*} {ι : α → Type t} {A B : ∀ a, ι a → C}
    (f : ∀ a, ∀ i, A a i ⟶ B a i) :
    ⨆ (a : α), ofHoms (f a) = ofHoms (fun (j : Σ (a : α), ι a) ↦ f j.1 j.2) := by
  ext f
  simp [ofHoms_iff]

instance {ι : Type t} [Small.{w} ι] (W : ι → MorphismProperty C) [∀ i, IsSmall.{w} (W i)] :
    IsSmall.{w} (⨆ i, W i) := by
  choose α A B f hf using fun i ↦ (isSmall_iff_eq_ofHoms.{w} (W i)).1 inferInstance
  simp only [hf, iSup_ofHoms]
  infer_instance

end MorphismProperty

end CategoryTheory
