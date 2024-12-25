/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.Logic.Small.Basic

/-!
# Small classes of morphisms

-/

universe w t v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

-- to be moved
lemma Arrow.ext {C : Type u} [Category.{v} C] {f g : Arrow C}
    (h₁ : f.left = g.left) (h₂ : f.right = g.right)
    (h₃ : f.hom = eqToHom h₁ ≫ g.hom ≫ eqToHom h₂.symm) : f = g := by
  obtain ⟨X, Y, f⟩ := f
  obtain ⟨X', Y', g⟩ := g
  obtain rfl : X = X' := h₁
  obtain rfl : Y = Y' := h₂
  obtain rfl : f = g := by simpa using h₃
  rfl

namespace MorphismProperty

variable (W : MorphismProperty C)

def toSet : Set (Arrow C) := setOf (fun f ↦ W f.hom)

def homFamily (f : W.toSet) : f.1.left ⟶ f.1.right := f.1.hom

@[simp]
lemma arrow_mk_mem_toSet_iff {X Y : C} (f : X ⟶ Y) : Arrow.mk f ∈ W.toSet ↔ W f := Iff.rfl

lemma ofHoms_iff {ι : Type*} {X Y : ι → C} (f : ∀ i, X i ⟶ Y i) {A B : C} (g : A ⟶ B) :
    ofHoms f g ↔ ∃ i, Arrow.mk g = Arrow.mk (f i) := by
  constructor
  · rintro ⟨i⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, h⟩
    rw [← (ofHoms f).arrow_mk_mem_toSet_iff, h, arrow_mk_mem_toSet_iff]
    constructor

@[simp]
lemma ofHoms_homFamily : ofHoms W.homFamily = W := by
  ext _ _ f
  constructor
  · intro hf
    rw [ofHoms_iff] at hf
    obtain ⟨⟨f, hf⟩, ⟨_, _⟩⟩ := hf
    exact hf
  · intro hf
    exact ⟨(⟨f, hf⟩ : W.toSet)⟩

@[pp_with_univ]
class IsSmall : Prop where
  small_toSet : Small.{w} W.toSet

attribute [instance] IsSmall.small_toSet

instance isSmall_ofHoms {ι : Type t} [Small.{w} ι] {A B : ι → C} (f : ∀ i, A i ⟶ B i) :
    IsSmall.{w} (ofHoms f) := by
  let φ (i : Shrink.{w} ι) : (ofHoms f).toSet :=
    ⟨Arrow.mk (f ((equivShrink _).symm i)), ⟨(equivShrink _).symm i⟩⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨⟨_, _, f⟩, ⟨i⟩⟩
    refine ⟨equivShrink _ i, ?_⟩
    simp only [Subtype.mk.injEq, φ]
    fapply Arrow.ext <;> simp
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

end MorphismProperty

end CategoryTheory
