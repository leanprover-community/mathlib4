/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.CategoryTheory.Sites.Pretopology
import Mathlib.Data.Set.Finite.Lattice

/-! # The Finite Pretopology

In this file we define the finite pretopology on a category, which consists of presieves that
contain only finitely many arrows.

## Main Definitions

- `CategoryTheory.Pretopology.finite`: The finite pretopology on a category.
-/

universe v v₁ u u₁

namespace CategoryTheory

open Limits

namespace Presieve

variable {C : Type u} [Category.{v} C] {X : C} (s : Presieve X)
  {D : Type u₁} [Category.{v₁} D] (F : C ⥤ D)

@[ext] lemma ext {s₁ s₂ : Presieve X} (h : ∀ Y : C, @s₁ Y = @s₂ Y) : s₁ = s₂ :=
  funext h

/-- Uncurry a presieve to one set over the sigma type. -/
def uncurry : Set (Σ Y, Y ⟶ X) :=
  { u | s u.snd }

@[simp] theorem uncurry_singleton {Y : C} (u : Y ⟶ X) : (singleton u).uncurry = { ⟨Y, u⟩ } := by
  ext ⟨Z, v⟩; constructor
  · rintro ⟨⟩; rfl
  · intro h
    rw [Set.mem_singleton_iff, Sigma.ext_iff] at h
    obtain ⟨rfl, h⟩ := h; subst h; constructor

/-- The uncurried version of `pullbackArrows`. -/
@[simp] noncomputable nonrec
def _root_.Sigma.pullback [HasPullbacks C] {B : C} (b : B ⟶ X) (f : Σ Y, Y ⟶ X) : Σ Y, Y ⟶ B :=
  ⟨pullback f.2 b, pullback.snd _ _⟩

@[simp] theorem uncurry_pullbackArrows [HasPullbacks C] {B : C} (b : B ⟶ X) :
    (pullbackArrows b s).uncurry = Sigma.pullback b '' s.uncurry := by
  ext ⟨Z, v⟩; constructor
  · rintro ⟨Y, u, hu⟩; exact ⟨⟨Y, u⟩, hu, rfl⟩
  · rintro ⟨⟨Y, u⟩, hu, h⟩
    rw [Sigma.ext_iff] at h
    obtain ⟨rfl, h⟩ := h
    rw [heq_iff_eq] at h; subst h
    exact ⟨Y, u, hu⟩

/-- The uncurried version of composing on the right. -/
@[simp]
def _root_.Sigma.map_hom {Y : C} (u : Y ⟶ X) (f : Σ Z, Z ⟶ Y) : Σ Z, Z ⟶ X :=
  ⟨f.1, f.2 ≫ u⟩

@[simp] theorem uncurry_bind (t : ⦃Y : C⦄ → (f : Y ⟶ X) → s f → Presieve Y) :
    (s.bind t).uncurry = ⋃ i ∈ s.uncurry, Sigma.map_hom i.2 '' (t _ ‹_›).uncurry := by
  ext ⟨Z, v⟩; simp only [Set.mem_iUnion, Set.mem_image]; constructor
  · rintro ⟨Y, g, f, hf, ht, hv⟩
    exact ⟨⟨_, f⟩, hf, ⟨_, g⟩, ht, Sigma.ext rfl (heq_of_eq hv)⟩
  · rintro ⟨⟨_, f⟩, hf, ⟨Y, g⟩, hg, h⟩
    rw [Sigma.ext_iff] at h
    obtain ⟨rfl, h⟩ := h
    rw [heq_iff_eq] at h; subst h
    exact ⟨_, _, _, _, hg, rfl⟩

/-- This presieve generates `functorPushforward`. -/
inductive map : Presieve (F.obj X) where
  | of {Y : C} {u : Y ⟶ X} (h : s u) : map (F.map u)

end Presieve

namespace Pretopology

open Presieve

/-- The finite pretopology on a category consists of finite presieves, i.e. a presieve with finitely
many maps after uncurrying. -/
def finite (C : Type u) [Category.{v} C] [HasPullbacks C] : Pretopology C where
  coverings X := { s : Presieve X | s.uncurry.Finite }
  has_isos X Y f _ := by simp
  pullbacks X Y u s hs := by simpa using hs.image _
  transitive X s t hs ht := by simpa using hs.biUnion' fun _ _ ↦ (ht _ _).image _

end Pretopology

end CategoryTheory
