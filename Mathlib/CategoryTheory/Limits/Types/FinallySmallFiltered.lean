/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Filtered.FinallySmall
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Colimits of types indexed by finally small filtered categories

We deduce properties of colimits of types indexed by finally small filtered
categories from results about filtered colimits.

-/

@[expose] public section

universe w t v' u' v u

namespace CategoryTheory.FinallySmallFiltered

open Limits

variable {J : Type u} [Category.{v} J] [FinallySmallFiltered.{w} J]
  {F : J ⥤ Type t} {c : Cocone F} (hc : IsColimit c)

include hc

lemma jointly_surjective₂_of_isColimit (z₁ z₂ : c.pt) :
    ∃ (j : J) (x₁ x₂ : F.obj j), c.ι.app j x₁ = z₁ ∧ c.ι.app j x₂ = z₂ := by
  obtain ⟨j₁, y₁, rfl⟩ := Types.jointly_surjective_of_isColimit hc z₁
  obtain ⟨j₂, y₂, rfl⟩ := Types.jointly_surjective_of_isColimit hc z₂
  let k₁ : StructuredArrow j₁ (fromFilteredFinalModel.{w} J) := Classical.arbitrary _
  let k₂ : StructuredArrow j₂ (fromFilteredFinalModel.{w} J) := Classical.arbitrary _
  exact ⟨(fromFilteredFinalModel.{w} J).obj (IsFiltered.max k₁.right k₂.right), _, _,
    congr_fun (c.w (k₁.hom ≫ (fromFilteredFinalModel.{w} J).map
      (IsFiltered.leftToMax k₁.right k₂.right))) y₁,
    congr_fun (c.w (k₂.hom ≫ (fromFilteredFinalModel.{w} J).map
      (IsFiltered.rightToMax k₁.right k₂.right))) y₂,⟩

lemma eq_iff_of_isColimit {j : J} (x₁ x₂ : F.obj j) :
    c.ι.app j x₁ = c.ι.app j x₂ ↔
      ∃ (k : J) (f : j ⟶ k), F.map f x₁ = F.map f x₂ := by
  refine ⟨fun h ↦ ?_, fun ⟨k, f, hf⟩ ↦ by simp [← congr_fun (c.w f), hf]⟩
  let D := FilteredFinalModel.{w} J
  let G := fromFilteredFinalModel.{w} J
  wlog hj : ∃ i, G.obj i = j generalizing j
  · let k : StructuredArrow j G := Classical.arbitrary _
    obtain ⟨l, f, hl⟩ := this (F.map k.hom x₁) (F.map k.hom x₂) (by
      have := congr_fun (c.w k.hom)
      dsimp at this
      simpa [this]) ⟨_, rfl⟩
    exact ⟨l, k.hom ≫ f, by simpa⟩
  obtain ⟨i, rfl⟩ := hj
  obtain ⟨k, f, hk⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    ((Functor.Final.isColimitWhiskerEquiv G _).2 hc) (x := x₁) (y := x₂)).1 h
  exact ⟨G.obj k, G.map f, hk⟩

end CategoryTheory.FinallySmallFiltered
