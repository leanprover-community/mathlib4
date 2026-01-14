/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Multiequalizer
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Types.Set
import Mathlib.Data.Set.BooleanAlgebra
import Mathlib.Order.CompleteLattice.MulticoequalizerDiagram

/-!
# Multicoequalizers in the category of types

Given `J : MultispanShape`, `d : MultispanIndex J (Type u)` and
`c : d.multispan.CoconeTypes`, we obtain a lemma `isMulticoequalizer_iff`
which gives a criteria for `c` to be a colimit (i.e. a multicoequalizer):
it restates in a more explicit manner the injectivity and surjectivity
conditions for the map `d.multispan.descColimitType c : d.multispan.ColimitType → c.pt`.

We deduce a definition `Set.isColimitOfMulticoequalizerDiagram` which shows
that given `X : Type u`, a `MulticoequalizerDiagram` in `Set X` gives
a multicoequalizer in the category of types.

-/

universe w w' u

namespace CategoryTheory.Functor.CoconeTypes

open Limits

lemma isMulticoequalizer_iff {J : MultispanShape.{w, w'}} {d : MultispanIndex J (Type u)}
    (c : d.multispan.CoconeTypes) :
    c.IsColimit ↔
      (∀ (i₁ i₂ : J.R) (x₁ : d.right i₁) (x₂ : d.right i₂),
        c.ι (.right i₁) x₁ = c.ι (.right i₂) x₂ →
          d.multispan.ιColimitType (.right i₁) x₁ = d.multispan.ιColimitType (.right i₂) x₂) ∧
      (∀ (x : c.pt), ∃ (i : J.R) (a : d.right i), c.ι (.right i) a = x) := by
  have (x : d.multispan.ColimitType) :
      ∃ (i : J.R) (a : d.right i), d.multispan.ιColimitType (.right i) a = x := by
    obtain ⟨(l | r), z, rfl⟩ := d.multispan.ιColimitType_jointly_surjective x
    · exact ⟨J.fst l, d.multispan.map (WalkingMultispan.Hom.fst l) z,
        by rw [ιColimitType_map]⟩
    · exact ⟨r, z, by simp⟩
  constructor
  · intro hc
    refine ⟨fun i₁ i₂ x₁ x₂ h ↦ ?_, ?_⟩
    · simp only [← descColimitType_ιColimitType_apply] at h
      exact hc.bijective.1 h
    · intro x
      obtain ⟨y, rfl⟩ := hc.bijective.2 x
      obtain ⟨i, z, rfl⟩ := this y
      exact ⟨i, z, by simp⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun x₁ x₂ h ↦ ?_, fun x ↦ ?_⟩
    · obtain ⟨i₁, a₁, rfl⟩ := this x₁
      obtain ⟨i₂, a₂, rfl⟩ := this x₂
      exact h₁ _ _ _ _ h
    · obtain ⟨i, y, rfl⟩ := h₂ x
      exact ⟨d.multispan.ιColimitType (.right i) y, rfl⟩

end CategoryTheory.Functor.CoconeTypes

open CompleteLattice CategoryTheory Limits

namespace CategoryTheory.Limits.Types

variable {X : Type u} {ι : Type w} {A : Set X} {U : ι → Set X} {V : ι → ι → Set X}

/-- Given `X : Type u`, `A : Set X`, `U : ι → Set X` and `V : ι → ι → Set X` such
that `MulticoequalizerDiagram A U V` holds, then in the category of types,
`A` is the multicoequalizer of the `U i`s along the `V i j`s. -/
noncomputable def isColimitOfMulticoequalizerDiagram
    (c : MulticoequalizerDiagram A U V) :
    IsColimit (c.multicofork.map Set.functorToTypes) := by
  let e := (c.multispanIndex.map Set.functorToTypes).multispan
  apply _root_.Nonempty.some
  rw [Types.isColimit_iff_coconeTypesIsColimit,
    Functor.CoconeTypes.isMulticoequalizer_iff]
  refine ⟨fun i₁ i₂ ⟨x₁, h₁⟩ ⟨x₂, h₂⟩ h ↦ ?_, fun ⟨x, hx⟩ ↦ ?_⟩
  · dsimp at i₁ i₂ h₁ h₂
    obtain rfl : x₁ = x₂ := by simpa using h
    have eq₁ := e.ιColimitType_map (WalkingMultispan.Hom.fst (J := .prod ι) ⟨i₁, i₂⟩)
      ⟨x₁, by dsimp; rw [c.min_eq]; exact ⟨h₁, h₂⟩⟩
    have eq₂ := e.ιColimitType_map (WalkingMultispan.Hom.snd (J := .prod ι) ⟨i₁, i₂⟩)
      ⟨x₁, by dsimp; rw [c.min_eq]; exact ⟨h₁, h₂⟩⟩
    dsimp [e] at eq₁ eq₂
    rw [eq₁, eq₂]
  · simp only [MulticoequalizerDiagram.multicofork_pt, ← c.iSup_eq,
      Set.iSup_eq_iUnion, Set.mem_iUnion] at hx
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, ⟨x, hi⟩, rfl⟩

end CategoryTheory.Limits.Types
