/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

/-!
# Stability properties of monomorphisms in Type

In this file, we show that in the category `Type u`, monomorphisms
are stable under cobase change, filtered colimits and
transfinite compositions.
(The stability by retracts holds in any category: it is shown
in the file `CategoryTheory.MorphismProperty.Retract`.)

-/

universe v' u' u

namespace CategoryTheory

open MorphismProperty Limits Types

namespace Types

instance : (monomorphisms (Type u)).IsStableUnderCobaseChange where
  of_isPushout {X₁ X₂ X₃ X₄ t l r b} sq ht := by
    simp only [monomorphisms.iff, mono_iff_injective] at ht ⊢
    exact Limits.Types.pushoutCocone_injective_inr_of_isColimit sq.flip.isColimit ht

lemma isStableUnderColimitsOfShape_monomorphisms_of_isFiltered
    (J : Type u') [Category.{v'} J] [IsFiltered J] :
    (monomorphisms (Type u)).IsStableUnderColimitsOfShape J := by
  intro F₁ F₂ c₁ c₂ hc₁ hc₂ f hf
  simp only [functorCategory, monomorphisms.iff, mono_iff_injective] at hf
  let φ : c₁.pt ⟶ c₂.pt := hc₁.desc { ι := f ≫ c₂.ι }
  have hφ (j : J) : c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j := hc₁.fac _ j
  replace hφ (j : J) := congr_fun (hφ j)
  dsimp at hφ
  change Mono φ
  rw [mono_iff_injective]
  intro x₁ y₁ h
  obtain ⟨j, x₁, y₁, rfl, rfl⟩ : ∃ (j : J) (x₁' y₁' : F₁.obj j),
      x₁ = c₁.ι.app j x₁' ∧ y₁ = c₁.ι.app j y₁' := by
    obtain ⟨j, x₁, rfl⟩ := jointly_surjective_of_isColimit hc₁ x₁
    obtain ⟨l, y₁, rfl⟩ := jointly_surjective_of_isColimit hc₁ y₁
    exact ⟨_,  _, _, congr_fun (c₁.w (IsFiltered.leftToMax j l)).symm _,
      congr_fun (c₁.w (IsFiltered.rightToMax j l)).symm _⟩
  rw [hφ, hφ] at h
  obtain ⟨k, α, hk⟩ := (FilteredColimit.isColimit_eq_iff' hc₂ _ _).1 h
  simp only [← FunctorToTypes.naturality] at hk
  rw [← c₁.w α, types_comp_apply, types_comp_apply, hf _ hk]

section

variable {J : Type u'} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]

namespace isStableUnderTransfiniteCompositionOfShape_monomorphisms

variable {X Y : Type u} {f : X ⟶ Y}
  (h : (monomorphisms (Type u)).TransfiniteCompositionOfShape J f)

attribute [local instance] IsCofiltered.isConnected

instance (j : J) : Mono (h.F.map (homOfLE bot_le : ⊥ ⟶ j)) := by
  induction j using SuccOrder.limitRecOn with
  | hm j hj =>
    obtain rfl := hj.eq_bot
    exact inferInstanceAs (Mono (h.F.map (𝟙 _)))
  | hs j hj hj' =>
    have : Mono _ := h.map_mem j hj
    rw [← homOfLE_comp bot_le (Order.le_succ j), Functor.map_comp]
    infer_instance
  | hl j hj hj' =>
    have : OrderBot (Set.Iio j) :=
      { bot := ⟨⊥, Order.IsSuccLimit.bot_lt hj ⟩
        bot_le _ := bot_le }
    let φ : (Functor.const _).obj (h.F.obj ⊥) ⟶
        (Set.principalSegIio j).monotone.functor ⋙ h.F :=
      { app k := h.F.map (homOfLE bot_le)
        naturality k k' hkk' := by
          dsimp
          rw [Category.id_comp, ← Functor.map_comp]
          rfl }
    have (k : Set.Iio j) : Mono (φ.app k) := hj' k.1 k.2
    convert isStableUnderColimitsOfShape_monomorphisms_of_isFiltered _ _ _ _ _
      (isColimitConstCocone (Set.Iio j) (h.F.obj ⊥))
      (h.F.isColimitOfIsWellOrderContinuous j hj) φ
        (fun _ ↦ monomorphisms.infer_property _)
    apply (isColimitConstCocone (Set.Iio j) (h.F.obj ⊥)).hom_ext
    intro j
    rw [IsColimit.fac]
    dsimp [φ]
    simp only [Category.id_comp, ← Functor.map_comp, homOfLE_comp]

include h in
lemma mono : Mono f := by
  let φ : (Functor.const _).obj X ⟶ h.F :=
    { app k := h.isoBot.inv ≫ h.F.map (homOfLE bot_le)
      naturality k k' hkk' := by
        dsimp
        rw [Category.id_comp, Category.assoc, ← Functor.map_comp]
        rfl }
  convert isStableUnderColimitsOfShape_monomorphisms_of_isFiltered J _ _ _ _
    (isColimitConstCocone J X) h.isColimit φ (fun _ ↦ monomorphisms.infer_property _)
  apply (isColimitConstCocone J X).hom_ext
  intro j
  rw [IsColimit.fac]
  simp [φ]

end isStableUnderTransfiniteCompositionOfShape_monomorphisms

instance : (monomorphisms (Type u)).IsStableUnderTransfiniteCompositionOfShape J where
  le := by
    rintro X Y f ⟨hf⟩
    exact isStableUnderTransfiniteCompositionOfShape_monomorphisms.mono hf

instance : IsStableUnderTransfiniteComposition.{u'} (monomorphisms (Type u)) where

end

end Types

end CategoryTheory
