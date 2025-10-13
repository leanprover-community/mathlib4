/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

/-!
# Monomorphisms in Grothendieck abelian categories

In this file, we show that in a Grothendieck abelian category,
monomorphisms are stable under transfinite composition.

-/

universe w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

namespace MorphismProperty.TransfiniteCompositionOfShape

variable {J : Type w} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
  {X Y : C} {f : X ⟶ Y} (h : (monomorphisms C).TransfiniteCompositionOfShape J f)

attribute [local instance] IsCofiltered.isConnected

namespace mono

instance map_bot_le (j : J) : Mono (h.F.map (homOfLE bot_le : ⊥ ⟶ j)) := by
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl := hj.eq_bot
    exact inferInstanceAs (Mono (h.F.map (𝟙 _)))
  | succ j hj hj' =>
    have : Mono _ := h.map_mem j hj
    rw [← homOfLE_comp bot_le (Order.le_succ j), Functor.map_comp]
    infer_instance
  | isSuccLimit j hj hj' =>
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
    have : Mono φ := NatTrans.mono_of_mono_app φ
    apply colim.map_mono' φ
      (isColimitConstCocone (Set.Iio j) (h.F.obj ⊥))
      (h.F.isColimitOfIsWellOrderContinuous j hj)
    rintro k
    dsimp [φ]
    rw [Category.id_comp, ← Functor.map_comp]
    rfl

end mono

include h in
lemma mono : Mono f := by
  let φ : (Functor.const _).obj X ⟶ h.F :=
    { app k := h.isoBot.inv ≫ h.F.map (homOfLE bot_le)
      naturality k k' hkk' := by
        dsimp
        rw [Category.id_comp, Category.assoc, ← Functor.map_comp]
        rfl }
  have : Mono φ := NatTrans.mono_of_mono_app φ
  exact colim.map_mono' φ (isColimitConstCocone J X) (h.isColimit) f (by cat_disch)

instance mono_map (j j' : J) (f : j ⟶ j') : Mono (h.F.map f) :=
  ((h.ici j).iic ⟨j', leOfHom f⟩).mono

end MorphismProperty.TransfiniteCompositionOfShape

namespace IsGrothendieckAbelian

open MorphismProperty

instance : IsStableUnderTransfiniteComposition.{w} (monomorphisms C) where
  isStableUnderTransfiniteCompositionOfShape _ _ _ _ _ :=
    ⟨fun _ _ _ ⟨hf⟩ ↦ hf.mono⟩

end IsGrothendieckAbelian

end CategoryTheory
