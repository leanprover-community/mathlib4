/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.Bousfield
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
import Mathlib.CategoryTheory.SmallObject.WellOrderInductionData

/-!
# LeftBousfield.W is stable under transfinite compositions

If `P : ObjectProperty C`, then `Localization.LeftBousfield.W P : MorphismProperty C`
is stable under transfinite compositions.

-/

universe w v u

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} [Category.{v} C]

namespace Localization.LeftBousfield

variable (P : ObjectProperty C)

instance (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J] :
    (W P).IsStableUnderTransfiniteCompositionOfShape J where
  le := fun X Y f ⟨hf⟩ Z hZ ↦ by
    refine ⟨fun g₁ g₂ h ↦ hf.isColimit.hom_ext (fun j ↦ ?_), fun g ↦ ?_⟩
    · dsimp at h ⊢
      induction j using SuccOrder.limitRecOn with
      | isMin j hj =>
        obtain rfl := hj.eq_bot
        simpa [← cancel_epi hf.isoBot.inv]
      | succ j hj hj' => exact (hf.map_mem j hj _ hZ).1 (by simpa)
      | isSuccLimit j hj hj' =>
        exact (hf.F.isColimitOfIsWellOrderContinuous j hj).hom_ext
          (fun ⟨k, hk⟩ ↦ by simpa using hj' _ hk)
    · let d : (hf.F.op ⋙ yoneda.obj Z).WellOrderInductionData :=
        .ofExists (fun j hj ↦ (hf.map_mem j hj _ hZ).2) (fun j hj s ↦ by
          let c : Cocone ((Set.principalSegIio j).monotone.functor ⋙ hf.F) :=
            { pt := Z
              ι.app k := s.1 (op k)
              ι.naturality _ _ g := by
                dsimp
                simpa only [Category.comp_id] using s.2 g.op }
          exact ⟨(hf.F.isColimitOfIsWellOrderContinuous j hj).desc c, fun k hk ↦
            by simpa using (hf.F.isColimitOfIsWellOrderContinuous j hj).fac c ⟨k, hk⟩⟩)
      let σ := d.sectionsMk (hf.isoBot.hom ≫ g)
      let c : Cocone hf.F :=
        { pt := Z
          ι.app j := σ.1 (op j)
          ι.naturality _ _ f := by
            dsimp
            simpa only [Category.comp_id] using σ.2 f.op }
      exact ⟨hf.isColimit.desc c, by
        simp only [← hf.fac, Category.assoc, hf.isColimit.fac c ⊥, c, σ,
          d.sectionsMk_val_op_bot, Iso.inv_hom_id_assoc]⟩

instance : MorphismProperty.IsStableUnderTransfiniteComposition.{w} (W P) where

end Localization.LeftBousfield

end CategoryTheory
