/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Localization.CalculusOfFractions

/-!
# The calculus of fractions deduced from an adjunction

If `G ⊣ F` is an adjunction, and `F` is fully faithful,
then there is a left calculus of fractions for
the inverse image by `G` of the class of isomorphisms.

(The dual statement is also obtained.)

-/

namespace CategoryTheory

open MorphismProperty

namespace Adjunction

variable {C₁ C₂ : Type*} [Category C₁] [Category C₂]
  {G : C₁ ⥤ C₂} {F : C₂ ⥤ C₁} [F.Full] [F.Faithful]

lemma hasLeftCalculusOfFractions (adj : G ⊣ F) :
    ((isomorphisms C₂).inverseImage G).HasLeftCalculusOfFractions where
  exists_leftFraction X Y φ := by
    obtain ⟨W, s, _, f, rfl⟩ := φ.cases
    have : IsIso (G.map s) := by assumption
    exact ⟨{
      f := adj.unit.app X ≫ F.map (inv (G.map s)) ≫ F.map (G.map f)
      s := adj.unit.app Y
      hs := by
        simp only [inverseImage_iff, isomorphisms.iff]
        infer_instance }, by
      have := adj.unit.naturality s
      dsimp at this ⊢
      rw [reassoc_of% this, Functor.map_inv, IsIso.hom_inv_id_assoc, adj.unit_naturality]⟩
  ext X' X Y f₁ f₂ s _ h := by
    have : IsIso (G.map s) := by assumption
    refine ⟨_, adj.unit.app Y, ?_, ?_⟩
    · simp only [inverseImage_iff, isomorphisms.iff]
      infer_instance
    · rw [← adj.unit_naturality f₁, ← adj.unit_naturality f₂]
      congr 2
      rw [← cancel_epi (G.map s), ← G.map_comp, ← G.map_comp, h]

lemma hasRightCalculusOfFractions (adj : F ⊣ G) :
    ((isomorphisms C₂).inverseImage G).HasRightCalculusOfFractions := by
  suffices ((isomorphisms C₂).inverseImage G).op.HasLeftCalculusOfFractions from
    inferInstanceAs ((isomorphisms C₂).inverseImage G).op.unop.HasRightCalculusOfFractions
  simpa only [← isomorphisms_op] using adj.op.hasLeftCalculusOfFractions

end Adjunction

end CategoryTheory
