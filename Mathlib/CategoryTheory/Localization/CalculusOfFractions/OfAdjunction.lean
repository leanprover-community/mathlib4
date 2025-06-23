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
  {G : C₁ ⥤ C₂} {F : C₂ ⥤ C₁}

lemma isLocalization_leftAdjoint [F.Full] [F.Faithful]
    (adj : G ⊣ F) (W : MorphismProperty C₁)
    (hW : W.IsInvertedBy G) (hW' : (W.functorCategory C₁) adj.unit) :
    G.IsLocalization W := by
  let Φ : W.Localization ⥤ C₂ := Localization.lift _ hW W.Q
  let e : W.Q ⋙ Φ ≅ G := by apply Localization.fac
  have : IsIso (whiskerRight adj.unit W.Q) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    exact Localization.inverts W.Q W _ (hW' X)
  have : Localization.Lifting W.Q W (G ⋙ F ⋙ W.Q) (Φ ⋙ F ⋙ W.Q) :=
    ⟨(Functor.associator _ _ _).symm ≪≫ isoWhiskerRight e _⟩
  exact Functor.IsLocalization.of_equivalence_target W.Q W _
    (Equivalence.mk Φ (F ⋙ W.Q)
    (Localization.liftNatIso W.Q W W.Q (G ⋙ F ⋙ W.Q) _ _
      (W.Q.leftUnitor.symm ≪≫ asIso (whiskerRight adj.unit W.Q) ≪≫ Functor.associator _ _ _))
      (Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ e ≪≫ (asIso adj.counit))) e

lemma hasLeftCalculusOfFractions (adj : G ⊣ F) (W : MorphismProperty C₁)
    [W.IsMultiplicative] (hW : W.IsInvertedBy G) (hW' : (W.functorCategory C₁) adj.unit) :
    W.HasLeftCalculusOfFractions where
  exists_leftFraction X Y φ := by
    obtain ⟨T, s, _, f, rfl⟩ := φ.cases
    dsimp
    have := hW s (by assumption)
    exact ⟨{
      f := adj.unit.app X ≫ F.map (inv (G.map s)) ≫ F.map (G.map f)
      s := adj.unit.app Y
      hs := hW' Y}, by
      have := adj.unit.naturality s
      dsimp at this ⊢
      rw [reassoc_of% this, Functor.map_inv, IsIso.hom_inv_id_assoc, adj.unit_naturality]⟩
  ext X' X Y f₁ f₂ s _ h := by
    have := hW s (by assumption)
    refine ⟨_, adj.unit.app Y, hW' _, ?_⟩
    rw [← adj.unit_naturality f₁, ← adj.unit_naturality f₂]
    congr 2
    rw [← cancel_epi (G.map s), ← G.map_comp, ← G.map_comp, h]

lemma hasLeftCalculusOfFractions' [F.Full] [F.Faithful] (adj : G ⊣ F) :
    ((isomorphisms C₂).inverseImage G).HasLeftCalculusOfFractions :=
  hasLeftCalculusOfFractions adj _ (fun _ _ _ h ↦ h) (fun X ↦ by
    rw [inverseImage_iff, isomorphisms.iff]
    apply isIso_of_reflects_iso _ F)

lemma hasRightCalculusOfFractions [F.Full] [F.Faithful] (adj : F ⊣ G) :
    ((isomorphisms C₂).inverseImage G).HasRightCalculusOfFractions := by
  suffices ((isomorphisms C₂).inverseImage G).op.HasLeftCalculusOfFractions from
    inferInstanceAs ((isomorphisms C₂).inverseImage G).op.unop.HasRightCalculusOfFractions
  simpa only [← isomorphisms_op] using adj.op.hasLeftCalculusOfFractions'

end Adjunction

end CategoryTheory
