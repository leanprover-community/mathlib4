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

If `G ⊣ F` is an adjunction, `F` is fully faithful,
and `W` is a class of morphisms that is inverted by `G`
and such that the morphism `adj.unit.app X` belongs to `W`
for any object `X`, then `G` is a localization functor
with respect to `W`. Moreover, if `W` is multiplicative,
then `W` has a calculus of left fractions. This
holds in particular if `W` is the inverse image of
the class of isomorphisms by `G`.

(The dual statement is also obtained.)

-/

namespace CategoryTheory

open MorphismProperty

namespace Adjunction

variable {C₁ C₂ : Type*} [Category C₁] [Category C₂]
  {G : C₁ ⥤ C₂} {F : C₂ ⥤ C₁}

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

lemma hasRightCalculusOfFractions (adj : F ⊣ G) (W : MorphismProperty C₁)
    [W.IsMultiplicative] (hW : W.IsInvertedBy G) (hW' : (W.functorCategory _) adj.counit) :
    W.HasRightCalculusOfFractions :=
  have := hasLeftCalculusOfFractions adj.op W.op hW.op (fun _ ↦ hW' _)
  inferInstanceAs W.op.unop.HasRightCalculusOfFractions

section

variable [F.Full] [F.Faithful]

lemma isLocalization_leftAdjoint
    (adj : G ⊣ F) (W : MorphismProperty C₁)
    (hW : W.IsInvertedBy G) (hW' : (W.functorCategory C₁) adj.unit) :
    G.IsLocalization W := by
  let Φ : W.Localization ⥤ C₂ := Localization.lift _ hW W.Q
  let e : W.Q ⋙ Φ ≅ G := by apply Localization.fac
  have : IsIso (Functor.whiskerRight adj.unit W.Q) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    exact Localization.inverts W.Q W _ (hW' X)
  exact Functor.IsLocalization.of_equivalence_target W.Q W _
    (Equivalence.mk Φ (F ⋙ W.Q)
      (Localization.liftNatIso W.Q W W.Q (G ⋙ F ⋙ W.Q) _ _
        (W.Q.leftUnitor.symm ≪≫ asIso (Functor.whiskerRight adj.unit W.Q) ≪≫
        Functor.associator _ _ _))
      (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ e ≪≫ asIso adj.counit)) e

lemma isLocalization_rightAdjoint
    (adj : F ⊣ G) (W : MorphismProperty C₁)
    (hW : W.IsInvertedBy G) (hW' : (W.functorCategory C₁) adj.counit) :
    G.IsLocalization W := by
  simpa using isLocalization_leftAdjoint adj.op W.op hW.op (fun X ↦ hW' X.unop)

lemma functorCategory_inverseImage_isomorphisms_unit (adj : G ⊣ F) :
    ((isomorphisms C₂).inverseImage G).functorCategory C₁ adj.unit := by
  intro
  simp only [Functor.id_obj, Functor.comp_obj, inverseImage_iff, isomorphisms.iff]
  infer_instance

lemma functorCategory_inverseImage_isomorphisms_counit (adj : F ⊣ G) :
    ((isomorphisms C₂).inverseImage G).functorCategory C₁ adj.counit := by
  intro
  simp only [Functor.id_obj, Functor.comp_obj, inverseImage_iff, isomorphisms.iff]
  infer_instance

lemma isLocalization_leftAdjoint' (adj : G ⊣ F) :
    G.IsLocalization ((isomorphisms C₂).inverseImage G) :=
  adj.isLocalization_leftAdjoint _ (fun _ _ _ h ↦ h)
    adj.functorCategory_inverseImage_isomorphisms_unit

lemma isLocalization_rightAdjoint' (adj : F ⊣ G) :
    G.IsLocalization ((isomorphisms C₂).inverseImage G) :=
  adj.isLocalization_rightAdjoint _ (fun _ _ _ h ↦ h)
    adj.functorCategory_inverseImage_isomorphisms_counit

lemma hasLeftCalculusOfFractions' (adj : G ⊣ F) :
    ((isomorphisms C₂).inverseImage G).HasLeftCalculusOfFractions :=
  hasLeftCalculusOfFractions adj _ (fun _ _ _ h ↦ h)
    adj.functorCategory_inverseImage_isomorphisms_unit

lemma hasRightCalculusOfFractions' (adj : F ⊣ G) :
    ((isomorphisms C₂).inverseImage G).HasRightCalculusOfFractions :=
  hasRightCalculusOfFractions adj _ (fun _ _ _ h ↦ h)
    adj.functorCategory_inverseImage_isomorphisms_counit

end

end Adjunction

end CategoryTheory
