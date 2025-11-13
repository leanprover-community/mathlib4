/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Basic

/-!
# Constructor for derivability structures

In this file, we provide a constructor for right derivability structures.
Assume that `W₁` and `W₂` are classes of morphisms in categories `C₁` and `C₂`,
and that we have a localizer morphism `Φ : LocalizerMorphism W₁ W₂` that is
a localized equivalence, i.e. `Φ.functor` induces an equivalence of categories
between the localized categories. Assume moreover that `W₂` contains identities.
Then, `Φ` is a right derivability structure
(`LocalizerMorphism.IsRightDerivabilityStructure.mk'`) if it satisfies the
two following conditions:
* for any `X₂ : C₂`, the category `Φ.RightResolution X₂` of resolutions of `X₂` is connected
* any arrow in `C₂` admits a resolution (i.e. `Φ.arrow.HasRightResolutions` holds, where
  `Φ.arrow` is the induced localizer morphism on categories of arrows in `C₁` and `C₂`)

This statement is essentially Lemme 6.5 in
[the paper by Kahn and Maltsiniotis][KahnMaltsiniotis2008].

## References

* [Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008]

-/

namespace CategoryTheory

open Category Localization

variable {C₁ C₂ : Type*} [Category C₁] [Category C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism
namespace IsRightDerivabilityStructure

section

variable (Φ : LocalizerMorphism W₁ W₂)
  [∀ X₂, IsConnected (Φ.RightResolution X₂)]
  [Φ.arrow.HasRightResolutions] [W₂.ContainsIdentities]

namespace Constructor

variable {D : Type*} [Category D] (L : C₂ ⥤ D) [L.IsLocalization W₂]
  {X₂ : C₂} {X₃ : D} (y : L.obj X₂ ⟶ X₃)

/-- Given `Φ : LocalizerMorphism W₁ W₂`, `L : C₂ ⥤ D` a localization functor for `W₂` and
a morphism `y : L.obj X₂ ⟶ X₃`, this is the functor which sends `R : Φ.RightResolution d` to
`(isoOfHom L W₂ R.w R.hw).inv ≫ y` in the category `w.CostructuredArrowDownwards y`
where `w` is `TwoSquare.mk Φ.functor (Φ.functor ⋙ L) L (𝟭 _) (Functor.rightUnitor _).inv`. -/
@[simps]
noncomputable def fromRightResolution :
    Φ.RightResolution X₂ ⥤ (TwoSquare.mk Φ.functor (Φ.functor ⋙ L) L (𝟭 _)
      (Functor.rightUnitor _).inv).CostructuredArrowDownwards y where
  obj R := CostructuredArrow.mk (Y := StructuredArrow.mk R.w)
    (StructuredArrow.homMk ((isoOfHom L W₂ R.w R.hw).inv ≫ y))
  map {R R'} φ := CostructuredArrow.homMk (StructuredArrow.homMk φ.f) (by
    ext
    dsimp
    rw [← assoc, ← cancel_epi (isoOfHom L W₂ R.w R.hw).hom,
      isoOfHom_hom, isoOfHom_hom_inv_id_assoc, assoc, ← L.map_comp_assoc,
      φ.comm, isoOfHom_hom_inv_id_assoc])

lemma isConnected :
    IsConnected ((TwoSquare.mk Φ.functor (Φ.functor ⋙ L) L (𝟭 _)
      (Functor.rightUnitor _).inv).CostructuredArrowDownwards y) := by
  let w := (TwoSquare.mk Φ.functor (Φ.functor ⋙ L) L (𝟭 _) (Functor.rightUnitor _).inv)
  have : Nonempty (w.CostructuredArrowDownwards y) :=
    ⟨(fromRightResolution Φ L y).obj (Classical.arbitrary _)⟩
  suffices ∀ (X : w.CostructuredArrowDownwards y),
      ∃ Y, Zigzag X ((fromRightResolution Φ L y).obj Y) by
    refine zigzag_isConnected (fun X X' => ?_)
    obtain ⟨Y, hX⟩ := this X
    obtain ⟨Y', hX'⟩ := this X'
    exact hX.trans ((zigzag_obj_of_zigzag _ (isPreconnected_zigzag Y Y')).trans hX'.symm)
  intro X
  obtain ⟨c, g, x, fac, rfl⟩ := TwoSquare.CostructuredArrowDownwards.mk_surjective X
  dsimp [w] at x fac
  rw [id_comp] at fac
  let ρ : Φ.arrow.RightResolution (Arrow.mk g) := Classical.arbitrary _
  refine ⟨RightResolution.mk ρ.w.left ρ.hw.1, ?_⟩
  have := zigzag_obj_of_zigzag
    (fromRightResolution Φ L x ⋙ w.costructuredArrowDownwardsPrecomp x y g fac)
      (isPreconnected_zigzag (RightResolution.mk (𝟙 _) (W₂.id_mem _))
        (RightResolution.mk ρ.w.right ρ.hw.2))
  refine Zigzag.trans ?_ (Zigzag.trans this ?_)
  · exact Zigzag.of_hom (eqToHom (by simp))
  · apply Zigzag.of_inv
    refine CostructuredArrow.homMk (StructuredArrow.homMk ρ.X₁.hom (by simp)) ?_
    ext
    dsimp
    rw [← cancel_epi (isoOfHom L W₂ ρ.w.left ρ.hw.1).hom, isoOfHom_hom,
      isoOfHom_hom_inv_id_assoc, ← L.map_comp_assoc, Arrow.w_mk_right, Arrow.mk_hom,
      L.map_comp, assoc, isoOfHom_hom_inv_id_assoc, fac]

end Constructor

/-- If a localizer morphism `Φ` is a localized equivalence, then it is a right
derivability structure if the categories of right resolutions are connected and the
categories of right resolutions of arrows are nonempty. -/
lemma mk' [Φ.IsLocalizedEquivalence] : Φ.IsRightDerivabilityStructure := by
  rw [Φ.isRightDerivabilityStructure_iff (Φ.functor ⋙ W₂.Q) W₂.Q (𝟭 _)
    (Functor.rightUnitor _).symm, TwoSquare.guitartExact_iff_isConnected_downwards]
  intro X₂ X₃ g
  apply Constructor.isConnected

end

end IsRightDerivabilityStructure

end LocalizerMorphism

end CategoryTheory
