/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Iso
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.CategoryTheory.MorphismProperty.Limits

#align_import ring_theory.ring_hom_properties from "leanprover-community/mathlib"@"a7c017d750512a352b623b1824d75da5998457d0"

/-!
# Properties of ring homomorphisms

We provide the basic framework for talking about properties of ring homomorphisms.
The following meta-properties of predicates on ring homomorphisms are defined

* `RingHom.RespectsIso`: `P` respects isomorphisms if `P f → P (e ≫ f)` and
  `P f → P (f ≫ e)`, where `e` is an isomorphism.
* `RingHom.StableUnderComposition`: `P` is stable under composition if `P f → P g → P (f ≫ g)`.
* `RingHom.StableUnderBaseChange`: `P` is stable under base change if `P (S ⟶ Y)`
  implies `P (X ⟶ X ⊗[S] Y)`.

-/


universe w₁ w₂ u v

open CategoryTheory Opposite CategoryTheory.Limits

namespace RingHom

variable (P : ∀ {R S : Type u} [CommRing R] [CommRing S] (_ : R →+* S), Prop)

section ToMorphismProperty

/-- The categorical `MorphismProperty` associated to a property of ring homs expressed
non-categorical terms. -/
def toMorphismProperty :
    MorphismProperty CommRingCat := fun _ _ f ↦ P f

end ToMorphismProperty

section RespectsIso

/-- A property `RespectsIso` if it still holds when composed with an isomorphism -/
abbrev RespectsIso := (toMorphismProperty @P).RespectsIso
#align ring_hom.respects_iso RingHom.RespectsIso

variable {P}

lemma respectsIso_mk
    (ringEquiv_comp : ∀ {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
      (f : R →+* S) (e : S ≃+* T) (_ : P f), P (e.toRingHom.comp f))
    (comp_ringEquiv : ∀ {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
      (f : S →+* T) (e : R ≃+* S) (_ : P f), P (f.comp e.toRingHom)) :
    RespectsIso @P where
  precomp e f hf := comp_ringEquiv f e.commRingCatIsoToRingEquiv hf
  postcomp e f hf := ringEquiv_comp f e.commRingCatIsoToRingEquiv hf

theorem cancel_left_of_respectsIso [RespectsIso @P] {R S T : CommRingCat} (f : R ⟶ S)
    (g : S ⟶ T) [IsIso f] : P (f ≫ g) ↔ P g :=
  MorphismProperty.cancel_left_of_respectsIso (toMorphismProperty @P) f g
#align ring_hom.respects_iso.cancel_left_is_iso RingHom.cancel_left_of_respectsIso

theorem cancel_right_of_respectsIso [RespectsIso @P] {R S T : CommRingCat} (f : R ⟶ S)
    (g : S ⟶ T) [IsIso g] : P (f ≫ g) ↔ P f :=
  MorphismProperty.cancel_right_of_respectsIso (toMorphismProperty @P) f g
#align ring_hom.respects_iso.cancel_right_is_iso RingHom.cancel_right_of_respectsIso

theorem is_localization_away_iff_of_respectsIso [RespectsIso @P] {R S : Type u}
    (R' S' : Type u) [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] [Algebra R R']
    [Algebra S S'] (f : R →+* S) (r : R) [IsLocalization.Away r R'] [IsLocalization.Away (f r) S'] :
    P (Localization.awayMap f r) ↔ P (IsLocalization.Away.map R' S' f r) := by
  let e₁ : R' ≃+* Localization.Away r :=
    (IsLocalization.algEquiv (Submonoid.powers r) _ _).toRingEquiv
  let e₂ : Localization.Away (f r) ≃+* S' :=
    (IsLocalization.algEquiv (Submonoid.powers (f r)) _ _).toRingEquiv
  refine (cancel_left_of_respectsIso e₁.toCommRingCatIso.hom (CommRingCat.ofHom _)).symm.trans ?_
  refine (cancel_right_of_respectsIso (CommRingCat.ofHom _) e₂.toCommRingCatIso.hom).symm.trans ?_
  rw [← eq_iff_iff]
  congr 1
  -- Porting note: Here, the proof used to have a huge `simp` involving `[anonymous]`, which didn't
  -- work out anymore. The issue seemed to be that it couldn't handle a term in which Ring
  -- homomorphisms were repeatedly casted to the bundled category and back. Here we resolve the
  -- problem by converting the goal to a more straightforward form.
  let e := (e₂ : Localization.Away (f r) →+* S').comp
      (((IsLocalization.map (Localization.Away (f r)) f
            (by rintro x ⟨n, rfl⟩; use n; simp : Submonoid.powers r ≤ Submonoid.comap f
                (Submonoid.powers (f r)))) : Localization.Away r →+* Localization.Away (f r)).comp
                (e₁ : R' →+* Localization.Away r))
  suffices e = IsLocalization.Away.map R' S' f r by
    convert this
  apply IsLocalization.ringHom_ext (Submonoid.powers r) _
  ext1 x
  dsimp [e, e₁, e₂, IsLocalization.Away.map]
  simp only [IsLocalization.map_eq, id_apply, RingHomCompTriple.comp_apply]
#align ring_hom.respects_iso.is_localization_away_iff RingHom.is_localization_away_iff_of_respectsIso

end RespectsIso

section StableUnderComposition

/-- A property is `StableUnderComposition` if the composition of two such morphisms
still falls in the class. -/
abbrev StableUnderComposition := (toMorphismProperty @P).IsStableUnderComposition
#align ring_hom.stable_under_composition RingHom.StableUnderComposition

variable {P}

theorem StableUnderComposition.respectsIso [StableUnderComposition @P]
    (hP' : ∀ {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S), P e.toRingHom) :
    RingHom.RespectsIso @P :=
  MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ f (_ : IsIso f) ↦
    (hP' (asIso f).commRingCatIsoToRingEquiv)
#align ring_hom.stable_under_composition.respects_iso RingHom.StableUnderComposition.respectsIso

end StableUnderComposition

section StableUnderBaseChange

/-- A morphism property `P` is `StableUnderBaseChange` if `P(S →+* A)` implies
`P(B →+* A ⊗[S] B)`. -/
abbrev StableUnderBaseChange : Prop := (toMorphismProperty @P).StableUnderCobaseChange
#align ring_hom.stable_under_base_change RingHom.StableUnderBaseChange

theorem StableUnderBaseChange.mk (h₁ : RespectsIso @P)
    (h₂ :
      ∀ (R S T) [CommRing R] [CommRing S] [CommRing T],
        ∀ [Algebra R S] [Algebra R T],
          P (algebraMap R T) →
            P (Algebra.TensorProduct.includeLeftRingHom : S →+* TensorProduct R S T)) :
    StableUnderBaseChange @P := by
  refine MorphismProperty.StableUnderCobaseChange.mk' (fun {R S T} f g hg ↦ ?_)
  letI := f.toAlgebra
  letI := g.toAlgebra
  exact ⟨_, _, _, .of_isColimit (CommRingCat.pushoutCoconeIsColimit T S R), h₂ T S R hg⟩

attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem StableUnderBaseChange.pushout_inl (hP : RingHom.StableUnderBaseChange @P)
    {R S T : CommRingCat} (f : R ⟶ S) (g : R ⟶ T) (H : P g) :
    P (pushout.inl _ _ : S ⟶ pushout f g) :=
  hP.inl _ _ H
#align ring_hom.stable_under_base_change.pushout_inl RingHom.StableUnderBaseChange.pushout_inl

end StableUnderBaseChange

end RingHom
