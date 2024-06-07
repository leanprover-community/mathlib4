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


universe u

open CategoryTheory Opposite CategoryTheory.Limits

namespace RingHom

-- Porting Note: Deleted variable `f` here, since it wasn't used explicitly
variable (P : ∀ {R S : Type u} [CommRing R] [CommRing S] (_ : R →+* S), Prop)

section RespectsIso

/-- A property `RespectsIso` if it still holds when composed with an isomorphism -/
def RespectsIso : Prop :=
  (∀ {R S T : Type u} [CommRing R] [CommRing S] [CommRing T],
      ∀ (f : R →+* S) (e : S ≃+* T) (_ : P f), P (e.toRingHom.comp f)) ∧
    ∀ {R S T : Type u} [CommRing R] [CommRing S] [CommRing T],
      ∀ (f : S →+* T) (e : R ≃+* S) (_ : P f), P (f.comp e.toRingHom)
#align ring_hom.respects_iso RingHom.RespectsIso

variable {P}

theorem RespectsIso.cancel_left_isIso (hP : RespectsIso @P) {R S T : CommRingCat} (f : R ⟶ S)
    (g : S ⟶ T) [IsIso f] : P (f ≫ g) ↔ P g :=
  ⟨fun H => by
    convert hP.2 (f ≫ g) (asIso f).symm.commRingCatIsoToRingEquiv H
    exact (IsIso.inv_hom_id_assoc _ _).symm, hP.2 g (asIso f).commRingCatIsoToRingEquiv⟩
#align ring_hom.respects_iso.cancel_left_is_iso RingHom.RespectsIso.cancel_left_isIso

theorem RespectsIso.cancel_right_isIso (hP : RespectsIso @P) {R S T : CommRingCat} (f : R ⟶ S)
    (g : S ⟶ T) [IsIso g] : P (f ≫ g) ↔ P f :=
  ⟨fun H => by
    convert hP.1 (f ≫ g) (asIso g).symm.commRingCatIsoToRingEquiv H
    change f = f ≫ g ≫ inv g
    simp, hP.1 f (asIso g).commRingCatIsoToRingEquiv⟩
#align ring_hom.respects_iso.cancel_right_is_iso RingHom.RespectsIso.cancel_right_isIso

theorem RespectsIso.is_localization_away_iff (hP : RingHom.RespectsIso @P) {R S : Type u}
    (R' S' : Type u) [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] [Algebra R R']
    [Algebra S S'] (f : R →+* S) (r : R) [IsLocalization.Away r R'] [IsLocalization.Away (f r) S'] :
    P (Localization.awayMap f r) ↔ P (IsLocalization.Away.map R' S' f r) := by
  let e₁ : R' ≃+* Localization.Away r :=
    (IsLocalization.algEquiv (Submonoid.powers r) _ _).toRingEquiv
  let e₂ : Localization.Away (f r) ≃+* S' :=
    (IsLocalization.algEquiv (Submonoid.powers (f r)) _ _).toRingEquiv
  refine (hP.cancel_left_isIso e₁.toCommRingCatIso.hom (CommRingCat.ofHom _)).symm.trans ?_
  refine (hP.cancel_right_isIso (CommRingCat.ofHom _) e₂.toCommRingCatIso.hom).symm.trans ?_
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
                (e₁: R' →+* Localization.Away r))
  suffices e = IsLocalization.Away.map R' S' f r by
    convert this
  apply IsLocalization.ringHom_ext (Submonoid.powers r) _
  ext1 x
  dsimp [e, e₁, e₂, IsLocalization.Away.map]
  simp only [IsLocalization.map_eq, id_apply, RingHomCompTriple.comp_apply]
#align ring_hom.respects_iso.is_localization_away_iff RingHom.RespectsIso.is_localization_away_iff

end RespectsIso

section StableUnderComposition

/-- A property is `StableUnderComposition` if the composition of two such morphisms
still falls in the class. -/
def StableUnderComposition : Prop :=
  ∀ ⦃R S T⦄ [CommRing R] [CommRing S] [CommRing T],
    ∀ (f : R →+* S) (g : S →+* T) (_ : P f) (_ : P g), P (g.comp f)
#align ring_hom.stable_under_composition RingHom.StableUnderComposition

variable {P}

theorem StableUnderComposition.respectsIso (hP : RingHom.StableUnderComposition @P)
    (hP' : ∀ {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S), P e.toRingHom) :
    RingHom.RespectsIso @P := by
  constructor
  · introv H
    apply hP
    exacts [H, hP' e]
  · introv H
    apply hP
    exacts [hP' e, H]
#align ring_hom.stable_under_composition.respects_iso RingHom.StableUnderComposition.respectsIso

end StableUnderComposition

section StableUnderBaseChange

/-- A morphism property `P` is `StableUnderBaseChange` if `P(S →+* A)` implies
`P(B →+* A ⊗[S] B)`. -/
def StableUnderBaseChange : Prop :=
  ∀ (R S R' S') [CommRing R] [CommRing S] [CommRing R'] [CommRing S'],
    ∀ [Algebra R S] [Algebra R R'] [Algebra R S'] [Algebra S S'] [Algebra R' S'],
      ∀ [IsScalarTower R S S'] [IsScalarTower R R' S'],
        ∀ [Algebra.IsPushout R S R' S'], P (algebraMap R S) → P (algebraMap R' S')
#align ring_hom.stable_under_base_change RingHom.StableUnderBaseChange

theorem StableUnderBaseChange.mk (h₁ : RespectsIso @P)
    (h₂ :
      ∀ ⦃R S T⦄ [CommRing R] [CommRing S] [CommRing T],
        ∀ [Algebra R S] [Algebra R T],
          P (algebraMap R T) →
            P (Algebra.TensorProduct.includeLeftRingHom : S →+* TensorProduct R S T)) :
    StableUnderBaseChange @P := by
  introv R h H
  let e := h.symm.1.equiv
  let f' :=
    Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom R R' S')
      (IsScalarTower.toAlgHom R S S')
  have : ∀ x, e x = f' x := by
    intro x
    change e.toLinearMap.restrictScalars R x = f'.toLinearMap x
    congr 1
    apply TensorProduct.ext'
    intro x y
    simp [e, f', IsBaseChange.equiv_tmul, Algebra.smul_def]
  -- Porting Note: This had a lot of implicit inferences which didn't resolve anymore.
  -- Added those in
  convert h₁.1 (_ : R' →+* TensorProduct R R' S) (_ : TensorProduct R R' S ≃+* S')
      (h₂ H : P (_ : R' →+* TensorProduct R R' S))
  swap
  · refine { e with map_mul' := fun x y => ?_ }
    change e (x * y) = e x * e y
    simp_rw [this]
    exact map_mul f' _ _
  · ext x
    change _ = e (x ⊗ₜ[R] 1)
    -- Porting note: Had `dsimp only [e]` here, which didn't work anymore
    rw [h.symm.1.equiv_tmul, Algebra.smul_def, AlgHom.toLinearMap_apply, map_one, mul_one]
#align ring_hom.stable_under_base_change.mk RingHom.StableUnderBaseChange.mk

attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem StableUnderBaseChange.pushout_inl (hP : RingHom.StableUnderBaseChange @P)
    (hP' : RingHom.RespectsIso @P) {R S T : CommRingCat} (f : R ⟶ S) (g : R ⟶ T) (H : P g) :
    P (pushout.inl : S ⟶ pushout f g) := by
  rw [←
    show _ = pushout.inl from
      colimit.isoColimitCocone_ι_inv ⟨_, CommRingCat.pushoutCoconeIsColimit f g⟩
        WalkingSpan.left,
    hP'.cancel_right_isIso]
  letI := f.toAlgebra
  letI := g.toAlgebra
  dsimp only [CommRingCat.pushoutCocone_inl, PushoutCocone.ι_app_left]
  apply hP R T S (TensorProduct R S T)
  exact H
#align ring_hom.stable_under_base_change.pushout_inl RingHom.StableUnderBaseChange.pushout_inl

end StableUnderBaseChange

end RingHom
