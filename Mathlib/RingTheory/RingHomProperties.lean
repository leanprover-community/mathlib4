/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module ring_theory.ring_hom_properties
! leanprover-community/mathlib commit a7c017d750512a352b623b1824d75da5998457d0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Isomorphism
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.IsTensorProduct

/-!
# Properties of ring homomorphisms

We provide the basic framework for talking about properties of ring homomorphisms.
The following meta-properties of predicates on ring homomorphisms are defined

* `ring_hom.respects_iso`: `P` respects isomorphisms if `P f → P (e ≫ f)` and
  `P f → P (f ≫ e)`, where `e` is an isomorphism.
* `ring_hom.stable_under_composition`: `P` is stable under composition if `P f → P g → P (f ≫ g)`.
* `ring_hom.stable_under_base_change`: `P` is stable under base change if `P (S ⟶ Y)`
  implies `P (X ⟶ X ⊗[S] Y)`.

-/


universe u

open CategoryTheory Opposite CategoryTheory.Limits

namespace RingHom

variable (P : ∀ {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S), Prop)

include P

section RespectsIso

/-- A property `respects_iso` if it still holds when composed with an isomorphism -/
def RespectsIso : Prop :=
  (∀ {R S T : Type u} [CommRing R] [CommRing S] [CommRing T],
      ∀ (f : R →+* S) (e : S ≃+* T) (hf : P f), P (e.to_ring_hom.comp f)) ∧
    ∀ {R S T : Type u} [CommRing R] [CommRing S] [CommRing T],
      ∀ (f : S →+* T) (e : R ≃+* S) (hf : P f), P (f.comp e.toRingHom)
#align ring_hom.respects_iso RingHom.RespectsIso

variable {P}

theorem RespectsIso.cancel_left_isIso (hP : RespectsIso @P) {R S T : CommRingCat} (f : R ⟶ S)
    (g : S ⟶ T) [IsIso f] : P (f ≫ g) ↔ P g :=
  ⟨fun H => by
    convert hP.2 (f ≫ g) (as_iso f).symm.commRingCatIsoToRingEquiv H
    exact (is_iso.inv_hom_id_assoc _ _).symm, hP.2 g (asIso f).commRingCatIsoToRingEquiv⟩
#align ring_hom.respects_iso.cancel_left_is_iso RingHom.RespectsIso.cancel_left_isIso

theorem RespectsIso.cancel_right_isIso (hP : RespectsIso @P) {R S T : CommRingCat} (f : R ⟶ S)
    (g : S ⟶ T) [IsIso g] : P (f ≫ g) ↔ P f :=
  ⟨fun H => by
    convert hP.1 (f ≫ g) (as_iso g).symm.commRingCatIsoToRingEquiv H
    change f = f ≫ g ≫ inv g
    simp, hP.1 f (asIso g).commRingCatIsoToRingEquiv⟩
#align ring_hom.respects_iso.cancel_right_is_iso RingHom.RespectsIso.cancel_right_isIso

theorem RespectsIso.is_localization_away_iff (hP : RingHom.RespectsIso @P) {R S : Type _}
    (R' S' : Type _) [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] [Algebra R R']
    [Algebra S S'] (f : R →+* S) (r : R) [IsLocalization.Away r R'] [IsLocalization.Away (f r) S'] :
    P (Localization.awayMap f r) ↔ P (IsLocalization.Away.map R' S' f r) := by
  let e₁ : R' ≃+* Localization.Away r :=
    (IsLocalization.algEquiv (Submonoid.powers r) _ _).toRingEquiv
  let e₂ : Localization.Away (f r) ≃+* S' :=
    (IsLocalization.algEquiv (Submonoid.powers (f r)) _ _).toRingEquiv
  refine' (hP.cancel_left_is_iso e₁.to_CommRing_iso.hom (CommRingCat.ofHom _)).symm.trans _
  refine' (hP.cancel_right_is_iso (CommRingCat.ofHom _) e₂.to_CommRing_iso.hom).symm.trans _
  rw [← eq_iff_iff]
  congr 1
  dsimp [CommRingCat.ofHom, CommRingCat.of, bundled.of]
  refine' IsLocalization.ringHom_ext (Submonoid.powers r) _
  ext1
  revert e₁ e₂
  dsimp [RingEquiv.toRingHom, IsLocalization.Away.map]
  simp only [CategoryTheory.comp_apply, RingEquiv.refl_apply, IsLocalization.algEquiv_apply,
    IsLocalization.ringEquivOfRingEquiv_apply, RingHom.coe_mk, [anonymous],
    IsLocalization.ringEquivOfRingEquiv_eq, IsLocalization.map_eq]
#align ring_hom.respects_iso.is_localization_away_iff RingHom.RespectsIso.is_localization_away_iff

end RespectsIso

section StableUnderComposition

/-- A property is `stable_under_composition` if the composition of two such morphisms
still falls in the class. -/
def StableUnderComposition : Prop :=
  ∀ ⦃R S T⦄ [CommRing R] [CommRing S] [CommRing T],
    ∀ (f : R →+* S) (g : S →+* T) (hf : P f) (hg : P g), P (g.comp f)
#align ring_hom.stable_under_composition RingHom.StableUnderComposition

variable {P}

theorem StableUnderComposition.respectsIso (hP : RingHom.StableUnderComposition @P)
    (hP' : ∀ {R S : Type _} [CommRing R] [CommRing S] (e : R ≃+* S), P e.to_ring_hom) :
    RingHom.RespectsIso @P := by
  constructor
  · introv H
    skip
    apply hP
    exacts[H, hP' e]
  · introv H
    skip
    apply hP
    exacts[hP' e, H]
#align ring_hom.stable_under_composition.respects_iso RingHom.StableUnderComposition.respectsIso

end StableUnderComposition

section StableUnderBaseChange

/-- A morphism property `P` is `stable_under_base_change` if `P(S →+* A)` implies
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
            P (algebra.tensor_product.include_left.to_ring_hom : S →+* TensorProduct R S T)) :
    StableUnderBaseChange @P := by
  introv R h H
  skip
  let e := h.symm.1.Equiv
  let f' :=
    Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom R R' S')
      (IsScalarTower.toAlgHom R S S')
  have : ∀ x, e x = f' x := by
    intro x
    change e.to_linear_map.restrict_scalars R x = f'.to_linear_map x
    congr 1
    apply TensorProduct.ext'
    intro x y
    simp [IsBaseChange.equiv_tmul, Algebra.smul_def]
  convert h₁.1 _ _ (h₂ H : P (_ : R' →+* _))
  swap
  · refine' { e with map_mul' := fun x y => _ }
    change e (x * y) = e x * e y
    simp_rw [this]
    exact map_mul f' _ _
  · ext
    change _ = e (x ⊗ₜ[R] 1)
    dsimp only [e]
    rw [h.symm.1.equiv_tmul, Algebra.smul_def, AlgHom.toLinearMap_apply, map_one, mul_one]
#align ring_hom.stable_under_base_change.mk RingHom.StableUnderBaseChange.mk

omit P

attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem StableUnderBaseChange.pushout_inl (hP : RingHom.StableUnderBaseChange @P)
    (hP' : RingHom.RespectsIso @P) {R S T : CommRingCat} (f : R ⟶ S) (g : R ⟶ T) (H : P g) :
    P (pushout.inl : S ⟶ pushout f g) := by
  rw [←
    show _ = pushout.inl from
      colimit.iso_colimit_cocone_ι_inv ⟨_, CommRingCat.pushoutCoconeIsColimit f g⟩
        walking_span.left,
    hP'.cancel_right_is_iso]
  letI := f.to_algebra
  letI := g.to_algebra
  dsimp only [CommRingCat.pushoutCocone_inl, pushout_cocone.ι_app_left]
  apply hP R T S (TensorProduct R S T)
  exact H
#align ring_hom.stable_under_base_change.pushout_inl RingHom.StableUnderBaseChange.pushout_inl

end StableUnderBaseChange

end RingHom

