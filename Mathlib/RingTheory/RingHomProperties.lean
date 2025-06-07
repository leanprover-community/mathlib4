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

/-!
# Properties of ring homomorphisms

We provide the basic framework for talking about properties of ring homomorphisms.
The following meta-properties of predicates on ring homomorphisms are defined

* `RingHom.RespectsIso`: `P` respects isomorphisms if `P f → P (e ≫ f)` and
  `P f → P (f ≫ e)`, where `e` is an isomorphism.
* `RingHom.StableUnderComposition`: `P` is stable under composition if `P f → P g → P (f ≫ g)`.
* `RingHom.IsStableUnderBaseChange`: `P` is stable under base change if `P (S ⟶ Y)`
  implies `P (X ⟶ X ⊗[S] Y)`.

-/


universe u

open CategoryTheory Opposite CategoryTheory.Limits

namespace RingHom

variable {P Q : ∀ {R S : Type u} [CommRing R] [CommRing S] (_ : R →+* S), Prop}

section RespectsIso

variable (P) in
/-- A property `RespectsIso` if it still holds when composed with an isomorphism -/
def RespectsIso : Prop :=
  (∀ {R S T : Type u} [CommRing R] [CommRing S] [CommRing T],
      ∀ (f : R →+* S) (e : S ≃+* T) (_ : P f), P (e.toRingHom.comp f)) ∧
    ∀ {R S T : Type u} [CommRing R] [CommRing S] [CommRing T],
      ∀ (f : S →+* T) (e : R ≃+* S) (_ : P f), P (f.comp e.toRingHom)

theorem RespectsIso.cancel_left_isIso (hP : RespectsIso @P) {R S T : CommRingCat} (f : R ⟶ S)
    (g : S ⟶ T) [IsIso f] : P (g.hom.comp f.hom) ↔ P g.hom :=
  ⟨fun H => by
    convert hP.2 (f ≫ g).hom (asIso f).symm.commRingCatIsoToRingEquiv H
    simp [← CommRingCat.hom_comp], hP.2 g.hom (asIso f).commRingCatIsoToRingEquiv⟩

theorem RespectsIso.cancel_right_isIso (hP : RespectsIso @P) {R S T : CommRingCat} (f : R ⟶ S)
    (g : S ⟶ T) [IsIso g] : P (g.hom.comp f.hom) ↔ P f.hom :=
  ⟨fun H => by
    convert hP.1 (f ≫ g).hom (asIso g).symm.commRingCatIsoToRingEquiv H
    simp [← CommRingCat.hom_comp],
   hP.1 f.hom (asIso g).commRingCatIsoToRingEquiv⟩

theorem RespectsIso.isLocalization_away_iff (hP : RingHom.RespectsIso @P) {R S : Type u}
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
                (e₁ : R' →+* Localization.Away r))
  suffices e = IsLocalization.Away.map R' S' f r by
    convert this
  apply IsLocalization.ringHom_ext (Submonoid.powers r) _
  ext1 x
  dsimp [e, e₁, e₂, IsLocalization.Away.map]
  simp only [IsLocalization.map_eq, id_apply, RingHomCompTriple.comp_apply]

@[deprecated (since := "2025-03-01")]
alias RespectsIso.is_localization_away_iff := RespectsIso.isLocalization_away_iff

lemma RespectsIso.and (hP : RespectsIso P) (hQ : RespectsIso Q) :
    RespectsIso (fun f ↦ P f ∧ Q f) := by
  refine ⟨?_, ?_⟩
  · introv hf
    exact ⟨hP.1 f e hf.1, hQ.1 f e hf.2⟩
  · introv hf
    exact ⟨hP.2 f e hf.1, hQ.2 f e hf.2⟩

end RespectsIso

section StableUnderComposition

variable (P) in
/-- A property is `StableUnderComposition` if the composition of two such morphisms
still falls in the class. -/
def StableUnderComposition : Prop :=
  ∀ ⦃R S T⦄ [CommRing R] [CommRing S] [CommRing T],
    ∀ (f : R →+* S) (g : S →+* T) (_ : P f) (_ : P g), P (g.comp f)

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

lemma StableUnderComposition.and (hP : StableUnderComposition P) (hQ : StableUnderComposition Q) :
    StableUnderComposition (fun f ↦ P f ∧ Q f) := by
  introv R hf hg
  exact ⟨hP f g hf.1 hg.1, hQ f g hf.2 hg.2⟩

end StableUnderComposition

section IsStableUnderBaseChange

variable (P) in
/-- A morphism property `P` is `IsStableUnderBaseChange` if `P(S →+* A)` implies
`P(B →+* A ⊗[S] B)`. -/
def IsStableUnderBaseChange : Prop :=
  ∀ (R S R' S') [CommRing R] [CommRing S] [CommRing R'] [CommRing S'],
    ∀ [Algebra R S] [Algebra R R'] [Algebra R S'] [Algebra S S'] [Algebra R' S'],
      ∀ [IsScalarTower R S S'] [IsScalarTower R R' S'],
        ∀ [Algebra.IsPushout R S R' S'], P (algebraMap R S) → P (algebraMap R' S')

theorem IsStableUnderBaseChange.mk (h₁ : RespectsIso @P)
    (h₂ :
      ∀ ⦃R S T⦄ [CommRing R] [CommRing S] [CommRing T],
        ∀ [Algebra R S] [Algebra R T],
          P (algebraMap R T) →
            P (Algebra.TensorProduct.includeLeftRingHom : S →+* TensorProduct R S T)) :
    IsStableUnderBaseChange @P := by
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

attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem IsStableUnderBaseChange.pushout_inl (hP : RingHom.IsStableUnderBaseChange @P)
    (hP' : RingHom.RespectsIso @P) {R S T : CommRingCat} (f : R ⟶ S) (g : R ⟶ T) (H : P g.hom) :
    P (pushout.inl _ _ : S ⟶ pushout f g).hom := by
  letI := f.hom.toAlgebra
  letI := g.hom.toAlgebra
  rw [← show _ = pushout.inl f g from
      colimit.isoColimitCocone_ι_inv ⟨_, CommRingCat.pushoutCoconeIsColimit R S T⟩ WalkingSpan.left,
    CommRingCat.hom_comp, hP'.cancel_right_isIso]
  dsimp only [CommRingCat.pushoutCocone_inl, PushoutCocone.ι_app_left]
  apply hP R T S (TensorProduct R S T)
  exact H

lemma IsStableUnderBaseChange.and (hP : IsStableUnderBaseChange P)
    (hQ : IsStableUnderBaseChange Q) :
    IsStableUnderBaseChange (fun f ↦ P f ∧ Q f) := by
  introv R _ h
  exact ⟨hP R S R' S' h.1, hQ R S R' S' h.2⟩

end IsStableUnderBaseChange

section ToMorphismProperty

variable (P) in
/-- The categorical `MorphismProperty` associated to a property of ring homs expressed
non-categorical terms. -/
def toMorphismProperty : MorphismProperty CommRingCat := fun _ _ f ↦ P f.hom

lemma toMorphismProperty_respectsIso_iff :
    RespectsIso P ↔ (toMorphismProperty P).RespectsIso := by
  refine ⟨fun h ↦ MorphismProperty.RespectsIso.mk _ ?_ ?_, fun h ↦ ⟨?_, ?_⟩⟩
  · intro X Y Z e f hf
    exact h.right f.hom e.commRingCatIsoToRingEquiv hf
  · intro X Y Z e f hf
    exact h.left f.hom e.commRingCatIsoToRingEquiv hf
  · intro X Y Z _ _ _ f e hf
    exact MorphismProperty.RespectsIso.postcomp (toMorphismProperty P)
      e.toCommRingCatIso.hom (CommRingCat.ofHom f) hf
  · intro X Y Z _ _ _ f e
    exact MorphismProperty.RespectsIso.precomp (toMorphismProperty P)
      e.toCommRingCatIso.hom (CommRingCat.ofHom f)

/-- Variant of `MorphismProperty.arrow_mk_iso_iff` specialized to morphism properties in
`CommRingCat` given by ring hom properties. -/
lemma RespectsIso.arrow_mk_iso_iff (hQ : RingHom.RespectsIso P) {A B A' B' : CommRingCat}
    {f : A ⟶ B} {g : A' ⟶ B'} (e : Arrow.mk f ≅ Arrow.mk g) :
    P f.hom ↔ P g.hom := by
  have : (toMorphismProperty P).RespectsIso := by
    rwa [← toMorphismProperty_respectsIso_iff]
  change toMorphismProperty P _ ↔ toMorphismProperty P _
  rw [MorphismProperty.arrow_mk_iso_iff (toMorphismProperty P) e]

end ToMorphismProperty

end RingHom
