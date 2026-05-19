/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.IsTensorProduct

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

@[expose] public section


universe u

open CategoryTheory Opposite CategoryTheory.Limits TensorProduct

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

set_option backward.defeqAttrib.useBackward true in
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
    (h₂ : ∀ ⦃R S T⦄ [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T],
      P (algebraMap R T) → P (algebraMap S (S ⊗[R] T))) :
    IsStableUnderBaseChange @P := by
  introv R h H
  let e := h.symm.1.equiv
  let f' := Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom R R' S')
    (IsScalarTower.toAlgHom R S S')
  have hef (x : _) : e x = f' x := by
    suffices e.toLinearMap.restrictScalars R = f'.toLinearMap from congr($this x)
    exact ext' fun x y ↦ by simp [e, f', IsBaseChange.equiv_tmul, Algebra.smul_def]
  have hemul (x y : _) : e (x * y) = e x * e y := by simp_rw [hef, map_mul]
  convert h₁.1 _ { e with map_mul' := hemul } (h₂ H)
  ext x
  simp [e, h.symm.1.equiv_tmul, Algebra.smul_def]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

lemma IsStableUnderBaseChange.tensorProduct (hP : RingHom.IsStableUnderBaseChange P)
    {R S : Type u} (T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (h : P (algebraMap R S)) :
    P (algebraMap T (T ⊗[R] S)) :=
  -- This only works because the `Algebra.TensorProduct.rightAlgebra` instance is present here.
  hP _ _ _ _ h

set_option backward.isDefEq.respectTransparency false in
theorem IsStableUnderBaseChange.pushout_inl (hP : RingHom.IsStableUnderBaseChange @P)
    (hP' : RingHom.RespectsIso @P) {R S T : CommRingCat} (f : R ⟶ S) (g : R ⟶ T) (H : P g.hom) :
    P (pushout.inl _ _ : S ⟶ pushout f g).hom := by
  letI := f.hom.toAlgebra
  letI := g.hom.toAlgebra
  rw [← show _ = pushout.inl f g from
      colimit.isoColimitCocone_ι_inv ⟨_, CommRingCat.pushoutCoconeIsColimit R S T⟩ WalkingSpan.left,
    CommRingCat.hom_comp, hP'.cancel_right_isIso]
  dsimp only [CommRingCat.pushoutCocone_inl, PushoutCocone.ι_app_left]
  apply hP R T S (S ⊗[R] T)
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

lemma isStableUnderCobaseChange_toMorphismProperty_iff :
    (toMorphismProperty P).IsStableUnderCobaseChange ↔ IsStableUnderBaseChange P := by
  refine ⟨fun h R S R' S' _ _ _ _ _ _ _ _ _ _ _ hsq hRS ↦ ?_,
      fun h ↦ ⟨fun {R} S R' S' f g f' g' hsq hf ↦ ?_⟩⟩
  · rw [← CommRingCat.isPushout_iff_isPushout] at hsq
    exact h.1 (f := CommRingCat.ofHom (algebraMap R S)) hsq.flip hRS
  · algebraize [f.hom, g.hom, f'.hom, g'.hom, f'.hom.comp g.hom]
    have : IsScalarTower R S S' := .of_algebraMap_eq fun x ↦ congr($(hsq.1.1).hom x)
    have : Algebra.IsPushout R S R' S' := (CommRingCat.isPushout_iff_isPushout.mp hsq).symm
    exact h (R := R) (S := S) _ _ hf

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

section Descent

variable (Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)

variable (R S T : Type u) [CommRing R] [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]

variable (P) in
/-- A property of ring homomorphisms `Q` codescends along `Q'` if whenever
`R' →+* R' ⊗[R] S` satisfies `Q` and `R →+* R'` satisfies `Q'`, then `R →+* S` satisfies `Q`. -/
def CodescendsAlong : Prop :=
  ∀ ⦃R S R' S' : Type u⦄ [CommRing R] [CommRing S] [CommRing R'] [CommRing S'],
  ∀ [Algebra R S] [Algebra R R'] [Algebra R S'] [Algebra S S'] [Algebra R' S'],
    ∀ [IsScalarTower R S S'] [IsScalarTower R R' S'],
      ∀ [Algebra.IsPushout R S R' S'],
        Q (algebraMap R R') → P (algebraMap R' S') → P (algebraMap R S)

lemma CodescendsAlong.mk (h₁ : RespectsIso P)
    (h₂ : ∀ ⦃R S T⦄ [CommRing R] [CommRing S] [CommRing T],
      ∀ [Algebra R S] [Algebra R T],
        Q (algebraMap R S) → P (algebraMap S (S ⊗[R] T)) → P (algebraMap R T)) :
    CodescendsAlong P Q := by
  introv R h hQ H
  let e := h.symm.equiv
  have : (e.symm : _ →+* _).comp (algebraMap R' S') = algebraMap R' (R' ⊗[R] S) := by
    ext r
    simp [e]
  apply h₂ hQ
  rw [← this]
  exact h₁.1 _ _ H

lemma CodescendsAlong.algebraMap_tensorProduct (hPQ : CodescendsAlong P Q)
    (h : Q (algebraMap R S)) (H : P (algebraMap S (S ⊗[R] T))) :
    P (algebraMap R T) :=
  let _ : Algebra T (S ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
  hPQ h H

lemma CodescendsAlong.includeRight (hPQ : CodescendsAlong P Q) (h : Q (algebraMap R T))
    (H : P ((Algebra.TensorProduct.includeRight.toRingHom : T →+* S ⊗[R] T))) :
    P (algebraMap R S) := by
  let _ : Algebra T (S ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
  apply hPQ h H

variable {Q} {P' : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}

lemma CodescendsAlong.and (hP : CodescendsAlong P Q) (hP' : CodescendsAlong P' Q) :
    CodescendsAlong (fun f ↦ P f ∧ P' f) Q :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ ↦ ⟨hP h₁ h₂.1, hP' h₁ h₂.2⟩

end Descent

/-- A property of ring homomorphisms `P` is said to have equalizers, if the equalizer of algebra
maps between algebras satisfiying `P` also satisfies `P`. -/
def HasEqualizers (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop) : Prop :=
  ∀ {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f g : S →ₐ[R] T), P (algebraMap R S) → P (algebraMap R T) →
      P (algebraMap R (AlgHom.equalizer f g))

lemma HasEqualizers.and (hP : HasEqualizers P) (hQ : HasEqualizers Q) :
    HasEqualizers (fun f ↦ P f ∧ Q f) :=
  fun f g hf hg ↦ ⟨hP f g hf.1 hg.1, hQ f g hf.2 hg.2⟩

/-- A property of ring homomorphisms `P` is said to have finite products, if a finite product of
algebras satisfiying `Q` also satisfies `P`. -/
def HasFiniteProducts (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop) : Prop :=
  ∀ {R : Type u} [CommRing R] {ι : Type u} [_root_.Finite ι] (S : ι → Type u) [∀ i, CommRing (S i)]
    [∀ i, Algebra R (S i)],
    (∀ i, P (algebraMap R (S i))) → P (algebraMap R (Π i, S i))

lemma HasFiniteProducts.and (hP : HasFiniteProducts P) (hQ : HasFiniteProducts Q) :
    HasFiniteProducts (fun f ↦ P f ∧ Q f) :=
  fun _ _ _ hS ↦ ⟨hP _ fun i ↦ (hS i).1, hQ _ fun i ↦ (hS i).2⟩

end RingHom
