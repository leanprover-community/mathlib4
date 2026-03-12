/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.Ideal.GoingDown

/-!
# Flat ring homomorphisms

In this file we define flat ring homomorphisms and show their meta properties.

-/

@[expose] public section

universe u v

open TensorProduct

/-- A ring homomorphism `f : R →+* S` is flat if `S` is flat as an `R` module. -/
@[algebraize Module.Flat]
def RingHom.Flat {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  Module.Flat R S

lemma RingHom.flat_algebraMap_iff {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    (algebraMap R S).Flat ↔ Module.Flat R S := by
  rw [RingHom.Flat, toAlgebra_algebraMap]

namespace RingHom.Flat

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

variable (R) in
/-- The identity of a ring is flat. -/
lemma id : RingHom.Flat (RingHom.id R) :=
  Module.Flat.self

/-- Composition of flat ring homomorphisms is flat. -/
lemma comp {f : R →+* S} {g : S →+* T} (hf : f.Flat) (hg : g.Flat) : Flat (g.comp f) := by
  algebraize [f, g, (g.comp f)]
  exact Module.Flat.trans R S T

/-- Bijective ring maps are flat. -/
lemma of_bijective {f : R →+* S} (hf : Function.Bijective f) : Flat f := by
  algebraize [f]
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofBijective (Algebra.linearMap R S) hf).symm

lemma containsIdentities : ContainsIdentities Flat := id

lemma stableUnderComposition : StableUnderComposition Flat := by
  introv R hf hg
  exact hf.comp hg

lemma respectsIso : RespectsIso Flat := by
  apply stableUnderComposition.respectsIso
  introv
  exact of_bijective e.bijective

lemma isStableUnderBaseChange : IsStableUnderBaseChange Flat := by
  apply IsStableUnderBaseChange.mk respectsIso
  introv h
  rw [flat_algebraMap_iff] at h ⊢
  infer_instance

lemma holdsForLocalizationAway : HoldsForLocalizationAway Flat := by
  introv R h
  suffices Module.Flat R S by
    rw [RingHom.Flat]; convert this; ext; simp_rw [Algebra.smul_def]; rfl
  exact IsLocalization.flat _ (Submonoid.powers r)

lemma ofLocalizationSpanTarget : OfLocalizationSpanTarget Flat := by
  introv R hsp h
  algebraize_only [f]
  refine Module.flat_of_isLocalized_span _ _ s hsp _
    (fun r ↦ Algebra.linearMap S <| Localization.Away r.1) ?_
  dsimp only [RingHom.Flat] at h
  convert h; ext
  apply Algebra.smul_def

/-- Flat is a local property of ring homomorphisms. -/
lemma propertyIsLocal : PropertyIsLocal Flat where
  localizationAwayPreserves := isStableUnderBaseChange.localizationPreserves.away
  ofLocalizationSpanTarget := ofLocalizationSpanTarget
  ofLocalizationSpan := ofLocalizationSpanTarget.ofLocalizationSpan
    (stableUnderComposition.stableUnderCompositionWithLocalizationAway
      holdsForLocalizationAway).left
  StableUnderCompositionWithLocalizationAwayTarget :=
    (stableUnderComposition.stableUnderCompositionWithLocalizationAway
      holdsForLocalizationAway).right

lemma ofLocalizationPrime : OfLocalizationPrime Flat := by
  introv R h
  algebraize_only [f]
  rw [RingHom.Flat]
  apply Module.flat_of_isLocalized_maximal S S (fun P ↦ Localization.AtPrime P)
    (fun P ↦ Algebra.linearMap S _)
  intro P _
  algebraize_only [Localization.localRingHom (Ideal.comap f P) P f rfl]
  have : IsScalarTower R (Localization.AtPrime (Ideal.comap f P)) (Localization.AtPrime P) :=
    .of_algebraMap_eq fun x ↦ (Localization.localRingHom_to_map _ _ _ rfl x).symm
  replace h : Module.Flat (Localization.AtPrime (Ideal.comap f P)) (Localization.AtPrime P) := h ..
  exact Module.Flat.trans R (Localization.AtPrime <| Ideal.comap f P) (Localization.AtPrime P)

lemma localRingHom {f : R →+* S} (hf : f.Flat)
    (P : Ideal S) [P.IsPrime] (Q : Ideal R) [Q.IsPrime] (hQP : Q = Ideal.comap f P) :
    (Localization.localRingHom Q P f hQP).Flat := by
  subst hQP
  algebraize [f, Localization.localRingHom (Ideal.comap f P) P f rfl]
  have : IsScalarTower R (Localization.AtPrime (Ideal.comap f P)) (Localization.AtPrime P) :=
    .of_algebraMap_eq fun x ↦ (Localization.localRingHom_to_map _ _ _ rfl x).symm
  rw [RingHom.Flat, Module.flat_iff_of_isLocalization
    (S := (Localization.AtPrime (Ideal.comap f P))) (p := (Ideal.comap f P).primeCompl)]
  exact Module.Flat.trans R S (Localization.AtPrime P)

open PrimeSpectrum

/-- `Spec S → Spec R` is generalizing if `R →+* S` is flat. -/
lemma generalizingMap_comap {f : R →+* S} (hf : f.Flat) : GeneralizingMap (comap f) := by
  algebraize [f]
  change GeneralizingMap (comap (algebraMap R S))
  rw [← Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
lemma of_isField (hR : IsField R) (f : R →+* S) : f.Flat := by
  let := f.toAlgebra
  let := hR.toField
  rw [← f.algebraMap_toAlgebra, RingHom.flat_algebraMap_iff]
  infer_instance

section

variable [Algebra R S]
variable (A : Type*) {B C D : Type*} [CommRing A] [Algebra R A] [Algebra S A]
  [IsScalarTower R S A] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C] [Algebra S C]
  [IsScalarTower R S C] [CommRing D] [Algebra R D]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
lemma lTensor {f : B →ₐ[R] D} (hf : f.Flat) :
    (Algebra.TensorProduct.lTensor (S := S) A f).Flat := by
  algebraize [f.toRingHom, (Algebra.TensorProduct.lTensor (S := A) A f).toRingHom]
  let e : A ⊗[R] D ≃ₐ[A ⊗[R] B] (A ⊗[R] B) ⊗[B] D :=
    { __ := (Algebra.IsPushout.cancelBaseChangeAlg _ _ _ _ _).symm,
      commutes' x := congr($(Algebra.IsPushout.cancelBaseChange_symm_comp_lTensor R B D A) x) }
  exact .of_linearEquiv e.toLinearEquiv

variable {A} in
lemma tensorProductMap {f : A →ₐ[S] C} {g : B →ₐ[R] D} (hf : f.Flat) (hg : g.Flat) :
    (Algebra.TensorProduct.map f g).Flat := by
  have heq : Algebra.TensorProduct.map f g =
      (Algebra.TensorProduct.map f (.id R D)).comp (Algebra.TensorProduct.map (.id _ _) g) := by
    ext <;> simp
  rw [heq]
  refine RingHom.Flat.comp ?_ ?_
  · exact hg.lTensor _
  · have : (Algebra.TensorProduct.map f (AlgHom.id R D)).restrictScalars R =
        (Algebra.TensorProduct.comm _ _ _).toAlgHom.comp
          ((Algebra.TensorProduct.lTensor _ (f.restrictScalars R)).comp
            (Algebra.TensorProduct.comm _ _ _).toAlgHom) := by
      ext <;> simp
    change ((Algebra.TensorProduct.map f (AlgHom.id R D)).restrictScalars R).Flat
    rw [this]
    refine RingHom.Flat.comp ?_ (.of_bijective <| AlgEquiv.bijective _)
    change RingHom.Flat (RingHom.comp (Algebra.TensorProduct.lTensor D
      (AlgHom.restrictScalars R f)).toRingHom _)
    exact RingHom.Flat.comp (.of_bijective <| (TensorProduct.comm R A D).bijective) (lTensor D hf)

end

end RingHom.Flat

section

open CategoryTheory Limits

variable {R S T : CommRingCat} (f : R ⟶ S) (g : R ⟶ T)

lemma CommRingCat.inr_injective_of_flat
    (hf : Function.Injective f) (hg : g.hom.Flat) : Function.Injective (pushout.inr f g) := by
  algebraize [f.hom, g.hom]
  have : _ = pushout.inr f g := (CommRingCat.isPushout_tensorProduct R S T).inr_isoPushout_hom
  rw [← this]
  exact (CommRingCat.isPushout_tensorProduct R S T).isoPushout.commRingCatIsoToRingEquiv
    |>.injective.comp (Algebra.TensorProduct.includeRight_injective (B := T) hf)

lemma CommRingCat.inl_injective_of_flat
    (hf : f.hom.Flat) (hg : Function.Injective g) : Function.Injective (pushout.inl f g) := by
  algebraize [f.hom, g.hom]
  have : _ = pushout.inl f g := (CommRingCat.isPushout_tensorProduct R S T).inl_isoPushout_hom
  rw [← this]
  exact (CommRingCat.isPushout_tensorProduct R S T).isoPushout.commRingCatIsoToRingEquiv
    |>.injective.comp (Algebra.TensorProduct.includeLeft_injective (S := R) (A := S) hg)

end
