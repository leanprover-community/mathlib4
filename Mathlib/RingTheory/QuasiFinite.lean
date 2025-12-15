/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CFT.Prestuff
public import Mathlib.RingTheory.Jacobson.Artinian
public import Mathlib.RingTheory.Spectrum.Prime.Jacobson
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Finiteness.NilpotentKer
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.LocalRing.ResidueField.Polynomial
public import Mathlib.RingTheory.Noetherian.Nilpotent

/-! # Quasi-finite -/

@[expose] public section

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

open TensorProduct PrimeSpectrum

attribute [-instance] Module.free_of_finite_type_torsion_free'
  NoZeroSMulDivisors.instFaithfulSMulOfNontrivial
  Module.Free.instFaithfulSMulOfNontrivial

namespace Algebra

variable (R S) in
@[mk_iff]
class QuasiFinite : Prop where
  finite_fiber (P : Ideal R) [P.IsPrime] :
    Module.Finite P.ResidueField (P.Fiber S) := by infer_instance

namespace QuasiFinite

attribute [instance] finite_fiber

instance [QuasiFinite R S] (P : Ideal R) [P.IsPrime] : IsArtinianRing (P.Fiber S) :=
  .of_finite P.ResidueField _

lemma finite_specComap_preimage_singleton [QuasiFinite R S] (P : PrimeSpectrum R) :
    (comap (algebraMap R S) ⁻¹' {P}).Finite :=
  (PrimeSpectrum.preimageEquivFiber R S P).finite_iff.mpr finite_of_compact_of_discrete

lemma finite_primesOver [QuasiFinite R S] (I : Ideal R) : (I.primesOver S).Finite := by
  by_cases h : I.IsPrime
  · refine ((finite_specComap_preimage_singleton ⟨I, h⟩).image PrimeSpectrum.asIdeal).subset ?_
    exact fun J hJ ↦ ⟨⟨_, hJ.1⟩, PrimeSpectrum.ext hJ.2.1.symm, rfl⟩
  · convert Set.finite_empty
    by_contra!
    obtain ⟨J, h₁, ⟨rfl⟩⟩ := this
    exact h inferInstance

lemma finite_specComap_preimage [QuasiFinite R S] {s : Set (PrimeSpectrum R)} (hs : s.Finite) :
    (comap (algebraMap R S) ⁻¹' s).Finite :=
  hs.preimage' fun _ _ ↦ finite_specComap_preimage_singleton _

lemma isDiscrete_specComap_preimage_singleton [QuasiFinite R S] (P : PrimeSpectrum R) :
    IsDiscrete (comap (algebraMap R S) ⁻¹' {P}) :=
  ⟨(PrimeSpectrum.preimageHomeomorphFiber R S P).symm.discreteTopology⟩

lemma isDiscrete_specComap_preimage [QuasiFinite R S] {s : Set (PrimeSpectrum R)}
    (hs : IsDiscrete s) :
    IsDiscrete (comap (algebraMap R S) ⁻¹' s) :=
  hs.preimage' (PrimeSpectrum.continuous_comap _).continuousOn
    fun _ ↦ isDiscrete_specComap_preimage_singleton _

instance (priority := low) [Module.Finite R S] : QuasiFinite R S where

instance baseChange [QuasiFinite R S] {A : Type*} [CommRing A] [Algebra R A] :
    QuasiFinite A (A ⊗[R] S) := by
  refine ⟨fun P hP ↦ ?_⟩
  let p := P.under R
  let e : P.Fiber (A ⊗[R] S) ≃ₐ[P.ResidueField] P.ResidueField ⊗[p.ResidueField] (p.Fiber S) :=
    (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).trans
      (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm
  exact .of_surjective e.symm.toLinearMap e.symm.surjective

lemma Ideal.algebraMap_residueField_surjective
    {R : Type*} [CommRing R] (I : Ideal R) [I.IsMaximal] :
    Function.Surjective (algebraMap R I.ResidueField) := by
  rw [IsScalarTower.algebraMap_eq R (R ⧸ I) _]
  exact I.bijective_algebraMap_quotient_residueField.surjective.comp Ideal.Quotient.mk_surjective

-- move me
instance {R : Type*} [CommRing R] (I : Ideal R) [I.IsMaximal] :
    Module.Finite R I.ResidueField :=
  .of_surjective (Algebra.linearMap _ _) I.algebraMap_residueField_surjective

-- See `Module.Finite.of_quasiFinite` instead
open IsLocalRing in
private lemma finite_of_isArtinianRing_of_isLocalRing
    [QuasiFinite R S] [IsArtinianRing R] [IsLocalRing R] : Module.Finite R S := by
  let e : (maximalIdeal R).Fiber S ≃ₐ[R] S ⧸ (maximalIdeal R).map (algebraMap R S) :=
    (Algebra.TensorProduct.congr (.symm <| .ofBijective _
      (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))) .refl).trans <|
    (Algebra.TensorProduct.comm _ _ _).trans
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot _ _).symm.restrictScalars _)
  have : Module.Finite R (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
    have : Module.Finite R ((maximalIdeal R).Fiber S) :=
      .trans (maximalIdeal R).ResidueField _
    .of_surjective e.toLinearMap e.surjective
  refine Module.finite_of_surjective_of_ker_le_nilradical (Ideal.Quotient.mkₐ R
    ((maximalIdeal R).map (algebraMap R S))) Ideal.Quotient.mk_surjective ?_ ?_
  · refine Ideal.mk_ker.trans_le ?_
    rw [Ideal.map_le_iff_le_comap, ← Ring.KrullDimLE.nilradical_eq_maximalIdeal]
    exact fun x hx ↦ IsNilpotent.map hx _
  · rw [← RingHom.ker_coe_toRingHom, Ideal.Quotient.mkₐ_ker]
    exact Ideal.FG.map (IsNoetherian.noetherian _) _

lemma _root_.Module.Finite.of_quasiFinite [IsArtinianRing R] [QuasiFinite R S] :
    Module.Finite R S := by
  classical
  let e : R ≃ₐ[R] PrimeSpectrum.PiLocalization R :=
    .ofBijective (IsScalarTower.toAlgHom _ _ _)
      (PrimeSpectrum.discreteTopology_iff_toPiLocalization_bijective.mp inferInstance)
  have : Fintype (PrimeSpectrum R) := .ofFinite _
  let e' : S ≃ₐ[R] Π p : PrimeSpectrum R, Localization p.asIdeal.primeCompl ⊗[R] S :=
    (Algebra.TensorProduct.rid R R S).symm.trans <| (Algebra.TensorProduct.congr .refl e).trans <|
      (Algebra.TensorProduct.piRight _ _ _ _).trans <| AlgEquiv.piCongrRight
      fun _ ↦ Algebra.TensorProduct.comm _ _ _
  have (p : PrimeSpectrum R) : Module.Finite R (Localization p.asIdeal.primeCompl ⊗[R] S) :=
    have : Module.Finite R (Localization.AtPrime p.asIdeal) :=
      .of_surjective (Algebra.linearMap _ _)
        (IsArtinianRing.localization_surjective p.asIdeal.primeCompl _)
    have : Module.Finite (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⊗[R] S) := finite_of_isArtinianRing_of_isLocalRing
    .trans (Localization.AtPrime p.asIdeal) _
  exact .of_surjective e'.symm.toLinearMap e'.symm.surjective

lemma quasiFinite_iff_of_isArtinianRing [IsArtinianRing R] :
    QuasiFinite R S ↔ Module.Finite R S :=
  ⟨fun _ ↦ .of_quasiFinite, fun _ ↦ inferInstance⟩

attribute [local instance] TensorProduct.rightAlgebra in
variable (R S T) in
lemma trans [QuasiFinite R S] [QuasiFinite S T] : QuasiFinite R T := by
  refine ⟨fun P hP ↦ ?_⟩
  have : Module.Finite (P.Fiber S) ((P.Fiber S) ⊗[S] T) :=
    quasiFinite_iff_of_isArtinianRing.mp inferInstance
  have : Module.Finite P.ResidueField ((P.Fiber S) ⊗[S] T) :=
    .trans (P.Fiber S) _
  let e : P.Fiber S ≃ₐ[S] S ⊗[R] P.ResidueField :=
    { __ := Algebra.TensorProduct.comm _ _ _, commutes' _ := rfl }
  let e' : (P.Fiber S) ⊗[S] T ≃ₐ[R] P.Fiber T :=
    ((Algebra.TensorProduct.congr e .refl).restrictScalars R).trans <|
    ((Algebra.TensorProduct.comm _ _ _).restrictScalars R).trans <|
    ((Algebra.TensorProduct.cancelBaseChange _ _ T _ _).restrictScalars R).trans
    (Algebra.TensorProduct.comm _ _ _)
  let e'' : (P.Fiber S) ⊗[S] T ≃ₐ[P.ResidueField] P.Fiber T :=
    { __ := e', commutes' _ := by simp [e', e] }
  exact .of_surjective e''.toLinearMap e''.surjective

omit [Algebra S T] in
lemma of_surjective_algHom [QuasiFinite R S] (f : S →ₐ[R] T) (hf : Function.Surjective f) :
    QuasiFinite R T :=
  let := f.toRingHom.toAlgebra
  let := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have : Module.Finite S T := .of_surjective (Algebra.linearMap _ _) hf
  trans R S T

instance (I : Ideal S) [QuasiFinite R S] : QuasiFinite R (S ⧸ I) :=
  of_surjective_algHom (Ideal.Quotient.mkₐ _ _) Ideal.Quotient.mk_surjective

lemma of_isLocalization (M : Submonoid S) [IsLocalization M T] [QuasiFinite R S] :
    QuasiFinite R T :=
  letI : QuasiFinite S T := by
    refine ⟨fun P hP ↦ .of_surjective (Algebra.linearMap P.ResidueField (P.Fiber T)) ?_⟩
    rw [← LinearMap.coe_restrictScalars (R := S), ← LinearMap.range_eq_top,
      ← top_le_iff, ← TensorProduct.span_tmul_eq_top, Submodule.span_le]
    rintro _ ⟨p, s, rfl⟩
    obtain ⟨s, t, rfl⟩ := IsLocalization.exists_mk'_eq M s
    use s • p / algebraMap _ _ t.1
    apply ((IsLocalization.map_units T t).map
      Algebra.TensorProduct.includeRight).mul_left_injective
    by_cases ht : algebraMap _ P.ResidueField t.1 = 0
    · simp [ht]
    trans (s • p) ⊗ₜ[S] 1
    · simp [div_mul_cancel₀ _ ht]
    · dsimp; simp [Algebra.algebraMap_eq_smul_one, smul_tmul]
  trans R S T

instance (M : Submonoid S) [QuasiFinite R S] : QuasiFinite R (Localization M) := of_isLocalization M

instance (priority := low) [IsFractionRing R S] : QuasiFinite R S :=
  of_isLocalization (nonZeroDivisors R)

instance (P : Ideal S) [P.IsPrime] [QuasiFinite R S] : QuasiFinite R P.ResidueField :=
  .trans _ (S ⧸ P) _

variable (R S T) in
lemma of_restrictScalars [QuasiFinite R T] : QuasiFinite S T := by
  refine ⟨fun P hP ↦ ?_⟩
  let f : P.ResidueField ⊗[R] T →ₐ[P.ResidueField] P.Fiber T :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _)
      (Algebra.TensorProduct.includeRight.restrictScalars R) fun _ _ ↦ .all _ _
  have hf : Function.Surjective f := by
    rw [← AlgHom.coe_restrictScalars' (R := S), ← LinearMap.range_eq_top,
      ← top_le_iff, ← TensorProduct.span_tmul_eq_top, Submodule.span_le]
    rintro _ ⟨a, b, rfl⟩
    exact ⟨a ⊗ₜ b, by simp [f]⟩
  have : Module.Finite P.ResidueField (P.ResidueField ⊗[R] T) := .of_quasiFinite
  exact .of_surjective f.toLinearMap hf

variable (R S) in
lemma discreteTopology_primeSpectrum [DiscreteTopology (PrimeSpectrum R)] [QuasiFinite R S] :
    DiscreteTopology (PrimeSpectrum S) :=
  isDiscrete_univ_iff.mp
    (isDiscrete_specComap_preimage (R := R) (S := S) (isDiscrete_univ_iff.mpr ‹_›))

variable (R S) in
lemma finite_primeSpectrum [Finite (PrimeSpectrum R)] [QuasiFinite R S] :
    Finite (PrimeSpectrum S) :=
  Set.finite_univ_iff.mp
    (finite_specComap_preimage (Set.finite_univ (α := PrimeSpectrum R)))

omit [Algebra S T] in
lemma of_forall_exists_mul_mem_range [QuasiFinite R S] (f : S →ₐ[R] T)
    (H : ∀ x : T, ∃ s : S, IsUnit (f s) ∧ x * f s ∈ f.range) :
    QuasiFinite R T := by
  let φ : Localization ((IsUnit.submonoid T).comap f) →ₐ[R] T :=
    IsLocalization.liftAlgHom (M := (IsUnit.submonoid T).comap f) (f := f)
      (by simp [IsUnit.mem_submonoid_iff])
  suffices Function.Surjective φ from .of_surjective_algHom φ this
  intro x
  obtain ⟨s, hs, t, ht⟩ := H x
  refine ⟨IsLocalization.mk' (M := (IsUnit.submonoid T).comap f) _ t ⟨s, hs⟩, ?_⟩
  simpa [φ, IsLocalization.lift_mk', Units.mul_inv_eq_iff_eq_mul, IsUnit.coe_liftRight]

omit [Algebra S T] in
lemma eq_of_le_of_under_eq [QuasiFinite R S] (P Q : Ideal S) [P.IsPrime] [Q.IsPrime]
    (h₁ : P ≤ Q) (h₂ : P.under R = Q.under R) : P = Q :=
  congr($((isDiscrete_specComap_preimage_singleton ⟨_, inferInstance⟩).eq_of_specializes
    (a := ⟨P, ‹_›⟩) (b := ⟨Q, ‹_›⟩) (by simpa [← PrimeSpectrum.le_iff_specializes]) rfl
    (PrimeSpectrum.ext h₂.symm)).1)

instance [QuasiFinite R S] (P : Ideal R) [P.IsPrime] (Q : Ideal S) [Q.IsPrime] [Q.LiesOver P] :
    Module.Finite P.ResidueField Q.ResidueField :=
  have : QuasiFinite P.ResidueField Q.ResidueField := .of_restrictScalars R _ _
  .of_quasiFinite

section Finite

lemma iff_finite_specComap_preimage_singleton [FiniteType R S] :
    QuasiFinite R S ↔ ∀ x, (comap (algebraMap R S) ⁻¹' {x}).Finite := by
  refine ⟨fun H _ ↦ finite_specComap_preimage_singleton _, fun H ↦ ⟨fun P _ ↦ ?_⟩⟩
  rw [Module.finite_iff_isArtinianRing, isArtinianRing_iff_isNoetherianRing_krullDimLE_zero]
  have : IsJacobsonRing (P.Fiber S) := isJacobsonRing_of_finiteType (A := P.ResidueField)
  have : Finite (PrimeSpectrum (P.Fiber S)) :=
    (PrimeSpectrum.preimageEquivFiber R S ⟨P, ‹_›⟩).finite_iff.mp (H ⟨P, ‹_›⟩)
  exact ⟨.of_essFiniteType P.ResidueField _,
    (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp inferInstance).right⟩

lemma iff_finite_primesOver [FiniteType R S] :
    QuasiFinite R S ↔ ∀ I : Ideal R, I.IsPrime → (I.primesOver S).Finite := by
  rw [iff_finite_specComap_preimage_singleton,
    (PrimeSpectrum.equivSubtype R).forall_congr_left, Subtype.forall]
  refine forall₂_congr fun I hI ↦ ?_
  rw [← Set.finite_image_iff (Function.Injective.injOn fun _ _ ↦ PrimeSpectrum.ext)]
  congr!
  ext J
  simp [(PrimeSpectrum.equivSubtype S).exists_congr_left, PrimeSpectrum.ext_iff, eq_comm,
    PrimeSpectrum.equivSubtype, Ideal.primesOver, and_comm, Ideal.liesOver_iff, Ideal.under]

lemma iff_finite_specComap_preimage [FiniteType R S] :
    QuasiFinite R S ↔ ∀ s, s.Finite → (comap (algebraMap R S) ⁻¹' s).Finite :=
  ⟨fun _ _ ↦ finite_specComap_preimage, fun H ↦
    iff_finite_specComap_preimage_singleton.mpr fun _ ↦ H _ (Set.finite_singleton _)⟩

lemma quasiFinite_iff_isArtinianRing_of_essFiniteType
    [IsArtinianRing R] [Algebra.EssFiniteType R S] :
    QuasiFinite R S ↔ Module.Finite R S := by
  refine ⟨fun H ↦ ?_, fun _ ↦ ?_⟩
  · have : IsArtinianRing S :=
      isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mpr
      ⟨.of_essFiniteType R S, (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp
        (discreteTopology_primeSpectrum R S)).2⟩
    suffices ∀ (Q : Ideal S) [Q.IsPrime], Module.Finite R (Localization.AtPrime Q) from
      let e : S ≃ₐ[R] PrimeSpectrum.PiLocalization S :=
        .ofBijective (IsScalarTower.toAlgHom _ _ _)
          ((PrimeSpectrum.discreteTopology_iff_toPiLocalization_bijective (R := S)).mp
            inferInstance)
      .of_surjective e.symm.toLinearMap e.symm.surjective
    intro Q _
    have : Module.Finite R Q.ResidueField := .trans (Q.under R).ResidueField _
    refine Module.finite_of_surjective_of_ker_le_nilradical (IsScalarTower.toAlgHom R _ _)
        Q.algebraMap_localization_residueField_surjective ?_ (IsNoetherian.noetherian _)
    rw [Ring.KrullDimLE.nilradical_eq_maximalIdeal]
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
  · have : IsArtinianRing S := .of_finite R S
    rw [iff_finite_specComap_preimage_singleton]
    exact fun _ ↦ Set.toFinite _

/-- If `T` is both a finite type `R`-algebra, and the localization of an integral `R`-algebra,
then `T` is quasi-finite over `R` -/
lemma of_isIntegral_of_finiteType [Algebra.IsIntegral R S] [Algebra.FiniteType R T]
    (s : S) [IsLocalization.Away s T] : Algebra.QuasiFinite R T := by
  let A := Algebra.adjoin R {s}
  let sA : A := ⟨s, Algebra.subset_adjoin (by simp)⟩
  let f : Localization.Away sA →+* T := IsLocalization.Away.lift sA (g := algebraMap _ _)
    (IsLocalization.Away.algebraMap_isUnit s)
  let := f.toAlgebra
  let : Algebra A (Localization.Away sA) := OreLocalization.instAlgebra
  let : SMul A (Localization.Away sA) := Algebra.toSMul
  let : MulAction A (Localization.Away sA) := Algebra.toModule.toDistribMulAction.toMulAction
  have : IsScalarTower R A (Localization.Away sA) := OreLocalization.instIsScalarTower
  have : IsScalarTower A (Localization.Away sA) T :=
    .of_algebraMap_eq (by simp [f, RingHom.algebraMap_toAlgebra, A])
  have : IsScalarTower R (Localization.Away sA) T := .to₁₃₄ R A (Localization.Away sA) T
  have : Algebra.IsIntegral (Localization.Away sA) T := by
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (.powers s) x
    have : _root_.IsIntegral (Localization.Away sA) (algebraMap S T x) :=
      (Algebra.IsIntegral.isIntegral (R := R) x).algebraMap.tower_top
    convert this.smul (Localization.Away.invSelf sA ^ n)
    rw [IsLocalization.mk'_eq_iff_eq_mul]
    simp only [map_pow, Algebra.smul_mul_assoc]
    trans (sA • Localization.Away.invSelf sA) ^ n • (algebraMap S T x)
    · simp [Algebra.smul_def, -map_pow, Localization.Away.invSelf, Localization.mk_eq_mk']
    · simp only [Algebra.smul_def, map_pow, map_mul, mul_pow,
        ← IsScalarTower.algebraMap_apply, Subalgebra.algebraMap_def, sA]
      ring
  have : Module.Finite (Localization.Away sA) T :=
    have : Algebra.FiniteType (Localization.Away sA) T := .of_restrictScalars_finiteType R _ _
    Algebra.IsIntegral.finite
  have : Module.Finite R A :=
    Algebra.finite_adjoin_simple_of_isIntegral (Algebra.IsIntegral.isIntegral _)
  have : Algebra.QuasiFinite R (Localization.Away sA) := .of_isLocalization (.powers sA)
  exact .trans _ (Localization.Away sA) _

end Finite

end QuasiFinite

section locus

variable (R) in
abbrev QuasiFiniteAt (p : Ideal S) [p.IsPrime] : Prop :=
  QuasiFinite R (Localization.AtPrime p)

attribute [simp] Localization.localRingHom_to_map

lemma QuasiFiniteAt.baseChange (p : Ideal S) [p.IsPrime] [QuasiFiniteAt R p]
    {A : Type*} [CommRing A] [Algebra R A] (q : Ideal (A ⊗[R] S)) [q.IsPrime]
    (hq : p = q.comap Algebra.TensorProduct.includeRight.toRingHom) :
    QuasiFiniteAt A q := by
  let f : A ⊗[R] Localization.AtPrime p →ₐ[A] Localization.AtPrime q :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) ⟨Localization.localRingHom _ _ _ hq, by
      simp [IsScalarTower.algebraMap_apply R S (Localization.AtPrime p),
        IsScalarTower.algebraMap_apply R (A ⊗[R] S) (Localization.AtPrime q)]⟩ fun _ _ ↦ .all _ _
  let g : A ⊗[R] S →ₐ[A] A ⊗[R] Localization.AtPrime p :=
    Algebra.TensorProduct.map (.id _ _) (IsScalarTower.toAlgHom _ _ _)
  have : f.comp g = IsScalarTower.toAlgHom _ _ _ := by ext; simp [f, g]
  replace this (x : _) : f (g x) = algebraMap _ _ x := DFunLike.congr_fun this x
  refine .of_forall_exists_mul_mem_range f fun x ↦ ?_
  obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl x
  refine ⟨g s, this s ▸ IsLocalization.map_units _ ⟨s, hs⟩, ?_⟩
  rw [this, IsLocalization.mk'_spec_mk]
  exact ⟨g x, this x⟩

omit [Algebra S T] in
lemma QuasiFiniteAt.of_surjectiveOnStalks (p : Ideal S) [p.IsPrime] [QuasiFiniteAt R p]
    (f : S →ₐ[R] T) (hf : f.SurjectiveOnStalks) (q : Ideal T) [q.IsPrime]
    (hq : p = q.comap f.toRingHom) :
    QuasiFiniteAt R q := by
  subst hq
  refine .of_surjective_algHom ⟨Localization.localRingHom _ q f.toRingHom rfl, ?_⟩ (hf q ‹_›)
  simp [IsScalarTower.algebraMap_apply R S (Localization.AtPrime (q.comap _)),
    IsScalarTower.algebraMap_apply R T (Localization.AtPrime _)]

omit [Algebra S T] in
lemma QuasiFiniteAt.of_le {P Q : Ideal S} [P.IsPrime] [Q.IsPrime]
    (h₁ : P ≤ Q) [QuasiFiniteAt R Q] :
    QuasiFiniteAt R P := by
  let f : Localization.AtPrime Q →ₐ[R] Localization.AtPrime P :=
    IsLocalization.liftAlgHom (M := Q.primeCompl) (f := IsScalarTower.toAlgHom _ _ _) <| by
      simp only [IsScalarTower.coe_toAlgHom', Subtype.forall, Ideal.mem_primeCompl_iff]
      exact fun a ha ↦ IsLocalization.map_units (M := P.primeCompl) _ ⟨a, fun h ↦ ha (h₁ h)⟩
  refine .of_forall_exists_mul_mem_range f fun x ↦ ?_
  obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl x
  exact ⟨algebraMap _ _ s, by simpa [f] using IsLocalization.map_units _ ⟨s, hs⟩,
    algebraMap _ _ x, by simp [f]⟩

omit [Algebra S T] in
lemma QuasiFiniteAt.eq_of_le_of_under_eq (P Q : Ideal S) [P.IsPrime] [Q.IsPrime]
    (h₁ : P ≤ Q) (h₂ : P.under R = Q.under R) [QuasiFiniteAt R Q] :
    P = Q := by
  have : Disjoint (Q.primeCompl : Set S) P := by simpa [Set.disjoint_iff, Set.ext_iff, not_imp_comm]
  have inst := IsLocalization.isPrime_of_isPrime_disjoint _ (Localization.AtPrime Q) P ‹_› this
  have H := QuasiFinite.eq_of_le_of_under_eq (R := R)
    (Ideal.map (algebraMap S (Localization.AtPrime Q)) P) _
    (IsLocalRing.le_maximalIdeal_of_isPrime _) (by
      convert h₂ <;> rw [← Ideal.under_under (B := S), Ideal.under_def S]
      · rw [IsLocalization.comap_map_of_isPrime_disjoint Q.primeCompl _ _ ‹P.IsPrime› this]
      · rw [Localization.AtPrime.comap_maximalIdeal])
  rw [← Localization.AtPrime.comap_maximalIdeal (I := Q), ← H,
    IsLocalization.comap_map_of_isPrime_disjoint Q.primeCompl _ _ ‹P.IsPrime› this]

instance (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p] [QuasiFiniteAt R P] :
    Module.Finite p.ResidueField P.ResidueField := by
  let m := IsLocalRing.maximalIdeal (Localization.AtPrime P)
  have : m.LiesOver p := .trans _ P _
  let e := AlgEquiv.ofBijective (IsScalarTower.toAlgHom p.ResidueField P.ResidueField
    m.ResidueField) ((RingHom.surjectiveOnStalks_of_isLocalization
        P.primeCompl _).residueFieldMap_bijective P m (m.over_def P))
  exact .of_surjective e.symm.toLinearMap e.symm.surjective

end locus

instance QuasiFiniteAt.comap_algEquiv (p : Ideal S) [p.IsPrime] [Algebra.QuasiFiniteAt R p]
    (f : T ≃ₐ[R] S) : QuasiFiniteAt R (p.comap f.toRingHom) :=
  .of_surjectiveOnStalks p f.symm.toAlgHom
    (RingHom.surjectiveOnStalks_of_surjective f.symm.surjective) _ (by ext; simp)

end Algebra

open Polynomial

lemma Polynomial.not_quasiFiniteAt
  {R : Type*} [CommRing R] (P : Ideal R[X]) [P.IsPrime] : ¬ Algebra.QuasiFiniteAt R P := by
  intro H
  wlog hR : IsField R
  · let p := P.under R
    obtain ⟨Q, hQ⟩ := (PrimeSpectrum.preimageEquivFiber R R[X]
        ⟨p, inferInstance⟩).symm.surjective ⟨⟨P, ‹_›⟩, rfl⟩
    have inst : Algebra.QuasiFiniteAt p.ResidueField Q.asIdeal :=
      .baseChange P Q.asIdeal congr($(hQ.symm).1.1)
    exact this (Q.asIdeal.comap (polyEquivTensor' R p.ResidueField).toRingHom)
      inferInstance (Field.toIsField _)
  let := hR.toField
  rw [Algebra.QuasiFiniteAt,
    Algebra.QuasiFinite.quasiFinite_iff_isArtinianRing_of_essFiniteType] at H
  have := Module.Finite.of_injective
    (IsScalarTower.toAlgHom R R[X] (Localization.AtPrime P)).toLinearMap
    (IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors)
  exact Polynomial.not_isIntegral_X (Algebra.IsIntegral.isIntegral (R := R) X)

lemma Ideal.map_under_lt_comap_of_quasiFiniteAt
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (f : R[X] →ₐ[R] S) (P : Ideal S) [P.IsPrime] [Algebra.QuasiFiniteAt R P] :
    (P.under R).map C < P.comap (f : R[X] →+* S) := by
  let := f.toRingHom.toAlgebra
  refine lt_of_le_of_ne (Ideal.map_le_iff_le_comap.mpr ?_) fun e ↦ ?_
  · rw [Ideal.comap_comap, ← algebraMap_eq, f.comp_algebraMap]
  have : Module.Finite (P.under R).ResidueField (P.under R[X]).ResidueField :=
    .of_injective (IsScalarTower.toAlgHom _ _ P.ResidueField).toLinearMap
      (algebraMap (P.under R[X]).ResidueField P.ResidueField).injective
  have : Module.Finite (P.under R).ResidueField (RatFunc (P.under R).ResidueField) :=
    .of_surjective (residueFieldMapCAlgEquiv _ (P.under _) e.symm).toLinearMap
      (residueFieldMapCAlgEquiv _ (P.under _) e.symm).surjective
  have : Algebra.IsIntegral (P.under R).ResidueField (RatFunc (P.under R).ResidueField) :=
    inferInstance
  exact RatFunc.not_isIntegral_X
    (Algebra.IsIntegral.isIntegral (R := (P.under R).ResidueField) RatFunc.X)

attribute [local instance 2000] Algebra.toSMul
  Ring.toAddCommGroup AddCommGroup.toAddCommMonoid Algebra.toModule Module.toDistribMulAction in
lemma Polynomial.ker_le_map_C_of_surjective_of_quasiFiniteAt
    (f : R[X] →ₐ[R] S) (hf : Function.Surjective f)
    (P : Ideal S) [P.IsPrime] [Algebra.QuasiFiniteAt R P]
    (p : Ideal R) [P.LiesOver p] :
    ¬ RingHom.ker f ≤ p.map C := by
  intro H
  let := f.toRingHom.toAlgebra
  have : p.IsPrime := P.over_def p ▸ inferInstance
  letI : Algebra (R[X] ⊗[R] p.ResidueField) (R[X] ⊗[R] p.ResidueField ⊗[R[X]]
    (R[X] ⧸ RingHom.ker f)) := Algebra.TensorProduct.leftAlgebra
  have : IsScalarTower R (R[X] ⊗[R] p.ResidueField)
      (R[X] ⊗[R] p.ResidueField ⊗[R[X]] (R[X] ⧸ RingHom.ker f)) :=
    TensorProduct.isScalarTower_left
  have H' : (RingHom.ker f).map (mapRingHom (algebraMap R p.ResidueField)) = ⊥ := by
    rw [← le_bot_iff, Ideal.map_le_iff_le_comap]
    intro x hx
    simpa [Polynomial.ext_iff, Ideal.mem_map_C_iff] using H hx
  let g' : p.ResidueField[X] ≃ₐ[p.ResidueField] p.Fiber S :=
    .trans ((AlgEquiv.quotientBot _ _).symm.trans (Ideal.quotientEquivAlgOfEq _ H'.symm))
      (Polynomial.fiberEquivQuotient f hf _).symm
  obtain ⟨Q, hQ⟩ := (PrimeSpectrum.preimageEquivFiber _ _
      ⟨p, inferInstance⟩).symm.surjective ⟨⟨P, ‹_›⟩, PrimeSpectrum.ext (P.over_def p).symm⟩
  have inst : Algebra.QuasiFiniteAt p.ResidueField Q.asIdeal :=
    .baseChange P Q.asIdeal congr($(hQ.symm).1.1)
  exact Polynomial.not_quasiFiniteAt (Q.asIdeal.comap g'.toRingHom) inferInstance
