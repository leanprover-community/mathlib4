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

/-! # Quasi-finite -/

@[expose] public section

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

open TensorProduct

namespace Algebra

variable (R S) in
@[mk_iff]
class QuasiFinite : Prop where
  isDiscrete_specComap_preimage_singleton :
    ∀ P : PrimeSpectrum R, IsDiscrete ((algebraMap R S).specComap ⁻¹' {P})
  finite_residueField_residueField :
    ∀ (P : Ideal R) [P.IsPrime] (Q : Ideal S) [Q.IsPrime] [Q.LiesOver P],
      Module.Finite P.ResidueField Q.ResidueField

namespace QuasiFinite

attribute [instance] finite_residueField_residueField

instance [QuasiFinite R S] (P : Ideal R) [P.IsPrime] :
    DiscreteTopology (PrimeSpectrum <| P.Fiber S) :=
  have := (QuasiFinite.isDiscrete_specComap_preimage_singleton (S := S) ⟨P, ‹_›⟩).to_subtype
  (PrimeSpectrum.preimageHomeomorphFiber R S ⟨P, _⟩).discreteTopology

instance [QuasiFinite R S] (P : Ideal R) [P.IsPrime] :
    Ring.KrullDimLE 0 (P.Fiber S) :=
  (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp inferInstance).right

lemma finite_specComap_preimage_singleton [QuasiFinite R S] (P : PrimeSpectrum R) :
    ((algebraMap R S).specComap ⁻¹' {P}).Finite :=
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
    ((algebraMap R S).specComap ⁻¹' s).Finite :=
  hs.preimage' fun _ _ ↦ finite_specComap_preimage_singleton _

lemma isDiscrete_specComap_preimage [QuasiFinite R S] {s : Set (PrimeSpectrum R)}
    (hs : IsDiscrete s) :
    IsDiscrete ((algebraMap R S).specComap ⁻¹' s) :=
  hs.preimage' (PrimeSpectrum.comap _).2.continuousOn
    fun _ ↦ isDiscrete_specComap_preimage_singleton _

lemma iff_isDiscrete_specComap_preimage :
    QuasiFinite R S ↔ (∀ s, IsDiscrete s → IsDiscrete ((algebraMap R S).specComap ⁻¹' s)) ∧
      (∀ (P : Ideal R) [P.IsPrime] (Q : Ideal S) [Q.IsPrime] [Q.LiesOver P],
        Module.Finite P.ResidueField Q.ResidueField) :=
  ⟨fun _ ↦ ⟨fun _ ↦ isDiscrete_specComap_preimage, finite_residueField_residueField⟩,
    fun H ↦ ⟨fun _ ↦ H.1 _ Set.subsingleton_singleton.isDiscrete, H.2⟩⟩

attribute [-instance] Module.free_of_finite_type_torsion_free'
  NoZeroSMulDivisors.instFaithfulSMulOfNontrivial
  Module.Free.instFaithfulSMulOfNontrivial in
lemma of_specComap_injective
    (H : Function.Injective (algebraMap R S).specComap)
    (H' : (algebraMap R S).SurjectiveOnStalks) : QuasiFinite R S :=
  ⟨fun _ ↦ (Set.subsingleton_singleton.preimage H).isDiscrete, fun _ _ _ _ e ↦
    .of_surjective (Algebra.ofId _ _).toLinearMap (H'.residueFieldMap_bijective _ _ e.1).surjective⟩

lemma of_surjective (H : Function.Surjective (algebraMap R S)) : QuasiFinite R S :=
  of_specComap_injective (PrimeSpectrum.specComap_injective_of_surjective _ H)
    (RingHom.surjectiveOnStalks_of_surjective H)

instance (I : Ideal R) : QuasiFinite R (R ⧸ I) := .of_surjective Ideal.Quotient.mk_surjective

variable (R S T) in
lemma trans [QuasiFinite R S] [QuasiFinite S T] : QuasiFinite R T := by
  refine iff_isDiscrete_specComap_preimage.mpr ⟨fun s hs ↦ ?_, fun P _ Q _ _ ↦ ?_⟩
  · rw [IsScalarTower.algebraMap_eq R S T, PrimeSpectrum.specComap_comp, Set.preimage_comp]
    exact isDiscrete_specComap_preimage (isDiscrete_specComap_preimage hs)
  · exact .trans (Q.under S).ResidueField _

omit [Algebra S T] in
lemma of_surjective_algHom [QuasiFinite R S] (f : S →ₐ[R] T) (hf : Function.Surjective f) :
    QuasiFinite R T :=
  letI := f.toRingHom.toAlgebra
  letI := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have := of_surjective hf
  trans R S T

lemma of_isLocalization (M : Submonoid S) [IsLocalization M T] [QuasiFinite R S] :
    QuasiFinite R T :=
  letI : QuasiFinite S T :=
    of_specComap_injective (PrimeSpectrum.localization_specComap_injective _ M)
      (RingHom.surjectiveOnStalks_of_isLocalization M _)
  trans R S T

instance (M : Submonoid S) [QuasiFinite R S] : QuasiFinite R (Localization M) := of_isLocalization M

variable (R S T) in
lemma of_restrictScalars [QuasiFinite R T] : QuasiFinite S T := by
  refine ⟨fun x ↦ (isDiscrete_specComap_preimage_singleton (S := T)
    ((algebraMap R S).specComap x)).mono ?_, fun P _ Q _ _ ↦ ?_⟩
  · rintro s rfl; simp
  · exact .of_restrictScalars_finite (P.under R).ResidueField _ _

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

-- Subsumed by `QuasiFinite.baseChange`
attribute [-instance] Module.free_of_finite_type_torsion_free'
  NoZeroSMulDivisors.instFaithfulSMulOfNontrivial
  Module.Free.instFaithfulSMulOfNontrivial in
private instance [QuasiFinite R S] (p : Ideal R) [p.IsPrime] :
    QuasiFinite p.ResidueField (p.Fiber S) := by
  refine ⟨fun _ ↦ ⟨inferInstance⟩, fun P _ Q _ _ ↦ ?_⟩
  have : Module.Finite p.ResidueField Q.ResidueField :=
    let e := Ideal.Fiber.residueFieldEquiv p _ Q rfl
    .of_surjective e.symm.toLinearMap e.symm.surjective
  have : P.LiesOver p := by rw [Ideal.eq_bot_of_prime P]; infer_instance
  exact .of_restrictScalars_finite p.ResidueField _ _

attribute [local instance] Ideal.bot_prime in
attribute [-instance] Module.free_of_finite_type_torsion_free'
  NoZeroSMulDivisors.instFaithfulSMulOfNontrivial
  Module.Free.instFaithfulSMulOfNontrivial in
lemma iff_residueField_tensorProduct :
    QuasiFinite R S ↔
      ∀ (p : Ideal R) [p.IsPrime], QuasiFinite p.ResidueField (p.Fiber S) := by
  refine ⟨fun _ _ _ ↦ inferInstance, fun H ↦ ⟨fun P ↦ ?_, fun P _ Q _ _ ↦ ?_⟩⟩
  · have := discreteTopology_primeSpectrum P.asIdeal.ResidueField (P.asIdeal.ResidueField ⊗[R] S)
    exact ⟨(PrimeSpectrum.preimageHomeomorphFiber R S P).symm.discreteTopology⟩
  · have := H P
    let Q' : PrimeSpectrum (P.Fiber S) := PrimeSpectrum.preimageEquivFiber
      R S ⟨P, ‹_›⟩ ⟨⟨Q, ‹_›⟩, PrimeSpectrum.ext (Q.over_def P).symm⟩
    have hQ' : Q'.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom = Q :=
      congr($((PrimeSpectrum.preimageEquivFiber R S ⟨P, _⟩).symm_apply_apply
        ⟨⟨Q, ‹_›⟩, PrimeSpectrum.ext (Q.over_def P).symm⟩).1.1)
    have := P.surjectiveOnStalks_residueField.residueFieldMap_bijective P ⊥
      (by simp [← RingHom.ker_eq_comap_bot])
    have : Module.Finite P.ResidueField (⊥ : Ideal P.ResidueField).ResidueField :=
      .of_surjective (Algebra.linearMap _ _) this.surjective
    have : Module.Finite P.ResidueField Q'.asIdeal.ResidueField :=
      .trans (⊥ : Ideal P.ResidueField).ResidueField _
    let e := Ideal.Fiber.residueFieldEquiv P Q Q'.asIdeal hQ'
    exact .of_surjective e.toLinearMap e.surjective

open IsLocalRing in
attribute [local instance] Ideal.bot_isMaximal in
instance {k K S : Type*} [Field k] [Field K] [CommRing S] [Algebra k K] [Algebra k S]
    [QuasiFinite k S] : DiscreteTopology (PrimeSpectrum (K ⊗[k] S)) := by
  classical
  wlog H : IsLocalRing S generalizing S
  · have inst := discreteTopology_primeSpectrum k S
    let e : S ≃ₐ[k] PrimeSpectrum.PiLocalization S :=
      .ofBijective (IsScalarTower.toAlgHom _ _ _)
        (PrimeSpectrum.discreteTopology_iff_toPiLocalization_bijective.mp ‹_›)
    have inst : Finite (PrimeSpectrum S) := finite_of_compact_of_discrete
    have inst : Fintype (PrimeSpectrum S) := .ofFinite _
    let e' : (K ⊗[k] S) ≃ₐ[k] Π p : PrimeSpectrum S, K ⊗[k] Localization p.asIdeal.primeCompl :=
      (Algebra.TensorProduct.congr .refl e).trans (Algebra.TensorProduct.piRight _ _ _ _)
    have (p : Ideal S) [p.IsPrime] :
        DiscreteTopology (PrimeSpectrum (K ⊗[k] Localization.AtPrime p)) := by
      suffices h : DiscreteTopology (PrimeSpectrum (Localization.AtPrime p)) from this inferInstance
      exact (PrimeSpectrum.localization_comap_isEmbedding _ p.primeCompl).discreteTopology
    exact ((PrimeSpectrum.homeomorphOfRingEquiv e'.toRingEquiv).trans
      (PrimeSpectrum.piHomeomorph _)).symm.discreteTopology
  have := (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp
    (discreteTopology_primeSpectrum k S)).2
  have : Module.Finite k (ResidueField S) :=
    have : Module.Finite k (maximalIdeal S).ResidueField :=
      .trans (⊥ : Ideal k).ResidueField _
    let e : ResidueField S ≃ₐ[k] (maximalIdeal S).ResidueField :=
      .ofBijective (IsScalarTower.toAlgHom _ (S ⧸ _) _)
        (Ideal.bijective_algebraMap_quotient_residueField _)
    .of_surjective e.symm.toLinearMap e.symm.surjective
  have : IsArtinianRing (K ⊗[k] ResidueField S) := .of_finite K _
  let φ : K ⊗[k] S →ₐ[k] K ⊗[k] ResidueField S :=
    Algebra.TensorProduct.map (.id _ _) (IsScalarTower.toAlgHom _ _ _)
  have h₁ : Function.Surjective φ :=
    Algebra.TensorProduct.map_surjective _ _ Function.surjective_id residue_surjective
  have h₂ : Function.Surjective (PrimeSpectrum.comap φ.toRingHom) := by
    intro p
    let f : K ⊗[k] ResidueField S →ₐ[k] K ⊗[k] S ⧸ p.asIdeal :=
      Algebra.TensorProduct.lift (IsScalarTower.toAlgHom _ _ _) (Ideal.Quotient.liftₐ _
        ((Ideal.Quotient.mkₐ _ _).comp Algebra.TensorProduct.includeRight) <| by
        have : p.comap Algebra.TensorProduct.includeRight.toRingHom = closedPoint _ :=
          Subsingleton.elim _ _
        replace this : (p.asIdeal.comap _) = maximalIdeal _ := congr(($this).1)
        rw [← this]
        simp [Ideal.Quotient.eq_zero_iff_mem]) fun _ _ ↦ .all _ _
    have H : f.comp φ = Ideal.Quotient.mkₐ _ _ := by ext <;> simp [f, φ] <;> rfl
    refine ⟨⟨_, RingHom.ker_isPrime f.toRingHom⟩, ?_⟩
    ext1
    simp [RingHom.comap_ker, ← AlgHom.comp_toRingHom, H]
  exact ((PrimeSpectrum.isClosedEmbedding_comap_of_surjective _
    φ.toRingHom h₁).isEmbedding.toHomeomorphOfSurjective h₂).discreteTopology

-- Subsumed by `QuasiFinite.baseChange`
-- set_option trace.profiler true in
-- set_option synthInstance.maxHeartbeats 0 in
attribute [local instance] Ideal.Quotient.field RingHom.ker_isPrime in
private instance {k K S : Type*} [Field k] [Field K] [CommRing S] [Algebra k K] [Algebra k S]
    [QuasiFinite k S] : QuasiFinite K (K ⊗[k] S) := by
  refine ⟨fun _ ↦ ⟨inferInstance⟩, fun P _ Q _ _ ↦ ?_⟩
  let q := Q.comap Algebra.TensorProduct.includeRight.toRingHom
  have : Module.Finite k q.ResidueField := .trans (q.under k).ResidueField _
  suffices Module.Finite K Q.ResidueField from .of_restrictScalars_finite K _ _
  have : Ring.KrullDimLE 0 (K ⊗[k] S) :=
    (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp inferInstance).right
  have : IsArtinianRing (K ⊗[k] q.ResidueField) := .of_finite K _
  have hq : q = RingHom.ker ((Ideal.Quotient.mkₐ k Q).comp TensorProduct.includeRight) := by
    rw [← RingHom.ker_coe_toRingHom, AlgHom.comp_toRingHom, ← RingHom.comap_ker]
    simp [q]
  let φ : K ⊗[k] q.ResidueField →ₐ[K] K ⊗[k] S ⧸ Q :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) (Ideal.ResidueField.liftₐ _
      ((Ideal.Quotient.mkₐ _ _).comp Algebra.TensorProduct.includeRight)
      (by simp [hq]) (fun x ↦ by
        simp only [hq, Ideal.mem_primeCompl_iff, RingHom.mem_ker, AlgHom.coe_comp,
          Ideal.Quotient.mkₐ_eq_mk, Function.comp_apply, ne_eq, Submonoid.mem_comap,
          IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero, imp_self])) fun _ _ ↦ .all _ _
  let Q' : Ideal (K ⊗[k] q.ResidueField) := RingHom.ker φ.toRingHom
  have : Module.Finite K Q'.ResidueField := .trans (K ⊗[k] q.ResidueField) _
  let e := RingEquiv.ofBijective _ <| RingHom.SurjectiveOnStalks.tensorProductMap
    (f := .id k K) (RingHom.surjectiveOnStalks_of_surjective Function.surjective_id)
    (g := IsScalarTower.toAlgHom k S q.ResidueField) q.surjectiveOnStalks_residueField
    |>.residueFieldMap_bijective Q Q' <| by
      rw [RingHom.comap_ker]
      convert Q.mk_ker.symm
      ext r s;
      simp [φ, IsScalarTower.algebraMap_apply K (K ⊗[k] S) (K ⊗[k] S ⧸ Q), ← map_mul]
  refine .of_equiv_equiv (.refl _) e.symm ?_
  ext x
  apply e.injective
  dsimp
  simp only [RingEquiv.apply_symm_apply]
  simp [e, IsScalarTower.algebraMap_apply K (K ⊗[k] S) Q.ResidueField,
    IsScalarTower.algebraMap_apply K (K ⊗[k] q.ResidueField) Q'.ResidueField]

attribute [-instance] Module.free_of_finite_type_torsion_free'
  NoZeroSMulDivisors.instFaithfulSMulOfNontrivial
  Module.Free.instFaithfulSMulOfNontrivial in
instance baseChange [QuasiFinite R S] {A : Type*} [CommRing A] [Algebra R A] :
    QuasiFinite A (A ⊗[R] S) := by
  rw [iff_residueField_tensorProduct]
  intro P _
  let p := P.under R
  let e : P.Fiber (A ⊗[R] S) ≃ₐ[P.ResidueField] P.ResidueField ⊗[p.ResidueField] (p.Fiber S) :=
    (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).trans
      (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm
  exact .of_surjective_algHom e.symm.toAlgHom e.symm.surjective

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

section Finite

attribute [-instance] Module.free_of_finite_type_torsion_free'
  NoZeroSMulDivisors.instFaithfulSMulOfNontrivial
  Module.Free.instFaithfulSMulOfNontrivial in
lemma iff_finite_specComap_preimage_singleton [FiniteType R S] :
    QuasiFinite R S ↔ ∀ x, ((algebraMap R S).specComap ⁻¹' {x}).Finite := by
  refine ⟨fun H _ ↦ finite_specComap_preimage_singleton _, fun H ↦ ?_⟩
  have (P : Ideal R) [P.IsPrime] : DiscreteTopology (PrimeSpectrum (P.Fiber S)) := by
    have : IsJacobsonRing (P.Fiber S) :=
      isJacobsonRing_of_finiteType (A := P.ResidueField)
    have : Finite (PrimeSpectrum (P.Fiber S)) :=
      (PrimeSpectrum.preimageEquivFiber R S ⟨P, ‹_›⟩).finite_iff.mp (H ⟨P, ‹_›⟩)
    infer_instance
  refine ⟨fun P ↦ ⟨(PrimeSpectrum.preimageHomeomorphFiber
    R S P).symm.discreteTopology⟩, fun P _ Q _ _ ↦ ?_⟩
  have : IsArtinianRing (P.Fiber S) :=
    isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mpr ⟨.of_essFiniteType P.ResidueField _,
      (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp (this P)).right⟩
  have : Module.Finite P.ResidueField (P.Fiber S) :=
    (Module.finite_iff_isArtinianRing _ _).mpr ‹_›
  let Q' := PrimeSpectrum.preimageEquivFiber R S ⟨P, ‹_›⟩
    ⟨⟨Q, ‹_›⟩, PrimeSpectrum.ext <| (Q.over_def P).symm⟩
  have : (IsScalarTower.toAlgHom R (P.Fiber S) Q'.asIdeal.ResidueField).comp
    (IsScalarTower.toAlgHom R P.ResidueField _) = IsScalarTower.toAlgHom _ _ _ := by ext
  let f : P.Fiber S →ₐ[P.ResidueField] Q'.asIdeal.ResidueField :=
    ⟨algebraMap _ _, fun r ↦ congr($this r)⟩
  have : Module.Finite P.ResidueField Q'.asIdeal.ResidueField :=
    .of_surjective f.toLinearMap (Ideal.algebraMap_residueField_surjective _)
  have := (PrimeSpectrum.preimageEquivFiber R S ⟨P, ‹_›⟩).symm_apply_apply
    ⟨⟨Q, ‹_›⟩, PrimeSpectrum.ext <| (Q.over_def P).symm⟩
  let e := Ideal.Fiber.residueFieldEquiv P Q Q'.asIdeal congr($(this).1.1)
  exact .of_surjective e.toLinearMap e.surjective

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
    QuasiFinite R S ↔ ∀ s, s.Finite → ((algebraMap R S).specComap ⁻¹' s).Finite :=
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

attribute [-instance] Module.free_of_finite_type_torsion_free'
  NoZeroSMulDivisors.instFaithfulSMulOfNontrivial
  Module.Free.instFaithfulSMulOfNontrivial in
instance (priority := low) [Module.Finite R S] : QuasiFinite R S := by
  rw [iff_finite_specComap_preimage_singleton]
  intro P
  have : IsArtinianRing (P.asIdeal.Fiber S) := .of_finite P.asIdeal.ResidueField _
  exact (PrimeSpectrum.preimageEquivFiber R S P).finite_iff.mpr inferInstance

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

attribute [-instance] Module.free_of_finite_type_torsion_free'
  NoZeroSMulDivisors.instFaithfulSMulOfNontrivial
  Module.Free.instFaithfulSMulOfNontrivial in
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

attribute [-instance] Module.free_of_finite_type_torsion_free'
  NoZeroSMulDivisors.instFaithfulSMulOfNontrivial
  Module.Free.instFaithfulSMulOfNontrivial in
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
attribute [-instance] Module.free_of_finite_type_torsion_free'
  NoZeroSMulDivisors.instFaithfulSMulOfNontrivial
  Module.Free.instFaithfulSMulOfNontrivial in
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
  have H' : (RingHom.ker f).map (algebraMap R[X] (R[X] ⊗[R] p.ResidueField)) = ⊥ := by
    rw [← le_bot_iff, Ideal.map_le_iff_le_comap]
    intro x hx
    refine ((polyEquivTensor R _).trans (Algebra.TensorProduct.comm _ _ _)).symm.injective ?_
    simpa [Polynomial.ext_iff, Ideal.mem_map_C_iff] using H hx
  let g : p.Fiber S ≃ₐ[R] p.ResidueField[X] :=
    .trans (Algebra.TensorProduct.congr .refl (Ideal.quotientKerAlgEquivOfSurjective hf).symm) <|
    .trans (Algebra.TensorProduct.cancelBaseChangeLeft R R[X] _ _).symm <|
    .trans ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot _ _).symm.restrictScalars R) <|
    .trans (Ideal.quotientEquivAlgOfEq _ H') <|
    .trans (AlgEquiv.quotientBot _ _) <|
    .trans (Algebra.TensorProduct.comm _ _ _) <| (polyEquivTensor _ _).symm
  have : g.symm.toRingHom.comp (algebraMap p.ResidueField _) = algebraMap _ _ := by
    ext r
    change g.symm _ = _
    simp [g]
  let g' : p.ResidueField[X] ≃ₐ[p.ResidueField] p.Fiber S :=
    { __ := g.symm.toRingEquiv, commutes' r := congr($this r) }
  obtain ⟨Q, hQ⟩ := (PrimeSpectrum.preimageEquivFiber _ _
      ⟨p, inferInstance⟩).symm.surjective ⟨⟨P, ‹_›⟩, PrimeSpectrum.ext (P.over_def p).symm⟩
  have inst : Algebra.QuasiFiniteAt p.ResidueField Q.asIdeal :=
    .baseChange P Q.asIdeal congr($(hQ.symm).1.1)
  exact Polynomial.not_quasiFiniteAt (Q.asIdeal.comap g'.toRingHom) inferInstance
