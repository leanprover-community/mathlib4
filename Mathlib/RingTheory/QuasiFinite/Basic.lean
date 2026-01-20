/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Finiteness.NilpotentKer
public import Mathlib.RingTheory.Jacobson.Artinian
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Spectrum.Prime.Jacobson
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.Topology.DiscreteSubset

/-!
# Quasi-finite algebras

In this file, we define the notion of quasi-finite algebras and prove basic properties about them

## Main definition and results
- `Algebra.QuasiFinite`: The class of quasi-finite algebras.
  We say that an `R`-algebra `S` is quasi-finite
  if `κ(p) ⊗[R] S` is finite-dimensional over `κ(p)` for all primes `p` of `R`.
- `Algebra.QuasiFinite.finite_comap_preimage_singleton`:
  Quasi-finite algebras have finite fibers.
- `Algebra.QuasiFinite.iff_of_isArtinianRing`:
  Over an artinian ring, an algebra is quasi-finite iff it is module-finite.
- `Algebra.QuasiFinite.iff_finite_comap_preimage_singleton`: For a finite-type `R`-algebra `S`,
  `S` is quasi-finite if and only if `Spec S → Spec R` has finite fibers.

-/

@[expose] public section

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

open TensorProduct

-- for performance reasons
attribute [-instance] Module.Free.instFaithfulSMulOfNontrivial Algebra.IsIntegral.isLocalHom

namespace Algebra

variable (R S) in
/--
We say that an `R`-algebra `S` is quasi-finite
if `κ(p) ⊗[R] S` is finite-dimensional over `κ(p)` for all primes `p` of `R`.

This is slightly different from the
[stacks projects definition](https://stacks.math.columbia.edu/tag/00PL),
which requires `S` to be of finite type over `R`.

Also see `Algebra.QuasiFinite.iff_finite_comap_preimage_singleton` that
this is equivalent to having finite fibers for finite-type algebas.
-/
@[mk_iff, stacks 00PL]
class QuasiFinite : Prop where
  finite_fiber (P : Ideal R) [P.IsPrime] :
    Module.Finite P.ResidueField (P.Fiber S) := by infer_instance

attribute [stacks 00PM] quasiFinite_iff

namespace QuasiFinite

attribute [instance] finite_fiber

instance [QuasiFinite R S] (P : Ideal R) [P.IsPrime] : IsArtinianRing (P.Fiber S) :=
  .of_finite P.ResidueField _

lemma finite_comap_preimage_singleton [QuasiFinite R S] (P : PrimeSpectrum R) :
    (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {P}).Finite :=
  (PrimeSpectrum.preimageEquivFiber R S P).finite_iff.mpr finite_of_compact_of_discrete

lemma finite_primesOver [QuasiFinite R S] (I : Ideal R) : (I.primesOver S).Finite := by
  by_cases h : I.IsPrime
  · refine ((finite_comap_preimage_singleton ⟨I, h⟩).image PrimeSpectrum.asIdeal).subset ?_
    exact fun J hJ ↦ ⟨⟨_, hJ.1⟩, PrimeSpectrum.ext hJ.2.1.symm, rfl⟩
  · convert Set.finite_empty
    by_contra!
    obtain ⟨J, h₁, ⟨rfl⟩⟩ := this
    exact h inferInstance

lemma finite_comap_preimage [QuasiFinite R S] {s : Set (PrimeSpectrum R)} (hs : s.Finite) :
    (PrimeSpectrum.comap (algebraMap R S) ⁻¹' s).Finite :=
  hs.preimage' fun _ _ ↦ finite_comap_preimage_singleton _

lemma isDiscrete_comap_preimage_singleton [QuasiFinite R S] (P : PrimeSpectrum R) :
    IsDiscrete (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {P}) :=
  ⟨(PrimeSpectrum.preimageHomeomorphFiber R S P).symm.discreteTopology⟩

lemma isDiscrete_comap_preimage [QuasiFinite R S] {s : Set (PrimeSpectrum R)}
    (hs : IsDiscrete s) :
    IsDiscrete (PrimeSpectrum.comap (algebraMap R S) ⁻¹' s) :=
  hs.preimage' (PrimeSpectrum.continuous_comap _).continuousOn
    fun _ ↦ isDiscrete_comap_preimage_singleton _

instance (priority := low) [Module.Finite R S] : QuasiFinite R S where

@[stacks 00PP "(3)"]
instance baseChange [QuasiFinite R S] {A : Type*} [CommRing A] [Algebra R A] :
    QuasiFinite A (A ⊗[R] S) := by
  refine ⟨fun P hP ↦ ?_⟩
  let p := P.under R
  let e : P.Fiber (A ⊗[R] S) ≃ₐ[P.ResidueField] P.ResidueField ⊗[p.ResidueField] (p.Fiber S) :=
    (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).trans
      (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm
  exact .of_surjective e.symm.toLinearMap e.symm.surjective

open IsLocalRing in
-- See `Module.Finite.of_quasiFinite` instead
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

lemma iff_of_isArtinianRing [IsArtinianRing R] :
    QuasiFinite R S ↔ Module.Finite R S :=
  ⟨fun _ ↦ .of_quasiFinite, fun _ ↦ inferInstance⟩

attribute [local instance] TensorProduct.rightAlgebra in
variable (R S T) in
@[stacks 00PO]
lemma trans [QuasiFinite R S] [QuasiFinite S T] : QuasiFinite R T := by
  refine ⟨fun P hP ↦ ?_⟩
  have : Module.Finite (P.Fiber S) ((P.Fiber S) ⊗[S] T) :=
    iff_of_isArtinianRing.mp inferInstance
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
    rw [← AlgHom.coe_restrictScalars' (R := S), ← AlgHom.coe_toLinearMap, ← LinearMap.range_eq_top,
      ← top_le_iff, ← TensorProduct.span_tmul_eq_top, Submodule.span_le]
    rintro _ ⟨a, b, rfl⟩
    exact ⟨a ⊗ₜ b, by simp [f]⟩
  have : Module.Finite P.ResidueField (P.ResidueField ⊗[R] T) := .of_quasiFinite
  exact .of_surjective f.toLinearMap hf

variable (R S) in
lemma discreteTopology_primeSpectrum [DiscreteTopology (PrimeSpectrum R)] [QuasiFinite R S] :
    DiscreteTopology (PrimeSpectrum S) :=
  isDiscrete_univ_iff.mp
    (isDiscrete_comap_preimage (R := R) (S := S) (isDiscrete_univ_iff.mpr ‹_›))

variable (R S) in
lemma finite_primeSpectrum [Finite (PrimeSpectrum R)] [QuasiFinite R S] :
    Finite (PrimeSpectrum S) :=
  Set.finite_univ_iff.mp
    (finite_comap_preimage (Set.finite_univ (α := PrimeSpectrum R)))

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
  congr($((isDiscrete_comap_preimage_singleton ⟨_, inferInstance⟩).eq_of_specializes
    (a := ⟨P, ‹_›⟩) (b := ⟨Q, ‹_›⟩) (by simpa [← PrimeSpectrum.le_iff_specializes]) rfl
    (PrimeSpectrum.ext h₂.symm)).1)

instance [QuasiFinite R S] (P : Ideal R) [P.IsPrime] (Q : Ideal S) [Q.IsPrime] [Q.LiesOver P] :
    Module.Finite P.ResidueField Q.ResidueField :=
  have : QuasiFinite P.ResidueField Q.ResidueField := .of_restrictScalars R _ _
  .of_quasiFinite

section Finite

lemma iff_finite_comap_preimage_singleton [FiniteType R S] :
    QuasiFinite R S ↔ ∀ x, (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {x}).Finite := by
  refine ⟨fun H _ ↦ finite_comap_preimage_singleton _, fun H ↦ ⟨fun P _ ↦ ?_⟩⟩
  rw [Module.finite_iff_isArtinianRing, isArtinianRing_iff_isNoetherianRing_krullDimLE_zero]
  have : IsJacobsonRing (P.Fiber S) := isJacobsonRing_of_finiteType (A := P.ResidueField)
  have : Finite (PrimeSpectrum (P.Fiber S)) :=
    (PrimeSpectrum.preimageEquivFiber R S ⟨P, ‹_›⟩).finite_iff.mp (H ⟨P, ‹_›⟩)
  exact ⟨Algebra.FiniteType.isNoetherianRing P.ResidueField _,
    (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp inferInstance).right⟩

lemma iff_finite_primesOver [FiniteType R S] :
    QuasiFinite R S ↔ ∀ I : Ideal R, I.IsPrime → (I.primesOver S).Finite := by
  rw [iff_finite_comap_preimage_singleton,
    (PrimeSpectrum.equivSubtype R).forall_congr_left, Subtype.forall]
  refine forall₂_congr fun I hI ↦ ?_
  rw [← Set.finite_image_iff (Function.Injective.injOn fun _ _ ↦ PrimeSpectrum.ext)]
  congr!
  ext J
  simp [(PrimeSpectrum.equivSubtype S).exists_congr_left, PrimeSpectrum.ext_iff, eq_comm,
    PrimeSpectrum.equivSubtype, Ideal.primesOver, and_comm, Ideal.liesOver_iff, Ideal.under]

/-- If `T` is both a finite type `R`-algebra, and the localization of an integral `R`-algebra
(away from an element), then `T` is quasi-finite over `R` -/
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

end Algebra
