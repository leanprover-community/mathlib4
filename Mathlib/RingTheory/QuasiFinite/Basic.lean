/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Finiteness.NilpotentKer
public import Mathlib.RingTheory.Jacobson.Artinian
public import Mathlib.RingTheory.LocalRing.ResidueField.Polynomial
public import Mathlib.RingTheory.Spectrum.Prime.Jacobson
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.RingTheory.TensorProduct.Quotient

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
- `Algebra.QuasiFiniteAt`: If `S` is an `R`-algebra and `p` a prime of `S`,
  we say that `S` is `R`-quasi-finite at `p` if `Sₚ` is `R`-quasi-finite.

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

section QuasiFiniteAt

variable (R) in
/-- If `S` is an `R`-algebra and `p` a prime of `S`, we say that `S` is `R`-quasi-finite at `p`
if `Sₚ` is `R`-quasi-finite. In the case where `S` is (essentially) of finite type over `R`,
this is equivalent to the usual definition that `p` is isolated in its fiber.
See `Ideal.exists_notMem_forall_mem_of_ne_of_liesOver`. -/
abbrev QuasiFiniteAt (p : Ideal S) [p.IsPrime] : Prop :=
  QuasiFinite R (Localization.AtPrime p)

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

lemma QuasiFiniteAt.of_surjectiveOnStalks_of_liesOver (p : Ideal S) [p.IsPrime]
    [QuasiFiniteAt R p] (hf : (algebraMap S T).SurjectiveOnStalks) (q : Ideal T) [q.IsPrime]
    [q.LiesOver p] : QuasiFiniteAt R q :=
  .of_surjectiveOnStalks p (IsScalarTower.toAlgHom R S T) hf _ (q.over_def p)

instance QuasiFiniteAt.comap_algEquiv (p : Ideal S) [p.IsPrime] [Algebra.QuasiFiniteAt R p]
    (f : T ≃ₐ[R] S) : QuasiFiniteAt R (p.comap f.toRingHom) :=
  .of_surjectiveOnStalks p f.symm.toAlgHom
    (RingHom.surjectiveOnStalks_of_surjective f.symm.surjective) _ (by ext; simp)

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
lemma QuasiFiniteAt.eq_of_le_of_under_eq {P Q : Ideal S} [P.IsPrime] [Q.IsPrime]
    (h₁ : P ≤ Q) (h₂ : P.under R = Q.under R) [QuasiFiniteAt R Q] :
    P = Q := by
  have : Disjoint (Q.primeCompl : Set S) P := by simpa [Set.disjoint_iff, Set.ext_iff, not_imp_comm]
  have inst := IsLocalization.isPrime_of_isPrime_disjoint _ (Localization.AtPrime Q) P ‹_› this
  have H := QuasiFinite.eq_of_le_of_under_eq (R := R)
    (Ideal.map (algebraMap S (Localization.AtPrime Q)) P) _
    (IsLocalRing.le_maximalIdeal_of_isPrime _) (by
      convert h₂ <;> rw [← Ideal.under_under (B := S), Ideal.under_def S]
      · rw [IsLocalization.comap_map_of_isPrime_disjoint Q.primeCompl _ ‹P.IsPrime› this]
      · rw [Localization.AtPrime.comap_maximalIdeal])
  rw [← Localization.AtPrime.comap_maximalIdeal (I := Q), ← H,
    IsLocalization.comap_map_of_isPrime_disjoint Q.primeCompl _ ‹P.IsPrime› this]

instance (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p] [QuasiFiniteAt R P] :
    Module.Finite p.ResidueField P.ResidueField := by
  let m := IsLocalRing.maximalIdeal (Localization.AtPrime P)
  let : m.LiesOver p := .trans _ P _
  let e := AlgEquiv.ofBijective (IsScalarTower.toAlgHom p.ResidueField P.ResidueField
    m.ResidueField) ((RingHom.surjectiveOnStalks_of_isLocalization
        P.primeCompl _).residueFieldMap_bijective P m (m.over_def P))
  exact .of_surjective e.symm.toLinearMap e.symm.surjective

lemma QuasiFiniteAt.exists_basicOpen_eq_singleton
    (p : Ideal S) [p.IsPrime] [IsArtinianRing R] [Algebra.EssFiniteType R S]
    [Algebra.QuasiFiniteAt R p] :
    ∃ f ∉ p, (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum S)) = {⟨p, ‹_›⟩} := by
  have : IsLocalizedModule p.primeCompl (.id (R := S) (M := Localization.AtPrime p)) :=
    ⟨IsLocalizedModule.map_units (Algebra.linearMap S (Localization.AtPrime p)),
      fun y ↦ ⟨⟨y, 1⟩, by simp⟩, by simpa using ⟨1, p.primeCompl.one_mem⟩⟩
  have : Module.Finite R (Localization.AtPrime p) := .of_quasiFinite
  have : Module.Finite S (Localization.AtPrime p) := .of_restrictScalars_finite R _ _
  have : IsArtinianRing (Localization.AtPrime p) := .of_finite R _
  have : IsNoetherianRing S := Algebra.EssFiniteType.isNoetherianRing R S
  have : Module.FinitePresentation S (Localization.AtPrime p) :=
    Module.finitePresentation_of_finite _ _
  obtain ⟨r, hrp, H⟩ := IsLocalizedModule.exists_isLocalizedModule_powers_of_finitePresentation
    p.primeCompl (Algebra.linearMap S (Localization.AtPrime p))
  have : IsLocalization (.powers r) (Localization.AtPrime p) :=
    (isLocalizedModule_iff_isLocalization' _ _).mp H
  let φ : Localization.Away r ≃ₐ[S] Localization.AtPrime p :=
    IsLocalization.algEquiv (.powers r) _ _
  refine ⟨r, hrp, subset_antisymm (fun q hrq ↦ ?_) (Set.singleton_subset_iff.mpr hrp)⟩
  obtain ⟨q, rfl⟩ := (PrimeSpectrum.localization_away_comap_range (Localization.Away r) r).ge hrq
  obtain ⟨q, rfl⟩ := (PrimeSpectrum.comapEquiv φ.toRingEquiv).symm.surjective q
  -- As Sₚ is an artinian local ring, its prime spectrum is a singleton.
  obtain rfl : q = IsLocalRing.closedPoint _ := Subsingleton.elim _ _
  ext1
  dsimp
  rw [Ideal.comap_comap, ← AlgEquiv.toAlgHom_toRingHom, AlgHom.comp_algebraMap]
  exact IsLocalization.AtPrime.comap_maximalIdeal _ _

/-- If `R` is an artinian ring, and `S` is a finite type `R`-algebra `R`-quasi-finite at `p`,
then `{p}` is clopen in `Spec S`. -/
lemma QuasiFiniteAt.isClopen_singleton
    (p : PrimeSpectrum S) [IsArtinianRing R] [Algebra.FiniteType R S]
    [Algebra.QuasiFiniteAt R p.asIdeal] : IsClopen {p} := by
  have : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := R)
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  refine ((PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing p).out 0 1).mp ?_
  obtain ⟨f, hf, e⟩ := exists_basicOpen_eq_singleton (R := R) p.asIdeal
  exact e ▸ (PrimeSpectrum.basicOpen f).isOpen

attribute [local instance] RingHom.ker_isPrime in
lemma _root_.Ideal.exists_not_mem_forall_mem_of_ne_of_liesOver
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [Algebra.EssFiniteType R S] [Algebra.QuasiFiniteAt R q] :
    ∃ s ∉ q, ∀ q' : Ideal S, q'.IsPrime → q' ≠ q → q'.LiesOver p → s ∈ q' := by
  classical
  let e := PrimeSpectrum.preimageHomeomorphFiber _ S ⟨p, inferInstance⟩
  let qF : PrimeSpectrum (p.Fiber S) := e ⟨⟨q, ‹_›⟩, PrimeSpectrum.ext (q.over_def p).symm⟩
  have : Algebra.QuasiFiniteAt p.ResidueField qF.asIdeal := .baseChange q _
    congr($(e.symm_apply_apply ⟨⟨q, ‹_›⟩, PrimeSpectrum.ext (q.over_def p).symm⟩).1.1).symm
  obtain ⟨r, hr, hrq⟩ := Algebra.QuasiFiniteAt.exists_basicOpen_eq_singleton
    (R := p.ResidueField) qF.asIdeal
  obtain ⟨s, hs, x, hsx⟩ := Ideal.Fiber.exists_smul_eq_one_tmul _ r
  have : x ∉ q := by
    have : r ∉ _ := hrq.ge rfl
    simp only [PrimeSpectrum.preimageHomeomorphFiber, PrimeSpectrum.preimageOrderIsoFiber,
      Homeomorph.homeomorph_mk_coe, qF, e] at this
    rw [PrimeSpectrum.preimageEquivFiber_apply_asIdeal,
        ← Ideal.IsPrime.mul_mem_left_iff (x := algebraMap _ _ s), ← Algebra.smul_def, hsx] at this
    · simpa using this
    · simpa [IsScalarTower.algebraMap_apply R S q.ResidueField, q.over_def p] using hs
  refine ⟨x, this, fun q' _ hq' _ ↦ not_not.mp fun hxq' ↦ hq' ?_⟩
  refine congr($(e.injective (a₁ := ⟨⟨q', ‹_›⟩, PrimeSpectrum.ext (q'.over_def p).symm⟩)
    (a₂ := ⟨⟨q, ‹_›⟩, PrimeSpectrum.ext (q.over_def p).symm⟩) (hrq.le ?_)).1.1)
  simp only [PrimeSpectrum.basicOpen_eq_zeroLocus_compl, PrimeSpectrum.preimageHomeomorphFiber,
    PrimeSpectrum.preimageOrderIsoFiber, Homeomorph.homeomorph_mk_coe, Set.mem_compl_iff,
    PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe, e]
  rw [PrimeSpectrum.preimageEquivFiber_apply_asIdeal,
    ← Ideal.IsPrime.mul_mem_left_iff (x := algebraMap _ _ s), ← Algebra.smul_def, hsx]
  · simpa
  · simpa [IsScalarTower.algebraMap_apply R S q'.ResidueField, ← Ideal.mem_comap, ← q'.over_def p]

end QuasiFiniteAt

end Algebra

namespace Polynomial

/-- `R[X]` is not quasi-finite over `R` at any prime. -/
lemma not_quasiFiniteAt (P : Ideal R[X]) [P.IsPrime] : ¬ Algebra.QuasiFiniteAt R P := by
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
  rw [Algebra.QuasiFiniteAt, Algebra.QuasiFinite.iff_of_isArtinianRing] at H
  have := Module.Finite.of_injective
    (IsScalarTower.toAlgHom R R[X] (Localization.AtPrime P)).toLinearMap
    (IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors)
  exact transcendental_X R (Algebra.IsIntegral.isIntegral X).isAlgebraic

lemma map_under_lt_comap_of_quasiFiniteAt
    (f : R[X] →ₐ[R] S) (P : Ideal S) [P.IsPrime] [Algebra.QuasiFiniteAt R P] :
    (P.under R).map C < P.comap (f : R[X] →+* S) := by
  algebraize [f.toRingHom]
  refine lt_of_le_of_ne (Ideal.map_le_iff_le_comap.mpr ?_) fun e ↦ ?_
  · rw [Ideal.comap_comap, ← algebraMap_eq, f.comp_algebraMap]
  have : Module.Finite (P.under R).ResidueField (P.under R[X]).ResidueField :=
    .of_injective (IsScalarTower.toAlgHom _ _ P.ResidueField).toLinearMap
      (algebraMap (P.under R[X]).ResidueField P.ResidueField).injective
  have : Module.Finite (P.under R).ResidueField (RatFunc (P.under R).ResidueField) :=
    .of_surjective (residueFieldMapCAlgEquiv _ (P.under _) e.symm).toLinearMap
      (residueFieldMapCAlgEquiv _ (P.under _) e.symm).surjective
  exact RatFunc.transcendental_X (K := (P.under R).ResidueField)
    (Algebra.IsIntegral.isIntegral _).isAlgebraic

/--
If `P` is a prime of `R[X]/I` that is quasi finite over `R`,
then `I` is not contained in `(P ∩ R)[X]`.

For usability, we replace `I` by the kernel of a surjective map `R[X] →ₐ[R] S`. -/
lemma not_ker_le_map_C_of_surjective_of_quasiFiniteAt
    (f : R[X] →ₐ[R] S) (hf : Function.Surjective f)
    (P : Ideal S) [P.IsPrime] [Algebra.QuasiFiniteAt R P] :
    ¬ RingHom.ker f ≤ (P.under R).map C := by
  intro H
  algebraize [f.toRingHom]
  let p := P.under R
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

end Polynomial
