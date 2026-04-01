/-
Copyright (c) 2025 Jingting Wang, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Junyan Xu, Andrew Yang
-/
module

public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Spectrum.Prime.TensorProduct
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The fiber of a ring homomorphism at a prime ideal

## Main results

* `Ideal.Fiber`: `p.Fiber S` is the fiber of a prime `p` of `R` in an `R`-algebra `S`,
  defined to be `κ(p) ⊗ S`.
* `PrimeSpectrum.preimageHomeomorphFiber` : We show that there is a homeomorphism between the
  fiber of the induced map `PrimeSpectrum S → PrimeSpectrum R` at a prime ideal `p` and
  the prime spectrum of `p.Fiber S`.
-/

@[expose] public section

-- PR #37380
namespace Localization

open TensorProduct Algebra

variable {R : Type*} [CommRing R] (M : Submonoid R) (Rₘ : Type*) [CommRing Rₘ] [Algebra R Rₘ]
  (S : Type*) [CommRing S] [Algebra R S]

/-- The isomorphism `S ⊗[R] Rₘ ≃ₐ[S] Sₘ`. This is a specialization of `IsLocalization.algEquiv`,
but with additional properties since now `Sₘ` is automatically an `Rₘ`-algebra. -/
noncomputable def tensor_localization_algEquiv :
    (S ⊗[R] Localization M) ≃ₐ[S] Localization (Algebra.algebraMapSubmonoid S M) :=
  (Localization.algEquiv (Algebra.algebraMapSubmonoid S M) (S ⊗[R] Localization M)).symm

@[simp]
theorem tensor_localization_algEquiv_apply_tmul_one (x : S) :
    Localization.tensor_localization_algEquiv M S (x ⊗ₜ[R] 1) = algebraMap _ _ x :=
  (Localization.tensor_localization_algEquiv M S).commutes x

@[simp]
theorem tensor_localization_algEquiv_apply_one_tmul (x : Localization M) :
    Localization.tensor_localization_algEquiv M S (1 ⊗ₜ[R] x) = algebraMap _ _ x := by
  let Rₘ := Localization M
  let Sₘ := Localization (Algebra.algebraMapSubmonoid S M)
  obtain ⟨x, y, rfl⟩ := IsLocalization.exists_mk'_eq M x
  letI : Algebra Rₘ (S ⊗[R] Rₘ) := Algebra.TensorProduct.rightAlgebra
  have h1 : (1 : S) ⊗ₜ[R] IsLocalization.mk' Rₘ x y = algebraMap _ _ (IsLocalization.mk' Rₘ x y) :=
    rfl
  rw [h1, Localization.tensor_localization_algEquiv, Localization.algEquiv_symm_apply,
    IsLocalization.algebraMap_mk' S, IsLocalization.map_mk', IsLocalization.mk'_eq_iff_eq_mul]
  simp_rw [RingHom.id_apply]
  have h x : algebraMap S Sₘ ((algebraMap R S) x) = algebraMap Rₘ Sₘ ((algebraMap R Rₘ) x) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rw [h, h, ← map_mul, IsLocalization.mk'_spec]

/-- The isomorphism `Rₘ ⊗[R] S ≃ₐ[Rₘ] Sₘ`. -/
noncomputable def localization_tensor_algEquiv :
    (Localization M ⊗[R] S) ≃ₐ[Localization M] Localization (Algebra.algebraMapSubmonoid S M) :=
  { __ := (Algebra.TensorProduct.comm R (Localization M) S).toRingEquiv.trans
      (Localization.tensor_localization_algEquiv M S).toRingEquiv
    commutes' := Localization.tensor_localization_algEquiv_apply_one_tmul M S }

@[simp]
theorem localization_tensor_algEquiv_apply_tmul_one (x : Localization M) :
    Localization.localization_tensor_algEquiv M S (x ⊗ₜ[R] 1) = algebraMap _ _ x :=
  (Localization.localization_tensor_algEquiv M S).commutes x

@[simp]
theorem localization_tensor_algEquiv_apply_one_tmul (x : S) :
    Localization.localization_tensor_algEquiv M S (1 ⊗ₜ[R] x) = algebraMap _ _ x :=
  (Localization.tensor_localization_algEquiv M S).commutes x

end Localization

--PR #37382
namespace Algebra.TensorProduct

open _root_.TensorProduct

variable {R : Type*} (S T A : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [CommRing T] [Algebra R T] [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]

/-- The tensor product over `R` of the quotient of an `S`-algebra `A` by an ideal `I` with `T`
is isomorphic to the quotient of `A ⊗[R] T` by the extended ideal, as an `S`-algebra. -/
noncomputable def quotientTensorEquiv (I : Ideal A) :
    (A ⧸ I) ⊗[R] T ≃ₐ[S] (A ⊗[R] T) ⧸ I.map (algebraMap A (A ⊗[R] T)) :=
  { __ := (TensorProduct.comm R (A ⧸ I) T).toRingEquiv.trans <|
      (tensorQuotientEquiv (R := R) R A T I).toRingEquiv.trans <|
      Ideal.quotientEquiv _ _ (TensorProduct.comm R T A).toRingEquiv <| (I.map_map _ _).symm
    commutes' _ := rfl }

@[simp]
lemma quotientTensorEquiv_apply_tmul (I : Ideal A) (a : A) (t : T) :
    quotientTensorEquiv (R := R) S T A I (a ⊗ₜ t) = a ⊗ₜ[R] t :=
  rfl

@[simp]
lemma quotientTensorEquiv_symm_apply_tmul (I : Ideal A) (a : A) (t : T) :
    (quotientTensorEquiv (R := R) S T A I).symm (a ⊗ₜ[R] t) = Ideal.Quotient.mk _ a ⊗ₜ[R] t :=
  rfl

end Algebra.TensorProduct

open Algebra TensorProduct nonZeroDivisors

variable {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] (S : Type*) [CommRing S] [Algebra R S]

set_option backward.isDefEq.respectTransparency false in
open IsLocalRing in
instance [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] :
    IsLocalRing (ResidueField R ⊗[R] S) :=
  let eSp : ResidueField R ⊗[R] S ≃ₐ[R] S ⧸ (maximalIdeal R).map (algebraMap R S) :=
    (Algebra.TensorProduct.comm _ _ _).trans
      ((TensorProduct.quotIdealMapEquivTensorQuot _ _).symm.restrictScalars _)
  have : Nontrivial (IsLocalRing.ResidueField R ⊗[R] S) := by
    rw [eSp.nontrivial_congr, Ideal.Quotient.nontrivial_iff]
    exact ((((local_hom_TFAE (algebraMap R S)).out 0 2 rfl rfl).mp inferInstance).trans_lt
      (inferInstance : (maximalIdeal S).IsMaximal).lt_top).ne
  .of_surjective' TensorProduct.includeRight.toRingHom
    (TensorProduct.mk_surjective _ _ _ residue_surjective)

@[deprecated "Use `Ideal.Fiber.exists_smul_eq_algebraMap` instead." (since := "2026-03-31")]
lemma Ideal.ResidueField.exists_smul_eq_tmul_one
    (x : S ⊗[R] p.ResidueField) : ∃ r ∉ p, ∃ s, r • x = s ⊗ₜ[R] 1 := by
  obtain ⟨t, r, a, hrt, e⟩ := RingHom.SurjectiveOnStalks.exists_mul_eq_tmul
    p.surjectiveOnStalks_residueField x ⊥ isPrime_bot
  obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective t
  obtain ⟨⟨y, t⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl t
  simp only [smul_def, Submodule.mem_bot, mul_eq_zero, algebraMap_residueField_eq_zero,
    IsLocalRing.residue_eq_zero_iff, not_or, IsLocalization.AtPrime.mk'_mem_maximal_iff] at hrt
  refine ⟨r * y, p.primeCompl.mul_mem hrt.1 hrt.2, y • a, ?_⟩
  rw [Algebra.smul_def, ← Algebra.TensorProduct.includeRight.commutes, smul_tmul,
    ← Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.includeRight_apply]
  simpa [← tmul_smul, Submonoid.smul_def, ← smul_mul_assoc, smul_comm _ r,
    ← IsLocalRing.ResidueField.algebraMap_eq, ← algebraMap.coe_smul,
    ← IsScalarTower.algebraMap_apply] using congr(t • $e)

/-- The fiber of a prime `p` of `R` in an `R`-algebra `S`, defined to be `κ(p) ⊗ S`.

See `PrimeSpectrum.preimageHomeomorphFiber` for the homeomorphism between the spectrum of it
and the actual set-theoretic fiber of `PrimeSpectrum S → PrimeSpectrum R` at `p`. -/
structure Ideal.Fiber where
  of : p.ResidueField ⊗[R] S

namespace Ideal.Fiber

/-- The bijection used to transfer instances from `κ(p) ⊗ S` to `p.Fiber S`. -/
def equiv : p.Fiber S ≃ p.ResidueField ⊗[R] S where
  toFun := Ideal.Fiber.of
  invFun x := ⟨x⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : CommRing (p.Fiber S) :=
  (Ideal.Fiber.equiv p S).commRing

noncomputable instance : Algebra R (p.Fiber S) :=
  (Ideal.Fiber.equiv p S).algebra R

noncomputable instance : Algebra p.ResidueField (p.Fiber S) :=
  (Ideal.Fiber.equiv p S).algebra p.ResidueField

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
noncomputable instance : Algebra S (p.Fiber S) :=
  (Ideal.Fiber.equiv p S).algebra S

instance : IsScalarTower R p.ResidueField (p.Fiber S) :=
  IsScalarTower.of_algebraMap_eq' rfl

instance : IsScalarTower R S (p.Fiber S) :=
  IsScalarTower.of_algebraMap_eq fun x ↦ congrArg _ (algebraMap_apply' x)

/-- `p.Fiber S` is isomorphic to the tensor product `κ(p) ⊗[R] S`. -/
noncomputable def algEquivTensor : p.Fiber S ≃ₐ[p.ResidueField] p.ResidueField ⊗[R] S :=
  (Ideal.Fiber.equiv p S).algEquiv p.ResidueField

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- `p.Fiber S` is isomorphic to the tensor product `κ(p) ⊗[R] S`. -/
noncomputable def algEquivTensorRight : p.Fiber S ≃ₐ[S] p.ResidueField ⊗[R] S :=
  (Ideal.Fiber.equiv p S).algEquiv S

-- todo: cleanup
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
noncomputable def algEquivBaseChange
    (T : Type*) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T] :
    p.Fiber S ⊗[S] T ≃ₐ[p.ResidueField] p.Fiber T := by
  let e2 := (algEquivTensorRight p S)
  let e4 := Algebra.TensorProduct.commRight R S p.ResidueField
  let e5 := ((Algebra.TensorProduct.congr (e2.trans e4.symm) (AlgEquiv.refl : T ≃ₐ[S] T)).trans
    (Algebra.TensorProduct.comm _ _ _)).trans
    (Algebra.TensorProduct.cancelBaseChange R S S T p.ResidueField)
  refine AlgEquiv.trans ?_ (algEquivTensor p T).symm
  refine AlgEquiv.trans ?_ (Algebra.TensorProduct.commRight R p.ResidueField T).symm
  exact
  { __ := e5
    commutes' _ := by
      simp [e5, e4, e2]
      rw [← (cancelBaseChange R S S T p.ResidueField).eq_symm_apply]
      simp [algebraMap_eq_includeRight]
      congr 1 }

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- `p.Fiber S` is isomorphic to the quotient `Sₚ ⧸ pSₚ`. -/
noncomputable def algEquivQuotient :
    letI Rp := Localization p.primeCompl
    letI pRp := IsLocalRing.maximalIdeal Rp
    letI Sp := Localization (algebraMapSubmonoid S p.primeCompl)
    letI pSp := pRp.map (algebraMap Rp Sp)
    p.Fiber S ≃ₐ[S] Sp ⧸ pSp :=
  letI Rp := Localization p.primeCompl
  letI pRp := IsLocalRing.maximalIdeal Rp
  letI Sp := Localization (algebraMapSubmonoid S p.primeCompl)
  letI pSp := pRp.map (algebraMap Rp Sp)
  (algEquivTensorRight p S).trans <| (commRight R S p.ResidueField).symm.trans <|
    (tensorQuotientEquiv S Rp S pRp).trans <|
    { __ := quotientEquiv _ _ (Localization.tensor_localization_algEquiv p.primeCompl S) (by
        rw [← Ideal.map_coe includeRight, Ideal.map_map]
        congr
        ext
        simp [Localization.tensor_localization_algEquiv_apply_one_tmul p.primeCompl])
      commutes' x := by simp }

noncomputable instance : Algebra (Localization (algebraMapSubmonoid S p.primeCompl)) (p.Fiber S) :=
  ((algEquivQuotient p S).symm.toAlgHom.comp (Ideal.Quotient.mkₐ S _)).toAlgebra

theorem algebraMap_localization_surjective :
    Function.Surjective
      (algebraMap (Localization (algebraMapSubmonoid S p.primeCompl)) (p.Fiber S)) :=
  (algEquivQuotient p S).symm.surjective.comp (Ideal.Quotient.mkₐ_surjective S _)

theorem ker_algebraMap_localization :
    letI Rp := Localization p.primeCompl
    letI pRp := IsLocalRing.maximalIdeal Rp
    letI Sp := Localization (algebraMapSubmonoid S p.primeCompl)
    letI pSp := pRp.map (algebraMap Rp Sp)
    RingHom.ker (algebraMap Sp (p.Fiber S)) = pSp :=
  (RingHom.ker_comp_of_injective _ (algEquivQuotient p S).symm.injective).trans Ideal.mk_ker

/-- Variant of `ker_algebraMap_localization` going the other way around the commutative square. -/
theorem ker_algebraMap_localization' :
    letI Sp := Localization (algebraMapSubmonoid S p.primeCompl)
    RingHom.ker (algebraMap Sp (p.Fiber S)) = (p.map (algebraMap R S)).map (algebraMap S Sp) := by
  rw [ker_algebraMap_localization, ← Localization.AtPrime.map_eq_maximalIdeal, map_map,
    ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R S, ← map_map]

instance (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    (q.map (algebraMap S (p.Fiber S))).IsPrime := by
  rw [IsScalarTower.algebraMap_eq S (Localization (algebraMapSubmonoid S p.primeCompl)), ← map_map]
  have : ((map (algebraMap S (Localization (algebraMapSubmonoid S p.primeCompl))) q)).IsPrime :=
    IsLocalization.AtPrime.isPrime_map_of_liesOver S p _ q
  apply Ideal.map_isPrime_of_surjective (algebraMap_localization_surjective p S)
  rw [ker_algebraMap_localization']
  exact map_mono (map_le_iff_le_comap.mpr LiesOver.over.le)

instance (p : Ideal R) [p.IsPrime] (q : Ideal (p.Fiber S)) [q.IsPrime] : q.LiesOver p :=
  .trans _ (⊥ : Ideal p.ResidueField) _

lemma exists_smul_eq_algebraMap (x : p.Fiber S) :
    ∃ r ∉ p, ∃ s, r • x = algebraMap S (p.Fiber S) s := by
  obtain ⟨x, rfl⟩ := (algEquivQuotient p S).symm.surjective x
  obtain ⟨x, rfl⟩ := Quotient.mk_surjective x
  obtain ⟨s, ⟨-, r, hr, rfl⟩, rfl⟩ :=
    IsLocalization.exists_mk'_eq (algebraMapSubmonoid S p.primeCompl) x
  refine ⟨r, hr, s, ?_⟩
  rw [← AlgEquiv.toAlgHom_apply, ← AlgHom.map_smul_of_tower,
    AlgEquiv.toAlgHom_apply, AlgEquiv.symm_apply_eq, AlgEquiv.commutes]
  simpa using congrArg (Ideal.Quotient.mk _)
    (IsLocalization.smul_mk'_self (M := algebraMapSubmonoid S p.primeCompl)
      (S := Localization (algebraMapSubmonoid S p.primeCompl))
        (r := s) (m := ⟨algebraMap R S r, r, hr, rfl⟩))

@[deprecated (since := "2026-03-31")] alias exists_smul_eq_one_tmul := exists_smul_eq_algebraMap

end Ideal.Fiber

variable {S}

variable (R S) in
/-- The fiber `PrimeSpectrum S → PrimeSpectrum R` at a prime ideal
`p : PrimeSpectrum R` is in bijection with the prime spectrum of `κ(p) ⊗[R] S`. -/
@[simps]
noncomputable def PrimeSpectrum.preimageEquivFiber (p : PrimeSpectrum R) :
    comap (algebraMap R S) ⁻¹' {p} ≃ PrimeSpectrum (p.asIdeal.Fiber S) where
  toFun q := ⟨q.1.1.map (algebraMap S (p.1.Fiber S)),
    have : q.1.1.LiesOver p.1 := ⟨PrimeSpectrum.ext_iff.mp q.2.symm⟩
    inferInstance⟩
  invFun q := ⟨⟨q.1.under S, q.2.under S⟩, PrimeSpectrum.ext Ideal.LiesOver.over.symm⟩
  left_inv q := by
    let m := algebraMapSubmonoid S p.1.primeCompl
    simp only [Subtype.ext_iff, PrimeSpectrum.ext_iff, Ideal.under_def]
    rw [IsScalarTower.algebraMap_eq S (Localization m), ← Ideal.map_map, ← Ideal.comap_comap,
      Ideal.comap_map_of_surjective _ (Ideal.Fiber.algebraMap_localization_surjective p.1 S),
      ← RingHom.ker_eq_comap_bot, sup_of_le_left,
      IsLocalization.comap_map_of_isPrime_disjoint m _ q.1.2]
    · exact Set.disjoint_image_left.mpr (Set.disjoint_compl_left_iff_subset.mpr q.2.le)
    · rw [Ideal.Fiber.ker_algebraMap_localization']
      exact Ideal.map_mono (Ideal.map_le_iff_le_comap.mpr q.2.ge)
  right_inv q := by
    simp only [PrimeSpectrum.ext_iff, Ideal.under_def]
    rw [IsScalarTower.algebraMap_eq S (Localization (algebraMapSubmonoid S p.1.primeCompl)),
      ← Ideal.map_map, ← Ideal.comap_comap,
      IsLocalization.map_comap (Algebra.algebraMapSubmonoid S p.1.primeCompl),
      Ideal.map_comap_of_surjective _ (Ideal.Fiber.algebraMap_localization_surjective p.1 S)]

variable (R S) in
/-- The `OrderIso` between the fiber of `PrimeSpectrum S → PrimeSpectrum R` at a prime
ideal `p : PrimeSpectrum R` and the prime spectrum of `κ(p) ⊗[R] S`. -/
@[simps!]
noncomputable def PrimeSpectrum.preimageOrderIsoFiber (p : PrimeSpectrum R) :
    comap (algebraMap R S) ⁻¹' {p} ≃o PrimeSpectrum (p.asIdeal.Fiber S) where
  toEquiv := preimageEquivFiber R S p
  map_rel_iff' {q₁ q₂} := by
    constructor
    · obtain ⟨q₁, rfl⟩ := (preimageEquivFiber R S p).symm.surjective q₁
      obtain ⟨q₂, rfl⟩ := (preimageEquivFiber R S p).symm.surjective q₂
      simpa using Ideal.comap_mono
    · exact Ideal.map_mono

@[deprecated (since := "2025-12-07")]
alias PrimeSpectrum.preimageOrderIsoTensorResidueField := PrimeSpectrum.preimageOrderIsoFiber

variable (R S) in
/-- The `OrderIso` between the set of primes lying over a prime ideal `p : Ideal R`,
and the prime spectrum of `κ(p) ⊗[R] S`. -/
@[simps!]
noncomputable def PrimeSpectrum.primesOverOrderIsoFiber (R S : Type*) [CommRing R]
    [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime] :
    p.primesOver S ≃o PrimeSpectrum (p.Fiber S) :=
  .trans ⟨⟨fun q ↦ ⟨⟨q, q.2.1⟩, PrimeSpectrum.ext q.2.2.1.symm⟩,
    fun q ↦ ⟨q.1.asIdeal, ⟨q.1.2, ⟨congr($(q.2).1).symm⟩⟩⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩, .rfl⟩
    (PrimeSpectrum.preimageOrderIsoFiber R S ⟨p, ‹_›⟩)

/-- The `Homeomorph` between the fiber of `PrimeSpectrum S → PrimeSpectrum R`
at a prime ideal `p : PrimeSpectrum R` and the prime spectrum of `κ(p) ⊗[R] S`. -/
@[simps!]
noncomputable def PrimeSpectrum.preimageHomeomorphFiber (R S : Type*) [CommRing R]
    [CommRing S] [Algebra R S] (p : PrimeSpectrum R) :
    comap (algebraMap R S) ⁻¹' {p} ≃ₜ PrimeSpectrum (p.asIdeal.Fiber S) := by
  letI H : Topology.IsEmbedding (preimageOrderIsoFiber R S p).symm := by
    refine (Topology.IsEmbedding.of_comp_iff .subtypeVal).mp ?_
    simpa only [← IsScalarTower.algebraMap_eq, ← PrimeSpectrum.comap_comp] using
      (localization_comap_isEmbedding _ (algebraMapSubmonoid S p.1.primeCompl)).comp
        (isEmbedding_comap_of_surjective _ _ (Ideal.Fiber.algebraMap_localization_surjective p.1 S))
  exact
  { __ := preimageOrderIsoFiber R S p
    continuous_toFun := by
      convert (H.toHomeomorphOfSurjective
        (preimageOrderIsoFiber R S p).symm.surjective).symm.continuous
      ext1 x
      obtain ⟨x, rfl⟩ := (H.toHomeomorphOfSurjective
        (preimageOrderIsoFiber R S p).symm.surjective).surjective x
      simp only [Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, Homeomorph.symm_apply_apply]
      simp
    continuous_invFun := H.continuous }
