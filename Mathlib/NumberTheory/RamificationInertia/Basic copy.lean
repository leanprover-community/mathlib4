/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.GroupWithZero.Torsion
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Finiteness.Quotient
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.SurjectiveOnStalks
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.RingTheory.LocalProperties.Projective
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Ramification index

-/

@[expose] public section

section

-- PRed
instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
    (q : Ideal (p.Fiber S)) [q.IsPrime] : Localization.AtPrime.IsLiesOverAlgebra p q where
  algebraMap_eq := (Localization.localRingHom_unique p q _ Ideal.LiesOver.over fun _ ↦ rfl).symm

-- PRed
open Module TensorProduct in
lemma _root_.Ideal.finrank_fiber_eq_finrank {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Flat R M] [Module.Finite R M] [IsDomain R] (p : Ideal R) [p.IsPrime] :
    finrank p.ResidueField (p.Fiber M) = finrank R M := by
  let K := FractionRing R
  let Rp := Localization.AtPrime p
  let Mp := LocalizedModule.AtPrime p M
  rw [p.finrank_fiber_eq_rankAtStalk, rankAtStalk, ← (isBaseChange R M K).finrank_eq,
    ← (AlgebraTensorModule.cancelBaseChange R Rp K K M).finrank_eq,
    ← (((LocalizedModule.equivTensorProduct p.primeCompl M).baseChange Rp K Mp _)).finrank_eq]
  symm
  exact (isBaseChange Rp Mp K).finrank_eq

open Ideal

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]

-- PRed
instance [Algebra.QuasiFinite R S] (q : Ideal (p.Fiber S)) [q.IsPrime] :
    Module.Finite p.ResidueField (Localization.AtPrime q) :=
  Module.Finite.of_quasiFinite

-- PRed
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
open Algebra Algebra.TensorProduct in
/-- `p.Fiber S` is isomorphic to the quotient `Sₚ ⧸ pSₚ`. -/
noncomputable def Fiber.algEquivQuotient :
    letI Rp := Localization p.primeCompl
    letI pRp := IsLocalRing.maximalIdeal Rp
    letI Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
    letI pSp := pRp.map (algebraMap Rp Sp)
    p.Fiber S ≃ₐ[S] Sp ⧸ pSp :=
  letI Rp := Localization p.primeCompl
  letI pRp := IsLocalRing.maximalIdeal Rp
  letI Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  letI pSp := pRp.map (algebraMap Rp Sp)
  (commRight R S p.ResidueField).symm.trans <| (tensorQuotientEquiv S Rp S pRp).trans <|
    { __ := quotientEquiv _ _ (Localization.tensorLeftAlgEquiv p.primeCompl S) (by
        rw [← Ideal.map_coe includeRight, Ideal.map_map]
        congr
        ext
        simp [Localization.tensorLeftAlgEquiv_apply_one_tmul p.primeCompl])
      commutes' := by simp }

open TensorProduct

/-- The localization of the fiber `p.Fiber S` is isomorphic to a quotient of a localization. -/
noncomputable def foo8 (q : Ideal (p.Fiber S)) [q.IsPrime]
    [h1 : Algebra (Localization.AtPrime p)
      (Localization.AtPrime (q.comap Algebra.TensorProduct.includeRight))]
    [h2 : Localization.AtPrime.IsLiesOverAlgebra p (q.comap Algebra.TensorProduct.includeRight)] :
    letI r := q.comap Algebra.TensorProduct.includeRight
    letI Sr := Localization.AtPrime r
    Localization.AtPrime q ≃ₐ[Localization.AtPrime p] Sr ⧸ p.map (algebraMap R Sr) := by
  letI : Algebra S (p.Fiber S) := Algebra.TensorProduct.rightAlgebra
  letI Rp := Localization.AtPrime p
  letI Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  letI pS := p.map (algebraMap R S)
  letI pSp := pS.map (algebraMap S Sp)
  letI r := q.under S
  letI Sr := Localization.AtPrime r
  let : Algebra Rp Sr := h1
  have : Localization.AtPrime.IsLiesOverAlgebra p r := h2
  letI e₁ : (Sp ⧸ pSp) ≃ₐ[S] p.Fiber S :=
    .symm <| (Fiber.algEquivQuotient p).trans <| quotientEquivAlgOfEq S <| by
      simp [Sp, pS, pSp, map_map, ← IsScalarTower.algebraMap_eq,
        ← Localization.AtPrime.map_eq_maximalIdeal]
  letI q' : Ideal (Sp ⧸ pSp) := q.comap e₁
  haveI : Algebra.algebraMapSubmonoid (S ⧸ pS) r.primeCompl = (under (S ⧸ pS) q').primeCompl :=
    algebraMapSubmonoid_primeCompl_of_liesOver_surjective
      (q'.under (S ⧸ pS)) r Ideal.Quotient.mk_surjective
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (S ⧸ pS) r.primeCompl)
      (Localization.AtPrime q') := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid (S ⧸ pS) (Algebra.algebraMapSubmonoid S p.primeCompl))
          (Localization.AtPrime q') q'
  haveI := IsScalarTower.to₁₃₄ R S (S ⧸ pS) (Localization.AtPrime q')
  haveI := IsScalarTower.to₁₃₄ R S (S ⧸ pS) (Sr ⧸ map (algebraMap S Sr) pS)
  haveI : IsScalarTower R Rp (Sr ⧸ map (algebraMap S Sr) pS) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rw [IsScalarTower.algebraMap_apply Rp Sr,
      ← IsScalarTower.algebraMap_apply R Rp,
      ← IsScalarTower.algebraMap_apply]
  letI e₂ := (IsLocalization.algEquiv (Algebra.algebraMapSubmonoid (S ⧸ pS) r.primeCompl)
    (Localization.AtPrime q') ((Sr ⧸ pS.map (algebraMap S Sr)))).restrictScalars R
  letI e₃ : Localization.AtPrime q' ≃ₐ[Rp] Sr ⧸ pS.map (algebraMap S Sr) :=
  { __ := e₂
    commutes' := by
      let f := e₂.toAlgHom.comp (IsScalarTower.toAlgHom R Rp (Localization.AtPrime q'))
      let g := IsScalarTower.toAlgHom R Rp (Sr ⧸ pS.map (algebraMap S Sr))
      have : f.toRingHom.comp (algebraMap R Rp) = g.toRingHom.comp (algebraMap R Rp) := by simp
      suffices f = g by rwa [DFunLike.ext_iff] at this
      apply Localization.algHom_ext
      rwa [DFunLike.ext_iff] at this ⊢ }
  letI e₄ : Localization.AtPrime q' ≃ₐ[Rp] Localization.AtPrime q :=
    { __ := Localization.localAlgEquiv q' q e₁ rfl
      commutes' := by
        let f := ((Localization.localAlgEquiv q' q e₁ rfl).toAlgHom.restrictScalars R).comp
          (IsScalarTower.toAlgHom R Rp (Localization.AtPrime q'))
        let g := IsScalarTower.toAlgHom R Rp (Localization.AtPrime q)
        have : f.toRingHom.comp (algebraMap R Rp) = g.toRingHom.comp (algebraMap R Rp) := by simp
        suffices f = g by rwa [DFunLike.ext_iff] at this
        apply Localization.algHom_ext
        rwa [DFunLike.ext_iff] at this ⊢ }
  exact e₄.symm.trans <| e₃.trans <| quotientEquivAlgOfEq Rp (map_map _ _)

theorem foo3 (q : Ideal (p.Fiber S)) [q.IsPrime]
    [Algebra (Localization.AtPrime p)
      (Localization.AtPrime (q.comap Algebra.TensorProduct.includeRight))]
    [Localization.AtPrime.IsLiesOverAlgebra p (q.comap Algebra.TensorProduct.includeRight)] :
    letI r := q.comap Algebra.TensorProduct.includeRight
    letI Sr := Localization.AtPrime r
    Module.length (Localization.AtPrime p) (Localization.AtPrime q) =
      Module.length (Localization.AtPrime p) (Sr ⧸ p.map (algebraMap R Sr)) := by
  apply LinearEquiv.length_eq
  exact (foo8 p q).toLinearEquiv

noncomputable instance [Algebra.QuasiFinite R S] : Fintype (p.primesOver S) :=
  (Algebra.QuasiFinite.finite_primesOver p).fintype

theorem sum_ramification_inertia
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.QuasiFinite R S] [Module.Flat R S] (p : Ideal R) [p.IsPrime] :
    Module.finrank p.ResidueField (p.Fiber S) =
      ∑ q : p.primesOver S, q.1.ramificationIdx' R * q.1.inertiaDeg' R := by
  rw [IsArtinianRing.finrank_eq_sum_primeSpectrum,
    ← (PrimeSpectrum.primesOverOrderIsoFiber R S p).symm.sum_comp]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  let r := q.1.comap Algebra.TensorProduct.includeRight
  let Sr := Localization.AtPrime r
  let A := Sr ⧸ p.map (algebraMap R Sr)
  let := Localization.AtPrime.algebraOfLiesOver p r
  transitivity (Module.length (Localization.AtPrime p) A).toNat
  · rw [← foo3,
      Module.length_eq_of_surjective (IsLocalRing.residue_surjective (R := Localization.AtPrime p)),
      Module.length_eq_finrank, ENat.toNat_coe]
  · rw [IsLocalRing.length_restrictScalars (Localization.AtPrime p) (Localization.AtPrime r) A,
      ENat.toNat_mul, Module.length_eq_finrank, ramificationIdx'_eq p, ← inertiaDeg'_eq p r]
    rfl

theorem sum_ramification_inertia'
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain R] [Module.Finite R S] [Module.Flat R S]
    (p : Ideal R) [p.IsPrime] :
    Module.finrank R S =
      ∑ q : p.primesOver S, q.1.ramificationIdx' R * q.1.inertiaDeg' R := by
  rw [← sum_ramification_inertia, finrank_fiber_eq_finrank]

theorem sum_ramification_inertia''
    {R S G : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S]
    [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
    [Module.Flat R S] [Module.Finite R S] (p : Ideal R) [p.IsPrime] :
    Nat.card G =
      ∑ q : p.primesOver S, q.1.ramificationIdx' R * q.1.inertiaDeg' R := by
  let := FractionRing.mulSemiringAction_of_isGaloisGroup G R S
  let := FractionRing.liftAlgebra R (FractionRing S)
  rw [← sum_ramification_inertia', (IsGaloisGroup.toFractionRing G R S).card_eq_finrank,
    Algebra.IsAlgebraic.finrank_of_isFractionRing R (FractionRing R) S (FractionRing S)]

end Ideal
