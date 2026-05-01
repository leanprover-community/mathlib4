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
public import Mathlib.NumberTheory.RamificationInertia.Inertia
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
open TensorProduct in
def TensorProduct.includeLeft (R S K : Type*) [CommSemiring R] [AddCommMonoid S] [Module R S]
    [AddCommMonoid K] [One K] [Module R K] : S →ₗ[R] S ⊗[R] K where
  toFun x := tmul _ x 1
  map_add' x y := add_tmul x y 1
  map_smul' x y := (smul_tmul' x y 1).symm

-- PRed
open TensorProduct in
def TensorProduct.includeRight (R S K : Type*) [CommSemiring R] [AddCommMonoid S] [Module R S]
    [AddCommMonoid K] [One K] [Module R K] : S →ₗ[R] K ⊗[R] S where
  toFun := tmul _ 1
  map_add' := tmul_add 1
  map_smul' x := tmul_smul x 1

-- PRed
open TensorProduct in
theorem foo (R S K : Type*) [CommSemiring R] [AddCommMonoid S] [Module R S]
    [CommSemiring K] [Algebra R K] :
    IsBaseChange K (TensorProduct.includeRight R S K) := by
  have := IsBaseChange.of_equiv (f := TensorProduct.includeRight R S K)
    (LinearEquiv.refl (R := K) (M := K ⊗[R] S))
  apply this
  intro x
  rfl

open TensorProduct in
theorem foo17 (R S K : Type*) [CommRing R] [AddCommGroup S] [Module R S]
    [CommRing K] [NoZeroDivisors K] [Algebra R K] [FaithfulSMul R K] :
    Module.finrank R S = Module.finrank K (K ⊗[R] S) :=
  (IsBaseChange.finrank_eq (foo R S K)).symm

open TensorProduct in
/-- _ -/
noncomputable def foo18 (R S K : Type*) [CommRing R] [AddCommGroup S] [Module R S]
    [CommRing K] [Algebra R K] (p : Ideal R) [p.IsPrime]
    [Algebra (Localization.AtPrime p) K] [IsScalarTower R (Localization.AtPrime p) K] :
    letI Rp := Localization.AtPrime p
    letI Sp := LocalizedModule.AtPrime p S
    (K ⊗[Rp] Sp) ≃ₗ[K] K ⊗[R] S :=
  letI Rp := Localization.AtPrime p
  letI Sp := LocalizedModule.AtPrime p S
  ((LinearEquiv.baseChange Rp K Sp (Rp ⊗[R] S)
    (LocalizedModule.equivTensorProduct p.primeCompl S)).trans
      (AlgebraTensorModule.cancelBaseChange R Rp K K S))

open TensorProduct in
theorem finrank_fiber_eq_finrank
    {R S : Type*} [CommRing R] [IsDomain R] [AddCommGroup S] [Module R S]
    [Module.Finite R S] [Module.Flat R S] (p : Ideal R) [p.IsPrime] :
    Module.finrank p.ResidueField (p.Fiber S) = Module.finrank R S := by
  rw [Ideal.finrank_fiber_eq_rankAtStalk]
  let Rp := Localization.AtPrime p
  let Sp := LocalizedModule.AtPrime p S
  have : Module.Free Rp Sp := Module.free_of_flat_of_isLocalRing
  transitivity Module.finrank Rp Sp
  · simp only [Module.rankAtStalk_eq]
    transitivity Module.finrank p.ResidueField (p.ResidueField ⊗[Rp] Sp)
    · exact (foo18 R S p.ResidueField p).finrank_eq.symm
    · exact Module.finrank_baseChange
  · let K := FractionRing R
    have : FaithfulSMul Rp K := IsFractionRing.instFaithfulSMul Rp K
    rw [foo17 R S K, foo17 Rp Sp K]
    exact (foo18 R S K p).finrank_eq

open Ideal

namespace Ideal

section ramification_inertia

variable {S : Type*} [CommRing S] (q : Ideal S) (R : Type*) [CommRing R] [Algebra R S]

section ramificationIdx

open Classical in
/-- An alternate definition of ramification index. -/
noncomputable def ramificationIdx' : ℕ :=
  if _ : q.IsPrime then
    letI Sq := Localization.AtPrime q
    (Module.length Sq (Sq ⧸ (q.under R).map (algebraMap R Sq))).toNat
  else 0

theorem ramificationIdx'_def [q.IsPrime] :
    letI Sq := Localization.AtPrime q
    q.ramificationIdx' R = (Module.length Sq (Sq ⧸ (q.under R).map (algebraMap R Sq))).toNat :=
  dif_pos _

theorem ramificationIdx'_of_not_isPrime (hq : ¬ q.IsPrime) : q.ramificationIdx' R = 0 :=
  dif_neg hq

theorem ramificationIdx'_eq {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) (q : Ideal S) [h : q.LiesOver p] [q.IsPrime] :
    letI Sq := Localization.AtPrime q
    q.ramificationIdx' R = (Module.length Sq (Sq ⧸ p.map (algebraMap R Sq))).toNat := by
  rw [ramificationIdx'_def, h.over]

/-- See `ramificationIdx'_tower'` for a version that does not assume primality. -/
theorem ramificationIdx'_tower
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (q : Ideal S) [q.IsPrime] (r : Ideal T) [r.IsPrime] [r.LiesOver q]
    [Algebra (Localization.AtPrime q) (Localization.AtPrime r)]
    [Localization.AtPrime.IsLiesOverAlgebra q r]
    [Module.Flat (Localization.AtPrime q) (Localization.AtPrime r)] :
    r.ramificationIdx' R = q.ramificationIdx' R * r.ramificationIdx' S := by
  have : q.LiesOver (r.under R) := LiesOver.tower_bot r q (r.under R)
  rw [ramificationIdx'_def, ramificationIdx'_eq (r.under R), ramificationIdx'_eq q,
    ← ENat.toNat_mul]
  congr
  set Sq := Localization.AtPrime q
  set Tr := Localization.AtPrime r
  have := IsLocalRing.length_baseChange
    (A := Sq) (B := Tr) (M := Sq ⧸ (r.under R).map (algebraMap R Sq))
  rw [← Localization.AtPrime.map_eq_maximalIdeal, map_map, ← IsScalarTower.algebraMap_eq] at this
  convert this
  let f := (Ideal.quotientEquivAlgOfEq Tr (by rw [map_map, ← IsScalarTower.algebraMap_eq])).trans
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot Tr ((r.under R).map (algebraMap R Sq)))
  exact f.toLinearEquiv.length_eq

theorem ramificationIdx'_tower'
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (q : Ideal S) (r : Ideal T) [h : r.LiesOver q] [Module.Flat S T] :
    r.ramificationIdx' R = q.ramificationIdx' R * r.ramificationIdx' S := by
  by_cases hr : r.IsPrime
  · have : q.IsPrime := by rw [h.over]; exact IsPrime.under S r -- should be lemma
    let := Localization.AtPrime.algebraOfLiesOver q r
    apply ramificationIdx'_tower
  · rw [ramificationIdx'_of_not_isPrime r R hr, ramificationIdx'_of_not_isPrime r S hr, mul_zero]

end ramificationIdx

section inertiaDeg

open Classical in
/-- An alternate definition of inertia degree. -/
noncomputable def inertiaDeg' : ℕ :=
  if _ : q.IsPrime then
    letI := Localization.AtPrime.algebraOfLiesOver (q.under R) q
    Module.finrank (q.under R).ResidueField q.ResidueField else 0

theorem inertiaDeg'_def [q.IsPrime]
    [Algebra (Localization.AtPrime (q.under R)) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra (q.under R) q] :
    q.inertiaDeg' R = Module.finrank (q.under R).ResidueField q.ResidueField := by
  convert dif_pos _
  apply Algebra.algebra_ext
  rw [← DFunLike.ext_iff]
  exact Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq

theorem inertiaDeg'_of_not_isPrime (hq : ¬ q.IsPrime) : q.inertiaDeg' R = 0 :=
  dif_neg hq

theorem inertiaDeg'_eq {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) (q : Ideal S) [h : q.LiesOver p] [q.IsPrime] [p.IsPrime]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q] :
    q.inertiaDeg' R = Module.finrank p.ResidueField q.ResidueField := by
  let : Algebra (Localization.AtPrime (q.under R)) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver (q.under R) q
  rw [inertiaDeg'_def]
  have := Ideal.over_def q p
  subst this
  convert rfl
  apply Algebra.algebra_ext
  rw [← DFunLike.ext_iff]
  exact Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq

theorem inertiaDeg'_tower'
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (q : Ideal S) (r : Ideal T) [h : r.LiesOver q] [Module.Flat S T] :
    r.inertiaDeg' R = q.inertiaDeg' R * r.inertiaDeg' S := by
  by_cases hr : r.IsPrime
  · have : q.IsPrime := by rw [h.over]; exact IsPrime.under S r -- should be lemma
    have : q.LiesOver (r.under R) := LiesOver.tower_bot r q (r.under R)
    let := Localization.AtPrime.algebraOfLiesOver (r.under R) r
    let := Localization.AtPrime.algebraOfLiesOver (r.under R) q
    let := Localization.AtPrime.algebraOfLiesOver q r
    rw [inertiaDeg'_eq (r.under R), inertiaDeg'_eq (r.under R), inertiaDeg'_eq q, eq_comm]
    apply Module.finrank_mul_finrank
  · rw [inertiaDeg'_of_not_isPrime r R hr, inertiaDeg'_of_not_isPrime r S hr, mul_zero]

end inertiaDeg

end ramification_inertia

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

instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
    (q : Ideal (p.Fiber S)) [q.IsPrime] : Localization.AtPrime.IsLiesOverAlgebra p q where
  algebraMap_eq := (Localization.localRingHom_unique p q _ Ideal.LiesOver.over fun _ ↦ rfl).symm

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
    algebraMapSubmonoid_primeCompl_of_liesOver_surjective (q'.under (S ⧸ pS)) r Ideal.Quotient.mk_surjective
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
    [Localization.AtPrime.IsLiesOverAlgebra p (q.comap Algebra.TensorProduct.includeRight)]:
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

open NumberField in
example {K L : Type*} [Field K] [Field L] [Algebra K L] [NumberField K] [NumberField L] :
    Module.Flat (𝓞 K) (𝓞 L) :=
  inferInstance

end Ideal
