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

open Ideal

-- PRed
theorem le_of_liesOver_quotient {R : Type*} [CommRing R]
    (I : Ideal R) (p : Ideal R) (q : Ideal (R ⧸ I)) [q.LiesOver p] : I ≤ p := by
  simp [over_def q p, ← map_le_iff_le_comap]

-- PRed
theorem algebraMapSubmonoid_primeCompl_of_liesOver_quotient
    {R : Type*} [CommRing R] (I : Ideal R) (p : Ideal R) (q : Ideal (R ⧸ I))
    [p.IsPrime] [q.IsPrime] [q.LiesOver p] :
    Algebra.algebraMapSubmonoid (R ⧸ I) p.primeCompl = q.primeCompl := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [mem_primeCompl_iff, ← Quotient.algebraMap_eq, ← mem_comap, ← under_def, ← over_def q p]
  refine ⟨fun ⟨y, hy, hx⟩ ↦ ?_, fun hx ↦ ⟨x, hx, rfl⟩⟩
  rw [← sub_eq_zero, ← map_sub, Quotient.algebraMap_eq, Quotient.eq_zero_iff_mem] at hx
  contrapose! hy
  simpa [p.sub_mem_iff_left hy] using le_of_liesOver_quotient I p q hx

-- PRed
theorem IsArtinianRing.finrank_eq_sum_primeSpectrum
    {R S : Type*} [Field R] [CommRing S] [IsArtinianRing S] [Algebra R S] [Module.Finite R S] :
    Module.finrank R S = ∑ p : PrimeSpectrum S, Module.finrank R (Localization.AtPrime p.1) :=
  have (p : Ideal S) [p.IsPrime] : Module.Finite R (Localization.AtPrime p) :=
    Module.Finite.of_surjective (Algebra.algHom R S (Localization.AtPrime p)).toLinearMap
      (IsArtinianRing.localization_surjective p.primeCompl (Localization.AtPrime p))
  ((PrimeSpectrum.toPiLocalizationEquiv S).restrictScalars R).toLinearEquiv.finrank_eq.trans
    (Module.finrank_pi_fintype R)

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
    apply ramificationIdx'_tower
  · rw [ramificationIdx'_of_not_isPrime r R hr, ramificationIdx'_of_not_isPrime r S hr, mul_zero]

end ramificationIdx

section inertiaDeg

open Classical in
/-- An alternate definition of inertia degree. -/
noncomputable def inertiaDeg' : ℕ :=
  if _ : q.IsPrime then Module.finrank (q.under R).ResidueField q.ResidueField else 0

theorem inertiaDeg'_def [q.IsPrime] :
    q.inertiaDeg' R = Module.finrank (q.under R).ResidueField q.ResidueField :=
  dif_pos _

theorem inertiaDeg'_of_not_isPrime (hq : ¬ q.IsPrime) : q.inertiaDeg' R = 0 :=
  dif_neg hq

theorem inertiaDeg'_eq {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) (q : Ideal S) [h : q.LiesOver p] [q.IsPrime] [p.IsPrime] :
    q.inertiaDeg' R = Module.finrank p.ResidueField q.ResidueField := by
  rw [inertiaDeg'_def]
  convert rfl <;> exact LiesOver.over

theorem inertiaDeg'_tower'
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (q : Ideal S) (r : Ideal T) [h : r.LiesOver q] [Module.Flat S T] :
    r.inertiaDeg' R = q.inertiaDeg' R * r.inertiaDeg' S := by
  by_cases hr : r.IsPrime
  · have : q.IsPrime := by rw [h.over]; exact IsPrime.under S r -- should be lemma
    have : q.LiesOver (r.under R) := LiesOver.tower_bot r q (r.under R)
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

/-- The localization of the fiber `p.Fiber S` is isomorphic to a quotient of a localization. -/
noncomputable def foo8 (q : Ideal (p.Fiber S)) [q.IsPrime] :
    letI r := q.comap Algebra.TensorProduct.includeRight
    letI Sr := Localization.AtPrime r
    Localization.AtPrime q ≃ₐ[Localization.AtPrime p] Sr ⧸ p.map (algebraMap R Sr) :=
  letI : Algebra S (p.Fiber S) := Algebra.TensorProduct.rightAlgebra
  letI Rp := Localization p.primeCompl
  letI Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  letI pS := p.map (algebraMap R S)
  letI pSp := pS.map (algebraMap S Sp)
  letI r := q.under S
  letI Sr := Localization.AtPrime r
  letI e₁ : (Sp ⧸ pSp) ≃ₐ[S] p.Fiber S :=
    .symm <| (Fiber.algEquivQuotient p).trans <| quotientEquivAlgOfEq S <| by
      simp [Sp, pS, pSp, map_map, ← IsScalarTower.algebraMap_eq,
        ← Localization.AtPrime.map_eq_maximalIdeal]
  letI q' : Ideal (Sp ⧸ pSp) := q.comap e₁
  haveI := algebraMapSubmonoid_primeCompl_of_liesOver_quotient pS r (q'.under (S ⧸ pS))
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (S ⧸ pS) r.primeCompl)
      (Localization.AtPrime q') := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid (S ⧸ pS) (Algebra.algebraMapSubmonoid S p.primeCompl))
          (Localization.AtPrime q') q'
  haveI := IsScalarTower.to₁₃₄ R S (S ⧸ pS) (Localization.AtPrime q')
  haveI := IsScalarTower.to₁₃₄ R S (S ⧸ pS) (Sr ⧸ map (algebraMap S Sr) pS)
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
  let e₄ : Localization.AtPrime q' ≃ₐ[Rp] Localization.AtPrime q :=
    { __ := Localization.localAlgEquiv q' q e₁ rfl
      commutes' := by
        let f := ((Localization.localAlgEquiv q' q e₁ rfl).toAlgHom.restrictScalars R).comp
          (IsScalarTower.toAlgHom R Rp (Localization.AtPrime q'))
        let g := IsScalarTower.toAlgHom R Rp (Localization.AtPrime q)
        have : f.toRingHom.comp (algebraMap R Rp) = g.toRingHom.comp (algebraMap R Rp) := by simp
        suffices f = g by rwa [DFunLike.ext_iff] at this
        apply Localization.algHom_ext
        rwa [DFunLike.ext_iff] at this ⊢ }
  e₄.symm.trans <| e₃.trans <| quotientEquivAlgOfEq Rp (map_map _ _)

/-- If `q` is a prime ideal of `p.Fiber S`, then `q` lies over `p`, so the localization
`(p.Fiber S)_q` is an algebra the localization `R_p`. But `p.Fiber S = Rp ⊗[R] S` is itself an
algebra over `Rp`, and this gives another instance of `(p.Fiber S)_q` as an `Rp`-algebra.

This was discussed on Zulip here:
https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/instance.20diamond.20with.20.60Ideal.2EFiber.60. -/
theorem Fiber.localization_diamond
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
    (q : Ideal (p.Fiber S)) [q.IsPrime] :
    Localization.AtPrime.instAlgebraOfLiesOver p q = OreLocalization.instAlgebra := by
  apply Algebra.algebra_ext
  rw [← DFunLike.ext_iff]
  exact Localization.localRingHom_unique p q _ Ideal.LiesOver.over fun x ↦ rfl

theorem foo3 (q : Ideal (p.Fiber S)) [q.IsPrime] :
    letI r := q.comap Algebra.TensorProduct.includeRight
    letI Sr := Localization.AtPrime r
    Module.length (Localization.AtPrime p) (Localization.AtPrime q) =
      Module.length (Localization.AtPrime p) (Sr ⧸ p.map (algebraMap R Sr)) := by
  apply LinearEquiv.length_eq
  convert (foo8 p q).toLinearEquiv
  rw [Fiber.localization_diamond]
  rfl

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
  transitivity (Module.length (Localization.AtPrime p) A).toNat
  · rw [← foo3,
      Module.length_eq_of_surjective (IsLocalRing.residue_surjective (R := Localization.AtPrime p)),
      Module.length_eq_finrank, ENat.toNat_coe]
  · rw [IsLocalRing.length_restrictScalars (Localization.AtPrime p) (Localization.AtPrime r) A,
      ENat.toNat_mul, Module.length_eq_finrank, ramificationIdx'_eq p, inertiaDeg'_eq p]
    rfl

-- PRed
lemma finrank_fiber_eq_rankAtStalk (R S : Type*) [CommRing R] [AddCommGroup S] [Module R S]
    [Module.Finite R S] [Module.Flat R S] (p : Ideal R) [hp : p.IsPrime] :
    Module.finrank p.ResidueField (p.ResidueField ⊗[R] S) = Module.rankAtStalk S ⟨p, hp⟩ :=
  (Module.rankAtStalk_eq ⟨p, hp⟩).symm

theorem foo17 (R S K : Type*) [CommRing R] [AddCommGroup S] [Module R S]
    [CommRing K] [NoZeroDivisors K] [Algebra R K] [FaithfulSMul R K] :
    Module.finrank R S = Module.finrank K (K ⊗[R] S) := by
  symm
  let h : S →ₗ[R] K ⊗[R] S :=
  { toFun := tmul _ 1
    map_add' := tmul_add 1
    map_smul' x := tmul_smul x 1 }
  apply IsBaseChange.finrank_eq (g := h)
  have := IsBaseChange.of_equiv (f := h) (LinearEquiv.refl (R := K) (M := K ⊗[R] S))
  apply this
  intro x
  rfl

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

theorem finrank_fiber_eq_finrank
    {R S : Type*} [CommRing R] [IsDomain R] [AddCommGroup S] [Module R S]
    [Module.Finite R S] [Module.Flat R S] (p : Ideal R) [p.IsPrime] :
    Module.finrank p.ResidueField (p.ResidueField ⊗[R] S) = Module.finrank R S := by
  rw [finrank_fiber_eq_rankAtStalk]
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
