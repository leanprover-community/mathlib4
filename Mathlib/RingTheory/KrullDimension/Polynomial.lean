/-
Copyright (c) 2025 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang
-/
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-!
# Krull dimension of polynomial ring

This file proves properties of the krull dimension of the polynomial ring over a commutative ring

## Main results

* `Polynomial.ringKrullDim_le`: the krull dimension of the polynomial ring over a commutative ring
  `R` is less than `2 * (ringKrullDim R) + 1`.
-/

variable {R : Type*} [CommRing R]

namespace Polynomial

theorem ringKrullDim_le : ringKrullDim (Polynomial R) ≤ 2 * (ringKrullDim R) + 1 := by
  rw [ringKrullDim, ringKrullDim]
  apply Order.krullDim_le_of_krullDim_preimage_le' C.specComap ?_ (fun p ↦ ?_)
  · exact fun {a b} h ↦ Ideal.comap_mono h
  · rw [show C = (algebraMap R (Polynomial R)) from rfl, Order.krullDim_eq_of_orderIso
      (PrimeSpectrum.preimageOrderIsoTensorResidueField R (Polynomial R) p), ← ringKrullDim,
      ← ringKrullDim_eq_of_ringEquiv (polyEquivTensor R (p.asIdeal.ResidueField)).toRingEquiv,
      ← Ring.krullDimLE_iff]
    infer_instance

variable [IsNoetherianRing R]
open Ideal IsLocalization

/--
Let `p` be a maximal ideal of `A`. If `P` is a maximal ideal of `A[X]` lying above `p`,
then `ht(P) = ht(p) + 1`.
See `Ideal.height_polynomial` for the more general version that does not assume `p` is maximal.
-/
lemma height_eq_height_succ_of_isMaximal (p : Ideal R) [p.IsMaximal] (P : Ideal R[X])
    [P.IsMaximal] [P.LiesOver p] : P.height = p.height + 1 := by
  let _ : Field (R ⧸ p) := Quotient.field p
  suffices h : (P.map (Ideal.Quotient.mk (Ideal.map (algebraMap R R[X]) p))).height = 1 by
    rw [height_eq_height_add_of_liesOver_of_hasGoingDown p, h]
  let e : (R[X] ⧸ (p.map C)) ≃+* (R ⧸ p)[X] := (polynomialQuotientEquivQuotientPolynomial p).symm
  let P' : Ideal (R ⧸ p)[X] := Ideal.map e <| P.map (Ideal.Quotient.mk <| p.map (algebraMap R R[X]))
  have : (P.map (Ideal.Quotient.mk <| p.map (algebraMap R R[X]))).IsMaximal := by
    refine .map_of_surjective_of_ker_le Quotient.mk_surjective ?_
    rw [mk_ker, LiesOver.over (P := P) (p := p)]
    exact map_comap_le
  have : P'.IsMaximal := map_isMaximal_of_equiv e
  have : P'.height = 1 := IsPrincipalIdealRing.height_eq_one_of_isMaximal P' polynomial_not_isField
  rwa [← e.height_map <| P.map (Ideal.Quotient.mk <| p.map (algebraMap R R[X]))]

/-- Let `p` be a maximal ideal of `R`. Then the height of `p[X]` equals the height of `p`. -/
lemma height_map_C (p : Ideal R) [p.IsMaximal] : (p.map C).height = p.height := by
  have : (p.map C).LiesOver p := ⟨IsMaximal.eq_of_le inferInstance IsPrime.ne_top' le_comap_map⟩
  simp [height_eq_height_add_of_liesOver_of_hasGoingDown p]

attribute [local instance] Polynomial.algebra Polynomial.isLocalization

/-- Let `p` be a prime ideal of `A`. If `P` is a maximal ideal of `A[X]` lying over `p`,
`ht(P) = ht(p) + 1`. -/
lemma height_eq_height_succ (p : Ideal R)
    [p.IsPrime] (P : Ideal R[X]) [P.IsMaximal] [P.LiesOver p] :
    P.height = p.height + 1 := by
  let Rₚ := Localization.AtPrime p
  set p' : Ideal Rₚ := p.map (algebraMap R Rₚ) with p'_def
  have : p'.IsMaximal := by
    rw [p'_def, Localization.AtPrime.map_eq_maximalIdeal]
    exact IsLocalRing.maximalIdeal.isMaximal Rₚ
  let P' : Ideal Rₚ[X] := P.map (algebraMap R[X] Rₚ[X])
  have disj : Disjoint (p.primeCompl.map C : Set R[X]) P := by
    refine Set.disjoint_left.mpr fun a ⟨b, hb⟩ ha ↦ hb.1 ?_
    rwa [SetLike.mem_coe, LiesOver.over (P := P) (p := p), mem_comap, algebraMap_eq, hb.2]
  have eq := comap_map_of_isPrime_disjoint _ Rₚ[X] P ‹P.IsMaximal›.isPrime disj
  have : (comap (algebraMap R[X] Rₚ[X]) P').IsMaximal := eq.symm ▸ ‹P.IsMaximal›
  have : P'.IsMaximal := .of_isLocalization_of_disjoint (eq.symm ▸ disj)
  have : P'.LiesOver p' := liesOver_of_isPrime_of_disjoint p.primeCompl _ _ disj
  have eq1 : p.height = p'.height := by
    rw [height_map_of_disjoint p.primeCompl]
    exact Disjoint.symm <| Set.disjoint_left.mpr fun _ a b ↦ b a
  have eq2 : P.height = P'.height := by
    rw [height_map_of_disjoint (Submonoid.map C <| p.primeCompl) _ disj]
  rw [eq1, eq2]
  apply height_eq_height_succ_of_isMaximal p' P'

/-- If `R` is Noetherian, `dim R[X] = dim R + 1`. -/
lemma ringKrullDim_of_isNoetherianRing : ringKrullDim R[X] = ringKrullDim R + 1 := by
  refine le_antisymm ?_ ?_
  · nontriviality R[X]
    refine (ringKrullDim_le_iff_isMaximal_height_le (ringKrullDim R + 1)).mpr fun M hM ↦ ?_
    rw [height_eq_height_succ (M.under R) M, WithBot.coe_add, WithBot.coe_one]
    gcongr
    exact Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'
  · exact ringKrullDim_succ_le_ringKrullDim_polynomial

end Polynomial
