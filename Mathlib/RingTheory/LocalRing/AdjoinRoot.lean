/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Radical.Basic

import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!

# Results on `AdjoinRoot` and Local Rings

This file establishes the necessary and sufficient conditions for the polynomial
quotient ring $R[X]/(p)$ (i.e., `AdjoinRoot p`) to be a local ring.

## Main results

* `AdjoinRoot.isLocalRing_iff_isPrimePow_normalize`: Over a field $k$, the quotient
  ring $k[X]/(f)$ is a local ring if and only if $f$ is a prime power.
* `AdjoinRoot.isLocalRing_iff_of_monic`: Over a commutative ring $R$, for a monic
  polynomial $p$, $R[X]/(p)$ is a local ring if and only if $R$ is a local ring
  and the reduction of $p$ modulo the maximal ideal of $R$ is a prime power
  in the polynomial ring over the residue field.

-/

public section

open Polynomial IsLocalRing Ideal UniqueFactorizationMonoid

namespace AdjoinRoot

variable {R k : Type*} [CommRing R] [Field k] {p q : R[X]} {f : k[X]}

lemma isLocalRing_of_monic_of_isLocalRing (monic : p.Monic) [IsLocalRing (AdjoinRoot p)] :
    IsLocalRing R :=
  haveI : IsLocalHom (algebraMap R (AdjoinRoot p)) :=
    isLocalHom_of_monic_of_degree_pos monic ((nontrivial_iff_of_monic monic).mp inferInstance)
  RingHom.domain_isLocalRing (algebraMap R (AdjoinRoot p))

lemma nilradical_eq_span_mk_radical (ne : p ≠ 0) [UniqueFactorizationMonoid R]
    [NormalizationMonoid R] : nilradical (AdjoinRoot p) = span {mk p (radical p)} := by
  rw [nilradical_eq_map_radical_ker_of_surjective mk_surjective, AdjoinRoot.mk_ker,
    radical_span_singleton_eq_span_radical ne, map_span, Set.image_singleton]

lemma isMaximal_nilradical_of_isPrimePow_normalize (ne : f ≠ 0) [DecidableEq k]
    (h : IsPrimePow (normalize f)) : (nilradical (AdjoinRoot f)).IsMaximal := by
  rw [← prime_radical_iff_isPrimePow_normalize ne] at h
  rw [nilradical_eq_span_mk_radical ne, ← Set.image_singleton, ← map_span]
  exact h.isMaximal_span_singleton.map_of_surjective_of_ker_le mk_surjective
    (by simpa [mem_span_singleton] using radical_dvd_self)

theorem isLocalRing_iff_isPrimePow_normalize (ne : f ≠ 0) [DecidableEq k] :
    IsLocalRing (AdjoinRoot f) ↔ IsPrimePow (normalize f) := by
  refine ⟨fun _ ↦ ?_, fun h ↦ ?_⟩
  · have eq : {J | span {f} ≤ J ∧ J.IsPrime} = {(maximalIdeal (AdjoinRoot f)).comap (mk f)} := by
      suffices ∀ (I : Ideal k[X]), f ∈ I → I.IsPrime →
        I = comap (mk f) (maximalIdeal (AdjoinRoot f)) by
          simpa [Set.eq_singleton_iff_unique_mem, comap_isPrime]
      intro I f_in hI
      replace hI := hI.isMaximal (ne_of_mem_of_not_mem' f_in ne)
      have maximal := hI.map_of_surjective_of_ker_le (f := mk f) mk_surjective (by simpa)
      rw [← eq_maximalIdeal maximal, comap_map_eq_self_of_isMaximal _ maximal.ne_top]
    rw [← prime_radical_iff_isPrimePow_normalize ne, ← prime_span_singleton_iff,
      prime_iff_isPrime (by simp), ← radical_span_singleton_eq_span_radical ne,
      radical_eq_sInf, eq, sInf_singleton]
    exact comap_isPrime ..
  · exact ((Ring.krullDimLE_zero_and_isLocalRing_tfae (AdjoinRoot f)).out 3 0 rfl rfl).mp
      (isMaximal_nilradical_of_isPrimePow_normalize ne h) |>.2

theorem krullDimLE_zero_of_isPrimePow_normalize (ne : f ≠ 0) [DecidableEq k]
    (h : IsPrimePow (normalize f)) : Ring.KrullDimLE 0 (AdjoinRoot f) :=
  ((Ring.krullDimLE_zero_and_isLocalRing_tfae (AdjoinRoot f)).out 3 0 rfl rfl).mp
      (isMaximal_nilradical_of_isPrimePow_normalize ne h) |>.1

lemma isPrimePow_map_residue_of_monic_of_isLocalRing (monic : p.Monic) [IsLocalRing R]
    [IsLocalRing (AdjoinRoot p)] : IsPrimePow (p.map (residue R)) := by
  classical
  rw [← (monic.map (residue R)).normalize_eq_self,
    ← isLocalRing_iff_isPrimePow_normalize (monic.map (residue R)).ne_zero]
  have : Nontrivial (AdjoinRoot (p.map (residue R))) := by
    rw [nontrivial_iff_of_monic (monic.map (residue R)), monic.degree_map,
      ← nontrivial_iff_of_monic monic]
    infer_instance
  let f := map (residue R) p (p.map (residue R)) dvd_rfl
  exact of_surjective' f (map_surjective_of_surjective residue_surjective dvd_rfl)

private lemma isLocalRingAux (monic : p.Monic) [IsLocalRing R]
    (hp : IsPrimePow (p.map (residue R))) :
    IsLocalRing (AdjoinRoot p ⧸ Ideal.map (of p) (maximalIdeal R)) := by
  classical
  have : IsLocalRing ((ResidueField R)[X] ⧸ span {p.map (residue R)}) :=
    (isLocalRing_iff_isPrimePow_normalize (monic.map (residue R)).ne_zero).mpr
      (by rwa [(monic.map (residue R)).normalize_eq_self])
  let e : AdjoinRoot p ⧸ Ideal.map (of p) (maximalIdeal R) ≃+*
    (ResidueField R)[X] ⧸ span {p.map (residue R)} :=
      quotAdjoinRootEquivQuotPolynomialQuot (maximalIdeal R) p
  exact e.symm.isLocalRing

theorem isLocalRing_of_isPrimePow_map_residue (monic : p.Monic) [IsLocalRing R]
    (hp : IsPrimePow (p.map (residue R))) : IsLocalRing (AdjoinRoot p) := by
  have : IsLocalRing (AdjoinRoot p ⧸ Ideal.map (of p) (maximalIdeal R)) := isLocalRingAux monic hp
  suffices IsLocalHom (Ideal.Quotient.mk (Ideal.map (of p) (maximalIdeal R))) from
    RingHom.domain_isLocalRing (Ideal.Quotient.mk (Ideal.map (of p) (maximalIdeal R)))
  refine Quotient.mk_isLocalHom_iff_forall_isMaximal_le.mpr fun I hI ↦ ?_
  have comap : (I.comap (of p)).IsMaximal := isMaximal_comap_of_isIntegral_of_isMaximal'
    (of p) (fun _ ↦ (isIntegral_of_monic monic).isIntegral _) I
  rw [map_le_iff_le_comap, eq_maximalIdeal comap]

theorem isLocalRing_iff_of_monic (monic : p.Monic) : IsLocalRing (AdjoinRoot p) ↔
    ∃ _ : IsLocalRing R, IsPrimePow (p.map (residue R)) := by
  refine ⟨fun _ ↦ ?_, fun h ↦ ?_⟩
  · have := isLocalRing_of_monic_of_isLocalRing monic
    exact ⟨this, isPrimePow_map_residue_of_monic_of_isLocalRing monic⟩
  · rcases h with ⟨_, h⟩
    exact isLocalRing_of_isPrimePow_map_residue monic h

end AdjoinRoot
