/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.GroupWithZero.Torsion
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Finiteness.Quotient
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Flat.Basic

/-!
# Ramification index and inertia degree

Given `P : Ideal S` lying over `p : Ideal R` for the ring extension `f : R →+* S`
(assuming `P` and `p` are prime or maximal where needed),
the **ramification index** `Ideal.ramificationIdx f p P` is the multiplicity of `P` in `map f p`,
and the **inertia degree** `Ideal.inertiaDeg f p P` is the degree of the field extension
`(S / P) : (R / p)`.

## Main results

The main theorem `Ideal.sum_ramification_inertia` states that for all coprime `P` lying over `p`,
`Σ P, ramification_idx f p P * inertia_deg f p P` equals the degree of the field extension
`Frac(S) : Frac(R)`.

## Implementation notes

Often the above theory is set up in the case where:
* `R` is the ring of integers of a number field `K`,
* `L` is a finite separable extension of `K`,
* `S` is the integral closure of `R` in `L`,
* `p` and `P` are maximal ideals,
* `P` is an ideal lying over `p`
We will try to relax the above hypotheses as much as possible.

## Notation

In this file, `e` stands for the ramification index and `f` for the inertia degree of `P` over `p`,
leaving `p` and `P` implicit.

-/

@[expose] public section

namespace Ideal

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  (p : Ideal R) (q : Ideal S) [q.IsPrime] (r : Ideal T) [r.IsPrime]

noncomputable def ramificationIdx : ℕ :=
  letI Sq := Localization.AtPrime q
  (Module.length Sq (Sq ⧸ p.map (algebraMap R Sq))).toNat

theorem ramificationIdx_tower [r.LiesOver q] [q.LiesOver p]
    [Module.Flat (Localization.AtPrime q) (Localization.AtPrime r)] :
    p.ramificationIdx r = p.ramificationIdx q * q.ramificationIdx r := by
  have : r.LiesOver p := LiesOver.trans r q p
  let Sq := Localization.AtPrime q
  let Tr := Localization.AtPrime r
  by_cases h : IsFiniteLength Sq (Sq ⧸ p.map (algebraMap R Sq))
  · rw [isFiniteLength_iff_exists_compositionSeries] at h
    obtain ⟨s, hs0, hs1⟩ := h
    sorry
  · suffices ¬ IsFiniteLength Tr (Tr ⧸ p.map (algebraMap R Tr)) by
      rw [← Module.length_ne_top_iff, not_ne_iff] at h this
      rw [ramificationIdx, ramificationIdx, ramificationIdx, h, this, ENat.toNat_top, zero_mul]
    contrapose! h
    let ψ : Sq ⧸ p.map (algebraMap R Sq) →+* Tr ⧸ p.map (algebraMap R Tr) := by
      refine Ideal.quotientMap _ (algebraMap Sq Tr) ?_
      rw [Ideal.map_le_iff_le_comap, comap_comap, ← IsScalarTower.algebraMap_eq]
      exact le_comap_map
    sorry

end Ideal
