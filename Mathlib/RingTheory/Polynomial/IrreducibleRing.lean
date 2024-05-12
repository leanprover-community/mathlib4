/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Polynomial.Nilpotent

/-!

# Polynomials over an irreducible ring

This file contains results about the polynomials over an irreducible ring (i.e. a ring with only
one minimal prime ideal, equivalently, whose spectrum is an irreducible topological space).

## Main results

- `Polynomial.Monic.irreducible_of_irreducible_map_of_isPrime_nilradical`: a monic polynomial over
  an irreducible ring is irreducible if it is irreducible after mapping into an integral domain.
  A generalization to `Polynomial.Monic.irreducible_of_irreducible_map`.

## Tags

polynomial, irreducible ring, nilradical, prime ideal

-/

open scoped Classical Polynomial

open Polynomial

noncomputable section

/-- A polynomial over an irreducible ring `R` is irreducible if it is monic and irreducible after
mapping into an integral domain `S` (https://math.stackexchange.com/a/4843432/235999).
A generalization to `Polynomial.Monic.irreducible_of_irreducible_map`. -/
theorem Polynomial.Monic.irreducible_of_irreducible_map_of_isPrime_nilradical
    {R S : Type*} [CommRing R] [(nilradical R).IsPrime] [CommRing S] [IsDomain S]
    (φ : R →+* S) (f : R[X]) (hm : f.Monic) (hi : Irreducible (f.map φ)) : Irreducible f := by
  let R' := R ⧸ nilradical R
  let ψ : R' →+* S := Ideal.Quotient.lift (nilradical R) φ
    (haveI := RingHom.ker_isPrime φ; nilradical_le_prime (RingHom.ker φ))
  let ι := algebraMap R R'
  rw [show φ = ψ.comp ι from rfl, ← map_map] at hi
  replace hi := hm.map ι |>.irreducible_of_irreducible_map _ _ hi
  refine ⟨fun h ↦ hi.1 <| (mapRingHom ι).isUnit_map h, fun a b h ↦ ?_⟩
  wlog hb : IsUnit (b.map ι) generalizing a b
  · exact (this b a (mul_comm a b ▸ h)
      (hi.2 _ _ (by rw [h, Polynomial.map_mul]) |>.resolve_right hb)).symm
  have hn (i : ℕ) (hi : i ≠ 0) : IsNilpotent (b.coeff i) := by
    obtain ⟨_, _, h⟩ := Polynomial.isUnit_iff.1 hb
    simpa only [coeff_map, coeff_C, hi, ite_false, ← RingHom.mem_ker,
      show RingHom.ker ι = nilradical R from Ideal.mk_ker] using congr(coeff $(h.symm) i)
  refine .inr <| isUnit_of_coeff_isUnit_isNilpotent (isUnit_of_mul_isUnit_right
    (x := a.coeff f.natDegree) <| (IsUnit.neg_iff _).1 ?_) hn
  have hc : f.leadingCoeff = _ := congr(coeff $h f.natDegree)
  rw [hm, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun i j ↦ a.coeff i * b.coeff j,
    Finset.sum_range_succ, ← sub_eq_iff_eq_add, Nat.sub_self] at hc
  rw [← add_sub_cancel_left 1 (-(_ * _)), ← sub_eq_add_neg, hc]
  exact IsNilpotent.isUnit_sub_one <| show _ ∈ nilradical R from sum_mem fun i hi ↦
    Ideal.mul_mem_left _ _ <| hn _ <| Nat.sub_ne_zero_of_lt (List.mem_range.1 hi)
