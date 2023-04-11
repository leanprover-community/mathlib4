/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca

! This file was ported from Lean 3 source module ring_theory.polynomial.eisenstein.basic
! leanprover-community/mathlib commit 2032a878972d5672e7c27c957e7a6e297b044973
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.EisensteinCriterion
import Mathbin.RingTheory.Polynomial.ScaleRoots

/-!
# Eisenstein polynomials
Given an ideal `𝓟` of a commutative semiring `R`, we say that a polynomial `f : R[X]` is
*Eisenstein at `𝓟`* if `f.leading_coeff ∉ 𝓟`, `∀ n, n < f.nat_degree → f.coeff n ∈ 𝓟` and
`f.coeff 0 ∉ 𝓟 ^ 2`. In this file we gather miscellaneous results about Eisenstein polynomials.

## Main definitions
* `polynomial.is_eisenstein_at f 𝓟`: the property of being Eisenstein at `𝓟`.

## Main results
* `polynomial.is_eisenstein_at.irreducible`: if a primitive `f` satisfies `f.is_eisenstein_at 𝓟`,
  where `𝓟.is_prime`, then `f` is irreducible.

## Implementation details
We also define a notion `is_weakly_eisenstein_at` requiring only that
`∀ n < f.nat_degree → f.coeff n ∈ 𝓟`. This makes certain results slightly more general and it is
useful since it is sometimes better behaved (for example it is stable under `polynomial.map`).

-/


universe u v w z

variable {R : Type u}

open Ideal Algebra Finset

open BigOperators Polynomial

namespace Polynomial

/-- Given an ideal `𝓟` of a commutative semiring `R`, we say that a polynomial `f : R[X]`
is *weakly Eisenstein at `𝓟`* if `∀ n, n < f.nat_degree → f.coeff n ∈ 𝓟`. -/
@[mk_iff]
structure IsWeaklyEisensteinAt [CommSemiring R] (f : R[X]) (𝓟 : Ideal R) : Prop where
  Mem : ∀ {n}, n < f.natDegree → f.coeff n ∈ 𝓟
#align polynomial.is_weakly_eisenstein_at Polynomial.IsWeaklyEisensteinAt

/-- Given an ideal `𝓟` of a commutative semiring `R`, we say that a polynomial `f : R[X]`
is *Eisenstein at `𝓟`* if `f.leading_coeff ∉ 𝓟`, `∀ n, n < f.nat_degree → f.coeff n ∈ 𝓟` and
`f.coeff 0 ∉ 𝓟 ^ 2`. -/
@[mk_iff]
structure IsEisensteinAt [CommSemiring R] (f : R[X]) (𝓟 : Ideal R) : Prop where
  leading : f.leadingCoeff ∉ 𝓟
  Mem : ∀ {n}, n < f.natDegree → f.coeff n ∈ 𝓟
  not_mem : f.coeff 0 ∉ 𝓟 ^ 2
#align polynomial.is_eisenstein_at Polynomial.IsEisensteinAt

namespace IsWeaklyEisensteinAt

section CommSemiring

variable [CommSemiring R] {𝓟 : Ideal R} {f : R[X]} (hf : f.IsWeaklyEisensteinAt 𝓟)

include hf

theorem map {A : Type v} [CommRing A] (φ : R →+* A) : (f.map φ).IsWeaklyEisensteinAt (𝓟.map φ) :=
  by
  refine' (is_weakly_eisenstein_at_iff _ _).2 fun n hn => _
  rw [coeff_map]
  exact mem_map_of_mem _ (hf.mem (lt_of_lt_of_le hn (nat_degree_map_le _ _)))
#align polynomial.is_weakly_eisenstein_at.map Polynomial.IsWeaklyEisensteinAt.map

end CommSemiring

section CommRing

variable [CommRing R] {𝓟 : Ideal R} {f : R[X]} (hf : f.IsWeaklyEisensteinAt 𝓟)

variable {S : Type v} [CommRing S] [Algebra R S]

section Principal

variable {p : R}

-- mathport name: exprP
local notation "P" => Submodule.span R {p}

theorem exists_mem_adjoin_mul_eq_pow_natDegree {x : S} (hx : aeval x f = 0) (hmo : f.Monic)
    (hf : f.IsWeaklyEisensteinAt P) :
    ∃ y ∈ adjoin R ({x} : Set S), (algebraMap R S) p * y = x ^ (f.map (algebraMap R S)).natDegree :=
  by
  rw [aeval_def, Polynomial.eval₂_eq_eval_map, eval_eq_sum_range, range_add_one,
    sum_insert not_mem_range_self, sum_range, (hmo.map (algebraMap R S)).coeff_natDegree,
    one_mul] at hx
  replace hx := eq_neg_of_add_eq_zero_left hx
  have : ∀ n < f.nat_degree, p ∣ f.coeff n :=
    by
    intro n hn
    refine' mem_span_singleton.1 (by simpa using hf.mem hn)
  choose! φ hφ using this
  conv_rhs at hx =>
    congr
    congr
    skip
    ext
    rw [[anonymous], coeff_map, hφ i.1 (lt_of_lt_of_le i.2 (nat_degree_map_le _ _)),
      RingHom.map_mul, mul_assoc]
  rw [hx, ← mul_sum, neg_eq_neg_one_mul, ← mul_assoc (-1 : S), mul_comm (-1 : S), mul_assoc]
  refine'
    ⟨-1 * ∑ i : Fin (f.map (algebraMap R S)).natDegree, (algebraMap R S) (φ i.1) * x ^ i.1, _, rfl⟩
  exact
    Subalgebra.mul_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _))
      (Subalgebra.sum_mem _ fun i hi =>
        Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
          (Subalgebra.pow_mem _ (subset_adjoin (Set.mem_singleton x)) _))
#align polynomial.is_weakly_eisenstein_at.exists_mem_adjoin_mul_eq_pow_nat_degree Polynomial.IsWeaklyEisensteinAt.exists_mem_adjoin_mul_eq_pow_natDegree

theorem exists_mem_adjoin_mul_eq_pow_natDegree_le {x : S} (hx : aeval x f = 0) (hmo : f.Monic)
    (hf : f.IsWeaklyEisensteinAt P) :
    ∀ i,
      (f.map (algebraMap R S)).natDegree ≤ i →
        ∃ y ∈ adjoin R ({x} : Set S), (algebraMap R S) p * y = x ^ i :=
  by
  intro i hi
  obtain ⟨k, hk⟩ := exists_add_of_le hi
  rw [hk, pow_add]
  obtain ⟨y, hy, H⟩ := exists_mem_adjoin_mul_eq_pow_nat_degree hx hmo hf
  refine' ⟨y * x ^ k, _, _⟩
  · exact Subalgebra.mul_mem _ hy (Subalgebra.pow_mem _ (subset_adjoin (Set.mem_singleton x)) _)
  · rw [← mul_assoc _ y, H]
#align polynomial.is_weakly_eisenstein_at.exists_mem_adjoin_mul_eq_pow_nat_degree_le Polynomial.IsWeaklyEisensteinAt.exists_mem_adjoin_mul_eq_pow_natDegree_le

end Principal

include hf

theorem pow_natDegree_le_of_root_of_monic_mem {x : R} (hroot : IsRoot f x) (hmo : f.Monic) :
    ∀ i, f.natDegree ≤ i → x ^ i ∈ 𝓟 := by
  intro i hi
  obtain ⟨k, hk⟩ := exists_add_of_le hi
  rw [hk, pow_add]
  suffices x ^ f.nat_degree ∈ 𝓟 by exact mul_mem_right (x ^ k) 𝓟 this
  rw [is_root.def, eval_eq_sum_range, Finset.range_add_one,
    Finset.sum_insert Finset.not_mem_range_self, Finset.sum_range, hmo.coeff_nat_degree, one_mul] at
    hroot
  rw [eq_neg_of_add_eq_zero_left hroot, neg_mem_iff]
  refine' Submodule.sum_mem _ fun i hi => mul_mem_right _ _ (hf.mem (Fin.is_lt i))
#align polynomial.is_weakly_eisenstein_at.pow_nat_degree_le_of_root_of_monic_mem Polynomial.IsWeaklyEisensteinAt.pow_natDegree_le_of_root_of_monic_mem

theorem pow_natDegree_le_of_aeval_zero_of_monic_mem_map {x : S} (hx : aeval x f = 0)
    (hmo : f.Monic) :
    ∀ i, (f.map (algebraMap R S)).natDegree ≤ i → x ^ i ∈ 𝓟.map (algebraMap R S) :=
  by
  suffices x ^ (f.map (algebraMap R S)).natDegree ∈ 𝓟.map (algebraMap R S)
    by
    intro i hi
    obtain ⟨k, hk⟩ := exists_add_of_le hi
    rw [hk, pow_add]
    refine' mul_mem_right _ _ this
  rw [aeval_def, eval₂_eq_eval_map, ← is_root.def] at hx
  refine' pow_nat_degree_le_of_root_of_monic_mem (hf.map _) hx (hmo.map _) _ rfl.le
#align polynomial.is_weakly_eisenstein_at.pow_nat_degree_le_of_aeval_zero_of_monic_mem_map Polynomial.IsWeaklyEisensteinAt.pow_natDegree_le_of_aeval_zero_of_monic_mem_map

end CommRing

end IsWeaklyEisensteinAt

section ScaleRoots

variable {A : Type _} [CommRing R] [CommRing A]

theorem scaleRoots.isWeaklyEisensteinAt (p : R[X]) {x : R} {P : Ideal R} (hP : x ∈ P) :
    (scaleRoots p x).IsWeaklyEisensteinAt P :=
  by
  refine' ⟨fun i hi => _⟩
  rw [coeff_scale_roots]
  rw [nat_degree_scale_roots, ← tsub_pos_iff_lt] at hi
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem P hP _ hi)
#align polynomial.scale_roots.is_weakly_eisenstein_at Polynomial.scaleRoots.isWeaklyEisensteinAt

theorem dvd_pow_natDegree_of_eval₂_eq_zero {f : R →+* A} (hf : Function.Injective f) {p : R[X]}
    (hp : p.Monic) (x y : R) (z : A) (h : p.eval₂ f z = 0) (hz : f x * z = f y) :
    x ∣ y ^ p.natDegree :=
  by
  rw [← nat_degree_scale_roots p x, ← Ideal.mem_span_singleton]
  refine'
    (scale_roots.is_weakly_eisenstein_at _
          (ideal.mem_span_singleton.mpr <| dvd_refl x)).pow_natDegree_le_of_root_of_monic_mem
      _ ((monic_scale_roots_iff x).mpr hp) _ le_rfl
  rw [injective_iff_map_eq_zero'] at hf
  have := scale_roots_eval₂_eq_zero f h
  rwa [hz, Polynomial.eval₂_at_apply, hf] at this
#align polynomial.dvd_pow_nat_degree_of_eval₂_eq_zero Polynomial.dvd_pow_natDegree_of_eval₂_eq_zero

theorem dvd_pow_natDegree_of_aeval_eq_zero [Algebra R A] [Nontrivial A] [NoZeroSMulDivisors R A]
    {p : R[X]} (hp : p.Monic) (x y : R) (z : A) (h : Polynomial.aeval z p = 0)
    (hz : z * algebraMap R A x = algebraMap R A y) : x ∣ y ^ p.natDegree :=
  dvd_pow_natDegree_of_eval₂_eq_zero (NoZeroSMulDivisors.algebraMap_injective R A) hp x y z h
    ((mul_comm _ _).trans hz)
#align polynomial.dvd_pow_nat_degree_of_aeval_eq_zero Polynomial.dvd_pow_natDegree_of_aeval_eq_zero

end ScaleRoots

namespace IsEisensteinAt

section CommSemiring

variable [CommSemiring R] {𝓟 : Ideal R} {f : R[X]} (hf : f.IsEisensteinAt 𝓟)

theorem Polynomial.Monic.leadingCoeff_not_mem (hf : f.Monic) (h : 𝓟 ≠ ⊤) : ¬f.leadingCoeff ∈ 𝓟 :=
  hf.leadingCoeff.symm ▸ (Ideal.ne_top_iff_one _).1 h
#align polynomial.monic.leading_coeff_not_mem Polynomial.Monic.leadingCoeff_not_mem

theorem Polynomial.Monic.isEisensteinAt_of_mem_of_not_mem (hf : f.Monic) (h : 𝓟 ≠ ⊤)
    (hmem : ∀ {n}, n < f.natDegree → f.coeff n ∈ 𝓟) (hnot_mem : f.coeff 0 ∉ 𝓟 ^ 2) :
    f.IsEisensteinAt 𝓟 :=
  { leading := hf.leadingCoeff_not_mem h
    Mem := fun n hn => hmem hn
    not_mem := hnot_mem }
#align polynomial.monic.is_eisenstein_at_of_mem_of_not_mem Polynomial.Monic.isEisensteinAt_of_mem_of_not_mem

include hf

theorem isWeaklyEisensteinAt : IsWeaklyEisensteinAt f 𝓟 :=
  ⟨fun _ => hf.Mem⟩
#align polynomial.is_eisenstein_at.is_weakly_eisenstein_at Polynomial.IsEisensteinAt.isWeaklyEisensteinAt

theorem coeff_mem {n : ℕ} (hn : n ≠ f.natDegree) : f.coeff n ∈ 𝓟 :=
  by
  cases ne_iff_lt_or_gt.1 hn
  · exact hf.mem h
  · rw [coeff_eq_zero_of_nat_degree_lt h]
    exact Ideal.zero_mem _
#align polynomial.is_eisenstein_at.coeff_mem Polynomial.IsEisensteinAt.coeff_mem

end CommSemiring

section IsDomain

variable [CommRing R] [IsDomain R] {𝓟 : Ideal R} {f : R[X]} (hf : f.IsEisensteinAt 𝓟)

/-- If a primitive `f` satisfies `f.is_eisenstein_at 𝓟`, where `𝓟.is_prime`, then `f` is
irreducible. -/
theorem irreducible (hprime : 𝓟.IsPrime) (hu : f.IsPrimitive) (hfd0 : 0 < f.natDegree) :
    Irreducible f :=
  irreducible_of_eisenstein_criterion hprime hf.leading (fun n hn => hf.Mem (coe_lt_degree.1 hn))
    (natDegree_pos_iff_degree_pos.1 hfd0) hf.not_mem hu
#align polynomial.is_eisenstein_at.irreducible Polynomial.IsEisensteinAt.irreducible

end IsDomain

end IsEisensteinAt

end Polynomial

