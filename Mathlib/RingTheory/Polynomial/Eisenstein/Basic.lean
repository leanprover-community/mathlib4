/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
public import Mathlib.RingTheory.Polynomial.ScaleRoots
meta import Mathlib.Tactic.Attr.Register

/-!
# Eisenstein polynomials
Given an ideal `𝓟` of a commutative semiring `R`, we say that a polynomial `f : R[X]` is
*Eisenstein at `𝓟`* if `f.leadingCoeff ∉ 𝓟`, `∀ n, n < f.natDegree → f.coeff n ∈ 𝓟` and
`f.coeff 0 ∉ 𝓟 ^ 2`. In this file we gather miscellaneous results about Eisenstein polynomials.

## Main definitions
* `Polynomial.IsEisensteinAt f 𝓟`: the property of being Eisenstein at `𝓟`.

## Main results
* `Polynomial.IsEisensteinAt.irreducible`: if a primitive `f` satisfies `f.IsEisensteinAt 𝓟`,
  where `𝓟.IsPrime`, then `f` is irreducible.

## Implementation details
We also define a notion `IsWeaklyEisensteinAt` requiring only that
`∀ n < f.natDegree → f.coeff n ∈ 𝓟`. This makes certain results slightly more general and it is
useful since it is sometimes better behaved (for example it is stable under `Polynomial.map`).

-/

@[expose] public section


universe u v w z

variable {R : Type u}

open Ideal Algebra Finset

open Polynomial

namespace Polynomial

/-- Given an ideal `𝓟` of a commutative semiring `R`, we say that a polynomial `f : R[X]`
is *weakly Eisenstein at `𝓟`* if `∀ n, n < f.natDegree → f.coeff n ∈ 𝓟`. -/
@[mk_iff]
structure IsWeaklyEisensteinAt [CommSemiring R] (f : R[X]) (𝓟 : Ideal R) : Prop where
  mem : ∀ {n}, n < f.natDegree → f.coeff n ∈ 𝓟

/-- Given an ideal `𝓟` of a commutative semiring `R`, we say that a polynomial `f : R[X]`
is *Eisenstein at `𝓟`* if `f.leadingCoeff ∉ 𝓟`, `∀ n, n < f.natDegree → f.coeff n ∈ 𝓟` and
`f.coeff 0 ∉ 𝓟 ^ 2`. -/
@[mk_iff]
structure IsEisensteinAt [CommSemiring R] (f : R[X]) (𝓟 : Ideal R) : Prop where
  leading : f.leadingCoeff ∉ 𝓟
  mem : ∀ {n}, n < f.natDegree → f.coeff n ∈ 𝓟
  notMem : f.coeff 0 ∉ 𝓟 ^ 2

namespace IsWeaklyEisensteinAt

section CommSemiring

variable [CommSemiring R] {𝓟 : Ideal R} {f f' : R[X]}

theorem map (hf : f.IsWeaklyEisensteinAt 𝓟) {A : Type v} [CommSemiring A] (φ : R →+* A) :
    (f.map φ).IsWeaklyEisensteinAt (𝓟.map φ) := by
  refine (isWeaklyEisensteinAt_iff _ _).2 fun hn => ?_
  rw [coeff_map]
  exact mem_map_of_mem _ (hf.mem (lt_of_lt_of_le hn natDegree_map_le))

theorem mul (hf : f.IsWeaklyEisensteinAt 𝓟) (hf' : f'.IsWeaklyEisensteinAt 𝓟) :
    (f * f').IsWeaklyEisensteinAt 𝓟 := by
  rw [isWeaklyEisensteinAt_iff] at hf hf' ⊢
  intro n hn
  rw [coeff_mul]
  refine sum_mem _ fun x hx ↦ ?_
  rcases lt_or_ge x.1 f.natDegree with hx1 | hx1
  · exact mul_mem_right _ _ (hf hx1)
  replace hx1 : x.2 < f'.natDegree := by
    by_contra!
    rw [HasAntidiagonal.mem_antidiagonal] at hx
    replace hn := hn.trans_le natDegree_mul_le
    linarith
  exact mul_mem_left _ _ (hf' hx1)

end CommSemiring

section CommRing

variable [CommRing R] {𝓟 : Ideal R} {f : R[X]}
variable {S : Type v} [CommRing S] [Algebra R S]

section Principal

variable {p : R}

theorem exists_mem_adjoin_mul_eq_pow_natDegree {x : S} (hx : aeval x f = 0) (hmo : f.Monic)
    (hf : f.IsWeaklyEisensteinAt (Submodule.span R {p})) : ∃ y ∈ adjoin R ({x} : Set S),
    (algebraMap R S) p * y = x ^ (f.map (algebraMap R S)).natDegree := by
  rw [aeval_def, Polynomial.eval₂_eq_eval_map, eval_eq_sum_range, range_add_one,
    sum_insert notMem_range_self, sum_range, (hmo.map (algebraMap R S)).coeff_natDegree,
    one_mul] at hx
  replace hx := eq_neg_of_add_eq_zero_left hx
  have : ∀ n < f.natDegree, p ∣ f.coeff n := by
    intro n hn
    exact mem_span_singleton.1 (by simpa using hf.mem hn)
  choose! φ hφ using this
  conv_rhs at hx =>
    congr
    congr
    · skip
    ext i
    rw [coeff_map, hφ i.1 (lt_of_lt_of_le i.2 natDegree_map_le), map_mul, mul_assoc]
  rw [hx, ← mul_sum, neg_eq_neg_one_mul, ← mul_assoc (-1 : S), mul_comm (-1 : S), mul_assoc]
  refine
    ⟨-1 * ∑ i : Fin (f.map (algebraMap R S)).natDegree, (algebraMap R S) (φ i.1) * x ^ i.1, ?_, rfl⟩
  exact
    Subalgebra.mul_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _))
      (Subalgebra.sum_mem _ fun i _ =>
        Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
          (Subalgebra.pow_mem _ (subset_adjoin (Set.mem_singleton x)) _))

theorem exists_mem_adjoin_mul_eq_pow_natDegree_le {x : S} (hx : aeval x f = 0) (hmo : f.Monic)
    (hf : f.IsWeaklyEisensteinAt (Submodule.span R {p})) :
    ∀ i, (f.map (algebraMap R S)).natDegree ≤ i →
        ∃ y ∈ adjoin R ({x} : Set S), (algebraMap R S) p * y = x ^ i := by
  intro i hi
  obtain ⟨k, hk⟩ := exists_add_of_le hi
  rw [hk, pow_add]
  obtain ⟨y, hy, H⟩ := exists_mem_adjoin_mul_eq_pow_natDegree hx hmo hf
  refine ⟨y * x ^ k, ?_, ?_⟩
  · exact Subalgebra.mul_mem _ hy (Subalgebra.pow_mem _ (subset_adjoin (Set.mem_singleton x)) _)
  · rw [← mul_assoc _ y, H]

end Principal

theorem pow_natDegree_le_of_root_of_monic_mem (hf : f.IsWeaklyEisensteinAt 𝓟)
    {x : R} (hroot : IsRoot f x) (hmo : f.Monic) :
    ∀ i, f.natDegree ≤ i → x ^ i ∈ 𝓟 := by
  intro i hi
  obtain ⟨k, hk⟩ := exists_add_of_le hi
  rw [hk, pow_add]
  suffices x ^ f.natDegree ∈ 𝓟 by exact mul_mem_right (x ^ k) 𝓟 this
  rw [IsRoot.def, eval_eq_sum_range, Finset.range_add_one,
    Finset.sum_insert Finset.notMem_range_self, Finset.sum_range, hmo.coeff_natDegree, one_mul] at
    *
  rw [eq_neg_of_add_eq_zero_left hroot, neg_mem_iff]
  exact Submodule.sum_mem _ fun i _ => mul_mem_right _ _ (hf.mem (Fin.is_lt i))

theorem pow_natDegree_le_of_aeval_zero_of_monic_mem_map (hf : f.IsWeaklyEisensteinAt 𝓟)
    {x : S} (hx : aeval x f = 0) (hmo : f.Monic) :
    ∀ i, (f.map (algebraMap R S)).natDegree ≤ i → x ^ i ∈ 𝓟.map (algebraMap R S) := by
  suffices x ^ (f.map (algebraMap R S)).natDegree ∈ 𝓟.map (algebraMap R S) by
    intro i hi
    obtain ⟨k, hk⟩ := exists_add_of_le hi
    rw [hk, pow_add]
    exact mul_mem_right _ _ this
  rw [aeval_def, eval₂_eq_eval_map, ← IsRoot.def] at hx
  exact pow_natDegree_le_of_root_of_monic_mem (hf.map _) hx (hmo.map _) _ rfl.le

end CommRing

end IsWeaklyEisensteinAt

section ScaleRoots

variable {A : Type*} [CommRing R] [CommRing A]

theorem scaleRoots.isWeaklyEisensteinAt (p : R[X]) {x : R} {P : Ideal R} (hP : x ∈ P) :
    (scaleRoots p x).IsWeaklyEisensteinAt P := by
  refine ⟨fun i => ?_⟩
  rw [coeff_scaleRoots]
  rw [natDegree_scaleRoots, ← tsub_pos_iff_lt] at i
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem P hP _ i)

theorem dvd_pow_natDegree_of_eval₂_eq_zero {f : R →+* A} (hf : Function.Injective f) {p : R[X]}
    (hp : p.Monic) (x y : R) (z : A) (h : p.eval₂ f z = 0) (hz : f x * z = f y) :
    x ∣ y ^ p.natDegree := by
  rw [← natDegree_scaleRoots p x, ← Ideal.mem_span_singleton]
  refine
    (scaleRoots.isWeaklyEisensteinAt _
          (Ideal.mem_span_singleton.mpr <| dvd_refl x)).pow_natDegree_le_of_root_of_monic_mem
      ?_ ((monic_scaleRoots_iff x).mpr hp) _ le_rfl
  rw [injective_iff_map_eq_zero'] at hf
  have : eval₂ f _ (p.scaleRoots x) = 0 := scaleRoots_eval₂_eq_zero f h
  rwa [hz, Polynomial.eval₂_at_apply, hf] at this

theorem dvd_pow_natDegree_of_aeval_eq_zero [IsDomain R] [Algebra R A] [Nontrivial A]
    [Module.IsTorsionFree R A] {p : R[X]} (hp : p.Monic) (x y : R) (z : A) (h : p.aeval z = 0)
    (hz : z * algebraMap R A x = algebraMap R A y) : x ∣ y ^ p.natDegree :=
  dvd_pow_natDegree_of_eval₂_eq_zero (FaithfulSMul.algebraMap_injective R A) hp x y z h
    ((mul_comm _ _).trans hz)

end ScaleRoots

namespace IsEisensteinAt

section CommSemiring

variable [CommSemiring R] {𝓟 : Ideal R} {f : R[X]}

theorem _root_.Polynomial.Monic.leadingCoeff_notMem (hf : f.Monic) (h : 𝓟 ≠ ⊤) :
    f.leadingCoeff ∉ 𝓟 := hf.leadingCoeff.symm ▸ (Ideal.ne_top_iff_one _).1 h

theorem _root_.Polynomial.Monic.isEisensteinAt_of_mem_of_notMem (hf : f.Monic) (h : 𝓟 ≠ ⊤)
    (hmem : ∀ {n}, n < f.natDegree → f.coeff n ∈ 𝓟) (hnotMem : f.coeff 0 ∉ 𝓟 ^ 2) :
    f.IsEisensteinAt 𝓟 :=
  { leading := Polynomial.Monic.leadingCoeff_notMem hf h
    mem := fun hn => hmem hn
    notMem := hnotMem }

theorem isWeaklyEisensteinAt (hf : f.IsEisensteinAt 𝓟) : IsWeaklyEisensteinAt f 𝓟 :=
  ⟨fun h => hf.mem h⟩

theorem coeff_mem (hf : f.IsEisensteinAt 𝓟) {n : ℕ} (hn : n ≠ f.natDegree) : f.coeff n ∈ 𝓟 := by
  rcases ne_iff_lt_or_gt.1 hn with h₁ | h₂
  · exact hf.mem h₁
  · rw [coeff_eq_zero_of_natDegree_lt h₂]
    exact Ideal.zero_mem _

end CommSemiring

section IsDomain

variable [CommRing R] [IsDomain R] {𝓟 : Ideal R} {f : R[X]}

/-- If a primitive `f` satisfies `f.IsEisensteinAt 𝓟`, where `𝓟.IsPrime`,
then `f` is irreducible. -/
theorem irreducible (hf : f.IsEisensteinAt 𝓟) (hprime : 𝓟.IsPrime) (hu : f.IsPrimitive)
    (hfd0 : 0 < f.natDegree) : Irreducible f :=
  irreducible_of_eisenstein_criterion hprime hf.leading (fun _ hn => hf.mem (coe_lt_degree.1 hn))
    (natDegree_pos_iff_degree_pos.1 hfd0) hf.notMem hu

end IsDomain

end IsEisensteinAt

end Polynomial
