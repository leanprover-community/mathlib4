/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Eval.Subring
import Mathlib.Algebra.Polynomial.Monic

/-!
# Polynomials that lift

Given semirings `R` and `S` with a morphism `f : R →+* S`, we define a subsemiring `lifts` of
`S[X]` by the image of `RingHom.of (map f)`.
Then, we prove that a polynomial that lifts can always be lifted to a polynomial of the same degree
and that a monic polynomial that lifts can be lifted to a monic polynomial (of the same degree).

## Main definition

* `lifts (f : R →+* S)` : the subsemiring of polynomials that lift.

## Main results

* `lifts_and_degree_eq` : A polynomial lifts if and only if it can be lifted to a polynomial
  of the same degree.
* `lifts_and_degree_eq_and_monic` : A monic polynomial lifts if and only if it can be lifted to a
  monic polynomial of the same degree.
* `lifts_iff_alg` : if `R` is commutative, a polynomial lifts if and only if it is in the image of
  `mapAlg`, where `mapAlg : R[X] →ₐ[R] S[X]` is the only `R`-algebra map
  that sends `X` to `X`.

## Implementation details

In general `R` and `S` are semiring, so `lifts` is a semiring. In the case of rings, see
`lifts_iff_lifts_ring`.

Since we do not assume `R` to be commutative, we cannot say in general that the set of polynomials
that lift is a subalgebra. (By `lift_iff` this is true if `R` is commutative.)

-/


open Polynomial

noncomputable section

namespace Polynomial

universe u v w

section Semiring

variable {R : Type u} [Semiring R] {S : Type v} [Semiring S] {f : R →+* S}

/-- We define the subsemiring of polynomials that lifts as the image of `RingHom.of (map f)`. -/
def lifts (f : R →+* S) : Subsemiring S[X] :=
  RingHom.rangeS (mapRingHom f)

theorem mem_lifts (p : S[X]) : p ∈ lifts f ↔ ∃ q : R[X], map f q = p := by
  simp only [coe_mapRingHom, lifts, RingHom.mem_rangeS]

theorem lifts_iff_set_range (p : S[X]) : p ∈ lifts f ↔ p ∈ Set.range (map f) := by
  simp only [coe_mapRingHom, lifts, Set.mem_range, RingHom.mem_rangeS]

theorem lifts_iff_ringHom_rangeS (p : S[X]) : p ∈ lifts f ↔ p ∈ (mapRingHom f).rangeS := by
  simp only [coe_mapRingHom, lifts, Set.mem_range, RingHom.mem_rangeS]

theorem lifts_iff_coeff_lifts (p : S[X]) : p ∈ lifts f ↔ ∀ n : ℕ, p.coeff n ∈ Set.range f := by
  rw [lifts_iff_ringHom_rangeS, mem_map_rangeS f]
  rfl

theorem lifts_iff_coeffs_subset_range (p : S[X]) :
    p ∈ lifts f ↔ (p.coeffs : Set S) ⊆ Set.range f := by
  rw [lifts_iff_coeff_lifts]
  constructor
  · intro h _ hc
    obtain ⟨n, ⟨-, hn⟩⟩ := mem_coeffs_iff.mp hc
    exact hn ▸ h n
  · intro h n
    by_cases hn : p.coeff n = 0
    · exact ⟨0, by simp [hn]⟩
    · exact h <| coeff_mem_coeffs _ _ hn

/-- If `(r : R)`, then `C (f r)` lifts. -/
theorem C_mem_lifts (f : R →+* S) (r : R) : C (f r) ∈ lifts f :=
  ⟨C r, by
    simp only [coe_mapRingHom, map_C, Set.mem_univ, Subsemiring.coe_top, eq_self_iff_true,
      and_self_iff]⟩

/-- If `(s : S)` is in the image of `f`, then `C s` lifts. -/
theorem C'_mem_lifts {f : R →+* S} {s : S} (h : s ∈ Set.range f) : C s ∈ lifts f := by
  obtain ⟨r, rfl⟩ := Set.mem_range.1 h
  use C r
  simp only [coe_mapRingHom, map_C, Set.mem_univ, Subsemiring.coe_top, eq_self_iff_true,
    and_self_iff]

/-- The polynomial `X` lifts. -/
theorem X_mem_lifts (f : R →+* S) : (X : S[X]) ∈ lifts f :=
  ⟨X, by
    simp only [coe_mapRingHom, Set.mem_univ, Subsemiring.coe_top, eq_self_iff_true, map_X,
      and_self_iff]⟩

/-- The polynomial `X ^ n` lifts. -/
theorem X_pow_mem_lifts (f : R →+* S) (n : ℕ) : (X ^ n : S[X]) ∈ lifts f :=
  ⟨X ^ n, by
    simp only [coe_mapRingHom, map_pow, Set.mem_univ, Subsemiring.coe_top, eq_self_iff_true,
      map_X, and_self_iff]⟩

/-- If `p` lifts and `(r : R)` then `r * p` lifts. -/
theorem base_mul_mem_lifts {p : S[X]} (r : R) (hp : p ∈ lifts f) : C (f r) * p ∈ lifts f := by
  simp only [lifts, RingHom.mem_rangeS] at hp ⊢
  obtain ⟨p₁, rfl⟩ := hp
  use C r * p₁
  simp only [coe_mapRingHom, map_C, map_mul]

/-- If `(s : S)` is in the image of `f`, then `monomial n s` lifts. -/
theorem monomial_mem_lifts {s : S} (n : ℕ) (h : s ∈ Set.range f) : monomial n s ∈ lifts f := by
  obtain ⟨r, rfl⟩ := Set.mem_range.1 h
  use monomial n r
  simp only [coe_mapRingHom, Set.mem_univ, map_monomial, Subsemiring.coe_top, eq_self_iff_true,
    and_self_iff]

/-- If `p` lifts then `p.erase n` lifts. -/
theorem erase_mem_lifts {p : S[X]} (n : ℕ) (h : p ∈ lifts f) : p.erase n ∈ lifts f := by
  rw [lifts_iff_ringHom_rangeS, mem_map_rangeS] at h ⊢
  intro k
  by_cases hk : k = n
  · use 0
    simp only [hk, RingHom.map_zero, erase_same]
  obtain ⟨i, hi⟩ := h k
  use i
  simp only [hi, hk, erase_ne, Ne, not_false_iff]

section LiftDeg

theorem monomial_mem_lifts_and_degree_eq {s : S} {n : ℕ} (hl : monomial n s ∈ lifts f) :
    ∃ q : R[X], map f q = monomial n s ∧ q.degree = (monomial n s).degree := by
  rcases eq_or_ne s 0 with rfl | h
  · exact ⟨0, by simp⟩
  obtain ⟨a, rfl⟩ := coeff_monomial_same n s ▸ (monomial n s).lifts_iff_coeff_lifts.mp hl n
  refine ⟨monomial n a, map_monomial f, ?_⟩
  rw [degree_monomial, degree_monomial n h]
  exact mt (fun ha ↦ ha ▸ map_zero f) h

/-- A polynomial lifts if and only if it can be lifted to a polynomial of the same degree. -/
theorem mem_lifts_and_degree_eq {p : S[X]} (hlifts : p ∈ lifts f) :
    ∃ q : R[X], map f q = p ∧ q.degree = p.degree := by
  rw [lifts_iff_coeff_lifts] at hlifts
  let g : ℕ → R := fun k ↦ (hlifts k).choose
  have hg : ∀ k, f (g k) = p.coeff k := fun k ↦ (hlifts k).choose_spec
  let q : R[X] := ∑ k ∈ p.support, monomial k (g k)
  have hq : map f q = p := by simp_rw [q, Polynomial.map_sum, map_monomial, hg, ← as_sum_support]
  have hq' : q.support = p.support := by
    simp_rw [Finset.ext_iff, mem_support_iff, q, finset_sum_coeff, coeff_monomial,
      Finset.sum_ite_eq', ite_ne_right_iff, mem_support_iff, and_iff_left_iff_imp, not_imp_not]
    exact fun k h ↦ by rw [← hg, h, map_zero]
  exact ⟨q, hq, congrArg Finset.max hq'⟩

end LiftDeg

section Monic

/-- A monic polynomial lifts if and only if it can be lifted to a monic polynomial
of the same degree. -/
theorem lifts_and_degree_eq_and_monic [Nontrivial S] {p : S[X]} (hlifts : p ∈ lifts f)
    (hp : p.Monic) : ∃ q : R[X], map f q = p ∧ q.degree = p.degree ∧ q.Monic := by
  rw [lifts_iff_coeff_lifts] at hlifts
  let g : ℕ → R := fun k ↦ (hlifts k).choose
  have hg k : f (g k) = p.coeff k := (hlifts k).choose_spec
  let q : R[X] := X ^ p.natDegree + ∑ k ∈ Finset.range p.natDegree, C (g k) * X ^ k
  have hq : map f q = p := by
    simp_rw [q, Polynomial.map_add, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow,
      map_X, map_C, hg, ← hp.as_sum]
  have h : q.Monic := monic_X_pow_add (by simp_rw [← Fin.sum_univ_eq_sum_range, degree_sum_fin_lt])
  exact ⟨q, hq, hq ▸ (h.degree_map f).symm, h⟩

theorem lifts_and_natDegree_eq_and_monic {p : S[X]} (hlifts : p ∈ lifts f) (hp : p.Monic) :
    ∃ q : R[X], map f q = p ∧ q.natDegree = p.natDegree ∧ q.Monic := by
  rcases subsingleton_or_nontrivial S with hR | hR
  · obtain rfl : p = 1 := Subsingleton.elim _ _
    exact ⟨1, Subsingleton.elim _ _, by simp, by simp⟩
  obtain ⟨p', h₁, h₂, h₃⟩ := lifts_and_degree_eq_and_monic hlifts hp
  exact ⟨p', h₁, natDegree_eq_of_degree_eq h₂, h₃⟩

end Monic

end Semiring

section Ring

variable {R : Type u} [Ring R] {S : Type v} [Ring S] (f : R →+* S)

/-- The subring of polynomials that lift. -/
def liftsRing (f : R →+* S) : Subring S[X] :=
  RingHom.range (mapRingHom f)

/-- If `R` and `S` are rings, `p` is in the subring of polynomials that lift if and only if it is in
the subsemiring of polynomials that lift. -/
theorem lifts_iff_liftsRing (p : S[X]) : p ∈ lifts f ↔ p ∈ liftsRing f := by
  simp only [lifts, liftsRing, RingHom.mem_range, RingHom.mem_rangeS]

end Ring

section Algebra

variable {R : Type u} [CommSemiring R] {S : Type v} [Semiring S] [Algebra R S]

/-- The map `R[X] → S[X]` as an algebra homomorphism. -/
def mapAlg (R : Type u) [CommSemiring R] (S : Type v) [Semiring S] [Algebra R S] :
    R[X] →ₐ[R] S[X] :=
  @aeval _ S[X] _ _ _ (X : S[X])

/-- `mapAlg` is the morphism induced by `R → S`. -/
theorem mapAlg_eq_map (p : R[X]) : mapAlg R S p = map (algebraMap R S) p := by
  simp only [mapAlg, aeval_def, eval₂_eq_sum, map, algebraMap_apply, RingHom.coe_comp]
  ext; congr

/-- A polynomial `p` lifts if and only if it is in the image of `mapAlg`. -/
theorem mem_lifts_iff_mem_alg (R : Type u) [CommSemiring R] {S : Type v} [Semiring S] [Algebra R S]
    (p : S[X]) : p ∈ lifts (algebraMap R S) ↔ p ∈ AlgHom.range (@mapAlg R _ S _ _) := by
  simp only [coe_mapRingHom, lifts, mapAlg_eq_map, AlgHom.mem_range, RingHom.mem_rangeS]

/-- If `p` lifts and `(r : R)` then `r • p` lifts. -/
theorem smul_mem_lifts {p : S[X]} (r : R) (hp : p ∈ lifts (algebraMap R S)) :
    r • p ∈ lifts (algebraMap R S) := by
  rw [mem_lifts_iff_mem_alg] at hp ⊢
  exact Subalgebra.smul_mem (mapAlg R S).range hp r

theorem monic_of_monic_mapAlg [FaithfulSMul R S] {p : Polynomial R} (hp : (mapAlg R S p).Monic) :
    p.Monic :=
  monic_of_injective (FaithfulSMul.algebraMap_injective R S) hp

end Algebra

end Polynomial
