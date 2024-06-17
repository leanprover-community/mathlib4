/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Monic

#align_import data.polynomial.lifts from "leanprover-community/mathlib"@"63417e01fbc711beaf25fa73b6edb395c0cfddd0"

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
#align polynomial.lifts Polynomial.lifts

theorem mem_lifts (p : S[X]) : p ∈ lifts f ↔ ∃ q : R[X], map f q = p := by
  simp only [coe_mapRingHom, lifts, RingHom.mem_rangeS]
#align polynomial.mem_lifts Polynomial.mem_lifts

theorem lifts_iff_set_range (p : S[X]) : p ∈ lifts f ↔ p ∈ Set.range (map f) := by
  simp only [coe_mapRingHom, lifts, Set.mem_range, RingHom.mem_rangeS]
#align polynomial.lifts_iff_set_range Polynomial.lifts_iff_set_range

theorem lifts_iff_ringHom_rangeS (p : S[X]) : p ∈ lifts f ↔ p ∈ (mapRingHom f).rangeS := by
  simp only [coe_mapRingHom, lifts, Set.mem_range, RingHom.mem_rangeS]
#align polynomial.lifts_iff_ring_hom_srange Polynomial.lifts_iff_ringHom_rangeS

theorem lifts_iff_coeff_lifts (p : S[X]) : p ∈ lifts f ↔ ∀ n : ℕ, p.coeff n ∈ Set.range f := by
  rw [lifts_iff_ringHom_rangeS, mem_map_rangeS f]
  rfl
#align polynomial.lifts_iff_coeff_lifts Polynomial.lifts_iff_coeff_lifts

/-- If `(r : R)`, then `C (f r)` lifts. -/
theorem C_mem_lifts (f : R →+* S) (r : R) : C (f r) ∈ lifts f :=
  ⟨C r, by
    simp only [coe_mapRingHom, map_C, Set.mem_univ, Subsemiring.coe_top, eq_self_iff_true,
      and_self_iff]⟩
set_option linter.uppercaseLean3 false in
#align polynomial.C_mem_lifts Polynomial.C_mem_lifts

/-- If `(s : S)` is in the image of `f`, then `C s` lifts. -/
theorem C'_mem_lifts {f : R →+* S} {s : S} (h : s ∈ Set.range f) : C s ∈ lifts f := by
  obtain ⟨r, rfl⟩ := Set.mem_range.1 h
  use C r
  simp only [coe_mapRingHom, map_C, Set.mem_univ, Subsemiring.coe_top, eq_self_iff_true,
    and_self_iff]
set_option linter.uppercaseLean3 false in
#align polynomial.C'_mem_lifts Polynomial.C'_mem_lifts

/-- The polynomial `X` lifts. -/
theorem X_mem_lifts (f : R →+* S) : (X : S[X]) ∈ lifts f :=
  ⟨X, by
    simp only [coe_mapRingHom, Set.mem_univ, Subsemiring.coe_top, eq_self_iff_true, map_X,
      and_self_iff]⟩
set_option linter.uppercaseLean3 false in
#align polynomial.X_mem_lifts Polynomial.X_mem_lifts

/-- The polynomial `X ^ n` lifts. -/
theorem X_pow_mem_lifts (f : R →+* S) (n : ℕ) : (X ^ n : S[X]) ∈ lifts f :=
  ⟨X ^ n, by
    simp only [coe_mapRingHom, map_pow, Set.mem_univ, Subsemiring.coe_top, eq_self_iff_true,
      map_X, and_self_iff]⟩
set_option linter.uppercaseLean3 false in
#align polynomial.X_pow_mem_lifts Polynomial.X_pow_mem_lifts

/-- If `p` lifts and `(r : R)` then `r * p` lifts. -/
theorem base_mul_mem_lifts {p : S[X]} (r : R) (hp : p ∈ lifts f) : C (f r) * p ∈ lifts f := by
  simp only [lifts, RingHom.mem_rangeS] at hp ⊢
  obtain ⟨p₁, rfl⟩ := hp
  use C r * p₁
  simp only [coe_mapRingHom, map_C, map_mul]
#align polynomial.base_mul_mem_lifts Polynomial.base_mul_mem_lifts

/-- If `(s : S)` is in the image of `f`, then `monomial n s` lifts. -/
theorem monomial_mem_lifts {s : S} (n : ℕ) (h : s ∈ Set.range f) : monomial n s ∈ lifts f := by
  obtain ⟨r, rfl⟩ := Set.mem_range.1 h
  use monomial n r
  simp only [coe_mapRingHom, Set.mem_univ, map_monomial, Subsemiring.coe_top, eq_self_iff_true,
    and_self_iff]
#align polynomial.monomial_mem_lifts Polynomial.monomial_mem_lifts

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
#align polynomial.erase_mem_lifts Polynomial.erase_mem_lifts

section LiftDeg

theorem monomial_mem_lifts_and_degree_eq {s : S} {n : ℕ} (hl : monomial n s ∈ lifts f) :
    ∃ q : R[X], map f q = monomial n s ∧ q.degree = (monomial n s).degree := by
  by_cases hzero : s = 0
  · use 0
    simp only [hzero, degree_zero, eq_self_iff_true, and_self_iff, monomial_zero_right,
      Polynomial.map_zero]
  rw [lifts_iff_set_range] at hl
  obtain ⟨q, hq⟩ := hl
  replace hq := (ext_iff.1 hq) n
  have hcoeff : f (q.coeff n) = s := by
    simp? [coeff_monomial] at hq says simp only [coeff_map, coeff_monomial, ↓reduceIte] at hq
    exact hq
  use monomial n (q.coeff n)
  constructor
  · simp only [hcoeff, map_monomial]
  have hqzero : q.coeff n ≠ 0 := by
    intro habs
    simp only [habs, RingHom.map_zero] at hcoeff
    exact hzero hcoeff.symm
  rw [← C_mul_X_pow_eq_monomial]
  rw [← C_mul_X_pow_eq_monomial]
  simp only [hzero, hqzero, Ne, not_false_iff, degree_C_mul_X_pow]
#align polynomial.monomial_mem_lifts_and_degree_eq Polynomial.monomial_mem_lifts_and_degree_eq

/-- A polynomial lifts if and only if it can be lifted to a polynomial of the same degree. -/
theorem mem_lifts_and_degree_eq {p : S[X]} (hlifts : p ∈ lifts f) :
    ∃ q : R[X], map f q = p ∧ q.degree = p.degree := by
  generalize hd : p.natDegree = d
  revert hd p
  induction' d using Nat.strong_induction_on with n hn
  intros p hlifts hdeg
  by_cases erase_zero : p.eraseLead = 0
  · rw [← eraseLead_add_monomial_natDegree_leadingCoeff p, erase_zero, zero_add, leadingCoeff]
    exact
      monomial_mem_lifts_and_degree_eq
        (monomial_mem_lifts p.natDegree ((lifts_iff_coeff_lifts p).1 hlifts p.natDegree))
  have deg_erase := Or.resolve_right (eraseLead_natDegree_lt_or_eraseLead_eq_zero p) erase_zero
  have pzero : p ≠ 0 := by
    intro habs
    exfalso
    rw [habs, eraseLead_zero, eq_self_iff_true, not_true] at erase_zero
    exact erase_zero
  have lead_zero : p.coeff p.natDegree ≠ 0 := by
    rw [← leadingCoeff, Ne, leadingCoeff_eq_zero]; exact pzero
  obtain ⟨lead, hlead⟩ :=
    monomial_mem_lifts_and_degree_eq
      (monomial_mem_lifts p.natDegree ((lifts_iff_coeff_lifts p).1 hlifts p.natDegree))
  have deg_lead : lead.degree = p.natDegree := by
    rw [hlead.2, ← C_mul_X_pow_eq_monomial, degree_C_mul_X_pow p.natDegree lead_zero]
  rw [hdeg] at deg_erase
  obtain ⟨erase, herase⟩ :=
    hn p.eraseLead.natDegree deg_erase (erase_mem_lifts p.natDegree hlifts)
      (refl p.eraseLead.natDegree)
  use erase + lead
  constructor
  · simp only [hlead, herase, Polynomial.map_add]
    rw [← eraseLead, ← leadingCoeff]
    rw [eraseLead_add_monomial_natDegree_leadingCoeff p]
  rw [degree_eq_natDegree pzero, ← deg_lead]
  apply degree_add_eq_right_of_degree_lt
  rw [herase.2, deg_lead, ← degree_eq_natDegree pzero]
  exact degree_erase_lt pzero
#align polynomial.mem_lifts_and_degree_eq Polynomial.mem_lifts_and_degree_eq

end LiftDeg

section Monic

/-- A monic polynomial lifts if and only if it can be lifted to a monic polynomial
of the same degree. -/
theorem lifts_and_degree_eq_and_monic [Nontrivial S] {p : S[X]} (hlifts : p ∈ lifts f)
    (hp : p.Monic) : ∃ q : R[X], map f q = p ∧ q.degree = p.degree ∧ q.Monic := by
  cases' subsingleton_or_nontrivial R with hR hR
  · obtain ⟨q, hq⟩ := mem_lifts_and_degree_eq hlifts
    exact ⟨q, hq.1, hq.2, monic_of_subsingleton _⟩
  have H : erase p.natDegree p + X ^ p.natDegree = p := by
    simpa only [hp.leadingCoeff, C_1, one_mul, eraseLead] using eraseLead_add_C_mul_X_pow p
  by_cases h0 : erase p.natDegree p = 0
  · rw [← H, h0, zero_add]
    refine ⟨X ^ p.natDegree, ?_, ?_, monic_X_pow p.natDegree⟩
    · rw [Polynomial.map_pow, map_X]
    · rw [degree_X_pow, degree_X_pow]
  obtain ⟨q, hq⟩ := mem_lifts_and_degree_eq (erase_mem_lifts p.natDegree hlifts)
  have p_neq_0 : p ≠ 0 := by intro hp; apply h0; rw [hp]; simp only [natDegree_zero, erase_zero]
  have hdeg : q.degree < ((X : R[X]) ^ p.natDegree).degree := by
    rw [@degree_X_pow R, hq.2, ← degree_eq_natDegree p_neq_0]
    exact degree_erase_lt p_neq_0
  refine ⟨q + X ^ p.natDegree, ?_, ?_, (monic_X_pow _).add_of_right hdeg⟩
  · rw [Polynomial.map_add, hq.1, Polynomial.map_pow, map_X, H]
  · rw [degree_add_eq_right_of_degree_lt hdeg, degree_X_pow, degree_eq_natDegree hp.ne_zero]
#align polynomial.lifts_and_degree_eq_and_monic Polynomial.lifts_and_degree_eq_and_monic

theorem lifts_and_natDegree_eq_and_monic {p : S[X]} (hlifts : p ∈ lifts f) (hp : p.Monic) :
    ∃ q : R[X], map f q = p ∧ q.natDegree = p.natDegree ∧ q.Monic := by
  cases' subsingleton_or_nontrivial S with hR hR
  · obtain rfl : p = 1 := Subsingleton.elim _ _
    exact ⟨1, Subsingleton.elim _ _, by simp, by simp⟩
  obtain ⟨p', h₁, h₂, h₃⟩ := lifts_and_degree_eq_and_monic hlifts hp
  exact ⟨p', h₁, natDegree_eq_of_degree_eq h₂, h₃⟩
#align polynomial.lifts_and_nat_degree_eq_and_monic Polynomial.lifts_and_natDegree_eq_and_monic

end Monic

end Semiring

section Ring

variable {R : Type u} [Ring R] {S : Type v} [Ring S] (f : R →+* S)

/-- The subring of polynomials that lift. -/
def liftsRing (f : R →+* S) : Subring S[X] :=
  RingHom.range (mapRingHom f)
#align polynomial.lifts_ring Polynomial.liftsRing

/-- If `R` and `S` are rings, `p` is in the subring of polynomials that lift if and only if it is in
the subsemiring of polynomials that lift. -/
theorem lifts_iff_liftsRing (p : S[X]) : p ∈ lifts f ↔ p ∈ liftsRing f := by
  simp only [lifts, liftsRing, RingHom.mem_range, RingHom.mem_rangeS]
#align polynomial.lifts_iff_lifts_ring Polynomial.lifts_iff_liftsRing

end Ring

section Algebra

variable {R : Type u} [CommSemiring R] {S : Type v} [Semiring S] [Algebra R S]

/-- The map `R[X] → S[X]` as an algebra homomorphism. -/
def mapAlg (R : Type u) [CommSemiring R] (S : Type v) [Semiring S] [Algebra R S] :
    R[X] →ₐ[R] S[X] :=
  @aeval _ S[X] _ _ _ (X : S[X])
#align polynomial.map_alg Polynomial.mapAlg

/-- `mapAlg` is the morphism induced by `R → S`. -/
theorem mapAlg_eq_map (p : R[X]) : mapAlg R S p = map (algebraMap R S) p := by
  simp only [mapAlg, aeval_def, eval₂_eq_sum, map, algebraMap_apply, RingHom.coe_comp]
  ext; congr
#align polynomial.map_alg_eq_map Polynomial.mapAlg_eq_map

/-- A polynomial `p` lifts if and only if it is in the image of `mapAlg`. -/
theorem mem_lifts_iff_mem_alg (R : Type u) [CommSemiring R] {S : Type v} [Semiring S] [Algebra R S]
    (p : S[X]) : p ∈ lifts (algebraMap R S) ↔ p ∈ AlgHom.range (@mapAlg R _ S _ _) := by
  simp only [coe_mapRingHom, lifts, mapAlg_eq_map, AlgHom.mem_range, RingHom.mem_rangeS]
#align polynomial.mem_lifts_iff_mem_alg Polynomial.mem_lifts_iff_mem_alg

/-- If `p` lifts and `(r : R)` then `r • p` lifts. -/
theorem smul_mem_lifts {p : S[X]} (r : R) (hp : p ∈ lifts (algebraMap R S)) :
    r • p ∈ lifts (algebraMap R S) := by
  rw [mem_lifts_iff_mem_alg] at hp ⊢
  exact Subalgebra.smul_mem (mapAlg R S).range hp r
#align polynomial.smul_mem_lifts Polynomial.smul_mem_lifts

end Algebra

end Polynomial
