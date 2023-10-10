/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Eric Wieser
-/
import Mathlib.Algebra.DirectSum.Internal
import Mathlib.Algebra.GradedMonoid
import Mathlib.Data.MvPolynomial.Variables
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

#align_import ring_theory.mv_polynomial.homogeneous from "leanprover-community/mathlib"@"2f5b500a507264de86d666a5f87ddb976e2d8de4"

/-!
# Homogeneous polynomials

A multivariate polynomial `φ` is homogeneous of degree `n`
if all monomials occurring in `φ` have degree `n`.

## Main definitions/lemmas

* `IsHomogeneous φ n`: a predicate that asserts that `φ` is homogeneous of degree `n`.
* `homogeneousSubmodule σ R n`: the submodule of homogeneous polynomials of degree `n`.
* `homogeneousComponent n`: the additive morphism that projects polynomials onto
  their summand that is homogeneous of degree `n`.
* `sum_homogeneousComponent`: every polynomial is the sum of its homogeneous components.

-/


open BigOperators

namespace MvPolynomial

variable {σ : Type*} {τ : Type*} {R : Type*} {S : Type*}

/-
TODO
* show that `MvPolynomial σ R ≃ₐ[R] ⨁ i, homogeneousSubmodule σ R i`
-/

/-- The degree of a monomial. -/
def degree (d : σ →₀ ℕ) := ∑ i in d.support, d i

theorem degree_eq_weightedDegree (d : σ →₀ ℕ) :
    ∑ i in d.support, d i = weightedDegree 1 d := by
  simp [weightedDegree, Finsupp.total, Finsupp.sum]

/-- A multivariate polynomial `φ` is homogeneous of degree `n`
if all monomials occurring in `φ` have degree `n`. -/
def IsHomogeneous [CommSemiring R] (φ : MvPolynomial σ R) (n : ℕ) :=
  IsWeightedHomogeneous 1 φ n
#align mv_polynomial.is_homogeneous MvPolynomial.IsHomogeneous

variable [CommSemiring R]

theorem totalDegree_eq_weightedTotalDegree (φ : MvPolynomial σ R) :
    φ.totalDegree = weightedTotalDegree (1 : σ → ℕ) φ := by
  simp only [totalDegree, weightedTotalDegree, weightedDegree, LinearMap.toAddMonoidHom_coe,
    Finsupp.total, Pi.one_apply, Finsupp.coe_lsum, LinearMap.coe_smulRight, LinearMap.id_coe,
    id.def, Algebra.id.smul_eq_mul, mul_one]

variable (σ R)

/-- The submodule of homogeneous `MvPolynomial`s of degree `n`. -/
def homogeneousSubmodule (n : ℕ) : Submodule R (MvPolynomial σ R) where
  carrier := { x | x.IsHomogeneous n }
  smul_mem' r a ha c hc := by
    rw [coeff_smul] at hc
    apply ha
    intro h
    apply hc
    rw [h]
    exact smul_zero r
  zero_mem' d hd := False.elim (hd <| coeff_zero _)
  add_mem' {a b} ha hb c hc := by
    rw [coeff_add] at hc
    obtain h | h : coeff c a ≠ 0 ∨ coeff c b ≠ 0 := by
      contrapose! hc
      simp only [hc, add_zero]
    · exact ha h
    · exact hb h
#align mv_polynomial.homogeneous_submodule MvPolynomial.homogeneousSubmodule

variable {σ R}

@[simp]
theorem mem_homogeneousSubmodule [CommSemiring R] (n : ℕ) (p : MvPolynomial σ R) :
    p ∈ homogeneousSubmodule σ R n ↔ p.IsHomogeneous n := Iff.rfl
#align mv_polynomial.mem_homogeneous_submodule MvPolynomial.mem_homogeneousSubmodule

variable (σ R)

/-- While equal, the former has a convenient definitional reduction. -/
theorem homogeneousSubmodule_eq_finsupp_supported [CommSemiring R] (n : ℕ) :
    homogeneousSubmodule σ R n = Finsupp.supported _ R { d | ∑ i in d.support, d i = n } := by
  simp_rw [degree_eq_weightedDegree]
  exact weightedHomogeneousSubmodule_eq_finsupp_supported R 1 n
#align mv_polynomial.homogeneous_submodule_eq_finsupp_supported MvPolynomial.homogeneousSubmodule_eq_finsupp_supported

variable {σ R}

theorem homogeneousSubmodule_mul [CommSemiring R] (m n : ℕ) :
    homogeneousSubmodule σ R m * homogeneousSubmodule σ R n ≤ homogeneousSubmodule σ R (m + n) :=
  weightedHomogeneousSubmodule_mul 1 m n
#align mv_polynomial.homogeneous_submodule_mul MvPolynomial.homogeneousSubmodule_mul

section

variable [CommSemiring R]

theorem isHomogeneous_monomial (d : σ →₀ ℕ) (r : R) (n : ℕ) (hn : ∑ i in d.support, d i = n) :
    IsHomogeneous (monomial d r) n := by
  simp_rw [degree_eq_weightedDegree] at hn
  exact isWeightedHomogeneous_monomial 1 d r hn
#align mv_polynomial.is_homogeneous_monomial MvPolynomial.isHomogeneous_monomial

variable (σ)

theorem isHomogeneous_of_totalDegree_zero_iff {p : MvPolynomial σ R} :
    p.totalDegree = 0 ↔ IsHomogeneous p 0 := by
  rw [totalDegree_eq_weightedTotalDegree,
    ← isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero, IsHomogeneous]

theorem isHomogeneous_of_totalDegree_zero {p : MvPolynomial σ R} (hp : p.totalDegree = 0) :
    IsHomogeneous p 0 :=
  (isHomogeneous_of_totalDegree_zero_iff _).mp hp
#align mv_polynomial.is_homogeneous_of_total_degree_zero MvPolynomial.isHomogeneous_of_totalDegree_zero

theorem isHomogeneous_C (r : R) : IsHomogeneous (C r : MvPolynomial σ R) 0 := by
  apply isHomogeneous_monomial
  simp only [Finsupp.zero_apply, Finset.sum_const_zero]
set_option linter.uppercaseLean3 false in
#align mv_polynomial.is_homogeneous_C MvPolynomial.isHomogeneous_C

variable (R)

theorem isHomogeneous_zero (n : ℕ) : IsHomogeneous (0 : MvPolynomial σ R) n :=
  (homogeneousSubmodule σ R n).zero_mem
#align mv_polynomial.is_homogeneous_zero MvPolynomial.isHomogeneous_zero

theorem isHomogeneous_one : IsHomogeneous (1 : MvPolynomial σ R) 0 :=
  isHomogeneous_C _ _
#align mv_polynomial.is_homogeneous_one MvPolynomial.isHomogeneous_one

variable {σ}

theorem isHomogeneous_X (i : σ) : IsHomogeneous (X i : MvPolynomial σ R) 1 := by
  apply isHomogeneous_monomial
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton]
  exact Finsupp.single_eq_same
set_option linter.uppercaseLean3 false in
#align mv_polynomial.is_homogeneous_X MvPolynomial.isHomogeneous_X

end

namespace IsHomogeneous

variable [CommSemiring R] {φ ψ : MvPolynomial σ R} {m n : ℕ}

theorem coeff_eq_zero (hφ : IsHomogeneous φ n) (d : σ →₀ ℕ) (hd : ∑ i in d.support, d i ≠ n) :
    coeff d φ = 0 := by
  simp_rw [degree_eq_weightedDegree] at hd
  exact IsWeightedHomogeneous.coeff_eq_zero hφ d hd
#align mv_polynomial.is_homogeneous.coeff_eq_zero MvPolynomial.IsHomogeneous.coeff_eq_zero

theorem inj_right (hm : IsHomogeneous φ m) (hn : IsHomogeneous φ n) (hφ : φ ≠ 0) : m = n := by
  obtain ⟨d, hd⟩ : ∃ d, coeff d φ ≠ 0 := exists_coeff_ne_zero hφ
  rw [← hm hd, ← hn hd]
#align mv_polynomial.is_homogeneous.inj_right MvPolynomial.IsHomogeneous.inj_right

theorem add (hφ : IsHomogeneous φ n) (hψ : IsHomogeneous ψ n) : IsHomogeneous (φ + ψ) n :=
  (homogeneousSubmodule σ R n).add_mem hφ hψ
#align mv_polynomial.is_homogeneous.add MvPolynomial.IsHomogeneous.add

theorem sum {ι : Type*} (s : Finset ι) (φ : ι → MvPolynomial σ R) (n : ℕ)
    (h : ∀ i ∈ s, IsHomogeneous (φ i) n) : IsHomogeneous (∑ i in s, φ i) n :=
  (homogeneousSubmodule σ R n).sum_mem h
#align mv_polynomial.is_homogeneous.sum MvPolynomial.IsHomogeneous.sum

theorem mul (hφ : IsHomogeneous φ m) (hψ : IsHomogeneous ψ n) : IsHomogeneous (φ * ψ) (m + n) :=
  homogeneousSubmodule_mul m n <| Submodule.mul_mem_mul hφ hψ
#align mv_polynomial.is_homogeneous.mul MvPolynomial.IsHomogeneous.mul

theorem prod {ι : Type*} (s : Finset ι) (φ : ι → MvPolynomial σ R) (n : ι → ℕ)
    (h : ∀ i ∈ s, IsHomogeneous (φ i) (n i)) : IsHomogeneous (∏ i in s, φ i) (∑ i in s, n i) := by
  classical
  revert h
  refine' Finset.induction_on s _ _
  · intro
    simp only [isHomogeneous_one, Finset.sum_empty, Finset.prod_empty]
  · intro i s his IH h
    simp only [his, Finset.prod_insert, Finset.sum_insert, not_false_iff]
    apply (h i (Finset.mem_insert_self _ _)).mul (IH _)
    intro j hjs
    exact h j (Finset.mem_insert_of_mem hjs)
#align mv_polynomial.is_homogeneous.prod MvPolynomial.IsHomogeneous.prod

theorem totalDegree (hφ : IsHomogeneous φ n) (h : φ ≠ 0) : totalDegree φ = n := by
  rw [totalDegree_eq_weightedTotalDegree, ← WithBot.coe_eq_coe, ←
    weightedTotalDegree_coe _ φ h, IsWeightedHomogeneous.weighted_total_degree hφ h]
#align mv_polynomial.is_homogeneous.total_degree MvPolynomial.IsHomogeneous.totalDegree

/-- The homogeneous submodules form a graded ring. This instance is used by `DirectSum.commSemiring`
and `DirectSum.algebra`. -/
instance HomogeneousSubmodule.gcommSemiring : SetLike.GradedMonoid (homogeneousSubmodule σ R) where
  one_mem := isHomogeneous_one σ R
  mul_mem _ _ _ _ := IsHomogeneous.mul
#align mv_polynomial.is_homogeneous.homogeneous_submodule.gcomm_semiring MvPolynomial.IsHomogeneous.HomogeneousSubmodule.gcommSemiring

open DirectSum

noncomputable example : CommSemiring (⨁ i, homogeneousSubmodule σ R i) :=
  inferInstance

noncomputable example : Algebra R (⨁ i, homogeneousSubmodule σ R i) :=
  inferInstance

end IsHomogeneous

noncomputable section

open Finset

/-- `homogeneousComponent n φ` is the part of `φ` that is homogeneous of degree `n`.
See `sum_homogeneousComponent` for the statement that `φ` is equal to the sum
of all its homogeneous components. -/
def homogeneousComponent [CommSemiring R] (n : ℕ) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  weightedHomogeneousComponent 1 n
#align mv_polynomial.homogeneous_component MvPolynomial.homogeneousComponent

section HomogeneousComponent

open Finset

variable [CommSemiring R] (n : ℕ) (φ ψ : MvPolynomial σ R)

theorem coeff_homogeneousComponent (d : σ →₀ ℕ) :
    coeff d (homogeneousComponent n φ) = if (∑ i in d.support, d i) = n then coeff d φ else 0 := by
  simp_rw [degree_eq_weightedDegree]
  convert coeff_weightedHomogeneousComponent n φ d
#align mv_polynomial.coeff_homogeneous_component MvPolynomial.coeff_homogeneousComponent

theorem homogeneousComponent_apply :
    homogeneousComponent n φ =
      ∑ d in φ.support.filter fun d => ∑ i in d.support, d i = n, monomial d (coeff d φ) := by
  simp_rw [degree_eq_weightedDegree]
  convert weightedHomogeneousComponent_apply n φ
#align mv_polynomial.homogeneous_component_apply MvPolynomial.homogeneousComponent_apply

theorem homogeneousComponent_isHomogeneous : (homogeneousComponent n φ).IsHomogeneous n :=
  weightedHomogeneousComponent_isWeightedHomogeneous n φ
#align mv_polynomial.homogeneous_component_is_homogeneous MvPolynomial.homogeneousComponent_isHomogeneous

@[simp]
theorem homogeneousComponent_zero : homogeneousComponent 0 φ = C (coeff 0 φ) :=
  weightedHomogeneousComponent_zero φ (fun _ => Nat.succ_ne_zero Nat.zero)
#align mv_polynomial.homogeneous_component_zero MvPolynomial.homogeneousComponent_zero

@[simp]
theorem homogeneousComponent_C_mul (n : ℕ) (r : R) :
    homogeneousComponent n (C r * φ) = C r * homogeneousComponent n φ :=
  weightedHomogeneousComponent_C_mul φ n r
set_option linter.uppercaseLean3 false in
#align mv_polynomial.homogeneous_component_C_mul MvPolynomial.homogeneousComponent_C_mul

theorem homogeneousComponent_eq_zero'
    (h : ∀ d : σ →₀ ℕ, d ∈ φ.support → ∑ i in d.support, d i ≠ n) :
    homogeneousComponent n φ = 0 := by
  simp_rw [degree_eq_weightedDegree] at h
  exact weightedHomogeneousComponent_eq_zero' n φ h
#align mv_polynomial.homogeneous_component_eq_zero' MvPolynomial.homogeneousComponent_eq_zero'

theorem homogeneousComponent_eq_zero (h : φ.totalDegree < n) : homogeneousComponent n φ = 0 := by
  apply homogeneousComponent_eq_zero'
  rw [totalDegree, Finset.sup_lt_iff] at h
  · intro d hd; exact ne_of_lt (h d hd)
  · exact lt_of_le_of_lt (Nat.zero_le _) h
#align mv_polynomial.homogeneous_component_eq_zero MvPolynomial.homogeneousComponent_eq_zero

theorem sum_homogeneousComponent :
    (∑ i in range (φ.totalDegree + 1), homogeneousComponent i φ) = φ := by
  ext1 d
  suffices φ.totalDegree < d.support.sum d → 0 = coeff d φ by
    simpa [coeff_sum, coeff_homogeneousComponent]
  exact fun h => (coeff_eq_zero_of_totalDegree_lt h).symm
#align mv_polynomial.sum_homogeneous_component MvPolynomial.sum_homogeneousComponent

theorem homogeneousComponent_homogeneous_polynomial (m n : ℕ) (p : MvPolynomial σ R)
    (h : p ∈ homogeneousSubmodule σ R n) : homogeneousComponent m p = if m = n then p else 0 := by
  convert weightedHomogeneousComponent_weighted_homogeneous_polynomial m n p h
#align mv_polynomial.homogeneous_component_homogeneous_polynomial MvPolynomial.homogeneousComponent_homogeneous_polynomial

end HomogeneousComponent

end

end MvPolynomial
