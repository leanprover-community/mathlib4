/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import Mathlib.Algebra.GradedMonoid
import Mathlib.Data.MvPolynomial.Variables

#align_import ring_theory.mv_polynomial.weighted_homogeneous from "leanprover-community/mathlib"@"2f5b500a507264de86d666a5f87ddb976e2d8de4"

/-!
# Weighted homogeneous polynomials

It is possible to assign weights (in a commutative additive monoid `M`) to the variables of a
multivariate polynomial ring, so that monomials of the ring then have a weighted degree with
respect to the weights of the variables. The weights are represented by a function `w : σ → M`,
where `σ` are the indeterminates.

A multivariate polynomial `φ` is weighted homogeneous of weighted degree `m : M` if all monomials
occurring in `φ` have the same weighted degree `m`.

## Main definitions/lemmas

* `weightedTotalDegree' w φ` : the weighted total degree of a multivariate polynomial with respect
to the weights `w`, taking values in `WithBot M`.

* `weightedTotalDegree w φ` : When `M` has a `⊥` element, we can define the weighted total degree
of a multivariate polynomial as a function taking values in `M`.

* `IsWeightedHomogeneous w φ m`: a predicate that asserts that `φ` is weighted homogeneous
of weighted degree `m` with respect to the weights `w`.

* `weightedHomogeneousSubmodule R w m`: the submodule of homogeneous polynomials
of weighted degree `m`.

* `weightedHomogeneousComponent w m`: the additive morphism that projects polynomials
onto their summand that is weighted homogeneous of degree `n` with respect to `w`.

* `sum_weightedHomogeneousComponent`: every polynomial is the sum of its weighted homogeneous
components.
-/


noncomputable section

open BigOperators

open Set Function Finset Finsupp AddMonoidAlgebra

variable {R M : Type*} [CommSemiring R]

namespace MvPolynomial

variable {σ : Type*}

section AddCommMonoid

variable [AddCommMonoid M]

/-! ### `weightedDegree'` -/


/-- The `weightedDegree'` of the finitely supported function `s : σ →₀ ℕ` is the sum
  `∑(s i)•(w i)`. -/
def weightedDegree' (w : σ → M) : (σ →₀ ℕ) →+ M :=
  (Finsupp.total σ M ℕ w).toAddMonoidHom
#align mv_polynomial.weighted_degree' MvPolynomial.weightedDegree'

section SemilatticeSup

variable [SemilatticeSup M]

/-- The weighted total degree of a multivariate polynomial, taking values in `WithBot M`. -/
def weightedTotalDegree' (w : σ → M) (p : MvPolynomial σ R) : WithBot M :=
  p.support.sup fun s => weightedDegree' w s
#align mv_polynomial.weighted_total_degree' MvPolynomial.weightedTotalDegree'

/-- The `weightedTotalDegree'` of a polynomial `p` is `⊥` if and only if `p = 0`. -/
theorem weightedTotalDegree'_eq_bot_iff (w : σ → M) (p : MvPolynomial σ R) :
    weightedTotalDegree' w p = ⊥ ↔ p = 0 := by
  simp only [weightedTotalDegree', Finset.sup_eq_bot_iff, mem_support_iff, WithBot.coe_ne_bot,
    MvPolynomial.eq_zero_iff]
  exact forall_congr' fun _ => Classical.not_not
  -- 🎉 no goals
#align mv_polynomial.weighted_total_degree'_eq_bot_iff MvPolynomial.weightedTotalDegree'_eq_bot_iff

/-- The `weightedTotalDegree'` of the zero polynomial is `⊥`. -/
theorem weightedTotalDegree'_zero (w : σ → M) : weightedTotalDegree' w (0 : MvPolynomial σ R) = ⊥ :=
  by simp only [weightedTotalDegree', support_zero, Finset.sup_empty]
     -- 🎉 no goals
#align mv_polynomial.weighted_total_degree'_zero MvPolynomial.weightedTotalDegree'_zero

section OrderBot

variable [OrderBot M]

/-- When `M` has a `⊥` element, we can define the weighted total degree of a multivariate
  polynomial as a function taking values in `M`. -/
def weightedTotalDegree (w : σ → M) (p : MvPolynomial σ R) : M :=
  p.support.sup fun s => weightedDegree' w s
#align mv_polynomial.weighted_total_degree MvPolynomial.weightedTotalDegree

/-- This lemma relates `weightedTotalDegree` and `weightedTotalDegree'`. -/
theorem weightedTotalDegree_coe (w : σ → M) (p : MvPolynomial σ R) (hp : p ≠ 0) :
    weightedTotalDegree' w p = ↑(weightedTotalDegree w p) := by
  rw [Ne.def, ← weightedTotalDegree'_eq_bot_iff w p, ← Ne.def, WithBot.ne_bot_iff_exists] at hp
  -- ⊢ weightedTotalDegree' w p = ↑(weightedTotalDegree w p)
  obtain ⟨m, hm⟩ := hp
  -- ⊢ weightedTotalDegree' w p = ↑(weightedTotalDegree w p)
  apply le_antisymm
  -- ⊢ weightedTotalDegree' w p ≤ ↑(weightedTotalDegree w p)
  · simp only [weightedTotalDegree, weightedTotalDegree', Finset.sup_le_iff, WithBot.coe_le_coe]
    -- ⊢ ∀ (b : σ →₀ ℕ), b ∈ support p → ↑(weightedDegree' w) b ≤ sup (support p) fun …
    intro b
    -- ⊢ b ∈ support p → ↑(weightedDegree' w) b ≤ sup (support p) fun s => ↑(weighted …
    exact Finset.le_sup
    -- 🎉 no goals
  · simp only [weightedTotalDegree]
    -- ⊢ ↑(sup (support p) fun s => ↑(weightedDegree' w) s) ≤ weightedTotalDegree' w p
    have hm' : weightedTotalDegree' w p ≤ m := le_of_eq hm.symm
    -- ⊢ ↑(sup (support p) fun s => ↑(weightedDegree' w) s) ≤ weightedTotalDegree' w p
    rw [← hm]
    -- ⊢ ↑(sup (support p) fun s => ↑(weightedDegree' w) s) ≤ ↑m
    simpa [weightedTotalDegree'] using hm'
    -- 🎉 no goals
#align mv_polynomial.weighted_total_degree_coe MvPolynomial.weightedTotalDegree_coe

/-- The `weightedTotalDegree` of the zero polynomial is `⊥`. -/
theorem weightedTotalDegree_zero (w : σ → M) : weightedTotalDegree w (0 : MvPolynomial σ R) = ⊥ :=
  by simp only [weightedTotalDegree, support_zero, Finset.sup_empty]
     -- 🎉 no goals
#align mv_polynomial.weighted_total_degree_zero MvPolynomial.weightedTotalDegree_zero

theorem le_weightedTotalDegree (w : σ → M) {φ : MvPolynomial σ R} {d : σ →₀ ℕ}
    (hd : d ∈ φ.support) : weightedDegree' w d ≤ φ.weightedTotalDegree w :=
  le_sup hd
#align mv_polynomial.le_weighted_total_degree MvPolynomial.le_weightedTotalDegree

end OrderBot

end SemilatticeSup

/-- A multivariate polynomial `φ` is weighted homogeneous of weighted degree `m` if all monomials
  occurring in `φ` have weighted degree `m`. -/
def IsWeightedHomogeneous (w : σ → M) (φ : MvPolynomial σ R) (m : M) : Prop :=
  ∀ ⦃d⦄, coeff d φ ≠ 0 → weightedDegree' w d = m
#align mv_polynomial.is_weighted_homogeneous MvPolynomial.IsWeightedHomogeneous

variable (R)

/-- The submodule of homogeneous `MvPolynomial`s of degree `n`. -/
def weightedHomogeneousSubmodule (w : σ → M) (m : M) : Submodule R (MvPolynomial σ R) where
  carrier := { x | x.IsWeightedHomogeneous w m }
  smul_mem' r a ha c hc := by
    rw [coeff_smul] at hc
    -- ⊢ ↑(weightedDegree' w) c = m
    exact ha (right_ne_zero_of_mul hc)
    -- 🎉 no goals
  zero_mem' d hd := False.elim (hd <| coeff_zero _)
    -- ⊢ ↑(weightedDegree' w) c = m
  add_mem' {a} {b} ha hb c hc := by
    rw [coeff_add] at hc
    obtain h | h : coeff c a ≠ 0 ∨ coeff c b ≠ 0 := by
      contrapose! hc
      -- 🎉 no goals
      simp only [hc, add_zero]
      -- 🎉 no goals
    · exact ha h
    · exact hb h
#align mv_polynomial.weighted_homogeneous_submodule MvPolynomial.weightedHomogeneousSubmodule

@[simp]
theorem mem_weightedHomogeneousSubmodule (w : σ → M) (m : M) (p : MvPolynomial σ R) :
    p ∈ weightedHomogeneousSubmodule R w m ↔ p.IsWeightedHomogeneous w m :=
  Iff.rfl
#align mv_polynomial.mem_weighted_homogeneous_submodule MvPolynomial.mem_weightedHomogeneousSubmodule

/-- The submodule `weightedHomogeneousSubmodule R w m` of homogeneous `MvPolynomial`s of
  degree `n` is equal to the `R`-submodule of all `p : (σ →₀ ℕ) →₀ R` such that
  `p.support ⊆ {d | weightedDegree' w d = m}`. While equal, the former has a
  convenient definitional reduction. -/
theorem weightedHomogeneousSubmodule_eq_finsupp_supported (w : σ → M) (m : M) :
    weightedHomogeneousSubmodule R w m = Finsupp.supported R R { d | weightedDegree' w d = m } := by
  ext x
  -- ⊢ x ∈ weightedHomogeneousSubmodule R w m ↔ x ∈ supported R R {d | ↑(weightedDe …
  rw [mem_supported, Set.subset_def]
  -- ⊢ x ∈ weightedHomogeneousSubmodule R w m ↔ ∀ (x_1 : σ →₀ ℕ), x_1 ∈ ↑x.support  …
  simp only [Finsupp.mem_support_iff, mem_coe]
  -- ⊢ x ∈ weightedHomogeneousSubmodule R w m ↔ ∀ (x_1 : σ →₀ ℕ), ↑x x_1 ≠ 0 → x_1  …
  rfl
  -- 🎉 no goals
#align mv_polynomial.weighted_homogeneous_submodule_eq_finsupp_supported MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported

variable {R}

/-- The submodule generated by products `Pm * Pn` of weighted homogeneous polynomials of degrees `m`
  and `n` is contained in the submodule of weighted homogeneous polynomials of degree `m + n`. -/
theorem weightedHomogeneousSubmodule_mul (w : σ → M) (m n : M) :
    weightedHomogeneousSubmodule R w m * weightedHomogeneousSubmodule R w n ≤
      weightedHomogeneousSubmodule R w (m + n) := by
  classical
  rw [Submodule.mul_le]
  intro φ hφ ψ hψ c hc
  rw [coeff_mul] at hc
  obtain ⟨⟨d, e⟩, hde, H⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  have aux : coeff d φ ≠ 0 ∧ coeff e ψ ≠ 0 := by
    contrapose! H
    by_cases h : coeff d φ = 0 <;>
      simp_all only [Ne.def, not_false_iff, zero_mul, mul_zero]
  rw [← Finsupp.mem_antidiagonal.mp hde, ← hφ aux.1, ← hψ aux.2, map_add]
#align mv_polynomial.weighted_homogeneous_submodule_mul MvPolynomial.weightedHomogeneousSubmodule_mul

/-- Monomials are weighted homogeneous. -/
theorem isWeightedHomogeneous_monomial (w : σ → M) (d : σ →₀ ℕ) (r : R) {m : M}
    (hm : weightedDegree' w d = m) : IsWeightedHomogeneous w (monomial d r) m := by
  classical
  intro c hc
  rw [coeff_monomial] at hc
  split_ifs at hc with h
  · subst c
    exact hm
  · contradiction
#align mv_polynomial.is_weighted_homogeneous_monomial MvPolynomial.isWeightedHomogeneous_monomial

/-- A polynomial of weightedTotalDegree `⊥` is weighted_homogeneous of degree `⊥`. -/
theorem isWeightedHomogeneous_of_total_degree_zero [SemilatticeSup M] [OrderBot M] (w : σ → M)
    {p : MvPolynomial σ R} (hp : weightedTotalDegree w p = (⊥ : M)) :
    IsWeightedHomogeneous w p (⊥ : M) := by
  intro d hd
  -- ⊢ ↑(weightedDegree' w) d = ⊥
  have h := weightedTotalDegree_coe w p (MvPolynomial.ne_zero_iff.mpr ⟨d, hd⟩)
  -- ⊢ ↑(weightedDegree' w) d = ⊥
  simp only [weightedTotalDegree', hp] at h
  -- ⊢ ↑(weightedDegree' w) d = ⊥
  rw [eq_bot_iff, ← WithBot.coe_le_coe, ← h]
  -- ⊢ ↑(↑(weightedDegree' w) d) ≤ sup (support p) fun s => ↑(↑(weightedDegree' w) s)
  apply Finset.le_sup (mem_support_iff.mpr hd)
  -- 🎉 no goals
#align mv_polynomial.is_weighted_homogeneous_of_total_degree_zero MvPolynomial.isWeightedHomogeneous_of_total_degree_zero

/-- Constant polynomials are weighted homogeneous of degree 0. -/
theorem isWeightedHomogeneous_C (w : σ → M) (r : R) :
    IsWeightedHomogeneous w (C r : MvPolynomial σ R) 0 :=
  isWeightedHomogeneous_monomial _ _ _ (map_zero _)
set_option linter.uppercaseLean3 false in
#align mv_polynomial.is_weighted_homogeneous_C MvPolynomial.isWeightedHomogeneous_C

variable (R)

/-- 0 is weighted homogeneous of any degree. -/
theorem isWeightedHomogeneous_zero (w : σ → M) (m : M) :
    IsWeightedHomogeneous w (0 : MvPolynomial σ R) m :=
  (weightedHomogeneousSubmodule R w m).zero_mem
#align mv_polynomial.is_weighted_homogeneous_zero MvPolynomial.isWeightedHomogeneous_zero

/-- 1 is weighted homogeneous of degree 0. -/
theorem isWeightedHomogeneous_one (w : σ → M) : IsWeightedHomogeneous w (1 : MvPolynomial σ R) 0 :=
  isWeightedHomogeneous_C _ _
#align mv_polynomial.is_weighted_homogeneous_one MvPolynomial.isWeightedHomogeneous_one

/-- An indeterminate `i : σ` is weighted homogeneous of degree `w i`. -/
theorem isWeightedHomogeneous_X (w : σ → M) (i : σ) :
    IsWeightedHomogeneous w (X i : MvPolynomial σ R) (w i) := by
  apply isWeightedHomogeneous_monomial
  -- ⊢ ↑(weightedDegree' w) (Finsupp.single i 1) = w i
  simp only [weightedDegree', LinearMap.toAddMonoidHom_coe, total_single, one_nsmul]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mv_polynomial.is_weighted_homogeneous_X MvPolynomial.isWeightedHomogeneous_X

namespace IsWeightedHomogeneous

variable {R}

variable {φ ψ : MvPolynomial σ R} {m n : M}

/-- The weighted degree of a weighted homogeneous polynomial controls its support. -/
theorem coeff_eq_zero {w : σ → M} (hφ : IsWeightedHomogeneous w φ n) (d : σ →₀ ℕ)
    (hd : weightedDegree' w d ≠ n) : coeff d φ = 0 := by
  have aux := mt (@hφ d) hd
  -- ⊢ coeff d φ = 0
  rwa [Classical.not_not] at aux
  -- 🎉 no goals
#align mv_polynomial.is_weighted_homogeneous.coeff_eq_zero MvPolynomial.IsWeightedHomogeneous.coeff_eq_zero

/-- The weighted degree of a nonzero weighted homogeneous polynomial is well-defined. -/
theorem inj_right {w : σ → M} (hφ : φ ≠ 0) (hm : IsWeightedHomogeneous w φ m)
    (hn : IsWeightedHomogeneous w φ n) : m = n := by
  obtain ⟨d, hd⟩ : ∃ d, coeff d φ ≠ 0 := exists_coeff_ne_zero hφ
  -- ⊢ m = n
  rw [← hm hd, ← hn hd]
  -- 🎉 no goals
#align mv_polynomial.is_weighted_homogeneous.inj_right MvPolynomial.IsWeightedHomogeneous.inj_right

/-- The sum of two weighted homogeneous polynomials of degree `n` is weighted homogeneous of
  weighted degree `n`. -/
theorem add {w : σ → M} (hφ : IsWeightedHomogeneous w φ n) (hψ : IsWeightedHomogeneous w ψ n) :
    IsWeightedHomogeneous w (φ + ψ) n :=
  (weightedHomogeneousSubmodule R w n).add_mem hφ hψ
#align mv_polynomial.is_weighted_homogeneous.add MvPolynomial.IsWeightedHomogeneous.add

/-- The sum of weighted homogeneous polynomials of degree `n` is weighted homogeneous of
  weighted degree `n`. -/
theorem sum {ι : Type*} (s : Finset ι) (φ : ι → MvPolynomial σ R) (n : M) {w : σ → M}
    (h : ∀ i ∈ s, IsWeightedHomogeneous w (φ i) n) : IsWeightedHomogeneous w (∑ i in s, φ i) n :=
  (weightedHomogeneousSubmodule R w n).sum_mem h
#align mv_polynomial.is_weighted_homogeneous.sum MvPolynomial.IsWeightedHomogeneous.sum

/-- The product of weighted homogeneous polynomials of weighted degrees `m` and `n` is weighted
  homogeneous of weighted degree `m + n`. -/
theorem mul {w : σ → M} (hφ : IsWeightedHomogeneous w φ m) (hψ : IsWeightedHomogeneous w ψ n) :
    IsWeightedHomogeneous w (φ * ψ) (m + n) :=
  weightedHomogeneousSubmodule_mul w m n <| Submodule.mul_mem_mul hφ hψ
#align mv_polynomial.is_weighted_homogeneous.mul MvPolynomial.IsWeightedHomogeneous.mul

/-- A product of weighted homogeneous polynomials is weighted homogeneous, with weighted degree
  equal to the sum of the weighted degrees. -/
theorem prod {ι : Type*} (s : Finset ι) (φ : ι → MvPolynomial σ R) (n : ι → M) {w : σ → M} :
    (∀ i ∈ s, IsWeightedHomogeneous w (φ i) (n i)) →
      IsWeightedHomogeneous w (∏ i in s, φ i) (∑ i in s, n i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · intro
    simp only [isWeightedHomogeneous_one, Finset.sum_empty, Finset.prod_empty]
  · intro i s his IH h
    simp only [his, Finset.prod_insert, Finset.sum_insert, not_false_iff]
    apply (h i (Finset.mem_insert_self _ _)).mul (IH _)
    intro j hjs
    exact h j (Finset.mem_insert_of_mem hjs)
#align mv_polynomial.is_weighted_homogeneous.prod MvPolynomial.IsWeightedHomogeneous.prod

/-- A non zero weighted homogeneous polynomial of weighted degree `n` has weighted total degree
  `n`. -/
theorem weighted_total_degree [SemilatticeSup M] {w : σ → M} (hφ : IsWeightedHomogeneous w φ n)
    (h : φ ≠ 0) : weightedTotalDegree' w φ = n := by
  simp only [weightedTotalDegree']
  -- ⊢ (sup (support φ) fun s => ↑(↑(weightedDegree' w) s)) = ↑n
  apply le_antisymm
  -- ⊢ (sup (support φ) fun s => ↑(↑(weightedDegree' w) s)) ≤ ↑n
  · simp only [Finset.sup_le_iff, mem_support_iff, WithBot.coe_le_coe]
    -- ⊢ ∀ (b : σ →₀ ℕ), coeff b φ ≠ 0 → ↑(weightedDegree' w) b ≤ n
    exact fun d hd => le_of_eq (hφ hd)
    -- 🎉 no goals
  · obtain ⟨d, hd⟩ : ∃ d, coeff d φ ≠ 0 := exists_coeff_ne_zero h
    -- ⊢ ↑n ≤ sup (support φ) fun s => ↑(↑(weightedDegree' w) s)
    simp only [← hφ hd, Finsupp.sum]
    -- ⊢ ↑(↑(weightedDegree' w) d) ≤ sup (support φ) fun s => ↑(↑(weightedDegree' w) s)
    replace hd := Finsupp.mem_support_iff.mpr hd
    -- ⊢ ↑(↑(weightedDegree' w) d) ≤ sup (support φ) fun s => ↑(↑(weightedDegree' w) s)
    apply Finset.le_sup hd
    -- 🎉 no goals
#align mv_polynomial.is_weighted_homogeneous.weighted_total_degree MvPolynomial.IsWeightedHomogeneous.weighted_total_degree

/-- The weighted homogeneous submodules form a graded monoid. -/
instance WeightedHomogeneousSubmodule.gcomm_monoid {w : σ → M} :
    SetLike.GradedMonoid (weightedHomogeneousSubmodule R w) where
  one_mem := isWeightedHomogeneous_one R w
  mul_mem _ _ _ _ := IsWeightedHomogeneous.mul
#align mv_polynomial.is_weighted_homogeneous.weighted_homogeneous_submodule.gcomm_monoid MvPolynomial.IsWeightedHomogeneous.WeightedHomogeneousSubmodule.gcomm_monoid

end IsWeightedHomogeneous

variable {R}

/-- `weightedHomogeneousComponent w n φ` is the part of `φ` that is weighted homogeneous of
  weighted degree `n`, with respect to the weights `w`.
  See `sum_weightedHomogeneousComponent` for the statement that `φ` is equal to the sum
  of all its weighted homogeneous components. -/
def weightedHomogeneousComponent (w : σ → M) (n : M) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  (Submodule.subtype _).comp <| Finsupp.restrictDom _ _ { d | weightedDegree' w d = n }
#align mv_polynomial.weighted_homogeneous_component MvPolynomial.weightedHomogeneousComponent

section WeightedHomogeneousComponent

variable {w : σ → M} (n : M) (φ ψ : MvPolynomial σ R)

theorem coeff_weightedHomogeneousComponent [DecidableEq M] (d : σ →₀ ℕ) :
    coeff d (weightedHomogeneousComponent w n φ) =
      if weightedDegree' w d = n then coeff d φ else 0 :=
  Finsupp.filter_apply (fun d : σ →₀ ℕ => weightedDegree' w d = n) φ d
#align mv_polynomial.coeff_weighted_homogeneous_component MvPolynomial.coeff_weightedHomogeneousComponent

theorem weightedHomogeneousComponent_apply [DecidableEq M] :
    weightedHomogeneousComponent w n φ =
      ∑ d in φ.support.filter fun d => weightedDegree' w d = n, monomial d (coeff d φ) :=
  Finsupp.filter_eq_sum (fun d : σ →₀ ℕ => weightedDegree' w d = n) φ
#align mv_polynomial.weighted_homogeneous_component_apply MvPolynomial.weightedHomogeneousComponent_apply

/-- The `n` weighted homogeneous component of a polynomial is weighted homogeneous of
weighted degree `n`. -/
theorem weightedHomogeneousComponent_isWeightedHomogeneous :
    (weightedHomogeneousComponent w n φ).IsWeightedHomogeneous w n := by
  classical
  intro d hd
  contrapose! hd
  rw [coeff_weightedHomogeneousComponent, if_neg hd]
#align mv_polynomial.weighted_homogeneous_component_is_weighted_homogeneous MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous

@[simp]
theorem weightedHomogeneousComponent_C_mul (n : M) (r : R) :
    weightedHomogeneousComponent w n (C r * φ) = C r * weightedHomogeneousComponent w n φ := by
  simp only [C_mul', LinearMap.map_smul]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mv_polynomial.weighted_homogeneous_component_C_mul MvPolynomial.weightedHomogeneousComponent_C_mul

theorem weightedHomogeneousComponent_eq_zero'
    (h : ∀ d : σ →₀ ℕ, d ∈ φ.support → weightedDegree' w d ≠ n) :
    weightedHomogeneousComponent w n φ = 0 := by
  classical
  rw [weightedHomogeneousComponent_apply, sum_eq_zero]
  intro d hd; rw [mem_filter] at hd
  exfalso; exact h _ hd.1 hd.2
#align mv_polynomial.weighted_homogeneous_component_eq_zero' MvPolynomial.weightedHomogeneousComponent_eq_zero'

theorem weightedHomogeneousComponent_eq_zero [SemilatticeSup M] [OrderBot M]
    (h : weightedTotalDegree w φ < n) : weightedHomogeneousComponent w n φ = 0 := by
  classical
  rw [weightedHomogeneousComponent_apply, sum_eq_zero]
  intro d hd
  rw [Finset.mem_filter] at hd
  exfalso
  apply lt_irrefl n
  nth_rw 1 [← hd.2]
  exact lt_of_le_of_lt (le_weightedTotalDegree w hd.1) h
#align mv_polynomial.weighted_homogeneous_component_eq_zero MvPolynomial.weightedHomogeneousComponent_eq_zero

theorem weightedHomogeneousComponent_finsupp :
    (Function.support fun m => weightedHomogeneousComponent w m φ).Finite := by
  suffices
    (Function.support fun m => weightedHomogeneousComponent w m φ) ⊆
      (fun d => weightedDegree' w d) '' φ.support by
    exact Finite.subset ((fun d : σ →₀ ℕ => (weightedDegree' w) d) '' ↑(support φ)).toFinite this
  intro m hm
  -- ⊢ m ∈ (fun d => ↑(weightedDegree' w) d) '' ↑(support φ)
  by_contra hm'
  -- ⊢ False
  apply hm
  -- ⊢ (fun m => ↑(weightedHomogeneousComponent w m) φ) m = 0
  simp only [mem_support, Ne.def] at hm
  -- ⊢ (fun m => ↑(weightedHomogeneousComponent w m) φ) m = 0
  simp only [Set.mem_image, not_exists, not_and] at hm'
  -- ⊢ (fun m => ↑(weightedHomogeneousComponent w m) φ) m = 0
  exact weightedHomogeneousComponent_eq_zero' m φ hm'
  -- 🎉 no goals
#align mv_polynomial.weighted_homogeneous_component_finsupp MvPolynomial.weightedHomogeneousComponent_finsupp

variable (w)

/-- Every polynomial is the sum of its weighted homogeneous components. -/
theorem sum_weightedHomogeneousComponent :
    (finsum fun m => weightedHomogeneousComponent w m φ) = φ := by
  classical
  rw [finsum_eq_sum _ (weightedHomogeneousComponent_finsupp φ)]
  ext1 d
  simp only [coeff_sum, coeff_weightedHomogeneousComponent]
  rw [Finset.sum_eq_single (weightedDegree' w d)]
  · rw [if_pos rfl]
  · intro m _ hm'
    rw [if_neg hm'.symm]
  · intro hm
    rw [if_pos rfl]
    simp only [Finite.mem_toFinset, mem_support, Ne.def, Classical.not_not] at hm
    have := coeff_weightedHomogeneousComponent (w := w) (weightedDegree' w d) φ d
    rw [hm, if_pos rfl, coeff_zero] at this
    exact this.symm
#align mv_polynomial.sum_weighted_homogeneous_component MvPolynomial.sum_weightedHomogeneousComponent

variable {w}

/-- The weighted homogeneous components of a weighted homogeneous polynomial. -/
theorem weightedHomogeneousComponent_weighted_homogeneous_polynomial [DecidableEq M] (m n : M)
    (p : MvPolynomial σ R) (h : p ∈ weightedHomogeneousSubmodule R w n) :
    weightedHomogeneousComponent w m p = if m = n then p else 0 := by
  simp only [mem_weightedHomogeneousSubmodule] at h
  -- ⊢ ↑(weightedHomogeneousComponent w m) p = if m = n then p else 0
  ext x
  -- ⊢ coeff x (↑(weightedHomogeneousComponent w m) p) = coeff x (if m = n then p e …
  rw [coeff_weightedHomogeneousComponent]
  -- ⊢ (if ↑(weightedDegree' w) x = m then coeff x p else 0) = coeff x (if m = n th …
  by_cases zero_coeff : coeff x p = 0
  -- ⊢ (if ↑(weightedDegree' w) x = m then coeff x p else 0) = coeff x (if m = n th …
  · split_ifs
    all_goals simp only [zero_coeff, coeff_zero]
    -- 🎉 no goals
  · rw [h zero_coeff]
    -- ⊢ (if n = m then coeff x p else 0) = coeff x (if m = n then p else 0)
    simp only [show n = m ↔ m = n from eq_comm]
    -- ⊢ (if m = n then coeff x p else 0) = coeff x (if m = n then p else 0)
    split_ifs with h1
    -- ⊢ coeff x p = coeff x p
    · rfl
      -- 🎉 no goals
    · simp only [coeff_zero]
      -- 🎉 no goals
#align mv_polynomial.weighted_homogeneous_component_weighted_homogeneous_polynomial MvPolynomial.weightedHomogeneousComponent_weighted_homogeneous_polynomial

end WeightedHomogeneousComponent

end AddCommMonoid

section CanonicallyOrderedAddMonoid

variable [CanonicallyOrderedAddMonoid M] {w : σ → M} (φ : MvPolynomial σ R)

/-- If `M` is a `CanonicallyOrderedAddMonoid`, then the `weightedHomogeneousComponent`
  of weighted degree `0` of a polynomial is its constant coefficient. -/
@[simp]
theorem weightedHomogeneousComponent_zero [NoZeroSMulDivisors ℕ M] (hw : ∀ i : σ, w i ≠ 0) :
    weightedHomogeneousComponent w 0 φ = C (coeff 0 φ) := by
  classical
  ext1 d
  rcases Classical.em (d = 0) with (rfl | hd)
  · simp only [coeff_weightedHomogeneousComponent, if_pos, map_zero, coeff_zero_C]
  · rw [coeff_weightedHomogeneousComponent, if_neg, coeff_C, if_neg (Ne.symm hd)]
    simp only [weightedDegree', LinearMap.toAddMonoidHom_coe, Finsupp.total_apply, Finsupp.sum,
      sum_eq_zero_iff, Finsupp.mem_support_iff, Ne.def, smul_eq_zero, not_forall, not_or,
      and_self_left, exists_prop]
    simp only [FunLike.ext_iff, Finsupp.coe_zero, Pi.zero_apply, not_forall] at hd
    obtain ⟨i, hi⟩ := hd
    exact ⟨i, hi, hw i⟩
#align mv_polynomial.weighted_homogeneous_component_zero MvPolynomial.weightedHomogeneousComponent_zero

end CanonicallyOrderedAddMonoid

end MvPolynomial
