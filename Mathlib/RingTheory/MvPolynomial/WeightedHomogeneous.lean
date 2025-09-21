/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.GradedMonoid
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Data.Finsupp.Weight
import Mathlib.RingTheory.GradedAlgebra.Basic

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

open Set Function Finset Finsupp AddMonoidAlgebra

variable {R M : Type*} [CommSemiring R]

namespace MvPolynomial

variable {σ : Type*}

section AddCommMonoid

variable [AddCommMonoid M]

/-! ### `weight` -/


section SemilatticeSup

variable [SemilatticeSup M]

/-- The weighted total degree of a multivariate polynomial, taking values in `WithBot M`. -/
def weightedTotalDegree' (w : σ → M) (p : MvPolynomial σ R) : WithBot M :=
  p.support.sup fun s => weight w s

/-- The `weightedTotalDegree'` of a polynomial `p` is `⊥` if and only if `p = 0`. -/
theorem weightedTotalDegree'_eq_bot_iff (w : σ → M) (p : MvPolynomial σ R) :
    weightedTotalDegree' w p = ⊥ ↔ p = 0 := by
  simp only [weightedTotalDegree', Finset.sup_eq_bot_iff, mem_support_iff, WithBot.coe_ne_bot,
    MvPolynomial.eq_zero_iff]
  exact forall_congr' fun _ => Classical.not_not

/-- The `weightedTotalDegree'` of the zero polynomial is `⊥`. -/
theorem weightedTotalDegree'_zero (w : σ → M) :
    weightedTotalDegree' w (0 : MvPolynomial σ R) = ⊥ := by
  simp only [weightedTotalDegree', support_zero, Finset.sup_empty]

section OrderBot

variable [OrderBot M]

/-- When `M` has a `⊥` element, we can define the weighted total degree of a multivariate
  polynomial as a function taking values in `M`. -/
def weightedTotalDegree (w : σ → M) (p : MvPolynomial σ R) : M :=
  p.support.sup fun s => weight w s

/-- This lemma relates `weightedTotalDegree` and `weightedTotalDegree'`. -/
theorem weightedTotalDegree_coe (w : σ → M) (p : MvPolynomial σ R) (hp : p ≠ 0) :
    weightedTotalDegree' w p = ↑(weightedTotalDegree w p) := by
  rw [Ne, ← weightedTotalDegree'_eq_bot_iff w p, ← Ne, WithBot.ne_bot_iff_exists] at hp
  obtain ⟨m, hm⟩ := hp
  apply le_antisymm
  · simp only [weightedTotalDegree, weightedTotalDegree', Finset.sup_le_iff, WithBot.coe_le_coe]
    intro b
    exact Finset.le_sup
  · simp only [weightedTotalDegree]
    have hm' : weightedTotalDegree' w p ≤ m := le_of_eq hm.symm
    rw [← hm]
    simpa [weightedTotalDegree'] using hm'

/-- The `weightedTotalDegree` of the zero polynomial is `⊥`. -/
theorem weightedTotalDegree_zero (w : σ → M) :
    weightedTotalDegree w (0 : MvPolynomial σ R) = ⊥ := by
  simp only [weightedTotalDegree, support_zero, Finset.sup_empty]

theorem le_weightedTotalDegree (w : σ → M) {φ : MvPolynomial σ R} {d : σ →₀ ℕ}
    (hd : d ∈ φ.support) : weight w d ≤ φ.weightedTotalDegree w :=
  le_sup hd

end OrderBot

end SemilatticeSup

/-- A multivariate polynomial `φ` is weighted homogeneous of weighted degree `m` if all monomials
  occurring in `φ` have weighted degree `m`. -/
def IsWeightedHomogeneous (w : σ → M) (φ : MvPolynomial σ R) (m : M) : Prop :=
  ∀ ⦃d⦄, coeff d φ ≠ 0 → weight w d = m

variable (R)

/-- The submodule of homogeneous `MvPolynomial`s of degree `n`. -/
def weightedHomogeneousSubmodule (w : σ → M) (m : M) : Submodule R (MvPolynomial σ R) where
  carrier := { x | x.IsWeightedHomogeneous w m }
  smul_mem' r a ha c hc := by
    rw [coeff_smul] at hc
    exact ha (right_ne_zero_of_mul hc)
  zero_mem' _ hd := False.elim (hd <| coeff_zero _)
  add_mem' {a} {b} ha hb c hc := by
    rw [coeff_add] at hc
    obtain h | h : coeff c a ≠ 0 ∨ coeff c b ≠ 0 := by
      contrapose! hc
      simp only [hc, add_zero]
    · exact ha h
    · exact hb h

@[simp]
theorem mem_weightedHomogeneousSubmodule (w : σ → M) (m : M) (p : MvPolynomial σ R) :
    p ∈ weightedHomogeneousSubmodule R w m ↔ p.IsWeightedHomogeneous w m :=
  Iff.rfl

/-- The submodule `weightedHomogeneousSubmodule R w m` of homogeneous `MvPolynomial`s of
  degree `n` is equal to the `R`-submodule of all `p : (σ →₀ ℕ) →₀ R` such that
  `p.support ⊆ {d | weight w d = m}`. While equal, the former has a
  convenient definitional reduction. -/
theorem weightedHomogeneousSubmodule_eq_finsupp_supported (w : σ → M) (m : M) :
    weightedHomogeneousSubmodule R w m = Finsupp.supported R R { d | weight w d = m } := by
  ext x
  rw [mem_supported, Set.subset_def]
  simp only [Finsupp.mem_support_iff, mem_coe]
  rfl

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
      simp_all only [Ne, not_false_iff, zero_mul, mul_zero]
  rw [← mem_antidiagonal.mp hde, ← hφ aux.1, ← hψ aux.2, map_add]

/-- Monomials are weighted homogeneous. -/
theorem isWeightedHomogeneous_monomial (w : σ → M) (d : σ →₀ ℕ) (r : R) {m : M}
    (hm : weight w d = m) : IsWeightedHomogeneous w (monomial d r) m := by
  classical
  intro c hc
  rw [coeff_monomial] at hc
  split_ifs at hc with h
  · subst c
    exact hm
  · contradiction

/-- A polynomial of weightedTotalDegree `⊥` is weighted_homogeneous of degree `⊥`. -/
theorem isWeightedHomogeneous_of_total_degree_zero [SemilatticeSup M] [OrderBot M] (w : σ → M)
    {p : MvPolynomial σ R} (hp : weightedTotalDegree w p = (⊥ : M)) :
    IsWeightedHomogeneous w p (⊥ : M) := by
  intro d hd
  have h := weightedTotalDegree_coe w p (MvPolynomial.ne_zero_iff.mpr ⟨d, hd⟩)
  simp only [weightedTotalDegree', hp] at h
  rw [eq_bot_iff, ← WithBot.coe_le_coe, ← h]
  apply Finset.le_sup (mem_support_iff.mpr hd)

/-- Constant polynomials are weighted homogeneous of degree 0. -/
theorem isWeightedHomogeneous_C (w : σ → M) (r : R) :
    IsWeightedHomogeneous w (C r : MvPolynomial σ R) 0 :=
  isWeightedHomogeneous_monomial _ _ _ (map_zero _)

variable (R)

/-- 0 is weighted homogeneous of any degree. -/
theorem isWeightedHomogeneous_zero (w : σ → M) (m : M) :
    IsWeightedHomogeneous w (0 : MvPolynomial σ R) m :=
  (weightedHomogeneousSubmodule R w m).zero_mem

/-- 1 is weighted homogeneous of degree 0. -/
theorem isWeightedHomogeneous_one (w : σ → M) : IsWeightedHomogeneous w (1 : MvPolynomial σ R) 0 :=
  isWeightedHomogeneous_C _ _

/-- An indeterminate `i : σ` is weighted homogeneous of degree `w i`. -/
theorem isWeightedHomogeneous_X (w : σ → M) (i : σ) :
    IsWeightedHomogeneous w (X i : MvPolynomial σ R) (w i) := by
  apply isWeightedHomogeneous_monomial
  simp only [weight, LinearMap.toAddMonoidHom_coe, linearCombination_single, one_nsmul]

namespace IsWeightedHomogeneous

variable {R}
variable {φ ψ : MvPolynomial σ R} {m n : M}

/-- The weighted degree of a weighted homogeneous polynomial controls its support. -/
theorem coeff_eq_zero {w : σ → M} (hφ : IsWeightedHomogeneous w φ n) (d : σ →₀ ℕ)
    (hd : weight w d ≠ n) : coeff d φ = 0 := by
  have aux := mt (@hφ d) hd
  rwa [Classical.not_not] at aux

/-- The weighted degree of a nonzero weighted homogeneous polynomial is well-defined. -/
theorem inj_right {w : σ → M} (hφ : φ ≠ 0) (hm : IsWeightedHomogeneous w φ m)
    (hn : IsWeightedHomogeneous w φ n) : m = n := by
  obtain ⟨d, hd⟩ : ∃ d, coeff d φ ≠ 0 := exists_coeff_ne_zero hφ
  rw [← hm hd, ← hn hd]

/-- The sum of two weighted homogeneous polynomials of degree `n` is weighted homogeneous of
  weighted degree `n`. -/
theorem add {w : σ → M} (hφ : IsWeightedHomogeneous w φ n) (hψ : IsWeightedHomogeneous w ψ n) :
    IsWeightedHomogeneous w (φ + ψ) n :=
  (weightedHomogeneousSubmodule R w n).add_mem hφ hψ

/-- The sum of weighted homogeneous polynomials of degree `n` is weighted homogeneous of
  weighted degree `n`. -/
theorem sum {ι : Type*} (s : Finset ι) (φ : ι → MvPolynomial σ R) (n : M) {w : σ → M}
    (h : ∀ i ∈ s, IsWeightedHomogeneous w (φ i) n) : IsWeightedHomogeneous w (∑ i ∈ s, φ i) n :=
  (weightedHomogeneousSubmodule R w n).sum_mem h

/-- The product of weighted homogeneous polynomials of weighted degrees `m` and `n` is weighted
  homogeneous of weighted degree `m + n`. -/
theorem mul {w : σ → M} (hφ : IsWeightedHomogeneous w φ m) (hψ : IsWeightedHomogeneous w ψ n) :
    IsWeightedHomogeneous w (φ * ψ) (m + n) :=
  weightedHomogeneousSubmodule_mul w m n <| Submodule.mul_mem_mul hφ hψ

theorem pow {w : σ → M} (hφ : IsWeightedHomogeneous w φ m) (n : ℕ) :
    IsWeightedHomogeneous w (φ ^ n) (n • m) := by
  induction n with
  | zero => rw [pow_zero, zero_smul]; exact isWeightedHomogeneous_one R w
  | succ n ih => rw [pow_succ, succ_nsmul]; exact ih.mul hφ

/-- A product of weighted homogeneous polynomials is weighted homogeneous, with weighted degree
  equal to the sum of the weighted degrees. -/
theorem prod {ι : Type*} (s : Finset ι) (φ : ι → MvPolynomial σ R) (n : ι → M) {w : σ → M} :
    (∀ i ∈ s, IsWeightedHomogeneous w (φ i) (n i)) →
      IsWeightedHomogeneous w (∏ i ∈ s, φ i) (∑ i ∈ s, n i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · intro
    simp only [isWeightedHomogeneous_one, Finset.sum_empty, Finset.prod_empty]
  · intro i s his IH h
    simp only [his, Finset.prod_insert, Finset.sum_insert, not_false_iff]
    apply (h i (Finset.mem_insert_self _ _)).mul (IH _)
    intro j hjs
    exact h j (Finset.mem_insert_of_mem hjs)

/-- A non zero weighted homogeneous polynomial of weighted degree `n` has weighted total degree
  `n`. -/
theorem weighted_total_degree [SemilatticeSup M] {w : σ → M} (hφ : IsWeightedHomogeneous w φ n)
    (h : φ ≠ 0) : weightedTotalDegree' w φ = n := by
  simp only [weightedTotalDegree']
  apply le_antisymm
  · simp only [Finset.sup_le_iff, mem_support_iff, WithBot.coe_le_coe]
    exact fun d hd => le_of_eq (hφ hd)
  · obtain ⟨d, hd⟩ : ∃ d, coeff d φ ≠ 0 := exists_coeff_ne_zero h
    simp only [← hφ hd]
    replace hd := Finsupp.mem_support_iff.mpr hd
    apply Finset.le_sup hd

end IsWeightedHomogeneous

variable {R}

/-- The weighted homogeneous submodules form a graded monoid. -/
lemma WeightedHomogeneousSubmodule.gradedMonoid {w : σ → M} :
    SetLike.GradedMonoid (weightedHomogeneousSubmodule R w) where
  one_mem := isWeightedHomogeneous_one R w
  mul_mem _ _ _ _ := IsWeightedHomogeneous.mul

/-- `weightedHomogeneousComponent w n φ` is the part of `φ` that is weighted homogeneous of
  weighted degree `n`, with respect to the weights `w`.
  See `sum_weightedHomogeneousComponent` for the statement that `φ` is equal to the sum
  of all its weighted homogeneous components. -/
def weightedHomogeneousComponent (w : σ → M) (n : M) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  letI := Classical.decEq M
  (Submodule.subtype _).comp <| Finsupp.restrictDom _ _ { d | weight w d = n }

section WeightedHomogeneousComponent

variable {w : σ → M} (n : M) (φ ψ : MvPolynomial σ R)

theorem coeff_weightedHomogeneousComponent [DecidableEq M] (d : σ →₀ ℕ) :
    coeff d (weightedHomogeneousComponent w n φ) =
      if weight w d = n then coeff d φ else 0 :=
  letI := Classical.decEq M
  Finsupp.filter_apply (fun d : σ →₀ ℕ => weight w d = n) φ d |>.trans <| by convert rfl

theorem weightedHomogeneousComponent_apply [DecidableEq M] :
    weightedHomogeneousComponent w n φ =
      ∑ d ∈ φ.support with weight w d = n, monomial d (coeff d φ) :=
  letI := Classical.decEq M
  Finsupp.filter_eq_sum (fun d : σ →₀ ℕ => weight w d = n) φ |>.trans <| by convert rfl

/-- The `n` weighted homogeneous component of a polynomial is weighted homogeneous of
weighted degree `n`. -/
theorem weightedHomogeneousComponent_isWeightedHomogeneous :
    (weightedHomogeneousComponent w n φ).IsWeightedHomogeneous w n := by
  classical
  intro d hd
  contrapose! hd
  rw [coeff_weightedHomogeneousComponent, if_neg hd]

theorem weightedHomogeneousComponent_mem (w : σ → M) (φ : MvPolynomial σ R) (m : M) :
    weightedHomogeneousComponent w m φ ∈ weightedHomogeneousSubmodule R w m := by
  rw [mem_weightedHomogeneousSubmodule]
  exact weightedHomogeneousComponent_isWeightedHomogeneous m φ

@[simp]
theorem weightedHomogeneousComponent_C_mul (n : M) (r : R) :
    weightedHomogeneousComponent w n (C r * φ) = C r * weightedHomogeneousComponent w n φ := by
  simp only [C_mul', LinearMap.map_smul]

theorem weightedHomogeneousComponent_eq_zero'
    (h : ∀ d : σ →₀ ℕ, d ∈ φ.support → weight w d ≠ n) :
    weightedHomogeneousComponent w n φ = 0 := by
  classical
  rw [weightedHomogeneousComponent_apply, sum_eq_zero]
  intro d hd; rw [mem_filter] at hd
  exfalso; exact h _ hd.1 hd.2

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

theorem weightedHomogeneousComponent_finsupp :
    (Function.support fun m => weightedHomogeneousComponent w m φ).Finite := by
  apply ((fun d : σ →₀ ℕ => (weight w) d) '' (φ.support : Set (σ →₀ ℕ))).toFinite.subset
  intro m hm
  by_contra hm'
  apply hm (weightedHomogeneousComponent_eq_zero' m φ _)
  simpa only [Set.mem_image, not_exists, not_and] using hm'

variable (w)

/-- Every polynomial is the sum of its weighted homogeneous components. -/
theorem sum_weightedHomogeneousComponent :
    (finsum fun m => weightedHomogeneousComponent w m φ) = φ := by
  classical
  rw [finsum_eq_sum _ (weightedHomogeneousComponent_finsupp φ)]
  ext1 d
  simp only [coeff_sum, coeff_weightedHomogeneousComponent]
  rw [Finset.sum_eq_single (weight w d)]
  · rw [if_pos rfl]
  · intro m _ hm'
    rw [if_neg hm'.symm]
  · intro hm
    rw [if_pos rfl]
    simp only [Finite.mem_toFinset, mem_support, Ne, Classical.not_not] at hm
    have := coeff_weightedHomogeneousComponent (w := w) (weight w d) φ d
    rw [hm, if_pos rfl, coeff_zero] at this
    exact this.symm

theorem finsum_weightedHomogeneousComponent :
    (finsum fun m => weightedHomogeneousComponent w m φ) = φ := by
  rw [sum_weightedHomogeneousComponent]

variable {w}

theorem IsWeightedHomogeneous.weightedHomogeneousComponent_same {m : M} {p : MvPolynomial σ R}
    (hp : IsWeightedHomogeneous w p m) :
    weightedHomogeneousComponent w m p = p := by
  classical
  ext x
  rw [coeff_weightedHomogeneousComponent]
  by_cases zero_coeff : coeff x p = 0
  · split_ifs
    · rfl
    rw [zero_coeff]
  · rw [hp zero_coeff, if_pos rfl]

theorem IsWeightedHomogeneous.weightedHomogeneousComponent_ne {m : M} (n : M)
    {p : MvPolynomial σ R} (hp : IsWeightedHomogeneous w p m) :
    n ≠ m → weightedHomogeneousComponent w n p = 0 := by
  classical
  intro hn
  ext x
  rw [coeff_weightedHomogeneousComponent]
  by_cases zero_coeff : coeff x p = 0
  · simp [zero_coeff]
  · rw [if_neg]
    · rw [coeff_zero]
    · rw [hp zero_coeff]; exact Ne.symm hn

/-- The weighted homogeneous components of a weighted homogeneous polynomial. -/
theorem weightedHomogeneousComponent_of_mem [DecidableEq M] {m n : M}
    {p : MvPolynomial σ R} (h : p ∈ weightedHomogeneousSubmodule R w n) :
    weightedHomogeneousComponent w m p = if m = n then p else 0 := by
  simp only [mem_weightedHomogeneousSubmodule] at h
  ext x
  rw [coeff_weightedHomogeneousComponent]
  by_cases zero_coeff : coeff x p = 0
  · split_ifs <;>
    simp only [zero_coeff, coeff_zero]
  · rw [h zero_coeff]
    simp only [show n = m ↔ m = n from eq_comm]
    split_ifs with h1
    · rfl
    · simp only [coeff_zero]

theorem weightedHomogeneousComponent_of_isWeightedHomogeneous_same
    {m : M} {p : MvPolynomial σ R} (hp : IsWeightedHomogeneous w p m) :
    weightedHomogeneousComponent w m p = p := by
  classical
  ext x
  rw [coeff_weightedHomogeneousComponent]
  by_cases zero_coeff : coeff x p = 0
  · simp [zero_coeff]
  · rw [hp zero_coeff, if_pos rfl]

theorem weightedHomogeneousComponent_of_isWeightedHomogeneous_ne
    {m n : M} {p : MvPolynomial σ R} (hp : IsWeightedHomogeneous w p m) (hn : n ≠ m) :
    weightedHomogeneousComponent w n p = 0 := by
  classical
  ext x
  rw [coeff_weightedHomogeneousComponent]
  by_cases zero_coeff : coeff x p = 0
  · simp [zero_coeff]
  · rw [if_neg (by simp only [hp zero_coeff, hn.symm, not_false_eq_true]), coeff_zero]

variable (R w)

open DirectSum

theorem DirectSum.coeLinearMap_eq_dfinsuppSum [DecidableEq σ] [DecidableEq R] [DecidableEq M]
    (x : DirectSum M fun i : M => ↥(weightedHomogeneousSubmodule R w i)) :
    (coeLinearMap fun i : M => weightedHomogeneousSubmodule R w i) x =
      DFinsupp.sum x (fun _ x => ↑x) := by
  rw [_root_.DirectSum.coeLinearMap_eq_dfinsuppSum]

theorem DirectSum.coeAddMonoidHom_eq_support_sum [DecidableEq σ] [DecidableEq R] [DecidableEq M]
    (x : DirectSum M fun i : M => ↥(weightedHomogeneousSubmodule R w i)) :
    (DirectSum.coeAddMonoidHom fun i : M => weightedHomogeneousSubmodule R w i) x =
      DFinsupp.sum x (fun _ x => ↑x) :=
  DirectSum.coeLinearMap_eq_dfinsuppSum R w x

theorem DirectSum.coeLinearMap_eq_finsum [DecidableEq M]
    (x : DirectSum M fun i : M => ↥(weightedHomogeneousSubmodule R w i)) :
    (DirectSum.coeLinearMap fun i : M => weightedHomogeneousSubmodule R w i) x =
      finsum fun m => x m := by
  classical
  rw [DirectSum.coeLinearMap_eq_dfinsuppSum, DFinsupp.sum, finsum_eq_sum_of_support_subset]
  apply DirectSum.support_subset

theorem weightedHomogeneousComponent_directSum [DecidableEq M]
    (x : DirectSum M fun i : M => ↥(weightedHomogeneousSubmodule R w i)) (m : M) :
    (weightedHomogeneousComponent w m)
      ((DirectSum.coeLinearMap fun i : M => weightedHomogeneousSubmodule R w i) x) = x m := by
  classical
  rw [DirectSum.coeLinearMap_eq_dfinsuppSum, DFinsupp.sum, map_sum]
  convert @Finset.sum_eq_single M (MvPolynomial σ R) _ (DFinsupp.support x) _ m _ _
  · rw [weightedHomogeneousComponent_of_isWeightedHomogeneous_same (x m).prop]
  · intro n _ hmn
    rw [weightedHomogeneousComponent_of_isWeightedHomogeneous_ne (x n).prop hmn.symm]
  · rw [DFinsupp.notMem_support_iff]
    intro hm; rw [hm, Submodule.coe_zero, map_zero]

end WeightedHomogeneousComponent

end AddCommMonoid

section OrderedAddCommMonoid

variable [AddCommMonoid M] [PartialOrder M]
  {w : σ → M} (φ : MvPolynomial σ R)

/-- If `M` is a canonically `OrderedAddCommMonoid`, then the `weightedHomogeneousComponent`
  of weighted degree `0` of a polynomial is its constant coefficient. -/
@[simp]
theorem weightedHomogeneousComponent_zero [CanonicallyOrderedAdd M] [NoZeroSMulDivisors ℕ M]
    (hw : ∀ i : σ, w i ≠ 0) :
    weightedHomogeneousComponent w 0 φ = C (coeff 0 φ) := by
  classical
  ext1 d
  rcases Classical.em (d = 0) with (rfl | hd)
  · simp only [coeff_weightedHomogeneousComponent, if_pos, map_zero, coeff_zero_C]
  · rw [coeff_weightedHomogeneousComponent, if_neg, coeff_C, if_neg (Ne.symm hd)]
    simp only [weight, LinearMap.toAddMonoidHom_coe, Finsupp.linearCombination_apply, Finsupp.sum,
      sum_eq_zero_iff, Finsupp.mem_support_iff, Ne, smul_eq_zero, not_forall, not_or,
      and_self_left, exists_prop]
    simp only [DFunLike.ext_iff, Finsupp.coe_zero, Pi.zero_apply, not_forall] at hd
    obtain ⟨i, hi⟩ := hd
    exact ⟨i, hi, hw i⟩

/-- A weight function is nontorsion if its values are not torsion. -/
def NonTorsionWeight (w : σ → M) :=
  ∀ n x, n • w x = (0 : M) → n = 0

omit [PartialOrder M] in
theorem nonTorsionWeight_of [NoZeroSMulDivisors ℕ M] (hw : ∀ i : σ, w i ≠ 0) :
    NonTorsionWeight w :=
  fun _ x hnx => (smul_eq_zero_iff_left (hw x)).mp hnx

/-- If `w` is a nontorsion weight function, then the finitely supported function `m : σ →₀ ℕ`
  has weighted degree zero if and only if `∀ x : σ, m x = 0`. -/
theorem weightedDegree_eq_zero_iff [CanonicallyOrderedAdd M]
    (hw : NonTorsionWeight w) {m : σ →₀ ℕ} :
    weight w m = 0 ↔ ∀ x : σ, m x = 0 := by
  simp only [weight, Finsupp.linearCombination, LinearMap.toAddMonoidHom_coe, coe_lsum,
    LinearMap.coe_smulRight, LinearMap.id_coe, id_eq]
  rw [Finsupp.sum, Finset.sum_eq_zero_iff]
  apply forall_congr'
  intro x
  rw [Finsupp.mem_support_iff]
  constructor
  · intro hx
    by_contra hx'
    exact absurd (hw _ _ (hx hx')) hx'
  · intro hax _
    simp only [hax, zero_smul]

end OrderedAddCommMonoid

section LinearOrderedAddCommMonoid

variable [AddCommMonoid M] [LinearOrder M] [OrderBot M] [CanonicallyOrderedAdd M]
  {w : σ → M} (φ : MvPolynomial σ R)

/-- A multivariate polynomial is weighted homogeneous of weighted degree zero if and only if
  its weighted total degree is equal to zero. -/
theorem isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero {p : MvPolynomial σ R} :
    IsWeightedHomogeneous w p 0 ↔ p.weightedTotalDegree w = 0 := by
  rw [weightedTotalDegree, ← bot_eq_zero, Finset.sup_eq_bot_iff, bot_eq_zero, IsWeightedHomogeneous]
  apply forall_congr'
  intro m
  rw [mem_support_iff]

/-- If `w` is a nontorsion weight function, then a multivariate polynomial has weighted total
  degree zero if and only if for every `m ∈ p.support` and `x : σ`, `m x = 0`. -/
theorem weightedTotalDegree_eq_zero_iff (hw : NonTorsionWeight w) (p : MvPolynomial σ R) :
    p.weightedTotalDegree w = 0 ↔ ∀ (m : σ →₀ ℕ) (_ : m ∈ p.support) (x : σ), m x = 0 := by
  rw [← isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero, IsWeightedHomogeneous]
  apply forall_congr'
  intro m
  rw [mem_support_iff]
  apply forall_congr'
  intro _
  exact weightedDegree_eq_zero_iff hw

end LinearOrderedAddCommMonoid

section GradedAlgebra

/- Here, given a weight `w : σ → M`, where `M` is an additive and commutative monoid, we endow the
  ring of multivariate polynomials `MvPolynomial σ R` with the structure of a graded algebra -/
variable (w : σ → M) [AddCommMonoid M]

theorem weightedHomogeneousComponent_eq_zero_of_notMem [DecidableEq M]
    (φ : MvPolynomial σ R) (i : M) (hi : i ∉ Finset.image (weight w) φ.support) :
    weightedHomogeneousComponent w i φ = 0 := by
  apply weightedHomogeneousComponent_eq_zero'
  simp only [Finset.mem_image, mem_support_iff, ne_eq, not_exists, not_and] at hi
  exact fun m hm ↦ hi m (mem_support_iff.mp hm)

@[deprecated (since := "2025-05-23")]
alias weightedHomogeneousComponent_eq_zero_of_not_mem :=
  weightedHomogeneousComponent_eq_zero_of_notMem

variable (R)

/-- The `decompose'` argument of `weightedDecomposition`. -/
def decompose' [DecidableEq M] := fun φ : MvPolynomial σ R =>
  DirectSum.mk (fun i : M => ↥(weightedHomogeneousSubmodule R w i))
    (Finset.image (weight w) φ.support) fun m =>
      ⟨weightedHomogeneousComponent w m φ, weightedHomogeneousComponent_mem w φ m⟩

theorem decompose'_apply [DecidableEq M] (φ : MvPolynomial σ R) (m : M) :
    (decompose' R w φ m : MvPolynomial σ R) = weightedHomogeneousComponent w m φ := by
  rw [decompose']
  by_cases hm : m ∈ Finset.image (weight w) φ.support
  · simp only [DirectSum.mk_apply_of_mem hm, Subtype.coe_mk]
  · rw [DirectSum.mk_apply_of_notMem hm, Submodule.coe_zero,
      weightedHomogeneousComponent_eq_zero_of_notMem w φ m hm]

/-- Given a weight `w`, the decomposition of `MvPolynomial σ R` into weighted homogeneous
submodules -/
def weightedDecomposition [DecidableEq M] :
    DirectSum.Decomposition (weightedHomogeneousSubmodule R w) where
  decompose' := decompose' R w
  left_inv φ := by
    classical
    conv_rhs => rw [← sum_weightedHomogeneousComponent w φ]
    rw [← DirectSum.sum_support_of (decompose' R w φ)]
    simp only [DirectSum.coeAddMonoidHom_of, map_sum,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp φ)]
    apply Finset.sum_congr _ (fun m _ ↦ by rw [decompose'_apply])
    ext m
    simp only [DFinsupp.mem_support_toFun, ne_eq, Set.Finite.mem_toFinset, Function.mem_support,
      not_iff_not]
    conv_lhs => rw [← Subtype.coe_inj]
    rw [decompose'_apply, Submodule.coe_zero]
  right_inv x := by
    classical
    apply DFinsupp.ext
    intro m
    rw [← Subtype.coe_inj, decompose'_apply]
    exact weightedHomogeneousComponent_directSum R w x m


/-- Given a weight, `MvPolynomial` as a graded algebra -/
def weightedGradedAlgebra [DecidableEq M] :
    GradedAlgebra (weightedHomogeneousSubmodule R w) where
  toDecomposition := weightedDecomposition R w
  toGradedMonoid  := WeightedHomogeneousSubmodule.gradedMonoid

theorem weightedDecomposition.decompose'_eq [DecidableEq M] :
    (weightedDecomposition R w).decompose' = fun φ : MvPolynomial σ R =>
      DirectSum.mk (fun i : M => ↥(weightedHomogeneousSubmodule R w i))
        (Finset.image (weight w) φ.support) fun m =>
          ⟨weightedHomogeneousComponent w m φ, weightedHomogeneousComponent_mem w φ m⟩ := rfl

theorem weightedDecomposition.decompose'_apply [DecidableEq M]
    (φ : MvPolynomial σ R) (m : M) :
    ((weightedDecomposition R w).decompose' φ m : MvPolynomial σ R) =
      weightedHomogeneousComponent w m φ :=
  MvPolynomial.decompose'_apply R w φ m

end GradedAlgebra

end MvPolynomial
