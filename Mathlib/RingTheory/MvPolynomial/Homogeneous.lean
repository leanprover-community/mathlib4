/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Eric Wieser
-/
import Mathlib.Algebra.DirectSum.Internal
import Mathlib.Algebra.GradedMonoid
import Mathlib.Data.MvPolynomial.Variables

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
* create definition for `∑ i in d.support, d i`
* show that `MvPolynomial σ R ≃ₐ[R] ⨁ i, homogeneousSubmodule σ R i`
-/
/-- A multivariate polynomial `φ` is homogeneous of degree `n`
if all monomials occurring in `φ` have degree `n`. -/
def IsHomogeneous [CommSemiring R] (φ : MvPolynomial σ R) (n : ℕ) :=
  ∀ ⦃d⦄, coeff d φ ≠ 0 → ∑ i in d.support, d i = n
#align mv_polynomial.is_homogeneous MvPolynomial.IsHomogeneous

variable (σ R)

/-- The submodule of homogeneous `MvPolynomial`s of degree `n`. -/
def homogeneousSubmodule [CommSemiring R] (n : ℕ) : Submodule R (MvPolynomial σ R) where
  carrier := { x | x.IsHomogeneous n }
  smul_mem' r a ha c hc := by
    rw [coeff_smul] at hc
    -- ⊢ ∑ i in c.support, ↑c i = n
    apply ha
    -- ⊢ coeff c a ≠ 0
    intro h
    -- ⊢ False
    apply hc
    -- ⊢ r • coeff c a = 0
    rw [h]
    -- ⊢ ∑ i in c.support, ↑c i = n
    -- ⊢ r • 0 = 0
    exact smul_zero r
    -- 🎉 no goals
  zero_mem' d hd := False.elim (hd <| coeff_zero _)
      -- 🎉 no goals
  add_mem' {a b} ha hb c hc := by
      -- 🎉 no goals
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
  ext
  -- ⊢ x✝ ∈ homogeneousSubmodule σ R n ↔ x✝ ∈ Finsupp.supported R R {d | ∑ i in d.s …
  rw [Finsupp.mem_supported, Set.subset_def]
  -- ⊢ x✝ ∈ homogeneousSubmodule σ R n ↔ ∀ (x : σ →₀ ℕ), x ∈ ↑x✝.support → x ∈ {d | …
  simp only [Finsupp.mem_support_iff, Finset.mem_coe]
  -- ⊢ x✝ ∈ homogeneousSubmodule σ R n ↔ ∀ (x : σ →₀ ℕ), ↑x✝ x ≠ 0 → x ∈ {d | ∑ x i …
  rfl
  -- 🎉 no goals
#align mv_polynomial.homogeneous_submodule_eq_finsupp_supported MvPolynomial.homogeneousSubmodule_eq_finsupp_supported

variable {σ R}

theorem homogeneousSubmodule_mul [CommSemiring R] (m n : ℕ) :
    homogeneousSubmodule σ R m * homogeneousSubmodule σ R n ≤ homogeneousSubmodule σ R (m + n) := by
  rw [Submodule.mul_le]
  -- ⊢ ∀ (m_1 : MvPolynomial σ R), m_1 ∈ homogeneousSubmodule σ R m → ∀ (n_1 : MvPo …
  intro φ hφ ψ hψ c hc
  -- ⊢ ∑ i in c.support, ↑c i = m + n
  classical
  rw [coeff_mul] at hc
  obtain ⟨⟨d, e⟩, hde, H⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  have aux : coeff d φ ≠ 0 ∧ coeff e ψ ≠ 0 := by
    contrapose! H
    by_cases h : coeff d φ = 0 <;>
      simp_all only [Ne.def, not_false_iff, zero_mul, mul_zero]
  specialize hφ aux.1
  specialize hψ aux.2
  rw [Finsupp.mem_antidiagonal] at hde
  classical
  have hd' : d.support ⊆ d.support ∪ e.support := Finset.subset_union_left _ _
  have he' : e.support ⊆ d.support ∪ e.support := Finset.subset_union_right _ _
  rw [← hde, ← hφ, ← hψ, Finset.sum_subset Finsupp.support_add, Finset.sum_subset hd',
    Finset.sum_subset he', ← Finset.sum_add_distrib]
  · congr
  all_goals intro i hi; apply Finsupp.not_mem_support_iff.mp
#align mv_polynomial.homogeneous_submodule_mul MvPolynomial.homogeneousSubmodule_mul

section

variable [CommSemiring R]

theorem isHomogeneous_monomial (d : σ →₀ ℕ) (r : R) (n : ℕ) (hn : ∑ i in d.support, d i = n) :
    IsHomogeneous (monomial d r) n := by
  intro c hc
  -- ⊢ ∑ i in c.support, ↑c i = n
  classical
  rw [coeff_monomial] at hc
  split_ifs at hc with h
  · subst c
    exact hn
  · contradiction
#align mv_polynomial.is_homogeneous_monomial MvPolynomial.isHomogeneous_monomial

variable (σ)

theorem isHomogeneous_of_totalDegree_zero {p : MvPolynomial σ R} (hp : p.totalDegree = 0) :
    IsHomogeneous p 0 := by
  erw [totalDegree, Finset.sup_eq_bot_iff] at hp
  -- ⊢ IsHomogeneous p 0
  -- we have to do this in two steps to stop simp changing bot to zero
  simp_rw [mem_support_iff] at hp
  -- ⊢ IsHomogeneous p 0
  exact hp
  -- 🎉 no goals
#align mv_polynomial.is_homogeneous_of_total_degree_zero MvPolynomial.isHomogeneous_of_totalDegree_zero

theorem isHomogeneous_C (r : R) : IsHomogeneous (C r : MvPolynomial σ R) 0 := by
  apply isHomogeneous_monomial
  -- ⊢ ∑ i in 0.support, ↑0 i = 0
  simp only [Finsupp.zero_apply, Finset.sum_const_zero]
  -- 🎉 no goals
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
  -- ⊢ ∑ i_1 in (Finsupp.single i 1).support, ↑(Finsupp.single i 1) i_1 = 1
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton]
  -- ⊢ ↑(Finsupp.single i 1) i = 1
  exact Finsupp.single_eq_same
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mv_polynomial.is_homogeneous_X MvPolynomial.isHomogeneous_X

end

namespace IsHomogeneous

variable [CommSemiring R] {φ ψ : MvPolynomial σ R} {m n : ℕ}

theorem coeff_eq_zero (hφ : IsHomogeneous φ n) (d : σ →₀ ℕ) (hd : ∑ i in d.support, d i ≠ n) :
    coeff d φ = 0 := by
  have aux := mt (@hφ d) hd
  -- ⊢ coeff d φ = 0
  classical
  rwa [Classical.not_not] at aux
#align mv_polynomial.is_homogeneous.coeff_eq_zero MvPolynomial.IsHomogeneous.coeff_eq_zero

theorem inj_right (hm : IsHomogeneous φ m) (hn : IsHomogeneous φ n) (hφ : φ ≠ 0) : m = n := by
  obtain ⟨d, hd⟩ : ∃ d, coeff d φ ≠ 0 := exists_coeff_ne_zero hφ
  -- ⊢ m = n
  rw [← hm hd, ← hn hd]
  -- 🎉 no goals
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
  rw [totalDegree]
  -- ⊢ (Finset.sup (support φ) fun s => Finsupp.sum s fun x e => e) = n
  apply le_antisymm
  -- ⊢ (Finset.sup (support φ) fun s => Finsupp.sum s fun x e => e) ≤ n
  · apply Finset.sup_le
    -- ⊢ ∀ (b : σ →₀ ℕ), b ∈ support φ → (Finsupp.sum b fun x e => e) ≤ n
    intro d hd
    -- ⊢ (Finsupp.sum d fun x e => e) ≤ n
    rw [mem_support_iff] at hd
    -- ⊢ (Finsupp.sum d fun x e => e) ≤ n
    rw [Finsupp.sum, hφ hd]
    -- 🎉 no goals
  · obtain ⟨d, hd⟩ : ∃ d, coeff d φ ≠ 0 := exists_coeff_ne_zero h
    -- ⊢ n ≤ Finset.sup (support φ) fun s => Finsupp.sum s fun x e => e
    simp only [← hφ hd, Finsupp.sum]
    -- ⊢ ∑ x in d.support, ↑d x ≤ Finset.sup (support φ) fun s => ∑ x in s.support, ↑ …
    replace hd := Finsupp.mem_support_iff.mpr hd
    -- ⊢ ∑ x in d.support, ↑d x ≤ Finset.sup (support φ) fun s => ∑ x in s.support, ↑ …
    -- Porting note: Original proof did not define `f`
    exact Finset.le_sup (f := fun s ↦ ∑ x in s.support, (⇑s) x) hd
    -- 🎉 no goals
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
  (Submodule.subtype _).comp <| Finsupp.restrictDom _ _ { d | ∑ i in d.support, d i = n }
#align mv_polynomial.homogeneous_component MvPolynomial.homogeneousComponent

section HomogeneousComponent

open Finset

variable [CommSemiring R] (n : ℕ) (φ ψ : MvPolynomial σ R)

theorem coeff_homogeneousComponent (d : σ →₀ ℕ) :
    coeff d (homogeneousComponent n φ) = if (∑ i in d.support, d i) = n then coeff d φ else 0 :=
  Finsupp.filter_apply (fun d : σ →₀ ℕ => ∑ i in d.support, d i = n) φ d
#align mv_polynomial.coeff_homogeneous_component MvPolynomial.coeff_homogeneousComponent

theorem homogeneousComponent_apply :
    homogeneousComponent n φ =
      ∑ d in φ.support.filter fun d => ∑ i in d.support, d i = n, monomial d (coeff d φ) :=
  Finsupp.filter_eq_sum (fun d : σ →₀ ℕ => ∑ i in d.support, d i = n) φ
#align mv_polynomial.homogeneous_component_apply MvPolynomial.homogeneousComponent_apply

theorem homogeneousComponent_isHomogeneous : (homogeneousComponent n φ).IsHomogeneous n := by
  intro d hd
  -- ⊢ ∑ i in d.support, ↑d i = n
  contrapose! hd
  -- ⊢ coeff d (↑(homogeneousComponent n) φ) = 0
  rw [coeff_homogeneousComponent, if_neg hd]
  -- 🎉 no goals
#align mv_polynomial.homogeneous_component_is_homogeneous MvPolynomial.homogeneousComponent_isHomogeneous

@[simp]
theorem homogeneousComponent_zero : homogeneousComponent 0 φ = C (coeff 0 φ) := by
  ext1 d
  -- ⊢ coeff d (↑(homogeneousComponent 0) φ) = coeff d (↑C (coeff 0 φ))
  rcases em (d = 0) with (rfl | hd)
  -- ⊢ coeff 0 (↑(homogeneousComponent 0) φ) = coeff 0 (↑C (coeff 0 φ))
  classical
  · simp only [coeff_homogeneousComponent, sum_eq_zero_iff, Finsupp.zero_apply, if_true, coeff_C,
      eq_self_iff_true, forall_true_iff]
  · rw [coeff_homogeneousComponent, if_neg, coeff_C, if_neg (Ne.symm hd)]
    simp only [FunLike.ext_iff, Finsupp.zero_apply] at hd
    simp [hd]
#align mv_polynomial.homogeneous_component_zero MvPolynomial.homogeneousComponent_zero

@[simp]
theorem homogeneousComponent_C_mul (n : ℕ) (r : R) :
    homogeneousComponent n (C r * φ) = C r * homogeneousComponent n φ := by
  simp only [C_mul', LinearMap.map_smul]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align mv_polynomial.homogeneous_component_C_mul MvPolynomial.homogeneousComponent_C_mul

theorem homogeneousComponent_eq_zero'
    (h : ∀ d : σ →₀ ℕ, d ∈ φ.support → ∑ i in d.support, d i ≠ n) :
    homogeneousComponent n φ = 0 := by
  rw [homogeneousComponent_apply, sum_eq_zero]
  -- ⊢ ∀ (x : σ →₀ ℕ), x ∈ filter (fun d => ∑ i in d.support, ↑d i = n) (support φ) …
  intro d hd; rw [mem_filter] at hd
  -- ⊢ ↑(monomial d) (coeff d φ) = 0
              -- ⊢ ↑(monomial d) (coeff d φ) = 0
  exfalso; exact h _ hd.1 hd.2
  -- ⊢ False
           -- 🎉 no goals
#align mv_polynomial.homogeneous_component_eq_zero' MvPolynomial.homogeneousComponent_eq_zero'

theorem homogeneousComponent_eq_zero (h : φ.totalDegree < n) : homogeneousComponent n φ = 0 := by
  apply homogeneousComponent_eq_zero'
  -- ⊢ ∀ (d : σ →₀ ℕ), d ∈ support φ → ∑ i in d.support, ↑d i ≠ n
  rw [totalDegree, Finset.sup_lt_iff] at h
  -- ⊢ ∀ (d : σ →₀ ℕ), d ∈ support φ → ∑ i in d.support, ↑d i ≠ n
  · intro d hd
    -- ⊢ ∑ i in d.support, ↑d i ≠ n
    exact ne_of_lt (h d hd)
    -- 🎉 no goals
  · exact lt_of_le_of_lt (Nat.zero_le _) h
    -- 🎉 no goals
#align mv_polynomial.homogeneous_component_eq_zero MvPolynomial.homogeneousComponent_eq_zero

theorem sum_homogeneousComponent :
    (∑ i in range (φ.totalDegree + 1), homogeneousComponent i φ) = φ := by
  ext1 d
  -- ⊢ coeff d (∑ i in range (totalDegree φ + 1), ↑(homogeneousComponent i) φ) = co …
  suffices φ.totalDegree < d.support.sum d → 0 = coeff d φ by
    simpa [coeff_sum, coeff_homogeneousComponent]
  exact fun h => (coeff_eq_zero_of_totalDegree_lt h).symm
  -- 🎉 no goals
#align mv_polynomial.sum_homogeneous_component MvPolynomial.sum_homogeneousComponent

theorem homogeneousComponent_homogeneous_polynomial (m n : ℕ) (p : MvPolynomial σ R)
    (h : p ∈ homogeneousSubmodule σ R n) : homogeneousComponent m p = if m = n then p else 0 := by
  simp only [mem_homogeneousSubmodule] at h
  -- ⊢ ↑(homogeneousComponent m) p = if m = n then p else 0
  ext x
  -- ⊢ coeff x (↑(homogeneousComponent m) p) = coeff x (if m = n then p else 0)
  rw [coeff_homogeneousComponent]
  -- ⊢ (if ∑ i in x.support, ↑x i = m then coeff x p else 0) = coeff x (if m = n th …
  by_cases zero_coeff : coeff x p = 0
  -- ⊢ (if ∑ i in x.support, ↑x i = m then coeff x p else 0) = coeff x (if m = n th …
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
#align mv_polynomial.homogeneous_component_homogeneous_polynomial MvPolynomial.homogeneousComponent_homogeneous_polynomial

end HomogeneousComponent

end

end MvPolynomial
