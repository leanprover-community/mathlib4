/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/
import Mathlib.Algebra.MvPolynomial.Degrees

#align_import data.mv_polynomial.variables from "leanprover-community/mathlib"@"2f5b500a507264de86d666a5f87ddb976e2d8de4"

/-!
# Variables of polynomials

This file establishes many results about the variable sets of a multivariate polynomial.

The *variable set* of a polynomial $P \in R[X]$ is a `Finset` containing each $x \in X$
that appears in a monomial in $P$.


## Main declarations

* `MvPolynomial.vars p` : the finset of variables occurring in `p`.
  For example if `p = x⁴y+yz` then `vars p = {x, y, z}`

## Notation

As in other polynomial files, we typically use the notation:

+ `σ τ : Type*` (indexing the variables)

+ `R : Type*` `[CommSemiring R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `MvPolynomial σ R` which mathematicians might call `X^s`

+ `r : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : MvPolynomial σ R`

-/


noncomputable section

open Set Function Finsupp AddMonoidAlgebra

universe u v w

variable {R : Type u} {S : Type v}

namespace MvPolynomial

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section CommSemiring

variable [CommSemiring R] {p q : MvPolynomial σ R}

section Vars

/-! ### `vars` -/


/-- `vars p` is the set of variables appearing in the polynomial `p` -/
def vars (p : MvPolynomial σ R) : Finset σ :=
  letI := Classical.decEq σ
  p.degrees.toFinset
#align mv_polynomial.vars MvPolynomial.vars

theorem vars_def [DecidableEq σ] (p : MvPolynomial σ R) : p.vars = p.degrees.toFinset := by
  rw [vars]
  convert rfl
#align mv_polynomial.vars_def MvPolynomial.vars_def

@[simp]
theorem vars_0 : (0 : MvPolynomial σ R).vars = ∅ := by
  classical rw [vars_def, degrees_zero, Multiset.toFinset_zero]
#align mv_polynomial.vars_0 MvPolynomial.vars_0

@[simp]
theorem vars_monomial (h : r ≠ 0) : (monomial s r).vars = s.support := by
  classical rw [vars_def, degrees_monomial_eq _ _ h, Finsupp.toFinset_toMultiset]
#align mv_polynomial.vars_monomial MvPolynomial.vars_monomial

@[simp]
theorem vars_C : (C r : MvPolynomial σ R).vars = ∅ := by
  classical rw [vars_def, degrees_C, Multiset.toFinset_zero]
set_option linter.uppercaseLean3 false in
#align mv_polynomial.vars_C MvPolynomial.vars_C

@[simp]
theorem vars_X [Nontrivial R] : (X n : MvPolynomial σ R).vars = {n} := by
  rw [X, vars_monomial (one_ne_zero' R), Finsupp.support_single_ne_zero _ (one_ne_zero' ℕ)]
set_option linter.uppercaseLean3 false in
#align mv_polynomial.vars_X MvPolynomial.vars_X

theorem mem_vars (i : σ) : i ∈ p.vars ↔ ∃ d ∈ p.support, i ∈ d.support := by
  classical simp only [vars_def, Multiset.mem_toFinset, mem_degrees, mem_support_iff, exists_prop]
#align mv_polynomial.mem_vars MvPolynomial.mem_vars

theorem mem_support_not_mem_vars_zero {f : MvPolynomial σ R} {x : σ →₀ ℕ} (H : x ∈ f.support)
    {v : σ} (h : v ∉ vars f) : x v = 0 := by
  contrapose! h
  exact (mem_vars v).mpr ⟨x, H, Finsupp.mem_support_iff.mpr h⟩
#align mv_polynomial.mem_support_not_mem_vars_zero MvPolynomial.mem_support_not_mem_vars_zero

theorem vars_add_subset [DecidableEq σ] (p q : MvPolynomial σ R) :
    (p + q).vars ⊆ p.vars ∪ q.vars := by
  intro x hx
  simp only [vars_def, Finset.mem_union, Multiset.mem_toFinset] at hx ⊢
  simpa using Multiset.mem_of_le (degrees_add _ _) hx
#align mv_polynomial.vars_add_subset MvPolynomial.vars_add_subset

theorem vars_add_of_disjoint [DecidableEq σ] (h : Disjoint p.vars q.vars) :
    (p + q).vars = p.vars ∪ q.vars := by
  refine (vars_add_subset p q).antisymm fun x hx => ?_
  simp only [vars_def, Multiset.disjoint_toFinset] at h hx ⊢
  rwa [degrees_add_of_disjoint h, Multiset.toFinset_union]
#align mv_polynomial.vars_add_of_disjoint MvPolynomial.vars_add_of_disjoint

section Mul

theorem vars_mul [DecidableEq σ] (φ ψ : MvPolynomial σ R) : (φ * ψ).vars ⊆ φ.vars ∪ ψ.vars := by
  simp_rw [vars_def, ← Multiset.toFinset_add, Multiset.toFinset_subset]
  exact Multiset.subset_of_le (degrees_mul φ ψ)
#align mv_polynomial.vars_mul MvPolynomial.vars_mul

@[simp]
theorem vars_one : (1 : MvPolynomial σ R).vars = ∅ :=
  vars_C
#align mv_polynomial.vars_one MvPolynomial.vars_one

theorem vars_pow (φ : MvPolynomial σ R) (n : ℕ) : (φ ^ n).vars ⊆ φ.vars := by
  classical
  induction' n with n ih
  · simp
  · rw [pow_succ']
    apply Finset.Subset.trans (vars_mul _ _)
    exact Finset.union_subset (Finset.Subset.refl _) ih
#align mv_polynomial.vars_pow MvPolynomial.vars_pow

/-- The variables of the product of a family of polynomials
are a subset of the union of the sets of variables of each polynomial.
-/
theorem vars_prod {ι : Type*} [DecidableEq σ] {s : Finset ι} (f : ι → MvPolynomial σ R) :
    (∏ i ∈ s, f i).vars ⊆ s.biUnion fun i => (f i).vars := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert hs hsub =>
    simp only [hs, Finset.biUnion_insert, Finset.prod_insert, not_false_iff]
    apply Finset.Subset.trans (vars_mul _ _)
    exact Finset.union_subset_union (Finset.Subset.refl _) hsub
#align mv_polynomial.vars_prod MvPolynomial.vars_prod

section IsDomain

variable {A : Type*} [CommRing A] [IsDomain A]

theorem vars_C_mul (a : A) (ha : a ≠ 0) (φ : MvPolynomial σ A) :
    (C a * φ : MvPolynomial σ A).vars = φ.vars := by
  ext1 i
  simp only [mem_vars, exists_prop, mem_support_iff]
  apply exists_congr
  intro d
  apply and_congr _ Iff.rfl
  rw [coeff_C_mul, mul_ne_zero_iff, eq_true ha, true_and_iff]
set_option linter.uppercaseLean3 false in
#align mv_polynomial.vars_C_mul MvPolynomial.vars_C_mul

end IsDomain

end Mul

section Sum

variable {ι : Type*} (t : Finset ι) (φ : ι → MvPolynomial σ R)

theorem vars_sum_subset [DecidableEq σ] :
    (∑ i ∈ t, φ i).vars ⊆ Finset.biUnion t fun i => (φ i).vars := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert has hsum =>
    rw [Finset.biUnion_insert, Finset.sum_insert has]
    refine Finset.Subset.trans
      (vars_add_subset _ _) (Finset.union_subset_union (Finset.Subset.refl _) ?_)
    assumption
#align mv_polynomial.vars_sum_subset MvPolynomial.vars_sum_subset

theorem vars_sum_of_disjoint [DecidableEq σ] (h : Pairwise <| (Disjoint on fun i => (φ i).vars)) :
    (∑ i ∈ t, φ i).vars = Finset.biUnion t fun i => (φ i).vars := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert has hsum =>
    rw [Finset.biUnion_insert, Finset.sum_insert has, vars_add_of_disjoint, hsum]
    unfold Pairwise onFun at h
    rw [hsum]
    simp only [Finset.disjoint_iff_ne] at h ⊢
    intro v hv v2 hv2
    rw [Finset.mem_biUnion] at hv2
    rcases hv2 with ⟨i, his, hi⟩
    refine h ?_ _ hv _ hi
    rintro rfl
    contradiction
#align mv_polynomial.vars_sum_of_disjoint MvPolynomial.vars_sum_of_disjoint

end Sum

section Map

variable [CommSemiring S] (f : R →+* S)
variable (p)

theorem vars_map : (map f p).vars ⊆ p.vars := by classical simp [vars_def, degrees_map]
#align mv_polynomial.vars_map MvPolynomial.vars_map

variable {f}

theorem vars_map_of_injective (hf : Injective f) : (map f p).vars = p.vars := by
  simp [vars, degrees_map_of_injective _ hf]
#align mv_polynomial.vars_map_of_injective MvPolynomial.vars_map_of_injective

theorem vars_monomial_single (i : σ) {e : ℕ} {r : R} (he : e ≠ 0) (hr : r ≠ 0) :
    (monomial (Finsupp.single i e) r).vars = {i} := by
  rw [vars_monomial hr, Finsupp.support_single_ne_zero _ he]
#align mv_polynomial.vars_monomial_single MvPolynomial.vars_monomial_single

theorem vars_eq_support_biUnion_support [DecidableEq σ] :
    p.vars = p.support.biUnion Finsupp.support := by
  ext i
  rw [mem_vars, Finset.mem_biUnion]
#align mv_polynomial.vars_eq_support_bUnion_support MvPolynomial.vars_eq_support_biUnion_support

end Map

end Vars

section EvalVars

/-! ### `vars` and `eval` -/


variable [CommSemiring S]

theorem eval₂Hom_eq_constantCoeff_of_vars (f : R →+* S) {g : σ → S} {p : MvPolynomial σ R}
    (hp : ∀ i ∈ p.vars, g i = 0) : eval₂Hom f g p = f (constantCoeff p) := by
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, eval₂Hom_monomial]
  by_cases h0 : constantCoeff p = 0
  on_goal 1 =>
    rw [h0, f.map_zero, Finset.sum_eq_zero]
    intro d hd
  on_goal 2 =>
    rw [Finset.sum_eq_single (0 : σ →₀ ℕ)]
    · rw [Finsupp.prod_zero_index, mul_one]
      rfl
    on_goal 1 => intro d hd hd0
  on_goal 3 =>
    rw [constantCoeff_eq, coeff, ← Ne, ← Finsupp.mem_support_iff] at h0
    intro
    contradiction
  repeat'
    obtain ⟨i, hi⟩ : Finset.Nonempty (Finsupp.support d) := by
      rw [constantCoeff_eq, coeff, ← Finsupp.not_mem_support_iff] at h0
      rw [Finset.nonempty_iff_ne_empty, Ne, Finsupp.support_eq_empty]
      rintro rfl
      contradiction
    rw [Finsupp.prod, Finset.prod_eq_zero hi, mul_zero]
    rw [hp, zero_pow (Finsupp.mem_support_iff.1 hi)]
    rw [mem_vars]
    exact ⟨d, hd, hi⟩
#align mv_polynomial.eval₂_hom_eq_constant_coeff_of_vars MvPolynomial.eval₂Hom_eq_constantCoeff_of_vars

theorem aeval_eq_constantCoeff_of_vars [Algebra R S] {g : σ → S} {p : MvPolynomial σ R}
    (hp : ∀ i ∈ p.vars, g i = 0) : aeval g p = algebraMap _ _ (constantCoeff p) :=
  eval₂Hom_eq_constantCoeff_of_vars _ hp
#align mv_polynomial.aeval_eq_constant_coeff_of_vars MvPolynomial.aeval_eq_constantCoeff_of_vars

theorem eval₂Hom_congr' {f₁ f₂ : R →+* S} {g₁ g₂ : σ → S} {p₁ p₂ : MvPolynomial σ R} :
    f₁ = f₂ →
      (∀ i, i ∈ p₁.vars → i ∈ p₂.vars → g₁ i = g₂ i) →
        p₁ = p₂ → eval₂Hom f₁ g₁ p₁ = eval₂Hom f₂ g₂ p₂ := by
  rintro rfl h rfl
  rw [p₁.as_sum]
  simp only [map_sum, eval₂Hom_monomial]
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  simp only [Finsupp.prod]
  apply Finset.prod_congr rfl
  intro i hi
  have : i ∈ p₁.vars := by
    rw [mem_vars]
    exact ⟨d, hd, hi⟩
  rw [h i this this]
#align mv_polynomial.eval₂_hom_congr' MvPolynomial.eval₂Hom_congr'

/-- If `f₁` and `f₂` are ring homs out of the polynomial ring and `p₁` and `p₂` are polynomials,
  then `f₁ p₁ = f₂ p₂` if `p₁ = p₂` and `f₁` and `f₂` are equal on `R` and on the variables
  of `p₁`.  -/
theorem hom_congr_vars {f₁ f₂ : MvPolynomial σ R →+* S} {p₁ p₂ : MvPolynomial σ R}
    (hC : f₁.comp C = f₂.comp C) (hv : ∀ i, i ∈ p₁.vars → i ∈ p₂.vars → f₁ (X i) = f₂ (X i))
    (hp : p₁ = p₂) : f₁ p₁ = f₂ p₂ :=
  calc
    f₁ p₁ = eval₂Hom (f₁.comp C) (f₁ ∘ X) p₁ := RingHom.congr_fun (by ext <;> simp) _
    _ = eval₂Hom (f₂.comp C) (f₂ ∘ X) p₂ := eval₂Hom_congr' hC hv hp
    _ = f₂ p₂ := RingHom.congr_fun (by ext <;> simp) _
#align mv_polynomial.hom_congr_vars MvPolynomial.hom_congr_vars

theorem exists_rename_eq_of_vars_subset_range (p : MvPolynomial σ R) (f : τ → σ) (hfi : Injective f)
    (hf : ↑p.vars ⊆ Set.range f) : ∃ q : MvPolynomial τ R, rename f q = p :=
  ⟨aeval (fun i : σ => Option.elim' 0 X <| partialInv f i) p,
    by
      show (rename f).toRingHom.comp _ p = RingHom.id _ p
      refine hom_congr_vars ?_ ?_ ?_
      · ext1
        simp [algebraMap_eq]
      · intro i hip _
        rcases hf hip with ⟨i, rfl⟩
        simp [partialInv_left hfi]
      · rfl⟩
#align mv_polynomial.exists_rename_eq_of_vars_subset_range MvPolynomial.exists_rename_eq_of_vars_subset_range

theorem vars_rename [DecidableEq τ] (f : σ → τ) (φ : MvPolynomial σ R) :
    (rename f φ).vars ⊆ φ.vars.image f := by
  classical
  intro i hi
  simp only [vars_def, exists_prop, Multiset.mem_toFinset, Finset.mem_image] at hi ⊢
  simpa only [Multiset.mem_map] using degrees_rename _ _ hi
#align mv_polynomial.vars_rename MvPolynomial.vars_rename

theorem mem_vars_rename (f : σ → τ) (φ : MvPolynomial σ R) {j : τ} (h : j ∈ (rename f φ).vars) :
    ∃ i : σ, i ∈ φ.vars ∧ f i = j := by
  classical
  simpa only [exists_prop, Finset.mem_image] using vars_rename f φ h
#align mv_polynomial.mem_vars_rename MvPolynomial.mem_vars_rename

end EvalVars

end CommSemiring

end MvPolynomial
