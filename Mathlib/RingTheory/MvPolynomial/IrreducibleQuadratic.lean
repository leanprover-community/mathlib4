/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Johan Commelin
-/
module

public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Tactic.ComputeDegree

/-!
# Irreducibility of linear and quadratic polynomials

* For `c : n →₀ R`, `MvPolynomial.sum_smul_X c` is the linear polynomial
  $\sum_i c_i X_i$ of $R[X_1\dots,X_n]$.

* `MvPolynomial.irreducible_sum_smul_X` : if the support of `c` is nontrivial,
  if `R` is a domain,
  and if the only common divisors to all `c i` are units,
  then `MvPolynomial.sum_smul_X c` is irreducible.

* For `c : n →₀ R`, `MvPolynomial.sum_X_mul_Y c` is the quadratic polynomial
  $\sum_i c_i X_i Y_i$ of $R[X_1\dots,X_n,Y_1,\dots,Y_n]$.
  It is constructed as an object of `MvPolynomial (n ⊕ n) R`,
  the first component of `n ⊕ n` represents the `X` indeterminates,
  and the second component represents the `Y` indeterminates.

* `MvPolynomial.irreducible_sum_smul_X_mul_Y` :
  if the support of `c` is nontrivial,
  the ring `R` is a domain,
  and the only divisors common to all `c i` are units,
  then `MvPolynomial.sum_smul_X_mul_Y c` is irreducible.

## TODO

* Treat the case of diagonal quadratic polynomials,
  $ \sum c_i X_i ^ 2$. For irreducibility, one will need that
  there are at least 3 nonzero values of `c`,
  and that the only common divisors to all `c i` are units.

* Addition of quadratic polynomial of both kinds are relevant too.

* Prove, over a field, that a polynomial of degree at most 2 whose quadratic
  part has rank at least 3 is irreducible.

* Cases of ranks 1 and 2 can be treated as well, but the answer depends
  on the terms of degree 0 and 1.
  Eg, $X^2-Y$ is irreducible, but $X^2$, $X^2-1$, $X^2-Y^2$, $X^2-Y$ are not.
  And $X^2+Y^2$ is irreducible over the reals but not over the complex numbers.

-/

@[expose] public section

namespace MvPolynomial

open scoped Polynomial

section

variable {n : Type*} {R : Type*} [CommRing R]

lemma irreducible_mul_X_add [IsDomain R]
    (f g : MvPolynomial n R) (i : n) (hf0 : f ≠ 0) (hif : i ∉ f.vars) (hig : i ∉ g.vars)
    (h : IsRelPrime f g) :
    Irreducible (f * X i + g) := by
  classical
  let e₁ := renameEquiv R (σ := n) (Equiv.optionSubtypeNe i).symm
  let e₂ := optionEquivLeft R {j // j ≠ i}
  let e := e₁.trans e₂
  have heX : e (X i) = .X := by simp [e, e₁, e₂, optionEquivLeft_X_none]
  suffices ∀ {p}, i ∉ p.vars → e p = .C ((e p).coeff 0) by
    rw [← MulEquiv.irreducible_iff e, map_add, map_mul, heX, this hif, this hig,
      ← Polynomial.smul_eq_C_mul]
    apply Polynomial.irreducible_smul_X_add_C
    · contrapose! hf0
      apply e.injective
      rw [this hif, hf0, map_zero, map_zero]
    · intro p hpf hpg
      refine isUnit_of_map_unit Polynomial.C _ (isUnit_of_map_unit e.symm _ ?_)
      apply h
      · replace hpf := map_dvd e.symm <| map_dvd Polynomial.C hpf
        rwa [← this hif, e.symm_apply_apply] at hpf
      · replace hpg := map_dvd e.symm <| map_dvd Polynomial.C hpg
        rwa [← this hig, e.symm_apply_apply] at hpg
  intro p hp
  apply Polynomial.eq_C_of_degree_le_zero
  rw [Polynomial.degree_le_iff_coeff_zero]
  intro m hm
  ext d
  suffices ((rename (Equiv.optionSubtypeNe i).symm) p).coeff (d.optionElim m) = 0 by
    simpa [e, e₁, e₂, optionEquivLeft_coeff_coeff']
  rw [coeff_rename_eq_zero]
  intro d' hd'
  contrapose! hp
  rw [mem_vars]
  rw [← mem_support_iff] at hp
  refine ⟨_, hp, ?_⟩
  rw [Finsupp.mem_support_iff]
  obtain rfl : d' i = m := by simpa [Finsupp.mapDomain_equiv_apply] using congr($hd' none)
  simp_all [ne_of_gt]

/-- A multivariate polynomial `f` whose support is nontrivial,
such that some variable `i` appears with exponent `1` in one nontrivial monomial,
whose monomials have disjoint supports, and which is primitive, is irreducible. -/
lemma irreducible_of_disjoint_support [IsDomain R]
    {f : MvPolynomial n R}
    (nontrivial : f.support.Nontrivial)
    {d : n →₀ ℕ} (hd : d ∈ f.support) {i : n} (hdi : d i = 1)
    -- Question — should one state this `disjoint` hypothesis as:
    --  Set.Pairwise (f.support : Set (n →₀ ℕ)) (fun x y ↦ Disjoint x.support y.support))
    (disjoint : ∀ d₁ ∈ f.support, ∀ d₂ ∈ f.support, ∀ i, i ∈ d₁.support → i ∈ d₂.support → d₁ = d₂)
    (isPrimitive : ∀ r, (∀ d, r ∣ f.coeff d) → IsUnit r) :
    Irreducible f := by
  classical
  have hi : i ∈ d.support := by simp [Finsupp.mem_support_iff, hdi]
  have hfd : f.coeff d ≠ 0 := by simpa [mem_support_iff] using hd
  let d₀ := d - .single i 1
  have hd₀ : d = d₀ + .single i 1 := by
    rw [Finsupp.sub_add_single_one_cancel (by simp [hdi])]
  let φ : MvPolynomial n R := monomial d₀ (f.coeff d)
  let ψ : MvPolynomial n R := f - φ * X i
  have hf : f = φ * X i + ψ := by grind only
  have hdφX (k) : (φ * X i).coeff k = if k = d then f.coeff d else 0 := by
    simp only [X, monomial_mul, ← hd₀, mul_one, coeff_monomial, eq_comm (a := k), φ]
  have hdψ (k) : ψ.coeff k = if k = d then 0 else f.coeff k := by
    simp +contextual [ψ, hdφX, sub_eq_iff_eq_add, ite_add_ite]
  have hψsupp : ψ.support = f.support.erase d := by ext; simp [mem_support_iff, hdψ]
  rw [hf]
  apply irreducible_mul_X_add
  · grind only [monomial_eq_zero]
  · simp [φ, hfd, d₀, hdi]
  · grind only [mem_vars, Finset.mem_erase]
  · intro p hpφ hpψ
    simp_rw [φ, dvd_monomial_iff_exists hfd] at hpφ
    obtain ⟨m, b, hm, hb, rfl⟩ := hpφ
    obtain ⟨q, hq⟩ := hpψ
    obtain ⟨d₂, hd₂, H⟩ := nontrivial.exists_ne d
    obtain rfl : m = 0 := by
      ext j
      rw [Finsupp.zero_apply]
      have aux : coeff d₂ ψ ≠ 0 := by simpa only [hdψ, H, ↓reduceIte,  mem_support_iff] using hd₂
      simp only [hq, coeff_monomial_mul', ne_eq, ite_eq_right_iff, Classical.not_imp] at aux
      replace aux := aux.1 j
      specialize hm j
      simp only [Finsupp.coe_tsub, Pi.sub_apply, d₀] at hm
      contrapose! H
      apply disjoint d₂ hd₂ d hd j <;> grind only [= Finsupp.mem_support_iff]
    simp_rw [isUnit_iff_eq_C_of_isReduced, ← C_apply, C_inj]
    refine ⟨b, ?_, rfl⟩
    apply isPrimitive
    intro k
    obtain rfl | hk := eq_or_ne k d
    · exact hb
    simp [hf, hk, hq, hdφX]

end

section
/-! ## The quadratic polynomial $$\sum_{i=1}^n X_i Y_i$$. -/

open Polynomial

variable {n : Type*} {R : Type*} [CommRing R]

/-- The linear polynomial $$\sum_i c_i X_i$$. -/
noncomputable def sum_smul_X :
    (n →₀ R) →ₗ[R] MvPolynomial n R :=
  Finsupp.linearCombination R X

variable (c : n →₀ R)

theorem irreducible_sum_smul_X [IsDomain R]
    (hc_nontrivial : c.support.Nontrivial)
    (hc_gcd : ∀ r, (∀ i, r ∣ c i) → IsUnit r) :
    Irreducible (sum_smul_X c) := by
  classical
  let ι : n ↪ (n →₀ ℕ) :=
    ⟨fun i ↦ .single i 1, fun i j ↦ by simp +contextual [Finsupp.single_eq_single_iff]⟩
  -- unfortunate defeq abuse... we should have an `.embDomain`-like constructor for MvPolys
  have aux : sum_smul_X c = c.embDomain ι := by
    rw [← Finsupp.sum_single (Finsupp.embDomain _ _)]
    simp [Finsupp.sum_embDomain, sum_smul_X, X,
      Finsupp.linearCombination_apply, smul_monomial, ι]
    rfl
  have hcoeff (i : n) : coeff (ι i) (sum_smul_X c) = c i := by
    simp [aux, coeff, Finsupp.embDomain_apply]
  have hsupp : (sum_smul_X c).support = c.support.map ι := by
    rw [aux, support, Finsupp.support_embDomain]
  obtain ⟨a, ha⟩ := hc_nontrivial.nonempty
  apply irreducible_of_disjoint_support (d := ι a) (i := a)
  · rwa [hsupp, Finset.map_nontrivial]
  · rwa [MvPolynomial.mem_support_iff, hcoeff, ← Finsupp.mem_support_iff]
  · simp [ι]
  · simp +contextual [hsupp, ι, Finsupp.single_apply]
  · intro r hr
    apply hc_gcd
    intro i
    simpa [hcoeff] using hr (ι i)

/-- The quadratic polynomial $$\sum_i c_i X_i Y_i$$. -/
noncomputable def sum_smul_X_mul_Y :
    (n →₀ R) →ₗ[R] MvPolynomial (n ⊕ n) R :=
  Finsupp.linearCombination R (fun i ↦ X (.inl i) * X (.inr i))

variable (c : n →₀ R)

theorem irreducible_sum_smul_X_mul_Y [IsDomain R]
    (hc : c.support.Nontrivial)
    (h_dvd : ∀ r, (∀ i, r ∣ c i) → IsUnit r) :
    Irreducible (sum_smul_X_mul_Y c) := by
  classical
  let ι : n ↪ ((n ⊕ n) →₀ ℕ) :=
    ⟨fun i ↦ .single (.inl i) 1 + .single (.inr i) 1,
     fun i j ↦ by classical simp +contextual [Finsupp.ext_iff, Finsupp.single_apply, ite_eq_iff']⟩
  -- unfortunate defeq abuse... we should have an `.embDomain`-like constructor for MvPolys
  have aux : sum_smul_X_mul_Y c = c.embDomain ι := by
    rw [← Finsupp.sum_single (Finsupp.embDomain _ _)]
    simp [Finsupp.sum_embDomain, sum_smul_X_mul_Y, X, monomial_mul,
      Finsupp.linearCombination_apply, smul_monomial, ι]
    rfl
  have hcoeff (i : n) : coeff (ι i) (sum_smul_X_mul_Y c) = c i := by
    simp [aux, coeff, Finsupp.embDomain_apply]
  have hsupp : (sum_smul_X_mul_Y c).support = c.support.map ι := by
    rw [aux, support, Finsupp.support_embDomain]
  obtain ⟨a, ha⟩ := hc.nonempty
  apply irreducible_of_disjoint_support (d := ι a) (i := .inl a)
  · rwa [hsupp, Finset.map_nontrivial]
  · rwa [MvPolynomial.mem_support_iff, hcoeff, ← Finsupp.mem_support_iff]
  · simp [ι]
  · simp +contextual [hsupp, ι, Finsupp.single_apply]
  · intro r hr
    apply h_dvd
    intro i
    simpa [hcoeff] using hr (ι i)

end

end MvPolynomial
