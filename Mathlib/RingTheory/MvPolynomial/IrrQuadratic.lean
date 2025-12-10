/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
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

theorem Function.nontrivial_of_nontrivial (α β : Type*) [Nontrivial (α → β)] :
    Nontrivial β := by
  obtain ⟨x, y, h⟩ := exists_pair_ne (α → β)
  rw [ne_eq, funext_iff, not_forall] at h
  obtain ⟨a, h⟩ := h
  exact nontrivial_of_ne _ _ h

theorem Finsupp.nontrivial_of_nontrivial (α β : Type*) [Zero β] [Nontrivial (α →₀ β)] :
    Nontrivial β := by
  obtain ⟨x, y, h⟩ := exists_pair_ne (α →₀ β)
  rw [ne_eq, Finsupp.ext_iff, not_forall] at h
  obtain ⟨a, h⟩ := h
  exact nontrivial_of_ne _ _ h

namespace Polynomial

variable {R : Type*} [CommRing R]

-- move this
instance : IsLocalHom (C : _ →+* Polynomial R) where
  map_nonunit := by classical simp +contextual [isUnit_iff_coeff_isUnit_isNilpotent, coeff_C]

end Polynomial

namespace MvPolynomial

open scoped Polynomial

section

variable {n : Type*} {R : Type*} [CommRing R]

-- move this
theorem optionEquivLeft_coeff_coeff'
    (p : MvPolynomial (Option n) R) (m : ℕ) (d : n →₀ ℕ) :
    coeff d (((optionEquivLeft R n) p).coeff m) = p.coeff (d.optionElim m) := by
  induction p using MvPolynomial.induction_on' generalizing d m with
  | monomial j r =>
    rw [optionEquivLeft_monomial]
    classical
    simp +contextual [Finsupp.ext_iff, Option.forall, Polynomial.coeff_monomial, apply_ite]
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, coeff_add, hp, hq]

lemma irreducible_mul_X_add [IsDomain R]
    (f g : MvPolynomial n R) (i : n) (hf0 : f ≠ 0) (hif : i ∉ f.vars) (hig : i ∉ g.vars)
    (h : ∀ p, p ∣ f → p ∣ g → IsUnit p) :
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

lemma irreducible_of_disjoint_support [IsDomain R]
    (f : MvPolynomial n R) (h0 : f.support.Nontrivial)
    (h1 : ∀ d ∈ f.support, ∀ i ∈ d.support, d i ≤ 1)
    (h2 : ∀ d₁ ∈ f.support, ∀ d₂ ∈ f.support, ∀ i, i ∈ d₁.support → i ∈ d₂.support → d₁ = d₂)
    (h3 : ∀ r, (∀ d, r ∣ f.coeff d) → IsUnit r) :
    Irreducible f := by
  classical
  obtain ⟨d, hd, hd0⟩ := h0.exists_ne 0
  rw [ne_eq, ← Finsupp.support_eq_empty, ← ne_eq, ← Finset.nonempty_iff_ne_empty] at hd0
  rcases hd0 with ⟨i, hi⟩
  have hfd : f.coeff d ≠ 0 := by simpa [mem_support_iff] using hd
  let d₀ := d - .single i 1
  have hd₀ : d = d₀ + .single i 1 := by
    rw [Finsupp.mem_support_iff] at hi
    rw [Finsupp.sub_add_single_one_cancel hi]
  let φ : MvPolynomial n R := monomial d₀ (f.coeff d)
  let ψ : MvPolynomial n R := f - φ * X i
  have hf : f = φ * X i + ψ := by grind
  rw [hf]
  apply irreducible_mul_X_add
  · simp [φ, monomial_eq_zero, hfd]
  · simp [φ, hfd, h1 d hd i hi, d₀]
  · simp_rw [mem_vars, not_exists, not_and]
    intro k hk hik
    obtain rfl : d = k := by
      by_contra! hdk
      have hkf : k ∈ f.support := by
        rw [mem_support_iff] at hk ⊢
        rw [hf, coeff_add, coeff_mul_X', if_pos hik]
        dsimp only [φ]
        rwa [coeff_monomial, if_neg, zero_add]
        contrapose! hdk
        apply tsub_inj_left _ _ hdk
        · simp only [Finsupp.mem_support_iff, ne_eq, Finsupp.single_le_iff] at hi ⊢
          grind
        · simp only [Finsupp.mem_support_iff, ne_eq, Finsupp.single_le_iff] at hik ⊢
          grind
      have := h2 _ hd _ hkf i hi hik
      contradiction
    rw [mem_support_iff] at hk
    apply hk
    rw [Finsupp.mem_support_iff] at hi
    simp [ψ, coeff_mul_X', hi, φ, d₀]
  · intro p hpφ hpψ
    simp_rw [φ, dvd_monomial_iff_exists hfd] at hpφ
    obtain ⟨m, b, hm, hb, rfl⟩ := hpφ
    obtain rfl : m = 0 := by
      obtain ⟨d₂, hd₂, H⟩ := h0.exists_ne d
      ext j
      have hne := H
      contrapose! H
      rw [Finsupp.zero_apply] at H
      apply h2 d₂ hd₂ d hd j
      · have := support_add (p := φ * X i) (q := ψ)
        rw [← hf] at this
        specialize this hd₂
        have : coeff d₂ ψ ≠ 0 := by
          simpa [φ, hfd, ← hd₀, hne.symm] using this
        obtain ⟨q, hq⟩ := hpψ
        simp only [hq, coeff_monomial_mul', ne_eq, ite_eq_right_iff, Classical.not_imp] at this
        replace this := this.1 j
        rw [Finsupp.mem_support_iff]
        grind
      · rw [Finsupp.mem_support_iff]
        specialize hm j
        simp only [Finsupp.coe_tsub, Pi.sub_apply, d₀] at hm
        grind
    simp_rw [isUnit_iff_eq_C_of_isReduced, ← C_apply, C_inj]
    refine ⟨b, ?_, rfl⟩
    apply h3
    intro k
    obtain rfl | hk := eq_or_ne k d
    · exact hb
    by_cases hkf : coeff k f = 0
    · simp [hkf]
    suffices coeff k (φ * X i) = 0 by
      rw [hf, coeff_add, this, zero_add]
      rw [← C_apply, C_dvd_iff_dvd_coeff] at hpψ
      apply hpψ
    rw [coeff_mul_X', ite_eq_right_iff]
    intro hik
    rw [← ne_eq, ← mem_support_iff] at hkf
    have := h2 _ hkf _ hd i hik hi
    contradiction

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
    rw [aux, coeff, Finsupp.embDomain_apply]
  have hsupp : (sum_smul_X c).support = c.support.map ι := by
    rw [aux, support, Finsupp.support_embDomain]
  apply irreducible_of_disjoint_support
  · rwa [hsupp, Finset.map_nontrivial]
  · simp [hsupp, ι, Finsupp.single_apply]
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
    rw [aux, coeff, Finsupp.embDomain_apply]
  have hsupp : (sum_smul_X_mul_Y c).support = c.support.map ι := by
    rw [aux, support, Finsupp.support_embDomain]
  apply irreducible_of_disjoint_support
  · rwa [hsupp, Finset.map_nontrivial]
  · simp [hsupp, ι, Finsupp.single_apply]
  · simp +contextual [hsupp, ι, Finsupp.single_apply]
  · intro r hr
    apply h_dvd
    intro i
    simpa [hcoeff] using hr (ι i)

end

end MvPolynomial
