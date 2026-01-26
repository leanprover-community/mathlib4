/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Johan Commelin, Andrew Yang
-/
module

public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-!
# Irreducibility of linear and quadratic polynomials

* `MvPolynomial.irreducible_of_totalDegree_eq_one`:
  a multivariate polynomial of `totalDegree` one is irreducible
  if its coefficients are relatively prime.

* For `c : n →₀ R`, `MvPolynomial.sumSMulX c` is the linear polynomial
  $\sum_i c_i X_i$ of $R[X_1\dots,X_n]$.

* `MvPolynomial.irreducible_sumSMulX` : if the support of `c` is nontrivial,
  if `R` is a domain,
  and if the only common divisors to all `c i` are units,
  then `MvPolynomial.sumSMulX c` is irreducible.

* For `c : n →₀ R`, `MvPolynomial.sumXSMulY c` is the quadratic polynomial
  $\sum_i c_i X_i Y_i$ of $R[X_1\dots,X_n,Y_1,\dots,Y_n]$.
  It is constructed as an object of `MvPolynomial (n ⊕ n) R`,
  the first component of `n ⊕ n` represents the `X` indeterminates,
  and the second component represents the `Y` indeterminates.

* `MvPolynomial.irreducible_sumSMulXSMulY` :
  if the support of `c` is nontrivial,
  the ring `R` is a domain,
  and the only divisors common to all `c i` are units,
  then `MvPolynomial.sumSMulXSMulY c` is irreducible.

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
  Eg, $X^2-Y$ is irreducible, but $X^2$, $X^2-1$, $X^2-Y^2$ are not.
  And $X^2+Y^2$ is irreducible over the reals but not over the complex numbers.

-/

@[expose] public section

namespace MvPolynomial

open scoped Polynomial

section

variable {n : Type*} {R : Type*} [CommRing R]

open scoped Polynomial in
attribute [local simp] MvPolynomial.optionEquivLeft_X_none in -- tag simp globally?
lemma irreducible_mul_X_add {n : Type*} {R : Type*} [CommRing R] [IsDomain R]
    (f g : MvPolynomial n R) (i : n) (hf0 : f ≠ 0) (hif : i ∉ f.vars) (hig : i ∉ g.vars)
    (h : IsRelPrime f g) :
    Irreducible (f * X i + g) := by
  classical
  let S := MvPolynomial { j // j ≠ i } R
  let e : MvPolynomial n R ≃ₐ[R] S[X] :=
    (renameEquiv R (Equiv.optionSubtypeNe i).symm).trans (optionEquivLeft R _)
  have he : e.symm.toAlgHom.comp Polynomial.CAlgHom = rename (↑) := by ext; simp [e, S]
  obtain ⟨f, rfl⟩ : f ∈ (e.symm.toAlgHom.comp Polynomial.CAlgHom).range :=
    he ▸ exists_rename_eq_of_vars_subset_range _ _ Subtype.val_injective (by simpa [Set.subset_def])
  obtain ⟨g, rfl⟩ : g ∈ (e.symm.toAlgHom.comp Polynomial.CAlgHom).range :=
    he ▸ exists_rename_eq_of_vars_subset_range _ _ Subtype.val_injective (by simpa [Set.subset_def])
  refine .of_map (f := e) ?_
  simpa [e, S] using Polynomial.irreducible_C_mul_X_add_C (by aesop)
    (IsRelPrime.of_map Polynomial.C (IsRelPrime.of_map e.symm h))

/-- A multivariate polynomial `f` whose support is nontrivial,
such that some variable `i` appears with exponent `1` in one nontrivial monomial,
whose monomials have disjoint supports, and which is primitive, is irreducible. -/
lemma irreducible_of_disjoint_support [IsDomain R]
    {f : MvPolynomial n R}
    (nontrivial : f.support.Nontrivial)
    {d : n →₀ ℕ} (hd : d ∈ f.support) {i : n} (hdi : d i = 1)
    (disjoint : (f.support : Set (n →₀ ℕ)).PairwiseDisjoint Finsupp.support)
    (isPrimitive : ∀ r, (∀ d, r ∣ f.coeff d) → IsUnit r) :
    Irreducible f := by
  classical
  have hfd : f.coeff d ≠ 0 := by simpa using hd
  let d₀ := d.erase i
  let φ : MvPolynomial n R := monomial d₀ (f.coeff d)
  let ψ : MvPolynomial n R := f - φ * X i
  have hf : f = φ * X i + ψ := by grind only
  have hφ : φ * X i = monomial d (f.coeff d) := by
    nth_rw 1 [← Finsupp.erase_add_single i d]; simp [φ, monomial_add_single, hdi, d₀]
  have hdψ (k) : ψ.coeff k = if d = k then 0 else f.coeff k := by
    simp +contextual [ψ, hφ, sub_eq_iff_eq_add, ite_add_ite]
  rw [hf]
  apply irreducible_mul_X_add
  · grind only [monomial_eq_zero]
  · simp [φ, hfd, d₀, hdi]
  · suffices ∀ x, d ≠ x → x ∈ f.support → i ∉ x.support by simpa [mem_vars, hdψ] using this
    exact fun x hxd hx hix ↦
      Finset.disjoint_iff_ne.mp (disjoint hd hx hxd) i (by simp [hdi]) _ hix rfl
  · rintro p hpφ ⟨q, hq⟩
    obtain ⟨m, b, hm, hb, rfl⟩ := (dvd_monomial_iff_exists hfd).mp hpφ
    obtain ⟨d₂, hd₂, H⟩ := nontrivial.exists_ne d
    obtain rfl : m = 0 := by
      have aux : coeff d₂ ψ ≠ 0 := by simpa [hdψ, H.symm] using hd₂
      simp only [hq, coeff_monomial_mul', ne_eq, ite_eq_right_iff, Classical.not_imp] at aux
      simpa using disjoint hd₂ hd H (Finsupp.support_mono aux.1)
        ((Finsupp.support_mono hm).trans (d.support.erase_subset i))
    have hb' : IsUnit b := isPrimitive _ fun k ↦
      if hk : k = d then hk ▸ hb else hf ▸ by simp [hq, hφ, Ne.symm hk]
    simpa

end

section
/-! ## The quadratic polynomial $$\sum_{i=1}^n X_i Y_i$$. -/

open Polynomial

variable {n : Type*} {R : Type*} [CommRing R]

theorem irreducible_of_totalDegree_eq_one
    [IsDomain R] {p : MvPolynomial n R} (hp : p.totalDegree = 1)
    (hp' : ∀ x, (∀ i, x ∣ p.coeff i) → IsUnit x) :
    Irreducible p where
  not_isUnit H := by
    simp [(MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp H).2] at hp
  isUnit_or_isUnit a b hab := by
    wlog hle : a.totalDegree ≤ b.totalDegree generalizing a b
    · exact (this b a (by rw [hab, mul_comm]) (by lia)).symm
    obtain rfl | ha₀ := eq_or_ne a 0; · simp_all
    obtain rfl | hb₀ := eq_or_ne b 0; · simp_all
    have : a.totalDegree + b.totalDegree = 1 := by
      simpa [totalDegree_mul_of_isDomain, ha₀, hb₀, hp] using congr(($hab).totalDegree).symm
    obtain ⟨r, rfl⟩ : ∃ r, a = C r := ⟨_, (totalDegree_eq_zero_iff_eq_C (p := a)).mp (by lia)⟩
    simp [hp' r fun i ↦ by simp [hab]]

variable (c : n →₀ R)

/-- The linear polynomial $$\sum_i c_i X_i$$. -/
noncomputable def sumSMulX :
    (n →₀ R) →ₗ[R] MvPolynomial n R :=
  Finsupp.linearCombination R X

theorem coeff_sumSMulX (i : n) :
    (sumSMulX c).coeff (Finsupp.single i 1) = c i := by
  classical
  rw [sumSMulX, Finsupp.linearCombination_apply, Finsupp.sum, coeff_sum]
  rw [Finset.sum_eq_single i _ (by simp)]
  · simp
  intro j hj hji
  rw [coeff_smul, coeff_X', if_neg]
  · aesop
  · rwa [Finsupp.single_left_inj Nat.one_ne_zero]

theorem irreducible_sumSMulX [IsDomain R]
    (hc_nonempty : c.support.Nonempty)
    (hc_gcd : ∀ r, (∀ i, r ∣ c i) → IsUnit r) :
    Irreducible (sumSMulX c) := by
  apply irreducible_of_totalDegree_eq_one
  · apply le_antisymm
    · simp only [sumSMulX, Finsupp.linearCombination_apply, Finsupp.sum]
      apply totalDegree_finsetSum_le
      intros
      apply le_trans (totalDegree_smul_le ..)
      simp
    · rw [← not_lt, Nat.lt_one_iff, totalDegree_eq_zero_iff]
      intro h
      obtain ⟨i, hi⟩ := hc_nonempty
      simp only [Finsupp.mem_support_iff] at hi
      specialize h (Finsupp.single i 1) (by
        rwa [mem_support_iff, coeff_sumSMulX]) i
      simp only [Finsupp.single_eq_same, one_ne_zero] at h
  · intro r hr
    apply hc_gcd
    intro i
    simpa [coeff_sumSMulX] using hr (Finsupp.single i 1)

/-- The quadratic polynomial $$\sum_i c_i X_i Y_i$$. -/
noncomputable def sumSMulXSMulY :
    (n →₀ R) →ₗ[R] MvPolynomial (n ⊕ n) R :=
  Finsupp.linearCombination R (fun i ↦ X (.inl i) * X (.inr i))

variable (c : n →₀ R)

theorem irreducible_sumSMulXSMulY [IsDomain R]
    (hc : c.support.Nontrivial)
    (h_dvd : ∀ r, (∀ i, r ∣ c i) → IsUnit r) :
    Irreducible (sumSMulXSMulY c) := by
  classical
  let ι : n ↪ ((n ⊕ n) →₀ ℕ) :=
    ⟨fun i ↦ .single (.inl i) 1 + .single (.inr i) 1,
     fun i j ↦ by simp +contextual [Finsupp.ext_iff, Finsupp.single_apply, ite_eq_iff']⟩
  -- unfortunate defeq abuse... we should have an `.embDomain`-like constructor for MvPolys
  have aux : sumSMulXSMulY c = c.embDomain ι := by
    rw [← Finsupp.sum_single (Finsupp.embDomain _ _)]
    simp [Finsupp.sum_embDomain, sumSMulXSMulY, X, monomial_mul,
      Finsupp.linearCombination_apply, smul_monomial, ι]
    rfl
  have hcoeff (i : n) : coeff (ι i) (sumSMulXSMulY c) = c i := by
    simp [aux, coeff, Finsupp.embDomain_apply]
  have hsupp : (sumSMulXSMulY c).support = c.support.map ι := by
    rw [aux, support, Finsupp.support_embDomain]
  obtain ⟨a, ha⟩ := hc.nonempty
  apply irreducible_of_disjoint_support (d := ι a) (i := .inl a)
  · rwa [hsupp, Finset.map_nontrivial]
  · rwa [MvPolynomial.mem_support_iff, hcoeff, ← Finsupp.mem_support_iff]
  · simp [ι]
  · rw [hsupp, Finset.coe_map, ι.injective.injOn.pairwiseDisjoint_image]
    suffices (c.support : Set n).PairwiseDisjoint fun x ↦ {Sum.inr x, Sum.inl x} by
      simpa [ι, Function.comp_def, Finsupp.support_add_eq, Finsupp.support_single_ne_zero]
    simp [Set.PairwiseDisjoint, Set.Pairwise, ne_comm]
  · intro r hr
    apply h_dvd
    intro i
    simpa [hcoeff] using hr (ι i)

end

end MvPolynomial
