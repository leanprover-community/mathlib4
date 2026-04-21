/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Spectrum mapping theorem

This file develops and proves the spectral mapping theorem for polynomials over algebraically closed
fields. In particular, if `a` is an element of a `𝕜`-algebra `A` where `𝕜` is a field, and
`p : 𝕜[X]` is a polynomial, then the spectrum of `Polynomial.aeval a p` contains the image of the
spectrum of `a` under `(fun k ↦ Polynomial.eval k p)`. When `𝕜` is algebraically closed,
these are in fact equal (assuming either that the spectrum of `a` is nonempty or the polynomial
has positive degree), which is the **spectral mapping theorem**.

In addition, this file contains the fact that every element of a finite-dimensional nontrivial
algebra over an algebraically closed field has nonempty spectrum. In particular, this is used in
`Module.End.exists_eigenvalue` to show that every linear map from a vector space to itself has an
eigenvalue.

## Main statements

* `spectrum.subset_polynomial_aeval`, `spectrum.map_polynomial_aeval_of_degree_pos`,
  `spectrum.map_polynomial_aeval_of_nonempty`: variations on the **spectral mapping theorem**.
* `spectrum.nonempty_of_isAlgClosed_of_finiteDimensional`: the spectrum is nonempty for any
  element of a nontrivial finite-dimensional algebra over an algebraically closed field.

## Notation

* `σ a` : `spectrum R a` of `a : A`
-/
set_option backward.defeqAttrib.useBackward true

public section

namespace spectrum

open Set Polynomial

open scoped Pointwise Polynomial

universe u v

section ScalarRing

variable {R : Type u} {A : Type v}
variable [CommRing R] [Ring A] [Algebra R A]

local notation "σ" => spectrum R
local notation "↑ₐ" => algebraMap R A

theorem exists_mem_of_not_isUnit_aeval_prod [IsDomain R] {p : R[X]} {a : A}
    (h : ¬IsUnit (aeval a (Multiset.map (fun x : R => X - C x) p.roots).prod)) :
    ∃ k : R, k ∈ σ a ∧ eval k p = 0 := by
  rw [← Multiset.prod_toList, map_list_prod] at h
  replace h := mt List.prod_isUnit h
  simp only [not_forall, exists_prop, aeval_C, Multiset.mem_toList, List.mem_map, aeval_X,
    exists_exists_and_eq_and, Multiset.mem_map, map_sub] at h
  rcases h with ⟨r, r_mem, r_nu⟩
  exact ⟨r, by rwa [mem_iff, ← IsUnit.sub_iff], (mem_roots'.1 r_mem).2⟩

end ScalarRing

section ScalarField

variable {𝕜 : Type u} {A : Type v}
variable [Field 𝕜] [Ring A] [Algebra 𝕜 A]

local notation "σ" => spectrum 𝕜
local notation "↑ₐ" => algebraMap 𝕜 A

open Polynomial

/-- Half of the spectral mapping theorem for polynomials. We prove it separately
because it holds over any field, whereas `spectrum.map_polynomial_aeval_of_degree_pos` and
`spectrum.map_polynomial_aeval_of_nonempty` need the field to be algebraically closed. -/
theorem subset_polynomial_aeval (a : A) (p : 𝕜[X]) : (eval · p) '' σ a ⊆ σ (aeval a p) := by
  rintro _ ⟨k, hk, rfl⟩
  let q := C (eval k p) - p
  have hroot : IsRoot q k := by simp only [q, eval_C, eval_sub, sub_self, IsRoot.def]
  rw [← mul_div_eq_iff_isRoot, ← neg_mul_neg, neg_sub] at hroot
  have aeval_q_eq : ↑ₐ (eval k p) - aeval a p = aeval a q := by
    simp only [q, aeval_C, map_sub]
  rw [mem_iff, aeval_q_eq, ← hroot, aeval_mul]
  have hcomm := (Commute.all (C k - X) (-(q / (X - C k)))).map (aeval a : 𝕜[X] →ₐ[𝕜] A)
  apply mt fun h => (hcomm.isUnit_mul_iff.mp h).1
  simpa only [aeval_X, aeval_C, map_sub] using hk

/-- The *spectral mapping theorem* for polynomials.  Note: the assumption `degree p > 0`
is necessary in case `σ a = ∅`, for then the left-hand side is `∅` and the right-hand side,
assuming `[Nontrivial A]`, is `{k}` where `p = Polynomial.C k`. -/
theorem map_polynomial_aeval_of_degree_pos [IsAlgClosed 𝕜] (a : A) (p : 𝕜[X])
    (hdeg : 0 < degree p) : σ (aeval a p) = (eval · p) '' σ a := by
  -- handle the easy direction via `spectrum.subset_polynomial_aeval`
  refine Set.eq_of_subset_of_subset (fun k hk => ?_) (subset_polynomial_aeval a p)
  -- write `C k - p` product of linear factors and a constant; show `C k - p ≠ 0`.
  have hprod := (IsAlgClosed.splits (C k - p)).eq_prod_roots
  have h_ne : C k - p ≠ 0 := ne_zero_of_degree_gt <| by
    rwa [degree_sub_eq_right_of_degree_lt (lt_of_le_of_lt degree_C_le hdeg)]
  have lead_ne := leadingCoeff_ne_zero.mpr h_ne
  have lead_unit := (Units.map ↑ₐ.toMonoidHom (Units.mk0 _ lead_ne)).isUnit
  /- leading coefficient is a unit so product of linear factors is not a unit;
    apply `exists_mem_of_not_is_unit_aeval_prod`. -/
  have p_a_eq : aeval a (C k - p) = ↑ₐ k - aeval a p := by
    simp only [aeval_C, map_sub]
  rw [mem_iff, ← p_a_eq, hprod, aeval_mul,
    ((Commute.all _ _).map (aeval a : 𝕜[X] →ₐ[𝕜] A)).isUnit_mul_iff, aeval_C] at hk
  replace hk := exists_mem_of_not_isUnit_aeval_prod (not_and.mp hk lead_unit)
  rcases hk with ⟨r, r_mem, r_ev⟩
  exact ⟨r, r_mem, symm (by simpa [eval_sub, eval_C, sub_eq_zero] using r_ev)⟩

/-- In this version of the spectral mapping theorem, we assume the spectrum
is nonempty instead of assuming the degree of the polynomial is positive. -/
theorem map_polynomial_aeval_of_nonempty [IsAlgClosed 𝕜] (a : A) (p : 𝕜[X])
    (hnon : (σ a).Nonempty) : σ (aeval a p) = (fun k => eval k p) '' σ a := by
  nontriviality A
  refine Or.elim (le_or_gt (degree p) 0) (fun h => ?_) (map_polynomial_aeval_of_degree_pos a p)
  rw [eq_C_of_degree_le_zero h]
  simp only [eval_C, aeval_C, scalar_eq, Set.Nonempty.image_const hnon]

/-- A specialization of `spectrum.subset_polynomial_aeval` to monic monomials for convenience. -/
theorem pow_image_subset (a : A) (n : ℕ) : (fun x => x ^ n) '' σ a ⊆ σ (a ^ n) := by
  simpa only [eval_X_pow, aeval_X_pow] using subset_polynomial_aeval a (X ^ n : 𝕜[X])

theorem pow_mem_pow (a : A) (n : ℕ) {k : 𝕜} (hk : k ∈ σ a) : k ^ n ∈ σ (a ^ n) :=
  pow_image_subset a n ⟨k, ⟨hk, rfl⟩⟩

/-- A specialization of `spectrum.map_polynomial_aeval_of_nonempty` to monic monomials for
convenience. -/
theorem map_pow_of_pos [IsAlgClosed 𝕜] (a : A) {n : ℕ} (hn : 0 < n) :
    σ (a ^ n) = (· ^ n) '' σ a := by
  simpa only [aeval_X_pow, eval_X_pow]
    using map_polynomial_aeval_of_degree_pos a (X ^ n : 𝕜[X]) (by rwa [degree_X_pow, Nat.cast_pos])

/-- A specialization of `spectrum.map_polynomial_aeval_of_nonempty` to monic monomials for
convenience. -/
theorem map_pow_of_nonempty [IsAlgClosed 𝕜] {a : A} (ha : (σ a).Nonempty) (n : ℕ) :
    σ (a ^ n) = (· ^ n) '' σ a := by
  simpa only [aeval_X_pow, eval_X_pow] using map_polynomial_aeval_of_nonempty a (X ^ n) ha

variable (𝕜)

-- We will use this both to show eigenvalues exist, and to prove Schur's lemma.
/-- Every element `a` in a nontrivial finite-dimensional algebra `A`
over an algebraically closed field `𝕜` has non-empty spectrum. -/
theorem nonempty_of_isAlgClosed_of_finiteDimensional [IsAlgClosed 𝕜] [Nontrivial A]
    [I : FiniteDimensional 𝕜 A] (a : A) : (σ a).Nonempty := by
  obtain ⟨p, ⟨h_mon, h_eval_p⟩⟩ := isIntegral_of_noetherian (IsNoetherian.iff_fg.2 I) a
  have nu : ¬IsUnit (aeval a p) := by rw [← aeval_def] at h_eval_p; rw [h_eval_p]; simp
  rw [(IsAlgClosed.splits p).eq_prod_roots_of_monic h_mon] at nu
  obtain ⟨k, hk, _⟩ := exists_mem_of_not_isUnit_aeval_prod nu
  exact ⟨k, hk⟩

end ScalarField

end spectrum

open Polynomial in
theorem IsIdempotentElem.spectrum_subset (𝕜 : Type*) {A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
    {p : A} (hp : IsIdempotentElem p) : spectrum 𝕜 p ⊆ {0, 1} := by
  nontriviality A
  apply Set.image_subset_iff.mp (spectrum.subset_polynomial_aeval p (X ^ 2 - X)) |>.trans
  refine fun a ha => eq_zero_or_one_of_sq_eq_self ?_
  simpa [pow_two p, hp.eq, sub_eq_zero] using ha

lemma IsIdempotentElem.finite_spectrum (𝕜 : Type*) {A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
    {p : A} (hp : IsIdempotentElem p) : (spectrum 𝕜 p).Finite :=
  have : ({0, 1} : Set 𝕜).encard = (2 : ℕ) := Set.encard_pair (by simp)
  Set.finite_of_encard_le_coe (this ▸ Set.encard_le_encard (hp.spectrum_subset 𝕜))

open Unitization in
theorem IsIdempotentElem.quasispectrum_subset (𝕜 : Type*) {A : Type*} [Field 𝕜] [NonUnitalRing A]
    [Module 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] {p : A} (hp : IsIdempotentElem p) :
    quasispectrum 𝕜 p ⊆ {0, 1} :=
  quasispectrum_eq_spectrum_inr' 𝕜 𝕜 p ▸ (hp.inr _ |>.spectrum_subset _)

theorem IsIdempotentElem.finite_quasispectrum (𝕜 : Type*) {A : Type*} [Field 𝕜] [NonUnitalRing A]
    [Module 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] {p : A} (hp : IsIdempotentElem p) :
    (quasispectrum 𝕜 p).Finite :=
  have : ({0, 1} : Set 𝕜).encard = (2 : ℕ) := Set.encard_pair (by simp)
  Set.finite_of_encard_le_coe (this ▸ Set.encard_le_encard (hp.quasispectrum_subset 𝕜))
