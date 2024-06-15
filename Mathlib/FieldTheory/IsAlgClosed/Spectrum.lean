/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Algebra.Algebra.Spectrum
import Mathlib.FieldTheory.IsAlgClosed.Basic

#align_import field_theory.is_alg_closed.spectrum from "leanprover-community/mathlib"@"58a272265b5e05f258161260dd2c5d247213cbd3"

/-!
# Spectrum mapping theorem

This file develops proves the spectral mapping theorem for polynomials over algebraically closed
fields. In particular, if `a` is an element of a `𝕜`-algebra `A` where `𝕜` is a field, and
`p : 𝕜[X]` is a polynomial, then the spectrum of `Polynomial.aeval a p` contains the image of the
spectrum of `a` under `(fun k ↦ Polynomial.eval k p)`. When `𝕜` is algebraically closed,
these are in fact equal (assuming either that the spectrum of `a` is nonempty or the polynomial
has positive degree), which is the **spectral mapping theorem**.

In addition, this file contains the fact that every element of a finite dimensional nontrivial
algebra over an algebraically closed field has nonempty spectrum. In particular, this is used in
`Module.End.exists_eigenvalue` to show that every linear map from a vector space to itself has an
eigenvalue.

## Main statements

* `spectrum.subset_polynomial_aeval`, `spectrum.map_polynomial_aeval_of_degree_pos`,
  `spectrum.map_polynomial_aeval_of_nonempty`: variations on the **spectral mapping theorem**.
* `spectrum.nonempty_of_isAlgClosed_of_finiteDimensional`: the spectrum is nonempty for any
  element of a nontrivial finite dimensional algebra over an algebraically closed field.

## Notations

* `σ a` : `spectrum R a` of `a : A`
-/

namespace spectrum

open Set Polynomial

open scoped Pointwise Polynomial

universe u v

section ScalarRing

variable {R : Type u} {A : Type v}
variable [CommRing R] [Ring A] [Algebra R A]

local notation "σ" => spectrum R
local notation "↑ₐ" => algebraMap R A

-- Porting note: removed an unneeded assumption `p ≠ 0`
theorem exists_mem_of_not_isUnit_aeval_prod [IsDomain R] {p : R[X]} {a : A}
    (h : ¬IsUnit (aeval a (Multiset.map (fun x : R => X - C x) p.roots).prod)) :
    ∃ k : R, k ∈ σ a ∧ eval k p = 0 := by
  rw [← Multiset.prod_toList, AlgHom.map_list_prod] at h
  replace h := mt List.prod_isUnit h
  simp only [not_forall, exists_prop, aeval_C, Multiset.mem_toList, List.mem_map, aeval_X,
    exists_exists_and_eq_and, Multiset.mem_map, AlgHom.map_sub] at h
  rcases h with ⟨r, r_mem, r_nu⟩
  exact ⟨r, by rwa [mem_iff, ← IsUnit.sub_iff], (mem_roots'.1 r_mem).2⟩
#align spectrum.exists_mem_of_not_is_unit_aeval_prod spectrum.exists_mem_of_not_isUnit_aeval_prodₓ

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
    simp only [q, aeval_C, AlgHom.map_sub, sub_left_inj]
  rw [mem_iff, aeval_q_eq, ← hroot, aeval_mul]
  have hcomm := (Commute.all (C k - X) (-(q / (X - C k)))).map (aeval a : 𝕜[X] →ₐ[𝕜] A)
  apply mt fun h => (hcomm.isUnit_mul_iff.mp h).1
  simpa only [aeval_X, aeval_C, AlgHom.map_sub] using hk
#align spectrum.subset_polynomial_aeval spectrum.subset_polynomial_aeval

/-- The *spectral mapping theorem* for polynomials.  Note: the assumption `degree p > 0`
is necessary in case `σ a = ∅`, for then the left-hand side is `∅` and the right-hand side,
assuming `[Nontrivial A]`, is `{k}` where `p = Polynomial.C k`. -/
theorem map_polynomial_aeval_of_degree_pos [IsAlgClosed 𝕜] (a : A) (p : 𝕜[X])
    (hdeg : 0 < degree p) : σ (aeval a p) = (eval · p) '' σ a := by
  -- handle the easy direction via `spectrum.subset_polynomial_aeval`
  refine Set.eq_of_subset_of_subset (fun k hk => ?_) (subset_polynomial_aeval a p)
  -- write `C k - p` product of linear factors and a constant; show `C k - p ≠ 0`.
  have hprod := eq_prod_roots_of_splits_id (IsAlgClosed.splits (C k - p))
  have h_ne : C k - p ≠ 0 := ne_zero_of_degree_gt <| by
    rwa [degree_sub_eq_right_of_degree_lt (lt_of_le_of_lt degree_C_le hdeg)]
  have lead_ne := leadingCoeff_ne_zero.mpr h_ne
  have lead_unit := (Units.map ↑ₐ.toMonoidHom (Units.mk0 _ lead_ne)).isUnit
  /- leading coefficient is a unit so product of linear factors is not a unit;
    apply `exists_mem_of_not_is_unit_aeval_prod`. -/
  have p_a_eq : aeval a (C k - p) = ↑ₐ k - aeval a p := by
    simp only [aeval_C, AlgHom.map_sub, sub_left_inj]
  rw [mem_iff, ← p_a_eq, hprod, aeval_mul,
    ((Commute.all _ _).map (aeval a : 𝕜[X] →ₐ[𝕜] A)).isUnit_mul_iff, aeval_C] at hk
  replace hk := exists_mem_of_not_isUnit_aeval_prod (not_and.mp hk lead_unit)
  rcases hk with ⟨r, r_mem, r_ev⟩
  exact ⟨r, r_mem, symm (by simpa [eval_sub, eval_C, sub_eq_zero] using r_ev)⟩
#align spectrum.map_polynomial_aeval_of_degree_pos spectrum.map_polynomial_aeval_of_degree_pos

/-- In this version of the spectral mapping theorem, we assume the spectrum
is nonempty instead of assuming the degree of the polynomial is positive. -/
theorem map_polynomial_aeval_of_nonempty [IsAlgClosed 𝕜] (a : A) (p : 𝕜[X])
    (hnon : (σ a).Nonempty) : σ (aeval a p) = (fun k => eval k p) '' σ a := by
  nontriviality A
  refine Or.elim (le_or_gt (degree p) 0) (fun h => ?_) (map_polynomial_aeval_of_degree_pos a p)
  rw [eq_C_of_degree_le_zero h]
  simp only [Set.image_congr, eval_C, aeval_C, scalar_eq, Set.Nonempty.image_const hnon]
#align spectrum.map_polynomial_aeval_of_nonempty spectrum.map_polynomial_aeval_of_nonempty

/-- A specialization of `spectrum.subset_polynomial_aeval` to monic monomials for convenience. -/
theorem pow_image_subset (a : A) (n : ℕ) : (fun x => x ^ n) '' σ a ⊆ σ (a ^ n) := by
  simpa only [eval_pow, eval_X, aeval_X_pow] using subset_polynomial_aeval a (X ^ n : 𝕜[X])
#align spectrum.pow_image_subset spectrum.pow_image_subset

/-- A specialization of `spectrum.map_polynomial_aeval_of_nonempty` to monic monomials for
convenience. -/
theorem map_pow_of_pos [IsAlgClosed 𝕜] (a : A) {n : ℕ} (hn : 0 < n) :
    σ (a ^ n) = (· ^ n) '' σ a := by
  simpa only [aeval_X_pow, eval_pow, eval_X]
    using map_polynomial_aeval_of_degree_pos a (X ^ n : 𝕜[X]) (by rwa [degree_X_pow, Nat.cast_pos])
#align spectrum.map_pow_of_pos spectrum.map_pow_of_pos

/-- A specialization of `spectrum.map_polynomial_aeval_of_nonempty` to monic monomials for
convenience. -/
theorem map_pow_of_nonempty [IsAlgClosed 𝕜] {a : A} (ha : (σ a).Nonempty) (n : ℕ) :
    σ (a ^ n) = (· ^ n) '' σ a := by
  simpa only [aeval_X_pow, eval_pow, eval_X] using map_polynomial_aeval_of_nonempty a (X ^ n) ha
#align spectrum.map_pow_of_nonempty spectrum.map_pow_of_nonempty

variable (𝕜)

-- We will use this both to show eigenvalues exist, and to prove Schur's lemma.
/-- Every element `a` in a nontrivial finite-dimensional algebra `A`
over an algebraically closed field `𝕜` has non-empty spectrum. -/
theorem nonempty_of_isAlgClosed_of_finiteDimensional [IsAlgClosed 𝕜] [Nontrivial A]
    [I : FiniteDimensional 𝕜 A] (a : A) : (σ a).Nonempty := by
  obtain ⟨p, ⟨h_mon, h_eval_p⟩⟩ := isIntegral_of_noetherian (IsNoetherian.iff_fg.2 I) a
  have nu : ¬IsUnit (aeval a p) := by rw [← aeval_def] at h_eval_p; rw [h_eval_p]; simp
  rw [eq_prod_roots_of_monic_of_splits_id h_mon (IsAlgClosed.splits p)] at nu
  obtain ⟨k, hk, _⟩ := exists_mem_of_not_isUnit_aeval_prod nu
  exact ⟨k, hk⟩
#align spectrum.nonempty_of_is_alg_closed_of_finite_dimensional spectrum.nonempty_of_isAlgClosed_of_finiteDimensional

end ScalarField

end spectrum
