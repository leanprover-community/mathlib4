/-
Copyright (c) 2026 Yuxuan Xiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxuan Xiao
-/
module

public import Mathlib.Algebra.MvPolynomial.Variables

/-!
# Main degree of a polynomial

This file defines the *main degree* of a multivariate polynomial,
which is the degree with respect to its main variable.

## Main definitions

* `MvPolynomial.mainDegree p`:
  The degree of `p` with respect to its main variable.
  If `max_vars p = ⊥` (i.e., `p` is a constant or zero), the degree is `0`.

## Main theorems

* `mainDegree_eq_zero_iff`: `p.mainDegree = 0` iff `p.max_vars = ⊥`
* `mainDegree_of_max_vars_isSome`: When `p.max_vars = c ≠ ⊥`,
  `p.mainDegree = p.degreeOf c`

-/

@[expose] public section

namespace MvPolynomial

variable {R σ : Type*} [CommSemiring R] {p q : MvPolynomial σ R}

section MainDegree

variable [LinearOrder σ] {i j c : σ}

/-- The "main degree" of `p`: the degree of `p` with respect to its main variable.
If `max_vars p = ⊥` (i.e., `p` is a constant or zero), the degree is 0. -/
noncomputable def mainDegree (p : MvPolynomial σ R) : ℕ :=
  match p.vars.max with
  | ⊥ => 0
  | some c => p.degreeOf c

theorem mainDegree_of_max_vars_isSome : p.vars.max = c → p.mainDegree = p.degreeOf c :=
  fun h ↦ by rw [mainDegree, h]

theorem mainDegree_of_max_vars_isSome' :
    p.vars.max = c → p.mainDegree = p.support.sup (fun s ↦ s c) :=
  fun h ↦ by rw [mainDegree_of_max_vars_isSome h, degreeOf_eq_sup]

theorem mainDegree_eq_zero_iff : p.mainDegree = 0 ↔ p.vars.max = ⊥ where
  mp h :=
    match hc : p.vars.max with
    | ⊥ => rfl
    | some c => by
      rw [mainDegree_of_max_vars_isSome hc, degreeOf] at h
      have : c ∉ p.degrees := by simpa only [Multiset.count_eq_zero] using h
      have hc := Finset.mem_of_max hc
      simp only [vars_def, Multiset.mem_toFinset] at hc
      exact absurd hc this
  mpr h := by rw [mainDegree, h]

theorem mainDegree_eq_zero_iff_eq_C : p.mainDegree = 0 ↔ p = C (p.coeff 0) :=
  mainDegree_eq_zero_iff.trans <| Finset.max_eq_bot.trans vars_eq_empty_iff_eq_C

theorem degreeOf_max_vars_ne_zero : p.vars.max = c → p.degreeOf c ≠ 0 := fun h ↦
  have := (not_iff_not.mpr mainDegree_eq_zero_iff).mpr (h ▸ WithBot.coe_ne_bot)
  mainDegree_of_max_vars_isSome h ▸ this

theorem max_vars_mem_degrees : p.vars.max = c → c ∈ p.degrees := fun h ↦
  have := degreeOf_max_vars_ne_zero h; Multiset.count_ne_zero.mp (degreeOf_def c p ▸ this)

@[simp] theorem mainDegree_zero : (0 : MvPolynomial σ R).mainDegree = 0 := rfl

@[simp] theorem mainDegree_monomial {s : σ →₀ ℕ} {r : R} (hr : r ≠ 0)
    (hs : s.support.max = c) : (monomial s r).mainDegree = s c := by
  rw [mainDegree_of_max_vars_isSome <| (congrArg _ (vars_monomial hr)).trans hs]
  exact degreeOf_monomial_eq s c hr

@[simp] theorem mainDegree_C (r : R) : (C r : MvPolynomial σ R).mainDegree = 0 :=
  mainDegree_eq_zero_iff.mpr <| congrArg _ (vars_C)

@[simp] theorem mainDegree_X_pow [Nontrivial R] (i : σ) (k : ℕ) :
    ((X i : MvPolynomial σ R) ^ k).mainDegree = k := by
  by_cases hk : k = 0
  · exact hk ▸ pow_zero (X i : MvPolynomial σ R) ▸ mainDegree_C 1
  have : (Finsupp.single i k).support.max = i := by rw [Finsupp.support_single_ne_zero i hk]; rfl
  rw [X_pow_eq_monomial, mainDegree_monomial one_ne_zero this, Finsupp.single_eq_same]

@[simp] theorem mainDegree_X [Nontrivial R] (i : σ) : (X i : MvPolynomial σ R).mainDegree = 1 :=
  pow_one (X i : MvPolynomial σ R) ▸ mainDegree_X_pow i 1

end MainDegree
end MvPolynomial
