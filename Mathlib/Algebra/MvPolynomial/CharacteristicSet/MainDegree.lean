/-
Copyright (c) 2026 Yuxuan Xiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxuan Xiao
-/
module

public import Mathlib.Algebra.MvPolynomial.CharacteristicSet.MainVariable

/-!
# Main degree of a polynomial

This file defines the *main degree* of a multivariate polynomial,
which is the degree with respect to its main variable.

## Main definitions

* `MvPolynomial.mainDegree p`:
  The degree of `p` with respect to its main variable.
  If `mainVariable p = ⊥` (i.e., `p` is a constant or zero), the degree is `0`.

## Main theorems

* `mainDegree_eq_zero_iff`: `p.mainDegree = 0` iff `p.mainVariable = ⊥`
* `mainDegree_of_mainVariable_isSome`: When `p.mainVariable = c ≠ ⊥`,
  `p.mainDegree = p.degreeOf c`

-/

@[expose] public section

namespace MvPolynomial

variable {R σ : Type*} [CommSemiring R] {p q : MvPolynomial σ R}

section MainDegree

variable [LinearOrder σ] {i j c : σ}

/-- The "main degree" of `p`: the degree of `p` with respect to its main variable.
If `mainVariable p = ⊥` (i.e., `p` is a constant or zero), the degree is 0. -/
noncomputable def mainDegree (p : MvPolynomial σ R) : ℕ :=
  match mainVariable p with
  | ⊥ => 0
  | some c => p.degreeOf c

theorem mainDegree_of_mainVariable_isSome : p.mainVariable = c → p.mainDegree = p.degreeOf c :=
  fun h ↦ by rw [mainDegree, h]

theorem mainDegree_of_mainVariable_isSome' :
    p.mainVariable = c → p.mainDegree = p.support.sup (fun s ↦ s c) :=
  fun h ↦ by rw [mainDegree_of_mainVariable_isSome h, degreeOf_eq_sup]

theorem mainDegree_eq_zero_iff : p.mainDegree = 0 ↔ p.mainVariable = ⊥ where
  mp h :=
    match hc : p.mainVariable with
    | ⊥ => rfl
    | some c => by
      simp only [mainDegree_of_mainVariable_isSome hc, degreeOf_eq_sup] at h
      rewrite [← Nat.bot_eq_zero, Finset.sup_eq_bot_iff] at h
      simp only [mem_support_iff, ne_eq, Nat.bot_eq_zero] at h
      have : ⊥ < p.mainVariable := by rewrite [hc]; exact compareOfLessAndEq_eq_lt.mp rfl
      rcases (Finset.le_sup_iff this).mp le_rfl with ⟨t, ht1, ht2⟩
      absurd (Finset.sup_le_iff.mp <| le_of_eq hc) t ht1
      have h := Finsupp.notMem_support_iff.mpr (h t <| mem_support_iff.mp ht1)
      have : c ≠ t.support.max := by contrapose! h; exact Finset.mem_of_max h.symm
      exact not_le_of_gt <| lt_of_le_of_ne (le_of_eq_of_le hc.symm ht2) this
  mpr h := by rw [mainDegree, h]

theorem mainDegree_eq_zero_iff' : p.mainDegree = 0 ↔ (∃ r : R, p = C r) :=
  Iff.trans mainDegree_eq_zero_iff mainVariable_eq_bot_iff_eq_C

theorem degreeOf_mainVariable_ne_zero : p.mainVariable = c → p.degreeOf c ≠ 0 := fun h ↦
  have := (not_iff_not.mpr mainDegree_eq_zero_iff).mpr (h ▸ WithBot.coe_ne_bot)
  mainDegree_of_mainVariable_isSome h ▸ this

theorem mainVariable_mem_degrees : p.mainVariable = c → c ∈ p.degrees := fun h ↦
  have := degreeOf_mainVariable_ne_zero h; Multiset.count_ne_zero.mp (degreeOf_def c p ▸ this)

@[simp] theorem mainDegree_zero : (0 : MvPolynomial σ R).mainDegree = 0 := rfl

@[simp] theorem mainDegree_monomial {s : σ →₀ ℕ} {r : R} (hr : r ≠ 0)
    (hs : s.support.max = c) : (monomial s r).mainDegree = s c := by
  rewrite [mainDegree_of_mainVariable_isSome <| (mainVariable_monomial s hr).trans hs]
  exact degreeOf_monomial_eq s c hr

@[simp] theorem mainDegree_C (r : R) : (C r : MvPolynomial σ R).mainDegree = 0 :=
  mainDegree_eq_zero_iff.mpr <| mainVariable_C r

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
