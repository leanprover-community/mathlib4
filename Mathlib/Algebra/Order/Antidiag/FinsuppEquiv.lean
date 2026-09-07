/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card

/-!

# Equivalence between `Finset.finsuppAntidiagonal` and `Sym`

This file collects further results about equivalence and cardinality related to
`Finset.finsuppAntidiagonal`. This file is separated from
`Mathlib.Algebra.Order.Antidiag.Finsupp` to reduce imports.

## Main declarations
* `Finset.finsuppAntidiagonalEquivSubtype`: `Finset.finsuppAntidiagonal s n` is equivalent to
  subtype of `s →₀ μ` whose sum is `n`.
* `Finset.finsuppAntidiagonalEquiv`: `Finset.finsuppAntidiagonal s n` is equivalent to `Sym s n` for
  natural number `n`.
* `Finset.card_finsuppAntidiagonal_nat_eq_choose` and
  `Finset.card_finsuppAntidiagonal_nat_eq_multichoose`:
  cardinality formula for `Finset.finsuppAntidiagonal s n` for natural number `n`.
-/

@[expose] public section

open Finsupp Function

variable {ι μ : Type*}

namespace Finset
variable [DecidableEq ι] [AddCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ] {s : Finset ι}
  {n : μ}

variable (s n) in
/-- The equivalence between `Finset.finsuppAntidiagonal s n` and the subtype of `s →₀ μ`
whose sum is `n`. -/
@[simps]
noncomputable def finsuppAntidiagonalEquivSubtype :
    s.finsuppAntidiagonal n ≃ { P : s →₀ μ // (P.sum fun (_ : s) ↦ id) = n } where
  toFun f := ⟨subtypeDomain (· ∈ s) f.val, by
    have hf := f.2
    rw [mem_finsuppAntidiagonal'] at hf
    simpa [sum, filter_mem_eq_inter, inter_eq_left.mpr hf.2] using hf.1⟩
  invFun f := ⟨extendDomain f.val, mem_finsuppAntidiagonal'.mpr
    ⟨by simpa [sum] using f.2, by simp [map_eq_image, image_subset_iff]⟩⟩
  left_inv f := by
    obtain ⟨hsum, hs⟩ := mem_finsuppAntidiagonal.mp f.prop
    ext1
    exact extendDomain_subtypeDomain _ hs
  right_inv f := by simp

@[deprecated (since := "2026-09-06")]
alias finsuppAntidiagEquivSubtype := finsuppAntidiagonalEquivSubtype

variable (s) in
/-- The equivalence between `Finset.finsuppAntidiagonal s n` and `Sym s n`. -/
noncomputable def finsuppAntidiagonalEquiv (n : ℕ) : s.finsuppAntidiagonal n ≃ Sym s n :=
  (finsuppAntidiagonalEquivSubtype s n).trans (Sym.equivNatSum s n).symm

@[deprecated (since := "2026-09-06")] alias finsuppAntidiagEquiv := finsuppAntidiagonalEquiv

@[simp]
theorem finsuppAntidiagonalEquiv_symm_apply_apply (n : ℕ) (f : Sym s n) (a : s) :
    ((finsuppAntidiagonalEquiv s n).symm f).val a.val = f.toMultiset.count a := by
  simp [finsuppAntidiagonalEquiv]

@[deprecated (since := "2026-09-06")]
alias finsuppAntidiagEquiv_symm_apply_apply := finsuppAntidiagonalEquiv_symm_apply_apply

@[simp]
theorem count_coe_finsuppAntidiagonalEquiv_apply (n : ℕ) (f : s.finsuppAntidiagonal n) (a : s) :
    (finsuppAntidiagonalEquiv s n f).toMultiset.count a = f.val a := by
  simp [finsuppAntidiagonalEquiv]

@[deprecated (since := "2026-09-06")]
alias count_coe_finsuppAntidiagEquiv_apply := count_coe_finsuppAntidiagonalEquiv_apply

theorem card_finsuppAntidiagonal_nat_eq_choose (n : ℕ) :
    #(s.finsuppAntidiagonal n) = (#s + n - 1).choose n := by
  simp [card_eq_of_equiv_fintype (finsuppAntidiagonalEquiv s n), Sym.card_sym_eq_choose]

@[deprecated (since := "2026-09-06")]
alias card_finsuppAntidiag_nat_eq_choose := card_finsuppAntidiagonal_nat_eq_choose

theorem card_finsuppAntidiagonal_nat_eq_multichoose (n : ℕ) :
    #(s.finsuppAntidiagonal n) = (#s).multichoose n := by
  simp [card_eq_of_equiv_fintype (finsuppAntidiagonalEquiv s n), Sym.card_sym_eq_multichoose]

@[deprecated (since := "2026-09-06")]
alias card_finsuppAntidiag_nat_eq_multichoose := card_finsuppAntidiagonal_nat_eq_multichoose

end Finset
