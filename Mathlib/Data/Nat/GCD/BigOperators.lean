/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.BigOperators.Basic

#align_import data.nat.gcd.big_operators from "leanprover-community/mathlib"@"008205aa645b3f194c1da47025c5f110c8406eab"

/-! # Lemmas about coprimality with big products.

These lemmas are kept separate from `Data.Nat.GCD.Basic` in order to minimize imports.
-/


namespace Nat

open BigOperators

theorem coprime_prod_left_iff {ι : Type*} {x : ℕ} {s : ι → ℕ} {t : Finset ι} :
    Coprime (∏ i in t, s i) x ↔ ∀ i ∈ t, Coprime (s i) x :=
  Finset.cons_induction_on t (by simp) fun i s his ih ↦ by
    rw [Finset.prod_cons, Nat.coprime_mul_iff_left, ih, Finset.forall_mem_cons]

theorem coprime_prod_right_iff {ι : Type*} {x : ℕ} {s : ι → ℕ} {t : Finset ι} :
    Coprime x (∏ i in t, s i) ↔ ∀ i ∈ t, Coprime x (s i) :=
  Finset.cons_induction_on t (by simp) fun i s his ih ↦ by
    rw [Finset.prod_cons, Nat.coprime_mul_iff_right, ih, Finset.forall_mem_cons]

/-- See `IsCoprime.prod_left` for the corresponding lemma about `IsCoprime` -/
alias ⟨_, Coprime.prod_left⟩ := coprime_prod_left_iff
#align nat.coprime_prod_left Nat.Coprime.prod_left

/-- See `IsCoprime.prod_right` for the corresponding lemma about `IsCoprime` -/
alias ⟨_, Coprime.prod_right⟩ := coprime_prod_right_iff
#align nat.coprime_prod_right Nat.Coprime.prod_right

theorem coprime_fintype_prod_left_iff {ι : Type*} [Fintype ι] {x : ℕ} {s : ι → ℕ} :
    Coprime (∏ i, s i) x ↔ ∀ i, Coprime (s i) x := by
  simp [coprime_prod_left_iff]

theorem coprime_fintype_prod_right_iff {ι : Type*} [Fintype ι]
    {x : ℕ} {s : ι → ℕ} : Coprime x (∏ i, s i) ↔ ∀ i, Coprime x (s i) := by
  simp [coprime_prod_right_iff]

theorem coprime_list_prod_left_iff {k} {l : List ℕ} :
    Coprime l.prod k ↔ ∀ n ∈ l, Coprime n k := by
  induction l <;> simp [Nat.coprime_mul_iff_left, *]

theorem coprime_list_prod_right_iff {k} {l : List ℕ} :
    Coprime k l.prod ↔ ∀ n ∈ l, Coprime k n := by
  induction l <;> simp [Nat.coprime_mul_iff_right, *]

theorem coprime_multiset_prod_left_iff {k} {m : Multiset ℕ} :
    Coprime m.prod k ↔ ∀ n ∈ m, Coprime n k := by
  induction m using Multiset.induction <;> simp [Nat.coprime_mul_iff_left, *]

theorem coprime_multiset_prod_right_iff {k} {m : Multiset ℕ} :
    Coprime k m.prod ↔ ∀ n ∈ m, Coprime k n := by
  induction m using Multiset.induction <;> simp [Nat.coprime_mul_iff_right, *]

end Nat
