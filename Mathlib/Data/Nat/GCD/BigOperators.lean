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

/-- See `IsCoprime.prod_left` for the corresponding lemma about `IsCoprime` -/
theorem coprime_prod_left {ι : Type*} {x : ℕ} {s : ι → ℕ} {t : Finset ι} :
    (∀ i : ι, i ∈ t → Coprime (s i) x) → Coprime (∏ i : ι in t, s i) x :=
  Finset.prod_induction s (fun y ↦ y.Coprime x) (fun a b ↦ Coprime.mul) (by simp)
#align nat.coprime_prod_left Nat.coprime_prod_left

/-- See `IsCoprime.prod_right` for the corresponding lemma about `IsCoprime` -/
theorem coprime_prod_right {ι : Type*} {x : ℕ} {s : ι → ℕ} {t : Finset ι} :
    (∀ i : ι, i ∈ t → Coprime x (s i)) → Coprime x (∏ i : ι in t, s i) :=
  Finset.prod_induction s (fun y ↦ x.Coprime y) (fun a b ↦ Coprime.mul_right) (by simp)
#align nat.coprime_prod_right Nat.coprime_prod_right

theorem coprime_prod_left_iff {ι : Type*} [DecidableEq ι] {x : ℕ} {s : ι → ℕ} {t : Finset ι} :
    Coprime (∏ i : ι in t, s i) x ↔ (∀ i : ι, i ∈ t → Coprime (s i) x) :=
  Finset.induction_on t (by simp) fun i s his ih ↦ by
    rw [Finset.prod_insert his, Nat.coprime_mul_iff_left, ih, Finset.forall_mem_insert]

theorem coprime_prod_right_iff {ι : Type*} [DecidableEq ι] {x : ℕ} {s : ι → ℕ} {t : Finset ι} :
    Coprime x (∏ i : ι in t, s i) ↔ (∀ i : ι, i ∈ t → Coprime x (s i)) :=
  Finset.induction_on t (by simp) fun i s his ih ↦ by
    rw [Finset.prod_insert his, Nat.coprime_mul_iff_right, ih, Finset.forall_mem_insert]

theorem coprime_fintype_prod_left_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {x : ℕ} {s : ι → ℕ} :
    Coprime (∏ i, s i) x ↔ (∀ i : ι, Coprime (s i) x) := by
  simp [coprime_prod_left_iff]

theorem coprime_fintype_prod_right_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {x : ℕ} {s : ι → ℕ} : Coprime x (∏ i, s i) ↔ (∀ i : ι, Coprime x (s i)) := by
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
