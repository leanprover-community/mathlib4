/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

! This file was ported from Lean 3 source module data.nat.gcd.big_operators
! leanprover-community/mathlib commit 008205aa645b3f194c1da47025c5f110c8406eab
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Gcd.Basic
import Mathbin.Algebra.BigOperators.Basic

/-! # Lemmas about coprimality with big products.

These lemmas are kept separate from `data.nat.gcd.basic` in order to minimize imports.
-/


namespace Nat

open BigOperators

/-- See `is_coprime.prod_left` for the corresponding lemma about `is_coprime` -/
theorem coprime_prod_left {ι : Type _} {x : ℕ} {s : ι → ℕ} {t : Finset ι} :
    (∀ i : ι, i ∈ t → Coprime (s i) x) → Coprime (∏ i : ι in t, s i) x :=
  Finset.prod_induction s (fun y => y.Coprime x) (fun a b => Coprime.mul) (by simp)
#align nat.coprime_prod_left Nat.coprime_prod_left

/-- See `is_coprime.prod_right` for the corresponding lemma about `is_coprime` -/
theorem coprime_prod_right {ι : Type _} {x : ℕ} {s : ι → ℕ} {t : Finset ι} :
    (∀ i : ι, i ∈ t → Coprime x (s i)) → Coprime x (∏ i : ι in t, s i) :=
  Finset.prod_induction s (fun y => x.Coprime y) (fun a b => Coprime.mul_right) (by simp)
#align nat.coprime_prod_right Nat.coprime_prod_right

end Nat

