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

end Nat
