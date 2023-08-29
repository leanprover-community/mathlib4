/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Data.Int.Order.Basic

#align_import data.int.least_greatest from "leanprover-community/mathlib"@"3342d1b2178381196f818146ff79bc0e7ccd9e2d"

/-! # Least upper bound and greatest lower bound properties for integers

In this file we prove that a bounded above nonempty set of integers has the greatest element, and a
counterpart of this statement for the least element.

## Main definitions

* `Int.leastOfBdd`: if `P : ℤ → Prop` is a decidable predicate, `b` is a lower bound of the set
  `{m | P m}`, and there exists `m : ℤ` such that `P m` (this time, no witness is required), then
  `Int.leastOfBdd` returns the least number `m` such that `P m`, together with proofs of `P m` and
  of the minimality. This definition is computable and does not rely on the axiom of choice.
* `Int.greatestOfBdd`: a similar definition with all inequalities reversed.

## Main statements

* `Int.exists_least_of_bdd`: if `P : ℤ → Prop` is a predicate such that the set `{m : P m}` is
  bounded below and nonempty, then this set has the least element. This lemma uses classical logic
  to avoid assumption `[DecidablePred P]`. See `Int.leastOfBdd` for a constructive counterpart.

* `Int.coe_leastOfBdd_eq`: `(Int.leastOfBdd b Hb Hinh : ℤ)` does not depend on `b`.

* `Int.exists_greatest_of_bdd`, `Int.coe_greatest_of_bdd_eq`: versions of the above lemmas with all
  inequalities reversed.

## Tags

integer numbers, least element, greatest element
-/


namespace Int

/-- A computable version of `exists_least_of_bdd`: given a decidable predicate on the
integers, with an explicit lower bound and a proof that it is somewhere true, return
the least value for which the predicate is true. -/
def leastOfBdd {P : ℤ → Prop} [DecidablePred P] (b : ℤ) (Hb : ∀ z : ℤ, P z → b ≤ z)
    (Hinh : ∃ z : ℤ, P z) : { lb : ℤ // P lb ∧ ∀ z : ℤ, P z → lb ≤ z } :=
  have EX : ∃ n : ℕ, P (b + n) :=
    let ⟨elt, Helt⟩ := Hinh
    match elt, le.dest (Hb _ Helt), Helt with
    | _, ⟨n, rfl⟩, Hn => ⟨n, Hn⟩
  ⟨b + (Nat.find EX : ℤ), Nat.find_spec EX, fun z h =>
    match z, le.dest (Hb _ h), h with
    | _, ⟨_, rfl⟩, h => add_le_add_left (Int.ofNat_le.2 <| Nat.find_min' _ h) _⟩
#align int.least_of_bdd Int.leastOfBdd


/--
    If `P : ℤ → Prop` is a predicate such that the set `{m : P m}` is bounded below and nonempty,
    then this set has the least element. This lemma uses classical logic to avoid assumption
    `[DecidablePred P]`. See `Int.leastOfBdd` for a constructive counterpart. -/
theorem exists_least_of_bdd
    {P : ℤ → Prop}
    [DecidablePred P]
    (Hbdd : ∃ b : ℤ , ∀ z : ℤ , P z → b ≤ z)
    (Hinh : ∃ z : ℤ , P z) : ∃ lb : ℤ , P lb ∧ ∀ z : ℤ , P z → lb ≤ z := by
  let ⟨b , Hb⟩ := Hbdd
  -- ⊢ ∃ lb, P lb ∧ ∀ (z : ℤ), P z → lb ≤ z
  let ⟨lb , H⟩ := leastOfBdd b Hb Hinh
  -- ⊢ ∃ lb, P lb ∧ ∀ (z : ℤ), P z → lb ≤ z
  exact ⟨lb , H⟩
  -- 🎉 no goals
#align int.exists_least_of_bdd Int.exists_least_of_bdd

theorem coe_leastOfBdd_eq {P : ℤ → Prop} [DecidablePred P] {b b' : ℤ} (Hb : ∀ z : ℤ, P z → b ≤ z)
    (Hb' : ∀ z : ℤ, P z → b' ≤ z) (Hinh : ∃ z : ℤ, P z) :
    (leastOfBdd b Hb Hinh : ℤ) = leastOfBdd b' Hb' Hinh := by
  rcases leastOfBdd b Hb Hinh with ⟨n, hn, h2n⟩
  -- ⊢ ↑{ val := n, property := (_ : P n ∧ ∀ (z : ℤ), P z → n ≤ z) } = ↑(leastOfBdd …
  rcases leastOfBdd b' Hb' Hinh with ⟨n', hn', h2n'⟩
  -- ⊢ ↑{ val := n, property := (_ : P n ∧ ∀ (z : ℤ), P z → n ≤ z) } = ↑{ val := n' …
  exact le_antisymm (h2n _ hn') (h2n' _ hn)
  -- 🎉 no goals
#align int.coe_least_of_bdd_eq Int.coe_leastOfBdd_eq

/-- A computable version of `exists_greatest_of_bdd`: given a decidable predicate on the
integers, with an explicit upper bound and a proof that it is somewhere true, return
the greatest value for which the predicate is true. -/
def greatestOfBdd {P : ℤ → Prop} [DecidablePred P] (b : ℤ) (Hb : ∀ z : ℤ, P z → z ≤ b)
    (Hinh : ∃ z : ℤ, P z) : { ub : ℤ // P ub ∧ ∀ z : ℤ, P z → z ≤ ub } :=
  have Hbdd' : ∀ z : ℤ, P (-z) → -b ≤ z := fun z h => neg_le.1 (Hb _ h)
  have Hinh' : ∃ z : ℤ, P (-z) :=
    let ⟨elt, Helt⟩ := Hinh
    ⟨-elt, by rw [neg_neg]; exact Helt⟩
              -- ⊢ P elt
                            -- 🎉 no goals
  let ⟨lb, Plb, al⟩ := leastOfBdd (-b) Hbdd' Hinh'
  ⟨-lb, Plb, fun z h => le_neg.1 <| al _ <| by rwa [neg_neg]⟩
                                               -- 🎉 no goals
#align int.greatest_of_bdd Int.greatestOfBdd

/--
    If `P : ℤ → Prop` is a predicate such that the set `{m : P m}` is bounded above and nonempty,
    then this set has the greatest element. This lemma uses classical logic to avoid assumption
    `[DecidablePred P]`. See `Int.greatestOfBdd` for a constructive counterpart. -/
theorem exists_greatest_of_bdd
    {P : ℤ → Prop}
    [DecidablePred P]
    (Hbdd : ∃ b : ℤ , ∀ z : ℤ , P z → z ≤ b)
    (Hinh : ∃ z : ℤ , P z) : ∃ ub : ℤ , P ub ∧ ∀ z : ℤ , P z → z ≤ ub := by
  let ⟨ b , Hb ⟩ := Hbdd
  -- ⊢ ∃ ub, P ub ∧ ∀ (z : ℤ), P z → z ≤ ub
  let ⟨ lb , H ⟩ := greatestOfBdd b Hb Hinh
  -- ⊢ ∃ ub, P ub ∧ ∀ (z : ℤ), P z → z ≤ ub
  exact ⟨ lb , H ⟩
  -- 🎉 no goals
#align int.exists_greatest_of_bdd Int.exists_greatest_of_bdd

theorem coe_greatestOfBdd_eq {P : ℤ → Prop} [DecidablePred P] {b b' : ℤ}
    (Hb : ∀ z : ℤ, P z → z ≤ b) (Hb' : ∀ z : ℤ, P z → z ≤ b') (Hinh : ∃ z : ℤ, P z) :
    (greatestOfBdd b Hb Hinh : ℤ) = greatestOfBdd b' Hb' Hinh := by
  rcases greatestOfBdd b Hb Hinh with ⟨n, hn, h2n⟩
  -- ⊢ ↑{ val := n, property := (_ : P n ∧ ∀ (z : ℤ), P z → z ≤ n) } = ↑(greatestOf …
  rcases greatestOfBdd b' Hb' Hinh with ⟨n', hn', h2n'⟩
  -- ⊢ ↑{ val := n, property := (_ : P n ∧ ∀ (z : ℤ), P z → z ≤ n) } = ↑{ val := n' …
  exact le_antisymm (h2n' _ hn) (h2n _ hn')
  -- 🎉 no goals
#align int.coe_greatest_of_bdd_eq Int.coe_greatestOfBdd_eq

end Int
