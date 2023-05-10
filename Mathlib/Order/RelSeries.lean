/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.Data.Rel
import Mathlib.Logic.Equiv.Fin

/-!
# Series of a relation
If `r` is a relation on `α` then a relation series of length `n` is a series
`a_0, a_1, ..., a_n` such that `r a_i a_{i+1}` for all `i < n`

-/

variable {α : Type _} (r : Rel α α)

/--
Let `r` be a relation on `α`, a relation series of `r` of length `n` is a series
`a_0, a_1, ..., a_n` such that `r a_i a_{i+1}` for all `i < n`
-/
structure RelSeries where
/-- the number of inequalities in the series -/
length : ℕ
/-- the underlying function of a relation series -/
toFun : Fin (length + 1) → α
/-- adjacent elements are related by the said relation -/
step : ∀ (i : Fin length), r (toFun <| Fin.castSucc i) <| toFun <| i.succ

namespace RelSeries

instance : CoeFun (RelSeries r) (fun x ↦ Fin (x.length + 1) → α) :=
{ coe := RelSeries.toFun }

/--
For any type `α`, each term of `α` gives a relation series with the right most index to be 0.
-/
@[simps!] def singleton (a : α) : RelSeries r where
length := 0
toFun := fun _ => a
step := fun i => Fin.elim0 i

instance [IsEmpty α] : IsEmpty (RelSeries r) where
false := fun x ↦ IsEmpty.false (x 0)

instance [Inhabited α] : Inhabited (RelSeries r) where
default := singleton r default

instance [Nonempty α] : Nonempty (RelSeries r) :=
Nonempty.map (singleton r) inferInstance

variable {r}

lemma StrictMono [IsTrans α r] (x : RelSeries r) {i j : Fin (x.length + 1)} (h : i < j) :
    r (x i) (x j) := by
  induction i using Fin.inductionOn generalizing j with
  | h0 => induction j using Fin.inductionOn with
    | h0 => cases lt_irrefl _ h
    | hs j ihj =>
      by_cases H : 0 < Fin.castSucc j
      . exact IsTrans.trans _ _ _ (ihj H) (x.step _)
      . convert x.step _
        simp only [not_lt, Fin.le_zero_iff] at H
        exact H.symm
  | hs i _ => induction j using Fin.inductionOn with
    | h0 => cases not_lt_of_lt (Fin.succ_pos i) h
    | hs j ihj =>
      obtain (H|H) : i.succ = Fin.castSucc j ∨ i.succ < Fin.castSucc j
      . change (i + 1 : ℕ) < (j + 1 : ℕ) at h
        rw [Nat.lt_succ_iff, le_iff_lt_or_eq] at h
        rcases h with (h|h)
        . right
          exact h
        . left
          ext
          exact h
      . rw [H]
        exact x.step _
      . exact IsTrans.trans _ _ _ (ihj H) (x.step _)

lemma Monotone [IsTrans α r] (x : RelSeries r) {i j : Fin (x.length + 1)} (h : i ≤ j) :
    r (x i) (x j) ∨ x i = x j := by
  rw [le_iff_lt_or_eq] at h
  rcases h with (h|h)
  . left
    apply x.StrictMono h
  . right
    rw [h]

end RelSeries

section LTSeries

variable (α) [Preorder α]
/--
If `α` is a preordered set, a series ordered by less than is a relation series of the less than
relation.
-/
structure LTSeries extends RelSeries ((. < .) : Rel α α)

namespace LTSeries

instance : Preorder (LTSeries α) :=
Preorder.lift fun x => x.length

variable {α}

instance : CoeFun (LTSeries α) (fun x ↦ Fin (x.length + 1) → α) :=
{ coe := fun x => x.toFun }

lemma le_def (x y : LTSeries α) : x ≤ y ↔ x.length ≤ y.length :=
Iff.rfl

lemma lt_def (x y : LTSeries α) : x < y ↔ x.length < y.length :=
Iff.rfl

lemma top_len_unique [OrderTop (LTSeries α)] (p : LTSeries α) (hp : IsTop p) :
  p.length = (⊤ : LTSeries α).length :=
le_antisymm (@le_top (LTSeries α) _ _ _) (hp ⊤)

lemma top_len_unique' (H1 H2 : OrderTop (LTSeries α)) : H1.top.length = H2.top.length :=
le_antisymm (H2.le_top H1.top) (H1.le_top H2.top)

lemma StrictMono (x : LTSeries α) : StrictMono x :=
fun _ _ h => x.toRelSeries.StrictMono h

section PartialOrder

variable {β : Type _} [PartialOrder β]

lemma Monotone (x : LTSeries β) : Monotone x :=
fun _ _ h => by
  rw [le_iff_lt_or_eq]
  exact x.toRelSeries.Monotone h

end PartialOrder

end LTSeries

end LTSeries
