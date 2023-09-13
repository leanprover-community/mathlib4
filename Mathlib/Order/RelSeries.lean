/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.Logic.Equiv.Fin
import Mathlib.Data.List.Indexes
import Mathlib.Data.Rel

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
/-- The number of inequalities in the series -/
length : ℕ
/-- The underlying function of a relation series -/
toFun : Fin (length + 1) → α
/-- Adjacent elements are related -/
step : ∀ (i : Fin length), r (toFun (Fin.castSucc i)) (toFun i.succ)

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

@[ext]
lemma ext {x y : RelSeries r} (length_eq : x.length = y.length)
    (toFun_eq : x.toFun = y.toFun ∘ Fin.cast (by rw [length_eq])) : x = y := by
  rcases x with ⟨nx, fx⟩
  rcases y with ⟨ny, fy⟩
  dsimp at length_eq toFun_eq
  subst length_eq
  rw [Fin.cast_refl, Function.comp.right_id] at toFun_eq
  subst toFun_eq
  rfl

lemma rel_of_lt [IsTrans α r] (x : RelSeries r) {i j : Fin (x.length + 1)} (h : i < j) :
    r (x i) (x j) := by
  induction i using Fin.inductionOn generalizing j with
  | zero => induction j using Fin.inductionOn with
    | zero => cases lt_irrefl _ h
    | succ j ihj =>
      by_cases H : 0 < Fin.castSucc j
      · exact IsTrans.trans _ _ _ (ihj H) (x.step _)
      · simp only [not_lt, Fin.le_zero_iff] at H
        rw [← H]
        exact x.step _
  | succ i _ => induction j using Fin.inductionOn with
    | zero => cases not_lt_of_lt (Fin.succ_pos i) h
    | succ j ihj =>
      obtain (H|H) : i.succ = Fin.castSucc j ∨ i.succ < Fin.castSucc j
      . change (i + 1 : ℕ) < (j + 1 : ℕ) at h
        rw [Nat.lt_succ_iff, le_iff_lt_or_eq] at h
        rcases h with (h|h)
        . exact Or.inr h
        . left
          ext
          exact h
      . rw [H]
        exact x.step _
      . exact IsTrans.trans _ _ _ (ihj H) (x.step _)

lemma rel_or_eq_of_le [IsTrans α r] (x : RelSeries r) {i j : Fin (x.length + 1)} (h : i ≤ j) :
    r (x i) (x j) ∨ x i = x j :=
  (le_iff_lt_or_eq.mp h).by_cases (Or.intro_left _ $ x.rel_of_lt .) (Or.intro_right _ $ . ▸ rfl)

/--
Given two relations `r, s` on `α` such that `r ≤ s`, any relation series of `r` induces a relation
series of `s`
-/
@[simps!]
def OfLE (x : RelSeries r) {s : Rel α α} (h : r ≤ s) : RelSeries s where
  length := x.length
  toFun := x
  step := fun _ => h _ _ <| x.step _

lemma ofLE_length (x : RelSeries r) {s : Rel α α} (h : r ≤ s) :
    (x.OfLE h).length = x.length := rfl

lemma coe_ofLE (x : RelSeries r) {s : Rel α α} (h : r ≤ s) :
  (x.OfLE h : _ → _) = x := rfl

/-- Every relation series gives a list -/
abbrev toList (x : RelSeries r) : List α := List.ofFn x

lemma toList_chain' (x : RelSeries r) : x.toList.Chain' r := by
  rw [List.chain'_iff_get]
  intros i h
  have h' : i < x.length := by simpa [List.length_ofFn] using h
  convert x.step ⟨i, h'⟩ <;>
  . rw [List.get_ofFn]
    congr 1

lemma toList_ne_empty (x : RelSeries r) : x.toList ≠ ∅ := fun m =>
  List.eq_nil_iff_forall_not_mem.mp m (x 0) <| (List.mem_ofFn _ _).mpr ⟨_, rfl⟩

/-- Every nonempty list satisfying the chain condition gives a relation series-/
@[simps]
def fromListChain' (x : List α) (x_ne_empty : x ≠ ∅) (hx : x.Chain' r) : RelSeries r where
  length := x.length.pred
  toFun := x.get ∘ Fin.cast (Nat.succ_pred_eq_of_pos <| List.length_pos.mpr x_ne_empty)
  step := fun i => List.chain'_iff_get.mp hx i i.2

/-- Relation series of `r` and nonempty list of `α` satisfying `r`-chain condition bijectively
corresponds to each other.-/
protected def Equiv : RelSeries r ≃ {x : List α | x ≠ ∅ ∧ x.Chain' r} where
  toFun := fun x => ⟨_, x.toList_ne_empty, x.toList_chain'⟩
  invFun := fun x => fromListChain' _ x.2.1 x.2.2
  left_inv := fun x => ext (by dsimp; rw [List.length_ofFn, Nat.pred_succ]) <| by
    ext f
    simp only [List.empty_eq, ne_eq, Set.coe_setOf, Set.mem_setOf_eq, fromListChain'_toFun,
      Function.comp_apply, List.get_ofFn, fromListChain'_length]
    rfl
  right_inv := by
    intro x
    refine Subtype.ext (List.ext_get ?_ <| fun n hn1 hn2 => ?_)
    . dsimp
      rw [List.length_ofFn, fromListChain'_length, ←Nat.succ_eq_add_one, Nat.succ_pred_eq_of_pos]
      rw [List.length_pos]
      exact x.2.1
    . rw [List.get_ofFn, fromListChain'_toFun, Function.comp_apply]
      congr

-- TODO : build a similar bijection between `RelSeries α` and `Quiver.Path`

end RelSeries

namespace Rel

/-- a relation `r` is said to be finite dimensional iff there is a relation series of `r` with the
  maximum length. -/
class FiniteDimensional where
  /-- the longest relation series-/
  longestRelSeries : RelSeries r
  /-- the longest relation series is longer than any other series -/
  is_longest : ∀ (y : RelSeries r), y.length ≤ longestRelSeries.length

/-- the longest relational series when a relation is finite dimensional -/
def longestRelSeries [r.FiniteDimensional] : RelSeries r := FiniteDimensional.longestRelSeries

lemma longestRelSeries_is_longest [r.FiniteDimensional] (x : RelSeries r) :
  x.length ≤ r.longestRelSeries.length := FiniteDimensional.is_longest _

/-- a relation `r` is said to be infinite dimensional iff there exists relation series of arbitrary
  length. -/
class InfiniteDimensional where
  /-- there should a relation series with length at least `n` for all natural number `n` -/
  longRelSeries : ℕ → RelSeries r
  /-- there should a relation series with length at least `n` for all natural number `n` -/
  longRelSeries_length : ∀ (n : ℕ), n ≤ (longRelSeries n).length

/-- a relation series with length at least `n` if the relation is infinite dimensional -/
def relSeriesOfInfiniteDimensional [InfiniteDimensional r] (n : ℕ) : RelSeries r :=
  (InfiniteDimensional.longRelSeries n)

lemma le_relSeriesOfInfiniteDimensional_length [InfiniteDimensional r] (n : ℕ) :
  n ≤ (r.relSeriesOfInfiniteDimensional n).length := InfiniteDimensional.longRelSeries_length n

/-- if a relation on `α` is infinite dimensional, then `α` is inhabited -/
def inhabited_of_infiniteDimensional [r.InfiniteDimensional] : Inhabited α :=
  ⟨(r.relSeriesOfInfiniteDimensional 0) 0⟩

end Rel

class FiniteDimensionalType (γ : Type _) [Preorder γ] extends
  Rel.FiniteDimensional ((. < .) : γ → γ → Prop)

class InfiniteDimensionalType (γ : Type _) [Preorder γ] extends
  Rel.InfiniteDimensional ((. < .) : γ → γ → Prop)

section LTSeries

variable (α) [Preorder α]
/--
If `α` is a preordered set, a series ordered by less than is a relation series of the less than
relation.
-/
abbrev LTSeries := RelSeries ((. < .) : Rel α α)

namespace LTSeries

/-- the longest  `<`-series when a type is finite dimensional -/
def longest [FiniteDimensionalType α] : LTSeries α :=
  (inferInstance : FiniteDimensionalType α).longestRelSeries

/-- a `<`-series with length at least `n` if the relation is infinite dimensional -/
def lengthAtLeast [InfiniteDimensionalType α] (n : ℕ) : LTSeries α :=
  ((inferInstance : InfiniteDimensionalType α).longRelSeries n)

lemma le_lengthAtLeast_length [InfiniteDimensionalType α] (n : ℕ) :
  n ≤ (LTSeries.lengthAtLeast α n).length :=
((inferInstance : InfiniteDimensionalType α).longRelSeries_length n)

/-- if `α` is infinite dimensional, then `α` is inhabited -/
def inhabited_of_infiniteDimensionalType [InfiniteDimensionalType α] : Inhabited α :=
  ⟨(LTSeries.lengthAtLeast α 0) 0⟩

variable {α}

lemma longest_is_longest [FiniteDimensionalType α] (x : LTSeries α) :
  x.length ≤ (LTSeries.longest α).length :=
(inferInstance : FiniteDimensionalType α).is_longest x

lemma longest_len_unique [FiniteDimensionalType α] (p : LTSeries α)
  (is_longest : ∀ (q : LTSeries α), q.length ≤ p.length) :
  p.length = (longest α).length :=
le_antisymm (longest_is_longest _) (is_longest _)

lemma longest_len_unique' (H1 H2 : FiniteDimensionalType α) :
  (@longest α _ H1).length = (@longest α _ H2).length :=
le_antisymm
  (@longest_is_longest α _ H2 (@longest α _ H1))
  (@longest_is_longest α _ H1 (@longest α _ H2))

lemma strictMono (x : LTSeries α) : StrictMono x :=
  fun _ _ h => x.rel_of_lt h

section PartialOrder

variable {β : Type _} [PartialOrder β]

lemma Monotone (x : LTSeries β) : Monotone x :=
  fun _ _ h => le_iff_lt_or_eq.mpr $ x.rel_or_eq_of_le h

end PartialOrder

end LTSeries

end LTSeries
