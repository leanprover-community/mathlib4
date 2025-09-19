/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.Tactic.Zify
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.Ring.Basic

/-! # Normal forms for morphisms in `SimplexCategoryGenRel`.

In this file, we establish that `P_δ` and `P_σ` morphisms in `SimplexCategoryGenRel`
each admits a normal form.

In both cases, the normal forms are encoded as an integer `m`, and a strictly increasing
lists of integers `[i₀,…,iₙ]` such that `iₖ ≤ m + k` for all `k`. We define a predicate
`isAdmissible m : List ℕ → Prop` encoding this property. And provide some lemmas to help
work with such lists.

Normal forms for `P_σ` morphisms are encoded by `m`-admissible lists, in which case the list
`[i₀,…,iₙ]` represents the morphism `σ iₙ ≫ ⋯ ≫ σ i₀ : .mk (m + n) ⟶ .mk n`.

Normal forms for `P_δ` morphisms are encoded by `(m + 1)`-admissible lists, in which case the list
`[i₀,…,iₙ]` represents the morphism `δ i₀ ≫ ⋯ ≫ δ iₙ : .mk n ⟶ .mk (m + n)`.

The results in this file are to be treated as implementation-only, and they only serve as stepping
stones towards proving that the canonical functor
`toSimplexCategory : SimplexCategoryGenRel ⥤ SimplexCategory` is an equivalence.

## References:
* [Kerodon Tag 04FQ](https://kerodon.net/tag/04FQ)
* [Kerodon Tag 04FT](https://kerodon.net/tag/04FT)

## TODOs:
- Show that every `P_σ` admits a unique normal form.
- Show that every `P_δ` admits a unique normal form.
-/

namespace SimplexCategoryGenRel

section AdmissibleLists
-- Impl. note: We are not bundling admissible lists as a subtype of `List ℕ` so that it remains
-- easier to perform inductive constructions and proofs on such lists, and we instead bundle
-- propositions asserting that various List constructions produce admissible lists.

variable (m : ℕ)
/-- A list of natural numbers [i₀, ⋯, iₙ]) is said to be `m`-admissible (for `m : ℕ`) if
`i₀ < ⋯ < iₙ` and `iₖ ≤ m + k` for all `k`.
-/
def IsAdmissible (L : List ℕ) : Prop :=
  List.Sorted (· < ·) L ∧
  ∀ (k : ℕ), (h : k < L.length) → L[k] ≤ m + k

namespace IsAdmissible

lemma nil : IsAdmissible m [] := by simp [IsAdmissible]

variable {m}

lemma sorted {L : List ℕ} (hL : IsAdmissible m L) : L.Sorted (· < ·) := hL.1

lemma le {L : List ℕ} (hL : IsAdmissible m L) : ∀ (k : ℕ), (h : k < L.length) → L[k] ≤ m + k := hL.2

/-- If `(a :: l)` is `m`-admissible then a is less than all elements of `l` -/
lemma head_lt (a : ℕ) (L : List ℕ) (hl : IsAdmissible m (a :: L)) :
    ∀ a' ∈ L, a < a' := fun i hi ↦ (List.sorted_cons.mp hl.sorted).left i hi

/-- If `L` is a `(m + 1)`-admissible list, and `a` is natural number such that a ≤ m and a < L[0],
then `a::L` is `m`-admissible -/
lemma cons (L : List ℕ) (hL : IsAdmissible (m + 1) L) (a : ℕ) (ha : a ≤ m)
    (ha' : (_ : 0 < L.length) → a < L[0]) : IsAdmissible m (a :: L) := by
  cases L with
  | nil => constructor <;> simp [ha]
  | cons head tail =>
    simp only [List.length_cons, lt_add_iff_pos_left, add_pos_iff,
      Nat.lt_one_iff, pos_of_gt, or_true, List.getElem_cons_zero,
      forall_const] at ha'
    simp only [IsAdmissible, List.sorted_cons, List.mem_cons, forall_eq_or_imp]
    constructor <;> repeat constructor
    · exact ha'
    · rw [← List.forall_getElem]
      intro i hi
      exact ha'.trans <| (List.sorted_cons.mp hL.sorted).left tail[i] <| List.getElem_mem hi
    · exact List.sorted_cons.mp hL.sorted
    · rintro ⟨_ | _⟩ hi
      · simp [ha]
      · haveI := hL.le _ <| Nat.lt_of_succ_lt_succ hi
        rw [List.getElem_cons_succ]
        cutsat

/-- The tail of an `m`-admissible list is (m+1)-admissible. -/
lemma tail (a : ℕ) (l : List ℕ) (h : IsAdmissible m (a::l)) :
    IsAdmissible (m + 1) l := by
  refine ⟨(List.sorted_cons.mp h.sorted).right, ?_⟩
  intro k _
  simpa [Nat.add_assoc, Nat.add_comm 1] using h.le (k + 1) (by simpa)

/-- An element of a `m`-admissible list, as an element of the appropriate `Fin` -/
@[simps]
def getElemAsFin {L : List ℕ} (hl : IsAdmissible m L) (k : ℕ)
    (hK : k < L.length) : Fin (m + k + 1) :=
  Fin.mk L[k] <| Nat.le_iff_lt_add_one.mp (by simp [hl.le])

/-- The head of an `m`-admissible list. -/
@[simps!]
def head (a : ℕ) (L : List ℕ) (hl : IsAdmissible m (a :: L)) : Fin (m + 1) :=
  hl.getElemAsFin 0 (by simp)

end IsAdmissible

/-- The construction `simplicialInsert` describes inserting an element in a list of integer and
moving it to its "right place" according to the simplicial relations. Somewhat miraculously,
the algorithm is the same for the first or the fifth simplicial relations, making it "valid"
when we treat the list as a normal form for a morphism satisfying `P_δ`, or for a morphism
satisfying `P_σ`!

This is similar in nature to `List.orderedInsert`, but note that we increment one of the element
every time we perform an exchange, making it a different construction. -/
def simplicialInsert (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | b :: l => if a < b then a :: b :: l else b :: simplicialInsert (a + 1) l

/-- `simplicialInsert` just adds one to the length. -/
lemma simplicialInsert_length (a : ℕ) (L : List ℕ) :
    (simplicialInsert a L).length = L.length + 1 := by
  induction L generalizing a with
  | nil => rfl
  | cons head tail h_rec =>
    dsimp only [simplicialInsert, List.length_cons]
    split_ifs with h <;> simp only [List.length_cons, h_rec (a + 1)]

/-- `simplicialInsert` preserves admissibility -/
theorem simplicialInsert_isAdmissible (L : List ℕ) (hL : IsAdmissible (m + 1) L) (j : ℕ)
    (hj : j < m + 1) :
    IsAdmissible m <| simplicialInsert j L := by
  induction L generalizing j m with
  | nil => constructor <;> simp [simplicialInsert, j.le_of_lt_add_one hj]
  | cons a L h_rec =>
    dsimp only [simplicialInsert]
    split_ifs with ha
    · exact .cons _ hL _ (j.le_of_lt_add_one hj) (fun _ ↦ ha)
    · refine IsAdmissible.cons _ ?_ _ (not_lt.mp ha |>.trans <| j.le_of_lt_add_one hj) ?_
      · refine h_rec _ (.tail a L hL) _ (by simp [hj])
      · rw [not_lt, Nat.le_iff_lt_add_one] at ha
        intro u
        cases L with
        | nil => simp [simplicialInsert, ha]
        | cons a' l' =>
          dsimp only [simplicialInsert]
          split_ifs
          · exact ha
          · exact (List.sorted_cons_cons.mp hL.sorted).1

end AdmissibleLists

end SimplexCategoryGenRel
