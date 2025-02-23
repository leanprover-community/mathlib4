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
  ∀ k: ℕ, (h : k < L.length) → L[k] ≤ m + k

namespace IsAdmissible

lemma nil : IsAdmissible m [] := by simp [IsAdmissible]

variable {m}

/-- If `(a :: l)` is `m`-admissible then a is less than all elements of `l` -/
lemma head_lt (a : ℕ) (L : List ℕ) (hl : IsAdmissible m (a :: L)) :
    ∀ a' ∈ L, a < a' := by
  obtain ⟨h₁, h₂⟩ := hl
  intro i hi
  exact (List.sorted_cons.mp h₁).left i hi

/-- If `L` is (m+1)-admissible index, and `a` is natural number such that a ≤ m and a < L[0], then
  `a::L` is `m`-admissible -/
lemma cons (L : List ℕ) (hL : IsAdmissible (m + 1) L) (a : ℕ) (ha : a ≤ m)
    (ha' : (_ : 0 < L.length) → a < L[0]) : IsAdmissible m (a :: L) := by
  dsimp [IsAdmissible] at hL ⊢
  cases L with
  | nil => constructor <;> simp [ha]
  | cons head tail =>
    simp only [List.length_cons, lt_add_iff_pos_left, add_pos_iff,
      Nat.lt_one_iff, pos_of_gt, or_true, List.getElem_cons_zero,
      forall_const] at ha'
    have ⟨P₁, P₂⟩ := hL
    simp only [List.sorted_cons, List.mem_cons, forall_eq_or_imp] at P₁ ⊢
    constructor <;> repeat constructor
    · exact ha'
    · have h_tail := P₁.left
      rw [← List.forall_getElem] at h_tail ⊢
      intro i hi
      exact ha'.trans <| h_tail i hi
    · exact P₁
    · rintro ⟨_ | _⟩ hi
      · simp [ha]
      · haveI := P₂ _ <| Nat.lt_of_succ_lt_succ hi
        rw [List.getElem_cons_succ]
        omega

/-- The tail of an `m`-admissible list is (m+1)-admissible. -/
lemma tail (a : ℕ) (l : List ℕ) (h : IsAdmissible m (a::l)) :
      IsAdmissible (m + 1) l := by
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨(List.sorted_cons.mp h₁).right, ?_⟩
  intro k hk
  haveI := h₂ (k + 1) (by simpa)
  simpa [Nat.add_assoc, Nat.add_comm 1] using this

/-- Since they are strictly sorted, two admissible lists with same elements are equal -/
lemma ext (L₁ : List ℕ) (L₂ : List ℕ)
    (hL₁ : IsAdmissible m L₁) (hL₂ : IsAdmissible m L₂)
    (h : ∀ x : ℕ, x ∈ L₁ ↔ x ∈ L₂) : L₁ = L₂ := by
  obtain ⟨hL₁, -⟩ := hL₁
  obtain ⟨hL₂, -⟩ := hL₂
  induction L₁ generalizing L₂ with
  | nil =>
    simp only [List.nil_eq, List.eq_nil_iff_forall_not_mem]
    intro a ha
    exact List.not_mem_nil _ ((h a).mpr ha)
  | cons a L₁ h_rec =>
    cases L₂ with
    | nil =>
      simp only [List.nil_eq, List.eq_nil_iff_forall_not_mem]
      intro a ha
      exact List.not_mem_nil _ ((h a).mp ha)
    | cons b L₂ =>
      rw [List.cons_eq_cons]
      simp only [List.mem_cons] at h
      simp only [List.sorted_cons] at hL₁ hL₂
      obtain ⟨haL₁, hL₁⟩ := hL₁
      obtain ⟨hbL₂, hL₂⟩ := hL₂
      obtain rfl : a = b := by
        haveI := h b
        simp only [true_or, iff_true] at this
        obtain rfl | bL₁ := this
        · rfl
        · have ha := h a
          simp only [true_or, true_iff] at ha
          obtain rfl | aL₂ := ha
          · rfl
          · have f₁ := haL₁ _ bL₁
            have f₂ := hbL₂ _ aL₂
            linarith
      refine ⟨rfl, ?_⟩
      apply h_rec L₂ _ hL₁ hL₂
      intro x
      by_cases hax : x = a
      · subst hax
        constructor
        · intro h₁
          haveI := haL₁ x h₁
          linarith
        · intro h₁
          haveI := hbL₂ x h₁
          linarith
      simpa [hax] using h x

/-- An element of a `m`-admissible list, as an element of the appropriate `Fin` -/
@[simps]
def getElemAsFin {L : List ℕ} (hl : IsAdmissible m L) (k : ℕ)
    (hK : k < L.length) : Fin (m + k + 1) :=
  Fin.mk L[k] <| Nat.le_iff_lt_add_one.mp (by simp [hl.right])

/-- The head of an `m`-admissible list is a special case of this.  -/
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

/-- `simplicialInsert ` just adds one to the length. -/
lemma simplicialInsert_length (a : ℕ) (L : List ℕ) :
    (simplicialInsert a L).length = L.length + 1 := by
  induction L generalizing a with
  | nil => rfl
  | cons head tail h_rec =>
    dsimp only [simplicialInsert, List.length_cons]
    split_ifs with h <;> simp only [List.length_cons, add_left_inj, h_rec (a + 1)]

/-- `simplicialInsert` preserves admissibility -/
theorem simplicialInsert_isAdmissible (L : List ℕ) (hL : IsAdmissible (m + 1) L) (j : ℕ)
    (hj : j < m + 1) :
    IsAdmissible m (simplicialInsert j L) := by
  have ⟨h₁, h₂⟩ := hL
  induction L generalizing j m with
  | nil => constructor <;> simp [simplicialInsert, j.le_of_lt_add_one hj]
  | cons a L h_rec =>
    dsimp only [simplicialInsert]
    split_ifs with ha
    · exact .cons _ hL _ (j.le_of_lt_add_one hj) (fun _ ↦ ha)
    · refine IsAdmissible.cons _ ?_ _ (not_lt.mp ha |>.trans <| j.le_of_lt_add_one hj) ?_
      · refine h_rec _ (.tail a L hL) _ (by simp [hj]) (List.sorted_cons.mp h₁).right ?_
        intro k hk
        haveI := h₂ (k + 1) (by simpa)
        conv_rhs at this => rw [k.add_comm 1, ← Nat.add_assoc]
        exact this
      · rw [not_lt, Nat.le_iff_lt_add_one] at ha
        intro u
        cases L with
        | nil => simp [simplicialInsert, ha]
        | cons a' l' =>
          dsimp only [simplicialInsert]
          split_ifs
          · exact ha
          · simp only [List.sorted_cons, List.mem_cons, forall_eq_or_imp] at h₁
            simpa using h₁.left.left

end AdmissibleLists

end SimplexCategoryGenRel
