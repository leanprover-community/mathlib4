/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.Tactic.Zify
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Linarith.Lemmas
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

namespace AlgebraicTopology.SimplexCategory.SimplexCategoryGenRel

open CategoryTheory

section AdmissibleLists
-- Impl. note: We are not bundling admissible lists as a subtype of `List ℕ` so that it remains
-- easier to perform inductive constructions and proofs on such lists, and we instead bundle
-- propositions asserting that various List constructions produce admissible lists.

variable (m : ℕ)
/-- A list of natural numbers [i₀, ⋯, iₙ]) is said to be `m`-admissible (for `m : ℕ`) if
`i₀ < ⋯ < iₙ` and `iₖ ≤ m + k` for all `k`.
-/
def isAdmissible (L : List ℕ) : Prop :=
  List.Sorted (· < ·) L ∧
  ∀ k: ℕ, (h : k < L.length) → L[k] ≤ m + k

lemma isAdmissible_nil : isAdmissible m [] := by simp [isAdmissible]

variable {m}
/-- If `(a :: l)` is `m`-admissible then a is less than all elements of `l` -/
lemma isAdmissible_head_lt (a : ℕ) (L : List ℕ) (hl : isAdmissible m (a :: L)) :
    ∀ a' ∈ L, a < a' := by
  obtain ⟨h₁, h₂⟩ := hl
  intro i hi
  exact (List.sorted_cons.mp h₁).left i hi

/-- If `L` is (m+1)-admissible index, and `a` is natural number such that a ≤ m and a < L[0], then
  `a::L` is `m`-admissible -/
lemma isAdmissible_cons (L : List ℕ) (hL : isAdmissible (m + 1) L) (a : ℕ) (ha : a ≤ m)
    (ha' : (_ : 0 < L.length) → a < L[0]) : isAdmissible m (a :: L) := by
  dsimp [isAdmissible] at hL ⊢
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
    · intro i hi
      cases i with
      | zero => simp [ha]
      | succ i =>
          simp only [List.getElem_cons_succ]
          haveI := P₂ i <| Nat.lt_of_succ_lt_succ hi
          rwa [← add_comm 1, ← add_assoc]

/-- The tail of an `m`-admissible list is (m+1)-admissible. -/
lemma isAdmissible_tail (a : ℕ) (l : List ℕ) (h : isAdmissible m (a::l)) :
      isAdmissible (m + 1) l := by
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨(List.sorted_cons.mp h₁).right, ?_⟩
  intro k hk
  haveI := h₂ (k + 1) (by simpa)
  simpa [Nat.add_assoc, Nat.add_comm 1] using this

/-- Since they are strictly sorted, two admissible lists with same elements are equal -/
lemma isAdmissible_ext (L₁ : List ℕ) (L₂ : List ℕ)
    (hL₁ : isAdmissible m L₁) (hL₂ : isAdmissible m L₂)
    (h : ∀ x : ℕ, x ∈ L₁ ↔ x ∈ L₂) : L₁ = L₂ := by
  obtain ⟨hL₁, hL₁₂⟩ := hL₁
  obtain ⟨hL₂, hL₂₂⟩ := hL₂
  clear hL₁₂ hL₂₂
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
      have hab : a = b := by
        haveI := h b
        simp only [true_or, iff_true] at this
        obtain hb | bL₁ := this
        · exact hb.symm
        · have ha := h a
          simp only [true_or, true_iff] at ha
          obtain hab | aL₂ := ha
          · exact hab
          · have f₁ := haL₁ _ bL₁
            have f₂ := hbL₂ _ aL₂
            linarith
      refine ⟨hab, ?_⟩
      apply h_rec L₂ _ hL₁ hL₂
      intro x
      subst hab
      haveI := h x
      by_cases hax : x = a
      · subst hax
        constructor
        · intro h₁
          haveI := haL₁ x h₁
          linarith
        · intro h₁
          haveI := hbL₂ x h₁
          linarith
      simpa [hax] using this

/-- An element of a `m`-admissible list, as an element of the appropriate `Fin` -/
@[simps]
def isAdmissibleGetElemAsFin (L : List ℕ) (hl : isAdmissible m L) (k : ℕ)
    (hK : k < L.length) : Fin (m + k + 1) :=
  Fin.mk L[k] <| Nat.le_iff_lt_add_one.mp (by simp [hl.right])

/-- The head of an `m`-admissible list is a special case of this.  -/
@[simps!]
def isAdmissibleHead (a : ℕ) (L : List ℕ) (hl : isAdmissible m (a :: L)) : Fin (m + 1) :=
  isAdmissibleGetElemAsFin (a :: L) hl 0 (by simp)

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
    simp only [simplicialInsert, List.length_cons]
    split_ifs with h <;> simp only [List.length_cons, add_left_inj]
    exact h_rec (a + 1)

/-- `simplicialInsert` preserves admissibility -/
theorem simplicialInsert_isAdmissible (L : List ℕ) (hL : isAdmissible (m + 1) L) (j : ℕ)
    (hj : j < m + 1) :
    isAdmissible m (simplicialInsert j L) := by
  have ⟨h₁, h₂⟩ := hL
  induction L generalizing j m with
  | nil =>
    simp only [simplicialInsert]
    constructor
    · simp
    · simp [j.le_of_lt_add_one hj]
  | cons a L h_rec =>
    simp only [simplicialInsert]
    split_ifs <;> rename_i ha
    · exact isAdmissible_cons _ hL _ (j.le_of_lt_add_one hj) (fun _ ↦ ha)
    · apply isAdmissible_cons
      · apply h_rec
        · exact isAdmissible_tail a L hL
        · simp [hj]
        · exact (List.sorted_cons.mp h₁).right
        · intro k hk
          haveI := h₂ (k + 1) (by simpa)
          conv_rhs at this => rw [k.add_comm 1, ← Nat.add_assoc]
          exact this
      · rw [not_lt] at ha
        apply ha.trans
        exact j.le_of_lt_add_one hj
      · rw [not_lt, Nat.le_iff_lt_add_one] at ha
        intro u
        cases L with
        | nil => simp [simplicialInsert, ha]
        | cons a' l' =>
          simp only [simplicialInsert]
          split_ifs <;> rename_i h'
          · exact ha
          · simp only [List.sorted_cons, List.mem_cons, forall_eq_or_imp] at h₁
            simpa using h₁.left.left

end AdmissibleLists

end AlgebraicTopology.SimplexCategory.SimplexCategoryGenRel
