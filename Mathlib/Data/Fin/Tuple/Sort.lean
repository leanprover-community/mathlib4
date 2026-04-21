/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Prod.Lex
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Data.Fintype.Fin

/-!

# Sorting tuples by their values

Given an `n`-tuple `f : Fin n → α` where `α` is ordered,
we may want to turn it into a sorted `n`-tuple.
This file provides an API for doing so, with the sorted `n`-tuple given by
`f ∘ Tuple.sort f`.

## Main declarations

* `Tuple.sort`: given `f : Fin n → α`, produces a permutation on `Fin n`
* `Tuple.monotone_sort`: `f ∘ Tuple.sort f` is `Monotone`

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


namespace Tuple

variable {n : ℕ}
variable {α : Type*} [LinearOrder α]

/-- `graph f` produces the finset of pairs `(f i, i)`
equipped with the lexicographic order.
-/
def graph (f : Fin n → α) : Finset (α ×ₗ Fin n) :=
  Finset.univ.image fun i => (f i, i)

/-- Given `p : α ×ₗ (Fin n) := (f i, i)` with `p ∈ graph f`,
`graph.proj p` is defined to be `f i`.
-/
def graph.proj {f : Fin n → α} : graph f → α := fun p => p.1.1

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem graph.card (f : Fin n → α) : (graph f).card = n := by
  rw [graph, Finset.card_image_of_injective]
  · exact Finset.card_fin _
  · intro _ _
    -- Porting note: proof was `simp`
    rw [Prod.ext_iff]
    simp

/-- `graphEquiv₁ f` is the natural equivalence between `Fin n` and `graph f`,
mapping `i` to `(f i, i)`. -/
def graphEquiv₁ (f : Fin n → α) : Fin n ≃ graph f where
  toFun i := ⟨(f i, i), by simp [graph]⟩
  invFun p := p.1.2
  left_inv i := by simp
  right_inv := fun ⟨⟨x, i⟩, h⟩ => by
    -- Porting note: was `simpa [graph] using h`
    simp only [graph, Finset.mem_image, Finset.mem_univ, true_and] at h
    obtain ⟨i', hi'⟩ := h
    obtain ⟨-, rfl⟩ := Prod.mk_inj.mp hi'
    simpa

@[simp]
theorem proj_equiv₁' (f : Fin n → α) : graph.proj ∘ graphEquiv₁ f = f :=
  rfl

/-- `graphEquiv₂ f` is an equivalence between `Fin n` and `graph f` that respects the order.
-/
def graphEquiv₂ (f : Fin n → α) : Fin n ≃o graph f :=
  Finset.orderIsoOfFin _ (by simp)

/-- `sort f` is the permutation that orders `Fin n` according to the order of the outputs of `f`. -/
def sort (f : Fin n → α) : Equiv.Perm (Fin n) :=
  (graphEquiv₂ f).toEquiv.trans (graphEquiv₁ f).symm

theorem graphEquiv₂_apply (f : Fin n → α) (i : Fin n) :
    graphEquiv₂ f i = graphEquiv₁ f (sort f i) :=
  ((graphEquiv₁ f).apply_symm_apply _).symm

theorem self_comp_sort (f : Fin n → α) : f ∘ sort f = graph.proj ∘ graphEquiv₂ f :=
  show graph.proj ∘ (graphEquiv₁ f ∘ (graphEquiv₁ f).symm) ∘ (graphEquiv₂ f).toEquiv = _ by simp

theorem monotone_proj (f : Fin n → α) : Monotone (graph.proj : graph f → α) := by
  rintro ⟨⟨x, i⟩, hx⟩ ⟨⟨y, j⟩, hy⟩ (_ | h)
  · exact le_of_lt ‹_›
  · simp [graph.proj]

theorem monotone_sort (f : Fin n → α) : Monotone (f ∘ sort f) := by
  rw [self_comp_sort]
  exact (monotone_proj f).comp (graphEquiv₂ f).monotone

end Tuple

namespace Tuple

open List

variable {n : ℕ} {α : Type*}

section

open Finset

variable {j : Fin n} {f : Fin n → α} [Preorder α] {a : α}

/-- If `f₀ ≤ f₁ ≤ f₂ ≤ ⋯` is a sorted `n`-tuple of elements of `α`, then for any `j : Fin n` and
`a : α` we have `j < #{i | fᵢ ≤ a}` iff `fⱼ ≤ a`. -/
theorem lt_card_le_iff_apply_le_of_monotone [DecidableLE α] (h_sorted : Monotone f) :
    j < #{i | f i ≤ a} ↔ f j ≤ a :=
  Fin.lt_card_filter_univ_iff_apply_of_imp (f · ≤ a) (by grind [Monotone])

theorem lt_card_ge_iff_apply_ge_of_antitone [DecidableLE α] (h_sorted : Antitone f) :
    j < #{i | a ≤ f i} ↔ a ≤ f j :=
  Fin.lt_card_filter_univ_iff_apply_of_imp (a ≤ f ·) (by grind [Antitone])

theorem lt_card_lt_iff_apply_lt_of_monotone [DecidableLT α] (h_sorted : Monotone f) :
    j < #{i | f i < a} ↔ f j < a :=
  Fin.lt_card_filter_univ_iff_apply_of_imp (f · < a) (by grind [Monotone])

theorem lt_card_gt_iff_apply_gt_of_antitone [DecidableLT α] (h_sorted : Antitone f) :
    j < #{i | a < f i} ↔ a < f j :=
  Fin.lt_card_filter_univ_iff_apply_of_imp (a < f ·) (by grind [Antitone])

end

/-- If two permutations of a tuple `f` are both monotone, then they are equal. -/
theorem unique_monotone [PartialOrder α] {f : Fin n → α} {σ τ : Equiv.Perm (Fin n)}
    (hfσ : Monotone (f ∘ σ)) (hfτ : Monotone (f ∘ τ)) : f ∘ σ = f ∘ τ :=
  ofFn_injective <|
    ((σ.ofFn_comp_perm f).trans (τ.ofFn_comp_perm f).symm).eq_of_pairwise'
      hfσ.sortedLE_ofFn.pairwise hfτ.sortedLE_ofFn.pairwise

/-- If two permutations of a tuple `f` are both antitone, then they are equal. -/
theorem unique_antitone [PartialOrder α] {f : Fin n → α} {σ τ : Equiv.Perm (Fin n)}
    (hfσ : Antitone (f ∘ σ)) (hfτ : Antitone (f ∘ τ)) : f ∘ σ = f ∘ τ :=
  ofFn_injective <|
    ((σ.ofFn_comp_perm f).trans (τ.ofFn_comp_perm f).symm).eq_of_pairwise'
      hfσ.sortedGE_ofFn.pairwise hfτ.sortedGE_ofFn.pairwise

variable [LinearOrder α] {f : Fin n → α} {σ : Equiv.Perm (Fin n)}

/-- A permutation `σ` equals `sort f` if and only if the map `i ↦ (f (σ i), σ i)` is
strictly monotone (w.r.t. the lexicographic ordering on the target). -/
theorem eq_sort_iff' : σ = sort f ↔ StrictMono (σ.trans <| graphEquiv₁ f) := by
  constructor <;> intro h
  · rw [h, sort, Equiv.trans_assoc, Equiv.symm_trans_self]
    exact (graphEquiv₂ f).strictMono
  · have := Subsingleton.elim (graphEquiv₂ f) (h.orderIsoOfSurjective _ <| Equiv.surjective _)
    ext1 x
    exact (graphEquiv₁ f).apply_eq_iff_eq_symm_apply.1 (DFunLike.congr_fun this x).symm

/-- A permutation `σ` equals `sort f` if and only if `f ∘ σ` is monotone and whenever `i < j`
and `f (σ i) = f (σ j)`, then `σ i < σ j`. This means that `sort f` is the lexicographically
smallest permutation `σ` such that `f ∘ σ` is monotone. -/
theorem eq_sort_iff :
    σ = sort f ↔ Monotone (f ∘ σ) ∧ ∀ i j, i < j → f (σ i) = f (σ j) → σ i < σ j := by
  rw [eq_sort_iff']
  refine ⟨fun h => ⟨(monotone_proj f).comp h.monotone, fun i j hij hfij => ?_⟩, fun h i j hij => ?_⟩
  · exact ((Prod.Lex.toLex_lt_toLex.1 <| h hij).resolve_left hfij.not_lt).2
  · obtain he | hl := (h.1 hij.le).eq_or_lt <;> apply Prod.Lex.toLex_lt_toLex.2
    exacts [Or.inr ⟨he, h.2 i j hij he⟩, Or.inl hl]

/-- The permutation that sorts `f` is the identity if and only if `f` is monotone. -/
theorem sort_eq_refl_iff_monotone : sort f = Equiv.refl _ ↔ Monotone f := by
  rw [eq_comm, eq_sort_iff, Equiv.coe_refl, Function.comp_id]
  simp only [id, and_iff_left_iff_imp]
  exact fun _ _ _ hij _ => hij

/-- A permutation of a tuple `f` is `f` sorted if and only if it is monotone. -/
theorem comp_sort_eq_comp_iff_monotone : f ∘ σ = f ∘ sort f ↔ Monotone (f ∘ σ) :=
  ⟨fun h => h.symm ▸ monotone_sort f, fun h => unique_monotone h (monotone_sort f)⟩

/-- The sorted versions of a tuple `f` and of any permutation of `f` agree. -/
theorem comp_perm_comp_sort_eq_comp_sort : (f ∘ σ) ∘ sort (f ∘ σ) = f ∘ sort f := by
  rw [Function.comp_assoc, ← Equiv.Perm.coe_mul]
  exact unique_monotone (monotone_sort (f ∘ σ)) (monotone_sort f)

/-- If a permutation `f ∘ σ` of the tuple `f` is not the same as `f ∘ sort f`, then `f ∘ σ`
has a pair of strictly decreasing entries. -/
theorem antitone_pair_of_not_sorted' (h : f ∘ σ ≠ f ∘ sort f) :
    ∃ i j, i < j ∧ (f ∘ σ) j < (f ∘ σ) i := by
  contrapose! h
  exact comp_sort_eq_comp_iff_monotone.mpr (monotone_iff_forall_lt.mpr h)

/-- If the tuple `f` is not the same as `f ∘ sort f`, then `f` has a pair of strictly decreasing
entries. -/
theorem antitone_pair_of_not_sorted (h : f ≠ f ∘ sort f) : ∃ i j, i < j ∧ f j < f i :=
  antitone_pair_of_not_sorted' (id h : f ∘ Equiv.refl _ ≠ _)

/-- The sorted version of a permutation `σ` is its inverse `σ⁻¹`. -/
@[simp]
theorem sort_perm (σ : Equiv.Perm (Fin n)) :
    sort σ = σ⁻¹ := by
  apply (eq_sort_iff.2 ⟨?_ , ?_⟩).symm
  · simpa using monotone_id
  · intro _ _ hij h
    exact (hij.ne (by simpa using h)).elim

end Tuple

theorem Equiv.Perm.monotone_iff {n : ℕ} (σ : Perm (Fin n)) :
    Monotone σ ↔ σ = 1 := by
  rw [← Tuple.sort_eq_refl_iff_monotone, Tuple.sort_perm, ← inv_eq_one, one_def]
