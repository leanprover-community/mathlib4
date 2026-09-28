/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Prod.Lex
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Fintype.Fin

/-!

# Sorting tuples by their values

Given an `n`-tuple `f : Fin n → α` where `α` is ordered,
we may want to turn it into a sorted `n`-tuple.
This file provides an API for doing so, with the sorted `n`-tuple given by
`f ∘ Tuple.sort f`.

## Main declarations

* `Tuple.sort`: given `f : Fin n → α`, produces a permutation on `Fin n`
* `Tuple.monotone_sort`: `f ∘ Tuple.sort f` is `Monotone`
* `Tuple.sortDesc`: given `f : Fin n → α`, produces a permutation on `Fin n` sorting into decreasing
  order
* `Tuple.antitone_sortDesc`: `f ∘ Tuple.sortDesc f` is `Antitone`
* `Tuple.comp_sort_comp_rev_eq_comp_sortDesc`: sorting descending equals sorting ascending, reversed

-/

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

set_option backward.isDefEq.respectTransparency false in
/-- `graphEquiv₁ f` is the natural equivalence between `Fin n` and `graph f`,
mapping `i` to `(f i, i)`. -/
def graphEquiv₁ (f : Fin n → α) : Fin n ≃ graph f where
  toFun i := ⟨(f i, i), by simp [graph]⟩
  invFun p := p.1.2
  left_inv i := by simp
  right_inv := fun ⟨⟨x, i⟩, h⟩ => by
    simpa [graph, eq_comm, eqComm] using h

@[simp]
theorem proj_equiv₁' (f : Fin n → α) : graph.proj ∘ graphEquiv₁ f = f :=
  rfl

/-- `graphEquiv₂ f` is an equivalence between `Fin n` and `graph f` that respects the order.
-/
def graphEquiv₂ (f : Fin n → α) : Fin n ≃o graph f :=
  Finset.orderIsoOfFin _ (by simp)

/-- `σ` is *stable* for `f` if it breaks ties by increasing index: any two indices sharing the
same `f`-value keep their original order. This property is independent of the sort direction. -/
def IsStable (f : Fin n → α) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j, i < j → f (σ i) = f (σ j) → σ i < σ j

/-- `σ` is a *stable sort* of `f` if `f ∘ σ` is monotone and `σ` is stable (`IsStable`). This is
the property characterising `sort f` among all permutations, see `eq_sort_iff`. -/
def StableSort (f : Fin n → α) (σ : Equiv.Perm (Fin n)) :=
  Monotone (f ∘ σ) ∧ IsStable f σ

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

/-- `sortDesc f` is the permutation that orders `Fin n` according to the reverse order of the
outputs of `f`, so that `f ∘ sortDesc f` is decreasing.

Unlike `sort f ∘ Fin.revPerm`, which also arranges `f` in decreasing order, `sortDesc f` is a
*stable* sort: among indices with equal `f`-value it keeps their original order
(`isStable_sortDesc`), whereas `sort f ∘ Fin.revPerm` reverses it and so is stable only when `f`
is injective (`isStable_sort_mul_revPerm_iff`), in which case the two coincide
(`sort_comp_rev_eq_sortDesc_of_injective`). -/
def sortDesc (f : Fin n → α) : Equiv.Perm (Fin n) :=
  sort (OrderDual.toDual ∘ f)

theorem antitone_sortDesc (f : Fin n → α) : Antitone (f ∘ sortDesc f) := by
  have hmono : Monotone ((OrderDual.toDual ∘ f) ∘ sort (OrderDual.toDual ∘ f)) := monotone_sort _
  rw [Function.comp_assoc] at hmono
  exact monotone_toDual_comp_iff.mp hmono

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
    exact (graphEquiv₁ f).eq_symm_apply.2 congr($this x).symm

/-- A permutation `σ` equals `sort f` if and only if `f ∘ σ` is monotone and whenever `i < j`
and `f (σ i) = f (σ j)`, then `σ i < σ j`. This means that `sort f` is the lexicographically
smallest permutation `σ` such that `f ∘ σ` is monotone. -/
theorem eq_sort_iff : σ = sort f ↔ StableSort f σ := by
  rw [eq_sort_iff']
  refine ⟨fun h => ⟨(monotone_proj f).comp h.monotone, fun i j hij hfij => ?_⟩, fun h i j hij => ?_⟩
  · exact ((Prod.Lex.toLex_lt_toLex.1 <| h hij).resolve_left hfij.not_lt).2
  · obtain he | hl := (h.1 hij.le).eq_or_lt <;> apply Prod.Lex.toLex_lt_toLex.2
    exacts [Or.inr ⟨he, h.2 i j hij he⟩, Or.inl hl]

/-- The permutation that sorts `f` is the identity if and only if `f` is monotone. -/
theorem sort_eq_refl_iff_monotone : sort f = Equiv.refl _ ↔ Monotone f := by
  rw [eq_comm, eq_sort_iff, StableSort, Equiv.coe_refl, Function.comp_id]
  simp only [and_iff_left_iff_imp]
  exact fun _ _ _ hij _ => hij

/-- A permutation of a tuple `f` is `f` sorted if and only if it is monotone. -/
theorem comp_sort_eq_comp_iff_monotone : f ∘ σ = f ∘ sort f ↔ Monotone (f ∘ σ) :=
  ⟨fun h => h.symm ▸ monotone_sort f, fun h => unique_monotone h (monotone_sort f)⟩

/-- The sorted versions of a tuple `f` and of any permutation of `f` agree. -/
theorem comp_perm_comp_sort_eq_comp_sort : (f ∘ σ) ∘ sort (f ∘ σ) = f ∘ sort f := by
  rw [Function.comp_assoc, ← Equiv.Perm.coe_mul]
  exact unique_monotone (monotone_sort (f ∘ σ)) (monotone_sort f)

/-- The sorted-descending versions of a tuple `f` and of any permutation of `f` agree. -/
theorem comp_perm_comp_sortDesc_eq_comp_sortDesc :
    (f ∘ σ) ∘ sortDesc (f ∘ σ) = f ∘ sortDesc f := by
  rw [Function.comp_assoc, ← Equiv.Perm.coe_mul]
  exact unique_antitone (antitone_sortDesc (f ∘ σ)) (antitone_sortDesc f)

/-- Sorting `f` in descending order is the same as sorting it in ascending order, then reversing. -/
theorem comp_sort_comp_rev_eq_comp_sortDesc : f ∘ sort f ∘ Fin.rev = f ∘ sortDesc f := by
  rw [show ⇑(sort f) ∘ Fin.rev = ⇑(sort f * Fin.revPerm : Equiv.Perm (Fin n)) from rfl]
  exact unique_antitone ((monotone_sort f).comp_antitone Fin.rev_anti) (antitone_sortDesc f)

/-- Sorting `f` in ascending order is the same as sorting it in descending order, then reversing. -/
theorem comp_sortDesc_comp_rev_eq_comp_sort : f ∘ sortDesc f ∘ Fin.rev = f ∘ sort f := by
  rw [show ⇑(sortDesc f) ∘ Fin.rev = ⇑(sortDesc f * Fin.revPerm : Equiv.Perm (Fin n)) from rfl]
  exact unique_monotone ((antitone_sortDesc f).comp Fin.rev_anti) (monotone_sort f)

/-- When `f` is injective there are no ties, so sorting descending agrees with sorting ascending
then reversing, already as an equality of permutations. -/
theorem sort_comp_rev_eq_sortDesc_of_injective (inj : Function.Injective f) :
    sort f ∘ Fin.rev = sortDesc f :=
  inj.comp_left comp_sort_comp_rev_eq_comp_sortDesc

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

theorem stableSort_sort (f : Fin n → α) : StableSort f (sort f) :=
  eq_sort_iff.mp rfl

theorem isStable_sort (f : Fin n → α) : IsStable f (sort f) :=
  (stableSort_sort f).2

theorem stableSort_sortDesc (f : Fin n → α) : StableSort (OrderDual.toDual ∘ f) (sortDesc f) :=
  stableSort_sort (OrderDual.toDual ∘ f)

theorem isStable_sortDesc (f : Fin n → α) : IsStable f (sortDesc f) :=
  (stableSort_sortDesc f).2

/-- `sort f ∘ Fin.revPerm` is a stable sort exactly when `f` is injective: on tied values it orders
them by *decreasing* index, the opposite of the stable `sortDesc f`. -/
theorem isStable_sort_mul_revPerm_iff :
    IsStable f (sort f * Fin.revPerm) ↔ Function.Injective f := by
  refine ⟨fun hσ => ?_, fun inj => ?_⟩
  · -- `sort f` and its reversal order any tied `x, y` oppositely, so `f` can have no tie.
    have key : ∀ x y, f x = f y → (sort f).symm x < (sort f).symm y → False := by
      intro x y hxy hlt
      have h1 : x < y := by simpa using isStable_sort f _ _ hlt (by simp [hxy])
      have h2 : y < x := by
        simpa [Equiv.Perm.mul_apply] using hσ (Fin.rev ((sort f).symm y))
          (Fin.rev ((sort f).symm x)) (Fin.rev_strictAnti hlt) (by simp [Equiv.Perm.mul_apply, hxy])
      exact absurd h1 (asymm h2)
    intro a b hfab
    by_contra hab
    rcases lt_or_gt_of_ne (fun h => hab ((sort f).symm.injective h)) with hlt | hlt
    · exact key a b hfab hlt
    · exact key b a hfab.symm hlt
  · have h : sort f * Fin.revPerm = sortDesc f :=
      DFunLike.coe_injective (by
        rw [Equiv.Perm.coe_mul]
        exact sort_comp_rev_eq_sortDesc_of_injective inj)
    rw [h]
    exact isStable_sortDesc f

end Tuple

theorem Equiv.Perm.monotone_iff {n : ℕ} (σ : Perm (Fin n)) :
    Monotone σ ↔ σ = 1 := by
  rw [← Tuple.sort_eq_refl_iff_monotone, Tuple.sort_perm, ← inv_eq_one, one_def]
