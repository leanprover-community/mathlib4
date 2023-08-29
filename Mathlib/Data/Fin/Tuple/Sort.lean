/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Data.Prod.Lex
import Mathlib.GroupTheory.Perm.Basic

#align_import data.fin.tuple.sort from "leanprover-community/mathlib"@"8631e2d5ea77f6c13054d9151d82b83069680cb1"

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


namespace Tuple

variable {n : ℕ}

variable {α : Type*} [LinearOrder α]

/-- `graph f` produces the finset of pairs `(f i, i)`
equipped with the lexicographic order.
-/
def graph (f : Fin n → α) : Finset (α ×ₗ Fin n) :=
  Finset.univ.image fun i => (f i, i)
#align tuple.graph Tuple.graph

/-- Given `p : α ×ₗ (Fin n) := (f i, i)` with `p ∈ graph f`,
`graph.proj p` is defined to be `f i`.
-/
def graph.proj {f : Fin n → α} : graph f → α := fun p => p.1.1
#align tuple.graph.proj Tuple.graph.proj

@[simp]
theorem graph.card (f : Fin n → α) : (graph f).card = n := by
  rw [graph, Finset.card_image_of_injective]
  -- ⊢ Finset.card Finset.univ = n
  · exact Finset.card_fin _
    -- 🎉 no goals
  · intro _ _
    -- ⊢ (fun i => (f i, i)) a₁✝ = (fun i => (f i, i)) a₂✝ → a₁✝ = a₂✝
    -- Porting note: was `simp`
    dsimp only
    -- ⊢ (f a₁✝, a₁✝) = (f a₂✝, a₂✝) → a₁✝ = a₂✝
    rw [Prod.ext_iff]
    -- ⊢ (f a₁✝, a₁✝).fst = (f a₂✝, a₂✝).fst ∧ (f a₁✝, a₁✝).snd = (f a₂✝, a₂✝).snd →  …
    simp
    -- 🎉 no goals
#align tuple.graph.card Tuple.graph.card

/-- `graphEquiv₁ f` is the natural equivalence between `Fin n` and `graph f`,
mapping `i` to `(f i, i)`. -/
def graphEquiv₁ (f : Fin n → α) : Fin n ≃ graph f where
  toFun i := ⟨(f i, i), by simp [graph]⟩
                           -- 🎉 no goals
  invFun p := p.1.2
  left_inv i := by simp
                   -- 🎉 no goals
  right_inv := fun ⟨⟨x, i⟩, h⟩ => by
    -- Porting note: was `simpa [graph] using h`
    simp only [graph, Finset.mem_image, Finset.mem_univ, true_and] at h
    -- ⊢ (fun i => { val := (f i, i), property := (_ : (f i, i) ∈ Finset.image (fun i …
    obtain ⟨i', hi'⟩ := h
    -- ⊢ (fun i => { val := (f i, i), property := (_ : (f i, i) ∈ Finset.image (fun i …
    obtain ⟨-, rfl⟩ := Prod.mk.inj_iff.mp hi'
    -- ⊢ (fun i => { val := (f i, i), property := (_ : (f i, i) ∈ Finset.image (fun i …
    simpa
    -- 🎉 no goals
#align tuple.graph_equiv₁ Tuple.graphEquiv₁

@[simp]
theorem proj_equiv₁' (f : Fin n → α) : graph.proj ∘ graphEquiv₁ f = f :=
  rfl
#align tuple.proj_equiv₁' Tuple.proj_equiv₁'

/-- `graphEquiv₂ f` is an equivalence between `Fin n` and `graph f` that respects the order.
-/
def graphEquiv₂ (f : Fin n → α) : Fin n ≃o graph f :=
  Finset.orderIsoOfFin _ (by simp)
                             -- 🎉 no goals
#align tuple.graph_equiv₂ Tuple.graphEquiv₂

/-- `sort f` is the permutation that orders `Fin n` according to the order of the outputs of `f`. -/
def sort (f : Fin n → α) : Equiv.Perm (Fin n) :=
  (graphEquiv₂ f).toEquiv.trans (graphEquiv₁ f).symm
#align tuple.sort Tuple.sort

theorem graphEquiv₂_apply (f : Fin n → α) (i : Fin n) :
    graphEquiv₂ f i = graphEquiv₁ f (sort f i) :=
  ((graphEquiv₁ f).apply_symm_apply _).symm
#align tuple.graph_equiv₂_apply Tuple.graphEquiv₂_apply

theorem self_comp_sort (f : Fin n → α) : f ∘ sort f = graph.proj ∘ graphEquiv₂ f :=
  show graph.proj ∘ (graphEquiv₁ f ∘ (graphEquiv₁ f).symm) ∘ (graphEquiv₂ f).toEquiv = _ by simp
                                                                                            -- 🎉 no goals
#align tuple.self_comp_sort Tuple.self_comp_sort

theorem monotone_proj (f : Fin n → α) : Monotone (graph.proj : graph f → α) := by
  rintro ⟨⟨x, i⟩, hx⟩ ⟨⟨y, j⟩, hy⟩ (_ | h)
  -- ⊢ graph.proj { val := (x, i), property := hx } ≤ graph.proj { val := (y, j), p …
  · exact le_of_lt ‹_›
    -- 🎉 no goals
  · simp [graph.proj]
    -- 🎉 no goals
#align tuple.monotone_proj Tuple.monotone_proj

theorem monotone_sort (f : Fin n → α) : Monotone (f ∘ sort f) := by
  rw [self_comp_sort]
  -- ⊢ Monotone (graph.proj ∘ ↑(graphEquiv₂ f))
  exact (monotone_proj f).comp (graphEquiv₂ f).monotone
  -- 🎉 no goals
#align tuple.monotone_sort Tuple.monotone_sort

end Tuple

namespace Tuple

open List

variable {n : ℕ} {α : Type*}

/-- If two permutations of a tuple `f` are both monotone, then they are equal. -/
theorem unique_monotone [PartialOrder α] {f : Fin n → α} {σ τ : Equiv.Perm (Fin n)}
    (hfσ : Monotone (f ∘ σ)) (hfτ : Monotone (f ∘ τ)) : f ∘ σ = f ∘ τ :=
  ofFn_injective <|
    eq_of_perm_of_sorted ((σ.ofFn_comp_perm f).trans (τ.ofFn_comp_perm f).symm)
      hfσ.ofFn_sorted hfτ.ofFn_sorted
#align tuple.unique_monotone Tuple.unique_monotone

variable [LinearOrder α] {f : Fin n → α} {σ : Equiv.Perm (Fin n)}

/-- A permutation `σ` equals `sort f` if and only if the map `i ↦ (f (σ i), σ i)` is
strictly monotone (w.r.t. the lexicographic ordering on the target). -/
theorem eq_sort_iff' : σ = sort f ↔ StrictMono (σ.trans <| graphEquiv₁ f) := by
  constructor <;> intro h
  -- ⊢ σ = sort f → StrictMono ↑(σ.trans (graphEquiv₁ f))
                  -- ⊢ StrictMono ↑(σ.trans (graphEquiv₁ f))
                  -- ⊢ σ = sort f
  · rw [h, sort, Equiv.trans_assoc, Equiv.symm_trans_self]
    -- ⊢ StrictMono ↑((graphEquiv₂ f).trans (Equiv.refl { x // x ∈ graph f }))
    exact (graphEquiv₂ f).strictMono
    -- 🎉 no goals
  · have := Subsingleton.elim (graphEquiv₂ f) (h.orderIsoOfSurjective _ <| Equiv.surjective _)
    -- ⊢ σ = sort f
    ext1 x
    -- ⊢ ↑σ x = ↑(sort f) x
    exact (graphEquiv₁ f).apply_eq_iff_eq_symm_apply.1 (FunLike.congr_fun this x).symm
    -- 🎉 no goals
#align tuple.eq_sort_iff' Tuple.eq_sort_iff'

/-- A permutation `σ` equals `sort f` if and only if `f ∘ σ` is monotone and whenever `i < j`
and `f (σ i) = f (σ j)`, then `σ i < σ j`. This means that `sort f` is the lexicographically
smallest permutation `σ` such that `f ∘ σ` is monotone. -/
theorem eq_sort_iff :
    σ = sort f ↔ Monotone (f ∘ σ) ∧ ∀ i j, i < j → f (σ i) = f (σ j) → σ i < σ j := by
  rw [eq_sort_iff']
  -- ⊢ StrictMono ↑(σ.trans (graphEquiv₁ f)) ↔ Monotone (f ∘ ↑σ) ∧ ∀ (i j : Fin n), …
  refine' ⟨fun h => ⟨(monotone_proj f).comp h.monotone, fun i j hij hfij => _⟩, fun h i j hij => _⟩
  -- ⊢ ↑σ i < ↑σ j
  · exact (((Prod.Lex.lt_iff _ _).1 <| h hij).resolve_left hfij.not_lt).2
    -- 🎉 no goals
  · obtain he | hl := (h.1 hij.le).eq_or_lt <;> apply (Prod.Lex.lt_iff _ _).2
    -- ⊢ ↑(σ.trans (graphEquiv₁ f)) i < ↑(σ.trans (graphEquiv₁ f)) j
                                                -- ⊢ (f (↑σ i), ↑σ i).fst < (f (↑σ j), ↑σ j).fst ∨ (f (↑σ i), ↑σ i).fst = (f (↑σ  …
                                                -- ⊢ (f (↑σ i), ↑σ i).fst < (f (↑σ j), ↑σ j).fst ∨ (f (↑σ i), ↑σ i).fst = (f (↑σ  …
    exacts [Or.inr ⟨he, h.2 i j hij he⟩, Or.inl hl]
    -- 🎉 no goals
#align tuple.eq_sort_iff Tuple.eq_sort_iff

/-- The permutation that sorts `f` is the identity if and only if `f` is monotone. -/
theorem sort_eq_refl_iff_monotone : sort f = Equiv.refl _ ↔ Monotone f := by
  rw [eq_comm, eq_sort_iff, Equiv.coe_refl, Function.comp.right_id]
  -- ⊢ (Monotone f ∧ ∀ (i j : Fin n), i < j → f (id i) = f (id j) → id i < id j) ↔  …
  simp only [id.def, and_iff_left_iff_imp]
  -- ⊢ Monotone f → ∀ (i j : Fin n), i < j → f i = f j → i < j
  exact fun _ _ _ hij _ => hij
  -- 🎉 no goals
#align tuple.sort_eq_refl_iff_monotone Tuple.sort_eq_refl_iff_monotone

/-- A permutation of a tuple `f` is `f` sorted if and only if it is monotone. -/
theorem comp_sort_eq_comp_iff_monotone : f ∘ σ = f ∘ sort f ↔ Monotone (f ∘ σ) :=
  ⟨fun h => h.symm ▸ monotone_sort f, fun h => unique_monotone h (monotone_sort f)⟩
#align tuple.comp_sort_eq_comp_iff_monotone Tuple.comp_sort_eq_comp_iff_monotone

/-- The sorted versions of a tuple `f` and of any permutation of `f` agree. -/
theorem comp_perm_comp_sort_eq_comp_sort : (f ∘ σ) ∘ sort (f ∘ σ) = f ∘ sort f := by
  rw [Function.comp.assoc, ← Equiv.Perm.coe_mul]
  -- ⊢ f ∘ ↑(σ * sort (f ∘ ↑σ)) = f ∘ ↑(sort f)
  exact unique_monotone (monotone_sort (f ∘ σ)) (monotone_sort f)
  -- 🎉 no goals
#align tuple.comp_perm_comp_sort_eq_comp_sort Tuple.comp_perm_comp_sort_eq_comp_sort

/-- If a permutation `f ∘ σ` of the tuple `f` is not the same as `f ∘ sort f`, then `f ∘ σ`
has a pair of strictly decreasing entries. -/
theorem antitone_pair_of_not_sorted' (h : f ∘ σ ≠ f ∘ sort f) :
    ∃ i j, i < j ∧ (f ∘ σ) j < (f ∘ σ) i := by
  contrapose! h
  -- ⊢ f ∘ ↑σ = f ∘ ↑(sort f)
  exact comp_sort_eq_comp_iff_monotone.mpr (monotone_iff_forall_lt.mpr h)
  -- 🎉 no goals
#align tuple.antitone_pair_of_not_sorted' Tuple.antitone_pair_of_not_sorted'

/-- If the tuple `f` is not the same as `f ∘ sort f`, then `f` has a pair of strictly decreasing
entries. -/
theorem antitone_pair_of_not_sorted (h : f ≠ f ∘ sort f) : ∃ i j, i < j ∧ f j < f i :=
  antitone_pair_of_not_sorted' (id h : f ∘ Equiv.refl _ ≠ _)
#align tuple.antitone_pair_of_not_sorted Tuple.antitone_pair_of_not_sorted

end Tuple
