/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Data.Prod.Lex
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fin.Interval
import Mathlib.Tactic.FinCases

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
  · exact Finset.card_fin _
  · intro _ _
    -- Porting note: was `simp`
    dsimp only
    rw [Prod.ext_iff]
    simp
#align tuple.graph.card Tuple.graph.card

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
    obtain ⟨-, rfl⟩ := Prod.mk.inj_iff.mp hi'
    simpa
#align tuple.graph_equiv₁ Tuple.graphEquiv₁

@[simp]
theorem proj_equiv₁' (f : Fin n → α) : graph.proj ∘ graphEquiv₁ f = f :=
  rfl
#align tuple.proj_equiv₁' Tuple.proj_equiv₁'

/-- `graphEquiv₂ f` is an equivalence between `Fin n` and `graph f` that respects the order.
-/
def graphEquiv₂ (f : Fin n → α) : Fin n ≃o graph f :=
  Finset.orderIsoOfFin _ (by simp)
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
#align tuple.self_comp_sort Tuple.self_comp_sort

theorem monotone_proj (f : Fin n → α) : Monotone (graph.proj : graph f → α) := by
  rintro ⟨⟨x, i⟩, hx⟩ ⟨⟨y, j⟩, hy⟩ (_ | h)
  · exact le_of_lt ‹_›
  · simp [graph.proj]
#align tuple.monotone_proj Tuple.monotone_proj

theorem monotone_sort (f : Fin n → α) : Monotone (f ∘ sort f) := by
  rw [self_comp_sort]
  exact (monotone_proj f).comp (graphEquiv₂ f).monotone
#align tuple.monotone_sort Tuple.monotone_sort

/-- All the elements `· ≤ a` appear the start of a sorted tuple -/
theorem sort_lt_at_start_of_monotone {α} [LinearOrder α] (m : ℕ) (f : Fin m → α) (a : α)
    (h_sorted : Monotone f)
    (j : Fin m) (h : j < Fintype.card {i // f i ≤ a}) :
    f j ≤ a := by
  contrapose! h
  rw [← Fin.card_Iio, Fintype.card_subtype]
  refine Finset.card_mono (fun i => Function.mtr ?_)
  simp_rw [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
  exact fun hij => (h.trans_le <| h_sorted <| le_of_not_lt hij).not_le

lemma Fintype.card_eq_subtypeSubtype_comm {α : Type} [Fintype α] (p q : α → Prop)
    [DecidablePred p] [DecidablePred q] : Fintype.card (Subtype fun x => (p x) ∧ (q x)) =
      Fintype.card (Subtype fun x => (q x) ∧ (p x)) := by
  apply Fintype.card_congr
  exact ⟨fun x => ⟨x, ⟨x.2.2, x.2.1⟩⟩, fun x => ⟨x, ⟨x.2.2, x.2.1⟩⟩,
    fun _ => by dsimp, fun _ => by dsimp ⟩

lemma Fintype.card_inter_eq_card_and {α : Type} [Fintype α] (p q : α → Prop)
    [DecidablePred p] [DecidablePred q] : Fintype.card {i : (Subtype fun x => (p x)) // (q i)} =
      Fintype.card (Subtype fun x => (q x) ∧ (p x)) := by
  rw [← Fintype.card_eq_subtypeSubtype_comm p q]
  refine' Fintype.card_eq.2 (Nonempty.intro ?_)
  exact Equiv.subtypeSubtypeEquivSubtypeInter (fun x ↦ p x) q

lemma Fintype.card_fin_lt_nat (m g : ℕ) (h : g ≤ m) : Fintype.card {i : Fin m // i < g } = g := by
  conv_rhs => rw [← Fintype.card_fin g]
  apply Fintype.card_congr
  exact ⟨ fun x => ⟨x, x.prop⟩, fun x => ⟨⟨x, (lt_of_lt_of_le (Fin.is_lt x) h)⟩, x.prop⟩,
    fun x => by simp, fun x => by simp⟩

theorem sort_lt_at_start_of_monotone' {α} [LinearOrder α] (m : ℕ)(f : Fin m → α) (a : α)
    (h_sorted : Monotone f)
    (j : Fin m) :
    f j ≤ a → (j < Fintype.card {i // f i ≤ a}) := by
  intro h
  by_contra' hc
  let p := fun x : Fin m => f x ≤ a
  let q := fun x : Fin m => (x < (Fintype.card {i // f i ≤ a}))
  let q' := fun x : {i // f i ≤ a} => q x

  have he := Fintype.card_congr $ Equiv.sumCompl $ q'
  have h4 := (Fintype.card_congr (@Equiv.subtypeSubtypeEquivSubtype _ p q
    (sort_lt_at_start_of_monotone m f a h_sorted _)))
  have hw : 0 < Fintype.card {j : {x : Fin m // p x} // ¬q' j} :=
    Fintype.card_pos_iff.2 (Nonempty.intro ⟨⟨j, h⟩, not_lt.2 hc⟩)

  rw [Fintype.card_sum, h4, Fintype.card_fin_lt_nat, add_right_eq_self] at he
  apply (ne_of_lt hw) he.symm
  conv_rhs => rw [← Fintype.card_fin m]
  exact Fintype.card_subtype_le _

theorem sort_lt_at_start_of_monotone_iff {α} [LinearOrder α] (m : ℕ) (f : Fin m → α) (a : α)
    (h_sorted : Monotone f)
    (j : Fin m) :
    (j < Fintype.card {i // f i ≤ a})  ↔ f j ≤ a :=
  ⟨sort_lt_at_start_of_monotone m f a h_sorted j, sort_lt_at_start_of_monotone' _ _ _ h_sorted _⟩

theorem sort_ge_at_start_of_antitone {α} [LinearOrder α] (m : ℕ) (f : Fin m → α) (a : α)
    (h_sorted : Antitone f)
    (j : Fin m) :
    (j < Fintype.card {i // a ≤ f i})  → a ≤ f j := by
  · contrapose!
    intro h
    rw [← Fin.card_Iio, Fintype.card_subtype]
    refine Finset.card_mono (fun i => Function.mtr ?_)
    simp_rw [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio, not_lt, not_le]
    exact fun hij => lt_of_le_of_lt (h_sorted hij) h

theorem sort_ge_at_start_of_antitone' {α} [LinearOrder α] (m : ℕ) (f : Fin m → α) (a : α)
    (h_sorted : Antitone f)
    (j : Fin m) :
    a ≤ f j → (j < Fintype.card {i // a ≤ f i})  := by
  intro h
  by_contra' hc
  let p := fun x : Fin m => a ≤ f x
  let q := fun x : Fin m => (x < (Fintype.card {i // a ≤ f i}))
  let q' := fun x : {i // a ≤ f i} => q x

  have he := Fintype.card_congr $ Equiv.sumCompl $ q'
  have h4 := (Fintype.card_congr (@Equiv.subtypeSubtypeEquivSubtype _ p q
    (sort_ge_at_start_of_antitone m f a h_sorted _)))
  have hw : 0 < Fintype.card {j : {x : Fin m // p x} // ¬q' j} := by
    apply Fintype.card_pos_iff.2 (Nonempty.intro ⟨⟨j, h⟩, not_lt.2 hc⟩)
  rw [Fintype.card_sum, h4, Fintype.card_fin_lt_nat, add_right_eq_self] at he
  apply (ne_of_lt hw) he.symm
  conv_rhs => rw [← Fintype.card_fin m]
  exact Fintype.card_subtype_le _

theorem sort_ge_at_start_of_anittone_iff {α} [LinearOrder α] (m : ℕ) (f : Fin m → α) (a : α)
    (h_sorted : Antitone f)
    (j : Fin m) :
    (j < Fintype.card {i // a ≤ f i})  ↔ a ≤ f j :=
  ⟨sort_ge_at_start_of_antitone m f a h_sorted j, sort_ge_at_start_of_antitone' _ _ _ h_sorted _⟩


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
  · rw [h, sort, Equiv.trans_assoc, Equiv.symm_trans_self]
    exact (graphEquiv₂ f).strictMono
  · have := Subsingleton.elim (graphEquiv₂ f) (h.orderIsoOfSurjective _ <| Equiv.surjective _)
    ext1 x
    exact (graphEquiv₁ f).apply_eq_iff_eq_symm_apply.1 (FunLike.congr_fun this x).symm
#align tuple.eq_sort_iff' Tuple.eq_sort_iff'

/-- A permutation `σ` equals `sort f` if and only if `f ∘ σ` is monotone and whenever `i < j`
and `f (σ i) = f (σ j)`, then `σ i < σ j`. This means that `sort f` is the lexicographically
smallest permutation `σ` such that `f ∘ σ` is monotone. -/
theorem eq_sort_iff :
    σ = sort f ↔ Monotone (f ∘ σ) ∧ ∀ i j, i < j → f (σ i) = f (σ j) → σ i < σ j := by
  rw [eq_sort_iff']
  refine' ⟨fun h => ⟨(monotone_proj f).comp h.monotone, fun i j hij hfij => _⟩, fun h i j hij => _⟩
  · exact (((Prod.Lex.lt_iff _ _).1 <| h hij).resolve_left hfij.not_lt).2
  · obtain he | hl := (h.1 hij.le).eq_or_lt <;> apply (Prod.Lex.lt_iff _ _).2
    exacts [Or.inr ⟨he, h.2 i j hij he⟩, Or.inl hl]
#align tuple.eq_sort_iff Tuple.eq_sort_iff

/-- The permutation that sorts `f` is the identity if and only if `f` is monotone. -/
theorem sort_eq_refl_iff_monotone : sort f = Equiv.refl _ ↔ Monotone f := by
  rw [eq_comm, eq_sort_iff, Equiv.coe_refl, Function.comp.right_id]
  simp only [id.def, and_iff_left_iff_imp]
  exact fun _ _ _ hij _ => hij
#align tuple.sort_eq_refl_iff_monotone Tuple.sort_eq_refl_iff_monotone

/-- A permutation of a tuple `f` is `f` sorted if and only if it is monotone. -/
theorem comp_sort_eq_comp_iff_monotone : f ∘ σ = f ∘ sort f ↔ Monotone (f ∘ σ) :=
  ⟨fun h => h.symm ▸ monotone_sort f, fun h => unique_monotone h (monotone_sort f)⟩
#align tuple.comp_sort_eq_comp_iff_monotone Tuple.comp_sort_eq_comp_iff_monotone

/-- The sorted versions of a tuple `f` and of any permutation of `f` agree. -/
theorem comp_perm_comp_sort_eq_comp_sort : (f ∘ σ) ∘ sort (f ∘ σ) = f ∘ sort f := by
  rw [Function.comp.assoc, ← Equiv.Perm.coe_mul]
  exact unique_monotone (monotone_sort (f ∘ σ)) (monotone_sort f)
#align tuple.comp_perm_comp_sort_eq_comp_sort Tuple.comp_perm_comp_sort_eq_comp_sort

/-- If a permutation `f ∘ σ` of the tuple `f` is not the same as `f ∘ sort f`, then `f ∘ σ`
has a pair of strictly decreasing entries. -/
theorem antitone_pair_of_not_sorted' (h : f ∘ σ ≠ f ∘ sort f) :
    ∃ i j, i < j ∧ (f ∘ σ) j < (f ∘ σ) i := by
  contrapose! h
  exact comp_sort_eq_comp_iff_monotone.mpr (monotone_iff_forall_lt.mpr h)
#align tuple.antitone_pair_of_not_sorted' Tuple.antitone_pair_of_not_sorted'

/-- If the tuple `f` is not the same as `f ∘ sort f`, then `f` has a pair of strictly decreasing
entries. -/
theorem antitone_pair_of_not_sorted (h : f ≠ f ∘ sort f) : ∃ i j, i < j ∧ f j < f i :=
  antitone_pair_of_not_sorted' (id h : f ∘ Equiv.refl _ ≠ _)
#align tuple.antitone_pair_of_not_sorted Tuple.antitone_pair_of_not_sorted

end Tuple
