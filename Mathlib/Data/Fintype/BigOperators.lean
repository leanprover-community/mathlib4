/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Vector

/-!
Results about "big operations" over a `Fintype`, and consequent
results about cardinalities of certain types.

## Implementation note
This content had previously been in `Data.Fintype.Basic`, but was moved here to avoid
requiring `Algebra.BigOperators` (and hence many other imports) as a
dependency of `Fintype`.

However many of the results here really belong in `Algebra.BigOperators.Group.Finset`
and should be moved at some point.
-/

assert_not_exists MulAction

open Mathlib

universe u v

variable {α : Type*} {β : Type*} {γ : Type*}

namespace Fintype

@[to_additive]
theorem prod_bool [CommMonoid α] (f : Bool → α) : ∏ b, f b = f true * f false := by simp

theorem card_eq_sum_ones {α} [Fintype α] : Fintype.card α = ∑ _a : α, 1 :=
  Finset.card_eq_sum_ones _

section

open Finset

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

@[to_additive]
theorem prod_extend_by_one [CommMonoid α] (s : Finset ι) (f : ι → α) :
    ∏ i, (if i ∈ s then f i else 1) = ∏ i ∈ s, f i := by
  rw [← prod_filter, filter_mem_eq_inter, univ_inter]

end

section

variable {M : Type*} [Fintype α] [CommMonoid M]

@[to_additive]
theorem prod_eq_one (f : α → M) (h : ∀ a, f a = 1) : ∏ a, f a = 1 :=
  Finset.prod_eq_one fun a _ha => h a

@[to_additive]
theorem prod_congr (f g : α → M) (h : ∀ a, f a = g a) : ∏ a, f a = ∏ a, g a :=
  Finset.prod_congr rfl fun a _ha => h a

@[to_additive]
theorem prod_eq_single {f : α → M} (a : α) (h : ∀ x ≠ a, f x = 1) : ∏ x, f x = f a :=
  Finset.prod_eq_single a (fun x _ hx => h x hx) fun ha => (ha (Finset.mem_univ a)).elim

@[to_additive]
theorem prod_eq_mul {f : α → M} (a b : α) (h₁ : a ≠ b) (h₂ : ∀ x, x ≠ a ∧ x ≠ b → f x = 1) :
    ∏ x, f x = f a * f b := by
  apply Finset.prod_eq_mul a b h₁ fun x _ hx => h₂ x hx <;>
    exact fun hc => (hc (Finset.mem_univ _)).elim

/-- If a product of a `Finset` of a subsingleton type has a given
value, so do the terms in that product. -/
@[to_additive /-- If a sum of a `Finset` of a subsingleton type has a given
  value, so do the terms in that sum. -/]
theorem eq_of_subsingleton_of_prod_eq {ι : Type*} [Subsingleton ι] {s : Finset ι} {f : ι → M}
    {b : M} (h : ∏ i ∈ s, f i = b) : ∀ i ∈ s, f i = b :=
  Finset.eq_of_card_le_one_of_prod_eq (Finset.card_le_one_of_subsingleton s) h

end

end Fintype

open Finset

section

variable {M : Type*} [Fintype α] [CommMonoid M]

@[to_additive (attr := simp)]
theorem Fintype.prod_option (f : Option α → M) : ∏ i, f i = f none * ∏ i, f (some i) :=
  Finset.prod_insertNone f univ

@[to_additive]
theorem Fintype.prod_eq_mul_prod_subtype_ne [DecidableEq α] (f : α → M) (a : α) :
    ∏ i, f i = f a * ∏ i : {i // i ≠ a}, f i.1 := by
  simp_rw [← (Equiv.optionSubtypeNe a).prod_comp, prod_option, Equiv.optionSubtypeNe_none,
    Equiv.optionSubtypeNe_some]

end

section Pi
variable {ι κ : Type*} {α : ι → Type*} [DecidableEq ι] [DecidableEq κ]

@[simp] lemma Finset.card_pi (s : Finset ι) (t : ∀ i, Finset (α i)) :
    #(s.pi t) = ∏ i ∈ s, #(t i) := Multiset.card_pi _ _

namespace Fintype

variable [Fintype ι]

@[simp] lemma card_piFinset (s : ∀ i, Finset (α i)) :
    #(piFinset s) = ∏ i, #(s i) := by simp [piFinset, card_map]

/-- This lemma is specifically designed to be used backwards, whence the specialisation to `Fin n`
as the indexing type doesn't matter in practice. The more general forward direction lemma here is
`Fintype.card_piFinset`. -/
lemma card_piFinset_const {α : Type*} (s : Finset α) (n : ℕ) :
    #(piFinset fun _ : Fin n ↦ s) = #s ^ n := by simp

@[simp] lemma card_pi [∀ i, Fintype (α i)] : card (∀ i, α i) = ∏ i, card (α i) :=
  card_piFinset _

/-- This lemma is specifically designed to be used backwards, whence the specialisation to `Fin n`
as the indexing type doesn't matter in practice. The more general forward direction lemma here is
`Fintype.card_pi`. -/
lemma card_pi_const (α : Type*) [Fintype α] (n : ℕ) : card (Fin n → α) = card α ^ n :=
  card_piFinset_const _ _

/-- Product over a sigma type equals the repeated product.

This is a version of `Finset.prod_sigma` specialized to the case
of multiplication over `Finset.univ`. -/
@[to_additive /-- Sum over a sigma type equals the repeated sum.

This is a version of `Finset.sum_sigma` specialized to the case of summation over `Finset.univ`. -/]
theorem prod_sigma {ι} {α : ι → Type*} {M : Type*} [Fintype ι] [∀ i, Fintype (α i)] [CommMonoid M]
    (f : Sigma α → M) : ∏ x, f x = ∏ x, ∏ y, f ⟨x, y⟩ :=
  Finset.prod_sigma ..

/-- Product over a sigma type equals the repeated product, curried version.
This version is useful to rewrite from right to left. -/
@[to_additive /-- Sum over a sigma type equals the repeated sum, curried version.
This version is useful to rewrite from right to left. -/]
theorem prod_sigma' {ι} {α : ι → Type*} {M : Type*} [Fintype ι] [∀ i, Fintype (α i)] [CommMonoid M]
    (f : (i : ι) → α i → M) : ∏ x : Sigma α, f x.1 x.2 = ∏ x, ∏ y, f x y :=
  prod_sigma ..

@[simp] nonrec lemma card_sigma {ι} {α : ι → Type*} [Fintype ι] [∀ i, Fintype (α i)] :
    card (Sigma α) = ∑ i, card (α i) := card_sigma _ _

/-- The number of dependent maps `f : Π j, s j` for which the `i` component is `a` is the product
over all `j ≠ i` of `#(s j)`.

Note that this is just a composition of easier lemmas, but there's some glue missing to make that
smooth enough not to need this lemma. -/
lemma card_filter_piFinset_eq_of_mem [∀ i, DecidableEq (α i)]
    (s : ∀ i, Finset (α i)) (i : ι) {a : α i} (ha : a ∈ s i) :
    #{f ∈ piFinset s | f i = a} = ∏ j ∈ univ.erase i, #(s j) := by
  calc
    _ = ∏ j, #(Function.update s i {a} j) := by
      rw [← piFinset_update_singleton_eq_filter_piFinset_eq _ _ ha, Fintype.card_piFinset]
    _ = ∏ j, Function.update (fun j ↦ #(s j)) i 1 j :=
      Fintype.prod_congr _ _ fun j ↦ by obtain rfl | hji := eq_or_ne j i <;> simp [*]
    _ = _ := by simp [prod_update_of_mem, erase_eq]

lemma card_filter_piFinset_const_eq_of_mem (s : Finset κ) (i : ι) {x : κ} (hx : x ∈ s) :
    #{f ∈ piFinset fun _ ↦ s | f i = x} = #s ^ (card ι - 1) :=
  (card_filter_piFinset_eq_of_mem _ _ hx).trans <| by
    rw [prod_const #s, card_erase_of_mem (mem_univ _), card_univ]

lemma card_filter_piFinset_eq [∀ i, DecidableEq (α i)] (s : ∀ i, Finset (α i)) (i : ι) (a : α i) :
    #{f ∈ piFinset s | f i = a} = if a ∈ s i then ∏ b ∈ univ.erase i, #(s b) else 0 := by
  split_ifs with h
  · rw [card_filter_piFinset_eq_of_mem _ _ h]
  · rw [filter_piFinset_of_notMem _ _ _ h, Finset.card_empty]

lemma card_filter_piFinset_const (s : Finset κ) (i : ι) (j : κ) :
    #{f ∈ piFinset fun _ ↦ s | f i = j} = if j ∈ s then #s ^ (card ι - 1) else 0 :=
  (card_filter_piFinset_eq _ _ _).trans <| by
    rw [prod_const #s, card_erase_of_mem (mem_univ _), card_univ]

end Fintype
end Pi

-- TODO: this is a basic theorem about `Fintype.card`,
-- and ideally could be moved to `Mathlib/Data/Fintype/Card.lean`.
theorem Fintype.card_fun [DecidableEq α] [Fintype α] [Fintype β] :
    Fintype.card (α → β) = Fintype.card β ^ Fintype.card α := by
  simp

@[simp]
theorem card_vector [Fintype α] (n : ℕ) :
    Fintype.card (List.Vector α n) = Fintype.card α ^ n := by
  rw [Fintype.ofEquiv_card]; simp

/-- It is equivalent to compute the product of a function over `Fin n` or `Finset.range n`. -/
@[to_additive /-- It is equivalent to sum a function over `fin n` or `finset.range n`. -/]
theorem Fin.prod_univ_eq_prod_range [CommMonoid α] (f : ℕ → α) (n : ℕ) :
    ∏ i : Fin n, f i = ∏ i ∈ range n, f i :=
  calc
    ∏ i : Fin n, f i = ∏ i : { x // x ∈ range n }, f i :=
      Fintype.prod_equiv (Fin.equivSubtype.trans (Equiv.subtypeEquivRight (by simp))) _ _ (by simp)
    _ = ∏ i ∈ range n, f i := by rw [← attach_eq_univ, prod_attach]

@[to_additive]
theorem Finset.prod_fin_eq_prod_range [CommMonoid β] {n : ℕ} (c : Fin n → β) :
    ∏ i, c i = ∏ i ∈ Finset.range n, if h : i < n then c ⟨i, h⟩ else 1 := by
  rw [← Fin.prod_univ_eq_prod_range, Finset.prod_congr rfl]
  rintro ⟨i, hi⟩ _
  simp only [hi, dif_pos]

@[to_additive]
theorem Finset.prod_toFinset_eq_subtype {M : Type*} [CommMonoid M] [Fintype α] (p : α → Prop)
    [DecidablePred p] (f : α → M) : ∏ a ∈ { x | p x }.toFinset, f a = ∏ a : Subtype p, f a := by
  rw [← Finset.prod_subtype]
  simp_rw [Set.mem_toFinset]; intro; rfl

nonrec theorem Fintype.prod_dite [Fintype α] {p : α → Prop} [DecidablePred p] [CommMonoid β]
    (f : ∀ a, p a → β) (g : ∀ a, ¬p a → β) :
    (∏ a, dite (p a) (f a) (g a)) =
    (∏ a : { a // p a }, f a a.2) * ∏ a : { a // ¬p a }, g a a.2 := by
  simp only [prod_dite]
  congr 1
  · exact (Equiv.subtypeEquivRight <| by simp).prod_comp fun x : { x // p x } => f x x.2
  · exact (Equiv.subtypeEquivRight <| by simp).prod_comp fun x : { x // ¬p x } => g x x.2

section

variable {α₁ : Type*} {α₂ : Type*} {M : Type*} [Fintype α₁] [Fintype α₂] [CommMonoid M]

@[to_additive]
theorem Fintype.prod_sumElim (f : α₁ → M) (g : α₂ → M) :
    ∏ x, Sum.elim f g x = (∏ a₁, f a₁) * ∏ a₂, g a₂ :=
  prod_disjSum _ _ _

@[deprecated (since := "2025-02-20")] alias prod_sum_elim := prod_sumElim
@[deprecated (since := "2025-02-20")] alias sum_sum_elim := sum_sumElim

@[to_additive (attr := simp)]
theorem Fintype.prod_sum_type (f : α₁ ⊕ α₂ → M) :
    ∏ x, f x = (∏ a₁, f (Sum.inl a₁)) * ∏ a₂, f (Sum.inr a₂) :=
  prod_disjSum _ _ _

/-- The product over a product type equals the product of the fiberwise products. For rewriting
in the reverse direction, use `Fintype.prod_prod_type'`. -/
@[to_additive Fintype.sum_prod_type /-- The sum over a product type equals the sum of fiberwise
sums. For rewriting in the reverse direction, use `Fintype.sum_prod_type'`. -/]
theorem Fintype.prod_prod_type [CommMonoid γ] (f : α₁ × α₂ → γ) :
    ∏ x, f x = ∏ x, ∏ y, f (x, y) :=
  Finset.prod_product ..

/-- The product over a product type equals the product of the fiberwise products. For rewriting
in the reverse direction, use `Fintype.prod_prod_type`. -/
@[to_additive Fintype.sum_prod_type' /-- The sum over a product type equals the sum of fiberwise
sums. For rewriting in the reverse direction, use `Fintype.sum_prod_type`. -/]
theorem Fintype.prod_prod_type' [CommMonoid γ] (f : α₁ → α₂ → γ) :
    ∏ x : α₁ × α₂, f x.1 x.2 = ∏ x, ∏ y, f x y :=
  Finset.prod_product' ..

@[to_additive Fintype.sum_prod_type_right]
theorem Fintype.prod_prod_type_right [CommMonoid γ] (f : α₁ × α₂ → γ) :
    ∏ x, f x = ∏ y, ∏ x, f (x, y) :=
  Finset.prod_product_right ..

/-- An uncurried version of `Finset.prod_prod_type_right`. -/
@[to_additive Fintype.sum_prod_type_right'
/-- An uncurried version of `Finset.sum_prod_type_right` -/]
theorem Fintype.prod_prod_type_right' [CommMonoid γ] (f : α₁ → α₂ → γ) :
    ∏ x : α₁ × α₂, f x.1 x.2 = ∏ y, ∏ x, f x y :=
  Finset.prod_product_right' ..

end
