/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Option

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
@[to_additive "If a sum of a `Finset` of a subsingleton type has a given
  value, so do the terms in that sum."]
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

end

open Finset

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
  · rw [filter_piFinset_of_not_mem _ _ _ h, Finset.card_empty]

lemma card_filter_piFinset_const (s : Finset κ) (i : ι) (j : κ) :
    #{f ∈ piFinset fun _ ↦ s | f i = j} = if j ∈ s then #s ^ (card ι - 1) else 0 :=
  (card_filter_piFinset_eq _ _ _).trans <| by
    rw [prod_const #s, card_erase_of_mem (mem_univ _), card_univ]

end Fintype
end Pi

-- TODO: this is a basic theorem about `Fintype.card`,
-- and ideally could be moved to `Mathlib.Data.Fintype.Card`.
theorem Fintype.card_fun [DecidableEq α] [Fintype α] [Fintype β] :
    Fintype.card (α → β) = Fintype.card β ^ Fintype.card α := by
  simp

@[simp]
theorem card_vector [Fintype α] (n : ℕ) : Fintype.card (Vector α n) = Fintype.card α ^ n := by
  rw [Fintype.ofEquiv_card]; simp

/-- It is equivalent to compute the product of a function over `Fin n` or `Finset.range n`. -/
@[to_additive "It is equivalent to sum a function over `fin n` or `finset.range n`."]
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
  simp only [prod_dite, attach_eq_univ]
  congr 1
  · exact (Equiv.subtypeEquivRight <| by simp).prod_comp fun x : { x // p x } => f x x.2
  · exact (Equiv.subtypeEquivRight <| by simp).prod_comp fun x : { x // ¬p x } => g x x.2

section

open Finset

variable {α₁ : Type*} {α₂ : Type*} {M : Type*} [Fintype α₁] [Fintype α₂] [CommMonoid M]

@[to_additive]
theorem Fintype.prod_sum_elim (f : α₁ → M) (g : α₂ → M) :
    ∏ x, Sum.elim f g x = (∏ a₁, f a₁) * ∏ a₂, g a₂ :=
  prod_disj_sum _ _ _

@[to_additive (attr := simp)]
theorem Fintype.prod_sum_type (f : α₁ ⊕ α₂ → M) :
    ∏ x, f x = (∏ a₁, f (Sum.inl a₁)) * ∏ a₂, f (Sum.inr a₂) :=
  prod_disj_sum _ _ _

/-- The product over a product type equals the product of the fiberwise products. For rewriting
in the reverse direction, use `Fintype.prod_prod_type'`. -/
@[to_additive Fintype.sum_prod_type "The sum over a product type equals the sum of fiberwise sums.
For rewriting in the reverse direction, use `Fintype.sum_prod_type'`."]
theorem Fintype.prod_prod_type (f : α₁ × α₂ → M) : ∏ x, f x = ∏ x, ∏ y, f (x, y) :=
  Finset.prod_product ..

/-- The product over a product type equals the product of the fiberwise products. For rewriting
in the reverse direction, use `Fintype.prod_prod_type`. -/
@[to_additive Fintype.sum_prod_type' "The sum over a product type equals the sum of fiberwise sums.
For rewriting in the reverse direction, use `Fintype.sum_prod_type`."]
theorem Fintype.prod_prod_type' (f : α₁ → α₂ → M) : ∏ x : α₁ × α₂, f x.1 x.2 = ∏ x, ∏ y, f x y :=
  Finset.prod_product' ..

@[to_additive Fintype.sum_prod_type_right]
theorem Fintype.prod_prod_type_right (f : α₁ × α₂ → M) : ∏ x, f x = ∏ y, ∏ x, f (x, y) :=
  Finset.prod_product_right ..

/-- An uncurried version of `Finset.prod_prod_type_right`. -/
@[to_additive Fintype.sum_prod_type_right' "An uncurried version of `Finset.sum_prod_type_right`"]
theorem Fintype.prod_prod_type_right' (f : α₁ → α₂ → M) :
    ∏ x : α₁ × α₂, f x.1 x.2 = ∏ y, ∏ x, f x y :=
  Finset.prod_product_right' ..

/-! ### Sums over `Fin n` -/

@[to_additive]
theorem Finset.prod_range {n : ℕ} (f : ℕ → M) : ∏ i ∈ Finset.range n, f i = ∏ i : Fin n, f i :=
  (Fin.prod_univ_eq_prod_range _ _).symm

namespace Fin

@[to_additive]
theorem prod_ofFn {n : ℕ} (f : Fin n → M) : (List.ofFn f).prod = ∏ i, f i := by
  simp [prod_eq_multiset_prod]

@[to_additive]
theorem prod_univ_def {n : ℕ} (f : Fin n → M) : ∏ i, f i = ((List.finRange n).map f).prod := by
  rw [← List.ofFn_eq_map, prod_ofFn]

/-- A product of a function `f : Fin 0 → M` is `1` because `Fin 0` is empty -/
@[to_additive "A sum of a function `f : Fin 0 → M` is `0` because `Fin 0` is empty"]
theorem prod_univ_zero (f : Fin 0 → M) : ∏ i, f i = 1 :=
  rfl

/-- A product of a function `f : Fin (n + 1) → M` over all `Fin (n + 1)`
is the product of `f x`, for some `x : Fin (n + 1)` times the remaining product -/
@[to_additive "A sum of a function `f : Fin (n + 1) → M` over all `Fin (n + 1)` is the sum of
`f x`, for some `x : Fin (n + 1)` plus the remaining product"]
theorem prod_univ_succAbove {n : ℕ} (f : Fin (n + 1) → M) (x : Fin (n + 1)) :
    ∏ i, f i = f x * ∏ i : Fin n, f (x.succAbove i) := by
  rw [univ_succAbove, prod_cons, Finset.prod_map _ x.succAboveEmb]
  rfl

/-- A product of a function `f : Fin (n + 1) → M` over all `Fin (n + 1)`
is the product of `f 0` plus the remaining product -/
@[to_additive "A sum of a function `f : Fin (n + 1) → M` over all `Fin (n + 1)` is the sum of
`f 0` plus the remaining product"]
theorem prod_univ_succ {n : ℕ} (f : Fin (n + 1) → M) :
    ∏ i, f i = f 0 * ∏ i : Fin n, f i.succ :=
  prod_univ_succAbove f 0

/-- A product of a function `f : Fin (n + 1) → M` over all `Fin (n + 1)`
is the product of `f (Fin.last n)` plus the remaining product -/
@[to_additive "A sum of a function `f : Fin (n + 1) → M` over all `Fin (n + 1)` is the sum of
`f (Fin.last n)` plus the remaining sum"]
theorem prod_univ_castSucc {n : ℕ} (f : Fin (n + 1) → M) :
    ∏ i, f i = (∏ i : Fin n, f (Fin.castSucc i)) * f (last n) := by
  simpa [mul_comm] using prod_univ_succAbove f (last n)

@[to_additive (attr := simp)]
theorem prod_univ_get [CommMonoid α] (l : List α) : ∏ i : Fin l.length, l[i.1] = l.prod := by
  simp [Finset.prod_eq_multiset_prod]

@[to_additive (attr := simp)]
theorem prod_univ_get' (l : List α) (f : α → M) :
    ∏ i : Fin l.length, f l[i.1] = (l.map f).prod := by
  simp [Finset.prod_eq_multiset_prod]

@[to_additive (attr := simp)]
theorem prod_cons {n : ℕ} (x : M) (f : Fin n → M) :
    (∏ i : Fin n.succ, (cons x f : Fin n.succ → M) i) = x * ∏ i : Fin n, f i := by
  simp_rw [prod_univ_succ, cons_zero, cons_succ]

@[to_additive (attr := simp)]
theorem prod_snoc {n : ℕ} (x : M) (f : Fin n → M) :
    (∏ i : Fin n.succ, (snoc f x : Fin n.succ → M) i) = (∏ i : Fin n, f i) * x := by
  simp [prod_univ_castSucc]

@[to_additive sum_univ_one]
theorem prod_univ_one (f : Fin 1 → M) : ∏ i, f i = f 0 := by simp

@[to_additive (attr := simp)]
theorem prod_univ_two (f : Fin 2 → M) : ∏ i, f i = f 0 * f 1 := by
  simp [prod_univ_succ]

@[to_additive]
theorem prod_univ_two' (f : α → M) (a b : α) :
    ∏ i, f (![a, b] i) = f a * f b :=
  prod_univ_two _

@[to_additive]
theorem prod_univ_three (f : Fin 3 → M) : ∏ i, f i = f 0 * f 1 * f 2 := by
  rw [prod_univ_castSucc, prod_univ_two]
  rfl

@[to_additive]
theorem prod_univ_four (f : Fin 4 → M) : ∏ i, f i = f 0 * f 1 * f 2 * f 3 := by
  rw [prod_univ_castSucc, prod_univ_three]
  rfl

@[to_additive]
theorem prod_univ_five (f : Fin 5 → M) : ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 := by
  rw [prod_univ_castSucc, prod_univ_four]
  rfl

@[to_additive]
theorem prod_univ_six (f : Fin 6 → M) : ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 := by
  rw [prod_univ_castSucc, prod_univ_five]
  rfl

@[to_additive]
theorem prod_univ_seven (f : Fin 7 → M) : ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 := by
  rw [prod_univ_castSucc, prod_univ_six]
  rfl

@[to_additive]
theorem prod_univ_eight (f : Fin 8 → M) :
    ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 * f 7 := by
  rw [prod_univ_castSucc, prod_univ_seven]
  rfl

theorem prod_const [CommMonoid α] (n : ℕ) (x : α) : ∏ _i : Fin n, x = x ^ n := by simp

theorem sum_const [AddCommMonoid α] (n : ℕ) (x : α) : ∑ _i : Fin n, x = n • x := by simp

@[to_additive]
theorem prod_congr' {M : Type*} [CommMonoid M] {a b : ℕ} (f : Fin b → M) (h : a = b) :
    (∏ i : Fin a, f (cast h i)) = ∏ i : Fin b, f i := by
  subst h
  congr

end Fin

end
