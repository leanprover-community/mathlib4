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
import Mathlib.Algebra.BigOperators.Option

#align_import data.fintype.big_operators from "leanprover-community/mathlib"@"2445c98ae4b87eabebdde552593519b9b6dc350c"

/-!
Results about "big operations" over a `Fintype`, and consequent
results about cardinalities of certain types.

## Implementation note
This content had previously been in `Data.Fintype.Basic`, but was moved here to avoid
requiring `Algebra.BigOperators` (and hence many other imports) as a
dependency of `Fintype`.

However many of the results here really belong in `Algebra.BigOperators.Basic`
and should be moved at some point.
-/


universe u v

variable {α : Type*} {β : Type*} {γ : Type*}

open BigOperators

namespace Fintype

@[to_additive]
theorem prod_bool [CommMonoid α] (f : Bool → α) : ∏ b, f b = f true * f false := by simp
#align fintype.prod_bool Fintype.prod_bool
#align fintype.sum_bool Fintype.sum_bool

theorem card_eq_sum_ones {α} [Fintype α] : Fintype.card α = ∑ _a : α, 1 :=
  Finset.card_eq_sum_ones _
#align fintype.card_eq_sum_ones Fintype.card_eq_sum_ones

section

open Finset

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

@[to_additive]
theorem prod_extend_by_one [CommMonoid α] (s : Finset ι) (f : ι → α) :
    ∏ i, (if i ∈ s then f i else 1) = ∏ i in s, f i := by
  rw [← prod_filter, filter_mem_eq_inter, univ_inter]
#align fintype.prod_extend_by_one Fintype.prod_extend_by_one
#align fintype.sum_extend_by_zero Fintype.sum_extend_by_zero

end

section

variable {M : Type*} [Fintype α] [CommMonoid M]

@[to_additive]
theorem prod_eq_one (f : α → M) (h : ∀ a, f a = 1) : ∏ a, f a = 1 :=
  Finset.prod_eq_one fun a _ha => h a
#align fintype.prod_eq_one Fintype.prod_eq_one
#align fintype.sum_eq_zero Fintype.sum_eq_zero

@[to_additive]
theorem prod_congr (f g : α → M) (h : ∀ a, f a = g a) : ∏ a, f a = ∏ a, g a :=
  Finset.prod_congr rfl fun a _ha => h a
#align fintype.prod_congr Fintype.prod_congr
#align fintype.sum_congr Fintype.sum_congr

@[to_additive]
theorem prod_eq_single {f : α → M} (a : α) (h : ∀ x ≠ a, f x = 1) : ∏ x, f x = f a :=
  Finset.prod_eq_single a (fun x _ hx => h x hx) fun ha => (ha (Finset.mem_univ a)).elim
#align fintype.prod_eq_single Fintype.prod_eq_single
#align fintype.sum_eq_single Fintype.sum_eq_single

@[to_additive]
theorem prod_eq_mul {f : α → M} (a b : α) (h₁ : a ≠ b) (h₂ : ∀ x, x ≠ a ∧ x ≠ b → f x = 1) :
    ∏ x, f x = f a * f b := by
  apply Finset.prod_eq_mul a b h₁ fun x _ hx => h₂ x hx <;>
    exact fun hc => (hc (Finset.mem_univ _)).elim
#align fintype.prod_eq_mul Fintype.prod_eq_mul
#align fintype.sum_eq_add Fintype.sum_eq_add

/-- If a product of a `Finset` of a subsingleton type has a given
value, so do the terms in that product. -/
@[to_additive "If a sum of a `Finset` of a subsingleton type has a given
  value, so do the terms in that sum."]
theorem eq_of_subsingleton_of_prod_eq {ι : Type*} [Subsingleton ι] {s : Finset ι} {f : ι → M}
    {b : M} (h : ∏ i in s, f i = b) : ∀ i ∈ s, f i = b :=
  Finset.eq_of_card_le_one_of_prod_eq (Finset.card_le_one_of_subsingleton s) h
#align fintype.eq_of_subsingleton_of_prod_eq Fintype.eq_of_subsingleton_of_prod_eq
#align fintype.eq_of_subsingleton_of_sum_eq Fintype.eq_of_subsingleton_of_sum_eq

end

end Fintype

open Finset

section

variable {M : Type*} [Fintype α] [CommMonoid M]

@[to_additive (attr := simp)]
theorem Fintype.prod_option (f : Option α → M) : ∏ i, f i = f none * ∏ i, f (some i) :=
  Finset.prod_insertNone f univ
#align fintype.prod_option Fintype.prod_option
#align fintype.sum_option Fintype.sum_option

end

open Finset

@[simp]
nonrec theorem Fintype.card_sigma {α : Type*} (β : α → Type*) [Fintype α] [∀ a, Fintype (β a)] :
    Fintype.card (Sigma β) = ∑ a, Fintype.card (β a) :=
  card_sigma _ _
#align fintype.card_sigma Fintype.card_sigma

@[simp]
theorem Finset.card_pi [DecidableEq α] {δ : α → Type*} (s : Finset α) (t : ∀ a, Finset (δ a)) :
    (s.pi t).card = ∏ a in s, card (t a) :=
  Multiset.card_pi _ _
#align finset.card_pi Finset.card_pi

@[simp]
theorem Fintype.card_piFinset [DecidableEq α] [Fintype α] {δ : α → Type*} (t : ∀ a, Finset (δ a)) :
    (Fintype.piFinset t).card = ∏ a, Finset.card (t a) := by simp [Fintype.piFinset, card_map]
#align fintype.card_pi_finset Fintype.card_piFinset

@[simp]
theorem Fintype.card_pi {β : α → Type*} [DecidableEq α] [Fintype α] [∀ a, Fintype (β a)] :
    Fintype.card (∀ a, β a) = ∏ a, Fintype.card (β a) :=
  Fintype.card_piFinset _
#align fintype.card_pi Fintype.card_pi

-- FIXME ouch, this should be in the main file.
@[simp]
theorem Fintype.card_fun [DecidableEq α] [Fintype α] [Fintype β] :
    Fintype.card (α → β) = Fintype.card β ^ Fintype.card α := by
  rw [Fintype.card_pi, Finset.prod_const]; rfl
#align fintype.card_fun Fintype.card_fun

@[simp]
theorem card_vector [Fintype α] (n : ℕ) : Fintype.card (Vector α n) = Fintype.card α ^ n := by
  rw [Fintype.ofEquiv_card]; simp
#align card_vector card_vector

/-- It is equivalent to compute the product of a function over `Fin n` or `Finset.range n`. -/
@[to_additive "It is equivalent to sum a function over `fin n` or `finset.range n`."]
theorem Fin.prod_univ_eq_prod_range [CommMonoid α] (f : ℕ → α) (n : ℕ) :
    ∏ i : Fin n, f i = ∏ i in range n, f i :=
  calc
    ∏ i : Fin n, f i = ∏ i : { x // x ∈ range n }, f i :=
      Fintype.prod_equiv (Fin.equivSubtype.trans (Equiv.subtypeEquivRight (by simp))) _ _ (by simp)
    _ = ∏ i in range n, f i := by rw [← attach_eq_univ, prod_attach]
#align fin.prod_univ_eq_prod_range Fin.prod_univ_eq_prod_range
#align fin.sum_univ_eq_sum_range Fin.sum_univ_eq_sum_range

@[to_additive]
theorem Finset.prod_fin_eq_prod_range [CommMonoid β] {n : ℕ} (c : Fin n → β) :
    ∏ i, c i = ∏ i in Finset.range n, if h : i < n then c ⟨i, h⟩ else 1 := by
  rw [← Fin.prod_univ_eq_prod_range, Finset.prod_congr rfl]
  rintro ⟨i, hi⟩ _
  simp only [hi, dif_pos]
#align finset.prod_fin_eq_prod_range Finset.prod_fin_eq_prod_range
#align finset.sum_fin_eq_sum_range Finset.sum_fin_eq_sum_range

@[to_additive]
theorem Finset.prod_toFinset_eq_subtype {M : Type*} [CommMonoid M] [Fintype α] (p : α → Prop)
    [DecidablePred p] (f : α → M) : ∏ a in { x | p x }.toFinset, f a = ∏ a : Subtype p, f a := by
  rw [← Finset.prod_subtype]
  simp_rw [Set.mem_toFinset]; intro; rfl
#align finset.prod_to_finset_eq_subtype Finset.prod_toFinset_eq_subtype
#align finset.sum_to_finset_eq_subtype Finset.sum_toFinset_eq_subtype

nonrec theorem Fintype.prod_dite [Fintype α] {p : α → Prop} [DecidablePred p] [CommMonoid β]
    (f : ∀ a, p a → β) (g : ∀ a, ¬p a → β) :
    (∏ a, dite (p a) (f a) (g a)) =
    (∏ a : { a // p a }, f a a.2) * ∏ a : { a // ¬p a }, g a a.2 := by
  simp only [prod_dite, attach_eq_univ]
  congr 1
  · exact (Equiv.subtypeEquivRight <| by simp).prod_comp fun x : { x // p x } => f x x.2
  · exact (Equiv.subtypeEquivRight <| by simp).prod_comp fun x : { x // ¬p x } => g x x.2
#align fintype.prod_dite Fintype.prod_dite

section

open Finset

variable {α₁ : Type*} {α₂ : Type*} {M : Type*} [Fintype α₁] [Fintype α₂] [CommMonoid M]

@[to_additive]
theorem Fintype.prod_sum_elim (f : α₁ → M) (g : α₂ → M) :
    ∏ x, Sum.elim f g x = (∏ a₁, f a₁) * ∏ a₂, g a₂ :=
  prod_disj_sum _ _ _
#align fintype.prod_sum_elim Fintype.prod_sum_elim
#align fintype.sum_sum_elim Fintype.sum_sum_elim

@[to_additive (attr := simp)]
theorem Fintype.prod_sum_type (f : Sum α₁ α₂ → M) :
    ∏ x, f x = (∏ a₁, f (Sum.inl a₁)) * ∏ a₂, f (Sum.inr a₂) :=
  prod_disj_sum _ _ _
#align fintype.prod_sum_type Fintype.prod_sum_type
#align fintype.sum_sum_type Fintype.sum_sum_type

@[to_additive (attr := simp) Fintype.sum_prod_type]
theorem Fintype.prod_prod_type [CommMonoid γ] {f : α₁ × α₂ → γ} :
    ∏ x, f x = ∏ x, ∏ y, f (x, y) :=
  Finset.prod_product

/-- An uncurried version of `Finset.prod_prod_type`. -/
@[to_additive Fintype.sum_prod_type' "An uncurried version of `Finset.sum_prod_type`"]
theorem Fintype.prod_prod_type' [CommMonoid γ] {f : α₁ → α₂ → γ} :
    ∏ x : α₁ × α₂, f x.1 x.2 = ∏ x, ∏ y, f x y :=
  Finset.prod_product'

@[to_additive Fintype.sum_prod_type_right]
theorem Fintype.prod_prod_type_right [CommMonoid γ] {f : α₁ × α₂ → γ} :
    ∏ x, f x = ∏ y, ∏ x, f (x, y) :=
  Finset.prod_product_right

/-- An uncurried version of `Finset.prod_prod_type_right`. -/
@[to_additive Fintype.sum_prod_type_right' "An uncurried version of `Finset.sum_prod_type_right`"]
theorem Fintype.prod_prod_type_right' [CommMonoid γ] {f : α₁ → α₂ → γ} :
    ∏ x : α₁ × α₂, f x.1 x.2 = ∏ y, ∏ x, f x y :=
  Finset.prod_product_right'

end
