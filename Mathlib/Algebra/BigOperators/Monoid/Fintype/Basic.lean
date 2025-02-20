/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.BigOperators.Monoid.Finset.Basic

/-!
# Big operators

In this file we prove lemmas about products and sums indexed by finite types
(specifically, `Fintype`).

## Implementation Notes

The first arguments in all definitions and lemmas is the codomain of the function of the big
operator. This is necessary for the heuristic in `@[to_additive]`.
See the documentation of `to_additive.attr` for more information.

-/

-- TODO
-- assert_not_exists AddCommMonoidWithOne
assert_not_exists MonoidWithZero MulAction OrderedCommMonoid

variable {ι κ α β γ : Type*}

open Fin Function

namespace Finset

variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}


end Finset


variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}

namespace Finset

section CommMonoid

variable [CommMonoid β]


end CommMonoid

end Finset

section

open Finset

variable [Fintype α] [CommMonoid β]

@[to_additive]
theorem IsCompl.prod_mul_prod {s t : Finset α} (h : IsCompl s t) (f : α → β) :
    (∏ i ∈ s, f i) * ∏ i ∈ t, f i = ∏ i, f i :=
  (Finset.prod_disjUnion h.disjoint).symm.trans <| by
    classical rw [Finset.disjUnion_eq_union, ← Finset.sup_eq_union, h.sup_eq_top]; rfl

end

namespace Finset

section CommMonoid

variable [CommMonoid β]

/-- Multiplying the products of a function over `s` and over `sᶜ` gives the whole product.
For a version expressed with subtypes, see `Fintype.prod_subtype_mul_prod_subtype`. -/
@[to_additive "Adding the sums of a function over `s` and over `sᶜ` gives the whole sum.
For a version expressed with subtypes, see `Fintype.sum_subtype_add_sum_subtype`. "]
theorem prod_mul_prod_compl [Fintype α] [DecidableEq α] (s : Finset α) (f : α → β) :
    (∏ i ∈ s, f i) * ∏ i ∈ sᶜ, f i = ∏ i, f i :=
  IsCompl.prod_mul_prod isCompl_compl f

@[to_additive]
theorem prod_compl_mul_prod [Fintype α] [DecidableEq α] (s : Finset α) (f : α → β) :
    (∏ i ∈ sᶜ, f i) * ∏ i ∈ s, f i = ∏ i, f i :=
  (@isCompl_compl _ s _).symm.prod_mul_prod f


section bij
variable {ι κ α : Type*} [CommMonoid α] {s : Finset ι} {t : Finset κ} {f : ι → α} {g : κ → α}

variable [DecidableEq κ]


variable [Fintype κ]

@[to_additive]
lemma prod_fiberwise (s : Finset ι) (g : ι → κ) (f : ι → α) :
    ∏ j, ∏ i ∈ s with g i = j, f i = ∏ i ∈ s, f i :=
  prod_fiberwise_of_maps_to (fun _ _ ↦ mem_univ _) _

@[to_additive]
lemma prod_fiberwise' (s : Finset ι) (g : ι → κ) (f : κ → α) :
    ∏ j, ∏ i ∈ s with g i = j, f j = ∏ i ∈ s, f (g i) :=
  prod_fiberwise_of_maps_to' (fun _ _ ↦ mem_univ _) _

end bij

variable (f s)

variable {f s}

@[to_additive]
theorem prod_subtype {p : α → Prop} {F : Fintype (Subtype p)} (s : Finset α) (h : ∀ x, x ∈ s ↔ p x)
    (f : α → β) : ∏ a ∈ s, f a = ∏ a : Subtype p, f a := by
  have : (· ∈ s) = p := Set.ext h
  subst p
  rw [← prod_coe_sort]
  congr!

@[to_additive]
theorem prod_set_coe (s : Set α) [Fintype s] : (∏ i : s, f i) = ∏ i ∈ s.toFinset, f i :=
(Finset.prod_subtype s.toFinset (fun _ ↦ Set.mem_toFinset) f).symm

/-- The product of a function `g` defined only on a set `s` is equal to
the product of a function `f` defined everywhere,
as long as `f` and `g` agree on `s`, and `f = 1` off `s`. -/
@[to_additive "The sum of a function `g` defined only on a set `s` is equal to
the sum of a function `f` defined everywhere,
as long as `f` and `g` agree on `s`, and `f = 0` off `s`."]
theorem prod_congr_set {α : Type*} [CommMonoid α] {β : Type*} [Fintype β] (s : Set β)
    [DecidablePred (· ∈ s)] (f : β → α) (g : s → α) (w : ∀ (x : β) (h : x ∈ s), f x = g ⟨x, h⟩)
    (w' : ∀ x : β, x ∉ s → f x = 1) : Finset.univ.prod f = Finset.univ.prod g := by
  rw [← @Finset.prod_subset _ _ s.toFinset Finset.univ f _ (by simp)]
  · rw [Finset.prod_subtype]
    · apply Finset.prod_congr rfl
      exact fun ⟨x, h⟩ _ => w x h
    · simp
  · rintro x _ h
    exact w' x (by simpa using h)

@[to_additive]
lemma prod_attach_eq_prod_dite [Fintype α] (s : Finset α) (f : s → β) [DecidablePred (· ∈ s)] :
    ∏ i ∈ s.attach, f i = ∏ i, if h : i ∈ s then f ⟨i, h⟩ else 1 := by
  rw [Finset.prod_dite, Finset.univ_eq_attach, Finset.prod_const_one, mul_one]
  congr
  · ext; simp
  · ext; simp
  · apply Function.hfunext <;> simp +contextual [Subtype.heq_iff_coe_eq]

open List

open Multiset

@[to_additive]
theorem _root_.Fintype.prod_eq_mul_prod_compl [DecidableEq α] [Fintype α] (a : α) (f : α → β) :
    ∏ i, f i = f a * ∏ i ∈ {a}ᶜ, f i :=
  prod_eq_mul_prod_diff_singleton (mem_univ a) f

@[to_additive]
theorem _root_.Fintype.prod_eq_prod_compl_mul [DecidableEq α] [Fintype α] (a : α) (f : α → β) :
    ∏ i, f i = (∏ i ∈ {a}ᶜ, f i) * f a :=
  prod_eq_prod_diff_singleton_mul (mem_univ a) f

end CommMonoid

end Finset

namespace Fintype
variable {ι κ α : Type*} [Fintype ι] [Fintype κ]

open Finset

section CommMonoid
variable [CommMonoid α]

@[to_additive]
lemma prod_of_injective (e : ι → κ) (he : Injective e) (f : ι → α) (g : κ → α)
    (h' : ∀ i ∉ Set.range e, g i = 1) (h : ∀ i, f i = g (e i)) : ∏ i, f i = ∏ j, g j :=
  prod_of_injOn e he.injOn (by simp) (by simpa using h') (fun i _ ↦ h i)

@[to_additive]
lemma prod_fiberwise [DecidableEq κ] (g : ι → κ) (f : ι → α) :
    ∏ j, ∏ i : {i // g i = j}, f i = ∏ i, f i := by
  rw [← Finset.prod_fiberwise _ g f]
  congr with j
  exact (prod_subtype _ (by simp) _).symm

@[to_additive]
lemma prod_fiberwise' [DecidableEq κ] (g : ι → κ) (f : κ → α) :
    ∏ j, ∏ _i : {i // g i = j}, f j = ∏ i, f (g i) := by
  rw [← Finset.prod_fiberwise' _ g f]
  congr with j
  exact (prod_subtype _ (by simp) fun _ ↦ _).symm

@[to_additive]
theorem prod_unique {α β : Type*} [CommMonoid β] [Unique α] [Fintype α] (f : α → β) :
    ∏ x : α, f x = f default := by rw [univ_unique, prod_singleton]

@[to_additive]
theorem prod_subsingleton {α β : Type*} [CommMonoid β] [Subsingleton α] [Fintype α] (f : α → β)
    (a : α) : ∏ x : α, f x = f a := by
  have : Unique α := uniqueOfSubsingleton a
  rw [prod_unique f, Subsingleton.elim default a]

@[to_additive] theorem prod_Prop {β} [CommMonoid β] (f : Prop → β) :
    ∏ p, f p = f True * f False := by simp

@[to_additive]
theorem prod_subtype_mul_prod_subtype {α β : Type*} [Fintype α] [CommMonoid β] (p : α → Prop)
    (f : α → β) [DecidablePred p] :
    (∏ i : { x // p x }, f i) * ∏ i : { x // ¬p x }, f i = ∏ i, f i := by
  classical
    let s := { x | p x }.toFinset
    rw [← Finset.prod_subtype s, ← Finset.prod_subtype sᶜ]
    · exact Finset.prod_mul_prod_compl _ _
    · simp [s]
    · simp [s]

@[to_additive] lemma prod_subset {s : Finset ι} {f : ι → α} (h : ∀ i, f i ≠ 1 → i ∈ s) :
    ∏ i ∈ s, f i = ∏ i, f i :=
  Finset.prod_subset s.subset_univ <| by simpa [not_imp_comm (a := _ ∈ s)]

@[to_additive]
lemma prod_ite_eq_ite_exists (p : ι → Prop) [DecidablePred p] (h : ∀ i j, p i → p j → i = j)
    (a : α) : ∏ i, ite (p i) a 1 = ite (∃ i, p i) a 1 := by
  simp [prod_ite_one univ p (by simpa using h)]

variable [DecidableEq ι]

@[to_additive]
lemma prod_ite_mem (s : Finset ι) (f : ι → α) : ∏ i, (if i ∈ s then f i else 1) = ∏ i ∈ s, f i := by
  simp

/-- See also `Finset.prod_dite_eq`. -/
@[to_additive "See also `Finset.sum_dite_eq`."] lemma prod_dite_eq (i : ι) (f : ∀ j, i = j → α) :
    ∏ j, (if h : i = j then f j h else 1) = f i rfl := by
  rw [Finset.prod_dite_eq, if_pos (mem_univ _)]

/-- See also `Finset.prod_dite_eq'`. -/
@[to_additive "See also `Finset.sum_dite_eq'`."] lemma prod_dite_eq' (i : ι) (f : ∀ j, j = i → α) :
    ∏ j, (if h : j = i then f j h else 1) = f i rfl := by
  rw [Finset.prod_dite_eq', if_pos (mem_univ _)]

/-- See also `Finset.prod_ite_eq`. -/
@[to_additive "See also `Finset.sum_ite_eq`."]
lemma prod_ite_eq (i : ι) (f : ι → α) : ∏ j, (if i = j then f j else 1) = f i := by
  rw [Finset.prod_ite_eq, if_pos (mem_univ _)]

/-- See also `Finset.prod_ite_eq'`. -/
@[to_additive "See also `Finset.sum_ite_eq'`."]
lemma prod_ite_eq' (i : ι) (f : ι → α) : ∏ j, (if j = i then f j else 1) = f i := by
  rw [Finset.prod_ite_eq', if_pos (mem_univ _)]

/-- See also `Finset.prod_pi_mulSingle`. -/
@[to_additive "See also `Finset.sum_pi_single`."]
lemma prod_pi_mulSingle {α : ι → Type*} [∀ i, CommMonoid (α i)] (i : ι) (f : ∀ i, α i) :
    ∏ j, Pi.mulSingle j (f j) i = f i := prod_dite_eq _ _

/-- See also `Finset.prod_pi_mulSingle'`. -/
@[to_additive "See also `Finset.sum_pi_single'`."]
lemma prod_pi_mulSingle' (i : ι) (a : α) : ∏ j, Pi.mulSingle i a j = a := prod_dite_eq' _ _

end CommMonoid
end Fintype
