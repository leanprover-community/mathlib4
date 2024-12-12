/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Image.Basic

/-! # Subtypes of finsets

## Main definitions

* `Finset.subtype`: `s.subtype p` is the finset of `Subtype p` whose elements belong to `s`.
* `Finset.fin`:`s.fin n` is the finset of all elements of `s` less than `n`.

-/
-- set_option linter.minImports true
assert_not_exists OrderedCommMonoid
assert_not_exists MonoidWithZero
assert_not_exists MulAction

variable {α β γ : Type*}

open Multiset

open Function

namespace Finset

/-! ### Subtype -/

section Subtype

/-- Given a finset `s` and a predicate `p`, `s.subtype p` is the finset of `Subtype p` whose
elements belong to `s`. -/
protected def subtype {α} (p : α → Prop) [DecidablePred p] (s : Finset α) : Finset (Subtype p) :=
  (s.filter p).attach.map
    ⟨fun x => ⟨x.1, by simpa using (Finset.mem_filter.1 x.2).2⟩,
     fun _ _ H => Subtype.eq <| Subtype.mk.inj H⟩

@[simp]
theorem mem_subtype {p : α → Prop} [DecidablePred p] {s : Finset α} :
    ∀ {a : Subtype p}, a ∈ s.subtype p ↔ (a : α) ∈ s
  | ⟨a, ha⟩ => by simp [Finset.subtype, ha]

theorem subtype_eq_empty {p : α → Prop} [DecidablePred p] {s : Finset α} :
    s.subtype p = ∅ ↔ ∀ x, p x → x ∉ s := by simp [Finset.ext_iff, Subtype.forall, Subtype.coe_mk]

@[mono]
theorem subtype_mono {p : α → Prop} [DecidablePred p] : Monotone (Finset.subtype p) :=
  fun _ _ h _ hx => mem_subtype.2 <| h <| mem_subtype.1 hx

/-- `s.subtype p` converts back to `s.filter p` with
`Embedding.subtype`. -/
@[simp]
theorem subtype_map (p : α → Prop) [DecidablePred p] {s : Finset α} :
    (s.subtype p).map (Embedding.subtype _) = s.filter p := by
  ext x
  simp [@and_comm _ (_ = _), @and_left_comm _ (_ = _), @and_comm (p x) (x ∈ s)]

/-- If all elements of a `Finset` satisfy the predicate `p`,
`s.subtype p` converts back to `s` with `Embedding.subtype`. -/
theorem subtype_map_of_mem {p : α → Prop} [DecidablePred p] {s : Finset α} (h : ∀ x ∈ s, p x) :
    (s.subtype p).map (Embedding.subtype _) = s := ext <| by simpa [subtype_map] using h

/-- If a `Finset` of a subtype is converted to the main type with
`Embedding.subtype`, all elements of the result have the property of
the subtype. -/
theorem property_of_mem_map_subtype {p : α → Prop} (s : Finset { x // p x }) {a : α}
    (h : a ∈ s.map (Embedding.subtype _)) : p a := by
  rcases mem_map.1 h with ⟨x, _, rfl⟩
  exact x.2

/-- If a `Finset` of a subtype is converted to the main type with
`Embedding.subtype`, the result does not contain any value that does
not satisfy the property of the subtype. -/
theorem not_mem_map_subtype_of_not_property {p : α → Prop} (s : Finset { x // p x }) {a : α}
    (h : ¬p a) : a ∉ s.map (Embedding.subtype _) :=
  mt s.property_of_mem_map_subtype h

/-- If a `Finset` of a subtype is converted to the main type with
`Embedding.subtype`, the result is a subset of the set giving the
subtype. -/
theorem map_subtype_subset {t : Set α} (s : Finset t) : ↑(s.map (Embedding.subtype _)) ⊆ t := by
  intro a ha
  rw [mem_coe] at ha
  convert property_of_mem_map_subtype s ha

end Subtype

/-! ### Fin -/


/-- Given a finset `s` of natural numbers and a bound `n`,
`s.fin n` is the finset of all elements of `s` less than `n`.
-/
protected def fin (n : ℕ) (s : Finset ℕ) : Finset (Fin n) :=
  (s.subtype _).map Fin.equivSubtype.symm.toEmbedding

@[simp]
theorem mem_fin {n} {s : Finset ℕ} : ∀ a : Fin n, a ∈ s.fin n ↔ (a : ℕ) ∈ s
  | ⟨a, ha⟩ => by simp [Finset.fin, ha, and_comm]

@[mono]
theorem fin_mono {n} : Monotone (Finset.fin n) := fun s t h x => by simpa using @h x

@[simp]
theorem fin_map {n} {s : Finset ℕ} : (s.fin n).map Fin.valEmbedding = s.filter (· < n) := by
  simp [Finset.fin, Finset.map_map]

/--
If a finset `t` is a subset of the image of another finset `s` under `f`, then it is equal to the
image of a subset of `s`.

For the version where `s` is a set, see `subset_set_image_iff`.
-/
theorem subset_image_iff [DecidableEq β] {s : Finset α} {t : Finset β} {f : α → β} :
    t ⊆ s.image f ↔ ∃ s' : Finset α, s' ⊆ s ∧ s'.image f = t := by
  refine ⟨fun ht => ?_, fun ⟨s', hs', h⟩ => h ▸ image_subset_image hs'⟩
  refine ⟨s.filter (f · ∈ t), filter_subset _ _, le_antisymm (by simp [image_subset_iff]) ?_⟩
  intro x hx
  specialize ht hx
  aesop

/-- If a `Finset` is a subset of the image of a `Set` under `f`,
then it is equal to the `Finset.image` of a `Finset` subset of that `Set`. -/
theorem subset_set_image_iff [DecidableEq β] {s : Set α} {t : Finset β} {f : α → β} :
    ↑t ⊆ f '' s ↔ ∃ s' : Finset α, ↑s' ⊆ s ∧ s'.image f = t := by
  constructor; swap
  · rintro ⟨t, ht, rfl⟩
    rw [coe_image]
    exact Set.image_subset f ht
  intro h
  letI : CanLift β s (f ∘ (↑)) fun y => y ∈ f '' s := ⟨fun y ⟨x, hxt, hy⟩ => ⟨⟨x, hxt⟩, hy⟩⟩
  lift t to Finset s using h
  refine ⟨t.map (Embedding.subtype _), map_subtype_subset _, ?_⟩
  ext y; simp

theorem range_sdiff_zero {n : ℕ} : range (n + 1) \ {0} = (range n).image Nat.succ := by
  induction' n with k hk
  · simp
  conv_rhs => rw [range_succ]
  rw [range_succ, image_insert, ← hk, insert_sdiff_of_not_mem]
  simp

end Finset
