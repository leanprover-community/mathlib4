/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Finset.Image
import Mathlib.Data.List.FinRange

#align_import data.fintype.basic from "leanprover-community/mathlib"@"d78597269638367c3863d40d45108f52207e03cf"

/-!
# Finite types

This file defines a typeclass to state that a type is finite.

## Main declarations

* `Fintype α`:  Typeclass saying that a type is finite. It takes as fields a `Finset` and a proof
  that all terms of type `α` are in it.
* `Finset.univ`: The finset of all elements of a fintype.

See `Data.Fintype.Card` for the cardinality of a fintype,
the equivalence with `Fin (Fintype.card α)`, and pigeonhole principles.

## Instances

Instances for `Fintype` for
* `{x // p x}` are in this file as `Fintype.subtype`
* `Option α` are in `Data.Fintype.Option`
* `α × β` are in `Data.Fintype.Prod`
* `α ⊕ β` are in `Data.Fintype.Sum`
* `Σ (a : α), β a` are in `Data.Fintype.Sigma`

These files also contain appropriate `Infinite` instances for these types.

`Infinite` instances for `ℕ`, `ℤ`, `Multiset α`, and `List α` are in `Data.Fintype.Lattice`.

Types which have a surjection from/an injection to a `Fintype` are themselves fintypes.
See `Fintype.ofInjective` and `Fintype.ofSurjective`.
-/

assert_not_exists MonoidWithZero
assert_not_exists MulAction

open Function

open Nat

universe u v

variable {α β γ : Type*}

/-- `Fintype α` means that `α` is finite, i.e. there are only
  finitely many distinct elements of type `α`. The evidence of this
  is a finset `elems` (a list up to permutation without duplicates),
  together with a proof that everything of type `α` is in the list. -/
class Fintype (α : Type*) where
  /-- The `Finset` containing all elements of a `Fintype` -/
  elems : Finset α
  /-- A proof that `elems` contains every element of the type -/
  complete : ∀ x : α, x ∈ elems
#align fintype Fintype

namespace Finset

variable [Fintype α] {s t : Finset α}

/-- `univ` is the universal finite set of type `Finset α` implied from
  the assumption `Fintype α`. -/
def univ : Finset α :=
  @Fintype.elems α _
#align finset.univ Finset.univ

@[simp]
theorem mem_univ (x : α) : x ∈ (univ : Finset α) :=
  Fintype.complete x
#align finset.mem_univ Finset.mem_univ

-- Porting note: removing @[simp], simp can prove it
theorem mem_univ_val : ∀ x, x ∈ (univ : Finset α).1 :=
  mem_univ
#align finset.mem_univ_val Finset.mem_univ_val

theorem eq_univ_iff_forall : s = univ ↔ ∀ x, x ∈ s := by simp [ext_iff]
#align finset.eq_univ_iff_forall Finset.eq_univ_iff_forall

theorem eq_univ_of_forall : (∀ x, x ∈ s) → s = univ :=
  eq_univ_iff_forall.2
#align finset.eq_univ_of_forall Finset.eq_univ_of_forall

@[simp, norm_cast]
theorem coe_univ : ↑(univ : Finset α) = (Set.univ : Set α) := by ext; simp
#align finset.coe_univ Finset.coe_univ

@[simp, norm_cast]
theorem coe_eq_univ : (s : Set α) = Set.univ ↔ s = univ := by rw [← coe_univ, coe_inj]
#align finset.coe_eq_univ Finset.coe_eq_univ

theorem Nonempty.eq_univ [Subsingleton α] : s.Nonempty → s = univ := by
  rintro ⟨x, hx⟩
  exact eq_univ_of_forall fun y => by rwa [Subsingleton.elim y x]
#align finset.nonempty.eq_univ Finset.Nonempty.eq_univ

theorem univ_nonempty_iff : (univ : Finset α).Nonempty ↔ Nonempty α := by
  rw [← coe_nonempty, coe_univ, Set.nonempty_iff_univ_nonempty]
#align finset.univ_nonempty_iff Finset.univ_nonempty_iff

@[aesop unsafe apply (rule_sets := [finsetNonempty])]
theorem univ_nonempty [Nonempty α] : (univ : Finset α).Nonempty :=
  univ_nonempty_iff.2 ‹_›
#align finset.univ_nonempty Finset.univ_nonempty

theorem univ_eq_empty_iff : (univ : Finset α) = ∅ ↔ IsEmpty α := by
  rw [← not_nonempty_iff, ← univ_nonempty_iff, not_nonempty_iff_eq_empty]
#align finset.univ_eq_empty_iff Finset.univ_eq_empty_iff

@[simp]
theorem univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅ :=
  univ_eq_empty_iff.2 ‹_›
#align finset.univ_eq_empty Finset.univ_eq_empty

@[simp]
theorem univ_unique [Unique α] : (univ : Finset α) = {default} :=
  Finset.ext fun x => iff_of_true (mem_univ _) <| mem_singleton.2 <| Subsingleton.elim x default
#align finset.univ_unique Finset.univ_unique

@[simp]
theorem subset_univ (s : Finset α) : s ⊆ univ := fun a _ => mem_univ a
#align finset.subset_univ Finset.subset_univ

instance boundedOrder : BoundedOrder (Finset α) :=
  { inferInstanceAs (OrderBot (Finset α)) with
    top := univ
    le_top := subset_univ }
#align finset.bounded_order Finset.boundedOrder

@[simp]
theorem top_eq_univ : (⊤ : Finset α) = univ :=
  rfl
#align finset.top_eq_univ Finset.top_eq_univ

theorem ssubset_univ_iff {s : Finset α} : s ⊂ univ ↔ s ≠ univ :=
  @lt_top_iff_ne_top _ _ _ s
#align finset.ssubset_univ_iff Finset.ssubset_univ_iff

@[simp]
theorem univ_subset_iff {s : Finset α} : univ ⊆ s ↔ s = univ :=
  @top_le_iff _ _ _ s

theorem codisjoint_left : Codisjoint s t ↔ ∀ ⦃a⦄, a ∉ s → a ∈ t := by
  classical simp [codisjoint_iff, eq_univ_iff_forall, or_iff_not_imp_left]
#align finset.codisjoint_left Finset.codisjoint_left

theorem codisjoint_right : Codisjoint s t ↔ ∀ ⦃a⦄, a ∉ t → a ∈ s :=
  Codisjoint_comm.trans codisjoint_left
#align finset.codisjoint_right Finset.codisjoint_right

section BooleanAlgebra

variable [DecidableEq α] {a : α}

instance booleanAlgebra : BooleanAlgebra (Finset α) :=
  GeneralizedBooleanAlgebra.toBooleanAlgebra
#align finset.boolean_algebra Finset.booleanAlgebra

theorem sdiff_eq_inter_compl (s t : Finset α) : s \ t = s ∩ tᶜ :=
  sdiff_eq
#align finset.sdiff_eq_inter_compl Finset.sdiff_eq_inter_compl

theorem compl_eq_univ_sdiff (s : Finset α) : sᶜ = univ \ s :=
  rfl
#align finset.compl_eq_univ_sdiff Finset.compl_eq_univ_sdiff

@[simp]
theorem mem_compl : a ∈ sᶜ ↔ a ∉ s := by simp [compl_eq_univ_sdiff]
#align finset.mem_compl Finset.mem_compl

theorem not_mem_compl : a ∉ sᶜ ↔ a ∈ s := by rw [mem_compl, not_not]
#align finset.not_mem_compl Finset.not_mem_compl

@[simp, norm_cast]
theorem coe_compl (s : Finset α) : ↑sᶜ = (↑s : Set α)ᶜ :=
  Set.ext fun _ => mem_compl
#align finset.coe_compl Finset.coe_compl

@[simp] lemma compl_subset_compl : sᶜ ⊆ tᶜ ↔ t ⊆ s := @compl_le_compl_iff_le (Finset α) _ _ _
@[simp] lemma compl_ssubset_compl : sᶜ ⊂ tᶜ ↔ t ⊂ s := @compl_lt_compl_iff_lt (Finset α) _ _ _

lemma subset_compl_comm : s ⊆ tᶜ ↔ t ⊆ sᶜ := le_compl_iff_le_compl (α := Finset α)

@[simp] lemma subset_compl_singleton : s ⊆ {a}ᶜ ↔ a ∉ s := by
  rw [subset_compl_comm, singleton_subset_iff, mem_compl]

@[simp]
theorem compl_empty : (∅ : Finset α)ᶜ = univ :=
  compl_bot
#align finset.compl_empty Finset.compl_empty

@[simp]
theorem compl_univ : (univ : Finset α)ᶜ = ∅ :=
  compl_top
#align finset.compl_univ Finset.compl_univ

@[simp]
theorem compl_eq_empty_iff (s : Finset α) : sᶜ = ∅ ↔ s = univ :=
  compl_eq_bot
#align finset.compl_eq_empty_iff Finset.compl_eq_empty_iff

@[simp]
theorem compl_eq_univ_iff (s : Finset α) : sᶜ = univ ↔ s = ∅ :=
  compl_eq_top
#align finset.compl_eq_univ_iff Finset.compl_eq_univ_iff

@[simp]
theorem union_compl (s : Finset α) : s ∪ sᶜ = univ :=
  sup_compl_eq_top
#align finset.union_compl Finset.union_compl

@[simp]
theorem inter_compl (s : Finset α) : s ∩ sᶜ = ∅ :=
  inf_compl_eq_bot
#align finset.inter_compl Finset.inter_compl

@[simp]
theorem compl_union (s t : Finset α) : (s ∪ t)ᶜ = sᶜ ∩ tᶜ :=
  compl_sup
#align finset.compl_union Finset.compl_union

@[simp]
theorem compl_inter (s t : Finset α) : (s ∩ t)ᶜ = sᶜ ∪ tᶜ :=
  compl_inf
#align finset.compl_inter Finset.compl_inter

@[simp]
theorem compl_erase : (s.erase a)ᶜ = insert a sᶜ := by
  ext
  simp only [or_iff_not_imp_left, mem_insert, not_and, mem_compl, mem_erase]
#align finset.compl_erase Finset.compl_erase

@[simp]
theorem compl_insert : (insert a s)ᶜ = sᶜ.erase a := by
  ext
  simp only [not_or, mem_insert, iff_self_iff, mem_compl, mem_erase]
#align finset.compl_insert Finset.compl_insert

theorem insert_compl_insert (ha : a ∉ s) : insert a (insert a s)ᶜ = sᶜ := by
  simp_rw [compl_insert, insert_erase (mem_compl.2 ha)]

@[simp]
theorem insert_compl_self (x : α) : insert x ({x}ᶜ : Finset α) = univ := by
  rw [← compl_erase, erase_singleton, compl_empty]
#align finset.insert_compl_self Finset.insert_compl_self

@[simp]
theorem compl_filter (p : α → Prop) [DecidablePred p] [∀ x, Decidable ¬p x] :
    (univ.filter p)ᶜ = univ.filter fun x => ¬p x :=
  ext <| by simp
#align finset.compl_filter Finset.compl_filter

theorem compl_ne_univ_iff_nonempty (s : Finset α) : sᶜ ≠ univ ↔ s.Nonempty := by
  simp [eq_univ_iff_forall, Finset.Nonempty]
#align finset.compl_ne_univ_iff_nonempty Finset.compl_ne_univ_iff_nonempty

theorem compl_singleton (a : α) : ({a} : Finset α)ᶜ = univ.erase a := by
  rw [compl_eq_univ_sdiff, sdiff_singleton_eq_erase]
#align finset.compl_singleton Finset.compl_singleton

theorem insert_inj_on' (s : Finset α) : Set.InjOn (fun a => insert a s) (sᶜ : Finset α) := by
  rw [coe_compl]
  exact s.insert_inj_on
#align finset.insert_inj_on' Finset.insert_inj_on'

theorem image_univ_of_surjective [Fintype β] {f : β → α} (hf : Surjective f) :
    univ.image f = univ :=
  eq_univ_of_forall <| hf.forall.2 fun _ => mem_image_of_mem _ <| mem_univ _
#align finset.image_univ_of_surjective Finset.image_univ_of_surjective

@[simp]
theorem image_univ_equiv [Fintype β] (f : β ≃ α) : univ.image f = univ :=
  Finset.image_univ_of_surjective f.surjective

@[simp] lemma univ_inter (s : Finset α) : univ ∩ s = s := by ext a; simp
#align finset.univ_inter Finset.univ_inter

@[simp] lemma inter_univ (s : Finset α) : s ∩ univ = s := by rw [inter_comm, univ_inter]
#align finset.inter_univ Finset.inter_univ

@[simp] lemma inter_eq_univ : s ∩ t = univ ↔ s = univ ∧ t = univ := inf_eq_top_iff

end BooleanAlgebra

-- @[simp] --Note this would loop with `Finset.univ_unique`
lemma singleton_eq_univ [Subsingleton α] (a : α) : ({a} : Finset α) = univ := by
  ext b; simp [Subsingleton.elim a b]


theorem map_univ_of_surjective [Fintype β] {f : β ↪ α} (hf : Surjective f) : univ.map f = univ :=
  eq_univ_of_forall <| hf.forall.2 fun _ => mem_map_of_mem _ <| mem_univ _
#align finset.map_univ_of_surjective Finset.map_univ_of_surjective

@[simp]
theorem map_univ_equiv [Fintype β] (f : β ≃ α) : univ.map f.toEmbedding = univ :=
  map_univ_of_surjective f.surjective
#align finset.map_univ_equiv Finset.map_univ_equiv

theorem univ_map_equiv_to_embedding {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) :
    univ.map e.toEmbedding = univ :=
  eq_univ_iff_forall.mpr fun b => mem_map.mpr ⟨e.symm b, mem_univ _, by simp⟩
#align finset.univ_map_equiv_to_embedding Finset.univ_map_equiv_to_embedding

@[simp]
theorem univ_filter_exists (f : α → β) [Fintype β] [DecidablePred fun y => ∃ x, f x = y]
    [DecidableEq β] : (Finset.univ.filter fun y => ∃ x, f x = y) = Finset.univ.image f := by
  ext
  simp
#align finset.univ_filter_exists Finset.univ_filter_exists

/-- Note this is a special case of `(Finset.image_preimage f univ _).symm`. -/
theorem univ_filter_mem_range (f : α → β) [Fintype β] [DecidablePred fun y => y ∈ Set.range f]
    [DecidableEq β] : (Finset.univ.filter fun y => y ∈ Set.range f) = Finset.univ.image f := by
  letI : DecidablePred (fun y => ∃ x, f x = y) := by simpa using ‹_›
  exact univ_filter_exists f
#align finset.univ_filter_mem_range Finset.univ_filter_mem_range

theorem coe_filter_univ (p : α → Prop) [DecidablePred p] :
    (univ.filter p : Set α) = { x | p x } := by simp
#align finset.coe_filter_univ Finset.coe_filter_univ

@[simp] lemma subtype_eq_univ {p : α → Prop} [DecidablePred p] [Fintype {a // p a}] :
    s.subtype p = univ ↔ ∀ ⦃a⦄, p a → a ∈ s := by simp [ext_iff]

@[simp] lemma subtype_univ [Fintype α] (p : α → Prop) [DecidablePred p] [Fintype {a // p a}] :
    univ.subtype p = univ := by simp

lemma univ_map_subtype [Fintype α] (p : α → Prop) [DecidablePred p] [Fintype {a // p a}] :
    univ.map (Function.Embedding.subtype p) = univ.filter p := by
  rw [← subtype_map, subtype_univ]

lemma univ_val_map_subtype_val [Fintype α] (p : α → Prop) [DecidablePred p] [Fintype {a // p a}] :
    univ.val.map ((↑) : { a // p a } → α) = (univ.filter p).val := by
  apply (map_val (Function.Embedding.subtype p) univ).symm.trans
  apply congr_arg
  apply univ_map_subtype

lemma univ_val_map_subtype_restrict [Fintype α] (f : α → β)
    (p : α → Prop) [DecidablePred p] [Fintype {a // p a}] :
    univ.val.map (Subtype.restrict p f) = (univ.filter p).val.map f := by
  rw [← univ_val_map_subtype_val, Multiset.map_map, Subtype.restrict_def]

end Finset

open Finset Function

namespace Fintype

instance decidablePiFintype {α} {β : α → Type*} [∀ a, DecidableEq (β a)] [Fintype α] :
    DecidableEq (∀ a, β a) := fun f g =>
  decidable_of_iff (∀ a ∈ @Fintype.elems α _, f a = g a)
    (by simp [Function.funext_iff, Fintype.complete])
#align fintype.decidable_pi_fintype Fintype.decidablePiFintype

instance decidableForallFintype {p : α → Prop} [DecidablePred p] [Fintype α] :
    Decidable (∀ a, p a) :=
  decidable_of_iff (∀ a ∈ @univ α _, p a) (by simp)
#align fintype.decidable_forall_fintype Fintype.decidableForallFintype

instance decidableExistsFintype {p : α → Prop} [DecidablePred p] [Fintype α] :
    Decidable (∃ a, p a) :=
  decidable_of_iff (∃ a ∈ @univ α _, p a) (by simp)
#align fintype.decidable_exists_fintype Fintype.decidableExistsFintype

instance decidableMemRangeFintype [Fintype α] [DecidableEq β] (f : α → β) :
    DecidablePred (· ∈ Set.range f) := fun _ => Fintype.decidableExistsFintype
#align fintype.decidable_mem_range_fintype Fintype.decidableMemRangeFintype

instance decidableSubsingleton [Fintype α] [DecidableEq α] {s : Set α} [DecidablePred (· ∈ s)] :
    Decidable s.Subsingleton := decidable_of_iff (∀ a ∈ s, ∀ b ∈ s, a = b) Iff.rfl

section BundledHoms

instance decidableEqEquivFintype [DecidableEq β] [Fintype α] : DecidableEq (α ≃ β) := fun a b =>
  decidable_of_iff (a.1 = b.1) Equiv.coe_fn_injective.eq_iff
#align fintype.decidable_eq_equiv_fintype Fintype.decidableEqEquivFintype

instance decidableEqEmbeddingFintype [DecidableEq β] [Fintype α] : DecidableEq (α ↪ β) := fun a b =>
  decidable_of_iff ((a : α → β) = b) Function.Embedding.coe_injective.eq_iff
#align fintype.decidable_eq_embedding_fintype Fintype.decidableEqEmbeddingFintype

end BundledHoms

instance decidableInjectiveFintype [DecidableEq α] [DecidableEq β] [Fintype α] :
    DecidablePred (Injective : (α → β) → Prop) := fun x => by unfold Injective; infer_instance
#align fintype.decidable_injective_fintype Fintype.decidableInjectiveFintype

instance decidableSurjectiveFintype [DecidableEq β] [Fintype α] [Fintype β] :
    DecidablePred (Surjective : (α → β) → Prop) := fun x => by unfold Surjective; infer_instance
#align fintype.decidable_surjective_fintype Fintype.decidableSurjectiveFintype

instance decidableBijectiveFintype [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] :
    DecidablePred (Bijective : (α → β) → Prop) := fun x => by unfold Bijective; infer_instance
#align fintype.decidable_bijective_fintype Fintype.decidableBijectiveFintype

instance decidableRightInverseFintype [DecidableEq α] [Fintype α] (f : α → β) (g : β → α) :
    Decidable (Function.RightInverse f g) :=
  show Decidable (∀ x, g (f x) = x) by infer_instance
#align fintype.decidable_right_inverse_fintype Fintype.decidableRightInverseFintype

instance decidableLeftInverseFintype [DecidableEq β] [Fintype β] (f : α → β) (g : β → α) :
    Decidable (Function.LeftInverse f g) :=
  show Decidable (∀ x, f (g x) = x) by infer_instance
#align fintype.decidable_left_inverse_fintype Fintype.decidableLeftInverseFintype

/-- Construct a proof of `Fintype α` from a universal multiset -/
def ofMultiset [DecidableEq α] (s : Multiset α) (H : ∀ x : α, x ∈ s) : Fintype α :=
  ⟨s.toFinset, by simpa using H⟩
#align fintype.of_multiset Fintype.ofMultiset

/-- Construct a proof of `Fintype α` from a universal list -/
def ofList [DecidableEq α] (l : List α) (H : ∀ x : α, x ∈ l) : Fintype α :=
  ⟨l.toFinset, by simpa using H⟩
#align fintype.of_list Fintype.ofList

instance subsingleton (α : Type*) : Subsingleton (Fintype α) :=
  ⟨fun ⟨s₁, h₁⟩ ⟨s₂, h₂⟩ => by congr; simp [Finset.ext_iff, h₁, h₂]⟩
#align fintype.subsingleton Fintype.subsingleton

instance (α : Type*) : Lean.Meta.FastSubsingleton (Fintype α) := {}

/-- Given a predicate that can be represented by a finset, the subtype
associated to the predicate is a fintype. -/
protected def subtype {p : α → Prop} (s : Finset α) (H : ∀ x : α, x ∈ s ↔ p x) :
    Fintype { x // p x } :=
  ⟨⟨s.1.pmap Subtype.mk fun x => (H x).1, s.nodup.pmap fun _ _ _ _ => congr_arg Subtype.val⟩,
    fun ⟨x, px⟩ => Multiset.mem_pmap.2 ⟨x, (H x).2 px, rfl⟩⟩
#align fintype.subtype Fintype.subtype

/-- Construct a fintype from a finset with the same elements. -/
def ofFinset {p : Set α} (s : Finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) : Fintype p :=
  Fintype.subtype s H
#align fintype.of_finset Fintype.ofFinset

/-- If `f : α → β` is a bijection and `α` is a fintype, then `β` is also a fintype. -/
def ofBijective [Fintype α] (f : α → β) (H : Function.Bijective f) : Fintype β :=
  ⟨univ.map ⟨f, H.1⟩, fun b =>
    let ⟨_, e⟩ := H.2 b
    e ▸ mem_map_of_mem _ (mem_univ _)⟩
#align fintype.of_bijective Fintype.ofBijective

/-- If `f : α → β` is a surjection and `α` is a fintype, then `β` is also a fintype. -/
def ofSurjective [DecidableEq β] [Fintype α] (f : α → β) (H : Function.Surjective f) : Fintype β :=
  ⟨univ.image f, fun b =>
    let ⟨_, e⟩ := H b
    e ▸ mem_image_of_mem _ (mem_univ _)⟩
#align fintype.of_surjective Fintype.ofSurjective

end Fintype

namespace Finset

variable [Fintype α] [DecidableEq α] {s t : Finset α}

@[simp]
lemma filter_univ_mem (s : Finset α) : univ.filter (· ∈ s) = s := by simp [filter_mem_eq_inter]

instance decidableCodisjoint : Decidable (Codisjoint s t) :=
  decidable_of_iff _ codisjoint_left.symm
#align finset.decidable_codisjoint Finset.decidableCodisjoint

instance decidableIsCompl : Decidable (IsCompl s t) :=
  decidable_of_iff' _ isCompl_iff
#align finset.decidable_is_compl Finset.decidableIsCompl

end Finset

section Inv

namespace Function

variable [Fintype α] [DecidableEq β]

namespace Injective

variable {f : α → β} (hf : Function.Injective f)

/-- The inverse of an `hf : injective` function `f : α → β`, of the type `↥(Set.range f) → α`.
This is the computable version of `Function.invFun` that requires `Fintype α` and `DecidableEq β`,
or the function version of applying `(Equiv.ofInjective f hf).symm`.
This function should not usually be used for actual computation because for most cases,
an explicit inverse can be stated that has better computational properties.
This function computes by checking all terms `a : α` to find the `f a = b`, so it is O(N) where
`N = Fintype.card α`.
-/
def invOfMemRange : Set.range f → α := fun b =>
  Finset.choose (fun a => f a = b) Finset.univ
    ((exists_unique_congr (by simp)).mp (hf.exists_unique_of_mem_range b.property))
#align function.injective.inv_of_mem_range Function.Injective.invOfMemRange

theorem left_inv_of_invOfMemRange (b : Set.range f) : f (hf.invOfMemRange b) = b :=
  (Finset.choose_spec (fun a => f a = b) _ _).right
#align function.injective.left_inv_of_inv_of_mem_range Function.Injective.left_inv_of_invOfMemRange

@[simp]
theorem right_inv_of_invOfMemRange (a : α) : hf.invOfMemRange ⟨f a, Set.mem_range_self a⟩ = a :=
  hf (Finset.choose_spec (fun a' => f a' = f a) _ _).right
#align function.injective.right_inv_of_inv_of_mem_range Function.Injective.right_inv_of_invOfMemRange

theorem invFun_restrict [Nonempty α] : (Set.range f).restrict (invFun f) = hf.invOfMemRange := by
  ext ⟨b, h⟩
  apply hf
  simp [hf.left_inv_of_invOfMemRange, @invFun_eq _ _ _ f b (Set.mem_range.mp h)]
#align function.injective.inv_fun_restrict Function.Injective.invFun_restrict

theorem invOfMemRange_surjective : Function.Surjective hf.invOfMemRange := fun a =>
  ⟨⟨f a, Set.mem_range_self a⟩, by simp⟩
#align function.injective.inv_of_mem_range_surjective Function.Injective.invOfMemRange_surjective

end Injective

namespace Embedding

variable (f : α ↪ β) (b : Set.range f)

/-- The inverse of an embedding `f : α ↪ β`, of the type `↥(Set.range f) → α`.
This is the computable version of `Function.invFun` that requires `Fintype α` and `DecidableEq β`,
or the function version of applying `(Equiv.ofInjective f f.injective).symm`.
This function should not usually be used for actual computation because for most cases,
an explicit inverse can be stated that has better computational properties.
This function computes by checking all terms `a : α` to find the `f a = b`, so it is O(N) where
`N = Fintype.card α`.
-/
def invOfMemRange : α :=
  f.injective.invOfMemRange b
#align function.embedding.inv_of_mem_range Function.Embedding.invOfMemRange

@[simp]
theorem left_inv_of_invOfMemRange : f (f.invOfMemRange b) = b :=
  f.injective.left_inv_of_invOfMemRange b
#align function.embedding.left_inv_of_inv_of_mem_range Function.Embedding.left_inv_of_invOfMemRange

@[simp]
theorem right_inv_of_invOfMemRange (a : α) : f.invOfMemRange ⟨f a, Set.mem_range_self a⟩ = a :=
  f.injective.right_inv_of_invOfMemRange a
#align function.embedding.right_inv_of_inv_of_mem_range Function.Embedding.right_inv_of_invOfMemRange

theorem invFun_restrict [Nonempty α] : (Set.range f).restrict (invFun f) = f.invOfMemRange := by
  ext ⟨b, h⟩
  apply f.injective
  simp [f.left_inv_of_invOfMemRange, @invFun_eq _ _ _ f b (Set.mem_range.mp h)]
#align function.embedding.inv_fun_restrict Function.Embedding.invFun_restrict

theorem invOfMemRange_surjective : Function.Surjective f.invOfMemRange := fun a =>
  ⟨⟨f a, Set.mem_range_self a⟩, by simp⟩
#align function.embedding.inv_of_mem_range_surjective Function.Embedding.invOfMemRange_surjective

end Embedding

end Function

end Inv

namespace Fintype

/-- Given an injective function to a fintype, the domain is also a
fintype. This is noncomputable because injectivity alone cannot be
used to construct preimages. -/
noncomputable def ofInjective [Fintype β] (f : α → β) (H : Function.Injective f) : Fintype α :=
  letI := Classical.dec
  if hα : Nonempty α then
    letI := Classical.inhabited_of_nonempty hα
    ofSurjective (invFun f) (invFun_surjective H)
  else ⟨∅, fun x => (hα ⟨x⟩).elim⟩
#align fintype.of_injective Fintype.ofInjective

/-- If `f : α ≃ β` and `α` is a fintype, then `β` is also a fintype. -/
def ofEquiv (α : Type*) [Fintype α] (f : α ≃ β) : Fintype β :=
  ofBijective _ f.bijective
#align fintype.of_equiv Fintype.ofEquiv

/-- Any subsingleton type with a witness is a fintype (with one term). -/
def ofSubsingleton (a : α) [Subsingleton α] : Fintype α :=
  ⟨{a}, fun _ => Finset.mem_singleton.2 (Subsingleton.elim _ _)⟩
#align fintype.of_subsingleton Fintype.ofSubsingleton

@[simp]
theorem univ_ofSubsingleton (a : α) [Subsingleton α] : @univ _ (ofSubsingleton a) = {a} :=
  rfl
#align fintype.univ_of_subsingleton Fintype.univ_ofSubsingleton

/-- An empty type is a fintype. Not registered as an instance, to make sure that there aren't two
conflicting `Fintype ι` instances around when casing over whether a fintype `ι` is empty or not. -/
def ofIsEmpty [IsEmpty α] : Fintype α :=
  ⟨∅, isEmptyElim⟩
#align fintype.of_is_empty Fintype.ofIsEmpty

/-- Note: this lemma is specifically about `Fintype.ofIsEmpty`. For a statement about
arbitrary `Fintype` instances, use `Finset.univ_eq_empty`. -/
theorem univ_ofIsEmpty [IsEmpty α] : @univ α Fintype.ofIsEmpty = ∅ :=
  rfl
#align fintype.univ_of_is_empty Fintype.univ_ofIsEmpty

instance : Fintype Empty := Fintype.ofIsEmpty
instance : Fintype PEmpty := Fintype.ofIsEmpty

end Fintype

namespace Set

variable {s t : Set α}

/-- Construct a finset enumerating a set `s`, given a `Fintype` instance.  -/
def toFinset (s : Set α) [Fintype s] : Finset α :=
  (@Finset.univ s _).map <| Function.Embedding.subtype _
#align set.to_finset Set.toFinset

@[congr]
theorem toFinset_congr {s t : Set α} [Fintype s] [Fintype t] (h : s = t) :
    toFinset s = toFinset t := by subst h; congr; exact Subsingleton.elim _ _
#align set.to_finset_congr Set.toFinset_congr

@[simp]
theorem mem_toFinset {s : Set α} [Fintype s] {a : α} : a ∈ s.toFinset ↔ a ∈ s := by
  simp [toFinset]
#align set.mem_to_finset Set.mem_toFinset

/-- Many `Fintype` instances for sets are defined using an extensionally equal `Finset`.
Rewriting `s.toFinset` with `Set.toFinset_ofFinset` replaces the term with such a `Finset`. -/
theorem toFinset_ofFinset {p : Set α} (s : Finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) :
    @Set.toFinset _ p (Fintype.ofFinset s H) = s :=
  Finset.ext fun x => by rw [@mem_toFinset _ _ (id _), H]
#align set.to_finset_of_finset Set.toFinset_ofFinset

/-- Membership of a set with a `Fintype` instance is decidable.

Using this as an instance leads to potential loops with `Subtype.fintype` under certain decidability
assumptions, so it should only be declared a local instance. -/
def decidableMemOfFintype [DecidableEq α] (s : Set α) [Fintype s] (a) : Decidable (a ∈ s) :=
  decidable_of_iff _ mem_toFinset
#align set.decidable_mem_of_fintype Set.decidableMemOfFintype

@[simp]
theorem coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : Set α) = s :=
  Set.ext fun _ => mem_toFinset
#align set.coe_to_finset Set.coe_toFinset

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]
theorem toFinset_nonempty {s : Set α} [Fintype s] : s.toFinset.Nonempty ↔ s.Nonempty := by
  rw [← Finset.coe_nonempty, coe_toFinset]
#align set.to_finset_nonempty Set.toFinset_nonempty

@[simp]
theorem toFinset_inj {s t : Set α} [Fintype s] [Fintype t] : s.toFinset = t.toFinset ↔ s = t :=
  ⟨fun h => by rw [← s.coe_toFinset, h, t.coe_toFinset], fun h => by simp [h]⟩
#align set.to_finset_inj Set.toFinset_inj

@[mono]
theorem toFinset_subset_toFinset [Fintype s] [Fintype t] : s.toFinset ⊆ t.toFinset ↔ s ⊆ t := by
  simp [Finset.subset_iff, Set.subset_def]
#align set.to_finset_subset_to_finset Set.toFinset_subset_toFinset

@[simp]
theorem toFinset_ssubset [Fintype s] {t : Finset α} : s.toFinset ⊂ t ↔ s ⊂ t := by
  rw [← Finset.coe_ssubset, coe_toFinset]
#align set.to_finset_ssubset Set.toFinset_ssubset

@[simp]
theorem subset_toFinset {s : Finset α} [Fintype t] : s ⊆ t.toFinset ↔ ↑s ⊆ t := by
  rw [← Finset.coe_subset, coe_toFinset]
#align set.subset_to_finset Set.subset_toFinset

@[simp]
theorem ssubset_toFinset {s : Finset α} [Fintype t] : s ⊂ t.toFinset ↔ ↑s ⊂ t := by
  rw [← Finset.coe_ssubset, coe_toFinset]
#align set.ssubset_to_finset Set.ssubset_toFinset

@[mono]
theorem toFinset_ssubset_toFinset [Fintype s] [Fintype t] : s.toFinset ⊂ t.toFinset ↔ s ⊂ t := by
  simp only [Finset.ssubset_def, toFinset_subset_toFinset, ssubset_def]
#align set.to_finset_ssubset_to_finset Set.toFinset_ssubset_toFinset

@[simp]
theorem toFinset_subset [Fintype s] {t : Finset α} : s.toFinset ⊆ t ↔ s ⊆ t := by
  rw [← Finset.coe_subset, coe_toFinset]
#align set.to_finset_subset Set.toFinset_subset

alias ⟨_, toFinset_mono⟩ := toFinset_subset_toFinset
#align set.to_finset_mono Set.toFinset_mono

alias ⟨_, toFinset_strict_mono⟩ := toFinset_ssubset_toFinset
#align set.to_finset_strict_mono Set.toFinset_strict_mono

@[simp]
theorem disjoint_toFinset [Fintype s] [Fintype t] :
    Disjoint s.toFinset t.toFinset ↔ Disjoint s t := by simp only [← disjoint_coe, coe_toFinset]
#align set.disjoint_to_finset Set.disjoint_toFinset

section DecidableEq

variable [DecidableEq α] (s t) [Fintype s] [Fintype t]

@[simp]
theorem toFinset_inter [Fintype (s ∩ t : Set _)] : (s ∩ t).toFinset = s.toFinset ∩ t.toFinset := by
  ext
  simp
#align set.to_finset_inter Set.toFinset_inter

@[simp]
theorem toFinset_union [Fintype (s ∪ t : Set _)] : (s ∪ t).toFinset = s.toFinset ∪ t.toFinset := by
  ext
  simp
#align set.to_finset_union Set.toFinset_union

@[simp]
theorem toFinset_diff [Fintype (s \ t : Set _)] : (s \ t).toFinset = s.toFinset \ t.toFinset := by
  ext
  simp
#align set.to_finset_diff Set.toFinset_diff

open scoped symmDiff in
@[simp]
theorem toFinset_symmDiff [Fintype (s ∆ t : Set _)] :
    (s ∆ t).toFinset = s.toFinset ∆ t.toFinset := by
  ext
  simp [mem_symmDiff, Finset.mem_symmDiff]
#align set.to_finset_symm_diff Set.toFinset_symmDiff

@[simp]
theorem toFinset_compl [Fintype α] [Fintype (sᶜ : Set _)] : sᶜ.toFinset = s.toFinsetᶜ := by
  ext
  simp
#align set.to_finset_compl Set.toFinset_compl

end DecidableEq

-- TODO The `↥` circumvents an elaboration bug. See comment on `Set.toFinset_univ`.
@[simp]
theorem toFinset_empty [Fintype (∅ : Set α)] : (∅ : Set α).toFinset = ∅ := by
  ext
  simp
#align set.to_finset_empty Set.toFinset_empty

/- TODO Without the coercion arrow (`↥`) there is an elaboration bug in the following two;
it essentially infers `Fintype.{v} (Set.univ.{u} : Set α)` with `v` and `u` distinct.
Reported in leanprover-community/lean#672 -/
@[simp]
theorem toFinset_univ [Fintype α] [Fintype (Set.univ : Set α)] :
    (Set.univ : Set α).toFinset = Finset.univ := by
  ext
  simp
#align set.to_finset_univ Set.toFinset_univ

@[simp]
theorem toFinset_eq_empty [Fintype s] : s.toFinset = ∅ ↔ s = ∅ := by
  let A : Fintype (∅ : Set α) := Fintype.ofIsEmpty
  rw [← toFinset_empty, toFinset_inj]
#align set.to_finset_eq_empty Set.toFinset_eq_empty

@[simp]
theorem toFinset_eq_univ [Fintype α] [Fintype s] : s.toFinset = Finset.univ ↔ s = univ := by
  rw [← coe_inj, coe_toFinset, coe_univ]
#align set.to_finset_eq_univ Set.toFinset_eq_univ

@[simp]
theorem toFinset_setOf [Fintype α] (p : α → Prop) [DecidablePred p] [Fintype { x | p x }] :
    { x | p x }.toFinset = Finset.univ.filter p := by
  ext
  simp
#align set.to_finset_set_of Set.toFinset_setOf

--@[simp] Porting note: removing simp, simp can prove it
theorem toFinset_ssubset_univ [Fintype α] {s : Set α} [Fintype s] :
    s.toFinset ⊂ Finset.univ ↔ s ⊂ univ := by rw [← coe_ssubset, coe_toFinset, coe_univ]
#align set.to_finset_ssubset_univ Set.toFinset_ssubset_univ

@[simp]
theorem toFinset_image [DecidableEq β] (f : α → β) (s : Set α) [Fintype s] [Fintype (f '' s)] :
    (f '' s).toFinset = s.toFinset.image f :=
  Finset.coe_injective <| by simp
#align set.to_finset_image Set.toFinset_image

@[simp]
theorem toFinset_range [DecidableEq α] [Fintype β] (f : β → α) [Fintype (Set.range f)] :
    (Set.range f).toFinset = Finset.univ.image f := by
  ext
  simp
#align set.to_finset_range Set.toFinset_range

@[simp] -- Porting note: new attribute
theorem toFinset_singleton (a : α) [Fintype ({a} : Set α)] : ({a} : Set α).toFinset = {a} := by
  ext
  simp
#align set.to_finset_singleton Set.toFinset_singleton

@[simp]
theorem toFinset_insert [DecidableEq α] {a : α} {s : Set α} [Fintype (insert a s : Set α)]
    [Fintype s] : (insert a s).toFinset = insert a s.toFinset := by
  ext
  simp
#align set.to_finset_insert Set.toFinset_insert

theorem filter_mem_univ_eq_toFinset [Fintype α] (s : Set α) [Fintype s] [DecidablePred (· ∈ s)] :
    Finset.univ.filter (· ∈ s) = s.toFinset := by
  ext
  simp only [Finset.mem_univ, decide_eq_true_eq, forall_true_left, mem_filter,
    true_and, mem_toFinset]
#align set.filter_mem_univ_eq_to_finset Set.filter_mem_univ_eq_toFinset

end Set

@[simp]
theorem Finset.toFinset_coe (s : Finset α) [Fintype (s : Set α)] : (s : Set α).toFinset = s :=
  ext fun _ => Set.mem_toFinset
#align finset.to_finset_coe Finset.toFinset_coe

instance Fin.fintype (n : ℕ) : Fintype (Fin n) :=
  ⟨⟨List.finRange n, List.nodup_finRange n⟩, List.mem_finRange⟩

theorem Fin.univ_def (n : ℕ) : (univ : Finset (Fin n)) = ⟨List.finRange n, List.nodup_finRange n⟩ :=
  rfl
#align fin.univ_def Fin.univ_def

@[simp] theorem List.toFinset_finRange (n : ℕ) : (List.finRange n).toFinset = Finset.univ := by
  ext; simp

@[simp] theorem Fin.univ_val_map {n : ℕ} (f : Fin n → α) :
    Finset.univ.val.map f = List.ofFn f := by
  simp [List.ofFn_eq_map, univ_def]

theorem Fin.univ_image_def {n : ℕ} [DecidableEq α] (f : Fin n → α) :
    Finset.univ.image f = (List.ofFn f).toFinset := by
  simp [Finset.image]

theorem Fin.univ_map_def {n : ℕ} (f : Fin n ↪ α) :
    Finset.univ.map f = ⟨List.ofFn f, List.nodup_ofFn.mpr f.injective⟩ := by
  simp [Finset.map]

@[simp]
theorem Fin.image_succAbove_univ {n : ℕ} (i : Fin (n + 1)) : univ.image i.succAbove = {i}ᶜ := by
  ext m
  simp
#align fin.image_succ_above_univ Fin.image_succAbove_univ

@[simp]
theorem Fin.image_succ_univ (n : ℕ) : (univ : Finset (Fin n)).image Fin.succ = {0}ᶜ := by
  rw [← Fin.succAbove_zero, Fin.image_succAbove_univ]
#align fin.image_succ_univ Fin.image_succ_univ

@[simp]
theorem Fin.image_castSucc (n : ℕ) :
    (univ : Finset (Fin n)).image Fin.castSucc = {Fin.last n}ᶜ := by
  rw [← Fin.succAbove_last, Fin.image_succAbove_univ]
#align fin.image_cast_succ Fin.image_castSucc

/- The following three lemmas use `Finset.cons` instead of `insert` and `Finset.map` instead of
`Finset.image` to reduce proof obligations downstream. -/
/-- Embed `Fin n` into `Fin (n + 1)` by prepending zero to the `univ` -/
theorem Fin.univ_succ (n : ℕ) :
    (univ : Finset (Fin (n + 1))) =
      Finset.cons 0 (univ.map ⟨Fin.succ, Fin.succ_injective _⟩) (by simp [map_eq_image]) := by
  simp [map_eq_image]
#align fin.univ_succ Fin.univ_succ

/-- Embed `Fin n` into `Fin (n + 1)` by appending a new `Fin.last n` to the `univ` -/
theorem Fin.univ_castSuccEmb (n : ℕ) :
    (univ : Finset (Fin (n + 1))) =
      Finset.cons (Fin.last n) (univ.map Fin.castSuccEmb) (by simp [map_eq_image]) := by
  simp [map_eq_image]
#align fin.univ_cast_succ Fin.univ_castSuccEmb

/-- Embed `Fin n` into `Fin (n + 1)` by inserting
around a specified pivot `p : Fin (n + 1)` into the `univ` -/
theorem Fin.univ_succAbove (n : ℕ) (p : Fin (n + 1)) :
    (univ : Finset (Fin (n + 1))) = Finset.cons p (univ.map <| Fin.succAboveEmb p) (by simp) := by
  simp [map_eq_image]
#align fin.univ_succ_above Fin.univ_succAbove

@[simp] theorem Fin.univ_image_get [DecidableEq α] (l : List α) :
    Finset.univ.image l.get = l.toFinset := by
  simp [univ_image_def]

@[simp] theorem Fin.univ_image_get' [DecidableEq β] (l : List α) (f : α → β) :
    Finset.univ.image (f <| l.get ·) = (l.map f).toFinset := by
  simp [univ_image_def]

@[instance]
def Unique.fintype {α : Type*} [Unique α] : Fintype α :=
  Fintype.ofSubsingleton default
#align unique.fintype Unique.fintype

/-- Short-circuit instance to decrease search for `Unique.fintype`,
since that relies on a subsingleton elimination for `Unique`. -/
instance Fintype.subtypeEq (y : α) : Fintype { x // x = y } :=
  Fintype.subtype {y} (by simp)
#align fintype.subtype_eq Fintype.subtypeEq

/-- Short-circuit instance to decrease search for `Unique.fintype`,
since that relies on a subsingleton elimination for `Unique`. -/
instance Fintype.subtypeEq' (y : α) : Fintype { x // y = x } :=
  Fintype.subtype {y} (by simp [eq_comm])
#align fintype.subtype_eq' Fintype.subtypeEq'

-- Porting note: removing @[simp], simp can prove it
theorem Fintype.univ_empty : @univ Empty _ = ∅ :=
  rfl
#align fintype.univ_empty Fintype.univ_empty

--@[simp] Porting note: removing simp, simp can prove it
theorem Fintype.univ_pempty : @univ PEmpty _ = ∅ :=
  rfl
#align fintype.univ_pempty Fintype.univ_pempty

instance Unit.fintype : Fintype Unit :=
  Fintype.ofSubsingleton ()
#align unit.fintype Unit.fintype

theorem Fintype.univ_unit : @univ Unit _ = {()} :=
  rfl
#align fintype.univ_unit Fintype.univ_unit

instance PUnit.fintype : Fintype PUnit :=
  Fintype.ofSubsingleton PUnit.unit
#align punit.fintype PUnit.fintype

--@[simp] Porting note: removing simp, simp can prove it
theorem Fintype.univ_punit : @univ PUnit _ = {PUnit.unit} :=
  rfl
#align fintype.univ_punit Fintype.univ_punit

instance Bool.fintype : Fintype Bool :=
  ⟨⟨{true, false}, by simp⟩, fun x => by cases x <;> simp⟩
#align bool.fintype Bool.fintype

@[simp]
theorem Fintype.univ_bool : @univ Bool _ = {true, false} :=
  rfl
#align fintype.univ_bool Fintype.univ_bool

instance Additive.fintype : ∀ [Fintype α], Fintype (Additive α) :=
  Fintype.ofEquiv α Additive.ofMul
#align additive.fintype Additive.fintype

instance Multiplicative.fintype : ∀ [Fintype α], Fintype (Multiplicative α) :=
  Fintype.ofEquiv α Multiplicative.ofAdd
#align multiplicative.fintype Multiplicative.fintype

/-- Given that `α × β` is a fintype, `α` is also a fintype. -/
def Fintype.prodLeft {α β} [DecidableEq α] [Fintype (α × β)] [Nonempty β] : Fintype α :=
  ⟨(@univ (α × β) _).image Prod.fst, fun a => by simp⟩
#align fintype.prod_left Fintype.prodLeft

/-- Given that `α × β` is a fintype, `β` is also a fintype. -/
def Fintype.prodRight {α β} [DecidableEq β] [Fintype (α × β)] [Nonempty α] : Fintype β :=
  ⟨(@univ (α × β) _).image Prod.snd, fun b => by simp⟩
#align fintype.prod_right Fintype.prodRight

instance ULift.fintype (α : Type*) [Fintype α] : Fintype (ULift α) :=
  Fintype.ofEquiv _ Equiv.ulift.symm
#align ulift.fintype ULift.fintype

instance PLift.fintype (α : Type*) [Fintype α] : Fintype (PLift α) :=
  Fintype.ofEquiv _ Equiv.plift.symm
#align plift.fintype PLift.fintype

instance OrderDual.fintype (α : Type*) [Fintype α] : Fintype αᵒᵈ :=
  ‹Fintype α›
#align order_dual.fintype OrderDual.fintype

instance OrderDual.finite (α : Type*) [Finite α] : Finite αᵒᵈ :=
  ‹Finite α›
#align order_dual.finite OrderDual.finite

instance Lex.fintype (α : Type*) [Fintype α] : Fintype (Lex α) :=
  ‹Fintype α›
#align lex.fintype Lex.fintype

section Finset

/-! ### `Fintype (s : Finset α)` -/


instance Finset.fintypeCoeSort {α : Type u} (s : Finset α) : Fintype s :=
  ⟨s.attach, s.mem_attach⟩
#align finset.fintype_coe_sort Finset.fintypeCoeSort

@[simp]
theorem Finset.univ_eq_attach {α : Type u} (s : Finset α) : (univ : Finset s) = s.attach :=
  rfl
#align finset.univ_eq_attach Finset.univ_eq_attach

end Finset

theorem Fintype.coe_image_univ [Fintype α] [DecidableEq β] {f : α → β} :
    ↑(Finset.image f Finset.univ) = Set.range f := by
  ext x
  simp
#align fintype.coe_image_univ Fintype.coe_image_univ

instance List.Subtype.fintype [DecidableEq α] (l : List α) : Fintype { x // x ∈ l } :=
  Fintype.ofList l.attach l.mem_attach
#align list.subtype.fintype List.Subtype.fintype

instance Multiset.Subtype.fintype [DecidableEq α] (s : Multiset α) : Fintype { x // x ∈ s } :=
  Fintype.ofMultiset s.attach s.mem_attach
#align multiset.subtype.fintype Multiset.Subtype.fintype

instance Finset.Subtype.fintype (s : Finset α) : Fintype { x // x ∈ s } :=
  ⟨s.attach, s.mem_attach⟩
#align finset.subtype.fintype Finset.Subtype.fintype

instance FinsetCoe.fintype (s : Finset α) : Fintype (↑s : Set α) :=
  Finset.Subtype.fintype s
#align finset_coe.fintype FinsetCoe.fintype

theorem Finset.attach_eq_univ {s : Finset α} : s.attach = Finset.univ :=
  rfl
#align finset.attach_eq_univ Finset.attach_eq_univ

instance PLift.fintypeProp (p : Prop) [Decidable p] : Fintype (PLift p) :=
  ⟨if h : p then {⟨h⟩} else ∅, fun ⟨h⟩ => by simp [h]⟩
#align plift.fintype_Prop PLift.fintypeProp

instance Prop.fintype : Fintype Prop :=
  ⟨⟨{True, False}, by simp [true_ne_false]⟩, by simpa using em⟩
#align Prop.fintype Prop.fintype

@[simp]
theorem Fintype.univ_Prop : (Finset.univ : Finset Prop) = {True, False} :=
  Finset.eq_of_veq <| by simp; rfl
#align fintype.univ_Prop Fintype.univ_Prop

instance Subtype.fintype (p : α → Prop) [DecidablePred p] [Fintype α] : Fintype { x // p x } :=
  Fintype.subtype (univ.filter p) (by simp)
#align subtype.fintype Subtype.fintype

/-- A set on a fintype, when coerced to a type, is a fintype. -/
def setFintype [Fintype α] (s : Set α) [DecidablePred (· ∈ s)] : Fintype s :=
  Subtype.fintype fun x => x ∈ s
#align set_fintype setFintype

namespace Fintype
variable [Fintype α]

/-- Given `Fintype α`, `finsetEquivSet` is the equiv between `Finset α` and `Set α`. (All
sets on a finite type are finite.) -/
noncomputable def finsetEquivSet : Finset α ≃ Set α where
  toFun := (↑)
  invFun := by classical exact fun s => s.toFinset
  left_inv s := by convert Finset.toFinset_coe s
  right_inv s := by classical exact s.coe_toFinset
#align fintype.finset_equiv_set Fintype.finsetEquivSet

@[simp, norm_cast] lemma coe_finsetEquivSet : ⇑finsetEquivSet = ((↑) : Finset α → Set α) := rfl

@[simp] lemma finsetEquivSet_apply (s : Finset α) : finsetEquivSet s = s := rfl
#align fintype.finset_equiv_set_apply Fintype.finsetEquivSet_apply

@[simp] lemma finsetEquivSet_symm_apply (s : Set α) [Fintype s] :
    finsetEquivSet.symm s = s.toFinset := by simp [finsetEquivSet]
#align fintype.finset_equiv_set_symm_apply Fintype.finsetEquivSet_symm_apply

/-- Given a fintype `α`, `finsetOrderIsoSet` is the order isomorphism between `Finset α` and `Set α`
(all sets on a finite type are finite). -/
@[simps toEquiv]
noncomputable def finsetOrderIsoSet : Finset α ≃o Set α where
  toEquiv := finsetEquivSet
  map_rel_iff' := Finset.coe_subset

@[simp, norm_cast]
lemma coe_finsetOrderIsoSet : ⇑finsetOrderIsoSet = ((↑) : Finset α → Set α) := rfl

@[simp] lemma coe_finsetOrderIsoSet_symm :
    ⇑(finsetOrderIsoSet : Finset α ≃o Set α).symm = ⇑finsetEquivSet.symm := rfl

end Fintype

instance Quotient.fintype [Fintype α] (s : Setoid α) [DecidableRel ((· ≈ ·) : α → α → Prop)] :
    Fintype (Quotient s) :=
  Fintype.ofSurjective Quotient.mk'' Quotient.surjective_Quotient_mk''
#align quotient.fintype Quotient.fintype

instance PSigma.fintypePropLeft {α : Prop} {β : α → Type*} [Decidable α] [∀ a, Fintype (β a)] :
    Fintype (Σ'a, β a) :=
  if h : α then Fintype.ofEquiv (β h) ⟨fun x => ⟨h, x⟩, PSigma.snd, fun _ => rfl, fun ⟨_, _⟩ => rfl⟩
  else ⟨∅, fun x => (h x.1).elim⟩
#align psigma.fintype_prop_left PSigma.fintypePropLeft

instance PSigma.fintypePropRight {α : Type*} {β : α → Prop} [∀ a, Decidable (β a)] [Fintype α] :
    Fintype (Σ'a, β a) :=
  Fintype.ofEquiv { a // β a }
    ⟨fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨_, _⟩ => rfl, fun ⟨_, _⟩ => rfl⟩
#align psigma.fintype_prop_right PSigma.fintypePropRight

instance PSigma.fintypePropProp {α : Prop} {β : α → Prop} [Decidable α] [∀ a, Decidable (β a)] :
    Fintype (Σ'a, β a) :=
  if h : ∃ a, β a then ⟨{⟨h.fst, h.snd⟩}, fun ⟨_, _⟩ => by simp⟩ else ⟨∅, fun ⟨x, y⟩ =>
    (h ⟨x, y⟩).elim⟩
#align psigma.fintype_prop_prop PSigma.fintypePropProp

instance pfunFintype (p : Prop) [Decidable p] (α : p → Type*) [∀ hp, Fintype (α hp)] :
    Fintype (∀ hp : p, α hp) :=
  if hp : p then Fintype.ofEquiv (α hp) ⟨fun a _ => a, fun f => f hp, fun _ => rfl, fun _ => rfl⟩
  else ⟨singleton fun h => (hp h).elim, fun h => mem_singleton.2
    (funext fun x => by contradiction)⟩
#align pfun_fintype pfunFintype

theorem mem_image_univ_iff_mem_range {α β : Type*} [Fintype α] [DecidableEq β] {f : α → β}
    {b : β} : b ∈ univ.image f ↔ b ∈ Set.range f := by simp
#align mem_image_univ_iff_mem_range mem_image_univ_iff_mem_range

namespace Fintype

section Choose

open Fintype Equiv

variable [Fintype α] (p : α → Prop) [DecidablePred p]

/-- Given a fintype `α` and a predicate `p`, associate to a proof that there is a unique element of
`α` satisfying `p` this unique element, as an element of the corresponding subtype. -/
def chooseX (hp : ∃! a : α, p a) : { a // p a } :=
  ⟨Finset.choose p univ (by simp; exact hp), Finset.choose_property _ _ _⟩
#align fintype.choose_x Fintype.chooseX

/-- Given a fintype `α` and a predicate `p`, associate to a proof that there is a unique element of
`α` satisfying `p` this unique element, as an element of `α`. -/
def choose (hp : ∃! a, p a) : α :=
  chooseX p hp
#align fintype.choose Fintype.choose

theorem choose_spec (hp : ∃! a, p a) : p (choose p hp) :=
  (chooseX p hp).property
#align fintype.choose_spec Fintype.choose_spec

-- @[simp] Porting note: removing simp, never applies
theorem choose_subtype_eq {α : Type*} (p : α → Prop) [Fintype { a : α // p a }] [DecidableEq α]
    (x : { a : α // p a })
    (h : ∃! a : { a // p a }, (a : α) = x :=
      ⟨x, rfl, fun y hy => by simpa [Subtype.ext_iff] using hy⟩) :
    Fintype.choose (fun y : { a : α // p a } => (y : α) = x) h = x := by
  rw [Subtype.ext_iff, Fintype.choose_spec (fun y : { a : α // p a } => (y : α) = x) _]
#align fintype.choose_subtype_eq Fintype.choose_subtype_eq

end Choose

section BijectionInverse

open Function

variable [Fintype α] [DecidableEq β] {f : α → β}

/-- `bijInv f` is the unique inverse to a bijection `f`. This acts
  as a computable alternative to `Function.invFun`. -/
def bijInv (f_bij : Bijective f) (b : β) : α :=
  Fintype.choose (fun a => f a = b)
    (by
      rcases f_bij.right b with ⟨a', fa_eq_b⟩
      rw [← fa_eq_b]
      exact ⟨a', ⟨rfl, fun a h => f_bij.left h⟩⟩)
#align fintype.bij_inv Fintype.bijInv

theorem leftInverse_bijInv (f_bij : Bijective f) : LeftInverse (bijInv f_bij) f := fun a =>
  f_bij.left (choose_spec (fun a' => f a' = f a) _)
#align fintype.left_inverse_bij_inv Fintype.leftInverse_bijInv

theorem rightInverse_bijInv (f_bij : Bijective f) : RightInverse (bijInv f_bij) f := fun b =>
  choose_spec (fun a' => f a' = b) _
#align fintype.right_inverse_bij_inv Fintype.rightInverse_bijInv

theorem bijective_bijInv (f_bij : Bijective f) : Bijective (bijInv f_bij) :=
  ⟨(rightInverse_bijInv _).injective, (leftInverse_bijInv _).surjective⟩
#align fintype.bijective_bij_inv Fintype.bijective_bijInv

end BijectionInverse

end Fintype

section Trunc

/-- For `s : Multiset α`, we can lift the existential statement that `∃ x, x ∈ s` to a `Trunc α`.
-/
def truncOfMultisetExistsMem {α} (s : Multiset α) : (∃ x, x ∈ s) → Trunc α :=
  Quotient.recOnSubsingleton s fun l h =>
    match l, h with
    | [], _ => False.elim (by tauto)
    | a :: _, _ => Trunc.mk a
#align trunc_of_multiset_exists_mem truncOfMultisetExistsMem

/-- A `Nonempty` `Fintype` constructively contains an element.
-/
def truncOfNonemptyFintype (α) [Nonempty α] [Fintype α] : Trunc α :=
  truncOfMultisetExistsMem Finset.univ.val (by simp)
#align trunc_of_nonempty_fintype truncOfNonemptyFintype

/-- By iterating over the elements of a fintype, we can lift an existential statement `∃ a, P a`
to `Trunc (Σ' a, P a)`, containing data.
-/
def truncSigmaOfExists {α} [Fintype α] {P : α → Prop} [DecidablePred P] (h : ∃ a, P a) :
    Trunc (Σ'a, P a) :=
  @truncOfNonemptyFintype (Σ'a, P a) ((Exists.elim h) fun a ha => ⟨⟨a, ha⟩⟩) _
#align trunc_sigma_of_exists truncSigmaOfExists

end Trunc

namespace Multiset

variable [Fintype α] [Fintype β]

@[simp]
theorem count_univ [DecidableEq α] (a : α) : count a Finset.univ.val = 1 :=
  count_eq_one_of_mem Finset.univ.nodup (Finset.mem_univ _)
#align multiset.count_univ Multiset.count_univ

@[simp]
theorem map_univ_val_equiv (e : α ≃ β) :
    map e univ.val = univ.val := by
  rw [← congr_arg Finset.val (Finset.map_univ_equiv e), Finset.map_val, Equiv.coe_toEmbedding]

/-- For functions on finite sets, they are bijections iff they map universes into universes. -/
@[simp]
theorem bijective_iff_map_univ_eq_univ (f : α → β) :
    f.Bijective ↔ map f (Finset.univ : Finset α).val = univ.val :=
  ⟨fun bij ↦ congr_arg (·.val) (map_univ_equiv <| Equiv.ofBijective f bij),
    fun eq ↦ ⟨
      fun a₁ a₂ ↦ inj_on_of_nodup_map (eq.symm ▸ univ.nodup) _ (mem_univ a₁) _ (mem_univ a₂),
      fun b ↦ have ⟨a, _, h⟩ := mem_map.mp (eq.symm ▸ mem_univ_val b); ⟨a, h⟩⟩⟩

end Multiset

/-- Auxiliary definition to show `exists_seq_of_forall_finset_exists`. -/
noncomputable def seqOfForallFinsetExistsAux {α : Type*} [DecidableEq α] (P : α → Prop)
    (r : α → α → Prop) (h : ∀ s : Finset α, ∃ y, (∀ x ∈ s, P x) → P y ∧ ∀ x ∈ s, r x y) : ℕ → α
  | n =>
    Classical.choose
      (h
        (Finset.image (fun i : Fin n => seqOfForallFinsetExistsAux P r h i)
          (Finset.univ : Finset (Fin n))))
#align seq_of_forall_finset_exists_aux seqOfForallFinsetExistsAux

/-- Induction principle to build a sequence, by adding one point at a time satisfying a given
relation with respect to all the previously chosen points.

More precisely, Assume that, for any finite set `s`, one can find another point satisfying
some relation `r` with respect to all the points in `s`. Then one may construct a
function `f : ℕ → α` such that `r (f m) (f n)` holds whenever `m < n`.
We also ensure that all constructed points satisfy a given predicate `P`. -/
theorem exists_seq_of_forall_finset_exists {α : Type*} (P : α → Prop) (r : α → α → Prop)
    (h : ∀ s : Finset α, (∀ x ∈ s, P x) → ∃ y, P y ∧ ∀ x ∈ s, r x y) :
    ∃ f : ℕ → α, (∀ n, P (f n)) ∧ ∀ m n, m < n → r (f m) (f n) := by
  classical
    have : Nonempty α := by
      rcases h ∅ (by simp) with ⟨y, _⟩
      exact ⟨y⟩
    choose! F hF using h
    have h' : ∀ s : Finset α, ∃ y, (∀ x ∈ s, P x) → P y ∧ ∀ x ∈ s, r x y := fun s => ⟨F s, hF s⟩
    set f := seqOfForallFinsetExistsAux P r h' with hf
    have A : ∀ n : ℕ, P (f n) := by
      intro n
      induction' n using Nat.strong_induction_on with n IH
      have IH' : ∀ x : Fin n, P (f x) := fun n => IH n.1 n.2
      rw [hf, seqOfForallFinsetExistsAux]
      exact
        (Classical.choose_spec
            (h' (Finset.image (fun i : Fin n => f i) (Finset.univ : Finset (Fin n))))
            (by simp [IH'])).1
    refine ⟨f, A, fun m n hmn => ?_⟩
    conv_rhs => rw [hf]
    rw [seqOfForallFinsetExistsAux]
    apply
      (Classical.choose_spec
          (h' (Finset.image (fun i : Fin n => f i) (Finset.univ : Finset (Fin n)))) (by simp [A])).2
    exact Finset.mem_image.2 ⟨⟨m, hmn⟩, Finset.mem_univ _, rfl⟩
#align exists_seq_of_forall_finset_exists exists_seq_of_forall_finset_exists

/-- Induction principle to build a sequence, by adding one point at a time satisfying a given
symmetric relation with respect to all the previously chosen points.

More precisely, Assume that, for any finite set `s`, one can find another point satisfying
some relation `r` with respect to all the points in `s`. Then one may construct a
function `f : ℕ → α` such that `r (f m) (f n)` holds whenever `m ≠ n`.
We also ensure that all constructed points satisfy a given predicate `P`. -/
theorem exists_seq_of_forall_finset_exists' {α : Type*} (P : α → Prop) (r : α → α → Prop)
    [IsSymm α r] (h : ∀ s : Finset α, (∀ x ∈ s, P x) → ∃ y, P y ∧ ∀ x ∈ s, r x y) :
    ∃ f : ℕ → α, (∀ n, P (f n)) ∧ Pairwise fun m n => r (f m) (f n) := by
  rcases exists_seq_of_forall_finset_exists P r h with ⟨f, hf, hf'⟩
  refine ⟨f, hf, fun m n hmn => ?_⟩
  rcases lt_trichotomy m n with (h | rfl | h)
  · exact hf' m n h
  · exact (hmn rfl).elim
  · apply symm
    exact hf' n m h
#align exists_seq_of_forall_finset_exists' exists_seq_of_forall_finset_exists'

open Batteries.ExtendedBinder Lean Meta

/-- `finset% t` elaborates `t` as a `Finset`.
If `t` is a `Set`, then inserts `Set.toFinset`.
Does not make use of the expected type; useful for big operators over finsets.
```
#check finset% Finset.range 2 -- Finset Nat
#check finset% (Set.univ : Set Bool) -- Finset Bool
```
-/
elab (name := finsetStx) "finset% " t:term : term => do
  let u ← mkFreshLevelMVar
  let ty ← mkFreshExprMVar (mkSort (.succ u))
  let x ← Elab.Term.elabTerm t (mkApp (.const ``Finset [u]) ty)
  let xty ← whnfR (← inferType x)
  if xty.isAppOfArity ``Set 1 then
    Elab.Term.elabAppArgs (.const ``Set.toFinset [u]) #[] #[.expr x] none false false
  else
    return x

open Lean.Elab.Term.Quotation in
/-- `quot_precheck` for the `finset%` syntax. -/
@[quot_precheck finsetStx] def precheckFinsetStx : Precheck
  | `(finset% $t) => precheck t
  | _ => Elab.throwUnsupportedSyntax
