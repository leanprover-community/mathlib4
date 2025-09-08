/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Defs

/-!
# `Finset`s are a boolean algebra

This file provides the `BooleanAlgebra (Finset α)` instance, under the assumption that `α` is a
`Fintype`.

## Main results

* `Finset.boundedOrder`: `Finset.univ` is the top element of `Finset α`
* `Finset.booleanAlgebra`: `Finset α` is a boolean algebra if `α` is finite
-/

assert_not_exists Monoid

open Function

open Nat

universe u v

variable {α β γ : Type*}

namespace Finset

variable {s t : Finset α}

section Fintypeα

variable [Fintype α]

theorem Nonempty.eq_univ [Subsingleton α] : s.Nonempty → s = univ := by
  rintro ⟨x, hx⟩
  exact eq_univ_of_forall fun y => by rwa [Subsingleton.elim y x]

theorem univ_nonempty_iff : (univ : Finset α).Nonempty ↔ Nonempty α := by
  rw [← coe_nonempty, coe_univ, Set.nonempty_iff_univ_nonempty]

@[simp, aesop unsafe apply (rule_sets := [finsetNonempty])]
theorem univ_nonempty [Nonempty α] : (univ : Finset α).Nonempty :=
  univ_nonempty_iff.2 ‹_›

theorem univ_eq_empty_iff : (univ : Finset α) = ∅ ↔ IsEmpty α := by
  rw [← not_nonempty_iff, ← univ_nonempty_iff, not_nonempty_iff_eq_empty]

theorem univ_nontrivial_iff :
    (Finset.univ : Finset α).Nontrivial ↔ Nontrivial α := by
  rw [Finset.Nontrivial, Finset.coe_univ, Set.nontrivial_univ_iff]

theorem univ_nontrivial [h : Nontrivial α] :
    (Finset.univ : Finset α).Nontrivial :=
  univ_nontrivial_iff.mpr h

@[simp]
theorem univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅ :=
  univ_eq_empty_iff.2 ‹_›

@[simp]
theorem univ_unique [Unique α] : (univ : Finset α) = {default} :=
  Finset.ext fun x => iff_of_true (mem_univ _) <| mem_singleton.2 <| Subsingleton.elim x default

instance boundedOrder : BoundedOrder (Finset α) :=
  { inferInstanceAs (OrderBot (Finset α)) with
    top := univ
    le_top := subset_univ }

@[simp]
theorem top_eq_univ : (⊤ : Finset α) = univ :=
  rfl

theorem ssubset_univ_iff {s : Finset α} : s ⊂ univ ↔ s ≠ univ :=
  @lt_top_iff_ne_top _ _ _ s

@[simp]
theorem univ_subset_iff {s : Finset α} : univ ⊆ s ↔ s = univ :=
  @top_le_iff _ _ _ s

theorem codisjoint_left : Codisjoint s t ↔ ∀ ⦃a⦄, a ∉ s → a ∈ t := by
  classical simp [codisjoint_iff, eq_univ_iff_forall, or_iff_not_imp_left]

theorem codisjoint_right : Codisjoint s t ↔ ∀ ⦃a⦄, a ∉ t → a ∈ s :=
  codisjoint_comm.trans codisjoint_left

instance booleanAlgebra [DecidableEq α] : BooleanAlgebra (Finset α) :=
  GeneralizedBooleanAlgebra.toBooleanAlgebra

section BooleanAlgebra
variable [DecidableEq α] {a : α}

theorem sdiff_eq_inter_compl (s t : Finset α) : s \ t = s ∩ tᶜ :=
  sdiff_eq

theorem compl_eq_univ_sdiff (s : Finset α) : sᶜ = univ \ s :=
  rfl

@[simp]
theorem mem_compl : a ∈ sᶜ ↔ a ∉ s := by simp [compl_eq_univ_sdiff]

theorem notMem_compl : a ∉ sᶜ ↔ a ∈ s := by rw [mem_compl, not_not]

@[deprecated (since := "2025-05-23")] alias not_mem_compl := notMem_compl

@[simp, norm_cast]
theorem coe_compl (s : Finset α) : ↑sᶜ = (↑s : Set α)ᶜ :=
  Set.ext fun _ => mem_compl

@[simp] lemma compl_subset_compl : sᶜ ⊆ tᶜ ↔ t ⊆ s := @compl_le_compl_iff_le (Finset α) _ _ _
@[simp] lemma compl_ssubset_compl : sᶜ ⊂ tᶜ ↔ t ⊂ s := @compl_lt_compl_iff_lt (Finset α) _ _ _

lemma subset_compl_comm : s ⊆ tᶜ ↔ t ⊆ sᶜ := le_compl_iff_le_compl (α := Finset α)

lemma subset_compl_iff_disjoint_right : s ⊆ tᶜ ↔ Disjoint s t :=
  le_compl_iff_disjoint_right (α := Finset α)

lemma subset_compl_iff_disjoint_left : s ⊆ tᶜ ↔ Disjoint t s :=
  le_compl_iff_disjoint_left (α := Finset α)

@[simp] lemma subset_compl_singleton : s ⊆ {a}ᶜ ↔ a ∉ s := by
  rw [subset_compl_comm, singleton_subset_iff, mem_compl]

@[simp]
theorem compl_empty : (∅ : Finset α)ᶜ = univ :=
  compl_bot

@[simp]
theorem compl_univ : (univ : Finset α)ᶜ = ∅ :=
  compl_top

@[simp]
theorem compl_eq_empty_iff (s : Finset α) : sᶜ = ∅ ↔ s = univ :=
  compl_eq_bot

@[simp]
theorem compl_eq_univ_iff (s : Finset α) : sᶜ = univ ↔ s = ∅ :=
  compl_eq_top

@[simp]
theorem union_compl (s : Finset α) : s ∪ sᶜ = univ :=
  sup_compl_eq_top

@[simp]
theorem inter_compl (s : Finset α) : s ∩ sᶜ = ∅ :=
  inf_compl_eq_bot

@[simp]
theorem compl_union (s t : Finset α) : (s ∪ t)ᶜ = sᶜ ∩ tᶜ :=
  compl_sup

@[simp]
theorem compl_inter (s t : Finset α) : (s ∩ t)ᶜ = sᶜ ∪ tᶜ :=
  compl_inf

@[simp]
theorem compl_erase : (s.erase a)ᶜ = insert a sᶜ := by
  ext
  simp only [or_iff_not_imp_left, mem_insert, not_and, mem_compl, mem_erase]

@[simp]
theorem compl_insert : (insert a s)ᶜ = sᶜ.erase a := by
  ext
  simp only [not_or, mem_insert, mem_compl, mem_erase]

theorem insert_compl_insert (ha : a ∉ s) : insert a (insert a s)ᶜ = sᶜ := by
  simp_rw [compl_insert, insert_erase (mem_compl.2 ha)]

@[simp]
theorem insert_compl_self (x : α) : insert x ({x}ᶜ : Finset α) = univ := by
  rw [← compl_erase, erase_singleton, compl_empty]

@[simp]
theorem compl_filter (p : α → Prop) [DecidablePred p] [∀ x, Decidable ¬p x] :
    (univ.filter p)ᶜ = univ.filter fun x => ¬p x :=
  ext <| by simp

theorem compl_ne_univ_iff_nonempty (s : Finset α) : sᶜ ≠ univ ↔ s.Nonempty := by
  simp [eq_univ_iff_forall, Finset.Nonempty]

theorem compl_singleton (a : α) : ({a} : Finset α)ᶜ = univ.erase a := by
  rw [compl_eq_univ_sdiff, sdiff_singleton_eq_erase]

theorem insert_inj_on' (s : Finset α) : Set.InjOn (fun a => insert a s) (sᶜ : Finset α) := by
  rw [coe_compl]
  exact s.insert_inj_on

theorem image_univ_of_surjective [Fintype β] {f : β → α} (hf : Surjective f) :
    univ.image f = univ :=
  eq_univ_of_forall <| hf.forall.2 fun _ => mem_image_of_mem _ <| mem_univ _

@[simp]
theorem image_univ_equiv [Fintype β] (f : β ≃ α) : univ.image f = univ :=
  Finset.image_univ_of_surjective f.surjective

@[simp] lemma univ_inter (s : Finset α) : univ ∩ s = s := by ext a; simp

@[simp] lemma inter_univ (s : Finset α) : s ∩ univ = s := by rw [inter_comm, univ_inter]

@[simp] lemma inter_eq_univ : s ∩ t = univ ↔ s = univ ∧ t = univ := inf_eq_top_iff

end BooleanAlgebra

-- @[simp] --Note this would loop with `Finset.univ_unique`
lemma singleton_eq_univ [Subsingleton α] (a : α) : ({a} : Finset α) = univ := by
  ext b; simp [Subsingleton.elim a b]


theorem map_univ_of_surjective [Fintype β] {f : β ↪ α} (hf : Surjective f) : univ.map f = univ :=
  eq_univ_of_forall <| hf.forall.2 fun _ => mem_map_of_mem _ <| mem_univ _

@[simp]
theorem map_univ_equiv [Fintype β] (f : β ≃ α) : univ.map f.toEmbedding = univ :=
  map_univ_of_surjective f.surjective

theorem univ_map_equiv_to_embedding {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) :
    univ.map e.toEmbedding = univ :=
  eq_univ_iff_forall.mpr fun b => mem_map.mpr ⟨e.symm b, mem_univ _, by simp⟩

@[simp]
theorem univ_filter_exists (f : α → β) [Fintype β] [DecidablePred fun y => ∃ x, f x = y]
    [DecidableEq β] : (Finset.univ.filter fun y => ∃ x, f x = y) = Finset.univ.image f := by
  ext
  simp

/-- Note this is a special case of `(Finset.image_preimage f univ _).symm`. -/
theorem univ_filter_mem_range (f : α → β) [Fintype β] [DecidablePred fun y => y ∈ Set.range f]
    [DecidableEq β] : (Finset.univ.filter fun y => y ∈ Set.range f) = Finset.univ.image f := by
  grind

theorem coe_filter_univ (p : α → Prop) [DecidablePred p] :
    (univ.filter p : Set α) = { x | p x } := by simp

end Fintypeα

@[simp] lemma subtype_eq_univ {p : α → Prop} [DecidablePred p] [Fintype {a // p a}] :
    s.subtype p = univ ↔ ∀ ⦃a⦄, p a → a ∈ s := by simp [Finset.ext_iff]

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

section DecEq

variable [Fintype α] [DecidableEq α]

@[simp]
lemma filter_univ_mem (s : Finset α) : univ.filter (· ∈ s) = s := by simp [filter_mem_eq_inter]

instance decidableCodisjoint : Decidable (Codisjoint s t) :=
  decidable_of_iff _ codisjoint_left.symm

instance decidableIsCompl : Decidable (IsCompl s t) :=
  decidable_of_iff' _ isCompl_iff

end DecEq

end Finset
