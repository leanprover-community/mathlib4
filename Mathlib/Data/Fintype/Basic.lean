/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Finset.Image

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

namespace Finset

variable [Fintype α] {s t : Finset α}

/-- `univ` is the universal finite set of type `Finset α` implied from
  the assumption `Fintype α`. -/
def univ : Finset α :=
  @Fintype.elems α _

@[simp]
theorem mem_univ (x : α) : x ∈ (univ : Finset α) :=
  Fintype.complete x

--Porting note: removing @[simp], simp can prove it
theorem mem_univ_val : ∀ x, x ∈ (univ : Finset α).1 :=
  mem_univ

theorem eq_univ_iff_forall : s = univ ↔ ∀ x, x ∈ s := by simp [ext_iff]

theorem eq_univ_of_forall : (∀ x, x ∈ s) → s = univ :=
  eq_univ_iff_forall.2

@[simp, norm_cast]
theorem coe_univ : ↑(univ : Finset α) = (Set.univ : Set α) := by ext; simp

@[simp, norm_cast]
theorem coe_eq_univ : (s : Set α) = Set.univ ↔ s = univ := by rw [← coe_univ, coe_inj]

theorem Nonempty.eq_univ [Subsingleton α] : s.Nonempty → s = univ := by
  rintro ⟨x, hx⟩
  refine' eq_univ_of_forall fun y => by rwa [Subsingleton.elim y x]

theorem univ_nonempty_iff : (univ : Finset α).Nonempty ↔ Nonempty α := by
  rw [← coe_nonempty, coe_univ, Set.nonempty_iff_univ_nonempty]

theorem univ_nonempty [Nonempty α] : (univ : Finset α).Nonempty :=
  univ_nonempty_iff.2 ‹_›

theorem univ_eq_empty_iff : (univ : Finset α) = ∅ ↔ IsEmpty α := by
  rw [← not_nonempty_iff, ← univ_nonempty_iff, not_nonempty_iff_eq_empty]

@[simp]
theorem univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅ :=
  univ_eq_empty_iff.2 ‹_›

@[simp]
theorem univ_unique [Unique α] : (univ : Finset α) = {default} :=
  Finset.ext fun x => iff_of_true (mem_univ _) <| mem_singleton.2 <| Subsingleton.elim x default

@[simp]
theorem subset_univ (s : Finset α) : s ⊆ univ := fun a _ => mem_univ a

instance boundedOrder : BoundedOrder (Finset α) :=
  { inferInstanceAs (OrderBot (Finset α)) with
    top := univ
    le_top := subset_univ }

@[simp]
theorem top_eq_univ : (⊤ : Finset α) = univ :=
  rfl

theorem ssubset_univ_iff {s : Finset α} : s ⊂ univ ↔ s ≠ univ :=
  @lt_top_iff_ne_top _ _ _ s

theorem codisjoint_left : Codisjoint s t ↔ ∀ ⦃a⦄, a ∉ s → a ∈ t := by
  classical simp [codisjoint_iff, eq_univ_iff_forall, or_iff_not_imp_left]

theorem codisjoint_right : Codisjoint s t ↔ ∀ ⦃a⦄, a ∉ t → a ∈ s :=
  Codisjoint_comm.trans codisjoint_left

section BooleanAlgebra

variable [DecidableEq α] {a : α}

instance booleanAlgebra : BooleanAlgebra (Finset α) :=
  GeneralizedBooleanAlgebra.toBooleanAlgebra

theorem sdiff_eq_inter_compl (s t : Finset α) : s \ t = s ∩ tᶜ :=
  sdiff_eq

theorem compl_eq_univ_sdiff (s : Finset α) : sᶜ = univ \ s :=
  rfl

@[simp]
theorem mem_compl : a ∈ sᶜ ↔ a ∉ s := by simp [compl_eq_univ_sdiff]

theorem not_mem_compl : a ∉ sᶜ ↔ a ∈ s := by rw [mem_compl, not_not]

@[simp, norm_cast]
theorem coe_compl (s : Finset α) : ↑sᶜ = (↑s : Set α)ᶜ :=
  Set.ext fun _ => mem_compl

@[simp] lemma compl_subset_compl : sᶜ ⊆ tᶜ ↔ t ⊆ s := @compl_le_compl_iff_le (Finset α) _ _ _
@[simp] lemma compl_ssubset_compl : sᶜ ⊂ tᶜ ↔ t ⊂ s := @compl_lt_compl_iff_lt (Finset α) _ _ _

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
  simp only [not_or, mem_insert, iff_self_iff, mem_compl, mem_erase]

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

theorem map_univ_of_surjective [Fintype β] {f : β ↪ α} (hf : Surjective f) : univ.map f = univ :=
  eq_univ_of_forall <| hf.forall.2 fun _ => mem_map_of_mem _ <| mem_univ _

@[simp]
theorem map_univ_equiv [Fintype β] (f : β ≃ α) : univ.map f.toEmbedding = univ :=
  map_univ_of_surjective f.surjective

@[simp]
theorem piecewise_univ [∀ i : α, Decidable (i ∈ (univ : Finset α))] {δ : α → Sort*}
    (f g : ∀ i, δ i) : univ.piecewise f g = f := by
  ext i
  simp [piecewise]

theorem piecewise_compl [DecidableEq α] (s : Finset α) [∀ i : α, Decidable (i ∈ s)]
    [∀ i : α, Decidable (i ∈ sᶜ)] {δ : α → Sort*} (f g : ∀ i, δ i) :
    sᶜ.piecewise f g = s.piecewise g f := by
  ext i
  simp [piecewise]

@[simp]
theorem piecewise_erase_univ {δ : α → Sort*} [DecidableEq α] (a : α) (f g : ∀ a, δ a) :
    (Finset.univ.erase a).piecewise f g = Function.update f a (g a) := by
  rw [← compl_singleton, piecewise_compl, piecewise_singleton]

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
  letI : DecidablePred (fun y => ∃ x, f x = y) := by simpa using ‹_›
  exact univ_filter_exists f

theorem coe_filter_univ (p : α → Prop) [DecidablePred p] : (univ.filter p : Set α) = { x | p x } :=
  by simp

@[simp] lemma subtype_eq_univ {p : α → Prop} [DecidablePred p] [Fintype {a // p a}] :
    s.subtype p = univ ↔ ∀ ⦃a⦄, p a → a ∈ s := by simp [ext_iff]

@[simp] lemma subtype_univ [Fintype α] (p : α → Prop) [DecidablePred p] [Fintype {a // p a}] :
    univ.subtype p = univ := by simp

end Finset

open Finset Function

namespace Fintype

instance decidablePiFintype {α} {β : α → Type*} [∀ a, DecidableEq (β a)] [Fintype α] :
    DecidableEq (∀ a, β a) := fun f g =>
  decidable_of_iff (∀ a ∈ @Fintype.elems α _, f a = g a)
    (by simp [Function.funext_iff, Fintype.complete])

instance decidableForallFintype {p : α → Prop} [DecidablePred p] [Fintype α] :
    Decidable (∀ a, p a) :=
  decidable_of_iff (∀ a ∈ @univ α _, p a) (by simp)

instance decidableExistsFintype {p : α → Prop} [DecidablePred p] [Fintype α] :
    Decidable (∃ a, p a) :=
  decidable_of_iff (∃ a ∈ @univ α _, p a) (by simp)

instance decidableMemRangeFintype [Fintype α] [DecidableEq β] (f : α → β) :
    DecidablePred (· ∈ Set.range f) := fun _ => Fintype.decidableExistsFintype

section BundledHoms

instance decidableEqEquivFintype [DecidableEq β] [Fintype α] : DecidableEq (α ≃ β) := fun a b =>
  decidable_of_iff (a.1 = b.1) Equiv.coe_fn_injective.eq_iff

instance decidableEqEmbeddingFintype [DecidableEq β] [Fintype α] : DecidableEq (α ↪ β) := fun a b =>
  decidable_of_iff ((a : α → β) = b) Function.Embedding.coe_injective.eq_iff

@[to_additive]
instance decidableEqOneHomFintype [DecidableEq β] [Fintype α] [One α] [One β] :
    DecidableEq (OneHom α β) := fun a b =>
  decidable_of_iff ((a : α → β) = b) (Injective.eq_iff FunLike.coe_injective)

@[to_additive]
instance decidableEqMulHomFintype [DecidableEq β] [Fintype α] [Mul α] [Mul β] :
    DecidableEq (α →ₙ* β) := fun a b =>
  decidable_of_iff ((a : α → β) = b) (Injective.eq_iff FunLike.coe_injective)

@[to_additive]
instance decidableEqMonoidHomFintype [DecidableEq β] [Fintype α] [MulOneClass α] [MulOneClass β] :
    DecidableEq (α →* β) := fun a b =>
  decidable_of_iff ((a : α → β) = b) (Injective.eq_iff FunLike.coe_injective)

instance decidableEqMonoidWithZeroHomFintype [DecidableEq β] [Fintype α] [MulZeroOneClass α]
    [MulZeroOneClass β] : DecidableEq (α →*₀ β) := fun a b =>
  decidable_of_iff ((a : α → β) = b) (Injective.eq_iff FunLike.coe_injective)

instance decidableEqRingHomFintype [DecidableEq β] [Fintype α] [Semiring α] [Semiring β] :
    DecidableEq (α →+* β) := fun a b =>
  decidable_of_iff ((a : α → β) = b) (Injective.eq_iff RingHom.coe_inj)

end BundledHoms

instance decidableInjectiveFintype [DecidableEq α] [DecidableEq β] [Fintype α] :
    DecidablePred (Injective : (α → β) → Prop) := fun x => by unfold Injective; infer_instance

instance decidableSurjectiveFintype [DecidableEq β] [Fintype α] [Fintype β] :
    DecidablePred (Surjective : (α → β) → Prop) := fun x => by unfold Surjective; infer_instance

instance decidableBijectiveFintype [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] :
    DecidablePred (Bijective : (α → β) → Prop) := fun x => by unfold Bijective; infer_instance

instance decidableRightInverseFintype [DecidableEq α] [Fintype α] (f : α → β) (g : β → α) :
    Decidable (Function.RightInverse f g) :=
  show Decidable (∀ x, g (f x) = x) by infer_instance

instance decidableLeftInverseFintype [DecidableEq β] [Fintype β] (f : α → β) (g : β → α) :
    Decidable (Function.LeftInverse f g) :=
  show Decidable (∀ x, f (g x) = x) by infer_instance

/-- Construct a proof of `Fintype α` from a universal multiset -/
def ofMultiset [DecidableEq α] (s : Multiset α) (H : ∀ x : α, x ∈ s) : Fintype α :=
  ⟨s.toFinset, by simpa using H⟩

/-- Construct a proof of `Fintype α` from a universal list -/
def ofList [DecidableEq α] (l : List α) (H : ∀ x : α, x ∈ l) : Fintype α :=
  ⟨l.toFinset, by simpa using H⟩

instance subsingleton (α : Type*) : Subsingleton (Fintype α) :=
  ⟨fun ⟨s₁, h₁⟩ ⟨s₂, h₂⟩ => by congr; simp [Finset.ext_iff, h₁, h₂]⟩

/-- Given a predicate that can be represented by a finset, the subtype
associated to the predicate is a fintype. -/
protected def subtype {p : α → Prop} (s : Finset α) (H : ∀ x : α, x ∈ s ↔ p x) :
    Fintype { x // p x } :=
  ⟨⟨s.1.pmap Subtype.mk fun x => (H x).1, s.nodup.pmap fun _ _ _ _ => congr_arg Subtype.val⟩,
    fun ⟨x, px⟩ => Multiset.mem_pmap.2 ⟨x, (H x).2 px, rfl⟩⟩

/-- Construct a fintype from a finset with the same elements. -/
def ofFinset {p : Set α} (s : Finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) : Fintype p :=
  Fintype.subtype s H

/-- If `f : α → β` is a bijection and `α` is a fintype, then `β` is also a fintype. -/
def ofBijective [Fintype α] (f : α → β) (H : Function.Bijective f) : Fintype β :=
  ⟨univ.map ⟨f, H.1⟩, fun b =>
    let ⟨_, e⟩ := H.2 b
    e ▸ mem_map_of_mem _ (mem_univ _)⟩

/-- If `f : α → β` is a surjection and `α` is a fintype, then `β` is also a fintype. -/
def ofSurjective [DecidableEq β] [Fintype α] (f : α → β) (H : Function.Surjective f) : Fintype β :=
  ⟨univ.image f, fun b =>
    let ⟨_, e⟩ := H b
    e ▸ mem_image_of_mem _ (mem_univ _)⟩

end Fintype

namespace Finset

variable [Fintype α] [DecidableEq α] {s t : Finset α}

instance decidableCodisjoint : Decidable (Codisjoint s t) :=
  decidable_of_iff _ codisjoint_left.symm

instance decidableIsCompl : Decidable (IsCompl s t) :=
  decidable_of_iff' _ isCompl_iff

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

theorem left_inv_of_invOfMemRange (b : Set.range f) : f (hf.invOfMemRange b) = b :=
  (Finset.choose_spec (fun a => f a = b) _ _).right

@[simp]
theorem right_inv_of_invOfMemRange (a : α) : hf.invOfMemRange ⟨f a, Set.mem_range_self a⟩ = a :=
  hf (Finset.choose_spec (fun a' => f a' = f a) _ _).right

theorem invFun_restrict [Nonempty α] : (Set.range f).restrict (invFun f) = hf.invOfMemRange := by
  ext ⟨b, h⟩
  apply hf
  simp [hf.left_inv_of_invOfMemRange, @invFun_eq _ _ _ f b (Set.mem_range.mp h)]

theorem invOfMemRange_surjective : Function.Surjective hf.invOfMemRange := fun a =>
  ⟨⟨f a, Set.mem_range_self a⟩, by simp⟩

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

@[simp]
theorem left_inv_of_invOfMemRange : f (f.invOfMemRange b) = b :=
  f.injective.left_inv_of_invOfMemRange b

@[simp]
theorem right_inv_of_invOfMemRange (a : α) : f.invOfMemRange ⟨f a, Set.mem_range_self a⟩ = a :=
  f.injective.right_inv_of_invOfMemRange a

theorem invFun_restrict [Nonempty α] : (Set.range f).restrict (invFun f) = f.invOfMemRange := by
  ext ⟨b, h⟩
  apply f.injective
  simp [f.left_inv_of_invOfMemRange, @invFun_eq _ _ _ f b (Set.mem_range.mp h)]

theorem invOfMemRange_surjective : Function.Surjective f.invOfMemRange := fun a =>
  ⟨⟨f a, Set.mem_range_self a⟩, by simp⟩

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

/-- If `f : α ≃ β` and `α` is a fintype, then `β` is also a fintype. -/
def ofEquiv (α : Type*) [Fintype α] (f : α ≃ β) : Fintype β :=
  ofBijective _ f.bijective

/-- Any subsingleton type with a witness is a fintype (with one term). -/
def ofSubsingleton (a : α) [Subsingleton α] : Fintype α :=
  ⟨{a}, fun _ => Finset.mem_singleton.2 (Subsingleton.elim _ _)⟩

@[simp]
theorem univ_ofSubsingleton (a : α) [Subsingleton α] : @univ _ (ofSubsingleton a) = {a} :=
  rfl

-- see Note [lower instance priority]
instance (priority := 100) ofIsEmpty [IsEmpty α] : Fintype α :=
  ⟨∅, isEmptyElim⟩

-- no-lint since while `Finset.univ_eq_empty` can prove this, it isn't applicable for `dsimp`.
/-- Note: this lemma is specifically about `Fintype.of_isEmpty`. For a statement about
arbitrary `Fintype` instances, use `Finset.univ_eq_empty`. -/
@[simp, nolint simpNF]
theorem univ_of_isEmpty [IsEmpty α] : @univ α _ = ∅ :=
  rfl

end Fintype

namespace Set

variable {s t : Set α}

/-- Construct a finset enumerating a set `s`, given a `Fintype` instance.  -/
def toFinset (s : Set α) [Fintype s] : Finset α :=
  (@Finset.univ s _).map <| Function.Embedding.subtype _

@[congr]
theorem toFinset_congr {s t : Set α} [Fintype s] [Fintype t] (h : s = t) :
    toFinset s = toFinset t := by subst h; congr; exact Subsingleton.elim _ _

@[simp]
theorem mem_toFinset {s : Set α} [Fintype s] {a : α} : a ∈ s.toFinset ↔ a ∈ s := by
  simp [toFinset]

/-- Many `Fintype` instances for sets are defined using an extensionally equal `Finset`.
Rewriting `s.toFinset` with `Set.toFinset_ofFinset` replaces the term with such a `Finset`. -/
theorem toFinset_ofFinset {p : Set α} (s : Finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) :
    @Set.toFinset _ p (Fintype.ofFinset s H) = s :=
  Finset.ext fun x => by rw [@mem_toFinset _ _ (id _), H]

/-- Membership of a set with a `Fintype` instance is decidable.

Using this as an instance leads to potential loops with `Subtype.fintype` under certain decidability
assumptions, so it should only be declared a local instance. -/
def decidableMemOfFintype [DecidableEq α] (s : Set α) [Fintype s] (a) : Decidable (a ∈ s) :=
  decidable_of_iff _ mem_toFinset

@[simp]
theorem coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : Set α) = s :=
  Set.ext fun _ => mem_toFinset

@[simp]
theorem toFinset_nonempty {s : Set α} [Fintype s] : s.toFinset.Nonempty ↔ s.Nonempty := by
  rw [← Finset.coe_nonempty, coe_toFinset]

@[simp]
theorem toFinset_inj {s t : Set α} [Fintype s] [Fintype t] : s.toFinset = t.toFinset ↔ s = t :=
  ⟨fun h => by rw [← s.coe_toFinset, h, t.coe_toFinset], fun h => by simp [h] ⟩

@[mono]
theorem toFinset_subset_toFinset [Fintype s] [Fintype t] : s.toFinset ⊆ t.toFinset ↔ s ⊆ t := by
  simp [Finset.subset_iff, Set.subset_def]

@[simp]
theorem toFinset_ssubset [Fintype s] {t : Finset α} : s.toFinset ⊂ t ↔ s ⊂ t := by
  rw [← Finset.coe_ssubset, coe_toFinset]

@[simp]
theorem subset_toFinset {s : Finset α} [Fintype t] : s ⊆ t.toFinset ↔ ↑s ⊆ t := by
  rw [← Finset.coe_subset, coe_toFinset]

@[simp]
theorem ssubset_toFinset {s : Finset α} [Fintype t] : s ⊂ t.toFinset ↔ ↑s ⊂ t := by
  rw [← Finset.coe_ssubset, coe_toFinset]

@[mono]
theorem toFinset_ssubset_toFinset [Fintype s] [Fintype t] : s.toFinset ⊂ t.toFinset ↔ s ⊂ t := by
  simp only [Finset.ssubset_def, toFinset_subset_toFinset, ssubset_def]

@[simp]
theorem toFinset_subset [Fintype s] {t : Finset α} : s.toFinset ⊆ t ↔ s ⊆ t := by
  rw [← Finset.coe_subset, coe_toFinset]

alias ⟨_, toFinset_mono⟩ := toFinset_subset_toFinset

alias ⟨_, toFinset_strict_mono⟩ := toFinset_ssubset_toFinset

@[simp]
theorem disjoint_toFinset [Fintype s] [Fintype t] :
    Disjoint s.toFinset t.toFinset ↔ Disjoint s t := by simp only [← disjoint_coe, coe_toFinset]

section DecidableEq

variable [DecidableEq α] (s t) [Fintype s] [Fintype t]

@[simp]
theorem toFinset_inter [Fintype (s ∩ t : Set _)] : (s ∩ t).toFinset = s.toFinset ∩ t.toFinset := by
  ext
  simp

@[simp]
theorem toFinset_union [Fintype (s ∪ t : Set _)] : (s ∪ t).toFinset = s.toFinset ∪ t.toFinset := by
  ext
  simp

@[simp]
theorem toFinset_diff [Fintype (s \ t : Set _)] : (s \ t).toFinset = s.toFinset \ t.toFinset := by
  ext
  simp

@[simp]
theorem toFinset_symmDiff [Fintype (s ∆ t : Set _)] :
    (s ∆ t).toFinset = s.toFinset ∆ t.toFinset := by
  ext
  simp [mem_symmDiff, Finset.mem_symmDiff]

@[simp]
theorem toFinset_compl [Fintype α] [Fintype (sᶜ : Set _)] : sᶜ.toFinset = s.toFinsetᶜ := by
  ext
  simp

end DecidableEq

-- TODO The `↥` circumvents an elaboration bug. See comment on `Set.toFinset_univ`.
@[simp]
theorem toFinset_empty [Fintype (∅ : Set α)] : (∅ : Set α).toFinset = ∅ := by
  ext
  simp

/- TODO Without the coercion arrow (`↥`) there is an elaboration bug in the following two;
it essentially infers `Fintype.{v} (Set.univ.{u} : Set α)` with `v` and `u` distinct.
Reported in leanprover-community/lean#672 -/
@[simp]
theorem toFinset_univ [Fintype α] [Fintype (Set.univ : Set α)] :
    (Set.univ : Set α).toFinset = Finset.univ := by
  ext
  simp

@[simp]
theorem toFinset_eq_empty [Fintype s] : s.toFinset = ∅ ↔ s = ∅ := by
  rw [← toFinset_empty, toFinset_inj]

@[simp]
theorem toFinset_eq_univ [Fintype α] [Fintype s] : s.toFinset = Finset.univ ↔ s = univ := by
  rw [← coe_inj, coe_toFinset, coe_univ]

@[simp]
theorem toFinset_setOf [Fintype α] (p : α → Prop) [DecidablePred p] [Fintype { x | p x }] :
    { x | p x }.toFinset = Finset.univ.filter p := by
  ext
  simp

--@[simp] Porting note: removing simp, simp can prove it
theorem toFinset_ssubset_univ [Fintype α] {s : Set α} [Fintype s] :
    s.toFinset ⊂ Finset.univ ↔ s ⊂ univ := by rw [← coe_ssubset, coe_toFinset, coe_univ]

@[simp]
theorem toFinset_image [DecidableEq β] (f : α → β) (s : Set α) [Fintype s] [Fintype (f '' s)] :
    (f '' s).toFinset = s.toFinset.image f :=
  Finset.coe_injective <| by simp

@[simp]
theorem toFinset_range [DecidableEq α] [Fintype β] (f : β → α) [Fintype (Set.range f)] :
    (Set.range f).toFinset = Finset.univ.image f := by
  ext
  simp

@[simp] -- porting note: new attribute
theorem toFinset_singleton (a : α) [Fintype ({a} : Set α)] : ({a} : Set α).toFinset = {a} := by
  ext
  simp

@[simp]
theorem toFinset_insert [DecidableEq α] {a : α} {s : Set α} [Fintype (insert a s : Set α)]
    [Fintype s] : (insert a s).toFinset = insert a s.toFinset := by
  ext
  simp

theorem filter_mem_univ_eq_toFinset [Fintype α] (s : Set α) [Fintype s] [DecidablePred (· ∈ s)] :
    Finset.univ.filter (· ∈ s) = s.toFinset := by
  ext
  simp only [Finset.mem_univ, decide_eq_true_eq, forall_true_left, mem_filter,
    true_and, mem_toFinset]

end Set

@[simp]
theorem Finset.toFinset_coe (s : Finset α) [Fintype (s : Set α)] : (s : Set α).toFinset = s :=
  ext fun _ => Set.mem_toFinset

instance Fin.fintype (n : ℕ) : Fintype (Fin n) :=
  ⟨⟨List.finRange n, List.nodup_finRange n⟩, List.mem_finRange⟩

theorem Fin.univ_def (n : ℕ) : (univ : Finset (Fin n)) = ⟨List.finRange n, List.nodup_finRange n⟩ :=
  rfl

@[simp] theorem List.toFinset_finRange (n : ℕ) : (List.finRange n).toFinset = Finset.univ := by
  ext; simp

@[simp]
theorem Fin.image_succAbove_univ {n : ℕ} (i : Fin (n + 1)) : univ.image i.succAbove = {i}ᶜ := by
  ext m
  simp

@[simp]
theorem Fin.image_succ_univ (n : ℕ) : (univ : Finset (Fin n)).image Fin.succ = {0}ᶜ := by
  rw [← Fin.succAbove_zero, Fin.image_succAbove_univ]

@[simp]
theorem Fin.image_castSucc (n : ℕ) :
    (univ : Finset (Fin n)).image Fin.castSucc = {Fin.last n}ᶜ := by
  rw [← Fin.succAbove_last, Fin.image_succAbove_univ]

/- The following three lemmas use `Finset.cons` instead of `insert` and `Finset.map` instead of
`Finset.image` to reduce proof obligations downstream. -/
/-- Embed `Fin n` into `Fin (n + 1)` by prepending zero to the `univ` -/
theorem Fin.univ_succ (n : ℕ) :
    (univ : Finset (Fin (n + 1))) =
      cons 0 (univ.map ⟨Fin.succ, Fin.succ_injective _⟩) (by simp [map_eq_image]) :=
  by simp [map_eq_image]

/-- Embed `Fin n` into `Fin (n + 1)` by appending a new `Fin.last n` to the `univ` -/
theorem Fin.univ_castSuccEmb (n : ℕ) :
    (univ : Finset (Fin (n + 1))) =
      cons (Fin.last n) (univ.map Fin.castSuccEmb.toEmbedding) (by simp [map_eq_image]) :=
  by simp [map_eq_image]

/-- Embed `Fin n` into `Fin (n + 1)` by inserting
around a specified pivot `p : Fin (n + 1)` into the `univ` -/
theorem Fin.univ_succAbove (n : ℕ) (p : Fin (n + 1)) :
    (univ : Finset (Fin (n + 1))) =
      cons p (univ.map <| (Fin.succAboveEmb p).toEmbedding) (by simp) :=
  by simp [map_eq_image]

@[instance]
def Unique.fintype {α : Type*} [Unique α] : Fintype α :=
  Fintype.ofSubsingleton default

/-- Short-circuit instance to decrease search for `Unique.fintype`,
since that relies on a subsingleton elimination for `Unique`. -/
instance Fintype.subtypeEq (y : α) : Fintype { x // x = y } :=
  Fintype.subtype {y} (by simp)

/-- Short-circuit instance to decrease search for `Unique.fintype`,
since that relies on a subsingleton elimination for `Unique`. -/
instance Fintype.subtypeEq' (y : α) : Fintype { x // y = x } :=
  Fintype.subtype {y} (by simp [eq_comm])

--Porting note: removing @[simp], simp can prove it
theorem Fintype.univ_empty : @univ Empty _ = ∅ :=
  rfl

--@[simp] Porting note: removing simp, simp can prove it
theorem Fintype.univ_pempty : @univ PEmpty _ = ∅ :=
  rfl

instance Unit.fintype : Fintype Unit :=
  Fintype.ofSubsingleton ()

theorem Fintype.univ_unit : @univ Unit _ = {()} :=
  rfl

instance PUnit.fintype : Fintype PUnit :=
  Fintype.ofSubsingleton PUnit.unit

--@[simp] Porting note: removing simp, simp can prove it
theorem Fintype.univ_punit : @univ PUnit _ = {PUnit.unit} :=
  rfl

instance Bool.fintype : Fintype Bool :=
  ⟨⟨{true, false}, by simp⟩, fun x => by cases x <;> simp⟩

@[simp]
theorem Fintype.univ_bool : @univ Bool _ = {true, false} :=
  rfl

instance Additive.fintype : ∀ [Fintype α], Fintype (Additive α) :=
  Fintype.ofEquiv α Additive.ofMul

instance Multiplicative.fintype : ∀ [Fintype α], Fintype (Multiplicative α) :=
  Fintype.ofEquiv α Multiplicative.ofAdd

/-- Given that `α × β` is a fintype, `α` is also a fintype. -/
def Fintype.prodLeft {α β} [DecidableEq α] [Fintype (α × β)] [Nonempty β] : Fintype α :=
  ⟨(@univ (α × β) _).image Prod.fst, fun a => by simp⟩

/-- Given that `α × β` is a fintype, `β` is also a fintype. -/
def Fintype.prodRight {α β} [DecidableEq β] [Fintype (α × β)] [Nonempty α] : Fintype β :=
  ⟨(@univ (α × β) _).image Prod.snd, fun b => by simp⟩

instance ULift.fintype (α : Type*) [Fintype α] : Fintype (ULift α) :=
  Fintype.ofEquiv _ Equiv.ulift.symm

instance PLift.fintype (α : Type*) [Fintype α] : Fintype (PLift α) :=
  Fintype.ofEquiv _ Equiv.plift.symm

instance OrderDual.fintype (α : Type*) [Fintype α] : Fintype αᵒᵈ :=
  ‹Fintype α›

instance OrderDual.finite (α : Type*) [Finite α] : Finite αᵒᵈ :=
  ‹Finite α›

instance Lex.fintype (α : Type*) [Fintype α] : Fintype (Lex α) :=
  ‹Fintype α›

section Finset

/-! ### `Fintype (s : Finset α)` -/


instance Finset.fintypeCoeSort {α : Type u} (s : Finset α) : Fintype s :=
  ⟨s.attach, s.mem_attach⟩

@[simp]
theorem Finset.univ_eq_attach {α : Type u} (s : Finset α) : (univ : Finset s) = s.attach :=
  rfl

end Finset

theorem Fintype.coe_image_univ [Fintype α] [DecidableEq β] {f : α → β} :
    ↑(Finset.image f Finset.univ) = Set.range f := by
  ext x
  simp

instance List.Subtype.fintype [DecidableEq α] (l : List α) : Fintype { x // x ∈ l } :=
  Fintype.ofList l.attach l.mem_attach

instance Multiset.Subtype.fintype [DecidableEq α] (s : Multiset α) : Fintype { x // x ∈ s } :=
  Fintype.ofMultiset s.attach s.mem_attach

instance Finset.Subtype.fintype (s : Finset α) : Fintype { x // x ∈ s } :=
  ⟨s.attach, s.mem_attach⟩

instance FinsetCoe.fintype (s : Finset α) : Fintype (↑s : Set α) :=
  Finset.Subtype.fintype s

theorem Finset.attach_eq_univ {s : Finset α} : s.attach = Finset.univ :=
  rfl

instance PLift.fintypeProp (p : Prop) [Decidable p] : Fintype (PLift p) :=
  ⟨if h : p then {⟨h⟩} else ∅, fun ⟨h⟩ => by simp [h]⟩

instance Prop.fintype : Fintype Prop :=
  ⟨⟨{True, False}, by simp [true_ne_false]⟩, Classical.cases (by simp) (by simp)⟩

@[simp]
theorem Fintype.univ_Prop : (Finset.univ : Finset Prop) = {True, False} :=
  Finset.eq_of_veq <| by simp; rfl

instance Subtype.fintype (p : α → Prop) [DecidablePred p] [Fintype α] : Fintype { x // p x } :=
  Fintype.subtype (univ.filter p) (by simp)

/-- A set on a fintype, when coerced to a type, is a fintype. -/
def setFintype [Fintype α] (s : Set α) [DecidablePred (· ∈ s)] : Fintype s :=
  Subtype.fintype fun x => x ∈ s

section

variable (α)

/-- The `αˣ` type is equivalent to a subtype of `α × α`. -/
@[simps]
def unitsEquivProdSubtype [Monoid α] : αˣ ≃ { p : α × α // p.1 * p.2 = 1 ∧ p.2 * p.1 = 1 }
    where
  toFun u := ⟨(u, ↑u⁻¹), u.val_inv, u.inv_val⟩
  invFun p := Units.mk (p : α × α).1 (p : α × α).2 p.prop.1 p.prop.2
  left_inv _ := Units.ext rfl
  right_inv _ := Subtype.ext <| Prod.ext rfl rfl

/-- In a `GroupWithZero` `α`, the unit group `αˣ` is equivalent to the subtype of nonzero
elements. -/
@[simps]
def unitsEquivNeZero [GroupWithZero α] : αˣ ≃ { a : α // a ≠ 0 } :=
  ⟨fun a => ⟨a, a.ne_zero⟩, fun a => Units.mk0 _ a.prop, fun _ => Units.ext rfl, fun _ =>
    Subtype.ext rfl⟩

end

namespace Fintype
variable [Fintype α]

/-- Given `Fintype α`, `finsetEquivSet` is the equiv between `Finset α` and `Set α`. (All
sets on a finite type are finite.) -/
noncomputable def finsetEquivSet : Finset α ≃ Set α where
  toFun := (↑)
  invFun := by classical exact fun s => s.toFinset
  left_inv s := by convert Finset.toFinset_coe s
  right_inv s := by classical exact s.coe_toFinset

@[simp, norm_cast] lemma coe_finsetEquivSet : ⇑finsetEquivSet = ((↑) : Finset α → Set α) := rfl

@[simp] lemma finsetEquivSet_apply (s : Finset α) : finsetEquivSet s = s := rfl

@[simp] lemma finsetEquivSet_symm_apply (s : Set α) [Fintype s] :
    finsetEquivSet.symm s = s.toFinset := by
  simp [finsetEquivSet]; congr; exact Subsingleton.elim _ _

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
  Fintype.ofSurjective Quotient.mk'' fun x => Quotient.inductionOn x fun x => ⟨x, rfl⟩

instance PSigma.fintypePropLeft {α : Prop} {β : α → Type*} [Decidable α] [∀ a, Fintype (β a)] :
    Fintype (Σ'a, β a) :=
  if h : α then Fintype.ofEquiv (β h) ⟨fun x => ⟨h, x⟩, PSigma.snd, fun _ => rfl, fun ⟨_, _⟩ => rfl⟩
  else ⟨∅, fun x => (h x.1).elim⟩

instance PSigma.fintypePropRight {α : Type*} {β : α → Prop} [∀ a, Decidable (β a)] [Fintype α] :
    Fintype (Σ'a, β a) :=
  Fintype.ofEquiv { a // β a }
    ⟨fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨_, _⟩ => rfl, fun ⟨_, _⟩ => rfl⟩

instance PSigma.fintypePropProp {α : Prop} {β : α → Prop} [Decidable α] [∀ a, Decidable (β a)] :
    Fintype (Σ'a, β a) :=
  if h : ∃ a, β a then ⟨{⟨h.fst, h.snd⟩}, fun ⟨_, _⟩ => by simp⟩ else ⟨∅, fun ⟨x, y⟩ =>
    (h ⟨x, y⟩).elim⟩

instance pfunFintype (p : Prop) [Decidable p] (α : p → Type*) [∀ hp, Fintype (α hp)] :
    Fintype (∀ hp : p, α hp) :=
  if hp : p then Fintype.ofEquiv (α hp) ⟨fun a _ => a, fun f => f hp, fun _ => rfl, fun _ => rfl⟩
  else ⟨singleton fun h => (hp h).elim, fun h => mem_singleton.2
    (funext $ fun x => by contradiction)⟩

theorem mem_image_univ_iff_mem_range {α β : Type*} [Fintype α] [DecidableEq β] {f : α → β}
    {b : β} : b ∈ univ.image f ↔ b ∈ Set.range f := by simp

namespace Fintype

section Choose

open Fintype Equiv

variable [Fintype α] (p : α → Prop) [DecidablePred p]

/-- Given a fintype `α` and a predicate `p`, associate to a proof that there is a unique element of
`α` satisfying `p` this unique element, as an element of the corresponding subtype. -/
def chooseX (hp : ∃! a : α, p a) : { a // p a } :=
  ⟨Finset.choose p univ (by simp; exact hp), Finset.choose_property _ _ _⟩

/-- Given a fintype `α` and a predicate `p`, associate to a proof that there is a unique element of
`α` satisfying `p` this unique element, as an element of `α`. -/
def choose (hp : ∃! a, p a) : α :=
  chooseX p hp

theorem choose_spec (hp : ∃! a, p a) : p (choose p hp) :=
  (chooseX p hp).property

-- @[simp] Porting note: removing simp, never applies
theorem choose_subtype_eq {α : Type*} (p : α → Prop) [Fintype { a : α // p a }] [DecidableEq α]
    (x : { a : α // p a })
    (h : ∃! a : { a // p a }, (a : α) = x :=
      ⟨x, rfl, fun y hy => by simpa [Subtype.ext_iff] using hy⟩) :
    Fintype.choose (fun y : { a : α // p a } => (y : α) = x) h = x := by
  rw [Subtype.ext_iff, Fintype.choose_spec (fun y : { a : α // p a } => (y : α) = x) _]

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

theorem leftInverse_bijInv (f_bij : Bijective f) : LeftInverse (bijInv f_bij) f := fun a =>
  f_bij.left (choose_spec (fun a' => f a' = f a) _)

theorem rightInverse_bijInv (f_bij : Bijective f) : RightInverse (bijInv f_bij) f := fun b =>
  choose_spec (fun a' => f a' = b) _

theorem bijective_bijInv (f_bij : Bijective f) : Bijective (bijInv f_bij) :=
  ⟨(rightInverse_bijInv _).injective, (leftInverse_bijInv _).surjective⟩

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

/-- A `Nonempty` `Fintype` constructively contains an element.
-/
def truncOfNonemptyFintype (α) [Nonempty α] [Fintype α] : Trunc α :=
  truncOfMultisetExistsMem Finset.univ.val (by simp)

/-- By iterating over the elements of a fintype, we can lift an existential statement `∃ a, P a`
to `Trunc (Σ' a, P a)`, containing data.
-/
def truncSigmaOfExists {α} [Fintype α] {P : α → Prop} [DecidablePred P] (h : ∃ a, P a) :
    Trunc (Σ'a, P a) :=
  @truncOfNonemptyFintype (Σ'a, P a) ((Exists.elim h) fun a ha => ⟨⟨a, ha⟩⟩) _

end Trunc

namespace Multiset

variable [Fintype α] [Fintype β]

@[simp]
theorem count_univ [DecidableEq α] (a : α) : count a Finset.univ.val = 1 :=
  count_eq_one_of_mem Finset.univ.nodup (Finset.mem_univ _)

@[simp]
theorem map_univ_val_equiv (e : α ≃ β) :
    map e univ.val = univ.val := by
  rw [←congr_arg Finset.val (Finset.map_univ_equiv e), Finset.map_val, Equiv.coe_toEmbedding]

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
  decreasing_by exact i.2

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
    refine' ⟨f, A, fun m n hmn => _⟩
    conv_rhs => rw [hf]
    rw [seqOfForallFinsetExistsAux]
    apply
      (Classical.choose_spec
          (h' (Finset.image (fun i : Fin n => f i) (Finset.univ : Finset (Fin n)))) (by simp [A])).2
    exact Finset.mem_image.2 ⟨⟨m, hmn⟩, Finset.mem_univ _, rfl⟩

/-- Induction principle to build a sequence, by adding one point at a time satisfying a given
symmetric relation with respect to all the previously chosen points.

More precisely, Assume that, for any finite set `s`, one can find another point satisfying
some relation `r` with respect to all the points in `s`. Then one may construct a
function `f : ℕ → α` such that `r (f m) (f n)` holds whenever `m ≠ n`.
We also ensure that all constructed points satisfy a given predicate `P`. -/
theorem exists_seq_of_forall_finset_exists' {α : Type*} (P : α → Prop) (r : α → α → Prop)
    [IsSymm α r] (h : ∀ s : Finset α, (∀ x ∈ s, P x) → ∃ y, P y ∧ ∀ x ∈ s, r x y) :
    ∃ f : ℕ → α, (∀ n, P (f n)) ∧ ∀ m n, m ≠ n → r (f m) (f n) := by
  rcases exists_seq_of_forall_finset_exists P r h with ⟨f, hf, hf'⟩
  refine' ⟨f, hf, fun m n hmn => _⟩
  rcases lt_trichotomy m n with (h | rfl | h)
  · exact hf' m n h
  · exact (hmn rfl).elim
  · apply symm
    exact hf' n m h
