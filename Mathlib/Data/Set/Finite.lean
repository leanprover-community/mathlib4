/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kyle Miller
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finite.Basic
import Mathlib.Data.Set.Functor
import Mathlib.Data.Set.Lattice

#align_import data.set.finite from "leanprover-community/mathlib"@"65a1391a0106c9204fe45bc73a039f056558cb83"

/-!
# Finite sets

This file defines predicates for finite and infinite sets and provides
`Fintype` instances for many set constructions. It also proves basic facts
about finite sets and gives ways to manipulate `Set.Finite` expressions.

## Main definitions

* `Set.Finite : Set α → Prop`
* `Set.Infinite : Set α → Prop`
* `Set.toFinite` to prove `Set.Finite` for a `Set` from a `Finite` instance.
* `Set.Finite.toFinset` to noncomputably produce a `Finset` from a `Set.Finite` proof.
  (See `Set.toFinset` for a computable version.)

## Implementation

A finite set is defined to be a set whose coercion to a type has a `Finite` instance.

There are two components to finiteness constructions. The first is `Fintype` instances for each
construction. This gives a way to actually compute a `Finset` that represents the set, and these
may be accessed using `set.toFinset`. This gets the `Finset` in the correct form, since otherwise
`Finset.univ : Finset s` is a `Finset` for the subtype for `s`. The second component is
"constructors" for `Set.Finite` that give proofs that `Fintype` instances exist classically given
other `Set.Finite` proofs. Unlike the `Fintype` instances, these *do not* use any decidability
instances since they do not compute anything.

## Tags

finite sets
-/

assert_not_exists OrderedRing
assert_not_exists MonoidWithZero

open Set Function

universe u v w x

variable {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

namespace Set

/-- A set is finite if the corresponding `Subtype` is finite,
i.e., if there exists a natural `n : ℕ` and an equivalence `s ≃ Fin n`. -/
protected def Finite (s : Set α) : Prop := Finite s
#align set.finite Set.Finite

-- The `protected` attribute does not take effect within the same namespace block.
end Set

namespace Set

theorem finite_def {s : Set α} : s.Finite ↔ Nonempty (Fintype s) :=
  finite_iff_nonempty_fintype s
#align set.finite_def Set.finite_def

protected alias ⟨Finite.nonempty_fintype, _⟩ := finite_def
#align set.finite.nonempty_fintype Set.Finite.nonempty_fintype

theorem finite_coe_iff {s : Set α} : Finite s ↔ s.Finite := .rfl
#align set.finite_coe_iff Set.finite_coe_iff

/-- Constructor for `Set.Finite` using a `Finite` instance. -/
theorem toFinite (s : Set α) [Finite s] : s.Finite := ‹_›
#align set.to_finite Set.toFinite

/-- Construct a `Finite` instance for a `Set` from a `Finset` with the same elements. -/
protected theorem Finite.ofFinset {p : Set α} (s : Finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) : p.Finite :=
  have := Fintype.ofFinset s H; p.toFinite
#align set.finite.of_finset Set.Finite.ofFinset

/-- Projection of `Set.Finite` to its `Finite` instance.
This is intended to be used with dot notation.
See also `Set.Finite.Fintype` and `Set.Finite.nonempty_fintype`. -/
protected theorem Finite.to_subtype {s : Set α} (h : s.Finite) : Finite s := h
#align set.finite.to_subtype Set.Finite.to_subtype

/-- A finite set coerced to a type is a `Fintype`.
This is the `Fintype` projection for a `Set.Finite`.

Note that because `Finite` isn't a typeclass, this definition will not fire if it
is made into an instance -/
protected noncomputable def Finite.fintype {s : Set α} (h : s.Finite) : Fintype s :=
  h.nonempty_fintype.some
#align set.finite.fintype Set.Finite.fintype

/-- Using choice, get the `Finset` that represents this `Set`. -/
protected noncomputable def Finite.toFinset {s : Set α} (h : s.Finite) : Finset α :=
  @Set.toFinset _ _ h.fintype
#align set.finite.to_finset Set.Finite.toFinset

theorem Finite.toFinset_eq_toFinset {s : Set α} [Fintype s] (h : s.Finite) :
    h.toFinset = s.toFinset := by
  -- Porting note: was `rw [Finite.toFinset]; congr`
  -- in Lean 4, a goal is left after `congr`
  have : h.fintype = ‹_› := Subsingleton.elim _ _
  rw [Finite.toFinset, this]
#align set.finite.to_finset_eq_to_finset Set.Finite.toFinset_eq_toFinset

@[simp]
theorem toFinite_toFinset (s : Set α) [Fintype s] : s.toFinite.toFinset = s.toFinset :=
  s.toFinite.toFinset_eq_toFinset
#align set.to_finite_to_finset Set.toFinite_toFinset

theorem Finite.exists_finset {s : Set α} (h : s.Finite) :
    ∃ s' : Finset α, ∀ a : α, a ∈ s' ↔ a ∈ s := by
  cases h.nonempty_fintype
  exact ⟨s.toFinset, fun _ => mem_toFinset⟩
#align set.finite.exists_finset Set.Finite.exists_finset

theorem Finite.exists_finset_coe {s : Set α} (h : s.Finite) : ∃ s' : Finset α, ↑s' = s := by
  cases h.nonempty_fintype
  exact ⟨s.toFinset, s.coe_toFinset⟩
#align set.finite.exists_finset_coe Set.Finite.exists_finset_coe

/-- Finite sets can be lifted to finsets. -/
instance : CanLift (Set α) (Finset α) (↑) Set.Finite where prf _ hs := hs.exists_finset_coe

/-- A set is infinite if it is not finite.

This is protected so that it does not conflict with global `Infinite`. -/
protected def Infinite (s : Set α) : Prop :=
  ¬s.Finite
#align set.infinite Set.Infinite

@[simp]
theorem not_infinite {s : Set α} : ¬s.Infinite ↔ s.Finite :=
  not_not
#align set.not_infinite Set.not_infinite

alias ⟨_, Finite.not_infinite⟩ := not_infinite
#align set.finite.not_infinite Set.Finite.not_infinite

attribute [simp] Finite.not_infinite

/-- See also `finite_or_infinite`, `fintypeOrInfinite`. -/
protected theorem finite_or_infinite (s : Set α) : s.Finite ∨ s.Infinite :=
  em _
#align set.finite_or_infinite Set.finite_or_infinite

protected theorem infinite_or_finite (s : Set α) : s.Infinite ∨ s.Finite :=
  em' _
#align set.infinite_or_finite Set.infinite_or_finite

/-! ### Basic properties of `Set.Finite.toFinset` -/


namespace Finite

variable {s t : Set α} {a : α} (hs : s.Finite) {ht : t.Finite}

@[simp]
protected theorem mem_toFinset : a ∈ hs.toFinset ↔ a ∈ s :=
  @mem_toFinset _ _ hs.fintype _
#align set.finite.mem_to_finset Set.Finite.mem_toFinset

@[simp]
protected theorem coe_toFinset : (hs.toFinset : Set α) = s :=
  @coe_toFinset _ _ hs.fintype
#align set.finite.coe_to_finset Set.Finite.coe_toFinset

@[simp]
protected theorem toFinset_nonempty : hs.toFinset.Nonempty ↔ s.Nonempty := by
  rw [← Finset.coe_nonempty, Finite.coe_toFinset]
#align set.finite.to_finset_nonempty Set.Finite.toFinset_nonempty

/-- Note that this is an equality of types not holding definitionally. Use wisely. -/
theorem coeSort_toFinset : ↥hs.toFinset = ↥s := by
  rw [← Finset.coe_sort_coe _, hs.coe_toFinset]
#align set.finite.coe_sort_to_finset Set.Finite.coeSort_toFinset

/-- The identity map, bundled as an equivalence between the subtypes of `s : Set α` and of
`h.toFinset : Finset α`, where `h` is a proof of finiteness of `s`. -/
@[simps!] def subtypeEquivToFinset : {x // x ∈ s} ≃ {x // x ∈ hs.toFinset} :=
  (Equiv.refl α).subtypeEquiv fun _ ↦ hs.mem_toFinset.symm

variable {hs}

@[simp]
protected theorem toFinset_inj : hs.toFinset = ht.toFinset ↔ s = t :=
  @toFinset_inj _ _ _ hs.fintype ht.fintype
#align set.finite.to_finset_inj Set.Finite.toFinset_inj

@[simp]
theorem toFinset_subset {t : Finset α} : hs.toFinset ⊆ t ↔ s ⊆ t := by
  rw [← Finset.coe_subset, Finite.coe_toFinset]
#align set.finite.to_finset_subset Set.Finite.toFinset_subset

@[simp]
theorem toFinset_ssubset {t : Finset α} : hs.toFinset ⊂ t ↔ s ⊂ t := by
  rw [← Finset.coe_ssubset, Finite.coe_toFinset]
#align set.finite.to_finset_ssubset Set.Finite.toFinset_ssubset

@[simp]
theorem subset_toFinset {s : Finset α} : s ⊆ ht.toFinset ↔ ↑s ⊆ t := by
  rw [← Finset.coe_subset, Finite.coe_toFinset]
#align set.finite.subset_to_finset Set.Finite.subset_toFinset

@[simp]
theorem ssubset_toFinset {s : Finset α} : s ⊂ ht.toFinset ↔ ↑s ⊂ t := by
  rw [← Finset.coe_ssubset, Finite.coe_toFinset]
#align set.finite.ssubset_to_finset Set.Finite.ssubset_toFinset

@[mono]
protected theorem toFinset_subset_toFinset : hs.toFinset ⊆ ht.toFinset ↔ s ⊆ t := by
  simp only [← Finset.coe_subset, Finite.coe_toFinset]
#align set.finite.to_finset_subset_to_finset Set.Finite.toFinset_subset_toFinset

@[mono]
protected theorem toFinset_ssubset_toFinset : hs.toFinset ⊂ ht.toFinset ↔ s ⊂ t := by
  simp only [← Finset.coe_ssubset, Finite.coe_toFinset]
#align set.finite.to_finset_ssubset_to_finset Set.Finite.toFinset_ssubset_toFinset

alias ⟨_, toFinset_mono⟩ := Finite.toFinset_subset_toFinset
#align set.finite.to_finset_mono Set.Finite.toFinset_mono

alias ⟨_, toFinset_strictMono⟩ := Finite.toFinset_ssubset_toFinset
#align set.finite.to_finset_strict_mono Set.Finite.toFinset_strictMono

-- Porting note: attribute [protected] doesn't work
-- attribute [protected] toFinset_mono toFinset_strictMono

-- Porting note: `simp` can simplify LHS but then it simplifies something
-- in the generated `Fintype {x | p x}` instance and fails to apply `Set.toFinset_setOf`
@[simp high]
protected theorem toFinset_setOf [Fintype α] (p : α → Prop) [DecidablePred p]
    (h : { x | p x }.Finite) : h.toFinset = Finset.univ.filter p := by
  ext
  -- Porting note: `simp` doesn't use the `simp` lemma `Set.toFinset_setOf` without the `_`
  simp [Set.toFinset_setOf _]
#align set.finite.to_finset_set_of Set.Finite.toFinset_setOf

@[simp]
nonrec theorem disjoint_toFinset {hs : s.Finite} {ht : t.Finite} :
    Disjoint hs.toFinset ht.toFinset ↔ Disjoint s t :=
  @disjoint_toFinset _ _ _ hs.fintype ht.fintype
#align set.finite.disjoint_to_finset Set.Finite.disjoint_toFinset

protected theorem toFinset_inter [DecidableEq α] (hs : s.Finite) (ht : t.Finite)
    (h : (s ∩ t).Finite) : h.toFinset = hs.toFinset ∩ ht.toFinset := by
  ext
  simp
#align set.finite.to_finset_inter Set.Finite.toFinset_inter

protected theorem toFinset_union [DecidableEq α] (hs : s.Finite) (ht : t.Finite)
    (h : (s ∪ t).Finite) : h.toFinset = hs.toFinset ∪ ht.toFinset := by
  ext
  simp
#align set.finite.to_finset_union Set.Finite.toFinset_union

protected theorem toFinset_diff [DecidableEq α] (hs : s.Finite) (ht : t.Finite)
    (h : (s \ t).Finite) : h.toFinset = hs.toFinset \ ht.toFinset := by
  ext
  simp
#align set.finite.to_finset_diff Set.Finite.toFinset_diff

open scoped symmDiff in
protected theorem toFinset_symmDiff [DecidableEq α] (hs : s.Finite) (ht : t.Finite)
    (h : (s ∆ t).Finite) : h.toFinset = hs.toFinset ∆ ht.toFinset := by
  ext
  simp [mem_symmDiff, Finset.mem_symmDiff]
#align set.finite.to_finset_symm_diff Set.Finite.toFinset_symmDiff

protected theorem toFinset_compl [DecidableEq α] [Fintype α] (hs : s.Finite) (h : sᶜ.Finite) :
    h.toFinset = hs.toFinsetᶜ := by
  ext
  simp
#align set.finite.to_finset_compl Set.Finite.toFinset_compl

protected theorem toFinset_univ [Fintype α] (h : (Set.univ : Set α).Finite) :
    h.toFinset = Finset.univ := by
  simp
#align set.finite.to_finset_univ Set.Finite.toFinset_univ

@[simp]
protected theorem toFinset_eq_empty {h : s.Finite} : h.toFinset = ∅ ↔ s = ∅ :=
  @toFinset_eq_empty _ _ h.fintype
#align set.finite.to_finset_eq_empty Set.Finite.toFinset_eq_empty

protected theorem toFinset_empty (h : (∅ : Set α).Finite) : h.toFinset = ∅ := by
  simp
#align set.finite.to_finset_empty Set.Finite.toFinset_empty

@[simp]
protected theorem toFinset_eq_univ [Fintype α] {h : s.Finite} :
    h.toFinset = Finset.univ ↔ s = univ :=
  @toFinset_eq_univ _ _ _ h.fintype
#align set.finite.to_finset_eq_univ Set.Finite.toFinset_eq_univ

protected theorem toFinset_image [DecidableEq β] (f : α → β) (hs : s.Finite) (h : (f '' s).Finite) :
    h.toFinset = hs.toFinset.image f := by
  ext
  simp
#align set.finite.to_finset_image Set.Finite.toFinset_image

-- Porting note (#10618): now `simp` can prove it but it needs the `fintypeRange` instance
-- from the next section
protected theorem toFinset_range [DecidableEq α] [Fintype β] (f : β → α) (h : (range f).Finite) :
    h.toFinset = Finset.univ.image f := by
  ext
  simp
#align set.finite.to_finset_range Set.Finite.toFinset_range

end Finite

/-! ### Fintype instances

Every instance here should have a corresponding `Set.Finite` constructor in the next section.
-/

section FintypeInstances

instance fintypeUniv [Fintype α] : Fintype (@univ α) :=
  Fintype.ofEquiv α (Equiv.Set.univ α).symm
#align set.fintype_univ Set.fintypeUniv

/-- If `(Set.univ : Set α)` is finite then `α` is a finite type. -/
noncomputable def fintypeOfFiniteUniv (H : (univ (α := α)).Finite) : Fintype α :=
  @Fintype.ofEquiv _ (univ : Set α) H.fintype (Equiv.Set.univ _)
#align set.fintype_of_finite_univ Set.fintypeOfFiniteUniv

instance fintypeUnion [DecidableEq α] (s t : Set α) [Fintype s] [Fintype t] :
    Fintype (s ∪ t : Set α) :=
  Fintype.ofFinset (s.toFinset ∪ t.toFinset) <| by simp
#align set.fintype_union Set.fintypeUnion

instance fintypeSep (s : Set α) (p : α → Prop) [Fintype s] [DecidablePred p] :
    Fintype ({ a ∈ s | p a } : Set α) :=
  Fintype.ofFinset (s.toFinset.filter p) <| by simp
#align set.fintype_sep Set.fintypeSep

instance fintypeInter (s t : Set α) [DecidableEq α] [Fintype s] [Fintype t] :
    Fintype (s ∩ t : Set α) :=
  Fintype.ofFinset (s.toFinset ∩ t.toFinset) <| by simp
#align set.fintype_inter Set.fintypeInter

/-- A `Fintype` instance for set intersection where the left set has a `Fintype` instance. -/
instance fintypeInterOfLeft (s t : Set α) [Fintype s] [DecidablePred (· ∈ t)] :
    Fintype (s ∩ t : Set α) :=
  Fintype.ofFinset (s.toFinset.filter (· ∈ t)) <| by simp
#align set.fintype_inter_of_left Set.fintypeInterOfLeft

/-- A `Fintype` instance for set intersection where the right set has a `Fintype` instance. -/
instance fintypeInterOfRight (s t : Set α) [Fintype t] [DecidablePred (· ∈ s)] :
    Fintype (s ∩ t : Set α) :=
  Fintype.ofFinset (t.toFinset.filter (· ∈ s)) <| by simp [and_comm]
#align set.fintype_inter_of_right Set.fintypeInterOfRight

/-- A `Fintype` structure on a set defines a `Fintype` structure on its subset. -/
def fintypeSubset (s : Set α) {t : Set α} [Fintype s] [DecidablePred (· ∈ t)] (h : t ⊆ s) :
    Fintype t := by
  rw [← inter_eq_self_of_subset_right h]
  apply Set.fintypeInterOfLeft
#align set.fintype_subset Set.fintypeSubset

instance fintypeDiff [DecidableEq α] (s t : Set α) [Fintype s] [Fintype t] :
    Fintype (s \ t : Set α) :=
  Fintype.ofFinset (s.toFinset \ t.toFinset) <| by simp
#align set.fintype_diff Set.fintypeDiff

instance fintypeDiffLeft (s t : Set α) [Fintype s] [DecidablePred (· ∈ t)] :
    Fintype (s \ t : Set α) :=
  Set.fintypeSep s (· ∈ tᶜ)
#align set.fintype_diff_left Set.fintypeDiffLeft

instance fintypeiUnion [DecidableEq α] [Fintype (PLift ι)] (f : ι → Set α) [∀ i, Fintype (f i)] :
    Fintype (⋃ i, f i) :=
  Fintype.ofFinset (Finset.univ.biUnion fun i : PLift ι => (f i.down).toFinset) <| by simp
#align set.fintype_Union Set.fintypeiUnion

instance fintypesUnion [DecidableEq α] {s : Set (Set α)} [Fintype s]
    [H : ∀ t : s, Fintype (t : Set α)] : Fintype (⋃₀ s) := by
  rw [sUnion_eq_iUnion]
  exact @Set.fintypeiUnion _ _ _ _ _ H
#align set.fintype_sUnion Set.fintypesUnion

/-- A union of sets with `Fintype` structure over a set with `Fintype` structure has a `Fintype`
structure. -/
def fintypeBiUnion [DecidableEq α] {ι : Type*} (s : Set ι) [Fintype s] (t : ι → Set α)
    (H : ∀ i ∈ s, Fintype (t i)) : Fintype (⋃ x ∈ s, t x) :=
  haveI : ∀ i : toFinset s, Fintype (t i) := fun i => H i (mem_toFinset.1 i.2)
  Fintype.ofFinset (s.toFinset.attach.biUnion fun x => (t x).toFinset) fun x => by simp
#align set.fintype_bUnion Set.fintypeBiUnion

instance fintypeBiUnion' [DecidableEq α] {ι : Type*} (s : Set ι) [Fintype s] (t : ι → Set α)
    [∀ i, Fintype (t i)] : Fintype (⋃ x ∈ s, t x) :=
  Fintype.ofFinset (s.toFinset.biUnion fun x => (t x).toFinset) <| by simp
#align set.fintype_bUnion' Set.fintypeBiUnion'

section monad
attribute [local instance] Set.monad

/-- If `s : Set α` is a set with `Fintype` instance and `f : α → Set β` is a function such that
each `f a`, `a ∈ s`, has a `Fintype` structure, then `s >>= f` has a `Fintype` structure. -/
def fintypeBind {α β} [DecidableEq β] (s : Set α) [Fintype s] (f : α → Set β)
    (H : ∀ a ∈ s, Fintype (f a)) : Fintype (s >>= f) :=
  Set.fintypeBiUnion s f H
#align set.fintype_bind Set.fintypeBind

instance fintypeBind' {α β} [DecidableEq β] (s : Set α) [Fintype s] (f : α → Set β)
    [∀ a, Fintype (f a)] : Fintype (s >>= f) :=
  Set.fintypeBiUnion' s f
#align set.fintype_bind' Set.fintypeBind'

end monad

instance fintypeEmpty : Fintype (∅ : Set α) :=
  Fintype.ofFinset ∅ <| by simp
#align set.fintype_empty Set.fintypeEmpty

instance fintypeSingleton (a : α) : Fintype ({a} : Set α) :=
  Fintype.ofFinset {a} <| by simp
#align set.fintype_singleton Set.fintypeSingleton

instance fintypePure : ∀ a : α, Fintype (pure a : Set α) :=
  Set.fintypeSingleton
#align set.fintype_pure Set.fintypePure

/-- A `Fintype` instance for inserting an element into a `Set` using the
corresponding `insert` function on `Finset`. This requires `DecidableEq α`.
There is also `Set.fintypeInsert'` when `a ∈ s` is decidable. -/
instance fintypeInsert (a : α) (s : Set α) [DecidableEq α] [Fintype s] :
    Fintype (insert a s : Set α) :=
  Fintype.ofFinset (insert a s.toFinset) <| by simp
#align set.fintype_insert Set.fintypeInsert

/-- A `Fintype` structure on `insert a s` when inserting a new element. -/
def fintypeInsertOfNotMem {a : α} (s : Set α) [Fintype s] (h : a ∉ s) :
    Fintype (insert a s : Set α) :=
  Fintype.ofFinset ⟨a ::ₘ s.toFinset.1, s.toFinset.nodup.cons (by simp [h])⟩ <| by simp
#align set.fintype_insert_of_not_mem Set.fintypeInsertOfNotMem

/-- A `Fintype` structure on `insert a s` when inserting a pre-existing element. -/
def fintypeInsertOfMem {a : α} (s : Set α) [Fintype s] (h : a ∈ s) : Fintype (insert a s : Set α) :=
  Fintype.ofFinset s.toFinset <| by simp [h]
#align set.fintype_insert_of_mem Set.fintypeInsertOfMem

/-- The `Set.fintypeInsert` instance requires decidable equality, but when `a ∈ s`
is decidable for this particular `a` we can still get a `Fintype` instance by using
`Set.fintypeInsertOfNotMem` or `Set.fintypeInsertOfMem`.

This instance pre-dates `Set.fintypeInsert`, and it is less efficient.
When `Set.decidableMemOfFintype` is made a local instance, then this instance would
override `Set.fintypeInsert` if not for the fact that its priority has been
adjusted. See Note [lower instance priority]. -/
instance (priority := 100) fintypeInsert' (a : α) (s : Set α) [Decidable <| a ∈ s] [Fintype s] :
    Fintype (insert a s : Set α) :=
  if h : a ∈ s then fintypeInsertOfMem s h else fintypeInsertOfNotMem s h
#align set.fintype_insert' Set.fintypeInsert'

instance fintypeImage [DecidableEq β] (s : Set α) (f : α → β) [Fintype s] : Fintype (f '' s) :=
  Fintype.ofFinset (s.toFinset.image f) <| by simp
#align set.fintype_image Set.fintypeImage

/-- If a function `f` has a partial inverse and sends a set `s` to a set with `[Fintype]` instance,
then `s` has a `Fintype` structure as well. -/
def fintypeOfFintypeImage (s : Set α) {f : α → β} {g} (I : IsPartialInv f g) [Fintype (f '' s)] :
    Fintype s :=
  Fintype.ofFinset ⟨_, (f '' s).toFinset.2.filterMap g <| injective_of_isPartialInv_right I⟩
    fun a => by
    suffices (∃ b x, f x = b ∧ g b = some a ∧ x ∈ s) ↔ a ∈ s by
      simpa [exists_and_left.symm, and_comm, and_left_comm, and_assoc]
    rw [exists_swap]
    suffices (∃ x, x ∈ s ∧ g (f x) = some a) ↔ a ∈ s by simpa [and_comm, and_left_comm, and_assoc]
    simp [I _, (injective_of_isPartialInv I).eq_iff]
#align set.fintype_of_fintype_image Set.fintypeOfFintypeImage

instance fintypeRange [DecidableEq α] (f : ι → α) [Fintype (PLift ι)] : Fintype (range f) :=
  Fintype.ofFinset (Finset.univ.image <| f ∘ PLift.down) <| by simp
#align set.fintype_range Set.fintypeRange

instance fintypeMap {α β} [DecidableEq β] :
    ∀ (s : Set α) (f : α → β) [Fintype s], Fintype (f <$> s) :=
  Set.fintypeImage
#align set.fintype_map Set.fintypeMap

instance fintypeLTNat (n : ℕ) : Fintype { i | i < n } :=
  Fintype.ofFinset (Finset.range n) <| by simp
#align set.fintype_lt_nat Set.fintypeLTNat

instance fintypeLENat (n : ℕ) : Fintype { i | i ≤ n } := by
  simpa [Nat.lt_succ_iff] using Set.fintypeLTNat (n + 1)
#align set.fintype_le_nat Set.fintypeLENat

/-- This is not an instance so that it does not conflict with the one
in `Mathlib/Order/LocallyFinite.lean`. -/
def Nat.fintypeIio (n : ℕ) : Fintype (Iio n) :=
  Set.fintypeLTNat n
#align set.nat.fintype_Iio Set.Nat.fintypeIio

instance fintypeProd (s : Set α) (t : Set β) [Fintype s] [Fintype t] :
    Fintype (s ×ˢ t : Set (α × β)) :=
  Fintype.ofFinset (s.toFinset ×ˢ t.toFinset) <| by simp
#align set.fintype_prod Set.fintypeProd

instance fintypeOffDiag [DecidableEq α] (s : Set α) [Fintype s] : Fintype s.offDiag :=
  Fintype.ofFinset s.toFinset.offDiag <| by simp
#align set.fintype_off_diag Set.fintypeOffDiag

/-- `image2 f s t` is `Fintype` if `s` and `t` are. -/
instance fintypeImage2 [DecidableEq γ] (f : α → β → γ) (s : Set α) (t : Set β) [hs : Fintype s]
    [ht : Fintype t] : Fintype (image2 f s t : Set γ) := by
  rw [← image_prod]
  apply Set.fintypeImage
#align set.fintype_image2 Set.fintypeImage2

instance fintypeSeq [DecidableEq β] (f : Set (α → β)) (s : Set α) [Fintype f] [Fintype s] :
    Fintype (f.seq s) := by
  rw [seq_def]
  apply Set.fintypeBiUnion'
#align set.fintype_seq Set.fintypeSeq

instance fintypeSeq' {α β : Type u} [DecidableEq β] (f : Set (α → β)) (s : Set α) [Fintype f]
    [Fintype s] : Fintype (f <*> s) :=
  Set.fintypeSeq f s
#align set.fintype_seq' Set.fintypeSeq'

instance fintypeMemFinset (s : Finset α) : Fintype { a | a ∈ s } :=
  Finset.fintypeCoeSort s
#align set.fintype_mem_finset Set.fintypeMemFinset

end FintypeInstances

end Set

theorem Equiv.set_finite_iff {s : Set α} {t : Set β} (hst : s ≃ t) : s.Finite ↔ t.Finite := by
  simp_rw [← Set.finite_coe_iff, hst.finite_iff]
#align equiv.set_finite_iff Equiv.set_finite_iff

/-! ### Finset -/

namespace Finset

/-- Gives a `Set.Finite` for the `Finset` coerced to a `Set`.
This is a wrapper around `Set.toFinite`. -/
@[simp]
theorem finite_toSet (s : Finset α) : (s : Set α).Finite :=
  Set.toFinite _
#align finset.finite_to_set Finset.finite_toSet

-- Porting note (#10618): was @[simp], now `simp` can prove it
theorem finite_toSet_toFinset (s : Finset α) : s.finite_toSet.toFinset = s := by
  rw [toFinite_toFinset, toFinset_coe]
#align finset.finite_to_set_to_finset Finset.finite_toSet_toFinset

end Finset

namespace Multiset

@[simp]
theorem finite_toSet (s : Multiset α) : { x | x ∈ s }.Finite := by
  classical simpa only [← Multiset.mem_toFinset] using s.toFinset.finite_toSet
#align multiset.finite_to_set Multiset.finite_toSet

@[simp]
theorem finite_toSet_toFinset [DecidableEq α] (s : Multiset α) :
    s.finite_toSet.toFinset = s.toFinset := by
  ext x
  simp
#align multiset.finite_to_set_to_finset Multiset.finite_toSet_toFinset

end Multiset

@[simp]
theorem List.finite_toSet (l : List α) : { x | x ∈ l }.Finite :=
  (show Multiset α from ⟦l⟧).finite_toSet
#align list.finite_to_set List.finite_toSet

/-! ### Finite instances

There is seemingly some overlap between the following instances and the `Fintype` instances
in `Data.Set.Finite`. While every `Fintype` instance gives a `Finite` instance, those
instances that depend on `Fintype` or `Decidable` instances need an additional `Finite` instance
to be able to generally apply.

Some set instances do not appear here since they are consequences of others, for example
`Subtype.Finite` for subsets of a finite type.
-/


namespace Finite.Set

open scoped Classical

example {s : Set α} [Finite α] : Finite s :=
  inferInstance

example : Finite (∅ : Set α) :=
  inferInstance

example (a : α) : Finite ({a} : Set α) :=
  inferInstance

instance finite_union (s t : Set α) [Finite s] [Finite t] : Finite (s ∪ t : Set α) := by
  cases nonempty_fintype s
  cases nonempty_fintype t
  infer_instance
#align finite.set.finite_union Finite.Set.finite_union

instance finite_sep (s : Set α) (p : α → Prop) [Finite s] : Finite ({ a ∈ s | p a } : Set α) := by
  cases nonempty_fintype s
  infer_instance
#align finite.set.finite_sep Finite.Set.finite_sep

protected theorem subset (s : Set α) {t : Set α} [Finite s] (h : t ⊆ s) : Finite t := by
  rw [← sep_eq_of_subset h]
  infer_instance
#align finite.set.subset Finite.Set.subset

instance finite_inter_of_right (s t : Set α) [Finite t] : Finite (s ∩ t : Set α) :=
  Finite.Set.subset t (inter_subset_right s t)
#align finite.set.finite_inter_of_right Finite.Set.finite_inter_of_right

instance finite_inter_of_left (s t : Set α) [Finite s] : Finite (s ∩ t : Set α) :=
  Finite.Set.subset s (inter_subset_left s t)
#align finite.set.finite_inter_of_left Finite.Set.finite_inter_of_left

instance finite_diff (s t : Set α) [Finite s] : Finite (s \ t : Set α) :=
  Finite.Set.subset s (diff_subset s t)
#align finite.set.finite_diff Finite.Set.finite_diff

instance finite_range (f : ι → α) [Finite ι] : Finite (range f) := by
  haveI := Fintype.ofFinite (PLift ι)
  infer_instance
#align finite.set.finite_range Finite.Set.finite_range

instance finite_iUnion [Finite ι] (f : ι → Set α) [∀ i, Finite (f i)] : Finite (⋃ i, f i) := by
  rw [iUnion_eq_range_psigma]
  apply Set.finite_range
#align finite.set.finite_Union Finite.Set.finite_iUnion

instance finite_sUnion {s : Set (Set α)} [Finite s] [H : ∀ t : s, Finite (t : Set α)] :
    Finite (⋃₀ s) := by
  rw [sUnion_eq_iUnion]
  exact @Finite.Set.finite_iUnion _ _ _ _ H
#align finite.set.finite_sUnion Finite.Set.finite_sUnion

theorem finite_biUnion {ι : Type*} (s : Set ι) [Finite s] (t : ι → Set α)
    (H : ∀ i ∈ s, Finite (t i)) : Finite (⋃ x ∈ s, t x) := by
  rw [biUnion_eq_iUnion]
  haveI : ∀ i : s, Finite (t i) := fun i => H i i.property
  infer_instance
#align finite.set.finite_bUnion Finite.Set.finite_biUnion

instance finite_biUnion' {ι : Type*} (s : Set ι) [Finite s] (t : ι → Set α) [∀ i, Finite (t i)] :
    Finite (⋃ x ∈ s, t x) :=
  finite_biUnion s t fun _ _ => inferInstance
#align finite.set.finite_bUnion' Finite.Set.finite_biUnion'

/-- Example: `Finite (⋃ (i < n), f i)` where `f : ℕ → Set α` and `[∀ i, Finite (f i)]`
(when given instances from `Order.Interval.Finset.Nat`).
-/
instance finite_biUnion'' {ι : Type*} (p : ι → Prop) [h : Finite { x | p x }] (t : ι → Set α)
    [∀ i, Finite (t i)] : Finite (⋃ (x) (_ : p x), t x) :=
  @Finite.Set.finite_biUnion' _ _ (setOf p) h t _
#align finite.set.finite_bUnion'' Finite.Set.finite_biUnion''

instance finite_iInter {ι : Sort*} [Nonempty ι] (t : ι → Set α) [∀ i, Finite (t i)] :
    Finite (⋂ i, t i) :=
  Finite.Set.subset (t <| Classical.arbitrary ι) (iInter_subset _ _)
#align finite.set.finite_Inter Finite.Set.finite_iInter

instance finite_insert (a : α) (s : Set α) [Finite s] : Finite (insert a s : Set α) :=
  Finite.Set.finite_union {a} s
#align finite.set.finite_insert Finite.Set.finite_insert

instance finite_image (s : Set α) (f : α → β) [Finite s] : Finite (f '' s) := by
  cases nonempty_fintype s
  infer_instance
#align finite.set.finite_image Finite.Set.finite_image

instance finite_replacement [Finite α] (f : α → β) :
    Finite {f x | x : α} :=
  Finite.Set.finite_range f
#align finite.set.finite_replacement Finite.Set.finite_replacement

instance finite_prod (s : Set α) (t : Set β) [Finite s] [Finite t] :
    Finite (s ×ˢ t : Set (α × β)) :=
  Finite.of_equiv _ (Equiv.Set.prod s t).symm
#align finite.set.finite_prod Finite.Set.finite_prod

instance finite_image2 (f : α → β → γ) (s : Set α) (t : Set β) [Finite s] [Finite t] :
    Finite (image2 f s t : Set γ) := by
  rw [← image_prod]
  infer_instance
#align finite.set.finite_image2 Finite.Set.finite_image2

instance finite_seq (f : Set (α → β)) (s : Set α) [Finite f] [Finite s] : Finite (f.seq s) := by
  rw [seq_def]
  infer_instance
#align finite.set.finite_seq Finite.Set.finite_seq

end Finite.Set

namespace Set

/-! ### Constructors for `Set.Finite`

Every constructor here should have a corresponding `Fintype` instance in the previous section
(or in the `Fintype` module).

The implementation of these constructors ideally should be no more than `Set.toFinite`,
after possibly setting up some `Fintype` and classical `Decidable` instances.
-/


section SetFiniteConstructors

@[nontriviality]
theorem Finite.of_subsingleton [Subsingleton α] (s : Set α) : s.Finite :=
  s.toFinite
#align set.finite.of_subsingleton Set.Finite.of_subsingleton

theorem finite_univ [Finite α] : (@univ α).Finite :=
  Set.toFinite _
#align set.finite_univ Set.finite_univ

theorem finite_univ_iff : (@univ α).Finite ↔ Finite α := (Equiv.Set.univ α).finite_iff
#align set.finite_univ_iff Set.finite_univ_iff

alias ⟨_root_.Finite.of_finite_univ, _⟩ := finite_univ_iff
#align finite.of_finite_univ Finite.of_finite_univ

theorem Finite.subset {s : Set α} (hs : s.Finite) {t : Set α} (ht : t ⊆ s) : t.Finite := by
  have := hs.to_subtype
  exact Finite.Set.subset _ ht
#align set.finite.subset Set.Finite.subset

theorem Finite.union {s t : Set α} (hs : s.Finite) (ht : t.Finite) : (s ∪ t).Finite := by
  rw [Set.Finite] at hs ht
  apply toFinite
#align set.finite.union Set.Finite.union

theorem Finite.finite_of_compl {s : Set α} (hs : s.Finite) (hsc : sᶜ.Finite) : Finite α := by
  rw [← finite_univ_iff, ← union_compl_self s]
  exact hs.union hsc
#align set.finite.finite_of_compl Set.Finite.finite_of_compl

theorem Finite.sup {s t : Set α} : s.Finite → t.Finite → (s ⊔ t).Finite :=
  Finite.union
#align set.finite.sup Set.Finite.sup

theorem Finite.sep {s : Set α} (hs : s.Finite) (p : α → Prop) : { a ∈ s | p a }.Finite :=
  hs.subset <| sep_subset _ _
#align set.finite.sep Set.Finite.sep

theorem Finite.inter_of_left {s : Set α} (hs : s.Finite) (t : Set α) : (s ∩ t).Finite :=
  hs.subset <| inter_subset_left _ _
#align set.finite.inter_of_left Set.Finite.inter_of_left

theorem Finite.inter_of_right {s : Set α} (hs : s.Finite) (t : Set α) : (t ∩ s).Finite :=
  hs.subset <| inter_subset_right _ _
#align set.finite.inter_of_right Set.Finite.inter_of_right

theorem Finite.inf_of_left {s : Set α} (h : s.Finite) (t : Set α) : (s ⊓ t).Finite :=
  h.inter_of_left t
#align set.finite.inf_of_left Set.Finite.inf_of_left

theorem Finite.inf_of_right {s : Set α} (h : s.Finite) (t : Set α) : (t ⊓ s).Finite :=
  h.inter_of_right t
#align set.finite.inf_of_right Set.Finite.inf_of_right

protected lemma Infinite.mono {s t : Set α} (h : s ⊆ t) : s.Infinite → t.Infinite :=
  mt fun ht ↦ ht.subset h
#align set.infinite.mono Set.Infinite.mono

theorem Finite.diff {s : Set α} (hs : s.Finite) (t : Set α) : (s \ t).Finite :=
  hs.subset <| diff_subset _ _
#align set.finite.diff Set.Finite.diff

theorem Finite.of_diff {s t : Set α} (hd : (s \ t).Finite) (ht : t.Finite) : s.Finite :=
  (hd.union ht).subset <| subset_diff_union _ _
#align set.finite.of_diff Set.Finite.of_diff

theorem finite_iUnion [Finite ι] {f : ι → Set α} (H : ∀ i, (f i).Finite) : (⋃ i, f i).Finite :=
  haveI := fun i => (H i).to_subtype
  toFinite _
#align set.finite_Union Set.finite_iUnion

/-- Dependent version of `Finite.biUnion`. -/
theorem Finite.biUnion' {ι} {s : Set ι} (hs : s.Finite) {t : ∀ i ∈ s, Set α}
    (ht : ∀ i (hi : i ∈ s), (t i hi).Finite) : (⋃ i ∈ s, t i ‹_›).Finite := by
  have := hs.to_subtype
  rw [biUnion_eq_iUnion]
  apply finite_iUnion fun i : s => ht i.1 i.2
#align set.finite.bUnion' Set.Finite.biUnion'

theorem Finite.biUnion {ι} {s : Set ι} (hs : s.Finite) {t : ι → Set α}
    (ht : ∀ i ∈ s, (t i).Finite) : (⋃ i ∈ s, t i).Finite :=
  hs.biUnion' ht
#align set.finite.bUnion Set.Finite.biUnion

theorem Finite.sUnion {s : Set (Set α)} (hs : s.Finite) (H : ∀ t ∈ s, Set.Finite t) :
    (⋃₀ s).Finite := by
  simpa only [sUnion_eq_biUnion] using hs.biUnion H
#align set.finite.sUnion Set.Finite.sUnion

theorem Finite.sInter {α : Type*} {s : Set (Set α)} {t : Set α} (ht : t ∈ s) (hf : t.Finite) :
    (⋂₀ s).Finite :=
  hf.subset (sInter_subset_of_mem ht)
#align set.finite.sInter Set.Finite.sInter

/-- If sets `s i` are finite for all `i` from a finite set `t` and are empty for `i ∉ t`, then the
union `⋃ i, s i` is a finite set. -/
theorem Finite.iUnion {ι : Type*} {s : ι → Set α} {t : Set ι} (ht : t.Finite)
    (hs : ∀ i ∈ t, (s i).Finite) (he : ∀ i, i ∉ t → s i = ∅) : (⋃ i, s i).Finite := by
  suffices ⋃ i, s i ⊆ ⋃ i ∈ t, s i by exact (ht.biUnion hs).subset this
  refine iUnion_subset fun i x hx => ?_
  by_cases hi : i ∈ t
  · exact mem_biUnion hi hx
  · rw [he i hi, mem_empty_iff_false] at hx
    contradiction
#align set.finite.Union Set.Finite.iUnion

section monad
attribute [local instance] Set.monad

theorem Finite.bind {α β} {s : Set α} {f : α → Set β} (h : s.Finite) (hf : ∀ a ∈ s, (f a).Finite) :
    (s >>= f).Finite :=
  h.biUnion hf
#align set.finite.bind Set.Finite.bind

end monad

@[simp]
theorem finite_empty : (∅ : Set α).Finite :=
  toFinite _
#align set.finite_empty Set.finite_empty

protected theorem Infinite.nonempty {s : Set α} (h : s.Infinite) : s.Nonempty :=
  nonempty_iff_ne_empty.2 <| by
    rintro rfl
    exact h finite_empty
#align set.infinite.nonempty Set.Infinite.nonempty

@[simp]
theorem finite_singleton (a : α) : ({a} : Set α).Finite :=
  toFinite _
#align set.finite_singleton Set.finite_singleton

theorem finite_pure (a : α) : (pure a : Set α).Finite :=
  toFinite _
#align set.finite_pure Set.finite_pure

@[simp]
protected theorem Finite.insert (a : α) {s : Set α} (hs : s.Finite) : (insert a s).Finite :=
  (finite_singleton a).union hs
#align set.finite.insert Set.Finite.insert

theorem Finite.image {s : Set α} (f : α → β) (hs : s.Finite) : (f '' s).Finite := by
  have := hs.to_subtype
  apply toFinite
#align set.finite.image Set.Finite.image

theorem finite_range (f : ι → α) [Finite ι] : (range f).Finite :=
  toFinite _
#align set.finite_range Set.finite_range

lemma Finite.of_surjOn {s : Set α} {t : Set β} (f : α → β) (hf : SurjOn f s t) (hs : s.Finite) :
    t.Finite := (hs.image _).subset hf

theorem Finite.dependent_image {s : Set α} (hs : s.Finite) (F : ∀ i ∈ s, β) :
    {y : β | ∃ x hx, F x hx = y}.Finite := by
  have := hs.to_subtype
  simpa [range] using finite_range fun x : s => F x x.2
#align set.finite.dependent_image Set.Finite.dependent_image

theorem Finite.map {α β} {s : Set α} : ∀ f : α → β, s.Finite → (f <$> s).Finite :=
  Finite.image
#align set.finite.map Set.Finite.map

theorem Finite.of_finite_image {s : Set α} {f : α → β} (h : (f '' s).Finite) (hi : Set.InjOn f s) :
    s.Finite :=
  have := h.to_subtype
  .of_injective _ hi.bijOn_image.bijective.injective
#align set.finite.of_finite_image Set.Finite.of_finite_image

section preimage
variable {f : α → β} {s : Set β}

theorem finite_of_finite_preimage (h : (f ⁻¹' s).Finite) (hs : s ⊆ range f) : s.Finite := by
  rw [← image_preimage_eq_of_subset hs]
  exact Finite.image f h
#align set.finite_of_finite_preimage Set.finite_of_finite_preimage

theorem Finite.of_preimage (h : (f ⁻¹' s).Finite) (hf : Surjective f) : s.Finite :=
  hf.image_preimage s ▸ h.image _
#align set.finite.of_preimage Set.Finite.of_preimage

theorem Finite.preimage (I : Set.InjOn f (f ⁻¹' s)) (h : s.Finite) : (f ⁻¹' s).Finite :=
  (h.subset (image_preimage_subset f s)).of_finite_image I
#align set.finite.preimage Set.Finite.preimage

protected lemma Infinite.preimage (hs : s.Infinite) (hf : s ⊆ range f) : (f ⁻¹' s).Infinite :=
  fun h ↦ hs <| finite_of_finite_preimage h hf

lemma Infinite.preimage' (hs : (s ∩ range f).Infinite) : (f ⁻¹' s).Infinite :=
  (hs.preimage <| inter_subset_right _ _).mono <| preimage_mono <| inter_subset_left _ _

theorem Finite.preimage_embedding {s : Set β} (f : α ↪ β) (h : s.Finite) : (f ⁻¹' s).Finite :=
  h.preimage fun _ _ _ _ h' => f.injective h'
#align set.finite.preimage_embedding Set.Finite.preimage_embedding

end preimage

theorem finite_lt_nat (n : ℕ) : Set.Finite { i | i < n } :=
  toFinite _
#align set.finite_lt_nat Set.finite_lt_nat

theorem finite_le_nat (n : ℕ) : Set.Finite { i | i ≤ n } :=
  toFinite _
#align set.finite_le_nat Set.finite_le_nat

section MapsTo

variable {s : Set α} {f : α → α} (hs : s.Finite) (hm : MapsTo f s s)

theorem Finite.surjOn_iff_bijOn_of_mapsTo : SurjOn f s s ↔ BijOn f s s := by
  refine ⟨fun h ↦ ⟨hm, ?_, h⟩, BijOn.surjOn⟩
  have : Finite s := finite_coe_iff.mpr hs
  exact hm.restrict_inj.mp (Finite.injective_iff_surjective.mpr <| hm.restrict_surjective_iff.mpr h)

theorem Finite.injOn_iff_bijOn_of_mapsTo : InjOn f s ↔ BijOn f s s := by
  refine ⟨fun h ↦ ⟨hm, h, ?_⟩, BijOn.injOn⟩
  have : Finite s := finite_coe_iff.mpr hs
  exact hm.restrict_surjective_iff.mp (Finite.injective_iff_surjective.mp <| hm.restrict_inj.mpr h)

end MapsTo

section Prod

variable {s : Set α} {t : Set β}

protected theorem Finite.prod (hs : s.Finite) (ht : t.Finite) : (s ×ˢ t : Set (α × β)).Finite := by
  have := hs.to_subtype
  have := ht.to_subtype
  apply toFinite
#align set.finite.prod Set.Finite.prod

theorem Finite.of_prod_left (h : (s ×ˢ t : Set (α × β)).Finite) : t.Nonempty → s.Finite :=
  fun ⟨b, hb⟩ => (h.image Prod.fst).subset fun a ha => ⟨(a, b), ⟨ha, hb⟩, rfl⟩
#align set.finite.of_prod_left Set.Finite.of_prod_left

theorem Finite.of_prod_right (h : (s ×ˢ t : Set (α × β)).Finite) : s.Nonempty → t.Finite :=
  fun ⟨a, ha⟩ => (h.image Prod.snd).subset fun b hb => ⟨(a, b), ⟨ha, hb⟩, rfl⟩
#align set.finite.of_prod_right Set.Finite.of_prod_right

protected theorem Infinite.prod_left (hs : s.Infinite) (ht : t.Nonempty) : (s ×ˢ t).Infinite :=
  fun h => hs <| h.of_prod_left ht
#align set.infinite.prod_left Set.Infinite.prod_left

protected theorem Infinite.prod_right (ht : t.Infinite) (hs : s.Nonempty) : (s ×ˢ t).Infinite :=
  fun h => ht <| h.of_prod_right hs
#align set.infinite.prod_right Set.Infinite.prod_right

protected theorem infinite_prod :
    (s ×ˢ t).Infinite ↔ s.Infinite ∧ t.Nonempty ∨ t.Infinite ∧ s.Nonempty := by
  refine ⟨fun h => ?_, ?_⟩
  · simp_rw [Set.Infinite, @and_comm ¬_, ← Classical.not_imp]
    by_contra!
    exact h ((this.1 h.nonempty.snd).prod <| this.2 h.nonempty.fst)
  · rintro (h | h)
    · exact h.1.prod_left h.2
    · exact h.1.prod_right h.2
#align set.infinite_prod Set.infinite_prod

theorem finite_prod : (s ×ˢ t).Finite ↔ (s.Finite ∨ t = ∅) ∧ (t.Finite ∨ s = ∅) := by
  simp only [← not_infinite, Set.infinite_prod, not_or, not_and_or, not_nonempty_iff_eq_empty]
#align set.finite_prod Set.finite_prod

protected theorem Finite.offDiag {s : Set α} (hs : s.Finite) : s.offDiag.Finite :=
  (hs.prod hs).subset s.offDiag_subset_prod
#align set.finite.off_diag Set.Finite.offDiag

protected theorem Finite.image2 (f : α → β → γ) (hs : s.Finite) (ht : t.Finite) :
    (image2 f s t).Finite := by
  have := hs.to_subtype
  have := ht.to_subtype
  apply toFinite
#align set.finite.image2 Set.Finite.image2

end Prod

theorem Finite.seq {f : Set (α → β)} {s : Set α} (hf : f.Finite) (hs : s.Finite) :
    (f.seq s).Finite :=
  hf.image2 _ hs
#align set.finite.seq Set.Finite.seq

theorem Finite.seq' {α β : Type u} {f : Set (α → β)} {s : Set α} (hf : f.Finite) (hs : s.Finite) :
    (f <*> s).Finite :=
  hf.seq hs
#align set.finite.seq' Set.Finite.seq'

theorem finite_mem_finset (s : Finset α) : { a | a ∈ s }.Finite :=
  toFinite _
#align set.finite_mem_finset Set.finite_mem_finset

theorem Subsingleton.finite {s : Set α} (h : s.Subsingleton) : s.Finite :=
  h.induction_on finite_empty finite_singleton
#align set.subsingleton.finite Set.Subsingleton.finite

theorem Infinite.nontrivial {s : Set α} (hs : s.Infinite) : s.Nontrivial :=
  not_subsingleton_iff.1 <| mt Subsingleton.finite hs

theorem finite_preimage_inl_and_inr {s : Set (Sum α β)} :
    (Sum.inl ⁻¹' s).Finite ∧ (Sum.inr ⁻¹' s).Finite ↔ s.Finite :=
  ⟨fun h => image_preimage_inl_union_image_preimage_inr s ▸ (h.1.image _).union (h.2.image _),
    fun h => ⟨h.preimage (Sum.inl_injective.injOn _), h.preimage (Sum.inr_injective.injOn _)⟩⟩
#align set.finite_preimage_inl_and_inr Set.finite_preimage_inl_and_inr

theorem exists_finite_iff_finset {p : Set α → Prop} :
    (∃ s : Set α, s.Finite ∧ p s) ↔ ∃ s : Finset α, p ↑s :=
  ⟨fun ⟨_, hs, hps⟩ => ⟨hs.toFinset, hs.coe_toFinset.symm ▸ hps⟩, fun ⟨s, hs⟩ =>
    ⟨s, s.finite_toSet, hs⟩⟩
#align set.exists_finite_iff_finset Set.exists_finite_iff_finset

/-- There are finitely many subsets of a given finite set -/
theorem Finite.finite_subsets {α : Type u} {a : Set α} (h : a.Finite) : { b | b ⊆ a }.Finite := by
  convert ((Finset.powerset h.toFinset).map Finset.coeEmb.1).finite_toSet
  ext s
  simpa [← @exists_finite_iff_finset α fun t => t ⊆ a ∧ t = s, Finite.subset_toFinset,
    ← and_assoc, Finset.coeEmb] using h.subset
#align set.finite.finite_subsets Set.Finite.finite_subsets

section Pi
variable {ι : Type*} [Finite ι] {κ : ι → Type*} {t : ∀ i, Set (κ i)}

/-- Finite product of finite sets is finite -/
theorem Finite.pi (ht : ∀ i, (t i).Finite) : (pi univ t).Finite := by
  cases nonempty_fintype ι
  lift t to ∀ d, Finset (κ d) using ht
  classical
    rw [← Fintype.coe_piFinset]
    apply Finset.finite_toSet
#align set.finite.pi Set.Finite.pi

/-- Finite product of finite sets is finite. Note this is a variant of `Set.Finite.pi` without the
extra `i ∈ univ` binder. -/
lemma Finite.pi' (ht : ∀ i, (t i).Finite) : {f : ∀ i, κ i | ∀ i, f i ∈ t i}.Finite := by
  simpa [Set.pi] using Finite.pi ht

end Pi

/-- A finite union of finsets is finite. -/
theorem union_finset_finite_of_range_finite (f : α → Finset β) (h : (range f).Finite) :
    (⋃ a, (f a : Set β)).Finite := by
  rw [← biUnion_range]
  exact h.biUnion fun y _ => y.finite_toSet
#align set.union_finset_finite_of_range_finite Set.union_finset_finite_of_range_finite

theorem finite_range_ite {p : α → Prop} [DecidablePred p] {f g : α → β} (hf : (range f).Finite)
    (hg : (range g).Finite) : (range fun x => if p x then f x else g x).Finite :=
  (hf.union hg).subset range_ite_subset
#align set.finite_range_ite Set.finite_range_ite

theorem finite_range_const {c : β} : (range fun _ : α => c).Finite :=
  (finite_singleton c).subset range_const_subset
#align set.finite_range_const Set.finite_range_const

end SetFiniteConstructors

/-! ### Properties -/

instance Finite.inhabited : Inhabited { s : Set α // s.Finite } :=
  ⟨⟨∅, finite_empty⟩⟩
#align set.finite.inhabited Set.Finite.inhabited

@[simp]
theorem finite_union {s t : Set α} : (s ∪ t).Finite ↔ s.Finite ∧ t.Finite :=
  ⟨fun h => ⟨h.subset (subset_union_left _ _), h.subset (subset_union_right _ _)⟩, fun ⟨hs, ht⟩ =>
    hs.union ht⟩
#align set.finite_union Set.finite_union

theorem finite_image_iff {s : Set α} {f : α → β} (hi : InjOn f s) : (f '' s).Finite ↔ s.Finite :=
  ⟨fun h => h.of_finite_image hi, Finite.image _⟩
#align set.finite_image_iff Set.finite_image_iff

theorem univ_finite_iff_nonempty_fintype : (univ : Set α).Finite ↔ Nonempty (Fintype α) :=
  ⟨fun h => ⟨fintypeOfFiniteUniv h⟩, fun ⟨_i⟩ => finite_univ⟩
#align set.univ_finite_iff_nonempty_fintype Set.univ_finite_iff_nonempty_fintype

-- Porting note: moved `@[simp]` to `Set.toFinset_singleton` because `simp` can now simplify LHS
theorem Finite.toFinset_singleton {a : α} (ha : ({a} : Set α).Finite := finite_singleton _) :
    ha.toFinset = {a} :=
  Set.toFinite_toFinset _
#align set.finite.to_finset_singleton Set.Finite.toFinset_singleton

@[simp]
theorem Finite.toFinset_insert [DecidableEq α] {s : Set α} {a : α} (hs : (insert a s).Finite) :
    hs.toFinset = insert a (hs.subset <| subset_insert _ _).toFinset :=
  Finset.ext <| by simp
#align set.finite.to_finset_insert Set.Finite.toFinset_insert

theorem Finite.toFinset_insert' [DecidableEq α] {a : α} {s : Set α} (hs : s.Finite) :
    (hs.insert a).toFinset = insert a hs.toFinset :=
  Finite.toFinset_insert _
#align set.finite.to_finset_insert' Set.Finite.toFinset_insert'

theorem Finite.toFinset_prod {s : Set α} {t : Set β} (hs : s.Finite) (ht : t.Finite) :
    hs.toFinset ×ˢ ht.toFinset = (hs.prod ht).toFinset :=
  Finset.ext <| by simp
#align set.finite.to_finset_prod Set.Finite.toFinset_prod

theorem Finite.toFinset_offDiag {s : Set α} [DecidableEq α] (hs : s.Finite) :
    hs.offDiag.toFinset = hs.toFinset.offDiag :=
  Finset.ext <| by simp
#align set.finite.to_finset_off_diag Set.Finite.toFinset_offDiag

theorem Finite.fin_embedding {s : Set α} (h : s.Finite) :
    ∃ (n : ℕ) (f : Fin n ↪ α), range f = s :=
  ⟨_, (Fintype.equivFin (h.toFinset : Set α)).symm.asEmbedding, by
    simp only [Finset.coe_sort_coe, Equiv.asEmbedding_range, Finite.coe_toFinset, setOf_mem_eq]⟩
#align set.finite.fin_embedding Set.Finite.fin_embedding

theorem Finite.fin_param {s : Set α} (h : s.Finite) :
    ∃ (n : ℕ) (f : Fin n → α), Injective f ∧ range f = s :=
  let ⟨n, f, hf⟩ := h.fin_embedding
  ⟨n, f, f.injective, hf⟩
#align set.finite.fin_param Set.Finite.fin_param

theorem finite_option {s : Set (Option α)} : s.Finite ↔ { x : α | some x ∈ s }.Finite :=
  ⟨fun h => h.preimage_embedding Embedding.some, fun h =>
    ((h.image some).insert none).subset fun x =>
      x.casesOn (fun _ => Or.inl rfl) fun _ hx => Or.inr <| mem_image_of_mem _ hx⟩
#align set.finite_option Set.finite_option

theorem finite_image_fst_and_snd_iff {s : Set (α × β)} :
    (Prod.fst '' s).Finite ∧ (Prod.snd '' s).Finite ↔ s.Finite :=
  ⟨fun h => (h.1.prod h.2).subset fun _ h => ⟨mem_image_of_mem _ h, mem_image_of_mem _ h⟩,
    fun h => ⟨h.image _, h.image _⟩⟩
#align set.finite_image_fst_and_snd_iff Set.finite_image_fst_and_snd_iff

theorem forall_finite_image_eval_iff {δ : Type*} [Finite δ] {κ : δ → Type*} {s : Set (∀ d, κ d)} :
    (∀ d, (eval d '' s).Finite) ↔ s.Finite :=
  ⟨fun h => (Finite.pi h).subset <| subset_pi_eval_image _ _, fun h _ => h.image _⟩
#align set.forall_finite_image_eval_iff Set.forall_finite_image_eval_iff

theorem finite_subset_iUnion {s : Set α} (hs : s.Finite) {ι} {t : ι → Set α} (h : s ⊆ ⋃ i, t i) :
    ∃ I : Set ι, I.Finite ∧ s ⊆ ⋃ i ∈ I, t i := by
  have := hs.to_subtype
  choose f hf using show ∀ x : s, ∃ i, x.1 ∈ t i by simpa [subset_def] using h
  refine ⟨range f, finite_range f, fun x hx => ?_⟩
  rw [biUnion_range, mem_iUnion]
  exact ⟨⟨x, hx⟩, hf _⟩
#align set.finite_subset_Union Set.finite_subset_iUnion

theorem eq_finite_iUnion_of_finite_subset_iUnion {ι} {s : ι → Set α} {t : Set α} (tfin : t.Finite)
    (h : t ⊆ ⋃ i, s i) :
    ∃ I : Set ι,
      I.Finite ∧
        ∃ σ : { i | i ∈ I } → Set α, (∀ i, (σ i).Finite) ∧ (∀ i, σ i ⊆ s i) ∧ t = ⋃ i, σ i :=
  let ⟨I, Ifin, hI⟩ := finite_subset_iUnion tfin h
  ⟨I, Ifin, fun x => s x ∩ t, fun i => tfin.subset (inter_subset_right _ _), fun i =>
    inter_subset_left _ _, by
    ext x
    rw [mem_iUnion]
    constructor
    · intro x_in
      rcases mem_iUnion.mp (hI x_in) with ⟨i, _, ⟨hi, rfl⟩, H⟩
      exact ⟨⟨i, hi⟩, ⟨H, x_in⟩⟩
    · rintro ⟨i, -, H⟩
      exact H⟩
#align set.eq_finite_Union_of_finite_subset_Union Set.eq_finite_iUnion_of_finite_subset_iUnion

@[elab_as_elim]
theorem Finite.induction_on {C : Set α → Prop} {s : Set α} (h : s.Finite) (H0 : C ∅)
    (H1 : ∀ {a s}, a ∉ s → Set.Finite s → C s → C (insert a s)) : C s := by
  lift s to Finset α using h
  induction' s using Finset.cons_induction_on with a s ha hs
  · rwa [Finset.coe_empty]
  · rw [Finset.coe_cons]
    exact @H1 a s ha (Set.toFinite _) hs
#align set.finite.induction_on Set.Finite.induction_on

/-- Analogous to `Finset.induction_on'`. -/
@[elab_as_elim]
theorem Finite.induction_on' {C : Set α → Prop} {S : Set α} (h : S.Finite) (H0 : C ∅)
    (H1 : ∀ {a s}, a ∈ S → s ⊆ S → a ∉ s → C s → C (insert a s)) : C S := by
  refine @Set.Finite.induction_on α (fun s => s ⊆ S → C s) S h (fun _ => H0) ?_ Subset.rfl
  intro a s has _ hCs haS
  rw [insert_subset_iff] at haS
  exact H1 haS.1 haS.2 has (hCs haS.2)
#align set.finite.induction_on' Set.Finite.induction_on'

@[elab_as_elim]
theorem Finite.dinduction_on {C : ∀ s : Set α, s.Finite → Prop} (s : Set α) (h : s.Finite)
    (H0 : C ∅ finite_empty)
    (H1 : ∀ {a s}, a ∉ s → ∀ h : Set.Finite s, C s h → C (insert a s) (h.insert a)) : C s h :=
  have : ∀ h : s.Finite, C s h :=
    Finite.induction_on h (fun _ => H0) fun has hs ih _ => H1 has hs (ih _)
  this h
#align set.finite.dinduction_on Set.Finite.dinduction_on

/-- Induction up to a finite set `S`. -/
theorem Finite.induction_to {C : Set α → Prop} {S : Set α} (h : S.Finite)
    (S0 : Set α) (hS0 : S0 ⊆ S) (H0 : C S0) (H1 : ∀ s ⊂ S, C s → ∃ a ∈ S \ s, C (insert a s)) :
    C S := by
  have : Finite S := Finite.to_subtype h
  have : Finite {T : Set α // T ⊆ S} := Finite.of_equiv (Set S) (Equiv.Set.powerset S).symm
  rw [← Subtype.coe_mk (p := (· ⊆ S)) _ le_rfl]
  rw [← Subtype.coe_mk (p := (· ⊆ S)) _ hS0] at H0
  refine Finite.to_wellFoundedGT.wf.induction_bot' (fun s hs hs' ↦ ?_) H0
  obtain ⟨a, ⟨ha1, ha2⟩, ha'⟩ := H1 s (ssubset_of_ne_of_subset hs s.2) hs'
  exact ⟨⟨insert a s.1, insert_subset ha1 s.2⟩, Set.ssubset_insert ha2, ha'⟩

/-- Induction up to `univ`. -/
theorem Finite.induction_to_univ [Finite α] {C : Set α → Prop} (S0 : Set α)
    (H0 : C S0) (H1 : ∀ S ≠ univ, C S → ∃ a ∉ S, C (insert a S)) : C univ :=
  finite_univ.induction_to S0 (subset_univ S0) H0 (by simpa [ssubset_univ_iff])

section

attribute [local instance] Nat.fintypeIio

/-- If `P` is some relation between terms of `γ` and sets in `γ`, such that every finite set
`t : Set γ` has some `c : γ` related to it, then there is a recursively defined sequence `u` in `γ`
so `u n` is related to the image of `{0, 1, ..., n-1}` under `u`.

(We use this later to show sequentially compact sets are totally bounded.)
-/
theorem seq_of_forall_finite_exists {γ : Type*} {P : γ → Set γ → Prop}
    (h : ∀ t : Set γ, t.Finite → ∃ c, P c t) : ∃ u : ℕ → γ, ∀ n, P (u n) (u '' Iio n) := by
  haveI : Nonempty γ := (h ∅ finite_empty).nonempty
  choose! c hc using h
  set f : (n : ℕ) → (g : (m : ℕ) → m < n → γ) → γ := fun n g => c (range fun k : Iio n => g k.1 k.2)
  set u : ℕ → γ := fun n => Nat.strongRecOn' n f
  refine ⟨u, fun n => ?_⟩
  convert hc (u '' Iio n) ((finite_lt_nat _).image _)
  rw [image_eq_range]
  exact Nat.strongRecOn'_beta
#align set.seq_of_forall_finite_exists Set.seq_of_forall_finite_exists

end

/-! ### Cardinality -/

theorem empty_card : Fintype.card (∅ : Set α) = 0 :=
  rfl
#align set.empty_card Set.empty_card

theorem empty_card' {h : Fintype.{u} (∅ : Set α)} : @Fintype.card (∅ : Set α) h = 0 := by
  simp
#align set.empty_card' Set.empty_card'

theorem card_fintypeInsertOfNotMem {a : α} (s : Set α) [Fintype s] (h : a ∉ s) :
    @Fintype.card _ (fintypeInsertOfNotMem s h) = Fintype.card s + 1 := by
  simp [fintypeInsertOfNotMem, Fintype.card_ofFinset]
#align set.card_fintype_insert_of_not_mem Set.card_fintypeInsertOfNotMem

@[simp]
theorem card_insert {a : α} (s : Set α) [Fintype s] (h : a ∉ s)
    {d : Fintype.{u} (insert a s : Set α)} : @Fintype.card _ d = Fintype.card s + 1 := by
  rw [← card_fintypeInsertOfNotMem s h]; congr; exact Subsingleton.elim _ _
#align set.card_insert Set.card_insert

theorem card_image_of_inj_on {s : Set α} [Fintype s] {f : α → β} [Fintype (f '' s)]
    (H : ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y) : Fintype.card (f '' s) = Fintype.card s :=
  haveI := Classical.propDecidable
  calc
    Fintype.card (f '' s) = (s.toFinset.image f).card := Fintype.card_of_finset' _ (by simp)
    _ = s.toFinset.card :=
      Finset.card_image_of_injOn fun x hx y hy hxy =>
        H x (mem_toFinset.1 hx) y (mem_toFinset.1 hy) hxy
    _ = Fintype.card s := (Fintype.card_of_finset' _ fun a => mem_toFinset).symm
#align set.card_image_of_inj_on Set.card_image_of_inj_on

theorem card_image_of_injective (s : Set α) [Fintype s] {f : α → β} [Fintype (f '' s)]
    (H : Function.Injective f) : Fintype.card (f '' s) = Fintype.card s :=
  card_image_of_inj_on fun _ _ _ _ h => H h
#align set.card_image_of_injective Set.card_image_of_injective

@[simp]
theorem card_singleton (a : α) : Fintype.card ({a} : Set α) = 1 :=
  Fintype.card_ofSubsingleton _
#align set.card_singleton Set.card_singleton

theorem card_lt_card {s t : Set α} [Fintype s] [Fintype t] (h : s ⊂ t) :
    Fintype.card s < Fintype.card t :=
  Fintype.card_lt_of_injective_not_surjective (Set.inclusion h.1) (Set.inclusion_injective h.1)
    fun hst => (ssubset_iff_subset_ne.1 h).2 (eq_of_inclusion_surjective hst)
#align set.card_lt_card Set.card_lt_card

theorem card_le_card {s t : Set α} [Fintype s] [Fintype t] (hsub : s ⊆ t) :
    Fintype.card s ≤ Fintype.card t :=
  Fintype.card_le_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)
#align set.card_le_card Set.card_le_card

theorem eq_of_subset_of_card_le {s t : Set α} [Fintype s] [Fintype t] (hsub : s ⊆ t)
    (hcard : Fintype.card t ≤ Fintype.card s) : s = t :=
  (eq_or_ssubset_of_subset hsub).elim id fun h => absurd hcard <| not_le_of_lt <| card_lt_card h
#align set.eq_of_subset_of_card_le Set.eq_of_subset_of_card_le

theorem card_range_of_injective [Fintype α] {f : α → β} (hf : Injective f) [Fintype (range f)] :
    Fintype.card (range f) = Fintype.card α :=
  Eq.symm <| Fintype.card_congr <| Equiv.ofInjective f hf
#align set.card_range_of_injective Set.card_range_of_injective

theorem Finite.card_toFinset {s : Set α} [Fintype s] (h : s.Finite) :
    h.toFinset.card = Fintype.card s :=
  Eq.symm <| Fintype.card_of_finset' _ fun _ ↦ h.mem_toFinset
#align set.finite.card_to_finset Set.Finite.card_toFinset

theorem card_ne_eq [Fintype α] (a : α) [Fintype { x : α | x ≠ a }] :
    Fintype.card { x : α | x ≠ a } = Fintype.card α - 1 := by
  haveI := Classical.decEq α
  rw [← toFinset_card, toFinset_setOf, Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
#align set.card_ne_eq Set.card_ne_eq

/-! ### Infinite sets -/

variable {s t : Set α}

theorem infinite_univ_iff : (@univ α).Infinite ↔ Infinite α := by
  rw [Set.Infinite, finite_univ_iff, not_finite_iff_infinite]
#align set.infinite_univ_iff Set.infinite_univ_iff

theorem infinite_univ [h : Infinite α] : (@univ α).Infinite :=
  infinite_univ_iff.2 h
#align set.infinite_univ Set.infinite_univ

theorem infinite_coe_iff {s : Set α} : Infinite s ↔ s.Infinite :=
  not_finite_iff_infinite.symm.trans finite_coe_iff.not
#align set.infinite_coe_iff Set.infinite_coe_iff

-- Porting note: something weird happened here
alias ⟨_, Infinite.to_subtype⟩ := infinite_coe_iff
#align set.infinite.to_subtype Set.Infinite.to_subtype

lemma Infinite.exists_not_mem_finite (hs : s.Infinite) (ht : t.Finite) : ∃ a, a ∈ s ∧ a ∉ t := by
  by_contra! h; exact hs <| ht.subset h

lemma Infinite.exists_not_mem_finset (hs : s.Infinite) (t : Finset α) : ∃ a ∈ s, a ∉ t :=
  hs.exists_not_mem_finite t.finite_toSet
#align set.infinite.exists_not_mem_finset Set.Infinite.exists_not_mem_finset

section Infinite
variable [Infinite α]

lemma Finite.exists_not_mem (hs : s.Finite) : ∃ a, a ∉ s := by
  by_contra! h; exact infinite_univ (hs.subset fun a _ ↦ h _)

lemma _root_.Finset.exists_not_mem (s : Finset α) : ∃ a, a ∉ s := s.finite_toSet.exists_not_mem

end Infinite

/-- Embedding of `ℕ` into an infinite set. -/
noncomputable def Infinite.natEmbedding (s : Set α) (h : s.Infinite) : ℕ ↪ s :=
  h.to_subtype.natEmbedding
#align set.infinite.nat_embedding Set.Infinite.natEmbedding

theorem Infinite.exists_subset_card_eq {s : Set α} (hs : s.Infinite) (n : ℕ) :
    ∃ t : Finset α, ↑t ⊆ s ∧ t.card = n :=
  ⟨((Finset.range n).map (hs.natEmbedding _)).map (Embedding.subtype _), by simp⟩
#align set.infinite.exists_subset_card_eq Set.Infinite.exists_subset_card_eq

theorem infinite_of_finite_compl [Infinite α] {s : Set α} (hs : sᶜ.Finite) : s.Infinite := fun h =>
  Set.infinite_univ (by simpa using hs.union h)
#align set.infinite_of_finite_compl Set.infinite_of_finite_compl

theorem Finite.infinite_compl [Infinite α] {s : Set α} (hs : s.Finite) : sᶜ.Infinite := fun h =>
  Set.infinite_univ (by simpa using hs.union h)
#align set.finite.infinite_compl Set.Finite.infinite_compl

theorem Infinite.diff {s t : Set α} (hs : s.Infinite) (ht : t.Finite) : (s \ t).Infinite := fun h =>
  hs <| h.of_diff ht
#align set.infinite.diff Set.Infinite.diff

@[simp]
theorem infinite_union {s t : Set α} : (s ∪ t).Infinite ↔ s.Infinite ∨ t.Infinite := by
  simp only [Set.Infinite, finite_union, not_and_or]
#align set.infinite_union Set.infinite_union

theorem Infinite.of_image (f : α → β) {s : Set α} (hs : (f '' s).Infinite) : s.Infinite :=
  mt (Finite.image f) hs
#align set.infinite.of_image Set.Infinite.of_image

theorem infinite_image_iff {s : Set α} {f : α → β} (hi : InjOn f s) :
    (f '' s).Infinite ↔ s.Infinite :=
  not_congr <| finite_image_iff hi
#align set.infinite_image_iff Set.infinite_image_iff

theorem infinite_range_iff {f : α → β} (hi : Injective f) :
    (range f).Infinite ↔ Infinite α := by
  rw [← image_univ, infinite_image_iff (hi.injOn _), infinite_univ_iff]

alias ⟨_, Infinite.image⟩ := infinite_image_iff
#align set.infinite.image Set.Infinite.image

-- Porting note: attribute [protected] doesn't work
-- attribute [protected] infinite.image

section Image2

variable {f : α → β → γ} {s : Set α} {t : Set β} {a : α} {b : β}

protected theorem Infinite.image2_left (hs : s.Infinite) (hb : b ∈ t)
    (hf : InjOn (fun a => f a b) s) : (image2 f s t).Infinite :=
  (hs.image hf).mono <| image_subset_image2_left hb
#align set.infinite.image2_left Set.Infinite.image2_left

protected theorem Infinite.image2_right (ht : t.Infinite) (ha : a ∈ s) (hf : InjOn (f a) t) :
    (image2 f s t).Infinite :=
  (ht.image hf).mono <| image_subset_image2_right ha
#align set.infinite.image2_right Set.Infinite.image2_right

theorem infinite_image2 (hfs : ∀ b ∈ t, InjOn (fun a => f a b) s) (hft : ∀ a ∈ s, InjOn (f a) t) :
    (image2 f s t).Infinite ↔ s.Infinite ∧ t.Nonempty ∨ t.Infinite ∧ s.Nonempty := by
  refine ⟨fun h => Set.infinite_prod.1 ?_, ?_⟩
  · rw [← image_uncurry_prod] at h
    exact h.of_image _
  · rintro (⟨hs, b, hb⟩ | ⟨ht, a, ha⟩)
    · exact hs.image2_left hb (hfs _ hb)
    · exact ht.image2_right ha (hft _ ha)
#align set.infinite_image2 Set.infinite_image2

lemma finite_image2 (hfs : ∀ b ∈ t, InjOn (f · b) s) (hft : ∀ a ∈ s, InjOn (f a) t) :
    (image2 f s t).Finite ↔ s.Finite ∧ t.Finite ∨ s = ∅ ∨ t = ∅ := by
  rw [← not_infinite, infinite_image2 hfs hft]
  simp [not_or, -not_and, not_and_or, not_nonempty_iff_eq_empty]
  aesop

end Image2

theorem infinite_of_injOn_mapsTo {s : Set α} {t : Set β} {f : α → β} (hi : InjOn f s)
    (hm : MapsTo f s t) (hs : s.Infinite) : t.Infinite :=
  ((infinite_image_iff hi).2 hs).mono (mapsTo'.mp hm)
#align set.infinite_of_inj_on_maps_to Set.infinite_of_injOn_mapsTo

theorem Infinite.exists_ne_map_eq_of_mapsTo {s : Set α} {t : Set β} {f : α → β} (hs : s.Infinite)
    (hf : MapsTo f s t) (ht : t.Finite) : ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y := by
  contrapose! ht
  exact infinite_of_injOn_mapsTo (fun x hx y hy => not_imp_not.1 (ht x hx y hy)) hf hs
#align set.infinite.exists_ne_map_eq_of_maps_to Set.Infinite.exists_ne_map_eq_of_mapsTo

theorem infinite_range_of_injective [Infinite α] {f : α → β} (hi : Injective f) :
    (range f).Infinite := by
  rw [← image_univ, infinite_image_iff (injOn_of_injective hi _)]
  exact infinite_univ
#align set.infinite_range_of_injective Set.infinite_range_of_injective

theorem infinite_of_injective_forall_mem [Infinite α] {s : Set β} {f : α → β} (hi : Injective f)
    (hf : ∀ x : α, f x ∈ s) : s.Infinite := by
  rw [← range_subset_iff] at hf
  exact (infinite_range_of_injective hi).mono hf
#align set.infinite_of_injective_forall_mem Set.infinite_of_injective_forall_mem

theorem not_injOn_infinite_finite_image {f : α → β} {s : Set α} (h_inf : s.Infinite)
    (h_fin : (f '' s).Finite) : ¬InjOn f s := by
  have : Finite (f '' s) := finite_coe_iff.mpr h_fin
  have : Infinite s := infinite_coe_iff.mpr h_inf
  have h := not_injective_infinite_finite
            ((f '' s).codRestrict (s.restrict f) fun x => ⟨x, x.property, rfl⟩)
  contrapose! h
  rwa [injective_codRestrict, ← injOn_iff_injective]
#align set.not_inj_on_infinite_finite_image Set.not_injOn_infinite_finite_image

/-! ### Order properties -/

section Preorder

variable [Preorder α] [Nonempty α] {s : Set α}

theorem infinite_of_forall_exists_gt (h : ∀ a, ∃ b ∈ s, a < b) : s.Infinite := by
  inhabit α
  set f : ℕ → α := fun n => Nat.recOn n (h default).choose fun _ a => (h a).choose
  have hf : ∀ n, f n ∈ s := by rintro (_ | _) <;> exact (h _).choose_spec.1
  exact infinite_of_injective_forall_mem
    (strictMono_nat_of_lt_succ fun n => (h _).choose_spec.2).injective hf
#align set.infinite_of_forall_exists_gt Set.infinite_of_forall_exists_gt

theorem infinite_of_forall_exists_lt (h : ∀ a, ∃ b ∈ s, b < a) : s.Infinite :=
  @infinite_of_forall_exists_gt αᵒᵈ _ _ _ h
#align set.infinite_of_forall_exists_lt Set.infinite_of_forall_exists_lt

end Preorder

theorem finite_isTop (α : Type*) [PartialOrder α] : { x : α | IsTop x }.Finite :=
  (subsingleton_isTop α).finite
#align set.finite_is_top Set.finite_isTop

theorem finite_isBot (α : Type*) [PartialOrder α] : { x : α | IsBot x }.Finite :=
  (subsingleton_isBot α).finite
#align set.finite_is_bot Set.finite_isBot

theorem Infinite.exists_lt_map_eq_of_mapsTo [LinearOrder α] {s : Set α} {t : Set β} {f : α → β}
    (hs : s.Infinite) (hf : MapsTo f s t) (ht : t.Finite) : ∃ x ∈ s, ∃ y ∈ s, x < y ∧ f x = f y :=
  let ⟨x, hx, y, hy, hxy, hf⟩ := hs.exists_ne_map_eq_of_mapsTo hf ht
  hxy.lt_or_lt.elim (fun hxy => ⟨x, hx, y, hy, hxy, hf⟩) fun hyx => ⟨y, hy, x, hx, hyx, hf.symm⟩
#align set.infinite.exists_lt_map_eq_of_maps_to Set.Infinite.exists_lt_map_eq_of_mapsTo

theorem Finite.exists_lt_map_eq_of_forall_mem [LinearOrder α] [Infinite α] {t : Set β} {f : α → β}
    (hf : ∀ a, f a ∈ t) (ht : t.Finite) : ∃ a b, a < b ∧ f a = f b := by
  rw [← mapsTo_univ_iff] at hf
  obtain ⟨a, -, b, -, h⟩ := infinite_univ.exists_lt_map_eq_of_mapsTo hf ht
  exact ⟨a, b, h⟩
#align set.finite.exists_lt_map_eq_of_forall_mem Set.Finite.exists_lt_map_eq_of_forall_mem

theorem exists_min_image [LinearOrder β] (s : Set α) (f : α → β) (h1 : s.Finite) :
    s.Nonempty → ∃ a ∈ s, ∀ b ∈ s, f a ≤ f b
  | ⟨x, hx⟩ => by
    simpa only [exists_prop, Finite.mem_toFinset] using
      h1.toFinset.exists_min_image f ⟨x, h1.mem_toFinset.2 hx⟩
#align set.exists_min_image Set.exists_min_image

theorem exists_max_image [LinearOrder β] (s : Set α) (f : α → β) (h1 : s.Finite) :
    s.Nonempty → ∃ a ∈ s, ∀ b ∈ s, f b ≤ f a
  | ⟨x, hx⟩ => by
    simpa only [exists_prop, Finite.mem_toFinset] using
      h1.toFinset.exists_max_image f ⟨x, h1.mem_toFinset.2 hx⟩
#align set.exists_max_image Set.exists_max_image

theorem exists_lower_bound_image [Nonempty α] [LinearOrder β] (s : Set α) (f : α → β)
    (h : s.Finite) : ∃ a : α, ∀ b ∈ s, f a ≤ f b := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ‹Nonempty α›.elim fun a => ⟨a, fun _ => False.elim⟩
  · rcases Set.exists_min_image s f h hs with ⟨x₀, _, hx₀⟩
    exact ⟨x₀, fun x hx => hx₀ x hx⟩
#align set.exists_lower_bound_image Set.exists_lower_bound_image

theorem exists_upper_bound_image [Nonempty α] [LinearOrder β] (s : Set α) (f : α → β)
    (h : s.Finite) : ∃ a : α, ∀ b ∈ s, f b ≤ f a :=
  exists_lower_bound_image (β := βᵒᵈ) s f h
#align set.exists_upper_bound_image Set.exists_upper_bound_image

theorem Finite.iSup_biInf_of_monotone {ι ι' α : Type*} [Preorder ι'] [Nonempty ι']
    [IsDirected ι' (· ≤ ·)] [Order.Frame α] {s : Set ι} (hs : s.Finite) {f : ι → ι' → α}
    (hf : ∀ i ∈ s, Monotone (f i)) : ⨆ j, ⨅ i ∈ s, f i j = ⨅ i ∈ s, ⨆ j, f i j := by
  induction' s, hs using Set.Finite.dinduction_on with a s _ _ ihs hf
  · simp [iSup_const]
  · rw [forall_mem_insert] at hf
    simp only [iInf_insert, ← ihs hf.2]
    exact iSup_inf_of_monotone hf.1 fun j₁ j₂ hj => iInf₂_mono fun i hi => hf.2 i hi hj
#align set.finite.supr_binfi_of_monotone Set.Finite.iSup_biInf_of_monotone

theorem Finite.iSup_biInf_of_antitone {ι ι' α : Type*} [Preorder ι'] [Nonempty ι']
    [IsDirected ι' (swap (· ≤ ·))] [Order.Frame α] {s : Set ι} (hs : s.Finite) {f : ι → ι' → α}
    (hf : ∀ i ∈ s, Antitone (f i)) : ⨆ j, ⨅ i ∈ s, f i j = ⨅ i ∈ s, ⨆ j, f i j :=
  @Finite.iSup_biInf_of_monotone ι ι'ᵒᵈ α _ _ _ _ _ hs _ fun i hi => (hf i hi).dual_left
#align set.finite.supr_binfi_of_antitone Set.Finite.iSup_biInf_of_antitone

theorem Finite.iInf_biSup_of_monotone {ι ι' α : Type*} [Preorder ι'] [Nonempty ι']
    [IsDirected ι' (swap (· ≤ ·))] [Order.Coframe α] {s : Set ι} (hs : s.Finite) {f : ι → ι' → α}
    (hf : ∀ i ∈ s, Monotone (f i)) : ⨅ j, ⨆ i ∈ s, f i j = ⨆ i ∈ s, ⨅ j, f i j :=
  hs.iSup_biInf_of_antitone (α := αᵒᵈ) fun i hi => (hf i hi).dual_right
#align set.finite.infi_bsupr_of_monotone Set.Finite.iInf_biSup_of_monotone

theorem Finite.iInf_biSup_of_antitone {ι ι' α : Type*} [Preorder ι'] [Nonempty ι']
    [IsDirected ι' (· ≤ ·)] [Order.Coframe α] {s : Set ι} (hs : s.Finite) {f : ι → ι' → α}
    (hf : ∀ i ∈ s, Antitone (f i)) : ⨅ j, ⨆ i ∈ s, f i j = ⨆ i ∈ s, ⨅ j, f i j :=
  hs.iSup_biInf_of_monotone (α := αᵒᵈ) fun i hi => (hf i hi).dual_right
#align set.finite.infi_bsupr_of_antitone Set.Finite.iInf_biSup_of_antitone

theorem iSup_iInf_of_monotone {ι ι' α : Type*} [Finite ι] [Preorder ι'] [Nonempty ι']
    [IsDirected ι' (· ≤ ·)] [Order.Frame α] {f : ι → ι' → α} (hf : ∀ i, Monotone (f i)) :
    ⨆ j, ⨅ i, f i j = ⨅ i, ⨆ j, f i j := by
  simpa only [iInf_univ] using finite_univ.iSup_biInf_of_monotone fun i _ => hf i
#align supr_infi_of_monotone Set.iSup_iInf_of_monotone

theorem iSup_iInf_of_antitone {ι ι' α : Type*} [Finite ι] [Preorder ι'] [Nonempty ι']
    [IsDirected ι' (swap (· ≤ ·))] [Order.Frame α] {f : ι → ι' → α} (hf : ∀ i, Antitone (f i)) :
    ⨆ j, ⨅ i, f i j = ⨅ i, ⨆ j, f i j :=
  @iSup_iInf_of_monotone ι ι'ᵒᵈ α _ _ _ _ _ _ fun i => (hf i).dual_left
#align supr_infi_of_antitone Set.iSup_iInf_of_antitone

theorem iInf_iSup_of_monotone {ι ι' α : Type*} [Finite ι] [Preorder ι'] [Nonempty ι']
    [IsDirected ι' (swap (· ≤ ·))] [Order.Coframe α] {f : ι → ι' → α} (hf : ∀ i, Monotone (f i)) :
    ⨅ j, ⨆ i, f i j = ⨆ i, ⨅ j, f i j :=
  iSup_iInf_of_antitone (α := αᵒᵈ) fun i => (hf i).dual_right
#align infi_supr_of_monotone Set.iInf_iSup_of_monotone

theorem iInf_iSup_of_antitone {ι ι' α : Type*} [Finite ι] [Preorder ι'] [Nonempty ι']
    [IsDirected ι' (· ≤ ·)] [Order.Coframe α] {f : ι → ι' → α} (hf : ∀ i, Antitone (f i)) :
    ⨅ j, ⨆ i, f i j = ⨆ i, ⨅ j, f i j :=
  iSup_iInf_of_monotone (α := αᵒᵈ) fun i => (hf i).dual_right
#align infi_supr_of_antitone Set.iInf_iSup_of_antitone

/-- An increasing union distributes over finite intersection. -/
theorem iUnion_iInter_of_monotone {ι ι' α : Type*} [Finite ι] [Preorder ι'] [IsDirected ι' (· ≤ ·)]
    [Nonempty ι'] {s : ι → ι' → Set α} (hs : ∀ i, Monotone (s i)) :
    ⋃ j : ι', ⋂ i : ι, s i j = ⋂ i : ι, ⋃ j : ι', s i j :=
  iSup_iInf_of_monotone hs
#align set.Union_Inter_of_monotone Set.iUnion_iInter_of_monotone

/-- A decreasing union distributes over finite intersection. -/
theorem iUnion_iInter_of_antitone {ι ι' α : Type*} [Finite ι] [Preorder ι']
    [IsDirected ι' (swap (· ≤ ·))] [Nonempty ι'] {s : ι → ι' → Set α} (hs : ∀ i, Antitone (s i)) :
    ⋃ j : ι', ⋂ i : ι, s i j = ⋂ i : ι, ⋃ j : ι', s i j :=
  iSup_iInf_of_antitone hs
#align set.Union_Inter_of_antitone Set.iUnion_iInter_of_antitone

/-- An increasing intersection distributes over finite union. -/
theorem iInter_iUnion_of_monotone {ι ι' α : Type*} [Finite ι] [Preorder ι']
    [IsDirected ι' (swap (· ≤ ·))] [Nonempty ι'] {s : ι → ι' → Set α} (hs : ∀ i, Monotone (s i)) :
    ⋂ j : ι', ⋃ i : ι, s i j = ⋃ i : ι, ⋂ j : ι', s i j :=
  iInf_iSup_of_monotone hs
#align set.Inter_Union_of_monotone Set.iInter_iUnion_of_monotone

/-- A decreasing intersection distributes over finite union. -/
theorem iInter_iUnion_of_antitone {ι ι' α : Type*} [Finite ι] [Preorder ι'] [IsDirected ι' (· ≤ ·)]
    [Nonempty ι'] {s : ι → ι' → Set α} (hs : ∀ i, Antitone (s i)) :
    ⋂ j : ι', ⋃ i : ι, s i j = ⋃ i : ι, ⋂ j : ι', s i j :=
  iInf_iSup_of_antitone hs
#align set.Inter_Union_of_antitone Set.iInter_iUnion_of_antitone

theorem iUnion_pi_of_monotone {ι ι' : Type*} [LinearOrder ι'] [Nonempty ι'] {α : ι → Type*}
    {I : Set ι} {s : ∀ i, ι' → Set (α i)} (hI : I.Finite) (hs : ∀ i ∈ I, Monotone (s i)) :
    ⋃ j : ι', I.pi (fun i => s i j) = I.pi fun i => ⋃ j, s i j := by
  simp only [pi_def, biInter_eq_iInter, preimage_iUnion]
  haveI := hI.fintype.finite
  refine iUnion_iInter_of_monotone (ι' := ι') (fun (i : I) j₁ j₂ h => ?_)
  exact preimage_mono <| hs i i.2 h
#align set.Union_pi_of_monotone Set.iUnion_pi_of_monotone

theorem iUnion_univ_pi_of_monotone {ι ι' : Type*} [LinearOrder ι'] [Nonempty ι'] [Finite ι]
    {α : ι → Type*} {s : ∀ i, ι' → Set (α i)} (hs : ∀ i, Monotone (s i)) :
    ⋃ j : ι', pi univ (fun i => s i j) = pi univ fun i => ⋃ j, s i j :=
  iUnion_pi_of_monotone finite_univ fun i _ => hs i
#align set.Union_univ_pi_of_monotone Set.iUnion_univ_pi_of_monotone

theorem finite_range_findGreatest {P : α → ℕ → Prop} [∀ x, DecidablePred (P x)] {b : ℕ} :
    (range fun x => Nat.findGreatest (P x) b).Finite :=
  (finite_le_nat b).subset <| range_subset_iff.2 fun _ => Nat.findGreatest_le _
#align set.finite_range_find_greatest Set.finite_range_findGreatest

theorem Finite.exists_maximal_wrt [PartialOrder β] (f : α → β) (s : Set α) (h : s.Finite)
    (hs : s.Nonempty) : ∃ a ∈ s, ∀ a' ∈ s, f a ≤ f a' → f a = f a' := by
  induction s, h using Set.Finite.dinduction_on with
  | H0 => exact absurd hs not_nonempty_empty
  | @H1 a s his _ ih =>
    rcases s.eq_empty_or_nonempty with h | h
    · use a
      simp [h]
    rcases ih h with ⟨b, hb, ih⟩
    by_cases h : f b ≤ f a
    · refine ⟨a, Set.mem_insert _ _, fun c hc hac => le_antisymm hac ?_⟩
      rcases Set.mem_insert_iff.1 hc with (rfl | hcs)
      · rfl
      · rwa [← ih c hcs (le_trans h hac)]
    · refine ⟨b, Set.mem_insert_of_mem _ hb, fun c hc hbc => ?_⟩
      rcases Set.mem_insert_iff.1 hc with (rfl | hcs)
      · exact (h hbc).elim
      · exact ih c hcs hbc
#align set.finite.exists_maximal_wrt Set.Finite.exists_maximal_wrt

/-- A version of `Finite.exists_maximal_wrt` with the (weaker) hypothesis that the image of `s`
  is finite rather than `s` itself. -/
theorem Finite.exists_maximal_wrt' [PartialOrder β] (f : α → β) (s : Set α) (h : (f '' s).Finite)
    (hs : s.Nonempty) : (∃ a ∈ s, ∀ (a' : α), a' ∈ s → f a ≤ f a' → f a = f a') := by
  obtain ⟨_, ⟨a, ha, rfl⟩, hmax⟩ := Finite.exists_maximal_wrt id (f '' s) h (hs.image f)
  exact ⟨a, ha, fun a' ha' hf ↦ hmax _ (mem_image_of_mem f ha') hf⟩

theorem Finite.exists_minimal_wrt [PartialOrder β] (f : α → β) (s : Set α) (h : s.Finite)
    (hs : s.Nonempty) : ∃ a ∈ s, ∀ a' ∈ s, f a' ≤ f a → f a = f a' :=
  Finite.exists_maximal_wrt (β := βᵒᵈ) f s h hs

/-- A version of `Finite.exists_minimal_wrt` with the (weaker) hypothesis that the image of `s`
  is finite rather than `s` itself. -/
lemma Finite.exists_minimal_wrt' [PartialOrder β] (f : α → β) (s : Set α) (h : (f '' s).Finite)
    (hs : s.Nonempty) : (∃ a ∈ s, ∀ (a' : α), a' ∈ s → f a' ≤ f a → f a = f a') :=
  Set.Finite.exists_maximal_wrt' (β := βᵒᵈ) f s h hs

section

variable [Preorder α] [IsDirected α (· ≤ ·)] [Nonempty α] {s : Set α}

/-- A finite set is bounded above. -/
protected theorem Finite.bddAbove (hs : s.Finite) : BddAbove s :=
  Finite.induction_on hs bddAbove_empty fun _ _ h => h.insert _
#align set.finite.bdd_above Set.Finite.bddAbove

/-- A finite union of sets which are all bounded above is still bounded above. -/
theorem Finite.bddAbove_biUnion {I : Set β} {S : β → Set α} (H : I.Finite) :
    BddAbove (⋃ i ∈ I, S i) ↔ ∀ i ∈ I, BddAbove (S i) :=
  Finite.induction_on H (by simp only [biUnion_empty, bddAbove_empty, forall_mem_empty])
    fun _ _ hs => by simp only [biUnion_insert, forall_mem_insert, bddAbove_union, hs]
#align set.finite.bdd_above_bUnion Set.Finite.bddAbove_biUnion

theorem infinite_of_not_bddAbove : ¬BddAbove s → s.Infinite :=
  mt Finite.bddAbove
#align set.infinite_of_not_bdd_above Set.infinite_of_not_bddAbove

end

section

variable [Preorder α] [IsDirected α (· ≥ ·)] [Nonempty α] {s : Set α}

/-- A finite set is bounded below. -/
protected theorem Finite.bddBelow (hs : s.Finite) : BddBelow s :=
  @Finite.bddAbove αᵒᵈ _ _ _ _ hs
#align set.finite.bdd_below Set.Finite.bddBelow

/-- A finite union of sets which are all bounded below is still bounded below. -/
theorem Finite.bddBelow_biUnion {I : Set β} {S : β → Set α} (H : I.Finite) :
    BddBelow (⋃ i ∈ I, S i) ↔ ∀ i ∈ I, BddBelow (S i) :=
  @Finite.bddAbove_biUnion αᵒᵈ _ _ _ _ _ _ H
#align set.finite.bdd_below_bUnion Set.Finite.bddBelow_biUnion

theorem infinite_of_not_bddBelow : ¬BddBelow s → s.Infinite := mt Finite.bddBelow
#align set.infinite_of_not_bdd_below Set.infinite_of_not_bddBelow

end

end Set

namespace Finset

lemma exists_card_eq [Infinite α] : ∀ n : ℕ, ∃ s : Finset α, s.card = n
  | 0 => ⟨∅, card_empty⟩
  | n + 1 => by
    classical
    obtain ⟨s, rfl⟩ := exists_card_eq n
    obtain ⟨a, ha⟩ := s.exists_not_mem
    exact ⟨insert a s, card_insert_of_not_mem ha⟩

/-- A finset is bounded above. -/
protected theorem bddAbove [SemilatticeSup α] [Nonempty α] (s : Finset α) : BddAbove (↑s : Set α) :=
  s.finite_toSet.bddAbove
#align finset.bdd_above Finset.bddAbove

/-- A finset is bounded below. -/
protected theorem bddBelow [SemilatticeInf α] [Nonempty α] (s : Finset α) : BddBelow (↑s : Set α) :=
  s.finite_toSet.bddBelow
#align finset.bdd_below Finset.bddBelow

end Finset

variable [LinearOrder α] {s : Set α}

/-- If a linear order does not contain any triple of elements `x < y < z`, then this type
is finite. -/
lemma Finite.of_forall_not_lt_lt (h : ∀ ⦃x y z : α⦄, x < y → y < z → False) : Finite α := by
  nontriviality α
  rcases exists_pair_ne α with ⟨x, y, hne⟩
  refine @Finite.of_fintype α ⟨{x, y}, fun z => ?_⟩
  simpa [hne] using eq_or_eq_or_eq_of_forall_not_lt_lt h z x y
#align finite.of_forall_not_lt_lt Finite.of_forall_not_lt_lt

/-- If a set `s` does not contain any triple of elements `x < y < z`, then `s` is finite. -/
lemma Set.finite_of_forall_not_lt_lt (h : ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, x < y → y < z → False) :
    Set.Finite s :=
  @Set.toFinite _ s <| Finite.of_forall_not_lt_lt <| by simpa only [SetCoe.forall'] using h
#align set.finite_of_forall_not_lt_lt Set.finite_of_forall_not_lt_lt

lemma Set.finite_diff_iUnion_Ioo (s : Set α) : (s \ ⋃ (x ∈ s) (y ∈ s), Ioo x y).Finite :=
  Set.finite_of_forall_not_lt_lt fun _x hx _y hy _z hz hxy hyz => hy.2 <| mem_iUnion₂_of_mem hx.1 <|
    mem_iUnion₂_of_mem hz.1 ⟨hxy, hyz⟩
#align set.finite_diff_Union_Ioo Set.finite_diff_iUnion_Ioo

lemma Set.finite_diff_iUnion_Ioo' (s : Set α) : (s \ ⋃ x : s × s, Ioo x.1 x.2).Finite := by
  simpa only [iUnion, iSup_prod, iSup_subtype] using s.finite_diff_iUnion_Ioo
#align set.finite_diff_Union_Ioo' Set.finite_diff_iUnion_Ioo'

lemma Directed.exists_mem_subset_of_finset_subset_biUnion {α ι : Type*} [Nonempty ι]
    {f : ι → Set α} (h : Directed (· ⊆ ·) f) {s : Finset α} (hs : (s : Set α) ⊆ ⋃ i, f i) :
    ∃ i, (s : Set α) ⊆ f i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons b t hbt iht =>
    simp only [Finset.coe_cons, Set.insert_subset_iff, Set.mem_iUnion] at hs ⊢
    rcases hs.imp_right iht with ⟨⟨i, hi⟩, j, hj⟩
    rcases h i j with ⟨k, hik, hjk⟩
    exact ⟨k, hik hi, hj.trans hjk⟩
#align directed.exists_mem_subset_of_finset_subset_bUnion Directed.exists_mem_subset_of_finset_subset_biUnion

theorem DirectedOn.exists_mem_subset_of_finset_subset_biUnion {α ι : Type*} {f : ι → Set α}
    {c : Set ι} (hn : c.Nonempty) (hc : DirectedOn (fun i j => f i ⊆ f j) c) {s : Finset α}
    (hs : (s : Set α) ⊆ ⋃ i ∈ c, f i) : ∃ i ∈ c, (s : Set α) ⊆ f i := by
  rw [Set.biUnion_eq_iUnion] at hs
  haveI := hn.coe_sort
  simpa using (directed_comp.2 hc.directed_val).exists_mem_subset_of_finset_subset_biUnion hs
#align directed_on.exists_mem_subset_of_finset_subset_bUnion DirectedOn.exists_mem_subset_of_finset_subset_biUnion
