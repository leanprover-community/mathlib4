/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kyle Miller
-/
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Nontriviality

/-!
# Finite sets

This file provides `Fintype` instances for many set constructions. It also proves basic facts about
finite sets and gives ways to manipulate `Set.Finite` expressions.

Note that the instances in this file are selected somewhat arbitrarily on the basis of them not
needing any imports beyond `Data.Fintype.Card` (which is required by `Finite.ofFinset`); they can
certainly be organized better.

## Main definitions

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

assert_not_exists Monoid

open Set Function
open scoped symmDiff

universe u v w x

variable {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

namespace Set

theorem finite_def {s : Set α} : s.Finite ↔ Nonempty (Fintype s) :=
  finite_iff_nonempty_fintype s

protected alias ⟨Finite.nonempty_fintype, _⟩ := finite_def

/-- Construct a `Finite` instance for a `Set` from a `Finset` with the same elements. -/
protected theorem Finite.ofFinset {p : Set α} (s : Finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) : p.Finite :=
  have := Fintype.ofFinset s H; p.toFinite

/-- A finite set coerced to a type is a `Fintype`.
This is the `Fintype` projection for a `Set.Finite`.

Note that because `Finite` isn't a typeclass, this definition will not fire if it
is made into an instance -/
protected noncomputable def Finite.fintype {s : Set α} (h : s.Finite) : Fintype s :=
  h.nonempty_fintype.some

/-- Using choice, get the `Finset` that represents this `Set`. -/
protected noncomputable def Finite.toFinset {s : Set α} (h : s.Finite) : Finset α :=
  @Set.toFinset _ _ h.fintype

theorem Finite.toFinset_eq_toFinset {s : Set α} [Fintype s] (h : s.Finite) :
    h.toFinset = s.toFinset := by
  rw [Finite.toFinset, Subsingleton.elim h.fintype]

@[simp]
theorem toFinite_toFinset (s : Set α) [Fintype s] : s.toFinite.toFinset = s.toFinset :=
  s.toFinite.toFinset_eq_toFinset

theorem Finite.exists_finset {s : Set α} (h : s.Finite) :
    ∃ s' : Finset α, ∀ a : α, a ∈ s' ↔ a ∈ s := by
  cases h.nonempty_fintype
  exact ⟨s.toFinset, fun _ => mem_toFinset⟩

theorem Finite.exists_finset_coe {s : Set α} (h : s.Finite) : ∃ s' : Finset α, ↑s' = s := by
  cases h.nonempty_fintype
  exact ⟨s.toFinset, s.coe_toFinset⟩

/-- Finite sets can be lifted to finsets. -/
instance : CanLift (Set α) (Finset α) (↑) Set.Finite where prf _ hs := hs.exists_finset_coe

/-! ### Basic properties of `Set.Finite.toFinset` -/


namespace Finite

variable {s t : Set α} {a : α} (hs : s.Finite) {ht : t.Finite}

@[simp]
protected theorem mem_toFinset : a ∈ hs.toFinset ↔ a ∈ s :=
  @mem_toFinset _ _ hs.fintype _

@[simp]
protected theorem coe_toFinset : (hs.toFinset : Set α) = s :=
  @coe_toFinset _ _ hs.fintype

@[simp]
protected theorem toFinset_nonempty : hs.toFinset.Nonempty ↔ s.Nonempty := by
  rw [← Finset.coe_nonempty, Finite.coe_toFinset]

/-- Note that this is an equality of types not holding definitionally. Use wisely. -/
theorem coeSort_toFinset : ↥hs.toFinset = ↥s := by
  rw [← Finset.coe_sort_coe _, hs.coe_toFinset]

/-- The identity map, bundled as an equivalence between the subtypes of `s : Set α` and of
`h.toFinset : Finset α`, where `h` is a proof of finiteness of `s`. -/
@[simps!] def subtypeEquivToFinset : {x // x ∈ s} ≃ {x // x ∈ hs.toFinset} :=
  (Equiv.refl α).subtypeEquiv fun _ ↦ hs.mem_toFinset.symm

variable {hs}

@[simp]
protected theorem toFinset_inj : hs.toFinset = ht.toFinset ↔ s = t :=
  @toFinset_inj _ _ _ hs.fintype ht.fintype

@[simp]
theorem toFinset_subset {t : Finset α} : hs.toFinset ⊆ t ↔ s ⊆ t := by
  rw [← Finset.coe_subset, Finite.coe_toFinset]

@[simp]
theorem toFinset_ssubset {t : Finset α} : hs.toFinset ⊂ t ↔ s ⊂ t := by
  rw [← Finset.coe_ssubset, Finite.coe_toFinset]

@[simp]
theorem subset_toFinset {s : Finset α} : s ⊆ ht.toFinset ↔ ↑s ⊆ t := by
  rw [← Finset.coe_subset, Finite.coe_toFinset]

@[simp]
theorem ssubset_toFinset {s : Finset α} : s ⊂ ht.toFinset ↔ ↑s ⊂ t := by
  rw [← Finset.coe_ssubset, Finite.coe_toFinset]

@[mono]
protected theorem toFinset_subset_toFinset : hs.toFinset ⊆ ht.toFinset ↔ s ⊆ t := by
  simp only [← Finset.coe_subset, Finite.coe_toFinset]

@[mono]
protected theorem toFinset_ssubset_toFinset : hs.toFinset ⊂ ht.toFinset ↔ s ⊂ t := by
  simp only [← Finset.coe_ssubset, Finite.coe_toFinset]

protected alias ⟨_, toFinset_mono⟩ := Finite.toFinset_subset_toFinset

protected alias ⟨_, toFinset_strictMono⟩ := Finite.toFinset_ssubset_toFinset

@[simp high]
protected theorem toFinset_setOf [Fintype α] (p : α → Prop) [DecidablePred p]
    (h : { x | p x }.Finite) : h.toFinset = ({x | p x} : Finset α) := by simp

@[simp]
nonrec theorem disjoint_toFinset {hs : s.Finite} {ht : t.Finite} :
    Disjoint hs.toFinset ht.toFinset ↔ Disjoint s t :=
  @disjoint_toFinset _ _ _ hs.fintype ht.fintype

protected theorem toFinset_inter [DecidableEq α] (hs : s.Finite) (ht : t.Finite)
    (h : (s ∩ t).Finite) : h.toFinset = hs.toFinset ∩ ht.toFinset := by
  ext
  simp

protected theorem toFinset_union [DecidableEq α] (hs : s.Finite) (ht : t.Finite)
    (h : (s ∪ t).Finite) : h.toFinset = hs.toFinset ∪ ht.toFinset := by
  ext
  simp

protected theorem toFinset_diff [DecidableEq α] (hs : s.Finite) (ht : t.Finite)
    (h : (s \ t).Finite) : h.toFinset = hs.toFinset \ ht.toFinset := by
  ext
  simp

open scoped symmDiff in
protected theorem toFinset_symmDiff [DecidableEq α] (hs : s.Finite) (ht : t.Finite)
    (h : (s ∆ t).Finite) : h.toFinset = hs.toFinset ∆ ht.toFinset := by
  ext
  simp [mem_symmDiff, Finset.mem_symmDiff]

protected theorem toFinset_compl [DecidableEq α] [Fintype α] (hs : s.Finite) (h : sᶜ.Finite) :
    h.toFinset = hs.toFinsetᶜ := by
  ext
  simp

protected theorem toFinset_univ [Fintype α] (h : (Set.univ : Set α).Finite) :
    h.toFinset = Finset.univ := by
  simp

@[simp]
protected theorem toFinset_eq_empty {h : s.Finite} : h.toFinset = ∅ ↔ s = ∅ :=
  @toFinset_eq_empty _ _ h.fintype

protected theorem toFinset_empty (h : (∅ : Set α).Finite) : h.toFinset = ∅ := by
  simp

@[simp]
protected theorem toFinset_eq_univ [Fintype α] {h : s.Finite} :
    h.toFinset = Finset.univ ↔ s = univ :=
  @toFinset_eq_univ _ _ _ h.fintype

protected theorem toFinset_image [DecidableEq β] (f : α → β) (hs : s.Finite) (h : (f '' s).Finite) :
    h.toFinset = hs.toFinset.image f := by
  ext
  simp

protected theorem toFinset_range [DecidableEq α] [Fintype β] (f : β → α) (h : (range f).Finite) :
    h.toFinset = Finset.univ.image f := by
  ext
  simp

@[simp]
protected theorem toFinset_nontrivial (h : s.Finite) : h.toFinset.Nontrivial ↔ s.Nontrivial := by
  rw [Finset.Nontrivial, h.coe_toFinset]

end Finite

/-! ### Fintype instances

Every instance here should have a corresponding `Set.Finite` constructor in the next section.
-/

section FintypeInstances

instance fintypeUniv [Fintype α] : Fintype (@univ α) :=
  Fintype.ofEquiv α (Equiv.Set.univ α).symm

-- Redeclared with appropriate keys
instance fintypeTop [Fintype α] : Fintype (⊤ : Set α) := inferInstanceAs (Fintype (univ : Set α))

/-- If `(Set.univ : Set α)` is finite then `α` is a finite type. -/
noncomputable def fintypeOfFiniteUniv (H : (univ (α := α)).Finite) : Fintype α :=
  @Fintype.ofEquiv _ (univ : Set α) H.fintype (Equiv.Set.univ _)

instance fintypeUnion [DecidableEq α] (s t : Set α) [Fintype s] [Fintype t] :
    Fintype (s ∪ t : Set α) :=
  Fintype.ofFinset (s.toFinset ∪ t.toFinset) <| by simp

instance fintypeSep (s : Set α) (p : α → Prop) [Fintype s] [DecidablePred p] :
    Fintype ({ a ∈ s | p a } : Set α) :=
  Fintype.ofFinset {a ∈ s.toFinset | p a} <| by simp

instance fintypeInter (s t : Set α) [DecidableEq α] [Fintype s] [Fintype t] :
    Fintype (s ∩ t : Set α) :=
  Fintype.ofFinset (s.toFinset ∩ t.toFinset) <| by simp

/-- A `Fintype` instance for set intersection where the left set has a `Fintype` instance. -/
instance fintypeInterOfLeft (s t : Set α) [Fintype s] [DecidablePred (· ∈ t)] :
    Fintype (s ∩ t : Set α) :=
  Fintype.ofFinset {a ∈ s.toFinset | a ∈ t} <| by simp

/-- A `Fintype` instance for set intersection where the right set has a `Fintype` instance. -/
instance fintypeInterOfRight (s t : Set α) [Fintype t] [DecidablePred (· ∈ s)] :
    Fintype (s ∩ t : Set α) :=
  Fintype.ofFinset {a ∈ t.toFinset | a ∈ s} <| by simp [and_comm]

/-- A `Fintype` structure on a set defines a `Fintype` structure on its subset. -/
def fintypeSubset (s : Set α) {t : Set α} [Fintype s] [DecidablePred (· ∈ t)] (h : t ⊆ s) :
    Fintype t := by
  rw [← inter_eq_self_of_subset_right h]
  apply Set.fintypeInterOfLeft

instance fintypeDiff [DecidableEq α] (s t : Set α) [Fintype s] [Fintype t] :
    Fintype (s \ t : Set α) :=
  Fintype.ofFinset (s.toFinset \ t.toFinset) <| by simp

instance fintypeDiffLeft (s t : Set α) [Fintype s] [DecidablePred (· ∈ t)] :
    Fintype (s \ t : Set α) :=
  Set.fintypeSep s (· ∈ tᶜ)

instance fintypeEmpty : Fintype (∅ : Set α) :=
  Fintype.ofFinset ∅ <| by simp

instance fintypeSingleton (a : α) : Fintype ({a} : Set α) :=
  Fintype.ofFinset {a} <| by simp

/-- A `Fintype` instance for inserting an element into a `Set` using the
corresponding `insert` function on `Finset`. This requires `DecidableEq α`.
There is also `Set.fintypeInsert'` when `a ∈ s` is decidable. -/
instance fintypeInsert (a : α) (s : Set α) [DecidableEq α] [Fintype s] :
    Fintype (insert a s : Set α) :=
  Fintype.ofFinset (insert a s.toFinset) <| by simp

/-- A `Fintype` structure on `insert a s` when inserting a new element. -/
def fintypeInsertOfNotMem {a : α} (s : Set α) [Fintype s] (h : a ∉ s) :
    Fintype (insert a s : Set α) :=
  Fintype.ofFinset ⟨a ::ₘ s.toFinset.1, s.toFinset.nodup.cons (by simp [h])⟩ <| by simp

/-- A `Fintype` structure on `insert a s` when inserting a pre-existing element. -/
def fintypeInsertOfMem {a : α} (s : Set α) [Fintype s] (h : a ∈ s) : Fintype (insert a s : Set α) :=
  Fintype.ofFinset s.toFinset <| by simp [h]

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

instance fintypeImage [DecidableEq β] (s : Set α) (f : α → β) [Fintype s] : Fintype (f '' s) :=
  Fintype.ofFinset (s.toFinset.image f) <| by simp

/-- If a function `f` has a partial inverse `g` and the image of `s` under `f` is a set with
a `Fintype` instance, then `s` has a `Fintype` structure as well. -/
def fintypeOfFintypeImage (s : Set α) {f : α → β} {g} (I : IsPartialInv f g) [Fintype (f '' s)] :
    Fintype s :=
  Fintype.ofFinset ⟨_, (f '' s).toFinset.2.filterMap g <| injective_of_isPartialInv_right I⟩
    fun a => by
    suffices (∃ b x, f x = b ∧ g b = some a ∧ x ∈ s) ↔ a ∈ s by
      simpa [exists_and_left.symm, and_comm, and_left_comm, and_assoc]
    rw [exists_swap]
    suffices (∃ x, x ∈ s ∧ g (f x) = some a) ↔ a ∈ s by simpa [and_comm, and_left_comm, and_assoc]
    simp [I _, (injective_of_isPartialInv I).eq_iff]

instance fintypeMap {α β} [DecidableEq β] :
    ∀ (s : Set α) (f : α → β) [Fintype s], Fintype (f <$> s) :=
  Set.fintypeImage

instance fintypeLTNat (n : ℕ) : Fintype { i | i < n } :=
  Fintype.ofFinset (Finset.range n) <| by simp

instance fintypeLENat (n : ℕ) : Fintype { i | i ≤ n } := by
  simpa [Nat.lt_succ_iff] using Set.fintypeLTNat (n + 1)

/-- This is not an instance so that it does not conflict with the one
in `Mathlib/Order/Interval/Finset/Defs.lean`. -/
def Nat.fintypeIio (n : ℕ) : Fintype (Iio n) :=
  Set.fintypeLTNat n

instance fintypeMemFinset (s : Finset α) : Fintype { a | a ∈ s } :=
  Finset.fintypeCoeSort s

end FintypeInstances

end Set

/-! ### Finset -/

namespace Finset

/-- Gives a `Set.Finite` for the `Finset` coerced to a `Set`.
This is a wrapper around `Set.toFinite`. -/
@[simp]
theorem finite_toSet (s : Finset α) : (s : Set α).Finite :=
  Set.toFinite _

theorem finite_toSet_toFinset (s : Finset α) : s.finite_toSet.toFinset = s := by
  rw [toFinite_toFinset, toFinset_coe]

/-- This is a kind of induction principle. See `Finset.induction` for the usual induction principle
for finsets. -/
lemma «forall» {p : Finset α → Prop} :
    (∀ s, p s) ↔ ∀ (s : Set α) (hs : s.Finite), p hs.toFinset where
  mp h s hs := h _
  mpr h s := by simpa using h s s.finite_toSet

lemma «exists» {p : Finset α → Prop} :
    (∃ s, p s) ↔ ∃ (s : Set α) (hs : s.Finite), p hs.toFinset where
  mp := fun ⟨s, hs⟩ ↦ ⟨s, s.finite_toSet, by simpa⟩
  mpr := fun ⟨s, hs, hs'⟩ ↦ ⟨hs.toFinset, hs'⟩

end Finset

namespace Multiset

@[simp]
theorem finite_toSet (s : Multiset α) : { x | x ∈ s }.Finite := by
  classical simpa only [← Multiset.mem_toFinset] using s.toFinset.finite_toSet

@[simp]
theorem finite_toSet_toFinset [DecidableEq α] (s : Multiset α) :
    s.finite_toSet.toFinset = s.toFinset := by
  ext x
  simp

end Multiset

@[simp]
theorem List.finite_toSet (l : List α) : { x | x ∈ l }.Finite :=
  (show Multiset α from ⟦l⟧).finite_toSet

/-! ### Finite instances

There is seemingly some overlap between the following instances and the `Fintype` instances
in `Data.Set.Finite`. While every `Fintype` instance gives a `Finite` instance, those
instances that depend on `Fintype` or `Decidable` instances need an additional `Finite` instance
to be able to generally apply.

Some set instances do not appear here since they are consequences of others, for example
`Subtype.Finite` for subsets of a finite type.
-/


namespace Finite.Set

example {s : Set α} [Finite α] : Finite s :=
  inferInstance

example : Finite (∅ : Set α) :=
  inferInstance

example (a : α) : Finite ({a} : Set α) :=
  inferInstance

instance finite_union (s t : Set α) [Finite s] [Finite t] : Finite (s ∪ t : Set α) := by
  cases nonempty_fintype s
  cases nonempty_fintype t
  classical
  infer_instance

instance finite_sep (s : Set α) (p : α → Prop) [Finite s] : Finite ({ a ∈ s | p a } : Set α) := by
  cases nonempty_fintype s
  classical
  infer_instance

protected theorem subset (s : Set α) {t : Set α} [Finite s] (h : t ⊆ s) : Finite t := by
  rw [← sep_eq_of_subset h]
  infer_instance

instance finite_inter_of_right (s t : Set α) [Finite t] : Finite (s ∩ t : Set α) :=
  Finite.Set.subset t inter_subset_right

instance finite_inter_of_left (s t : Set α) [Finite s] : Finite (s ∩ t : Set α) :=
  Finite.Set.subset s inter_subset_left

instance finite_diff (s t : Set α) [Finite s] : Finite (s \ t : Set α) :=
  Finite.Set.subset s diff_subset

instance finite_insert (a : α) (s : Set α) [Finite s] : Finite (insert a s : Set α) :=
  Finite.Set.finite_union {a} s

instance finite_image (s : Set α) (f : α → β) [Finite s] : Finite (f '' s) := by
  cases nonempty_fintype s
  classical
  infer_instance

end Finite.Set

namespace Set

/-! ### Constructors for `Set.Finite`

Every constructor here should have a corresponding `Fintype` instance in the previous section
(or in the `Fintype` module).

The implementation of these constructors ideally should be no more than `Set.toFinite`,
after possibly setting up some `Fintype` and classical `Decidable` instances.
-/


section SetFiniteConstructors
variable {s t u : Set α}

@[nontriviality]
theorem Finite.of_subsingleton [Subsingleton α] (s : Set α) : s.Finite :=
  s.toFinite

theorem finite_univ [Finite α] : (@univ α).Finite :=
  Set.toFinite _

theorem finite_univ_iff : (@univ α).Finite ↔ Finite α := (Equiv.Set.univ α).finite_iff

alias ⟨_root_.Finite.of_finite_univ, _⟩ := finite_univ_iff

theorem Finite.subset {s : Set α} (hs : s.Finite) {t : Set α} (ht : t ⊆ s) : t.Finite := by
  have := hs.to_subtype
  exact Finite.Set.subset _ ht

theorem Finite.union (hs : s.Finite) (ht : t.Finite) : (s ∪ t).Finite := by
  rw [Set.Finite] at hs ht
  apply toFinite

theorem Finite.finite_of_compl {s : Set α} (hs : s.Finite) (hsc : sᶜ.Finite) : Finite α := by
  rw [← finite_univ_iff, ← union_compl_self s]
  exact hs.union hsc

theorem Finite.sup {s t : Set α} : s.Finite → t.Finite → (s ⊔ t).Finite :=
  Finite.union

theorem Finite.sep {s : Set α} (hs : s.Finite) (p : α → Prop) : { a ∈ s | p a }.Finite :=
  hs.subset <| sep_subset _ _

theorem Finite.inter_of_left {s : Set α} (hs : s.Finite) (t : Set α) : (s ∩ t).Finite :=
  hs.subset inter_subset_left

theorem Finite.inter_of_right {s : Set α} (hs : s.Finite) (t : Set α) : (t ∩ s).Finite :=
  hs.subset inter_subset_right

theorem Finite.inf_of_left {s : Set α} (h : s.Finite) (t : Set α) : (s ⊓ t).Finite :=
  h.inter_of_left t

theorem Finite.inf_of_right {s : Set α} (h : s.Finite) (t : Set α) : (t ⊓ s).Finite :=
  h.inter_of_right t

protected lemma Infinite.mono {s t : Set α} (h : s ⊆ t) : s.Infinite → t.Infinite :=
  mt fun ht ↦ ht.subset h

theorem Finite.diff (hs : s.Finite) : (s \ t).Finite := hs.subset diff_subset

theorem Finite.of_diff {s t : Set α} (hd : (s \ t).Finite) (ht : t.Finite) : s.Finite :=
  (hd.union ht).subset <| subset_diff_union _ _

lemma Finite.symmDiff (hs : s.Finite) (ht : t.Finite) : (s ∆ t).Finite := hs.diff.union ht.diff

lemma Finite.symmDiff_congr (hst : (s ∆ t).Finite) : (s ∆ u).Finite ↔ (t ∆ u).Finite where
  mp hsu := (hst.union hsu).subset (symmDiff_comm s t ▸ symmDiff_triangle ..)
  mpr htu := (hst.union htu).subset (symmDiff_triangle ..)

@[simp]
theorem finite_empty : (∅ : Set α).Finite :=
  toFinite _

protected theorem Infinite.nonempty {s : Set α} (h : s.Infinite) : s.Nonempty :=
  nonempty_iff_ne_empty.2 <| by
    rintro rfl
    exact h finite_empty

@[simp]
theorem finite_singleton (a : α) : ({a} : Set α).Finite :=
  toFinite _

@[simp]
protected theorem Finite.insert (a : α) {s : Set α} (hs : s.Finite) : (insert a s).Finite :=
  (finite_singleton a).union hs

theorem Finite.image {s : Set α} (f : α → β) (hs : s.Finite) : (f '' s).Finite := by
  have := hs.to_subtype
  apply toFinite

lemma Finite.of_surjOn {s : Set α} {t : Set β} (f : α → β) (hf : SurjOn f s t) (hs : s.Finite) :
    t.Finite := (hs.image _).subset hf

theorem Finite.map {α β} {s : Set α} : ∀ f : α → β, s.Finite → (f <$> s).Finite :=
  Finite.image

theorem Finite.of_finite_image {s : Set α} {f : α → β} (h : (f '' s).Finite) (hi : Set.InjOn f s) :
    s.Finite :=
  have := h.to_subtype
  .of_injective _ hi.bijOn_image.bijective.injective

theorem Finite.of_injOn {f : α → β} {s : Set α} {t : Set β} (hm : MapsTo f s t) (hi : InjOn f s)
    (ht : t.Finite) : s.Finite :=
  .of_finite_image (ht.subset (image_subset_iff.mpr hm)) hi

theorem BijOn.finite_iff_finite {f : α → β} {s : Set α} {t : Set β} (h : BijOn f s t) :
    s.Finite ↔ t.Finite :=
  ⟨fun h1 ↦ h1.of_surjOn _ h.2.2, fun h1 ↦ h1.of_injOn h.1 h.2.1⟩

section preimage
variable {f : α → β} {s : Set β}

theorem finite_of_finite_preimage (h : (f ⁻¹' s).Finite) (hs : s ⊆ range f) : s.Finite := by
  rw [← image_preimage_eq_of_subset hs]
  exact Finite.image f h

theorem Finite.of_preimage (h : (f ⁻¹' s).Finite) (hf : Surjective f) : s.Finite :=
  hf.image_preimage s ▸ h.image _

theorem Finite.preimage (I : Set.InjOn f (f ⁻¹' s)) (h : s.Finite) : (f ⁻¹' s).Finite :=
  (h.subset (image_preimage_subset f s)).of_finite_image I

protected lemma Infinite.preimage (hs : s.Infinite) (hf : s ⊆ range f) : (f ⁻¹' s).Infinite :=
  fun h ↦ hs <| finite_of_finite_preimage h hf

lemma Infinite.preimage' (hs : (s ∩ range f).Infinite) : (f ⁻¹' s).Infinite :=
  (hs.preimage inter_subset_right).mono <| preimage_mono inter_subset_left

theorem Finite.preimage_embedding {s : Set β} (f : α ↪ β) (h : s.Finite) : (f ⁻¹' s).Finite :=
  h.preimage fun _ _ _ _ h' => f.injective h'

end preimage

theorem finite_lt_nat (n : ℕ) : Set.Finite { i | i < n } :=
  toFinite _

theorem finite_le_nat (n : ℕ) : Set.Finite { i | i ≤ n } :=
  toFinite _

section MapsTo

variable {s : Set α} {f : α → α}

theorem Finite.surjOn_iff_bijOn_of_mapsTo (hs : s.Finite) (hm : MapsTo f s s) :
    SurjOn f s s ↔ BijOn f s s := by
  refine ⟨fun h ↦ ⟨hm, ?_, h⟩, BijOn.surjOn⟩
  have : Finite s := finite_coe_iff.mpr hs
  exact hm.restrict_inj.mp (Finite.injective_iff_surjective.mpr <| hm.restrict_surjective_iff.mpr h)

theorem Finite.injOn_iff_bijOn_of_mapsTo (hs : s.Finite) (hm : MapsTo f s s) :
    InjOn f s ↔ BijOn f s s := by
  refine ⟨fun h ↦ ⟨hm, h, ?_⟩, BijOn.injOn⟩
  have : Finite s := finite_coe_iff.mpr hs
  exact hm.restrict_surjective_iff.mp (Finite.injective_iff_surjective.mp <| hm.restrict_inj.mpr h)

end MapsTo

theorem finite_mem_finset (s : Finset α) : { a | a ∈ s }.Finite :=
  toFinite _

theorem Subsingleton.finite {s : Set α} (h : s.Subsingleton) : s.Finite :=
  h.induction_on finite_empty finite_singleton

theorem Infinite.nontrivial {s : Set α} (hs : s.Infinite) : s.Nontrivial :=
  not_subsingleton_iff.1 <| mt Subsingleton.finite hs

theorem finite_preimage_inl_and_inr {s : Set (α ⊕ β)} :
    (Sum.inl ⁻¹' s).Finite ∧ (Sum.inr ⁻¹' s).Finite ↔ s.Finite :=
  ⟨fun h => image_preimage_inl_union_image_preimage_inr s ▸ (h.1.image _).union (h.2.image _),
    fun h => ⟨h.preimage Sum.inl_injective.injOn, h.preimage Sum.inr_injective.injOn⟩⟩

theorem exists_finite_iff_finset {p : Set α → Prop} :
    (∃ s : Set α, s.Finite ∧ p s) ↔ ∃ s : Finset α, p ↑s :=
  ⟨fun ⟨_, hs, hps⟩ => ⟨hs.toFinset, hs.coe_toFinset.symm ▸ hps⟩, fun ⟨s, hs⟩ =>
    ⟨s, s.finite_toSet, hs⟩⟩

theorem exists_subset_image_finite_and {f : α → β} {s : Set α} {p : Set β → Prop} :
    (∃ t ⊆ f '' s, t.Finite ∧ p t) ↔ ∃ t ⊆ s, t.Finite ∧ p (f '' t) := by
  classical
  simp_rw [@and_comm (_ ⊆ _), and_assoc, exists_finite_iff_finset, @and_comm (p _),
    Finset.subset_set_image_iff]
  aesop

theorem finite_range_ite {p : α → Prop} [DecidablePred p] {f g : α → β} (hf : (range f).Finite)
    (hg : (range g).Finite) : (range fun x => if p x then f x else g x).Finite :=
  (hf.union hg).subset range_ite_subset

theorem finite_range_const {c : β} : (range fun _ : α => c).Finite :=
  (finite_singleton c).subset range_const_subset

end SetFiniteConstructors

/-! ### Properties -/

instance Finite.inhabited : Inhabited { s : Set α // s.Finite } :=
  ⟨⟨∅, finite_empty⟩⟩

@[simp]
theorem finite_union {s t : Set α} : (s ∪ t).Finite ↔ s.Finite ∧ t.Finite :=
  ⟨fun h => ⟨h.subset subset_union_left, h.subset subset_union_right⟩, fun ⟨hs, ht⟩ =>
    hs.union ht⟩

theorem finite_image_iff {s : Set α} {f : α → β} (hi : InjOn f s) : (f '' s).Finite ↔ s.Finite :=
  ⟨fun h => h.of_finite_image hi, Finite.image _⟩

theorem univ_finite_iff_nonempty_fintype : (univ : Set α).Finite ↔ Nonempty (Fintype α) :=
  ⟨fun h => ⟨fintypeOfFiniteUniv h⟩, fun ⟨_i⟩ => finite_univ⟩

-- `simp`-normal form is `Set.toFinset_singleton`.
theorem Finite.toFinset_singleton {a : α} (ha : ({a} : Set α).Finite := finite_singleton _) :
    ha.toFinset = {a} :=
  Set.toFinite_toFinset _

@[simp]
theorem Finite.toFinset_insert [DecidableEq α] {s : Set α} {a : α} (hs : (insert a s).Finite) :
    hs.toFinset = insert a (hs.subset <| subset_insert _ _).toFinset :=
  Finset.ext <| by simp

theorem Finite.toFinset_insert' [DecidableEq α] {a : α} {s : Set α} (hs : s.Finite) :
    (hs.insert a).toFinset = insert a hs.toFinset :=
  Finite.toFinset_insert _

theorem finite_option {s : Set (Option α)} : s.Finite ↔ { x : α | some x ∈ s }.Finite :=
  ⟨fun h => h.preimage_embedding Embedding.some, fun h =>
    ((h.image some).insert none).subset fun x =>
      x.casesOn (fun _ => Or.inl rfl) fun _ hx => Or.inr <| mem_image_of_mem _ hx⟩

/-- Induction principle for finite sets: To prove a property `motive` of a finite set `s`, it's
enough to prove for the empty set and to prove that `motive t → motive ({a} ∪ t)` for all `t`.

See also `Set.Finite.induction_on` for the version requiring to check `motive t → motive ({a} ∪ t)`
only for `t ⊆ s`. -/
@[elab_as_elim]
theorem Finite.induction_on {motive : ∀ s : Set α, s.Finite → Prop} (s : Set α) (hs : s.Finite)
    (empty : motive ∅ finite_empty)
    (insert : ∀ {a s}, a ∉ s →
      ∀ hs : Set.Finite s, motive s hs → motive (insert a s) (hs.insert a)) :
    motive s hs := by
  lift s to Finset α using id hs
  induction' s using Finset.cons_induction_on with a s ha ih
  · simpa
  · simpa using @insert a s ha (Set.toFinite _) (ih _)

/-- Induction principle for finite sets: To prove a property `C` of a finite set `s`, it's enough
to prove for the empty set and to prove that `C t → C ({a} ∪ t)` for all `t ⊆ s`.

This is analogous to `Finset.induction_on'`. See also `Set.Finite.induction_on` for the version
requiring `C t → C ({a} ∪ t)` for all `t`. -/
@[elab_as_elim]
theorem Finite.induction_on_subset {motive : ∀ s : Set α, s.Finite → Prop} (s : Set α)
    (hs : s.Finite) (empty : motive ∅ finite_empty)
    (insert : ∀ {a t}, a ∈ s → ∀ hts : t ⊆ s, a ∉ t → motive t (hs.subset hts) →
      motive (insert a t) ((hs.subset hts).insert a)) : motive s hs := by
  refine Set.Finite.induction_on (motive := fun t _ => ∀ hts : t ⊆ s, motive t (hs.subset hts)) s hs
    (fun _ => empty) ?_ .rfl
  intro a s has _ hCs haS
  rw [insert_subset_iff] at haS
  exact insert haS.1 haS.2 has (hCs haS.2)

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

end

/-! ### Cardinality -/

theorem card_empty : Fintype.card (∅ : Set α) = 0 :=
  rfl

@[deprecated (since := "2025-02-05")] alias empty_card := card_empty

theorem card_fintypeInsertOfNotMem {a : α} (s : Set α) [Fintype s] (h : a ∉ s) :
    @Fintype.card _ (fintypeInsertOfNotMem s h) = Fintype.card s + 1 := by
  simp [fintypeInsertOfNotMem, Fintype.card_ofFinset]

@[simp]
theorem card_insert {a : α} (s : Set α) [Fintype s] (h : a ∉ s)
    {d : Fintype (insert a s : Set α)} : @Fintype.card _ d = Fintype.card s + 1 := by
  rw [← card_fintypeInsertOfNotMem s h]; congr!

theorem card_image_of_inj_on {s : Set α} [Fintype s] {f : α → β} [Fintype (f '' s)]
    (H : ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y) : Fintype.card (f '' s) = Fintype.card s :=
  haveI := Classical.propDecidable
  calc
    Fintype.card (f '' s) = (s.toFinset.image f).card := Fintype.card_of_finset' _ (by simp)
    _ = s.toFinset.card :=
      Finset.card_image_of_injOn fun x hx y hy hxy =>
        H x (mem_toFinset.1 hx) y (mem_toFinset.1 hy) hxy
    _ = Fintype.card s := (Fintype.card_of_finset' _ fun _ => mem_toFinset).symm

theorem card_image_of_injective (s : Set α) [Fintype s] {f : α → β} [Fintype (f '' s)]
    (H : Function.Injective f) : Fintype.card (f '' s) = Fintype.card s :=
  card_image_of_inj_on fun _ _ _ _ h => H h

@[simp]
theorem card_singleton (a : α) : Fintype.card ({a} : Set α) = 1 :=
  rfl

theorem card_lt_card {s t : Set α} [Fintype s] [Fintype t] (h : s ⊂ t) :
    Fintype.card s < Fintype.card t :=
  Fintype.card_lt_of_injective_not_surjective (Set.inclusion h.1) (Set.inclusion_injective h.1)
    fun hst => (ssubset_iff_subset_ne.1 h).2 (eq_of_inclusion_surjective hst)

theorem card_le_card {s t : Set α} [Fintype s] [Fintype t] (hsub : s ⊆ t) :
    Fintype.card s ≤ Fintype.card t :=
  Fintype.card_le_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)

theorem eq_of_subset_of_card_le {s t : Set α} [Fintype s] [Fintype t] (hsub : s ⊆ t)
    (hcard : Fintype.card t ≤ Fintype.card s) : s = t :=
  (eq_or_ssubset_of_subset hsub).elim id fun h => absurd hcard <| not_le_of_gt <| card_lt_card h

theorem card_range_of_injective [Fintype α] {f : α → β} (hf : Injective f) [Fintype (range f)] :
    Fintype.card (range f) = Fintype.card α :=
  Eq.symm <| Fintype.card_congr <| Equiv.ofInjective f hf

theorem Finite.card_toFinset {s : Set α} [Fintype s] (h : s.Finite) :
    h.toFinset.card = Fintype.card s :=
  Eq.symm <| Fintype.card_of_finset' _ fun _ ↦ h.mem_toFinset

theorem card_ne_eq [Fintype α] (a : α) [Fintype { x : α | x ≠ a }] :
    Fintype.card { x : α | x ≠ a } = Fintype.card α - 1 := by
  haveI := Classical.decEq α
  rw [← toFinset_card, toFinset_setOf, Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]

/-! ### Infinite sets -/

variable {s t : Set α}

theorem infinite_univ_iff : (@univ α).Infinite ↔ Infinite α := by
  rw [Set.Infinite, finite_univ_iff, not_finite_iff_infinite]

theorem infinite_univ [h : Infinite α] : (@univ α).Infinite :=
  infinite_univ_iff.2 h

lemma Infinite.exists_notMem_finite (hs : s.Infinite) (ht : t.Finite) : ∃ a, a ∈ s ∧ a ∉ t := by
  by_contra! h; exact hs <| ht.subset h

@[deprecated (since := "2025-05-23")]
alias Infinite.exists_not_mem_finite := Infinite.exists_notMem_finite

lemma Infinite.exists_notMem_finset (hs : s.Infinite) (t : Finset α) : ∃ a ∈ s, a ∉ t :=
  hs.exists_notMem_finite t.finite_toSet

@[deprecated (since := "2025-05-23")]
alias Infinite.exists_not_mem_finset := Infinite.exists_notMem_finset

section Infinite
variable [Infinite α]

lemma Finite.exists_notMem (hs : s.Finite) : ∃ a, a ∉ s := by
  by_contra! h; exact infinite_univ (hs.subset fun a _ ↦ h _)

@[deprecated (since := "2025-05-23")] alias Finite.exists_not_mem := Finite.exists_notMem

lemma _root_.Finset.exists_notMem (s : Finset α) : ∃ a, a ∉ s := s.finite_toSet.exists_notMem

@[deprecated (since := "2025-05-23")]
alias _root_.Finset.exists_not_mem := _root_.Finset.exists_notMem

end Infinite

/-- Embedding of `ℕ` into an infinite set. -/
noncomputable def Infinite.natEmbedding (s : Set α) (h : s.Infinite) : ℕ ↪ s :=
  h.to_subtype.natEmbedding

theorem Infinite.exists_subset_card_eq {s : Set α} (hs : s.Infinite) (n : ℕ) :
    ∃ t : Finset α, ↑t ⊆ s ∧ t.card = n :=
  ⟨((Finset.range n).map (hs.natEmbedding _)).map (Embedding.subtype _), by simp⟩

theorem infinite_of_finite_compl [Infinite α] {s : Set α} (hs : sᶜ.Finite) : s.Infinite := fun h =>
  Set.infinite_univ (α := α) (by simpa using hs.union h)

theorem Finite.infinite_compl [Infinite α] {s : Set α} (hs : s.Finite) : sᶜ.Infinite := fun h =>
  Set.infinite_univ (α := α) (by simpa using hs.union h)

theorem Infinite.diff {s t : Set α} (hs : s.Infinite) (ht : t.Finite) : (s \ t).Infinite := fun h =>
  hs <| h.of_diff ht

@[simp]
theorem infinite_union {s t : Set α} : (s ∪ t).Infinite ↔ s.Infinite ∨ t.Infinite := by
  simp only [Set.Infinite, finite_union, not_and_or]

theorem Infinite.of_image (f : α → β) {s : Set α} (hs : (f '' s).Infinite) : s.Infinite :=
  mt (Finite.image f) hs

theorem infinite_image_iff {s : Set α} {f : α → β} (hi : InjOn f s) :
    (f '' s).Infinite ↔ s.Infinite :=
  not_congr <| finite_image_iff hi

theorem infinite_range_iff {f : α → β} (hi : Injective f) :
    (range f).Infinite ↔ Infinite α := by
  rw [← image_univ, infinite_image_iff hi.injOn, infinite_univ_iff]

protected alias ⟨_, Infinite.image⟩ := infinite_image_iff

theorem infinite_of_injOn_mapsTo {s : Set α} {t : Set β} {f : α → β} (hi : InjOn f s)
    (hm : MapsTo f s t) (hs : s.Infinite) : t.Infinite :=
  ((infinite_image_iff hi).2 hs).mono (mapsTo'.mp hm)

theorem Infinite.exists_ne_map_eq_of_mapsTo {s : Set α} {t : Set β} {f : α → β} (hs : s.Infinite)
    (hf : MapsTo f s t) (ht : t.Finite) : ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y := by
  contrapose! ht
  exact infinite_of_injOn_mapsTo (fun x hx y hy => not_imp_not.1 (ht x hx y hy)) hf hs

theorem infinite_range_of_injective [Infinite α] {f : α → β} (hi : Injective f) :
    (range f).Infinite := by
  rw [← image_univ, infinite_image_iff hi.injOn]
  exact infinite_univ

theorem infinite_of_injective_forall_mem [Infinite α] {s : Set β} {f : α → β} (hi : Injective f)
    (hf : ∀ x : α, f x ∈ s) : s.Infinite := by
  rw [← range_subset_iff] at hf
  exact (infinite_range_of_injective hi).mono hf

theorem not_injOn_infinite_finite_image {f : α → β} {s : Set α} (h_inf : s.Infinite)
    (h_fin : (f '' s).Finite) : ¬InjOn f s := by
  have : Finite (f '' s) := finite_coe_iff.mpr h_fin
  have : Infinite s := infinite_coe_iff.mpr h_inf
  have h := not_injective_infinite_finite
            ((f '' s).codRestrict (s.restrict f) fun x => ⟨x, x.property, rfl⟩)
  contrapose! h
  rwa [injective_codRestrict, ← injOn_iff_injective]

theorem finite_range_findGreatest {P : α → ℕ → Prop} [∀ x, DecidablePred (P x)] {b : ℕ} :
    (range fun x => Nat.findGreatest (P x) b).Finite :=
  (finite_le_nat b).subset <| range_subset_iff.2 fun _ => Nat.findGreatest_le _

end Set

namespace Finset

lemma exists_card_eq [Infinite α] : ∀ n : ℕ, ∃ s : Finset α, s.card = n
  | 0 => ⟨∅, card_empty⟩
  | n + 1 => by
    classical
    obtain ⟨s, rfl⟩ := exists_card_eq n
    obtain ⟨a, ha⟩ := s.exists_notMem
    exact ⟨insert a s, card_insert_of_notMem ha⟩

end Finset

section LinearOrder
variable [LinearOrder α] {s : Set α}

/-- If a linear order does not contain any triple of elements `x < y < z`, then this type
is finite. -/
lemma Finite.of_forall_not_lt_lt (h : ∀ ⦃x y z : α⦄, x < y → y < z → False) : Finite α := by
  nontriviality α
  rcases exists_pair_ne α with ⟨x, y, hne⟩
  refine @Finite.of_fintype α ⟨{x, y}, fun z => ?_⟩
  simpa [hne] using eq_or_eq_or_eq_of_forall_not_lt_lt h z x y

/-- If a set `s` does not contain any triple of elements `x < y < z`, then `s` is finite. -/
lemma Set.finite_of_forall_not_lt_lt (h : ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, x < y → y < z → False) :
    Set.Finite s :=
  @Set.toFinite _ s <| Finite.of_forall_not_lt_lt <| by simpa only [SetCoe.forall'] using h

end LinearOrder
