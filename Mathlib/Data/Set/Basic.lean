/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
module

public import Mathlib.Order.PropInstances
public import Mathlib.Tactic.Lift
public import Mathlib.Tactic.Attr.Register

/-!
# Basic properties of sets

Sets in Lean are homogeneous; all their elements have the same type. Sets whose elements
have type `X` are thus defined as `Set X := X → Prop`. Note that this function need not
be decidable. The definition is in the module `Mathlib/Data/Set/Defs.lean`.

This file provides some basic definitions related to sets and functions not present in the
definitions file, as well as extra lemmas for functions defined in the definitions file and
`Mathlib/Data/Set/Operations.lean` (empty set, univ, union, intersection, insert, singleton and
powerset).

Note that a set is a term, not a type. There is a coercion from `Set α` to `Type*` sending
`s` to the corresponding subtype `↥s`.

See also the directory `Mathlib/SetTheory/ZFC/`, which contains an encoding of ZFC set theory in
Lean.

## Main definitions

Notation used here:

-  `f : α → β` is a function,

-  `s : Set α` and `s₁ s₂ : Set α` are subsets of `α`

-  `t : Set β` is a subset of `β`.

Definitions in the file:

* `Nonempty s : Prop` : the predicate `s ≠ ∅`. Note that this is the preferred way to express the
  fact that `s` has an element (see the Implementation Notes).

* `inclusion s₁ s₂ : ↥s₁ → ↥s₂` : the map `↥s₁ → ↥s₂` induced by an inclusion `s₁ ⊆ s₂`.

## Implementation notes

* `s.Nonempty` is to be preferred to `s ≠ ∅` or `∃ x, x ∈ s`. It has the advantage that
  the `s.Nonempty` dot notation can be used.

* For `s : Set α`, do not use `Subtype s`. Instead use `↥s` or `(s : Type*)` or `s`.

## Tags

set, sets, subset, subsets, union, intersection, insert, singleton, powerset
-/

@[expose] public section

assert_not_exists HeytingAlgebra RelIso

/-! ### Set coercion to a type -/

open Function

universe u v

namespace Set

variable {α : Type u} {s t : Set α}

protected theorem mem_injective : Injective (Membership.mem : Set α → α → Prop) := injective_id
protected theorem mem_surjective : Surjective (Membership.mem : Set α → α → Prop) := surjective_id
protected theorem mem_bijective : Bijective (Membership.mem : Set α → α → Prop) := bijective_id

instance instDistribLattice : DistribLattice (Set α) where
  __ : DistribLattice (α → Prop) := inferInstance
  le := (· ≤ ·)
  lt := fun s t => s ⊆ t ∧ ¬t ⊆ s
  sup := (· ∪ ·)
  inf := (· ∩ ·)

instance instBoundedOrder : BoundedOrder (Set α) where
  __ : BoundedOrder (α → Prop) := inferInstance
  bot := ∅
  top := univ

instance : HasSSubset (Set α) :=
  ⟨(· < ·)⟩

@[simp]
theorem top_eq_univ : (⊤ : Set α) = univ :=
  rfl

@[simp]
theorem bot_eq_empty : (⊥ : Set α) = ∅ :=
  rfl

@[simp]
theorem sup_eq_union : ((· ⊔ ·) : Set α → Set α → Set α) = (· ∪ ·) :=
  rfl

@[simp]
theorem inf_eq_inter : ((· ⊓ ·) : Set α → Set α → Set α) = (· ∩ ·) :=
  rfl

@[simp]
theorem le_eq_subset : ((· ≤ ·) : Set α → Set α → Prop) = (· ⊆ ·) :=
  rfl

@[simp]
theorem lt_eq_ssubset : ((· < ·) : Set α → Set α → Prop) = (· ⊂ ·) :=
  rfl

theorem le_iff_subset : s ≤ t ↔ s ⊆ t :=
  Iff.rfl

theorem lt_iff_ssubset : s < t ↔ s ⊂ t :=
  Iff.rfl

alias ⟨_root_.LE.le.subset, _root_.HasSubset.Subset.le⟩ := le_iff_subset

alias ⟨_root_.LT.lt.ssubset, _root_.HasSSubset.SSubset.lt⟩ := lt_iff_ssubset

instance PiSetCoe.canLift (ι : Type u) (α : ι → Type v) [∀ i, Nonempty (α i)] (s : Set ι) :
    CanLift (∀ i : s, α i) (∀ i, α i) (fun f i => f i) fun _ => True :=
  PiSubtype.canLift ι α (· ∈ s)

instance PiSetCoe.canLift' (ι : Type u) (α : Type v) [Nonempty α] (s : Set ι) :
    CanLift (s → α) (ι → α) (fun f i => f i) fun _ => True :=
  PiSetCoe.canLift ι (fun _ => α) s

end Set

section SetCoe

variable {α : Type u}

instance (s : Set α) : CoeTC s α := ⟨fun x => x.1⟩

theorem Set.coe_eq_subtype (s : Set α) : ↥s = { x // x ∈ s } :=
  rfl

@[simp]
theorem Set.coe_setOf (p : α → Prop) : ↥{ x | p x } = { x // p x } :=
  rfl

theorem SetCoe.forall {s : Set α} {p : s → Prop} : (∀ x : s, p x) ↔ ∀ (x) (h : x ∈ s), p ⟨x, h⟩ :=
  Subtype.forall

theorem SetCoe.exists {s : Set α} {p : s → Prop} :
    (∃ x : s, p x) ↔ ∃ (x : _) (h : x ∈ s), p ⟨x, h⟩ :=
  Subtype.exists

theorem SetCoe.exists' {s : Set α} {p : ∀ x, x ∈ s → Prop} :
    (∃ (x : _) (h : x ∈ s), p x h) ↔ ∃ x : s, p x.1 x.2 :=
  (@SetCoe.exists _ _ fun x => p x.1 x.2).symm

theorem SetCoe.forall' {s : Set α} {p : ∀ x, x ∈ s → Prop} :
    (∀ (x) (h : x ∈ s), p x h) ↔ ∀ x : s, p x.1 x.2 :=
  (@SetCoe.forall _ _ fun x => p x.1 x.2).symm

@[simp]
theorem set_coe_cast :
    ∀ {s t : Set α} (H' : s = t) (H : ↥s = ↥t) (x : s), cast H x = ⟨x.1, H' ▸ x.2⟩
  | _, _, rfl, _, _ => rfl

theorem SetCoe.ext {s : Set α} {a b : s} : (a : α) = b → a = b :=
  Subtype.ext

theorem SetCoe.ext_iff {s : Set α} {a b : s} : (↑a : α) = ↑b ↔ a = b :=
  Iff.intro SetCoe.ext fun h => h ▸ rfl

end SetCoe

/-- See also `Subtype.prop` -/
theorem Subtype.mem {α : Type*} {s : Set α} (p : s) : (p : α) ∈ s :=
  p.prop

namespace Set

variable {α : Type u} {β : Type v} {a b : α} {s s₁ s₂ t t₁ t₂ u : Set α}

instance : Inhabited (Set α) :=
  ⟨∅⟩

@[trans]
theorem mem_of_mem_of_subset {x : α} {s t : Set α} (hx : x ∈ s) (h : s ⊆ t) : x ∈ t :=
  h hx

theorem setOf_injective : Function.Injective (@setOf α) := injective_id

theorem setOf_inj {p q : α → Prop} : { x | p x } = { x | q x } ↔ p = q := Iff.rfl

/-! ### Lemmas about `mem` and `setOf` -/

theorem setOf_bijective : Bijective (setOf : (α → Prop) → Set α) :=
  bijective_id

theorem subset_setOf {p : α → Prop} {s : Set α} : s ⊆ setOf p ↔ ∀ x, x ∈ s → p x :=
  Iff.rfl

theorem setOf_subset {p : α → Prop} {s : Set α} : setOf p ⊆ s ↔ ∀ x, p x → x ∈ s :=
  Iff.rfl

@[simp]
theorem setOf_subset_setOf {p q : α → Prop} : { a | p a } ⊆ { a | q a } ↔ ∀ a, p a → q a :=
  Iff.rfl

@[gcongr]
alias ⟨_, setOf_subset_setOf_of_imp⟩ := setOf_subset_setOf

theorem setOf_and {p q : α → Prop} : { a | p a ∧ q a } = { a | p a } ∩ { a | q a } :=
  rfl

theorem setOf_or {p q : α → Prop} : { a | p a ∨ q a } = { a | p a } ∪ { a | q a } :=
  rfl

/-! ### Subset and strict subset relations -/


instance : @Std.Refl (Set α) (· ⊆ ·) :=
  show Std.Refl (· ≤ ·) by infer_instance

instance : IsTrans (Set α) (· ⊆ ·) :=
  show IsTrans (Set α) (· ≤ ·) by infer_instance

instance : Trans ((· ⊆ ·) : Set α → Set α → Prop) (· ⊆ ·) (· ⊆ ·) :=
  show Trans (· ≤ ·) (· ≤ ·) (· ≤ ·) by infer_instance

instance : @Std.Antisymm (Set α) (· ⊆ ·) :=
  show Std.Antisymm (· ≤ ·) by infer_instance

instance : @Std.Irrefl (Set α) (· ⊂ ·) :=
  show Std.Irrefl (· < ·) by infer_instance

instance : IsTrans (Set α) (· ⊂ ·) :=
  show IsTrans (Set α) (· < ·) by infer_instance

instance : Trans ((· ⊂ ·) : Set α → Set α → Prop) (· ⊂ ·) (· ⊂ ·) :=
  show Trans (· < ·) (· < ·) (· < ·) by infer_instance

instance : Trans ((· ⊂ ·) : Set α → Set α → Prop) (· ⊆ ·) (· ⊂ ·) :=
  show Trans (· < ·) (· ≤ ·) (· < ·) by infer_instance

instance : Trans ((· ⊆ ·) : Set α → Set α → Prop) (· ⊂ ·) (· ⊂ ·) :=
  show Trans (· ≤ ·) (· < ·) (· < ·) by infer_instance

instance : @Std.Asymm (Set α) (· ⊂ ·) :=
  show Std.Asymm (· < ·) by infer_instance

instance : IsNonstrictStrictOrder (Set α) (· ⊆ ·) (· ⊂ ·) :=
  ⟨fun _ _ => Iff.rfl⟩

-- TODO(Jeremy): write a tactic to unfold specific instances of generic notation?
@[grind =]
theorem subset_def : (s ⊆ t) = ∀ x, x ∈ s → x ∈ t :=
  rfl

@[grind =]
theorem ssubset_def : (s ⊂ t) = (s ⊆ t ∧ ¬t ⊆ s) :=
  rfl

@[refl]
theorem Subset.refl (a : Set α) : a ⊆ a := fun _ => id

theorem Subset.rfl {s : Set α} : s ⊆ s :=
  Subset.refl s

@[trans]
theorem Subset.trans {a b c : Set α} (ab : a ⊆ b) (bc : b ⊆ c) : a ⊆ c := fun _ h => bc <| ab h

@[trans]
theorem mem_of_eq_of_mem {x y : α} {s : Set α} (hx : x = y) (h : y ∈ s) : x ∈ s :=
  hx.symm ▸ h

theorem Subset.antisymm {a b : Set α} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b :=
  Set.ext fun _ => ⟨@h₁ _, @h₂ _⟩

theorem Subset.antisymm_iff {a b : Set α} : a = b ↔ a ⊆ b ∧ b ⊆ a :=
  ⟨fun e => ⟨e.subset, e.symm.subset⟩, fun ⟨h₁, h₂⟩ => Subset.antisymm h₁ h₂⟩

-- an alternative name
theorem eq_of_subset_of_subset {a b : Set α} : a ⊆ b → b ⊆ a → a = b :=
  Subset.antisymm

@[gcongr] theorem mem_of_subset_of_mem {s₁ s₂ : Set α} {a : α} (h : s₁ ⊆ s₂) : a ∈ s₁ → a ∈ s₂ :=
  @h _

theorem notMem_subset (h : s ⊆ t) : a ∉ t → a ∉ s :=
  mt <| mem_of_subset_of_mem h

theorem subset_iff_notMem : s ⊆ t ↔ ∀ ⦃a⦄, a ∉ t → a ∉ s := by
  simp only [subset_def, not_imp_not]

theorem not_subset : ¬s ⊆ t ↔ ∃ a ∈ s, a ∉ t := by
  simp only [subset_def, not_forall, exists_prop]

theorem not_univ_subset : ¬univ ⊆ s ↔ ∃ a, a ∉ s := by
  simp [not_subset]

@[deprecated not_univ_subset (since := "2026-03-12")]
theorem not_top_subset : ¬⊤ ⊆ s ↔ ∃ a, a ∉ s :=
  not_univ_subset

lemma eq_of_forall_subset_iff (h : ∀ u, s ⊆ u ↔ t ⊆ u) : s = t := eq_of_forall_ge_iff h

/-! ### Definition of strict subsets `s ⊂ t` and basic properties. -/

protected theorem eq_or_ssubset_of_subset (h : s ⊆ t) : s = t ∨ s ⊂ t :=
  eq_or_lt_of_le h

theorem exists_of_ssubset {s t : Set α} (h : s ⊂ t) : ∃ x ∈ t, x ∉ s :=
  not_subset.1 h.2

protected theorem ssubset_iff_subset_ne {s t : Set α} : s ⊂ t ↔ s ⊆ t ∧ s ≠ t :=
  @lt_iff_le_and_ne (Set α) _ s t

theorem ssubset_iff_of_subset {s t : Set α} (h : s ⊆ t) : s ⊂ t ↔ ∃ x ∈ t, x ∉ s :=
  ⟨exists_of_ssubset, fun ⟨_, hxt, hxs⟩ => ⟨h, fun h => hxs <| h hxt⟩⟩

theorem ssubset_iff_exists {s t : Set α} : s ⊂ t ↔ s ⊆ t ∧ ∃ x ∈ t, x ∉ s :=
  ⟨fun h ↦ ⟨h.le, Set.exists_of_ssubset h⟩, fun ⟨h1, h2⟩ ↦ (Set.ssubset_iff_of_subset h1).mpr h2⟩

protected theorem ssubset_of_ssubset_of_subset {s₁ s₂ s₃ : Set α} (hs₁s₂ : s₁ ⊂ s₂)
    (hs₂s₃ : s₂ ⊆ s₃) : s₁ ⊂ s₃ :=
  ⟨Subset.trans hs₁s₂.1 hs₂s₃, fun hs₃s₁ => hs₁s₂.2 (Subset.trans hs₂s₃ hs₃s₁)⟩

protected theorem ssubset_of_subset_of_ssubset {s₁ s₂ s₃ : Set α} (hs₁s₂ : s₁ ⊆ s₂)
    (hs₂s₃ : s₂ ⊂ s₃) : s₁ ⊂ s₃ :=
  ⟨Subset.trans hs₁s₂ hs₂s₃.1, fun hs₃s₁ => hs₂s₃.2 (Subset.trans hs₃s₁ hs₁s₂)⟩

theorem notMem_empty (x : α) : x ∉ (∅ : Set α) :=
  id

theorem not_notMem : ¬a ∉ s ↔ a ∈ s :=
  not_not

/-! ### Non-empty sets -/

theorem nonempty_coe_sort {s : Set α} : Nonempty ↥s ↔ s.Nonempty :=
  nonempty_subtype

alias ⟨_, Nonempty.coe_sort⟩ := nonempty_coe_sort

theorem nonempty_def : s.Nonempty ↔ ∃ x, x ∈ s :=
  Iff.rfl

theorem nonempty_of_mem {x} (h : x ∈ s) : s.Nonempty :=
  ⟨x, h⟩

theorem Nonempty.not_subset_empty : s.Nonempty → ¬s ⊆ ∅
  | ⟨_, hx⟩, hs => hs hx

/-- Extract a witness from `s.Nonempty`. This function might be used instead of case analysis
on the argument. Note that it makes a proof depend on the `Classical.choice` axiom. -/
protected noncomputable def Nonempty.some (h : s.Nonempty) : α :=
  Classical.choose h

protected theorem Nonempty.some_mem (h : s.Nonempty) : h.some ∈ s :=
  Classical.choose_spec h

@[gcongr] theorem Nonempty.mono (ht : s ⊆ t) (hs : s.Nonempty) : t.Nonempty :=
  hs.imp ht

theorem nonempty_of_not_subset (h : ¬s ⊆ t) : (s \ t).Nonempty :=
  let ⟨x, xs, xt⟩ := not_subset.1 h
  ⟨x, xs, xt⟩

theorem nonempty_of_ssubset (ht : s ⊂ t) : (t \ s).Nonempty :=
  nonempty_of_not_subset ht.2

theorem Nonempty.of_sdiff (h : (s \ t).Nonempty) : s.Nonempty :=
  h.imp fun _ => And.left

@[deprecated (since := "2026-06-03")] alias Nonempty.of_diff := Nonempty.of_sdiff

theorem nonempty_of_ssubset' (ht : s ⊂ t) : t.Nonempty :=
  (nonempty_of_ssubset ht).of_sdiff

theorem Nonempty.inl (hs : s.Nonempty) : (s ∪ t).Nonempty :=
  hs.imp fun _ => Or.inl

theorem Nonempty.inr (ht : t.Nonempty) : (s ∪ t).Nonempty :=
  ht.imp fun _ => Or.inr

@[simp]
theorem union_nonempty : (s ∪ t).Nonempty ↔ s.Nonempty ∨ t.Nonempty :=
  exists_or

theorem Nonempty.left (h : (s ∩ t).Nonempty) : s.Nonempty :=
  h.imp fun _ => And.left

theorem Nonempty.right (h : (s ∩ t).Nonempty) : t.Nonempty :=
  h.imp fun _ => And.right

theorem inter_nonempty : (s ∩ t).Nonempty ↔ ∃ x, x ∈ s ∧ x ∈ t :=
  Iff.rfl

theorem inter_nonempty_iff_exists_left : (s ∩ t).Nonempty ↔ ∃ x ∈ s, x ∈ t := by
  simp_rw [inter_nonempty]

theorem inter_nonempty_iff_exists_right : (s ∩ t).Nonempty ↔ ∃ x ∈ t, x ∈ s := by
  simp_rw [inter_nonempty, and_comm]

theorem nonempty_iff_univ_nonempty : Nonempty α ↔ (univ : Set α).Nonempty :=
  ⟨fun ⟨x⟩ => ⟨x, trivial⟩, fun ⟨x, _⟩ => ⟨x⟩⟩

@[simp]
theorem univ_nonempty : ∀ [Nonempty α], (univ : Set α).Nonempty
  | ⟨x⟩ => ⟨x, trivial⟩

theorem Nonempty.to_subtype : s.Nonempty → Nonempty (↥s) :=
  nonempty_subtype.2

theorem Nonempty.to_type : s.Nonempty → Nonempty α := fun ⟨x, _⟩ => ⟨x⟩

instance univ.nonempty [Nonempty α] : Nonempty (↥(Set.univ : Set α)) :=
  Set.univ_nonempty.to_subtype

-- Redeclare for refined keys
-- `Nonempty (@Subtype _ (@Membership.mem _ (Set _) _ (@Top.top (Set _) _)))`
instance instNonemptyTop [Nonempty α] : Nonempty (⊤ : Set α) :=
  inferInstanceAs (Nonempty (univ : Set α))

theorem Nonempty.of_subtype [Nonempty (↥s)] : s.Nonempty := nonempty_subtype.mp ‹_›

/-! ### Lemmas about the empty set -/

theorem empty_def : (∅ : Set α) = { _x : α | False } :=
  rfl

@[simp, grind =, push]
theorem mem_empty_iff_false (x : α) : x ∈ (∅ : Set α) ↔ False :=
  Iff.rfl

@[simp, grind =]
theorem setOf_false : { _a : α | False } = ∅ :=
  rfl

@[simp] theorem setOf_bot : { _x : α | ⊥ } = ∅ := rfl

@[simp]
theorem empty_subset (s : Set α) : ∅ ⊆ s :=
  nofun

@[simp, grind =]
theorem subset_empty_iff {s : Set α} : s ⊆ ∅ ↔ s = ∅ :=
  (Subset.antisymm_iff.trans <| and_iff_left (empty_subset _)).symm

theorem eq_empty_iff_forall_notMem {s : Set α} : s = ∅ ↔ ∀ x, x ∉ s :=
  subset_empty_iff.symm

theorem eq_empty_of_forall_notMem (h : ∀ x, x ∉ s) : s = ∅ :=
  subset_empty_iff.1 h

theorem eq_empty_of_subset_empty {s : Set α} : s ⊆ ∅ → s = ∅ :=
  subset_empty_iff.1

/-- See also `Set.nonempty_iff_ne_empty`. -/
@[push]
theorem not_nonempty_iff_eq_empty : ¬s.Nonempty ↔ s = ∅ := by
  simp only [Set.Nonempty, not_exists, eq_empty_iff_forall_notMem]

/-- See also `Set.not_nonempty_iff_eq_empty`. -/
@[push ←]
theorem nonempty_iff_ne_empty : s.Nonempty ↔ s ≠ ∅ :=
  not_nonempty_iff_eq_empty.not_right

/-- Variant of `nonempty_iff_ne_empty` used by `push Not`. -/
@[push ←]
theorem nonempty_iff_empty_ne : s.Nonempty ↔ ∅ ≠ s :=
  nonempty_iff_ne_empty.trans ne_comm

/-- See also `nonempty_iff_ne_empty'`. -/
theorem not_nonempty_iff_eq_empty' : ¬Nonempty s ↔ s = ∅ := by
  rw [nonempty_subtype, not_exists, eq_empty_iff_forall_notMem]

/-- See also `not_nonempty_iff_eq_empty'`. -/
theorem nonempty_iff_ne_empty' : Nonempty s ↔ s ≠ ∅ :=
  not_nonempty_iff_eq_empty'.not_right

alias ⟨Nonempty.ne_empty, _⟩ := nonempty_iff_ne_empty

@[simp]
theorem not_nonempty_empty : ¬(∅ : Set α).Nonempty := fun ⟨_, hx⟩ => hx

@[simp]
theorem isEmpty_coe_sort {s : Set α} : IsEmpty (↥s) ↔ s = ∅ :=
  not_iff_not.1 <| by simpa using! nonempty_iff_ne_empty

lemma eq_empty_of_isEmpty (s : Set α) [IsEmpty s] : s = ∅ := by
  simpa using ‹IsEmpty s›

/-- There is exactly one set of a type that is empty. -/
instance uniqueEmpty [IsEmpty α] : Unique (Set α) where
  uniq _ := eq_empty_of_isEmpty _

theorem eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.Nonempty :=
  or_iff_not_imp_left.2 nonempty_iff_ne_empty.2

theorem subset_eq_empty {s t : Set α} (h : t ⊆ s) (e : s = ∅) : t = ∅ :=
  subset_empty_iff.1 <| e ▸ h

theorem forall_mem_empty {p : α → Prop} : (∀ x ∈ (∅ : Set α), p x) ↔ True :=
  iff_true_intro fun _ => False.elim

instance (α : Type u) : IsEmpty.{u + 1} (↥(∅ : Set α)) :=
  ⟨fun x => x.2⟩

@[simp]
theorem empty_ssubset : ∅ ⊂ s ↔ s.Nonempty :=
  (@bot_lt_iff_ne_bot (Set α) _ _ _).trans nonempty_iff_ne_empty.symm

alias ⟨_, Nonempty.empty_ssubset⟩ := empty_ssubset

/-!

### Universal set.

In Lean `@univ α` (or `univ : Set α`) is the set that contains all elements of type `α`.
Mathematically it is the same as `α` but it has a different type.

-/


@[simp, grind =]
theorem setOf_true : { _x : α | True } = univ :=
  rfl

@[simp] theorem setOf_top : { _x : α | ⊤ } = univ := rfl

@[simp]
theorem univ_eq_empty_iff : (univ : Set α) = ∅ ↔ IsEmpty α :=
  eq_empty_iff_forall_notMem.trans
    ⟨fun H => ⟨fun x => H x trivial⟩, fun H x _ => @IsEmpty.false α H x⟩

theorem empty_ne_univ [Nonempty α] : (∅ : Set α) ≠ univ := fun e =>
  not_isEmpty_of_nonempty α <| univ_eq_empty_iff.1 e.symm

@[simp, grind ←]
theorem subset_univ (s : Set α) : s ⊆ univ := fun _ _ => trivial

@[simp, grind =]
theorem univ_subset_iff {s : Set α} : univ ⊆ s ↔ s = univ :=
  @top_le_iff _ _ _ s

alias ⟨eq_univ_of_univ_subset, _⟩ := univ_subset_iff

theorem eq_univ_iff_forall {s : Set α} : s = univ ↔ ∀ x, x ∈ s :=
  univ_subset_iff.symm.trans <| forall_congr' fun _ => imp_iff_right trivial

theorem eq_univ_of_forall {s : Set α} : (∀ x, x ∈ s) → s = univ :=
  eq_univ_iff_forall.2

theorem Nonempty.eq_univ [Subsingleton α] : s.Nonempty → s = univ := by
  rintro ⟨x, hx⟩
  exact eq_univ_of_forall fun y => by rwa [Subsingleton.elim y x]

theorem eq_univ_of_subset {s t : Set α} (h : s ⊆ t) (hs : s = univ) : t = univ :=
  eq_univ_of_univ_subset <| (hs ▸ h : univ ⊆ t)

theorem exists_mem_of_nonempty (α) : ∀ [Nonempty α], ∃ x : α, x ∈ (univ : Set α)
  | ⟨x⟩ => ⟨x, trivial⟩

theorem ne_univ_iff_exists_notMem {α : Type*} (s : Set α) : s ≠ univ ↔ ∃ a, a ∉ s := by
  rw [← not_forall, ← eq_univ_iff_forall]

theorem not_subset_iff_exists_mem_notMem {α : Type*} {s t : Set α} :
    ¬s ⊆ t ↔ ∃ x, x ∈ s ∧ x ∉ t := by simp [subset_def]

theorem univ_unique [Unique α] : @Set.univ α = {default} :=
  Set.ext fun x => iff_of_true trivial <| Subsingleton.elim x default

theorem ssubset_univ_iff : s ⊂ univ ↔ s ≠ univ :=
  lt_top_iff_ne_top

theorem ssubset_univ_iff_nonempty_compl : s ⊂ univ ↔ sᶜ.Nonempty := by
  rw [ssubset_def, Set.not_univ_subset, Set.nonempty_def]
  simp

alias ⟨_, Nonempty.ssubset_univ⟩ := ssubset_univ_iff_nonempty_compl

theorem compl_ssubset_univ : sᶜ ⊂ univ ↔ s.Nonempty := by
  rw [ssubset_def, Set.not_univ_subset, Set.nonempty_def]
  simp

alias ⟨_, Nonempty.compl_ssubset_univ⟩ := compl_ssubset_univ

instance nontrivial_of_nonempty [Nonempty α] : Nontrivial (Set α) :=
  ⟨⟨∅, univ, empty_ne_univ⟩⟩

/-! ### Lemmas about union -/

theorem union_def {s₁ s₂ : Set α} : s₁ ∪ s₂ = { a | a ∈ s₁ ∨ a ∈ s₂ } :=
  rfl

theorem mem_union_left {x : α} {a : Set α} (b : Set α) : x ∈ a → x ∈ a ∪ b :=
  Or.inl

theorem mem_union_right {x : α} {b : Set α} (a : Set α) : x ∈ b → x ∈ a ∪ b :=
  Or.inr

theorem mem_or_mem_of_mem_union {x : α} {a b : Set α} (H : x ∈ a ∪ b) : x ∈ a ∨ x ∈ b :=
  H

theorem MemUnion.elim {x : α} {a b : Set α} {P : Prop} (H₁ : x ∈ a ∪ b) (H₂ : x ∈ a → P)
    (H₃ : x ∈ b → P) : P :=
  Or.elim H₁ H₂ H₃

@[simp, grind =, push]
theorem mem_union (x : α) (a b : Set α) : x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b :=
  Iff.rfl

@[simp]
theorem union_self (a : Set α) : a ∪ a = a :=
  ext fun _ => or_self_iff

@[simp]
theorem union_empty (a : Set α) : a ∪ ∅ = a :=
  ext fun _ => iff_of_eq (or_false _)

@[simp]
theorem empty_union (a : Set α) : ∅ ∪ a = a :=
  ext fun _ => iff_of_eq (false_or _)

theorem union_comm (a b : Set α) : a ∪ b = b ∪ a :=
  ext fun _ => or_comm

theorem union_assoc (a b c : Set α) : a ∪ b ∪ c = a ∪ (b ∪ c) :=
  ext fun _ => or_assoc

instance union_isAssoc : Std.Associative (α := Set α) (· ∪ ·) :=
  ⟨union_assoc⟩

instance union_isComm : Std.Commutative (α := Set α) (· ∪ ·) :=
  ⟨union_comm⟩

theorem union_left_comm (s₁ s₂ s₃ : Set α) : s₁ ∪ (s₂ ∪ s₃) = s₂ ∪ (s₁ ∪ s₃) :=
  ext fun _ => or_left_comm

theorem union_right_comm (s₁ s₂ s₃ : Set α) : s₁ ∪ s₂ ∪ s₃ = s₁ ∪ s₃ ∪ s₂ :=
  ext fun _ => or_right_comm

@[simp]
theorem union_eq_left {s t : Set α} : s ∪ t = s ↔ t ⊆ s :=
  sup_eq_left

@[simp]
theorem union_eq_right {s t : Set α} : s ∪ t = t ↔ s ⊆ t :=
  sup_eq_right

theorem union_eq_self_of_subset_left {s t : Set α} (h : s ⊆ t) : s ∪ t = t :=
  union_eq_right.mpr h

theorem union_eq_self_of_subset_right {s t : Set α} (h : t ⊆ s) : s ∪ t = s :=
  union_eq_left.mpr h

@[simp]
theorem subset_union_left {s t : Set α} : s ⊆ s ∪ t := fun _ => Or.inl

@[simp]
theorem subset_union_right {s t : Set α} : t ⊆ s ∪ t := fun _ => Or.inr

theorem union_subset {s t r : Set α} (sr : s ⊆ r) (tr : t ⊆ r) : s ∪ t ⊆ r := fun _ =>
  Or.rec (@sr _) (@tr _)

@[simp]
theorem union_subset_iff {s t u : Set α} : s ∪ t ⊆ u ↔ s ⊆ u ∧ t ⊆ u :=
  (forall_congr' fun _ => or_imp).trans forall_and

@[gcongr]
theorem union_subset_union {s₁ s₂ t₁ t₂ : Set α} (h₁ : s₁ ⊆ s₂) (h₂ : t₁ ⊆ t₂) :
    s₁ ∪ t₁ ⊆ s₂ ∪ t₂ := fun _ => Or.imp (@h₁ _) (@h₂ _)

theorem union_subset_union_left {s₁ s₂ : Set α} (t) (h : s₁ ⊆ s₂) : s₁ ∪ t ⊆ s₂ ∪ t :=
  union_subset_union h Subset.rfl

theorem union_subset_union_right (s) {t₁ t₂ : Set α} (h : t₁ ⊆ t₂) : s ∪ t₁ ⊆ s ∪ t₂ :=
  union_subset_union Subset.rfl h

theorem subset_union_of_subset_left {s t : Set α} (h : s ⊆ t) (u : Set α) : s ⊆ t ∪ u :=
  h.trans subset_union_left

theorem subset_union_of_subset_right {s u : Set α} (h : s ⊆ u) (t : Set α) : s ⊆ t ∪ u :=
  h.trans subset_union_right

theorem union_congr_left (ht : t ⊆ s ∪ u) (hu : u ⊆ s ∪ t) : s ∪ t = s ∪ u :=
  sup_congr_left ht hu

theorem union_congr_right (hs : s ⊆ t ∪ u) (ht : t ⊆ s ∪ u) : s ∪ u = t ∪ u :=
  sup_congr_right hs ht

theorem union_eq_union_iff_left : s ∪ t = s ∪ u ↔ t ⊆ s ∪ u ∧ u ⊆ s ∪ t :=
  sup_eq_sup_iff_left

theorem union_eq_union_iff_right : s ∪ u = t ∪ u ↔ s ⊆ t ∪ u ∧ t ⊆ s ∪ u :=
  sup_eq_sup_iff_right

@[simp]
theorem union_empty_iff {s t : Set α} : s ∪ t = ∅ ↔ s = ∅ ∧ t = ∅ := by
  simp only [← subset_empty_iff]
  exact union_subset_iff

@[simp]
theorem union_univ (s : Set α) : s ∪ univ = univ := sup_top_eq _

@[simp]
theorem univ_union (s : Set α) : univ ∪ s = univ := top_sup_eq _

@[simp]
theorem ssubset_union_left_iff : s ⊂ s ∪ t ↔ ¬ t ⊆ s :=
  left_lt_sup

@[simp]
theorem ssubset_union_right_iff : t ⊂ s ∪ t ↔ ¬ s ⊆ t :=
  right_lt_sup

/-! ### Lemmas about intersection -/

theorem inter_def {s₁ s₂ : Set α} : s₁ ∩ s₂ = { a | a ∈ s₁ ∧ a ∈ s₂ } :=
  rfl

@[simp, mfld_simps, grind =, push]
theorem mem_inter_iff (x : α) (a b : Set α) : x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b :=
  Iff.rfl

theorem mem_inter {x : α} {a b : Set α} (ha : x ∈ a) (hb : x ∈ b) : x ∈ a ∩ b :=
  ⟨ha, hb⟩

theorem mem_of_mem_inter_left {x : α} {a b : Set α} (h : x ∈ a ∩ b) : x ∈ a :=
  h.left

theorem mem_of_mem_inter_right {x : α} {a b : Set α} (h : x ∈ a ∩ b) : x ∈ b :=
  h.right

@[simp]
theorem inter_self (a : Set α) : a ∩ a = a :=
  ext fun _ => and_self_iff

@[simp]
theorem inter_empty (a : Set α) : a ∩ ∅ = ∅ :=
  ext fun _ => iff_of_eq (and_false _)

@[simp]
theorem empty_inter (a : Set α) : ∅ ∩ a = ∅ :=
  ext fun _ => iff_of_eq (false_and _)

theorem inter_comm (a b : Set α) : a ∩ b = b ∩ a :=
  ext fun _ => and_comm

theorem inter_assoc (a b c : Set α) : a ∩ b ∩ c = a ∩ (b ∩ c) :=
  ext fun _ => and_assoc

instance inter_isAssoc : Std.Associative (α := Set α) (· ∩ ·) :=
  ⟨inter_assoc⟩

instance inter_isComm : Std.Commutative (α := Set α) (· ∩ ·) :=
  ⟨inter_comm⟩

theorem inter_left_comm (s₁ s₂ s₃ : Set α) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
  ext fun _ => and_left_comm

theorem inter_right_comm (s₁ s₂ s₃ : Set α) : s₁ ∩ s₂ ∩ s₃ = s₁ ∩ s₃ ∩ s₂ :=
  ext fun _ => and_right_comm

@[simp, mfld_simps]
theorem inter_subset_left {s t : Set α} : s ∩ t ⊆ s := fun _ => And.left

@[simp]
theorem inter_subset_right {s t : Set α} : s ∩ t ⊆ t := fun _ => And.right

theorem subset_inter {s t r : Set α} (rs : r ⊆ s) (rt : r ⊆ t) : r ⊆ s ∩ t := fun _ h =>
  ⟨rs h, rt h⟩

@[simp]
theorem subset_inter_iff {s t r : Set α} : r ⊆ s ∩ t ↔ r ⊆ s ∧ r ⊆ t :=
  (forall_congr' fun _ => imp_and).trans forall_and

@[simp] lemma inter_eq_left : s ∩ t = s ↔ s ⊆ t := inf_eq_left

@[simp] lemma inter_eq_right : s ∩ t = t ↔ t ⊆ s := inf_eq_right

@[simp] lemma left_eq_inter : s = s ∩ t ↔ s ⊆ t := left_eq_inf

@[simp] lemma right_eq_inter : t = s ∩ t ↔ t ⊆ s := right_eq_inf

theorem inter_eq_self_of_subset_left {s t : Set α} : s ⊆ t → s ∩ t = s :=
  inter_eq_left.mpr

theorem inter_eq_self_of_subset_right {s t : Set α} : t ⊆ s → s ∩ t = t :=
  inter_eq_right.mpr

theorem inter_congr_left (ht : s ∩ u ⊆ t) (hu : s ∩ t ⊆ u) : s ∩ t = s ∩ u :=
  inf_congr_left ht hu

theorem inter_congr_right (hs : t ∩ u ⊆ s) (ht : s ∩ u ⊆ t) : s ∩ u = t ∩ u :=
  inf_congr_right hs ht

theorem inter_eq_inter_iff_left : s ∩ t = s ∩ u ↔ s ∩ u ⊆ t ∧ s ∩ t ⊆ u :=
  inf_eq_inf_iff_left

theorem inter_eq_inter_iff_right : s ∩ u = t ∩ u ↔ t ∩ u ⊆ s ∧ s ∩ u ⊆ t :=
  inf_eq_inf_iff_right

@[simp, mfld_simps]
theorem inter_univ (a : Set α) : a ∩ univ = a := inf_top_eq _

@[simp, mfld_simps]
theorem univ_inter (a : Set α) : univ ∩ a = a := top_inf_eq _

@[gcongr]
theorem inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s₁ ⊆ t₁) (h₂ : s₂ ⊆ t₂) :
    s₁ ∩ s₂ ⊆ t₁ ∩ t₂ := fun _ => And.imp (@h₁ _) (@h₂ _)

theorem inter_subset_inter_left {s t : Set α} (u : Set α) (H : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  inter_subset_inter H Subset.rfl

theorem inter_subset_inter_right {s t : Set α} (u : Set α) (H : s ⊆ t) : u ∩ s ⊆ u ∩ t :=
  inter_subset_inter Subset.rfl H

theorem union_inter_cancel_left {s t : Set α} : (s ∪ t) ∩ s = s :=
  inter_eq_self_of_subset_right subset_union_left

theorem union_inter_cancel_right {s t : Set α} : (s ∪ t) ∩ t = t :=
  inter_eq_self_of_subset_right subset_union_right

theorem inter_setOf_eq_sep (s : Set α) (p : α → Prop) : s ∩ {a | p a} = {a ∈ s | p a} :=
  rfl

theorem setOf_inter_eq_sep (p : α → Prop) (s : Set α) : {a | p a} ∩ s = {a ∈ s | p a} :=
  inter_comm _ _

theorem sep_eq_inter_sep {α : Type*} {s t : Set α} {p : α → Prop} (hst : s ⊆ t) :
    {x ∈ s | p x} = s ∩ {x ∈ t | p x} := by
  rw [← inter_setOf_eq_sep s p, ← inter_setOf_eq_sep t p,
    ← inter_assoc, ← left_eq_inter.mpr hst]

@[deprecated (since := "2025-12-10")] alias sep_of_subset := sep_eq_inter_sep

@[simp]
theorem inter_ssubset_right_iff : s ∩ t ⊂ t ↔ ¬ t ⊆ s :=
  inf_lt_right

@[simp]
theorem inter_ssubset_left_iff : s ∩ t ⊂ s ↔ ¬ s ⊆ t :=
  inf_lt_left

/-! ### Distributivity laws -/

theorem inter_union_distrib_left (s t u : Set α) : s ∩ (t ∪ u) = s ∩ t ∪ s ∩ u :=
  inf_sup_left _ _ _

theorem union_inter_distrib_right (s t u : Set α) : (s ∪ t) ∩ u = s ∩ u ∪ t ∩ u :=
  inf_sup_right _ _ _

theorem union_inter_distrib_left (s t u : Set α) : s ∪ t ∩ u = (s ∪ t) ∩ (s ∪ u) :=
  sup_inf_left _ _ _

theorem inter_union_distrib_right (s t u : Set α) : s ∩ t ∪ u = (s ∪ u) ∩ (t ∪ u) :=
  sup_inf_right _ _ _

theorem union_union_distrib_left (s t u : Set α) : s ∪ (t ∪ u) = s ∪ t ∪ (s ∪ u) :=
  sup_sup_distrib_left _ _ _

theorem union_union_distrib_right (s t u : Set α) : s ∪ t ∪ u = s ∪ u ∪ (t ∪ u) :=
  sup_sup_distrib_right _ _ _

theorem inter_inter_distrib_left (s t u : Set α) : s ∩ (t ∩ u) = s ∩ t ∩ (s ∩ u) :=
  inf_inf_distrib_left _ _ _

theorem inter_inter_distrib_right (s t u : Set α) : s ∩ t ∩ u = s ∩ u ∩ (t ∩ u) :=
  inf_inf_distrib_right _ _ _

theorem union_union_union_comm (s t u v : Set α) : s ∪ t ∪ (u ∪ v) = s ∪ u ∪ (t ∪ v) :=
  sup_sup_sup_comm _ _ _ _

theorem inter_inter_inter_comm (s t u v : Set α) : s ∩ t ∩ (u ∩ v) = s ∩ u ∩ (t ∩ v) :=
  inf_inf_inf_comm _ _ _ _

/-! ### Lemmas about sets defined as `{x ∈ s | p x}`. -/

section Sep

variable {p q : α → Prop} {x : α}

theorem mem_sep (xs : x ∈ s) (px : p x) : x ∈ { x ∈ s | p x } :=
  ⟨xs, px⟩

@[simp]
theorem sep_mem_eq : { x ∈ s | x ∈ t } = s ∩ t :=
  rfl

@[simp]
theorem mem_sep_iff : x ∈ { x ∈ s | p x } ↔ x ∈ s ∧ p x :=
  Iff.rfl

theorem sep_ext_iff : { x ∈ s | p x } = { x ∈ s | q x } ↔ ∀ x ∈ s, p x ↔ q x := by
  simp_rw [Set.ext_iff, mem_sep_iff, and_congr_right_iff]

theorem sep_eq_of_subset (h : s ⊆ t) : { x ∈ t | x ∈ s } = s :=
  inter_eq_self_of_subset_right h

@[simp]
theorem sep_subset (s : Set α) (p : α → Prop) : { x ∈ s | p x } ⊆ s := fun _ => And.left

theorem sep_subset_setOf (s : Set α) (p : α → Prop) : { x ∈ s | p x } ⊆ { x | p x } :=
  fun _ => And.right

@[simp]
theorem sep_eq_self_iff_mem_true : { x ∈ s | p x } = s ↔ ∀ x ∈ s, p x := by
  simp_rw [Set.ext_iff, mem_sep_iff, and_iff_left_iff_imp]

@[simp]
theorem sep_eq_empty_iff_mem_false : { x ∈ s | p x } = ∅ ↔ ∀ x ∈ s, ¬p x := by
  simp_rw [Set.ext_iff, mem_sep_iff, mem_empty_iff_false, iff_false, not_and]

theorem sep_true : { x ∈ s | True } = s :=
  inter_univ s

theorem sep_false : { x ∈ s | False } = ∅ :=
  inter_empty s

theorem sep_empty (p : α → Prop) : { x ∈ (∅ : Set α) | p x } = ∅ :=
  empty_inter {x | p x}

theorem sep_univ : { x ∈ (univ : Set α) | p x } = { x | p x } :=
  univ_inter {x | p x}

@[simp]
theorem sep_union : { x | (x ∈ s ∨ x ∈ t) ∧ p x } = { x ∈ s | p x } ∪ { x ∈ t | p x } :=
  union_inter_distrib_right { x | x ∈ s } { x | x ∈ t } {x | p x}

@[simp]
theorem sep_inter : { x | (x ∈ s ∧ x ∈ t) ∧ p x } = { x ∈ s | p x } ∩ { x ∈ t | p x } :=
  inter_inter_distrib_right s t {x | p x}

@[simp]
theorem sep_and : { x ∈ s | p x ∧ q x } = { x ∈ s | p x } ∩ { x ∈ s | q x } :=
  inter_inter_distrib_left s {x | p x} {x | q x}

@[simp]
theorem sep_or : { x ∈ s | p x ∨ q x } = { x ∈ s | p x } ∪ { x ∈ s | q x } :=
  inter_union_distrib_left s {x | p x} {x | q x}

@[simp]
theorem sep_setOf : { x ∈ { y | p y } | q x } = { x | p x ∧ q x } :=
  rfl

end Sep

/-! ### Powerset -/

theorem mem_powerset {x s : Set α} (h : x ⊆ s) : x ∈ 𝒫 s := @h

theorem subset_of_mem_powerset {x s : Set α} (h : x ∈ 𝒫 s) : x ⊆ s := @h

@[simp, grind =, push]
theorem mem_powerset_iff (x s : Set α) : x ∈ 𝒫 s ↔ x ⊆ s :=
  Iff.rfl

theorem powerset_inter (s t : Set α) : 𝒫 (s ∩ t) = 𝒫 s ∩ 𝒫 t :=
  ext fun _ => subset_inter_iff

@[simp]
theorem powerset_mono : 𝒫 s ⊆ 𝒫 t ↔ s ⊆ t :=
  ⟨fun h => @h _ (fun _ h => h), fun h _ hu _ ha => h (hu ha)⟩

theorem monotone_powerset : Monotone (powerset : Set α → Set (Set α)) := fun _ _ => powerset_mono.2

@[simp]
theorem powerset_nonempty : (𝒫 s).Nonempty :=
  ⟨∅, fun _ h => empty_subset s h⟩

@[simp]
theorem powerset_empty : 𝒫 (∅ : Set α) = {∅} :=
  ext fun _ => subset_empty_iff

@[simp]
theorem powerset_univ : 𝒫 (univ : Set α) = univ :=
  eq_univ_of_forall subset_univ

/-! ### Sets defined as an if-then-else -/

theorem mem_dite_univ_right (p : Prop) [Decidable p] (t : p → Set α) (x : α) :
    (x ∈ if h : p then t h else univ) ↔ ∀ h : p, x ∈ t h := by
  simp [mem_dite]

@[simp]
theorem mem_ite_univ_right (p : Prop) [Decidable p] (t : Set α) (x : α) :
    x ∈ ite p t Set.univ ↔ p → x ∈ t :=
  mem_dite_univ_right p (fun _ => t) x

theorem mem_dite_univ_left (p : Prop) [Decidable p] (t : ¬p → Set α) (x : α) :
    (x ∈ if h : p then univ else t h) ↔ ∀ h : ¬p, x ∈ t h := by
  split_ifs <;> simp_all

@[simp]
theorem mem_ite_univ_left (p : Prop) [Decidable p] (t : Set α) (x : α) :
    x ∈ ite p Set.univ t ↔ ¬p → x ∈ t :=
  mem_dite_univ_left p (fun _ => t) x

theorem mem_dite_empty_right (p : Prop) [Decidable p] (t : p → Set α) (x : α) :
    (x ∈ if h : p then t h else ∅) ↔ ∃ h : p, x ∈ t h := by
  simp only [mem_dite, mem_empty_iff_false, imp_false, not_not]
  exact ⟨fun h => ⟨h.2, h.1 h.2⟩, fun ⟨h₁, h₂⟩ => ⟨fun _ => h₂, h₁⟩⟩

@[simp]
theorem mem_ite_empty_right (p : Prop) [Decidable p] (t : Set α) (x : α) :
    x ∈ ite p t ∅ ↔ p ∧ x ∈ t :=
  (mem_dite_empty_right p (fun _ => t) x).trans (by simp)

theorem mem_dite_empty_left (p : Prop) [Decidable p] (t : ¬p → Set α) (x : α) :
    (x ∈ if h : p then ∅ else t h) ↔ ∃ h : ¬p, x ∈ t h := by
  simp only [mem_dite, mem_empty_iff_false, imp_false]
  exact ⟨fun h => ⟨h.1, h.2 h.1⟩, fun ⟨h₁, h₂⟩ => ⟨fun h => h₁ h, fun _ => h₂⟩⟩

@[simp]
theorem mem_ite_empty_left (p : Prop) [Decidable p] (t : Set α) (x : α) :
    x ∈ ite p ∅ t ↔ ¬p ∧ x ∈ t :=
  (mem_dite_empty_left p (fun _ => t) x).trans (by simp)

end Set

open Set

namespace Function

variable {α : Type*} {β : Type*}

theorem Injective.nonempty_apply_iff {f : Set α → Set β} (hf : Injective f) (h2 : f ∅ = ∅)
    {s : Set α} : (f s).Nonempty ↔ s.Nonempty := by
  rw [nonempty_iff_ne_empty, ← h2, nonempty_iff_ne_empty, hf.ne_iff]

end Function

namespace Subsingleton

variable {α : Type*} [Subsingleton α]

theorem eq_univ_of_nonempty {s : Set α} : s.Nonempty → s = univ := fun ⟨x, hx⟩ =>
  eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx

@[elab_as_elim]
theorem set_cases {p : Set α → Prop} (h0 : p ∅) (h1 : p univ) (s) : p s :=
  (s.eq_empty_or_nonempty.elim fun h => h.symm ▸ h0) fun h => (eq_univ_of_nonempty h).symm ▸ h1

theorem mem_iff_nonempty {α : Type*} [Subsingleton α] {s : Set α} {x : α} : x ∈ s ↔ s.Nonempty :=
  ⟨fun hx => ⟨x, hx⟩, fun ⟨y, hy⟩ => Subsingleton.elim y x ▸ hy⟩

end Subsingleton

/-! ### Decidability instances for sets -/

namespace Set

variable {α : Type u} (s t : Set α) (a b : α)

instance decidableSdiff [Decidable (a ∈ s)] [Decidable (a ∈ t)] : Decidable (a ∈ s \ t) :=
  inferInstanceAs (Decidable (a ∈ s ∧ a ∉ t))

instance decidableInter [Decidable (a ∈ s)] [Decidable (a ∈ t)] : Decidable (a ∈ s ∩ t) :=
  inferInstanceAs (Decidable (a ∈ s ∧ a ∈ t))

instance decidableUnion [Decidable (a ∈ s)] [Decidable (a ∈ t)] : Decidable (a ∈ s ∪ t) :=
  inferInstanceAs (Decidable (a ∈ s ∨ a ∈ t))

instance decidableCompl [Decidable (a ∈ s)] : Decidable (a ∈ sᶜ) :=
  inferInstanceAs (Decidable (a ∉ s))

instance decidableEmptyset : Decidable (a ∈ (∅ : Set α)) := Decidable.isFalse (by simp)

instance decidableUniv : Decidable (a ∈ univ) := Decidable.isTrue (by simp)

instance decidableInsert [Decidable (a = b)] [Decidable (a ∈ s)] : Decidable (a ∈ insert b s) :=
  inferInstanceAs (Decidable (_ ∨ _))

instance decidableSetOf (p : α → Prop) [Decidable (p a)] : Decidable (a ∈ { a | p a }) := by
  assumption

/-- `Set α` almost never has decidable equality.
In fact, for an inhabited type `α`, `Set α` has decidable equality iff
all propositions are decidable. We add a global instance that `Set α` has decidable equality,
coming from the choice axiom, so that we don't have to provide `[DecidableEq (Set α)]` arguments
in lemma statements. -/
noncomputable instance decidableEq : DecidableEq (Set α) := Classical.typeDecidableEq (Set α)

end Set

variable {α : Type*} {s t u : Set α}

namespace Equiv

/-- Given a predicate `p : α → Prop`, produces an equivalence between
  `Set {a : α // p a}` and `{s : Set α // ∀ a ∈ s, p a}`. -/
protected def setSubtypeComm (p : α → Prop) :
    Set {a : α // p a} ≃ {s : Set α // ∀ a ∈ s, p a} where
  toFun s := ⟨{a | ∃ h : p a, ⟨a, h⟩ ∈ s}, fun _ h ↦ h.1⟩
  invFun s := {a | a.val ∈ s.val}
  left_inv s := by ext a; exact ⟨fun h ↦ h.2, fun h ↦ ⟨a.property, h⟩⟩
  right_inv s := by ext; exact ⟨fun h ↦ h.2, fun h ↦ ⟨s.property _ h, h⟩⟩

@[simp]
protected lemma setSubtypeComm_apply (p : α → Prop) (s : Set {a // p a}) :
    (Equiv.setSubtypeComm p) s = ⟨{a | ∃ h : p a, ⟨a, h⟩ ∈ s}, fun _ h ↦ h.1⟩ :=
  rfl

@[simp]
protected lemma setSubtypeComm_symm_apply (p : α → Prop) (s : {s // ∀ a ∈ s, p a}) :
    (Equiv.setSubtypeComm p).symm s = {a | a.val ∈ s.val} :=
  rfl

theorem setSubtypeComm_apply_symm_apply (p : α → Prop) (s : {s : Set α // ∀ a ∈ s, p a}) :
    Equiv.setSubtypeComm p ((Equiv.setSubtypeComm p).symm s) = s :=
  Equiv.apply_symm_apply _ _

theorem setSubtypeComm_symm_apply_apply (p : α → Prop) (t : Set {a // p a}) :
    (Equiv.setSubtypeComm p).symm (Equiv.setSubtypeComm p t) = t :=
  Equiv.symm_apply_apply _ _

theorem setSubtypeComm_symm_apply_eq (p : α → Prop) (s : {s : Set α // ∀ a ∈ s, p a})
    (t : Set {a // p a}) :
    (Equiv.setSubtypeComm p).symm s = t ↔ s = Equiv.setSubtypeComm p t :=
  Equiv.symm_apply_eq _

theorem setSubtypeComm_eq_symm_apply (p : α → Prop) (s : {s : Set α // ∀ a ∈ s, p a})
    (t : Set {a // p a}) :
    t = (Equiv.setSubtypeComm p).symm s ↔ Equiv.setSubtypeComm p t = s :=
  Equiv.eq_symm_apply _

end Equiv
