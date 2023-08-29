/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import Mathlib.Order.SymmDiff
import Mathlib.Logic.Function.Iterate

#align_import data.set.basic from "leanprover-community/mathlib"@"48fb5b5280e7c81672afc9524185ae994553ebf4"

/-!
# Basic properties of sets

Sets in Lean are homogeneous; all their elements have the same type. Sets whose elements
have type `X` are thus defined as `Set X := X → Prop`. Note that this function need not
be decidable. The definition is in the core library.

This file provides some basic definitions related to sets and functions not present in the core
library, as well as extra lemmas for functions in the core library (empty set, univ, union,
intersection, insert, singleton, set-theoretic difference, complement, and powerset).

Note that a set is a term, not a type. There is a coercion from `Set α` to `Type*` sending
`s` to the corresponding subtype `↥s`.

See also the file `SetTheory/ZFC.lean`, which contains an encoding of ZFC set theory in Lean.

## Main definitions

Notation used here:

-  `f : α → β` is a function,

-  `s : Set α` and `s₁ s₂ : Set α` are subsets of `α`

-  `t : Set β` is a subset of `β`.

Definitions in the file:

* `Nonempty s : Prop` : the predicate `s ≠ ∅`. Note that this is the preferred way to express the
  fact that `s` has an element (see the Implementation Notes).

* `Subsingleton s : Prop` : the predicate saying that `s` has at most one element.

* `Nontrivial s : Prop` : the predicate saying that `s` has at least two distinct elements.

* `inclusion s₁ s₂ : ↥s₁ → ↥s₂` : the map `↥s₁ → ↥s₂` induced by an inclusion `s₁ ⊆ s₂`.

## Notation

* `sᶜ` for the complement of `s`

## Implementation notes

* `s.Nonempty` is to be preferred to `s ≠ ∅` or `∃ x, x ∈ s`. It has the advantage that
the `s.Nonempty` dot notation can be used.

* For `s : Set α`, do not use `Subtype s`. Instead use `↥s` or `(s : Type*)` or `s`.

## Tags

set, sets, subset, subsets, union, intersection, insert, singleton, complement, powerset

-/

-- https://github.com/leanprover/lean4/issues/2096
compile_def% Union.union
compile_def% Inter.inter
compile_def% SDiff.sdiff
compile_def% HasCompl.compl
compile_def% EmptyCollection.emptyCollection
compile_def% Insert.insert
compile_def% Singleton.singleton

/-! ### Set coercion to a type -/

open Function

universe u v w x

namespace Set

variable {α : Type _} {s t : Set α}

instance instBooleanAlgebraSet {α : Type _} : BooleanAlgebra (Set α) :=
  { (inferInstance : BooleanAlgebra (α → Prop)) with
    sup := (· ∪ ·),
    le := (· ≤ ·),
    lt := fun s t => s ⊆ t ∧ ¬t ⊆ s,
    inf := (· ∩ ·),
    bot := ∅,
    compl := fun s => { x | x ∉ s },
    top := univ,
    sdiff := fun s t => { x | x ∈ s ∧ x ∉ t } }

instance : HasSSubset (Set α) :=
  ⟨(· < ·)⟩

@[simp]
theorem top_eq_univ : (⊤ : Set α) = univ :=
  rfl
#align set.top_eq_univ Set.top_eq_univ

@[simp]
theorem bot_eq_empty : (⊥ : Set α) = ∅ :=
  rfl
#align set.bot_eq_empty Set.bot_eq_empty

@[simp]
theorem sup_eq_union : ((· ⊔ ·) : Set α → Set α → Set α) = (· ∪ ·) :=
  rfl
#align set.sup_eq_union Set.sup_eq_union

@[simp]
theorem inf_eq_inter : ((· ⊓ ·) : Set α → Set α → Set α) = (· ∩ ·) :=
  rfl
#align set.inf_eq_inter Set.inf_eq_inter

@[simp]
theorem le_eq_subset : ((· ≤ ·) : Set α → Set α → Prop) = (· ⊆ ·) :=
  rfl
#align set.le_eq_subset Set.le_eq_subset

@[simp]
theorem lt_eq_ssubset : ((· < ·) : Set α → Set α → Prop) = (· ⊂ ·) :=
  rfl
#align set.lt_eq_ssubset Set.lt_eq_ssubset

theorem le_iff_subset : s ≤ t ↔ s ⊆ t :=
  Iff.rfl
#align set.le_iff_subset Set.le_iff_subset

theorem lt_iff_ssubset : s < t ↔ s ⊂ t :=
  Iff.rfl
#align set.lt_iff_ssubset Set.lt_iff_ssubset

alias ⟨_root_.LE.le.subset, _root_.HasSubset.Subset.le⟩ := le_iff_subset
#align has_subset.subset.le HasSubset.Subset.le

alias ⟨_root_.LT.lt.ssubset, _root_.HasSSubset.SSubset.lt⟩ := lt_iff_ssubset
#align has_ssubset.ssubset.lt HasSSubset.SSubset.lt

-- Porting note: I've introduced this abbreviation, with the `@[coe]` attribute,
-- so that `norm_cast` has something to index on.
-- It is currently an abbreviation so that instance coming from `Subtype` are available.
-- If you're interested in making it a `def`, as it probably should be,
-- you'll then need to create additional instances (and possibly prove lemmas about them).
-- The first error should appear below at `monotoneOn_iff_monotone`.
/-- Given the set `s`, `Elem s` is the `Type` of element of `s`. -/
@[coe, reducible] def Elem (s : Set α) : Type u := { x // x ∈ s }

/-- Coercion from a set to the corresponding subtype. -/
instance {α : Type u} : CoeSort (Set α) (Type u) :=
  ⟨Elem⟩

instance PiSetCoe.canLift (ι : Type u) (α : ι → Type v) [∀ i, Nonempty (α i)] (s : Set ι) :
    CanLift (∀ i : s, α i) (∀ i, α i) (fun f i => f i) fun _ => True :=
  PiSubtype.canLift ι α s
#align set.pi_set_coe.can_lift Set.PiSetCoe.canLift

instance PiSetCoe.canLift' (ι : Type u) (α : Type v) [Nonempty α] (s : Set ι) :
    CanLift (s → α) (ι → α) (fun f i => f i) fun _ => True :=
  PiSetCoe.canLift ι (fun _ => α) s
#align set.pi_set_coe.can_lift' Set.PiSetCoe.canLift'

end Set

section SetCoe

variable {α : Type u}

instance (s : Set α) : CoeTC s α := ⟨fun x => x.1⟩

theorem Set.coe_eq_subtype (s : Set α) : ↥s = { x // x ∈ s } :=
  rfl
#align set.coe_eq_subtype Set.coe_eq_subtype

@[simp]
theorem Set.coe_setOf (p : α → Prop) : ↥{ x | p x } = { x // p x } :=
  rfl
#align set.coe_set_of Set.coe_setOf

-- Porting note: removed `simp` because `simp` can prove it
theorem SetCoe.forall {s : Set α} {p : s → Prop} : (∀ x : s, p x) ↔ ∀ (x) (h : x ∈ s), p ⟨x, h⟩ :=
  Subtype.forall
#align set_coe.forall SetCoe.forall

-- Porting note: removed `simp` because `simp` can prove it
theorem SetCoe.exists {s : Set α} {p : s → Prop} :
    (∃ x : s, p x) ↔ ∃ (x : _) (h : x ∈ s), p ⟨x, h⟩ :=
  Subtype.exists
#align set_coe.exists SetCoe.exists

theorem SetCoe.exists' {s : Set α} {p : ∀ x, x ∈ s → Prop} :
    (∃ (x : _) (h : x ∈ s), p x h) ↔ ∃ x : s, p x.1 x.2 :=
  (@SetCoe.exists _ _ fun x => p x.1 x.2).symm
#align set_coe.exists' SetCoe.exists'

theorem SetCoe.forall' {s : Set α} {p : ∀ x, x ∈ s → Prop} :
    (∀ (x) (h : x ∈ s), p x h) ↔ ∀ x : s, p x.1 x.2 :=
  (@SetCoe.forall _ _ fun x => p x.1 x.2).symm
#align set_coe.forall' SetCoe.forall'

@[simp]
theorem set_coe_cast :
    ∀ {s t : Set α} (H' : s = t) (H : ↥s = ↥t) (x : s), cast H x = ⟨x.1, H' ▸ x.2⟩
  | _, _, rfl, _, _ => rfl
#align set_coe_cast set_coe_cast

theorem SetCoe.ext {s : Set α} {a b : s} : (a : α) = b → a = b :=
  Subtype.eq
#align set_coe.ext SetCoe.ext

theorem SetCoe.ext_iff {s : Set α} {a b : s} : (↑a : α) = ↑b ↔ a = b :=
  Iff.intro SetCoe.ext fun h => h ▸ rfl
#align set_coe.ext_iff SetCoe.ext_iff

end SetCoe

/-- See also `Subtype.prop` -/
theorem Subtype.mem {α : Type*} {s : Set α} (p : s) : (p : α) ∈ s :=
  p.prop
#align subtype.mem Subtype.mem

/-- Duplicate of `Eq.subset'`, which currently has elaboration problems. -/
theorem Eq.subset {α} {s t : Set α} : s = t → s ⊆ t :=
  fun h₁ _ h₂ => by rw [← h₁]; exact h₂
                    -- ⊢ x✝ ∈ s
                               -- 🎉 no goals
#align eq.subset Eq.subset

namespace Set

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x} {a b : α} {s s₁ s₂ t t₁ t₂ u : Set α}

instance : Inhabited (Set α) :=
  ⟨∅⟩

attribute [ext] Set.ext
#align set.ext Set.ext

theorem ext_iff {s t : Set α} : s = t ↔ ∀ x, x ∈ s ↔ x ∈ t :=
  ⟨fun h x => by rw [h], ext⟩
                 -- 🎉 no goals
#align set.ext_iff Set.ext_iff

@[trans]
theorem mem_of_mem_of_subset {x : α} {s t : Set α} (hx : x ∈ s) (h : s ⊆ t) : x ∈ t :=
  h hx
#align set.mem_of_mem_of_subset Set.mem_of_mem_of_subset

theorem forall_in_swap {p : α → β → Prop} : (∀ a ∈ s, ∀ (b), p a b) ↔ ∀ (b), ∀ a ∈ s, p a b := by
  tauto
  -- 🎉 no goals
#align set.forall_in_swap Set.forall_in_swap

/-! ### Lemmas about `mem` and `setOf` -/

@[simp, mfld_simps] theorem mem_setOf_eq {x : α} {p : α → Prop} : (x ∈ {y | p y}) = p x := rfl
#align set.mem_set_of_eq Set.mem_setOf_eq

theorem mem_setOf {a : α} {p : α → Prop} : a ∈ { x | p x } ↔ p a :=
  Iff.rfl
#align set.mem_set_of Set.mem_setOf

/-- If `h : a ∈ {x | p x}` then `h.out : p x`. These are definitionally equal, but this can
nevertheless be useful for various reasons, e.g. to apply further projection notation or in an
argument to `simp`. -/
theorem _root_.Membership.mem.out {p : α → Prop} {a : α} (h : a ∈ { x | p x }) : p a :=
  h
#align has_mem.mem.out Membership.mem.out

theorem nmem_setOf_iff {a : α} {p : α → Prop} : a ∉ { x | p x } ↔ ¬p a :=
  Iff.rfl
#align set.nmem_set_of_iff Set.nmem_setOf_iff

@[simp]
theorem setOf_mem_eq {s : Set α} : { x | x ∈ s } = s :=
  rfl
#align set.set_of_mem_eq Set.setOf_mem_eq

theorem setOf_set {s : Set α} : setOf s = s :=
  rfl
#align set.set_of_set Set.setOf_set

theorem setOf_app_iff {p : α → Prop} {x : α} : { x | p x } x ↔ p x :=
  Iff.rfl
#align set.set_of_app_iff Set.setOf_app_iff

theorem mem_def {a : α} {s : Set α} : a ∈ s ↔ s a :=
  Iff.rfl
#align set.mem_def Set.mem_def

theorem setOf_bijective : Bijective (setOf : (α → Prop) → Set α) :=
  bijective_id
#align set.set_of_bijective Set.setOf_bijective

@[simp]
theorem setOf_subset_setOf {p q : α → Prop} : { a | p a } ⊆ { a | q a } ↔ ∀ a, p a → q a :=
  Iff.rfl
#align set.set_of_subset_set_of Set.setOf_subset_setOf

theorem setOf_and {p q : α → Prop} : { a | p a ∧ q a } = { a | p a } ∩ { a | q a } :=
  rfl
#align set.set_of_and Set.setOf_and

theorem setOf_or {p q : α → Prop} : { a | p a ∨ q a } = { a | p a } ∪ { a | q a } :=
  rfl
#align set.set_of_or Set.setOf_or

/-! ### Subset and strict subset relations -/


instance : IsRefl (Set α) (· ⊆ ·) :=
  show IsRefl (Set α) (· ≤ ·) by infer_instance
                                 -- 🎉 no goals

instance : IsTrans (Set α) (· ⊆ ·) :=
  show IsTrans (Set α) (· ≤ ·) by infer_instance
                                  -- 🎉 no goals

instance : Trans ((· ⊆ ·) : Set α → Set α → Prop) (· ⊆ ·) (· ⊆ ·) :=
  show Trans (· ≤ ·) (· ≤ ·) (· ≤ ·) by infer_instance
                                        -- 🎉 no goals

instance : IsAntisymm (Set α) (· ⊆ ·) :=
  show IsAntisymm (Set α) (· ≤ ·) by infer_instance
                                     -- 🎉 no goals

instance : IsIrrefl (Set α) (· ⊂ ·) :=
  show IsIrrefl (Set α) (· < ·) by infer_instance
                                   -- 🎉 no goals

instance : IsTrans (Set α) (· ⊂ ·) :=
  show IsTrans (Set α) (· < ·) by infer_instance
                                  -- 🎉 no goals

instance : Trans ((· ⊂ ·) : Set α → Set α → Prop) (· ⊂ ·) (· ⊂ ·) :=
  show Trans (· < ·) (· < ·) (· < ·) by infer_instance
                                        -- 🎉 no goals

instance : Trans ((· ⊂ ·) : Set α → Set α → Prop) (· ⊆ ·) (· ⊂ ·) :=
  show Trans (· < ·) (· ≤ ·) (· < ·) by infer_instance
                                        -- 🎉 no goals

instance : Trans ((· ⊆ ·) : Set α → Set α → Prop) (· ⊂ ·) (· ⊂ ·) :=
  show Trans (· ≤ ·) (· < ·) (· < ·) by infer_instance
                                        -- 🎉 no goals

instance : IsAsymm (Set α) (· ⊂ ·) :=
  show IsAsymm (Set α) (· < ·) by infer_instance
                                  -- 🎉 no goals

instance : IsNonstrictStrictOrder (Set α) (· ⊆ ·) (· ⊂ ·) :=
  ⟨fun _ _ => Iff.rfl⟩

-- TODO(Jeremy): write a tactic to unfold specific instances of generic notation?
theorem subset_def : (s ⊆ t) = ∀ x, x ∈ s → x ∈ t :=
  rfl
#align set.subset_def Set.subset_def

theorem ssubset_def : (s ⊂ t) = (s ⊆ t ∧ ¬t ⊆ s) :=
  rfl
#align set.ssubset_def Set.ssubset_def

@[refl]
theorem Subset.refl (a : Set α) : a ⊆ a := fun _ => id
#align set.subset.refl Set.Subset.refl

theorem Subset.rfl {s : Set α} : s ⊆ s :=
  Subset.refl s
#align set.subset.rfl Set.Subset.rfl

@[trans]
theorem Subset.trans {a b c : Set α} (ab : a ⊆ b) (bc : b ⊆ c) : a ⊆ c := fun _ h => bc <| ab h
#align set.subset.trans Set.Subset.trans

@[trans]
theorem mem_of_eq_of_mem {x y : α} {s : Set α} (hx : x = y) (h : y ∈ s) : x ∈ s :=
  hx.symm ▸ h
#align set.mem_of_eq_of_mem Set.mem_of_eq_of_mem

theorem Subset.antisymm {a b : Set α} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b :=
  Set.ext fun _ => ⟨@h₁ _, @h₂ _⟩
#align set.subset.antisymm Set.Subset.antisymm

theorem Subset.antisymm_iff {a b : Set α} : a = b ↔ a ⊆ b ∧ b ⊆ a :=
  ⟨fun e => ⟨e.subset, e.symm.subset⟩, fun ⟨h₁, h₂⟩ => Subset.antisymm h₁ h₂⟩
#align set.subset.antisymm_iff Set.Subset.antisymm_iff

-- an alternative name
theorem eq_of_subset_of_subset {a b : Set α} : a ⊆ b → b ⊆ a → a = b :=
  Subset.antisymm
#align set.eq_of_subset_of_subset Set.eq_of_subset_of_subset

theorem mem_of_subset_of_mem {s₁ s₂ : Set α} {a : α} (h : s₁ ⊆ s₂) : a ∈ s₁ → a ∈ s₂ :=
  @h _
#align set.mem_of_subset_of_mem Set.mem_of_subset_of_mem

theorem not_mem_subset (h : s ⊆ t) : a ∉ t → a ∉ s :=
  mt <| mem_of_subset_of_mem h
#align set.not_mem_subset Set.not_mem_subset

theorem not_subset : ¬s ⊆ t ↔ ∃ a ∈ s, a ∉ t := by
  simp only [subset_def, not_forall, exists_prop]
  -- 🎉 no goals
#align set.not_subset Set.not_subset

/-! ### Definition of strict subsets `s ⊂ t` and basic properties. -/


protected theorem eq_or_ssubset_of_subset (h : s ⊆ t) : s = t ∨ s ⊂ t :=
  eq_or_lt_of_le h
#align set.eq_or_ssubset_of_subset Set.eq_or_ssubset_of_subset

theorem exists_of_ssubset {s t : Set α} (h : s ⊂ t) : ∃ x ∈ t, x ∉ s :=
  not_subset.1 h.2
#align set.exists_of_ssubset Set.exists_of_ssubset

protected theorem ssubset_iff_subset_ne {s t : Set α} : s ⊂ t ↔ s ⊆ t ∧ s ≠ t :=
  @lt_iff_le_and_ne (Set α) _ s t
#align set.ssubset_iff_subset_ne Set.ssubset_iff_subset_ne

theorem ssubset_iff_of_subset {s t : Set α} (h : s ⊆ t) : s ⊂ t ↔ ∃ x ∈ t, x ∉ s :=
  ⟨exists_of_ssubset, fun ⟨_, hxt, hxs⟩ => ⟨h, fun h => hxs <| h hxt⟩⟩
#align set.ssubset_iff_of_subset Set.ssubset_iff_of_subset

protected theorem ssubset_of_ssubset_of_subset {s₁ s₂ s₃ : Set α} (hs₁s₂ : s₁ ⊂ s₂)
    (hs₂s₃ : s₂ ⊆ s₃) : s₁ ⊂ s₃ :=
  ⟨Subset.trans hs₁s₂.1 hs₂s₃, fun hs₃s₁ => hs₁s₂.2 (Subset.trans hs₂s₃ hs₃s₁)⟩
#align set.ssubset_of_ssubset_of_subset Set.ssubset_of_ssubset_of_subset

protected theorem ssubset_of_subset_of_ssubset {s₁ s₂ s₃ : Set α} (hs₁s₂ : s₁ ⊆ s₂)
    (hs₂s₃ : s₂ ⊂ s₃) : s₁ ⊂ s₃ :=
  ⟨Subset.trans hs₁s₂ hs₂s₃.1, fun hs₃s₁ => hs₂s₃.2 (Subset.trans hs₃s₁ hs₁s₂)⟩
#align set.ssubset_of_subset_of_ssubset Set.ssubset_of_subset_of_ssubset

theorem not_mem_empty (x : α) : ¬x ∈ (∅ : Set α) :=
  id
#align set.not_mem_empty Set.not_mem_empty

-- Porting note: removed `simp` because `simp` can prove it
theorem not_not_mem : ¬a ∉ s ↔ a ∈ s :=
  not_not
#align set.not_not_mem Set.not_not_mem

/-! ### Non-empty sets -/


/-- The property `s.Nonempty` expresses the fact that the set `s` is not empty. It should be used
in theorem assumptions instead of `∃ x, x ∈ s` or `s ≠ ∅` as it gives access to a nice API thanks
to the dot notation. -/
protected def Nonempty (s : Set α) : Prop :=
  ∃ x, x ∈ s
#align set.nonempty Set.Nonempty

-- Porting note: we seem to need parentheses at `(↥s)`,
-- even if we increase the right precedence of `↥` in `Mathlib.Tactic.Coe`.
-- Porting note: removed `simp` as it is competing with `nonempty_subtype`.
-- @[simp]
theorem nonempty_coe_sort {s : Set α} : Nonempty (↥s) ↔ s.Nonempty :=
  nonempty_subtype
#align set.nonempty_coe_sort Set.nonempty_coe_sort

alias ⟨_, Nonempty.coe_sort⟩ := nonempty_coe_sort
#align set.nonempty.coe_sort Set.Nonempty.coe_sort

theorem nonempty_def : s.Nonempty ↔ ∃ x, x ∈ s :=
  Iff.rfl
#align set.nonempty_def Set.nonempty_def

theorem nonempty_of_mem {x} (h : x ∈ s) : s.Nonempty :=
  ⟨x, h⟩
#align set.nonempty_of_mem Set.nonempty_of_mem

theorem Nonempty.not_subset_empty : s.Nonempty → ¬s ⊆ ∅
  | ⟨_, hx⟩, hs => hs hx
#align set.nonempty.not_subset_empty Set.Nonempty.not_subset_empty

/-- Extract a witness from `s.Nonempty`. This function might be used instead of case analysis
on the argument. Note that it makes a proof depend on the `Classical.choice` axiom. -/
protected noncomputable def Nonempty.some (h : s.Nonempty) : α :=
  Classical.choose h
#align set.nonempty.some Set.Nonempty.some

protected theorem Nonempty.some_mem (h : s.Nonempty) : h.some ∈ s :=
  Classical.choose_spec h
#align set.nonempty.some_mem Set.Nonempty.some_mem

theorem Nonempty.mono (ht : s ⊆ t) (hs : s.Nonempty) : t.Nonempty :=
  hs.imp ht
#align set.nonempty.mono Set.Nonempty.mono

theorem nonempty_of_not_subset (h : ¬s ⊆ t) : (s \ t).Nonempty :=
  let ⟨x, xs, xt⟩ := not_subset.1 h
  ⟨x, xs, xt⟩
#align set.nonempty_of_not_subset Set.nonempty_of_not_subset

theorem nonempty_of_ssubset (ht : s ⊂ t) : (t \ s).Nonempty :=
  nonempty_of_not_subset ht.2
#align set.nonempty_of_ssubset Set.nonempty_of_ssubset

theorem Nonempty.of_diff (h : (s \ t).Nonempty) : s.Nonempty :=
  h.imp fun _ => And.left
#align set.nonempty.of_diff Set.Nonempty.of_diff

theorem nonempty_of_ssubset' (ht : s ⊂ t) : t.Nonempty :=
  (nonempty_of_ssubset ht).of_diff
#align set.nonempty_of_ssubset' Set.nonempty_of_ssubset'

theorem Nonempty.inl (hs : s.Nonempty) : (s ∪ t).Nonempty :=
  hs.imp fun _ => Or.inl
#align set.nonempty.inl Set.Nonempty.inl

theorem Nonempty.inr (ht : t.Nonempty) : (s ∪ t).Nonempty :=
  ht.imp fun _ => Or.inr
#align set.nonempty.inr Set.Nonempty.inr

@[simp]
theorem union_nonempty : (s ∪ t).Nonempty ↔ s.Nonempty ∨ t.Nonempty :=
  exists_or
#align set.union_nonempty Set.union_nonempty

theorem Nonempty.left (h : (s ∩ t).Nonempty) : s.Nonempty :=
  h.imp fun _ => And.left
#align set.nonempty.left Set.Nonempty.left

theorem Nonempty.right (h : (s ∩ t).Nonempty) : t.Nonempty :=
  h.imp fun _ => And.right
#align set.nonempty.right Set.Nonempty.right

theorem inter_nonempty : (s ∩ t).Nonempty ↔ ∃ x, x ∈ s ∧ x ∈ t :=
  Iff.rfl
#align set.inter_nonempty Set.inter_nonempty

theorem inter_nonempty_iff_exists_left : (s ∩ t).Nonempty ↔ ∃ x ∈ s, x ∈ t := by
  simp_rw [inter_nonempty]
  -- 🎉 no goals
#align set.inter_nonempty_iff_exists_left Set.inter_nonempty_iff_exists_left

theorem inter_nonempty_iff_exists_right : (s ∩ t).Nonempty ↔ ∃ x ∈ t, x ∈ s := by
  simp_rw [inter_nonempty, and_comm]
  -- 🎉 no goals
#align set.inter_nonempty_iff_exists_right Set.inter_nonempty_iff_exists_right

theorem nonempty_iff_univ_nonempty : Nonempty α ↔ (univ : Set α).Nonempty :=
  ⟨fun ⟨x⟩ => ⟨x, trivial⟩, fun ⟨x, _⟩ => ⟨x⟩⟩
#align set.nonempty_iff_univ_nonempty Set.nonempty_iff_univ_nonempty

@[simp]
theorem univ_nonempty : ∀ [Nonempty α], (univ : Set α).Nonempty
  | ⟨x⟩ => ⟨x, trivial⟩
#align set.univ_nonempty Set.univ_nonempty

theorem Nonempty.to_subtype : s.Nonempty → Nonempty (↥s) :=
  nonempty_subtype.2
#align set.nonempty.to_subtype Set.Nonempty.to_subtype

theorem Nonempty.to_type : s.Nonempty → Nonempty α := fun ⟨x, _⟩ => ⟨x⟩
#align set.nonempty.to_type Set.Nonempty.to_type

instance univ.nonempty [Nonempty α] : Nonempty (↥(Set.univ : Set α)) :=
  Set.univ_nonempty.to_subtype
#align set.univ.nonempty Set.univ.nonempty

theorem nonempty_of_nonempty_subtype [Nonempty (↥s)] : s.Nonempty :=
  nonempty_subtype.mp ‹_›
#align set.nonempty_of_nonempty_subtype Set.nonempty_of_nonempty_subtype

/-! ### Lemmas about the empty set -/


theorem empty_def : (↥(∅ : Set α)) = { _x : α | False } :=
  rfl
#align set.empty_def Set.empty_def

@[simp]
theorem mem_empty_iff_false (x : α) : x ∈ (∅ : Set α) ↔ False :=
  Iff.rfl
#align set.mem_empty_iff_false Set.mem_empty_iff_false

@[simp]
theorem setOf_false : { _a : α | False } = ∅ :=
  rfl
#align set.set_of_false Set.setOf_false

@[simp]
theorem empty_subset (s : Set α) : ∅ ⊆ s :=
  fun.
#align set.empty_subset Set.empty_subset

theorem subset_empty_iff {s : Set α} : s ⊆ ∅ ↔ s = ∅ :=
  (Subset.antisymm_iff.trans <| and_iff_left (empty_subset _)).symm
#align set.subset_empty_iff Set.subset_empty_iff

theorem eq_empty_iff_forall_not_mem {s : Set α} : s = ∅ ↔ ∀ x, x ∉ s :=
  subset_empty_iff.symm
#align set.eq_empty_iff_forall_not_mem Set.eq_empty_iff_forall_not_mem

theorem eq_empty_of_forall_not_mem (h : ∀ x, x ∉ s) : s = ∅ :=
  subset_empty_iff.1 h
#align set.eq_empty_of_forall_not_mem Set.eq_empty_of_forall_not_mem

theorem eq_empty_of_subset_empty {s : Set α} : s ⊆ ∅ → s = ∅ :=
  subset_empty_iff.1
#align set.eq_empty_of_subset_empty Set.eq_empty_of_subset_empty

theorem eq_empty_of_isEmpty [IsEmpty α] (s : Set α) : s = ∅ :=
  eq_empty_of_subset_empty fun x _ => isEmptyElim x
#align set.eq_empty_of_is_empty Set.eq_empty_of_isEmpty

/-- There is exactly one set of a type that is empty. -/
instance uniqueEmpty [IsEmpty α] : Unique (Set α) where
  default := ∅
  uniq := eq_empty_of_isEmpty
#align set.unique_empty Set.uniqueEmpty

/-- See also `Set.nonempty_iff_ne_empty`. -/
theorem not_nonempty_iff_eq_empty {s : Set α} : ¬s.Nonempty ↔ s = ∅ := by
  simp only [Set.Nonempty, not_exists, eq_empty_iff_forall_not_mem]
  -- 🎉 no goals
#align set.not_nonempty_iff_eq_empty Set.not_nonempty_iff_eq_empty

/-- See also `Set.not_nonempty_iff_eq_empty`. -/
theorem nonempty_iff_ne_empty : s.Nonempty ↔ s ≠ ∅ :=
  not_nonempty_iff_eq_empty.not_right
#align set.nonempty_iff_ne_empty Set.nonempty_iff_ne_empty

/-- See also `nonempty_iff_ne_empty'`. -/
theorem not_nonempty_iff_eq_empty' : ¬Nonempty s ↔ s = ∅ := by
  rw [nonempty_subtype, not_exists, eq_empty_iff_forall_not_mem]
  -- 🎉 no goals

/-- See also `not_nonempty_iff_eq_empty'`. -/
theorem nonempty_iff_ne_empty' : Nonempty s ↔ s ≠ ∅ :=
  not_nonempty_iff_eq_empty'.not_right

alias ⟨Nonempty.ne_empty, _⟩ := nonempty_iff_ne_empty
#align set.nonempty.ne_empty Set.Nonempty.ne_empty

@[simp]
theorem not_nonempty_empty : ¬(∅ : Set α).Nonempty := fun ⟨_, hx⟩ => hx
#align set.not_nonempty_empty Set.not_nonempty_empty

-- Porting note: removing `@[simp]` as it is competing with `isEmpty_subtype`.
-- @[simp]
theorem isEmpty_coe_sort {s : Set α} : IsEmpty (↥s) ↔ s = ∅ :=
  not_iff_not.1 <| by simpa using nonempty_iff_ne_empty
                      -- 🎉 no goals
#align set.is_empty_coe_sort Set.isEmpty_coe_sort

theorem eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.Nonempty :=
  or_iff_not_imp_left.2 nonempty_iff_ne_empty.2
#align set.eq_empty_or_nonempty Set.eq_empty_or_nonempty

theorem subset_eq_empty {s t : Set α} (h : t ⊆ s) (e : s = ∅) : t = ∅ :=
  subset_empty_iff.1 <| e ▸ h
#align set.subset_eq_empty Set.subset_eq_empty

theorem ball_empty_iff {p : α → Prop} : (∀ x ∈ (∅ : Set α), p x) ↔ True :=
  iff_true_intro fun _ => False.elim
#align set.ball_empty_iff Set.ball_empty_iff

instance (α : Type u) : IsEmpty.{u + 1} (↥(∅ : Set α)) :=
  ⟨fun x => x.2⟩

@[simp]
theorem empty_ssubset : ∅ ⊂ s ↔ s.Nonempty :=
  (@bot_lt_iff_ne_bot (Set α) _ _ _).trans nonempty_iff_ne_empty.symm
#align set.empty_ssubset Set.empty_ssubset

alias ⟨_, Nonempty.empty_ssubset⟩ := empty_ssubset
#align set.nonempty.empty_ssubset Set.Nonempty.empty_ssubset

/-!

### Universal set.

In Lean `@univ α` (or `univ : Set α`) is the set that contains all elements of type `α`.
Mathematically it is the same as `α` but it has a different type.

-/


@[simp]
theorem setOf_true : { _x : α | True } = univ :=
  rfl
#align set.set_of_true Set.setOf_true

@[simp, mfld_simps]
theorem mem_univ (x : α) : x ∈ @univ α :=
  trivial
#align set.mem_univ Set.mem_univ

@[simp]
theorem univ_eq_empty_iff : (univ : Set α) = ∅ ↔ IsEmpty α :=
  eq_empty_iff_forall_not_mem.trans
    ⟨fun H => ⟨fun x => H x trivial⟩, fun H x _ => @IsEmpty.false α H x⟩
#align set.univ_eq_empty_iff Set.univ_eq_empty_iff

theorem empty_ne_univ [Nonempty α] : (∅ : Set α) ≠ univ := fun e =>
  not_isEmpty_of_nonempty α <| univ_eq_empty_iff.1 e.symm
#align set.empty_ne_univ Set.empty_ne_univ

@[simp]
theorem subset_univ (s : Set α) : s ⊆ univ := fun _ _ => trivial
#align set.subset_univ Set.subset_univ

theorem univ_subset_iff {s : Set α} : univ ⊆ s ↔ s = univ :=
  @top_le_iff _ _ _ s
#align set.univ_subset_iff Set.univ_subset_iff

alias ⟨eq_univ_of_univ_subset, _⟩ := univ_subset_iff
#align set.eq_univ_of_univ_subset Set.eq_univ_of_univ_subset

theorem eq_univ_iff_forall {s : Set α} : s = univ ↔ ∀ x, x ∈ s :=
  univ_subset_iff.symm.trans <| forall_congr' fun _ => imp_iff_right trivial
#align set.eq_univ_iff_forall Set.eq_univ_iff_forall

theorem eq_univ_of_forall {s : Set α} : (∀ x, x ∈ s) → s = univ :=
  eq_univ_iff_forall.2
#align set.eq_univ_of_forall Set.eq_univ_of_forall

theorem Nonempty.eq_univ [Subsingleton α] : s.Nonempty → s = univ := by
  rintro ⟨x, hx⟩
  -- ⊢ s = univ
  refine' eq_univ_of_forall fun y => by rwa [Subsingleton.elim y x]
  -- 🎉 no goals
#align set.nonempty.eq_univ Set.Nonempty.eq_univ

theorem eq_univ_of_subset {s t : Set α} (h : s ⊆ t) (hs : s = univ) : t = univ :=
  eq_univ_of_univ_subset <| (hs ▸ h : univ ⊆ t)
#align set.eq_univ_of_subset Set.eq_univ_of_subset

theorem exists_mem_of_nonempty (α) : ∀ [Nonempty α], ∃ x : α, x ∈ (univ : Set α)
  | ⟨x⟩ => ⟨x, trivial⟩
#align set.exists_mem_of_nonempty Set.exists_mem_of_nonempty

theorem ne_univ_iff_exists_not_mem {α : Type*} (s : Set α) : s ≠ univ ↔ ∃ a, a ∉ s := by
  rw [← not_forall, ← eq_univ_iff_forall]
  -- 🎉 no goals
#align set.ne_univ_iff_exists_not_mem Set.ne_univ_iff_exists_not_mem

theorem not_subset_iff_exists_mem_not_mem {α : Type*} {s t : Set α} :
    ¬s ⊆ t ↔ ∃ x, x ∈ s ∧ x ∉ t := by simp [subset_def]
                                      -- 🎉 no goals
#align set.not_subset_iff_exists_mem_not_mem Set.not_subset_iff_exists_mem_not_mem

theorem univ_unique [Unique α] : @Set.univ α = {default} :=
  Set.ext fun x => iff_of_true trivial <| Subsingleton.elim x default
#align set.univ_unique Set.univ_unique

theorem ssubset_univ_iff : s ⊂ univ ↔ s ≠ univ :=
  lt_top_iff_ne_top
#align set.ssubset_univ_iff Set.ssubset_univ_iff

instance nontrivial_of_nonempty [Nonempty α] : Nontrivial (Set α) :=
  ⟨⟨∅, univ, empty_ne_univ⟩⟩
#align set.nontrivial_of_nonempty Set.nontrivial_of_nonempty

/-! ### Lemmas about union -/


theorem union_def {s₁ s₂ : Set α} : s₁ ∪ s₂ = { a | a ∈ s₁ ∨ a ∈ s₂ } :=
  rfl
#align set.union_def Set.union_def

theorem mem_union_left {x : α} {a : Set α} (b : Set α) : x ∈ a → x ∈ a ∪ b :=
  Or.inl
#align set.mem_union_left Set.mem_union_left

theorem mem_union_right {x : α} {b : Set α} (a : Set α) : x ∈ b → x ∈ a ∪ b :=
  Or.inr
#align set.mem_union_right Set.mem_union_right

theorem mem_or_mem_of_mem_union {x : α} {a b : Set α} (H : x ∈ a ∪ b) : x ∈ a ∨ x ∈ b :=
  H
#align set.mem_or_mem_of_mem_union Set.mem_or_mem_of_mem_union

theorem MemUnion.elim {x : α} {a b : Set α} {P : Prop} (H₁ : x ∈ a ∪ b) (H₂ : x ∈ a → P)
    (H₃ : x ∈ b → P) : P :=
  Or.elim H₁ H₂ H₃
#align set.mem_union.elim Set.MemUnion.elim

@[simp]
theorem mem_union (x : α) (a b : Set α) : x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b :=
  Iff.rfl
#align set.mem_union Set.mem_union

@[simp]
theorem union_self (a : Set α) : a ∪ a = a :=
  ext fun _ => or_self_iff _
#align set.union_self Set.union_self

@[simp]
theorem union_empty (a : Set α) : a ∪ ∅ = a :=
  ext fun _ => or_false_iff _
#align set.union_empty Set.union_empty

@[simp]
theorem empty_union (a : Set α) : ∅ ∪ a = a :=
  ext fun _ => false_or_iff _
#align set.empty_union Set.empty_union

theorem union_comm (a b : Set α) : a ∪ b = b ∪ a :=
  ext fun _ => or_comm
#align set.union_comm Set.union_comm

theorem union_assoc (a b c : Set α) : a ∪ b ∪ c = a ∪ (b ∪ c) :=
  ext fun _ => or_assoc
#align set.union_assoc Set.union_assoc

instance union_isAssoc : IsAssociative (Set α) (· ∪ ·) :=
  ⟨union_assoc⟩
#align set.union_is_assoc Set.union_isAssoc

instance union_isComm : IsCommutative (Set α) (· ∪ ·) :=
  ⟨union_comm⟩
#align set.union_is_comm Set.union_isComm

theorem union_left_comm (s₁ s₂ s₃ : Set α) : s₁ ∪ (s₂ ∪ s₃) = s₂ ∪ (s₁ ∪ s₃) :=
  ext fun _ => or_left_comm
#align set.union_left_comm Set.union_left_comm

theorem union_right_comm (s₁ s₂ s₃ : Set α) : s₁ ∪ s₂ ∪ s₃ = s₁ ∪ s₃ ∪ s₂ :=
  ext fun _ => or_right_comm
#align set.union_right_comm Set.union_right_comm

@[simp]
theorem union_eq_left_iff_subset {s t : Set α} : s ∪ t = s ↔ t ⊆ s :=
  sup_eq_left
#align set.union_eq_left_iff_subset Set.union_eq_left_iff_subset

@[simp]
theorem union_eq_right_iff_subset {s t : Set α} : s ∪ t = t ↔ s ⊆ t :=
  sup_eq_right
#align set.union_eq_right_iff_subset Set.union_eq_right_iff_subset

theorem union_eq_self_of_subset_left {s t : Set α} (h : s ⊆ t) : s ∪ t = t :=
  union_eq_right_iff_subset.mpr h
#align set.union_eq_self_of_subset_left Set.union_eq_self_of_subset_left

theorem union_eq_self_of_subset_right {s t : Set α} (h : t ⊆ s) : s ∪ t = s :=
  union_eq_left_iff_subset.mpr h
#align set.union_eq_self_of_subset_right Set.union_eq_self_of_subset_right

@[simp]
theorem subset_union_left (s t : Set α) : s ⊆ s ∪ t := fun _ => Or.inl
#align set.subset_union_left Set.subset_union_left

@[simp]
theorem subset_union_right (s t : Set α) : t ⊆ s ∪ t := fun _ => Or.inr
#align set.subset_union_right Set.subset_union_right

theorem union_subset {s t r : Set α} (sr : s ⊆ r) (tr : t ⊆ r) : s ∪ t ⊆ r := fun _ =>
  Or.rec (@sr _) (@tr _)
#align set.union_subset Set.union_subset

@[simp]
theorem union_subset_iff {s t u : Set α} : s ∪ t ⊆ u ↔ s ⊆ u ∧ t ⊆ u :=
  (forall_congr' fun _ => or_imp).trans forall_and
#align set.union_subset_iff Set.union_subset_iff

@[gcongr]
theorem union_subset_union {s₁ s₂ t₁ t₂ : Set α} (h₁ : s₁ ⊆ s₂) (h₂ : t₁ ⊆ t₂) :
    s₁ ∪ t₁ ⊆ s₂ ∪ t₂ := fun _ => Or.imp (@h₁ _) (@h₂ _)
#align set.union_subset_union Set.union_subset_union

@[gcongr]
theorem union_subset_union_left {s₁ s₂ : Set α} (t) (h : s₁ ⊆ s₂) : s₁ ∪ t ⊆ s₂ ∪ t :=
  union_subset_union h Subset.rfl
#align set.union_subset_union_left Set.union_subset_union_left

@[gcongr]
theorem union_subset_union_right (s) {t₁ t₂ : Set α} (h : t₁ ⊆ t₂) : s ∪ t₁ ⊆ s ∪ t₂ :=
  union_subset_union Subset.rfl h
#align set.union_subset_union_right Set.union_subset_union_right

theorem subset_union_of_subset_left {s t : Set α} (h : s ⊆ t) (u : Set α) : s ⊆ t ∪ u :=
  Subset.trans h (subset_union_left t u)
#align set.subset_union_of_subset_left Set.subset_union_of_subset_left

theorem subset_union_of_subset_right {s u : Set α} (h : s ⊆ u) (t : Set α) : s ⊆ t ∪ u :=
  Subset.trans h (subset_union_right t u)
#align set.subset_union_of_subset_right Set.subset_union_of_subset_right

-- Porting note: replaced `⊔` in RHS
theorem union_congr_left (ht : t ⊆ s ∪ u) (hu : u ⊆ s ∪ t) : s ∪ t = s ∪ u :=
  sup_congr_left ht hu
#align set.union_congr_left Set.union_congr_left

theorem union_congr_right (hs : s ⊆ t ∪ u) (ht : t ⊆ s ∪ u) : s ∪ u = t ∪ u :=
  sup_congr_right hs ht
#align set.union_congr_right Set.union_congr_right

theorem union_eq_union_iff_left : s ∪ t = s ∪ u ↔ t ⊆ s ∪ u ∧ u ⊆ s ∪ t :=
  sup_eq_sup_iff_left
#align set.union_eq_union_iff_left Set.union_eq_union_iff_left

theorem union_eq_union_iff_right : s ∪ u = t ∪ u ↔ s ⊆ t ∪ u ∧ t ⊆ s ∪ u :=
  sup_eq_sup_iff_right
#align set.union_eq_union_iff_right Set.union_eq_union_iff_right

@[simp]
theorem union_empty_iff {s t : Set α} : s ∪ t = ∅ ↔ s = ∅ ∧ t = ∅ := by
  simp only [← subset_empty_iff]
  -- ⊢ s ∪ t ⊆ ∅ ↔ s ⊆ ∅ ∧ t ⊆ ∅
  exact union_subset_iff
  -- 🎉 no goals
#align set.union_empty_iff Set.union_empty_iff

@[simp]
theorem union_univ {s : Set α} : s ∪ univ = univ :=
  sup_top_eq
#align set.union_univ Set.union_univ

@[simp]
theorem univ_union {s : Set α} : univ ∪ s = univ :=
  top_sup_eq
#align set.univ_union Set.univ_union

/-! ### Lemmas about intersection -/


theorem inter_def {s₁ s₂ : Set α} : s₁ ∩ s₂ = { a | a ∈ s₁ ∧ a ∈ s₂ } :=
  rfl
#align set.inter_def Set.inter_def

@[simp, mfld_simps]
theorem mem_inter_iff (x : α) (a b : Set α) : x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b :=
  Iff.rfl
#align set.mem_inter_iff Set.mem_inter_iff

theorem mem_inter {x : α} {a b : Set α} (ha : x ∈ a) (hb : x ∈ b) : x ∈ a ∩ b :=
  ⟨ha, hb⟩
#align set.mem_inter Set.mem_inter

theorem mem_of_mem_inter_left {x : α} {a b : Set α} (h : x ∈ a ∩ b) : x ∈ a :=
  h.left
#align set.mem_of_mem_inter_left Set.mem_of_mem_inter_left

theorem mem_of_mem_inter_right {x : α} {a b : Set α} (h : x ∈ a ∩ b) : x ∈ b :=
  h.right
#align set.mem_of_mem_inter_right Set.mem_of_mem_inter_right

@[simp]
theorem inter_self (a : Set α) : a ∩ a = a :=
  ext fun _ => and_self_iff _
#align set.inter_self Set.inter_self

@[simp]
theorem inter_empty (a : Set α) : a ∩ ∅ = ∅ :=
  ext fun _ => and_false_iff _
#align set.inter_empty Set.inter_empty

@[simp]
theorem empty_inter (a : Set α) : ∅ ∩ a = ∅ :=
  ext fun _ => false_and_iff _
#align set.empty_inter Set.empty_inter

theorem inter_comm (a b : Set α) : a ∩ b = b ∩ a :=
  ext fun _ => and_comm
#align set.inter_comm Set.inter_comm

theorem inter_assoc (a b c : Set α) : a ∩ b ∩ c = a ∩ (b ∩ c) :=
  ext fun _ => and_assoc
#align set.inter_assoc Set.inter_assoc

instance inter_isAssoc : IsAssociative (Set α) (· ∩ ·) :=
  ⟨inter_assoc⟩
#align set.inter_is_assoc Set.inter_isAssoc

instance inter_isComm : IsCommutative (Set α) (· ∩ ·) :=
  ⟨inter_comm⟩
#align set.inter_is_comm Set.inter_isComm

theorem inter_left_comm (s₁ s₂ s₃ : Set α) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
  ext fun _ => and_left_comm
#align set.inter_left_comm Set.inter_left_comm

theorem inter_right_comm (s₁ s₂ s₃ : Set α) : s₁ ∩ s₂ ∩ s₃ = s₁ ∩ s₃ ∩ s₂ :=
  ext fun _ => and_right_comm
#align set.inter_right_comm Set.inter_right_comm

@[simp, mfld_simps]
theorem inter_subset_left (s t : Set α) : s ∩ t ⊆ s := fun _ => And.left
#align set.inter_subset_left Set.inter_subset_left

@[simp]
theorem inter_subset_right (s t : Set α) : s ∩ t ⊆ t := fun _ => And.right
#align set.inter_subset_right Set.inter_subset_right

theorem subset_inter {s t r : Set α} (rs : r ⊆ s) (rt : r ⊆ t) : r ⊆ s ∩ t := fun _ h =>
  ⟨rs h, rt h⟩
#align set.subset_inter Set.subset_inter

@[simp]
theorem subset_inter_iff {s t r : Set α} : r ⊆ s ∩ t ↔ r ⊆ s ∧ r ⊆ t :=
  (forall_congr' fun _ => imp_and).trans forall_and
#align set.subset_inter_iff Set.subset_inter_iff

@[simp]
theorem inter_eq_left_iff_subset {s t : Set α} : s ∩ t = s ↔ s ⊆ t :=
  inf_eq_left
#align set.inter_eq_left_iff_subset Set.inter_eq_left_iff_subset

@[simp]
theorem inter_eq_right_iff_subset {s t : Set α} : s ∩ t = t ↔ t ⊆ s :=
  inf_eq_right
#align set.inter_eq_right_iff_subset Set.inter_eq_right_iff_subset

theorem inter_eq_self_of_subset_left {s t : Set α} : s ⊆ t → s ∩ t = s :=
  inter_eq_left_iff_subset.mpr
#align set.inter_eq_self_of_subset_left Set.inter_eq_self_of_subset_left

theorem inter_eq_self_of_subset_right {s t : Set α} : t ⊆ s → s ∩ t = t :=
  inter_eq_right_iff_subset.mpr
#align set.inter_eq_self_of_subset_right Set.inter_eq_self_of_subset_right

theorem inter_congr_left (ht : s ∩ u ⊆ t) (hu : s ∩ t ⊆ u) : s ∩ t = s ∩ u :=
  inf_congr_left ht hu
#align set.inter_congr_left Set.inter_congr_left

theorem inter_congr_right (hs : t ∩ u ⊆ s) (ht : s ∩ u ⊆ t) : s ∩ u = t ∩ u :=
  inf_congr_right hs ht
#align set.inter_congr_right Set.inter_congr_right

theorem inter_eq_inter_iff_left : s ∩ t = s ∩ u ↔ s ∩ u ⊆ t ∧ s ∩ t ⊆ u :=
  inf_eq_inf_iff_left
#align set.inter_eq_inter_iff_left Set.inter_eq_inter_iff_left

theorem inter_eq_inter_iff_right : s ∩ u = t ∩ u ↔ t ∩ u ⊆ s ∧ s ∩ u ⊆ t :=
  inf_eq_inf_iff_right
#align set.inter_eq_inter_iff_right Set.inter_eq_inter_iff_right

@[simp, mfld_simps]
theorem inter_univ (a : Set α) : a ∩ univ = a :=
  inf_top_eq
#align set.inter_univ Set.inter_univ

@[simp, mfld_simps]
theorem univ_inter (a : Set α) : univ ∩ a = a :=
  top_inf_eq
#align set.univ_inter Set.univ_inter

@[gcongr]
theorem inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s₁ ⊆ t₁) (h₂ : s₂ ⊆ t₂) :
    s₁ ∩ s₂ ⊆ t₁ ∩ t₂ := fun _ => And.imp (@h₁ _) (@h₂ _)
#align set.inter_subset_inter Set.inter_subset_inter

@[gcongr]
theorem inter_subset_inter_left {s t : Set α} (u : Set α) (H : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  inter_subset_inter H Subset.rfl
#align set.inter_subset_inter_left Set.inter_subset_inter_left

@[gcongr]
theorem inter_subset_inter_right {s t : Set α} (u : Set α) (H : s ⊆ t) : u ∩ s ⊆ u ∩ t :=
  inter_subset_inter Subset.rfl H
#align set.inter_subset_inter_right Set.inter_subset_inter_right

theorem union_inter_cancel_left {s t : Set α} : (s ∪ t) ∩ s = s :=
  inter_eq_self_of_subset_right <| subset_union_left _ _
#align set.union_inter_cancel_left Set.union_inter_cancel_left

theorem union_inter_cancel_right {s t : Set α} : (s ∪ t) ∩ t = t :=
  inter_eq_self_of_subset_right <| subset_union_right _ _
#align set.union_inter_cancel_right Set.union_inter_cancel_right

theorem inter_setOf_eq_sep (s : Set α) (p : α → Prop) : s ∩ {a | p a} = {a ∈ s | p a} :=
  rfl
#align set.inter_set_of_eq_sep Set.inter_setOf_eq_sep

theorem setOf_inter_eq_sep (p : α → Prop) (s : Set α) : {a | p a} ∩ s = {a ∈ s | p a} :=
  inter_comm _ _
#align set.set_of_inter_eq_sep Set.setOf_inter_eq_sep

/-! ### Distributivity laws -/


theorem inter_distrib_left (s t u : Set α) : s ∩ (t ∪ u) = s ∩ t ∪ s ∩ u :=
  inf_sup_left
#align set.inter_distrib_left Set.inter_distrib_left

theorem inter_union_distrib_left {s t u : Set α} : s ∩ (t ∪ u) = s ∩ t ∪ s ∩ u :=
  inf_sup_left
#align set.inter_union_distrib_left Set.inter_union_distrib_left

theorem inter_distrib_right (s t u : Set α) : (s ∪ t) ∩ u = s ∩ u ∪ t ∩ u :=
  inf_sup_right
#align set.inter_distrib_right Set.inter_distrib_right

theorem union_inter_distrib_right {s t u : Set α} : (s ∪ t) ∩ u = s ∩ u ∪ t ∩ u :=
  inf_sup_right
#align set.union_inter_distrib_right Set.union_inter_distrib_right

theorem union_distrib_left (s t u : Set α) : s ∪ t ∩ u = (s ∪ t) ∩ (s ∪ u) :=
  sup_inf_left
#align set.union_distrib_left Set.union_distrib_left

theorem union_inter_distrib_left {s t u : Set α} : s ∪ t ∩ u = (s ∪ t) ∩ (s ∪ u) :=
  sup_inf_left
#align set.union_inter_distrib_left Set.union_inter_distrib_left

theorem union_distrib_right (s t u : Set α) : s ∩ t ∪ u = (s ∪ u) ∩ (t ∪ u) :=
  sup_inf_right
#align set.union_distrib_right Set.union_distrib_right

theorem inter_union_distrib_right {s t u : Set α} : s ∩ t ∪ u = (s ∪ u) ∩ (t ∪ u) :=
  sup_inf_right
#align set.inter_union_distrib_right Set.inter_union_distrib_right

theorem union_union_distrib_left (s t u : Set α) : s ∪ (t ∪ u) = s ∪ t ∪ (s ∪ u) :=
  sup_sup_distrib_left _ _ _
#align set.union_union_distrib_left Set.union_union_distrib_left

theorem union_union_distrib_right (s t u : Set α) : s ∪ t ∪ u = s ∪ u ∪ (t ∪ u) :=
  sup_sup_distrib_right _ _ _
#align set.union_union_distrib_right Set.union_union_distrib_right

theorem inter_inter_distrib_left (s t u : Set α) : s ∩ (t ∩ u) = s ∩ t ∩ (s ∩ u) :=
  inf_inf_distrib_left _ _ _
#align set.inter_inter_distrib_left Set.inter_inter_distrib_left

theorem inter_inter_distrib_right (s t u : Set α) : s ∩ t ∩ u = s ∩ u ∩ (t ∩ u) :=
  inf_inf_distrib_right _ _ _
#align set.inter_inter_distrib_right Set.inter_inter_distrib_right

theorem union_union_union_comm (s t u v : Set α) : s ∪ t ∪ (u ∪ v) = s ∪ u ∪ (t ∪ v) :=
  sup_sup_sup_comm _ _ _ _
#align set.union_union_union_comm Set.union_union_union_comm

theorem inter_inter_inter_comm (s t u v : Set α) : s ∩ t ∩ (u ∩ v) = s ∩ u ∩ (t ∩ v) :=
  inf_inf_inf_comm _ _ _ _
#align set.inter_inter_inter_comm Set.inter_inter_inter_comm

/-!
### Lemmas about `insert`

`insert α s` is the set `{α} ∪ s`.
-/


theorem insert_def (x : α) (s : Set α) : insert x s = { y | y = x ∨ y ∈ s } :=
  rfl
#align set.insert_def Set.insert_def

@[simp]
theorem subset_insert (x : α) (s : Set α) : s ⊆ insert x s := fun _ => Or.inr
#align set.subset_insert Set.subset_insert

theorem mem_insert (x : α) (s : Set α) : x ∈ insert x s :=
  Or.inl rfl
#align set.mem_insert Set.mem_insert

theorem mem_insert_of_mem {x : α} {s : Set α} (y : α) : x ∈ s → x ∈ insert y s :=
  Or.inr
#align set.mem_insert_of_mem Set.mem_insert_of_mem

theorem eq_or_mem_of_mem_insert {x a : α} {s : Set α} : x ∈ insert a s → x = a ∨ x ∈ s :=
  id
#align set.eq_or_mem_of_mem_insert Set.eq_or_mem_of_mem_insert

theorem mem_of_mem_insert_of_ne : b ∈ insert a s → b ≠ a → b ∈ s :=
  Or.resolve_left
#align set.mem_of_mem_insert_of_ne Set.mem_of_mem_insert_of_ne

theorem eq_of_not_mem_of_mem_insert : b ∈ insert a s → b ∉ s → b = a :=
  Or.resolve_right
#align set.eq_of_not_mem_of_mem_insert Set.eq_of_not_mem_of_mem_insert

@[simp]
theorem mem_insert_iff {x a : α} {s : Set α} : x ∈ insert a s ↔ x = a ∨ x ∈ s :=
  Iff.rfl
#align set.mem_insert_iff Set.mem_insert_iff

@[simp]
theorem insert_eq_of_mem {a : α} {s : Set α} (h : a ∈ s) : insert a s = s :=
  ext fun _ => or_iff_right_of_imp fun e => e.symm ▸ h
#align set.insert_eq_of_mem Set.insert_eq_of_mem

theorem ne_insert_of_not_mem {s : Set α} (t : Set α) {a : α} : a ∉ s → s ≠ insert a t :=
  mt fun e => e.symm ▸ mem_insert _ _
#align set.ne_insert_of_not_mem Set.ne_insert_of_not_mem

@[simp]
theorem insert_eq_self : insert a s = s ↔ a ∈ s :=
  ⟨fun h => h ▸ mem_insert _ _, insert_eq_of_mem⟩
#align set.insert_eq_self Set.insert_eq_self

theorem insert_ne_self : insert a s ≠ s ↔ a ∉ s :=
  insert_eq_self.not
#align set.insert_ne_self Set.insert_ne_self

theorem insert_subset_iff : insert a s ⊆ t ↔ a ∈ t ∧ s ⊆ t := by
  simp only [subset_def, mem_insert_iff, or_imp, forall_and, forall_eq]
  -- 🎉 no goals
#align set.insert_subset Set.insert_subset_iff

theorem insert_subset (ha : a ∈ t) (hs : s ⊆ t) : insert a s ⊆ t :=
  insert_subset_iff.mpr ⟨ha, hs⟩

theorem insert_subset_insert (h : s ⊆ t) : insert a s ⊆ insert a t := fun _ => Or.imp_right (@h _)
#align set.insert_subset_insert Set.insert_subset_insert

theorem insert_subset_insert_iff (ha : a ∉ s) : insert a s ⊆ insert a t ↔ s ⊆ t := by
  refine' ⟨fun h x hx => _, insert_subset_insert⟩
  -- ⊢ x ∈ t
  rcases h (subset_insert _ _ hx) with (rfl | hxt)
  -- ⊢ x ∈ t
  exacts [(ha hx).elim, hxt]
  -- 🎉 no goals
#align set.insert_subset_insert_iff Set.insert_subset_insert_iff

theorem subset_insert_iff_of_not_mem (ha : a ∉ s) : s ⊆ insert a t ↔ s ⊆ t :=
  forall₂_congr <| fun _ hb => or_iff_right <| ne_of_mem_of_not_mem hb ha
#align set.subset_insert_iff_of_not_mem Set.subset_insert_iff_of_not_mem

theorem ssubset_iff_insert {s t : Set α} : s ⊂ t ↔ ∃ (a : α) (_ : a ∉ s), insert a s ⊆ t := by
  simp only [insert_subset_iff, exists_and_right, ssubset_def, not_subset]
  -- ⊢ (s ⊆ t ∧ ∃ a, a ∈ t ∧ ¬a ∈ s) ↔ (∃ x x_1, x ∈ t) ∧ s ⊆ t
  simp only [exists_prop, and_comm]
  -- 🎉 no goals
#align set.ssubset_iff_insert Set.ssubset_iff_insert

theorem ssubset_insert {s : Set α} {a : α} (h : a ∉ s) : s ⊂ insert a s :=
  ssubset_iff_insert.2 ⟨a, h, Subset.rfl⟩
#align set.ssubset_insert Set.ssubset_insert

theorem insert_comm (a b : α) (s : Set α) : insert a (insert b s) = insert b (insert a s) :=
  ext fun _ => or_left_comm
#align set.insert_comm Set.insert_comm

--Porting note: removing `simp` attribute because `simp` can prove it
theorem insert_idem (a : α) (s : Set α) : insert a (insert a s) = insert a s :=
  insert_eq_of_mem <| mem_insert _ _
#align set.insert_idem Set.insert_idem

theorem insert_union : insert a s ∪ t = insert a (s ∪ t) :=
  ext fun _ => or_assoc
#align set.insert_union Set.insert_union

@[simp]
theorem union_insert : s ∪ insert a t = insert a (s ∪ t) :=
  ext fun _ => or_left_comm
#align set.union_insert Set.union_insert

@[simp]
theorem insert_nonempty (a : α) (s : Set α) : (insert a s).Nonempty :=
  ⟨a, mem_insert a s⟩
#align set.insert_nonempty Set.insert_nonempty

instance (a : α) (s : Set α) : Nonempty (insert a s : Set α) :=
  (insert_nonempty a s).to_subtype

theorem insert_inter_distrib (a : α) (s t : Set α) : insert a (s ∩ t) = insert a s ∩ insert a t :=
  ext fun _ => or_and_left
#align set.insert_inter_distrib Set.insert_inter_distrib

theorem insert_union_distrib (a : α) (s t : Set α) : insert a (s ∪ t) = insert a s ∪ insert a t :=
  ext fun _ => or_or_distrib_left
#align set.insert_union_distrib Set.insert_union_distrib

theorem insert_inj (ha : a ∉ s) : insert a s = insert b s ↔ a = b :=
  ⟨fun h => eq_of_not_mem_of_mem_insert (h.subst <| mem_insert a s) ha,
    congr_arg (fun x => insert x s)⟩
#align set.insert_inj Set.insert_inj

-- useful in proofs by induction
theorem forall_of_forall_insert {P : α → Prop} {a : α} {s : Set α} (H : ∀ x, x ∈ insert a s → P x)
    (x) (h : x ∈ s) : P x :=
  H _ (Or.inr h)
#align set.forall_of_forall_insert Set.forall_of_forall_insert

theorem forall_insert_of_forall {P : α → Prop} {a : α} {s : Set α} (H : ∀ x, x ∈ s → P x) (ha : P a)
    (x) (h : x ∈ insert a s) : P x :=
  h.elim (fun e => e.symm ▸ ha) (H _)
#align set.forall_insert_of_forall Set.forall_insert_of_forall

/- Porting note: ∃ x ∈ insert a s, P x is parsed as ∃ x, x ∈ insert a s ∧ P x,
 where in Lean3 it was parsed as `∃ x, ∃ (h : x ∈ insert a s), P x` -/
theorem bex_insert_iff {P : α → Prop} {a : α} {s : Set α} :
    (∃ x ∈ insert a s, P x) ↔ (P a ∨ ∃ x ∈ s, P x) := by
  simp [mem_insert_iff, or_and_right, exists_and_left, exists_or]
  -- 🎉 no goals
#align set.bex_insert_iff Set.bex_insert_iff

theorem ball_insert_iff {P : α → Prop} {a : α} {s : Set α} :
    (∀ x ∈ insert a s, P x) ↔ P a ∧ ∀ x ∈ s, P x :=
  ball_or_left.trans <| and_congr_left' forall_eq
#align set.ball_insert_iff Set.ball_insert_iff

/-! ### Lemmas about singletons -/

/- porting note: instance was in core in Lean3 -/
instance : IsLawfulSingleton α (Set α) :=
  ⟨fun x => Set.ext <| fun a => by
    simp only [mem_empty_iff_false, mem_insert_iff, or_false]
    -- ⊢ a = x ↔ a ∈ {x}
    exact Iff.rfl⟩
    -- 🎉 no goals

theorem singleton_def (a : α) : ({a} : Set α) = insert a ∅ :=
  (insert_emptyc_eq a).symm
#align set.singleton_def Set.singleton_def

@[simp]
theorem mem_singleton_iff {a b : α} : a ∈ ({b} : Set α) ↔ a = b :=
  Iff.rfl
#align set.mem_singleton_iff Set.mem_singleton_iff

@[simp]
theorem setOf_eq_eq_singleton {a : α} : { n | n = a } = {a} :=
  rfl
#align set.set_of_eq_eq_singleton Set.setOf_eq_eq_singleton

@[simp]
theorem setOf_eq_eq_singleton' {a : α} : { x | a = x } = {a} :=
  ext fun _ => eq_comm
#align set.set_of_eq_eq_singleton' Set.setOf_eq_eq_singleton'

-- TODO: again, annotation needed
--Porting note: removed `simp` attribute
theorem mem_singleton (a : α) : a ∈ ({a} : Set α) :=
  @rfl _ _
#align set.mem_singleton Set.mem_singleton

theorem eq_of_mem_singleton {x y : α} (h : x ∈ ({y} : Set α)) : x = y :=
  h
#align set.eq_of_mem_singleton Set.eq_of_mem_singleton

@[simp]
theorem singleton_eq_singleton_iff {x y : α} : {x} = ({y} : Set α) ↔ x = y :=
  ext_iff.trans eq_iff_eq_cancel_left
#align set.singleton_eq_singleton_iff Set.singleton_eq_singleton_iff

theorem singleton_injective : Injective (singleton : α → Set α) := fun _ _ =>
  singleton_eq_singleton_iff.mp
#align set.singleton_injective Set.singleton_injective

theorem mem_singleton_of_eq {x y : α} (H : x = y) : x ∈ ({y} : Set α) :=
  H
#align set.mem_singleton_of_eq Set.mem_singleton_of_eq

theorem insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α) ∪ s :=
  rfl
#align set.insert_eq Set.insert_eq

@[simp]
theorem singleton_nonempty (a : α) : ({a} : Set α).Nonempty :=
  ⟨a, rfl⟩
#align set.singleton_nonempty Set.singleton_nonempty

@[simp]
theorem singleton_ne_empty (a : α) : ({a} : Set α) ≠ ∅ :=
  (singleton_nonempty _).ne_empty
#align set.singleton_ne_empty Set.singleton_ne_empty

--Porting note: removed `simp` attribute because `simp` can prove it
theorem empty_ssubset_singleton : (∅ : Set α) ⊂ {a} :=
  (singleton_nonempty _).empty_ssubset
#align set.empty_ssubset_singleton Set.empty_ssubset_singleton

@[simp]
theorem singleton_subset_iff {a : α} {s : Set α} : {a} ⊆ s ↔ a ∈ s :=
  forall_eq
#align set.singleton_subset_iff Set.singleton_subset_iff

theorem singleton_subset_singleton : ({a} : Set α) ⊆ {b} ↔ a = b := by simp
                                                                       -- 🎉 no goals
#align set.singleton_subset_singleton Set.singleton_subset_singleton

theorem set_compr_eq_eq_singleton {a : α} : { b | b = a } = {a} :=
  rfl
#align set.set_compr_eq_eq_singleton Set.set_compr_eq_eq_singleton

@[simp]
theorem singleton_union : {a} ∪ s = insert a s :=
  rfl
#align set.singleton_union Set.singleton_union

@[simp]
theorem union_singleton : s ∪ {a} = insert a s :=
  union_comm _ _
#align set.union_singleton Set.union_singleton

@[simp]
theorem singleton_inter_nonempty : ({a} ∩ s).Nonempty ↔ a ∈ s := by
  simp only [Set.Nonempty, mem_inter_iff, mem_singleton_iff, exists_eq_left]
  -- 🎉 no goals
#align set.singleton_inter_nonempty Set.singleton_inter_nonempty

@[simp]
theorem inter_singleton_nonempty : (s ∩ {a}).Nonempty ↔ a ∈ s := by
  rw [inter_comm, singleton_inter_nonempty]
  -- 🎉 no goals
#align set.inter_singleton_nonempty Set.inter_singleton_nonempty

@[simp]
theorem singleton_inter_eq_empty : {a} ∩ s = ∅ ↔ a ∉ s :=
  not_nonempty_iff_eq_empty.symm.trans singleton_inter_nonempty.not
#align set.singleton_inter_eq_empty Set.singleton_inter_eq_empty

@[simp]
theorem inter_singleton_eq_empty : s ∩ {a} = ∅ ↔ a ∉ s := by
  rw [inter_comm, singleton_inter_eq_empty]
  -- 🎉 no goals
#align set.inter_singleton_eq_empty Set.inter_singleton_eq_empty

theorem nmem_singleton_empty {s : Set α} : s ∉ ({∅} : Set (Set α)) ↔ s.Nonempty :=
  nonempty_iff_ne_empty.symm
#align set.nmem_singleton_empty Set.nmem_singleton_empty

instance uniqueSingleton (a : α) : Unique (↥({a} : Set α)) :=
  ⟨⟨⟨a, mem_singleton a⟩⟩, fun ⟨_, h⟩ => Subtype.eq h⟩
#align set.unique_singleton Set.uniqueSingleton

theorem eq_singleton_iff_unique_mem : s = {a} ↔ a ∈ s ∧ ∀ x ∈ s, x = a :=
  Subset.antisymm_iff.trans <| and_comm.trans <| and_congr_left' singleton_subset_iff
#align set.eq_singleton_iff_unique_mem Set.eq_singleton_iff_unique_mem

theorem eq_singleton_iff_nonempty_unique_mem : s = {a} ↔ s.Nonempty ∧ ∀ x ∈ s, x = a :=
  eq_singleton_iff_unique_mem.trans <|
    and_congr_left fun H => ⟨fun h' => ⟨_, h'⟩, fun ⟨x, h⟩ => H x h ▸ h⟩
#align set.eq_singleton_iff_nonempty_unique_mem Set.eq_singleton_iff_nonempty_unique_mem

-- while `simp` is capable of proving this, it is not capable of turning the LHS into the RHS.
@[simp]
theorem default_coe_singleton (x : α) : (default : ({x} : Set α)) = ⟨x, rfl⟩ :=
  rfl
#align set.default_coe_singleton Set.default_coe_singleton

/-! ### Lemmas about pairs -/


--Porting note: removed `simp` attribute because `simp` can prove it
theorem pair_eq_singleton (a : α) : ({a, a} : Set α) = {a} :=
  union_self _
#align set.pair_eq_singleton Set.pair_eq_singleton

theorem pair_comm (a b : α) : ({a, b} : Set α) = {b, a} :=
  union_comm _ _
#align set.pair_comm Set.pair_comm

-- Porting note: first branch after `constructor` used to be by `tauto!`.
theorem pair_eq_pair_iff {x y z w : α} :
    ({x, y} : Set α) = {z, w} ↔ x = z ∧ y = w ∨ x = w ∧ y = z := by
  simp only [Set.Subset.antisymm_iff, Set.insert_subset_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.singleton_subset_iff]
  constructor
  -- ⊢ ((x = z ∨ x = w) ∧ (y = z ∨ y = w)) ∧ (z = x ∨ z = y) ∧ (w = x ∨ w = y) → x  …
  · rintro ⟨⟨rfl | rfl, rfl | rfl⟩, ⟨h₁, h₂⟩⟩ <;> simp [h₁, h₂] at * <;> simp [h₁, h₂]
                                                  -- ⊢ y = w
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- ⊢ y = z
                                                                         -- 🎉 no goals
                                                                         -- 🎉 no goals
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp
    -- ⊢ ((x = x ∨ x = y) ∧ (y = x ∨ y = y)) ∧ (x = x ∨ x = y) ∧ (y = x ∨ y = y)
                                         -- 🎉 no goals
                                         -- 🎉 no goals
#align set.pair_eq_pair_iff Set.pair_eq_pair_iff

/-! ### Lemmas about sets defined as `{x ∈ s | p x}`. -/


section Sep

variable {p q : α → Prop} {x : α}

theorem mem_sep (xs : x ∈ s) (px : p x) : x ∈ { x ∈ s | p x } :=
  ⟨xs, px⟩
#align set.mem_sep Set.mem_sep

@[simp]
theorem sep_mem_eq : { x ∈ s | x ∈ t } = s ∩ t :=
  rfl
#align set.sep_mem_eq Set.sep_mem_eq

@[simp]
theorem mem_sep_iff : x ∈ { x ∈ s | p x } ↔ x ∈ s ∧ p x :=
  Iff.rfl
#align set.mem_sep_iff Set.mem_sep_iff

theorem sep_ext_iff : { x ∈ s | p x } = { x ∈ s | q x } ↔ ∀ x ∈ s, p x ↔ q x := by
  simp_rw [ext_iff, mem_sep_iff, and_congr_right_iff]
  -- 🎉 no goals
#align set.sep_ext_iff Set.sep_ext_iff

theorem sep_eq_of_subset (h : s ⊆ t) : { x ∈ t | x ∈ s } = s :=
  inter_eq_self_of_subset_right h
#align set.sep_eq_of_subset Set.sep_eq_of_subset

@[simp]
theorem sep_subset (s : Set α) (p : α → Prop) : { x ∈ s | p x } ⊆ s := fun _ => And.left
#align set.sep_subset Set.sep_subset

@[simp]
theorem sep_eq_self_iff_mem_true : { x ∈ s | p x } = s ↔ ∀ x ∈ s, p x := by
  simp_rw [ext_iff, mem_sep_iff, and_iff_left_iff_imp]
  -- 🎉 no goals
#align set.sep_eq_self_iff_mem_true Set.sep_eq_self_iff_mem_true

@[simp]
theorem sep_eq_empty_iff_mem_false : { x ∈ s | p x } = ∅ ↔ ∀ x ∈ s, ¬p x := by
  simp_rw [ext_iff, mem_sep_iff, mem_empty_iff_false, iff_false_iff, not_and]
  -- 🎉 no goals
#align set.sep_eq_empty_iff_mem_false Set.sep_eq_empty_iff_mem_false

--Porting note: removed `simp` attribute because `simp` can prove it
theorem sep_true : { x ∈ s | True } = s :=
  inter_univ s
#align set.sep_true Set.sep_true

--Porting note: removed `simp` attribute because `simp` can prove it
theorem sep_false : { x ∈ s | False } = ∅ :=
  inter_empty s
#align set.sep_false Set.sep_false

--Porting note: removed `simp` attribute because `simp` can prove it
theorem sep_empty (p : α → Prop) : { x ∈ (∅ : Set α) | p x } = ∅ :=
  empty_inter p
#align set.sep_empty Set.sep_empty

--Porting note: removed `simp` attribute because `simp` can prove it
theorem sep_univ : { x ∈ (univ : Set α) | p x } = { x | p x } :=
  univ_inter p
#align set.sep_univ Set.sep_univ

@[simp]
theorem sep_union : { x | (x ∈ s ∨ x ∈ t) ∧ p x } = { x ∈ s | p x } ∪ { x ∈ t | p x } :=
  union_inter_distrib_right
#align set.sep_union Set.sep_union

@[simp]
theorem sep_inter : { x | (x ∈ s ∧ x ∈ t) ∧ p x } = { x ∈ s | p x } ∩ { x ∈ t | p x } :=
  inter_inter_distrib_right s t p
#align set.sep_inter Set.sep_inter

@[simp]
theorem sep_and : { x ∈ s | p x ∧ q x } = { x ∈ s | p x } ∩ { x ∈ s | q x } :=
  inter_inter_distrib_left s p q
#align set.sep_and Set.sep_and

@[simp]
theorem sep_or : { x ∈ s | p x ∨ q x } = { x ∈ s | p x } ∪ { x ∈ s | q x } :=
  inter_union_distrib_left
#align set.sep_or Set.sep_or

@[simp]
theorem sep_setOf : { x ∈ { y | p y } | q x } = { x | p x ∧ q x } :=
  rfl
#align set.sep_set_of Set.sep_setOf

end Sep

@[simp]
theorem subset_singleton_iff {α : Type*} {s : Set α} {x : α} : s ⊆ {x} ↔ ∀ y ∈ s, y = x :=
  Iff.rfl
#align set.subset_singleton_iff Set.subset_singleton_iff

theorem subset_singleton_iff_eq {s : Set α} {x : α} : s ⊆ {x} ↔ s = ∅ ∨ s = {x} := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  -- ⊢ ∅ ⊆ {x} ↔ ∅ = ∅ ∨ ∅ = {x}
  · exact ⟨fun _ => Or.inl rfl, fun _ => empty_subset _⟩
    -- 🎉 no goals
  · simp [eq_singleton_iff_nonempty_unique_mem, hs, hs.ne_empty]
    -- 🎉 no goals
#align set.subset_singleton_iff_eq Set.subset_singleton_iff_eq

theorem Nonempty.subset_singleton_iff (h : s.Nonempty) : s ⊆ {a} ↔ s = {a} :=
  subset_singleton_iff_eq.trans <| or_iff_right h.ne_empty
#align set.nonempty.subset_singleton_iff Set.Nonempty.subset_singleton_iff

theorem ssubset_singleton_iff {s : Set α} {x : α} : s ⊂ {x} ↔ s = ∅ := by
  rw [ssubset_iff_subset_ne, subset_singleton_iff_eq, or_and_right, and_not_self_iff, or_false_iff,
    and_iff_left_iff_imp]
  exact fun h => h ▸ (singleton_ne_empty _).symm
  -- 🎉 no goals
#align set.ssubset_singleton_iff Set.ssubset_singleton_iff

theorem eq_empty_of_ssubset_singleton {s : Set α} {x : α} (hs : s ⊂ {x}) : s = ∅ :=
  ssubset_singleton_iff.1 hs
#align set.eq_empty_of_ssubset_singleton Set.eq_empty_of_ssubset_singleton

/-! ### Disjointness -/


protected theorem disjoint_iff : Disjoint s t ↔ s ∩ t ⊆ ∅ :=
  disjoint_iff_inf_le
#align set.disjoint_iff Set.disjoint_iff

theorem disjoint_iff_inter_eq_empty : Disjoint s t ↔ s ∩ t = ∅ :=
  disjoint_iff
#align set.disjoint_iff_inter_eq_empty Set.disjoint_iff_inter_eq_empty

theorem _root_.Disjoint.inter_eq : Disjoint s t → s ∩ t = ∅ :=
  Disjoint.eq_bot
#align disjoint.inter_eq Disjoint.inter_eq

theorem disjoint_left : Disjoint s t ↔ ∀ ⦃a⦄, a ∈ s → a ∉ t :=
  disjoint_iff_inf_le.trans <| forall_congr' fun _ => not_and
#align set.disjoint_left Set.disjoint_left

theorem disjoint_right : Disjoint s t ↔ ∀ ⦃a⦄, a ∈ t → a ∉ s := by rw [disjoint_comm, disjoint_left]
                                                                   -- 🎉 no goals
#align set.disjoint_right Set.disjoint_right

lemma not_disjoint_iff : ¬Disjoint s t ↔ ∃ x, x ∈ s ∧ x ∈ t :=
  Set.disjoint_iff.not.trans $ not_forall.trans $ exists_congr fun _ ↦ not_not
#align set.not_disjoint_iff Set.not_disjoint_iff

lemma not_disjoint_iff_nonempty_inter : ¬ Disjoint s t ↔ (s ∩ t).Nonempty := not_disjoint_iff
#align set.not_disjoint_iff_nonempty_inter Set.not_disjoint_iff_nonempty_inter

alias ⟨_, Nonempty.not_disjoint⟩ := not_disjoint_iff_nonempty_inter
#align set.nonempty.not_disjoint Set.Nonempty.not_disjoint

lemma disjoint_or_nonempty_inter (s t : Set α) : Disjoint s t ∨ (s ∩ t).Nonempty :=
  (em _).imp_right not_disjoint_iff_nonempty_inter.1
#align set.disjoint_or_nonempty_inter Set.disjoint_or_nonempty_inter

lemma disjoint_iff_forall_ne : Disjoint s t ↔ ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ t → a ≠ b := by
  simp only [Ne.def, disjoint_left, @imp_not_comm _ (_ = _), forall_eq']
  -- 🎉 no goals
#align set.disjoint_iff_forall_ne Set.disjoint_iff_forall_ne

alias ⟨_root_.Disjoint.ne_of_mem, _⟩ := disjoint_iff_forall_ne
#align disjoint.ne_of_mem Disjoint.ne_of_mem

lemma disjoint_of_subset_left (h : s ⊆ u) (d : Disjoint u t) : Disjoint s t := d.mono_left h
#align set.disjoint_of_subset_left Set.disjoint_of_subset_left
lemma disjoint_of_subset_right (h : t ⊆ u) (d : Disjoint s u) : Disjoint s t := d.mono_right h
#align set.disjoint_of_subset_right Set.disjoint_of_subset_right

lemma disjoint_of_subset (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) (h : Disjoint s₂ t₂) : Disjoint s₁ t₁ :=
  h.mono hs ht
#align set.disjoint_of_subset Set.disjoint_of_subset

@[simp]
lemma disjoint_union_left : Disjoint (s ∪ t) u ↔ Disjoint s u ∧ Disjoint t u := disjoint_sup_left
#align set.disjoint_union_left Set.disjoint_union_left

@[simp]
lemma disjoint_union_right : Disjoint s (t ∪ u) ↔ Disjoint s t ∧ Disjoint s u := disjoint_sup_right
#align set.disjoint_union_right Set.disjoint_union_right

@[simp] lemma disjoint_empty (s : Set α) : Disjoint s ∅ := disjoint_bot_right
#align set.disjoint_empty Set.disjoint_empty
@[simp] lemma empty_disjoint (s : Set α) : Disjoint ∅ s := disjoint_bot_left
#align set.empty_disjoint Set.empty_disjoint

@[simp] lemma univ_disjoint : Disjoint univ s ↔ s = ∅ := top_disjoint
#align set.univ_disjoint Set.univ_disjoint
@[simp] lemma disjoint_univ : Disjoint s univ ↔ s = ∅ := disjoint_top
#align set.disjoint_univ Set.disjoint_univ

lemma disjoint_sdiff_left : Disjoint (t \ s) s := disjoint_sdiff_self_left
#align set.disjoint_sdiff_left Set.disjoint_sdiff_left

lemma disjoint_sdiff_right : Disjoint s (t \ s) := disjoint_sdiff_self_right
#align set.disjoint_sdiff_right Set.disjoint_sdiff_right

theorem diff_union_diff_cancel (hts : t ⊆ s) (hut : u ⊆ t) : s \ t ∪ t \ u = s \ u :=
  sdiff_sup_sdiff_cancel hts hut
#align set.diff_union_diff_cancel Set.diff_union_diff_cancel

theorem diff_diff_eq_sdiff_union (h : u ⊆ s) : s \ (t \ u) = s \ t ∪ u := sdiff_sdiff_eq_sdiff_sup h
#align set.diff_diff_eq_sdiff_union Set.diff_diff_eq_sdiff_union

@[simp default+1]
lemma disjoint_singleton_left : Disjoint {a} s ↔ a ∉ s := by simp [Set.disjoint_iff, subset_def]
                                                             -- 🎉 no goals
#align set.disjoint_singleton_left Set.disjoint_singleton_left

@[simp]
lemma disjoint_singleton_right : Disjoint s {a} ↔ a ∉ s :=
  disjoint_comm.trans disjoint_singleton_left
#align set.disjoint_singleton_right Set.disjoint_singleton_right

lemma disjoint_singleton : Disjoint ({a} : Set α) {b} ↔ a ≠ b :=
  by simp
     -- 🎉 no goals
#align set.disjoint_singleton Set.disjoint_singleton

lemma subset_diff : s ⊆ t \ u ↔ s ⊆ t ∧ Disjoint s u := le_iff_subset.symm.trans le_sdiff
#align set.subset_diff Set.subset_diff

theorem inter_diff_distrib_left (s t u : Set α) : s ∩ (t \ u) = (s ∩ t) \ (s ∩ u) :=
  inf_sdiff_distrib_left _ _ _
#align set.inter_diff_distrib_left Set.inter_diff_distrib_left

theorem inter_diff_distrib_right (s t u : Set α) : s \ t ∩ u = (s ∩ u) \ (t ∩ u) :=
  inf_sdiff_distrib_right _ _ _
#align set.inter_diff_distrib_right Set.inter_diff_distrib_right

/-! ### Lemmas about complement -/


theorem compl_def (s : Set α) : sᶜ = { x | x ∉ s } :=
  rfl
#align set.compl_def Set.compl_def

theorem mem_compl {s : Set α} {x : α} (h : x ∉ s) : x ∈ sᶜ :=
  h
#align set.mem_compl Set.mem_compl

theorem compl_setOf {α} (p : α → Prop) : { a | p a }ᶜ = { a | ¬p a } :=
  rfl
#align set.compl_set_of Set.compl_setOf

theorem not_mem_of_mem_compl {s : Set α} {x : α} (h : x ∈ sᶜ) : x ∉ s :=
  h
#align set.not_mem_of_mem_compl Set.not_mem_of_mem_compl

@[simp]
theorem mem_compl_iff (s : Set α) (x : α) : x ∈ sᶜ ↔ x ∉ s :=
  Iff.rfl
#align set.mem_compl_iff Set.mem_compl_iff

theorem not_mem_compl_iff {x : α} : x ∉ sᶜ ↔ x ∈ s :=
  not_not
#align set.not_mem_compl_iff Set.not_mem_compl_iff

@[simp]
theorem inter_compl_self (s : Set α) : s ∩ sᶜ = ∅ :=
  inf_compl_eq_bot
#align set.inter_compl_self Set.inter_compl_self

@[simp]
theorem compl_inter_self (s : Set α) : sᶜ ∩ s = ∅ :=
  compl_inf_eq_bot
#align set.compl_inter_self Set.compl_inter_self

@[simp]
theorem compl_empty : (∅ : Set α)ᶜ = univ :=
  compl_bot
#align set.compl_empty Set.compl_empty

@[simp]
theorem compl_union (s t : Set α) : (s ∪ t)ᶜ = sᶜ ∩ tᶜ :=
  compl_sup
#align set.compl_union Set.compl_union

theorem compl_inter (s t : Set α) : (s ∩ t)ᶜ = sᶜ ∪ tᶜ :=
  compl_inf
#align set.compl_inter Set.compl_inter

@[simp]
theorem compl_univ : (univ : Set α)ᶜ = ∅ :=
  compl_top
#align set.compl_univ Set.compl_univ

@[simp]
theorem compl_empty_iff {s : Set α} : sᶜ = ∅ ↔ s = univ :=
  compl_eq_bot
#align set.compl_empty_iff Set.compl_empty_iff

@[simp]
theorem compl_univ_iff {s : Set α} : sᶜ = univ ↔ s = ∅ :=
  compl_eq_top
#align set.compl_univ_iff Set.compl_univ_iff

theorem compl_ne_univ : sᶜ ≠ univ ↔ s.Nonempty :=
  compl_univ_iff.not.trans nonempty_iff_ne_empty.symm
#align set.compl_ne_univ Set.compl_ne_univ

theorem nonempty_compl : sᶜ.Nonempty ↔ s ≠ univ :=
  (ne_univ_iff_exists_not_mem s).symm
#align set.nonempty_compl Set.nonempty_compl

@[simp] lemma nonempty_compl_of_nontrivial [Nontrivial α] (x : α) : Set.Nonempty {x}ᶜ := by
  obtain ⟨y, hy⟩ := exists_ne x
  -- ⊢ Set.Nonempty {x}ᶜ
  exact ⟨y, by simp [hy]⟩
  -- 🎉 no goals

theorem mem_compl_singleton_iff {a x : α} : x ∈ ({a} : Set α)ᶜ ↔ x ≠ a :=
  Iff.rfl
#align set.mem_compl_singleton_iff Set.mem_compl_singleton_iff

theorem compl_singleton_eq (a : α) : ({a} : Set α)ᶜ = { x | x ≠ a } :=
  rfl
#align set.compl_singleton_eq Set.compl_singleton_eq

@[simp]
theorem compl_ne_eq_singleton (a : α) : ({ x | x ≠ a } : Set α)ᶜ = {a} :=
  compl_compl _
#align set.compl_ne_eq_singleton Set.compl_ne_eq_singleton

theorem union_eq_compl_compl_inter_compl (s t : Set α) : s ∪ t = (sᶜ ∩ tᶜ)ᶜ :=
  ext fun _ => or_iff_not_and_not
#align set.union_eq_compl_compl_inter_compl Set.union_eq_compl_compl_inter_compl

theorem inter_eq_compl_compl_union_compl (s t : Set α) : s ∩ t = (sᶜ ∪ tᶜ)ᶜ :=
  ext fun _ => and_iff_not_or_not
#align set.inter_eq_compl_compl_union_compl Set.inter_eq_compl_compl_union_compl

@[simp]
theorem union_compl_self (s : Set α) : s ∪ sᶜ = univ :=
  eq_univ_iff_forall.2 fun _ => em _
#align set.union_compl_self Set.union_compl_self

@[simp]
theorem compl_union_self (s : Set α) : sᶜ ∪ s = univ := by rw [union_comm, union_compl_self]
                                                           -- 🎉 no goals
#align set.compl_union_self Set.compl_union_self

theorem compl_subset_comm : sᶜ ⊆ t ↔ tᶜ ⊆ s :=
  @compl_le_iff_compl_le _ s _ _
#align set.compl_subset_comm Set.compl_subset_comm

theorem subset_compl_comm : s ⊆ tᶜ ↔ t ⊆ sᶜ :=
  @le_compl_iff_le_compl _ _ _ t
#align set.subset_compl_comm Set.subset_compl_comm

@[simp]
theorem compl_subset_compl : sᶜ ⊆ tᶜ ↔ t ⊆ s :=
  @compl_le_compl_iff_le (Set α) _ _ _
#align set.compl_subset_compl Set.compl_subset_compl

@[gcongr] theorem compl_subset_compl_of_subset (h : t ⊆ s) : sᶜ ⊆ tᶜ := compl_subset_compl.2 h

theorem subset_compl_iff_disjoint_left : s ⊆ tᶜ ↔ Disjoint t s :=
  @le_compl_iff_disjoint_left (Set α) _ _ _
#align set.subset_compl_iff_disjoint_left Set.subset_compl_iff_disjoint_left

theorem subset_compl_iff_disjoint_right : s ⊆ tᶜ ↔ Disjoint s t :=
  @le_compl_iff_disjoint_right (Set α) _ _ _
#align set.subset_compl_iff_disjoint_right Set.subset_compl_iff_disjoint_right

theorem disjoint_compl_left_iff_subset : Disjoint sᶜ t ↔ t ⊆ s :=
  disjoint_compl_left_iff
#align set.disjoint_compl_left_iff_subset Set.disjoint_compl_left_iff_subset

theorem disjoint_compl_right_iff_subset : Disjoint s tᶜ ↔ s ⊆ t :=
  disjoint_compl_right_iff
#align set.disjoint_compl_right_iff_subset Set.disjoint_compl_right_iff_subset

alias ⟨_, _root_.Disjoint.subset_compl_right⟩ := subset_compl_iff_disjoint_right
#align disjoint.subset_compl_right Disjoint.subset_compl_right

alias ⟨_, _root_.Disjoint.subset_compl_left⟩ := subset_compl_iff_disjoint_left
#align disjoint.subset_compl_left Disjoint.subset_compl_left

alias ⟨_, _root_.HasSubset.Subset.disjoint_compl_left⟩ := disjoint_compl_left_iff_subset
#align has_subset.subset.disjoint_compl_left HasSubset.Subset.disjoint_compl_left

alias ⟨_, _root_.HasSubset.Subset.disjoint_compl_right⟩ := disjoint_compl_right_iff_subset
#align has_subset.subset.disjoint_compl_right HasSubset.Subset.disjoint_compl_right

theorem subset_union_compl_iff_inter_subset {s t u : Set α} : s ⊆ t ∪ uᶜ ↔ s ∩ u ⊆ t :=
  (@isCompl_compl _ u _).le_sup_right_iff_inf_left_le
#align set.subset_union_compl_iff_inter_subset Set.subset_union_compl_iff_inter_subset

theorem compl_subset_iff_union {s t : Set α} : sᶜ ⊆ t ↔ s ∪ t = univ :=
  Iff.symm <| eq_univ_iff_forall.trans <| forall_congr' fun _ => or_iff_not_imp_left
#align set.compl_subset_iff_union Set.compl_subset_iff_union

@[simp]
theorem subset_compl_singleton_iff {a : α} {s : Set α} : s ⊆ {a}ᶜ ↔ a ∉ s :=
  subset_compl_comm.trans singleton_subset_iff
#align set.subset_compl_singleton_iff Set.subset_compl_singleton_iff

theorem inter_subset (a b c : Set α) : a ∩ b ⊆ c ↔ a ⊆ bᶜ ∪ c :=
  forall_congr' fun _ => and_imp.trans <| imp_congr_right fun _ => imp_iff_not_or
#align set.inter_subset Set.inter_subset

theorem inter_compl_nonempty_iff {s t : Set α} : (s ∩ tᶜ).Nonempty ↔ ¬s ⊆ t :=
  (not_subset.trans <| exists_congr fun x => by simp [mem_compl]).symm
                                                -- 🎉 no goals
#align set.inter_compl_nonempty_iff Set.inter_compl_nonempty_iff

/-! ### Lemmas about set difference -/


theorem diff_eq (s t : Set α) : s \ t = s ∩ tᶜ :=
  rfl
#align set.diff_eq Set.diff_eq

@[simp]
theorem mem_diff {s t : Set α} (x : α) : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t :=
  Iff.rfl
#align set.mem_diff Set.mem_diff

theorem mem_diff_of_mem {s t : Set α} {x : α} (h1 : x ∈ s) (h2 : x ∉ t) : x ∈ s \ t :=
  ⟨h1, h2⟩
#align set.mem_diff_of_mem Set.mem_diff_of_mem

theorem not_mem_diff_of_mem {s t : Set α} {x : α} (hx : x ∈ t) : x ∉ s \ t := fun h => h.2 hx
#align set.not_mem_diff_of_mem Set.not_mem_diff_of_mem

theorem mem_of_mem_diff {s t : Set α} {x : α} (h : x ∈ s \ t) : x ∈ s :=
  h.left
#align set.mem_of_mem_diff Set.mem_of_mem_diff

theorem not_mem_of_mem_diff {s t : Set α} {x : α} (h : x ∈ s \ t) : x ∉ t :=
  h.right
#align set.not_mem_of_mem_diff Set.not_mem_of_mem_diff

theorem diff_eq_compl_inter {s t : Set α} : s \ t = tᶜ ∩ s := by rw [diff_eq, inter_comm]
                                                                 -- 🎉 no goals
#align set.diff_eq_compl_inter Set.diff_eq_compl_inter

theorem nonempty_diff {s t : Set α} : (s \ t).Nonempty ↔ ¬s ⊆ t :=
  inter_compl_nonempty_iff
#align set.nonempty_diff Set.nonempty_diff

theorem diff_subset (s t : Set α) : s \ t ⊆ s :=
  show s \ t ≤ s from sdiff_le
#align set.diff_subset Set.diff_subset

theorem union_diff_cancel' {s t u : Set α} (h₁ : s ⊆ t) (h₂ : t ⊆ u) : t ∪ u \ s = u :=
  sup_sdiff_cancel' h₁ h₂
#align set.union_diff_cancel' Set.union_diff_cancel'

theorem union_diff_cancel {s t : Set α} (h : s ⊆ t) : s ∪ t \ s = t :=
  sup_sdiff_cancel_right h
#align set.union_diff_cancel Set.union_diff_cancel

theorem union_diff_cancel_left {s t : Set α} (h : s ∩ t ⊆ ∅) : (s ∪ t) \ s = t :=
  Disjoint.sup_sdiff_cancel_left <| disjoint_iff_inf_le.2 h
#align set.union_diff_cancel_left Set.union_diff_cancel_left

theorem union_diff_cancel_right {s t : Set α} (h : s ∩ t ⊆ ∅) : (s ∪ t) \ t = s :=
  Disjoint.sup_sdiff_cancel_right <| disjoint_iff_inf_le.2 h
#align set.union_diff_cancel_right Set.union_diff_cancel_right

@[simp]
theorem union_diff_left {s t : Set α} : (s ∪ t) \ s = t \ s :=
  sup_sdiff_left_self
#align set.union_diff_left Set.union_diff_left

@[simp]
theorem union_diff_right {s t : Set α} : (s ∪ t) \ t = s \ t :=
  sup_sdiff_right_self
#align set.union_diff_right Set.union_diff_right

theorem union_diff_distrib {s t u : Set α} : (s ∪ t) \ u = s \ u ∪ t \ u :=
  sup_sdiff
#align set.union_diff_distrib Set.union_diff_distrib

theorem inter_diff_assoc (a b c : Set α) : (a ∩ b) \ c = a ∩ (b \ c) :=
  inf_sdiff_assoc
#align set.inter_diff_assoc Set.inter_diff_assoc

@[simp]
theorem inter_diff_self (a b : Set α) : a ∩ (b \ a) = ∅ :=
  inf_sdiff_self_right
#align set.inter_diff_self Set.inter_diff_self

@[simp]
theorem inter_union_diff (s t : Set α) : s ∩ t ∪ s \ t = s :=
  sup_inf_sdiff s t
#align set.inter_union_diff Set.inter_union_diff

@[simp]
theorem diff_union_inter (s t : Set α) : s \ t ∪ s ∩ t = s := by
  rw [union_comm]
  -- ⊢ s ∩ t ∪ s \ t = s
  exact sup_inf_sdiff _ _
  -- 🎉 no goals
#align set.diff_union_inter Set.diff_union_inter

@[simp]
theorem inter_union_compl (s t : Set α) : s ∩ t ∪ s ∩ tᶜ = s :=
  inter_union_diff _ _
#align set.inter_union_compl Set.inter_union_compl

theorem diff_subset_diff {s₁ s₂ t₁ t₂ : Set α} : s₁ ⊆ s₂ → t₂ ⊆ t₁ → s₁ \ t₁ ⊆ s₂ \ t₂ :=
  show s₁ ≤ s₂ → t₂ ≤ t₁ → s₁ \ t₁ ≤ s₂ \ t₂ from sdiff_le_sdiff
#align set.diff_subset_diff Set.diff_subset_diff

theorem diff_subset_diff_left {s₁ s₂ t : Set α} (h : s₁ ⊆ s₂) : s₁ \ t ⊆ s₂ \ t :=
  sdiff_le_sdiff_right ‹s₁ ≤ s₂›
#align set.diff_subset_diff_left Set.diff_subset_diff_left

theorem diff_subset_diff_right {s t u : Set α} (h : t ⊆ u) : s \ u ⊆ s \ t :=
  sdiff_le_sdiff_left ‹t ≤ u›
#align set.diff_subset_diff_right Set.diff_subset_diff_right

theorem compl_eq_univ_diff (s : Set α) : sᶜ = univ \ s :=
  top_sdiff.symm
#align set.compl_eq_univ_diff Set.compl_eq_univ_diff

@[simp]
theorem empty_diff (s : Set α) : (∅ \ s : Set α) = ∅ :=
  bot_sdiff
#align set.empty_diff Set.empty_diff

theorem diff_eq_empty {s t : Set α} : s \ t = ∅ ↔ s ⊆ t :=
  sdiff_eq_bot_iff
#align set.diff_eq_empty Set.diff_eq_empty

@[simp]
theorem diff_empty {s : Set α} : s \ ∅ = s :=
  sdiff_bot
#align set.diff_empty Set.diff_empty

@[simp]
theorem diff_univ (s : Set α) : s \ univ = ∅ :=
  diff_eq_empty.2 (subset_univ s)
#align set.diff_univ Set.diff_univ

theorem diff_diff {u : Set α} : (s \ t) \ u = s \ (t ∪ u) :=
  sdiff_sdiff_left
#align set.diff_diff Set.diff_diff

-- the following statement contains parentheses to help the reader
theorem diff_diff_comm {s t u : Set α} : (s \ t) \ u = (s \ u) \ t :=
  sdiff_sdiff_comm
#align set.diff_diff_comm Set.diff_diff_comm

theorem diff_subset_iff {s t u : Set α} : s \ t ⊆ u ↔ s ⊆ t ∪ u :=
  show s \ t ≤ u ↔ s ≤ t ∪ u from sdiff_le_iff
#align set.diff_subset_iff Set.diff_subset_iff

theorem subset_diff_union (s t : Set α) : s ⊆ s \ t ∪ t :=
  show s ≤ s \ t ∪ t from le_sdiff_sup
#align set.subset_diff_union Set.subset_diff_union

theorem diff_union_of_subset {s t : Set α} (h : t ⊆ s) : s \ t ∪ t = s :=
  Subset.antisymm (union_subset (diff_subset _ _) h) (subset_diff_union _ _)
#align set.diff_union_of_subset Set.diff_union_of_subset

@[simp]
theorem diff_singleton_subset_iff {x : α} {s t : Set α} : s \ {x} ⊆ t ↔ s ⊆ insert x t := by
  rw [← union_singleton, union_comm]
  -- ⊢ s \ {x} ⊆ t ↔ s ⊆ {x} ∪ t
  apply diff_subset_iff
  -- 🎉 no goals
#align set.diff_singleton_subset_iff Set.diff_singleton_subset_iff

theorem subset_diff_singleton {x : α} {s t : Set α} (h : s ⊆ t) (hx : x ∉ s) : s ⊆ t \ {x} :=
  subset_inter h <| subset_compl_comm.1 <| singleton_subset_iff.2 hx
#align set.subset_diff_singleton Set.subset_diff_singleton

theorem subset_insert_diff_singleton (x : α) (s : Set α) : s ⊆ insert x (s \ {x}) := by
  rw [← diff_singleton_subset_iff]
  -- 🎉 no goals
#align set.subset_insert_diff_singleton Set.subset_insert_diff_singleton

theorem diff_subset_comm {s t u : Set α} : s \ t ⊆ u ↔ s \ u ⊆ t :=
  show s \ t ≤ u ↔ s \ u ≤ t from sdiff_le_comm
#align set.diff_subset_comm Set.diff_subset_comm

theorem diff_inter {s t u : Set α} : s \ (t ∩ u) = s \ t ∪ s \ u :=
  sdiff_inf
#align set.diff_inter Set.diff_inter

theorem diff_inter_diff {s t u : Set α} : s \ t ∩ (s \ u) = s \ (t ∪ u) :=
  sdiff_sup.symm
#align set.diff_inter_diff Set.diff_inter_diff

theorem diff_compl : s \ tᶜ = s ∩ t :=
  sdiff_compl
#align set.diff_compl Set.diff_compl

theorem diff_diff_right {s t u : Set α} : s \ (t \ u) = s \ t ∪ s ∩ u :=
  sdiff_sdiff_right'
#align set.diff_diff_right Set.diff_diff_right

@[simp]
theorem insert_diff_of_mem (s) (h : a ∈ t) : insert a s \ t = s \ t := by
  ext
  -- ⊢ x✝ ∈ insert a s \ t ↔ x✝ ∈ s \ t
  constructor <;> simp (config := { contextual := true }) [or_imp, h]
  -- ⊢ x✝ ∈ insert a s \ t → x✝ ∈ s \ t
                  -- 🎉 no goals
                  -- 🎉 no goals
#align set.insert_diff_of_mem Set.insert_diff_of_mem

theorem insert_diff_of_not_mem (s) (h : a ∉ t) : insert a s \ t = insert a (s \ t) := by
  classical
    ext x
    by_cases h' : x ∈ t
    · have : x ≠ a := by
        intro H
        rw [H] at h'
        exact h h'
      simp [h, h', this]
    · simp [h, h']
#align set.insert_diff_of_not_mem Set.insert_diff_of_not_mem

theorem insert_diff_self_of_not_mem {a : α} {s : Set α} (h : a ∉ s) : insert a s \ {a} = s := by
  ext x
  -- ⊢ x ∈ insert a s \ {a} ↔ x ∈ s
  simp [and_iff_left_of_imp fun hx : x ∈ s => show x ≠ a from fun hxa => h <| hxa ▸ hx]
  -- 🎉 no goals
#align set.insert_diff_self_of_not_mem Set.insert_diff_self_of_not_mem

@[simp]
theorem insert_diff_eq_singleton {a : α} {s : Set α} (h : a ∉ s) : insert a s \ s = {a} := by
  ext
  -- ⊢ x✝ ∈ insert a s \ s ↔ x✝ ∈ {a}
  rw [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, or_and_right, and_not_self_iff,
    or_false_iff, and_iff_left_iff_imp]
  rintro rfl
  -- ⊢ ¬x✝ ∈ s
  exact h
  -- 🎉 no goals
#align set.insert_diff_eq_singleton Set.insert_diff_eq_singleton

theorem inter_insert_of_mem (h : a ∈ s) : s ∩ insert a t = insert a (s ∩ t) := by
  rw [insert_inter_distrib, insert_eq_of_mem h]
  -- 🎉 no goals
#align set.inter_insert_of_mem Set.inter_insert_of_mem

theorem insert_inter_of_mem (h : a ∈ t) : insert a s ∩ t = insert a (s ∩ t) := by
  rw [insert_inter_distrib, insert_eq_of_mem h]
  -- 🎉 no goals
#align set.insert_inter_of_mem Set.insert_inter_of_mem

theorem inter_insert_of_not_mem (h : a ∉ s) : s ∩ insert a t = s ∩ t :=
  ext fun _ => and_congr_right fun hx => or_iff_right <| ne_of_mem_of_not_mem hx h
#align set.inter_insert_of_not_mem Set.inter_insert_of_not_mem

theorem insert_inter_of_not_mem (h : a ∉ t) : insert a s ∩ t = s ∩ t :=
  ext fun _ => and_congr_left fun hx => or_iff_right <| ne_of_mem_of_not_mem hx h
#align set.insert_inter_of_not_mem Set.insert_inter_of_not_mem

@[simp]
theorem union_diff_self {s t : Set α} : s ∪ t \ s = s ∪ t :=
  sup_sdiff_self _ _
#align set.union_diff_self Set.union_diff_self

@[simp]
theorem diff_union_self {s t : Set α} : s \ t ∪ t = s ∪ t :=
  sdiff_sup_self _ _
#align set.diff_union_self Set.diff_union_self

@[simp]
theorem diff_inter_self {a b : Set α} : b \ a ∩ a = ∅ :=
  inf_sdiff_self_left
#align set.diff_inter_self Set.diff_inter_self

@[simp]
theorem diff_inter_self_eq_diff {s t : Set α} : s \ (t ∩ s) = s \ t :=
  sdiff_inf_self_right _ _
#align set.diff_inter_self_eq_diff Set.diff_inter_self_eq_diff

@[simp]
theorem diff_self_inter {s t : Set α} : s \ (s ∩ t) = s \ t :=
  sdiff_inf_self_left _ _
#align set.diff_self_inter Set.diff_self_inter

@[simp]
theorem diff_singleton_eq_self {a : α} {s : Set α} (h : a ∉ s) : s \ {a} = s :=
  sdiff_eq_self_iff_disjoint.2 $ by simp [h]
                                    -- 🎉 no goals
#align set.diff_singleton_eq_self Set.diff_singleton_eq_self

@[simp]
theorem diff_singleton_sSubset {s : Set α} {a : α} : s \ {a} ⊂ s ↔ a ∈ s :=
  sdiff_le.lt_iff_ne.trans <| sdiff_eq_left.not.trans <| by simp
                                                            -- 🎉 no goals
#align set.diff_singleton_ssubset Set.diff_singleton_sSubset

@[simp]
theorem insert_diff_singleton {a : α} {s : Set α} : insert a (s \ {a}) = insert a s := by
  simp [insert_eq, union_diff_self, -union_singleton, -singleton_union]
  -- 🎉 no goals
#align set.insert_diff_singleton Set.insert_diff_singleton

theorem insert_diff_singleton_comm (hab : a ≠ b) (s : Set α) :
    insert a (s \ {b}) = insert a s \ {b} := by
  simp_rw [← union_singleton, union_diff_distrib,
    diff_singleton_eq_self (mem_singleton_iff.not.2 hab.symm)]
#align set.insert_diff_singleton_comm Set.insert_diff_singleton_comm

--Porting note: removed `simp` attribute because `simp` can prove it
theorem diff_self {s : Set α} : s \ s = ∅ :=
  sdiff_self
#align set.diff_self Set.diff_self

theorem diff_diff_right_self (s t : Set α) : s \ (s \ t) = s ∩ t :=
  sdiff_sdiff_right_self
#align set.diff_diff_right_self Set.diff_diff_right_self

theorem diff_diff_cancel_left {s t : Set α} (h : s ⊆ t) : t \ (t \ s) = s :=
  sdiff_sdiff_eq_self h
#align set.diff_diff_cancel_left Set.diff_diff_cancel_left

theorem mem_diff_singleton {x y : α} {s : Set α} : x ∈ s \ {y} ↔ x ∈ s ∧ x ≠ y :=
  Iff.rfl
#align set.mem_diff_singleton Set.mem_diff_singleton

theorem mem_diff_singleton_empty {t : Set (Set α)} : s ∈ t \ {∅} ↔ s ∈ t ∧ s.Nonempty :=
  mem_diff_singleton.trans <| and_congr_right' nonempty_iff_ne_empty.symm
#align set.mem_diff_singleton_empty Set.mem_diff_singleton_empty

theorem union_eq_diff_union_diff_union_inter (s t : Set α) : s ∪ t = s \ t ∪ t \ s ∪ s ∩ t :=
  sup_eq_sdiff_sup_sdiff_sup_inf
#align set.union_eq_diff_union_diff_union_inter Set.union_eq_diff_union_diff_union_inter

/-! ### Symmetric difference -/


theorem mem_symmDiff : a ∈ s ∆ t ↔ a ∈ s ∧ a ∉ t ∨ a ∈ t ∧ a ∉ s :=
  Iff.rfl
#align set.mem_symm_diff Set.mem_symmDiff

protected theorem symmDiff_def (s t : Set α) : s ∆ t = s \ t ∪ t \ s :=
  rfl
#align set.symm_diff_def Set.symmDiff_def

theorem symmDiff_subset_union : s ∆ t ⊆ s ∪ t :=
  @symmDiff_le_sup (Set α) _ _ _
#align set.symm_diff_subset_union Set.symmDiff_subset_union

@[simp]
theorem symmDiff_eq_empty : s ∆ t = ∅ ↔ s = t :=
  symmDiff_eq_bot
#align set.symm_diff_eq_empty Set.symmDiff_eq_empty

@[simp]
theorem symmDiff_nonempty : (s ∆ t).Nonempty ↔ s ≠ t :=
  nonempty_iff_ne_empty.trans symmDiff_eq_empty.not
#align set.symm_diff_nonempty Set.symmDiff_nonempty

theorem inter_symmDiff_distrib_left (s t u : Set α) : s ∩ t ∆ u = (s ∩ t) ∆ (s ∩ u) :=
  inf_symmDiff_distrib_left _ _ _
#align set.inter_symm_diff_distrib_left Set.inter_symmDiff_distrib_left

theorem inter_symmDiff_distrib_right (s t u : Set α) : s ∆ t ∩ u = (s ∩ u) ∆ (t ∩ u) :=
  inf_symmDiff_distrib_right _ _ _
#align set.inter_symm_diff_distrib_right Set.inter_symmDiff_distrib_right

theorem subset_symmDiff_union_symmDiff_left (h : Disjoint s t) : u ⊆ s ∆ u ∪ t ∆ u :=
  h.le_symmDiff_sup_symmDiff_left
#align set.subset_symm_diff_union_symm_diff_left Set.subset_symmDiff_union_symmDiff_left

theorem subset_symmDiff_union_symmDiff_right (h : Disjoint t u) : s ⊆ s ∆ t ∪ s ∆ u :=
  h.le_symmDiff_sup_symmDiff_right
#align set.subset_symm_diff_union_symm_diff_right Set.subset_symmDiff_union_symmDiff_right

/-! ### Powerset -/

#align set.powerset Set.powerset

theorem mem_powerset {x s : Set α} (h : x ⊆ s) : x ∈ 𝒫 s := @h
#align set.mem_powerset Set.mem_powerset

theorem subset_of_mem_powerset {x s : Set α} (h : x ∈ 𝒫 s) : x ⊆ s := @h
#align set.subset_of_mem_powerset Set.subset_of_mem_powerset

@[simp]
theorem mem_powerset_iff (x s : Set α) : x ∈ 𝒫 s ↔ x ⊆ s :=
  Iff.rfl
#align set.mem_powerset_iff Set.mem_powerset_iff

theorem powerset_inter (s t : Set α) : 𝒫(s ∩ t) = 𝒫 s ∩ 𝒫 t :=
  ext fun _ => subset_inter_iff
#align set.powerset_inter Set.powerset_inter

@[simp]
theorem powerset_mono : 𝒫 s ⊆ 𝒫 t ↔ s ⊆ t :=
  ⟨fun h => @h _ (fun _ h => h), fun h _ hu _ ha => h (hu ha)⟩
#align set.powerset_mono Set.powerset_mono

theorem monotone_powerset : Monotone (powerset : Set α → Set (Set α)) := fun _ _ => powerset_mono.2
#align set.monotone_powerset Set.monotone_powerset

@[simp]
theorem powerset_nonempty : (𝒫 s).Nonempty :=
  ⟨∅, fun _ h => empty_subset s h⟩
#align set.powerset_nonempty Set.powerset_nonempty

@[simp]
theorem powerset_empty : 𝒫(∅ : Set α) = {∅} :=
  ext fun _ => subset_empty_iff
#align set.powerset_empty Set.powerset_empty

@[simp]
theorem powerset_univ : 𝒫(univ : Set α) = univ :=
  eq_univ_of_forall subset_univ
#align set.powerset_univ Set.powerset_univ

/-- The powerset of a singleton contains only `∅` and the singleton itself. -/
theorem powerset_singleton (x : α) : 𝒫({x} : Set α) = {∅, {x}} := by
  ext y
  -- ⊢ y ∈ 𝒫{x} ↔ y ∈ {∅, {x}}
  rw [mem_powerset_iff, subset_singleton_iff_eq, mem_insert_iff, mem_singleton_iff]
  -- 🎉 no goals
#align set.powerset_singleton Set.powerset_singleton

/-! ### Sets defined as an if-then-else -/

--Porting note: New theorem to prove `mem_dite` lemmas.
-- `simp [h]` where `h : p` does not simplify `∀ (h : p), x ∈ s h` any more.
-- https://github.com/leanprover/lean4/issues/1926
theorem mem_dite (p : Prop) [Decidable p] (s : p → Set α) (t : ¬ p → Set α) (x : α) :
    (x ∈ if h : p then s h else t h) ↔ (∀ h : p, x ∈ s h) ∧ ∀ h : ¬p, x ∈ t h := by
  split_ifs with hp
  -- ⊢ x ∈ s hp ↔ (∀ (h : p), x ∈ s h) ∧ ∀ (h : ¬p), x ∈ t h
  · exact ⟨fun hx => ⟨fun _ => hx, fun hnp => (hnp hp).elim⟩, fun hx => hx.1 hp⟩
    -- 🎉 no goals
  · exact ⟨fun hx => ⟨fun h => (hp h).elim, fun _ => hx⟩, fun hx => hx.2 hp⟩
    -- 🎉 no goals

--Porting note: Old proof was `split_ifs; simp [h]`
theorem mem_dite_univ_right (p : Prop) [Decidable p] (t : p → Set α) (x : α) :
    (x ∈ if h : p then t h else univ) ↔ ∀ h : p, x ∈ t h := by
  simp [mem_dite]
  -- 🎉 no goals
#align set.mem_dite_univ_right Set.mem_dite_univ_right

@[simp]
theorem mem_ite_univ_right (p : Prop) [Decidable p] (t : Set α) (x : α) :
    x ∈ ite p t Set.univ ↔ p → x ∈ t :=
  mem_dite_univ_right p (fun _ => t) x
#align set.mem_ite_univ_right Set.mem_ite_univ_right

theorem mem_dite_univ_left (p : Prop) [Decidable p] (t : ¬p → Set α) (x : α) :
    (x ∈ if h : p then univ else t h) ↔ ∀ h : ¬p, x ∈ t h := by
  simp [mem_dite]
  -- 🎉 no goals
#align set.mem_dite_univ_left Set.mem_dite_univ_left

@[simp]
theorem mem_ite_univ_left (p : Prop) [Decidable p] (t : Set α) (x : α) :
    x ∈ ite p Set.univ t ↔ ¬p → x ∈ t :=
  mem_dite_univ_left p (fun _ => t) x
#align set.mem_ite_univ_left Set.mem_ite_univ_left

theorem mem_dite_empty_right (p : Prop) [Decidable p] (t : p → Set α) (x : α) :
    (x ∈ if h : p then t h else ∅) ↔ ∃ h : p, x ∈ t h := by
  simp only [mem_dite, mem_empty_iff_false, imp_false, not_not]
  -- ⊢ (∀ (h : p), x ∈ t h) ∧ p ↔ ∃ h, x ∈ t h
  exact ⟨fun h => ⟨h.2, h.1 h.2⟩, fun ⟨h₁, h₂⟩ => ⟨fun _ => h₂, h₁⟩⟩
  -- 🎉 no goals
#align set.mem_dite_empty_right Set.mem_dite_empty_right

@[simp]
theorem mem_ite_empty_right (p : Prop) [Decidable p] (t : Set α) (x : α) :
    x ∈ ite p t ∅ ↔ p ∧ x ∈ t :=
  (mem_dite_empty_right p (fun _ => t) x).trans (by simp)
                                                    -- 🎉 no goals
#align set.mem_ite_empty_right Set.mem_ite_empty_right

theorem mem_dite_empty_left (p : Prop) [Decidable p] (t : ¬p → Set α) (x : α) :
    (x ∈ if h : p then ∅ else t h) ↔ ∃ h : ¬p, x ∈ t h := by
  simp only [mem_dite, mem_empty_iff_false, imp_false]
  -- ⊢ (¬p ∧ ∀ (h : ¬p), x ∈ t h) ↔ ∃ h, x ∈ t h
  exact ⟨fun h => ⟨h.1, h.2 h.1⟩, fun ⟨h₁, h₂⟩ => ⟨fun h => h₁ h, fun _ => h₂⟩⟩
  -- 🎉 no goals
#align set.mem_dite_empty_left Set.mem_dite_empty_left

@[simp]
theorem mem_ite_empty_left (p : Prop) [Decidable p] (t : Set α) (x : α) :
    x ∈ ite p ∅ t ↔ ¬p ∧ x ∈ t :=
  (mem_dite_empty_left p (fun _ => t) x).trans (by simp)
                                                   -- 🎉 no goals
#align set.mem_ite_empty_left Set.mem_ite_empty_left

/-! ### If-then-else for sets -/


/-- `ite` for sets: `Set.ite t s s' ∩ t = s ∩ t`, `Set.ite t s s' ∩ tᶜ = s' ∩ tᶜ`.
Defined as `s ∩ t ∪ s' \ t`. -/
protected def ite (t s s' : Set α) : Set α :=
  s ∩ t ∪ s' \ t
#align set.ite Set.ite

@[simp]
theorem ite_inter_self (t s s' : Set α) : t.ite s s' ∩ t = s ∩ t := by
  rw [Set.ite, union_inter_distrib_right, diff_inter_self, inter_assoc, inter_self, union_empty]
  -- 🎉 no goals
#align set.ite_inter_self Set.ite_inter_self

@[simp]
theorem ite_compl (t s s' : Set α) : tᶜ.ite s s' = t.ite s' s := by
  rw [Set.ite, Set.ite, diff_compl, union_comm, diff_eq]
  -- 🎉 no goals
#align set.ite_compl Set.ite_compl

@[simp]
theorem ite_inter_compl_self (t s s' : Set α) : t.ite s s' ∩ tᶜ = s' ∩ tᶜ := by
  rw [← ite_compl, ite_inter_self]
  -- 🎉 no goals
#align set.ite_inter_compl_self Set.ite_inter_compl_self

@[simp]
theorem ite_diff_self (t s s' : Set α) : t.ite s s' \ t = s' \ t :=
  ite_inter_compl_self t s s'
#align set.ite_diff_self Set.ite_diff_self

@[simp]
theorem ite_same (t s : Set α) : t.ite s s = s :=
  inter_union_diff _ _
#align set.ite_same Set.ite_same

@[simp]
theorem ite_left (s t : Set α) : s.ite s t = s ∪ t := by simp [Set.ite]
                                                         -- 🎉 no goals
#align set.ite_left Set.ite_left

@[simp]
theorem ite_right (s t : Set α) : s.ite t s = t ∩ s := by simp [Set.ite]
                                                          -- 🎉 no goals
#align set.ite_right Set.ite_right

@[simp]
theorem ite_empty (s s' : Set α) : Set.ite ∅ s s' = s' := by simp [Set.ite]
                                                             -- 🎉 no goals
#align set.ite_empty Set.ite_empty

@[simp]
theorem ite_univ (s s' : Set α) : Set.ite univ s s' = s := by simp [Set.ite]
                                                              -- 🎉 no goals
#align set.ite_univ Set.ite_univ

@[simp]
theorem ite_empty_left (t s : Set α) : t.ite ∅ s = s \ t := by simp [Set.ite]
                                                               -- 🎉 no goals
#align set.ite_empty_left Set.ite_empty_left

@[simp]
theorem ite_empty_right (t s : Set α) : t.ite s ∅ = s ∩ t := by simp [Set.ite]
                                                                -- 🎉 no goals
#align set.ite_empty_right Set.ite_empty_right

theorem ite_mono (t : Set α) {s₁ s₁' s₂ s₂' : Set α} (h : s₁ ⊆ s₂) (h' : s₁' ⊆ s₂') :
    t.ite s₁ s₁' ⊆ t.ite s₂ s₂' :=
  union_subset_union (inter_subset_inter_left _ h) (inter_subset_inter_left _ h')
#align set.ite_mono Set.ite_mono

theorem ite_subset_union (t s s' : Set α) : t.ite s s' ⊆ s ∪ s' :=
  union_subset_union (inter_subset_left _ _) (diff_subset _ _)
#align set.ite_subset_union Set.ite_subset_union

theorem inter_subset_ite (t s s' : Set α) : s ∩ s' ⊆ t.ite s s' :=
  ite_same t (s ∩ s') ▸ ite_mono _ (inter_subset_left _ _) (inter_subset_right _ _)
#align set.inter_subset_ite Set.inter_subset_ite

theorem ite_inter_inter (t s₁ s₂ s₁' s₂' : Set α) :
    t.ite (s₁ ∩ s₂) (s₁' ∩ s₂') = t.ite s₁ s₁' ∩ t.ite s₂ s₂' := by
  ext x
  -- ⊢ x ∈ Set.ite t (s₁ ∩ s₂) (s₁' ∩ s₂') ↔ x ∈ Set.ite t s₁ s₁' ∩ Set.ite t s₂ s₂'
  simp only [Set.ite, Set.mem_inter_iff, Set.mem_diff, Set.mem_union]
  -- ⊢ (x ∈ s₁ ∧ x ∈ s₂) ∧ x ∈ t ∨ (x ∈ s₁' ∧ x ∈ s₂') ∧ ¬x ∈ t ↔ (x ∈ s₁ ∧ x ∈ t ∨ …
  tauto
  -- 🎉 no goals
#align set.ite_inter_inter Set.ite_inter_inter

theorem ite_inter (t s₁ s₂ s : Set α) : t.ite (s₁ ∩ s) (s₂ ∩ s) = t.ite s₁ s₂ ∩ s := by
  rw [ite_inter_inter, ite_same]
  -- 🎉 no goals
#align set.ite_inter Set.ite_inter

theorem ite_inter_of_inter_eq (t : Set α) {s₁ s₂ s : Set α} (h : s₁ ∩ s = s₂ ∩ s) :
    t.ite s₁ s₂ ∩ s = s₁ ∩ s := by rw [← ite_inter, ← h, ite_same]
                                   -- 🎉 no goals
#align set.ite_inter_of_inter_eq Set.ite_inter_of_inter_eq

theorem subset_ite {t s s' u : Set α} : u ⊆ t.ite s s' ↔ u ∩ t ⊆ s ∧ u \ t ⊆ s' := by
  simp only [subset_def, ← forall_and]
  -- ⊢ (∀ (x : α), x ∈ u → x ∈ Set.ite t s s') ↔ ∀ (x : α), (x ∈ u ∩ t → x ∈ s) ∧ ( …
  refine' forall_congr' fun x => _
  -- ⊢ x ∈ u → x ∈ Set.ite t s s' ↔ (x ∈ u ∩ t → x ∈ s) ∧ (x ∈ u \ t → x ∈ s')
  by_cases hx : x ∈ t <;> simp [*, Set.ite]
  -- ⊢ x ∈ u → x ∈ Set.ite t s s' ↔ (x ∈ u ∩ t → x ∈ s) ∧ (x ∈ u \ t → x ∈ s')
                          -- 🎉 no goals
                          -- 🎉 no goals
#align set.subset_ite Set.subset_ite

/-! ### Subsingleton -/


/-- A set `s` is a `Subsingleton` if it has at most one element. -/
protected def Subsingleton (s : Set α) : Prop :=
  ∀ ⦃x⦄ (_ : x ∈ s) ⦃y⦄ (_ : y ∈ s), x = y
#align set.subsingleton Set.Subsingleton

theorem Subsingleton.anti (ht : t.Subsingleton) (hst : s ⊆ t) : s.Subsingleton := fun _ hx _ hy =>
  ht (hst hx) (hst hy)
#align set.subsingleton.anti Set.Subsingleton.anti

theorem Subsingleton.eq_singleton_of_mem (hs : s.Subsingleton) {x : α} (hx : x ∈ s) : s = {x} :=
  ext fun _ => ⟨fun hy => hs hx hy ▸ mem_singleton _, fun hy => (eq_of_mem_singleton hy).symm ▸ hx⟩
#align set.subsingleton.eq_singleton_of_mem Set.Subsingleton.eq_singleton_of_mem

@[simp]
theorem subsingleton_empty : (∅ : Set α).Subsingleton := fun _ => False.elim
#align set.subsingleton_empty Set.subsingleton_empty

@[simp]
theorem subsingleton_singleton {a} : ({a} : Set α).Subsingleton := fun _ hx _ hy =>
  (eq_of_mem_singleton hx).symm ▸ (eq_of_mem_singleton hy).symm ▸ rfl
#align set.subsingleton_singleton Set.subsingleton_singleton

theorem subsingleton_of_subset_singleton (h : s ⊆ {a}) : s.Subsingleton :=
  subsingleton_singleton.anti h
#align set.subsingleton_of_subset_singleton Set.subsingleton_of_subset_singleton

theorem subsingleton_of_forall_eq (a : α) (h : ∀ b ∈ s, b = a) : s.Subsingleton := fun _ hb _ hc =>
  (h _ hb).trans (h _ hc).symm
#align set.subsingleton_of_forall_eq Set.subsingleton_of_forall_eq

theorem subsingleton_iff_singleton {x} (hx : x ∈ s) : s.Subsingleton ↔ s = {x} :=
  ⟨fun h => h.eq_singleton_of_mem hx, fun h => h.symm ▸ subsingleton_singleton⟩
#align set.subsingleton_iff_singleton Set.subsingleton_iff_singleton

theorem Subsingleton.eq_empty_or_singleton (hs : s.Subsingleton) : s = ∅ ∨ ∃ x, s = {x} :=
  s.eq_empty_or_nonempty.elim Or.inl fun ⟨x, hx⟩ => Or.inr ⟨x, hs.eq_singleton_of_mem hx⟩
#align set.subsingleton.eq_empty_or_singleton Set.Subsingleton.eq_empty_or_singleton

theorem Subsingleton.induction_on {p : Set α → Prop} (hs : s.Subsingleton) (he : p ∅)
    (h₁ : ∀ x, p {x}) : p s := by
  rcases hs.eq_empty_or_singleton with (rfl | ⟨x, rfl⟩)
  -- ⊢ p ∅
  exacts [he, h₁ _]
  -- 🎉 no goals
#align set.subsingleton.induction_on Set.Subsingleton.induction_on

theorem subsingleton_univ [Subsingleton α] : (univ : Set α).Subsingleton := fun x _ y _ =>
  Subsingleton.elim x y
#align set.subsingleton_univ Set.subsingleton_univ

theorem subsingleton_of_univ_subsingleton (h : (univ : Set α).Subsingleton) : Subsingleton α :=
  ⟨fun a b => h (mem_univ a) (mem_univ b)⟩
#align set.subsingleton_of_univ_subsingleton Set.subsingleton_of_univ_subsingleton

@[simp]
theorem subsingleton_univ_iff : (univ : Set α).Subsingleton ↔ Subsingleton α :=
  ⟨subsingleton_of_univ_subsingleton, fun h => @subsingleton_univ _ h⟩
#align set.subsingleton_univ_iff Set.subsingleton_univ_iff

theorem subsingleton_of_subsingleton [Subsingleton α] {s : Set α} : Set.Subsingleton s :=
  subsingleton_univ.anti (subset_univ s)
#align set.subsingleton_of_subsingleton Set.subsingleton_of_subsingleton

theorem subsingleton_isTop (α : Type*) [PartialOrder α] : Set.Subsingleton { x : α | IsTop x } :=
  fun x hx _ hy => hx.isMax.eq_of_le (hy x)
#align set.subsingleton_is_top Set.subsingleton_isTop

theorem subsingleton_isBot (α : Type*) [PartialOrder α] : Set.Subsingleton { x : α | IsBot x } :=
  fun x hx _ hy => hx.isMin.eq_of_ge (hy x)
#align set.subsingleton_is_bot Set.subsingleton_isBot

theorem exists_eq_singleton_iff_nonempty_subsingleton :
    (∃ a : α, s = {a}) ↔ s.Nonempty ∧ s.Subsingleton := by
  refine' ⟨_, fun h => _⟩
  -- ⊢ (∃ a, s = {a}) → Set.Nonempty s ∧ Set.Subsingleton s
  · rintro ⟨a, rfl⟩
    -- ⊢ Set.Nonempty {a} ∧ Set.Subsingleton {a}
    exact ⟨singleton_nonempty a, subsingleton_singleton⟩
    -- 🎉 no goals
  · exact h.2.eq_empty_or_singleton.resolve_left h.1.ne_empty
    -- 🎉 no goals
#align set.exists_eq_singleton_iff_nonempty_subsingleton Set.exists_eq_singleton_iff_nonempty_subsingleton

/-- `s`, coerced to a type, is a subsingleton type if and only if `s` is a subsingleton set. -/
@[simp, norm_cast]
theorem subsingleton_coe (s : Set α) : Subsingleton s ↔ s.Subsingleton := by
  constructor
  -- ⊢ Subsingleton ↑s → Set.Subsingleton s
  · refine' fun h => fun a ha b hb => _
    -- ⊢ a = b
    exact SetCoe.ext_iff.2 (@Subsingleton.elim s h ⟨a, ha⟩ ⟨b, hb⟩)
    -- 🎉 no goals
  · exact fun h => Subsingleton.intro fun a b => SetCoe.ext (h a.property b.property)
    -- 🎉 no goals
#align set.subsingleton_coe Set.subsingleton_coe

theorem Subsingleton.coe_sort {s : Set α} : s.Subsingleton → Subsingleton s :=
  s.subsingleton_coe.2
#align set.subsingleton.coe_sort Set.Subsingleton.coe_sort

/-- The `coe_sort` of a set `s` in a subsingleton type is a subsingleton.
For the corresponding result for `Subtype`, see `subtype.subsingleton`. -/
instance subsingleton_coe_of_subsingleton [Subsingleton α] {s : Set α} : Subsingleton s := by
  rw [s.subsingleton_coe]
  -- ⊢ Set.Subsingleton s
  exact subsingleton_of_subsingleton
  -- 🎉 no goals
#align set.subsingleton_coe_of_subsingleton Set.subsingleton_coe_of_subsingleton

/-! ### Nontrivial -/

/-- A set `s` is `Set.Nontrivial` if it has at least two distinct elements. -/
protected def Nontrivial (s : Set α) : Prop :=
  ∃ (x : α) (_ : x ∈ s) (y : α) (_ : y ∈ s), x ≠ y
#align set.nontrivial Set.Nontrivial

theorem nontrivial_of_mem_mem_ne {x y} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) : s.Nontrivial :=
  ⟨x, hx, y, hy, hxy⟩
#align set.nontrivial_of_mem_mem_ne Set.nontrivial_of_mem_mem_ne

-- Porting note: following the pattern for `Exists`, we have renamed `some` to `choose`.

/-- Extract witnesses from s.nontrivial. This function might be used instead of case analysis on the
argument. Note that it makes a proof depend on the classical.choice axiom. -/
protected noncomputable def Nontrivial.choose (hs : s.Nontrivial) : α × α :=
  (Exists.choose hs, hs.choose_spec.choose_spec.choose)
#align set.nontrivial.some Set.Nontrivial.choose

protected theorem Nontrivial.choose_fst_mem (hs : s.Nontrivial) : hs.choose.fst ∈ s :=
  hs.choose_spec.choose
#align set.nontrivial.some_fst_mem Set.Nontrivial.choose_fst_mem

protected theorem Nontrivial.choose_snd_mem (hs : s.Nontrivial) : hs.choose.snd ∈ s :=
  hs.choose_spec.choose_spec.choose_spec.choose
#align set.nontrivial.some_snd_mem Set.Nontrivial.choose_snd_mem

protected theorem Nontrivial.choose_fst_ne_choose_snd (hs : s.Nontrivial) :
    hs.choose.fst ≠ hs.choose.snd :=
  hs.choose_spec.choose_spec.choose_spec.choose_spec
#align set.nontrivial.some_fst_ne_some_snd Set.Nontrivial.choose_fst_ne_choose_snd

theorem Nontrivial.mono (hs : s.Nontrivial) (hst : s ⊆ t) : t.Nontrivial :=
  let ⟨x, hx, y, hy, hxy⟩ := hs
  ⟨x, hst hx, y, hst hy, hxy⟩
#align set.nontrivial.mono Set.Nontrivial.mono

theorem nontrivial_pair {x y} (hxy : x ≠ y) : ({x, y} : Set α).Nontrivial :=
  ⟨x, mem_insert _ _, y, mem_insert_of_mem _ (mem_singleton _), hxy⟩
#align set.nontrivial_pair Set.nontrivial_pair

theorem nontrivial_of_pair_subset {x y} (hxy : x ≠ y) (h : {x, y} ⊆ s) : s.Nontrivial :=
  (nontrivial_pair hxy).mono h
#align set.nontrivial_of_pair_subset Set.nontrivial_of_pair_subset

theorem Nontrivial.pair_subset (hs : s.Nontrivial) : ∃ (x y : _) (_ : x ≠ y), {x, y} ⊆ s :=
  let ⟨x, hx, y, hy, hxy⟩ := hs
  ⟨x, y, hxy, insert_subset_iff.2 ⟨hx, singleton_subset_iff.2 hy⟩⟩
#align set.nontrivial.pair_subset Set.Nontrivial.pair_subset

theorem nontrivial_iff_pair_subset : s.Nontrivial ↔ ∃ (x y : _) (_ : x ≠ y), {x, y} ⊆ s :=
  ⟨Nontrivial.pair_subset, fun H =>
    let ⟨_, _, hxy, h⟩ := H
    nontrivial_of_pair_subset hxy h⟩
#align set.nontrivial_iff_pair_subset Set.nontrivial_iff_pair_subset

theorem nontrivial_of_exists_ne {x} (hx : x ∈ s) (h : ∃ y ∈ s, y ≠ x) : s.Nontrivial :=
  let ⟨y, hy, hyx⟩ := h
  ⟨y, hy, x, hx, hyx⟩
#align set.nontrivial_of_exists_ne Set.nontrivial_of_exists_ne

theorem Nontrivial.exists_ne (hs : s.Nontrivial) (z) : ∃ x ∈ s, x ≠ z := by
  by_contra' H
  -- ⊢ False
  rcases hs with ⟨x, hx, y, hy, hxy⟩
  -- ⊢ False
  rw [H x hx, H y hy] at hxy
  -- ⊢ False
  exact hxy rfl
  -- 🎉 no goals
#align set.nontrivial.exists_ne Set.Nontrivial.exists_ne

theorem nontrivial_iff_exists_ne {x} (hx : x ∈ s) : s.Nontrivial ↔ ∃ y ∈ s, y ≠ x :=
  ⟨fun H => H.exists_ne _, nontrivial_of_exists_ne hx⟩
#align set.nontrivial_iff_exists_ne Set.nontrivial_iff_exists_ne

theorem nontrivial_of_lt [Preorder α] {x y} (hx : x ∈ s) (hy : y ∈ s) (hxy : x < y) :
    s.Nontrivial :=
  ⟨x, hx, y, hy, ne_of_lt hxy⟩
#align set.nontrivial_of_lt Set.nontrivial_of_lt

theorem nontrivial_of_exists_lt [Preorder α]
    (H : ∃ (x : α) (_ : x ∈ s) (y : α) (_ : y ∈ s), x < y) : s.Nontrivial :=
  let ⟨_, hx, _, hy, hxy⟩ := H
  nontrivial_of_lt hx hy hxy
#align set.nontrivial_of_exists_lt Set.nontrivial_of_exists_lt

theorem Nontrivial.exists_lt [LinearOrder α] (hs : s.Nontrivial) :
    ∃ (x : α) (_ : x ∈ s) (y : α) (_ : y ∈ s), x < y :=
  let ⟨x, hx, y, hy, hxy⟩ := hs
  Or.elim (lt_or_gt_of_ne hxy) (fun H => ⟨x, hx, y, hy, H⟩) fun H => ⟨y, hy, x, hx, H⟩
#align set.nontrivial.exists_lt Set.Nontrivial.exists_lt

theorem nontrivial_iff_exists_lt [LinearOrder α] :
    s.Nontrivial ↔ ∃ (x : α) (_ : x ∈ s) (y : α) (_ : y ∈ s), x < y :=
  ⟨Nontrivial.exists_lt, nontrivial_of_exists_lt⟩
#align set.nontrivial_iff_exists_lt Set.nontrivial_iff_exists_lt

protected theorem Nontrivial.nonempty (hs : s.Nontrivial) : s.Nonempty :=
  let ⟨x, hx, _⟩ := hs
  ⟨x, hx⟩
#align set.nontrivial.nonempty Set.Nontrivial.nonempty

protected theorem Nontrivial.ne_empty (hs : s.Nontrivial) : s ≠ ∅ :=
  hs.nonempty.ne_empty
#align set.nontrivial.ne_empty Set.Nontrivial.ne_empty

theorem Nontrivial.not_subset_empty (hs : s.Nontrivial) : ¬s ⊆ ∅ :=
  hs.nonempty.not_subset_empty
#align set.nontrivial.not_subset_empty Set.Nontrivial.not_subset_empty

@[simp]
theorem not_nontrivial_empty : ¬(∅ : Set α).Nontrivial := fun h => h.ne_empty rfl
#align set.not_nontrivial_empty Set.not_nontrivial_empty

@[simp]
theorem not_nontrivial_singleton {x} : ¬({x} : Set α).Nontrivial := fun H => by
  rw [nontrivial_iff_exists_ne (mem_singleton x)] at H
  -- ⊢ False
  let ⟨y, hy, hya⟩ := H
  -- ⊢ False
  exact hya (mem_singleton_iff.1 hy)
  -- 🎉 no goals
#align set.not_nontrivial_singleton Set.not_nontrivial_singleton

theorem Nontrivial.ne_singleton {x} (hs : s.Nontrivial) : s ≠ {x} := fun H => by
  rw [H] at hs
  -- ⊢ False
  exact not_nontrivial_singleton hs
  -- 🎉 no goals
#align set.nontrivial.ne_singleton Set.Nontrivial.ne_singleton

theorem Nontrivial.not_subset_singleton {x} (hs : s.Nontrivial) : ¬s ⊆ {x} :=
  (not_congr subset_singleton_iff_eq).2 (not_or_of_not hs.ne_empty hs.ne_singleton)
#align set.nontrivial.not_subset_singleton Set.Nontrivial.not_subset_singleton

theorem nontrivial_univ [Nontrivial α] : (univ : Set α).Nontrivial :=
  let ⟨x, y, hxy⟩ := exists_pair_ne α
  ⟨x, mem_univ _, y, mem_univ _, hxy⟩
#align set.nontrivial_univ Set.nontrivial_univ

theorem nontrivial_of_univ_nontrivial (h : (univ : Set α).Nontrivial) : Nontrivial α :=
  let ⟨x, _, y, _, hxy⟩ := h
  ⟨⟨x, y, hxy⟩⟩
#align set.nontrivial_of_univ_nontrivial Set.nontrivial_of_univ_nontrivial

@[simp]
theorem nontrivial_univ_iff : (univ : Set α).Nontrivial ↔ Nontrivial α :=
  ⟨nontrivial_of_univ_nontrivial, fun h => @nontrivial_univ _ h⟩
#align set.nontrivial_univ_iff Set.nontrivial_univ_iff

theorem nontrivial_of_nontrivial (hs : s.Nontrivial) : Nontrivial α :=
  let ⟨x, _, y, _, hxy⟩ := hs
  ⟨⟨x, y, hxy⟩⟩
#align set.nontrivial_of_nontrivial Set.nontrivial_of_nontrivial

-- Porting note: simp_rw broken here
-- Perhaps review after https://github.com/leanprover/lean4/issues/1937?
/-- `s`, coerced to a type, is a nontrivial type if and only if `s` is a nontrivial set. -/
@[simp, norm_cast]
theorem nontrivial_coe_sort {s : Set α} : Nontrivial s ↔ s.Nontrivial := by
  -- simp_rw [← nontrivial_univ_iff, Set.Nontrivial, mem_univ, exists_true_left, SetCoe.exists,
  --   Subtype.mk_eq_mk]
  rw [← nontrivial_univ_iff, Set.Nontrivial, Set.Nontrivial]
  -- ⊢ (∃ x x_1 y x_2, x ≠ y) ↔ ∃ x x_1 y x_2, x ≠ y
  apply Iff.intro
  -- ⊢ (∃ x x_1 y x_2, x ≠ y) → ∃ x x_1 y x_2, x ≠ y
  · rintro ⟨x, _, y, _, hxy⟩
    -- ⊢ ∃ x x_1 y x_2, x ≠ y
    exact ⟨x, Subtype.prop x, y, Subtype.prop y, fun h => hxy (Subtype.coe_injective h)⟩
    -- 🎉 no goals
  · rintro ⟨x, hx, y, hy, hxy⟩
    -- ⊢ ∃ x x_1 y x_2, x ≠ y
    exact ⟨⟨x, hx⟩, mem_univ _, ⟨y, hy⟩, mem_univ _, Subtype.mk_eq_mk.not.mpr hxy⟩
    -- 🎉 no goals
#align set.nontrivial_coe_sort Set.nontrivial_coe_sort

alias ⟨_, Nontrivial.coe_sort⟩ := nontrivial_coe_sort
#align set.nontrivial.coe_sort Set.Nontrivial.coe_sort

/-- A type with a set `s` whose `coe_sort` is a nontrivial type is nontrivial.
For the corresponding result for `Subtype`, see `Subtype.nontrivial_iff_exists_ne`. -/
theorem nontrivial_of_nontrivial_coe (hs : Nontrivial s) : Nontrivial α :=
  nontrivial_of_nontrivial <| nontrivial_coe_sort.1 hs
#align set.nontrivial_of_nontrivial_coe Set.nontrivial_of_nontrivial_coe

theorem nontrivial_mono {α : Type*} {s t : Set α} (hst : s ⊆ t) (hs : Nontrivial s) :
    Nontrivial t :=
  Nontrivial.coe_sort <| (nontrivial_coe_sort.1 hs).mono hst
#align set.nontrivial_mono Set.nontrivial_mono

@[simp]
theorem not_subsingleton_iff : ¬s.Subsingleton ↔ s.Nontrivial := by
  simp_rw [Set.Subsingleton, Set.Nontrivial, not_forall]
  -- 🎉 no goals
#align set.not_subsingleton_iff Set.not_subsingleton_iff

@[simp]
theorem not_nontrivial_iff : ¬s.Nontrivial ↔ s.Subsingleton :=
  Iff.not_left not_subsingleton_iff.symm
#align set.not_nontrivial_iff Set.not_nontrivial_iff

alias ⟨_, Subsingleton.not_nontrivial⟩ := not_nontrivial_iff
#align set.subsingleton.not_nontrivial Set.Subsingleton.not_nontrivial

alias ⟨_, Nontrivial.not_subsingleton⟩ := not_subsingleton_iff
#align set.nontrivial.not_subsingleton Set.Nontrivial.not_subsingleton

protected lemma subsingleton_or_nontrivial (s : Set α) : s.Subsingleton ∨ s.Nontrivial := by
  simp [or_iff_not_imp_right]
  -- 🎉 no goals
#align set.subsingleton_or_nontrivial Set.subsingleton_or_nontrivial

lemma eq_singleton_or_nontrivial (ha : a ∈ s) : s = {a} ∨ s.Nontrivial := by
  rw [←subsingleton_iff_singleton ha]; exact s.subsingleton_or_nontrivial
  -- ⊢ Set.Subsingleton s ∨ Set.Nontrivial s
                                       -- 🎉 no goals
#align set.eq_singleton_or_nontrivial Set.eq_singleton_or_nontrivial

lemma nontrivial_iff_ne_singleton (ha : a ∈ s) : s.Nontrivial ↔ s ≠ {a} :=
  ⟨Nontrivial.ne_singleton, (eq_singleton_or_nontrivial ha).resolve_left⟩
#align set.nontrivial_iff_ne_singleton Set.nontrivial_iff_ne_singleton

lemma Nonempty.exists_eq_singleton_or_nontrivial : s.Nonempty → (∃ a, s = {a}) ∨ s.Nontrivial :=
  fun ⟨a, ha⟩ ↦ (eq_singleton_or_nontrivial ha).imp_left $ Exists.intro a
#align set.nonempty.exists_eq_singleton_or_nontrivial Set.Nonempty.exists_eq_singleton_or_nontrivial

theorem univ_eq_true_false : univ = ({True, False} : Set Prop) :=
  Eq.symm <| eq_univ_of_forall <| fun x => by
    rw [mem_insert_iff, mem_singleton_iff]
    -- ⊢ x = True ∨ x = False
    exact Classical.propComplete x
    -- 🎉 no goals
#align set.univ_eq_true_false Set.univ_eq_true_false

section Preorder

variable [Preorder α] [Preorder β] {f : α → β}

-- Porting note:
-- If we decide we want `Elem` to semireducible rather than reducible, we will need:
--   instance : Preorder (↑s) := Subtype.instPreorderSubtype _
-- here, along with appropriate lemmas.

theorem monotoneOn_iff_monotone : MonotoneOn f s ↔
    Monotone fun a : s => f a := by
  simp [Monotone, MonotoneOn]
  -- 🎉 no goals
#align set.monotone_on_iff_monotone Set.monotoneOn_iff_monotone

theorem antitoneOn_iff_antitone : AntitoneOn f s ↔
    Antitone fun a : s => f a := by
  simp [Antitone, AntitoneOn]
  -- 🎉 no goals
#align set.antitone_on_iff_antitone Set.antitoneOn_iff_antitone

theorem strictMonoOn_iff_strictMono : StrictMonoOn f s ↔
    StrictMono fun a : s => f a := by
  simp [StrictMono, StrictMonoOn]
  -- 🎉 no goals
#align set.strict_mono_on_iff_strict_mono Set.strictMonoOn_iff_strictMono

theorem strictAntiOn_iff_strictAnti : StrictAntiOn f s ↔
    StrictAnti fun a : s => f a := by
  simp [StrictAnti, StrictAntiOn]
  -- 🎉 no goals
#align set.strict_anti_on_iff_strict_anti Set.strictAntiOn_iff_strictAnti

variable (f)

/-! ### Monotonicity on singletons -/


protected theorem Subsingleton.monotoneOn (h : s.Subsingleton) : MonotoneOn f s :=
  fun _ ha _ hb _ => (congr_arg _ (h ha hb)).le
#align set.subsingleton.monotone_on Set.Subsingleton.monotoneOn

protected theorem Subsingleton.antitoneOn (h : s.Subsingleton) : AntitoneOn f s :=
  fun _ ha _ hb _ => (congr_arg _ (h hb ha)).le
#align set.subsingleton.antitone_on Set.Subsingleton.antitoneOn

protected theorem Subsingleton.strictMonoOn (h : s.Subsingleton) : StrictMonoOn f s :=
  fun _ ha _ hb hlt => (hlt.ne (h ha hb)).elim
#align set.subsingleton.strict_mono_on Set.Subsingleton.strictMonoOn

protected theorem Subsingleton.strictAntiOn (h : s.Subsingleton) : StrictAntiOn f s :=
  fun _ ha _ hb hlt => (hlt.ne (h ha hb)).elim
#align set.subsingleton.strict_anti_on Set.Subsingleton.strictAntiOn

@[simp]
theorem monotoneOn_singleton : MonotoneOn f {a} :=
  subsingleton_singleton.monotoneOn f
#align set.monotone_on_singleton Set.monotoneOn_singleton

@[simp]
theorem antitoneOn_singleton : AntitoneOn f {a} :=
  subsingleton_singleton.antitoneOn f
#align set.antitone_on_singleton Set.antitoneOn_singleton

@[simp]
theorem strictMonoOn_singleton : StrictMonoOn f {a} :=
  subsingleton_singleton.strictMonoOn f
#align set.strict_mono_on_singleton Set.strictMonoOn_singleton

@[simp]
theorem strictAntiOn_singleton : StrictAntiOn f {a} :=
  subsingleton_singleton.strictAntiOn f
#align set.strict_anti_on_singleton Set.strictAntiOn_singleton

end Preorder

section LinearOrder

variable [LinearOrder α] [LinearOrder β] {f : α → β}

/-- A function between linear orders which is neither monotone nor antitone makes a dent upright or
downright. -/
theorem not_monotoneOn_not_antitoneOn_iff_exists_le_le :
    ¬MonotoneOn f s ∧ ¬AntitoneOn f s ↔
      ∃ (a : α) (_ : a ∈ s) (b : α) (_ : b ∈ s) (c : α) (_ : c ∈ s),
        a ≤ b ∧ b ≤ c ∧ (f a < f b ∧ f c < f b ∨ f b < f a ∧ f b < f c) := by
  simp [monotoneOn_iff_monotone, antitoneOn_iff_antitone, and_assoc, exists_and_left,
    not_monotone_not_antitone_iff_exists_le_le, @and_left_comm (_ ∈ s)]
#align set.not_monotone_on_not_antitone_on_iff_exists_le_le Set.not_monotoneOn_not_antitoneOn_iff_exists_le_le

/-- A function between linear orders which is neither monotone nor antitone makes a dent upright or
downright. -/
theorem not_monotoneOn_not_antitoneOn_iff_exists_lt_lt :
    ¬MonotoneOn f s ∧ ¬AntitoneOn f s ↔
      ∃ (a : α) (_ : a ∈ s) (b : α) (_ : b ∈ s) (c : α) (_ : c ∈ s),
        a < b ∧ b < c ∧ (f a < f b ∧ f c < f b ∨ f b < f a ∧ f b < f c) := by
  simp [monotoneOn_iff_monotone, antitoneOn_iff_antitone, and_assoc, exists_and_left,
    not_monotone_not_antitone_iff_exists_lt_lt, @and_left_comm (_ ∈ s)]
#align set.not_monotone_on_not_antitone_on_iff_exists_lt_lt Set.not_monotoneOn_not_antitoneOn_iff_exists_lt_lt

end LinearOrder

end Set

open Set

namespace Function

variable {ι : Sort*} {α : Type*} {β : Type*} {f : α → β}

theorem Injective.nonempty_apply_iff {f : Set α → Set β} (hf : Injective f) (h2 : f ∅ = ∅)
    {s : Set α} : (f s).Nonempty ↔ s.Nonempty := by
  rw [nonempty_iff_ne_empty, ← h2, nonempty_iff_ne_empty, hf.ne_iff]
  -- 🎉 no goals
#align function.injective.nonempty_apply_iff Function.Injective.nonempty_apply_iff

end Function

open Function

namespace Set

/-! ### Lemmas about `inclusion`, the injection of subtypes induced by `⊆` -/


section Inclusion

variable {α : Type*} {s t u : Set α}

/-- `inclusion` is the "identity" function between two subsets `s` and `t`, where `s ⊆ t` -/
def inclusion (h : s ⊆ t) : s → t := fun x : s => (⟨x, h x.2⟩ : t)
#align set.inclusion Set.inclusion

@[simp]
theorem inclusion_self (x : s) : inclusion Subset.rfl x = x := by
  cases x
  -- ⊢ inclusion (_ : s ⊆ s) { val := val✝, property := property✝ } = { val := val✝ …
  rfl
  -- 🎉 no goals
#align set.inclusion_self Set.inclusion_self

theorem inclusion_eq_id (h : s ⊆ s) : inclusion h = id :=
  funext inclusion_self
#align set.inclusion_eq_id Set.inclusion_eq_id

@[simp]
theorem inclusion_mk {h : s ⊆ t} (a : α) (ha : a ∈ s) : inclusion h ⟨a, ha⟩ = ⟨a, h ha⟩ :=
  rfl
#align set.inclusion_mk Set.inclusion_mk

theorem inclusion_right (h : s ⊆ t) (x : t) (m : (x : α) ∈ s) : inclusion h ⟨x, m⟩ = x := by
  cases x
  -- ⊢ inclusion h { val := ↑{ val := val✝, property := property✝ }, property := m  …
  rfl
  -- 🎉 no goals
#align set.inclusion_right Set.inclusion_right

@[simp]
theorem inclusion_inclusion (hst : s ⊆ t) (htu : t ⊆ u) (x : s) :
    inclusion htu (inclusion hst x) = inclusion (hst.trans htu) x := by
  cases x
  -- ⊢ inclusion htu (inclusion hst { val := val✝, property := property✝ }) = inclu …
  rfl
  -- 🎉 no goals
#align set.inclusion_inclusion Set.inclusion_inclusion

@[simp]
theorem inclusion_comp_inclusion {α} {s t u : Set α} (hst : s ⊆ t) (htu : t ⊆ u) :
    inclusion htu ∘ inclusion hst = inclusion (hst.trans htu) :=
  funext (inclusion_inclusion hst htu)
#align set.inclusion_comp_inclusion Set.inclusion_comp_inclusion

@[simp]
theorem coe_inclusion (h : s ⊆ t) (x : s) : (inclusion h x : α) = (x : α) :=
  rfl
#align set.coe_inclusion Set.coe_inclusion

theorem inclusion_injective (h : s ⊆ t) : Injective (inclusion h)
  | ⟨_, _⟩, ⟨_, _⟩ => Subtype.ext_iff_val.2 ∘ Subtype.ext_iff_val.1
#align set.inclusion_injective Set.inclusion_injective

theorem eq_of_inclusion_surjective {s t : Set α} {h : s ⊆ t}
    (h_surj : Function.Surjective (inclusion h)) : s = t := by
  refine' Set.Subset.antisymm h (fun x hx => _)
  -- ⊢ x ∈ s
  obtain ⟨y, hy⟩ := h_surj ⟨x, hx⟩
  -- ⊢ x ∈ s
  exact mem_of_eq_of_mem (congr_arg Subtype.val hy).symm y.prop
  -- 🎉 no goals
#align set.eq_of_inclusion_surjective Set.eq_of_inclusion_surjective

end Inclusion

end Set

namespace Subsingleton

variable {α : Type*} [Subsingleton α]

theorem eq_univ_of_nonempty {s : Set α} : s.Nonempty → s = univ := fun ⟨x, hx⟩ =>
  eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
#align subsingleton.eq_univ_of_nonempty Subsingleton.eq_univ_of_nonempty

@[elab_as_elim]
theorem set_cases {p : Set α → Prop} (h0 : p ∅) (h1 : p univ) (s) : p s :=
  (s.eq_empty_or_nonempty.elim fun h => h.symm ▸ h0) fun h => (eq_univ_of_nonempty h).symm ▸ h1
#align subsingleton.set_cases Subsingleton.set_cases

theorem mem_iff_nonempty {α : Type*} [Subsingleton α] {s : Set α} {x : α} : x ∈ s ↔ s.Nonempty :=
  ⟨fun hx => ⟨x, hx⟩, fun ⟨y, hy⟩ => Subsingleton.elim y x ▸ hy⟩
#align subsingleton.mem_iff_nonempty Subsingleton.mem_iff_nonempty

end Subsingleton

/-! ### Decidability instances for sets -/


namespace Set

variable {α : Type u} (s t : Set α) (a : α)

instance decidableSdiff [Decidable (a ∈ s)] [Decidable (a ∈ t)] : Decidable (a ∈ s \ t) :=
  (by infer_instance : Decidable (a ∈ s ∧ a ∉ t))
      -- 🎉 no goals
#align set.decidable_sdiff Set.decidableSdiff

instance decidableInter [Decidable (a ∈ s)] [Decidable (a ∈ t)] : Decidable (a ∈ s ∩ t) :=
  (by infer_instance : Decidable (a ∈ s ∧ a ∈ t))
      -- 🎉 no goals
#align set.decidable_inter Set.decidableInter

instance decidableUnion [Decidable (a ∈ s)] [Decidable (a ∈ t)] : Decidable (a ∈ s ∪ t) :=
  (by infer_instance : Decidable (a ∈ s ∨ a ∈ t))
      -- 🎉 no goals
#align set.decidable_union Set.decidableUnion

instance decidableCompl [Decidable (a ∈ s)] : Decidable (a ∈ sᶜ) :=
  (by infer_instance : Decidable (a ∉ s))
      -- 🎉 no goals
#align set.decidable_compl Set.decidableCompl

instance decidableEmptyset : DecidablePred (· ∈ (∅ : Set α)) := fun _ => Decidable.isFalse (by simp)
                                                                                               -- 🎉 no goals
#align set.decidable_emptyset Set.decidableEmptyset

instance decidableUniv : DecidablePred (· ∈ (Set.univ : Set α)) := fun _ =>
  Decidable.isTrue (by simp)
                       -- 🎉 no goals
#align set.decidable_univ Set.decidableUniv

instance decidableSetOf (p : α → Prop) [Decidable (p a)] : Decidable (a ∈ { a | p a }) := by
  assumption
  -- 🎉 no goals
#align set.decidable_set_of Set.decidableSetOf

-- porting note: Lean 3 unfolded `{a}` before finding instances but Lean 4 needs additional help
instance decidableMemSingleton {a b : α} [DecidableEq α] :
    Decidable (a ∈ ({b} : Set α)) := decidableSetOf _ (· = b)

end Set

/-! ### Monotone lemmas for sets -/

section Monotone
variable {α β : Type*}

theorem Monotone.inter [Preorder β] {f g : β → Set α} (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x ∩ g x :=
  hf.inf hg
#align monotone.inter Monotone.inter

theorem MonotoneOn.inter [Preorder β] {f g : β → Set α} {s : Set β} (hf : MonotoneOn f s)
    (hg : MonotoneOn g s) : MonotoneOn (fun x => f x ∩ g x) s :=
  hf.inf hg
#align monotone_on.inter MonotoneOn.inter

theorem Antitone.inter [Preorder β] {f g : β → Set α} (hf : Antitone f) (hg : Antitone g) :
    Antitone fun x => f x ∩ g x :=
  hf.inf hg
#align antitone.inter Antitone.inter

theorem AntitoneOn.inter [Preorder β] {f g : β → Set α} {s : Set β} (hf : AntitoneOn f s)
    (hg : AntitoneOn g s) : AntitoneOn (fun x => f x ∩ g x) s :=
  hf.inf hg
#align antitone_on.inter AntitoneOn.inter

theorem Monotone.union [Preorder β] {f g : β → Set α} (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x ∪ g x :=
  hf.sup hg
#align monotone.union Monotone.union

theorem MonotoneOn.union [Preorder β] {f g : β → Set α} {s : Set β} (hf : MonotoneOn f s)
    (hg : MonotoneOn g s) : MonotoneOn (fun x => f x ∪ g x) s :=
  hf.sup hg
#align monotone_on.union MonotoneOn.union

theorem Antitone.union [Preorder β] {f g : β → Set α} (hf : Antitone f) (hg : Antitone g) :
    Antitone fun x => f x ∪ g x :=
  hf.sup hg
#align antitone.union Antitone.union

theorem AntitoneOn.union [Preorder β] {f g : β → Set α} {s : Set β} (hf : AntitoneOn f s)
    (hg : AntitoneOn g s) : AntitoneOn (fun x => f x ∪ g x) s :=
  hf.sup hg
#align antitone_on.union AntitoneOn.union

namespace Set

theorem monotone_setOf [Preorder α] {p : α → β → Prop} (hp : ∀ b, Monotone fun a => p a b) :
    Monotone fun a => { b | p a b } := fun _ _ h b => hp b h
#align set.monotone_set_of Set.monotone_setOf

theorem antitone_setOf [Preorder α] {p : α → β → Prop} (hp : ∀ b, Antitone fun a => p a b) :
    Antitone fun a => { b | p a b } := fun _ _ h b => hp b h
#align set.antitone_set_of Set.antitone_setOf

/-- Quantifying over a set is antitone in the set -/
theorem antitone_bforall {P : α → Prop} : Antitone fun s : Set α => ∀ x ∈ s, P x :=
  fun _ _ hst h x hx => h x <| hst hx
#align set.antitone_bforall Set.antitone_bforall

end Set

end Monotone

/-! ### Disjoint sets -/

variable {α β : Type*} {s t u : Set α} {f : α → β}

namespace Disjoint

theorem union_left (hs : Disjoint s u) (ht : Disjoint t u) : Disjoint (s ∪ t) u :=
  hs.sup_left ht
#align disjoint.union_left Disjoint.union_left

theorem union_right (ht : Disjoint s t) (hu : Disjoint s u) : Disjoint s (t ∪ u) :=
  ht.sup_right hu
#align disjoint.union_right Disjoint.union_right

theorem inter_left (u : Set α) (h : Disjoint s t) : Disjoint (s ∩ u) t :=
  h.inf_left _
#align disjoint.inter_left Disjoint.inter_left

theorem inter_left' (u : Set α) (h : Disjoint s t) : Disjoint (u ∩ s) t :=
  h.inf_left' _
#align disjoint.inter_left' Disjoint.inter_left'

theorem inter_right (u : Set α) (h : Disjoint s t) : Disjoint s (t ∩ u) :=
  h.inf_right _
#align disjoint.inter_right Disjoint.inter_right

theorem inter_right' (u : Set α) (h : Disjoint s t) : Disjoint s (u ∩ t) :=
  h.inf_right' _
#align disjoint.inter_right' Disjoint.inter_right'

theorem subset_left_of_subset_union (h : s ⊆ t ∪ u) (hac : Disjoint s u) : s ⊆ t :=
  hac.left_le_of_le_sup_right h
#align disjoint.subset_left_of_subset_union Disjoint.subset_left_of_subset_union

theorem subset_right_of_subset_union (h : s ⊆ t ∪ u) (hab : Disjoint s t) : s ⊆ u :=
  hab.left_le_of_le_sup_left h
#align disjoint.subset_right_of_subset_union Disjoint.subset_right_of_subset_union

end Disjoint
