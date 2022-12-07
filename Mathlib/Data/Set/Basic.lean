/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import Mathlib.Order.SymmDiff
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Use
import Mathlib.Tactic.SolveByElim

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

* `preimage f t : set α` : the preimage f⁻¹(t) (written `f ⁻¹' t` in Lean) of a subset of β.

* `Subsingleton s : Prop` : the predicate saying that `s` has at most one element.

* `Nontrivial s : Prop` : the predicate saying that `s` has at least two distinct elements.

* `range f : set β` : the image of `univ` under `f`.
  Also works for `{p : Prop} (f : p → α)` (unlike `image`)

* `inclusion s₁ s₂ : ↥s₁ → ↥s₂` : the map `↥s₁ → ↥s₂` induced by an inclusion `s₁ ⊆ s₂`.

## Notation

* `f ⁻¹' t` for `preimage f t`

* `f !! s` for `image f s`

* `sᶜ` for the complement of `s`

## Implementation notes

* `s.Nonempty` is to be preferred to `s ≠ ∅` or `∃ x, x ∈ s`. It has the advantage that
the `s.Nonempty` dot notation can be used.

* For `s : Set α`, do not use `Subtype s`. Instead use `↥s` or `(s : Type*)` or `s`.

## Tags

set, sets, subset, subsets, image, preimage, pre-image, range, union, intersection, insert,
singleton, complement, powerset

-/


-- Porting note: I have temporarily replaced the `''` notation with `!!`
-- See https://github.com/leanprover/lean4/issues/1922

-- Porting note: This is based on a future version of mathlib,
-- at https://github.com/leanprover-community/mathlib/pull/17836

/-! ### Set coercion to a type -/


open Function

universe u v w x

namespace Set

variable {α : Type _} {s t : Set α}

instance : LE (Set α) :=
  ⟨fun s t => ∀ ⦃x⦄, x ∈ s → x ∈ t⟩

instance : HasSubset (Set α) :=
  ⟨(· ≤ ·)⟩

instance {α : Type _} : BooleanAlgebra (Set α) :=
  { (inferInstance : BooleanAlgebra (α → Prop)) with
    sup := fun s t => { x | x ∈ s ∨ x ∈ t },
    le := (· ≤ ·),
    lt := fun s t => s ⊆ t ∧ ¬t ⊆ s,
    inf := fun s t => { x | x ∈ s ∧ x ∈ t },
    bot := ∅,
    compl := fun s => { x | x ∉ s },
    top := univ,
    sdiff := fun s t => { x | x ∈ s ∧ x ∉ t } }

instance : HasSSubset (Set α) :=
  ⟨(· < ·)⟩

instance : Union (Set α) :=
  ⟨(· ⊔ ·)⟩

instance : Inter (Set α) :=
  ⟨(· ⊓ ·)⟩

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

alias le_iff_subset ↔ _root_.has_le.le.subset _root_.has_subset.subset.le

alias lt_iff_ssubset ↔ _root_.has_lt.lt.ssubset _root_.has_ssubset.ssubset.lt

/-- Coercion from a set to the corresponding subtype. -/
instance {α : Type u} : CoeSort (Set α) (Type u) :=
  ⟨fun s => { x // x ∈ s }⟩

-- Porting note: the `lift` tactic has not been ported.
-- instance PiSetCoe.canLift (ι : Type u) (α : ∀ i : ι, Type v) [ne : ∀ i, Nonempty (α i)]
--     (s : Set ι) : CanLift (∀ i : s, α i) (∀ i, α i) (fun f i => f i) fun _ => True :=
--   PiSubtype.canLift ι α s
-- #align set.pi_set_coe.can_lift Set.PiSetCoe.canLift

-- instance PiSetCoe.canLift' (ι : Type u) (α : Type v) [ne : Nonempty α] (s : Set ι) :
--     CanLift (s → α) (ι → α) (fun f i => f i) fun _ => True :=
--   PiSetCoe.canLift ι (fun _ => α) s
-- #align set.pi_set_coe.can_lift' Set.PiSetCoe.canLift'

end Set

section SetCoe

variable {α : Type u}

theorem Set.coe_eq_subtype (s : Set α) : ↥s = { x // x ∈ s } :=
  rfl
#align set.coe_eq_subtype Set.coe_eq_subtype

@[simp]
theorem Set.coe_set_of (p : α → Prop) : ↥{ x | p x } = { x // p x } :=
  rfl
#align set.coe_set_of Set.coe_set_of

@[simp]
theorem SetCoe.forall {s : Set α} {p : s → Prop} : (∀ x : s, p x) ↔ ∀ (x) (h : x ∈ s), p ⟨x, h⟩ :=
  Subtype.forall
#align set_coe.forall SetCoe.forall

@[simp]
theorem SetCoe.exists {s : Set α} {p : s → Prop} :
    (∃ x : s, p x) ↔ ∃ (x : _)(h : x ∈ s), p ⟨x, h⟩ :=
  Subtype.exists
#align set_coe.exists SetCoe.exists

theorem SetCoe.exists' {s : Set α} {p : ∀ x, x ∈ s → Prop} :
    (∃ (x : _)(h : x ∈ s), p x h) ↔ ∃ x : s, p x x.2 :=
  (@SetCoe.exists _ _ fun x => p x.1 x.2).symm
#align set_coe.exists' SetCoe.exists'

theorem SetCoe.forall' {s : Set α} {p : ∀ x, x ∈ s → Prop} :
    (∀ (x) (h : x ∈ s), p x h) ↔ ∀ x : s, p x x.2 :=
  (@SetCoe.forall _ _ fun x => p x.1 x.2).symm
#align set_coe.forall' SetCoe.forall'

@[simp]
theorem set_coe_cast :
    ∀ {s t : Set α} (H' : s = t) (H : ↥s = ↥t) (x : s), cast H x = ⟨x.1, H' ▸ x.2⟩
  | _, _, rfl, _, _ => rfl
#align set_coe_cast set_coe_cast

theorem SetCoe.ext {s : Set α} {a b : s} : (↑a : α) = ↑b → a = b :=
  Subtype.eq
#align set_coe.ext SetCoe.ext

theorem SetCoe.ext_iff {s : Set α} {a b : s} : (↑a : α) = ↑b ↔ a = b :=
  Iff.intro SetCoe.ext fun h => h ▸ rfl
#align set_coe.ext_iff SetCoe.ext_iff

end SetCoe

/-- See also `subtype.prop` -/
theorem Subtype.mem {α : Type _} {s : Set α} (p : s) : (p : α) ∈ s :=
  p.prop
#align subtype.mem Subtype.mem

/-- Duplicate of `eq.subset'`, which currently has elaboration problems. -/
theorem Eq.subset {α} {s t : Set α} : s = t → s ⊆ t :=
  fun h₁ _ h₂ => by rw [← h₁] ; exact h₂
#align eq.subset Eq.subset

namespace Set

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x} {a b : α} {s t u : Set α}

-- Porting note: remove `noncomputable` later
noncomputable instance : Inhabited (Set α) :=
  ⟨∅⟩

attribute [ext] Set.ext
#align set.ext Set.ext

theorem ext_iff {s t : Set α} : s = t ↔ ∀ x, x ∈ s ↔ x ∈ t :=
  ⟨fun h x => by rw [h], ext⟩
#align set.ext_iff Set.ext_iff

-- Porting note: restore after https://github.com/leanprover-community/mathlib4/pull/857 is merged.
-- @[trans]
theorem mem_of_mem_of_subset {x : α} {s t : Set α} (hx : x ∈ s) (h : s ⊆ t) : x ∈ t :=
  h hx
#align set.mem_of_mem_of_subset Set.mem_of_mem_of_subset

-- Porting note: was `by tauto`
theorem forall_in_swap {p : α → β → Prop} : (∀ a ∈ s, ∀ (b), p a b) ↔ ∀ (b), ∀ a ∈ s, p a b :=
  ⟨fun h b a ha => h a ha b, fun h a ha b => h b a ha⟩
#align set.forall_in_swap Set.forall_in_swap

/-! ### Lemmas about `mem` and `set_of` -/


theorem mem_set_of {a : α} {p : α → Prop} : a ∈ { x | p x } ↔ p a :=
  Iff.rfl
#align set.mem_set_of Set.mem_set_of

/-- If `h : a ∈ {x | p x}` then `h.out : p x`. These are definitionally equal, but this can
nevertheless be useful for various reasons, e.g. to apply further projection notation or in an
argument to `simp`. -/
theorem _root_.Membership.Mem.out {p : α → Prop} {a : α} (h : a ∈ { x | p x }) : p a :=
  h
#align has_mem.mem.out Membership.Mem.out

theorem nmem_set_of_iff {a : α} {p : α → Prop} : a ∉ { x | p x } ↔ ¬p a :=
  Iff.rfl
#align set.nmem_set_of_iff Set.nmem_set_of_iff

@[simp]
theorem set_of_mem_eq {s : Set α} : { x | x ∈ s } = s :=
  rfl
#align set.set_of_mem_eq Set.set_of_mem_eq

theorem set_of_set {s : Set α} : setOf s = s :=
  rfl
#align set.set_of_set Set.set_of_set

theorem set_of_app_iff {p : α → Prop} {x : α} : { x | p x } x ↔ p x :=
  Iff.rfl
#align set.set_of_app_iff Set.set_of_app_iff

theorem mem_def {a : α} {s : Set α} : a ∈ s ↔ s a :=
  Iff.rfl
#align set.mem_def Set.mem_def

theorem set_of_bijective : Bijective (setOf : (α → Prop) → Set α) :=
  bijective_id
#align set.set_of_bijective Set.set_of_bijective

@[simp]
theorem set_of_subset_set_of {p q : α → Prop} : { a | p a } ⊆ { a | q a } ↔ ∀ a, p a → q a :=
  Iff.rfl
#align set.set_of_subset_set_of Set.set_of_subset_set_of

theorem set_of_and {p q : α → Prop} : { a | p a ∧ q a } = { a | p a } ∩ { a | q a } :=
  rfl
#align set.set_of_and Set.set_of_and

theorem set_of_or {p q : α → Prop} : { a | p a ∨ q a } = { a | p a } ∪ { a | q a } :=
  rfl
#align set.set_of_or Set.set_of_or

/-! ### Subset and strict subset relations -/


instance : IsRefl (Set α) (· ⊆ ·) :=
  show IsRefl (Set α) (. ≤ .) by infer_instance

instance : IsTrans (Set α) (· ⊆ ·) :=
  show IsTrans (Set α) (. ≤ .) by infer_instance

instance : IsAntisymm (Set α) (· ⊆ ·) :=
  show IsAntisymm (Set α) (. ≤ .) by infer_instance

instance : IsIrrefl (Set α) (· ⊂ ·) :=
  show IsIrrefl (Set α) (. < .) by infer_instance

instance : IsTrans (Set α) (· ⊂ ·) :=
  show IsTrans (Set α) (. < .) by infer_instance

instance : IsAsymm (Set α) (· ⊂ ·) :=
  show IsAsymm (Set α) (. < .) by infer_instance

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

-- Porting note: restore after https://github.com/leanprover-community/mathlib4/pull/857 is merged.
-- @[trans]
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
  simp only [subset_def, not_forall, exists_prop, iff_self]
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

@[simp]
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
@[simp]
theorem nonempty_coe_sort {s : Set α} : Nonempty (↥s) ↔ s.Nonempty :=
  nonempty_subtype
#align set.nonempty_coe_sort Set.nonempty_coe_sort

alias nonempty_coe_sort ↔ _ nonempty.coe_sort

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
  simp_rw [inter_nonempty, exists_prop]; rfl
#align set.inter_nonempty_iff_exists_left Set.inter_nonempty_iff_exists_left

theorem inter_nonempty_iff_exists_right : (s ∩ t).Nonempty ↔ ∃ x ∈ t, x ∈ s := by
  simp_rw [inter_nonempty, exists_prop, and_comm]; rfl
#align set.inter_nonempty_iff_exists_right Set.inter_nonempty_iff_exists_right

theorem nonempty_iff_univ_nonempty : Nonempty α ↔ (univ : Set α).Nonempty :=
  ⟨fun ⟨x⟩ => ⟨x, trivial⟩, fun ⟨x, _⟩ => ⟨x⟩⟩
#align set.nonempty_iff_univ_nonempty Set.nonempty_iff_univ_nonempty

@[simp]
theorem univ_nonempty : ∀ [Nonempty α], (univ : Set α).Nonempty
  | ⟨x⟩ => ⟨x, trivial⟩
#align set.univ_nonempty Set.univ_nonempty

theorem Nonempty.to_subtype : s.Nonempty → Nonempty s :=
  nonempty_subtype.2
#align set.nonempty.to_subtype Set.Nonempty.to_subtype

theorem Nonempty.to_type : s.Nonempty → Nonempty α := fun ⟨x, _⟩ => ⟨x⟩
#align set.nonempty.to_type Set.Nonempty.to_type

instance [Nonempty α] : Nonempty (Set.univ : Set α) :=
  Set.univ_nonempty.to_subtype

theorem nonempty_of_nonempty_subtype [Nonempty s] : s.Nonempty :=
  nonempty_subtype.mp ‹_›
#align set.nonempty_of_nonempty_subtype Set.nonempty_of_nonempty_subtype

/-! ### Lemmas about the empty set -/


theorem empty_def : (∅ : Set α) = { _x | False } :=
  rfl
#align set.empty_def Set.empty_def

@[simp]
theorem mem_empty_iff_false (x : α) : x ∈ (∅ : Set α) ↔ False :=
  Iff.rfl
#align set.mem_empty_iff_false Set.mem_empty_iff_false

@[simp]
theorem set_of_false : { _a : α | False } = ∅ :=
  rfl
#align set.set_of_false Set.set_of_false

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

theorem eq_empty_of_is_empty [IsEmpty α] (s : Set α) : s = ∅ :=
  eq_empty_of_subset_empty fun x _ => isEmptyElim x
#align set.eq_empty_of_is_empty Set.eq_empty_of_is_empty

/-- There is exactly one set of a type that is empty. -/
instance uniqueEmpty [IsEmpty α] :
    Unique (Set α) where
  default := ∅
  uniq := eq_empty_of_is_empty
#align set.unique_empty Set.uniqueEmpty

/-- See also `Set.nonempty_iff_ne_empty`. -/
theorem not_nonempty_iff_eq_empty {s : Set α} : ¬s.Nonempty ↔ s = ∅ := by
  simp only [Set.Nonempty, not_exists, eq_empty_iff_forall_not_mem, iff_self]
#align set.not_nonempty_iff_eq_empty Set.not_nonempty_iff_eq_empty

/-- See also `Set.not_nonempty_iff_eq_empty`. -/
theorem nonempty_iff_ne_empty : s.Nonempty ↔ s ≠ ∅ :=
  not_nonempty_iff_eq_empty.not_right
#align set.nonempty_iff_ne_empty Set.nonempty_iff_ne_empty

alias nonempty_iff_ne_empty ↔ Nonempty.ne_empty _

@[simp]
theorem not_nonempty_empty : ¬(∅ : Set α).Nonempty := fun ⟨_, hx⟩ => hx
#align set.not_nonempty_empty Set.not_nonempty_empty

@[simp]
theorem is_empty_coe_sort {s : Set α} : IsEmpty (↥s) ↔ s = ∅ :=
  not_iff_not.1 <| by simpa using nonempty_iff_ne_empty
#align set.is_empty_coe_sort Set.is_empty_coe_sort

theorem eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.Nonempty :=
  or_iff_not_imp_left.2 nonempty_iff_ne_empty.2
#align set.eq_empty_or_nonempty Set.eq_empty_or_nonempty

theorem subset_eq_empty {s t : Set α} (h : t ⊆ s) (e : s = ∅) : t = ∅ :=
  subset_empty_iff.1 <| e ▸ h
#align set.subset_eq_empty Set.subset_eq_empty

theorem ball_empty_iff {p : α → Prop} : (∀ x ∈ (∅ : Set α), p x) ↔ True :=
  iff_true_intro fun _ => False.elim
#align set.ball_empty_iff Set.ball_empty_iff

instance (α : Type u) : IsEmpty.{u + 1} (∅ : Set α) :=
  ⟨fun x => x.2⟩

@[simp]
theorem empty_ssubset : ∅ ⊂ s ↔ s.Nonempty :=
  (@bot_lt_iff_ne_bot (Set α) _ _ _).trans nonempty_iff_ne_empty.symm
#align set.empty_ssubset Set.empty_ssubset

alias empty_ssubset ↔ _ Nonempty.empty_ssubset

/-!

### Universal set.

In Lean `@univ α` (or `univ : Set α`) is the set that contains all elements of type `α`.
Mathematically it is the same as `α` but it has a different type.

-/


@[simp]
theorem set_of_true : { _x : α | True } = univ :=
  rfl
#align set.set_of_true Set.set_of_true

@[simp]
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

alias univ_subset_iff ↔ eq_univ_of_univ_subset _

theorem eq_univ_iff_forall {s : Set α} : s = univ ↔ ∀ x, x ∈ s :=
  univ_subset_iff.symm.trans <| forall_congr' fun _ => imp_iff_right trivial
#align set.eq_univ_iff_forall Set.eq_univ_iff_forall

theorem eq_univ_of_forall {s : Set α} : (∀ x, x ∈ s) → s = univ :=
  eq_univ_iff_forall.2
#align set.eq_univ_of_forall Set.eq_univ_of_forall

theorem Nonempty.eq_univ [Subsingleton α] : s.Nonempty → s = univ := by
  rintro ⟨x, hx⟩
  refine' eq_univ_of_forall fun y => by rwa [Subsingleton.elim y x]
#align set.nonempty.eq_univ Set.Nonempty.eq_univ

theorem eq_univ_of_subset {s t : Set α} (h : s ⊆ t) (hs : s = univ) : t = univ :=
  eq_univ_of_univ_subset <| (hs ▸ h : univ ⊆ t)
#align set.eq_univ_of_subset Set.eq_univ_of_subset

theorem exists_mem_of_nonempty (α) : ∀ [Nonempty α], ∃ x : α, x ∈ (univ : Set α)
  | ⟨x⟩ => ⟨x, trivial⟩
#align set.exists_mem_of_nonempty Set.exists_mem_of_nonempty

theorem ne_univ_iff_exists_not_mem {α : Type _} (s : Set α) : s ≠ univ ↔ ∃ a, a ∉ s := by
  rw [← not_forall, ← eq_univ_iff_forall]
#align set.ne_univ_iff_exists_not_mem Set.ne_univ_iff_exists_not_mem

theorem not_subset_iff_exists_mem_not_mem {α : Type _} {s t : Set α} :
    ¬s ⊆ t ↔ ∃ x, x ∈ s ∧ x ∉ t := by simp [subset_def]
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

instance union_is_assoc : IsAssociative (Set α) (· ∪ ·) :=
  ⟨union_assoc⟩
#align set.union_is_assoc Set.union_is_assoc

instance union_is_comm : IsCommutative (Set α) (· ∪ ·) :=
  ⟨union_comm⟩
#align set.union_is_comm Set.union_is_comm

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

theorem union_subset_union {s₁ s₂ t₁ t₂ : Set α} (h₁ : s₁ ⊆ s₂) (h₂ : t₁ ⊆ t₂) :
    s₁ ∪ t₁ ⊆ s₂ ∪ t₂ := fun _ => Or.imp (@h₁ _) (@h₂ _)
#align set.union_subset_union Set.union_subset_union

theorem union_subset_union_left {s₁ s₂ : Set α} (t) (h : s₁ ⊆ s₂) : s₁ ∪ t ⊆ s₂ ∪ t :=
  union_subset_union h Subset.rfl
#align set.union_subset_union_left Set.union_subset_union_left

theorem union_subset_union_right (s) {t₁ t₂ : Set α} (h : t₁ ⊆ t₂) : s ∪ t₁ ⊆ s ∪ t₂ :=
  union_subset_union Subset.rfl h
#align set.union_subset_union_right Set.union_subset_union_right

theorem subset_union_of_subset_left {s t : Set α} (h : s ⊆ t) (u : Set α) : s ⊆ t ∪ u :=
  Subset.trans h (subset_union_left t u)
#align set.subset_union_of_subset_left Set.subset_union_of_subset_left

theorem subset_union_of_subset_right {s u : Set α} (h : s ⊆ u) (t : Set α) : s ⊆ t ∪ u :=
  Subset.trans h (subset_union_right t u)
#align set.subset_union_of_subset_right Set.subset_union_of_subset_right

theorem union_congr_left (ht : t ⊆ s ∪ u) (hu : u ⊆ s ∪ t) : s ∪ t = s ⊔ u :=
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
  exact union_subset_iff
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

@[simp]
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

instance inter_is_assoc : IsAssociative (Set α) (· ∩ ·) :=
  ⟨inter_assoc⟩
#align set.inter_is_assoc Set.inter_is_assoc

instance inter_is_comm : IsCommutative (Set α) (· ∩ ·) :=
  ⟨inter_comm⟩
#align set.inter_is_comm Set.inter_is_comm

theorem inter_left_comm (s₁ s₂ s₃ : Set α) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
  ext fun _ => and_left_comm
#align set.inter_left_comm Set.inter_left_comm

theorem inter_right_comm (s₁ s₂ s₃ : Set α) : s₁ ∩ s₂ ∩ s₃ = s₁ ∩ s₃ ∩ s₂ :=
  ext fun _ => and_right_comm
#align set.inter_right_comm Set.inter_right_comm

@[simp]
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

@[simp]
theorem inter_univ (a : Set α) : a ∩ univ = a :=
  inf_top_eq
#align set.inter_univ Set.inter_univ

@[simp]
theorem univ_inter (a : Set α) : univ ∩ a = a :=
  top_inf_eq
#align set.univ_inter Set.univ_inter

theorem inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s₁ ⊆ t₁) (h₂ : s₂ ⊆ t₂) :
    s₁ ∩ s₂ ⊆ t₁ ∩ t₂ := fun _ => And.imp (@h₁ _) (@h₂ _)
#align set.inter_subset_inter Set.inter_subset_inter

theorem inter_subset_inter_left {s t : Set α} (u : Set α) (H : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  inter_subset_inter H Subset.rfl
#align set.inter_subset_inter_left Set.inter_subset_inter_left

theorem inter_subset_inter_right {s t : Set α} (u : Set α) (H : s ⊆ t) : u ∩ s ⊆ u ∩ t :=
  inter_subset_inter Subset.rfl H
#align set.inter_subset_inter_right Set.inter_subset_inter_right

theorem union_inter_cancel_left {s t : Set α} : (s ∪ t) ∩ s = s :=
  inter_eq_self_of_subset_right <| subset_union_left _ _
#align set.union_inter_cancel_left Set.union_inter_cancel_left

theorem union_inter_cancel_right {s t : Set α} : (s ∪ t) ∩ t = t :=
  inter_eq_self_of_subset_right <| subset_union_right _ _
#align set.union_inter_cancel_right Set.union_inter_cancel_right

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

theorem insert_subset : insert a s ⊆ t ↔ a ∈ t ∧ s ⊆ t := by
  simp only [subset_def, mem_insert_iff, or_imp, forall_and, forall_eq, iff_self]
#align set.insert_subset Set.insert_subset

theorem insert_subset_insert (h : s ⊆ t) : insert a s ⊆ insert a t := fun _ => Or.imp_right (@h _)
#align set.insert_subset_insert Set.insert_subset_insert

theorem insert_subset_insert_iff (ha : a ∉ s) : insert a s ⊆ insert a t ↔ s ⊆ t := by
  refine' ⟨fun h x hx => _, insert_subset_insert⟩
  rcases h (subset_insert _ _ hx) with (rfl | hxt)
  exacts[(ha hx).elim, hxt]
#align set.insert_subset_insert_iff Set.insert_subset_insert_iff

theorem ssubset_iff_insert {s t : Set α} : s ⊂ t ↔ ∃ (a : α) (_ : a ∉ s), insert a s ⊆ t := by
  simp only [insert_subset, exists_and_right, ssubset_def, not_subset]
  simp only [exists_prop, and_comm]
  rfl
#align set.ssubset_iff_insert Set.ssubset_iff_insert

theorem ssubset_insert {s : Set α} {a : α} (h : a ∉ s) : s ⊂ insert a s :=
  ssubset_iff_insert.2 ⟨a, h, Subset.rfl⟩
#align set.ssubset_insert Set.ssubset_insert

theorem insert_comm (a b : α) (s : Set α) : insert a (insert b s) = insert b (insert a s) :=
  ext fun _ => or_left_comm
#align set.insert_comm Set.insert_comm

@[simp]
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

theorem bex_insert_iff {P : α → Prop} {a : α} {s : Set α} :
    (∃ x ∈ insert a s, P x) ↔ P a ∨ ∃ x ∈ s, P x :=
  bex_or_left.trans <| or_congr_left bex_eq_left
#align set.bex_insert_iff Set.bex_insert_iff

theorem ball_insert_iff {P : α → Prop} {a : α} {s : Set α} :
    (∀ x ∈ insert a s, P x) ↔ P a ∧ ∀ x ∈ s, P x :=
  ball_or_left.trans <| and_congr_left' forall_eq
#align set.ball_insert_iff Set.ball_insert_iff

/-! ### Lemmas about singletons -/


theorem singleton_def (a : α) : ({a} : Set α) = insert a ∅ :=
  (insert_emptyc_eq _).symm
#align set.singleton_def Set.singleton_def

@[simp]
theorem mem_singleton_iff {a b : α} : a ∈ ({b} : Set α) ↔ a = b :=
  Iff.rfl
#align set.mem_singleton_iff Set.mem_singleton_iff

@[simp]
theorem set_of_eq_eq_singleton {a : α} : { n | n = a } = {a} :=
  rfl
#align set.set_of_eq_eq_singleton Set.set_of_eq_eq_singleton

@[simp]
theorem set_of_eq_eq_singleton' {a : α} : { x | a = x } = {a} :=
  ext fun _ => eq_comm
#align set.set_of_eq_eq_singleton' Set.set_of_eq_eq_singleton'

-- TODO: again, annotation needed
@[simp]
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

@[simp]
theorem empty_ssubset_singleton : (∅ : Set α) ⊂ {a} :=
  (singleton_nonempty _).empty_ssubset
#align set.empty_ssubset_singleton Set.empty_ssubset_singleton

@[simp]
theorem singleton_subset_iff {a : α} {s : Set α} : {a} ⊆ s ↔ a ∈ s :=
  forall_eq
#align set.singleton_subset_iff Set.singleton_subset_iff

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
  simp only [Set.Nonempty, mem_inter_iff, mem_singleton_iff, exists_eq_left, iff_self]
#align set.singleton_inter_nonempty Set.singleton_inter_nonempty

@[simp]
theorem inter_singleton_nonempty : (s ∩ {a}).Nonempty ↔ a ∈ s := by
  rw [inter_comm, singleton_inter_nonempty]
#align set.inter_singleton_nonempty Set.inter_singleton_nonempty

@[simp]
theorem singleton_inter_eq_empty : {a} ∩ s = ∅ ↔ a ∉ s :=
  not_nonempty_iff_eq_empty.symm.trans singleton_inter_nonempty.not
#align set.singleton_inter_eq_empty Set.singleton_inter_eq_empty

@[simp]
theorem inter_singleton_eq_empty : s ∩ {a} = ∅ ↔ a ∉ s := by
  rw [inter_comm, singleton_inter_eq_empty]
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


@[simp]
theorem pair_eq_singleton (a : α) : ({a, a} : Set α) = {a} :=
  union_self _
#align set.pair_eq_singleton Set.pair_eq_singleton

theorem pair_comm (a b : α) : ({a, b} : Set α) = {b, a} :=
  union_comm _ _
#align set.pair_comm Set.pair_comm

-- Porting note: first branch after `constructor` used to be by `tauto!`.
theorem pair_eq_pair_iff {x y z w : α} :
    ({x, y} : Set α) = {z, w} ↔ x = z ∧ y = w ∨ x = w ∧ y = z := by
  simp only [Set.Subset.antisymm_iff, Set.insert_subset, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.singleton_subset_iff]
  constructor
  · rintro ⟨⟨rfl | rfl, rfl | rfl⟩, ⟨h₁, h₂⟩⟩ <;> simp [h₁, h₂] at * <;> simp [h₁, h₂]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp
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
  simp_rw [ext_iff, mem_sep_iff, and_congr_right_iff]; rfl
#align set.sep_ext_iff Set.sep_ext_iff

theorem sep_eq_of_subset (h : s ⊆ t) : { x ∈ t | x ∈ s } = s :=
  inter_eq_self_of_subset_right h
#align set.sep_eq_of_subset Set.sep_eq_of_subset

@[simp]
theorem sep_subset (s : Set α) (p : α → Prop) : { x ∈ s | p x } ⊆ s := fun _ => And.left
#align set.sep_subset Set.sep_subset

@[simp]
theorem sep_eq_self_iff_mem_true : { x ∈ s | p x } = s ↔ ∀ x ∈ s, p x := by
  simp_rw [ext_iff, mem_sep_iff, and_iff_left_iff_imp]; rfl
#align set.sep_eq_self_iff_mem_true Set.sep_eq_self_iff_mem_true

@[simp]
theorem sep_eq_empty_iff_mem_false : { x ∈ s | p x } = ∅ ↔ ∀ x ∈ s, ¬p x := by
  simp_rw [ext_iff, mem_sep_iff, mem_empty_iff_false, iff_false_iff, not_and]; rfl
#align set.sep_eq_empty_iff_mem_false Set.sep_eq_empty_iff_mem_false

@[simp]
theorem sep_true : { x ∈ s | True } = s :=
  inter_univ s
#align set.sep_true Set.sep_true

@[simp]
theorem sep_false : { x ∈ s | False } = ∅ :=
  inter_empty s
#align set.sep_false Set.sep_false

@[simp]
theorem sep_empty (p : α → Prop) : { x ∈ (∅ : Set α) | p x } = ∅ :=
  empty_inter p
#align set.sep_empty Set.sep_empty

@[simp]
theorem sep_univ : { x ∈ (univ : Set α) | p x } = { x | p x } :=
  univ_inter p
#align set.sep_univ Set.sep_univ

@[simp]
theorem sep_union : { x ∈ s ∪ t | p x } = { x ∈ s | p x } ∪ { x ∈ t | p x } :=
  union_inter_distrib_right
#align set.sep_union Set.sep_union

@[simp]
theorem sep_inter : { x ∈ s ∩ t | p x } = { x ∈ s | p x } ∩ { x ∈ t | p x } :=
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
theorem sep_set_of : { x ∈ { y | p y } | q x } = { x | p x ∧ q x } :=
  rfl
#align set.sep_set_of Set.sep_set_of

end Sep

@[simp]
theorem subset_singleton_iff {α : Type _} {s : Set α} {x : α} : s ⊆ {x} ↔ ∀ y ∈ s, y = x :=
  Iff.rfl
#align set.subset_singleton_iff Set.subset_singleton_iff

theorem subset_singleton_iff_eq {s : Set α} {x : α} : s ⊆ {x} ↔ s = ∅ ∨ s = {x} := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · exact ⟨fun _ => Or.inl rfl, fun _ => empty_subset _⟩
  · simp [eq_singleton_iff_nonempty_unique_mem, hs, hs.ne_empty]
#align set.subset_singleton_iff_eq Set.subset_singleton_iff_eq

theorem Nonempty.subset_singleton_iff (h : s.Nonempty) : s ⊆ {a} ↔ s = {a} :=
  subset_singleton_iff_eq.trans <| or_iff_right h.ne_empty
#align set.nonempty.subset_singleton_iff Set.Nonempty.subset_singleton_iff

theorem ssubset_singleton_iff {s : Set α} {x : α} : s ⊂ {x} ↔ s = ∅ := by
  rw [ssubset_iff_subset_ne, subset_singleton_iff_eq, or_and_right, and_not_self_iff, or_false_iff,
    and_iff_left_iff_imp]
  exact fun h => ne_of_eq_of_ne h (singleton_ne_empty _).symm
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

theorem disjoint_right : Disjoint s t ↔ ∀ ⦃a⦄, a ∈ t → a ∉ s := by rw [Disjoint.comm, disjoint_left]
#align set.disjoint_right Set.disjoint_right

/-! ### Lemmas about complement -/


theorem compl_def (s : Set α) : sᶜ = { x | x ∉ s } :=
  rfl
#align set.compl_def Set.compl_def

theorem mem_compl {s : Set α} {x : α} (h : x ∉ s) : x ∈ sᶜ :=
  h
#align set.mem_compl Set.mem_compl

theorem compl_set_of {α} (p : α → Prop) : { a | p a }ᶜ = { a | ¬p a } :=
  rfl
#align set.compl_set_of Set.compl_set_of

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

theorem subset_compl_iff_disjoint_left : s ⊆ tᶜ ↔ Disjoint t s :=
  @le_compl_iff_disjoint_left (Set α) _ _ _
#align set.subset_compl_iff_disjoint_left Set.subset_compl_iff_disjoint_left

theorem subset_compl_iff_disjoint_right : s ⊆ tᶜ ↔ Disjoint s t :=
  @le_compl_iff_disjoint_right (Set α) _ _ _
#align set.subset_compl_iff_disjoint_right Set.subset_compl_iff_disjoint_right

theorem disjoint_compl_left_iff_subset : Disjoint (sᶜ) t ↔ t ⊆ s :=
  disjoint_compl_left_iff
#align set.disjoint_compl_left_iff_subset Set.disjoint_compl_left_iff_subset

theorem disjoint_compl_right_iff_subset : Disjoint s (tᶜ) ↔ s ⊆ t :=
  disjoint_compl_right_iff
#align set.disjoint_compl_right_iff_subset Set.disjoint_compl_right_iff_subset

alias subset_compl_iff_disjoint_right ↔ _ _root_.disjoint.subset_compl_right

alias subset_compl_iff_disjoint_left ↔ _ _root_.disjoint.subset_compl_left

alias disjoint_compl_left_iff_subset ↔ _ _root_.has_subset.subset.disjoint_compl_left

alias disjoint_compl_right_iff_subset ↔ _ _root_.has_subset.subset.disjoint_compl_right

theorem subset_union_compl_iff_inter_subset {s t u : Set α} : s ⊆ t ∪ uᶜ ↔ s ∩ u ⊆ t :=
  (@is_compl_compl _ u _).le_sup_right_iff_inf_left_le
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
  exact sup_inf_sdiff _ _
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
  apply diff_subset_iff
#align set.diff_singleton_subset_iff Set.diff_singleton_subset_iff

theorem subset_diff_singleton {x : α} {s t : Set α} (h : s ⊆ t) (hx : x ∉ s) : s ⊆ t \ {x} :=
  subset_inter h <| subset_compl_comm.1 <| singleton_subset_iff.2 hx
#align set.subset_diff_singleton Set.subset_diff_singleton

theorem subset_insert_diff_singleton (x : α) (s : Set α) : s ⊆ insert x (s \ {x}) := by
  rw [← diff_singleton_subset_iff]
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
  constructor <;> simp (config := { contextual := true }) [or_imp, h]
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
  simp [and_iff_left_of_imp fun hx : x ∈ s => show x ≠ a from fun hxa => h <| hxa ▸ hx]
#align set.insert_diff_self_of_not_mem Set.insert_diff_self_of_not_mem

@[simp]
theorem insert_diff_eq_singleton {a : α} {s : Set α} (h : a ∉ s) : insert a s \ s = {a} := by
  ext
  rw [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, or_and_right, and_not_self_iff,
    or_false_iff, and_iff_left_iff_imp]
  rintro rfl
  exact h
#align set.insert_diff_eq_singleton Set.insert_diff_eq_singleton

theorem inter_insert_of_mem (h : a ∈ s) : s ∩ insert a t = insert a (s ∩ t) := by
  rw [insert_inter_distrib, insert_eq_of_mem h]
#align set.inter_insert_of_mem Set.inter_insert_of_mem

theorem insert_inter_of_mem (h : a ∈ t) : insert a s ∩ t = insert a (s ∩ t) := by
  rw [insert_inter_distrib, insert_eq_of_mem h]
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
theorem diff_eq_self {s t : Set α} : s \ t = s ↔ t ∩ s ⊆ ∅ :=
  show s \ t = s ↔ t ⊓ s ≤ ⊥ from sdiff_eq_self_iff_disjoint.trans disjoint_iff_inf_le
#align set.diff_eq_self Set.diff_eq_self

@[simp]
theorem diff_singleton_eq_self {a : α} {s : Set α} (h : a ∉ s) : s \ {a} = s :=
  diff_eq_self.2 <| by simp [singleton_inter_eq_empty.2 h]
#align set.diff_singleton_eq_self Set.diff_singleton_eq_self

@[simp]
theorem insert_diff_singleton {a : α} {s : Set α} : insert a (s \ {a}) = insert a s := by
  simp [insert_eq, union_diff_self, -union_singleton, -singleton_union]
#align set.insert_diff_singleton Set.insert_diff_singleton

@[simp]
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
  ⟨fun h => h (Subset.refl s), fun h u hu => Subset.trans hu h⟩
#align set.powerset_mono Set.powerset_mono

theorem monotone_powerset : Monotone (powerset : Set α → Set (Set α)) := fun s t => powerset_mono.2
#align set.monotone_powerset Set.monotone_powerset

@[simp]
theorem powerset_nonempty : (𝒫 s).Nonempty :=
  ⟨∅, empty_subset s⟩
#align set.powerset_nonempty Set.powerset_nonempty

@[simp]
theorem powerset_empty : 𝒫(∅ : Set α) = {∅} :=
  ext fun _ => subset_empty_iff
#align set.powerset_empty Set.powerset_empty

@[simp]
theorem powerset_univ : 𝒫(univ : Set α) = univ :=
  eq_univ_of_forall subset_univ
#align set.powerset_univ Set.powerset_univ

/-! ### Sets defined as an if-then-else -/


theorem mem_dite_univ_right (p : Prop) [Decidable p] (t : p → Set α) (x : α) :
    (x ∈ if h : p then t h else univ) ↔ ∀ h : p, x ∈ t h := by split_ifs <;> simp [h]
#align set.mem_dite_univ_right Set.mem_dite_univ_right

@[simp]
theorem mem_ite_univ_right (p : Prop) [Decidable p] (t : Set α) (x : α) :
    x ∈ ite p t Set.univ ↔ p → x ∈ t :=
  mem_dite_univ_right p (fun _ => t) x
#align set.mem_ite_univ_right Set.mem_ite_univ_right

theorem mem_dite_univ_left (p : Prop) [Decidable p] (t : ¬p → Set α) (x : α) :
    (x ∈ if h : p then univ else t h) ↔ ∀ h : ¬p, x ∈ t h := by split_ifs <;> simp [h]
#align set.mem_dite_univ_left Set.mem_dite_univ_left

@[simp]
theorem mem_ite_univ_left (p : Prop) [Decidable p] (t : Set α) (x : α) :
    x ∈ ite p Set.univ t ↔ ¬p → x ∈ t :=
  mem_dite_univ_left p (fun _ => t) x
#align set.mem_ite_univ_left Set.mem_ite_univ_left

theorem mem_dite_empty_right (p : Prop) [Decidable p] (t : p → Set α) (x : α) :
    (x ∈ if h : p then t h else ∅) ↔ ∃ h : p, x ∈ t h := by split_ifs <;> simp [h]
#align set.mem_dite_empty_right Set.mem_dite_empty_right

@[simp]
theorem mem_ite_empty_right (p : Prop) [Decidable p] (t : Set α) (x : α) :
    x ∈ ite p t ∅ ↔ p ∧ x ∈ t := by split_ifs <;> simp [h]
#align set.mem_ite_empty_right Set.mem_ite_empty_right

theorem mem_dite_empty_left (p : Prop) [Decidable p] (t : ¬p → Set α) (x : α) :
    (x ∈ if h : p then ∅ else t h) ↔ ∃ h : ¬p, x ∈ t h := by split_ifs <;> simp [h]
#align set.mem_dite_empty_left Set.mem_dite_empty_left

@[simp]
theorem mem_ite_empty_left (p : Prop) [Decidable p] (t : Set α) (x : α) :
    x ∈ ite p ∅ t ↔ ¬p ∧ x ∈ t := by split_ifs <;> simp [h]
#align set.mem_ite_empty_left Set.mem_ite_empty_left

/-! ### If-then-else for sets -/


/-- `ite` for sets: `set.ite t s s' ∩ t = s ∩ t`, `set.ite t s s' ∩ tᶜ = s' ∩ tᶜ`.
Defined as `s ∩ t ∪ s' \ t`. -/
protected def ite (t s s' : Set α) : Set α :=
  s ∩ t ∪ s' \ t
#align set.ite Set.ite

@[simp]
theorem ite_inter_self (t s s' : Set α) : t.ite s s' ∩ t = s ∩ t := by
  rw [Set.ite, union_inter_distrib_right, diff_inter_self, inter_assoc, inter_self, union_empty]
#align set.ite_inter_self Set.ite_inter_self

@[simp]
theorem ite_compl (t s s' : Set α) : tᶜ.ite s s' = t.ite s' s := by
  rw [Set.ite, Set.ite, diff_compl, union_comm, diff_eq]
#align set.ite_compl Set.ite_compl

@[simp]
theorem ite_inter_compl_self (t s s' : Set α) : t.ite s s' ∩ tᶜ = s' ∩ tᶜ := by
  rw [← ite_compl, ite_inter_self]
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
#align set.ite_left Set.ite_left

@[simp]
theorem ite_right (s t : Set α) : s.ite t s = t ∩ s := by simp [Set.ite]
#align set.ite_right Set.ite_right

@[simp]
theorem ite_empty (s s' : Set α) : Set.ite ∅ s s' = s' := by simp [Set.ite]
#align set.ite_empty Set.ite_empty

@[simp]
theorem ite_univ (s s' : Set α) : Set.ite univ s s' = s := by simp [Set.ite]
#align set.ite_univ Set.ite_univ

@[simp]
theorem ite_empty_left (t s : Set α) : t.ite ∅ s = s \ t := by simp [Set.ite]
#align set.ite_empty_left Set.ite_empty_left

@[simp]
theorem ite_empty_right (t s : Set α) : t.ite s ∅ = s ∩ t := by simp [Set.ite]
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
  simp only [Set.ite, Set.mem_inter_iff, Set.mem_diff, Set.mem_union]
  itauto
#align set.ite_inter_inter Set.ite_inter_inter

theorem ite_inter (t s₁ s₂ s : Set α) : t.ite (s₁ ∩ s) (s₂ ∩ s) = t.ite s₁ s₂ ∩ s := by
  rw [ite_inter_inter, ite_same]
#align set.ite_inter Set.ite_inter

theorem ite_inter_of_inter_eq (t : Set α) {s₁ s₂ s : Set α} (h : s₁ ∩ s = s₂ ∩ s) :
    t.ite s₁ s₂ ∩ s = s₁ ∩ s := by rw [← ite_inter, ← h, ite_same]
#align set.ite_inter_of_inter_eq Set.ite_inter_of_inter_eq

theorem subset_ite {t s s' u : Set α} : u ⊆ t.ite s s' ↔ u ∩ t ⊆ s ∧ u \ t ⊆ s' := by
  simp only [subset_def, ← forall_and]
  refine' forall_congr' fun x => _
  by_cases hx : x ∈ t <;> simp [*, Set.ite]
#align set.subset_ite Set.subset_ite

/-! ### Inverse image -/


/-- The preimage of `s : set β` by `f : α → β`, written `f ⁻¹' s`,
  is the set of `x : α` such that `f x ∈ s`. -/
def preimage {α : Type u} {β : Type v} (f : α → β) (s : Set β) : Set α :=
  { x | f x ∈ s }
#align set.preimage Set.preimage

-- mathport name: «expr ⁻¹' »
infixl:80 " ⁻¹' " => preimage

section Preimage

variable {f : α → β} {g : β → γ}

@[simp]
theorem preimage_empty : f ⁻¹' ∅ = ∅ :=
  rfl
#align set.preimage_empty Set.preimage_empty

@[simp]
theorem mem_preimage {s : Set β} {a : α} : a ∈ f ⁻¹' s ↔ f a ∈ s :=
  Iff.rfl
#align set.mem_preimage Set.mem_preimage

-- Porting note: this used `apply_assumption` after `congr with x`.
theorem preimage_congr {f g : α → β} {s : Set β} (h : ∀ x : α, f x = g x) : f ⁻¹' s = g ⁻¹' s := by
  congr with x
  sorry
#align set.preimage_congr Set.preimage_congr

theorem preimage_mono {s t : Set β} (h : s ⊆ t) : f ⁻¹' s ⊆ f ⁻¹' t := fun _ hx => h hx
#align set.preimage_mono Set.preimage_mono

@[simp]
theorem preimage_univ : f ⁻¹' univ = univ :=
  rfl
#align set.preimage_univ Set.preimage_univ

theorem subset_preimage_univ {s : Set α} : s ⊆ f ⁻¹' univ :=
  subset_univ _
#align set.subset_preimage_univ Set.subset_preimage_univ

@[simp]
theorem preimage_inter {s t : Set β} : f ⁻¹' (s ∩ t) = f ⁻¹' s ∩ f ⁻¹' t :=
  rfl
#align set.preimage_inter Set.preimage_inter

@[simp]
theorem preimage_union {s t : Set β} : f ⁻¹' (s ∪ t) = f ⁻¹' s ∪ f ⁻¹' t :=
  rfl
#align set.preimage_union Set.preimage_union

@[simp]
theorem preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ :=
  rfl
#align set.preimage_compl Set.preimage_compl

@[simp]
theorem preimage_diff (f : α → β) (s t : Set β) : f ⁻¹' (s \ t) = f ⁻¹' s \ f ⁻¹' t :=
  rfl
#align set.preimage_diff Set.preimage_diff

@[simp]
theorem preimage_ite (f : α → β) (s t₁ t₂ : Set β) :
    f ⁻¹' s.ite t₁ t₂ = (f ⁻¹' s).ite (f ⁻¹' t₁) (f ⁻¹' t₂) :=
  rfl
#align set.preimage_ite Set.preimage_ite

@[simp]
theorem preimage_set_of_eq {p : α → Prop} {f : β → α} : f ⁻¹' { a | p a } = { a | p (f a) } :=
  rfl
#align set.preimage_set_of_eq Set.preimage_set_of_eq

@[simp]
theorem preimage_id_eq : preimage (id : α → α) = id :=
  rfl
#align set.preimage_id_eq Set.preimage_id_eq

theorem preimage_id {s : Set α} : id ⁻¹' s = s :=
  rfl
#align set.preimage_id Set.preimage_id

@[simp]
theorem preimage_id' {s : Set α} : (fun x => x) ⁻¹' s = s :=
  rfl
#align set.preimage_id' Set.preimage_id'

@[simp]
theorem preimage_const_of_mem {b : β} {s : Set β} (h : b ∈ s) : (fun _ : α => b) ⁻¹' s = univ :=
  eq_univ_of_forall fun x => h
#align set.preimage_const_of_mem Set.preimage_const_of_mem

@[simp]
theorem preimage_const_of_not_mem {b : β} {s : Set β} (h : b ∉ s) : (fun _ : α => b) ⁻¹' s = ∅ :=
  eq_empty_of_subset_empty fun x hx => h hx
#align set.preimage_const_of_not_mem Set.preimage_const_of_not_mem

theorem preimage_const (b : β) (s : Set β) [Decidable (b ∈ s)] :
    (fun x : α => b) ⁻¹' s = if b ∈ s then univ else ∅ := by
  split_ifs with hb hb
  exacts[preimage_const_of_mem hb, preimage_const_of_not_mem hb]
#align set.preimage_const Set.preimage_const

theorem preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' (g ⁻¹' s) :=
  rfl
#align set.preimage_comp Set.preimage_comp

theorem preimage_comp_eq : preimage (g ∘ f) = preimage f ∘ preimage g :=
  rfl
#align set.preimage_comp_eq Set.preimage_comp_eq

@[simp]
theorem preimage_iterate_eq {f : α → α} {n : ℕ} : Set.preimage (f^[n]) = Set.preimage f^[n] := by
  induction' n with n ih; · simp
  rw [iterate_succ, iterate_succ', Set.preimage_comp_eq, ih]
#align set.preimage_iterate_eq Set.preimage_iterate_eq

theorem preimage_preimage {g : β → γ} {f : α → β} {s : Set γ} :
    f ⁻¹' (g ⁻¹' s) = (fun x => g (f x)) ⁻¹' s :=
  preimage_comp.symm
#align set.preimage_preimage Set.preimage_preimage

theorem eq_preimage_subtype_val_iff {p : α → Prop} {s : Set (Subtype p)} {t : Set α} :
    s = Subtype.val ⁻¹' t ↔ ∀ (x) (h : p x), (⟨x, h⟩ : Subtype p) ∈ s ↔ x ∈ t :=
  ⟨fun s_eq x h => by
    rw [s_eq]
    simp, fun h => ext fun ⟨x, hx⟩ => by simp [h]⟩
#align set.eq_preimage_subtype_val_iff Set.eq_preimage_subtype_val_iff

theorem nonempty_of_nonempty_preimage {s : Set β} {f : α → β} (hf : (f ⁻¹' s).Nonempty) :
    s.Nonempty :=
  let ⟨x, hx⟩ := hf
  ⟨f x, hx⟩
#align set.nonempty_of_nonempty_preimage Set.nonempty_of_nonempty_preimage

theorem preimage_subtype_coe_eq_compl {α : Type _} {s u v : Set α} (hsuv : s ⊆ u ∪ v)
    (H : s ∩ (u ∩ v) = ∅) : (coe : s → α) ⁻¹' u = (coe ⁻¹' v)ᶜ := by
  ext ⟨x, x_in_s⟩
  constructor
  · intro x_in_u x_in_v
    exact eq_empty_iff_forall_not_mem.mp H x ⟨x_in_s, ⟨x_in_u, x_in_v⟩⟩
  · intro hx
    exact Or.elim (hsuv x_in_s) id fun hx' => hx.elim hx'
#align set.preimage_subtype_coe_eq_compl Set.preimage_subtype_coe_eq_compl

end Preimage

/-! ### Image of a set under a function -/


section Image

variable {f : α → β}

#align set.image Set.image

/-- Notation for the image of a set under a function. -/
infixl:80 " !! " => image

theorem mem_image_iff_bex {f : α → β} {s : Set α} {y : β} :
    y ∈ f !! s ↔ ∃ (x : _)(_ : x ∈ s), f x = y :=
  bex_def.symm
#align set.mem_image_iff_bex Set.mem_image_iff_bex

@[simp]
theorem mem_image (f : α → β) (s : Set α) (y : β) : y ∈ f !! s ↔ ∃ x, x ∈ s ∧ f x = y :=
  Iff.rfl
#align set.mem_image Set.mem_image

theorem image_eta (f : α → β) : f !! s = (fun x => f x) !! s :=
  rfl
#align set.image_eta Set.image_eta

theorem mem_image_of_mem (f : α → β) {x : α} {a : Set α} (h : x ∈ a) : f x ∈ f !! a :=
  ⟨_, h, rfl⟩
#align set.mem_image_of_mem Set.mem_image_of_mem

theorem _root_.Function.Injective.mem_set_image {f : α → β} (hf : Injective f) {s : Set α} {a : α} :
    f a ∈ f !! s ↔ a ∈ s :=
  ⟨fun ⟨_, hb, Eq⟩ => hf Eq ▸ hb, mem_image_of_mem f⟩
#align function.injective.mem_set_image Function.Injective.mem_set_image

theorem ball_image_iff {f : α → β} {s : Set α} {p : β → Prop} :
    (∀ y ∈ f !! s, p y) ↔ ∀ x ∈ s, p (f x) := by simp
#align set.ball_image_iff Set.ball_image_iff

theorem ball_image_of_ball {f : α → β} {s : Set α} {p : β → Prop} (h : ∀ x ∈ s, p (f x)) :
    ∀ y ∈ f !! s, p y :=
  ball_image_iff.2 h
#align set.ball_image_of_ball Set.ball_image_of_ball

theorem bex_image_iff {f : α → β} {s : Set α} {p : β → Prop} :
    (∃ y ∈ f !! s, p y) ↔ ∃ x ∈ s, p (f x) := by simp
#align set.bex_image_iff Set.bex_image_iff

theorem mem_image_elim {f : α → β} {s : Set α} {C : β → Prop} (h : ∀ x : α, x ∈ s → C (f x)) :
    ∀ {y : β}, y ∈ f !! s → C y
  | _, ⟨a, a_in, rfl⟩ => h a a_in
#align set.mem_image_elim Set.mem_image_elim

theorem mem_image_elim_on {f : α → β} {s : Set α} {C : β → Prop} {y : β} (h_y : y ∈ f !! s)
    (h : ∀ x : α, x ∈ s → C (f x)) : C y :=
  mem_image_elim h h_y
#align set.mem_image_elim_on Set.mem_image_elim_on

-- Porting note: used the tactic `safe`, which has not been ported.
@[congr]
theorem image_congr {f g : α → β} {s : Set α} (h : ∀ a ∈ s, f a = g a) : f !! s = g !! s := by
  sorry
  -- safe [ext_iff, iff_def]
#align set.image_congr Set.image_congr

/-- A common special case of `image_congr` -/
theorem image_congr' {f g : α → β} {s : Set α} (h : ∀ x : α, f x = g x) : f !! s = g !! s :=
  image_congr fun x _ => h x
#align set.image_congr' Set.image_congr'

theorem image_comp (f : β → γ) (g : α → β) (a : Set α) : f ∘ g !! a = f !! (g !! a) :=
  Subset.antisymm (ball_image_of_ball fun _ ha => mem_image_of_mem _ <| mem_image_of_mem _ ha)
    (ball_image_of_ball <| ball_image_of_ball fun _ ha => mem_image_of_mem _ ha)
#align set.image_comp Set.image_comp

/-- A variant of `image_comp`, useful for rewriting -/
theorem image_image (g : β → γ) (f : α → β) (s : Set α) : g !! (f !! s) = (fun x => g (f x)) !! s :=
  (image_comp g f s).symm
#align set.image_image Set.image_image

theorem image_comm {β'} {f : β → γ} {g : α → β} {f' : α → β'} {g' : β' → γ}
    (h_comm : ∀ a, f (g a) = g' (f' a)) : (s.image g).image f = (s.image f').image g' := by
  simp_rw [image_image, h_comm]
#align set.image_comm Set.image_comm

theorem _root_.Function.Semiconj.set_image {f : α → β} {ga : α → α} {gb : β → β}
    (h : Function.Semiconj f ga gb) : Function.Semiconj (image f) (image ga) (image gb) := fun s =>
  image_comm h
#align function.semiconj.set_image Function.Semiconj.set_image

theorem _root_.Function.Commute.set_image {f g : α → α} (h : Function.Commute f g) :
    Function.Commute (image f) (image g) :=
  Function.Semiconj.set_image h
#align function.commute.set_image Function.Commute.set_image

/-- Image is monotone with respect to `⊆`. See `Set.monotone_image` for the statement in
terms of `≤`. -/
theorem image_subset {a b : Set α} (f : α → β) (h : a ⊆ b) : f !! a ⊆ f !! b := by
  simp only [subset_def, mem_image]
  exact fun x => fun ⟨w, h1, h2⟩ => ⟨w, h h1, h2⟩
#align set.image_subset Set.image_subset

theorem image_union (f : α → β) (s t : Set α) : f !! (s ∪ t) = f !! s ∪ f !! t :=
  ext fun x =>
    ⟨by rintro ⟨a, h | h, rfl⟩ <;> [left, right] <;> exact ⟨_, h, rfl⟩, by
      rintro (⟨a, h, rfl⟩ | ⟨a, h, rfl⟩) <;> refine' ⟨_, _, rfl⟩ <;> [left, right] <;> exact h⟩
#align set.image_union Set.image_union

@[simp]
theorem image_empty (f : α → β) : f !! ∅ = ∅ := by
  ext
  simp
#align set.image_empty Set.image_empty

theorem image_inter_subset (f : α → β) (s t : Set α) : f !! (s ∩ t) ⊆ f !! s ∩ f !! t :=
  subset_inter (image_subset _ <| inter_subset_left _ _) (image_subset _ <| inter_subset_right _ _)
#align set.image_inter_subset Set.image_inter_subset

theorem image_inter_on {f : α → β} {s t : Set α} (h : ∀ x ∈ t, ∀ y ∈ s, f x = f y → x = y) :
    f !! s ∩ f !! t = f !! (s ∩ t) :=
  Subset.antisymm
    (fun b ⟨⟨a₁, ha₁, h₁⟩, ⟨a₂, ha₂, h₂⟩⟩ =>
      have : a₂ = a₁ := h _ ha₂ _ ha₁ (by simp [*])
      ⟨a₁, ⟨ha₁, this ▸ ha₂⟩, h₁⟩)
    (image_inter_subset _ _ _)
#align set.image_inter_on Set.image_inter_on

theorem image_inter {f : α → β} {s t : Set α} (H : Injective f) : f !! s ∩ f !! t = f !! (s ∩ t) :=
  image_inter_on fun x _ y _ h => H h
#align set.image_inter Set.image_inter

theorem image_univ_of_surjective {ι : Type _} {f : ι → β} (H : Surjective f) : f !! univ = univ :=
  eq_univ_of_forall <| by simpa [image]
#align set.image_univ_of_surjective Set.image_univ_of_surjective

@[simp]
theorem image_singleton {f : α → β} {a : α} : f !! {a} = {f a} := by
  ext
  simp [image, eq_comm]
#align set.image_singleton Set.image_singleton

@[simp]
theorem Nonempty.image_const {s : Set α} (hs : s.Nonempty) (a : β) : (fun _ => a) !! s = {a} :=
  ext fun x =>
    ⟨fun ⟨y, _, h⟩ => h ▸ mem_singleton _, fun h =>
      (eq_of_mem_singleton h).symm ▸ hs.imp fun y hy => ⟨hy, rfl⟩⟩
#align set.nonempty.image_const Set.Nonempty.image_const

@[simp]
theorem image_eq_empty {α β} {f : α → β} {s : Set α} : f !! s = ∅ ↔ s = ∅ := by
  simp only [eq_empty_iff_forall_not_mem]
  exact ⟨fun H a ha => H _ ⟨_, ha, rfl⟩, fun H b ⟨_, ha, _⟩ => H _ ha⟩
#align set.image_eq_empty Set.image_eq_empty

theorem preimage_compl_eq_image_compl [BooleanAlgebra α] (S : Set α) : compl ⁻¹' S = compl !! S :=
  Set.ext fun x =>
    ⟨fun h => ⟨xᶜ, h, compl_compl x⟩, fun h =>
      Exists.elim h fun y hy => (compl_eq_comm.mp hy.2).symm.subst hy.1⟩
#align set.preimage_compl_eq_image_compl Set.preimage_compl_eq_image_compl

theorem mem_compl_image [BooleanAlgebra α] (t : α) (S : Set α) : t ∈ compl !! S ↔ tᶜ ∈ S := by
  simp [← preimage_compl_eq_image_compl]
#align set.mem_compl_image Set.mem_compl_image

/-- A variant of `image_id` -/
@[simp]
theorem image_id' (s : Set α) : (fun x => x) !! s = s := by
  ext
  simp
#align set.image_id' Set.image_id'

theorem image_id (s : Set α) : id !! s = s := by simp
#align set.image_id Set.image_id

theorem compl_compl_image [BooleanAlgebra α] (S : Set α) : compl !! (compl !! S) = S := by
  rw [← image_comp, compl_comp_compl, image_id]
#align set.compl_compl_image Set.compl_compl_image

theorem image_insert_eq {f : α → β} {a : α} {s : Set α} : f !! insert a s = insert (f a) (f !! s) :=
  by
  ext
  simp [and_or_left, exists_or, eq_comm, or_comm', and_comm']
#align set.image_insert_eq Set.image_insert_eq

theorem image_pair (f : α → β) (a b : α) : f !! {a, b} = {f a, f b} := by
  simp only [image_insert_eq, image_singleton]
#align set.image_pair Set.image_pair

theorem image_subset_preimage_of_inverse {f : α → β} {g : β → α} (I : LeftInverse g f) (s : Set α) :
    f !! s ⊆ g ⁻¹' s := fun b ⟨a, h, e⟩ => e ▸ ((I a).symm ▸ h : g (f a) ∈ s)
#align set.image_subset_preimage_of_inverse Set.image_subset_preimage_of_inverse

theorem preimage_subset_image_of_inverse {f : α → β} {g : β → α} (I : LeftInverse g f) (s : Set β) :
    f ⁻¹' s ⊆ g !! s := fun b h => ⟨f b, h, I b⟩
#align set.preimage_subset_image_of_inverse Set.preimage_subset_image_of_inverse

theorem image_eq_preimage_of_inverse {f : α → β} {g : β → α} (h₁ : LeftInverse g f)
    (h₂ : RightInverse g f) : image f = preimage g :=
  funext fun s =>
    Subset.antisymm (image_subset_preimage_of_inverse h₁ s) (preimage_subset_image_of_inverse h₂ s)
#align set.image_eq_preimage_of_inverse Set.image_eq_preimage_of_inverse

theorem mem_image_iff_of_inverse {f : α → β} {g : β → α} {b : β} {s : Set α} (h₁ : LeftInverse g f)
    (h₂ : RightInverse g f) : b ∈ f !! s ↔ g b ∈ s := by
  rw [image_eq_preimage_of_inverse h₁ h₂] <;> rfl
#align set.mem_image_iff_of_inverse Set.mem_image_iff_of_inverse

theorem image_compl_subset {f : α → β} {s : Set α} (H : Injective f) : f !! sᶜ ⊆ (f !! s)ᶜ :=
  Disjoint.subset_compl_left <| by simp [disjoint_iff_inf_le, image_inter H]
#align set.image_compl_subset Set.image_compl_subset

theorem subset_image_compl {f : α → β} {s : Set α} (H : Surjective f) : (f !! s)ᶜ ⊆ f !! sᶜ :=
  compl_subset_iff_union.2 <| by
    rw [← image_union]
    simp [image_univ_of_surjective H]
#align set.subset_image_compl Set.subset_image_compl

theorem image_compl_eq {f : α → β} {s : Set α} (H : Bijective f) : f !! sᶜ = (f !! s)ᶜ :=
  Subset.antisymm (image_compl_subset H.1) (subset_image_compl H.2)
#align set.image_compl_eq Set.image_compl_eq

theorem subset_image_diff (f : α → β) (s t : Set α) : f !! s \ f !! t ⊆ f !! (s \ t) := by
  rw [diff_subset_iff, ← image_union, union_diff_self]
  exact image_subset f (subset_union_right t s)
#align set.subset_image_diff Set.subset_image_diff

theorem subset_image_symm_diff : (f !! s) ∆ (f !! t) ⊆ f !! s ∆ t :=
  (union_subset_union (subset_image_diff _ _ _) <| subset_image_diff _ _ _).trans
    (image_union _ _ _).superset
#align set.subset_image_symm_diff Set.subset_image_symm_diff

theorem image_diff {f : α → β} (hf : Injective f) (s t : Set α) : f !! (s \ t) = f !! s \ f !! t :=
  Subset.antisymm
    (Subset.trans (image_inter_subset _ _ _) <| inter_subset_inter_right _ <| image_compl_subset hf)
    (subset_image_diff f s t)
#align set.image_diff Set.image_diff

theorem image_symm_diff (hf : Injective f) (s t : Set α) : f !! s ∆ t = (f !! s) ∆ (f !! t) := by
  simp_rw [Set.symmDiff_def, image_union, image_diff hf]
#align set.image_symm_diff Set.image_symm_diff

theorem Nonempty.image (f : α → β) {s : Set α} : s.Nonempty → (f !! s).Nonempty
  | ⟨x, hx⟩ => ⟨f x, mem_image_of_mem f hx⟩
#align set.nonempty.image Set.Nonempty.image

theorem Nonempty.of_image {f : α → β} {s : Set α} : (f !! s).Nonempty → s.Nonempty
  | ⟨y, x, hx, _⟩ => ⟨x, hx⟩
#align set.nonempty.of_image Set.Nonempty.of_image

@[simp]
theorem nonempty_image_iff {f : α → β} {s : Set α} : (f !! s).Nonempty ↔ s.Nonempty :=
  ⟨Nonempty.of_image, fun h => h.image f⟩
#align set.nonempty_image_iff Set.nonempty_image_iff

theorem Nonempty.preimage {s : Set β} (hs : s.Nonempty) {f : α → β} (hf : Surjective f) :
    (f ⁻¹' s).Nonempty :=
  let ⟨y, hy⟩ := hs
  let ⟨x, hx⟩ := hf y
  ⟨x, mem_preimage.2 <| hx.symm ▸ hy⟩
#align set.nonempty.preimage Set.Nonempty.preimage

instance (f : α → β) (s : Set α) [Nonempty s] : Nonempty (f !! s) :=
  (Set.Nonempty.image f nonempty_of_nonempty_subtype).to_subtype

/-- image and preimage are a Galois connection -/
@[simp]
theorem image_subset_iff {s : Set α} {t : Set β} {f : α → β} : f !! s ⊆ t ↔ s ⊆ f ⁻¹' t :=
  ball_image_iff
#align set.image_subset_iff Set.image_subset_iff

theorem image_preimage_subset (f : α → β) (s : Set β) : f !! (f ⁻¹' s) ⊆ s :=
  image_subset_iff.2 Subset.rfl
#align set.image_preimage_subset Set.image_preimage_subset

theorem subset_preimage_image (f : α → β) (s : Set α) : s ⊆ f ⁻¹' (f !! s) := fun x =>
  mem_image_of_mem f
#align set.subset_preimage_image Set.subset_preimage_image

theorem preimage_image_eq {f : α → β} (s : Set α) (h : Injective f) : f ⁻¹' (f !! s) = s :=
  Subset.antisymm (fun x ⟨y, hy, e⟩ => h e ▸ hy) (subset_preimage_image f s)
#align set.preimage_image_eq Set.preimage_image_eq

theorem image_preimage_eq {f : α → β} (s : Set β) (h : Surjective f) : f !! (f ⁻¹' s) = s :=
  Subset.antisymm (image_preimage_subset f s) fun x hx =>
    let ⟨y, e⟩ := h x
    ⟨y, (e.symm ▸ hx : f y ∈ s), e⟩
#align set.image_preimage_eq Set.image_preimage_eq

theorem preimage_eq_preimage {f : β → α} (hf : Surjective f) : f ⁻¹' s = f ⁻¹' t ↔ s = t :=
  Iff.intro (fun eq => by rw [← image_preimage_eq s hf, ← image_preimage_eq t hf, eq]) fun eq =>
    eq ▸ rfl
#align set.preimage_eq_preimage Set.preimage_eq_preimage

theorem image_inter_preimage (f : α → β) (s : Set α) (t : Set β) :
    f !! (s ∩ f ⁻¹' t) = f !! s ∩ t := by
  apply Subset.antisymm
  · calc
      f !! (s ∩ f ⁻¹' t) ⊆ f !! s ∩ f !! (f ⁻¹' t) := image_inter_subset _ _ _
      _ ⊆ f !! s ∩ t := inter_subset_inter_right _ (image_preimage_subset f t)

  · rintro _ ⟨⟨x, h', rfl⟩, h⟩
    exact ⟨x, ⟨h', h⟩, rfl⟩
#align set.image_inter_preimage Set.image_inter_preimage

theorem image_preimage_inter (f : α → β) (s : Set α) (t : Set β) :
    f !! (f ⁻¹' t ∩ s) = t ∩ f !! s := by simp only [inter_comm, image_inter_preimage]
#align set.image_preimage_inter Set.image_preimage_inter

@[simp]
theorem image_inter_nonempty_iff {f : α → β} {s : Set α} {t : Set β} :
    (f !! s ∩ t).Nonempty ↔ (s ∩ f ⁻¹' t).Nonempty := by
  rw [← image_inter_preimage, nonempty_image_iff]
#align set.image_inter_nonempty_iff Set.image_inter_nonempty_iff

theorem image_diff_preimage {f : α → β} {s : Set α} {t : Set β} : f !! (s \ f ⁻¹' t) = f !! s \ t :=
  by simp_rw [diff_eq, ← preimage_compl, image_inter_preimage]
#align set.image_diff_preimage Set.image_diff_preimage

theorem compl_image : image (compl : Set α → Set α) = preimage compl :=
  image_eq_preimage_of_inverse compl_compl compl_compl
#align set.compl_image Set.compl_image

theorem compl_image_set_of {p : Set α → Prop} : compl !! { s | p s } = { s | p (sᶜ) } :=
  congr_fun compl_image p
#align set.compl_image_set_of Set.compl_image_set_of

theorem inter_preimage_subset (s : Set α) (t : Set β) (f : α → β) :
    s ∩ f ⁻¹' t ⊆ f ⁻¹' (f !! s ∩ t) := fun _ h => ⟨mem_image_of_mem _ h.left, h.right⟩
#align set.inter_preimage_subset Set.inter_preimage_subset

theorem union_preimage_subset (s : Set α) (t : Set β) (f : α → β) :
    s ∪ f ⁻¹' t ⊆ f ⁻¹' (f !! s ∪ t) := fun _ h =>
  Or.elim h (fun l => Or.inl <| mem_image_of_mem _ l) fun r => Or.inr r
#align set.union_preimage_subset Set.union_preimage_subset

theorem subset_image_union (f : α → β) (s : Set α) (t : Set β) : f !! (s ∪ f ⁻¹' t) ⊆ f !! s ∪ t :=
  image_subset_iff.2 (union_preimage_subset _ _ _)
#align set.subset_image_union Set.subset_image_union

theorem preimage_subset_iff {A : Set α} {B : Set β} {f : α → β} :
    f ⁻¹' B ⊆ A ↔ ∀ a : α, f a ∈ B → a ∈ A :=
  Iff.rfl
#align set.preimage_subset_iff Set.preimage_subset_iff

theorem image_eq_image {f : α → β} (hf : Injective f) : f !! s = f !! t ↔ s = t :=
  Iff.symm <|
    (Iff.intro fun eq => eq ▸ rfl) fun eq => by
      rw [← preimage_image_eq s hf, ← preimage_image_eq t hf, eq]
#align set.image_eq_image Set.image_eq_image

theorem image_subset_image_iff {f : α → β} (hf : Injective f) : f !! s ⊆ f !! t ↔ s ⊆ t := by
  refine' Iff.symm <| (Iff.intro (image_subset f)) fun h => _
  rw [← preimage_image_eq s hf, ← preimage_image_eq t hf]
  exact preimage_mono h
#align set.image_subset_image_iff Set.image_subset_image_iff

theorem prod_quotient_preimage_eq_image [s : Setoid α] (g : Quotient s → β) {h : α → β}
    (Hh : h = g ∘ Quotient.mk'') (r : Set (β × β)) :
    { x : Quotient s × Quotient s | (g x.1, g x.2) ∈ r } =
      (fun a : α × α => (⟦a.1⟧, ⟦a.2⟧)) !! ((fun a : α × α => (h a.1, h a.2)) ⁻¹' r) :=
  Hh.symm ▸
    Set.ext fun ⟨a₁, a₂⟩ =>
      ⟨Quotient.induction_on₂ a₁ a₂ fun a₁ a₂ h => ⟨(a₁, a₂), h, rfl⟩, fun ⟨⟨b₁, b₂⟩, h₁, h₂⟩ =>
        show (g a₁, g a₂) ∈ r from
          have h₃ : ⟦b₁⟧ = a₁ ∧ ⟦b₂⟧ = a₂ := Prod.ext_iff.1 h₂
          h₃.1 ▸ h₃.2 ▸ h₁⟩
#align set.prod_quotient_preimage_eq_image Set.prod_quotient_preimage_eq_image

theorem exists_image_iff (f : α → β) (x : Set α) (P : β → Prop) :
    (∃ a : f !! x, P a) ↔ ∃ a : x, P (f a) :=
  ⟨fun ⟨a, h⟩ => ⟨⟨_, a.prop.some_spec.1⟩, a.prop.some_spec.2.symm ▸ h⟩, fun ⟨a, h⟩ =>
    ⟨⟨_, _, a.prop, rfl⟩, h⟩⟩
#align set.exists_image_iff Set.exists_image_iff

/-- Restriction of `f` to `s` factors through `s.image_factorization f : s → f !! s`. -/
def imageFactorization (f : α → β) (s : Set α) : s → f !! s := fun p =>
  ⟨f p.1, mem_image_of_mem f p.2⟩
#align set.image_factorization Set.imageFactorization

theorem image_factorization_eq {f : α → β} {s : Set α} :
    Subtype.val ∘ imageFactorization f s = f ∘ Subtype.val :=
  funext fun _ => rfl
#align set.image_factorization_eq Set.image_factorization_eq

theorem surjective_onto_image {f : α → β} {s : Set α} : Surjective (imageFactorization f s) :=
  fun ⟨_, ⟨a, ha, rfl⟩⟩ => ⟨⟨a, ha⟩, rfl⟩
#align set.surjective_onto_image Set.surjective_onto_image

/-- If the only elements outside `s` are those left fixed by `σ`, then mapping by `σ` has no effect.
-/
theorem image_perm {s : Set α} {σ : Equiv.Perm α} (hs : { a : α | σ a ≠ a } ⊆ s) : σ !! s = s := by
  ext i
  obtain hi | hi := eq_or_ne (σ i) i
  · refine' ⟨_, fun h => ⟨i, h, hi⟩⟩
    rintro ⟨j, hj, h⟩
    rwa [σ.injective (hi.trans h.symm)]
  · refine' iff_of_true ⟨σ.symm i, hs fun h => hi _, σ.apply_symm_apply _⟩ (hs hi)
    convert congr_arg σ h <;> exact (σ.apply_symm_apply _).symm
#align set.image_perm Set.image_perm

end Image

/-! ### Subsingleton -/


/-- A set `s` is a `subsingleton` if it has at most one element. -/
protected def Subsingleton (s : Set α) : Prop :=
  ∀ ⦃x⦄ (_ : x ∈ s) ⦃y⦄ (_ : y ∈ s), x = y
#align set.subsingleton Set.Subsingleton

theorem Subsingleton.anti (ht : t.Subsingleton) (hst : s ⊆ t) : s.Subsingleton := fun x hx y hy =>
  ht (hst hx) (hst hy)
#align set.subsingleton.anti Set.Subsingleton.anti

theorem Subsingleton.eq_singleton_of_mem (hs : s.Subsingleton) {x : α} (hx : x ∈ s) : s = {x} :=
  ext fun y => ⟨fun hy => hs hx hy ▸ mem_singleton _, fun hy => (eq_of_mem_singleton hy).symm ▸ hx⟩
#align set.subsingleton.eq_singleton_of_mem Set.Subsingleton.eq_singleton_of_mem

@[simp]
theorem subsingleton_empty : (∅ : Set α).Subsingleton := fun x => False.elim
#align set.subsingleton_empty Set.subsingleton_empty

@[simp]
theorem subsingleton_singleton {a} : ({a} : Set α).Subsingleton := fun x hx y hy =>
  (eq_of_mem_singleton hx).symm ▸ (eq_of_mem_singleton hy).symm ▸ rfl
#align set.subsingleton_singleton Set.subsingleton_singleton

theorem subsingleton_of_subset_singleton (h : s ⊆ {a}) : s.Subsingleton :=
  subsingleton_singleton.anti h
#align set.subsingleton_of_subset_singleton Set.subsingleton_of_subset_singleton

theorem subsingleton_of_forall_eq (a : α) (h : ∀ b ∈ s, b = a) : s.Subsingleton := fun b hb c hc =>
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
  exacts[he, h₁ _]
#align set.subsingleton.induction_on Set.Subsingleton.induction_on

theorem subsingleton_univ [Subsingleton α] : (univ : Set α).Subsingleton := fun x hx y hy =>
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

theorem subsingleton_is_top (α : Type _) [PartialOrder α] : Set.Subsingleton { x : α | IsTop x } :=
  fun x hx y hy => hx.isMax.eq_of_le (hy x)
#align set.subsingleton_is_top Set.subsingleton_is_top

theorem subsingleton_is_bot (α : Type _) [PartialOrder α] : Set.Subsingleton { x : α | IsBot x } :=
  fun x hx y hy => hx.isMin.eq_of_ge (hy x)
#align set.subsingleton_is_bot Set.subsingleton_is_bot

theorem exists_eq_singleton_iff_nonempty_subsingleton :
    (∃ a : α, s = {a}) ↔ s.Nonempty ∧ s.Subsingleton := by
  refine' ⟨_, fun h => _⟩
  · rintro ⟨a, rfl⟩
    exact ⟨singleton_nonempty a, subsingleton_singleton⟩
  · exact h.2.eq_empty_or_singleton.resolve_left h.1.ne_empty
#align
  set.exists_eq_singleton_iff_nonempty_subsingleton Set.exists_eq_singleton_iff_nonempty_subsingleton

/-- `s`, coerced to a type, is a subsingleton type if and only if `s` is a subsingleton set. -/
@[simp, norm_cast]
theorem subsingleton_coe (s : Set α) : Subsingleton s ↔ s.Subsingleton := by
  constructor
  · refine' fun h => fun a ha b hb => _
    exact SetCoe.ext_iff.2 (@Subsingleton.elim s h ⟨a, ha⟩ ⟨b, hb⟩)
  · exact fun h => Subsingleton.intro fun a b => SetCoe.ext (h a.property b.property)
#align set.subsingleton_coe Set.subsingleton_coe

theorem Subsingleton.coe_sort {s : Set α} : s.Subsingleton → Subsingleton s :=
  s.subsingleton_coe.2
#align set.subsingleton.coe_sort Set.Subsingleton.coe_sort

/-- The `coe_sort` of a set `s` in a subsingleton type is a subsingleton.
For the corresponding result for `subtype`, see `subtype.subsingleton`. -/
instance subsingleton_coe_of_subsingleton [Subsingleton α] {s : Set α} : Subsingleton s := by
  rw [s.subsingleton_coe]
  exact subsingleton_of_subsingleton
#align set.subsingleton_coe_of_subsingleton Set.subsingleton_coe_of_subsingleton

/-- The image of a subsingleton is a subsingleton. -/
theorem Subsingleton.image (hs : s.Subsingleton) (f : α → β) : (f !! s).Subsingleton :=
  fun _ ⟨x, hx, Hx⟩ _ ⟨y, hy, Hy⟩ => Hx ▸ Hy ▸ congr_arg f (hs hx hy)
#align set.subsingleton.image Set.Subsingleton.image

/-- The preimage of a subsingleton under an injective map is a subsingleton. -/
theorem Subsingleton.preimage {s : Set β} (hs : s.Subsingleton) {f : α → β}
    (hf : Function.Injective f) : (f ⁻¹' s).Subsingleton := fun a ha b hb => hf <| hs ha hb
#align set.subsingleton.preimage Set.Subsingleton.preimage

/-- If the image of a set under an injective map is a subsingleton, the set is a subsingleton. -/
theorem subsingleton_of_image {α β : Type _} {f : α → β} (hf : Function.Injective f) (s : Set α)
    (hs : (f !! s).Subsingleton) : s.Subsingleton :=
  (hs.preimage hf).anti <| subset_preimage_image _ _
#align set.subsingleton_of_image Set.subsingleton_of_image

/-- If the preimage of a set under an surjective map is a subsingleton,
the set is a subsingleton. -/
theorem subsingleton_of_preimage {α β : Type _} {f : α → β} (hf : Function.Surjective f) (s : Set β)
    (hs : (f ⁻¹' s).Subsingleton) : s.Subsingleton := fun fx hx fy hy => by
  rcases hf fx, hf fy with ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
  exact congr_arg f (hs hx hy)
#align set.subsingleton_of_preimage Set.subsingleton_of_preimage

/-! ### Nontrivial -/


/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (x y «expr ∈ » s) -/
/-- A set `s` is `nontrivial` if it has at least two distinct elements. -/
protected def Nontrivial (s : Set α) : Prop :=
  ∃ (x y : _)(_ : x ∈ s)(_ : y ∈ s), x ≠ y
#align set.nontrivial Set.Nontrivial

theorem nontrivial_of_mem_mem_ne {x y} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) : s.Nontrivial :=
  ⟨x, hx, y, hy, hxy⟩
#align set.nontrivial_of_mem_mem_ne Set.nontrivial_of_mem_mem_ne

/-- Extract witnesses from s.nontrivial. This function might be used instead of case analysis on the
argument. Note that it makes a proof depend on the classical.choice axiom. -/
protected noncomputable def Nontrivial.some (hs : s.Nontrivial) : α × α :=
  (hs.some, hs.some_spec.some_spec.some)
#align set.nontrivial.some Set.Nontrivial.some

protected theorem Nontrivial.some_fst_mem (hs : s.Nontrivial) : hs.some.fst ∈ s :=
  hs.some_spec.some
#align set.nontrivial.some_fst_mem Set.Nontrivial.some_fst_mem

protected theorem Nontrivial.some_snd_mem (hs : s.Nontrivial) : hs.some.snd ∈ s :=
  hs.some_spec.some_spec.some_spec.some
#align set.nontrivial.some_snd_mem Set.Nontrivial.some_snd_mem

protected theorem Nontrivial.some_fst_ne_some_snd (hs : s.Nontrivial) : hs.some.fst ≠ hs.some.snd :=
  hs.some_spec.some_spec.some_spec.some_spec
#align set.nontrivial.some_fst_ne_some_snd Set.Nontrivial.some_fst_ne_some_snd

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

theorem Nontrivial.pair_subset (hs : s.Nontrivial) : ∃ (x y : _)(hab : x ≠ y), {x, y} ⊆ s :=
  let ⟨x, hx, y, hy, hxy⟩ := hs
  ⟨x, y, hxy, insert_subset.2 ⟨hx, singleton_subset_iff.2 hy⟩⟩
#align set.nontrivial.pair_subset Set.Nontrivial.pair_subset

theorem nontrivial_iff_pair_subset : s.Nontrivial ↔ ∃ (x y : _) (hxy : x ≠ y), {x, y} ⊆ s :=
  ⟨Nontrivial.pair_subset, fun H =>
    let ⟨x, y, hxy, h⟩ := H
    nontrivial_of_pair_subset hxy h⟩
#align set.nontrivial_iff_pair_subset Set.nontrivial_iff_pair_subset

theorem nontrivial_of_exists_ne {x} (hx : x ∈ s) (h : ∃ y ∈ s, y ≠ x) : s.Nontrivial :=
  let ⟨y, hy, hyx⟩ := h
  ⟨y, hy, x, hx, hyx⟩
#align set.nontrivial_of_exists_ne Set.nontrivial_of_exists_ne

theorem Nontrivial.exists_ne (hs : s.Nontrivial) (z) : ∃ x ∈ s, x ≠ z := by
  by_contra H; push_neg  at H
  rcases hs with ⟨x, hx, y, hy, hxy⟩
  rw [H x hx, H y hy] at hxy
  exact hxy rfl
#align set.nontrivial.exists_ne Set.Nontrivial.exists_ne

theorem nontrivial_iff_exists_ne {x} (hx : x ∈ s) : s.Nontrivial ↔ ∃ y ∈ s, y ≠ x :=
  ⟨fun H => H.exists_ne _, nontrivial_of_exists_ne hx⟩
#align set.nontrivial_iff_exists_ne Set.nontrivial_iff_exists_ne

theorem nontrivial_of_lt [Preorder α] {x y} (hx : x ∈ s) (hy : y ∈ s) (hxy : x < y) :
    s.Nontrivial :=
  ⟨x, hx, y, hy, ne_of_lt hxy⟩
#align set.nontrivial_of_lt Set.nontrivial_of_lt

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (x y «expr ∈ » s) -/
theorem nontrivial_of_exists_lt [Preorder α] (H : ∃ (x y : _)(_ : x ∈ s)(_ : y ∈ s), x < y) :
    s.Nontrivial :=
  let ⟨x, hx, y, hy, hxy⟩ := H
  nontrivial_of_lt hx hy hxy
#align set.nontrivial_of_exists_lt Set.nontrivial_of_exists_lt

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (x y «expr ∈ » s) -/
theorem Nontrivial.exists_lt [LinearOrder α] (hs : s.Nontrivial) :
    ∃ (x y : _)(_ : x ∈ s)(_ : y ∈ s), x < y :=
  let ⟨x, hx, y, hy, hxy⟩ := hs
  Or.elim (lt_or_gt_of_ne hxy) (fun H => ⟨x, hx, y, hy, H⟩) fun H => ⟨y, hy, x, hx, H⟩
#align set.nontrivial.exists_lt Set.Nontrivial.exists_lt

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (x y «expr ∈ » s) -/
theorem nontrivial_iff_exists_lt [LinearOrder α] :
    s.Nontrivial ↔ ∃ (x y : _)(_ : x ∈ s)(_ : y ∈ s), x < y :=
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
  exact
    let ⟨y, hy, hya⟩ := H
    hya (mem_singleton_iff.1 hy)
#align set.not_nontrivial_singleton Set.not_nontrivial_singleton

theorem Nontrivial.ne_singleton {x} (hs : s.Nontrivial) : s ≠ {x} := fun H => by
  rw [H] at hs
  exact not_nontrivial_singleton hs
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

/-- `s`, coerced to a type, is a nontrivial type if and only if `s` is a nontrivial set. -/
@[simp, norm_cast]
theorem nontrivial_coe_sort {s : Set α} : Nontrivial s ↔ s.Nontrivial := by
  simp_rw [← nontrivial_univ_iff, Set.Nontrivial, mem_univ, exists_true_left, SetCoe.exists,
    Subtype.mk_eq_mk]
#align set.nontrivial_coe_sort Set.nontrivial_coe_sort

alias nontrivial_coe_sort ↔ _ Nontrivial.coe_sort

/-- A type with a set `s` whose `coe_sort` is a nontrivial type is nontrivial.
For the corresponding result for `subtype`, see `subtype.nontrivial_iff_exists_ne`. -/
theorem nontrivial_of_nontrivial_coe (hs : Nontrivial s) : Nontrivial α :=
  nontrivial_of_nontrivial <| nontrivial_coe_sort.1 hs
#align set.nontrivial_of_nontrivial_coe Set.nontrivial_of_nontrivial_coe

theorem nontrivial_mono {α : Type _} {s t : Set α} (hst : s ⊆ t) (hs : Nontrivial s) :
    Nontrivial t :=
  Nontrivial.coe_sort <| (nontrivial_coe_sort.1 hs).mono hst
#align set.nontrivial_mono Set.nontrivial_mono

/-- The preimage of a nontrivial set under a surjective map is nontrivial. -/
theorem Nontrivial.preimage {s : Set β} (hs : s.Nontrivial) {f : α → β}
    (hf : Function.Surjective f) : (f ⁻¹' s).Nontrivial := by
  rcases hs with ⟨fx, hx, fy, hy, hxy⟩
  rcases hf fx, hf fy with ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
  exact ⟨x, hx, y, hy, mt (congr_arg f) hxy⟩
#align set.nontrivial.preimage Set.Nontrivial.preimage

/-- The image of a nontrivial set under an injective map is nontrivial. -/
theorem Nontrivial.image (hs : s.Nontrivial) {f : α → β} (hf : Function.Injective f) :
    (f !! s).Nontrivial :=
  let ⟨x, hx, y, hy, hxy⟩ := hs
  ⟨f x, mem_image_of_mem f hx, f y, mem_image_of_mem f hy, hf.ne hxy⟩
#align set.nontrivial.image Set.Nontrivial.image

/-- If the image of a set is nontrivial, the set is nontrivial. -/
theorem nontrivial_of_image (f : α → β) (s : Set α) (hs : (f !! s).Nontrivial) : s.Nontrivial :=
  let ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, hxy⟩ := hs
  ⟨x, hx, y, hy, mt (congr_arg f) hxy⟩
#align set.nontrivial_of_image Set.nontrivial_of_image

/-- If the preimage of a set under an injective map is nontrivial, the set is nontrivial. -/
theorem nontrivial_of_preimage {f : α → β} (hf : Function.Injective f) (s : Set β)
    (hs : (f ⁻¹' s).Nontrivial) : s.Nontrivial :=
  (hs.image hf).mono <| image_preimage_subset _ _
#align set.nontrivial_of_preimage Set.nontrivial_of_preimage

@[simp]
theorem not_subsingleton_iff : ¬s.Subsingleton ↔ s.Nontrivial := by
  simp_rw [Set.Subsingleton, Set.Nontrivial, not_forall]; rfl
#align set.not_subsingleton_iff Set.not_subsingleton_iff

@[simp]
theorem not_nontrivial_iff : ¬s.Nontrivial ↔ s.Subsingleton :=
  Iff.not_left not_subsingleton_iff.symm
#align set.not_nontrivial_iff Set.not_nontrivial_iff

alias not_nontrivial_iff ↔ _ Subsingleton.not_nontrivial

alias not_subsingleton_iff ↔ _ Nontrivial.not_subsingleton

theorem univ_eq_true_false : univ = ({True, False} : Set Prop) :=
  Eq.symm <| eq_univ_of_forall <| Classical.cases (by simp) (by simp)
#align set.univ_eq_true_false Set.univ_eq_true_false

section Preorder

variable [Preorder α] [Preorder β] {f : α → β}

theorem monotone_on_iff_monotone : MonotoneOn f s ↔ Monotone fun a : s => f a := by
  simp [Monotone, MonotoneOn]
#align set.monotone_on_iff_monotone Set.monotone_on_iff_monotone

theorem antitone_on_iff_antitone : AntitoneOn f s ↔ Antitone fun a : s => f a := by
  simp [Antitone, AntitoneOn]
#align set.antitone_on_iff_antitone Set.antitone_on_iff_antitone

theorem strict_mono_on_iff_strict_mono : StrictMonoOn f s ↔ StrictMono fun a : s => f a := by
  simp [StrictMono, StrictMonoOn]
#align set.strict_mono_on_iff_strict_mono Set.strict_mono_on_iff_strict_mono

theorem strict_anti_on_iff_strict_anti : StrictAntiOn f s ↔ StrictAnti fun a : s => f a := by
  simp [StrictAnti, StrictAntiOn]
#align set.strict_anti_on_iff_strict_anti Set.strict_anti_on_iff_strict_anti

variable (f)

/-! ### Monotonicity on singletons -/


protected theorem Subsingleton.monotoneOn (h : s.Subsingleton) : MonotoneOn f s :=
  fun a ha b hb _ => (congr_arg _ (h ha hb)).le
#align set.subsingleton.monotone_on Set.Subsingleton.monotoneOn

protected theorem Subsingleton.antitoneOn (h : s.Subsingleton) : AntitoneOn f s :=
  fun a ha b hb _ => (congr_arg _ (h hb ha)).le
#align set.subsingleton.antitone_on Set.Subsingleton.antitoneOn

protected theorem Subsingleton.strictMonoOn (h : s.Subsingleton) : StrictMonoOn f s :=
  fun a ha b hb hlt => (hlt.ne (h ha hb)).elim
#align set.subsingleton.strict_mono_on Set.Subsingleton.strictMonoOn

protected theorem Subsingleton.strictAntiOn (h : s.Subsingleton) : StrictAntiOn f s :=
  fun a ha b hb hlt => (hlt.ne (h ha hb)).elim
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

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (a b c «expr ∈ » s) -/
/-- A function between linear orders which is neither monotone nor antitone makes a dent upright or
downright. -/
theorem not_monotone_on_not_antitone_on_iff_exists_le_le :
    ¬MonotoneOn f s ∧ ¬AntitoneOn f s ↔
      ∃ (a b c : _)(_ : a ∈ s)(_ : b ∈ s)(_ : c ∈ s),
        a ≤ b ∧ b ≤ c ∧ (f a < f b ∧ f c < f b ∨ f b < f a ∧ f b < f c) :=
  by
  simp [monotone_on_iff_monotone, antitone_on_iff_antitone, and_assoc', exists_and_left,
    not_monotone_not_antitone_iff_exists_le_le, @and_left_comm (_ ∈ s)]
#align
  set.not_monotone_on_not_antitone_on_iff_exists_le_le Set.not_monotone_on_not_antitone_on_iff_exists_le_le

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (a b c «expr ∈ » s) -/
/-- A function between linear orders which is neither monotone nor antitone makes a dent upright or
downright. -/
theorem not_monotone_on_not_antitone_on_iff_exists_lt_lt :
    ¬MonotoneOn f s ∧ ¬AntitoneOn f s ↔
      ∃ (a b c : _)(_ : a ∈ s)(_ : b ∈ s)(_ : c ∈ s),
        a < b ∧ b < c ∧ (f a < f b ∧ f c < f b ∨ f b < f a ∧ f b < f c) :=
  by
  simp [monotone_on_iff_monotone, antitone_on_iff_antitone, and_assoc', exists_and_left,
    not_monotone_not_antitone_iff_exists_lt_lt, @and_left_comm (_ ∈ s)]
#align
  set.not_monotone_on_not_antitone_on_iff_exists_lt_lt Set.not_monotone_on_not_antitone_on_iff_exists_lt_lt

end LinearOrder

/-! ### Lemmas about range of a function. -/


section Range

variable {f : ι → α}

open Function

/-- Range of a function.

This function is more flexible than `f !! univ`, as the image requires that the domain is in Type
and not an arbitrary Sort. -/
def range (f : ι → α) : Set α :=
  { x | ∃ y, f y = x }
#align set.range Set.range

@[simp]
theorem mem_range {x : α} : x ∈ range f ↔ ∃ y, f y = x :=
  Iff.rfl
#align set.mem_range Set.mem_range

@[simp]
theorem mem_range_self (i : ι) : f i ∈ range f :=
  ⟨i, rfl⟩
#align set.mem_range_self Set.mem_range_self

theorem forall_range_iff {p : α → Prop} : (∀ a ∈ range f, p a) ↔ ∀ i, p (f i) := by simp
#align set.forall_range_iff Set.forall_range_iff

theorem forall_subtype_range_iff {p : range f → Prop} :
    (∀ a : range f, p a) ↔ ∀ i, p ⟨f i, mem_range_self _⟩ :=
  ⟨fun H i => H _, fun H ⟨y, i, hi⟩ => by
    subst hi
    apply H⟩
#align set.forall_subtype_range_iff Set.forall_subtype_range_iff

theorem subsingleton_range {α : Sort _} [Subsingleton α] (f : α → β) : (range f).Subsingleton :=
  forall_range_iff.2 fun x => forall_range_iff.2 fun y => congr_arg f (Subsingleton.elim x y)
#align set.subsingleton_range Set.subsingleton_range

theorem exists_range_iff {p : α → Prop} : (∃ a ∈ range f, p a) ↔ ∃ i, p (f i) := by simp
#align set.exists_range_iff Set.exists_range_iff

theorem exists_range_iff' {p : α → Prop} : (∃ a, a ∈ range f ∧ p a) ↔ ∃ i, p (f i) := by
  simpa only [exists_prop] using exists_range_iff
#align set.exists_range_iff' Set.exists_range_iff'

theorem exists_subtype_range_iff {p : range f → Prop} :
    (∃ a : range f, p a) ↔ ∃ i, p ⟨f i, mem_range_self _⟩ :=
  ⟨fun ⟨⟨a, i, hi⟩, ha⟩ => by
    subst a
    exact ⟨i, ha⟩, fun ⟨i, hi⟩ => ⟨_, hi⟩⟩
#align set.exists_subtype_range_iff Set.exists_subtype_range_iff

theorem range_iff_surjective : range f = univ ↔ Surjective f :=
  eq_univ_iff_forall
#align set.range_iff_surjective Set.range_iff_surjective

alias range_iff_surjective ↔ _ _root_.function.surjective.range_eq

@[simp]
theorem image_univ {f : α → β} : f !! univ = range f := by
  ext
  simp [image, range]
#align set.image_univ Set.image_univ

theorem image_subset_range (f : α → β) (s) : f !! s ⊆ range f := by
  rw [← image_univ] <;> exact image_subset _ (subset_univ _)
#align set.image_subset_range Set.image_subset_range

theorem mem_range_of_mem_image (f : α → β) (s) {x : β} (h : x ∈ f !! s) : x ∈ range f :=
  image_subset_range f s h
#align set.mem_range_of_mem_image Set.mem_range_of_mem_image

theorem Nat.mem_range_succ (i : ℕ) : i ∈ range Nat.succ ↔ 0 < i :=
  ⟨by
    rintro ⟨n, rfl⟩
    exact Nat.succ_pos n, fun h => ⟨_, Nat.succ_pred_eq_of_pos h⟩⟩
#align nat.mem_range_succ Nat.mem_range_succ

theorem Nonempty.preimage' {s : Set β} (hs : s.Nonempty) {f : α → β} (hf : s ⊆ Set.range f) :
    (f ⁻¹' s).Nonempty :=
  let ⟨y, hy⟩ := hs
  let ⟨x, hx⟩ := hf hy
  ⟨x, Set.mem_preimage.2 <| hx.symm ▸ hy⟩
#align set.nonempty.preimage' Set.Nonempty.preimage'

theorem range_comp (g : α → β) (f : ι → α) : range (g ∘ f) = g !! range f :=
  Subset.antisymm (forall_range_iff.mpr fun i => mem_image_of_mem g (mem_range_self _))
    (ball_image_iff.mpr <| forall_range_iff.mpr mem_range_self)
#align set.range_comp Set.range_comp

theorem range_subset_iff : range f ⊆ s ↔ ∀ y, f y ∈ s :=
  forall_range_iff
#align set.range_subset_iff Set.range_subset_iff

theorem range_eq_iff (f : α → β) (s : Set β) :
    range f = s ↔ (∀ a, f a ∈ s) ∧ ∀ b ∈ s, ∃ a, f a = b := by
  rw [← range_subset_iff]
  exact le_antisymm_iff
#align set.range_eq_iff Set.range_eq_iff

theorem range_comp_subset_range (f : α → β) (g : β → γ) : range (g ∘ f) ⊆ range g := by
  rw [range_comp] <;> apply image_subset_range
#align set.range_comp_subset_range Set.range_comp_subset_range

theorem range_nonempty_iff_nonempty : (range f).Nonempty ↔ Nonempty ι :=
  ⟨fun ⟨y, x, hxy⟩ => ⟨x⟩, fun ⟨x⟩ => ⟨f x, mem_range_self x⟩⟩
#align set.range_nonempty_iff_nonempty Set.range_nonempty_iff_nonempty

theorem range_nonempty [h : Nonempty ι] (f : ι → α) : (range f).Nonempty :=
  range_nonempty_iff_nonempty.2 h
#align set.range_nonempty Set.range_nonempty

@[simp]
theorem range_eq_empty_iff {f : ι → α} : range f = ∅ ↔ IsEmpty ι := by
  rw [← not_nonempty_iff, ← range_nonempty_iff_nonempty, not_nonempty_iff_eq_empty]
#align set.range_eq_empty_iff Set.range_eq_empty_iff

theorem range_eq_empty [IsEmpty ι] (f : ι → α) : range f = ∅ :=
  range_eq_empty_iff.2 ‹_›
#align set.range_eq_empty Set.range_eq_empty

instance [Nonempty ι] (f : ι → α) : Nonempty (range f) :=
  (range_nonempty f).to_subtype

@[simp]
theorem image_union_image_compl_eq_range (f : α → β) : f !! s ∪ f !! sᶜ = range f := by
  rw [← image_union, ← image_univ, ← union_compl_self]
#align set.image_union_image_compl_eq_range Set.image_union_image_compl_eq_range

theorem insert_image_compl_eq_range (f : α → β) (x : α) : insert (f x) (f !! {x}ᶜ) = range f := by
  ext y; rw [mem_range, mem_insert_iff, mem_image]
  constructor
  · rintro (h | ⟨x', hx', h⟩)
    · exact ⟨x, h.symm⟩
    · exact ⟨x', h⟩
  · rintro ⟨x', h⟩
    by_cases hx : x' = x
    · left
      rw [← h, hx]
    · right
      refine' ⟨_, _, h⟩
      rw [mem_compl_singleton_iff]
      exact hx
#align set.insert_image_compl_eq_range Set.insert_image_compl_eq_range

theorem image_preimage_eq_inter_range {f : α → β} {t : Set β} : f !! (f ⁻¹' t) = t ∩ range f :=
  ext fun x =>
    ⟨fun ⟨x, hx, HEq⟩ => HEq ▸ ⟨hx, mem_range_self _⟩, fun ⟨hx, ⟨y, h_eq⟩⟩ =>
      h_eq ▸ mem_image_of_mem f <| show y ∈ f ⁻¹' t by simp [preimage, h_eq, hx]⟩
#align set.image_preimage_eq_inter_range Set.image_preimage_eq_inter_range

theorem image_preimage_eq_of_subset {f : α → β} {s : Set β} (hs : s ⊆ range f) :
    f !! (f ⁻¹' s) = s := by rw [image_preimage_eq_inter_range, inter_eq_self_of_subset_left hs]
#align set.image_preimage_eq_of_subset Set.image_preimage_eq_of_subset

theorem image_preimage_eq_iff {f : α → β} {s : Set β} : f !! (f ⁻¹' s) = s ↔ s ⊆ range f :=
  ⟨by
    intro h
    rw [← h]
    apply image_subset_range, image_preimage_eq_of_subset⟩
#align set.image_preimage_eq_iff Set.image_preimage_eq_iff

theorem subset_range_iff_exists_image_eq {f : α → β} {s : Set β} : s ⊆ range f ↔ ∃ t, f !! t = s :=
  ⟨fun h => ⟨_, image_preimage_eq_iff.2 h⟩, fun ⟨t, ht⟩ => ht ▸ image_subset_range _ _⟩
#align set.subset_range_iff_exists_image_eq Set.subset_range_iff_exists_image_eq

@[simp]
theorem exists_subset_range_and_iff {f : α → β} {p : Set β → Prop} :
    (∃ s, s ⊆ range f ∧ p s) ↔ ∃ s, p (f !! s) :=
  ⟨fun ⟨s, hsf, hps⟩ => ⟨f ⁻¹' s, (image_preimage_eq_of_subset hsf).symm ▸ hps⟩, fun ⟨s, hs⟩ =>
    ⟨f !! s, image_subset_range _ _, hs⟩⟩
#align set.exists_subset_range_and_iff Set.exists_subset_range_and_iff

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (s «expr ⊆ » range[set.range] f) -/
theorem exists_subset_range_iff {f : α → β} {p : Set β → Prop} :
    (∃ (s : _)(_ : s ⊆ range f), p s) ↔ ∃ s, p (f !! s) := by
  simp only [exists_prop, exists_subset_range_and_iff]
#align set.exists_subset_range_iff Set.exists_subset_range_iff

theorem range_image (f : α → β) : range (image f) = 𝒫 range f :=
  ext fun s => subset_range_iff_exists_image_eq.symm
#align set.range_image Set.range_image

theorem preimage_subset_preimage_iff {s t : Set α} {f : β → α} (hs : s ⊆ range f) :
    f ⁻¹' s ⊆ f ⁻¹' t ↔ s ⊆ t := by
  constructor
  · intro h x hx
    rcases hs hx with ⟨y, rfl⟩
    exact h hx
  intro h x; apply h
#align set.preimage_subset_preimage_iff Set.preimage_subset_preimage_iff

theorem preimage_eq_preimage' {s t : Set α} {f : β → α} (hs : s ⊆ range f) (ht : t ⊆ range f) :
    f ⁻¹' s = f ⁻¹' t ↔ s = t := by
  constructor
  · intro h
    apply Subset.antisymm
    rw [← preimage_subset_preimage_iff hs, h]
    rw [← preimage_subset_preimage_iff ht, h]
  rintro rfl; rfl
#align set.preimage_eq_preimage' Set.preimage_eq_preimage'

@[simp]
theorem preimage_inter_range {f : α → β} {s : Set β} : f ⁻¹' (s ∩ range f) = f ⁻¹' s :=
  Set.ext fun x => and_iff_left ⟨x, rfl⟩
#align set.preimage_inter_range Set.preimage_inter_range

@[simp]
theorem preimage_range_inter {f : α → β} {s : Set β} : f ⁻¹' (range f ∩ s) = f ⁻¹' s := by
  rw [inter_comm, preimage_inter_range]
#align set.preimage_range_inter Set.preimage_range_inter

theorem preimage_image_preimage {f : α → β} {s : Set β} : f ⁻¹' (f !! (f ⁻¹' s)) = f ⁻¹' s := by
  rw [image_preimage_eq_inter_range, preimage_inter_range]
#align set.preimage_image_preimage Set.preimage_image_preimage

@[simp]
theorem range_id : range (@id α) = univ :=
  range_iff_surjective.2 surjective_id
#align set.range_id Set.range_id

@[simp]
theorem range_id' : (range fun x : α => x) = univ :=
  range_id
#align set.range_id' Set.range_id'

@[simp]
theorem Prod.range_fst [Nonempty β] : range (Prod.fst : α × β → α) = univ :=
  Prod.fst_surjective.range_eq
#align prod.range_fst Prod.range_fst

@[simp]
theorem Prod.range_snd [Nonempty α] : range (Prod.snd : α × β → β) = univ :=
  Prod.snd_surjective.range_eq
#align prod.range_snd Prod.range_snd

@[simp]
theorem range_eval {ι : Type _} {α : ι → Sort _} [∀ i, Nonempty (α i)] (i : ι) :
    range (eval i : (∀ i, α i) → α i) = univ :=
  (surjective_eval i).range_eq
#align set.range_eval Set.range_eval

theorem is_compl_range_inl_range_inr : IsCompl (range <| @Sum.inl α β) (range Sum.inr) :=
  IsCompl.of_le
    (by
      rintro y ⟨⟨x₁, rfl⟩, ⟨x₂, _⟩⟩
      cc)
    (by rintro (x | y) - <;> [left, right] <;> exact mem_range_self _)
#align set.is_compl_range_inl_range_inr Set.is_compl_range_inl_range_inr

@[simp]
theorem range_inl_union_range_inr : range (Sum.inl : α → Sum α β) ∪ range Sum.inr = univ :=
  is_compl_range_inl_range_inr.sup_eq_top
#align set.range_inl_union_range_inr Set.range_inl_union_range_inr

@[simp]
theorem range_inl_inter_range_inr : range (Sum.inl : α → Sum α β) ∩ range Sum.inr = ∅ :=
  is_compl_range_inl_range_inr.inf_eq_bot
#align set.range_inl_inter_range_inr Set.range_inl_inter_range_inr

@[simp]
theorem range_inr_union_range_inl : range (Sum.inr : β → Sum α β) ∪ range Sum.inl = univ :=
  is_compl_range_inl_range_inr.symm.sup_eq_top
#align set.range_inr_union_range_inl Set.range_inr_union_range_inl

@[simp]
theorem range_inr_inter_range_inl : range (Sum.inr : β → Sum α β) ∩ range Sum.inl = ∅ :=
  is_compl_range_inl_range_inr.symm.inf_eq_bot
#align set.range_inr_inter_range_inl Set.range_inr_inter_range_inl

@[simp]
theorem preimage_inl_image_inr (s : Set β) : Sum.inl ⁻¹' (@Sum.inr α β !! s) = ∅ := by
  ext
  simp
#align set.preimage_inl_image_inr Set.preimage_inl_image_inr

@[simp]
theorem preimage_inr_image_inl (s : Set α) : Sum.inr ⁻¹' (@Sum.inl α β !! s) = ∅ := by
  ext
  simp
#align set.preimage_inr_image_inl Set.preimage_inr_image_inl

@[simp]
theorem preimage_inl_range_inr : Sum.inl ⁻¹' range (Sum.inr : β → Sum α β) = ∅ := by
  rw [← image_univ, preimage_inl_image_inr]
#align set.preimage_inl_range_inr Set.preimage_inl_range_inr

@[simp]
theorem preimage_inr_range_inl : Sum.inr ⁻¹' range (Sum.inl : α → Sum α β) = ∅ := by
  rw [← image_univ, preimage_inr_image_inl]
#align set.preimage_inr_range_inl Set.preimage_inr_range_inl

@[simp]
theorem compl_range_inl : range (Sum.inl : α → Sum α β)ᶜ = range (Sum.inr : β → Sum α β) :=
  IsCompl.compl_eq is_compl_range_inl_range_inr
#align set.compl_range_inl Set.compl_range_inl

@[simp]
theorem compl_range_inr : range (Sum.inr : β → Sum α β)ᶜ = range (Sum.inl : α → Sum α β) :=
  IsCompl.compl_eq is_compl_range_inl_range_inr.symm
#align set.compl_range_inr Set.compl_range_inr

theorem image_preimage_inl_union_image_preimage_inr (s : Set (Sum α β)) :
    Sum.inl !! (Sum.inl ⁻¹' s) ∪ Sum.inr !! (Sum.inr ⁻¹' s) = s := by
  rw [image_preimage_eq_inter_range, image_preimage_eq_inter_range, ← inter_distrib_left,
    range_inl_union_range_inr, inter_univ]
#align
  set.image_preimage_inl_union_image_preimage_inr Set.image_preimage_inl_union_image_preimage_inr

@[simp]
theorem range_quot_mk (r : α → α → Prop) : range (Quot.mk r) = univ :=
  (surjective_quot_mk r).range_eq
#align set.range_quot_mk Set.range_quot_mk

@[simp]
theorem range_quot_lift {r : ι → ι → Prop} (hf : ∀ x y, r x y → f x = f y) :
    range (Quot.lift f hf) = range f :=
  ext fun y => (surjective_quot_mk _).exists
#align set.range_quot_lift Set.range_quot_lift

@[simp]
theorem range_quotient_mk [Setoid α] : (range fun x : α => ⟦x⟧) = univ :=
  range_quot_mk _
#align set.range_quotient_mk Set.range_quotient_mk

@[simp]
theorem range_quotient_lift [s : Setoid ι] (hf) :
    range (Quotient.lift f hf : Quotient s → α) = range f :=
  range_quot_lift _
#align set.range_quotient_lift Set.range_quotient_lift

@[simp]
theorem range_quotient_mk' {s : Setoid α} : range (Quotient.mk' : α → Quotient s) = univ :=
  range_quot_mk _
#align set.range_quotient_mk' Set.range_quotient_mk'

@[simp]
theorem range_quotient_lift_on' {s : Setoid ι} (hf) :
    (range fun x : Quotient s => Quotient.liftOn' x f hf) = range f :=
  range_quot_lift _
#align set.range_quotient_lift_on' Set.range_quotient_lift_on'

-- Porting note: commenting out until CanLift arrives from
-- https://github.com/leanprover-community/mathlib4/pull/723
-- instance canLift (c) (p) [CanLift α β c p] :
--     CanLift (Set α) (Set β) ((· !! ·) c) fun s =>
--       ∀ x ∈ s,
--         p
--           x where prf s hs :=
--     subset_range_iff_exists_image_eq.mp fun x hx => CanLift.prf _ (hs x hx)
-- #align set.can_lift Set.canLift

theorem range_const_subset {c : α} : (range fun x : ι => c) ⊆ {c} :=
  range_subset_iff.2 fun x => rfl
#align set.range_const_subset Set.range_const_subset

@[simp]
theorem range_const : ∀ [Nonempty ι] {c : α}, (range fun x : ι => c) = {c}
  | ⟨x⟩, c =>
    (Subset.antisymm range_const_subset) fun y hy =>
      (mem_singleton_iff.1 hy).symm ▸ mem_range_self x
#align set.range_const Set.range_const

theorem range_subtype_map {p : α → Prop} {q : β → Prop} (f : α → β) (h : ∀ x, p x → q (f x)) :
    range (Subtype.map f h) = coe ⁻¹' (f !! { x | p x }) := by
  ext ⟨x, hx⟩
  simp_rw [mem_preimage, mem_range, mem_image, Subtype.exists, Subtype.map, Subtype.coe_mk,
    mem_set_of, exists_prop]
#align set.range_subtype_map Set.range_subtype_map

theorem image_swap_eq_preimage_swap : image (@Prod.swap α β) = preimage Prod.swap :=
  image_eq_preimage_of_inverse Prod.swap_leftInverse Prod.swap_rightInverse
#align set.image_swap_eq_preimage_swap Set.image_swap_eq_preimage_swap

theorem preimage_singleton_nonempty {f : α → β} {y : β} : (f ⁻¹' {y}).Nonempty ↔ y ∈ range f :=
  Iff.rfl
#align set.preimage_singleton_nonempty Set.preimage_singleton_nonempty

theorem preimage_singleton_eq_empty {f : α → β} {y : β} : f ⁻¹' {y} = ∅ ↔ y ∉ range f :=
  not_nonempty_iff_eq_empty.symm.trans preimage_singleton_nonempty.not
#align set.preimage_singleton_eq_empty Set.preimage_singleton_eq_empty

theorem range_subset_singleton {f : ι → α} {x : α} : range f ⊆ {x} ↔ f = const ι x := by
  simp [range_subset_iff, funext_iff, mem_singleton]
#align set.range_subset_singleton Set.range_subset_singleton

theorem image_compl_preimage {f : α → β} {s : Set β} : f !! (f ⁻¹' s)ᶜ = range f \ s := by
  rw [compl_eq_univ_diff, image_diff_preimage, image_univ]
#align set.image_compl_preimage Set.image_compl_preimage

/-- Any map `f : ι → β` factors through a map `range_factorization f : ι → range f`. -/
def rangeFactorization (f : ι → β) : ι → range f := fun i => ⟨f i, mem_range_self i⟩
#align set.range_factorization Set.rangeFactorization

theorem range_factorization_eq {f : ι → β} : Subtype.val ∘ rangeFactorization f = f :=
  funext fun i => rfl
#align set.range_factorization_eq Set.range_factorization_eq

@[simp]
theorem range_factorization_coe (f : ι → β) (a : ι) : (rangeFactorization f a : β) = f a :=
  rfl
#align set.range_factorization_coe Set.range_factorization_coe

@[simp]
theorem coe_comp_range_factorization (f : ι → β) : coe ∘ rangeFactorization f = f :=
  rfl
#align set.coe_comp_range_factorization Set.coe_comp_range_factorization

theorem surjective_onto_range : Surjective (rangeFactorization f) := fun ⟨_, ⟨i, rfl⟩⟩ => ⟨i, rfl⟩
#align set.surjective_onto_range Set.surjective_onto_range

theorem image_eq_range (f : α → β) (s : Set α) : f !! s = range fun x : s => f x := by
  ext
  constructor
  rintro ⟨x, h1, h2⟩
  exact ⟨⟨x, h1⟩, h2⟩
  rintro ⟨⟨x, h1⟩, h2⟩
  exact ⟨x, h1, h2⟩
#align set.image_eq_range Set.image_eq_range

theorem _root_.Sum.range_eq (f : Sum α β → γ) : range f = range (f ∘ Sum.inl) ∪ range (f ∘ Sum.inr) :=
  ext fun x => Sum.exists
#align sum.range_eq Sum.range_eq

@[simp]
theorem _root_.Sum.elim_range (f : α → γ) (g : β → γ) : range (Sum.elim f g) = range f ∪ range g :=
  Sum.range_eq _
#align set.sum.elim_range Sum.elim_range

theorem range_ite_subset' {p : Prop} [Decidable p] {f g : α → β} :
    range (if p then f else g) ⊆ range f ∪ range g := by
  by_cases h : p;
  · rw [if_pos h]
    exact subset_union_left _ _
  · rw [if_neg h]
    exact subset_union_right _ _
#align set.range_ite_subset' Set.range_ite_subset'

theorem range_ite_subset {p : α → Prop} [DecidablePred p] {f g : α → β} :
    (range fun x => if p x then f x else g x) ⊆ range f ∪ range g := by
  rw [range_subset_iff]; intro x; by_cases h : p x
  simp [if_pos h, mem_union, mem_range_self]
  simp [if_neg h, mem_union, mem_range_self]
#align set.range_ite_subset Set.range_ite_subset

@[simp]
theorem preimage_range (f : α → β) : f ⁻¹' range f = univ :=
  eq_univ_of_forall mem_range_self
#align set.preimage_range Set.preimage_range

/-- The range of a function from a `unique` type contains just the
function applied to its single value. -/
theorem range_unique [h : Unique ι] : range f = {f default} := by
  ext x
  rw [mem_range]
  constructor
  · rintro ⟨i, hi⟩
    rw [h.uniq i] at hi
    exact hi ▸ mem_singleton _
  · exact fun h => ⟨default, h.symm⟩
#align set.range_unique Set.range_unique

theorem range_diff_image_subset (f : α → β) (s : Set α) : range f \ f !! s ⊆ f !! sᶜ :=
  fun y ⟨⟨x, h₁⟩, h₂⟩ => ⟨x, fun h => h₂ ⟨x, h, h₁⟩, h₁⟩
#align set.range_diff_image_subset Set.range_diff_image_subset

theorem range_diff_image {f : α → β} (H : Injective f) (s : Set α) : range f \ f !! s = f !! sᶜ :=
  (Subset.antisymm (range_diff_image_subset f s)) fun y ⟨x, hx, hy⟩ =>
    hy ▸ ⟨mem_range_self _, fun ⟨x', hx', Eq⟩ => hx <| H Eq ▸ hx'⟩
#align set.range_diff_image Set.range_diff_image

/-- We can use the axiom of choice to pick a preimage for every element of `range f`. -/
noncomputable def rangeSplitting (f : α → β) : range f → α := fun x => x.2.some
#align set.range_splitting Set.rangeSplitting

-- This can not be a `@[simp]` lemma because the head of the left hand side is a variable.
theorem apply_range_splitting (f : α → β) (x : range f) : f (rangeSplitting f x) = x :=
  x.2.some_spec
#align set.apply_range_splitting Set.apply_range_splitting

@[simp]
theorem comp_range_splitting (f : α → β) : f ∘ rangeSplitting f = coe := by
  ext
  simp only [Function.comp_apply]
  apply apply_range_splitting
#align set.comp_range_splitting Set.comp_range_splitting

-- When `f` is injective, see also `equiv.of_injective`.
theorem left_inverse_range_splitting (f : α → β) :
    LeftInverse (rangeFactorization f) (rangeSplitting f) := fun x => by
  ext
  simp only [range_factorization_coe]
  apply apply_range_splitting
#align set.left_inverse_range_splitting Set.left_inverse_range_splitting

theorem range_splitting_injective (f : α → β) : Injective (rangeSplitting f) :=
  (left_inverse_range_splitting f).injective
#align set.range_splitting_injective Set.range_splitting_injective

theorem right_inverse_range_splitting {f : α → β} (h : Injective f) :
    RightInverse (rangeFactorization f) (rangeSplitting f) :=
  (left_inverse_range_splitting f).right_inverse_of_injective fun x y hxy =>
    h <| Subtype.ext_iff.1 hxy
#align set.right_inverse_range_splitting Set.right_inverse_range_splitting

theorem preimage_range_splitting {f : α → β} (hf : Injective f) :
    preimage (rangeSplitting f) = image (rangeFactorization f) :=
  (image_eq_preimage_of_inverse (right_inverse_range_splitting hf)
      (left_inverse_range_splitting f)).symm
#align set.preimage_range_splitting Set.preimage_range_splitting

theorem is_compl_range_some_none (α : Type _) : IsCompl (range (some : α → Option α)) {none} :=
  IsCompl.of_le (fun x ⟨⟨a, ha⟩, (hn : x = none)⟩ => Option.some_ne_none _ (ha.trans hn))
    fun x hx => Option.casesOn x (Or.inr rfl) fun x => Or.inl <| mem_range_self _
#align set.is_compl_range_some_none Set.is_compl_range_some_none

@[simp]
theorem compl_range_some (α : Type _) : range (some : α → Option α)ᶜ = {none} :=
  (is_compl_range_some_none α).compl_eq
#align set.compl_range_some Set.compl_range_some

@[simp]
theorem range_some_inter_none (α : Type _) : range (some : α → Option α) ∩ {none} = ∅ :=
  (is_compl_range_some_none α).inf_eq_bot
#align set.range_some_inter_none Set.range_some_inter_none

@[simp]
theorem range_some_union_none (α : Type _) : range (some : α → Option α) ∪ {none} = univ :=
  (is_compl_range_some_none α).sup_eq_top
#align set.range_some_union_none Set.range_some_union_none

@[simp]
theorem insert_none_range_some (α : Type _) : insert none (range (some : α → Option α)) = univ :=
  (is_compl_range_some_none α).symm.sup_eq_top
#align set.insert_none_range_some Set.insert_none_range_some

end Range

end Set

open Set

namespace Function

variable {ι : Sort _} {α : Type _} {β : Type _} {f : α → β}

theorem Surjective.preimage_injective (hf : Surjective f) : Injective (preimage f) := fun s t =>
  (preimage_eq_preimage hf).1
#align function.surjective.preimage_injective Function.Surjective.preimage_injective

theorem Injective.preimage_image (hf : Injective f) (s : Set α) : f ⁻¹' (f !! s) = s :=
  preimage_image_eq s hf
#align function.injective.preimage_image Function.Injective.preimage_image

theorem Injective.preimage_surjective (hf : Injective f) : Surjective (preimage f) := by
  intro s
  use f !! s
  rw [hf.preimage_image]
#align function.injective.preimage_surjective Function.Injective.preimage_surjective

theorem Injective.subsingleton_image_iff (hf : Injective f) {s : Set α} :
    (f !! s).Subsingleton ↔ s.Subsingleton :=
  ⟨subsingleton_of_image hf s, fun h => h.image f⟩
#align function.injective.subsingleton_image_iff Function.Injective.subsingleton_image_iff

theorem Surjective.image_preimage (hf : Surjective f) (s : Set β) : f !! (f ⁻¹' s) = s :=
  image_preimage_eq s hf
#align function.surjective.image_preimage Function.Surjective.image_preimage

theorem Surjective.image_surjective (hf : Surjective f) : Surjective (image f) := by
  intro s
  use f ⁻¹' s
  rw [hf.image_preimage]
#align function.surjective.image_surjective Function.Surjective.image_surjective

theorem Surjective.nonempty_preimage (hf : Surjective f) {s : Set β} :
    (f ⁻¹' s).Nonempty ↔ s.Nonempty := by rw [← nonempty_image_iff, hf.image_preimage]
#align function.surjective.nonempty_preimage Function.Surjective.nonempty_preimage

theorem Injective.image_injective (hf : Injective f) : Injective (image f) := by
  intro s t h
  rw [← preimage_image_eq s hf, ← preimage_image_eq t hf, h]
#align function.injective.image_injective Function.Injective.image_injective

theorem Surjective.preimage_subset_preimage_iff {s t : Set β} (hf : Surjective f) :
    f ⁻¹' s ⊆ f ⁻¹' t ↔ s ⊆ t := by
  apply preimage_subset_preimage_iff
  rw [hf.range_eq]
  apply subset_univ
#align
  function.surjective.preimage_subset_preimage_iff Function.Surjective.preimage_subset_preimage_iff

theorem Surjective.range_comp {ι' : Sort _} {f : ι → ι'} (hf : Surjective f) (g : ι' → α) :
    range (g ∘ f) = range g :=
  ext fun y => (@Surjective.exists _ _ _ hf fun x => g x = y).symm
#align function.surjective.range_comp Function.Surjective.range_comp

theorem Injective.nonempty_apply_iff {f : Set α → Set β} (hf : Injective f) (h2 : f ∅ = ∅)
    {s : Set α} : (f s).Nonempty ↔ s.Nonempty := by
  rw [nonempty_iff_ne_empty, ← h2, nonempty_iff_ne_empty, hf.ne_iff]
#align function.injective.nonempty_apply_iff Function.Injective.nonempty_apply_iff

theorem Injective.mem_range_iff_exists_unique (hf : Injective f) {b : β} :
    b ∈ range f ↔ ∃! a, f a = b :=
  ⟨fun ⟨a, h⟩ => ⟨a, h, fun a' ha => hf (ha.trans h.symm)⟩, ExistsUnique.exists⟩
#align function.injective.mem_range_iff_exists_unique Function.Injective.mem_range_iff_exists_unique

theorem Injective.exists_unique_of_mem_range (hf : Injective f) {b : β} (hb : b ∈ range f) :
    ∃! a, f a = b :=
  hf.mem_range_iff_exists_unique.mp hb
#align function.injective.exists_unique_of_mem_range Function.Injective.exists_unique_of_mem_range

theorem Injective.compl_image_eq (hf : Injective f) (s : Set α) : (f !! s)ᶜ = f !! sᶜ ∪ range fᶜ :=
  by
  ext y
  rcases em (y ∈ range f) with (⟨x, rfl⟩ | hx)
  · simp [hf.eq_iff]
  · rw [mem_range, not_exists] at hx
    simp [hx]
#align function.injective.compl_image_eq Function.Injective.compl_image_eq

theorem LeftInverse.image_image {g : β → α} (h : LeftInverse g f) (s : Set α) : g !! (f !! s) = s :=
  by rw [← image_comp, h.comp_eq_id, image_id]
#align function.left_inverse.image_image Function.LeftInverse.image_image

theorem LeftInverse.preimage_preimage {g : β → α} (h : LeftInverse g f) (s : Set α) :
    f ⁻¹' (g ⁻¹' s) = s := by rw [← preimage_comp, h.comp_eq_id, preimage_id]
#align function.left_inverse.preimage_preimage Function.LeftInverse.preimage_preimage

end Function

open Function

namespace Option

theorem injective_iff {α β} {f : Option α → β} :
    Injective f ↔ Injective (f ∘ some) ∧ f none ∉ range (f ∘ some) := by
  simp only [mem_range, not_exists, (· ∘ ·)]
  refine'
    ⟨fun hf => ⟨hf.comp (Option.some_injective _), fun x => hf.ne <| Option.some_ne_none _⟩, _⟩
  rintro ⟨h_some, h_none⟩ (_ | a) (_ | b) hab
  exacts[rfl, (h_none _ hab.symm).elim, (h_none _ hab).elim, congr_arg some (h_some hab)]
#align option.injective_iff Option.injective_iff

theorem range_eq {α β} (f : Option α → β) : range f = insert (f none) (range (f ∘ some)) :=
  Set.ext fun y => Option.exists.trans <| eq_comm.or Iff.rfl
#align option.range_eq Option.range_eq

end Option

theorem WithBot.range_eq {α β} (f : WithBot α → β) :
    range f = insert (f ⊥) (range (f ∘ coe : α → β)) :=
  Option.range_eq f
#align with_bot.range_eq WithBot.range_eq

theorem WithTop.range_eq {α β} (f : WithTop α → β) :
    range f = insert (f ⊤) (range (f ∘ coe : α → β)) :=
  Option.range_eq f
#align with_top.range_eq WithTop.range_eq

/-! ### Image and preimage on subtypes -/


namespace Subtype

variable {α : Type _}

theorem coe_image {p : α → Prop} {s : Set (Subtype p)} :
    coe !! s = { x | ∃ h : p x, (⟨x, h⟩ : Subtype p) ∈ s } :=
  Set.ext fun a =>
    ⟨fun ⟨⟨a', ha'⟩, in_s, h_eq⟩ => h_eq ▸ ⟨ha', in_s⟩, fun ⟨ha, in_s⟩ => ⟨⟨a, ha⟩, in_s, rfl⟩⟩
#align subtype.coe_image Subtype.coe_image

@[simp]
theorem coe_image_of_subset {s t : Set α} (h : t ⊆ s) : coe !! { x : ↥s | ↑x ∈ t } = t := by
  ext x
  rw [Set.mem_image]
  exact ⟨fun ⟨x', hx', hx⟩ => hx ▸ hx', fun hx => ⟨⟨x, h hx⟩, hx, rfl⟩⟩
#align subtype.coe_image_of_subset Subtype.coe_image_of_subset

theorem range_coe {s : Set α} : range (coe : s → α) = s := by
  rw [← Set.image_univ]
  simp [-Set.image_univ, coe_image]
#align subtype.range_coe Subtype.range_coe

/-- A variant of `range_coe`. Try to use `range_coe` if possible.
  This version is useful when defining a new type that is defined as the subtype of something.
  In that case, the coercion doesn't fire anymore. -/
theorem range_val {s : Set α} : range (Subtype.val : s → α) = s :=
  range_coe
#align subtype.range_val Subtype.range_val

/-- We make this the simp lemma instead of `range_coe`. The reason is that if we write
  for `s : set α` the function `coe : s → α`, then the inferred implicit arguments of `coe` are
  `coe α (λ x, x ∈ s)`. -/
@[simp]
theorem range_coe_subtype {p : α → Prop} : range (coe : Subtype p → α) = { x | p x } :=
  range_coe
#align subtype.range_coe_subtype Subtype.range_coe_subtype

@[simp]
theorem coe_preimage_self (s : Set α) : (coe : s → α) ⁻¹' s = univ := by
  rw [← preimage_range (coe : s → α), range_coe]
#align subtype.coe_preimage_self Subtype.coe_preimage_self

theorem range_val_subtype {p : α → Prop} : range (Subtype.val : Subtype p → α) = { x | p x } :=
  range_coe
#align subtype.range_val_subtype Subtype.range_val_subtype

theorem coe_image_subset (s : Set α) (t : Set s) : coe !! t ⊆ s := fun x ⟨y, yt, yvaleq⟩ => by
  rw [← yvaleq] <;> exact y.property
#align subtype.coe_image_subset Subtype.coe_image_subset

theorem coe_image_univ (s : Set α) : (coe : s → α) !! Set.univ = s :=
  image_univ.trans range_coe
#align subtype.coe_image_univ Subtype.coe_image_univ

@[simp]
theorem image_preimage_coe (s t : Set α) : (coe : s → α) !! (coe ⁻¹' t) = t ∩ s :=
  image_preimage_eq_inter_range.trans <| congr_arg _ range_coe
#align subtype.image_preimage_coe Subtype.image_preimage_coe

theorem image_preimage_val (s t : Set α) : (Subtype.val : s → α) !! (Subtype.val ⁻¹' t) = t ∩ s :=
  image_preimage_coe s t
#align subtype.image_preimage_val Subtype.image_preimage_val

theorem preimage_coe_eq_preimage_coe_iff {s t u : Set α} :
    (coe : s → α) ⁻¹' t = coe ⁻¹' u ↔ t ∩ s = u ∩ s := by
  rw [← image_preimage_coe, ← image_preimage_coe, coe_injective.image_injective.eq_iff]
#align subtype.preimage_coe_eq_preimage_coe_iff Subtype.preimage_coe_eq_preimage_coe_iff

@[simp]
theorem preimage_coe_inter_self (s t : Set α) : (coe : s → α) ⁻¹' (t ∩ s) = coe ⁻¹' t := by
  rw [preimage_coe_eq_preimage_coe_iff, inter_assoc, inter_self]
#align subtype.preimage_coe_inter_self Subtype.preimage_coe_inter_self

theorem preimage_val_eq_preimage_val_iff (s t u : Set α) :
    (Subtype.val : s → α) ⁻¹' t = Subtype.val ⁻¹' u ↔ t ∩ s = u ∩ s :=
  preimage_coe_eq_preimage_coe_iff
#align subtype.preimage_val_eq_preimage_val_iff Subtype.preimage_val_eq_preimage_val_iff

theorem exists_set_subtype {t : Set α} (p : Set α → Prop) :
    (∃ s : Set t, p (coe !! s)) ↔ ∃ s : Set α, s ⊆ t ∧ p s := by
  constructor
  · rintro ⟨s, hs⟩
    refine' ⟨coe !! s, _, hs⟩
    convert image_subset_range _ _
    rw [range_coe]
  rintro ⟨s, hs₁, hs₂⟩; refine' ⟨coe ⁻¹' s, _⟩
  rw [image_preimage_eq_of_subset]; exact hs₂; rw [range_coe]; exact hs₁
#align subtype.exists_set_subtype Subtype.exists_set_subtype

theorem preimage_coe_nonempty {s t : Set α} : ((coe : s → α) ⁻¹' t).Nonempty ↔ (s ∩ t).Nonempty :=
  by rw [inter_comm, ← image_preimage_coe, nonempty_image_iff]
#align subtype.preimage_coe_nonempty Subtype.preimage_coe_nonempty

theorem preimage_coe_eq_empty {s t : Set α} : (coe : s → α) ⁻¹' t = ∅ ↔ s ∩ t = ∅ := by
  simp only [← not_nonempty_iff_eq_empty, preimage_coe_nonempty]
#align subtype.preimage_coe_eq_empty Subtype.preimage_coe_eq_empty

@[simp]
theorem preimage_coe_compl (s : Set α) : (coe : s → α) ⁻¹' sᶜ = ∅ :=
  preimage_coe_eq_empty.2 (inter_compl_self s)
#align subtype.preimage_coe_compl Subtype.preimage_coe_compl

@[simp]
theorem preimage_coe_compl' (s : Set α) : (coe : sᶜ → α) ⁻¹' s = ∅ :=
  preimage_coe_eq_empty.2 (compl_inter_self s)
#align subtype.preimage_coe_compl' Subtype.preimage_coe_compl'

end Subtype

namespace Set

/-! ### Lemmas about `inclusion`, the injection of subtypes induced by `⊆` -/


section Inclusion

variable {α : Type _} {s t u : Set α}

/-- `inclusion` is the "identity" function between two subsets `s` and `t`, where `s ⊆ t` -/
def inclusion (h : s ⊆ t) : s → t := fun x : s => (⟨x, h x.2⟩ : t)
#align set.inclusion Set.inclusion

@[simp]
theorem inclusion_self (x : s) : inclusion Subset.rfl x = x := by
  cases x
  rfl
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
  rfl
#align set.inclusion_right Set.inclusion_right

@[simp]
theorem inclusion_inclusion (hst : s ⊆ t) (htu : t ⊆ u) (x : s) :
    inclusion htu (inclusion hst x) = inclusion (hst.trans htu) x := by
  cases x
  rfl
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

@[simp]
theorem range_inclusion (h : s ⊆ t) : range (inclusion h) = { x : t | (x : α) ∈ s } := by
  ext ⟨x, hx⟩
  simp [inclusion]
#align set.range_inclusion Set.range_inclusion

theorem eq_of_inclusion_surjective {s t : Set α} {h : s ⊆ t}
    (h_surj : Function.Surjective (inclusion h)) : s = t := by
  rw [← range_iff_surjective, range_inclusion, eq_univ_iff_forall] at h_surj
  exact Set.Subset.antisymm h fun x hx => h_surj ⟨x, hx⟩
#align set.eq_of_inclusion_surjective Set.eq_of_inclusion_surjective

end Inclusion

/-! ### Injectivity and surjectivity lemmas for image and preimage -/


section ImagePreimage

variable {α : Type u} {β : Type v} {f : α → β}

@[simp]
theorem preimage_injective : Injective (preimage f) ↔ Surjective f := by
  refine' ⟨fun h y => _, Surjective.preimage_injective⟩
  obtain ⟨x, hx⟩ : (f ⁻¹' {y}).Nonempty := by
    rw [h.nonempty_apply_iff preimage_empty]
    apply singleton_nonempty
  exact ⟨x, hx⟩
#align set.preimage_injective Set.preimage_injective

@[simp]
theorem preimage_surjective : Surjective (preimage f) ↔ Injective f := by
  refine' ⟨fun h x x' hx => _, Injective.preimage_surjective⟩
  cases' h {x} with s hs; have := mem_singleton x
  rwa [← hs, mem_preimage, hx, ← mem_preimage, hs, mem_singleton_iff, eq_comm] at this
#align set.preimage_surjective Set.preimage_surjective

@[simp]
theorem image_surjective : Surjective (image f) ↔ Surjective f := by
  refine' ⟨fun h y => _, Surjective.image_surjective⟩
  cases' h {y} with s hs
  have := mem_singleton y; rw [← hs] at this; rcases this with ⟨x, _, h2x⟩
  exact ⟨x, h2x⟩
#align set.image_surjective Set.image_surjective

@[simp]
theorem image_injective : Injective (image f) ↔ Injective f := by
  refine' ⟨fun h x x' hx => _, Injective.image_injective⟩
  rw [← singleton_eq_singleton_iff]; apply h
  rw [image_singleton, image_singleton, hx]
#align set.image_injective Set.image_injective

theorem preimage_eq_iff_eq_image {f : α → β} (hf : Bijective f) {s t} : f ⁻¹' s = t ↔ s = f !! t :=
  by rw [← image_eq_image hf.1, hf.2.image_preimage]
#align set.preimage_eq_iff_eq_image Set.preimage_eq_iff_eq_image

theorem eq_preimage_iff_image_eq {f : α → β} (hf : Bijective f) {s t} : s = f ⁻¹' t ↔ f !! s = t :=
  by rw [← image_eq_image hf.1, hf.2.image_preimage]
#align set.eq_preimage_iff_image_eq Set.eq_preimage_iff_image_eq

end ImagePreimage

end Set

namespace Subsingleton

variable {α : Type _} [Subsingleton α]

theorem eq_univ_of_nonempty {s : Set α} : s.Nonempty → s = univ := fun ⟨x, hx⟩ =>
  eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
#align subsingleton.eq_univ_of_nonempty Subsingleton.eq_univ_of_nonempty

@[elab_as_elim]
theorem set_cases {p : Set α → Prop} (h0 : p ∅) (h1 : p univ) (s) : p s :=
  (s.eq_empty_or_nonempty.elim fun h => h.symm ▸ h0) fun h => (eq_univ_of_nonempty h).symm ▸ h1
#align subsingleton.set_cases Subsingleton.set_cases

theorem mem_iff_nonempty {α : Type _} [Subsingleton α] {s : Set α} {x : α} : x ∈ s ↔ s.Nonempty :=
  ⟨fun hx => ⟨x, hx⟩, fun ⟨y, hy⟩ => Subsingleton.elim y x ▸ hy⟩
#align subsingleton.mem_iff_nonempty Subsingleton.mem_iff_nonempty

end Subsingleton

/-! ### Decidability instances for sets -/


namespace Set

variable {α : Type u} (s t : Set α) (a : α)

instance decidableSdiff [Decidable (a ∈ s)] [Decidable (a ∈ t)] : Decidable (a ∈ s \ t) :=
  (by infer_instance : Decidable (a ∈ s ∧ a ∉ t))
#align set.decidable_sdiff Set.decidableSdiff

instance decidableInter [Decidable (a ∈ s)] [Decidable (a ∈ t)] : Decidable (a ∈ s ∩ t) :=
  (by infer_instance : Decidable (a ∈ s ∧ a ∈ t))
#align set.decidable_inter Set.decidableInter

instance decidableUnion [Decidable (a ∈ s)] [Decidable (a ∈ t)] : Decidable (a ∈ s ∪ t) :=
  (by infer_instance : Decidable (a ∈ s ∨ a ∈ t))
#align set.decidable_union Set.decidableUnion

instance decidableCompl [Decidable (a ∈ s)] : Decidable (a ∈ sᶜ) :=
  (by infer_instance : Decidable (a ∉ s))
#align set.decidable_compl Set.decidableCompl

instance decidableEmptyset : DecidablePred (· ∈ (∅ : Set α)) := fun _ => Decidable.isFalse (by simp)
#align set.decidable_emptyset Set.decidableEmptyset

instance decidableUniv : DecidablePred (· ∈ (Set.univ : Set α)) := fun _ =>
  Decidable.isTrue (by simp)
#align set.decidable_univ Set.decidableUniv

instance decidableSetOf (p : α → Prop) [Decidable (p a)] : Decidable (a ∈ { a | p a }) := by
  assumption
#align set.decidable_set_of Set.decidableSetOf

end Set

/-! ### Indicator function valued in bool -/


open Bool

namespace Set

variable {α : Type _} (s : Set α)

/-- `bool_indicator` maps `x` to `tt` if `x ∈ s`, else to `ff` -/
noncomputable def boolIndicator (x : α) :=
  @ite _ (x ∈ s) (Classical.propDecidable _) true false
#align set.bool_indicator Set.boolIndicator

theorem mem_iff_bool_indicator (x : α) : x ∈ s ↔ s.boolIndicator x = tt := by
  unfold bool_indicator
  split_ifs <;> tauto
#align set.mem_iff_bool_indicator Set.mem_iff_bool_indicator

theorem not_mem_iff_bool_indicator (x : α) : x ∉ s ↔ s.boolIndicator x = ff := by
  unfold bool_indicator
  split_ifs <;> tauto
#align set.not_mem_iff_bool_indicator Set.not_mem_iff_bool_indicator

theorem preimage_bool_indicator_tt : s.boolIndicator ⁻¹' {true} = s :=
  ext fun x => (s.mem_iff_bool_indicator x).symm
#align set.preimage_bool_indicator_tt Set.preimage_bool_indicator_tt

theorem preimage_bool_indicator_ff : s.boolIndicator ⁻¹' {false} = sᶜ :=
  ext fun x => (s.not_mem_iff_bool_indicator x).symm
#align set.preimage_bool_indicator_ff Set.preimage_bool_indicator_ff

open Classical

theorem preimage_bool_indicator_eq_union (t : Set Bool) :
    s.boolIndicator ⁻¹' t = (if tt ∈ t then s else ∅) ∪ if ff ∈ t then sᶜ else ∅ := by
  ext x
  dsimp [bool_indicator]
  split_ifs <;> tauto
#align set.preimage_bool_indicator_eq_union Set.preimage_bool_indicator_eq_union

theorem preimage_bool_indicator (t : Set Bool) :
    s.boolIndicator ⁻¹' t = univ ∨
      s.boolIndicator ⁻¹' t = s ∨ s.boolIndicator ⁻¹' t = sᶜ ∨ s.boolIndicator ⁻¹' t = ∅ :=
  by
  simp only [preimage_bool_indicator_eq_union]
  split_ifs <;> simp [s.union_compl_self]
#align set.preimage_bool_indicator Set.preimage_bool_indicator

end Set
