/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
import Mathlib.Data.Multiset.FinsetOps
import Mathlib.Data.Set.Lattice

#align_import data.finset.basic from "leanprover-community/mathlib"@"d9e96a3e3e0894e93e10aff5244f4c96655bac1c"

/-!
# Finite sets

Terms of type `Finset α` are one way of talking about finite subsets of `α` in mathlib.
Below, `Finset α` is defined as a structure with 2 fields:

  1. `val` is a `Multiset α` of elements;
  2. `nodup` is a proof that `val` has no duplicates.

Finsets in Lean are constructive in that they have an underlying `List` that enumerates their
elements. In particular, any function that uses the data of the underlying list cannot depend on its
ordering. This is handled on the `Multiset` level by multiset API, so in most cases one needn't
worry about it explicitly.

Finsets give a basic foundation for defining finite sums and products over types:

  1. `∑ i in (s : Finset α), f i`;
  2. `∏ i in (s : Finset α), f i`.

Lean refers to these operations as big operators.
More information can be found in `Mathlib.Algebra.BigOperators.Basic`.

Finsets are directly used to define fintypes in Lean.
A `Fintype α` instance for a type `α` consists of a universal `Finset α` containing every term of
`α`, called `univ`. See `Mathlib.Data.Fintype.Basic`.
There is also `univ'`, the noncomputable partner to `univ`,
which is defined to be `α` as a finset if `α` is finite,
and the empty finset otherwise. See `Mathlib.Data.Fintype.Basic`.

`Finset.card`, the size of a finset is defined in `Mathlib.Data.Finset.Card`.
This is then used to define `Fintype.card`, the size of a type.

## Main declarations

### Main definitions

* `Finset`: Defines a type for the finite subsets of `α`.
  Constructing a `Finset` requires two pieces of data: `val`, a `Multiset α` of elements,
  and `nodup`, a proof that `val` has no duplicates.
* `Finset.instMembershipFinset`: Defines membership `a ∈ (s : Finset α)`.
* `Finset.instCoeTCFinsetSet`: Provides a coercion `s : Finset α` to `s : Set α`.
* `Finset.instCoeSortFinsetType`: Coerce `s : Finset α` to the type of all `x ∈ s`.
* `Finset.induction_on`: Induction on finsets. To prove a proposition about an arbitrary `Finset α`,
  it suffices to prove it for the empty finset, and to show that if it holds for some `Finset α`,
  then it holds for the finset obtained by inserting a new element.
* `Finset.choose`: Given a proof `h` of existence and uniqueness of a certain element
  satisfying a predicate, `choose s h` returns the element of `s` satisfying that predicate.

### Finset constructions

* `Finset.instSingletonFinset`: Denoted by `{a}`; the finset consisting of one element.
* `Finset.empty`: Denoted by `∅`. The finset associated to any type consisting of no elements.
* `Finset.range`: For any `n : ℕ`, `range n` is equal to `{0, 1, ... , n - 1} ⊆ ℕ`.
  This convention is consistent with other languages and normalizes `card (range n) = n`.
  Beware, `n` is not in `range n`.
* `Finset.attach`: Given `s : Finset α`, `attach s` forms a finset of elements of the subtype
  `{a // a ∈ s}`; in other words, it attaches elements to a proof of membership in the set.

### Finsets from functions

* `Finset.filter`: Given a decidable predicate `p : α → Prop`, `s.filter p` is
  the finset consisting of those elements in `s` satisfying the predicate `p`.

### The lattice structure on subsets of finsets

There is a natural lattice structure on the subsets of a set.
In Lean, we use lattice notation to talk about things involving unions and intersections. See
`Mathlib.Order.Lattice`. For the lattice structure on finsets, `⊥` is called `bot` with `⊥ = ∅` and
`⊤` is called `top` with `⊤ = univ`.

* `Finset.instHasSubsetFinset`: Lots of API about lattices, otherwise behaves as one would expect.
* `Finset.instUnionFinset`: Defines `s ∪ t` (or `s ⊔ t`) as the union of `s` and `t`.
  See `Finset.sup`/`Finset.biUnion` for finite unions.
* `Finset.instInterFinset`: Defines `s ∩ t` (or `s ⊓ t`) as the intersection of `s` and `t`.
  See `Finset.inf` for finite intersections.
* `Finset.disjUnion`: Given a hypothesis `h` which states that finsets `s` and `t` are disjoint,
  `s.disjUnion t h` is the set such that `a ∈ disjUnion s t h` iff `a ∈ s` or `a ∈ t`; this does
  not require decidable equality on the type `α`.

### Operations on two or more finsets

* `insert` and `Finset.cons`: For any `a : α`, `insert s a` returns `s ∪ {a}`. `cons s a h`
  returns the same except that it requires a hypothesis stating that `a` is not already in `s`.
  This does not require decidable equality on the type `α`.
* `Finset.instUnionFinset`: see "The lattice structure on subsets of finsets"
* `Finset.instInterFinset`: see "The lattice structure on subsets of finsets"
* `Finset.erase`: For any `a : α`, `erase s a` returns `s` with the element `a` removed.
* `Finset.instSDiffFinset`: Defines the set difference `s \ t` for finsets `s` and `t`.
* `Finset.product`: Given finsets of `α` and `β`, defines finsets of `α × β`.
  For arbitrary dependent products, see `Mathlib.Data.Finset.Pi`.
* `Finset.biUnion`: Finite unions of finsets; given an indexing function `f : α → Finset β` and an
  `s : Finset α`, `s.biUnion f` is the union of all finsets of the form `f a` for `a ∈ s`.
* `Finset.bInter`: TODO: Implement finite intersections.

### Maps constructed using finsets

* `Finset.piecewise`: Given two functions `f`, `g`, `s.piecewise f g` is a function which is equal
  to `f` on `s` and `g` on the complement.

### Predicates on finsets

* `Disjoint`: defined via the lattice structure on finsets; two sets are disjoint if their
  intersection is empty.
* `Finset.Nonempty`: A finset is nonempty if it has elements.
  This is equivalent to saying `s ≠ ∅`. TODO: Decide on the simp normal form.

### Equivalences between finsets

* The `Mathlib.Data.Equiv` files describe a general type of equivalence, so look in there for any
  lemmas. There is some API for rewriting sums and products from `s` to `t` given that `s ≃ t`.
  TODO: examples

## Tags

finite sets, finset

-/


open Multiset Subtype Nat Function

universe u

variable {α : Type*} {β : Type*} {γ : Type*}

/-- `Finset α` is the type of finite sets of elements of `α`. It is implemented
  as a multiset (a list up to permutation) which has no duplicate elements. -/
structure Finset (α : Type*) where
  /-- The underlying multiset -/
  val : Multiset α
  /-- `val` contains no duplicates -/
  nodup : Nodup val
#align finset Finset

instance Multiset.canLiftFinset {α} : CanLift (Multiset α) (Finset α) Finset.val Multiset.Nodup :=
  ⟨fun m hm => ⟨⟨m, hm⟩, rfl⟩⟩
#align multiset.can_lift_finset Multiset.canLiftFinset

namespace Finset

theorem eq_of_veq : ∀ {s t : Finset α}, s.1 = t.1 → s = t
  | ⟨s, _⟩, ⟨t, _⟩, h => by cases h; rfl
                            -- ⊢ { val := s, nodup := nodup✝¹ } = { val := s, nodup := nodup✝ }
                                     -- 🎉 no goals
#align finset.eq_of_veq Finset.eq_of_veq

theorem val_injective : Injective (val : Finset α → Multiset α) := fun _ _ => eq_of_veq
#align finset.val_injective Finset.val_injective

@[simp]
theorem val_inj {s t : Finset α} : s.1 = t.1 ↔ s = t :=
  val_injective.eq_iff
#align finset.val_inj Finset.val_inj

@[simp]
theorem dedup_eq_self [DecidableEq α] (s : Finset α) : dedup s.1 = s.1 :=
  s.2.dedup
#align finset.dedup_eq_self Finset.dedup_eq_self

instance decidableEq [DecidableEq α] : DecidableEq (Finset α)
  | _, _ => decidable_of_iff _ val_inj
#align finset.has_decidable_eq Finset.decidableEq

/-! ### membership -/


instance : Membership α (Finset α) :=
  ⟨fun a s => a ∈ s.1⟩

theorem mem_def {a : α} {s : Finset α} : a ∈ s ↔ a ∈ s.1 :=
  Iff.rfl
#align finset.mem_def Finset.mem_def

@[simp]
theorem mem_val {a : α} {s : Finset α} : a ∈ s.1 ↔ a ∈ s :=
  Iff.rfl
#align finset.mem_val Finset.mem_val

@[simp]
theorem mem_mk {a : α} {s nd} : a ∈ @Finset.mk α s nd ↔ a ∈ s :=
  Iff.rfl
#align finset.mem_mk Finset.mem_mk

instance decidableMem [_h : DecidableEq α] (a : α) (s : Finset α) : Decidable (a ∈ s) :=
  Multiset.decidableMem _ _
#align finset.decidable_mem Finset.decidableMem

/-! ### set coercion -/

--Porting note: new definition
/-- Convert a finset to a set in the natural way. -/
@[coe] def toSet (s : Finset α) : Set α :=
  { a | a ∈ s }

/-- Convert a finset to a set in the natural way. -/
instance : CoeTC (Finset α) (Set α) :=
  ⟨toSet⟩

@[simp, norm_cast]
theorem mem_coe {a : α} {s : Finset α} : a ∈ (s : Set α) ↔ a ∈ (s : Finset α) :=
  Iff.rfl
#align finset.mem_coe Finset.mem_coe

@[simp]
theorem setOf_mem {α} {s : Finset α} : { a | a ∈ s } = s :=
  rfl
#align finset.set_of_mem Finset.setOf_mem

@[simp]
theorem coe_mem {s : Finset α} (x : (s : Set α)) : ↑x ∈ s :=
  x.2
#align finset.coe_mem Finset.coe_mem

-- Porting note: @[simp] can prove this
theorem mk_coe {s : Finset α} (x : (s : Set α)) {h} : (⟨x, h⟩ : (s : Set α)) = x :=
  Subtype.coe_eta _ _
#align finset.mk_coe Finset.mk_coe

instance decidableMem' [DecidableEq α] (a : α) (s : Finset α) : Decidable (a ∈ (s : Set α)) :=
  s.decidableMem _
#align finset.decidable_mem' Finset.decidableMem'

/-! ### extensionality -/


theorem ext_iff {s₁ s₂ : Finset α} : s₁ = s₂ ↔ ∀ a, a ∈ s₁ ↔ a ∈ s₂ :=
  val_inj.symm.trans <| s₁.nodup.ext s₂.nodup
#align finset.ext_iff Finset.ext_iff

@[ext]
theorem ext {s₁ s₂ : Finset α} : (∀ a, a ∈ s₁ ↔ a ∈ s₂) → s₁ = s₂ :=
  ext_iff.2
#align finset.ext Finset.ext

@[simp, norm_cast]
theorem coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂ :=
  Set.ext_iff.trans ext_iff.symm
#align finset.coe_inj Finset.coe_inj

theorem coe_injective {α} : Injective ((↑) : Finset α → Set α) := fun _s _t => coe_inj.1
#align finset.coe_injective Finset.coe_injective

/-! ### type coercion -/


/-- Coercion from a finset to the corresponding subtype. -/
instance {α : Type u} : CoeSort (Finset α) (Type u) :=
  ⟨fun s => { x // x ∈ s }⟩

-- Porting note: @[simp] can prove this
protected theorem forall_coe {α : Type*} (s : Finset α) (p : s → Prop) :
    (∀ x : s, p x) ↔ ∀ (x : α) (h : x ∈ s), p ⟨x, h⟩ :=
  Subtype.forall
#align finset.forall_coe Finset.forall_coe

-- Porting note: @[simp] can prove this
protected theorem exists_coe {α : Type*} (s : Finset α) (p : s → Prop) :
    (∃ x : s, p x) ↔ ∃ (x : α) (h : x ∈ s), p ⟨x, h⟩ :=
  Subtype.exists
#align finset.exists_coe Finset.exists_coe

instance PiFinsetCoe.canLift (ι : Type*) (α : ∀ _i : ι, Type*) [_ne : ∀ i, Nonempty (α i)]
    (s : Finset ι) : CanLift (∀ i : s, α i) (∀ i, α i) (fun f i => f i) fun _ => True :=
  PiSubtype.canLift ι α (· ∈ s)
#align finset.pi_finset_coe.can_lift Finset.PiFinsetCoe.canLift

instance PiFinsetCoe.canLift' (ι α : Type*) [_ne : Nonempty α] (s : Finset ι) :
    CanLift (s → α) (ι → α) (fun f i => f i) fun _ => True :=
  PiFinsetCoe.canLift ι (fun _ => α) s
#align finset.pi_finset_coe.can_lift' Finset.PiFinsetCoe.canLift'

instance FinsetCoe.canLift (s : Finset α) : CanLift α s (↑) fun a => a ∈ s
    where prf a ha := ⟨⟨a, ha⟩, rfl⟩
#align finset.finset_coe.can_lift Finset.FinsetCoe.canLift

@[simp, norm_cast]
theorem coe_sort_coe (s : Finset α) : ((s : Set α) : Sort _) = s :=
  rfl
#align finset.coe_sort_coe Finset.coe_sort_coe

/-! ### Subset and strict subset relations -/


section Subset

variable {s t : Finset α}

instance : HasSubset (Finset α) :=
  ⟨fun s t => ∀ ⦃a⦄, a ∈ s → a ∈ t⟩

instance : HasSSubset (Finset α) :=
  ⟨fun s t => s ⊆ t ∧ ¬t ⊆ s⟩

instance partialOrder : PartialOrder (Finset α) where
  le := (· ⊆ ·)
  lt := (· ⊂ ·)
  le_refl s a := id
  le_trans s t u hst htu a ha := htu <| hst ha
  le_antisymm s t hst hts := ext fun a => ⟨@hst _, @hts _⟩

instance : IsRefl (Finset α) (· ⊆ ·) :=
  show IsRefl (Finset α) (· ≤ ·) by infer_instance
                                    -- 🎉 no goals

instance : IsTrans (Finset α) (· ⊆ ·) :=
  show IsTrans (Finset α) (· ≤ ·) by infer_instance
                                     -- 🎉 no goals

instance : IsAntisymm (Finset α) (· ⊆ ·) :=
  show IsAntisymm (Finset α) (· ≤ ·) by infer_instance
                                        -- 🎉 no goals

instance : IsIrrefl (Finset α) (· ⊂ ·) :=
  show IsIrrefl (Finset α) (· < ·) by infer_instance
                                      -- 🎉 no goals

instance : IsTrans (Finset α) (· ⊂ ·) :=
  show IsTrans (Finset α) (· < ·) by infer_instance
                                     -- 🎉 no goals

instance : IsAsymm (Finset α) (· ⊂ ·) :=
  show IsAsymm (Finset α) (· < ·) by infer_instance
                                     -- 🎉 no goals

instance : IsNonstrictStrictOrder (Finset α) (· ⊆ ·) (· ⊂ ·) :=
  ⟨fun _ _ => Iff.rfl⟩

theorem subset_def : s ⊆ t ↔ s.1 ⊆ t.1 :=
  Iff.rfl
#align finset.subset_def Finset.subset_def

theorem ssubset_def : s ⊂ t ↔ s ⊆ t ∧ ¬t ⊆ s :=
  Iff.rfl
#align finset.ssubset_def Finset.ssubset_def

@[simp]
theorem Subset.refl (s : Finset α) : s ⊆ s :=
  Multiset.Subset.refl _
#align finset.subset.refl Finset.Subset.refl

protected theorem Subset.rfl {s : Finset α} : s ⊆ s :=
  Subset.refl _
#align finset.subset.rfl Finset.Subset.rfl

protected theorem subset_of_eq {s t : Finset α} (h : s = t) : s ⊆ t :=
  h ▸ Subset.refl _
#align finset.subset_of_eq Finset.subset_of_eq

theorem Subset.trans {s₁ s₂ s₃ : Finset α} : s₁ ⊆ s₂ → s₂ ⊆ s₃ → s₁ ⊆ s₃ :=
  Multiset.Subset.trans
#align finset.subset.trans Finset.Subset.trans

theorem Superset.trans {s₁ s₂ s₃ : Finset α} : s₁ ⊇ s₂ → s₂ ⊇ s₃ → s₁ ⊇ s₃ := fun h' h =>
  Subset.trans h h'
#align finset.superset.trans Finset.Superset.trans

theorem mem_of_subset {s₁ s₂ : Finset α} {a : α} : s₁ ⊆ s₂ → a ∈ s₁ → a ∈ s₂ :=
  Multiset.mem_of_subset
#align finset.mem_of_subset Finset.mem_of_subset

theorem not_mem_mono {s t : Finset α} (h : s ⊆ t) {a : α} : a ∉ t → a ∉ s :=
  mt <| @h _
#align finset.not_mem_mono Finset.not_mem_mono

theorem Subset.antisymm {s₁ s₂ : Finset α} (H₁ : s₁ ⊆ s₂) (H₂ : s₂ ⊆ s₁) : s₁ = s₂ :=
  ext fun a => ⟨@H₁ a, @H₂ a⟩
#align finset.subset.antisymm Finset.Subset.antisymm

theorem subset_iff {s₁ s₂ : Finset α} : s₁ ⊆ s₂ ↔ ∀ ⦃x⦄, x ∈ s₁ → x ∈ s₂ :=
  Iff.rfl
#align finset.subset_iff Finset.subset_iff

@[simp, norm_cast]
theorem coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) ⊆ s₂ ↔ s₁ ⊆ s₂ :=
  Iff.rfl
#align finset.coe_subset Finset.coe_subset

@[simp]
theorem val_le_iff {s₁ s₂ : Finset α} : s₁.1 ≤ s₂.1 ↔ s₁ ⊆ s₂ :=
  le_iff_subset s₁.2
#align finset.val_le_iff Finset.val_le_iff

theorem Subset.antisymm_iff {s₁ s₂ : Finset α} : s₁ = s₂ ↔ s₁ ⊆ s₂ ∧ s₂ ⊆ s₁ :=
  le_antisymm_iff
#align finset.subset.antisymm_iff Finset.Subset.antisymm_iff

theorem not_subset : ¬s ⊆ t ↔ ∃ x ∈ s, x ∉ t := by simp only [← coe_subset, Set.not_subset, mem_coe]
                                                   -- 🎉 no goals
#align finset.not_subset Finset.not_subset

@[simp]
theorem le_eq_subset : ((· ≤ ·) : Finset α → Finset α → Prop) = (· ⊆ ·) :=
  rfl
#align finset.le_eq_subset Finset.le_eq_subset

@[simp]
theorem lt_eq_subset : ((· < ·) : Finset α → Finset α → Prop) = (· ⊂ ·) :=
  rfl
#align finset.lt_eq_subset Finset.lt_eq_subset

theorem le_iff_subset {s₁ s₂ : Finset α} : s₁ ≤ s₂ ↔ s₁ ⊆ s₂ :=
  Iff.rfl
#align finset.le_iff_subset Finset.le_iff_subset

theorem lt_iff_ssubset {s₁ s₂ : Finset α} : s₁ < s₂ ↔ s₁ ⊂ s₂ :=
  Iff.rfl
#align finset.lt_iff_ssubset Finset.lt_iff_ssubset

@[simp, norm_cast]
theorem coe_ssubset {s₁ s₂ : Finset α} : (s₁ : Set α) ⊂ s₂ ↔ s₁ ⊂ s₂ :=
  show (s₁ : Set α) ⊂ s₂ ↔ s₁ ⊆ s₂ ∧ ¬s₂ ⊆ s₁ by simp only [Set.ssubset_def, Finset.coe_subset]
                                                 -- 🎉 no goals
#align finset.coe_ssubset Finset.coe_ssubset

@[simp]
theorem val_lt_iff {s₁ s₂ : Finset α} : s₁.1 < s₂.1 ↔ s₁ ⊂ s₂ :=
  and_congr val_le_iff <| not_congr val_le_iff
#align finset.val_lt_iff Finset.val_lt_iff

theorem ssubset_iff_subset_ne {s t : Finset α} : s ⊂ t ↔ s ⊆ t ∧ s ≠ t :=
  @lt_iff_le_and_ne _ _ s t
#align finset.ssubset_iff_subset_ne Finset.ssubset_iff_subset_ne

theorem ssubset_iff_of_subset {s₁ s₂ : Finset α} (h : s₁ ⊆ s₂) : s₁ ⊂ s₂ ↔ ∃ x ∈ s₂, x ∉ s₁ :=
  Set.ssubset_iff_of_subset h
#align finset.ssubset_iff_of_subset Finset.ssubset_iff_of_subset

theorem ssubset_of_ssubset_of_subset {s₁ s₂ s₃ : Finset α} (hs₁s₂ : s₁ ⊂ s₂) (hs₂s₃ : s₂ ⊆ s₃) :
    s₁ ⊂ s₃ :=
  Set.ssubset_of_ssubset_of_subset hs₁s₂ hs₂s₃
#align finset.ssubset_of_ssubset_of_subset Finset.ssubset_of_ssubset_of_subset

theorem ssubset_of_subset_of_ssubset {s₁ s₂ s₃ : Finset α} (hs₁s₂ : s₁ ⊆ s₂) (hs₂s₃ : s₂ ⊂ s₃) :
    s₁ ⊂ s₃ :=
  Set.ssubset_of_subset_of_ssubset hs₁s₂ hs₂s₃
#align finset.ssubset_of_subset_of_ssubset Finset.ssubset_of_subset_of_ssubset

theorem exists_of_ssubset {s₁ s₂ : Finset α} (h : s₁ ⊂ s₂) : ∃ x ∈ s₂, x ∉ s₁ :=
  Set.exists_of_ssubset h
#align finset.exists_of_ssubset Finset.exists_of_ssubset

instance isWellFounded_ssubset : IsWellFounded (Finset α) (· ⊂ ·) :=
  Subrelation.isWellFounded (InvImage _ _) val_lt_iff.2
#align finset.is_well_founded_ssubset Finset.isWellFounded_ssubset

instance wellFoundedLT : WellFoundedLT (Finset α) :=
  Finset.isWellFounded_ssubset
#align finset.is_well_founded_lt Finset.wellFoundedLT

end Subset

-- TODO: these should be global attributes, but this will require fixing other files
attribute [local trans] Subset.trans Superset.trans

/-! ### Order embedding from `Finset α` to `Set α` -/


/-- Coercion to `Set α` as an `OrderEmbedding`. -/
def coeEmb : Finset α ↪o Set α :=
  ⟨⟨(↑), coe_injective⟩, coe_subset⟩
#align finset.coe_emb Finset.coeEmb

@[simp]
theorem coe_coeEmb : ⇑(coeEmb : Finset α ↪o Set α) = ((↑) : Finset α → Set α) :=
  rfl
#align finset.coe_coe_emb Finset.coe_coeEmb

/-! ### Nonempty -/


/-- The property `s.Nonempty` expresses the fact that the finset `s` is not empty. It should be used
in theorem assumptions instead of `∃ x, x ∈ s` or `s ≠ ∅` as it gives access to a nice API thanks
to the dot notation. -/
protected def Nonempty (s : Finset α) : Prop :=
  ∃ x : α, x ∈ s
#align finset.nonempty Finset.Nonempty

--Porting note: Much longer than in Lean3
instance decidableNonempty {s : Finset α} : Decidable s.Nonempty :=
  Quotient.recOnSubsingleton (motive := fun s : Multiset α => Decidable (∃ a, a ∈ s)) s.1
    (fun l : List α =>
      match l with
      | [] => isFalse <| by simp
                            -- 🎉 no goals
      | a::l => isTrue ⟨a, by simp⟩)
                              -- 🎉 no goals
#align finset.decidable_nonempty Finset.decidableNonempty

@[simp, norm_cast]
theorem coe_nonempty {s : Finset α} : (s : Set α).Nonempty ↔ s.Nonempty :=
  Iff.rfl
#align finset.coe_nonempty Finset.coe_nonempty

-- Porting note: Left-hand side simplifies @[simp]
theorem nonempty_coe_sort {s : Finset α} : Nonempty (s : Type _) ↔ s.Nonempty :=
  nonempty_subtype
#align finset.nonempty_coe_sort Finset.nonempty_coe_sort

alias ⟨_, Nonempty.to_set⟩ := coe_nonempty
#align finset.nonempty.to_set Finset.Nonempty.to_set

alias ⟨_, Nonempty.coe_sort⟩ := nonempty_coe_sort
#align finset.nonempty.coe_sort Finset.Nonempty.coe_sort

theorem Nonempty.bex {s : Finset α} (h : s.Nonempty) : ∃ x : α, x ∈ s :=
  h
#align finset.nonempty.bex Finset.Nonempty.bex

theorem Nonempty.mono {s t : Finset α} (hst : s ⊆ t) (hs : s.Nonempty) : t.Nonempty :=
  Set.Nonempty.mono hst hs
#align finset.nonempty.mono Finset.Nonempty.mono

theorem Nonempty.forall_const {s : Finset α} (h : s.Nonempty) {p : Prop} : (∀ x ∈ s, p) ↔ p :=
  let ⟨x, hx⟩ := h
  ⟨fun h => h x hx, fun h _ _ => h⟩
#align finset.nonempty.forall_const Finset.Nonempty.forall_const

theorem Nonempty.to_subtype {s : Finset α} : s.Nonempty → Nonempty s :=
  nonempty_coe_sort.2
#align finset.nonempty.to_subtype Finset.Nonempty.to_subtype

theorem Nonempty.to_type {s : Finset α} : s.Nonempty → Nonempty α := fun ⟨x, _hx⟩ => ⟨x⟩
#align finset.nonempty.to_type Finset.Nonempty.to_type

/-! ### empty -/


section Empty

variable {s : Finset α}

/-- The empty finset -/
protected def empty : Finset α :=
  ⟨0, nodup_zero⟩
#align finset.empty Finset.empty

instance : EmptyCollection (Finset α) :=
  ⟨Finset.empty⟩

instance inhabitedFinset : Inhabited (Finset α) :=
  ⟨∅⟩
#align finset.inhabited_finset Finset.inhabitedFinset

@[simp]
theorem empty_val : (∅ : Finset α).1 = 0 :=
  rfl
#align finset.empty_val Finset.empty_val

@[simp]
theorem not_mem_empty (a : α) : a ∉ (∅ : Finset α) := by
  -- Porting note: was `id`. `a ∈ List.nil` is no longer definitionally equal to `False`
  simp only [mem_def, empty_val, not_mem_zero, not_false_iff]
  -- 🎉 no goals
#align finset.not_mem_empty Finset.not_mem_empty

@[simp]
theorem not_nonempty_empty : ¬(∅ : Finset α).Nonempty := fun ⟨x, hx⟩ => not_mem_empty x hx
#align finset.not_nonempty_empty Finset.not_nonempty_empty

@[simp]
theorem mk_zero : (⟨0, nodup_zero⟩ : Finset α) = ∅ :=
  rfl
#align finset.mk_zero Finset.mk_zero

theorem ne_empty_of_mem {a : α} {s : Finset α} (h : a ∈ s) : s ≠ ∅ := fun e =>
  not_mem_empty a <| e ▸ h
#align finset.ne_empty_of_mem Finset.ne_empty_of_mem

theorem Nonempty.ne_empty {s : Finset α} (h : s.Nonempty) : s ≠ ∅ :=
  (Exists.elim h) fun _a => ne_empty_of_mem
#align finset.nonempty.ne_empty Finset.Nonempty.ne_empty

@[simp]
theorem empty_subset (s : Finset α) : ∅ ⊆ s :=
  zero_subset _
#align finset.empty_subset Finset.empty_subset

theorem eq_empty_of_forall_not_mem {s : Finset α} (H : ∀ x, x ∉ s) : s = ∅ :=
  eq_of_veq (eq_zero_of_forall_not_mem H)
#align finset.eq_empty_of_forall_not_mem Finset.eq_empty_of_forall_not_mem

theorem eq_empty_iff_forall_not_mem {s : Finset α} : s = ∅ ↔ ∀ x, x ∉ s :=
  -- Porting note: used `id`
  ⟨by rintro rfl x; apply not_mem_empty, fun h => eq_empty_of_forall_not_mem h⟩
      -- ⊢ ¬x ∈ ∅
                    -- 🎉 no goals
#align finset.eq_empty_iff_forall_not_mem Finset.eq_empty_iff_forall_not_mem

@[simp]
theorem val_eq_zero {s : Finset α} : s.1 = 0 ↔ s = ∅ :=
  @val_inj _ s ∅
#align finset.val_eq_zero Finset.val_eq_zero

theorem subset_empty {s : Finset α} : s ⊆ ∅ ↔ s = ∅ :=
  subset_zero.trans val_eq_zero
#align finset.subset_empty Finset.subset_empty

@[simp]
theorem not_ssubset_empty (s : Finset α) : ¬s ⊂ ∅ := fun h =>
  let ⟨_, he, _⟩ := exists_of_ssubset h
  -- Porting note: was `he`
  not_mem_empty _ he
#align finset.not_ssubset_empty Finset.not_ssubset_empty

theorem nonempty_of_ne_empty {s : Finset α} (h : s ≠ ∅) : s.Nonempty :=
  exists_mem_of_ne_zero (mt val_eq_zero.1 h)
#align finset.nonempty_of_ne_empty Finset.nonempty_of_ne_empty

theorem nonempty_iff_ne_empty {s : Finset α} : s.Nonempty ↔ s ≠ ∅ :=
  ⟨Nonempty.ne_empty, nonempty_of_ne_empty⟩
#align finset.nonempty_iff_ne_empty Finset.nonempty_iff_ne_empty

@[simp]
theorem not_nonempty_iff_eq_empty {s : Finset α} : ¬s.Nonempty ↔ s = ∅ :=
  nonempty_iff_ne_empty.not.trans not_not
#align finset.not_nonempty_iff_eq_empty Finset.not_nonempty_iff_eq_empty

theorem eq_empty_or_nonempty (s : Finset α) : s = ∅ ∨ s.Nonempty :=
  by_cases Or.inl fun h => Or.inr (nonempty_of_ne_empty h)
#align finset.eq_empty_or_nonempty Finset.eq_empty_or_nonempty

@[simp, norm_cast]
theorem coe_empty : ((∅ : Finset α) : Set α) = ∅ :=
  Set.ext <| by simp
                -- 🎉 no goals
#align finset.coe_empty Finset.coe_empty

@[simp, norm_cast]
theorem coe_eq_empty {s : Finset α} : (s : Set α) = ∅ ↔ s = ∅ := by rw [← coe_empty, coe_inj]
                                                                    -- 🎉 no goals
#align finset.coe_eq_empty Finset.coe_eq_empty

-- Porting note: Left-hand side simplifies @[simp]
theorem isEmpty_coe_sort {s : Finset α} : IsEmpty (s : Type _) ↔ s = ∅ := by
  simpa using @Set.isEmpty_coe_sort α s
  -- 🎉 no goals
#align finset.is_empty_coe_sort Finset.isEmpty_coe_sort

instance instIsEmpty : IsEmpty (∅ : Finset α) :=
  isEmpty_coe_sort.2 rfl

/-- A `Finset` for an empty type is empty. -/
theorem eq_empty_of_isEmpty [IsEmpty α] (s : Finset α) : s = ∅ :=
  Finset.eq_empty_of_forall_not_mem isEmptyElim
#align finset.eq_empty_of_is_empty Finset.eq_empty_of_isEmpty

instance : OrderBot (Finset α) where
  bot := ∅
  bot_le := empty_subset

@[simp]
theorem bot_eq_empty : (⊥ : Finset α) = ∅ :=
  rfl
#align finset.bot_eq_empty Finset.bot_eq_empty

@[simp]
theorem empty_ssubset : ∅ ⊂ s ↔ s.Nonempty :=
  (@bot_lt_iff_ne_bot (Finset α) _ _ _).trans nonempty_iff_ne_empty.symm
#align finset.empty_ssubset Finset.empty_ssubset

alias ⟨_, Nonempty.empty_ssubset⟩ := empty_ssubset
#align finset.nonempty.empty_ssubset Finset.Nonempty.empty_ssubset

end Empty

/-! ### singleton -/


section Singleton

variable {s : Finset α} {a b : α}

/-- `{a} : Finset a` is the set `{a}` containing `a` and nothing else.

This differs from `insert a ∅` in that it does not require a `DecidableEq` instance for `α`.
-/
instance : Singleton α (Finset α) :=
  ⟨fun a => ⟨{a}, nodup_singleton a⟩⟩

@[simp]
theorem singleton_val (a : α) : ({a} : Finset α).1 = {a} :=
  rfl
#align finset.singleton_val Finset.singleton_val

@[simp]
theorem mem_singleton {a b : α} : b ∈ ({a} : Finset α) ↔ b = a :=
  Multiset.mem_singleton
#align finset.mem_singleton Finset.mem_singleton

theorem eq_of_mem_singleton {x y : α} (h : x ∈ ({y} : Finset α)) : x = y :=
  mem_singleton.1 h
#align finset.eq_of_mem_singleton Finset.eq_of_mem_singleton

theorem not_mem_singleton {a b : α} : a ∉ ({b} : Finset α) ↔ a ≠ b :=
  not_congr mem_singleton
#align finset.not_mem_singleton Finset.not_mem_singleton

theorem mem_singleton_self (a : α) : a ∈ ({a} : Finset α) :=
  -- Porting note: was `Or.inl rfl`
  mem_singleton.mpr rfl
#align finset.mem_singleton_self Finset.mem_singleton_self

@[simp]
theorem val_eq_singleton_iff {a : α} {s : Finset α} : s.val = {a} ↔ s = {a} := by
  rw [← val_inj]
  -- ⊢ s.val = {a} ↔ s.val = {a}.val
  rfl
  -- 🎉 no goals
#align finset.val_eq_singleton_iff Finset.val_eq_singleton_iff

theorem singleton_injective : Injective (singleton : α → Finset α) := fun _a _b h =>
  mem_singleton.1 (h ▸ mem_singleton_self _)
#align finset.singleton_injective Finset.singleton_injective

@[simp]
theorem singleton_inj : ({a} : Finset α) = {b} ↔ a = b :=
  singleton_injective.eq_iff
#align finset.singleton_inj Finset.singleton_inj

@[simp]
theorem singleton_nonempty (a : α) : ({a} : Finset α).Nonempty :=
  ⟨a, mem_singleton_self a⟩
#align finset.singleton_nonempty Finset.singleton_nonempty

@[simp]
theorem singleton_ne_empty (a : α) : ({a} : Finset α) ≠ ∅ :=
  (singleton_nonempty a).ne_empty
#align finset.singleton_ne_empty Finset.singleton_ne_empty

theorem empty_ssubset_singleton : (∅ : Finset α) ⊂ {a} :=
  (singleton_nonempty _).empty_ssubset
#align finset.empty_ssubset_singleton Finset.empty_ssubset_singleton

@[simp, norm_cast]
theorem coe_singleton (a : α) : (({a} : Finset α) : Set α) = {a} := by
  ext
  -- ⊢ x✝ ∈ ↑{a} ↔ x✝ ∈ {a}
  simp
  -- 🎉 no goals
#align finset.coe_singleton Finset.coe_singleton

@[simp, norm_cast]
theorem coe_eq_singleton {s : Finset α} {a : α} : (s : Set α) = {a} ↔ s = {a} := by
  rw [← coe_singleton, coe_inj]
  -- 🎉 no goals
#align finset.coe_eq_singleton Finset.coe_eq_singleton

theorem eq_singleton_iff_unique_mem {s : Finset α} {a : α} : s = {a} ↔ a ∈ s ∧ ∀ x ∈ s, x = a := by
  constructor <;> intro t
  -- ⊢ s = {a} → a ∈ s ∧ ∀ (x : α), x ∈ s → x = a
                  -- ⊢ a ∈ s ∧ ∀ (x : α), x ∈ s → x = a
                  -- ⊢ s = {a}
  · rw [t]
    -- ⊢ a ∈ {a} ∧ ∀ (x : α), x ∈ {a} → x = a
    exact ⟨Finset.mem_singleton_self _, fun _ => Finset.mem_singleton.1⟩
    -- 🎉 no goals
  · ext
    -- ⊢ a✝ ∈ s ↔ a✝ ∈ {a}
    rw [Finset.mem_singleton]
    -- ⊢ a✝ ∈ s ↔ a✝ = a
    exact ⟨t.right _, fun r => r.symm ▸ t.left⟩
    -- 🎉 no goals
#align finset.eq_singleton_iff_unique_mem Finset.eq_singleton_iff_unique_mem

theorem eq_singleton_iff_nonempty_unique_mem {s : Finset α} {a : α} :
    s = {a} ↔ s.Nonempty ∧ ∀ x ∈ s, x = a := by
  constructor
  -- ⊢ s = {a} → Finset.Nonempty s ∧ ∀ (x : α), x ∈ s → x = a
  · rintro rfl
    -- ⊢ Finset.Nonempty {a} ∧ ∀ (x : α), x ∈ {a} → x = a
    simp
    -- 🎉 no goals
  · rintro ⟨hne, h_uniq⟩
    -- ⊢ s = {a}
    rw [eq_singleton_iff_unique_mem]
    -- ⊢ a ∈ s ∧ ∀ (x : α), x ∈ s → x = a
    refine' ⟨_, h_uniq⟩
    -- ⊢ a ∈ s
    rw [← h_uniq hne.choose hne.choose_spec]
    -- ⊢ Exists.choose hne ∈ s
    exact hne.choose_spec
    -- 🎉 no goals
#align finset.eq_singleton_iff_nonempty_unique_mem Finset.eq_singleton_iff_nonempty_unique_mem

theorem nonempty_iff_eq_singleton_default [Unique α] {s : Finset α} : s.Nonempty ↔ s = {default} :=
  by simp [eq_singleton_iff_nonempty_unique_mem]
     -- 🎉 no goals
#align finset.nonempty_iff_eq_singleton_default Finset.nonempty_iff_eq_singleton_default

alias ⟨Nonempty.eq_singleton_default, _⟩ := nonempty_iff_eq_singleton_default
#align finset.nonempty.eq_singleton_default Finset.Nonempty.eq_singleton_default

theorem singleton_iff_unique_mem (s : Finset α) : (∃ a, s = {a}) ↔ ∃! a, a ∈ s := by
  simp only [eq_singleton_iff_unique_mem, ExistsUnique]
  -- 🎉 no goals
#align finset.singleton_iff_unique_mem Finset.singleton_iff_unique_mem

theorem singleton_subset_set_iff {s : Set α} {a : α} : ↑({a} : Finset α) ⊆ s ↔ a ∈ s := by
  rw [coe_singleton, Set.singleton_subset_iff]
  -- 🎉 no goals
#align finset.singleton_subset_set_iff Finset.singleton_subset_set_iff

@[simp]
theorem singleton_subset_iff {s : Finset α} {a : α} : {a} ⊆ s ↔ a ∈ s :=
  singleton_subset_set_iff
#align finset.singleton_subset_iff Finset.singleton_subset_iff

@[simp]
theorem subset_singleton_iff {s : Finset α} {a : α} : s ⊆ {a} ↔ s = ∅ ∨ s = {a} := by
  rw [← coe_subset, coe_singleton, Set.subset_singleton_iff_eq, coe_eq_empty, coe_eq_singleton]
  -- 🎉 no goals
#align finset.subset_singleton_iff Finset.subset_singleton_iff

theorem singleton_subset_singleton : ({a} : Finset α) ⊆ {b} ↔ a = b := by simp
                                                                          -- 🎉 no goals
#align finset.singleton_subset_singleton Finset.singleton_subset_singleton

protected theorem Nonempty.subset_singleton_iff {s : Finset α} {a : α} (h : s.Nonempty) :
    s ⊆ {a} ↔ s = {a} :=
  subset_singleton_iff.trans <| or_iff_right h.ne_empty
#align finset.nonempty.subset_singleton_iff Finset.Nonempty.subset_singleton_iff

theorem subset_singleton_iff' {s : Finset α} {a : α} : s ⊆ {a} ↔ ∀ b ∈ s, b = a :=
  forall₂_congr fun _ _ => mem_singleton
#align finset.subset_singleton_iff' Finset.subset_singleton_iff'

@[simp]
theorem ssubset_singleton_iff {s : Finset α} {a : α} : s ⊂ {a} ↔ s = ∅ := by
  rw [← coe_ssubset, coe_singleton, Set.ssubset_singleton_iff, coe_eq_empty]
  -- 🎉 no goals
#align finset.ssubset_singleton_iff Finset.ssubset_singleton_iff

theorem eq_empty_of_ssubset_singleton {s : Finset α} {x : α} (hs : s ⊂ {x}) : s = ∅ :=
  ssubset_singleton_iff.1 hs
#align finset.eq_empty_of_ssubset_singleton Finset.eq_empty_of_ssubset_singleton

theorem eq_singleton_or_nontrivial (ha : a ∈ s) : s = {a} ∨ (s : Set α).Nontrivial := by
  rw [← coe_eq_singleton]
  -- ⊢ ↑s = {a} ∨ Set.Nontrivial ↑s
  exact Set.eq_singleton_or_nontrivial ha
  -- 🎉 no goals
#align finset.eq_singleton_or_nontrivial Finset.eq_singleton_or_nontrivial

theorem Nonempty.exists_eq_singleton_or_nontrivial :
    s.Nonempty → (∃ a, s = {a}) ∨ (s : Set α).Nontrivial := fun ⟨a, ha⟩ =>
  (eq_singleton_or_nontrivial ha).imp_left <| Exists.intro a
#align finset.nonempty.exists_eq_singleton_or_nontrivial Finset.Nonempty.exists_eq_singleton_or_nontrivial

instance [Nonempty α] : Nontrivial (Finset α) :=
  ‹Nonempty α›.elim fun a => ⟨⟨{a}, ∅, singleton_ne_empty _⟩⟩

instance [IsEmpty α] : Unique (Finset α) where
  default := ∅
  uniq _ := eq_empty_of_forall_not_mem isEmptyElim

end Singleton

/-! ### cons -/


section Cons

variable {s t : Finset α} {a b : α}

/-- `cons a s h` is the set `{a} ∪ s` containing `a` and the elements of `s`. It is the same as
`insert a s` when it is defined, but unlike `insert a s` it does not require `DecidableEq α`,
and the union is guaranteed to be disjoint. -/
def cons (a : α) (s : Finset α) (h : a ∉ s) : Finset α :=
  ⟨a ::ₘ s.1, nodup_cons.2 ⟨h, s.2⟩⟩
#align finset.cons Finset.cons

@[simp]
theorem mem_cons {h} : b ∈ s.cons a h ↔ b = a ∨ b ∈ s :=
  Multiset.mem_cons
#align finset.mem_cons Finset.mem_cons

-- Porting note: @[simp] can prove this
theorem mem_cons_self (a : α) (s : Finset α) {h} : a ∈ cons a s h :=
  Multiset.mem_cons_self _ _
#align finset.mem_cons_self Finset.mem_cons_self

@[simp]
theorem cons_val (h : a ∉ s) : (cons a s h).1 = a ::ₘ s.1 :=
  rfl
#align finset.cons_val Finset.cons_val

theorem forall_mem_cons (h : a ∉ s) (p : α → Prop) :
    (∀ x, x ∈ cons a s h → p x) ↔ p a ∧ ∀ x, x ∈ s → p x := by
  simp only [mem_cons, or_imp, forall_and, forall_eq]
  -- 🎉 no goals
#align finset.forall_mem_cons Finset.forall_mem_cons

/-- Useful in proofs by induction. -/
theorem forall_of_forall_cons {p : α → Prop} {h : a ∉ s} (H : ∀ x, x ∈ cons a s h → p x) (x)
    (h : x ∈ s) : p x :=
  H _ <| mem_cons.2 <| Or.inr h
#align finset.forall_of_forall_cons Finset.forall_of_forall_cons

@[simp]
theorem mk_cons {s : Multiset α} (h : (a ::ₘ s).Nodup) :
    (⟨a ::ₘ s, h⟩ : Finset α) = cons a ⟨s, (nodup_cons.1 h).2⟩ (nodup_cons.1 h).1 :=
  rfl
#align finset.mk_cons Finset.mk_cons

@[simp]
theorem nonempty_cons (h : a ∉ s) : (cons a s h).Nonempty :=
  ⟨a, mem_cons.2 <| Or.inl rfl⟩
#align finset.nonempty_cons Finset.nonempty_cons

@[simp]
theorem nonempty_mk {m : Multiset α} {hm} : (⟨m, hm⟩ : Finset α).Nonempty ↔ m ≠ 0 := by
  induction m using Multiset.induction_on <;> simp
  -- ⊢ Finset.Nonempty { val := 0, nodup := hm } ↔ 0 ≠ 0
                                              -- 🎉 no goals
                                              -- 🎉 no goals
#align finset.nonempty_mk Finset.nonempty_mk

@[simp]
theorem coe_cons {a s h} : (@cons α a s h : Set α) = insert a (s : Set α) := by
  ext
  -- ⊢ x✝ ∈ ↑(cons a s h) ↔ x✝ ∈ insert a ↑s
  simp
  -- 🎉 no goals
#align finset.coe_cons Finset.coe_cons

theorem subset_cons (h : a ∉ s) : s ⊆ s.cons a h :=
  Multiset.subset_cons _ _
#align finset.subset_cons Finset.subset_cons

theorem ssubset_cons (h : a ∉ s) : s ⊂ s.cons a h :=
  Multiset.ssubset_cons h
#align finset.ssubset_cons Finset.ssubset_cons

theorem cons_subset {h : a ∉ s} : s.cons a h ⊆ t ↔ a ∈ t ∧ s ⊆ t :=
  Multiset.cons_subset
#align finset.cons_subset Finset.cons_subset

@[simp]
theorem cons_subset_cons {hs ht} : s.cons a hs ⊆ t.cons a ht ↔ s ⊆ t := by
  rwa [← coe_subset, coe_cons, coe_cons, Set.insert_subset_insert_iff, coe_subset]
  -- 🎉 no goals
#align finset.cons_subset_cons Finset.cons_subset_cons

theorem ssubset_iff_exists_cons_subset : s ⊂ t ↔ ∃ (a : _) (h : a ∉ s), s.cons a h ⊆ t := by
  refine' ⟨fun h => _, fun ⟨a, ha, h⟩ => ssubset_of_ssubset_of_subset (ssubset_cons _) h⟩
  -- ⊢ ∃ a h, cons a s h ⊆ t
  obtain ⟨a, hs, ht⟩ := not_subset.1 h.2
  -- ⊢ ∃ a h, cons a s h ⊆ t
  exact ⟨a, ht, cons_subset.2 ⟨hs, h.subset⟩⟩
  -- 🎉 no goals
#align finset.ssubset_iff_exists_cons_subset Finset.ssubset_iff_exists_cons_subset

end Cons

/-! ### disjoint -/


section Disjoint

variable {f : α → β} {s t u : Finset α} {a b : α}

theorem disjoint_left : Disjoint s t ↔ ∀ ⦃a⦄, a ∈ s → a ∉ t :=
  ⟨fun h a hs ht => not_mem_empty a <|
    singleton_subset_iff.mp (h (singleton_subset_iff.mpr hs) (singleton_subset_iff.mpr ht)),
    fun h _ hs ht _ ha => (h (hs ha) (ht ha)).elim⟩
#align finset.disjoint_left Finset.disjoint_left

theorem disjoint_right : Disjoint s t ↔ ∀ ⦃a⦄, a ∈ t → a ∉ s := by
  rw [_root_.disjoint_comm, disjoint_left]
  -- 🎉 no goals
#align finset.disjoint_right Finset.disjoint_right

theorem disjoint_iff_ne : Disjoint s t ↔ ∀ a ∈ s, ∀ b ∈ t, a ≠ b := by
  simp only [disjoint_left, imp_not_comm, forall_eq']
  -- 🎉 no goals
#align finset.disjoint_iff_ne Finset.disjoint_iff_ne

@[simp]
theorem disjoint_val : s.1.Disjoint t.1 ↔ Disjoint s t :=
  disjoint_left.symm
#align finset.disjoint_val Finset.disjoint_val

theorem _root_.Disjoint.forall_ne_finset (h : Disjoint s t) (ha : a ∈ s) (hb : b ∈ t) : a ≠ b :=
  disjoint_iff_ne.1 h _ ha _ hb
#align disjoint.forall_ne_finset Disjoint.forall_ne_finset

theorem not_disjoint_iff : ¬Disjoint s t ↔ ∃ a, a ∈ s ∧ a ∈ t :=
  disjoint_left.not.trans <| not_forall.trans <| exists_congr fun _ => by rw [not_imp, not_not]
                                                                          -- 🎉 no goals
#align finset.not_disjoint_iff Finset.not_disjoint_iff

theorem disjoint_of_subset_left (h : s ⊆ u) (d : Disjoint u t) : Disjoint s t :=
  disjoint_left.2 fun _x m₁ => (disjoint_left.1 d) (h m₁)
#align finset.disjoint_of_subset_left Finset.disjoint_of_subset_left

theorem disjoint_of_subset_right (h : t ⊆ u) (d : Disjoint s u) : Disjoint s t :=
  disjoint_right.2 fun _x m₁ => (disjoint_right.1 d) (h m₁)
#align finset.disjoint_of_subset_right Finset.disjoint_of_subset_right

@[simp]
theorem disjoint_empty_left (s : Finset α) : Disjoint ∅ s :=
  disjoint_bot_left
#align finset.disjoint_empty_left Finset.disjoint_empty_left

@[simp]
theorem disjoint_empty_right (s : Finset α) : Disjoint s ∅ :=
  disjoint_bot_right
#align finset.disjoint_empty_right Finset.disjoint_empty_right

@[simp]
theorem disjoint_singleton_left : Disjoint (singleton a) s ↔ a ∉ s := by
  simp only [disjoint_left, mem_singleton, forall_eq]
  -- 🎉 no goals
#align finset.disjoint_singleton_left Finset.disjoint_singleton_left

@[simp]
theorem disjoint_singleton_right : Disjoint s (singleton a) ↔ a ∉ s :=
  disjoint_comm.trans disjoint_singleton_left
#align finset.disjoint_singleton_right Finset.disjoint_singleton_right

-- Porting note: Left-hand side simplifies @[simp]
theorem disjoint_singleton : Disjoint ({a} : Finset α) {b} ↔ a ≠ b := by
  rw [disjoint_singleton_left, mem_singleton]
  -- 🎉 no goals
#align finset.disjoint_singleton Finset.disjoint_singleton

theorem disjoint_self_iff_empty (s : Finset α) : Disjoint s s ↔ s = ∅ :=
  disjoint_self
#align finset.disjoint_self_iff_empty Finset.disjoint_self_iff_empty

@[simp, norm_cast]
theorem disjoint_coe : Disjoint (s : Set α) t ↔ Disjoint s t := by
  simp only [Finset.disjoint_left, Set.disjoint_left, mem_coe]
  -- 🎉 no goals
#align finset.disjoint_coe Finset.disjoint_coe

@[simp, norm_cast]
theorem pairwiseDisjoint_coe {ι : Type*} {s : Set ι} {f : ι → Finset α} :
    s.PairwiseDisjoint (fun i => f i : ι → Set α) ↔ s.PairwiseDisjoint f :=
  forall₅_congr fun _ _ _ _ _ => disjoint_coe
#align finset.pairwise_disjoint_coe Finset.pairwiseDisjoint_coe

end Disjoint

/-! ### disjoint union -/


/-- `disjUnion s t h` is the set such that `a ∈ disjUnion s t h` iff `a ∈ s` or `a ∈ t`.
It is the same as `s ∪ t`, but it does not require decidable equality on the type. The hypothesis
ensures that the sets are disjoint. -/
def disjUnion (s t : Finset α) (h : Disjoint s t) : Finset α :=
  ⟨s.1 + t.1, Multiset.nodup_add.2 ⟨s.2, t.2, disjoint_val.2 h⟩⟩
#align finset.disj_union Finset.disjUnion

@[simp]
theorem mem_disjUnion {α s t h a} : a ∈ @disjUnion α s t h ↔ a ∈ s ∨ a ∈ t := by
  rcases s with ⟨⟨s⟩⟩; rcases t with ⟨⟨t⟩⟩; apply List.mem_append
  -- ⊢ a ∈ disjUnion { val := Quot.mk Setoid.r s, nodup := nodup✝ } t h ↔ a ∈ { val …
                       -- ⊢ a ∈ disjUnion { val := Quot.mk Setoid.r s, nodup := nodup✝¹ } { val := Quot. …
                                            -- 🎉 no goals
#align finset.mem_disj_union Finset.mem_disjUnion

theorem disjUnion_comm (s t : Finset α) (h : Disjoint s t) :
    disjUnion s t h = disjUnion t s h.symm :=
  eq_of_veq <| add_comm _ _
#align finset.disj_union_comm Finset.disjUnion_comm

@[simp]
theorem empty_disjUnion (t : Finset α) (h : Disjoint ∅ t := disjoint_bot_left) :
    disjUnion ∅ t h = t :=
  eq_of_veq <| zero_add _
#align finset.empty_disj_union Finset.empty_disjUnion

@[simp]
theorem disjUnion_empty (s : Finset α) (h : Disjoint s ∅ := disjoint_bot_right) :
    disjUnion s ∅ h = s :=
  eq_of_veq <| add_zero _
#align finset.disj_union_empty Finset.disjUnion_empty

theorem singleton_disjUnion (a : α) (t : Finset α) (h : Disjoint {a} t) :
    disjUnion {a} t h = cons a t (disjoint_singleton_left.mp h) :=
  eq_of_veq <| Multiset.singleton_add _ _
#align finset.singleton_disj_union Finset.singleton_disjUnion

theorem disjUnion_singleton (s : Finset α) (a : α) (h : Disjoint s {a}) :
    disjUnion s {a} h = cons a s (disjoint_singleton_right.mp h) := by
  rw [disjUnion_comm, singleton_disjUnion]
  -- 🎉 no goals
#align finset.disj_union_singleton Finset.disjUnion_singleton

/-! ### insert -/


section Insert

variable [DecidableEq α] {s t u v : Finset α} {a b : α}

/-- `insert a s` is the set `{a} ∪ s` containing `a` and the elements of `s`. -/
instance : Insert α (Finset α) :=
  ⟨fun a s => ⟨_, s.2.ndinsert a⟩⟩

theorem insert_def (a : α) (s : Finset α) : insert a s = ⟨_, s.2.ndinsert a⟩ :=
  rfl
#align finset.insert_def Finset.insert_def

@[simp]
theorem insert_val (a : α) (s : Finset α) : (insert a s).1 = ndinsert a s.1 :=
  rfl
#align finset.insert_val Finset.insert_val

theorem insert_val' (a : α) (s : Finset α) : (insert a s).1 = dedup (a ::ₘ s.1) := by
  rw [dedup_cons, dedup_eq_self]; rfl
  -- ⊢ (insert a s).val = ndinsert a s.val
                                  -- 🎉 no goals
#align finset.insert_val' Finset.insert_val'

theorem insert_val_of_not_mem {a : α} {s : Finset α} (h : a ∉ s) : (insert a s).1 = a ::ₘ s.1 := by
  rw [insert_val, ndinsert_of_not_mem h]
  -- 🎉 no goals
#align finset.insert_val_of_not_mem Finset.insert_val_of_not_mem

@[simp]
theorem mem_insert : a ∈ insert b s ↔ a = b ∨ a ∈ s :=
  mem_ndinsert
#align finset.mem_insert Finset.mem_insert

theorem mem_insert_self (a : α) (s : Finset α) : a ∈ insert a s :=
  mem_ndinsert_self a s.1
#align finset.mem_insert_self Finset.mem_insert_self

theorem mem_insert_of_mem (h : a ∈ s) : a ∈ insert b s :=
  mem_ndinsert_of_mem h
#align finset.mem_insert_of_mem Finset.mem_insert_of_mem

theorem mem_of_mem_insert_of_ne (h : b ∈ insert a s) : b ≠ a → b ∈ s :=
  (mem_insert.1 h).resolve_left
#align finset.mem_of_mem_insert_of_ne Finset.mem_of_mem_insert_of_ne

theorem eq_of_not_mem_of_mem_insert (ha : b ∈ insert a s) (hb : b ∉ s) : b = a :=
  (mem_insert.1 ha).resolve_right hb
#align finset.eq_of_not_mem_of_mem_insert Finset.eq_of_not_mem_of_mem_insert

@[simp]
theorem cons_eq_insert (a s h) : @cons α a s h = insert a s :=
  ext fun a => by simp
                  -- 🎉 no goals
#align finset.cons_eq_insert Finset.cons_eq_insert

@[simp, norm_cast]
theorem coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (insert a s : Set α) :=
  Set.ext fun x => by simp only [mem_coe, mem_insert, Set.mem_insert_iff]
                      -- 🎉 no goals
#align finset.coe_insert Finset.coe_insert

theorem mem_insert_coe {s : Finset α} {x y : α} : x ∈ insert y s ↔ x ∈ insert y (s : Set α) := by
  simp
  -- 🎉 no goals
#align finset.mem_insert_coe Finset.mem_insert_coe

instance : IsLawfulSingleton α (Finset α) :=
  ⟨fun a => by ext; simp⟩
               -- ⊢ a✝ ∈ insert a ∅ ↔ a✝ ∈ {a}
                    -- 🎉 no goals

@[simp]
theorem insert_eq_of_mem (h : a ∈ s) : insert a s = s :=
  eq_of_veq <| ndinsert_of_mem h
#align finset.insert_eq_of_mem Finset.insert_eq_of_mem

@[simp]
theorem insert_eq_self : insert a s = s ↔ a ∈ s :=
  ⟨fun h => h ▸ mem_insert_self _ _, insert_eq_of_mem⟩
#align finset.insert_eq_self Finset.insert_eq_self

theorem insert_ne_self : insert a s ≠ s ↔ a ∉ s :=
  insert_eq_self.not
#align finset.insert_ne_self Finset.insert_ne_self

-- Porting note: @[simp] can prove this
theorem pair_eq_singleton (a : α) : ({a, a} : Finset α) = {a} :=
  insert_eq_of_mem <| mem_singleton_self _
#align finset.pair_eq_singleton Finset.pair_eq_singleton

theorem Insert.comm (a b : α) (s : Finset α) : insert a (insert b s) = insert b (insert a s) :=
  ext fun x => by simp only [mem_insert, or_left_comm]
                  -- 🎉 no goals
#align finset.insert.comm Finset.Insert.comm

-- Porting note: @[simp] can prove this
@[norm_cast]
theorem coe_pair {a b : α} : (({a, b} : Finset α) : Set α) = {a, b} := by
  ext
  -- ⊢ x✝ ∈ ↑{a, b} ↔ x✝ ∈ {a, b}
  simp
  -- 🎉 no goals
#align finset.coe_pair Finset.coe_pair

@[simp, norm_cast]
theorem coe_eq_pair {s : Finset α} {a b : α} : (s : Set α) = {a, b} ↔ s = {a, b} := by
  rw [← coe_pair, coe_inj]
  -- 🎉 no goals
#align finset.coe_eq_pair Finset.coe_eq_pair

theorem pair_comm (a b : α) : ({a, b} : Finset α) = {b, a} :=
  Insert.comm a b ∅
#align finset.pair_comm Finset.pair_comm

-- Porting note: @[simp] can prove this
theorem insert_idem (a : α) (s : Finset α) : insert a (insert a s) = insert a s :=
  ext fun x => by simp only [mem_insert, ←or_assoc, or_self_iff]
                  -- 🎉 no goals
#align finset.insert_idem Finset.insert_idem

@[simp]
theorem insert_nonempty (a : α) (s : Finset α) : (insert a s).Nonempty :=
  ⟨a, mem_insert_self a s⟩
#align finset.insert_nonempty Finset.insert_nonempty

@[simp]
theorem insert_ne_empty (a : α) (s : Finset α) : insert a s ≠ ∅ :=
  (insert_nonempty a s).ne_empty
#align finset.insert_ne_empty Finset.insert_ne_empty

-- Porting note: explicit universe annotation is no longer required.
instance (i : α) (s : Finset α) : Nonempty ((insert i s : Finset α) : Set α) :=
  (Finset.coe_nonempty.mpr (s.insert_nonempty i)).to_subtype

theorem ne_insert_of_not_mem (s t : Finset α) {a : α} (h : a ∉ s) : s ≠ insert a t := by
  contrapose! h
  -- ⊢ a ∈ s
  simp [h]
  -- 🎉 no goals
#align finset.ne_insert_of_not_mem Finset.ne_insert_of_not_mem

theorem insert_subset_iff : insert a s ⊆ t ↔ a ∈ t ∧ s ⊆ t := by
  simp only [subset_iff, mem_insert, forall_eq, or_imp, forall_and]
  -- 🎉 no goals
#align finset.insert_subset Finset.insert_subset_iff

theorem insert_subset (ha : a ∈ t) (hs : s ⊆ t) : insert a s ⊆ t :=
  insert_subset_iff.mpr ⟨ha,hs⟩

theorem subset_insert (a : α) (s : Finset α) : s ⊆ insert a s := fun _b => mem_insert_of_mem
#align finset.subset_insert Finset.subset_insert

theorem insert_subset_insert (a : α) {s t : Finset α} (h : s ⊆ t) : insert a s ⊆ insert a t :=
  insert_subset_iff.2 ⟨mem_insert_self _ _, Subset.trans h (subset_insert _ _)⟩
#align finset.insert_subset_insert Finset.insert_subset_insert

theorem insert_inj (ha : a ∉ s) : insert a s = insert b s ↔ a = b :=
  ⟨fun h => eq_of_not_mem_of_mem_insert (h.subst <| mem_insert_self _ _) ha, congr_arg (insert · s)⟩
#align finset.insert_inj Finset.insert_inj

theorem insert_inj_on (s : Finset α) : Set.InjOn (fun a => insert a s) sᶜ := fun _ h _ _ =>
  (insert_inj h).1
#align finset.insert_inj_on Finset.insert_inj_on

theorem ssubset_iff : s ⊂ t ↔ ∃ (a : α) (_ : a ∉ s), insert a s ⊆ t := by
  exact_mod_cast @Set.ssubset_iff_insert α s t
  -- 🎉 no goals
#align finset.ssubset_iff Finset.ssubset_iff

theorem ssubset_insert (h : a ∉ s) : s ⊂ insert a s :=
  ssubset_iff.mpr ⟨a, h, Subset.rfl⟩
#align finset.ssubset_insert Finset.ssubset_insert

@[elab_as_elim]
theorem cons_induction {α : Type*} {p : Finset α → Prop} (empty : p ∅)
    (cons : ∀ ⦃a : α⦄ {s : Finset α} (h : a ∉ s), p s → p (cons a s h)) : ∀ s, p s
  | ⟨s, nd⟩ => by
    induction s using Multiset.induction with
    | empty => exact empty
    | @cons a s IH =>
      cases' nodup_cons.1 nd with m nd'
      rw [← (eq_of_veq _ : Finset.cons a ⟨s, _⟩ m = ⟨a ::ₘ s, nd⟩)]
      · exact cons m (IH nd')
      · rw [cons_val]
#align finset.cons_induction Finset.cons_induction

@[elab_as_elim]
theorem cons_induction_on {α : Type*} {p : Finset α → Prop} (s : Finset α) (h₁ : p ∅)
    (h₂ : ∀ ⦃a : α⦄ {s : Finset α} (h : a ∉ s), p s → p (cons a s h)) : p s :=
  cons_induction h₁ h₂ s
#align finset.cons_induction_on Finset.cons_induction_on

@[elab_as_elim]
protected theorem induction {α : Type*} {p : Finset α → Prop} [DecidableEq α] (empty : p ∅)
    (insert : ∀ ⦃a : α⦄ {s : Finset α}, a ∉ s → p s → p (insert a s)) : ∀ s, p s :=
  cons_induction empty fun a s ha => (s.cons_eq_insert a ha).symm ▸ insert ha
#align finset.induction Finset.induction

/-- To prove a proposition about an arbitrary `Finset α`,
it suffices to prove it for the empty `Finset`,
and to show that if it holds for some `Finset α`,
then it holds for the `Finset` obtained by inserting a new element.
-/
@[elab_as_elim]
protected theorem induction_on {α : Type*} {p : Finset α → Prop} [DecidableEq α] (s : Finset α)
    (empty : p ∅) (insert : ∀ ⦃a : α⦄ {s : Finset α}, a ∉ s → p s → p (insert a s)) : p s :=
  Finset.induction empty insert s
#align finset.induction_on Finset.induction_on

/-- To prove a proposition about `S : Finset α`,
it suffices to prove it for the empty `Finset`,
and to show that if it holds for some `Finset α ⊆ S`,
then it holds for the `Finset` obtained by inserting a new element of `S`.
-/
@[elab_as_elim]
theorem induction_on' {α : Type*} {p : Finset α → Prop} [DecidableEq α] (S : Finset α) (h₁ : p ∅)
    (h₂ : ∀ {a s}, a ∈ S → s ⊆ S → a ∉ s → p s → p (insert a s)) : p S :=
  @Finset.induction_on α (fun T => T ⊆ S → p T) _ S (fun _ => h₁)
    (fun _ _ has hqs hs =>
      let ⟨hS, sS⟩ := Finset.insert_subset_iff.1 hs
      h₂ hS sS has (hqs sS))
    (Finset.Subset.refl S)
#align finset.induction_on' Finset.induction_on'

/-- To prove a proposition about a nonempty `s : Finset α`, it suffices to show it holds for all
singletons and that if it holds for nonempty `t : Finset α`, then it also holds for the `Finset`
obtained by inserting an element in `t`. -/
@[elab_as_elim]
theorem Nonempty.cons_induction {α : Type*} {p : ∀ s : Finset α, s.Nonempty → Prop}
    (h₀ : ∀ a, p {a} (singleton_nonempty _))
    (h₁ : ∀ ⦃a⦄ (s) (h : a ∉ s) (hs), p s hs → p (Finset.cons a s h) (nonempty_cons h))
    {s : Finset α} (hs : s.Nonempty) : p s hs := by
  induction' s using Finset.cons_induction with a t ha h
  -- ⊢ p ∅ hs
  · exact (not_nonempty_empty hs).elim
    -- 🎉 no goals
  obtain rfl | ht := t.eq_empty_or_nonempty
  -- ⊢ p (cons a ∅ ha) hs
  · exact h₀ a
    -- 🎉 no goals
  · exact h₁ t ha ht (h ht)
    -- 🎉 no goals
#align finset.nonempty.cons_induction Finset.Nonempty.cons_induction

/-- Inserting an element to a finite set is equivalent to the option type. -/
def subtypeInsertEquivOption {t : Finset α} {x : α} (h : x ∉ t) :
    { i // i ∈ insert x t } ≃ Option { i // i ∈ t } := by
  refine'
    { toFun := fun y => if h : ↑y = x then none else some ⟨y, (mem_insert.mp y.2).resolve_left h⟩
      invFun := fun y => (y.elim ⟨x, mem_insert_self _ _⟩) fun z => ⟨z, mem_insert_of_mem z.2⟩.. }
  · intro y
    -- ⊢ (fun y => Option.elim y { val := x, property := (_ : x ∈ insert x t) } fun z …
    by_cases h : ↑y = x
    -- ⊢ (fun y => Option.elim y { val := x, property := (_ : x ∈ insert x t) } fun z …
    · simp only [Subtype.ext_iff, h, Option.elim, dif_pos, Subtype.coe_mk]
      -- 🎉 no goals
    · simp only [h, Option.elim, dif_neg, not_false_iff, Subtype.coe_eta, Subtype.coe_mk]
      -- 🎉 no goals
  · rintro (_ | y)
    -- ⊢ (fun y => if h : ↑y = x then none else some { val := ↑y, property := (_ : ↑y …
    · simp only [Option.elim, dif_pos]
      -- 🎉 no goals
    · have : ↑y ≠ x := by
        rintro ⟨⟩
        exact h y.2
      simp only [this, Option.elim, Subtype.eta, dif_neg, not_false_iff, Subtype.coe_mk]
      -- 🎉 no goals
#align finset.subtype_insert_equiv_option Finset.subtypeInsertEquivOption

@[simp]
theorem disjoint_insert_left : Disjoint (insert a s) t ↔ a ∉ t ∧ Disjoint s t := by
  simp only [disjoint_left, mem_insert, or_imp, forall_and, forall_eq]
  -- 🎉 no goals
#align finset.disjoint_insert_left Finset.disjoint_insert_left

@[simp]
theorem disjoint_insert_right : Disjoint s (insert a t) ↔ a ∉ s ∧ Disjoint s t :=
  disjoint_comm.trans <| by rw [disjoint_insert_left, _root_.disjoint_comm]
                            -- 🎉 no goals
#align finset.disjoint_insert_right Finset.disjoint_insert_right

end Insert

/-! ### Lattice structure -/


section Lattice

variable [DecidableEq α] {s s₁ s₂ t t₁ t₂ u v : Finset α} {a b : α}

/-- `s ∪ t` is the set such that `a ∈ s ∪ t` iff `a ∈ s` or `a ∈ t`. -/
instance : Union (Finset α) :=
  ⟨fun s t => ⟨_, t.2.ndunion s.1⟩⟩

/-- `s ∩ t` is the set such that `a ∈ s ∩ t` iff `a ∈ s` and `a ∈ t`. -/
instance : Inter (Finset α) :=
  ⟨fun s t => ⟨_, s.2.ndinter t.1⟩⟩

instance : Lattice (Finset α) :=
  { Finset.partialOrder with
    sup := (· ∪ ·)
    sup_le := fun _ _ _ hs ht _ ha => (mem_ndunion.1 ha).elim (fun h => hs h) fun h => ht h
    le_sup_left := fun _ _ _ h => mem_ndunion.2 <| Or.inl h
    le_sup_right := fun _ _ _ h => mem_ndunion.2 <| Or.inr h
    inf := (· ∩ ·)
    le_inf := fun _ _ _ ht hu _ h => mem_ndinter.2 ⟨ht h, hu h⟩
    inf_le_left := fun _ _ _ h => (mem_ndinter.1 h).1
    inf_le_right := fun _ _ _ h => (mem_ndinter.1 h).2 }

@[simp]
theorem sup_eq_union : (Sup.sup : Finset α → Finset α → Finset α) = Union.union :=
  rfl
#align finset.sup_eq_union Finset.sup_eq_union

@[simp]
theorem inf_eq_inter : (Inf.inf : Finset α → Finset α → Finset α) = Inter.inter :=
  rfl
#align finset.inf_eq_inter Finset.inf_eq_inter

theorem disjoint_iff_inter_eq_empty : Disjoint s t ↔ s ∩ t = ∅ :=
  disjoint_iff
#align finset.disjoint_iff_inter_eq_empty Finset.disjoint_iff_inter_eq_empty

instance decidableDisjoint (U V : Finset α) : Decidable (Disjoint U V) :=
  decidable_of_iff _ disjoint_left.symm
#align finset.decidable_disjoint Finset.decidableDisjoint

/-! #### union -/


theorem union_val_nd (s t : Finset α) : (s ∪ t).1 = ndunion s.1 t.1 :=
  rfl
#align finset.union_val_nd Finset.union_val_nd

@[simp]
theorem union_val (s t : Finset α) : (s ∪ t).1 = s.1 ∪ t.1 :=
  ndunion_eq_union s.2
#align finset.union_val Finset.union_val

@[simp]
theorem mem_union : a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t :=
  mem_ndunion
#align finset.mem_union Finset.mem_union

@[simp]
theorem disjUnion_eq_union (s t h) : @disjUnion α s t h = s ∪ t :=
  ext fun a => by simp
                  -- 🎉 no goals
#align finset.disj_union_eq_union Finset.disjUnion_eq_union

theorem mem_union_left (t : Finset α) (h : a ∈ s) : a ∈ s ∪ t :=
  mem_union.2 <| Or.inl h
#align finset.mem_union_left Finset.mem_union_left

theorem mem_union_right (s : Finset α) (h : a ∈ t) : a ∈ s ∪ t :=
  mem_union.2 <| Or.inr h
#align finset.mem_union_right Finset.mem_union_right

theorem forall_mem_union {p : α → Prop} : (∀ a ∈ s ∪ t, p a) ↔ (∀ a ∈ s, p a) ∧ ∀ a ∈ t, p a :=
  ⟨fun h => ⟨fun a => h a ∘ mem_union_left _, fun b => h b ∘ mem_union_right _⟩,
   fun h _ab hab => (mem_union.mp hab).elim (h.1 _) (h.2 _)⟩
#align finset.forall_mem_union Finset.forall_mem_union

theorem not_mem_union : a ∉ s ∪ t ↔ a ∉ s ∧ a ∉ t := by rw [mem_union, not_or]
                                                        -- 🎉 no goals
#align finset.not_mem_union Finset.not_mem_union

@[simp, norm_cast]
theorem coe_union (s₁ s₂ : Finset α) : ↑(s₁ ∪ s₂) = (s₁ ∪ s₂ : Set α) :=
  Set.ext fun _ => mem_union
#align finset.coe_union Finset.coe_union

theorem union_subset (hs : s ⊆ u) : t ⊆ u → s ∪ t ⊆ u :=
  sup_le <| le_iff_subset.2 hs
#align finset.union_subset Finset.union_subset

theorem subset_union_left (s₁ s₂ : Finset α) : s₁ ⊆ s₁ ∪ s₂ := fun _x => mem_union_left _
#align finset.subset_union_left Finset.subset_union_left

theorem subset_union_right (s₁ s₂ : Finset α) : s₂ ⊆ s₁ ∪ s₂ := fun _x => mem_union_right _
#align finset.subset_union_right Finset.subset_union_right

theorem union_subset_union (hsu : s ⊆ u) (htv : t ⊆ v) : s ∪ t ⊆ u ∪ v :=
  sup_le_sup (le_iff_subset.2 hsu) htv
#align finset.union_subset_union Finset.union_subset_union

theorem union_subset_union_left (h : s₁ ⊆ s₂) : s₁ ∪ t ⊆ s₂ ∪ t :=
  union_subset_union h Subset.rfl
#align finset.union_subset_union_left Finset.union_subset_union_left

theorem union_subset_union_right (h : t₁ ⊆ t₂) : s ∪ t₁ ⊆ s ∪ t₂ :=
  union_subset_union Subset.rfl h
#align finset.union_subset_union_right Finset.union_subset_union_right

theorem union_comm (s₁ s₂ : Finset α) : s₁ ∪ s₂ = s₂ ∪ s₁ :=
  sup_comm
#align finset.union_comm Finset.union_comm

instance : IsCommutative (Finset α) (· ∪ ·) :=
  ⟨union_comm⟩

@[simp]
theorem union_assoc (s₁ s₂ s₃ : Finset α) : s₁ ∪ s₂ ∪ s₃ = s₁ ∪ (s₂ ∪ s₃) :=
  sup_assoc
#align finset.union_assoc Finset.union_assoc

instance : IsAssociative (Finset α) (· ∪ ·) :=
  ⟨union_assoc⟩

@[simp]
theorem union_idempotent (s : Finset α) : s ∪ s = s :=
  sup_idem
#align finset.union_idempotent Finset.union_idempotent

instance : IsIdempotent (Finset α) (· ∪ ·) :=
  ⟨union_idempotent⟩

theorem union_subset_left (h : s ∪ t ⊆ u) : s ⊆ u :=
  (subset_union_left _ _).trans h
#align finset.union_subset_left Finset.union_subset_left

theorem union_subset_right {s t u : Finset α} (h : s ∪ t ⊆ u) : t ⊆ u :=
  Subset.trans (subset_union_right _ _) h
#align finset.union_subset_right Finset.union_subset_right

theorem union_left_comm (s t u : Finset α) : s ∪ (t ∪ u) = t ∪ (s ∪ u) :=
  ext fun _ => by simp only [mem_union, or_left_comm]
                  -- 🎉 no goals
#align finset.union_left_comm Finset.union_left_comm

theorem union_right_comm (s t u : Finset α) : s ∪ t ∪ u = s ∪ u ∪ t :=
  ext fun x => by simp only [mem_union, or_assoc, @or_comm (x ∈ t)]
                  -- 🎉 no goals
#align finset.union_right_comm Finset.union_right_comm

theorem union_self (s : Finset α) : s ∪ s = s :=
  union_idempotent s
#align finset.union_self Finset.union_self

@[simp]
theorem union_empty (s : Finset α) : s ∪ ∅ = s :=
  ext fun x => mem_union.trans <| by simp
                                     -- 🎉 no goals
#align finset.union_empty Finset.union_empty

@[simp]
theorem empty_union (s : Finset α) : ∅ ∪ s = s :=
  ext fun x => mem_union.trans <| by simp
                                     -- 🎉 no goals
#align finset.empty_union Finset.empty_union

theorem Nonempty.inl {s t : Finset α} (h : s.Nonempty) : (s ∪ t).Nonempty :=
  h.mono $ subset_union_left s t

theorem Nonempty.inr {s t : Finset α} (h : t.Nonempty) : (s ∪ t).Nonempty :=
  h.mono $ subset_union_right s t

theorem insert_eq (a : α) (s : Finset α) : insert a s = {a} ∪ s :=
  rfl
#align finset.insert_eq Finset.insert_eq

@[simp]
theorem insert_union (a : α) (s t : Finset α) : insert a s ∪ t = insert a (s ∪ t) := by
  simp only [insert_eq, union_assoc]
  -- 🎉 no goals
#align finset.insert_union Finset.insert_union

@[simp]
theorem union_insert (a : α) (s t : Finset α) : s ∪ insert a t = insert a (s ∪ t) := by
  simp only [insert_eq, union_left_comm]
  -- 🎉 no goals
#align finset.union_insert Finset.union_insert

theorem insert_union_distrib (a : α) (s t : Finset α) :
    insert a (s ∪ t) = insert a s ∪ insert a t := by
  simp only [insert_union, union_insert, insert_idem]
  -- 🎉 no goals
#align finset.insert_union_distrib Finset.insert_union_distrib

@[simp]
theorem union_eq_left_iff_subset {s t : Finset α} : s ∪ t = s ↔ t ⊆ s :=
  sup_eq_left
#align finset.union_eq_left_iff_subset Finset.union_eq_left_iff_subset

@[simp]
theorem left_eq_union_iff_subset {s t : Finset α} : s = s ∪ t ↔ t ⊆ s := by
  rw [← union_eq_left_iff_subset, eq_comm]
  -- 🎉 no goals
#align finset.left_eq_union_iff_subset Finset.left_eq_union_iff_subset

@[simp]
theorem union_eq_right_iff_subset {s t : Finset α} : s ∪ t = t ↔ s ⊆ t :=
  sup_eq_right
#align finset.union_eq_right_iff_subset Finset.union_eq_right_iff_subset

@[simp]
theorem right_eq_union_iff_subset {s t : Finset α} : s = t ∪ s ↔ t ⊆ s := by
  rw [← union_eq_right_iff_subset, eq_comm]
  -- 🎉 no goals
#align finset.right_eq_union_iff_subset Finset.right_eq_union_iff_subset

-- Porting note: replaced `⊔` in RHS
theorem union_congr_left (ht : t ⊆ s ∪ u) (hu : u ⊆ s ∪ t) : s ∪ t = s ∪ u :=
  sup_congr_left ht hu
#align finset.union_congr_left Finset.union_congr_left

theorem union_congr_right (hs : s ⊆ t ∪ u) (ht : t ⊆ s ∪ u) : s ∪ u = t ∪ u :=
  sup_congr_right hs ht
#align finset.union_congr_right Finset.union_congr_right

theorem union_eq_union_iff_left : s ∪ t = s ∪ u ↔ t ⊆ s ∪ u ∧ u ⊆ s ∪ t :=
  sup_eq_sup_iff_left
#align finset.union_eq_union_iff_left Finset.union_eq_union_iff_left

theorem union_eq_union_iff_right : s ∪ u = t ∪ u ↔ s ⊆ t ∪ u ∧ t ⊆ s ∪ u :=
  sup_eq_sup_iff_right
#align finset.union_eq_union_iff_right Finset.union_eq_union_iff_right

@[simp]
theorem disjoint_union_left : Disjoint (s ∪ t) u ↔ Disjoint s u ∧ Disjoint t u := by
  simp only [disjoint_left, mem_union, or_imp, forall_and]
  -- 🎉 no goals
#align finset.disjoint_union_left Finset.disjoint_union_left

@[simp]
theorem disjoint_union_right : Disjoint s (t ∪ u) ↔ Disjoint s t ∧ Disjoint s u := by
  simp only [disjoint_right, mem_union, or_imp, forall_and]
  -- 🎉 no goals
#align finset.disjoint_union_right Finset.disjoint_union_right

/-- To prove a relation on pairs of `Finset X`, it suffices to show that it is
  * symmetric,
  * it holds when one of the `Finset`s is empty,
  * it holds for pairs of singletons,
  * if it holds for `[a, c]` and for `[b, c]`, then it holds for `[a ∪ b, c]`.
-/
theorem induction_on_union (P : Finset α → Finset α → Prop) (symm : ∀ {a b}, P a b → P b a)
    (empty_right : ∀ {a}, P a ∅) (singletons : ∀ {a b}, P {a} {b})
    (union_of : ∀ {a b c}, P a c → P b c → P (a ∪ b) c) : ∀ a b, P a b := by
  intro a b
  -- ⊢ P a b
  refine' Finset.induction_on b empty_right fun x s _xs hi => symm _
  -- ⊢ P (insert x s) a
  rw [Finset.insert_eq]
  -- ⊢ P ({x} ∪ s) a
  apply union_of _ (symm hi)
  -- ⊢ P {x} a
  refine' Finset.induction_on a empty_right fun a t _ta hi => symm _
  -- ⊢ P (insert a t) {x}
  rw [Finset.insert_eq]
  -- ⊢ P ({a} ∪ t) {x}
  exact union_of singletons (symm hi)
  -- 🎉 no goals
#align finset.induction_on_union Finset.induction_on_union

theorem _root_.Directed.exists_mem_subset_of_finset_subset_biUnion {α ι : Type*} [hn : Nonempty ι]
    {f : ι → Set α} (h : Directed (· ⊆ ·) f) {s : Finset α} (hs : (s : Set α) ⊆ ⋃ i, f i) :
    ∃ i, (s : Set α) ⊆ f i := by
  classical
    revert hs
    refine' s.induction_on _ _
    · refine' fun _ => ⟨hn.some, _⟩
      simp only [coe_empty, Set.empty_subset]
    · intro b t _hbt htc hbtc
      obtain ⟨i : ι, hti : (t : Set α) ⊆ f i⟩ := htc (Set.Subset.trans (t.subset_insert b) hbtc)
      obtain ⟨j, hbj⟩ : ∃ j, b ∈ f j := by simpa [Set.mem_iUnion₂] using hbtc (t.mem_insert_self b)
      rcases h j i with ⟨k, hk, hk'⟩
      use k
      rw [coe_insert, Set.insert_subset_iff]
      exact ⟨hk hbj, _root_.trans hti hk'⟩
#align directed.exists_mem_subset_of_finset_subset_bUnion Directed.exists_mem_subset_of_finset_subset_biUnion

theorem _root_.DirectedOn.exists_mem_subset_of_finset_subset_biUnion {α ι : Type*} {f : ι → Set α}
    {c : Set ι} (hn : c.Nonempty) (hc : DirectedOn (fun i j => f i ⊆ f j) c) {s : Finset α}
    (hs : (s : Set α) ⊆ ⋃ i ∈ c, f i) : ∃ i ∈ c, (s : Set α) ⊆ f i := by
  rw [Set.biUnion_eq_iUnion] at hs
  -- ⊢ ∃ i, i ∈ c ∧ ↑s ⊆ f i
  haveI := hn.coe_sort
  -- ⊢ ∃ i, i ∈ c ∧ ↑s ⊆ f i
  obtain ⟨⟨i, hic⟩, hi⟩ :=
    (directed_comp.2 hc.directed_val).exists_mem_subset_of_finset_subset_biUnion hs
  exact ⟨i, hic, hi⟩
  -- 🎉 no goals
#align directed_on.exists_mem_subset_of_finset_subset_bUnion DirectedOn.exists_mem_subset_of_finset_subset_biUnion


/-! #### inter -/


theorem inter_val_nd (s₁ s₂ : Finset α) : (s₁ ∩ s₂).1 = ndinter s₁.1 s₂.1 :=
  rfl
#align finset.inter_val_nd Finset.inter_val_nd

@[simp]
theorem inter_val (s₁ s₂ : Finset α) : (s₁ ∩ s₂).1 = s₁.1 ∩ s₂.1 :=
  ndinter_eq_inter s₁.2
#align finset.inter_val Finset.inter_val

@[simp]
theorem mem_inter {a : α} {s₁ s₂ : Finset α} : a ∈ s₁ ∩ s₂ ↔ a ∈ s₁ ∧ a ∈ s₂ :=
  mem_ndinter
#align finset.mem_inter Finset.mem_inter

theorem mem_of_mem_inter_left {a : α} {s₁ s₂ : Finset α} (h : a ∈ s₁ ∩ s₂) : a ∈ s₁ :=
  (mem_inter.1 h).1
#align finset.mem_of_mem_inter_left Finset.mem_of_mem_inter_left

theorem mem_of_mem_inter_right {a : α} {s₁ s₂ : Finset α} (h : a ∈ s₁ ∩ s₂) : a ∈ s₂ :=
  (mem_inter.1 h).2
#align finset.mem_of_mem_inter_right Finset.mem_of_mem_inter_right

theorem mem_inter_of_mem {a : α} {s₁ s₂ : Finset α} : a ∈ s₁ → a ∈ s₂ → a ∈ s₁ ∩ s₂ :=
  and_imp.1 mem_inter.2
#align finset.mem_inter_of_mem Finset.mem_inter_of_mem

theorem inter_subset_left (s₁ s₂ : Finset α) : s₁ ∩ s₂ ⊆ s₁ := fun _a => mem_of_mem_inter_left
#align finset.inter_subset_left Finset.inter_subset_left

theorem inter_subset_right (s₁ s₂ : Finset α) : s₁ ∩ s₂ ⊆ s₂ := fun _a => mem_of_mem_inter_right
#align finset.inter_subset_right Finset.inter_subset_right

theorem subset_inter {s₁ s₂ u : Finset α} : s₁ ⊆ s₂ → s₁ ⊆ u → s₁ ⊆ s₂ ∩ u := by
  simp (config := { contextual := true }) [subset_iff, mem_inter]
  -- 🎉 no goals
#align finset.subset_inter Finset.subset_inter

@[simp, norm_cast]
theorem coe_inter (s₁ s₂ : Finset α) : ↑(s₁ ∩ s₂) = (s₁ ∩ s₂ : Set α) :=
  Set.ext fun _ => mem_inter
#align finset.coe_inter Finset.coe_inter

@[simp]
theorem union_inter_cancel_left {s t : Finset α} : (s ∪ t) ∩ s = s := by
  rw [← coe_inj, coe_inter, coe_union, Set.union_inter_cancel_left]
  -- 🎉 no goals
#align finset.union_inter_cancel_left Finset.union_inter_cancel_left

@[simp]
theorem union_inter_cancel_right {s t : Finset α} : (s ∪ t) ∩ t = t := by
  rw [← coe_inj, coe_inter, coe_union, Set.union_inter_cancel_right]
  -- 🎉 no goals
#align finset.union_inter_cancel_right Finset.union_inter_cancel_right

theorem inter_comm (s₁ s₂ : Finset α) : s₁ ∩ s₂ = s₂ ∩ s₁ :=
  ext fun _ => by simp only [mem_inter, and_comm]
                  -- 🎉 no goals
#align finset.inter_comm Finset.inter_comm

@[simp]
theorem inter_assoc (s₁ s₂ s₃ : Finset α) : s₁ ∩ s₂ ∩ s₃ = s₁ ∩ (s₂ ∩ s₃) :=
  ext fun _ => by simp only [mem_inter, and_assoc]
                  -- 🎉 no goals
#align finset.inter_assoc Finset.inter_assoc

theorem inter_left_comm (s₁ s₂ s₃ : Finset α) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
  ext fun _ => by simp only [mem_inter, and_left_comm]
                  -- 🎉 no goals
#align finset.inter_left_comm Finset.inter_left_comm

theorem inter_right_comm (s₁ s₂ s₃ : Finset α) : s₁ ∩ s₂ ∩ s₃ = s₁ ∩ s₃ ∩ s₂ :=
  ext fun _ => by simp only [mem_inter, and_right_comm]
                  -- 🎉 no goals
#align finset.inter_right_comm Finset.inter_right_comm

@[simp]
theorem inter_self (s : Finset α) : s ∩ s = s :=
  ext fun _ => mem_inter.trans <| and_self_iff _
#align finset.inter_self Finset.inter_self

@[simp]
theorem inter_empty (s : Finset α) : s ∩ ∅ = ∅ :=
  ext fun _ => mem_inter.trans <| by simp
                                     -- 🎉 no goals
#align finset.inter_empty Finset.inter_empty

@[simp]
theorem empty_inter (s : Finset α) : ∅ ∩ s = ∅ :=
  ext fun _ => mem_inter.trans <| by simp
                                     -- 🎉 no goals
#align finset.empty_inter Finset.empty_inter

@[simp]
theorem inter_union_self (s t : Finset α) : s ∩ (t ∪ s) = s := by
  rw [inter_comm, union_inter_cancel_right]
  -- 🎉 no goals
#align finset.inter_union_self Finset.inter_union_self

@[simp]
theorem insert_inter_of_mem {s₁ s₂ : Finset α} {a : α} (h : a ∈ s₂) :
    insert a s₁ ∩ s₂ = insert a (s₁ ∩ s₂) :=
  ext fun x => by
    have : x = a ∨ x ∈ s₂ ↔ x ∈ s₂ := or_iff_right_of_imp <| by rintro rfl; exact h
    -- ⊢ x ∈ insert a s₁ ∩ s₂ ↔ x ∈ insert a (s₁ ∩ s₂)
    simp only [mem_inter, mem_insert, or_and_left, this]
    -- 🎉 no goals
#align finset.insert_inter_of_mem Finset.insert_inter_of_mem

@[simp]
theorem inter_insert_of_mem {s₁ s₂ : Finset α} {a : α} (h : a ∈ s₁) :
    s₁ ∩ insert a s₂ = insert a (s₁ ∩ s₂) := by rw [inter_comm, insert_inter_of_mem h, inter_comm]
                                                -- 🎉 no goals
#align finset.inter_insert_of_mem Finset.inter_insert_of_mem

@[simp]
theorem insert_inter_of_not_mem {s₁ s₂ : Finset α} {a : α} (h : a ∉ s₂) :
    insert a s₁ ∩ s₂ = s₁ ∩ s₂ :=
  ext fun x => by
    have : ¬(x = a ∧ x ∈ s₂) := by rintro ⟨rfl, H⟩; exact h H
    -- ⊢ x ∈ insert a s₁ ∩ s₂ ↔ x ∈ s₁ ∩ s₂
    simp only [mem_inter, mem_insert, or_and_right, this, false_or_iff]
    -- 🎉 no goals
#align finset.insert_inter_of_not_mem Finset.insert_inter_of_not_mem

@[simp]
theorem inter_insert_of_not_mem {s₁ s₂ : Finset α} {a : α} (h : a ∉ s₁) :
    s₁ ∩ insert a s₂ = s₁ ∩ s₂ := by rw [inter_comm, insert_inter_of_not_mem h, inter_comm]
                                     -- 🎉 no goals
#align finset.inter_insert_of_not_mem Finset.inter_insert_of_not_mem

@[simp]
theorem singleton_inter_of_mem {a : α} {s : Finset α} (H : a ∈ s) : {a} ∩ s = {a} :=
  show insert a ∅ ∩ s = insert a ∅ by rw [insert_inter_of_mem H, empty_inter]
                                      -- 🎉 no goals
#align finset.singleton_inter_of_mem Finset.singleton_inter_of_mem

@[simp]
theorem singleton_inter_of_not_mem {a : α} {s : Finset α} (H : a ∉ s) : {a} ∩ s = ∅ :=
  eq_empty_of_forall_not_mem <| by
    simp only [mem_inter, mem_singleton]; rintro x ⟨rfl, h⟩; exact H h
    -- ⊢ ∀ (x : α), ¬(x = a ∧ x ∈ s)
                                          -- ⊢ False
                                                             -- 🎉 no goals
#align finset.singleton_inter_of_not_mem Finset.singleton_inter_of_not_mem

@[simp]
theorem inter_singleton_of_mem {a : α} {s : Finset α} (h : a ∈ s) : s ∩ {a} = {a} := by
  rw [inter_comm, singleton_inter_of_mem h]
  -- 🎉 no goals
#align finset.inter_singleton_of_mem Finset.inter_singleton_of_mem

@[simp]
theorem inter_singleton_of_not_mem {a : α} {s : Finset α} (h : a ∉ s) : s ∩ {a} = ∅ := by
  rw [inter_comm, singleton_inter_of_not_mem h]
  -- 🎉 no goals
#align finset.inter_singleton_of_not_mem Finset.inter_singleton_of_not_mem

@[mono]
theorem inter_subset_inter {x y s t : Finset α} (h : x ⊆ y) (h' : s ⊆ t) : x ∩ s ⊆ y ∩ t := by
  intro a a_in
  -- ⊢ a ∈ y ∩ t
  rw [Finset.mem_inter] at a_in ⊢
  -- ⊢ a ∈ y ∧ a ∈ t
  exact ⟨h a_in.1, h' a_in.2⟩
  -- 🎉 no goals
#align finset.inter_subset_inter Finset.inter_subset_inter

theorem inter_subset_inter_left (h : t ⊆ u) : s ∩ t ⊆ s ∩ u :=
  inter_subset_inter Subset.rfl h
#align finset.inter_subset_inter_left Finset.inter_subset_inter_left

theorem inter_subset_inter_right (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  inter_subset_inter h Subset.rfl
#align finset.inter_subset_inter_right Finset.inter_subset_inter_right

theorem inter_subset_union : s ∩ t ⊆ s ∪ t :=
  le_iff_subset.1 inf_le_sup
#align finset.inter_subset_union Finset.inter_subset_union

instance : DistribLattice (Finset α) :=
  { le_sup_inf := fun a b c => by
      simp (config := { contextual := true }) only
        [sup_eq_union, inf_eq_inter, le_eq_subset, subset_iff, mem_inter, mem_union, and_imp,
        or_imp, true_or_iff, imp_true_iff, true_and_iff, or_true_iff] }

@[simp]
theorem union_left_idem (s t : Finset α) : s ∪ (s ∪ t) = s ∪ t :=
  sup_left_idem
#align finset.union_left_idem Finset.union_left_idem

-- Porting note: @[simp] can prove this
theorem union_right_idem (s t : Finset α) : s ∪ t ∪ t = s ∪ t :=
  sup_right_idem
#align finset.union_right_idem Finset.union_right_idem

@[simp]
theorem inter_left_idem (s t : Finset α) : s ∩ (s ∩ t) = s ∩ t :=
  inf_left_idem
#align finset.inter_left_idem Finset.inter_left_idem

-- Porting note: @[simp] can prove this
theorem inter_right_idem (s t : Finset α) : s ∩ t ∩ t = s ∩ t :=
  inf_right_idem
#align finset.inter_right_idem Finset.inter_right_idem

theorem inter_distrib_left (s t u : Finset α) : s ∩ (t ∪ u) = s ∩ t ∪ s ∩ u :=
  inf_sup_left
#align finset.inter_distrib_left Finset.inter_distrib_left

theorem inter_distrib_right (s t u : Finset α) : (s ∪ t) ∩ u = s ∩ u ∪ t ∩ u :=
  inf_sup_right
#align finset.inter_distrib_right Finset.inter_distrib_right

theorem union_distrib_left (s t u : Finset α) : s ∪ t ∩ u = (s ∪ t) ∩ (s ∪ u) :=
  sup_inf_left
#align finset.union_distrib_left Finset.union_distrib_left

theorem union_distrib_right (s t u : Finset α) : s ∩ t ∪ u = (s ∪ u) ∩ (t ∪ u) :=
  sup_inf_right
#align finset.union_distrib_right Finset.union_distrib_right

theorem union_union_distrib_left (s t u : Finset α) : s ∪ (t ∪ u) = s ∪ t ∪ (s ∪ u) :=
  sup_sup_distrib_left _ _ _
#align finset.union_union_distrib_left Finset.union_union_distrib_left

theorem union_union_distrib_right (s t u : Finset α) : s ∪ t ∪ u = s ∪ u ∪ (t ∪ u) :=
  sup_sup_distrib_right _ _ _
#align finset.union_union_distrib_right Finset.union_union_distrib_right

theorem inter_inter_distrib_left (s t u : Finset α) : s ∩ (t ∩ u) = s ∩ t ∩ (s ∩ u) :=
  inf_inf_distrib_left _ _ _
#align finset.inter_inter_distrib_left Finset.inter_inter_distrib_left

theorem inter_inter_distrib_right (s t u : Finset α) : s ∩ t ∩ u = s ∩ u ∩ (t ∩ u) :=
  inf_inf_distrib_right _ _ _
#align finset.inter_inter_distrib_right Finset.inter_inter_distrib_right

theorem union_union_union_comm (s t u v : Finset α) : s ∪ t ∪ (u ∪ v) = s ∪ u ∪ (t ∪ v) :=
  sup_sup_sup_comm _ _ _ _
#align finset.union_union_union_comm Finset.union_union_union_comm

theorem inter_inter_inter_comm (s t u v : Finset α) : s ∩ t ∩ (u ∩ v) = s ∩ u ∩ (t ∩ v) :=
  inf_inf_inf_comm _ _ _ _
#align finset.inter_inter_inter_comm Finset.inter_inter_inter_comm

theorem union_eq_empty_iff (A B : Finset α) : A ∪ B = ∅ ↔ A = ∅ ∧ B = ∅ :=
  sup_eq_bot_iff
#align finset.union_eq_empty_iff Finset.union_eq_empty_iff

theorem union_subset_iff : s ∪ t ⊆ u ↔ s ⊆ u ∧ t ⊆ u :=
  (sup_le_iff : s ⊔ t ≤ u ↔ s ≤ u ∧ t ≤ u)
#align finset.union_subset_iff Finset.union_subset_iff

theorem subset_inter_iff : s ⊆ t ∩ u ↔ s ⊆ t ∧ s ⊆ u :=
  (le_inf_iff : s ≤ t ⊓ u ↔ s ≤ t ∧ s ≤ u)
#align finset.subset_inter_iff Finset.subset_inter_iff

@[simp]
theorem inter_eq_left_iff_subset (s t : Finset α) : s ∩ t = s ↔ s ⊆ t :=
  inf_eq_left
#align finset.inter_eq_left_iff_subset Finset.inter_eq_left_iff_subset

@[simp]
theorem inter_eq_right_iff_subset (s t : Finset α) : t ∩ s = s ↔ s ⊆ t :=
  inf_eq_right
#align finset.inter_eq_right_iff_subset Finset.inter_eq_right_iff_subset

theorem inter_congr_left (ht : s ∩ u ⊆ t) (hu : s ∩ t ⊆ u) : s ∩ t = s ∩ u :=
  inf_congr_left ht hu
#align finset.inter_congr_left Finset.inter_congr_left

theorem inter_congr_right (hs : t ∩ u ⊆ s) (ht : s ∩ u ⊆ t) : s ∩ u = t ∩ u :=
  inf_congr_right hs ht
#align finset.inter_congr_right Finset.inter_congr_right

theorem inter_eq_inter_iff_left : s ∩ t = s ∩ u ↔ s ∩ u ⊆ t ∧ s ∩ t ⊆ u :=
  inf_eq_inf_iff_left
#align finset.inter_eq_inter_iff_left Finset.inter_eq_inter_iff_left

theorem inter_eq_inter_iff_right : s ∩ u = t ∩ u ↔ t ∩ u ⊆ s ∧ s ∩ u ⊆ t :=
  inf_eq_inf_iff_right
#align finset.inter_eq_inter_iff_right Finset.inter_eq_inter_iff_right

theorem ite_subset_union (s s' : Finset α) (P : Prop) [Decidable P] : ite P s s' ⊆ s ∪ s' :=
  ite_le_sup s s' P
#align finset.ite_subset_union Finset.ite_subset_union

theorem inter_subset_ite (s s' : Finset α) (P : Prop) [Decidable P] : s ∩ s' ⊆ ite P s s' :=
  inf_le_ite s s' P
#align finset.inter_subset_ite Finset.inter_subset_ite

theorem not_disjoint_iff_nonempty_inter : ¬Disjoint s t ↔ (s ∩ t).Nonempty :=
  not_disjoint_iff.trans <| by simp [Finset.Nonempty]
                               -- 🎉 no goals
#align finset.not_disjoint_iff_nonempty_inter Finset.not_disjoint_iff_nonempty_inter

alias ⟨_, Nonempty.not_disjoint⟩ := not_disjoint_iff_nonempty_inter
#align finset.nonempty.not_disjoint Finset.Nonempty.not_disjoint

theorem disjoint_or_nonempty_inter (s t : Finset α) : Disjoint s t ∨ (s ∩ t).Nonempty := by
  rw [← not_disjoint_iff_nonempty_inter]
  -- ⊢ _root_.Disjoint s t ∨ ¬_root_.Disjoint s t
  exact em _
  -- 🎉 no goals
#align finset.disjoint_or_nonempty_inter Finset.disjoint_or_nonempty_inter

end Lattice

instance isDirected_le : IsDirected (Finset α) (· ≤ ·) := by classical infer_instance
                                                             -- 🎉 no goals
instance isDirected_subset : IsDirected (Finset α) (· ⊆ ·) := isDirected_le

/-! ### erase -/

section Erase

variable [DecidableEq α] {s t u v : Finset α} {a b : α}

/-- `erase s a` is the set `s - {a}`, that is, the elements of `s` which are
  not equal to `a`. -/
def erase (s : Finset α) (a : α) : Finset α :=
  ⟨_, s.2.erase a⟩
#align finset.erase Finset.erase

@[simp]
theorem erase_val (s : Finset α) (a : α) : (erase s a).1 = s.1.erase a :=
  rfl
#align finset.erase_val Finset.erase_val

@[simp]
theorem mem_erase {a b : α} {s : Finset α} : a ∈ erase s b ↔ a ≠ b ∧ a ∈ s :=
  s.2.mem_erase_iff
#align finset.mem_erase Finset.mem_erase

theorem not_mem_erase (a : α) (s : Finset α) : a ∉ erase s a :=
  s.2.not_mem_erase
#align finset.not_mem_erase Finset.not_mem_erase

-- While this can be solved by `simp`, this lemma is eligible for `dsimp`
@[nolint simpNF, simp]
theorem erase_empty (a : α) : erase ∅ a = ∅ :=
  rfl
#align finset.erase_empty Finset.erase_empty

@[simp]
theorem erase_singleton (a : α) : ({a} : Finset α).erase a = ∅ := by
  ext x
  -- ⊢ x ∈ erase {a} a ↔ x ∈ ∅
  simp
  -- 🎉 no goals
#align finset.erase_singleton Finset.erase_singleton

theorem ne_of_mem_erase : b ∈ erase s a → b ≠ a := fun h => (mem_erase.1 h).1
#align finset.ne_of_mem_erase Finset.ne_of_mem_erase

theorem mem_of_mem_erase : b ∈ erase s a → b ∈ s :=
  Multiset.mem_of_mem_erase
#align finset.mem_of_mem_erase Finset.mem_of_mem_erase

theorem mem_erase_of_ne_of_mem : a ≠ b → a ∈ s → a ∈ erase s b := by
  simp only [mem_erase]; exact And.intro
  -- ⊢ a ≠ b → a ∈ s → a ≠ b ∧ a ∈ s
                         -- 🎉 no goals
#align finset.mem_erase_of_ne_of_mem Finset.mem_erase_of_ne_of_mem

/-- An element of `s` that is not an element of `erase s a` must be`a`. -/
theorem eq_of_mem_of_not_mem_erase (hs : b ∈ s) (hsa : b ∉ s.erase a) : b = a := by
  rw [mem_erase, not_and] at hsa
  -- ⊢ b = a
  exact not_imp_not.mp hsa hs
  -- 🎉 no goals
#align finset.eq_of_mem_of_not_mem_erase Finset.eq_of_mem_of_not_mem_erase

@[simp]
theorem erase_eq_of_not_mem {a : α} {s : Finset α} (h : a ∉ s) : erase s a = s :=
  eq_of_veq <| erase_of_not_mem h
#align finset.erase_eq_of_not_mem Finset.erase_eq_of_not_mem

@[simp]
theorem erase_eq_self : s.erase a = s ↔ a ∉ s :=
  ⟨fun h => h ▸ not_mem_erase _ _, erase_eq_of_not_mem⟩
#align finset.erase_eq_self Finset.erase_eq_self

@[simp]
theorem erase_insert_eq_erase (s : Finset α) (a : α) : (insert a s).erase a = s.erase a :=
  ext fun x => by
    simp (config := { contextual := true }) only [mem_erase, mem_insert, and_congr_right_iff,
      false_or_iff, iff_self_iff, imp_true_iff]
#align finset.erase_insert_eq_erase Finset.erase_insert_eq_erase

theorem erase_insert {a : α} {s : Finset α} (h : a ∉ s) : erase (insert a s) a = s := by
  rw [erase_insert_eq_erase, erase_eq_of_not_mem h]
  -- 🎉 no goals
#align finset.erase_insert Finset.erase_insert

theorem erase_insert_of_ne {a b : α} {s : Finset α} (h : a ≠ b) :
    erase (insert a s) b = insert a (erase s b) :=
  ext fun x => by
    have : x ≠ b ∧ x = a ↔ x = a := and_iff_right_of_imp fun hx => hx.symm ▸ h
    -- ⊢ x ∈ erase (insert a s) b ↔ x ∈ insert a (erase s b)
    simp only [mem_erase, mem_insert, and_or_left, this]
    -- 🎉 no goals
#align finset.erase_insert_of_ne Finset.erase_insert_of_ne

theorem erase_cons_of_ne {a b : α} {s : Finset α} (ha : a ∉ s) (hb : a ≠ b) :
    erase (cons a s ha) b = cons a (erase s b) fun h => ha <| erase_subset _ _ h := by
  simp only [cons_eq_insert, erase_insert_of_ne hb]
  -- 🎉 no goals
#align finset.erase_cons_of_ne Finset.erase_cons_of_ne

theorem insert_erase {a : α} {s : Finset α} (h : a ∈ s) : insert a (erase s a) = s :=
  ext fun x => by
    simp only [mem_insert, mem_erase, or_and_left, dec_em, true_and_iff]
    -- ⊢ x = a ∨ x ∈ s ↔ x ∈ s
    apply or_iff_right_of_imp
    -- ⊢ x = a → x ∈ s
    rintro rfl
    -- ⊢ x ∈ s
    exact h
    -- 🎉 no goals
#align finset.insert_erase Finset.insert_erase

theorem erase_subset_erase (a : α) {s t : Finset α} (h : s ⊆ t) : erase s a ⊆ erase t a :=
  val_le_iff.1 <| erase_le_erase _ <| val_le_iff.2 h
#align finset.erase_subset_erase Finset.erase_subset_erase

theorem erase_subset (a : α) (s : Finset α) : erase s a ⊆ s :=
  Multiset.erase_subset _ _
#align finset.erase_subset Finset.erase_subset

theorem subset_erase {a : α} {s t : Finset α} : s ⊆ t.erase a ↔ s ⊆ t ∧ a ∉ s :=
  ⟨fun h => ⟨h.trans (erase_subset _ _), fun ha => not_mem_erase _ _ (h ha)⟩,
   fun h _b hb => mem_erase.2 ⟨ne_of_mem_of_not_mem hb h.2, h.1 hb⟩⟩
#align finset.subset_erase Finset.subset_erase

@[simp, norm_cast]
theorem coe_erase (a : α) (s : Finset α) : ↑(erase s a) = (s \ {a} : Set α) :=
  Set.ext fun _ => mem_erase.trans <| by rw [and_comm, Set.mem_diff, Set.mem_singleton_iff, mem_coe]
                                         -- 🎉 no goals
#align finset.coe_erase Finset.coe_erase

theorem erase_ssubset {a : α} {s : Finset α} (h : a ∈ s) : s.erase a ⊂ s :=
  calc
    s.erase a ⊂ insert a (s.erase a) := ssubset_insert <| not_mem_erase _ _
    _ = _ := insert_erase h
#align finset.erase_ssubset Finset.erase_ssubset

theorem ssubset_iff_exists_subset_erase {s t : Finset α} : s ⊂ t ↔ ∃ a ∈ t, s ⊆ t.erase a := by
  refine' ⟨fun h => _, fun ⟨a, ha, h⟩ => ssubset_of_subset_of_ssubset h <| erase_ssubset ha⟩
  -- ⊢ ∃ a, a ∈ t ∧ s ⊆ erase t a
  obtain ⟨a, ht, hs⟩ := not_subset.1 h.2
  -- ⊢ ∃ a, a ∈ t ∧ s ⊆ erase t a
  exact ⟨a, ht, subset_erase.2 ⟨h.1, hs⟩⟩
  -- 🎉 no goals
#align finset.ssubset_iff_exists_subset_erase Finset.ssubset_iff_exists_subset_erase

theorem erase_ssubset_insert (s : Finset α) (a : α) : s.erase a ⊂ insert a s :=
  ssubset_iff_exists_subset_erase.2
    ⟨a, mem_insert_self _ _, erase_subset_erase _ <| subset_insert _ _⟩
#align finset.erase_ssubset_insert Finset.erase_ssubset_insert

theorem erase_ne_self : s.erase a ≠ s ↔ a ∈ s :=
  erase_eq_self.not_left
#align finset.erase_ne_self Finset.erase_ne_self

theorem erase_cons {s : Finset α} {a : α} (h : a ∉ s) : (s.cons a h).erase a = s := by
  rw [cons_eq_insert, erase_insert_eq_erase, erase_eq_of_not_mem h]
  -- 🎉 no goals
#align finset.erase_cons Finset.erase_cons

theorem erase_idem {a : α} {s : Finset α} : erase (erase s a) a = erase s a := by simp
                                                                                  -- 🎉 no goals
#align finset.erase_idem Finset.erase_idem

theorem erase_right_comm {a b : α} {s : Finset α} : erase (erase s a) b = erase (erase s b) a := by
  ext x
  -- ⊢ x ∈ erase (erase s a) b ↔ x ∈ erase (erase s b) a
  simp only [mem_erase, ← and_assoc]
  -- ⊢ (x ≠ b ∧ x ≠ a) ∧ x ∈ s ↔ (x ≠ a ∧ x ≠ b) ∧ x ∈ s
  rw [@and_comm (x ≠ a)]
  -- 🎉 no goals
#align finset.erase_right_comm Finset.erase_right_comm

theorem subset_insert_iff {a : α} {s t : Finset α} : s ⊆ insert a t ↔ erase s a ⊆ t := by
  simp only [subset_iff, or_iff_not_imp_left, mem_erase, mem_insert, and_imp]
  -- ⊢ (∀ ⦃x : α⦄, x ∈ s → ¬x = a → x ∈ t) ↔ ∀ ⦃x : α⦄, x ≠ a → x ∈ s → x ∈ t
  exact forall_congr' fun x => forall_swap
  -- 🎉 no goals
#align finset.subset_insert_iff Finset.subset_insert_iff

theorem erase_insert_subset (a : α) (s : Finset α) : erase (insert a s) a ⊆ s :=
  subset_insert_iff.1 <| Subset.rfl
#align finset.erase_insert_subset Finset.erase_insert_subset

theorem insert_erase_subset (a : α) (s : Finset α) : s ⊆ insert a (erase s a) :=
  subset_insert_iff.2 <| Subset.rfl
#align finset.insert_erase_subset Finset.insert_erase_subset

theorem subset_insert_iff_of_not_mem (h : a ∉ s) : s ⊆ insert a t ↔ s ⊆ t := by
  rw [subset_insert_iff, erase_eq_of_not_mem h]
  -- 🎉 no goals
#align finset.subset_insert_iff_of_not_mem Finset.subset_insert_iff_of_not_mem

theorem erase_subset_iff_of_mem (h : a ∈ t) : s.erase a ⊆ t ↔ s ⊆ t := by
  rw [← subset_insert_iff, insert_eq_of_mem h]
  -- 🎉 no goals
#align finset.erase_subset_iff_of_mem Finset.erase_subset_iff_of_mem

theorem erase_inj {x y : α} (s : Finset α) (hx : x ∈ s) : s.erase x = s.erase y ↔ x = y := by
  refine ⟨fun h => eq_of_mem_of_not_mem_erase hx ?_, congr_arg _⟩
  -- ⊢ ¬x ∈ erase s y
  rw [← h]
  -- ⊢ ¬x ∈ erase s x
  simp
  -- 🎉 no goals
#align finset.erase_inj Finset.erase_inj

theorem erase_injOn (s : Finset α) : Set.InjOn s.erase s := fun _ _ _ _ => (erase_inj s ‹_›).mp
#align finset.erase_inj_on Finset.erase_injOn

theorem erase_injOn' (a : α) : { s : Finset α | a ∈ s }.InjOn fun s => erase s a :=
  fun s hs t ht (h : s.erase a = _) => by rw [← insert_erase hs, ← insert_erase ht, h]
                                          -- 🎉 no goals
#align finset.erase_inj_on' Finset.erase_injOn'

end Erase

/-! ### sdiff -/


section Sdiff

variable [DecidableEq α] {s t u v : Finset α} {a b : α}

/-- `s \ t` is the set consisting of the elements of `s` that are not in `t`. -/
instance : SDiff (Finset α) :=
  ⟨fun s₁ s₂ => ⟨s₁.1 - s₂.1, nodup_of_le tsub_le_self s₁.2⟩⟩

@[simp]
theorem sdiff_val (s₁ s₂ : Finset α) : (s₁ \ s₂).val = s₁.val - s₂.val :=
  rfl
#align finset.sdiff_val Finset.sdiff_val

@[simp]
theorem mem_sdiff : a ∈ s \ t ↔ a ∈ s ∧ a ∉ t :=
  mem_sub_of_nodup s.2
#align finset.mem_sdiff Finset.mem_sdiff

@[simp]
theorem inter_sdiff_self (s₁ s₂ : Finset α) : s₁ ∩ (s₂ \ s₁) = ∅ :=
  eq_empty_of_forall_not_mem <| by
    simp only [mem_inter, mem_sdiff]; rintro x ⟨h, _, hn⟩; exact hn h
    -- ⊢ ∀ (x : α), ¬(x ∈ s₁ ∧ x ∈ s₂ ∧ ¬x ∈ s₁)
                                      -- ⊢ False
                                                           -- 🎉 no goals
#align finset.inter_sdiff_self Finset.inter_sdiff_self

instance : GeneralizedBooleanAlgebra (Finset α) :=
  { sup_inf_sdiff := fun x y => by
      simp only [ext_iff, mem_union, mem_sdiff, inf_eq_inter, sup_eq_union, mem_inter, ←and_or_left,
        em, and_true, implies_true]
    inf_inf_sdiff := fun x y => by
      simp only [ext_iff, inter_sdiff_self, inter_empty, inter_assoc, false_iff_iff, inf_eq_inter,
        not_mem_empty, bot_eq_empty, not_false_iff, implies_true] }

theorem not_mem_sdiff_of_mem_right (h : a ∈ t) : a ∉ s \ t := by
  simp only [mem_sdiff, h, not_true, not_false_iff, and_false_iff]
  -- 🎉 no goals
#align finset.not_mem_sdiff_of_mem_right Finset.not_mem_sdiff_of_mem_right

theorem not_mem_sdiff_of_not_mem_left (h : a ∉ s) : a ∉ s \ t := by simp [h]
                                                                    -- 🎉 no goals
#align finset.not_mem_sdiff_of_not_mem_left Finset.not_mem_sdiff_of_not_mem_left

theorem union_sdiff_of_subset (h : s ⊆ t) : s ∪ t \ s = t :=
  sup_sdiff_cancel_right h
#align finset.union_sdiff_of_subset Finset.union_sdiff_of_subset

theorem sdiff_union_of_subset {s₁ s₂ : Finset α} (h : s₁ ⊆ s₂) : s₂ \ s₁ ∪ s₁ = s₂ :=
  (union_comm _ _).trans (union_sdiff_of_subset h)
#align finset.sdiff_union_of_subset Finset.sdiff_union_of_subset

theorem inter_sdiff (s t u : Finset α) : s ∩ (t \ u) = (s ∩ t) \ u := by
  ext x
  -- ⊢ x ∈ s ∩ (t \ u) ↔ x ∈ (s ∩ t) \ u
  simp [and_assoc]
  -- 🎉 no goals
#align finset.inter_sdiff Finset.inter_sdiff

@[simp]
theorem sdiff_inter_self (s₁ s₂ : Finset α) : s₂ \ s₁ ∩ s₁ = ∅ :=
  inf_sdiff_self_left
#align finset.sdiff_inter_self Finset.sdiff_inter_self

-- Porting note: @[simp] can prove this
theorem sdiff_self (s₁ : Finset α) : s₁ \ s₁ = ∅ :=
  _root_.sdiff_self
#align finset.sdiff_self Finset.sdiff_self

theorem sdiff_inter_distrib_right (s t u : Finset α) : s \ (t ∩ u) = s \ t ∪ s \ u :=
  sdiff_inf
#align finset.sdiff_inter_distrib_right Finset.sdiff_inter_distrib_right

@[simp]
theorem sdiff_inter_self_left (s t : Finset α) : s \ (s ∩ t) = s \ t :=
  sdiff_inf_self_left _ _
#align finset.sdiff_inter_self_left Finset.sdiff_inter_self_left

@[simp]
theorem sdiff_inter_self_right (s t : Finset α) : s \ (t ∩ s) = s \ t :=
  sdiff_inf_self_right _ _
#align finset.sdiff_inter_self_right Finset.sdiff_inter_self_right

@[simp]
theorem sdiff_empty : s \ ∅ = s :=
  sdiff_bot
#align finset.sdiff_empty Finset.sdiff_empty

@[mono]
theorem sdiff_subset_sdiff (hst : s ⊆ t) (hvu : v ⊆ u) : s \ u ⊆ t \ v :=
  sdiff_le_sdiff (le_iff_subset.mpr hst) (le_iff_subset.mpr hvu)
#align finset.sdiff_subset_sdiff Finset.sdiff_subset_sdiff

@[simp, norm_cast]
theorem coe_sdiff (s₁ s₂ : Finset α) : ↑(s₁ \ s₂) = (s₁ \ s₂ : Set α) :=
  Set.ext fun _ => mem_sdiff
#align finset.coe_sdiff Finset.coe_sdiff

@[simp]
theorem union_sdiff_self_eq_union : s ∪ t \ s = s ∪ t :=
  sup_sdiff_self_right _ _
#align finset.union_sdiff_self_eq_union Finset.union_sdiff_self_eq_union

@[simp]
theorem sdiff_union_self_eq_union : s \ t ∪ t = s ∪ t :=
  sup_sdiff_self_left _ _
#align finset.sdiff_union_self_eq_union Finset.sdiff_union_self_eq_union

theorem union_sdiff_left (s t : Finset α) : (s ∪ t) \ s = t \ s :=
  sup_sdiff_left_self
#align finset.union_sdiff_left Finset.union_sdiff_left

theorem union_sdiff_right (s t : Finset α) : (s ∪ t) \ t = s \ t :=
  sup_sdiff_right_self
#align finset.union_sdiff_right Finset.union_sdiff_right

theorem union_sdiff_cancel_left (h : Disjoint s t) : (s ∪ t) \ s = t :=
  h.sup_sdiff_cancel_left
#align finset.union_sdiff_cancel_left Finset.union_sdiff_cancel_left

theorem union_sdiff_cancel_right (h : Disjoint s t) : (s ∪ t) \ t = s :=
  h.sup_sdiff_cancel_right
#align finset.union_sdiff_cancel_right Finset.union_sdiff_cancel_right

theorem union_sdiff_symm : s ∪ t \ s = t ∪ s \ t := by simp [union_comm]
                                                       -- 🎉 no goals
#align finset.union_sdiff_symm Finset.union_sdiff_symm

theorem sdiff_union_inter (s t : Finset α) : s \ t ∪ s ∩ t = s :=
  sup_sdiff_inf _ _
#align finset.sdiff_union_inter Finset.sdiff_union_inter

-- Porting note: @[simp] can prove this
theorem sdiff_idem (s t : Finset α) : (s \ t) \ t = s \ t :=
  _root_.sdiff_idem
#align finset.sdiff_idem Finset.sdiff_idem

theorem subset_sdiff : s ⊆ t \ u ↔ s ⊆ t ∧ Disjoint s u :=
  le_iff_subset.symm.trans le_sdiff
#align finset.subset_sdiff Finset.subset_sdiff

@[simp]
theorem sdiff_eq_empty_iff_subset : s \ t = ∅ ↔ s ⊆ t :=
  sdiff_eq_bot_iff
#align finset.sdiff_eq_empty_iff_subset Finset.sdiff_eq_empty_iff_subset

theorem sdiff_nonempty : (s \ t).Nonempty ↔ ¬s ⊆ t :=
  nonempty_iff_ne_empty.trans sdiff_eq_empty_iff_subset.not
#align finset.sdiff_nonempty Finset.sdiff_nonempty

@[simp]
theorem empty_sdiff (s : Finset α) : ∅ \ s = ∅ :=
  bot_sdiff
#align finset.empty_sdiff Finset.empty_sdiff

theorem insert_sdiff_of_not_mem (s : Finset α) {t : Finset α} {x : α} (h : x ∉ t) :
    insert x s \ t = insert x (s \ t) := by
  rw [← coe_inj, coe_insert, coe_sdiff, coe_sdiff, coe_insert]
  -- ⊢ insert x ↑s \ ↑t = insert x (↑s \ ↑t)
  exact Set.insert_diff_of_not_mem _ h
  -- 🎉 no goals
#align finset.insert_sdiff_of_not_mem Finset.insert_sdiff_of_not_mem

theorem insert_sdiff_of_mem (s : Finset α) {x : α} (h : x ∈ t) : insert x s \ t = s \ t := by
  rw [← coe_inj, coe_sdiff, coe_sdiff, coe_insert]
  -- ⊢ insert x ↑s \ ↑t = ↑s \ ↑t
  exact Set.insert_diff_of_mem _ h
  -- 🎉 no goals
#align finset.insert_sdiff_of_mem Finset.insert_sdiff_of_mem

@[simp]
theorem insert_sdiff_insert (s t : Finset α) (x : α) : insert x s \ insert x t = s \ insert x t :=
  insert_sdiff_of_mem _ (mem_insert_self _ _)
#align finset.insert_sdiff_insert Finset.insert_sdiff_insert

theorem sdiff_insert_of_not_mem {x : α} (h : x ∉ s) (t : Finset α) : s \ insert x t = s \ t := by
  refine' Subset.antisymm (sdiff_subset_sdiff (Subset.refl _) (subset_insert _ _)) fun y hy => _
  -- ⊢ y ∈ s \ insert x t
  simp only [mem_sdiff, mem_insert, not_or] at hy ⊢
  -- ⊢ y ∈ s ∧ ¬y = x ∧ ¬y ∈ t
  exact ⟨hy.1, fun hxy => h <| hxy ▸ hy.1, hy.2⟩
  -- 🎉 no goals
#align finset.sdiff_insert_of_not_mem Finset.sdiff_insert_of_not_mem

@[simp]
theorem sdiff_subset (s t : Finset α) : s \ t ⊆ s :=
  le_iff_subset.mp sdiff_le
#align finset.sdiff_subset Finset.sdiff_subset

theorem sdiff_ssubset (h : t ⊆ s) (ht : t.Nonempty) : s \ t ⊂ s :=
  sdiff_lt (le_iff_subset.mpr h) ht.ne_empty
#align finset.sdiff_ssubset Finset.sdiff_ssubset

theorem union_sdiff_distrib (s₁ s₂ t : Finset α) : (s₁ ∪ s₂) \ t = s₁ \ t ∪ s₂ \ t :=
  sup_sdiff
#align finset.union_sdiff_distrib Finset.union_sdiff_distrib

theorem sdiff_union_distrib (s t₁ t₂ : Finset α) : s \ (t₁ ∪ t₂) = s \ t₁ ∩ (s \ t₂) :=
  sdiff_sup
#align finset.sdiff_union_distrib Finset.sdiff_union_distrib

theorem union_sdiff_self (s t : Finset α) : (s ∪ t) \ t = s \ t :=
  sup_sdiff_right_self
#align finset.union_sdiff_self Finset.union_sdiff_self

-- TODO: Do we want to delete this lemma and `Finset.disjUnion_singleton`,
-- or instead add `Finset.union_singleton`/`Finset.singleton_union`?
theorem sdiff_singleton_eq_erase (a : α) (s : Finset α) : s \ singleton a = erase s a := by
  ext
  -- ⊢ a✝ ∈ s \ {a} ↔ a✝ ∈ erase s a
  rw [mem_erase, mem_sdiff, mem_singleton, and_comm]
  -- 🎉 no goals
#align finset.sdiff_singleton_eq_erase Finset.sdiff_singleton_eq_erase

-- This lemma matches `Finset.insert_eq` in functionality.
theorem erase_eq (s : Finset α) (a : α) : s.erase a = s \ {a} :=
  (sdiff_singleton_eq_erase _ _).symm
#align finset.erase_eq Finset.erase_eq

theorem disjoint_erase_comm : Disjoint (s.erase a) t ↔ Disjoint s (t.erase a) := by
  simp_rw [erase_eq, disjoint_sdiff_comm]
  -- 🎉 no goals
#align finset.disjoint_erase_comm Finset.disjoint_erase_comm

theorem disjoint_of_erase_left (ha : a ∉ t) (hst : Disjoint (s.erase a) t) : Disjoint s t := by
  rw [← erase_insert ha, ← disjoint_erase_comm, disjoint_insert_right]
  -- ⊢ ¬a ∈ erase s a ∧ _root_.Disjoint (erase s a) t
  exact ⟨not_mem_erase _ _, hst⟩
  -- 🎉 no goals
#align finset.disjoint_of_erase_left Finset.disjoint_of_erase_left

theorem disjoint_of_erase_right (ha : a ∉ s) (hst : Disjoint s (t.erase a)) : Disjoint s t := by
  rw [← erase_insert ha, disjoint_erase_comm, disjoint_insert_left]
  -- ⊢ ¬a ∈ erase t a ∧ _root_.Disjoint s (erase t a)
  exact ⟨not_mem_erase _ _, hst⟩
  -- 🎉 no goals
#align finset.disjoint_of_erase_right Finset.disjoint_of_erase_right

theorem inter_erase (a : α) (s t : Finset α) : s ∩ t.erase a = (s ∩ t).erase a := by
  simp only [erase_eq, inter_sdiff]
  -- 🎉 no goals
#align finset.inter_erase Finset.inter_erase

@[simp]
theorem erase_inter (a : α) (s t : Finset α) : s.erase a ∩ t = (s ∩ t).erase a := by
  simpa only [inter_comm t] using inter_erase a t s
  -- 🎉 no goals
#align finset.erase_inter Finset.erase_inter

theorem erase_sdiff_comm (s t : Finset α) (a : α) : s.erase a \ t = (s \ t).erase a := by
  simp_rw [erase_eq, sdiff_right_comm]
  -- 🎉 no goals
#align finset.erase_sdiff_comm Finset.erase_sdiff_comm

theorem insert_union_comm (s t : Finset α) (a : α) : insert a s ∪ t = s ∪ insert a t := by
  rw [insert_union, union_insert]
  -- 🎉 no goals
#align finset.insert_union_comm Finset.insert_union_comm

theorem erase_inter_comm (s t : Finset α) (a : α) : s.erase a ∩ t = s ∩ t.erase a := by
  rw [erase_inter, inter_erase]
  -- 🎉 no goals
#align finset.erase_inter_comm Finset.erase_inter_comm

theorem erase_union_distrib (s t : Finset α) (a : α) : (s ∪ t).erase a = s.erase a ∪ t.erase a :=
  by simp_rw [erase_eq, union_sdiff_distrib]
     -- 🎉 no goals
#align finset.erase_union_distrib Finset.erase_union_distrib

theorem insert_inter_distrib (s t : Finset α) (a : α) :
    insert a (s ∩ t) = insert a s ∩ insert a t := by simp_rw [insert_eq, union_distrib_left]
                                                     -- 🎉 no goals
#align finset.insert_inter_distrib Finset.insert_inter_distrib

theorem erase_sdiff_distrib (s t : Finset α) (a : α) : (s \ t).erase a = s.erase a \ t.erase a :=
  by simp_rw [erase_eq, sdiff_sdiff, sup_sdiff_eq_sup le_rfl, sup_comm]
     -- 🎉 no goals
#align finset.erase_sdiff_distrib Finset.erase_sdiff_distrib

theorem erase_union_of_mem (ha : a ∈ t) (s : Finset α) : s.erase a ∪ t = s ∪ t := by
  rw [← insert_erase (mem_union_right s ha), erase_union_distrib, ← union_insert, insert_erase ha]
  -- 🎉 no goals
#align finset.erase_union_of_mem Finset.erase_union_of_mem

theorem union_erase_of_mem (ha : a ∈ s) (t : Finset α) : s ∪ t.erase a = s ∪ t := by
  rw [← insert_erase (mem_union_left t ha), erase_union_distrib, ← insert_union, insert_erase ha]
  -- 🎉 no goals
#align finset.union_erase_of_mem Finset.union_erase_of_mem

@[simp]
theorem sdiff_singleton_eq_self (ha : a ∉ s) : s \ {a} = s :=
  sdiff_eq_self_iff_disjoint.2 <| by simp [ha]
                                     -- 🎉 no goals
#align finset.sdiff_singleton_eq_self Finset.sdiff_singleton_eq_self

theorem sdiff_sdiff_left' (s t u : Finset α) : (s \ t) \ u = s \ t ∩ (s \ u) :=
  _root_.sdiff_sdiff_left'
#align finset.sdiff_sdiff_left' Finset.sdiff_sdiff_left'

theorem sdiff_union_sdiff_cancel (hts : t ⊆ s) (hut : u ⊆ t) : s \ t ∪ t \ u = s \ u :=
  sdiff_sup_sdiff_cancel hts hut
#align finset.sdiff_union_sdiff_cancel Finset.sdiff_union_sdiff_cancel

theorem sdiff_union_erase_cancel (hts : t ⊆ s) (ha : a ∈ t) : s \ t ∪ t.erase a = s.erase a := by
  simp_rw [erase_eq, sdiff_union_sdiff_cancel hts (singleton_subset_iff.2 ha)]
  -- 🎉 no goals
#align finset.sdiff_union_erase_cancel Finset.sdiff_union_erase_cancel

theorem sdiff_sdiff_eq_sdiff_union (h : u ⊆ s) : s \ (t \ u) = s \ t ∪ u :=
  sdiff_sdiff_eq_sdiff_sup h
#align finset.sdiff_sdiff_eq_sdiff_union Finset.sdiff_sdiff_eq_sdiff_union

theorem sdiff_insert (s t : Finset α) (x : α) : s \ insert x t = (s \ t).erase x := by
  simp_rw [← sdiff_singleton_eq_erase, insert_eq, sdiff_sdiff_left', sdiff_union_distrib,
    inter_comm]
#align finset.sdiff_insert Finset.sdiff_insert

theorem sdiff_insert_insert_of_mem_of_not_mem {s t : Finset α} {x : α} (hxs : x ∈ s) (hxt : x ∉ t) :
    insert x (s \ insert x t) = s \ t := by
  rw [sdiff_insert, insert_erase (mem_sdiff.mpr ⟨hxs, hxt⟩)]
  -- 🎉 no goals
#align finset.sdiff_insert_insert_of_mem_of_not_mem Finset.sdiff_insert_insert_of_mem_of_not_mem

theorem sdiff_erase (h : a ∈ s) : s \ t.erase a = insert a (s \ t) := by
  rw [← sdiff_singleton_eq_erase, sdiff_sdiff_eq_sdiff_union (singleton_subset_iff.2 h), insert_eq,
    union_comm]
#align finset.sdiff_erase Finset.sdiff_erase

theorem sdiff_erase_self (ha : a ∈ s) : s \ s.erase a = {a} := by
  rw [sdiff_erase ha, sdiff_self, insert_emptyc_eq]
  -- 🎉 no goals
#align finset.sdiff_erase_self Finset.sdiff_erase_self

theorem sdiff_sdiff_self_left (s t : Finset α) : s \ (s \ t) = s ∩ t :=
  sdiff_sdiff_right_self
#align finset.sdiff_sdiff_self_left Finset.sdiff_sdiff_self_left

theorem sdiff_sdiff_eq_self (h : t ⊆ s) : s \ (s \ t) = t :=
  _root_.sdiff_sdiff_eq_self h
#align finset.sdiff_sdiff_eq_self Finset.sdiff_sdiff_eq_self

theorem sdiff_eq_sdiff_iff_inter_eq_inter {s t₁ t₂ : Finset α} :
    s \ t₁ = s \ t₂ ↔ s ∩ t₁ = s ∩ t₂ :=
  sdiff_eq_sdiff_iff_inf_eq_inf
#align finset.sdiff_eq_sdiff_iff_inter_eq_inter Finset.sdiff_eq_sdiff_iff_inter_eq_inter

theorem union_eq_sdiff_union_sdiff_union_inter (s t : Finset α) : s ∪ t = s \ t ∪ t \ s ∪ s ∩ t :=
  sup_eq_sdiff_sup_sdiff_sup_inf
#align finset.union_eq_sdiff_union_sdiff_union_inter Finset.union_eq_sdiff_union_sdiff_union_inter

theorem erase_eq_empty_iff (s : Finset α) (a : α) : s.erase a = ∅ ↔ s = ∅ ∨ s = {a} := by
  rw [← sdiff_singleton_eq_erase, sdiff_eq_empty_iff_subset, subset_singleton_iff]
  -- 🎉 no goals
#align finset.erase_eq_empty_iff Finset.erase_eq_empty_iff

--TODO@Yaël: Kill lemmas duplicate with `BooleanAlgebra`
theorem sdiff_disjoint : Disjoint (t \ s) s :=
  disjoint_left.2 fun _a ha => (mem_sdiff.1 ha).2
#align finset.sdiff_disjoint Finset.sdiff_disjoint

theorem disjoint_sdiff : Disjoint s (t \ s) :=
  sdiff_disjoint.symm
#align finset.disjoint_sdiff Finset.disjoint_sdiff

theorem disjoint_sdiff_inter (s t : Finset α) : Disjoint (s \ t) (s ∩ t) :=
  disjoint_of_subset_right (inter_subset_right _ _) sdiff_disjoint
#align finset.disjoint_sdiff_inter Finset.disjoint_sdiff_inter

theorem sdiff_eq_self_iff_disjoint : s \ t = s ↔ Disjoint s t :=
  sdiff_eq_self_iff_disjoint'
#align finset.sdiff_eq_self_iff_disjoint Finset.sdiff_eq_self_iff_disjoint

theorem sdiff_eq_self_of_disjoint (h : Disjoint s t) : s \ t = s :=
  sdiff_eq_self_iff_disjoint.2 h
#align finset.sdiff_eq_self_of_disjoint Finset.sdiff_eq_self_of_disjoint

end Sdiff

/-! ### Symmetric difference -/


section SymmDiff

variable [DecidableEq α] {s t : Finset α} {a b : α}

theorem mem_symmDiff : a ∈ s ∆ t ↔ a ∈ s ∧ a ∉ t ∨ a ∈ t ∧ a ∉ s := by
  simp_rw [symmDiff, sup_eq_union, mem_union, mem_sdiff]
  -- 🎉 no goals
#align finset.mem_symm_diff Finset.mem_symmDiff

@[simp, norm_cast]
theorem coe_symmDiff : (↑(s ∆ t) : Set α) = (s : Set α) ∆ t :=
  Set.ext fun x => by simp [mem_symmDiff, Set.mem_symmDiff]
                      -- 🎉 no goals
#align finset.coe_symm_diff Finset.coe_symmDiff

end SymmDiff

/-! ### attach -/


/-- `attach s` takes the elements of `s` and forms a new set of elements of the subtype
`{x // x ∈ s}`. -/
def attach (s : Finset α) : Finset { x // x ∈ s } :=
  ⟨Multiset.attach s.1, nodup_attach.2 s.2⟩
#align finset.attach Finset.attach

theorem sizeOf_lt_sizeOf_of_mem [SizeOf α] {x : α} {s : Finset α} (hx : x ∈ s) :
    SizeOf.sizeOf x < SizeOf.sizeOf s := by
  cases s
  -- ⊢ sizeOf x < sizeOf { val := val✝, nodup := nodup✝ }
  dsimp [SizeOf.sizeOf, SizeOf.sizeOf, Multiset.sizeOf]
  -- ⊢ sizeOf x < 1 + Quot.liftOn val✝ (fun m => List._sizeOf_1 m) (_ : ∀ (x x_1 :  …
  rw [add_comm]
  -- ⊢ sizeOf x < Quot.liftOn val✝ (fun m => List._sizeOf_1 m) (_ : ∀ (x x_1 : List …
  refine' lt_trans _ (Nat.lt_succ_self _)
  -- ⊢ sizeOf x < Quot.liftOn val✝ (fun m => List._sizeOf_1 m) (_ : ∀ (x x_1 : List …
  exact Multiset.sizeOf_lt_sizeOf_of_mem hx
  -- 🎉 no goals
#align finset.sizeof_lt_sizeof_of_mem Finset.sizeOf_lt_sizeOf_of_mem

@[simp]
theorem attach_val (s : Finset α) : s.attach.1 = s.1.attach :=
  rfl
#align finset.attach_val Finset.attach_val

@[simp]
theorem mem_attach (s : Finset α) : ∀ x, x ∈ s.attach :=
  Multiset.mem_attach _
#align finset.mem_attach Finset.mem_attach

@[simp]
theorem attach_empty : attach (∅ : Finset α) = ∅ :=
  rfl
#align finset.attach_empty Finset.attach_empty

@[simp]
theorem attach_nonempty_iff (s : Finset α) : s.attach.Nonempty ↔ s.Nonempty := by
  simp [Finset.Nonempty]
  -- 🎉 no goals
#align finset.attach_nonempty_iff Finset.attach_nonempty_iff

@[simp]
theorem attach_eq_empty_iff (s : Finset α) : s.attach = ∅ ↔ s = ∅ := by
  simp [eq_empty_iff_forall_not_mem]
  -- 🎉 no goals
#align finset.attach_eq_empty_iff Finset.attach_eq_empty_iff

/-! ### piecewise -/


section Piecewise

/-- `s.piecewise f g` is the function equal to `f` on the finset `s`, and to `g` on its
complement. -/
def piecewise {α : Type*} {δ : α → Sort*} (s : Finset α) (f g : ∀ i, δ i)
    [∀ j, Decidable (j ∈ s)] : ∀ i, δ i := fun i => if i ∈ s then f i else g i
#align finset.piecewise Finset.piecewise

variable {δ : α → Sort*} (s : Finset α) (f g : ∀ i, δ i)

-- Porting note: @[simp] can prove this
theorem piecewise_insert_self [DecidableEq α] {j : α} [∀ i, Decidable (i ∈ insert j s)] :
    (insert j s).piecewise f g j = f j := by simp [piecewise]
                                             -- 🎉 no goals
#align finset.piecewise_insert_self Finset.piecewise_insert_self

@[simp]
theorem piecewise_empty [∀ i : α, Decidable (i ∈ (∅ : Finset α))] : piecewise ∅ f g = g := by
  ext i
  -- ⊢ piecewise ∅ f g i = g i
  simp [piecewise]
  -- 🎉 no goals
#align finset.piecewise_empty Finset.piecewise_empty

variable [∀ j, Decidable (j ∈ s)]

-- TODO: fix this in norm_cast
@[norm_cast move]
theorem piecewise_coe [∀ j, Decidable (j ∈ (s : Set α))] :
    (s : Set α).piecewise f g = s.piecewise f g := by
  ext
  -- ⊢ Set.piecewise (↑s) f g x✝ = piecewise s f g x✝
  congr
  -- 🎉 no goals
#align finset.piecewise_coe Finset.piecewise_coe

@[simp]
theorem piecewise_eq_of_mem {i : α} (hi : i ∈ s) : s.piecewise f g i = f i := by
  simp [piecewise, hi]
  -- 🎉 no goals
#align finset.piecewise_eq_of_mem Finset.piecewise_eq_of_mem

@[simp]
theorem piecewise_eq_of_not_mem {i : α} (hi : i ∉ s) : s.piecewise f g i = g i := by
  simp [piecewise, hi]
  -- 🎉 no goals
#align finset.piecewise_eq_of_not_mem Finset.piecewise_eq_of_not_mem

theorem piecewise_congr {f f' g g' : ∀ i, δ i} (hf : ∀ i ∈ s, f i = f' i)
    (hg : ∀ (i) (_ : i ∉ s), g i = g' i) : s.piecewise f g = s.piecewise f' g' :=
  funext fun i => if_ctx_congr Iff.rfl (hf i) (hg i)
#align finset.piecewise_congr Finset.piecewise_congr

@[simp]
theorem piecewise_insert_of_ne [DecidableEq α] {i j : α} [∀ i, Decidable (i ∈ insert j s)]
    (h : i ≠ j) : (insert j s).piecewise f g i = s.piecewise f g i := by simp [piecewise, h]
                                                                         -- 🎉 no goals
#align finset.piecewise_insert_of_ne Finset.piecewise_insert_of_ne

theorem piecewise_insert [DecidableEq α] (j : α) [∀ i, Decidable (i ∈ insert j s)] :
    (insert j s).piecewise f g = update (s.piecewise f g) j (f j) := by
  classical simp only [← piecewise_coe, coe_insert, ← Set.piecewise_insert]
  -- ⊢ Set.piecewise (↑(insert j s)) f g = Set.piecewise (insert j ↑s) f g
  ext
  -- ⊢ Set.piecewise (↑(insert j s)) f g x✝ = Set.piecewise (insert j ↑s) f g x✝
  congr
  -- ⊢ ↑(insert j s) = insert j ↑s
  simp
  -- 🎉 no goals
#align finset.piecewise_insert Finset.piecewise_insert

theorem piecewise_cases {i} (p : δ i → Prop) (hf : p (f i)) (hg : p (g i)) :
    p (s.piecewise f g i) := by
  by_cases hi : i ∈ s <;> simpa [hi]
  -- ⊢ p (piecewise s f g i)
                          -- 🎉 no goals
                          -- 🎉 no goals
#align finset.piecewise_cases Finset.piecewise_cases

theorem piecewise_mem_set_pi {δ : α → Type*} {t : Set α} {t' : ∀ i, Set (δ i)} {f g}
    (hf : f ∈ Set.pi t t') (hg : g ∈ Set.pi t t') : s.piecewise f g ∈ Set.pi t t' := by
  classical
    rw [← piecewise_coe]
    exact Set.piecewise_mem_pi (↑s) hf hg
#align finset.piecewise_mem_set_pi Finset.piecewise_mem_set_pi

theorem piecewise_singleton [DecidableEq α] (i : α) : piecewise {i} f g = update g i (f i) := by
  rw [← insert_emptyc_eq, piecewise_insert, piecewise_empty]
  -- 🎉 no goals
#align finset.piecewise_singleton Finset.piecewise_singleton

theorem piecewise_piecewise_of_subset_left {s t : Finset α} [∀ i, Decidable (i ∈ s)]
    [∀ i, Decidable (i ∈ t)] (h : s ⊆ t) (f₁ f₂ g : ∀ a, δ a) :
    s.piecewise (t.piecewise f₁ f₂) g = s.piecewise f₁ g :=
  s.piecewise_congr (fun _i hi => piecewise_eq_of_mem _ _ _ (h hi)) fun _ _ => rfl
#align finset.piecewise_piecewise_of_subset_left Finset.piecewise_piecewise_of_subset_left

@[simp]
theorem piecewise_idem_left (f₁ f₂ g : ∀ a, δ a) :
    s.piecewise (s.piecewise f₁ f₂) g = s.piecewise f₁ g :=
  piecewise_piecewise_of_subset_left (Subset.refl _) _ _ _
#align finset.piecewise_idem_left Finset.piecewise_idem_left

theorem piecewise_piecewise_of_subset_right {s t : Finset α} [∀ i, Decidable (i ∈ s)]
    [∀ i, Decidable (i ∈ t)] (h : t ⊆ s) (f g₁ g₂ : ∀ a, δ a) :
    s.piecewise f (t.piecewise g₁ g₂) = s.piecewise f g₂ :=
  s.piecewise_congr (fun _ _ => rfl) fun _i hi => t.piecewise_eq_of_not_mem _ _ (mt (@h _) hi)
#align finset.piecewise_piecewise_of_subset_right Finset.piecewise_piecewise_of_subset_right

@[simp]
theorem piecewise_idem_right (f g₁ g₂ : ∀ a, δ a) :
    s.piecewise f (s.piecewise g₁ g₂) = s.piecewise f g₂ :=
  piecewise_piecewise_of_subset_right (Subset.refl _) f g₁ g₂
#align finset.piecewise_idem_right Finset.piecewise_idem_right

theorem update_eq_piecewise {β : Type*} [DecidableEq α] (f : α → β) (i : α) (v : β) :
    update f i v = piecewise (singleton i) (fun _ => v) f :=
  (piecewise_singleton (fun _ => v) _ _).symm
#align finset.update_eq_piecewise Finset.update_eq_piecewise

theorem update_piecewise [DecidableEq α] (i : α) (v : δ i) :
    update (s.piecewise f g) i v = s.piecewise (update f i v) (update g i v) := by
  ext j
  -- ⊢ update (piecewise s f g) i v j = piecewise s (update f i v) (update g i v) j
  rcases em (j = i) with (rfl | hj) <;> by_cases hs : j ∈ s <;> simp [*]
  -- ⊢ update (piecewise s f g) j v j = piecewise s (update f j v) (update g j v) j
                                        -- ⊢ update (piecewise s f g) j v j = piecewise s (update f j v) (update g j v) j
                                        -- ⊢ update (piecewise s f g) i v j = piecewise s (update f i v) (update g i v) j
                                                                -- 🎉 no goals
                                                                -- 🎉 no goals
                                                                -- 🎉 no goals
                                                                -- 🎉 no goals
#align finset.update_piecewise Finset.update_piecewise

theorem update_piecewise_of_mem [DecidableEq α] {i : α} (hi : i ∈ s) (v : δ i) :
    update (s.piecewise f g) i v = s.piecewise (update f i v) g := by
  rw [update_piecewise]
  -- ⊢ piecewise s (update f i v) (update g i v) = piecewise s (update f i v) g
  refine' s.piecewise_congr (fun _ _ => rfl) fun j hj => update_noteq _ _ _
  -- ⊢ j ≠ i
  exact fun h => hj (h.symm ▸ hi)
  -- 🎉 no goals
#align finset.update_piecewise_of_mem Finset.update_piecewise_of_mem

theorem update_piecewise_of_not_mem [DecidableEq α] {i : α} (hi : i ∉ s) (v : δ i) :
    update (s.piecewise f g) i v = s.piecewise f (update g i v) := by
  rw [update_piecewise]
  -- ⊢ piecewise s (update f i v) (update g i v) = piecewise s f (update g i v)
  refine' s.piecewise_congr (fun j hj => update_noteq _ _ _) fun _ _ => rfl
  -- ⊢ j ≠ i
  exact fun h => hi (h ▸ hj)
  -- 🎉 no goals
#align finset.update_piecewise_of_not_mem Finset.update_piecewise_of_not_mem

theorem piecewise_le_of_le_of_le {δ : α → Type*} [∀ i, Preorder (δ i)] {f g h : ∀ i, δ i}
    (Hf : f ≤ h) (Hg : g ≤ h) : s.piecewise f g ≤ h := fun x =>
  piecewise_cases s f g (· ≤ h x) (Hf x) (Hg x)
#align finset.piecewise_le_of_le_of_le Finset.piecewise_le_of_le_of_le

theorem le_piecewise_of_le_of_le {δ : α → Type*} [∀ i, Preorder (δ i)] {f g h : ∀ i, δ i}
    (Hf : h ≤ f) (Hg : h ≤ g) : h ≤ s.piecewise f g := fun x =>
  piecewise_cases s f g (fun y => h x ≤ y) (Hf x) (Hg x)
#align finset.le_piecewise_of_le_of_le Finset.le_piecewise_of_le_of_le

theorem piecewise_le_piecewise' {δ : α → Type*} [∀ i, Preorder (δ i)] {f g f' g' : ∀ i, δ i}
    (Hf : ∀ x ∈ s, f x ≤ f' x) (Hg : ∀ (x) (_ : x ∉ s), g x ≤ g' x) :
    s.piecewise f g ≤ s.piecewise f' g' := fun x => by by_cases hx : x ∈ s <;> simp [hx, *]
                                                       -- ⊢ piecewise s f g x ≤ piecewise s f' g' x
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
#align finset.piecewise_le_piecewise' Finset.piecewise_le_piecewise'

theorem piecewise_le_piecewise {δ : α → Type*} [∀ i, Preorder (δ i)] {f g f' g' : ∀ i, δ i}
    (Hf : f ≤ f') (Hg : g ≤ g') : s.piecewise f g ≤ s.piecewise f' g' :=
  s.piecewise_le_piecewise' (fun x _ => Hf x) fun x _ => Hg x
#align finset.piecewise_le_piecewise Finset.piecewise_le_piecewise

theorem piecewise_mem_Icc_of_mem_of_mem {δ : α → Type*} [∀ i, Preorder (δ i)]
    {f f₁ g g₁ : ∀ i, δ i} (hf : f ∈ Set.Icc f₁ g₁) (hg : g ∈ Set.Icc f₁ g₁) :
    s.piecewise f g ∈ Set.Icc f₁ g₁ :=
  ⟨le_piecewise_of_le_of_le _ hf.1 hg.1, piecewise_le_of_le_of_le _ hf.2 hg.2⟩
#align finset.piecewise_mem_Icc_of_mem_of_mem Finset.piecewise_mem_Icc_of_mem_of_mem

theorem piecewise_mem_Icc {δ : α → Type*} [∀ i, Preorder (δ i)] {f g : ∀ i, δ i} (h : f ≤ g) :
    s.piecewise f g ∈ Set.Icc f g :=
  piecewise_mem_Icc_of_mem_of_mem _ (Set.left_mem_Icc.2 h) (Set.right_mem_Icc.2 h)
#align finset.piecewise_mem_Icc Finset.piecewise_mem_Icc

theorem piecewise_mem_Icc' {δ : α → Type*} [∀ i, Preorder (δ i)] {f g : ∀ i, δ i} (h : g ≤ f) :
    s.piecewise f g ∈ Set.Icc g f :=
  piecewise_mem_Icc_of_mem_of_mem _ (Set.right_mem_Icc.2 h) (Set.left_mem_Icc.2 h)
#align finset.piecewise_mem_Icc' Finset.piecewise_mem_Icc'

end Piecewise

section DecidablePiExists

variable {s : Finset α}

instance decidableDforallFinset {p : ∀ a ∈ s, Prop} [_hp : ∀ (a) (h : a ∈ s), Decidable (p a h)] :
    Decidable (∀ (a) (h : a ∈ s), p a h) :=
  Multiset.decidableDforallMultiset
#align finset.decidable_dforall_finset Finset.decidableDforallFinset

-- porting notes: In lean3, the above was picked up when decidability of s ⊆ t was needed
-- in lean4 it seems this is not the case.
instance decidableSubsetFinset [DecidableEq α] {s t : Finset α} : Decidable (s ⊆ t) :=
  decidableDforallFinset

-- porting notes: In lean3, the above was picked up when decidability of s ⊂ t was needed
-- in lean4 it seems this is not the case.
instance decidableSSubsetFinset [DecidableEq α] {s t : Finset α} : Decidable (s ⊂ t) := by
  rw [ssubset_iff_subset_ne]
  -- ⊢ Decidable (s ⊆ t ∧ s ≠ t)
  have h₁ : Decidable (s ⊆ t) := decidableSubsetFinset
  -- ⊢ Decidable (s ⊆ t ∧ s ≠ t)
  have h₂ : Decidable (s ≠ t) := instDecidableNot
  -- ⊢ Decidable (s ⊆ t ∧ s ≠ t)
  exact instDecidableAnd
  -- 🎉 no goals

/-- decidable equality for functions whose domain is bounded by finsets -/
instance decidableEqPiFinset {β : α → Type*} [_h : ∀ a, DecidableEq (β a)] :
    DecidableEq (∀ a ∈ s, β a) :=
  Multiset.decidableEqPiMultiset
#align finset.decidable_eq_pi_finset Finset.decidableEqPiFinset

instance decidableDexistsFinset {p : ∀ a ∈ s, Prop} [_hp : ∀ (a) (h : a ∈ s), Decidable (p a h)] :
    Decidable (∃ (a : _) (h : a ∈ s), p a h) :=
  Multiset.decidableDexistsMultiset
#align finset.decidable_dexists_finset Finset.decidableDexistsFinset

instance decidableExistsAndFinset {p : α → Prop} [_hp : ∀ (a), Decidable (p a)] :
    Decidable (∃ a ∈ s, p a) :=
  decidable_of_iff (∃ (a : _) (_ : a ∈ s), p a) (by simp)
                                                    -- 🎉 no goals

end DecidablePiExists

/-! ### filter -/


section Filter

variable (p q : α → Prop) [DecidablePred p] [DecidablePred q]

/-- `Finset.filter p s` is the set of elements of `s` that satisfy `p`. -/
def filter (s : Finset α) : Finset α :=
  ⟨_, s.2.filter p⟩
#align finset.filter Finset.filter

@[simp]
theorem filter_val (s : Finset α) : (filter p s).1 = s.1.filter p :=
  rfl
#align finset.filter_val Finset.filter_val

@[simp]
theorem filter_subset (s : Finset α) : s.filter p ⊆ s :=
  Multiset.filter_subset _ _
#align finset.filter_subset Finset.filter_subset

variable {p}

@[simp]
theorem mem_filter {s : Finset α} {a : α} : a ∈ s.filter p ↔ a ∈ s ∧ p a :=
  Multiset.mem_filter
#align finset.mem_filter Finset.mem_filter

theorem mem_of_mem_filter {s : Finset α} (x : α) (h : x ∈ s.filter p) : x ∈ s :=
  Multiset.mem_of_mem_filter h
#align finset.mem_of_mem_filter Finset.mem_of_mem_filter

theorem filter_ssubset {s : Finset α} : s.filter p ⊂ s ↔ ∃ x ∈ s, ¬p x :=
  ⟨fun h =>
    let ⟨x, hs, hp⟩ := Set.exists_of_ssubset h
    ⟨x, hs, mt (fun hp => mem_filter.2 ⟨hs, hp⟩) hp⟩,
    fun ⟨_, hs, hp⟩ => ⟨s.filter_subset _, fun h => hp (mem_filter.1 (h hs)).2⟩⟩
#align finset.filter_ssubset Finset.filter_ssubset

variable (p)

theorem filter_filter (s : Finset α) : (s.filter p).filter q = s.filter fun a => p a ∧ q a :=
  ext fun a => by
    simp only [mem_filter, and_assoc, Bool.decide_and, Bool.decide_coe, Bool.and_eq_true]
    -- 🎉 no goals
#align finset.filter_filter Finset.filter_filter

theorem filter_True {s : Finset α} : Finset.filter (fun _ => True) s = s := by
  ext; simp
  -- ⊢ a✝ ∈ filter (fun x => True) s ↔ a✝ ∈ s
       -- 🎉 no goals
#align finset.filter_true Finset.filter_True

@[simp]
theorem filter_False (s : Finset α) : filter (fun _ => False) s = ∅ :=
  ext fun a => by simp [mem_filter, and_false_iff]
                  -- 🎉 no goals
#align finset.filter_false Finset.filter_False

variable {p q}

theorem filter_eq_self (s : Finset α) : s.filter p = s ↔ ∀ x ∈ s, p x := by simp [Finset.ext_iff]
                                                                            -- 🎉 no goals
#align finset.filter_eq_self Finset.filter_eq_self

/-- If all elements of a `Finset` satisfy the predicate `p`, `s.filter p` is `s`. -/
@[simp]
theorem filter_true_of_mem {s : Finset α} (h : ∀ x ∈ s, p x) : s.filter p = s :=
  (filter_eq_self s).mpr h
#align finset.filter_true_of_mem Finset.filter_true_of_mem

/-- If all elements of a `Finset` fail to satisfy the predicate `p`, `s.filter p` is `∅`. -/
theorem filter_false_of_mem {s : Finset α} (h : ∀ x ∈ s, ¬p x) : s.filter p = ∅ :=
  eq_empty_of_forall_not_mem
    (by simpa only [eq_empty_iff_forall_not_mem, mem_filter, not_and] using h)
        -- 🎉 no goals
#align finset.filter_false_of_mem Finset.filter_false_of_mem

theorem filter_eq_empty_iff (s : Finset α) : s.filter p = ∅ ↔ ∀ x ∈ s, ¬p x := by
  refine' ⟨_, filter_false_of_mem⟩
  -- ⊢ filter p s = ∅ → ∀ (x : α), x ∈ s → ¬p x
  intro hs
  -- ⊢ ∀ (x : α), x ∈ s → ¬p x
  injection hs with hs'
  -- ⊢ ∀ (x : α), x ∈ s → ¬p x
  rwa [filter_eq_nil] at hs'
  -- 🎉 no goals
#align finset.filter_eq_empty_iff Finset.filter_eq_empty_iff

theorem filter_nonempty_iff {s : Finset α} : (s.filter p).Nonempty ↔ ∃ a ∈ s, p a := by
  simp [nonempty_iff_ne_empty, Ne.def, filter_eq_empty_iff, not_not, not_forall]
  -- 🎉 no goals
#align finset.filter_nonempty_iff Finset.filter_nonempty_iff

theorem filter_congr {s : Finset α} (H : ∀ x ∈ s, p x ↔ q x) : filter p s = filter q s :=
  eq_of_veq <| Multiset.filter_congr H
#align finset.filter_congr Finset.filter_congr

variable (p q)

theorem filter_empty : filter p ∅ = ∅ :=
  subset_empty.1 <| filter_subset _ _
#align finset.filter_empty Finset.filter_empty

theorem filter_subset_filter {s t : Finset α} (h : s ⊆ t) : s.filter p ⊆ t.filter p := fun _a ha =>
  mem_filter.2 ⟨h (mem_filter.1 ha).1, (mem_filter.1 ha).2⟩
#align finset.filter_subset_filter Finset.filter_subset_filter

theorem monotone_filter_left : Monotone (filter p) := fun _ _ => filter_subset_filter p
#align finset.monotone_filter_left Finset.monotone_filter_left

theorem monotone_filter_right (s : Finset α) ⦃p q : α → Prop⦄ [DecidablePred p] [DecidablePred q]
    (h : p ≤ q) : s.filter p ≤ s.filter q :=
  Multiset.subset_of_le (Multiset.monotone_filter_right s.val h)
#align finset.monotone_filter_right Finset.monotone_filter_right

@[simp, norm_cast]
theorem coe_filter (s : Finset α) : ↑(s.filter p) = ({ x ∈ ↑s | p x } : Set α) :=
  Set.ext fun _ => mem_filter
#align finset.coe_filter Finset.coe_filter

theorem subset_coe_filter_of_subset_forall (s : Finset α) {t : Set α} (h₁ : t ⊆ s)
    (h₂ : ∀ x ∈ t, p x) : t ⊆ s.filter p := fun x hx => (s.coe_filter p).symm ▸ ⟨h₁ hx, h₂ x hx⟩
#align finset.subset_coe_filter_of_subset_forall Finset.subset_coe_filter_of_subset_forall

theorem filter_singleton (a : α) : filter p (singleton a) = if p a then singleton a else ∅ := by
  classical
    ext x
    simp
    split_ifs with h <;> by_cases h' : x = a <;> simp [h, h']
#align finset.filter_singleton Finset.filter_singleton

theorem filter_cons_of_pos (a : α) (s : Finset α) (ha : a ∉ s) (hp : p a) :
    filter p (cons a s ha) = cons a (filter p s) (mem_filter.not.mpr <| mt And.left ha) :=
  eq_of_veq <| Multiset.filter_cons_of_pos s.val hp
#align finset.filter_cons_of_pos Finset.filter_cons_of_pos

theorem filter_cons_of_neg (a : α) (s : Finset α) (ha : a ∉ s) (hp : ¬p a) :
    filter p (cons a s ha) = filter p s :=
  eq_of_veq <| Multiset.filter_cons_of_neg s.val hp
#align finset.filter_cons_of_neg Finset.filter_cons_of_neg

theorem disjoint_filter {s : Finset α} {p q : α → Prop} [DecidablePred p] [DecidablePred q] :
    Disjoint (s.filter p) (s.filter q) ↔ ∀ x ∈ s, p x → ¬q x := by
  constructor <;> simp (config := { contextual := true }) [disjoint_left]
  -- ⊢ _root_.Disjoint (filter p s) (filter q s) → ∀ (x : α), x ∈ s → p x → ¬q x
                  -- 🎉 no goals
                  -- 🎉 no goals
#align finset.disjoint_filter Finset.disjoint_filter

theorem disjoint_filter_filter {s t : Finset α}
    {p q : α → Prop} [DecidablePred p] [DecidablePred q] :
    Disjoint s t → Disjoint (s.filter p) (t.filter q) :=
  Disjoint.mono (filter_subset _ _) (filter_subset _ _)
#align finset.disjoint_filter_filter Finset.disjoint_filter_filter

theorem disjoint_filter_filter' (s t : Finset α)
    {p q : α → Prop} [DecidablePred p] [DecidablePred q] (h : Disjoint p q) :
    Disjoint (s.filter p) (t.filter q) := by
  simp_rw [disjoint_left, mem_filter]
  -- ⊢ ∀ ⦃a : α⦄, a ∈ s ∧ p a → ¬(a ∈ t ∧ q a)
  rintro a ⟨_, hp⟩ ⟨_, hq⟩
  -- ⊢ False
  rw [Pi.disjoint_iff] at h
  -- ⊢ False
  simpa [hp, hq] using h a
  -- 🎉 no goals
#align finset.disjoint_filter_filter' Finset.disjoint_filter_filter'

theorem disjoint_filter_filter_neg (s t : Finset α) (p : α → Prop)
    [DecidablePred p] [∀ x, Decidable (¬p x)] :
    Disjoint (s.filter p) (t.filter fun a => ¬p a) :=
  disjoint_filter_filter' s t disjoint_compl_right
#align finset.disjoint_filter_filter_neg Finset.disjoint_filter_filter_neg

theorem filter_disj_union (s : Finset α) (t : Finset α) (h : Disjoint s t) :
    filter p (disjUnion s t h) = (filter p s).disjUnion (filter p t) (disjoint_filter_filter h) :=
  eq_of_veq <| Multiset.filter_add _ _ _
#align finset.filter_disj_union Finset.filter_disj_union

theorem filter_cons {a : α} (s : Finset α) (ha : a ∉ s) :
    filter p (cons a s ha) =
      (if p a then {a} else ∅ : Finset α).disjUnion (filter p s)
        (by
          split_ifs
          -- ⊢ _root_.Disjoint {a} (filter p s)
          · rw [disjoint_singleton_left]
            -- ⊢ ¬a ∈ filter p s
            exact mem_filter.not.mpr <| mt And.left ha
            -- 🎉 no goals
          · exact disjoint_empty_left _) := by
            -- 🎉 no goals
  split_ifs with h
  -- ⊢ filter p (cons a s ha) = disjUnion {a} (filter p s) (_ : _root_.Disjoint {a} …
  · rw [filter_cons_of_pos _ _ _ ha h, singleton_disjUnion]
    -- 🎉 no goals
  · rw [filter_cons_of_neg _ _ _ ha h, empty_disjUnion]
    -- 🎉 no goals
#align finset.filter_cons Finset.filter_cons

variable [DecidableEq α]

theorem filter_union (s₁ s₂ : Finset α) : (s₁ ∪ s₂).filter p = s₁.filter p ∪ s₂.filter p :=
  ext fun _ => by simp only [mem_filter, mem_union, or_and_right]
                  -- 🎉 no goals
#align finset.filter_union Finset.filter_union

theorem filter_union_right (s : Finset α) : s.filter p ∪ s.filter q = s.filter fun x => p x ∨ q x :=
  ext fun x => by simp [mem_filter, mem_union, ←and_or_left]
                  -- 🎉 no goals
#align finset.filter_union_right Finset.filter_union_right

theorem filter_mem_eq_inter {s t : Finset α} [∀ i, Decidable (i ∈ t)] :
    (s.filter fun i => i ∈ t) = s ∩ t :=
  ext fun i => by simp [mem_filter, mem_inter]
                  -- 🎉 no goals
#align finset.filter_mem_eq_inter Finset.filter_mem_eq_inter

theorem filter_inter_distrib (s t : Finset α) : (s ∩ t).filter p = s.filter p ∩ t.filter p := by
  ext
  -- ⊢ a✝ ∈ filter p (s ∩ t) ↔ a✝ ∈ filter p s ∩ filter p t
  simp [mem_filter, mem_inter, and_assoc]
  -- 🎉 no goals
#align finset.filter_inter_distrib Finset.filter_inter_distrib

theorem filter_inter (s t : Finset α) : filter p s ∩ t = filter p (s ∩ t) := by
  ext
  -- ⊢ a✝ ∈ filter p s ∩ t ↔ a✝ ∈ filter p (s ∩ t)
  simp only [mem_inter, mem_filter, and_right_comm]
  -- 🎉 no goals
#align finset.filter_inter Finset.filter_inter

theorem inter_filter (s t : Finset α) : s ∩ filter p t = filter p (s ∩ t) := by
  rw [inter_comm, filter_inter, inter_comm]
  -- 🎉 no goals
#align finset.inter_filter Finset.inter_filter

theorem filter_insert (a : α) (s : Finset α) :
    filter p (insert a s) = if p a then insert a (filter p s) else filter p s := by
  ext x
  -- ⊢ x ∈ filter p (insert a s) ↔ x ∈ if p a then insert a (filter p s) else filte …
  split_ifs with h <;> by_cases h' : x = a <;> simp [h, h']
  -- ⊢ x ∈ filter p (insert a s) ↔ x ∈ insert a (filter p s)
                       -- ⊢ x ∈ filter p (insert a s) ↔ x ∈ insert a (filter p s)
                       -- ⊢ x ∈ filter p (insert a s) ↔ x ∈ filter p s
                                               -- 🎉 no goals
                                               -- 🎉 no goals
                                               -- 🎉 no goals
                                               -- 🎉 no goals
#align finset.filter_insert Finset.filter_insert

theorem filter_erase (a : α) (s : Finset α) : filter p (erase s a) = erase (filter p s) a := by
  ext x
  -- ⊢ x ∈ filter p (erase s a) ↔ x ∈ erase (filter p s) a
  simp only [and_assoc, mem_filter, iff_self_iff, mem_erase]
  -- 🎉 no goals
#align finset.filter_erase Finset.filter_erase

theorem filter_or (s : Finset α) : (s.filter fun a => p a ∨ q a) = s.filter p ∪ s.filter q :=
  ext fun _ => by simp [mem_filter, mem_union, and_or_left]
                  -- 🎉 no goals
#align finset.filter_or Finset.filter_or

theorem filter_and (s : Finset α) : (s.filter fun a => p a ∧ q a) = s.filter p ∩ s.filter q :=
  ext fun _ => by simp [mem_filter, mem_inter, and_comm, and_left_comm, and_self_iff, and_assoc]
                  -- 🎉 no goals
#align finset.filter_and Finset.filter_and

theorem filter_not (s : Finset α) : (s.filter fun a => ¬p a) = s \ s.filter p :=
  ext <| fun a => by
    simp only [Bool.decide_coe, Bool.not_eq_true', mem_filter, and_comm, mem_sdiff, not_and_or,
      Bool.not_eq_true, and_or_left, and_not_self, or_false]
#align finset.filter_not Finset.filter_not

theorem sdiff_eq_filter (s₁ s₂ : Finset α) : s₁ \ s₂ = filter (· ∉ s₂) s₁ :=
  ext fun _ => by simp [mem_sdiff, mem_filter]
                  -- 🎉 no goals
#align finset.sdiff_eq_filter Finset.sdiff_eq_filter

theorem sdiff_eq_self (s₁ s₂ : Finset α) : s₁ \ s₂ = s₁ ↔ s₁ ∩ s₂ ⊆ ∅ := by
  simp [Subset.antisymm_iff, disjoint_iff_inter_eq_empty]
  -- 🎉 no goals
#align finset.sdiff_eq_self Finset.sdiff_eq_self

theorem subset_union_elim {s : Finset α} {t₁ t₂ : Set α} (h : ↑s ⊆ t₁ ∪ t₂) :
    ∃ s₁ s₂ : Finset α, s₁ ∪ s₂ = s ∧ ↑s₁ ⊆ t₁ ∧ ↑s₂ ⊆ t₂ \ t₁ := by
  classical
    refine' ⟨s.filter (· ∈ t₁), s.filter (· ∉ t₁), _, _, _⟩
    · simp [filter_union_right, em]
    · intro x
      simp
    · intro x
      simp
      intro hx hx₂
      refine' ⟨Or.resolve_left (h hx) hx₂, hx₂⟩
#align finset.subset_union_elim Finset.subset_union_elim

-- Porting note: likely no longer relevant with `Bool`s
#noalign finset.filter_congr_decidable

section Classical

open Classical

-- Porting note: The notation `{ x ∈ s | p x }` in Lean 4 is hardcoded to be about `Set`.
-- So at the moment the whole `Sep`-class is useless, as it doesn't have notation.
-- /-- The following instance allows us to write `{x ∈ s | p x}` for `Finset.filter p s`.
--   We don't want to redo all lemmas of `Finset.filter` for `Sep.sep`, so we make sure that `simp`
--   unfolds the notation `{x ∈ s | p x}` to `Finset.filter p s`.
-- -/
-- noncomputable instance {α : Type*} : Sep α (Finset α) :=
--   ⟨fun p x => x.filter p⟩

-- -- @[simp] -- Porting note: not a simp-lemma until `Sep`-notation is fixed.
-- theorem sep_def {α : Type*} (s : Finset α) (p : α → Prop) : { x ∈ s | p x } = s.filter p := by
--   ext
--   simp
-- #align finset.sep_def Finset.sep_def

end Classical

-- This is not a good simp lemma, as it would prevent `Finset.mem_filter` from firing
-- on, e.g. `x ∈ s.filter (Eq b)`.
/-- After filtering out everything that does not equal a given value, at most that value remains.

  This is equivalent to `filter_eq'` with the equality the other way.
-/
theorem filter_eq [DecidableEq β] (s : Finset β) (b : β) :
    s.filter (Eq b) = ite (b ∈ s) {b} ∅ := by
  split_ifs with h
  -- ⊢ filter (Eq b) s = {b}
  · ext
    -- ⊢ a✝ ∈ filter (Eq b) s ↔ a✝ ∈ {b}
    simp only [mem_filter, mem_singleton, decide_eq_true_eq]
    -- ⊢ a✝ ∈ s ∧ b = a✝ ↔ a✝ = b
    refine ⟨fun h => h.2.symm, ?_⟩
    -- ⊢ a✝ = b → a✝ ∈ s ∧ b = a✝
    rintro rfl
    -- ⊢ a✝ ∈ s ∧ a✝ = a✝
    exact ⟨h, rfl⟩
    -- 🎉 no goals
  · ext
    -- ⊢ a✝ ∈ filter (Eq b) s ↔ a✝ ∈ ∅
    simp only [mem_filter, not_and, iff_false_iff, not_mem_empty, decide_eq_true_eq]
    -- ⊢ a✝ ∈ s → ¬b = a✝
    rintro m rfl
    -- ⊢ False
    exact h m
    -- 🎉 no goals
#align finset.filter_eq Finset.filter_eq

/-- After filtering out everything that does not equal a given value, at most that value remains.

  This is equivalent to `filter_eq` with the equality the other way.
-/
theorem filter_eq' [DecidableEq β] (s : Finset β) (b : β) :
    (s.filter fun a => a = b) = ite (b ∈ s) {b} ∅ :=
  _root_.trans (filter_congr fun _ _ => by simp_rw [@eq_comm _ b]) (filter_eq s b)
                                           -- 🎉 no goals
#align finset.filter_eq' Finset.filter_eq'

theorem filter_ne [DecidableEq β] (s : Finset β) (b : β) :
    (s.filter fun a => b ≠ a) = s.erase b := by
  ext
  -- ⊢ a✝ ∈ filter (fun a => b ≠ a) s ↔ a✝ ∈ erase s b
  simp only [mem_filter, mem_erase, Ne.def, decide_not, Bool.not_eq_true', decide_eq_false_iff_not]
  -- ⊢ a✝ ∈ s ∧ ¬b = a✝ ↔ ¬a✝ = b ∧ a✝ ∈ s
  tauto
  -- 🎉 no goals
#align finset.filter_ne Finset.filter_ne

theorem filter_ne' [DecidableEq β] (s : Finset β) (b : β) : (s.filter fun a => a ≠ b) = s.erase b :=
  _root_.trans (filter_congr fun _ _ => by simp_rw [@ne_comm _ b]) (filter_ne s b)
                                           -- 🎉 no goals
#align finset.filter_ne' Finset.filter_ne'

theorem filter_inter_filter_neg_eq (s t : Finset α) :
    (s.filter p ∩ t.filter fun a => ¬p a) = ∅ :=
  by simpa using (disjoint_filter_filter_neg s t p).eq_bot
     -- 🎉 no goals
#align finset.filter_inter_filter_neg_eq Finset.filter_inter_filter_neg_eq

theorem filter_union_filter_of_codisjoint (s : Finset α) (h : Codisjoint p q) :
    s.filter p ∪ s.filter q = s :=
  (filter_or _ _ _).symm.trans <| filter_true_of_mem fun x _ => h.top_le x trivial
#align finset.filter_union_filter_of_codisjoint Finset.filter_union_filter_of_codisjoint

theorem filter_union_filter_neg_eq [∀ x, Decidable (¬p x)] (s : Finset α) :
    (s.filter p ∪ s.filter fun a => ¬p a) = s :=
  filter_union_filter_of_codisjoint _ _ _ <| @codisjoint_hnot_right _ _ p
#align finset.filter_union_filter_neg_eq Finset.filter_union_filter_neg_eq

end Filter

/-! ### range -/


section Range

variable {n m l : ℕ}

/-- `range n` is the set of natural numbers less than `n`. -/
def range (n : ℕ) : Finset ℕ :=
  ⟨_, nodup_range n⟩
#align finset.range Finset.range

@[simp]
theorem range_val (n : ℕ) : (range n).1 = Multiset.range n :=
  rfl
#align finset.range_val Finset.range_val

@[simp]
theorem mem_range : m ∈ range n ↔ m < n :=
  Multiset.mem_range
#align finset.mem_range Finset.mem_range

@[simp, norm_cast]
theorem coe_range (n : ℕ) : (range n : Set ℕ) = Set.Iio n :=
  Set.ext fun _ => mem_range
#align finset.coe_range Finset.coe_range

@[simp]
theorem range_zero : range 0 = ∅ :=
  rfl
#align finset.range_zero Finset.range_zero

@[simp]
theorem range_one : range 1 = {0} :=
  rfl
#align finset.range_one Finset.range_one

theorem range_succ : range (succ n) = insert n (range n) :=
  eq_of_veq <| (Multiset.range_succ n).trans <| (ndinsert_of_not_mem not_mem_range_self).symm
#align finset.range_succ Finset.range_succ

theorem range_add_one : range (n + 1) = insert n (range n) :=
  range_succ
#align finset.range_add_one Finset.range_add_one

-- Porting note: @[simp] can prove this
theorem not_mem_range_self : n ∉ range n :=
  Multiset.not_mem_range_self
#align finset.not_mem_range_self Finset.not_mem_range_self

-- Porting note: @[simp] can prove this
theorem self_mem_range_succ (n : ℕ) : n ∈ range (n + 1) :=
  Multiset.self_mem_range_succ n
#align finset.self_mem_range_succ Finset.self_mem_range_succ

@[simp]
theorem range_subset {n m} : range n ⊆ range m ↔ n ≤ m :=
  Multiset.range_subset
#align finset.range_subset Finset.range_subset

theorem range_mono : Monotone range := fun _ _ => range_subset.2
#align finset.range_mono Finset.range_mono

theorem mem_range_succ_iff {a b : ℕ} : a ∈ Finset.range b.succ ↔ a ≤ b :=
  Finset.mem_range.trans Nat.lt_succ_iff
#align finset.mem_range_succ_iff Finset.mem_range_succ_iff

theorem mem_range_le {n x : ℕ} (hx : x ∈ range n) : x ≤ n :=
  (mem_range.1 hx).le
#align finset.mem_range_le Finset.mem_range_le

theorem mem_range_sub_ne_zero {n x : ℕ} (hx : x ∈ range n) : n - x ≠ 0 :=
  _root_.ne_of_gt <| tsub_pos_of_lt <| mem_range.1 hx
#align finset.mem_range_sub_ne_zero Finset.mem_range_sub_ne_zero

@[simp]
theorem nonempty_range_iff : (range n).Nonempty ↔ n ≠ 0 :=
  ⟨fun ⟨k, hk⟩ => ((_root_.zero_le k).trans_lt <| mem_range.1 hk).ne',
   fun h => ⟨0, mem_range.2 <| pos_iff_ne_zero.2 h⟩⟩
#align finset.nonempty_range_iff Finset.nonempty_range_iff

@[simp]
theorem range_eq_empty_iff : range n = ∅ ↔ n = 0 := by
  rw [← not_nonempty_iff_eq_empty, nonempty_range_iff, not_not]
  -- 🎉 no goals
#align finset.range_eq_empty_iff Finset.range_eq_empty_iff

theorem nonempty_range_succ : (range <| n + 1).Nonempty :=
  nonempty_range_iff.2 n.succ_ne_zero
#align finset.nonempty_range_succ Finset.nonempty_range_succ

@[simp]
theorem range_filter_eq {n m : ℕ} : (range n).filter (· = m) = if m < n then {m} else ∅ := by
  convert filter_eq (range n) m using 2
  -- ⊢ (fun x => x = m) = Eq m
  · ext
    -- ⊢ x✝ = m ↔ m = x✝
    rw [eq_comm]
    -- 🎉 no goals
  · simp
    -- 🎉 no goals
#align finset.range_filter_eq Finset.range_filter_eq

end Range

-- useful rules for calculations with quantifiers
theorem exists_mem_empty_iff (p : α → Prop) : (∃ x, x ∈ (∅ : Finset α) ∧ p x) ↔ False := by
  simp only [not_mem_empty, false_and_iff, exists_false]
  -- 🎉 no goals
#align finset.exists_mem_empty_iff Finset.exists_mem_empty_iff

theorem exists_mem_insert [DecidableEq α] (a : α) (s : Finset α) (p : α → Prop) :
    (∃ x, x ∈ insert a s ∧ p x) ↔ p a ∨ ∃ x, x ∈ s ∧ p x := by
  simp only [mem_insert, or_and_right, exists_or, exists_eq_left]
  -- 🎉 no goals
#align finset.exists_mem_insert Finset.exists_mem_insert

theorem forall_mem_empty_iff (p : α → Prop) : (∀ x, x ∈ (∅ : Finset α) → p x) ↔ True :=
  iff_true_intro fun _ h => False.elim <| not_mem_empty _ h
#align finset.forall_mem_empty_iff Finset.forall_mem_empty_iff

theorem forall_mem_insert [DecidableEq α] (a : α) (s : Finset α) (p : α → Prop) :
    (∀ x, x ∈ insert a s → p x) ↔ p a ∧ ∀ x, x ∈ s → p x := by
  simp only [mem_insert, or_imp, forall_and, forall_eq]
  -- 🎉 no goals
#align finset.forall_mem_insert Finset.forall_mem_insert

/-- Useful in proofs by induction. -/
theorem forall_of_forall_insert [DecidableEq α] {p : α → Prop} {a : α} {s : Finset α}
    (H : ∀ x, x ∈ insert a s → p x) (x) (h : x ∈ s) : p x :=
  H _ <| mem_insert_of_mem h
#align finset.forall_of_forall_insert Finset.forall_of_forall_insert

end Finset

/-- Equivalence between the set of natural numbers which are `≥ k` and `ℕ`, given by `n → n - k`. -/
def notMemRangeEquiv (k : ℕ) : { n // n ∉ range k } ≃ ℕ where
  toFun i := i.1 - k
  invFun j := ⟨j + k, by simp⟩
                         -- 🎉 no goals
  left_inv j := by
    rw [Subtype.ext_iff_val]
    -- ⊢ ↑((fun j => { val := j + k, property := (_ : ¬j + k ∈ range k) }) ((fun i => …
    apply tsub_add_cancel_of_le
    -- ⊢ k ≤ ↑j
    simpa using j.2
    -- 🎉 no goals
  right_inv j := add_tsub_cancel_right _ _
#align not_mem_range_equiv notMemRangeEquiv

@[simp]
theorem coe_notMemRangeEquiv (k : ℕ) :
    (notMemRangeEquiv k : { n // n ∉ range k } → ℕ) = fun (i : { n // n ∉ range k }) => i - k :=
  rfl
#align coe_not_mem_range_equiv coe_notMemRangeEquiv

@[simp]
theorem coe_notMemRangeEquiv_symm (k : ℕ) :
    ((notMemRangeEquiv k).symm : ℕ → { n // n ∉ range k }) = fun j => ⟨j + k, by simp⟩ :=
                                                                                 -- 🎉 no goals
  rfl
#align coe_not_mem_range_equiv_symm coe_notMemRangeEquiv_symm

/-! ### dedup on list and multiset -/


namespace Multiset

variable [DecidableEq α] {s t : Multiset α}

/-- `toFinset s` removes duplicates from the multiset `s` to produce a finset. -/
def toFinset (s : Multiset α) : Finset α :=
  ⟨_, nodup_dedup s⟩
#align multiset.to_finset Multiset.toFinset

@[simp]
theorem toFinset_val (s : Multiset α) : s.toFinset.1 = s.dedup :=
  rfl
#align multiset.to_finset_val Multiset.toFinset_val

theorem toFinset_eq {s : Multiset α} (n : Nodup s) : Finset.mk s n = s.toFinset :=
  Finset.val_inj.1 n.dedup.symm
#align multiset.to_finset_eq Multiset.toFinset_eq

theorem Nodup.toFinset_inj {l l' : Multiset α} (hl : Nodup l) (hl' : Nodup l')
    (h : l.toFinset = l'.toFinset) : l = l' := by
  simpa [← toFinset_eq hl, ← toFinset_eq hl'] using h
  -- 🎉 no goals
#align multiset.nodup.to_finset_inj Multiset.Nodup.toFinset_inj

@[simp]
theorem mem_toFinset {a : α} {s : Multiset α} : a ∈ s.toFinset ↔ a ∈ s :=
  mem_dedup
#align multiset.mem_to_finset Multiset.mem_toFinset

@[simp]
theorem toFinset_zero : toFinset (0 : Multiset α) = ∅ :=
  rfl
#align multiset.to_finset_zero Multiset.toFinset_zero

@[simp]
theorem toFinset_cons (a : α) (s : Multiset α) : toFinset (a ::ₘ s) = insert a (toFinset s) :=
  Finset.eq_of_veq dedup_cons
#align multiset.to_finset_cons Multiset.toFinset_cons

@[simp]
theorem toFinset_singleton (a : α) : toFinset ({a} : Multiset α) = {a} := by
  rw [← cons_zero, toFinset_cons, toFinset_zero, IsLawfulSingleton.insert_emptyc_eq]
  -- 🎉 no goals
#align multiset.to_finset_singleton Multiset.toFinset_singleton

@[simp]
theorem toFinset_add (s t : Multiset α) : toFinset (s + t) = toFinset s ∪ toFinset t :=
  Finset.ext <| by simp
                   -- 🎉 no goals
#align multiset.to_finset_add Multiset.toFinset_add

@[simp]
theorem toFinset_nsmul (s : Multiset α) : ∀ (n : ℕ) (_ : n ≠ 0), (n • s).toFinset = s.toFinset
  | 0, h => by contradiction
               -- 🎉 no goals
  | n + 1, _ => by
    by_cases h : n = 0
    -- ⊢ toFinset ((n + 1) • s) = toFinset s
    · rw [h, zero_add, one_nsmul]
      -- 🎉 no goals
    · rw [add_nsmul, toFinset_add, one_nsmul, toFinset_nsmul s n h, Finset.union_idempotent]
      -- 🎉 no goals
#align multiset.to_finset_nsmul Multiset.toFinset_nsmul

@[simp]
theorem toFinset_inter (s t : Multiset α) : toFinset (s ∩ t) = toFinset s ∩ toFinset t :=
  Finset.ext <| by simp
                   -- 🎉 no goals
#align multiset.to_finset_inter Multiset.toFinset_inter

@[simp]
theorem toFinset_union (s t : Multiset α) : (s ∪ t).toFinset = s.toFinset ∪ t.toFinset := by
  ext; simp
  -- ⊢ a✝ ∈ toFinset (s ∪ t) ↔ a✝ ∈ toFinset s ∪ toFinset t
       -- 🎉 no goals
#align multiset.to_finset_union Multiset.toFinset_union

@[simp]
theorem toFinset_eq_empty {m : Multiset α} : m.toFinset = ∅ ↔ m = 0 :=
  Finset.val_inj.symm.trans Multiset.dedup_eq_zero
#align multiset.to_finset_eq_empty Multiset.toFinset_eq_empty

@[simp]
theorem toFinset_nonempty : s.toFinset.Nonempty ↔ s ≠ 0 := by
  simp only [toFinset_eq_empty, Ne.def, Finset.nonempty_iff_ne_empty]
  -- 🎉 no goals
#align multiset.to_finset_nonempty Multiset.toFinset_nonempty

@[simp]
theorem toFinset_subset : s.toFinset ⊆ t.toFinset ↔ s ⊆ t := by
  simp only [Finset.subset_iff, Multiset.subset_iff, Multiset.mem_toFinset]
  -- 🎉 no goals
#align multiset.to_finset_subset Multiset.toFinset_subset

@[simp]
theorem toFinset_ssubset : s.toFinset ⊂ t.toFinset ↔ s ⊂ t := by
  simp_rw [Finset.ssubset_def, toFinset_subset]
  -- ⊢ s ⊆ t ∧ ¬t ⊆ s ↔ s ⊂ t
  rfl
  -- 🎉 no goals
#align multiset.to_finset_ssubset Multiset.toFinset_ssubset

@[simp]
theorem toFinset_dedup (m : Multiset α) : m.dedup.toFinset = m.toFinset := by
  simp_rw [toFinset, dedup_idempotent]
  -- 🎉 no goals
#align multiset.to_finset_dedup Multiset.toFinset_dedup

@[simp]
theorem toFinset_bind_dedup [DecidableEq β] (m : Multiset α) (f : α → Multiset β) :
    (m.dedup.bind f).toFinset = (m.bind f).toFinset := by simp_rw [toFinset, dedup_bind_dedup]
                                                          -- 🎉 no goals
#align multiset.to_finset_bind_dedup Multiset.toFinset_bind_dedup

instance isWellFounded_ssubset : IsWellFounded (Multiset β) (· ⊂ ·) := by
  classical
  exact Subrelation.isWellFounded (InvImage _ toFinset) toFinset_ssubset.2
#align multiset.is_well_founded_ssubset Multiset.isWellFounded_ssubset

end Multiset

namespace Finset

@[simp]
theorem val_toFinset [DecidableEq α] (s : Finset α) : s.val.toFinset = s := by
  ext
  -- ⊢ a✝ ∈ toFinset s.val ↔ a✝ ∈ s
  rw [Multiset.mem_toFinset, ← mem_def]
  -- 🎉 no goals
#align finset.val_to_finset Finset.val_toFinset

theorem val_le_iff_val_subset {a : Finset α} {b : Multiset α} : a.val ≤ b ↔ a.val ⊆ b :=
  Multiset.le_iff_subset a.nodup
#align finset.val_le_iff_val_subset Finset.val_le_iff_val_subset

end Finset

namespace List

variable [DecidableEq α] {l l' : List α} {a : α}

/-- `toFinset l` removes duplicates from the list `l` to produce a finset. -/
def toFinset (l : List α) : Finset α :=
  Multiset.toFinset l
#align list.to_finset List.toFinset

@[simp]
theorem toFinset_val (l : List α) : l.toFinset.1 = (l.dedup : Multiset α) :=
  rfl
#align list.to_finset_val List.toFinset_val

@[simp]
theorem toFinset_coe (l : List α) : (l : Multiset α).toFinset = l.toFinset :=
  rfl
#align list.to_finset_coe List.toFinset_coe

theorem toFinset_eq (n : Nodup l) : @Finset.mk α l n = l.toFinset :=
  Multiset.toFinset_eq <| by rwa [Multiset.coe_nodup]
                             -- 🎉 no goals
#align list.to_finset_eq List.toFinset_eq

@[simp]
theorem mem_toFinset : a ∈ l.toFinset ↔ a ∈ l :=
  mem_dedup
#align list.mem_to_finset List.mem_toFinset

@[simp, norm_cast]
theorem coe_toFinset (l : List α) : (l.toFinset : Set α) = { a | a ∈ l } :=
  Set.ext fun _ => List.mem_toFinset
#align list.coe_to_finset List.coe_toFinset

@[simp]
theorem toFinset_nil : toFinset (@nil α) = ∅ :=
  rfl
#align list.to_finset_nil List.toFinset_nil

@[simp]
theorem toFinset_cons : toFinset (a :: l) = insert a (toFinset l) :=
  Finset.eq_of_veq <| by by_cases h : a ∈ l <;> simp [Finset.insert_val', Multiset.dedup_cons, h]
                         -- ⊢ (toFinset (a :: l)).val = (insert a (toFinset l)).val
                                                -- 🎉 no goals
                                                -- 🎉 no goals
#align list.to_finset_cons List.toFinset_cons

theorem toFinset_surj_on : Set.SurjOn toFinset { l : List α | l.Nodup } Set.univ := by
  rintro ⟨⟨l⟩, hl⟩ _
  -- ⊢ { val := Quot.mk Setoid.r l, nodup := hl } ∈ toFinset '' {l | Nodup l}
  exact ⟨l, hl, (toFinset_eq hl).symm⟩
  -- 🎉 no goals
#align list.to_finset_surj_on List.toFinset_surj_on

theorem toFinset_surjective : Surjective (toFinset : List α → Finset α) := fun s =>
  let ⟨l, _, hls⟩ := toFinset_surj_on (Set.mem_univ s)
  ⟨l, hls⟩
#align list.to_finset_surjective List.toFinset_surjective

theorem toFinset_eq_iff_perm_dedup : l.toFinset = l'.toFinset ↔ l.dedup ~ l'.dedup := by
  simp [Finset.ext_iff, perm_ext (nodup_dedup _) (nodup_dedup _)]
  -- 🎉 no goals
#align list.to_finset_eq_iff_perm_dedup List.toFinset_eq_iff_perm_dedup

theorem toFinset.ext_iff {a b : List α} : a.toFinset = b.toFinset ↔ ∀ x, x ∈ a ↔ x ∈ b := by
  simp only [Finset.ext_iff, mem_toFinset]
  -- 🎉 no goals
#align list.to_finset.ext_iff List.toFinset.ext_iff

theorem toFinset.ext : (∀ x, x ∈ l ↔ x ∈ l') → l.toFinset = l'.toFinset :=
  toFinset.ext_iff.mpr
#align list.to_finset.ext List.toFinset.ext

theorem toFinset_eq_of_perm (l l' : List α) (h : l ~ l') : l.toFinset = l'.toFinset :=
  toFinset_eq_iff_perm_dedup.mpr h.dedup
#align list.to_finset_eq_of_perm List.toFinset_eq_of_perm

theorem perm_of_nodup_nodup_toFinset_eq (hl : Nodup l) (hl' : Nodup l')
    (h : l.toFinset = l'.toFinset) : l ~ l' := by
  rw [← Multiset.coe_eq_coe]
  -- ⊢ ↑l = ↑l'
  exact Multiset.Nodup.toFinset_inj hl hl' h
  -- 🎉 no goals
#align list.perm_of_nodup_nodup_to_finset_eq List.perm_of_nodup_nodup_toFinset_eq

@[simp]
theorem toFinset_append : toFinset (l ++ l') = l.toFinset ∪ l'.toFinset := by
  induction' l with hd tl hl
  -- ⊢ toFinset ([] ++ l') = toFinset [] ∪ toFinset l'
  · simp
    -- 🎉 no goals
  · simp [hl]
    -- 🎉 no goals
#align list.to_finset_append List.toFinset_append

@[simp]
theorem toFinset_reverse {l : List α} : toFinset l.reverse = l.toFinset :=
  toFinset_eq_of_perm _ _ (reverse_perm l)
#align list.to_finset_reverse List.toFinset_reverse

theorem toFinset_replicate_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (List.replicate n a).toFinset = {a} := by
  ext x
  -- ⊢ x ∈ toFinset (replicate n a) ↔ x ∈ {a}
  simp [hn, List.mem_replicate]
  -- 🎉 no goals
#align list.to_finset_replicate_of_ne_zero List.toFinset_replicate_of_ne_zero

@[simp]
theorem toFinset_union (l l' : List α) : (l ∪ l').toFinset = l.toFinset ∪ l'.toFinset := by
  ext
  -- ⊢ a✝ ∈ toFinset (l ∪ l') ↔ a✝ ∈ toFinset l ∪ toFinset l'
  simp
  -- 🎉 no goals
#align list.to_finset_union List.toFinset_union

@[simp]
theorem toFinset_inter (l l' : List α) : (l ∩ l').toFinset = l.toFinset ∩ l'.toFinset := by
  ext
  -- ⊢ a✝ ∈ toFinset (l ∩ l') ↔ a✝ ∈ toFinset l ∩ toFinset l'
  simp
  -- 🎉 no goals
#align list.to_finset_inter List.toFinset_inter

@[simp]
theorem toFinset_eq_empty_iff (l : List α) : l.toFinset = ∅ ↔ l = nil := by
  cases l <;> simp
  -- ⊢ toFinset [] = ∅ ↔ [] = []
              -- 🎉 no goals
              -- 🎉 no goals
#align list.to_finset_eq_empty_iff List.toFinset_eq_empty_iff

@[simp]
theorem toFinset_nonempty_iff (l : List α) : l.toFinset.Nonempty ↔ l ≠ [] := by
  simp [Finset.nonempty_iff_ne_empty]
  -- 🎉 no goals
#align list.to_finset_nonempty_iff List.toFinset_nonempty_iff

end List

namespace Finset

section ToList

/-- Produce a list of the elements in the finite set using choice. -/
noncomputable def toList (s : Finset α) : List α :=
  s.1.toList
#align finset.to_list Finset.toList

theorem nodup_toList (s : Finset α) : s.toList.Nodup := by
  rw [toList, ← Multiset.coe_nodup, Multiset.coe_toList]
  -- ⊢ Nodup s.val
  exact s.nodup
  -- 🎉 no goals
#align finset.nodup_to_list Finset.nodup_toList

@[simp]
theorem mem_toList {a : α} {s : Finset α} : a ∈ s.toList ↔ a ∈ s :=
  Multiset.mem_toList
#align finset.mem_to_list Finset.mem_toList

@[simp]
theorem toList_eq_nil {s : Finset α} : s.toList = [] ↔ s = ∅ :=
  toList_eq_nil.trans val_eq_zero
#align finset.to_list_eq_nil Finset.toList_eq_nil

@[simp]
theorem empty_toList {s : Finset α} : s.toList.isEmpty ↔ s = ∅ :=
  List.isEmpty_iff_eq_nil.trans toList_eq_nil
#align finset.empty_to_list Finset.empty_toList

@[simp]
theorem toList_empty : (∅ : Finset α).toList = [] :=
  toList_eq_nil.mpr rfl
#align finset.to_list_empty Finset.toList_empty

theorem Nonempty.toList_ne_nil {s : Finset α} (hs : s.Nonempty) : s.toList ≠ [] :=
  mt toList_eq_nil.mp hs.ne_empty
#align finset.nonempty.to_list_ne_nil Finset.Nonempty.toList_ne_nil

theorem Nonempty.not_empty_toList {s : Finset α} (hs : s.Nonempty) : ¬s.toList.isEmpty :=
  mt empty_toList.mp hs.ne_empty
#align finset.nonempty.not_empty_to_list Finset.Nonempty.not_empty_toList

@[simp, norm_cast]
theorem coe_toList (s : Finset α) : (s.toList : Multiset α) = s.val :=
  s.val.coe_toList
#align finset.coe_to_list Finset.coe_toList

@[simp]
theorem toList_toFinset [DecidableEq α] (s : Finset α) : s.toList.toFinset = s := by
  ext
  -- ⊢ a✝ ∈ List.toFinset (toList s) ↔ a✝ ∈ s
  simp
  -- 🎉 no goals
#align finset.to_list_to_finset Finset.toList_toFinset

@[simp]
theorem toList_eq_singleton_iff {a : α} {s : Finset α} : s.toList = [a] ↔ s = {a} := by
  rw [toList, Multiset.toList_eq_singleton_iff, val_eq_singleton_iff]
  -- 🎉 no goals
#align finset.to_list_eq_singleton_iff Finset.toList_eq_singleton_iff

@[simp]
theorem toList_singleton : ∀ a, ({a} : Finset α).toList = [a] :=
  Multiset.toList_singleton
#align finset.to_list_singleton Finset.toList_singleton

theorem exists_list_nodup_eq [DecidableEq α] (s : Finset α) :
    ∃ l : List α, l.Nodup ∧ l.toFinset = s :=
  ⟨s.toList, s.nodup_toList, s.toList_toFinset⟩
#align finset.exists_list_nodup_eq Finset.exists_list_nodup_eq

theorem toList_cons {a : α} {s : Finset α} (h : a ∉ s) : (cons a s h).toList ~ a :: s.toList :=
  (List.perm_ext (nodup_toList _) (by simp [h, nodup_toList s])).2 fun x => by
                                      -- 🎉 no goals
    simp only [List.mem_cons, Finset.mem_toList, Finset.mem_cons]
    -- 🎉 no goals
#align finset.to_list_cons Finset.toList_cons

theorem toList_insert [DecidableEq α] {a : α} {s : Finset α} (h : a ∉ s) :
    (insert a s).toList ~ a :: s.toList :=
  cons_eq_insert _ _ h ▸ toList_cons _
#align finset.to_list_insert Finset.toList_insert

end ToList

/-!
### disjiUnion

This section is about the bounded union of a disjoint indexed family `t : α → Finset β` of finite
sets over a finite set `s : Finset α`. In most cases `Finset.biUnion` should be preferred.
-/


section DisjiUnion

variable {s s₁ s₂ : Finset α} {t t₁ t₂ : α → Finset β}

/-- `disjiUnion s f h` is the set such that `a ∈ disjiUnion s f` iff `a ∈ f i` for some `i ∈ s`.
It is the same as `s.biUnion f`, but it does not require decidable equality on the type. The
hypothesis ensures that the sets are disjoint. -/
def disjiUnion (s : Finset α) (t : α → Finset β) (hf : (s : Set α).PairwiseDisjoint t) : Finset β :=
  ⟨s.val.bind (Finset.val ∘ t),
    Multiset.nodup_bind.mpr
      ⟨fun a _ => (t a).nodup,
        s.nodup.pairwise fun _ ha _ hb hab => disjoint_val.2 <| hf ha hb hab⟩⟩
#align finset.disj_Union Finset.disjUnionₓ -- Porting note: universes and more

@[simp]
theorem disjiUnion_val (s : Finset α) (t : α → Finset β) (h) :
    (s.disjiUnion t h).1 = s.1.bind fun a => (t a).1 :=
  rfl
#align finset.disj_Union_val Finset.disjiUnion_val

@[simp]
theorem disjiUnion_empty (t : α → Finset β) : disjiUnion ∅ t (by simp) = ∅ :=
                                                                 -- 🎉 no goals
  rfl
#align finset.disj_Union_empty Finset.disjiUnion_empty

@[simp]
theorem mem_disjiUnion {b : β} {h} : b ∈ s.disjiUnion t h ↔ ∃ a ∈ s, b ∈ t a := by
  simp only [mem_def, disjiUnion_val, mem_bind, exists_prop]
  -- 🎉 no goals
#align finset.mem_disj_Union Finset.mem_disjiUnion

@[simp, norm_cast]
theorem coe_disjiUnion {h} : (s.disjiUnion t h : Set β) = ⋃ x ∈ (s : Set α), t x := by
  simp [Set.ext_iff, mem_disjiUnion, Set.mem_iUnion, iff_self_iff, mem_coe, imp_true_iff]
  -- 🎉 no goals
#align finset.coe_disj_Union Finset.coe_disjiUnion

@[simp]
theorem disjiUnion_cons (a : α) (s : Finset α) (ha : a ∉ s) (f : α → Finset β) (H) :
    disjiUnion (cons a s ha) f H =
    (f a).disjUnion ((s.disjiUnion f) fun _ hb _ hc => H (mem_cons_of_mem hb) (mem_cons_of_mem hc))
      (disjoint_left.mpr fun _ hb h =>
        let ⟨_, hc, h⟩ := mem_disjiUnion.mp h
        disjoint_left.mp
          (H (mem_cons_self a s) (mem_cons_of_mem hc) (ne_of_mem_of_not_mem hc ha).symm) hb h) :=
  eq_of_veq <| Multiset.cons_bind _ _ _
#align finset.disj_Union_cons Finset.disjiUnion_cons

@[simp]
theorem singleton_disjiUnion (a : α) {h} : Finset.disjiUnion {a} t h = t a :=
  eq_of_veq <| Multiset.singleton_bind _ _
#align finset.singleton_disj_Union Finset.singleton_disjiUnion

theorem disjiUnion_disjiUnion (s : Finset α) (f : α → Finset β) (g : β → Finset γ) (h1 h2) :
    (s.disjiUnion f h1).disjiUnion g h2 =
      s.attach.disjiUnion
        (fun a =>
          ((f a).disjiUnion g) fun b hb c hc =>
            h2 (mem_disjiUnion.mpr ⟨_, a.prop, hb⟩) (mem_disjiUnion.mpr ⟨_, a.prop, hc⟩))
        fun a _ b _ hab =>
        disjoint_left.mpr fun x hxa hxb => by
          obtain ⟨xa, hfa, hga⟩ := mem_disjiUnion.mp hxa
          -- ⊢ False
          obtain ⟨xb, hfb, hgb⟩ := mem_disjiUnion.mp hxb
          -- ⊢ False
          refine'
            disjoint_left.mp
              (h2 (mem_disjiUnion.mpr ⟨_, a.prop, hfa⟩) (mem_disjiUnion.mpr ⟨_, b.prop, hfb⟩) _) hga
              hgb
          rintro rfl
          -- ⊢ False
          exact disjoint_left.mp (h1 a.prop b.prop <| Subtype.coe_injective.ne hab) hfa hfb :=
          -- 🎉 no goals
  eq_of_veq <| Multiset.bind_assoc.trans (Multiset.attach_bind_coe _ _).symm
#align finset.disj_Union_disj_Union Finset.disjiUnion_disjiUnion

theorem disjiUnion_filter_eq_of_maps_to [DecidableEq β] {s : Finset α} {t : Finset β} {f : α → β}
    (h : ∀ x ∈ s, f x ∈ t) :
    t.disjiUnion (fun a => s.filter (fun c => f c = a))
      (fun x' hx y' hy hne => by
        simp_rw [disjoint_left, mem_filter]
        -- ⊢ ∀ ⦃a : α⦄, a ∈ s ∧ f a = x' → ¬(a ∈ s ∧ f a = y')
        rintro i ⟨_, rfl⟩ ⟨_, rfl⟩
        -- ⊢ False
        exact hne rfl) = s :=
        -- 🎉 no goals
  ext fun b => by simpa using h b
                  -- 🎉 no goals
#align finset.disj_Union_filter_eq_of_maps_to Finset.disjiUnion_filter_eq_of_maps_to

end DisjiUnion

section BUnion

/-!
### biUnion

This section is about the bounded union of an indexed family `t : α → Finset β` of finite sets
over a finite set `s : Finset α`.
-/

-- TODO: should be `biUnion`

variable [DecidableEq β] {s s₁ s₂ : Finset α} {t t₁ t₂ : α → Finset β}

/-- `biUnion s t` is the union of `t x` over `x ∈ s`.
(This was formerly `bind` due to the monad structure on types with `DecidableEq`.) -/
protected def biUnion (s : Finset α) (t : α → Finset β) : Finset β :=
  (s.1.bind fun a => (t a).1).toFinset
#align finset.bUnion Finset.biUnion

@[simp]
theorem biUnion_val (s : Finset α) (t : α → Finset β) :
    (s.biUnion t).1 = (s.1.bind fun a => (t a).1).dedup :=
  rfl
#align finset.bUnion_val Finset.biUnion_val

@[simp]
theorem biUnion_empty : Finset.biUnion ∅ t = ∅ :=
  rfl
#align finset.bUnion_empty Finset.biUnion_empty

@[simp]
theorem mem_biUnion {b : β} : b ∈ s.biUnion t ↔ ∃ a ∈ s, b ∈ t a := by
  simp only [mem_def, biUnion_val, mem_dedup, mem_bind, exists_prop]
  -- 🎉 no goals
#align finset.mem_bUnion Finset.mem_biUnion

@[simp, norm_cast]
theorem coe_biUnion : (s.biUnion t : Set β) = ⋃ x ∈ (s : Set α), t x := by
  simp [Set.ext_iff, mem_biUnion, Set.mem_iUnion, iff_self_iff, mem_coe, imp_true_iff]
  -- 🎉 no goals
#align finset.coe_bUnion Finset.coe_biUnion

@[simp]
theorem biUnion_insert [DecidableEq α] {a : α} : (insert a s).biUnion t = t a ∪ s.biUnion t :=
  ext fun x => by
    simp only [mem_biUnion, exists_prop, mem_union, mem_insert, or_and_right, exists_or,
      exists_eq_left]
#align finset.bUnion_insert Finset.biUnion_insert

-- ext $ λ x, by simp [or_and_distrib_right, exists_or_distrib]
theorem biUnion_congr (hs : s₁ = s₂) (ht : ∀ a ∈ s₁, t₁ a = t₂ a) : s₁.biUnion t₁ = s₂.biUnion t₂ :=
  ext fun x => by
    simp_rw [mem_biUnion]
    -- ⊢ (∃ a, a ∈ s₁ ∧ x ∈ t₁ a) ↔ ∃ a, a ∈ s₂ ∧ x ∈ t₂ a
    apply exists_congr
    -- ⊢ ∀ (a : α), a ∈ s₁ ∧ x ∈ t₁ a ↔ a ∈ s₂ ∧ x ∈ t₂ a
    simp (config := { contextual := true }) only [hs, and_congr_right_iff, ht, implies_true]
    -- 🎉 no goals
#align finset.bUnion_congr Finset.biUnion_congr

@[simp]
theorem disjiUnion_eq_biUnion (s : Finset α) (f : α → Finset β) (hf) :
    s.disjiUnion f hf = s.biUnion f :=
  eq_of_veq (s.disjiUnion f hf).nodup.dedup.symm
#align finset.disj_Union_eq_bUnion Finset.disjiUnion_eq_biUnion

theorem biUnion_subset {s' : Finset β} : s.biUnion t ⊆ s' ↔ ∀ x ∈ s, t x ⊆ s' := by
  simp only [subset_iff, mem_biUnion]
  -- ⊢ (∀ ⦃x : β⦄, (∃ a, a ∈ s ∧ x ∈ t a) → x ∈ s') ↔ ∀ (x : α), x ∈ s → ∀ ⦃x_1 : β …
  exact ⟨fun H a ha b hb => H ⟨a, ha, hb⟩, fun H b ⟨a, ha, hb⟩ => H a ha hb⟩
  -- 🎉 no goals
#align finset.bUnion_subset Finset.biUnion_subset

@[simp]
theorem singleton_biUnion {a : α} : Finset.biUnion {a} t = t a := by
  classical rw [← insert_emptyc_eq, biUnion_insert, biUnion_empty, union_empty]
  -- 🎉 no goals
#align finset.singleton_bUnion Finset.singleton_biUnion

theorem biUnion_inter (s : Finset α) (f : α → Finset β) (t : Finset β) :
    s.biUnion f ∩ t = s.biUnion fun x => f x ∩ t := by
  ext x
  -- ⊢ x ∈ Finset.biUnion s f ∩ t ↔ x ∈ Finset.biUnion s fun x => f x ∩ t
  simp only [mem_biUnion, mem_inter]
  -- ⊢ (∃ a, a ∈ s ∧ x ∈ f a) ∧ x ∈ t ↔ ∃ a, a ∈ s ∧ x ∈ f a ∧ x ∈ t
  tauto
  -- 🎉 no goals
#align finset.bUnion_inter Finset.biUnion_inter

theorem inter_biUnion (t : Finset β) (s : Finset α) (f : α → Finset β) :
    t ∩ s.biUnion f = s.biUnion fun x => t ∩ f x := by
  rw [inter_comm, biUnion_inter]
  -- ⊢ (Finset.biUnion s fun x => f x ∩ t) = Finset.biUnion s fun x => t ∩ f x
  simp [inter_comm]
  -- 🎉 no goals
#align finset.inter_bUnion Finset.inter_biUnion

theorem biUnion_biUnion [DecidableEq γ] (s : Finset α) (f : α → Finset β) (g : β → Finset γ) :
    (s.biUnion f).biUnion g = s.biUnion fun a => (f a).biUnion g := by
  ext
  -- ⊢ a✝ ∈ Finset.biUnion (Finset.biUnion s f) g ↔ a✝ ∈ Finset.biUnion s fun a =>  …
  simp only [Finset.mem_biUnion, exists_prop]
  -- ⊢ (∃ a, (∃ a_1, a_1 ∈ s ∧ a ∈ f a_1) ∧ a✝ ∈ g a) ↔ ∃ a, a ∈ s ∧ ∃ a_1, a_1 ∈ f …
  simp_rw [← exists_and_right, ← exists_and_left, and_assoc]
  -- ⊢ (∃ a x, x ∈ s ∧ a ∈ f x ∧ a✝ ∈ g a) ↔ ∃ a x, a ∈ s ∧ x ∈ f a ∧ a✝ ∈ g x
  rw [exists_comm]
  -- 🎉 no goals
#align finset.bUnion_bUnion Finset.biUnion_biUnion

theorem bind_toFinset [DecidableEq α] (s : Multiset α) (t : α → Multiset β) :
    (s.bind t).toFinset = s.toFinset.biUnion fun a => (t a).toFinset :=
  ext fun x => by simp only [Multiset.mem_toFinset, mem_biUnion, Multiset.mem_bind, exists_prop]
                  -- 🎉 no goals
#align finset.bind_to_finset Finset.bind_toFinset

theorem biUnion_mono (h : ∀ a ∈ s, t₁ a ⊆ t₂ a) : s.biUnion t₁ ⊆ s.biUnion t₂ := by
  have : ∀ b a, a ∈ s → b ∈ t₁ a → ∃ a : α, a ∈ s ∧ b ∈ t₂ a := fun b a ha hb =>
    ⟨a, ha, Finset.mem_of_subset (h a ha) hb⟩
  simpa only [subset_iff, mem_biUnion, exists_imp, and_imp, exists_prop]
  -- 🎉 no goals
#align finset.bUnion_mono Finset.biUnion_mono

theorem biUnion_subset_biUnion_of_subset_left (t : α → Finset β) (h : s₁ ⊆ s₂) :
    s₁.biUnion t ⊆ s₂.biUnion t := by
  intro x
  -- ⊢ x ∈ Finset.biUnion s₁ t → x ∈ Finset.biUnion s₂ t
  simp only [and_imp, mem_biUnion, exists_prop]
  -- ⊢ (∃ a, a ∈ s₁ ∧ x ∈ t a) → ∃ a, a ∈ s₂ ∧ x ∈ t a
  exact Exists.imp fun a ha => ⟨h ha.1, ha.2⟩
  -- 🎉 no goals
#align finset.bUnion_subset_bUnion_of_subset_left Finset.biUnion_subset_biUnion_of_subset_left

theorem subset_biUnion_of_mem (u : α → Finset β) {x : α} (xs : x ∈ s) : u x ⊆ s.biUnion u :=
  singleton_biUnion.superset.trans <|
    biUnion_subset_biUnion_of_subset_left u <| singleton_subset_iff.2 xs
#align finset.subset_bUnion_of_mem Finset.subset_biUnion_of_mem

@[simp]
theorem biUnion_subset_iff_forall_subset {α β : Type*} [DecidableEq β] {s : Finset α}
    {t : Finset β} {f : α → Finset β} : s.biUnion f ⊆ t ↔ ∀ x ∈ s, f x ⊆ t :=
  ⟨fun h _ hx => (subset_biUnion_of_mem f hx).trans h, fun h _ hx =>
    let ⟨_, ha₁, ha₂⟩ := mem_biUnion.mp hx
    h _ ha₁ ha₂⟩
#align finset.bUnion_subset_iff_forall_subset Finset.biUnion_subset_iff_forall_subset

@[simp]
theorem biUnion_singleton_eq_self [DecidableEq α] : s.biUnion (singleton : α → Finset α) = s :=
  ext fun x => by simp only [mem_biUnion, mem_singleton, exists_prop, exists_eq_right']
                  -- 🎉 no goals
#align finset.bUnion_singleton_eq_self Finset.biUnion_singleton_eq_self

theorem filter_biUnion (s : Finset α) (f : α → Finset β) (p : β → Prop) [DecidablePred p] :
    (s.biUnion f).filter p = s.biUnion fun a => (f a).filter p := by
  ext b
  -- ⊢ b ∈ filter p (Finset.biUnion s f) ↔ b ∈ Finset.biUnion s fun a => filter p ( …
  simp only [mem_biUnion, exists_prop, mem_filter]
  -- ⊢ (∃ a, a ∈ s ∧ b ∈ f a) ∧ p b ↔ ∃ a, a ∈ s ∧ b ∈ f a ∧ p b
  constructor
  -- ⊢ (∃ a, a ∈ s ∧ b ∈ f a) ∧ p b → ∃ a, a ∈ s ∧ b ∈ f a ∧ p b
  · rintro ⟨⟨a, ha, hba⟩, hb⟩
    -- ⊢ ∃ a, a ∈ s ∧ b ∈ f a ∧ p b
    exact ⟨a, ha, hba, hb⟩
    -- 🎉 no goals
  · rintro ⟨a, ha, hba, hb⟩
    -- ⊢ (∃ a, a ∈ s ∧ b ∈ f a) ∧ p b
    exact ⟨⟨a, ha, hba⟩, hb⟩
    -- 🎉 no goals
#align finset.filter_bUnion Finset.filter_biUnion

theorem biUnion_filter_eq_of_maps_to [DecidableEq α] {s : Finset α} {t : Finset β} {f : α → β}
    (h : ∀ x ∈ s, f x ∈ t) : (t.biUnion fun a => s.filter fun c => f c = a) = s := by
  simpa only [disjiUnion_eq_biUnion] using disjiUnion_filter_eq_of_maps_to h
  -- 🎉 no goals
#align finset.bUnion_filter_eq_of_maps_to Finset.biUnion_filter_eq_of_maps_to

theorem erase_biUnion (f : α → Finset β) (s : Finset α) (b : β) :
    (s.biUnion f).erase b = s.biUnion fun x => (f x).erase b := by
  ext a
  -- ⊢ a ∈ erase (Finset.biUnion s f) b ↔ a ∈ Finset.biUnion s fun x => erase (f x) b
  simp [Finset.mem_biUnion, iff_self_iff, exists_and_left, Finset.mem_erase]
  -- ⊢ (¬a = b ∧ ∃ a_1, a_1 ∈ s ∧ a ∈ f a_1) ↔ ∃ a_1, a_1 ∈ s ∧ ¬a = b ∧ a ∈ f a_1
  tauto
  -- 🎉 no goals
#align finset.erase_bUnion Finset.erase_biUnion

@[simp]
theorem biUnion_nonempty : (s.biUnion t).Nonempty ↔ ∃ x ∈ s, (t x).Nonempty := by
  simp only [Finset.Nonempty, mem_biUnion]
  -- ⊢ (∃ x a, a ∈ s ∧ x ∈ t a) ↔ ∃ x, x ∈ s ∧ ∃ x_1, x_1 ∈ t x
  rw [exists_swap]
  -- ⊢ (∃ y x, y ∈ s ∧ x ∈ t y) ↔ ∃ x, x ∈ s ∧ ∃ x_1, x_1 ∈ t x
  simp [exists_and_left]
  -- 🎉 no goals
#align finset.bUnion_nonempty Finset.biUnion_nonempty

theorem Nonempty.biUnion (hs : s.Nonempty) (ht : ∀ x ∈ s, (t x).Nonempty) :
    (s.biUnion t).Nonempty :=
  biUnion_nonempty.2 <| hs.imp fun x hx => ⟨hx, ht x hx⟩
#align finset.nonempty.bUnion Finset.Nonempty.biUnion

theorem disjoint_biUnion_left (s : Finset α) (f : α → Finset β) (t : Finset β) :
    Disjoint (s.biUnion f) t ↔ ∀ i ∈ s, Disjoint (f i) t := by
  classical
    refine' s.induction _ _
    · simp only [forall_mem_empty_iff, biUnion_empty, disjoint_empty_left]
    · intro i s his ih
      simp only [disjoint_union_left, biUnion_insert, his, forall_mem_insert, ih]
#align finset.disjoint_bUnion_left Finset.disjoint_biUnion_left

theorem disjoint_biUnion_right (s : Finset β) (t : Finset α) (f : α → Finset β) :
    Disjoint s (t.biUnion f) ↔ ∀ i ∈ t, Disjoint s (f i) := by
  simpa only [_root_.disjoint_comm] using disjoint_biUnion_left t f s
  -- 🎉 no goals
#align finset.disjoint_bUnion_right Finset.disjoint_biUnion_right

end BUnion

/-! ### choose -/


section Choose

variable (p : α → Prop) [DecidablePred p] (l : Finset α)

/-- Given a finset `l` and a predicate `p`, associate to a proof that there is a unique element of
`l` satisfying `p` this unique element, as an element of the corresponding subtype. -/
def chooseX (hp : ∃! a, a ∈ l ∧ p a) : { a // a ∈ l ∧ p a } :=
  Multiset.chooseX p l.val hp
#align finset.choose_x Finset.chooseX

/-- Given a finset `l` and a predicate `p`, associate to a proof that there is a unique element of
`l` satisfying `p` this unique element, as an element of the ambient type. -/
def choose (hp : ∃! a, a ∈ l ∧ p a) : α :=
  chooseX p l hp
#align finset.choose Finset.choose

theorem choose_spec (hp : ∃! a, a ∈ l ∧ p a) : choose p l hp ∈ l ∧ p (choose p l hp) :=
  (chooseX p l hp).property
#align finset.choose_spec Finset.choose_spec

theorem choose_mem (hp : ∃! a, a ∈ l ∧ p a) : choose p l hp ∈ l :=
  (choose_spec _ _ _).1
#align finset.choose_mem Finset.choose_mem

theorem choose_property (hp : ∃! a, a ∈ l ∧ p a) : p (choose p l hp) :=
  (choose_spec _ _ _).2
#align finset.choose_property Finset.choose_property

end Choose

section Pairwise

variable {s : Finset α}

theorem pairwise_subtype_iff_pairwise_finset' (r : β → β → Prop) (f : α → β) :
    Pairwise (r on fun x : s => f x) ↔ (s : Set α).Pairwise (r on f) :=
  pairwise_subtype_iff_pairwise_set (s : Set α) (r on f)
#align finset.pairwise_subtype_iff_pairwise_finset' Finset.pairwise_subtype_iff_pairwise_finset'

theorem pairwise_subtype_iff_pairwise_finset (r : α → α → Prop) :
    Pairwise (r on fun x : s => x) ↔ (s : Set α).Pairwise r :=
  pairwise_subtype_iff_pairwise_finset' r id
#align finset.pairwise_subtype_iff_pairwise_finset Finset.pairwise_subtype_iff_pairwise_finset

theorem pairwise_cons' {a : α} (ha : a ∉ s) (r : β → β → Prop) (f : α → β) :
    Pairwise (r on fun a : s.cons a ha => f a) ↔
    Pairwise (r on fun a : s => f a) ∧ ∀ b ∈ s, r (f a) (f b) ∧ r (f b) (f a) := by
  simp only [pairwise_subtype_iff_pairwise_finset', Finset.coe_cons, Set.pairwise_insert,
    Finset.mem_coe, and_congr_right_iff]
  exact fun _ =>
    ⟨fun h b hb =>
      h b hb <| by
        rintro rfl
        contradiction,
      fun h b hb _ => h b hb⟩
#align finset.pairwise_cons' Finset.pairwise_cons'

theorem pairwise_cons {a : α} (ha : a ∉ s) (r : α → α → Prop) :
    Pairwise (r on fun a : s.cons a ha => a) ↔
      Pairwise (r on fun a : s => a) ∧ ∀ b ∈ s, r a b ∧ r b a :=
  pairwise_cons' ha r id
#align finset.pairwise_cons Finset.pairwise_cons

end Pairwise

end Finset

namespace Equiv

/--
Inhabited types are equivalent to `Option β` for some `β` by identifying `default α` with `none`.
-/
def sigmaEquivOptionOfInhabited (α : Type u) [Inhabited α] [DecidableEq α] :
    Σβ : Type u, α ≃ Option β :=
  ⟨{ x : α // x ≠ default },
    { toFun := fun x : α => if h : x = default then none else some ⟨x, h⟩
      invFun := Option.elim' default (↑)
      left_inv := fun x => by
        dsimp only
        -- ⊢ Option.elim' default val (if h : x = default then none else some { val := x, …
        split_ifs <;> simp [*]
        -- ⊢ Option.elim' default val none = x
                      -- 🎉 no goals
                      -- 🎉 no goals
      right_inv := by
        rintro (_ | ⟨x, h⟩)
        -- ⊢ (fun x => if h : x = default then none else some { val := x, property := h } …
        · simp
          -- 🎉 no goals
        · dsimp only
          -- ⊢ (if h : Option.elim' default val (some { val := x, property := h }) = defaul …
          split_ifs with hi
          -- ⊢ False
          · simp [h] at hi
            -- 🎉 no goals
          · simp }⟩
            -- 🎉 no goals
#align equiv.sigma_equiv_option_of_inhabited Equiv.sigmaEquivOptionOfInhabited

end Equiv

namespace Multiset

variable [DecidableEq α]

theorem disjoint_toFinset {m1 m2 : Multiset α} :
    _root_.Disjoint m1.toFinset m2.toFinset ↔ m1.Disjoint m2 := by
  rw [Finset.disjoint_iff_ne]
  -- ⊢ (∀ (a : α), a ∈ toFinset m1 → ∀ (b : α), b ∈ toFinset m2 → a ≠ b) ↔ Disjoint …
  refine' ⟨fun h a ha1 ha2 => _, _⟩
  -- ⊢ False
  · rw [← Multiset.mem_toFinset] at ha1 ha2
    -- ⊢ False
    exact h _ ha1 _ ha2 rfl
    -- 🎉 no goals
  · rintro h a ha b hb rfl
    -- ⊢ False
    rw [Multiset.mem_toFinset] at ha hb
    -- ⊢ False
    exact h ha hb
    -- 🎉 no goals
#align multiset.disjoint_to_finset Multiset.disjoint_toFinset

end Multiset

namespace List

variable [DecidableEq α] {l l' : List α}

theorem disjoint_toFinset_iff_disjoint : _root_.Disjoint l.toFinset l'.toFinset ↔ l.Disjoint l' :=
  Multiset.disjoint_toFinset
#align list.disjoint_to_finset_iff_disjoint List.disjoint_toFinset_iff_disjoint

end List

-- Assert that we define `Finset` without the material on `List.sublists`.
-- Note that we cannot use `List.sublists` itself as that is defined very early.
assert_not_exists List.sublistsLen
assert_not_exists Multiset.powerset
