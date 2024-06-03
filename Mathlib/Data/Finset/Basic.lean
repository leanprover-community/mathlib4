/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Multiset.FinsetOps
import Mathlib.Logic.Equiv.Set
import Mathlib.Order.Directed
import Mathlib.Order.Interval.Set.Basic

#align_import data.finset.basic from "leanprover-community/mathlib"@"442a83d738cb208d3600056c489be16900ba701d"

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

  1. `∑ i ∈ (s : Finset α), f i`;
  2. `∏ i ∈ (s : Finset α), f i`.

Lean refers to these operations as big operators.
More information can be found in `Mathlib.Algebra.BigOperators.Group.Finset`.

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

### Predicates on finsets

* `Disjoint`: defined via the lattice structure on finsets; two sets are disjoint if their
  intersection is empty.
* `Finset.Nonempty`: A finset is nonempty if it has elements. This is equivalent to saying `s ≠ ∅`.

### Equivalences between finsets

* The `Mathlib.Data.Equiv` files describe a general type of equivalence, so look in there for any
  lemmas. There is some API for rewriting sums and products from `s` to `t` given that `s ≃ t`.
  TODO: examples

## Tags

finite sets, finset

-/

-- Assert that we define `Finset` without the material on `List.sublists`.
-- Note that we cannot use `List.sublists` itself as that is defined very early.
assert_not_exists List.sublistsLen
assert_not_exists Multiset.Powerset

assert_not_exists CompleteLattice

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

@[simp] lemma forall_mem_not_eq {s : Finset α} {a : α} : (∀ b ∈ s, ¬ a = b) ↔ a ∉ s := by aesop
@[simp] lemma forall_mem_not_eq' {s : Finset α} {a : α} : (∀ b ∈ s, ¬ b = a) ↔ a ∉ s := by aesop

/-! ### set coercion -/

-- Porting note (#11445): new definition
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

-- Porting note (#10618): @[simp] can prove this
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

-- Porting note (#10618): @[simp] can prove this
protected theorem forall_coe {α : Type*} (s : Finset α) (p : s → Prop) :
    (∀ x : s, p x) ↔ ∀ (x : α) (h : x ∈ s), p ⟨x, h⟩ :=
  Subtype.forall
#align finset.forall_coe Finset.forall_coe

-- Porting note (#10618): @[simp] can prove this
protected theorem exists_coe {α : Type*} (s : Finset α) (p : s → Prop) :
    (∃ x : s, p x) ↔ ∃ (x : α) (h : x ∈ s), p ⟨x, h⟩ :=
  Subtype.exists
#align finset.exists_coe Finset.exists_coe

instance PiFinsetCoe.canLift (ι : Type*) (α : ι → Type*) [_ne : ∀ i, Nonempty (α i)]
    (s : Finset ι) : CanLift (∀ i : s, α i) (∀ i, α i) (fun f i => f i) fun _ => True :=
  PiSubtype.canLift ι α (· ∈ s)
#align finset.pi_finset_coe.can_lift Finset.PiFinsetCoe.canLift

instance PiFinsetCoe.canLift' (ι α : Type*) [_ne : Nonempty α] (s : Finset ι) :
    CanLift (s → α) (ι → α) (fun f i => f i) fun _ => True :=
  PiFinsetCoe.canLift ι (fun _ => α) s
#align finset.pi_finset_coe.can_lift' Finset.PiFinsetCoe.canLift'

instance FinsetCoe.canLift (s : Finset α) : CanLift α s (↑) fun a => a ∈ s where
  prf a ha := ⟨⟨a, ha⟩, rfl⟩
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

instance : IsTrans (Finset α) (· ⊆ ·) :=
  show IsTrans (Finset α) (· ≤ ·) by infer_instance

instance : IsAntisymm (Finset α) (· ⊆ ·) :=
  show IsAntisymm (Finset α) (· ≤ ·) by infer_instance

instance : IsIrrefl (Finset α) (· ⊂ ·) :=
  show IsIrrefl (Finset α) (· < ·) by infer_instance

instance : IsTrans (Finset α) (· ⊂ ·) :=
  show IsTrans (Finset α) (· < ·) by infer_instance

instance : IsAsymm (Finset α) (· ⊂ ·) :=
  show IsAsymm (Finset α) (· < ·) by infer_instance

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
#align finset.coe_ssubset Finset.coe_ssubset

@[simp]
theorem val_lt_iff {s₁ s₂ : Finset α} : s₁.1 < s₂.1 ↔ s₁ ⊂ s₂ :=
  and_congr val_le_iff <| not_congr val_le_iff
#align finset.val_lt_iff Finset.val_lt_iff

lemma val_strictMono : StrictMono (val : Finset α → Multiset α) := fun _ _ ↦ val_lt_iff.2

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
protected def Nonempty (s : Finset α) : Prop := ∃ x : α, x ∈ s
#align finset.nonempty Finset.Nonempty

-- Porting note: Much longer than in Lean3
instance decidableNonempty {s : Finset α} : Decidable s.Nonempty :=
  Quotient.recOnSubsingleton (motive := fun s : Multiset α => Decidable (∃ a, a ∈ s)) s.1
    (fun l : List α =>
      match l with
      | [] => isFalse <| by simp
      | a::l => isTrue ⟨a, by simp⟩)
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

theorem Nonempty.exists_mem {s : Finset α} (h : s.Nonempty) : ∃ x : α, x ∈ s :=
  h
#align finset.nonempty.bex Finset.Nonempty.exists_mem
@[deprecated] alias Nonempty.bex := Nonempty.exists_mem -- 2024-03-23

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
#align finset.coe_empty Finset.coe_empty

@[simp, norm_cast]
theorem coe_eq_empty {s : Finset α} : (s : Set α) = ∅ ↔ s = ∅ := by rw [← coe_empty, coe_inj]
#align finset.coe_eq_empty Finset.coe_eq_empty

-- Porting note: Left-hand side simplifies @[simp]
theorem isEmpty_coe_sort {s : Finset α} : IsEmpty (s : Type _) ↔ s = ∅ := by
  simpa using @Set.isEmpty_coe_sort α s
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
  rfl
#align finset.val_eq_singleton_iff Finset.val_eq_singleton_iff

theorem singleton_injective : Injective (singleton : α → Finset α) := fun _a _b h =>
  mem_singleton.1 (h ▸ mem_singleton_self _)
#align finset.singleton_injective Finset.singleton_injective

@[simp]
theorem singleton_inj : ({a} : Finset α) = {b} ↔ a = b :=
  singleton_injective.eq_iff
#align finset.singleton_inj Finset.singleton_inj

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]
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
  simp
#align finset.coe_singleton Finset.coe_singleton

@[simp, norm_cast]
theorem coe_eq_singleton {s : Finset α} {a : α} : (s : Set α) = {a} ↔ s = {a} := by
  rw [← coe_singleton, coe_inj]
#align finset.coe_eq_singleton Finset.coe_eq_singleton

@[norm_cast]
lemma coe_subset_singleton : (s : Set α) ⊆ {a} ↔ s ⊆ {a} := by rw [← coe_subset, coe_singleton]

@[norm_cast]
lemma singleton_subset_coe : {a} ⊆ (s : Set α) ↔ {a} ⊆ s := by rw [← coe_subset, coe_singleton]

theorem eq_singleton_iff_unique_mem {s : Finset α} {a : α} : s = {a} ↔ a ∈ s ∧ ∀ x ∈ s, x = a := by
  constructor <;> intro t
  · rw [t]
    exact ⟨Finset.mem_singleton_self _, fun _ => Finset.mem_singleton.1⟩
  · ext
    rw [Finset.mem_singleton]
    exact ⟨t.right _, fun r => r.symm ▸ t.left⟩
#align finset.eq_singleton_iff_unique_mem Finset.eq_singleton_iff_unique_mem

theorem eq_singleton_iff_nonempty_unique_mem {s : Finset α} {a : α} :
    s = {a} ↔ s.Nonempty ∧ ∀ x ∈ s, x = a := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨hne, h_uniq⟩
    rw [eq_singleton_iff_unique_mem]
    refine ⟨?_, h_uniq⟩
    rw [← h_uniq hne.choose hne.choose_spec]
    exact hne.choose_spec
#align finset.eq_singleton_iff_nonempty_unique_mem Finset.eq_singleton_iff_nonempty_unique_mem

theorem nonempty_iff_eq_singleton_default [Unique α] {s : Finset α} :
    s.Nonempty ↔ s = {default} := by
  simp [eq_singleton_iff_nonempty_unique_mem, eq_iff_true_of_subsingleton]
#align finset.nonempty_iff_eq_singleton_default Finset.nonempty_iff_eq_singleton_default

alias ⟨Nonempty.eq_singleton_default, _⟩ := nonempty_iff_eq_singleton_default
#align finset.nonempty.eq_singleton_default Finset.Nonempty.eq_singleton_default

theorem singleton_iff_unique_mem (s : Finset α) : (∃ a, s = {a}) ↔ ∃! a, a ∈ s := by
  simp only [eq_singleton_iff_unique_mem, ExistsUnique]
#align finset.singleton_iff_unique_mem Finset.singleton_iff_unique_mem

theorem singleton_subset_set_iff {s : Set α} {a : α} : ↑({a} : Finset α) ⊆ s ↔ a ∈ s := by
  rw [coe_singleton, Set.singleton_subset_iff]
#align finset.singleton_subset_set_iff Finset.singleton_subset_set_iff

@[simp]
theorem singleton_subset_iff {s : Finset α} {a : α} : {a} ⊆ s ↔ a ∈ s :=
  singleton_subset_set_iff
#align finset.singleton_subset_iff Finset.singleton_subset_iff

@[simp]
theorem subset_singleton_iff {s : Finset α} {a : α} : s ⊆ {a} ↔ s = ∅ ∨ s = {a} := by
  rw [← coe_subset, coe_singleton, Set.subset_singleton_iff_eq, coe_eq_empty, coe_eq_singleton]
#align finset.subset_singleton_iff Finset.subset_singleton_iff

theorem singleton_subset_singleton : ({a} : Finset α) ⊆ {b} ↔ a = b := by simp
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
#align finset.ssubset_singleton_iff Finset.ssubset_singleton_iff

theorem eq_empty_of_ssubset_singleton {s : Finset α} {x : α} (hs : s ⊂ {x}) : s = ∅ :=
  ssubset_singleton_iff.1 hs
#align finset.eq_empty_of_ssubset_singleton Finset.eq_empty_of_ssubset_singleton

/-- A finset is nontrivial if it has at least two elements. -/
protected abbrev Nontrivial (s : Finset α) : Prop := (s : Set α).Nontrivial
#align finset.nontrivial Finset.Nontrivial

@[simp]
theorem not_nontrivial_empty : ¬ (∅ : Finset α).Nontrivial := by simp [Finset.Nontrivial]
#align finset.not_nontrivial_empty Finset.not_nontrivial_empty

@[simp]
theorem not_nontrivial_singleton : ¬ ({a} : Finset α).Nontrivial := by simp [Finset.Nontrivial]
#align finset.not_nontrivial_singleton Finset.not_nontrivial_singleton

theorem Nontrivial.ne_singleton (hs : s.Nontrivial) : s ≠ {a} := by
  rintro rfl; exact not_nontrivial_singleton hs
#align finset.nontrivial.ne_singleton Finset.Nontrivial.ne_singleton

nonrec lemma Nontrivial.exists_ne (hs : s.Nontrivial) (a : α) : ∃ b ∈ s, b ≠ a := hs.exists_ne _

theorem eq_singleton_or_nontrivial (ha : a ∈ s) : s = {a} ∨ s.Nontrivial := by
  rw [← coe_eq_singleton]; exact Set.eq_singleton_or_nontrivial ha
#align finset.eq_singleton_or_nontrivial Finset.eq_singleton_or_nontrivial

theorem nontrivial_iff_ne_singleton (ha : a ∈ s) : s.Nontrivial ↔ s ≠ {a} :=
  ⟨Nontrivial.ne_singleton, (eq_singleton_or_nontrivial ha).resolve_left⟩
#align finset.nontrivial_iff_ne_singleton Finset.nontrivial_iff_ne_singleton

theorem Nonempty.exists_eq_singleton_or_nontrivial : s.Nonempty → (∃ a, s = {a}) ∨ s.Nontrivial :=
  fun ⟨a, ha⟩ => (eq_singleton_or_nontrivial ha).imp_left <| Exists.intro a
#align finset.nonempty.exists_eq_singleton_or_nontrivial Finset.Nonempty.exists_eq_singleton_or_nontrivial

instance instNontrivial [Nonempty α] : Nontrivial (Finset α) :=
  ‹Nonempty α›.elim fun a => ⟨⟨{a}, ∅, singleton_ne_empty _⟩⟩
#align finset.nontrivial' Finset.instNontrivial

instance [IsEmpty α] : Unique (Finset α) where
  default := ∅
  uniq _ := eq_empty_of_forall_not_mem isEmptyElim

instance (i : α) : Unique ({i} : Finset α) where
  default := ⟨i, mem_singleton_self i⟩
  uniq j := Subtype.ext <| mem_singleton.mp j.2

set_option backward.synthInstance.canonInstances false in -- See https://github.com/leanprover-community/mathlib4/issues/12532
@[simp]
lemma default_singleton (i : α) : ((default : ({i} : Finset α)) : α) = i := rfl

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

theorem mem_cons_of_mem {a b : α} {s : Finset α} {hb : b ∉ s} (ha : a ∈ s) : a ∈ cons b s hb :=
  Multiset.mem_cons_of_mem ha

-- Porting note (#10618): @[simp] can prove this
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
theorem cons_empty (a : α) : cons a ∅ (not_mem_empty _) = {a} := rfl
#align finset.cons_empty Finset.cons_empty

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]
theorem nonempty_cons (h : a ∉ s) : (cons a s h).Nonempty :=
  ⟨a, mem_cons.2 <| Or.inl rfl⟩
#align finset.nonempty_cons Finset.nonempty_cons

@[simp]
theorem nonempty_mk {m : Multiset α} {hm} : (⟨m, hm⟩ : Finset α).Nonempty ↔ m ≠ 0 := by
  induction m using Multiset.induction_on <;> simp
#align finset.nonempty_mk Finset.nonempty_mk

@[simp]
theorem coe_cons {a s h} : (@cons α a s h : Set α) = insert a (s : Set α) := by
  ext
  simp
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
#align finset.cons_subset_cons Finset.cons_subset_cons

theorem ssubset_iff_exists_cons_subset : s ⊂ t ↔ ∃ (a : _) (h : a ∉ s), s.cons a h ⊆ t := by
  refine ⟨fun h => ?_, fun ⟨a, ha, h⟩ => ssubset_of_ssubset_of_subset (ssubset_cons _) h⟩
  obtain ⟨a, hs, ht⟩ := not_subset.1 h.2
  exact ⟨a, ht, cons_subset.2 ⟨hs, h.subset⟩⟩
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
#align finset.disjoint_right Finset.disjoint_right

theorem disjoint_iff_ne : Disjoint s t ↔ ∀ a ∈ s, ∀ b ∈ t, a ≠ b := by
  simp only [disjoint_left, imp_not_comm, forall_eq']
#align finset.disjoint_iff_ne Finset.disjoint_iff_ne

@[simp]
theorem disjoint_val : s.1.Disjoint t.1 ↔ Disjoint s t :=
  disjoint_left.symm
#align finset.disjoint_val Finset.disjoint_val

theorem _root_.Disjoint.forall_ne_finset (h : Disjoint s t) (ha : a ∈ s) (hb : b ∈ t) : a ≠ b :=
  disjoint_iff_ne.1 h _ ha _ hb
#align disjoint.forall_ne_finset Disjoint.forall_ne_finset

theorem not_disjoint_iff : ¬Disjoint s t ↔ ∃ a, a ∈ s ∧ a ∈ t :=
  disjoint_left.not.trans <| not_forall.trans <| exists_congr fun _ => by
    rw [Classical.not_imp, not_not]
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
#align finset.disjoint_singleton_left Finset.disjoint_singleton_left

@[simp]
theorem disjoint_singleton_right : Disjoint s (singleton a) ↔ a ∉ s :=
  disjoint_comm.trans disjoint_singleton_left
#align finset.disjoint_singleton_right Finset.disjoint_singleton_right

-- Porting note: Left-hand side simplifies @[simp]
theorem disjoint_singleton : Disjoint ({a} : Finset α) {b} ↔ a ≠ b := by
  rw [disjoint_singleton_left, mem_singleton]
#align finset.disjoint_singleton Finset.disjoint_singleton

theorem disjoint_self_iff_empty (s : Finset α) : Disjoint s s ↔ s = ∅ :=
  disjoint_self
#align finset.disjoint_self_iff_empty Finset.disjoint_self_iff_empty

@[simp, norm_cast]
theorem disjoint_coe : Disjoint (s : Set α) t ↔ Disjoint s t := by
  simp only [Finset.disjoint_left, Set.disjoint_left, mem_coe]
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
#align finset.mem_disj_union Finset.mem_disjUnion

@[simp, norm_cast]
theorem coe_disjUnion {s t : Finset α} (h : Disjoint s t) :
    (disjUnion s t h : Set α) = (s : Set α) ∪ t :=
  Set.ext <| by simp

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
#align finset.insert_val' Finset.insert_val'

theorem insert_val_of_not_mem {a : α} {s : Finset α} (h : a ∉ s) : (insert a s).1 = a ::ₘ s.1 := by
  rw [insert_val, ndinsert_of_not_mem h]
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

/-- A version of `IsLawfulSingleton.insert_emptyc_eq` that works with `dsimp`. -/
@[simp, nolint simpNF] lemma insert_empty : insert a (∅ : Finset α) = {a} := rfl

@[simp]
theorem cons_eq_insert (a s h) : @cons α a s h = insert a s :=
  ext fun a => by simp
#align finset.cons_eq_insert Finset.cons_eq_insert

@[simp, norm_cast]
theorem coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (insert a s : Set α) :=
  Set.ext fun x => by simp only [mem_coe, mem_insert, Set.mem_insert_iff]
#align finset.coe_insert Finset.coe_insert

theorem mem_insert_coe {s : Finset α} {x y : α} : x ∈ insert y s ↔ x ∈ insert y (s : Set α) := by
  simp
#align finset.mem_insert_coe Finset.mem_insert_coe

instance : IsLawfulSingleton α (Finset α) :=
  ⟨fun a => by ext; simp⟩

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

-- Porting note (#10618): @[simp] can prove this
theorem pair_eq_singleton (a : α) : ({a, a} : Finset α) = {a} :=
  insert_eq_of_mem <| mem_singleton_self _
#align finset.pair_eq_singleton Finset.pair_eq_singleton

theorem Insert.comm (a b : α) (s : Finset α) : insert a (insert b s) = insert b (insert a s) :=
  ext fun x => by simp only [mem_insert, or_left_comm]
#align finset.insert.comm Finset.Insert.comm

-- Porting note (#10618): @[simp] can prove this
@[norm_cast]
theorem coe_pair {a b : α} : (({a, b} : Finset α) : Set α) = {a, b} := by
  ext
  simp
#align finset.coe_pair Finset.coe_pair

@[simp, norm_cast]
theorem coe_eq_pair {s : Finset α} {a b : α} : (s : Set α) = {a, b} ↔ s = {a, b} := by
  rw [← coe_pair, coe_inj]
#align finset.coe_eq_pair Finset.coe_eq_pair

theorem pair_comm (a b : α) : ({a, b} : Finset α) = {b, a} :=
  Insert.comm a b ∅
#align finset.pair_comm Finset.pair_comm

-- Porting note (#10618): @[simp] can prove this
theorem insert_idem (a : α) (s : Finset α) : insert a (insert a s) = insert a s :=
  ext fun x => by simp only [mem_insert, ← or_assoc, or_self_iff]
#align finset.insert_idem Finset.insert_idem

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]
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
  simp [h]
#align finset.ne_insert_of_not_mem Finset.ne_insert_of_not_mem

theorem insert_subset_iff : insert a s ⊆ t ↔ a ∈ t ∧ s ⊆ t := by
  simp only [subset_iff, mem_insert, forall_eq, or_imp, forall_and]
#align finset.insert_subset Finset.insert_subset_iff

theorem insert_subset (ha : a ∈ t) (hs : s ⊆ t) : insert a s ⊆ t :=
  insert_subset_iff.mpr ⟨ha,hs⟩

@[simp] theorem subset_insert (a : α) (s : Finset α) : s ⊆ insert a s := fun _b => mem_insert_of_mem
#align finset.subset_insert Finset.subset_insert

@[gcongr]
theorem insert_subset_insert (a : α) {s t : Finset α} (h : s ⊆ t) : insert a s ⊆ insert a t :=
  insert_subset_iff.2 ⟨mem_insert_self _ _, Subset.trans h (subset_insert _ _)⟩
#align finset.insert_subset_insert Finset.insert_subset_insert

@[simp] lemma insert_subset_insert_iff (ha : a ∉ s) : insert a s ⊆ insert a t ↔ s ⊆ t := by
  simp_rw [← coe_subset]; simp [-coe_subset, ha]

theorem insert_inj (ha : a ∉ s) : insert a s = insert b s ↔ a = b :=
  ⟨fun h => eq_of_not_mem_of_mem_insert (h.subst <| mem_insert_self _ _) ha, congr_arg (insert · s)⟩
#align finset.insert_inj Finset.insert_inj

theorem insert_inj_on (s : Finset α) : Set.InjOn (fun a => insert a s) sᶜ := fun _ h _ _ =>
  (insert_inj h).1
#align finset.insert_inj_on Finset.insert_inj_on

theorem ssubset_iff : s ⊂ t ↔ ∃ a ∉ s, insert a s ⊆ t := mod_cast @Set.ssubset_iff_insert α s t
#align finset.ssubset_iff Finset.ssubset_iff

theorem ssubset_insert (h : a ∉ s) : s ⊂ insert a s :=
  ssubset_iff.mpr ⟨a, h, Subset.rfl⟩
#align finset.ssubset_insert Finset.ssubset_insert

@[elab_as_elim]
theorem cons_induction {α : Type*} {p : Finset α → Prop} (empty : p ∅)
    (cons : ∀ (a : α) (s : Finset α) (h : a ∉ s), p s → p (cons a s h)) : ∀ s, p s
  | ⟨s, nd⟩ => by
    induction s using Multiset.induction with
    | empty => exact empty
    | cons a s IH =>
      rw [mk_cons nd]
      exact cons a _ _ (IH _)
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
    (singleton : ∀ a, p {a} (singleton_nonempty _))
    (cons : ∀ a s (h : a ∉ s) (hs), p s hs → p (Finset.cons a s h) (nonempty_cons h))
    {s : Finset α} (hs : s.Nonempty) : p s hs := by
  induction s using Finset.cons_induction with
  | empty => exact (not_nonempty_empty hs).elim
  | cons a t ha h =>
    obtain rfl | ht := t.eq_empty_or_nonempty
    · exact singleton a
    · exact cons a t ha ht (h ht)
#align finset.nonempty.cons_induction Finset.Nonempty.cons_induction

lemma Nonempty.exists_cons_eq (hs : s.Nonempty) : ∃ t a ha, cons a t ha = s :=
  hs.cons_induction (fun a ↦ ⟨∅, a, _, cons_empty _⟩) fun _ _ _ _ _ ↦ ⟨_, _, _, rfl⟩

/-- Inserting an element to a finite set is equivalent to the option type. -/
def subtypeInsertEquivOption {t : Finset α} {x : α} (h : x ∉ t) :
    { i // i ∈ insert x t } ≃ Option { i // i ∈ t } := by
  refine'
    { toFun := fun y => if h : ↑y = x then none else some ⟨y, (mem_insert.mp y.2).resolve_left h⟩
      invFun := fun y => (y.elim ⟨x, mem_insert_self _ _⟩) fun z => ⟨z, mem_insert_of_mem z.2⟩.. }
  · intro y
    by_cases h : ↑y = x
    · simp only [Subtype.ext_iff, h, Option.elim, dif_pos, Subtype.coe_mk]
    · simp only [h, Option.elim, dif_neg, not_false_iff, Subtype.coe_eta, Subtype.coe_mk]
  · rintro (_ | y)
    · simp only [Option.elim, dif_pos]
    · have : ↑y ≠ x := by
        rintro ⟨⟩
        exact h y.2
      simp only [this, Option.elim, Subtype.eta, dif_neg, not_false_iff, Subtype.coe_mk]
#align finset.subtype_insert_equiv_option Finset.subtypeInsertEquivOption

@[simp]
theorem disjoint_insert_left : Disjoint (insert a s) t ↔ a ∉ t ∧ Disjoint s t := by
  simp only [disjoint_left, mem_insert, or_imp, forall_and, forall_eq]
#align finset.disjoint_insert_left Finset.disjoint_insert_left

@[simp]
theorem disjoint_insert_right : Disjoint s (insert a t) ↔ a ∉ s ∧ Disjoint s t :=
  disjoint_comm.trans <| by rw [disjoint_insert_left, _root_.disjoint_comm]
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

@[gcongr]
theorem union_subset_union (hsu : s ⊆ u) (htv : t ⊆ v) : s ∪ t ⊆ u ∪ v :=
  sup_le_sup (le_iff_subset.2 hsu) htv
#align finset.union_subset_union Finset.union_subset_union

@[gcongr]
theorem union_subset_union_left (h : s₁ ⊆ s₂) : s₁ ∪ t ⊆ s₂ ∪ t :=
  union_subset_union h Subset.rfl
#align finset.union_subset_union_left Finset.union_subset_union_left

@[gcongr]
theorem union_subset_union_right (h : t₁ ⊆ t₂) : s ∪ t₁ ⊆ s ∪ t₂ :=
  union_subset_union Subset.rfl h
#align finset.union_subset_union_right Finset.union_subset_union_right

theorem union_comm (s₁ s₂ : Finset α) : s₁ ∪ s₂ = s₂ ∪ s₁ := sup_comm _ _
#align finset.union_comm Finset.union_comm

instance : Std.Commutative (α := Finset α) (· ∪ ·) :=
  ⟨union_comm⟩

@[simp]
theorem union_assoc (s₁ s₂ s₃ : Finset α) : s₁ ∪ s₂ ∪ s₃ = s₁ ∪ (s₂ ∪ s₃) := sup_assoc _ _ _
#align finset.union_assoc Finset.union_assoc

instance : Std.Associative (α := Finset α) (· ∪ ·) :=
  ⟨union_assoc⟩

@[simp]
theorem union_idempotent (s : Finset α) : s ∪ s = s := sup_idem _
#align finset.union_idempotent Finset.union_idempotent

instance : Std.IdempotentOp (α := Finset α) (· ∪ ·) :=
  ⟨union_idempotent⟩

theorem union_subset_left (h : s ∪ t ⊆ u) : s ⊆ u :=
  (subset_union_left _ _).trans h
#align finset.union_subset_left Finset.union_subset_left

theorem union_subset_right {s t u : Finset α} (h : s ∪ t ⊆ u) : t ⊆ u :=
  Subset.trans (subset_union_right _ _) h
#align finset.union_subset_right Finset.union_subset_right

theorem union_left_comm (s t u : Finset α) : s ∪ (t ∪ u) = t ∪ (s ∪ u) :=
  ext fun _ => by simp only [mem_union, or_left_comm]
#align finset.union_left_comm Finset.union_left_comm

theorem union_right_comm (s t u : Finset α) : s ∪ t ∪ u = s ∪ u ∪ t :=
  ext fun x => by simp only [mem_union, or_assoc, @or_comm (x ∈ t)]
#align finset.union_right_comm Finset.union_right_comm

theorem union_self (s : Finset α) : s ∪ s = s :=
  union_idempotent s
#align finset.union_self Finset.union_self

@[simp]
theorem union_empty (s : Finset α) : s ∪ ∅ = s :=
  ext fun x => mem_union.trans <| by simp
#align finset.union_empty Finset.union_empty

@[simp]
theorem empty_union (s : Finset α) : ∅ ∪ s = s :=
  ext fun x => mem_union.trans <| by simp
#align finset.empty_union Finset.empty_union

@[aesop unsafe apply (rule_sets := [finsetNonempty])]
theorem Nonempty.inl {s t : Finset α} (h : s.Nonempty) : (s ∪ t).Nonempty :=
  h.mono <| subset_union_left s t

@[aesop unsafe apply (rule_sets := [finsetNonempty])]
theorem Nonempty.inr {s t : Finset α} (h : t.Nonempty) : (s ∪ t).Nonempty :=
  h.mono <| subset_union_right s t

theorem insert_eq (a : α) (s : Finset α) : insert a s = {a} ∪ s :=
  rfl
#align finset.insert_eq Finset.insert_eq

@[simp]
theorem insert_union (a : α) (s t : Finset α) : insert a s ∪ t = insert a (s ∪ t) := by
  simp only [insert_eq, union_assoc]
#align finset.insert_union Finset.insert_union

@[simp]
theorem union_insert (a : α) (s t : Finset α) : s ∪ insert a t = insert a (s ∪ t) := by
  simp only [insert_eq, union_left_comm]
#align finset.union_insert Finset.union_insert

theorem insert_union_distrib (a : α) (s t : Finset α) :
    insert a (s ∪ t) = insert a s ∪ insert a t := by
  simp only [insert_union, union_insert, insert_idem]
#align finset.insert_union_distrib Finset.insert_union_distrib

@[simp] lemma union_eq_left : s ∪ t = s ↔ t ⊆ s := sup_eq_left
#align finset.union_eq_left_iff_subset Finset.union_eq_left

@[simp] lemma left_eq_union : s = s ∪ t ↔ t ⊆ s := by rw [eq_comm, union_eq_left]
#align finset.left_eq_union_iff_subset Finset.left_eq_union

@[simp] lemma union_eq_right : s ∪ t = t ↔ s ⊆ t := sup_eq_right
#align finset.union_eq_right_iff_subset Finset.union_eq_right

@[simp] lemma right_eq_union : s = t ∪ s ↔ t ⊆ s := by rw [eq_comm, union_eq_right]
#align finset.right_eq_union_iff_subset Finset.right_eq_union

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
#align finset.disjoint_union_left Finset.disjoint_union_left

@[simp]
theorem disjoint_union_right : Disjoint s (t ∪ u) ↔ Disjoint s t ∧ Disjoint s u := by
  simp only [disjoint_right, mem_union, or_imp, forall_and]
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
  refine Finset.induction_on b empty_right fun x s _xs hi => symm ?_
  rw [Finset.insert_eq]
  apply union_of _ (symm hi)
  refine Finset.induction_on a empty_right fun a t _ta hi => symm ?_
  rw [Finset.insert_eq]
  exact union_of singletons (symm hi)
#align finset.induction_on_union Finset.induction_on_union

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
#align finset.subset_inter Finset.subset_inter

@[simp, norm_cast]
theorem coe_inter (s₁ s₂ : Finset α) : ↑(s₁ ∩ s₂) = (s₁ ∩ s₂ : Set α) :=
  Set.ext fun _ => mem_inter
#align finset.coe_inter Finset.coe_inter

@[simp]
theorem union_inter_cancel_left {s t : Finset α} : (s ∪ t) ∩ s = s := by
  rw [← coe_inj, coe_inter, coe_union, Set.union_inter_cancel_left]
#align finset.union_inter_cancel_left Finset.union_inter_cancel_left

@[simp]
theorem union_inter_cancel_right {s t : Finset α} : (s ∪ t) ∩ t = t := by
  rw [← coe_inj, coe_inter, coe_union, Set.union_inter_cancel_right]
#align finset.union_inter_cancel_right Finset.union_inter_cancel_right

theorem inter_comm (s₁ s₂ : Finset α) : s₁ ∩ s₂ = s₂ ∩ s₁ :=
  ext fun _ => by simp only [mem_inter, and_comm]
#align finset.inter_comm Finset.inter_comm

@[simp]
theorem inter_assoc (s₁ s₂ s₃ : Finset α) : s₁ ∩ s₂ ∩ s₃ = s₁ ∩ (s₂ ∩ s₃) :=
  ext fun _ => by simp only [mem_inter, and_assoc]
#align finset.inter_assoc Finset.inter_assoc

theorem inter_left_comm (s₁ s₂ s₃ : Finset α) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
  ext fun _ => by simp only [mem_inter, and_left_comm]
#align finset.inter_left_comm Finset.inter_left_comm

theorem inter_right_comm (s₁ s₂ s₃ : Finset α) : s₁ ∩ s₂ ∩ s₃ = s₁ ∩ s₃ ∩ s₂ :=
  ext fun _ => by simp only [mem_inter, and_right_comm]
#align finset.inter_right_comm Finset.inter_right_comm

@[simp]
theorem inter_self (s : Finset α) : s ∩ s = s :=
  ext fun _ => mem_inter.trans <| and_self_iff
#align finset.inter_self Finset.inter_self

@[simp]
theorem inter_empty (s : Finset α) : s ∩ ∅ = ∅ :=
  ext fun _ => mem_inter.trans <| by simp
#align finset.inter_empty Finset.inter_empty

@[simp]
theorem empty_inter (s : Finset α) : ∅ ∩ s = ∅ :=
  ext fun _ => mem_inter.trans <| by simp
#align finset.empty_inter Finset.empty_inter

@[simp]
theorem inter_union_self (s t : Finset α) : s ∩ (t ∪ s) = s := by
  rw [inter_comm, union_inter_cancel_right]
#align finset.inter_union_self Finset.inter_union_self

@[simp]
theorem insert_inter_of_mem {s₁ s₂ : Finset α} {a : α} (h : a ∈ s₂) :
    insert a s₁ ∩ s₂ = insert a (s₁ ∩ s₂) :=
  ext fun x => by
    have : x = a ∨ x ∈ s₂ ↔ x ∈ s₂ := or_iff_right_of_imp <| by rintro rfl; exact h
    simp only [mem_inter, mem_insert, or_and_left, this]
#align finset.insert_inter_of_mem Finset.insert_inter_of_mem

@[simp]
theorem inter_insert_of_mem {s₁ s₂ : Finset α} {a : α} (h : a ∈ s₁) :
    s₁ ∩ insert a s₂ = insert a (s₁ ∩ s₂) := by rw [inter_comm, insert_inter_of_mem h, inter_comm]
#align finset.inter_insert_of_mem Finset.inter_insert_of_mem

@[simp]
theorem insert_inter_of_not_mem {s₁ s₂ : Finset α} {a : α} (h : a ∉ s₂) :
    insert a s₁ ∩ s₂ = s₁ ∩ s₂ :=
  ext fun x => by
    have : ¬(x = a ∧ x ∈ s₂) := by rintro ⟨rfl, H⟩; exact h H
    simp only [mem_inter, mem_insert, or_and_right, this, false_or_iff]
#align finset.insert_inter_of_not_mem Finset.insert_inter_of_not_mem

@[simp]
theorem inter_insert_of_not_mem {s₁ s₂ : Finset α} {a : α} (h : a ∉ s₁) :
    s₁ ∩ insert a s₂ = s₁ ∩ s₂ := by rw [inter_comm, insert_inter_of_not_mem h, inter_comm]
#align finset.inter_insert_of_not_mem Finset.inter_insert_of_not_mem

@[simp]
theorem singleton_inter_of_mem {a : α} {s : Finset α} (H : a ∈ s) : {a} ∩ s = {a} :=
  show insert a ∅ ∩ s = insert a ∅ by rw [insert_inter_of_mem H, empty_inter]
#align finset.singleton_inter_of_mem Finset.singleton_inter_of_mem

@[simp]
theorem singleton_inter_of_not_mem {a : α} {s : Finset α} (H : a ∉ s) : {a} ∩ s = ∅ :=
  eq_empty_of_forall_not_mem <| by
    simp only [mem_inter, mem_singleton]; rintro x ⟨rfl, h⟩; exact H h
#align finset.singleton_inter_of_not_mem Finset.singleton_inter_of_not_mem

@[simp]
theorem inter_singleton_of_mem {a : α} {s : Finset α} (h : a ∈ s) : s ∩ {a} = {a} := by
  rw [inter_comm, singleton_inter_of_mem h]
#align finset.inter_singleton_of_mem Finset.inter_singleton_of_mem

@[simp]
theorem inter_singleton_of_not_mem {a : α} {s : Finset α} (h : a ∉ s) : s ∩ {a} = ∅ := by
  rw [inter_comm, singleton_inter_of_not_mem h]
#align finset.inter_singleton_of_not_mem Finset.inter_singleton_of_not_mem

@[mono, gcongr]
theorem inter_subset_inter {x y s t : Finset α} (h : x ⊆ y) (h' : s ⊆ t) : x ∩ s ⊆ y ∩ t := by
  intro a a_in
  rw [Finset.mem_inter] at a_in ⊢
  exact ⟨h a_in.1, h' a_in.2⟩
#align finset.inter_subset_inter Finset.inter_subset_inter

@[gcongr]
theorem inter_subset_inter_left (h : t ⊆ u) : s ∩ t ⊆ s ∩ u :=
  inter_subset_inter Subset.rfl h
#align finset.inter_subset_inter_left Finset.inter_subset_inter_left

@[gcongr]
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
theorem union_left_idem (s t : Finset α) : s ∪ (s ∪ t) = s ∪ t := sup_left_idem _ _
#align finset.union_left_idem Finset.union_left_idem

-- Porting note (#10618): @[simp] can prove this
theorem union_right_idem (s t : Finset α) : s ∪ t ∪ t = s ∪ t := sup_right_idem _ _
#align finset.union_right_idem Finset.union_right_idem

@[simp]
theorem inter_left_idem (s t : Finset α) : s ∩ (s ∩ t) = s ∩ t := inf_left_idem _ _
#align finset.inter_left_idem Finset.inter_left_idem

-- Porting note (#10618): @[simp] can prove this
theorem inter_right_idem (s t : Finset α) : s ∩ t ∩ t = s ∩ t := inf_right_idem _ _
#align finset.inter_right_idem Finset.inter_right_idem

theorem inter_union_distrib_left (s t u : Finset α) : s ∩ (t ∪ u) = s ∩ t ∪ s ∩ u :=
  inf_sup_left _ _ _
#align finset.inter_distrib_left Finset.inter_union_distrib_left

theorem union_inter_distrib_right (s t u : Finset α) : (s ∪ t) ∩ u = s ∩ u ∪ t ∩ u :=
  inf_sup_right _ _ _
#align finset.inter_distrib_right Finset.union_inter_distrib_right

theorem union_inter_distrib_left (s t u : Finset α) : s ∪ t ∩ u = (s ∪ t) ∩ (s ∪ u) :=
  sup_inf_left _ _ _
#align finset.union_distrib_left Finset.union_inter_distrib_left

theorem inter_union_distrib_right (s t u : Finset α) : s ∩ t ∪ u = (s ∪ u) ∩ (t ∪ u) :=
  sup_inf_right _ _ _
#align finset.union_distrib_right Finset.inter_union_distrib_right

-- 2024-03-22
@[deprecated] alias inter_distrib_left := inter_union_distrib_left
@[deprecated] alias inter_distrib_right := union_inter_distrib_right
@[deprecated] alias union_distrib_left := union_inter_distrib_left
@[deprecated] alias union_distrib_right := inter_union_distrib_right

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

lemma union_eq_empty : s ∪ t = ∅ ↔ s = ∅ ∧ t = ∅ := sup_eq_bot_iff
#align finset.union_eq_empty_iff Finset.union_eq_empty

theorem union_subset_iff : s ∪ t ⊆ u ↔ s ⊆ u ∧ t ⊆ u :=
  (sup_le_iff : s ⊔ t ≤ u ↔ s ≤ u ∧ t ≤ u)
#align finset.union_subset_iff Finset.union_subset_iff

theorem subset_inter_iff : s ⊆ t ∩ u ↔ s ⊆ t ∧ s ⊆ u :=
  (le_inf_iff : s ≤ t ⊓ u ↔ s ≤ t ∧ s ≤ u)
#align finset.subset_inter_iff Finset.subset_inter_iff

@[simp] lemma inter_eq_left : s ∩ t = s ↔ s ⊆ t := inf_eq_left
#align finset.inter_eq_left_iff_subset_iff_subset Finset.inter_eq_left

@[simp] lemma inter_eq_right : t ∩ s = s ↔ s ⊆ t := inf_eq_right
#align finset.inter_eq_right_iff_subset Finset.inter_eq_right

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
#align finset.not_disjoint_iff_nonempty_inter Finset.not_disjoint_iff_nonempty_inter

alias ⟨_, Nonempty.not_disjoint⟩ := not_disjoint_iff_nonempty_inter
#align finset.nonempty.not_disjoint Finset.Nonempty.not_disjoint

theorem disjoint_or_nonempty_inter (s t : Finset α) : Disjoint s t ∨ (s ∩ t).Nonempty := by
  rw [← not_disjoint_iff_nonempty_inter]
  exact em _
#align finset.disjoint_or_nonempty_inter Finset.disjoint_or_nonempty_inter

end Lattice

instance isDirected_le : IsDirected (Finset α) (· ≤ ·) := by classical infer_instance
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

protected lemma Nontrivial.erase_nonempty (hs : s.Nontrivial) : (s.erase a).Nonempty :=
  (hs.exists_ne a).imp $ by aesop

@[simp] lemma erase_nonempty (ha : a ∈ s) : (s.erase a).Nonempty ↔ s.Nontrivial := by
  simp only [Finset.Nonempty, mem_erase, and_comm (b := _ ∈ _)]
  refine ⟨?_, fun hs ↦ hs.exists_ne a⟩
  rintro ⟨b, hb, hba⟩
  exact ⟨_, hb, _, ha, hba⟩

@[simp]
theorem erase_singleton (a : α) : ({a} : Finset α).erase a = ∅ := by
  ext x
  simp
#align finset.erase_singleton Finset.erase_singleton

theorem ne_of_mem_erase : b ∈ erase s a → b ≠ a := fun h => (mem_erase.1 h).1
#align finset.ne_of_mem_erase Finset.ne_of_mem_erase

theorem mem_of_mem_erase : b ∈ erase s a → b ∈ s :=
  Multiset.mem_of_mem_erase
#align finset.mem_of_mem_erase Finset.mem_of_mem_erase

theorem mem_erase_of_ne_of_mem : a ≠ b → a ∈ s → a ∈ erase s b := by
  simp only [mem_erase]; exact And.intro
#align finset.mem_erase_of_ne_of_mem Finset.mem_erase_of_ne_of_mem

/-- An element of `s` that is not an element of `erase s a` must be`a`. -/
theorem eq_of_mem_of_not_mem_erase (hs : b ∈ s) (hsa : b ∉ s.erase a) : b = a := by
  rw [mem_erase, not_and] at hsa
  exact not_imp_not.mp hsa hs
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
#align finset.erase_insert Finset.erase_insert

theorem erase_insert_of_ne {a b : α} {s : Finset α} (h : a ≠ b) :
    erase (insert a s) b = insert a (erase s b) :=
  ext fun x => by
    have : x ≠ b ∧ x = a ↔ x = a := and_iff_right_of_imp fun hx => hx.symm ▸ h
    simp only [mem_erase, mem_insert, and_or_left, this]
#align finset.erase_insert_of_ne Finset.erase_insert_of_ne

theorem erase_cons_of_ne {a b : α} {s : Finset α} (ha : a ∉ s) (hb : a ≠ b) :
    erase (cons a s ha) b = cons a (erase s b) fun h => ha <| erase_subset _ _ h := by
  simp only [cons_eq_insert, erase_insert_of_ne hb]
#align finset.erase_cons_of_ne Finset.erase_cons_of_ne

@[simp] theorem insert_erase (h : a ∈ s) : insert a (erase s a) = s :=
  ext fun x => by
    simp only [mem_insert, mem_erase, or_and_left, dec_em, true_and_iff]
    apply or_iff_right_of_imp
    rintro rfl
    exact h
#align finset.insert_erase Finset.insert_erase

lemma erase_eq_iff_eq_insert (hs : a ∈ s) (ht : a ∉ t) : erase s a = t ↔ s = insert a t := by
  aesop

lemma insert_erase_invOn :
    Set.InvOn (insert a) (fun s ↦ erase s a) {s : Finset α | a ∈ s} {s : Finset α | a ∉ s} :=
  ⟨fun _s ↦ insert_erase, fun _s ↦ erase_insert⟩

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
#align finset.coe_erase Finset.coe_erase

theorem erase_ssubset {a : α} {s : Finset α} (h : a ∈ s) : s.erase a ⊂ s :=
  calc
    s.erase a ⊂ insert a (s.erase a) := ssubset_insert <| not_mem_erase _ _
    _ = _ := insert_erase h
#align finset.erase_ssubset Finset.erase_ssubset

theorem ssubset_iff_exists_subset_erase {s t : Finset α} : s ⊂ t ↔ ∃ a ∈ t, s ⊆ t.erase a := by
  refine ⟨fun h => ?_, fun ⟨a, ha, h⟩ => ssubset_of_subset_of_ssubset h <| erase_ssubset ha⟩
  obtain ⟨a, ht, hs⟩ := not_subset.1 h.2
  exact ⟨a, ht, subset_erase.2 ⟨h.1, hs⟩⟩
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
#align finset.erase_cons Finset.erase_cons

theorem erase_idem {a : α} {s : Finset α} : erase (erase s a) a = erase s a := by simp
#align finset.erase_idem Finset.erase_idem

theorem erase_right_comm {a b : α} {s : Finset α} : erase (erase s a) b = erase (erase s b) a := by
  ext x
  simp only [mem_erase, ← and_assoc]
  rw [@and_comm (x ≠ a)]
#align finset.erase_right_comm Finset.erase_right_comm

theorem subset_insert_iff {a : α} {s t : Finset α} : s ⊆ insert a t ↔ erase s a ⊆ t := by
  simp only [subset_iff, or_iff_not_imp_left, mem_erase, mem_insert, and_imp]
  exact forall_congr' fun x => forall_swap
#align finset.subset_insert_iff Finset.subset_insert_iff

theorem erase_insert_subset (a : α) (s : Finset α) : erase (insert a s) a ⊆ s :=
  subset_insert_iff.1 <| Subset.rfl
#align finset.erase_insert_subset Finset.erase_insert_subset

theorem insert_erase_subset (a : α) (s : Finset α) : s ⊆ insert a (erase s a) :=
  subset_insert_iff.2 <| Subset.rfl
#align finset.insert_erase_subset Finset.insert_erase_subset

theorem subset_insert_iff_of_not_mem (h : a ∉ s) : s ⊆ insert a t ↔ s ⊆ t := by
  rw [subset_insert_iff, erase_eq_of_not_mem h]
#align finset.subset_insert_iff_of_not_mem Finset.subset_insert_iff_of_not_mem

theorem erase_subset_iff_of_mem (h : a ∈ t) : s.erase a ⊆ t ↔ s ⊆ t := by
  rw [← subset_insert_iff, insert_eq_of_mem h]
#align finset.erase_subset_iff_of_mem Finset.erase_subset_iff_of_mem

theorem erase_inj {x y : α} (s : Finset α) (hx : x ∈ s) : s.erase x = s.erase y ↔ x = y := by
  refine ⟨fun h => eq_of_mem_of_not_mem_erase hx ?_, congr_arg _⟩
  rw [← h]
  simp
#align finset.erase_inj Finset.erase_inj

theorem erase_injOn (s : Finset α) : Set.InjOn s.erase s := fun _ _ _ _ => (erase_inj s ‹_›).mp
#align finset.erase_inj_on Finset.erase_injOn

theorem erase_injOn' (a : α) : { s : Finset α | a ∈ s }.InjOn fun s => erase s a :=
  fun s hs t ht (h : s.erase a = _) => by rw [← insert_erase hs, ← insert_erase ht, h]
#align finset.erase_inj_on' Finset.erase_injOn'

end Erase

lemma Nontrivial.exists_cons_eq {s : Finset α} (hs : s.Nontrivial) :
    ∃ t a ha b hb hab, (cons b t hb).cons a (mem_cons.not.2 <| not_or_intro hab ha) = s := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := hs
  have : b ∈ s.erase a := mem_erase.2 ⟨hab.symm, hb⟩
  refine ⟨(s.erase a).erase b, a, ?_, b, ?_, ?_, ?_⟩ <;>
    simp [insert_erase this, insert_erase ha, *]

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
#align finset.inter_sdiff_self Finset.inter_sdiff_self

instance : GeneralizedBooleanAlgebra (Finset α) :=
  { sup_inf_sdiff := fun x y => by
      simp only [ext_iff, mem_union, mem_sdiff, inf_eq_inter, sup_eq_union, mem_inter,
        ← and_or_left, em, and_true, implies_true]
    inf_inf_sdiff := fun x y => by
      simp only [ext_iff, inter_sdiff_self, inter_empty, inter_assoc, false_iff_iff, inf_eq_inter,
        not_mem_empty, bot_eq_empty, not_false_iff, implies_true] }

theorem not_mem_sdiff_of_mem_right (h : a ∈ t) : a ∉ s \ t := by
  simp only [mem_sdiff, h, not_true, not_false_iff, and_false_iff]
#align finset.not_mem_sdiff_of_mem_right Finset.not_mem_sdiff_of_mem_right

theorem not_mem_sdiff_of_not_mem_left (h : a ∉ s) : a ∉ s \ t := by simp [h]
#align finset.not_mem_sdiff_of_not_mem_left Finset.not_mem_sdiff_of_not_mem_left

theorem union_sdiff_of_subset (h : s ⊆ t) : s ∪ t \ s = t :=
  sup_sdiff_cancel_right h
#align finset.union_sdiff_of_subset Finset.union_sdiff_of_subset

theorem sdiff_union_of_subset {s₁ s₂ : Finset α} (h : s₁ ⊆ s₂) : s₂ \ s₁ ∪ s₁ = s₂ :=
  (union_comm _ _).trans (union_sdiff_of_subset h)
#align finset.sdiff_union_of_subset Finset.sdiff_union_of_subset

lemma inter_sdiff_assoc (s t u : Finset α) : (s ∩ t) \ u = s ∩ (t \ u) := by
  ext x; simp [and_assoc]

@[deprecated inter_sdiff_assoc] -- 2024-05-01
theorem inter_sdiff (s t u : Finset α) : s ∩ (t \ u) = (s ∩ t) \ u := (inter_sdiff_assoc _ _ _).symm
#align finset.inter_sdiff Finset.inter_sdiff

@[simp]
theorem sdiff_inter_self (s₁ s₂ : Finset α) : s₂ \ s₁ ∩ s₁ = ∅ :=
  inf_sdiff_self_left
#align finset.sdiff_inter_self Finset.sdiff_inter_self

-- Porting note (#10618): @[simp] can prove this
protected theorem sdiff_self (s₁ : Finset α) : s₁ \ s₁ = ∅ :=
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

@[mono, gcongr]
theorem sdiff_subset_sdiff (hst : s ⊆ t) (hvu : v ⊆ u) : s \ u ⊆ t \ v :=
  sdiff_le_sdiff hst hvu
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
#align finset.union_sdiff_symm Finset.union_sdiff_symm

theorem sdiff_union_inter (s t : Finset α) : s \ t ∪ s ∩ t = s :=
  sup_sdiff_inf _ _
#align finset.sdiff_union_inter Finset.sdiff_union_inter

-- Porting note (#10618): @[simp] can prove this
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
  exact Set.insert_diff_of_not_mem _ h
#align finset.insert_sdiff_of_not_mem Finset.insert_sdiff_of_not_mem

theorem insert_sdiff_of_mem (s : Finset α) {x : α} (h : x ∈ t) : insert x s \ t = s \ t := by
  rw [← coe_inj, coe_sdiff, coe_sdiff, coe_insert]
  exact Set.insert_diff_of_mem _ h
#align finset.insert_sdiff_of_mem Finset.insert_sdiff_of_mem

@[simp] lemma insert_sdiff_cancel (ha : a ∉ s) : insert a s \ s = {a} := by
  rw [insert_sdiff_of_not_mem _ ha, Finset.sdiff_self, insert_emptyc_eq]

@[simp]
theorem insert_sdiff_insert (s t : Finset α) (x : α) : insert x s \ insert x t = s \ insert x t :=
  insert_sdiff_of_mem _ (mem_insert_self _ _)
#align finset.insert_sdiff_insert Finset.insert_sdiff_insert

lemma insert_sdiff_insert' (hab : a ≠ b) (ha : a ∉ s) : insert a s \ insert b s = {a} := by
  ext; aesop

lemma erase_sdiff_erase (hab : a ≠ b) (hb : b ∈ s) : s.erase a \ s.erase b = {b} := by
  ext; aesop

lemma cons_sdiff_cons (hab : a ≠ b) (ha hb) : s.cons a ha \ s.cons b hb = {a} := by
  rw [cons_eq_insert, cons_eq_insert, insert_sdiff_insert' hab ha]

theorem sdiff_insert_of_not_mem {x : α} (h : x ∉ s) (t : Finset α) : s \ insert x t = s \ t := by
  refine Subset.antisymm (sdiff_subset_sdiff (Subset.refl _) (subset_insert _ _)) fun y hy => ?_
  simp only [mem_sdiff, mem_insert, not_or] at hy ⊢
  exact ⟨hy.1, fun hxy => h <| hxy ▸ hy.1, hy.2⟩
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
  rw [mem_erase, mem_sdiff, mem_singleton, and_comm]
#align finset.sdiff_singleton_eq_erase Finset.sdiff_singleton_eq_erase

-- This lemma matches `Finset.insert_eq` in functionality.
theorem erase_eq (s : Finset α) (a : α) : s.erase a = s \ {a} :=
  (sdiff_singleton_eq_erase _ _).symm
#align finset.erase_eq Finset.erase_eq

theorem disjoint_erase_comm : Disjoint (s.erase a) t ↔ Disjoint s (t.erase a) := by
  simp_rw [erase_eq, disjoint_sdiff_comm]
#align finset.disjoint_erase_comm Finset.disjoint_erase_comm

lemma disjoint_insert_erase (ha : a ∉ t) : Disjoint (s.erase a) (insert a t) ↔ Disjoint s t := by
  rw [disjoint_erase_comm, erase_insert ha]

lemma disjoint_erase_insert (ha : a ∉ s) : Disjoint (insert a s) (t.erase a) ↔ Disjoint s t := by
  rw [← disjoint_erase_comm, erase_insert ha]

theorem disjoint_of_erase_left (ha : a ∉ t) (hst : Disjoint (s.erase a) t) : Disjoint s t := by
  rw [← erase_insert ha, ← disjoint_erase_comm, disjoint_insert_right]
  exact ⟨not_mem_erase _ _, hst⟩
#align finset.disjoint_of_erase_left Finset.disjoint_of_erase_left

theorem disjoint_of_erase_right (ha : a ∉ s) (hst : Disjoint s (t.erase a)) : Disjoint s t := by
  rw [← erase_insert ha, disjoint_erase_comm, disjoint_insert_left]
  exact ⟨not_mem_erase _ _, hst⟩
#align finset.disjoint_of_erase_right Finset.disjoint_of_erase_right

theorem inter_erase (a : α) (s t : Finset α) : s ∩ t.erase a = (s ∩ t).erase a := by
  simp only [erase_eq, inter_sdiff_assoc]
#align finset.inter_erase Finset.inter_erase

@[simp]
theorem erase_inter (a : α) (s t : Finset α) : s.erase a ∩ t = (s ∩ t).erase a := by
  simpa only [inter_comm t] using inter_erase a t s
#align finset.erase_inter Finset.erase_inter

theorem erase_sdiff_comm (s t : Finset α) (a : α) : s.erase a \ t = (s \ t).erase a := by
  simp_rw [erase_eq, sdiff_right_comm]
#align finset.erase_sdiff_comm Finset.erase_sdiff_comm

theorem insert_union_comm (s t : Finset α) (a : α) : insert a s ∪ t = s ∪ insert a t := by
  rw [insert_union, union_insert]
#align finset.insert_union_comm Finset.insert_union_comm

theorem erase_inter_comm (s t : Finset α) (a : α) : s.erase a ∩ t = s ∩ t.erase a := by
  rw [erase_inter, inter_erase]
#align finset.erase_inter_comm Finset.erase_inter_comm

theorem erase_union_distrib (s t : Finset α) (a : α) : (s ∪ t).erase a = s.erase a ∪ t.erase a := by
  simp_rw [erase_eq, union_sdiff_distrib]
#align finset.erase_union_distrib Finset.erase_union_distrib

theorem insert_inter_distrib (s t : Finset α) (a : α) :
    insert a (s ∩ t) = insert a s ∩ insert a t := by simp_rw [insert_eq, union_inter_distrib_left]
#align finset.insert_inter_distrib Finset.insert_inter_distrib

theorem erase_sdiff_distrib (s t : Finset α) (a : α) : (s \ t).erase a = s.erase a \ t.erase a := by
  simp_rw [erase_eq, sdiff_sdiff, sup_sdiff_eq_sup le_rfl, sup_comm]
#align finset.erase_sdiff_distrib Finset.erase_sdiff_distrib

theorem erase_union_of_mem (ha : a ∈ t) (s : Finset α) : s.erase a ∪ t = s ∪ t := by
  rw [← insert_erase (mem_union_right s ha), erase_union_distrib, ← union_insert, insert_erase ha]
#align finset.erase_union_of_mem Finset.erase_union_of_mem

theorem union_erase_of_mem (ha : a ∈ s) (t : Finset α) : s ∪ t.erase a = s ∪ t := by
  rw [← insert_erase (mem_union_left t ha), erase_union_distrib, ← insert_union, insert_erase ha]
#align finset.union_erase_of_mem Finset.union_erase_of_mem

@[simp]
theorem sdiff_singleton_eq_self (ha : a ∉ s) : s \ {a} = s :=
  sdiff_eq_self_iff_disjoint.2 <| by simp [ha]
#align finset.sdiff_singleton_eq_self Finset.sdiff_singleton_eq_self

theorem Nontrivial.sdiff_singleton_nonempty {c : α} {s : Finset α} (hS : s.Nontrivial) :
    (s \ {c}).Nonempty := by
  rw [Finset.sdiff_nonempty, Finset.subset_singleton_iff]
  push_neg
  exact ⟨by rintro rfl; exact Finset.not_nontrivial_empty hS, hS.ne_singleton⟩

theorem sdiff_sdiff_left' (s t u : Finset α) : (s \ t) \ u = s \ t ∩ (s \ u) :=
  _root_.sdiff_sdiff_left'
#align finset.sdiff_sdiff_left' Finset.sdiff_sdiff_left'

theorem sdiff_union_sdiff_cancel (hts : t ⊆ s) (hut : u ⊆ t) : s \ t ∪ t \ u = s \ u :=
  sdiff_sup_sdiff_cancel hts hut
#align finset.sdiff_union_sdiff_cancel Finset.sdiff_union_sdiff_cancel

theorem sdiff_union_erase_cancel (hts : t ⊆ s) (ha : a ∈ t) : s \ t ∪ t.erase a = s.erase a := by
  simp_rw [erase_eq, sdiff_union_sdiff_cancel hts (singleton_subset_iff.2 ha)]
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
#align finset.sdiff_insert_insert_of_mem_of_not_mem Finset.sdiff_insert_insert_of_mem_of_not_mem

theorem sdiff_erase (h : a ∈ s) : s \ t.erase a = insert a (s \ t) := by
  rw [← sdiff_singleton_eq_erase, sdiff_sdiff_eq_sdiff_union (singleton_subset_iff.2 h), insert_eq,
    union_comm]
#align finset.sdiff_erase Finset.sdiff_erase

theorem sdiff_erase_self (ha : a ∈ s) : s \ s.erase a = {a} := by
  rw [sdiff_erase ha, Finset.sdiff_self, insert_emptyc_eq]
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

open scoped symmDiff

variable [DecidableEq α] {s t : Finset α} {a b : α}

theorem mem_symmDiff : a ∈ s ∆ t ↔ a ∈ s ∧ a ∉ t ∨ a ∈ t ∧ a ∉ s := by
  simp_rw [symmDiff, sup_eq_union, mem_union, mem_sdiff]
#align finset.mem_symm_diff Finset.mem_symmDiff

@[simp, norm_cast]
theorem coe_symmDiff : (↑(s ∆ t) : Set α) = (s : Set α) ∆ t :=
  Set.ext fun x => by simp [mem_symmDiff, Set.mem_symmDiff]
#align finset.coe_symm_diff Finset.coe_symmDiff

@[simp] lemma symmDiff_eq_empty : s ∆ t = ∅ ↔ s = t := symmDiff_eq_bot
@[simp] lemma symmDiff_nonempty : (s ∆ t).Nonempty ↔ s ≠ t :=
  nonempty_iff_ne_empty.trans symmDiff_eq_empty.not

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
  dsimp [SizeOf.sizeOf, SizeOf.sizeOf, Multiset.sizeOf]
  rw [add_comm]
  refine lt_trans ?_ (Nat.lt_succ_self _)
  exact Multiset.sizeOf_lt_sizeOf_of_mem hx
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

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]
theorem attach_nonempty_iff {s : Finset α} : s.attach.Nonempty ↔ s.Nonempty := by
  simp [Finset.Nonempty]
#align finset.attach_nonempty_iff Finset.attach_nonempty_iff

protected alias ⟨_, Nonempty.attach⟩ := attach_nonempty_iff

@[simp]
theorem attach_eq_empty_iff {s : Finset α} : s.attach = ∅ ↔ s = ∅ := by
  simp [eq_empty_iff_forall_not_mem]
#align finset.attach_eq_empty_iff Finset.attach_eq_empty_iff

section DecidablePiExists

variable {s : Finset α}

instance decidableDforallFinset {p : ∀ a ∈ s, Prop} [_hp : ∀ (a) (h : a ∈ s), Decidable (p a h)] :
    Decidable (∀ (a) (h : a ∈ s), p a h) :=
  Multiset.decidableDforallMultiset
#align finset.decidable_dforall_finset Finset.decidableDforallFinset

-- Porting note: In lean3, `decidableDforallFinset` was picked up when decidability of `s ⊆ t` was
-- needed. In lean4 it seems this is not the case.
instance instDecidableRelSubset [DecidableEq α] : @DecidableRel (Finset α) (· ⊆ ·) :=
  fun _ _ ↦ decidableDforallFinset

instance instDecidableRelSSubset [DecidableEq α] : @DecidableRel (Finset α) (· ⊂ ·) :=
  fun _ _ ↦ instDecidableAnd

instance instDecidableLE [DecidableEq α] : @DecidableRel (Finset α) (· ≤ ·) :=
  instDecidableRelSubset

instance instDecidableLT [DecidableEq α] : @DecidableRel (Finset α) (· < ·) :=
  instDecidableRelSSubset

instance decidableDExistsFinset {p : ∀ a ∈ s, Prop} [_hp : ∀ (a) (h : a ∈ s), Decidable (p a h)] :
    Decidable (∃ (a : _) (h : a ∈ s), p a h) :=
  Multiset.decidableDexistsMultiset
#align finset.decidable_dexists_finset Finset.decidableDExistsFinset

instance decidableExistsAndFinset {p : α → Prop} [_hp : ∀ (a), Decidable (p a)] :
    Decidable (∃ a ∈ s, p a) :=
  decidable_of_iff (∃ (a : _) (_ : a ∈ s), p a) (by simp)

instance decidableExistsAndFinsetCoe {p : α → Prop} [DecidablePred p] :
    Decidable (∃ a ∈ (s : Set α), p a) := decidableExistsAndFinset

/-- decidable equality for functions whose domain is bounded by finsets -/
instance decidableEqPiFinset {β : α → Type*} [_h : ∀ a, DecidableEq (β a)] :
    DecidableEq (∀ a ∈ s, β a) :=
  Multiset.decidableEqPiMultiset
#align finset.decidable_eq_pi_finset Finset.decidableEqPiFinset

end DecidablePiExists

/-! ### filter -/


section Filter

variable (p q : α → Prop) [DecidablePred p] [DecidablePred q] {s : Finset α}

/-- `Finset.filter p s` is the set of elements of `s` that satisfy `p`.

For example, one can use `s.filter (· ∈ t)` to get the intersection of `s` with `t : Set α`
as a `Finset α` (when a `DecidablePred (· ∈ t)` instance is available). -/
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
#align finset.filter_filter Finset.filter_filter

theorem filter_comm (s : Finset α) : (s.filter p).filter q = (s.filter q).filter p := by
  simp_rw [filter_filter, and_comm]
#align finset.filter_comm Finset.filter_comm

-- We can replace an application of filter where the decidability is inferred in "the wrong way".
theorem filter_congr_decidable (s : Finset α) (p : α → Prop) (h : DecidablePred p)
    [DecidablePred p] : @filter α p h s = s.filter p := by congr
#align finset.filter_congr_decidable Finset.filter_congr_decidable

@[simp]
theorem filter_True {h} (s : Finset α) : @filter _ (fun _ => True) h s = s := by ext; simp
#align finset.filter_true Finset.filter_True

@[simp]
theorem filter_False {h} (s : Finset α) : @filter _ (fun _ => False) h s = ∅ := by ext; simp
#align finset.filter_false Finset.filter_False

variable {p q}

lemma filter_eq_self : s.filter p = s ↔ ∀ x ∈ s, p x := by simp [Finset.ext_iff]
#align finset.filter_eq_self Finset.filter_eq_self

theorem filter_eq_empty_iff : s.filter p = ∅ ↔ ∀ ⦃x⦄, x ∈ s → ¬p x := by simp [Finset.ext_iff]
#align finset.filter_eq_empty_iff Finset.filter_eq_empty_iff

theorem filter_nonempty_iff : (s.filter p).Nonempty ↔ ∃ a ∈ s, p a := by
  simp only [nonempty_iff_ne_empty, Ne, filter_eq_empty_iff, Classical.not_not, not_forall,
    exists_prop]
#align finset.filter_nonempty_iff Finset.filter_nonempty_iff

/-- If all elements of a `Finset` satisfy the predicate `p`, `s.filter p` is `s`. -/
theorem filter_true_of_mem (h : ∀ x ∈ s, p x) : s.filter p = s := filter_eq_self.2 h
#align finset.filter_true_of_mem Finset.filter_true_of_mem

/-- If all elements of a `Finset` fail to satisfy the predicate `p`, `s.filter p` is `∅`. -/
theorem filter_false_of_mem (h : ∀ x ∈ s, ¬p x) : s.filter p = ∅ := filter_eq_empty_iff.2 h
#align finset.filter_false_of_mem Finset.filter_false_of_mem

@[simp]
theorem filter_const (p : Prop) [Decidable p] (s : Finset α) :
    (s.filter fun _a => p) = if p then s else ∅ := by split_ifs <;> simp [*]
#align finset.filter_const Finset.filter_const

theorem filter_congr {s : Finset α} (H : ∀ x ∈ s, p x ↔ q x) : filter p s = filter q s :=
  eq_of_veq <| Multiset.filter_congr H
#align finset.filter_congr Finset.filter_congr

variable (p q)

@[simp]
theorem filter_empty : filter p ∅ = ∅ :=
  subset_empty.1 <| filter_subset _ _
#align finset.filter_empty Finset.filter_empty

@[gcongr]
theorem filter_subset_filter {s t : Finset α} (h : s ⊆ t) : s.filter p ⊆ t.filter p := fun _a ha =>
  mem_filter.2 ⟨h (mem_filter.1 ha).1, (mem_filter.1 ha).2⟩
#align finset.filter_subset_filter Finset.filter_subset_filter

theorem monotone_filter_left : Monotone (filter p) := fun _ _ => filter_subset_filter p
#align finset.monotone_filter_left Finset.monotone_filter_left

-- TODO: `@[gcongr]` doesn't accept this lemma because of the `DecidablePred` arguments
theorem monotone_filter_right (s : Finset α) ⦃p q : α → Prop⦄ [DecidablePred p] [DecidablePred q]
    (h : p ≤ q) : s.filter p ⊆ s.filter q :=
  Multiset.subset_of_le (Multiset.monotone_filter_right s.val h)
#align finset.monotone_filter_right Finset.monotone_filter_right

@[simp, norm_cast]
theorem coe_filter (s : Finset α) : ↑(s.filter p) = ({ x ∈ ↑s | p x } : Set α) :=
  Set.ext fun _ => mem_filter
#align finset.coe_filter Finset.coe_filter

theorem subset_coe_filter_of_subset_forall (s : Finset α) {t : Set α} (h₁ : t ⊆ s)
    (h₂ : ∀ x ∈ t, p x) : t ⊆ s.filter p := fun x hx => (s.coe_filter p).symm ▸ ⟨h₁ hx, h₂ x hx⟩
#align finset.subset_coe_filter_of_subset_forall Finset.subset_coe_filter_of_subset_forall

theorem filter_singleton (a : α) : filter p {a} = if p a then {a} else ∅ := by
  classical
    ext x
    simp only [mem_singleton, forall_eq, mem_filter]
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
  rintro a ⟨_, hp⟩ ⟨_, hq⟩
  rw [Pi.disjoint_iff] at h
  simpa [hp, hq] using h a
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

lemma _root_.Set.pairwiseDisjoint_filter [DecidableEq β] (f : α → β) (s : Set β) (t : Finset α) :
    s.PairwiseDisjoint fun x ↦ t.filter (f · = x) := by
  rintro i - j - h u hi hj x hx
  obtain ⟨-, rfl⟩ : x ∈ t ∧ f x = i := by simpa using hi hx
  obtain ⟨-, rfl⟩ : x ∈ t ∧ f x = j := by simpa using hj hx
  contradiction

theorem filter_cons {a : α} (s : Finset α) (ha : a ∉ s) :
    filter p (cons a s ha) =
      (if p a then {a} else ∅ : Finset α).disjUnion (filter p s)
        (by
          split_ifs
          · rw [disjoint_singleton_left]
            exact mem_filter.not.mpr <| mt And.left ha
          · exact disjoint_empty_left _) := by
  split_ifs with h
  · rw [filter_cons_of_pos _ _ _ ha h, singleton_disjUnion]
  · rw [filter_cons_of_neg _ _ _ ha h, empty_disjUnion]
#align finset.filter_cons Finset.filter_cons

variable [DecidableEq α]

theorem filter_union (s₁ s₂ : Finset α) : (s₁ ∪ s₂).filter p = s₁.filter p ∪ s₂.filter p :=
  ext fun _ => by simp only [mem_filter, mem_union, or_and_right]
#align finset.filter_union Finset.filter_union

theorem filter_union_right (s : Finset α) : s.filter p ∪ s.filter q = s.filter fun x => p x ∨ q x :=
  ext fun x => by simp [mem_filter, mem_union, ← and_or_left]
#align finset.filter_union_right Finset.filter_union_right

theorem filter_mem_eq_inter {s t : Finset α} [∀ i, Decidable (i ∈ t)] :
    (s.filter fun i => i ∈ t) = s ∩ t :=
  ext fun i => by simp [mem_filter, mem_inter]
#align finset.filter_mem_eq_inter Finset.filter_mem_eq_inter

theorem filter_inter_distrib (s t : Finset α) : (s ∩ t).filter p = s.filter p ∩ t.filter p := by
  ext
  simp [mem_filter, mem_inter, and_assoc]
#align finset.filter_inter_distrib Finset.filter_inter_distrib

theorem filter_inter (s t : Finset α) : filter p s ∩ t = filter p (s ∩ t) := by
  ext
  simp only [mem_inter, mem_filter, and_right_comm]
#align finset.filter_inter Finset.filter_inter

theorem inter_filter (s t : Finset α) : s ∩ filter p t = filter p (s ∩ t) := by
  rw [inter_comm, filter_inter, inter_comm]
#align finset.inter_filter Finset.inter_filter

theorem filter_insert (a : α) (s : Finset α) :
    filter p (insert a s) = if p a then insert a (filter p s) else filter p s := by
  ext x
  split_ifs with h <;> by_cases h' : x = a <;> simp [h, h']
#align finset.filter_insert Finset.filter_insert

theorem filter_erase (a : α) (s : Finset α) : filter p (erase s a) = erase (filter p s) a := by
  ext x
  simp only [and_assoc, mem_filter, iff_self_iff, mem_erase]
#align finset.filter_erase Finset.filter_erase

theorem filter_or (s : Finset α) : (s.filter fun a => p a ∨ q a) = s.filter p ∪ s.filter q :=
  ext fun _ => by simp [mem_filter, mem_union, and_or_left]
#align finset.filter_or Finset.filter_or

theorem filter_and (s : Finset α) : (s.filter fun a => p a ∧ q a) = s.filter p ∩ s.filter q :=
  ext fun _ => by simp [mem_filter, mem_inter, and_comm, and_left_comm, and_self_iff, and_assoc]
#align finset.filter_and Finset.filter_and

theorem filter_not (s : Finset α) : (s.filter fun a => ¬p a) = s \ s.filter p :=
  ext fun a => by
    simp only [Bool.decide_coe, Bool.not_eq_true', mem_filter, and_comm, mem_sdiff, not_and_or,
      Bool.not_eq_true, and_or_left, and_not_self, or_false]
#align finset.filter_not Finset.filter_not

lemma filter_and_not (s : Finset α) (p q : α → Prop) [DecidablePred p] [DecidablePred q] :
    s.filter (fun a ↦ p a ∧ ¬ q a) = s.filter p \ s.filter q := by
  rw [filter_and, filter_not, ← inter_sdiff_assoc, inter_eq_left.2 (filter_subset _ _)]

theorem sdiff_eq_filter (s₁ s₂ : Finset α) : s₁ \ s₂ = filter (· ∉ s₂) s₁ :=
  ext fun _ => by simp [mem_sdiff, mem_filter]
#align finset.sdiff_eq_filter Finset.sdiff_eq_filter

theorem sdiff_eq_self (s₁ s₂ : Finset α) : s₁ \ s₂ = s₁ ↔ s₁ ∩ s₂ ⊆ ∅ := by
  simp [Subset.antisymm_iff, disjoint_iff_inter_eq_empty]
#align finset.sdiff_eq_self Finset.sdiff_eq_self

theorem subset_union_elim {s : Finset α} {t₁ t₂ : Set α} (h : ↑s ⊆ t₁ ∪ t₂) :
    ∃ s₁ s₂ : Finset α, s₁ ∪ s₂ = s ∧ ↑s₁ ⊆ t₁ ∧ ↑s₂ ⊆ t₂ \ t₁ := by
  classical
    refine ⟨s.filter (· ∈ t₁), s.filter (· ∉ t₁), ?_, ?_, ?_⟩
    · simp [filter_union_right, em]
    · intro x
      simp
    · intro x
      simp only [not_not, coe_filter, Set.mem_setOf_eq, Set.mem_diff, and_imp]
      intro hx hx₂
      exact ⟨Or.resolve_left (h hx) hx₂, hx₂⟩
#align finset.subset_union_elim Finset.subset_union_elim

section Classical

open scoped Classical

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
  · ext
    simp only [mem_filter, mem_singleton, decide_eq_true_eq]
    refine ⟨fun h => h.2.symm, ?_⟩
    rintro rfl
    exact ⟨h, rfl⟩
  · ext
    simp only [mem_filter, not_and, iff_false_iff, not_mem_empty, decide_eq_true_eq]
    rintro m rfl
    exact h m
#align finset.filter_eq Finset.filter_eq

/-- After filtering out everything that does not equal a given value, at most that value remains.

  This is equivalent to `filter_eq` with the equality the other way.
-/
theorem filter_eq' [DecidableEq β] (s : Finset β) (b : β) :
    (s.filter fun a => a = b) = ite (b ∈ s) {b} ∅ :=
  _root_.trans (filter_congr fun _ _ => by simp_rw [@eq_comm _ b]) (filter_eq s b)
#align finset.filter_eq' Finset.filter_eq'

theorem filter_ne [DecidableEq β] (s : Finset β) (b : β) :
    (s.filter fun a => b ≠ a) = s.erase b := by
  ext
  simp only [mem_filter, mem_erase, Ne, decide_not, Bool.not_eq_true', decide_eq_false_iff_not]
  tauto
#align finset.filter_ne Finset.filter_ne

theorem filter_ne' [DecidableEq β] (s : Finset β) (b : β) : (s.filter fun a => a ≠ b) = s.erase b :=
  _root_.trans (filter_congr fun _ _ => by simp_rw [@ne_comm _ b]) (filter_ne s b)
#align finset.filter_ne' Finset.filter_ne'

theorem filter_inter_filter_neg_eq (s t : Finset α) :
    (s.filter p ∩ t.filter fun a => ¬p a) = ∅ := by
  simpa using (disjoint_filter_filter_neg s t p).eq_bot
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

-- Porting note (#10618): @[simp] can prove this
theorem not_mem_range_self : n ∉ range n :=
  Multiset.not_mem_range_self
#align finset.not_mem_range_self Finset.not_mem_range_self

-- Porting note (#10618): @[simp] can prove this
theorem self_mem_range_succ (n : ℕ) : n ∈ range (n + 1) :=
  Multiset.self_mem_range_succ n
#align finset.self_mem_range_succ Finset.self_mem_range_succ

@[simp]
theorem range_subset {n m} : range n ⊆ range m ↔ n ≤ m :=
  Multiset.range_subset
#align finset.range_subset Finset.range_subset

theorem range_mono : Monotone range := fun _ _ => range_subset.2
#align finset.range_mono Finset.range_mono

@[gcongr] alias ⟨_, _root_.GCongr.finset_range_subset_of_le⟩ := range_subset

theorem mem_range_succ_iff {a b : ℕ} : a ∈ Finset.range b.succ ↔ a ≤ b :=
  Finset.mem_range.trans Nat.lt_succ_iff
#align finset.mem_range_succ_iff Finset.mem_range_succ_iff

theorem mem_range_le {n x : ℕ} (hx : x ∈ range n) : x ≤ n :=
  (mem_range.1 hx).le
#align finset.mem_range_le Finset.mem_range_le

theorem mem_range_sub_ne_zero {n x : ℕ} (hx : x ∈ range n) : n - x ≠ 0 :=
  _root_.ne_of_gt <| Nat.sub_pos_of_lt <| mem_range.1 hx
#align finset.mem_range_sub_ne_zero Finset.mem_range_sub_ne_zero

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]
theorem nonempty_range_iff : (range n).Nonempty ↔ n ≠ 0 :=
  ⟨fun ⟨k, hk⟩ => (k.zero_le.trans_lt <| mem_range.1 hk).ne',
   fun h => ⟨0, mem_range.2 <| Nat.pos_iff_ne_zero.2 h⟩⟩
#align finset.nonempty_range_iff Finset.nonempty_range_iff

@[simp]
theorem range_eq_empty_iff : range n = ∅ ↔ n = 0 := by
  rw [← not_nonempty_iff_eq_empty, nonempty_range_iff, not_not]
#align finset.range_eq_empty_iff Finset.range_eq_empty_iff

theorem nonempty_range_succ : (range <| n + 1).Nonempty :=
  nonempty_range_iff.2 n.succ_ne_zero
#align finset.nonempty_range_succ Finset.nonempty_range_succ

@[simp]
theorem range_filter_eq {n m : ℕ} : (range n).filter (· = m) = if m < n then {m} else ∅ := by
  convert filter_eq (range n) m using 2
  · ext
    rw [eq_comm]
  · simp
#align finset.range_filter_eq Finset.range_filter_eq

lemma range_nontrivial {n : ℕ} (hn : 1 < n) : (Finset.range n).Nontrivial := by
  rw [Finset.Nontrivial, Finset.coe_range]
  exact ⟨0, Nat.zero_lt_one.trans hn, 1, hn, zero_ne_one⟩

end Range

-- useful rules for calculations with quantifiers
theorem exists_mem_empty_iff (p : α → Prop) : (∃ x, x ∈ (∅ : Finset α) ∧ p x) ↔ False := by
  simp only [not_mem_empty, false_and_iff, exists_false]
#align finset.exists_mem_empty_iff Finset.exists_mem_empty_iff

theorem exists_mem_insert [DecidableEq α] (a : α) (s : Finset α) (p : α → Prop) :
    (∃ x, x ∈ insert a s ∧ p x) ↔ p a ∨ ∃ x, x ∈ s ∧ p x := by
  simp only [mem_insert, or_and_right, exists_or, exists_eq_left]
#align finset.exists_mem_insert Finset.exists_mem_insert

theorem forall_mem_empty_iff (p : α → Prop) : (∀ x, x ∈ (∅ : Finset α) → p x) ↔ True :=
  iff_true_intro fun _ h => False.elim <| not_mem_empty _ h
#align finset.forall_mem_empty_iff Finset.forall_mem_empty_iff

theorem forall_mem_insert [DecidableEq α] (a : α) (s : Finset α) (p : α → Prop) :
    (∀ x, x ∈ insert a s → p x) ↔ p a ∧ ∀ x, x ∈ s → p x := by
  simp only [mem_insert, or_imp, forall_and, forall_eq]
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
  left_inv j := by
    rw [Subtype.ext_iff_val]
    apply Nat.sub_add_cancel
    simpa using j.2
  right_inv j := Nat.add_sub_cancel_right _ _
#align not_mem_range_equiv notMemRangeEquiv

@[simp]
theorem coe_notMemRangeEquiv (k : ℕ) :
    (notMemRangeEquiv k : { n // n ∉ range k } → ℕ) = fun (i : { n // n ∉ range k }) => i - k :=
  rfl
#align coe_not_mem_range_equiv coe_notMemRangeEquiv

@[simp]
theorem coe_notMemRangeEquiv_symm (k : ℕ) :
    ((notMemRangeEquiv k).symm : ℕ → { n // n ∉ range k }) = fun j => ⟨j + k, by simp⟩ :=
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
#align multiset.to_finset_singleton Multiset.toFinset_singleton

@[simp]
theorem toFinset_add (s t : Multiset α) : toFinset (s + t) = toFinset s ∪ toFinset t :=
  Finset.ext <| by simp
#align multiset.to_finset_add Multiset.toFinset_add

@[simp]
theorem toFinset_nsmul (s : Multiset α) : ∀ n ≠ 0, (n • s).toFinset = s.toFinset
  | 0, h => by contradiction
  | n + 1, _ => by
    by_cases h : n = 0
    · rw [h, zero_add, one_nsmul]
    · rw [add_nsmul, toFinset_add, one_nsmul, toFinset_nsmul s n h, Finset.union_idempotent]
#align multiset.to_finset_nsmul Multiset.toFinset_nsmul

theorem toFinset_eq_singleton_iff (s : Multiset α) (a : α) :
    s.toFinset = {a} ↔ card s ≠ 0 ∧ s = card s • {a} := by
  refine ⟨fun H ↦ ⟨fun h ↦ ?_, ext' fun x ↦ ?_⟩, fun H ↦ ?_⟩
  · rw [card_eq_zero.1 h, toFinset_zero] at H
    exact Finset.singleton_ne_empty _ H.symm
  · rw [count_nsmul, count_singleton]
    by_cases hx : x = a
    · simp_rw [hx, ite_true, mul_one, count_eq_card]
      intro y hy
      rw [← mem_toFinset, H, Finset.mem_singleton] at hy
      exact hy.symm
    have hx' : x ∉ s := fun h' ↦ hx <| by rwa [← mem_toFinset, H, Finset.mem_singleton] at h'
    simp_rw [count_eq_zero_of_not_mem hx', hx, ite_false, Nat.mul_zero]
  simpa only [toFinset_nsmul _ _ H.1, toFinset_singleton] using congr($(H.2).toFinset)

@[simp]
theorem toFinset_inter (s t : Multiset α) : toFinset (s ∩ t) = toFinset s ∩ toFinset t :=
  Finset.ext <| by simp
#align multiset.to_finset_inter Multiset.toFinset_inter

@[simp]
theorem toFinset_union (s t : Multiset α) : (s ∪ t).toFinset = s.toFinset ∪ t.toFinset := by
  ext; simp
#align multiset.to_finset_union Multiset.toFinset_union

@[simp]
theorem toFinset_eq_empty {m : Multiset α} : m.toFinset = ∅ ↔ m = 0 :=
  Finset.val_inj.symm.trans Multiset.dedup_eq_zero
#align multiset.to_finset_eq_empty Multiset.toFinset_eq_empty

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]
theorem toFinset_nonempty : s.toFinset.Nonempty ↔ s ≠ 0 := by
  simp only [toFinset_eq_empty, Ne, Finset.nonempty_iff_ne_empty]
#align multiset.to_finset_nonempty Multiset.toFinset_nonempty

@[simp]
theorem toFinset_subset : s.toFinset ⊆ t.toFinset ↔ s ⊆ t := by
  simp only [Finset.subset_iff, Multiset.subset_iff, Multiset.mem_toFinset]
#align multiset.to_finset_subset Multiset.toFinset_subset

@[simp]
theorem toFinset_ssubset : s.toFinset ⊂ t.toFinset ↔ s ⊂ t := by
  simp_rw [Finset.ssubset_def, toFinset_subset]
  rfl
#align multiset.to_finset_ssubset Multiset.toFinset_ssubset

@[simp]
theorem toFinset_dedup (m : Multiset α) : m.dedup.toFinset = m.toFinset := by
  simp_rw [toFinset, dedup_idem]
#align multiset.to_finset_dedup Multiset.toFinset_dedup

-- @[simp]
-- theorem toFinset_bind_dedup [DecidableEq β] (m : Multiset α) (f : α → Multiset β) :
--     (m.dedup.bind f).toFinset = (m.bind f).toFinset := by simp_rw [toFinset, dedup_bind_dedup]
-- #align multiset.to_finset_bind_dedup Multiset.toFinset_bind_dedup

@[simp]
theorem toFinset_filter (s : Multiset α) (p : α → Prop) [DecidablePred p] :
    Multiset.toFinset (s.filter p) = s.toFinset.filter p := by
  ext; simp

instance isWellFounded_ssubset : IsWellFounded (Multiset β) (· ⊂ ·) := by
  classical
  exact Subrelation.isWellFounded (InvImage _ toFinset) toFinset_ssubset.2
#align multiset.is_well_founded_ssubset Multiset.isWellFounded_ssubset

end Multiset

namespace Finset

@[simp]
theorem val_toFinset [DecidableEq α] (s : Finset α) : s.val.toFinset = s := by
  ext
  rw [Multiset.mem_toFinset, ← mem_def]
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
#align list.to_finset_cons List.toFinset_cons

theorem toFinset_surj_on : Set.SurjOn toFinset { l : List α | l.Nodup } Set.univ := by
  rintro ⟨⟨l⟩, hl⟩ _
  exact ⟨l, hl, (toFinset_eq hl).symm⟩
#align list.to_finset_surj_on List.toFinset_surj_on

theorem toFinset_surjective : Surjective (toFinset : List α → Finset α) := fun s =>
  let ⟨l, _, hls⟩ := toFinset_surj_on (Set.mem_univ s)
  ⟨l, hls⟩
#align list.to_finset_surjective List.toFinset_surjective

theorem toFinset_eq_iff_perm_dedup : l.toFinset = l'.toFinset ↔ l.dedup ~ l'.dedup := by
  simp [Finset.ext_iff, perm_ext_iff_of_nodup (nodup_dedup _) (nodup_dedup _)]
#align list.to_finset_eq_iff_perm_dedup List.toFinset_eq_iff_perm_dedup

theorem toFinset.ext_iff {a b : List α} : a.toFinset = b.toFinset ↔ ∀ x, x ∈ a ↔ x ∈ b := by
  simp only [Finset.ext_iff, mem_toFinset]
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
  exact Multiset.Nodup.toFinset_inj hl hl' h
#align list.perm_of_nodup_nodup_to_finset_eq List.perm_of_nodup_nodup_toFinset_eq

@[simp]
theorem toFinset_append : toFinset (l ++ l') = l.toFinset ∪ l'.toFinset := by
  induction' l with hd tl hl
  · simp
  · simp [hl]
#align list.to_finset_append List.toFinset_append

@[simp]
theorem toFinset_reverse {l : List α} : toFinset l.reverse = l.toFinset :=
  toFinset_eq_of_perm _ _ (reverse_perm l)
#align list.to_finset_reverse List.toFinset_reverse

theorem toFinset_replicate_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (List.replicate n a).toFinset = {a} := by
  ext x
  simp [hn, List.mem_replicate]
#align list.to_finset_replicate_of_ne_zero List.toFinset_replicate_of_ne_zero

@[simp]
theorem toFinset_union (l l' : List α) : (l ∪ l').toFinset = l.toFinset ∪ l'.toFinset := by
  ext
  simp
#align list.to_finset_union List.toFinset_union

@[simp]
theorem toFinset_inter (l l' : List α) : (l ∩ l').toFinset = l.toFinset ∩ l'.toFinset := by
  ext
  simp
#align list.to_finset_inter List.toFinset_inter

@[simp]
theorem toFinset_eq_empty_iff (l : List α) : l.toFinset = ∅ ↔ l = nil := by
  cases l <;> simp
#align list.to_finset_eq_empty_iff List.toFinset_eq_empty_iff

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]
theorem toFinset_nonempty_iff (l : List α) : l.toFinset.Nonempty ↔ l ≠ [] := by
  simp [Finset.nonempty_iff_ne_empty]
#align list.to_finset_nonempty_iff List.toFinset_nonempty_iff

@[simp]
theorem toFinset_filter (s : List α) (p : α → Bool) :
    (s.filter p).toFinset = s.toFinset.filter (p ·) := by
  ext; simp [List.mem_filter]

end List

namespace Finset

section ToList

/-- Produce a list of the elements in the finite set using choice. -/
noncomputable def toList (s : Finset α) : List α :=
  s.1.toList
#align finset.to_list Finset.toList

theorem nodup_toList (s : Finset α) : s.toList.Nodup := by
  rw [toList, ← Multiset.coe_nodup, Multiset.coe_toList]
  exact s.nodup
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
  simp
#align finset.to_list_to_finset Finset.toList_toFinset

@[simp]
theorem toList_eq_singleton_iff {a : α} {s : Finset α} : s.toList = [a] ↔ s = {a} := by
  rw [toList, Multiset.toList_eq_singleton_iff, val_eq_singleton_iff]
#align finset.to_list_eq_singleton_iff Finset.toList_eq_singleton_iff

@[simp]
theorem toList_singleton : ∀ a, ({a} : Finset α).toList = [a] :=
  Multiset.toList_singleton
#align finset.to_list_singleton Finset.toList_singleton

theorem exists_list_nodup_eq [DecidableEq α] (s : Finset α) :
    ∃ l : List α, l.Nodup ∧ l.toFinset = s :=
  ⟨s.toList, s.nodup_toList, s.toList_toFinset⟩
#align finset.exists_list_nodup_eq Finset.exists_list_nodup_eq

open scoped List in
theorem toList_cons {a : α} {s : Finset α} (h : a ∉ s) : (cons a s h).toList ~ a :: s.toList :=
  (List.perm_ext_iff_of_nodup (nodup_toList _) (by simp [h, nodup_toList s])).2 fun x => by
    simp only [List.mem_cons, Finset.mem_toList, Finset.mem_cons]
#align finset.to_list_cons Finset.toList_cons

open scoped List in
theorem toList_insert [DecidableEq α] {a : α} {s : Finset α} (h : a ∉ s) :
    (insert a s).toList ~ a :: s.toList :=
  cons_eq_insert _ _ h ▸ toList_cons _
#align finset.to_list_insert Finset.toList_insert

end ToList

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
variable [DecidableEq α] {s t : Finset α}

open Finset

/-- The disjoint union of finsets is a sum -/
def Finset.union (s t : Finset α) (h : Disjoint s t) :
    s ⊕ t ≃ (s ∪ t : Finset α) :=
  Equiv.Set.ofEq (coe_union _ _) |>.trans (Equiv.Set.union (disjoint_coe.mpr h).le_bot) |>.symm

@[simp]
theorem Finset.union_symm_inl (h : Disjoint s t) (x : s) :
    Equiv.Finset.union s t h (Sum.inl x) = ⟨x, Finset.mem_union.mpr <| Or.inl x.2⟩ :=
  rfl

@[simp]
theorem Finset.union_symm_inr (h : Disjoint s t) (y : t) :
    Equiv.Finset.union s t h (Sum.inr y) = ⟨y, Finset.mem_union.mpr <| Or.inr y.2⟩ :=
  rfl

/-- The type of dependent functions on the disjoint union of finsets `s ∪ t` is equivalent to the
  type of pairs of functions on `s` and on `t`. This is similar to `Equiv.sumPiEquivProdPi`. -/
def piFinsetUnion {ι} [DecidableEq ι] (α : ι → Type*) {s t : Finset ι} (h : Disjoint s t) :
    ((∀ i : s, α i) × ∀ i : t, α i) ≃ ∀ i : (s ∪ t : Finset ι), α i :=
  let e := Equiv.Finset.union s t h
  sumPiEquivProdPi (fun b ↦ α (e b)) |>.symm.trans (.piCongrLeft (fun i : ↥(s ∪ t) ↦ α i) e)

end Equiv


namespace Multiset

variable [DecidableEq α]

theorem disjoint_toFinset {m1 m2 : Multiset α} :
    _root_.Disjoint m1.toFinset m2.toFinset ↔ m1.Disjoint m2 := by
  rw [Finset.disjoint_iff_ne]
  refine ⟨fun h a ha1 ha2 => ?_, ?_⟩
  · rw [← Multiset.mem_toFinset] at ha1 ha2
    exact h _ ha1 _ ha2 rfl
  · rintro h a ha b hb rfl
    rw [Multiset.mem_toFinset] at ha hb
    exact h ha hb
#align multiset.disjoint_to_finset Multiset.disjoint_toFinset

end Multiset

namespace List

variable [DecidableEq α] {l l' : List α}

theorem disjoint_toFinset_iff_disjoint : _root_.Disjoint l.toFinset l'.toFinset ↔ l.Disjoint l' :=
  Multiset.disjoint_toFinset
#align list.disjoint_to_finset_iff_disjoint List.disjoint_toFinset_iff_disjoint

end List

namespace Mathlib.Meta
open Qq Lean Meta Finset

/-- Attempt to prove that a finset is nonempty using the `finsetNonempty` aesop rule-set.

You can add lemmas to the rule-set by tagging them with either:
* `aesop safe apply (rule_sets := [finsetNonempty])` if they are always a good idea to follow or
* `aesop unsafe apply (rule_sets := [finsetNonempty])` if they risk directing the search to a blind
  alley.
-/
def proveFinsetNonempty {u : Level} {α : Q(Type u)} (s : Q(Finset $α)) :
    MetaM (Option Q(Finset.Nonempty $s)) := do
  -- Aesop expects to operate on goals, so we're going to make a new goal.
  let goal ← Lean.Meta.mkFreshExprMVar q(Finset.Nonempty $s)
  let mvar := goal.mvarId!
  -- We want this to be fast, so use only the basic and `Finset.Nonempty`-specific rules.
  let rulesets ← Aesop.Frontend.getGlobalRuleSets #[`builtin, `finsetNonempty]
  let options : Aesop.Options' :=
    { terminal := true, -- Fail if the new goal is not closed.
      generateScript := false,
      useDefaultSimpSet := false, -- Avoiding the whole simp set to speed up the tactic.
      warnOnNonterminal := false } -- Don't show a warning on failure, simply return `none`.
  let rules ← Aesop.mkLocalRuleSet rulesets options
  let (remainingGoals, _) ←
    try Aesop.search (options := options.toOptions) mvar (.some rules)
    catch _ => return none
  -- Fail if there are open goals remaining, this serves as an extra check for the
  -- Aesop configuration option `terminal := true`.
  if remainingGoals.size > 0 then return none
  Lean.getExprMVarAssignment? mvar

end Mathlib.Meta
