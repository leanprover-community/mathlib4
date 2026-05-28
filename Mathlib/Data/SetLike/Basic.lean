/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Tactic.Monotonicity.Attr
public import Mathlib.Tactic.SetLike
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Insert

/-!
# Typeclass for types with a set-like extensionality property

The `Membership` typeclass is used to let terms of a type have elements.
Many instances of `Membership` have a set-like extensionality property:
things are equal iff they have the same elements.  The `SetLike`
typeclass provides a unified interface to define a `Membership` that is
extensional in this way.

The main use of `SetLike` is for algebraic subobjects (such as
`Submonoid` and `Submodule`), whose non-proof data consists only of a
carrier set.  In such a situation, the projection to the carrier set
is injective.

In general, a type `A` is `SetLike` with elements of type `B` if it
has an injective map to `Set B`.  This module provides standard
boilerplate for every `SetLike`: a `coe_sort`, a `coe` to set,
and various extensionality and simp lemmas. The order induced by set inclusion is
called `PartialOrder.ofSetlike`: this is not an instance for flexibility in choosing orders.
The class `IsConcreteLE` abstractly states the order is equal to that induced by set inclusion;
an instance is automatically available when defining a `PartialOrder` as
`.ofSetLike (MySubobject X) X`.

A typical subobject should be declared as:
```
structure MySubobject (X : Type*) [ObjectTypeclass X] where
  (carrier : Set X)
  (op_mem' : ∀ {x : X}, x ∈ carrier → sorry ∈ carrier)

namespace MySubobject

variable {X : Type*} [ObjectTypeclass X] {x : X}

instance : SetLike (MySubobject X) X :=
  ⟨MySubobject.carrier, fun p q h => by cases p; cases q; congr!⟩

instance : PartialOrder (MySubobject X) := .ofSetLike (MySubobject X) X

@[simp] lemma mem_carrier {p : MySubobject X} : x ∈ p.carrier ↔ x ∈ (p : Set X) := Iff.rfl

@[ext] theorem ext {p q : MySubobject X} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := SetLike.ext h

/-- Copy of a `MySubobject` with a new `carrier` equal to the old one. Useful to fix definitional
equalities. See Note [range copy pattern]. -/
protected def copy (p : MySubobject X) (s : Set X) (hs : s = ↑p) : MySubobject X :=
  { carrier := s
    op_mem' := hs.symm ▸ p.op_mem' }

@[simp] lemma coe_copy (p : MySubobject X) (s : Set X) (hs : s = ↑p) :
  (p.copy s hs : Set X) = s := rfl

lemma copy_eq (p : MySubobject X) (s : Set X) (hs : s = ↑p) : p.copy s hs = p :=
  SetLike.coe_injective hs

end MySubobject
```

An alternative to `SetLike` could have been an extensional `Membership` typeclass:
```
class ExtMembership (α : out_param <| Type u) (β : Type v) extends Membership α β where
  (ext_iff : ∀ {s t : β}, s = t ↔ ∀ (x : α), x ∈ s ↔ x ∈ t)
```
While this is equivalent, `SetLike` conveniently uses a carrier set projection directly.

## Tags

subobjects
-/

@[expose] public section

assert_not_exists RelIso

/-- A class to indicate that there is a canonical injection between `A` and `Set B`.

This has the effect of giving terms of `A` elements of type `B` (through a `Membership`
instance) and a compatible coercion to `Type*` as a subtype.

Note: if `SetLike.coe` is a projection, implementers should create a simp lemma such as
```
@[simp] lemma mem_carrier {p : MySubobject X} : x ∈ p.carrier ↔ x ∈ (p : Set X) := Iff.rfl
```
to normalize terms.

If you declare an unbundled subclass of `SetLike`, for example:
```
class MulMemClass (S : Type*) (M : Type*) [Mul M] [SetLike S M] where
  ...
```
Then you should *not* repeat the `outParam` declaration so `SetLike` will supply the value instead.
This ensures your subclass will not have issues with synthesis of the `[Mul M]` parameter starting
before the value of `M` is known.
-/
@[notation_class* carrier Simps.findCoercionArgs]
class SetLike (A : Type*) (B : outParam Type*) where
  /-- The coercion from a term of a `SetLike` to its corresponding `Set`. -/
  protected coe : A → Set B
  /-- The coercion from a term of a `SetLike` to its corresponding `Set` is injective. -/
  protected coe_injective' : Function.Injective coe

attribute [coe] SetLike.coe

namespace SetLike

variable {A : Type*} {B : Type*} [i : SetLike A B]

instance : CoeTC A (Set B) where coe := SetLike.coe

instance (priority := 100) instMembership : Membership B A :=
  ⟨fun p x => x ∈ (p : Set B)⟩

instance (priority := 100) : CoeSort A (Type _) :=
  ⟨fun p => { x : B // x ∈ p }⟩

section Delab
open Lean PrettyPrinter.Delaborator SubExpr

/-- For terms that match the `CoeSort` instance's body, pretty print as `↥S`
rather than as `{ x // x ∈ S }`. The discriminating feature is that membership
uses the `SetLike.instMembership` instance. -/
@[app_delab Subtype]
meta def delabSubtypeSetLike : Delab := whenPPOption getPPNotation do
  let #[_, .lam n _ body _] := (← getExpr).getAppArgs | failure
  guard <| body.isAppOf ``Membership.mem
  let #[_, _, inst, _, .bvar 0] := body.getAppArgs | failure
  guard <| inst.isAppOfArity ``instMembership 3
  let S ← withAppArg <| withBindingBody n <| withNaryArg 3 delab
  `(↥$S)

end Delab

variable (p q : A)

@[simp, norm_cast]
theorem coe_sort_coe : ((p : Set B) : Type _) = p :=
  rfl

variable {p q}

protected theorem «exists» {q : p → Prop} : (∃ x, q x) ↔ ∃ (x : B) (h : x ∈ p), q ⟨x, ‹_›⟩ :=
  SetCoe.exists

protected theorem «forall» {q : p → Prop} : (∀ x, q x) ↔ ∀ (x : B) (h : x ∈ p), q ⟨x, ‹_›⟩ :=
  SetCoe.forall

theorem coe_injective : Function.Injective (SetLike.coe : A → Set B) := fun _ _ h =>
  SetLike.coe_injective' h

@[simp, norm_cast]
theorem coe_set_eq : (p : Set B) = q ↔ p = q :=
  coe_injective.eq_iff

@[norm_cast] lemma coe_ne_coe : (p : Set B) ≠ q ↔ p ≠ q := coe_injective.ne_iff

theorem ext' (h : (p : Set B) = q) : p = q :=
  coe_injective h

theorem ext'_iff : p = q ↔ (p : Set B) = q :=
  coe_set_eq.symm

/-- Note: implementers of `SetLike` must copy this lemma in order to tag it with `@[ext]`. -/
theorem ext (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q :=
  coe_injective <| Set.ext h

theorem ext_iff : p = q ↔ ∀ x, x ∈ p ↔ x ∈ q :=
  coe_injective.eq_iff.symm.trans Set.ext_iff

@[simp, push]
theorem mem_coe {x : B} : x ∈ (p : Set B) ↔ x ∈ p :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_eq_coe {x y : p} : (x : B) = y ↔ x = y :=
  Subtype.ext_iff.symm

@[simp]
theorem coe_mem (x : p) : (x : B) ∈ p :=
  x.2

@[aesop 5% (rule_sets := [SetLike!])]
lemma mem_of_subset {s : Set B} (hp : s ⊆ p) {x : B} (hx : x ∈ s) : x ∈ p := hp hx

@[simp]
protected theorem eta (x : p) (hx : (x : B) ∈ p) : (⟨x, hx⟩ : p) = x := rfl

@[simp] lemma setOf_mem_eq (a : A) : {b | b ∈ a} = a := rfl

@[nontriviality]
lemma mem_of_subsingleton [Subsingleton B] (S : A) [h : Nonempty S] {b : B} : b ∈ S := by
  obtain ⟨s, hs⟩ := nonempty_subtype.mp h
  simpa [Subsingleton.elim b s]

/-- If `s` is a proper element of a `SetLike` structure (i.e., `s ≠ ⊤`) and the top element
coerces to the universal set, then there exists an element not in `s`. -/
lemma exists_not_mem_of_ne_top [LE A] [OrderTop A] (s : A) (hs : s ≠ ⊤)
    (h_top : ((⊤ : A) : Set B) = Set.univ := by simp) :
    ∃ b : B, b ∉ s := by
  simpa [-SetLike.coe_set_eq, SetLike.ext'_iff, h_top, Set.ne_univ_iff_exists_notMem] using hs

end SetLike

/-- A class to indicate that the canonical injection between `A` and `Set B` is order-preserving.

An instance of this class is automatically available on any partial order defined as
`PartialOrder.ofSetLike`.
-/
class IsConcreteLE (A : Type*) (B : outParam Type*) [SetLike A B] [LE A] where
  /-- The coercion from a `SetLike` type preserves the ordering. -/
  protected coe_subset_coe' {S T : A} : SetLike.coe S ⊆ SetLike.coe T ↔ S ≤ T

section default

variable (A B : Type*) [SetLike A B]

/-- The order induced from a `SetLike` instance by inclusion. -/
@[reducible] def LE.ofSetLike : LE A where
  le := fun H K => ∀ ⦃x⦄, x ∈ H → x ∈ K

/-- The partial order induced from a `SetLike` instance by inclusion.

A partial order defined as `.ofSetLike` will automatically make available an instance
of `IsConcreteLE`.
-/
@[reducible] def PartialOrder.ofSetLike : PartialOrder A where
  __ := LE.ofSetLike A B
  __ := PartialOrder.lift (SetLike.coe : A → Set B) SetLike.coe_injective

instance : letI := PartialOrder.ofSetLike A B; IsConcreteLE A B :=
  letI := PartialOrder.ofSetLike A B; { coe_subset_coe' := Iff.rfl }

end default

namespace SetLike

variable {A B : Type*} [SetLike A B]

section LE

variable [LE A] [IsConcreteLE A B] {p q : A}

@[simp, norm_cast, gcongr] lemma coe_subset_coe {S T : A} : (S : Set B) ⊆ T ↔ S ≤ T :=
  IsConcreteLE.coe_subset_coe'

theorem le_def {S T : A} : S ≤ T ↔ ∀ ⦃x : B⦄, x ∈ S → x ∈ T := by
  simp [← coe_subset_coe, Set.subset_def]

@[gcongr low] -- lower priority than `Set.mem_of_subset_of_mem`
alias ⟨_root_.mem_of_le_of_mem, _⟩ := le_def

@[deprecated (since := "2026-01-07")] alias GCongr.mem_of_le_of_mem := _root_.mem_of_le_of_mem

theorem not_le_iff_exists : ¬p ≤ q ↔ ∃ x ∈ p, x ∉ q := by
  simpa [← coe_subset_coe] using Set.not_subset

end LE

section Preorder

variable [Preorder A] [IsConcreteLE A B] {p q : A}

@[gcongr, mono]
theorem coe_mono : Monotone (SetLike.coe : A → Set B) := fun _ _ => coe_subset_coe.mpr

end Preorder

section PartialOrder

variable [PartialOrder A] [IsConcreteLE A B] {p q : A}

@[simp, norm_cast, gcongr] lemma coe_ssubset_coe {S T : A} : (S : Set B) ⊂ T ↔ S < T := by
  rw [ssubset_iff_subset_ne, lt_iff_le_and_ne, coe_subset_coe, SetLike.coe_ne_coe]

@[gcongr, mono]
theorem coe_strictMono : StrictMono (SetLike.coe : A → Set B) := fun _ _ => coe_ssubset_coe.mpr

theorem exists_of_lt : p < q → ∃ x ∈ q, x ∉ p := by
  simpa [← coe_ssubset_coe] using Set.exists_of_ssubset

theorem lt_iff_le_and_exists : p < q ↔ p ≤ q ∧ ∃ x ∈ q, x ∉ p := by
  rw [lt_iff_le_not_ge, not_le_iff_exists]

theorem not_le_iff_exists_mem_notMem : ¬p ≤ q ↔ ∃ x, x ∈ p ∧ x ∉ q := by
  simpa only [← coe_subset_coe] using Set.not_subset_iff_exists_mem_notMem

theorem lt_of_mem_notMem {x : B} (hst : p ≤ q) (hat : x ∈ q) (has : x ∉ p) :
    p < q := by
  rw [← coe_subset_coe] at hst
  rw [← coe_ssubset_coe]
  exact HasSubset.Subset.ssubset_of_mem_notMem hst hat has

/-- membership is inherited from `Set X` -/
abbrev instSubtypeSet {X} {p : Set X → Prop} : SetLike {s // p s} X where
  coe := (↑)
  coe_injective' := Subtype.val_injective

/-- membership is inherited from `S` -/
abbrev instSubtype {X S} [SetLike S X] {p : S → Prop} : SetLike {s // p s} X where
  coe := (↑)
  coe_injective' := SetLike.coe_injective.comp Subtype.val_injective

section

attribute [local instance] instSubtypeSet instSubtype

@[simp] lemma mem_mk_set {X} {p : Set X → Prop} {U : Set X} {h : p U} {x : X} :
    x ∈ Subtype.mk U h ↔ x ∈ U := Iff.rfl

@[simp] lemma mem_mk {X S} [SetLike S X] {p : S → Prop} {U : S} {h : p U} {x : X} :
    x ∈ Subtype.mk U h ↔ x ∈ U := Iff.rfl

end

end PartialOrder

end SetLike


/- ## Concrete ## -/


/- # Bot # -/

class IsConcreteBot (A : Type*) (B : outParam Type*) [SetLike A B] [Bot A] where
  protected coe_bot' : (⊥ : A) = (⊥ : Set B)

namespace SetLike

variable {A B : Type*} [SetLike A B] [Bot A] [IsConcreteBot A B]

@[simp] lemma coe_bot : (⊥ : A) = (⊥ : Set B) := IsConcreteBot.coe_bot'

@[simp, grind =, push]
theorem mem_bot_iff_false {x : B} : x ∈ (⊥ : A) ↔ False := by simp [← mem_coe]

theorem eq_bot_iff_forall_notMem {a : A} : a = ⊥ ↔ ∀ x, x ∉ a := by
  simp [← coe_set_eq, ← mem_coe, Set.eq_empty_iff_forall_notMem]

theorem eq_bot_of_forall_notMem {a : A} (h : ∀ x, x ∉ a) : a = ⊥ :=
  eq_bot_iff_forall_notMem.mpr h

theorem forall_mem_bot {p : B → Prop} : (∀ x ∈ (⊥ : A), p x) ↔ True := by simp

section LE

variable [LE A] [IsConcreteLE A B]

instance : OrderBot A where
  bot_le:= by simp [← coe_subset_coe]

end LE


/- # Empty # -/

end SetLike

class IsConcreteEmpty (A : Type*) (B : outParam Type*) [SetLike A B] [EmptyCollection A] where
  protected coe_empty' : (∅ : A) = (∅ : Set B)

namespace SetLike

variable {A B : Type*} [setLike : SetLike A B] [EmptyCollection A] [IsConcreteEmpty A B]

@[simp] lemma coe_empty : (∅ : A) = (∅ : Set B) := IsConcreteEmpty.coe_empty'

@[simp, grind =, push]
theorem mem_empty_iff_false {x : B} : x ∈ (∅ : A) ↔ False := by simp [← mem_coe]

theorem eq_empty_iff_forall_notMem {a : A} : a = ∅ ↔ ∀ x, x ∉ a := by
  simp [← coe_set_eq, ← mem_coe, Set.eq_empty_iff_forall_notMem]

theorem eq_empty_of_forall_notMem {a : A} (h : ∀ x, x ∉ a) : a = ∅ :=
  eq_empty_iff_forall_notMem.mpr h

theorem forall_mem_empty {p : B → Prop} : (∀ x ∈ (∅ : A), p x) ↔ True := by simp

section LE

variable [LE A] [IsConcreteLE A B]

include setLike in
@[simp] theorem empty_le (a : A) : ∅ ≤ a := by simp [← coe_subset_coe]

include setLike in
@[simp, grind =]
theorem le_empty_iff {a : A} : a ≤ ∅ ↔ a = ∅ := by simp [← coe_set_eq, ← coe_subset_coe]

include setLike in
theorem eq_empty_of_le_empty {a : A} : a ≤ ∅ → a = ∅ := le_empty_iff.1

include setLike in
theorem le_eq_empty {a b : A} (h : b ≤ a) (e : a = ∅) : b = ∅ := by
  rw [← coe_set_eq] at ⊢ e
  rw [← coe_subset_coe] at h
  rw [coe_empty] at ⊢ e
  exact Set.subset_eq_empty h e

end LE

-- TODO: theorems about SetLike.nonempty once implemented

end SetLike


/- # Top # -/

class IsConcreteTop (A : Type*) (B : outParam Type*) [SetLike A B] [Top A] where
  protected coe_top' : (⊤ : A) = (⊤ : Set B)

namespace SetLike

variable {A B : Type*} [SetLike A B] [Top A] [IsConcreteTop A B]

@[simp] lemma coe_top : (⊤ : A) = (⊤ : Set B) := IsConcreteTop.coe_top'

section Bot

variable [Bot A] [IsConcreteBot A B]

theorem bot_ne_top [Nonempty B] : (⊥ : A) ≠ ⊤ := by
  simpa [← coe_set_eq] using Set.empty_ne_univ

end Bot

theorem eq_top_iff_forall {a : A} : a = ⊤ ↔ ∀ x, x ∈ a := by
  simpa [← coe_set_eq] using Set.eq_univ_iff_forall

theorem eq_top_of_forall {a : A} : (∀ x, x ∈ a) → a = ⊤ := eq_top_iff_forall.2

variable (B) in
theorem exists_mem_top_of_nonempty : ∀ [Nonempty B], ∃ x : B, x ∈ (⊤ : A) := by
  simp_rw [← mem_coe, coe_top]
  exact Set.exists_mem_of_nonempty B

theorem ne_top_iff_exists_notMem (a : A) : a ≠ ⊤ ↔ ∃ x, x ∉ a := by
  rw [← not_forall, ← eq_top_iff_forall]

section LE

variable [LE A] [IsConcreteLE A B]

instance : OrderTop A where
  le_top := by simp [← coe_subset_coe]

end LE

end SetLike


/- # Univ # -/

class HasConcreteUniv (A : Type*) (B : outParam Type*) [SetLike A B] where
  protected univ' : A
  protected coe_univ' : (univ' : A) = (Set.univ : Set B)

namespace SetLike

variable {A B : Type*} [setLike : SetLike A B] [HasConcreteUniv A B]

def univ : A := HasConcreteUniv.univ'

@[simp] lemma coe_univ : (SetLike.univ : A) = (Set.univ : Set B) := HasConcreteUniv.coe_univ'

section Empty

variable [EmptyCollection A] [IsConcreteEmpty A B]

theorem empty_ne_univ [Nonempty B] : (∅ : A) ≠ univ := by
  simp only [ne_eq, ← coe_set_eq, coe_empty, coe_univ]
  exact Set.empty_ne_univ

end Empty

theorem eq_univ_iff_forall {a : A} : a = univ ↔ ∀ x, x ∈ a := by
  simp only [← coe_set_eq, coe_univ]
  exact Set.eq_univ_iff_forall

theorem eq_univ_of_forall {a : A} : (∀ x, x ∈ a) → a = univ := eq_univ_iff_forall.2

variable (B) in
theorem exists_mem_of_nonempty : ∀ [Nonempty B], ∃ x : B, x ∈ (univ : A) := by
  simp_rw [← mem_coe, coe_univ]
  exact Set.exists_mem_of_nonempty B

theorem ne_univ_iff_exists_notMem (a : A) : a ≠ univ ↔ ∃ x, x ∉ a := by
  rw [← not_forall, ← eq_univ_iff_forall]

section LE

variable [LE A] [IsConcreteLE A B]

theorem not_univ_le {a : A} : ¬univ ≤ a ↔ ∃ x, x ∉ a := by
  simp only [← coe_subset_coe, coe_univ]
  exact Set.not_univ_subset

@[simp, grind ←]
theorem le_univ (a : A) : a ≤ univ := by simp [← coe_subset_coe]

@[simp, grind =]
theorem univ_le_iff {a : A} : univ ≤ a ↔ a = univ := by
  simp [← coe_subset_coe, ← coe_set_eq]

theorem eq_univ_of_le {a b : A} (h : a ≤ b) (hs : a = univ) : b = univ := by
  rw [← coe_set_eq] at ⊢ hs
  rw [← coe_subset_coe] at h
  rw [coe_univ] at ⊢ hs
  exact Set.eq_univ_of_subset h hs

end LE

section PartialOrder

variable [PartialOrder A] [IsConcreteLE A B]

theorem lt_univ_iff {a : A} : a < univ ↔ a ≠ univ := by
  simp only [← coe_ssubset_coe, coe_univ, ne_eq, ← coe_set_eq]
  exact Set.ssubset_univ_iff

end PartialOrder

-- TODO: theorems about SetLike.Nonempty once impemented

end SetLike


/- # Insert # -/

class IsConcreteInsert (A : Type*) (B : outParam Type*) [SetLike A B] [Insert B A] where
  protected coe_insert' (x : B) (s : A) : (insert x s : A) = insert x (s : Set B)

namespace SetLike

variable {A B : Type*} [SetLike A B] [Insert B A] [IsConcreteInsert A B]
variable {x y : B} {a b : A}

@[simp] lemma coe_insert (x : B) (s : A) : (insert x s : A) = insert x (s : Set B) :=
  IsConcreteInsert.coe_insert' x s

theorem mem_insert (x : B) (a : A) : x ∈ insert x a := by simp [← mem_coe]

theorem mem_insert_of_mem {x : B} {a : A} (y : B) : x ∈ a → x ∈ insert y a := by
  simpa [← mem_coe] using Set.mem_insert_of_mem y

theorem eq_or_mem_of_mem_insert {x y : B} {a : A} : x ∈ insert y a → x = y ∨ x ∈ a := by
  simp [← mem_coe]

theorem mem_of_mem_insert_of_ne {x y : B} {a : A} : y ∈ insert x a → y ≠ x → y ∈ a := by
  simpa [← mem_coe] using Set.mem_of_mem_insert_of_ne

theorem eq_of_mem_insert_of_notMem {x y : B} {a : A} : y ∈ insert x a → y ∉ a → y = x := by
  simpa [← mem_coe] using Set.eq_of_mem_insert_of_notMem

@[simp, grind =, push]
theorem mem_insert_iff {x y : B} {a : A} : x ∈ insert y a ↔ x = y ∨ x ∈ a := by simp [← mem_coe]

@[simp]
theorem insert_eq_of_mem {x : B} {a : A} (h : x ∈ a) : insert x a = a := by simp [← coe_set_eq, h]

theorem ne_insert_of_notMem {a : A} (b : A) {x : B} : x ∉ a → a ≠ insert x b := by grind

@[simp]
theorem insert_eq_self {x : B} {a : A} : insert x a = a ↔ x ∈ a := by simp [← coe_set_eq]

theorem insert_ne_self {x : B} {a : A} : insert x a ≠ a ↔ x ∉ a := by simp [← coe_set_eq]

theorem insert_comm (x y : B) (a : A) : insert x (insert y a) = insert y (insert x a) := by
  simpa [← coe_set_eq] using Set.insert_comm x y a

theorem insert_insert (x : B) (a : A) : insert x (insert x a) = insert x a := by simp

-- -- useful in proofs by induction
-- theorem forall_of_forall_insert {P : α → Prop} {a : α} {s : Set α} (H : ∀ x, x ∈ insert a s → P x)
--     (x) (h : x ∈ s) : P x := by grind

-- theorem forall_insert_of_forall {P : α → Prop} {a : α} {s : Set α} (H : ∀ x, x ∈ s → P x) (ha : P a)
--     (x) (h : x ∈ insert a s) : P x := by grind

-- theorem exists_mem_insert {P : α → Prop} {a : α} {s : Set α} :
--     (∃ x ∈ insert a s, P x) ↔ (P a ∨ ∃ x ∈ s, P x) := by grind

-- theorem forall_mem_insert {P : α → Prop} {a : α} {s : Set α} :
--     (∀ x ∈ insert a s, P x) ↔ P a ∧ ∀ x ∈ s, P x := by grind

-- /-- Inserting an element to a set is equivalent to the option type. -/
-- def subtypeInsertEquivOption
--     [DecidableEq α] {t : Set α} {x : α} (h : x ∉ t) :
--     { i // i ∈ insert x t } ≃ Option { i // i ∈ t } where
--   toFun y := if h : ↑y = x then none else some ⟨y, by grind⟩
--   invFun y := (y.elim ⟨x, mem_insert _ _⟩) fun z => ⟨z, by grind⟩
--   left_inv y := by grind
--   right_inv := by rintro (_ | y) <;> grind

section LE

variable [LE A] [IsConcreteLE A B]

@[simp]
theorem le_insert (x : B) (a : A) : a ≤ insert x a := by simp [← coe_subset_coe]

theorem insert_le_iff {x : B} {a b : A} : insert x a ≤ b ↔ x ∈ b ∧ a ≤ b := by
  simpa [← coe_subset_coe] using Set.insert_subset_iff

theorem insert_le {x : B} {a b : A} (hx : x ∈ b) (h : a ≤ b) : insert x a ≤ b := by
  rw [← coe_subset_coe] at ⊢ h
  rw [coe_insert]
  exact Set.insert_subset hx h

@[gcongr]
theorem insert_le_insert {x : B} {a b : A} (h : a ≤ b) : insert x a ≤ insert x b := by
  rw [← coe_subset_coe] at ⊢ h
  repeat rw [coe_insert]
  exact Set.insert_subset_insert h

@[simp] theorem insert_le_insert_iff (hxa : x ∉ a) : insert x a ≤ insert x b ↔ a ≤ b := by
  simpa [← coe_subset_coe] using Set.insert_subset_insert_iff hxa

theorem le_insert_iff_of_notMem (hxa : x ∉ a) : a ≤ insert x b ↔ a ≤ b := by
  simpa [← coe_subset_coe] using Set.subset_insert_iff_of_notMem hxa

end LE

section PartialOrder

variable [PartialOrder A] [IsConcreteLE A B]

theorem lt_iff_insert : a < b ↔ ∃ x ∉ a, insert x a ≤ b := by
  simpa [← coe_ssubset_coe, ← coe_subset_coe] using Set.ssubset_iff_insert

theorem lt_insert (h : x ∉ a) : a < insert x a := by
  simpa [← coe_ssubset_coe] using Set.ssubset_insert h

end PartialOrder

-- TODO: lemmas involving sup/inf

end SetLike


/- # Singleton # -/

class IsConcreteSingleton (A : Type*) (B : outParam Type*) [SetLike A B] [Singleton B A] where
  protected coe_singleton' (x : B) : ({x} : A) = ({x} : Set B)

namespace SetLike

variable {A B : Type*} [SetLike A B] [Singleton B A] [IsConcreteSingleton A B]
variable {x y : B} {a b : A}

@[simp] lemma coe_singleton (x : B) : ({x} : A) = ({x} : Set B) :=
  IsConcreteSingleton.coe_singleton' x

@[simp, grind =, push]
theorem mem_singleton_iff : x ∈ ({y} : A) ↔ x = y := by simp [← mem_coe]

theorem notMem_singleton_iff : x ∉ ({y} : A) ↔ x ≠ y := by simp [← mem_coe]

-- theorem mem_singleton (a : α) : a ∈ ({a} : Set α) :=
--   @rfl _ _

-- theorem eq_of_mem_singleton {x y : α} (h : x ∈ ({y} : Set α)) : x = y :=
--   h

-- @[simp]
-- theorem singleton_eq_singleton_iff {x y : α} : {x} = ({y} : Set α) ↔ x = y :=
--   Set.ext_iff.trans eq_iff_eq_cancel_left

-- theorem singleton_injective : Injective (singleton : α → Set α) := fun _ _ =>
--   singleton_eq_singleton_iff.mp

-- theorem mem_singleton_of_eq {x y : α} (H : x = y) : x ∈ ({y} : Set α) :=
--   H

-- @[simp]
-- theorem singleton_ne_empty (a : α) : ({a} : Set α) ≠ ∅ :=
--   (singleton_nonempty _).ne_empty

-- @[simp]
-- theorem empty_ne_singleton (a : α) : ∅ ≠ ({a} : Set α) :=
--   (singleton_ne_empty a).symm

-- theorem empty_ssubset_singleton : (∅ : Set α) ⊂ {a} :=
--   (singleton_nonempty _).empty_ssubset

-- @[simp, grind =]
-- theorem singleton_subset_iff {a : α} {s : Set α} : {a} ⊆ s ↔ a ∈ s :=
--   forall_eq

-- @[gcongr]
-- theorem singleton_subset_singleton : ({a} : Set α) ⊆ {b} ↔ a = b := by simp

section LawfulSingleton

variable [EmptyCollection A] [IsConcreteEmpty A B] [Insert B A] [IsConcreteInsert A B]

instance : LawfulSingleton B A where
  insert_empty_eq := by simp [← coe_set_eq]

theorem singleton_def (x : B) : ({x} : A) = insert x ∅ := by simp

-- theorem pair_eq_singleton (a : α) : ({a, a} : Set α) = {a} :=
--   union_self _

-- theorem pair_comm (a b : α) : ({a, b} : Set α) = {b, a} :=
--   union_comm _ _

-- theorem pair_eq_pair_iff {x y z w : α} :
--     ({x, y} : Set α) = {z, w} ↔ x = z ∧ y = w ∨ x = w ∧ y = z := by
--   simp [subset_antisymm_iff, insert_subset_iff]; aesop

-- theorem pair_subset_iff : {a, b} ⊆ s ↔ a ∈ s ∧ b ∈ s := by grind

-- theorem pair_subset (ha : a ∈ s) (hb : b ∈ s) : {a, b} ⊆ s :=
--   pair_subset_iff.2 ⟨ha,hb⟩

-- theorem subset_pair_iff : s ⊆ {a, b} ↔ ∀ x ∈ s, x = a ∨ x = b := by grind

-- theorem subset_pair_iff_eq {x y : α} : s ⊆ {x, y} ↔ s = ∅ ∨ s = {x} ∨ s = {y} ∨ s = {x, y} where
--   mp := by grind
--   mpr := by grind

end LawfulSingleton

section Univ

variable [HasConcreteUniv A B]

theorem univ_unique [Unique B] : (univ : A) = {default} := by
  simpa [← coe_set_eq] using Set.univ_unique

end Univ

-- TODO: add theorems

end SetLike


/- # Compl # -/

class IsConcreteCompl (A : Type*) (B : outParam Type*) [SetLike A B] [Compl A] where
  protected coe_compl' (a : A) : (aᶜ : A) = (aᶜ : Set B)

namespace SetLike

variable {A B : Type*} [SetLike A B] [Compl A] [IsConcreteCompl A B]

@[simp] lemma coe_compl (a : A) : (aᶜ : A) = (aᶜ : Set B) := IsConcreteCompl.coe_compl' a

-- TODO: add theorems

end SetLike
