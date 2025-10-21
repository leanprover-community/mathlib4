/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Tactic.Monotonicity.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Data.Set.Basic

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
boilerplate for every `SetLike`: a `coe_sort`, a `coe` to set, a
`PartialOrder`, and various extensionality and simp lemmas.

A typical subobject should be declared as:
```
structure MySubobject (X : Type*) [ObjectTypeclass X] where
  (carrier : Set X)
  (op_mem' : ∀ {x : X}, x ∈ carrier → sorry ∈ carrier)

namespace MySubobject

variable {X : Type*} [ObjectTypeclass X] {x : X}

instance : SetLike (MySubobject X) X :=
  ⟨MySubobject.carrier, fun p q h => by cases p; cases q; congr!⟩

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
def delabSubtypeSetLike : Delab := whenPPOption getPPNotation do
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

@[simp]
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

instance (priority := 100) instPartialOrder : PartialOrder A :=
  { PartialOrder.lift (SetLike.coe : A → Set B) coe_injective with
    le := fun H K => ∀ ⦃x⦄, x ∈ H → x ∈ K }

theorem le_def {S T : A} : S ≤ T ↔ ∀ ⦃x : B⦄, x ∈ S → x ∈ T :=
  Iff.rfl

@[simp, norm_cast] lemma coe_subset_coe {S T : A} : (S : Set B) ⊆ T ↔ S ≤ T := .rfl
@[simp, norm_cast] lemma coe_ssubset_coe {S T : A} : (S : Set B) ⊂ T ↔ S < T := .rfl

@[gcongr low] -- lower priority than `Set.mem_of_subset_of_mem`
protected alias ⟨GCongr.mem_of_le_of_mem, _⟩ := le_def
@[gcongr] protected alias ⟨_, GCongr.coe_subset_coe⟩ := coe_subset_coe
@[gcongr] protected alias ⟨_, GCongr.coe_ssubset_coe⟩ := coe_ssubset_coe

@[mono]
theorem coe_mono : Monotone (SetLike.coe : A → Set B) := fun _ _ => coe_subset_coe.mpr

@[mono]
theorem coe_strictMono : StrictMono (SetLike.coe : A → Set B) := fun _ _ => coe_ssubset_coe.mpr

theorem not_le_iff_exists : ¬p ≤ q ↔ ∃ x ∈ p, x ∉ q :=
  Set.not_subset

theorem exists_of_lt : p < q → ∃ x ∈ q, x ∉ p :=
  Set.exists_of_ssubset

theorem lt_iff_le_and_exists : p < q ↔ p ≤ q ∧ ∃ x ∈ q, x ∉ p := by
  rw [lt_iff_le_not_ge, not_le_iff_exists]

/-- membership is inherited from `Set X` -/
abbrev instSubtypeSet {X} {p : Set X → Prop} : SetLike {s // p s} X where
  coe := (↑)
  coe_injective' := Subtype.val_injective

/-- membership is inherited from `S` -/
abbrev instSubtype {X S} [SetLike S X] {p : S → Prop} : SetLike {s // p s} X where
  coe := (↑)
  coe_injective' := SetLike.coe_injective.comp Subtype.val_injective

instance {α : Type*} (r : α → α → Prop) : SetLike (Quot r) α where
  coe := Quot.toSet
  coe_injective' := Quot.toSet_injective

instance {α : Type*} (s : Setoid α) : SetLike (Quotient s) α where
  coe := Quotient.toSet
  coe_injective' := Quotient.toSet_injective

section

attribute [local instance] instSubtypeSet instSubtype

@[simp] lemma mem_mk_set {X} {p : Set X → Prop} {U : Set X} {h : p U} {x : X} :
    x ∈ Subtype.mk U h ↔ x ∈ U := Iff.rfl

@[simp] lemma mem_mk {X S} [SetLike S X] {p : S → Prop} {U : S} {h : p U} {x : X} :
    x ∈ Subtype.mk U h ↔ x ∈ U := Iff.rfl

end

@[nontriviality]
lemma mem_of_subsingleton {A F} [Subsingleton A] [SetLike F A] (S : F) [h : Nonempty S] {a : A} :
    a ∈ S := by
  obtain ⟨s, hs⟩ := nonempty_subtype.mp h
  simpa [Subsingleton.elim a s]

end SetLike
