/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Tactic.Monotonicity.Attr
public import Mathlib.Tactic.SetLike
public import Mathlib.Data.Set.Basic

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
  coe_injective : Function.Injective coe

attribute [coe] SetLike.coe

namespace SetLike

variable {A : Type*} {B : Type*} [i : SetLike A B]

@[deprecated (since := "2026-06-04")] alias coe_injective' := coe_injective

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

@[simp] lemma setOfPred_mem_eq (a : A) : {b | b ∈ a} = a := rfl

@[deprecated (since := "2026-07-09")] alias setOf_mem_eq := setOfPred_mem_eq

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

/--
A class to indicate that the order on a type corresponds to set inclusion.
An instance of this class is automatically available on any order defined via `LE.ofSetLike`.
-/
class IsConcreteLE (A : Type*) (B : outParam Type*) [Membership B A] [LE A] where
  /-- The order corresponds to set inclusion. -/
  protected le_iff {S T : A} : S ≤ T ↔ ∀ ⦃x⦄, x ∈ S → x ∈ T

section default

variable (A B : Type*)

/-- The order induced from a `Membership` instance by inclusion.
An order defined this way automatically makes available an instance of `IsConcreteLE`.
-/
@[reducible] def LE.ofSetLike [Membership B A] : LE A where
  le := fun H K ↦ ∀ ⦃x⦄, x ∈ H → x ∈ K

instance [Membership B A] : letI := LE.ofSetLike A B; IsConcreteLE A B :=
  letI := LE.ofSetLike A B; { le_iff := .rfl }

/-- The preorder induced from a `Membership` instance by inclusion.
A preorder defined this way automatically makes available an instance of `IsConcreteLE`.
-/
@[reducible] def Preorder.ofSetLike [Membership B A] : Preorder A where
  __ := LE.ofSetLike A B
  lt s t := letI := LE.ofSetLike A B; s ≤ t ∧ ¬t ≤ s
  le_refl _ _ h := h
  le_trans _ _ _ h₁ h₂ _ h₃ := h₂ (h₁ h₃)

/-- The partial order induced from a `SetLike` instance by inclusion.
A partial order defined this way automatically makes available an instance of `IsConcreteLE`.
-/
@[reducible] def PartialOrder.ofSetLike [SetLike A B] : PartialOrder A where
  __ := Preorder.ofSetLike A B
  __ := PartialOrder.lift (SetLike.coe : A → Set B) SetLike.coe_injective

end default

namespace SetLike

section Membership

variable {A B : Type*} [Membership B A]

section LE

variable [LE A] [IsConcreteLE A B] {p q : A}

alias le_def := IsConcreteLE.le_iff

@[gcongr low] -- lower priority than `Set.mem_of_subset_of_mem`
alias ⟨_root_.mem_of_le_of_mem, _⟩ := le_def

theorem not_le_iff_exists : ¬p ≤ q ↔ ∃ x ∈ p, x ∉ q := by
  simp [le_def]

end LE

section PartialOrder

variable [PartialOrder A] [IsConcreteLE A B] {p q : A}

theorem lt_iff_le_and_exists : p < q ↔ p ≤ q ∧ ∃ x ∈ q, x ∉ p := by
  rw [lt_iff_le_not_ge, not_le_iff_exists]

theorem exists_of_lt (h : p < q) : ∃ x ∈ q, x ∉ p :=
  (lt_iff_le_and_exists.mp h).2

end PartialOrder

end Membership

section SetLike

variable {A B : Type*} [SetLike A B]

section LE

variable [LE A] [IsConcreteLE A B] {p q : A}

@[simp, norm_cast, gcongr] lemma coe_subset_coe : (p : Set B) ⊆ q ↔ p ≤ q :=
  (SetLike.le_def (A := A)).symm

end LE

section Preorder

variable [Preorder A] [IsConcreteLE A B]

@[gcongr, mono]
theorem coe_mono : Monotone (SetLike.coe : A → Set B) := fun _ _ => coe_subset_coe.mpr

end Preorder

section PartialOrder

variable [PartialOrder A] [IsConcreteLE A B] {p q : A}

@[simp, norm_cast, gcongr] lemma coe_ssubset_coe : (p : Set B) ⊂ q ↔ p < q := by
  rw [ssubset_iff_subset_ne, lt_iff_le_and_ne, coe_subset_coe, SetLike.coe_ne_coe]

@[gcongr, mono]
theorem coe_strictMono : StrictMono (SetLike.coe : A → Set B) := fun _ _ => coe_ssubset_coe.mpr

/-- membership is inherited from `Set X` -/
abbrev instSubtypeSet {X} {p : Set X → Prop} : SetLike {s // p s} X where
  coe := (↑)
  coe_injective := Subtype.val_injective

/-- membership is inherited from `S` -/
abbrev instSubtype {X S} [SetLike S X] {p : S → Prop} : SetLike {s // p s} X where
  coe := (↑)
  coe_injective := SetLike.coe_injective.comp Subtype.val_injective

section

attribute [local instance] instSubtypeSet instSubtype

@[simp] lemma mem_mk_set {X} {p : Set X → Prop} {U : Set X} {h : p U} {x : X} :
    x ∈ Subtype.mk U h ↔ x ∈ U := Iff.rfl

@[simp] lemma mem_mk {X S} [SetLike S X] {p : S → Prop} {U : S} {h : p U} {x : X} :
    x ∈ Subtype.mk U h ↔ x ∈ U := Iff.rfl

end

end PartialOrder

end SetLike

end SetLike
