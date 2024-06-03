/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Monotonicity.Attr
import Mathlib.Tactic.SetLike

#align_import data.set_like.basic from "leanprover-community/mathlib"@"feb99064803fd3108e37c18b0f77d0a8344677a3"

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
structure MySubobject (X : Type*) [ObjectTypeclass X] :=
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
class ExtMembership (α : out_param <| Type u) (β : Type v) extends Membership α β :=
  (ext_iff : ∀ {s t : β}, s = t ↔ ∀ (x : α), x ∈ s ↔ x ∈ t)
```
While this is equivalent, `SetLike` conveniently uses a carrier set projection directly.

## Tags

subobjects
-/


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
@[notation_class * carrier Simps.findCoercionArgs]
class SetLike (A : Type*) (B : outParam Type*) where
  /-- The coercion from a term of a `SetLike` to its corresponding `Set`. -/
  protected coe : A → Set B
  /-- The coercion from a term of a `SetLike` to its corresponding `Set` is injective. -/
  protected coe_injective' : Function.Injective coe
#align set_like SetLike

attribute [coe] SetLike.coe
namespace SetLike

variable {A : Type*} {B : Type*} [i : SetLike A B]

instance : CoeTC A (Set B) where coe := SetLike.coe

instance (priority := 100) instMembership : Membership B A :=
  ⟨fun x p => x ∈ (p : Set B)⟩

instance (priority := 100) : CoeSort A (Type _) :=
  ⟨fun p => { x : B // x ∈ p }⟩

section Delab
open Lean PrettyPrinter.Delaborator SubExpr

/-- For terms that match the `CoeSort` instance's body, pretty print as `↥S`
rather than as `{ x // x ∈ S }`. The discriminating feature is that membership
uses the `SetLike.instMembership` instance. -/
@[delab app.Subtype]
def delabSubtypeSetLike : Delab := whenPPOption getPPNotation do
  let #[_, .lam n _ body _] := (← getExpr).getAppArgs | failure
  guard <| body.isAppOf ``Membership.mem
  let #[_, _, inst, .bvar 0, _] := body.getAppArgs | failure
  guard <| inst.isAppOfArity ``instMembership 3
  let S ← withAppArg <| withBindingBody n <| withNaryArg 4 delab
  `(↥$S)

end Delab

variable (p q : A)

@[simp, norm_cast]
theorem coe_sort_coe : ((p : Set B) : Type _) = p :=
  rfl
#align set_like.coe_sort_coe SetLike.coe_sort_coe

variable {p q}

protected theorem «exists» {q : p → Prop} : (∃ x, q x) ↔ ∃ (x : B) (h : x ∈ p), q ⟨x, ‹_›⟩ :=
  SetCoe.exists
#align set_like.exists SetLike.exists

protected theorem «forall» {q : p → Prop} : (∀ x, q x) ↔ ∀ (x : B) (h : x ∈ p), q ⟨x, ‹_›⟩ :=
  SetCoe.forall
#align set_like.forall SetLike.forall

theorem coe_injective : Function.Injective (SetLike.coe : A → Set B) := fun _ _ h =>
  SetLike.coe_injective' h
#align set_like.coe_injective SetLike.coe_injective

@[simp, norm_cast]
theorem coe_set_eq : (p : Set B) = q ↔ p = q :=
  coe_injective.eq_iff
#align set_like.coe_set_eq SetLike.coe_set_eq

@[norm_cast] lemma coe_ne_coe : (p : Set B) ≠ q ↔ p ≠ q := coe_injective.ne_iff

theorem ext' (h : (p : Set B) = q) : p = q :=
  coe_injective h
#align set_like.ext' SetLike.ext'

theorem ext'_iff : p = q ↔ (p : Set B) = q :=
  coe_set_eq.symm
#align set_like.ext'_iff SetLike.ext'_iff

/-- Note: implementers of `SetLike` must copy this lemma in order to tag it with `@[ext]`. -/
theorem ext (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q :=
  coe_injective <| Set.ext h
#align set_like.ext SetLike.ext

theorem ext_iff : p = q ↔ ∀ x, x ∈ p ↔ x ∈ q :=
  coe_injective.eq_iff.symm.trans Set.ext_iff
#align set_like.ext_iff SetLike.ext_iff

@[simp]
theorem mem_coe {x : B} : x ∈ (p : Set B) ↔ x ∈ p :=
  Iff.rfl
#align set_like.mem_coe SetLike.mem_coe

@[simp, norm_cast]
theorem coe_eq_coe {x y : p} : (x : B) = y ↔ x = y :=
  Subtype.ext_iff_val.symm
#align set_like.coe_eq_coe SetLike.coe_eq_coe

-- Porting note: this is not necessary anymore due to the way coercions work
#noalign set_like.coe_mk

@[simp]
theorem coe_mem (x : p) : (x : B) ∈ p :=
  x.2
#align set_like.coe_mem SetLike.coe_mem

@[aesop 5% apply (rule_sets := [SetLike])]
lemma mem_of_subset {s : Set B} (hp : s ⊆ p) {x : B} (hx : x ∈ s) : x ∈ p := hp hx

-- Porting note: removed `@[simp]` because `simpNF` linter complained
protected theorem eta (x : p) (hx : (x : B) ∈ p) : (⟨x, hx⟩ : p) = x := rfl
#align set_like.eta SetLike.eta

instance (priority := 100) instPartialOrder : PartialOrder A :=
  { PartialOrder.lift (SetLike.coe : A → Set B) coe_injective with
    le := fun H K => ∀ ⦃x⦄, x ∈ H → x ∈ K }

theorem le_def {S T : A} : S ≤ T ↔ ∀ ⦃x : B⦄, x ∈ S → x ∈ T :=
  Iff.rfl
#align set_like.le_def SetLike.le_def

@[simp, norm_cast]
theorem coe_subset_coe {S T : A} : (S : Set B) ⊆ T ↔ S ≤ T :=
  Iff.rfl
#align set_like.coe_subset_coe SetLike.coe_subset_coe

@[mono]
theorem coe_mono : Monotone (SetLike.coe : A → Set B) := fun _ _ => coe_subset_coe.mpr
#align set_like.coe_mono SetLike.coe_mono

@[simp, norm_cast]
theorem coe_ssubset_coe {S T : A} : (S : Set B) ⊂ T ↔ S < T :=
  Iff.rfl
#align set_like.coe_ssubset_coe SetLike.coe_ssubset_coe

@[mono]
theorem coe_strictMono : StrictMono (SetLike.coe : A → Set B) := fun _ _ => coe_ssubset_coe.mpr
#align set_like.coe_strict_mono SetLike.coe_strictMono

theorem not_le_iff_exists : ¬p ≤ q ↔ ∃ x ∈ p, x ∉ q :=
  Set.not_subset
#align set_like.not_le_iff_exists SetLike.not_le_iff_exists

theorem exists_of_lt : p < q → ∃ x ∈ q, x ∉ p :=
  Set.exists_of_ssubset
#align set_like.exists_of_lt SetLike.exists_of_lt

theorem lt_iff_le_and_exists : p < q ↔ p ≤ q ∧ ∃ x ∈ q, x ∉ p := by
  rw [lt_iff_le_not_le, not_le_iff_exists]
#align set_like.lt_iff_le_and_exists SetLike.lt_iff_le_and_exists

end SetLike
