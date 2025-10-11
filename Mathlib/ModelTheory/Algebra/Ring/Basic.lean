/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import Mathlib.Algebra.Ring.Equiv

/-!
# First-Order Language of Rings

This file defines the first-order language of rings, as well as defining instance of `Add`, `Mul`,
etc. on terms in the language.

## Main Definitions

- `FirstOrder.Language.ring` : the language of rings, with function symbols `+`, `*`, `-`, `0`, `1`
- `FirstOrder.Ring.CompatibleRing` : A class stating that a type is a `Language.ring.Structure`, and
  that this structure is the same as the structure given by the classes `Add`, `Mul`, etc. already
  on `R`.
- `FirstOrder.Ring.compatibleRingOfRing` : Given a type `R` with instances for each of the `Ring`
  operations, make a `compatibleRing` instance.

## Implementation Notes

There are implementation difficulties with the model theory of rings caused by the fact that there
are two different ways to say that `R` is a `Ring`. We can say `Ring R` or
`Language.ring.Structure R` and `Theory.ring.Model R` (The theory of rings is not implemented yet).

The recommended way to use this library is to use the hypotheses `CompatibleRing R` and `Ring R`
on any theorem that requires both a `Ring` instance and a `Language.ring.Structure` instance
in order to state the theorem. To apply such a theorem to a ring `R` with a `Ring` instance,
use the tactic `let _ := compatibleRingOfRing R`. To apply the theorem to `K`
a `Language.ring.Structure K` instance and for example an instance of `Theory.field.Model K`,
you must add local instances with definitions like `ModelTheory.Field.fieldOfModelField K` and
`FirstOrder.Ring.compatibleRingOfModelField K`.
(in `Mathlib/ModelTheory/Algebra/Field/Basic.lean`), depending on the Theory.
-/

variable {α : Type*}

namespace FirstOrder

/-- The type of Ring functions, to be used in the definition of the language of rings.
It contains the operations (+,*,-,0,1) -/
inductive ringFunc : ℕ → Type
  | add : ringFunc 2
  | mul : ringFunc 2
  | neg : ringFunc 1
  | zero : ringFunc 0
  | one : ringFunc 0
  deriving DecidableEq

/-- The language of rings contains the operations (+,*,-,0,1) -/
def Language.ring : Language :=
  { Functions := ringFunc
    Relations := fun _ => Empty }
  deriving IsAlgebraic

namespace Ring

open ringFunc Language

/-- This instance does not get inferred without `instDecidableEqFunctions` in
`ModelTheory/Basic`. -/
example (n : ℕ) : DecidableEq (Language.ring.Functions n) := inferInstance

/-- This instance does not get inferred without `instDecidableEqRelations` in
`ModelTheory/Basic`. -/
example (n : ℕ) : DecidableEq (Language.ring.Relations n) := inferInstance

/-- `RingFunc.add`, but with the defeq type `Language.ring.Functions 2` instead
of `RingFunc 2` -/
abbrev addFunc : Language.ring.Functions 2 := add

/-- `RingFunc.mul`, but with the defeq type `Language.ring.Functions 2` instead
of `RingFunc 2` -/
abbrev mulFunc : Language.ring.Functions 2 := mul

/-- `RingFunc.neg`, but with the defeq type `Language.ring.Functions 1` instead
of `RingFunc 1` -/
abbrev negFunc : Language.ring.Functions 1 := neg

/-- `RingFunc.zero`, but with the defeq type `Language.ring.Functions 0` instead
of `RingFunc 0` -/
abbrev zeroFunc : Language.ring.Functions 0 := zero

/-- `RingFunc.one`, but with the defeq type `Language.ring.Functions 0` instead
of `RingFunc 0` -/
abbrev oneFunc : Language.ring.Functions 0 := one

instance (α : Type*) : Zero (Language.ring.Term α) :=
{ zero := Constants.term zeroFunc }

theorem zero_def (α : Type*) : (0 : Language.ring.Term α) = Constants.term zeroFunc := rfl

instance (α : Type*) : One (Language.ring.Term α) :=
{ one := Constants.term oneFunc }

theorem one_def (α : Type*) : (1 : Language.ring.Term α) = Constants.term oneFunc := rfl

instance (α : Type*) : Add (Language.ring.Term α) :=
{ add := addFunc.apply₂ }

theorem add_def (α : Type*) (t₁ t₂ : Language.ring.Term α) :
    t₁ + t₂ = addFunc.apply₂ t₁ t₂ := rfl

instance (α : Type*) : Mul (Language.ring.Term α) :=
{ mul := mulFunc.apply₂ }

theorem mul_def (α : Type*) (t₁ t₂ : Language.ring.Term α) :
    t₁ * t₂ = mulFunc.apply₂ t₁ t₂ := rfl

instance (α : Type*) : Neg (Language.ring.Term α) :=
{ neg := negFunc.apply₁ }

theorem neg_def (α : Type*) (t : Language.ring.Term α) :
    -t = negFunc.apply₁ t := rfl

instance : Fintype Language.ring.Symbols :=
  ⟨⟨Multiset.ofList
      [Sum.inl ⟨2, .add⟩,
       Sum.inl ⟨2, .mul⟩,
       Sum.inl ⟨1, .neg⟩,
       Sum.inl ⟨0, .zero⟩,
       Sum.inl ⟨0, .one⟩], by
    dsimp [Language.Symbols]; decide⟩, by
    intro x
    dsimp [Language.Symbols]
    rcases x with ⟨_, f⟩ | ⟨_, f⟩
    · cases f <;> decide
    · cases f ⟩

@[simp]
theorem card_ring : card Language.ring = 5 := by
  have : Fintype.card Language.ring.Symbols = 5 := rfl
  simp [Language.card, this]

open Structure

/-- A Type `R` is a `CompatibleRing` if it is a structure for the language of rings and this
structure is the same as the structure already given on `R` by the classes `Add`, `Mul` etc.

It is recommended to use this type class as a hypothesis to any theorem whose statement
requires a type to have be both a `Ring` (or `Field` etc.) and a
`Language.ring.Structure` -/
/- This class does not extend `Add` etc, because this way it can be used in
combination with a `Ring`, or `Field` instance without having multiple different
`Add` structures on the Type. -/
class CompatibleRing (R : Type*) [Add R] [Mul R] [Neg R] [One R] [Zero R]
    extends Language.ring.Structure R where
  /-- Addition in the `Language.ring.Structure` is the same as the addition given by the
  `Add` instance -/
  funMap_add : ∀ x, funMap addFunc x = x 0 + x 1
  /-- Multiplication in the `Language.ring.Structure` is the same as the multiplication given by the
  `Mul` instance -/
  funMap_mul : ∀ x, funMap mulFunc x = x 0 * x 1
  /-- Negation in the `Language.ring.Structure` is the same as the negation given by the
  `Neg` instance -/
  funMap_neg : ∀ x, funMap negFunc x = -x 0
  /-- The constant `0` in the `Language.ring.Structure` is the same as the constant given by the
  `Zero` instance -/
  funMap_zero : ∀ x, funMap (zeroFunc : Language.ring.Constants) x = 0
  /-- The constant `1` in the `Language.ring.Structure` is the same as the constant given by the
  `One` instance -/
  funMap_one : ∀ x, funMap (oneFunc : Language.ring.Constants) x = 1

open CompatibleRing

attribute [simp] funMap_add funMap_mul funMap_neg funMap_zero funMap_one

section

variable {R : Type*} [Add R] [Mul R] [Neg R] [One R] [Zero R] [CompatibleRing R]

@[simp]
theorem realize_add (x y : ring.Term α) (v : α → R) :
    Term.realize v (x + y) = Term.realize v x + Term.realize v y := by
  simp [add_def, funMap_add]

@[simp]
theorem realize_mul (x y : ring.Term α) (v : α → R) :
    Term.realize v (x * y) = Term.realize v x * Term.realize v y := by
  simp [mul_def, funMap_mul]

@[simp]
theorem realize_neg (x : ring.Term α) (v : α → R) :
    Term.realize v (-x) = -Term.realize v x := by
  simp [neg_def, funMap_neg]

@[simp]
theorem realize_zero (v : α → R) : Term.realize v (0 : ring.Term α) = 0 := by
  simp [zero_def, funMap_zero, constantMap]

@[simp]
theorem realize_one (v : α → R) : Term.realize v (1 : ring.Term α) = 1 := by
  simp [one_def, funMap_one, constantMap]

end

/-- Given a Type `R` with instances for each of the `Ring` operations, make a
`Language.ring.Structure R` instance, along with a proof that the operations given
by the `Language.ring.Structure` are the same as those given by the `Add` or `Mul` etc.
instances.

This definition can be used when applying a theorem about the model theory of rings
to a literal ring `R`, by writing `let _ := compatibleRingOfRing R`. After this, if,
for example, `R` is a field, then Lean will be able to find the instance for
`Theory.field.Model R`, and it will be possible to apply theorems about the model theory
of fields.

This is a `def` and not an `instance`, because the path
`Ring` => `Language.ring.Structure` => `Ring` cannot be made to
commute by definition
-/
def compatibleRingOfRing (R : Type*) [Add R] [Mul R] [Neg R] [One R] [Zero R] :
    CompatibleRing R :=
  { funMap := fun {n} f =>
      match n, f with
      | _, .add => fun x => x 0 + x 1
      | _, .mul => fun x => x 0 * x 1
      | _, .neg => fun x => -x 0
      | _, .zero => fun _ => 0
      | _, .one => fun _ => 1
    funMap_add := fun _ => rfl,
    funMap_mul := fun _ => rfl,
    funMap_neg := fun _ => rfl,
    funMap_zero := fun _ => rfl,
    funMap_one := fun _ => rfl }

/-- An isomorphism in the language of rings is a ring isomorphism -/
def languageEquivEquivRingEquiv {R S : Type*}
    [NonAssocRing R] [NonAssocRing S]
    [CompatibleRing R] [CompatibleRing S] :
    (Language.ring.Equiv R S) ≃ (R ≃+* S) :=
  { toFun f :=
    { f with
      map_add' := by
        intro x y
        simpa using f.map_fun addFunc ![x, y]
      map_mul' := by
        intro x y
        simpa using f.map_fun mulFunc ![x, y] }
    invFun f :=
    { f with
      map_fun' := fun {n} f => by
        cases f <;> simp
      map_rel' := fun {n} f => by cases f } }

variable (R : Type*) [Language.ring.Structure R]

/-- A def to put an `Add` instance on a type with a `Language.ring.Structure` instance.

To be used sparingly, usually only when defining a more useful definition like,
`[Language.ring.Structure K] -> [Theory.field.Model K] -> Field K` -/
abbrev addOfRingStructure : Add R :=
  { add := fun x y => funMap addFunc ![x, y] }

/-- A def to put an `Mul` instance on a type with a `Language.ring.Structure` instance.

To be used sparingly, usually only when defining a more useful definition like,
`[Language.ring.Structure K] -> [Theory.field.Model K] -> Field K` -/
abbrev mulOfRingStructure : Mul R :=
  { mul := fun x y => funMap mulFunc ![x, y] }

/-- A def to put an `Neg` instance on a type with a `Language.ring.Structure` instance.

To be used sparingly, usually only when defining a more useful definition like,
`[Language.ring.Structure K] -> [Theory.field.Model K] -> Field K` -/
abbrev negOfRingStructure : Neg R :=
  { neg := fun x => funMap negFunc ![x] }

/-- A def to put an `Zero` instance on a type with a `Language.ring.Structure` instance.

To be used sparingly, usually only when defining a more useful definition like,
`[Language.ring.Structure K] -> [Theory.field.Model K] -> Field K` -/
abbrev zeroOfRingStructure : Zero R :=
  { zero := funMap zeroFunc ![] }

/-- A def to put an `One` instance on a type with a `Language.ring.Structure` instance.

To be used sparingly, usually only when defining a more useful definition like,
`[Language.ring.Structure K] -> [Theory.field.Model K] -> Field K` -/
abbrev oneOfRingStructure : One R :=
  { one := funMap oneFunc ![] }

attribute [local instance] addOfRingStructure mulOfRingStructure negOfRingStructure
  zeroOfRingStructure oneOfRingStructure

/--
Given a Type `R` with a `Language.ring.Structure R`, the instance given by
`addOfRingStructure` etc. are compatible with the `Language.ring.Structure` instance on `R`.

This definition is only to be used when `addOfRingStructure`, `mulOfRingStructure` etc
are local instances.
-/
abbrev compatibleRingOfRingStructure : CompatibleRing R :=
  { funMap_add := by
      simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi]
      intros; rfl
    funMap_mul := by
      simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi]
      intros; rfl
    funMap_neg := by
      simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi]
      intros; rfl
    funMap_zero := by
      simp only [Fin.forall_fin_zero_pi]
      rfl
    funMap_one := by
      simp only [Fin.forall_fin_zero_pi]
      rfl  }

end Ring

end FirstOrder
