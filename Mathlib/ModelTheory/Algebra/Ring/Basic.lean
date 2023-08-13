/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import Mathlib.Algebra.Ring.Equiv

/-!
# First Order Language of Rings

This file defines the first order language of rings, as well as defining instance of `Add`, `Mul`,
etc. on terms in the language.

-/


namespace FirstOrder

open FirstOrder

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

namespace Ring

open ringFunc Language

instance (n : ℕ) : DecidableEq (Language.ring.Functions n) := by
  dsimp [Language.ring]; infer_instance

instance (n : ℕ) : DecidableEq (Language.ring.Relations n) := by
  dsimp [Language.ring]; infer_instance

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

open Language ring Structure

/-- A Type, `R` is a `CompatibleRing` if it is structure for the language of rings and this structure
is the same as the structure already given on `R` by the classes `Add`, `Mul` etc. -/
class CompatibleRing (R : Type*) [Add R] [Mul R] [Neg R] [One R] [Zero R]
    extends Language.ring.Structure R where
  ( funMap_add : ∀ x, funMap addFunc x = x 0 + x 1 )
  ( funMap_mul : ∀ x, funMap mulFunc x = x 0 * x 1 )
  ( funMap_neg : ∀ x, funMap negFunc x = -x 0 )
  ( funMap_zero : ∀ x, funMap (zeroFunc : Language.ring.Constants) x = 0 )
  ( funMap_one : ∀ x, funMap (oneFunc : Language.ring.Constants) x = 1 )

attribute [simp] CompatibleRing.funMap_add CompatibleRing.funMap_mul CompatibleRing.funMap_neg
  CompatibleRing.funMap_zero CompatibleRing.funMap_one

@[reducible]
def compatibleRingOfRing (R : Type*) [Add R] [Mul R] [Neg R] [One R] [Zero R] :
    CompatibleRing R :=
  { funMap := fun {n} f =>
      match n, f with
      | _, .add => fun x => x 0 + x 1
      | _, .mul => fun x => x 0 * x 1
      | _, .neg => fun x => -x 0
      | _, .zero => fun _ => 0
      | _, .one => fun _ => 1
    RelMap := Empty.elim,
    funMap_add := fun _ => rfl,
    funMap_mul := fun _ => rfl,
    funMap_neg := fun _ => rfl,
    funMap_zero := fun _ => rfl,
    funMap_one := fun _ => rfl }

def languageEquivEquivRingEquiv {R S : Type*}
    [NonAssocRing R] [NonAssocRing S]
    [CompatibleRing R] [CompatibleRing S] :
    (R ≃+* S) ≃ (Language.ring.Equiv R S) :=
  { toFun := fun f =>
    { f with
      map_fun' := fun {n} f => by
        cases f <;> simp
      map_rel' := fun {n} f => by cases f },
    invFun := fun f =>
    { f with
      map_add' := by
        intro x y
        simpa using f.map_fun addFunc ![x, y]
      map_mul' := by
        intro x y
        simpa using f.map_fun mulFunc ![x, y] }
    left_inv := fun f => by ext; rfl
    right_inv := fun f => by ext; rfl }

variable (R : Type*) [Language.ring.Structure R]

@[reducible] def addOfRingStructure : Add R :=
  { add := fun x y => funMap addFunc ![x, y] }

@[reducible] def mulOfRingStructure : Mul R :=
  { mul := fun x y => funMap mulFunc ![x, y] }

@[reducible] def negOfRingStructure : Neg R :=
  { neg := fun x => funMap negFunc ![x] }

@[reducible] def zeroOfRingStructure : Zero R :=
  { zero := funMap zeroFunc ![] }

@[reducible] def oneOfRingStructure : One R :=
  { one := funMap oneFunc ![] }

attribute [local instance] addOfRingStructure mulOfRingStructure negOfRingStructure
  zeroOfRingStructure oneOfRingStructure

@[reducible] def compatibleRingOfRingStructure : CompatibleRing R :=
  { funMap_add := by
      simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi];
      intros; rfl
    funMap_mul := by
      simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi];
      intros; rfl
    funMap_neg := by
      simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi];
      intros; rfl
    funMap_zero := by
      simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi];
      intros; rfl
    funMap_one := by
      simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi];
      intros; rfl  }

end Ring

end FirstOrder
