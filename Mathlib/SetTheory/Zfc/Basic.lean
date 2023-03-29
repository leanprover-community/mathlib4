/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module set_theory.zfc.basic
! leanprover-community/mathlib commit ef5f2ce93dd79b7fb184018b6f48132a10c764e7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Small.Basic
import Mathlib.Order.WellFounded

/-!
# A model of ZFC

In this file, we model Zermelo-Fraenkel set theory (+ Choice) using Lean's underlying type theory.
We do this in four main steps:
* Define pre-sets inductively.
* Define extensional equivalence on pre-sets and give it a `setoid` instance.
* Define ZFC sets by quotienting pre-sets by extensional equivalence.
* Define classes as sets of ZFC sets.
Then the rest is usual set theory.

## The model

* `pSet`: Pre-set. A pre-set is inductively defined by its indexing type and its members, which are
  themselves pre-sets.
* `Set`: ZFC set. Defined as `pSet` quotiented by `pSet.equiv`, the extensional equivalence.
* `Class`: Class. Defined as `set Set`.
* `Set.choice`: Axiom of choice. Proved from Lean's axiom of choice.

## Other definitions

* `arity α n`: `n`-ary function `α → α → ... → α`. Defined inductively.
* `arity.const a n`: `n`-ary constant function equal to `a`.
* `pSet.type`: Underlying type of a pre-set.
* `pSet.func`: Underlying family of pre-sets of a pre-set.
* `pSet.equiv`: Extensional equivalence of pre-sets. Defined inductively.
* `pSet.omega`, `Set.omega`: The von Neumann ordinal `ω` as a `pSet`, as a `Set`.
* `pSet.arity.equiv`: Extensional equivalence of `n`-ary `pSet`-valued functions. Extension of
  `pSet.equiv`.
* `pSet.resp`: Collection of `n`-ary `pSet`-valued functions that respect extensional equivalence.
* `pSet.eval`: Turns a `pSet`-valued function that respect extensional equivalence into a
  `Set`-valued function.
* `classical.all_definable`: All functions are classically definable.
* `Set.is_func` : Predicate that a ZFC set is a subset of `x × y` that can be considered as a ZFC
  function `x → y`. That is, each member of `x` is related by the ZFC set to exactly one member of
  `y`.
* `Set.funs`: ZFC set of ZFC functions `x → y`.
* `Set.hereditarily p x`: Predicate that every set in the transitive closure of `x` has property
  `p`.
* `Class.iota`: Definite description operator.

## Notes

To avoid confusion between the Lean `set` and the ZFC `Set`, docstrings in this file refer to them
respectively as "`set`" and "ZFC set".

## TODO

Prove `Set.map_definable_aux` computably.
-/

set_option linter.uppercaseLean3 false

universe u v

/-- The type of `n`-ary functions `α → α → ... → α`. -/
def Arity (α : Type u) : ℕ → Type u
  | 0 => α
  | n + 1 => α → Arity α n
#align arity Arity

@[simp]
theorem arity_zero (α : Type u) : Arity α 0 = α :=
  rfl
#align arity_zero arity_zero

@[simp]
theorem arity_succ (α : Type u) (n : ℕ) : Arity α n.succ = (α → Arity α n) :=
  rfl
#align arity_succ arity_succ

namespace Arity

/-- Constant `n`-ary function with value `a`. -/
def Const {α : Type u} (a : α) : ∀ n, Arity α n
  | 0 => a
  | n + 1 => fun _ => Const a n
#align arity.const Arity.Const

@[simp]
theorem const_zero {α : Type u} (a : α) : Const a 0 = a :=
  rfl
#align arity.const_zero Arity.const_zero

@[simp]
theorem const_succ {α : Type u} (a : α) (n : ℕ) : Const a n.succ = fun _ => Const a n :=
  rfl
#align arity.const_succ Arity.const_succ

theorem const_succ_apply {α : Type u} (a : α) (n : ℕ) (x : α) : Const a n.succ x = Const a n :=
  rfl
#align arity.const_succ_apply Arity.const_succ_apply

instance Arity.inhabited {α n} [Inhabited α] : Inhabited (Arity α n) :=
  ⟨Const default _⟩
#align arity.arity.inhabited Arity.Arity.inhabited

end Arity

/-- The type of pre-sets in universe `u`. A pre-set
  is a family of pre-sets indexed by a type in `Type u`.
  The ZFC universe is defined as a quotient of this
  to ensure extensionality. -/
inductive PSet : Type (u + 1)
  | mk (α : Type u) (A : α → PSet) : PSet
#align pSet PSet

namespace PSet

/-- The underlying type of a pre-set -/
def «Type» : PSet → Type u
  | ⟨α, _⟩ => α
#align pSet.type PSet.Type

/-- The underlying pre-set family of a pre-set -/
def Func : ∀ x : PSet, x.Type → PSet
  | ⟨_, A⟩ => A
#align pSet.func PSet.Func

@[simp]
theorem mk_type (α A) : «Type» ⟨α, A⟩ = α :=
  rfl
#align pSet.mk_type PSet.mk_type

@[simp]
theorem mk_func (α A) : Func ⟨α, A⟩ = A :=
  rfl
#align pSet.mk_func PSet.mk_func

@[simp]
theorem eta : ∀ x : PSet, mk x.Type x.Func = x
  | ⟨_, _⟩ => rfl
#align pSet.eta PSet.eta

/-- Two pre-sets are extensionally equivalent if every element of the first family is extensionally
equivalent to some element of the second family and vice-versa. -/
def Equiv : PSet → PSet → Prop
  | ⟨_, A⟩, ⟨_, B⟩ => (∀ a, ∃ b, Equiv (A a) (B b)) ∧ (∀ b, ∃ a, Equiv (A a) (B b))
#align pSet.equiv PSet.Equiv

theorem equiv_iff :
   ∀ {x y : PSet},
      Equiv x y ↔ (∀ i, ∃ j, Equiv (x.Func i) (y.Func j)) ∧ ∀ j, ∃ i, Equiv (x.Func i) (y.Func j)
  | ⟨_, _⟩, ⟨_, _⟩ => Iff.rfl
#align pSet.equiv_iff PSet.equiv_iff

theorem Equiv.exists_left {x y : PSet} (h : Equiv x y) : ∀ i, ∃ j, Equiv (x.Func i) (y.Func j) :=
  (equiv_iff.1 h).1
#align pSet.equiv.exists_left PSet.Equiv.exists_left

theorem Equiv.exists_right {x y : PSet} (h : Equiv x y) : ∀ j, ∃ i, Equiv (x.Func i) (y.Func j) :=
  (equiv_iff.1 h).2
#align pSet.equiv.exists_right PSet.Equiv.exists_right

@[refl]
protected theorem Equiv.refl : ∀ x, Equiv x x
  | ⟨_, _⟩ => ⟨fun a => ⟨a, Equiv.refl _⟩, fun a => ⟨a, Equiv.refl _⟩⟩
#align pSet.equiv.refl PSet.Equiv.refl

protected theorem Equiv.rfl {x} : Equiv x x :=
  Equiv.refl x
#align pSet.equiv.rfl PSet.Equiv.rfl

protected theorem Equiv.euc : ∀ {x y z}, Equiv x y → Equiv z y → Equiv x z
  | ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨αβ, βα⟩, ⟨γβ, βγ⟩ =>
    ⟨ fun a =>
        let ⟨b, ab⟩ := αβ a
        let ⟨c, bc⟩ := βγ b
        ⟨c, Equiv.euc ab bc⟩,
      fun c =>
        let ⟨b, cb⟩ := γβ c
        let ⟨a, ba⟩ := βα b
        ⟨a, Equiv.euc ba cb⟩ ⟩
#align pSet.equiv.euc PSet.Equiv.euc

@[symm]
protected theorem Equiv.symm {x y} : Equiv x y → Equiv y x :=
  (Equiv.refl y).euc
#align pSet.equiv.symm PSet.Equiv.symm

protected theorem Equiv.comm {x y} : Equiv x y ↔ Equiv y x :=
  ⟨Equiv.symm, Equiv.symm⟩
#align pSet.equiv.comm PSet.Equiv.comm

@[trans]
protected theorem Equiv.trans {x y z} (h1 : Equiv x y) (h2 : Equiv y z) : Equiv x z :=
  h1.euc h2.symm
#align pSet.equiv.trans PSet.Equiv.trans

protected theorem equiv_of_isEmpty (x y : PSet) [IsEmpty x.Type] [IsEmpty y.Type] : Equiv x y :=
  equiv_iff.2 <| by simp
#align pSet.equiv_of_is_empty PSet.equiv_of_isEmpty

instance setoid : Setoid PSet :=
  ⟨PSet.Equiv, Equiv.refl, Equiv.symm, Equiv.trans⟩
#align pSet.setoid PSet.setoid
