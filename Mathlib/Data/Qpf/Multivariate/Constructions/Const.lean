/-
Copyright (c) 2020 Simon Hudon All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module data.qpf.multivariate.constructions.const
! leanprover-community/mathlib commit dc6c365e751e34d100e80fe6e314c3c3e0fd2988
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Control.Functor.Multivariate
import Mathbin.Data.Qpf.Multivariate.Basic

/-!
# Constant functors are QPFs

Constant functors map every type vectors to the same target type. This
is a useful device for constructing data types from more basic types
that are not actually functorial. For instance `const n nat` makes
`nat` into a functor that can be used in a functor-based data type
specification.
-/


universe u

namespace Mvqpf

open MvFunctor

variable (n : ℕ)

/-- Constant multivariate functor -/
@[nolint unused_arguments]
def Const (A : Type _) (v : TypeVec.{u} n) : Type _ :=
  A
#align mvqpf.const Mvqpf.Const

instance Const.inhabited {A α} [Inhabited A] : Inhabited (Const n A α) :=
  ⟨(default : A)⟩
#align mvqpf.const.inhabited Mvqpf.Const.inhabited

namespace Const

open MvFunctor Mvpfunctor

variable {n} {A : Type u} {α β : TypeVec.{u} n} (f : α ⟹ β)

/-- Constructor for constant functor -/
protected def mk (x : A) : (Const n A) α :=
  x
#align mvqpf.const.mk Mvqpf.Const.mk

/-- Destructor for constant functor -/
protected def get (x : (Const n A) α) : A :=
  x
#align mvqpf.const.get Mvqpf.Const.get

@[simp]
protected theorem mk_get (x : (Const n A) α) : Const.mk (Const.get x) = x :=
  rfl
#align mvqpf.const.mk_get Mvqpf.Const.mk_get

@[simp]
protected theorem get_mk (x : A) : Const.get (Const.mk x : Const n A α) = x :=
  rfl
#align mvqpf.const.get_mk Mvqpf.Const.get_mk

/-- `map` for constant functor -/
protected def map : (Const n A) α → (Const n A) β := fun x => x
#align mvqpf.const.map Mvqpf.Const.map

instance : MvFunctor (Const n A) where map α β f := Const.map

theorem map_mk (x : A) : f <$$> Const.mk x = Const.mk x :=
  rfl
#align mvqpf.const.map_mk Mvqpf.Const.map_mk

theorem get_map (x : (Const n A) α) : Const.get (f <$$> x) = Const.get x :=
  rfl
#align mvqpf.const.get_map Mvqpf.Const.get_map

instance mvqpf : @Mvqpf _ (Const n A) Mvqpf.Const.mvfunctor
    where
  p := Mvpfunctor.const n A
  abs α x := Mvpfunctor.const.get x
  repr α x := Mvpfunctor.const.mk n x
  abs_repr := by intros <;> simp
  abs_map := by intros <;> simp <;> rfl
#align mvqpf.const.mvqpf Mvqpf.Const.mvqpf

end Const

end Mvqpf

