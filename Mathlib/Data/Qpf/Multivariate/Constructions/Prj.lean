/-
Copyright (c) 2020 Simon Hudon All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module data.qpf.multivariate.constructions.prj
! leanprover-community/mathlib commit dc6c365e751e34d100e80fe6e314c3c3e0fd2988
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Control.Functor.Multivariate
import Mathbin.Data.Qpf.Multivariate.Basic

/-!
Projection functors are QPFs. The `n`-ary projection functors on `i` is an `n`-ary
functor `F` such that `F (α₀..αᵢ₋₁, αᵢ, αᵢ₊₁..αₙ₋₁) = αᵢ`
-/


universe u v

namespace Mvqpf

open MvFunctor

variable {n : ℕ} (i : Fin2 n)

/-- The projection `i` functor -/
def Prj (v : TypeVec.{u} n) : Type u :=
  v i
#align mvqpf.prj Mvqpf.Prj

instance Prj.inhabited {v : TypeVec.{u} n} [Inhabited (v i)] : Inhabited (Prj i v) :=
  ⟨(default : v i)⟩
#align mvqpf.prj.inhabited Mvqpf.Prj.inhabited

/-- `map` on functor `prj i` -/
def Prj.map ⦃α β : TypeVec n⦄ (f : α ⟹ β) : Prj i α → Prj i β :=
  f _
#align mvqpf.prj.map Mvqpf.Prj.map

instance Prj.mvfunctor : MvFunctor (Prj i) where map := Prj.map i
#align mvqpf.prj.mvfunctor Mvqpf.Prj.mvfunctor

/-- Polynomial representation of the projection functor -/
def Prj.p : Mvpfunctor.{u} n where
  A := PUnit
  B _ j := ULift <| PLift <| i = j
#align mvqpf.prj.P Mvqpf.Prj.p

/-- Abstraction function of the `qpf` instance -/
def Prj.abs ⦃α : TypeVec n⦄ : (Prj.p i).Obj α → Prj i α
  | ⟨x, f⟩ => f _ ⟨⟨rfl⟩⟩
#align mvqpf.prj.abs Mvqpf.Prj.abs

/-- Representation function of the `qpf` instance -/
def Prj.repr ⦃α : TypeVec n⦄ : Prj i α → (Prj.p i).Obj α := fun x : α i =>
  ⟨⟨⟩, fun j ⟨⟨h⟩⟩ => (h.rec x : α j)⟩
#align mvqpf.prj.repr Mvqpf.Prj.repr

instance Prj.mvqpf : Mvqpf (Prj i) where
  p := Prj.p i
  abs := Prj.abs i
  repr := Prj.repr i
  abs_repr := by intros <;> rfl
  abs_map := by intros <;> cases p <;> rfl
#align mvqpf.prj.mvqpf Mvqpf.Prj.mvqpf

end Mvqpf

