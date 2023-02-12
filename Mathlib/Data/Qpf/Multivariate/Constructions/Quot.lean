/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon

! This file was ported from Lean 3 source module data.qpf.multivariate.constructions.quot
! leanprover-community/mathlib commit dc6c365e751e34d100e80fe6e314c3c3e0fd2988
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Qpf.Multivariate.Basic

/-!
# The quotient of QPF is itself a QPF

The quotients are here defined using a surjective function and
its right inverse. They are very similar to the `abs` and `repr`
functions found in the definition of `mvqpf`
-/


universe u

open MvFunctor

namespace Mvqpf

variable {n : ℕ}

variable {F : TypeVec.{u} n → Type u}

section repr

variable [MvFunctor F] [q : Mvqpf F]

variable {G : TypeVec.{u} n → Type u} [MvFunctor G]

variable {FG_abs : ∀ {α}, F α → G α}

variable {FG_repr : ∀ {α}, G α → F α}

/-- If `F` is a QPF then `G` is a QPF as well. Can be used to
construct `mvqpf` instances by transporting them across
surjective functions -/
def quotientQpf (FG_abs_repr : ∀ {α} (x : G α), FG_abs (FG_repr x) = x)
    (FG_abs_map : ∀ {α β} (f : α ⟹ β) (x : F α), FG_abs (f <$$> x) = f <$$> FG_abs x) : Mvqpf G
    where
  p := q.p
  abs α p := FG_abs (abs p)
  repr α x := repr (FG_repr x)
  abs_repr α x := by rw [abs_repr, FG_abs_repr]
  abs_map α β f p := by rw [abs_map, FG_abs_map]
#align mvqpf.quotient_qpf Mvqpf.quotientQpf

end repr

section Rel

variable (R : ∀ ⦃α⦄, F α → F α → Prop)

/-- Functorial quotient type -/
def Quot1 (α : TypeVec n) :=
  Quot (@R α)
#align mvqpf.quot1 Mvqpf.Quot1

instance Quot1.inhabited {α : TypeVec n} [Inhabited <| F α] : Inhabited (Quot1 R α) :=
  ⟨Quot.mk _ default⟩
#align mvqpf.quot1.inhabited Mvqpf.Quot1.inhabited

variable [MvFunctor F] [q : Mvqpf F]

variable (Hfunc : ∀ ⦃α β⦄ (a b : F α) (f : α ⟹ β), R a b → R (f <$$> a) (f <$$> b))

/-- `map` of the `quot1` functor -/
def Quot1.map ⦃α β⦄ (f : α ⟹ β) : Quot1.{u} R α → Quot1.{u} R β :=
  Quot.lift (fun x : F α => Quot.mk _ (f <$$> x : F β)) fun a b h => Quot.sound <| Hfunc a b _ h
#align mvqpf.quot1.map Mvqpf.Quot1.map

/-- `mvfunctor` instance for `quot1` with well-behaved `R` -/
def Quot1.mvfunctor : MvFunctor (Quot1 R) where map := Quot1.map R Hfunc
#align mvqpf.quot1.mvfunctor Mvqpf.Quot1.mvfunctor

/-- `quot1` is a qpf -/
noncomputable def relQuot : @Mvqpf _ (Quot1 R) (Mvqpf.Quot1.mvfunctor R Hfunc) :=
  @quotientQpf n F _ q _ (Mvqpf.Quot1.mvfunctor R Hfunc) (fun α x => Quot.mk _ x)
    (fun α => Quot.out) (fun α x => Quot.out_eq _) fun α β f x => rfl
#align mvqpf.rel_quot Mvqpf.relQuot

end Rel

end Mvqpf

