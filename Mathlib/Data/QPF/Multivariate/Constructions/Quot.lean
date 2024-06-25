/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon
-/
import Mathlib.Data.QPF.Multivariate.Basic

#align_import data.qpf.multivariate.constructions.quot from "leanprover-community/mathlib"@"dc6c365e751e34d100e80fe6e314c3c3e0fd2988"

/-!
# The quotient of QPF is itself a QPF

The quotients are here defined using a surjective function and
its right inverse. They are very similar to the `abs` and `repr`
functions found in the definition of `MvQPF`
-/


universe u

open MvFunctor

namespace MvQPF

variable {n : ℕ}
variable {F : TypeVec.{u} n → Type u}

section repr

variable [q : MvQPF F]
variable {G : TypeVec.{u} n → Type u} [MvFunctor G]
variable {FG_abs : ∀ {α}, F α → G α}
variable {FG_repr : ∀ {α}, G α → F α}

/-- If `F` is a QPF then `G` is a QPF as well. Can be used to
construct `MvQPF` instances by transporting them across
surjective functions -/
def quotientQPF (FG_abs_repr : ∀ {α} (x : G α), FG_abs (FG_repr x) = x)
    (FG_abs_map : ∀ {α β} (f : α ⟹ β) (x : F α), FG_abs (f <$$> x) = f <$$> FG_abs x) :
    MvQPF G where
  P := q.P
  abs p := FG_abs (abs p)
  repr x := repr (FG_repr x)
  abs_repr x := by dsimp; rw [abs_repr, FG_abs_repr]
  abs_map f p := by dsimp; rw [abs_map, FG_abs_map]
#align mvqpf.quotient_qpf MvQPF.quotientQPF

end repr

section Rel

variable (R : ∀ ⦃α⦄, F α → F α → Prop)

/-- Functorial quotient type -/
def Quot1 (α : TypeVec n) :=
  Quot (@R α)
#align mvqpf.quot1 MvQPF.Quot1

instance Quot1.inhabited {α : TypeVec n} [Inhabited <| F α] : Inhabited (Quot1 R α) :=
  ⟨Quot.mk _ default⟩
#align mvqpf.quot1.inhabited MvQPF.Quot1.inhabited

section

variable [MvFunctor F] (Hfunc : ∀ ⦃α β⦄ (a b : F α) (f : α ⟹ β), R a b → R (f <$$> a) (f <$$> b))

/-- `map` of the `Quot1` functor -/
def Quot1.map ⦃α β⦄ (f : α ⟹ β) : Quot1.{u} R α → Quot1.{u} R β :=
  Quot.lift (fun x : F α => Quot.mk _ (f <$$> x : F β)) fun a b h => Quot.sound <| Hfunc a b _ h
#align mvqpf.quot1.map MvQPF.Quot1.map

/-- `mvFunctor` instance for `Quot1` with well-behaved `R` -/
def Quot1.mvFunctor : MvFunctor (Quot1 R) where map := @Quot1.map _ _ R _ Hfunc
#align mvqpf.quot1.mvfunctor MvQPF.Quot1.mvFunctor

end

section

variable [q : MvQPF F] (Hfunc : ∀ ⦃α β⦄ (a b : F α) (f : α ⟹ β), R a b → R (f <$$> a) (f <$$> b))

/-- `Quot1` is a QPF -/
noncomputable def relQuot : @MvQPF _ (Quot1 R) :=
  @quotientQPF n F q _ (MvQPF.Quot1.mvFunctor R Hfunc) (fun x => Quot.mk _ x)
    Quot.out (fun _x => Quot.out_eq _) fun _f _x => rfl
#align mvqpf.rel_quot MvQPF.relQuot

end

end Rel

end MvQPF
