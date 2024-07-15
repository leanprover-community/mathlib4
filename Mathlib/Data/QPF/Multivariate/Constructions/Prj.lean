/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Control.Functor.Multivariate
import Mathlib.Data.QPF.Multivariate.Basic

#align_import data.qpf.multivariate.constructions.prj from "leanprover-community/mathlib"@"dc6c365e751e34d100e80fe6e314c3c3e0fd2988"

/-!
Projection functors are QPFs. The `n`-ary projection functors on `i` is an `n`-ary
functor `F` such that `F (α₀..αᵢ₋₁, αᵢ, αᵢ₊₁..αₙ₋₁) = αᵢ`
-/


universe u v

namespace MvQPF

open MvFunctor

variable {n : ℕ} (i : Fin2 n)

/-- The projection `i` functor -/
def Prj (v : TypeVec.{u} n) : Type u := v i
#align mvqpf.prj MvQPF.Prj

instance Prj.inhabited {v : TypeVec.{u} n} [Inhabited (v i)] : Inhabited (Prj i v) :=
  ⟨(default : v i)⟩
#align mvqpf.prj.inhabited MvQPF.Prj.inhabited

/-- `map` on functor `Prj i` -/
def Prj.map ⦃α β : TypeVec n⦄ (f : α ⟹ β) : Prj i α → Prj i β := f _
#align mvqpf.prj.map MvQPF.Prj.map

instance Prj.mvfunctor : MvFunctor (Prj i) where map := @Prj.map _ i
#align mvqpf.prj.mvfunctor MvQPF.Prj.mvfunctor

/-- Polynomial representation of the projection functor -/
def Prj.P : MvPFunctor.{u} n where
  A := PUnit
  B _ j := ULift <| PLift <| i = j
set_option linter.uppercaseLean3 false in
#align mvqpf.prj.P MvQPF.Prj.P

/-- Abstraction function of the `QPF` instance -/
def Prj.abs ⦃α : TypeVec n⦄ : Prj.P i α → Prj i α
  | ⟨_x, f⟩ => f _ ⟨⟨rfl⟩⟩
#align mvqpf.prj.abs MvQPF.Prj.abs

/-- Representation function of the `QPF` instance -/
def Prj.repr ⦃α : TypeVec n⦄ : Prj i α → Prj.P i α := fun x : α i =>
  ⟨⟨⟩, fun j ⟨⟨h⟩⟩ => (h.rec x : α j)⟩
#align mvqpf.prj.repr MvQPF.Prj.repr

instance Prj.mvqpf : MvQPF (Prj i) where
  P := Prj.P i
  abs := @Prj.abs _ i
  repr := @Prj.repr _ i
  abs_repr := by intros; rfl
  abs_map := by intros α β f P; cases P; rfl
#align mvqpf.prj.mvqpf MvQPF.Prj.mvqpf

end MvQPF
