/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module data.qpf.multivariate.constructions.sigma
! leanprover-community/mathlib commit dc6c365e751e34d100e80fe6e314c3c3e0fd2988
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Pfunctor.Multivariate.Basic
import Mathbin.Data.Qpf.Multivariate.Basic

/-!
# Dependent product and sum of QPFs are QPFs
-/


universe u

namespace Mvqpf

open MvFunctor

variable {n : ℕ} {A : Type u}

variable (F : A → TypeVec.{u} n → Type u)

/-- Dependent sum of of an `n`-ary functor. The sum can range over
data types like `ℕ` or over `Type.{u-1}` -/
def Sigma (v : TypeVec.{u} n) : Type u :=
  Σα : A, F α v
#align mvqpf.sigma Mvqpf.Sigma

/-- Dependent product of of an `n`-ary functor. The sum can range over
data types like `ℕ` or over `Type.{u-1}` -/
def Pi (v : TypeVec.{u} n) : Type u :=
  ∀ α : A, F α v
#align mvqpf.pi Mvqpf.Pi

instance Sigma.inhabited {α} [Inhabited A] [Inhabited (F default α)] : Inhabited (Sigma F α) :=
  ⟨⟨default, default⟩⟩
#align mvqpf.sigma.inhabited Mvqpf.Sigma.inhabited

instance Pi.inhabited {α} [∀ a, Inhabited (F a α)] : Inhabited (Pi F α) :=
  ⟨fun a => default⟩
#align mvqpf.pi.inhabited Mvqpf.Pi.inhabited

variable [∀ α, MvFunctor <| F α]

namespace Sigma

instance : MvFunctor (Sigma F) where map := fun α β f ⟨a, x⟩ => ⟨a, f <$$> x⟩

variable [∀ α, Mvqpf <| F α]

/-- polynomial functor representation of a dependent sum -/
protected def p : Mvpfunctor n :=
  ⟨Σa, (p (F a)).A, fun x => (p (F x.1)).B x.2⟩
#align mvqpf.sigma.P Mvqpf.Sigma.p

/-- abstraction function for dependent sums -/
protected def abs ⦃α⦄ : (Sigma.p F).Obj α → Sigma F α
  | ⟨a, f⟩ => ⟨a.1, Mvqpf.abs ⟨a.2, f⟩⟩
#align mvqpf.sigma.abs Mvqpf.Sigma.abs

/-- representation function for dependent sums -/
protected def repr ⦃α⦄ : Sigma F α → (Sigma.p F).Obj α
  | ⟨a, f⟩ =>
    let x := Mvqpf.repr f
    ⟨⟨a, x.1⟩, x.2⟩
#align mvqpf.sigma.repr Mvqpf.Sigma.repr

instance : Mvqpf (Sigma F) where
  p := Sigma.p F
  abs := Sigma.abs F
  repr := Sigma.repr F
  abs_repr := by rintro α ⟨x, f⟩ <;> simp [sigma.repr, sigma.abs, abs_repr]
  abs_map := by
    rintro α β f ⟨x, g⟩ <;> simp [sigma.abs, Mvpfunctor.map_eq] <;>
      simp [(· <$$> ·), mvfunctor._match_1, ← abs_map, ← Mvpfunctor.map_eq]

end Sigma

namespace Pi

instance : MvFunctor (Pi F) where map α β f x a := f <$$> x a

variable [∀ α, Mvqpf <| F α]

/-- polynomial functor representation of a dependent product -/
protected def p : Mvpfunctor n :=
  ⟨∀ a, (p (F a)).A, fun x i => Σa : A, (p (F a)).B (x a) i⟩
#align mvqpf.pi.P Mvqpf.Pi.p

/-- abstraction function for dependent products -/
protected def abs ⦃α⦄ : (Pi.p F).Obj α → Pi F α
  | ⟨a, f⟩ => fun x => Mvqpf.abs ⟨a x, fun i y => f i ⟨_, y⟩⟩
#align mvqpf.pi.abs Mvqpf.Pi.abs

/-- representation function for dependent products -/
protected def repr ⦃α⦄ : Pi F α → (Pi.p F).Obj α
  | f => ⟨fun a => (Mvqpf.repr (f a)).1, fun i a => (Mvqpf.repr (f _)).2 _ a.2⟩
#align mvqpf.pi.repr Mvqpf.Pi.repr

instance : Mvqpf (Pi F) where
  p := Pi.p F
  abs := Pi.abs F
  repr := Pi.repr F
  abs_repr := by rintro α f <;> ext <;> simp [pi.repr, pi.abs, abs_repr]
  abs_map := by
    rintro α β f ⟨x, g⟩ <;> simp only [pi.abs, Mvpfunctor.map_eq] <;> ext <;>
          simp only [(· <$$> ·)] <;>
        simp only [← abs_map, Mvpfunctor.map_eq] <;>
      rfl

end Pi

end Mvqpf

