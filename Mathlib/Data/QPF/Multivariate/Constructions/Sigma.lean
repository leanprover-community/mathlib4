/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Data.PFunctor.Multivariate.Basic
import Mathlib.Data.QPF.Multivariate.Basic

#align_import data.qpf.multivariate.constructions.sigma from "leanprover-community/mathlib"@"dc6c365e751e34d100e80fe6e314c3c3e0fd2988"

/-!
# Dependent product and sum of QPFs are QPFs
-/


universe u

namespace MvQPF

open MvFunctor

variable {n : ℕ} {A : Type u}

variable (F : A → TypeVec.{u} n → Type u)

/-- Dependent sum of an `n`-ary functor. The sum can range over
data types like `ℕ` or over `Type.{u-1}` -/
def Sigma (v : TypeVec.{u} n) : Type u :=
  Σ α : A, F α v
#align mvqpf.sigma MvQPF.Sigma

/-- Dependent product of an `n`-ary functor. The sum can range over
data types like `ℕ` or over `Type.{u-1}` -/
def Pi (v : TypeVec.{u} n) : Type u :=
  ∀ α : A, F α v
#align mvqpf.pi MvQPF.Pi

instance Sigma.inhabited {α} [Inhabited A] [Inhabited (F default α)] : Inhabited (Sigma F α) :=
  ⟨⟨default, default⟩⟩
#align mvqpf.sigma.inhabited MvQPF.Sigma.inhabited

instance Pi.inhabited {α} [∀ a, Inhabited (F a α)] : Inhabited (Pi F α) :=
  ⟨fun _a => default⟩
#align mvqpf.pi.inhabited MvQPF.Pi.inhabited

variable [∀ α, MvFunctor <| F α]

namespace Sigma

instance : MvFunctor (Sigma F) where map := fun f ⟨a, x⟩ => ⟨a, f <$$> x⟩

variable [∀ α, MvQPF <| F α]

/-- polynomial functor representation of a dependent sum -/
protected def P : MvPFunctor n :=
  ⟨Σ a, (P (F a)).A, fun x => (P (F x.1)).B x.2⟩
set_option linter.uppercaseLean3 false in
#align mvqpf.sigma.P MvQPF.Sigma.P

/-- abstraction function for dependent sums -/
protected def abs ⦃α⦄ : (Sigma.P F).Obj α → Sigma F α
  | ⟨a, f⟩ => ⟨a.1, MvQPF.abs ⟨a.2, f⟩⟩
#align mvqpf.sigma.abs MvQPF.Sigma.abs

/-- representation function for dependent sums -/
protected def repr ⦃α⦄ : Sigma F α → (Sigma.P F).Obj α
  | ⟨a, f⟩ =>
    let x := MvQPF.repr f
    ⟨⟨a, x.1⟩, x.2⟩
#align mvqpf.sigma.repr MvQPF.Sigma.repr

instance : MvQPF (Sigma F) where
  P := Sigma.P F
  abs {α} := @Sigma.abs _ _ F _ _ α
  repr {α} := @Sigma.repr _ _ F _ _ α
  abs_repr := by rintro α ⟨x, f⟩; simp only [Sigma.abs, Sigma.repr, Sigma.eta, abs_repr]
                 -- ⊢ (fun {α} => Sigma.abs F) ((fun {α} => Sigma.repr F) { fst := x, snd := f })  …
                                  -- 🎉 no goals
  abs_map := by rintro α β f ⟨x, g⟩; simp only [Sigma.abs, MvPFunctor.map_eq]
                -- ⊢ (fun {α} => Sigma.abs F) (f <$$> { fst := x, snd := g }) = f <$$> (fun {α} = …
                                     -- ⊢ { fst := x.fst, snd := abs { fst := x.snd, snd := f ⊚ g } } = f <$$> { fst : …
                simp only [(· <$$> ·), ← abs_map, ← MvPFunctor.map_eq]
                -- 🎉 no goals

end Sigma

namespace Pi

instance : MvFunctor (Pi F) where map f x a := f <$$> x a

variable [∀ α, MvQPF <| F α]

/-- polynomial functor representation of a dependent product -/
protected def P : MvPFunctor n :=
  ⟨∀ a, (P (F a)).A, fun x i => Σ a, (P (F a)).B (x a) i⟩
set_option linter.uppercaseLean3 false in
#align mvqpf.pi.P MvQPF.Pi.P

/-- abstraction function for dependent products -/
protected def abs ⦃α⦄ : (Pi.P F).Obj α → Pi F α
  | ⟨a, f⟩ => fun x => MvQPF.abs ⟨a x, fun i y => f i ⟨_, y⟩⟩
#align mvqpf.pi.abs MvQPF.Pi.abs

/-- representation function for dependent products -/
protected def repr ⦃α⦄ : Pi F α → (Pi.P F).Obj α
  | f => ⟨fun a => (MvQPF.repr (f a)).1, fun _i a => (MvQPF.repr (f _)).2 _ a.2⟩
#align mvqpf.pi.repr MvQPF.Pi.repr

instance : MvQPF (Pi F) where
  P := Pi.P F
  abs := @Pi.abs _ _ F _ _
  repr := @Pi.repr _ _ F _ _
  abs_repr := by rintro α f; simp only [Pi.abs, Pi.repr, Sigma.eta, abs_repr]
                 -- ⊢ Pi.abs F (Pi.repr F f) = f
                             -- 🎉 no goals
  abs_map := by rintro α β f ⟨x, g⟩; simp only [Pi.abs, (· <$$> ·), ← abs_map]; rfl
                -- ⊢ Pi.abs F (f <$$> { fst := x, snd := g }) = f <$$> Pi.abs F { fst := x, snd : …
                                     -- ⊢ (match MvPFunctor.map (Pi.P F) f { fst := x, snd := g } with
                                                                                -- 🎉 no goals

end Pi

end MvQPF
