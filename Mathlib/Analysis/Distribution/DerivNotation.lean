/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Topology.Algebra.Module.Basic

/-! # Type classes for derivatives

In this file we define type classes for tba.

Moreover, we provide type-classes that encode the linear structure.
-/

@[expose] public section

universe u' u v w

open Fin

class LineDeriv (V : Type u) (E : Type v) (F : outParam (Type w)) where
  /-- `∂_{v} f` is the partial derivative of `f` in direction `v`. The meaning of this notation is
  type-dependent. -/
  lineDerivOp : V → E → F

namespace LineDeriv

@[inherit_doc] scoped notation "∂_{" v "}" => LineDeriv.lineDerivOp v

variable {V E : Type*} [LineDeriv V E E]

/-- The iterated line derivative. -/
def iteratedLineDerivOp {n : ℕ} : (Fin n → V) → E → E :=
  Nat.recOn n (fun _ ↦ id) (fun _ rec y ↦ LineDeriv.lineDerivOp (y 0) ∘ rec (Fin.tail y))

@[inherit_doc] scoped notation "∂^{" v "}" => LineDeriv.iteratedLineDerivOp v

@[simp]
theorem iteratedLineDerivOp_zero (m : Fin 0 → V) (f : E) : ∂^{m} f = f :=
  rfl

@[simp]
theorem iteratedLineDerivOp_zero' (m : Fin 0 → V) : (∂^{m} : E → E) = id :=
  rfl

@[simp]
theorem iteratedLineDerivOp_one (m : Fin 1 → V) (f : E) : ∂^{m} f = ∂_{m 0} f :=
  rfl

theorem iteratedLineDerivOp_succ_left {n : ℕ} (m : Fin (n + 1) → V) (f : E) :
    ∂^{m} f = ∂_{m 0} (∂^{Fin.tail m} f) :=
  rfl

theorem iteratedLineDerivOp_succ_left' {n : ℕ} (m : Fin (n + 1) → V) :
    (∂^{m} : E → E) = ∂_{m 0} ∘ ∂^{Fin.tail m} :=
  rfl

theorem iteratedLineDerivOp_succ_right {n : ℕ} (m : Fin (n + 1) → V) (f : E) :
    ∂^{m} f = ∂^{Fin.init m} (∂_{m (Fin.last n)} f) := by
  induction n with
  | zero =>
    rw [iteratedLineDerivOp_zero, iteratedLineDerivOp_one, Fin.last_zero]
  -- The proof is `∂^{n + 2} = ∂ ∂^{n + 1} = ∂ ∂^n ∂ = ∂^{n+1} ∂`
  | succ n IH =>
    have hmzero : Fin.init m 0 = m 0 := by simp only [Fin.init_def, Fin.castSucc_zero]
    have hmtail : Fin.tail m (Fin.last n) = m (Fin.last n.succ) := by
      simp only [Fin.tail_def, Fin.succ_last]
    calc
      _ = ∂_{m 0} (∂^{Fin.tail m} f) := iteratedLineDerivOp_succ_left _ _
      _ = ∂_{m 0} (∂^{_} (∂_{_} f)) := by
        congr 1
        exact IH _
      _ = _ := by
        simp only [hmtail, iteratedLineDerivOp_succ_left, hmzero, Fin.tail_init_eq_init_tail]

end LineDeriv

open LineDeriv

class LineDerivModule (R : Type u') (V : Type u) (E : Type v) (F : outParam (Type w))
  [AddCommGroup E] [AddCommGroup F] [SMul R E] [SMul R F] [LineDeriv V E F] where
  lineDerivOp_add (v : V) (x y : E) : ∂_{v} (x + y) = ∂_{v} x + ∂_{v} y
  lineDerivOp_smul (v : V) (r : R) (x : E) : ∂_{v} (r • x) = r • ∂_{v} x

class ContinuousLineDeriv (V : Type u) (E : Type v) (F : outParam (Type w))
  [TopologicalSpace E] [TopologicalSpace F] [LineDeriv V E F] where
  lineDerivOp_continuous (v : V) : Continuous (∂_{v} : E → F)

attribute [fun_prop] ContinuousLineDeriv.lineDerivOp_continuous

section LineDeriv

variable {R V E F : Type*} --[Ring R] [AddCommGroup E] [AddCommGroup F] [Module R E] [Module R F]
  [TopologicalSpace E] --[IsTopologicalAddGroup E]
  --[TopologicalSpace F] [IsTopologicalAddGroup F]
  [LineDeriv V E E] [ContinuousLineDeriv V E E]

@[fun_prop]
theorem continuous_iteratedLineDerivOp {n : ℕ} (m : Fin n → V) : Continuous (∂^{m} : E → E) := by
  induction n with
  | zero =>
    rw [iteratedLineDerivOp_zero']
    fun_prop
  | succ n IH =>
    rw [iteratedLineDerivOp_succ_left']
    exact (ContinuousLineDeriv.lineDerivOp_continuous _).comp (IH _)

end LineDeriv

class FDeriv (E : Type v) (F : outParam (Type w)) where
  /-- `∂_f f` is the Fréchet derivative of `f` in direction. The meaning of this notation is
  type-dependent. -/
  fderivOp : E → F

namespace FDeriv

@[inherit_doc] scoped notation "∂_f" => FDeriv.fderivOp

end FDeriv
