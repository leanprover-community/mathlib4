/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Topology.Algebra.Module.LinearMap

/-! # Type classes for derivatives

In this file we define notation type classes for line derivatives, also known as partial
derivatives.

Moreover, we provide type-classes that encode the linear structure.

Currently, this type class is only used by Schwartz functions. Future uses include derivatives on
test functions, distributions, tempered distributions, and Sobolev spaces (and other generalized
function spaces).
-/

@[expose] public section

universe u' u v w

variable {R V E F : Type*}

open Fin

/--
The notation typeclass for the line derivative.
-/
class LineDeriv (V : Type u) (E : Type v) (F : outParam (Type w)) where
  /-- `∂_{v} f` is the line derivative of `f` in direction `v`. The meaning of this notation is
  type-dependent. -/
  lineDerivOp : V → E → F

namespace LineDeriv

@[inherit_doc] scoped notation "∂_{" v "}" => LineDeriv.lineDerivOp v

variable {V E : Type*} [LineDeriv V E E]

/-- `∂^{m} f` is the iterated line derivative of `f`, where `m` is a finite number of (different)
directions. -/
def iteratedLineDerivOp {n : ℕ} : (Fin n → V) → E → E :=
  Nat.recOn n (fun _ ↦ id) (fun _ rec y ↦ LineDeriv.lineDerivOp (y 0) ∘ rec (tail y))

@[inherit_doc] scoped notation "∂^{" v "}" => LineDeriv.iteratedLineDerivOp v

@[simp]
theorem iteratedLineDerivOp_zero (m : Fin 0 → V) (f : E) : ∂^{m} f = f :=
  rfl

@[simp]
theorem iteratedLineDerivOp_one (m : Fin 1 → V) (f : E) : ∂^{m} f = ∂_{m 0} f :=
  rfl

theorem iteratedLineDerivOp_succ_left {n : ℕ} (m : Fin (n + 1) → V) (f : E) :
    ∂^{m} f = ∂_{m 0} (∂^{tail m} f) :=
  rfl

theorem iteratedLineDerivOp_succ_right {n : ℕ} (m : Fin (n + 1) → V) (f : E) :
    ∂^{m} f = ∂^{init m} (∂_{m (last n)} f) := by
  induction n with
  | zero => rfl
  -- The proof is `∂^{n + 2} = ∂ ∂^{n + 1} = ∂ ∂^n ∂ = ∂^{n+1} ∂`
  | succ n IH =>
    have hmzero : init m 0 = m 0 := by simp only [init_def, castSucc_zero]
    have hmtail : tail m (last n) = m (last n.succ) := by
      simp only [tail_def, succ_last]
    calc
      _ = ∂_{m 0} (∂^{tail m} f) := iteratedLineDerivOp_succ_left _ _
      _ = ∂_{m 0} (∂^{init <| tail m} (∂_{tail m <| last n} f)) := by
        congr 1
        exact IH _
      _ = _ := by
        rw [hmtail, iteratedLineDerivOp_succ_left, hmzero, tail_init_eq_init_tail]

@[simp]
theorem iteratedLineDerivOp_const_eq_iter_lineDerivOp (n : ℕ) (y : V) (f : E) :
    ∂^{fun (_ : Fin n) ↦ y} f = ∂_{y}^[n] f := by
  induction n with
  | zero => rfl
  | succ n IH =>
    rw [iteratedLineDerivOp_succ_left, Function.iterate_succ_apply']
    congr

end LineDeriv

open LineDeriv

/--
The line derivative is additive, `∂_{v} (x + y) = ∂_{v} x + ∂_{v} y` for all `x y : E`.

Note that `lineDeriv` on functions is not additive.
-/
class LineDerivAdd (V : Type u) (E : Type v) (F : outParam (Type w))
    [AddCommGroup E] [AddCommGroup F] [LineDeriv V E F] where
  lineDerivOp_add (v : V) (x y : E) : ∂_{v} (x + y) = ∂_{v} x + ∂_{v} y

/--
The line derivative commutes with scalar multiplication, `∂_{v} (r • x) = r • ∂_{v} x` for all
`r : R` and `x : E`.
-/
class LineDerivSMul (R : Type*) (V : Type u) (E : Type v) (F : outParam (Type w))
    [SMul R E] [SMul R F] [LineDeriv V E F] where
  lineDerivOp_smul (v : V) (r : R) (x : E) : ∂_{v} (r • x) = r • ∂_{v} x

/--
The line derivative is continuous.
-/
class ContinuousLineDeriv (V : Type u) (E : Type v) (F : outParam (Type w))
    [TopologicalSpace E] [TopologicalSpace F] [LineDeriv V E F] where
  continuous_lineDerivOp (v : V) : Continuous (∂_{v} : E → F)

attribute [fun_prop] ContinuousLineDeriv.continuous_lineDerivOp

namespace LineDeriv

export LineDerivAdd (lineDerivOp_add)
export LineDerivSMul (lineDerivOp_smul)
export ContinuousLineDeriv (continuous_lineDerivOp)

section lineDerivOpCLM

variable [Ring R] [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
  [TopologicalSpace E] [TopologicalSpace F]
  [LineDeriv V E F] [LineDerivAdd V E F] [LineDerivSMul R V E F] [ContinuousLineDeriv V E F]

variable (R E) in
/-- The line derivative as a continuous linear map. -/
def lineDerivOpCLM (m : V) : E →L[R] F where
  toFun := ∂_{m}
  map_add' := lineDerivOp_add m
  map_smul' := lineDerivOp_smul m
  cont := by fun_prop

@[simp]
theorem lineDerivOpCLM_apply (m : V) (x : E) :
    lineDerivOpCLM R E m x = ∂_{m} x := rfl

end lineDerivOpCLM

section iteratedLineDerivOp

variable [LineDeriv V E E]
variable {n : ℕ} (m : Fin n → V)

theorem iteratedLineDerivOp_add [AddCommGroup E] [LineDerivAdd V E E] (x y : E) :
    ∂^{m} (x + y) = ∂^{m} x + ∂^{m} y := by
  induction n with
  | zero =>
    simp
  | succ n IH =>
    simp_rw [iteratedLineDerivOp_succ_left, IH, lineDerivOp_add]

theorem iteratedLineDerivOp_smul [SMul R E] [LineDerivSMul R V E E] (r : R) (x : E) :
    ∂^{m} (r • x) = r • ∂^{m} x := by
  induction n with
  | zero =>
    simp
  | succ n IH =>
    simp_rw [iteratedLineDerivOp_succ_left, IH, lineDerivOp_smul]

variable [TopologicalSpace E]

@[fun_prop]
theorem continuous_iteratedLineDerivOp [ContinuousLineDeriv V E E] {n : ℕ} (m : Fin n → V) :
    Continuous (∂^{m} : E → E) := by
  induction n with
  | zero =>
    exact continuous_id
  | succ n IH =>
    exact (continuous_lineDerivOp _).comp (IH _)

variable [Ring R] [AddCommGroup E] [Module R E]
  [LineDerivAdd V E E] [LineDerivSMul R V E E] [ContinuousLineDeriv V E E]

variable (R E) in
/-- The iterated line derivative as a continuous linear map. -/
def iteratedLineDerivOpCLM {n : ℕ} (m : Fin n → V) : E →L[R] E where
  toFun := ∂^{m}
  map_add' := iteratedLineDerivOp_add m
  map_smul' := iteratedLineDerivOp_smul m
  cont := by fun_prop

@[simp]
theorem iteratedLineDerivOpCLM_apply {n : ℕ} (m : Fin n → V) (x : E) :
    iteratedLineDerivOpCLM R E m x = ∂^{m} x := rfl

end iteratedLineDerivOp

end LineDeriv
