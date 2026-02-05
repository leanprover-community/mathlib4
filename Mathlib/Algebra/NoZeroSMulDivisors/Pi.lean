/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Yaël Dillies
-/
module

public import Mathlib.Algebra.NoZeroSMulDivisors.Defs
public import Mathlib.Algebra.Group.Action.Pi

/-!
# Pi instances for NoZeroSMulDivisors

This file defines instances for NoZeroSMulDivisors on Pi types.
-/

@[expose] public section


universe u v

variable {I : Type u}

-- The indexing type
variable {f : I → Type v}

instance Pi.noZeroSMulDivisors (α) [Semiring α] [IsDomain α] [∀ i, AddCommGroup <| f i]
    [∀ i, Module α <| f i] [∀ i, NoZeroSMulDivisors α <| f i] :
    NoZeroSMulDivisors α (∀ i : I, f i) :=
  ⟨fun {_ _} h =>
    or_iff_not_imp_left.mpr fun hc =>
      funext fun i => (smul_eq_zero.mp (congr_fun h i)).resolve_left hc⟩

/-- A special case of `Pi.noZeroSMulDivisors` for non-dependent types. Lean struggles to
synthesize this instance by itself elsewhere in the library. -/
instance _root_.Function.noZeroSMulDivisors {ι α β : Type*} [Semiring α] [IsDomain α]
    [AddCommGroup β] [Module α β] [NoZeroSMulDivisors α β] : NoZeroSMulDivisors α (ι → β) :=
  Pi.noZeroSMulDivisors _
