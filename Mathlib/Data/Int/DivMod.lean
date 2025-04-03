/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

/-!
# Basic lemmas about division and modulo for integers

-/

namespace Int

/-! ### `emod` -/

theorem emod_eq_sub_self_emod {a b : Int} : a % b = (a - b) % b :=
  (emod_sub_cancel a b).symm

theorem emod_eq_add_self_emod {a b : Int} : a % b = (a + b) % b :=
  add_emod_self.symm
