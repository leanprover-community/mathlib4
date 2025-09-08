/-
Copyright (c) 2025 Javier Burroni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Javier Burroni
-/
import Mathlib.Data.PNat.Defs
import Mathlib.Data.PNat.Basic
import Mathlib.Order.SuccPred.Basic
import Mathlib.Algebra.Order.SuccPred

/-!
# Order related instances for `ℕ+`
-/

namespace PNat
open Nat

instance instSuccOrder : SuccOrder ℕ+ :=
  SuccOrder.ofSuccLeIff (fun n => succPNat n) (by rfl)

instance instSuccAddOrder : SuccAddOrder ℕ+ where
  succ_eq_add_one x := by rfl

instance instNoMaxOrder : NoMaxOrder ℕ+ where
  exists_gt n := ⟨succPNat n, lt_succ_self n⟩

@[simp]
lemma succ_eq_succPNat (n : ℕ+) : Order.succ n = succPNat n := rfl

end PNat
