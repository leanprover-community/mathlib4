/-
Copyright (c) 2025 Shimanonogov Igor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shimanonogov Igor
-/
import Mathlib.Data.List.Defs

/-!
# repeatSelf

Proves various lemmas about `List.repeatSelf`.
-/

variable {α : Type*} (n m : ℕ) (w : List α)

namespace List

theorem repeatself_homo :
  List.repeatSelf n w ++ List.repeatSelf m w =  List.repeatSelf (n+m) w := by
  induction n with
  | zero => simp
  | succ p ih => simp [List.append_assoc, ih, Nat.add_assoc, Nat.add_comm]

end List
