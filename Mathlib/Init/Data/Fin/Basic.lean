/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Init.Data.Nat.Notation

/-!
# Theorems about equality in `Fin`.
-/

namespace Fin

variable {n : ℕ} {i j : Fin n}

@[deprecated eq_of_val_eq (since := "2024-02-15")]
theorem eq_of_veq : i.val = j.val → i = j := eq_of_val_eq

@[deprecated val_eq_of_eq (since := "2024-02-15")]
theorem veq_of_eq : i = j → i.val = j.val := val_eq_of_eq

-- These two aren't deprecated because `ne_of_val_ne` and `val_ne_of_ne`
-- use `¬a = b` instead of `a ≠ b`. TODO: fix or rename in Lean core.
theorem ne_of_vne (h : i.val ≠ j.val) : i ≠ j := ne_of_val_ne h
theorem vne_of_ne (h : i ≠ j) : i.val ≠ j.val := val_ne_of_ne h

end Fin
