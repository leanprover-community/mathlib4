/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.ENat.Basic

#align_import data.enat.lattice from "leanprover-community/mathlib"@"f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c"

/-!
# Extended natural numbers form a complete linear order

This instance is not in `Data.ENat.Basic` to avoid dependency on `Finset`s.

We also restate some lemmas about `WithTop` for `ENat` to have versions that use `Nat.cast` instead
of `WithTop.some`.
-/

-- porting notes: was `deriving instance` but "default handlers have not been implemented yet"
-- porting notes: `noncomputable` through 'Nat.instConditionallyCompleteLinearOrderBotNat'
noncomputable instance : CompleteLinearOrder ENat :=
  inferInstanceAs (CompleteLinearOrder (WithTop ℕ))

namespace ENat

variable {ι : Sort*} {f : ι → ℕ}

lemma iSup_coe_lt_top : (⨆ x, ↑(f x) : ℕ∞) < ⊤ ↔ BddAbove (Set.range f) :=
  WithTop.iSup_coe_lt_top f

theorem coe_iSup (h : BddAbove (Set.range f)) : ↑(⨆ i, f i) = (⨆ i, f i : ℕ∞) :=
  WithTop.coe_iSup _ h

end ENat
