/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.ENat.Lattice

/-!
# N∞ scalar multiplication commutes with suprema
-/

public section

namespace ENat

variable {ι : Sort*}

lemma smul_iSup {R} [SMul R ℕ∞] [IsScalarTower R ℕ∞ ℕ∞] (f : ι → ℕ∞) (c : R) :
    c • ⨆ i, f i = ⨆ i, c • f i := by
  simpa using ENat.mul_iSup (c • 1) f

lemma smul_sSup {R} [SMul R ℕ∞] [IsScalarTower R ℕ∞ ℕ∞] (s : Set ℕ∞) (c : R) :
    c • sSup s = ⨆ a ∈ s, c • a := by
  simp_rw [sSup_eq_iSup, smul_iSup]

end ENat
