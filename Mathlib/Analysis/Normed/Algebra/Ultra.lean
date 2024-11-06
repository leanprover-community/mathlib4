/-
Copyright (c) 2024 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/

import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Normed algebra preserves ultrametricity

This file contains the proof that a normed division ring over an ultrametric field is ultrametric.
-/

theorem IsUltrametricDist.of_normedAlgebra (K : Type*) {L : Type*} [NormedField K]
    [NormedDivisionRing L] [NormedAlgebra K L] [h : IsUltrametricDist K] : IsUltrametricDist L := by
  rw [isUltrametricDist_iff_forall_norm_natCast_le_one] at h ⊢
  exact fun n => (algebraMap.coe_natCast (R := K) (A := L) n) ▸ norm_algebraMap' L (n : K) ▸ h n
