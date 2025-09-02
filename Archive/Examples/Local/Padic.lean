/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib

/-!
# Instances to declare the p-adic numbers as a local field

## Tags

valued, local field, nonarchimedean, rank one, compact, locally compact
-/

variable {p : ℕ} [Fact p.Prime]

suppress_compilation

local notation "F" => ℚ_[p]

example : Field F := inferInstance
example : UniformSpace F := inferInstance
example : IsTopologicalDivisionRing F := inferInstance
example : CompleteSpace F := inferInstance
example : LocallyCompactSpace F := inferInstance

-- local instance : ValuativeRel F := inferInstance
-- example : ValuativeTopology F := inferInstance
-- example : ValuativeRel.IsNontrivial F := inferInstance
-- example : ValuativeRel.IsRankLeOne F := inferInstance
-- example : ValuativeRel.IsDiscrete F := inferInstance
