/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib

/-!
# Instances to declare fraction rings of witt vectors over finite field as a local field

## Tags

valued, local field, nonarchimedean, rank one, compact, locally compact
-/

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K] [CharP K p]

suppress_compilation

local notation "F" => FractionRing (WittVector p K)

example : Field F := inferInstance
-- example : UniformSpace F := inferInstance  -- can't `proof_wanted` data
-- example : IsTopologicalDivisionRing F := inferInstance -- needs TopologicalSpace
-- example : CompleteSpace F := inferInstance
-- example : LocallyCompactSpace F := inferInstance

-- local instance : ValuativeRel F := inferInstance  -- can't `proof_wanted` data
-- proof_wanted valTopology : ValuativeTopology F  -- needs TopologicalSpace
-- example : ValuativeRel.IsNontrivial F := inferInstance
-- example : ValuativeRel.IsRankLeOne F := inferInstance
-- example : ValuativeRel.IsDiscrete F := inferInstance
