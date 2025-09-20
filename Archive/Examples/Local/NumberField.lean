/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib

/-!
# Instances to declare completions of a number field as a local field

## Tags

valued, local field, nonarchimedean, rank one, compact, locally compact
-/

open IsDedekindDomain

variable (A : Type*) [CommRing A] [IsDedekindDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (v : HeightOneSpectrum A) (hv : Finite (A ⧸ v.asIdeal))

suppress_compilation

local notation "F" => (v.adicCompletion K)

example : Field F := inferInstance
example : UniformSpace F := inferInstance
example : IsTopologicalDivisionRing F := inferInstance
example : CompleteSpace F := inferInstance
proof_wanted locallyCompact : LocallyCompactSpace F

-- local instance : ValuativeRel F := inferInstance
-- example : ValuativeTopology F := inferInstance
-- example : ValuativeRel.IsNontrivial F := inferInstance
-- example : ValuativeRel.IsRankLeOne F := inferInstance
-- example : ValuativeRel.IsDiscrete F := inferInstance
