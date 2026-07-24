/-
Copyright (c) 2026 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
module

public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology

/-!

-/

@[expose] public section

noncomputable section

open Filter Set Valuation MonoidWithZeroHom ValuativeRel

open scoped NNReal

section

variable {K : Type*} [hK : NormedField K] [IsUltrametricDist K]

namespace NormedField

@[instance_reducible]
def toValuativeRel : ValuativeRel K := sorry

@[instance_reducible]
def isValuativeTopology :
    letI := toValuativeRel (K := K)
    IsValuativeTopology K := sorry

end NormedField

namespace IsValuativeTopology

variable (L : Type*) [Field L] [ValuativeRel L]
  [IsRankLeOne L] [UniformSpace L] [IsUniformAddGroup L] [IsValuativeTopology L]

open Valuation

/-- The normed field structure determined by a rank one valuation. -/
@[instance_reducible]
def toNormedField : NormedField L := sorry

@[instance_reducible]
def toNontrivilallyNormedField [IsNontrivial L] : NontriviallyNormedField L := sorry

-- end of Mathlib.RingTheory.Valuation.RankOne
-- link between a valuation rank one and IsNontrivial

end IsValuativeTopology
