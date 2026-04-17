/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module -- shake: keep-all

public import Mathlib.RingTheory.FiniteType
public import Mathlib.LinearAlgebra.InvariantBasisNumber

deprecated_module (since := "2026-04-18")

@[expose] public section

@[deprecated "instance already exists" (since := "2026-04-18")]
instance (priority := 100) commRing_strongRankCondition (R : Type*) [CommRing R] [Nontrivial R] :
    StrongRankCondition R := inferInstance
