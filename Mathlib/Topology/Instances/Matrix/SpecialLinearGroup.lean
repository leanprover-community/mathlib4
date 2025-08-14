/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Topology.Instances.Matrix.Basic.Basic

/-!
# Topological properties of SLₙ

This file is a place to collect topological results about `SLₙ`
-/


open Matrix

variable {n R : Type*} [TopologicalSpace R] [DecidableEq n] [Fintype n] [CommRing R]

instance : TopologicalSpace (SpecialLinearGroup n R) :=
  instTopologicalSpaceSubtype
