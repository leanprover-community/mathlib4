/-
Copyright (c) 2021 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Topology.Instances.Matrix.Basic.Basic

open Matrix

variable {n R : Type*} [TopologicalSpace R] [DecidableEq n] [Fintype n] [CommRing R]

instance : TopologicalSpace (SpecialLinearGroup n R) :=
  instTopologicalSpaceSubtype
