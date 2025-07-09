/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Topology.EtaleSpace

/-!
# Primitives of holomorphic functions (and closed 1-forms)

We show that being a primitive of a holomorphic function is a locally constant predicate,
so the associated étalé space is a covering space. We then define integration of a holomorphic
function along a C⁰ path using monodromy of this covering space.
-/
