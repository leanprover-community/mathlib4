/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.Path
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Paths in uniform spaces

In this file we define a `UniformSpace` structure on `Path`s
between two points in a uniformspace
and prove that various functions associated with `Path`s are uniformly continuous.
-/

open scoped unitInterval

variable {X : Type*} [UniformSpace X] {x y : X}

namespace Path

instance instUniformSpace : UniformSpace (Path x y) :=
  .comap ((↑) : _ → C(I, X)) ContinuousMap.compactConvergenceUniformSpace

theorem uniformContinuous (γ : Path x y) : UniformContinuous γ :=
  CompactSpace.uniformContinuous_of_continuous <| map_continuous _

theorem uniformContinuous_extend_right (γ : Path x y) : UniformContinuous γ.extend :=
  γ.uniformContinuous.comp <| LipschitzWith.projIcc _ |>.uniformContinuous

end Path
