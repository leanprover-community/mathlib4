import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.Notation

/-! ## Tests for the differential geometry elaborators for spheres in metric spaces

**Note.**
This file also acts as a test for the delaborators corresponding to the custom elaborators,
so the resulting test output often does not show the inferred model with corners.
As that output is also tested elsewhere, this is fine.
-/

open Bundle Filter Function Topology Manifold

-- Suppose `M` is a real manifold over `E` with model `I`.
variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*}
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  -- suppose `E'` is a real normed space, and `E''` is a real inner product space.
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {E'' : Type*} [NormedAddCommGroup E''] [InnerProductSpace ℝ E''] {n : ℕ}

open ContDiff Manifold

section Circle

-- Make a new real manifold N with model J.
-- TODO: change this line to modify M and E instead (thus testing if everything
-- still works in the presence of two instances over different fields).
variable {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] {J : ModelWithCorners ℝ E'' H}
  {N : Type} [TopologicalSpace N] [ChartedSpace H N] [IsManifold J 2 N]

variable {g : Circle → N} {h : E'' → Circle} {k : Circle → ℝ} {y : Circle}

/-- info: ContMDiff (𝓡 1) J 2 g : Prop -/
#guard_msgs in
#check CMDiff 2 g

/-- info: MDiffAt h : E'' → Prop -/
#guard_msgs in
#check MDiffAt h

/-- info: MDiffAt k y : Prop -/
#guard_msgs in
#check MDiffAt k y

end Circle

section -- A sphere within a mere normed space is not supported.

variable {g : M → (Metric.sphere (0 : E') 1)} [Fact (Module.finrank ℝ E' = n + 1)]

/--
error: failed to synthesize instance of type class
  ChartedSpace (EuclideanSpace ℝ (Fin n)) ↑(Metric.sphere 0 1)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#check ContMDiff I (𝓡 n) 2 g

/--
error: Could not find a model with corners for `↑(Metric.sphere 0 1)`.

Hint: failures to find a model with corners can be debugged with the command `set_option trace.Elab.DiffGeo.MDiff true`.
-/
#guard_msgs in
#check CMDiff 2 g

end

section -- A domain with normed space also errors in the elaborators.

-- Assume we have a real inner product space which is not a normed space.
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  {f : (Metric.sphere (0 : G) 1) → E''} {g : ℝ → (Metric.sphere (0 : G) 1)}

-- The tests for the standard notation passes.

variable [Fact (Module.finrank ℝ G = 3)] in
/-- info: MDiff f : Prop -/
#guard_msgs in
#check MDifferentiable (𝓡 2) 𝓘(ℝ, E'') f

variable [Fact (Module.finrank ℝ G = 2 + 1)] in
/-- info: MDiff f : Prop -/
#guard_msgs in
#check MDifferentiable (𝓡 2) 𝓘(ℝ, E'') f

variable [Fact (Module.finrank ℝ G = 4 + 1)] in
/-- info: MDiff g : Prop -/
#guard_msgs in
#check MDifferentiable 𝓘(ℝ) (𝓡 4) g

variable [Fact (Module.finrank ℝ G = 3)] in
/-- info: MDiff f : Prop -/
#guard_msgs in
#check MDiff f

variable [Fact (Module.finrank ℝ G = 2 + 1)] in
/-- info: MDiff f : Prop -/
#guard_msgs in
#check MDiff f

-- The following two tests are variants of the previous tests with target an inner product space
-- and not a normed space: this used to fail in the past.
variable {f' : (Metric.sphere (0 : G) 1) → E'} [Fact (Module.finrank ℝ G = 3)] in
/-- info: MDiff f' : Prop -/
#guard_msgs in
#check MDiff f'

variable {f' : (Metric.sphere (0 : G) 1) → E'} [Fact (Module.finrank ℝ G = 2 + 1)] in
/-- info: MDiff f' : Prop -/
#guard_msgs in
#check MDiff f'

variable [Fact (Module.finrank ℝ G = 4 + 1)] in
/-- info: MDiff g : Prop -/
#guard_msgs in
#check MDiff g

end

variable {f : (Metric.sphere (0 : E'') 1) → ℝ} {g : M → (Metric.sphere (0 : E'') 1)}

variable [Fact (Module.finrank ℝ E'' = n + 1)] in
/-- info: ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 2 f : Prop -/
#guard_msgs in
#check ContMDiff (𝓡 n) 𝓘(ℝ) 2 f

variable [Fact (Module.finrank ℝ E'' = n + 1)] in
/-- info: ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 2 f : Prop -/
#guard_msgs in
#check CMDiff 2 f

variable [Fact (Module.finrank ℝ E'' = 2 * n + 1)] in
/-- info: ContMDiff I (𝓡 2 * n) 2 g : Prop -/
#guard_msgs in
#check ContMDiff I (𝓡 (2 * n)) 2 g

variable [Fact (Module.finrank ℝ E'' = 2 * n + 1)] in
/-- info: ContMDiff I (𝓡 2 * n) 2 g : Prop -/
#guard_msgs in
#check CMDiff 2 g

-- The elaborators even perform slightly sophisticated unification of dimensions.
section
variable [Fact (Module.finrank ℝ E'' = n + 2 * n + 3)]

/-- info: ContMDiff (𝓡 n + 2 * n + 2) 𝓘(ℝ, ℝ) ω f : Prop -/
#guard_msgs in
#check CMDiff ω f

/-- info: ContMDiff I (𝓡 n + 2 * n + 2) ∞ g : Prop -/
#guard_msgs in
#check CMDiff ∞ g
end

section

-- Note: 3 and 2 + 1 are treated the same \o/
-- (since our implementation uses qq matching, which does unification).
variable [Fact (Module.finrank ℝ E'' = 3)] in
/-- info: ContMDiff I (𝓡 2) ∞ g : Prop -/
#guard_msgs in
#check CMDiff ∞ g

variable [Fact (Module.finrank ℝ E'' = 2 + 1)] in
/-- info: ContMDiff I (𝓡 2) ∞ g : Prop -/
#guard_msgs in
#check CMDiff ∞ g

end

-- This matching is not too clever, though. 2 + 4 is unified as (2 + 3) + 1 (not 5 + 1).
variable [Fact (Module.finrank ℝ E'' = 2 + 4)] in
/-- info: MDiff f : Prop -/
#guard_msgs in
#check MDiff f

-- Testing an error message: if there's a finrank fact about a different normed space in scope,
-- the tracing output mentions this.
set_option trace.Elab.DiffGeo true in
variable [Fact (Module.finrank ℝ E = 3)] in
/--
error: Could not find a model with corners for `↑(Metric.sphere 0 1)`.
---
trace: [Elab.DiffGeo.MDiff] Finding a model with corners for: `↑(Metric.sphere 0 1)`
[Elab.DiffGeo.MDiff] ❌️ TotalSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      `↑(Metric.sphere 0 1)` is not a `Bundle.TotalSpace`.
[Elab.DiffGeo.MDiff] ❌️ TangentBundle
  [Elab.DiffGeo.MDiff] Failed with error:
      `↑(Metric.sphere 0 1)` is not a `TangentBundle`
[Elab.DiffGeo.MDiff] ❌️ NormedSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      Couldn't find a `NormedSpace` structure on `↑(Metric.sphere 0 1)` among local instances.
[Elab.DiffGeo.MDiff] ❌️ Manifold
  [Elab.DiffGeo.MDiff] considering instance of type `ChartedSpace H M`
  [Elab.DiffGeo.MDiff] Failed with error:
      Couldn't find a `ChartedSpace` structure on `↑(Metric.sphere 0
          1)` among local instances, and `↑(Metric.sphere 0
          1)` is not the charted space of some type in the local context either.
[Elab.DiffGeo.MDiff] ❌️ ContinuousLinearMap
  [Elab.DiffGeo.MDiff] Failed with error:
      `↑(Metric.sphere 0 1)` is not a space of continuous linear maps
[Elab.DiffGeo.MDiff] ❌️ RealInterval
  [Elab.DiffGeo.MDiff] Failed with error:
      `Metric.sphere 0 1` is not a closed real interval
[Elab.DiffGeo.MDiff] ❌️ EuclideanSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      `↑(Metric.sphere 0 1)` is not a Euclidean space, half-space or quadrant
[Elab.DiffGeo.MDiff] ❌️ UpperHalfPlane
  [Elab.DiffGeo.MDiff] Failed with error:
      `↑(Metric.sphere 0 1)` is not the complex upper half plane
[Elab.DiffGeo.MDiff] ❌️ Units of algebra
  [Elab.DiffGeo.MDiff] Failed with error:
      `↑(Metric.sphere 0 1)` is not a set of units, in particular not of a complete normed algebra
[Elab.DiffGeo.MDiff] ❌️ Complex unit circle
  [Elab.DiffGeo.MDiff] Failed with error:
      `↑(Metric.sphere 0 1)` is not the complex unit circle
[Elab.DiffGeo.MDiff] ❌️ Sphere
  [Elab.DiffGeo.MDiff] `Metric.sphere 0 1` is a metric sphere in `E''`
  [Elab.DiffGeo.MDiff] considering instance of type `InnerProductSpace ℝ E''`
  [Elab.DiffGeo.MDiff] `E''` is a `ℝ`-inner product space via `inst✝¹`
  [Elab.DiffGeo.MDiff] considering instance of type `Fact (Module.finrank ℝ E = 3)`
  [Elab.DiffGeo.MDiff] considering fact of kind `Module.finrank ℝ E = 3`
  [Elab.DiffGeo.MDiff] found a fact about finrank, but not about `finrank ℝ E`: continue the search
  [Elab.DiffGeo.MDiff] Failed with error:
      Found no fact `finrank ℝ E'' = n + 1` in the local context
[Elab.DiffGeo.MDiff] ❌️ NormedField
  [Elab.DiffGeo.MDiff] Failed with error:
      failed to synthesize instance of type class
        NontriviallyNormedField ↑(Metric.sphere 0 1)
      ⏎
      Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
[Elab.DiffGeo.MDiff] ❌️ InnerProductSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      Couldn't find an `InnerProductSpace` structure on `↑(Metric.sphere 0 1)` among local instances.
-/
#guard_msgs in
#check MDiff f
