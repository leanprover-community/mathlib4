import Mathlib.Geometry.Manifold.Notation
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Tests for the differential geometry delaborators

Specific tests for the delaborators corresponding to the custom elaborators.

-/

set_option pp.unicode.fun true

open Bundle Filter Function Topology
open scoped Manifold ContDiff

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]
  (f : M → M) (x : M) (s : Set M)
  (v : (x : M) → TangentSpace I x)

/-- info: MDiffAt f x : Prop -/
#guard_msgs in
#check MDiffAt f x

/-- info: MDiffAt[s] f x : Prop -/
#guard_msgs in
#check MDiffAt[s] f x

/-- info: MDiffAt (T% v) x : Prop -/
#guard_msgs in
#check MDiffAt (T% v) x

/-- info: MDiffAt[s] (T% v) x : Prop -/
#guard_msgs in
#check MDiffAt[s] (T% v) x

/-- info: mfderiv% f x : TangentSpace I x →L[ℝ] TangentSpace I (f x) -/
#guard_msgs in
#check mfderiv% f x

/-- info: mfderiv% (T% v) x : TangentSpace I x →L[ℝ] TangentSpace (I.prod 𝓘(ℝ, E)) ⟨x, v x⟩ -/
#guard_msgs in
#check mfderiv% (T% v) x

/-- info: ⟨x, v x⟩ : TotalSpace E (TangentSpace I) -/
#guard_msgs in
#check TotalSpace.mk' E x (v x)

/-- info: ⟨x, v x⟩ : TotalSpace E (TangentSpace I) -/
#guard_msgs in
#check TotalSpace.mk (F := E) x (v x)
