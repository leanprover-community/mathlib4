import Mathlib.Geometry.Manifold.Instances.Quotient
import Mathlib.Geometry.Manifold.Notation

/-! # Tests for the differential geometry elaborators for quotient manifolds

For now, we only support quotients by properly discontinuous actions.
-/

open Bundle Filter Function Topology ContDiff Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {E E' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' H'} {n : ℕ∞ω} [IsManifold I n M]
  [IsManifold J n N]
  [T2Space M] [LocallyCompactSpace M]

section multiplicative

variable {G : Type*} [Group G] [MulAction G M]
  [ContinuousConstSMul G M] [IsCancelSMul G M]
  [ContMDiffConstSMul I n G M]

/-- info: ContMDiff I I n Quotient.mk' : Prop -/
#guard_msgs in
variable [ProperlyDiscontinuousSMul G M] in
#check CMDiff n (Quotient.mk' (s := MulAction.orbitRel G M))

set_option trace.Elab.DiffGeo.MDiff true in
/--
error: Could not find a model with corners for `Quotient (MulAction.orbitRel G M)`.
---
trace: [Elab.DiffGeo.MDiff] Finding a model with corners for: `M`
[Elab.DiffGeo.MDiff] 💥️ TotalSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      `M` is not a `Bundle.TotalSpace`.
[Elab.DiffGeo.MDiff] 💥️ TangentBundle
  [Elab.DiffGeo.MDiff] Failed with error:
      `M` is not a `TangentBundle`
[Elab.DiffGeo.MDiff] 💥️ NormedSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      Couldn't find a `NormedSpace` structure on `M` among local instances.
[Elab.DiffGeo.MDiff] ✅️ Manifold
  [Elab.DiffGeo.MDiff] ... not a quotient
  [Elab.DiffGeo.MDiff] considering instance of type `ChartedSpace H M`
  [Elab.DiffGeo.MDiff] `M` is a charted space over `H` via `inst✝¹¹`
  [Elab.DiffGeo.MDiff] Found model: `I`
[Elab.DiffGeo.MDiff] Finding a model with corners for: `Quotient (MulAction.orbitRel G M)`
[Elab.DiffGeo.MDiff] 💥️ TotalSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      `Quotient (MulAction.orbitRel G M)` is not a `Bundle.TotalSpace`.
[Elab.DiffGeo.MDiff] 💥️ TangentBundle
  [Elab.DiffGeo.MDiff] Failed with error:
      `Quotient (MulAction.orbitRel G M)` is not a `TangentBundle`
[Elab.DiffGeo.MDiff] 💥️ NormedSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      Couldn't find a `NormedSpace` structure on `Quotient (MulAction.orbitRel G M)` among local instances.
[Elab.DiffGeo.MDiff] 💥️ Manifold
  [Elab.DiffGeo.MDiff] `Quotient (MulAction.orbitRel G M)` is the quotient of `M` under a `G`-action`
  [Elab.DiffGeo.MDiff] Failed with error:
      Couldn't find a `ProperlyDiscontinuousSMul` instance for `G` action on `M` among local instances.
[Elab.DiffGeo.MDiff] 💥️ ContinuousLinearMap
  [Elab.DiffGeo.MDiff] Failed with error:
      `Quotient (MulAction.orbitRel G M)` is not a space of continuous linear maps
[Elab.DiffGeo.MDiff] 💥️ RealInterval
  [Elab.DiffGeo.MDiff] Failed with error:
      `Quotient (MulAction.orbitRel G M)` is not a coercion of a set to a type
[Elab.DiffGeo.MDiff] 💥️ EuclideanSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      `Quotient (MulAction.orbitRel G M)` is not a Euclidean space, half-space or quadrant
[Elab.DiffGeo.MDiff] 💥️ UpperHalfPlane
  [Elab.DiffGeo.MDiff] Failed with error:
      `Quotient (MulAction.orbitRel G M)` is not the complex upper half plane
[Elab.DiffGeo.MDiff] 💥️ Units of algebra
  [Elab.DiffGeo.MDiff] Failed with error:
      `Quotient (MulAction.orbitRel G M)` is not a set of units, in particular not of a complete normed algebra
[Elab.DiffGeo.MDiff] 💥️ Complex unit circle
  [Elab.DiffGeo.MDiff] Failed with error:
      `Quotient (MulAction.orbitRel G M)` is not the complex unit circle
[Elab.DiffGeo.MDiff] 💥️ Sphere
  [Elab.DiffGeo.MDiff] Failed with error:
      `Quotient (MulAction.orbitRel G M)` is not a coercion of a set to a type
[Elab.DiffGeo.MDiff] 💥️ NormedField
  [Elab.DiffGeo.MDiff] Failed with error:
      failed to synthesize
        NontriviallyNormedField (Quotient (MulAction.orbitRel G M))
      ⏎
      Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
[Elab.DiffGeo.MDiff] 💥️ InnerProductSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      Couldn't find an `InnerProductSpace` structure on `Quotient (MulAction.orbitRel G M)` among local instances.
-/
#guard_msgs in
#check CMDiff n (Quotient.mk' (s := MulAction.orbitRel G M))

end multiplicative

section additive

variable {G : Type*} [AddGroup G] [AddAction G M]
  [ProperlyDiscontinuousVAdd G M] [ContinuousConstVAdd G M] [IsCancelVAdd G M]
  [ContMDiffConstVAdd I n G M]

/-- info: ContMDiff I I n Quotient.mk' : Prop -/
#guard_msgs in
#check CMDiff n (Quotient.mk' (s := AddAction.orbitRel G M))

end additive
