import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Tests for the differential geometry delaborators for `mvfderiv(Within)`

-/

set_option pp.unicode.fun true

open Bundle Filter Function Topology
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' n M']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J n N]
  {s t : Set M} {x : M}
  {n : ℕ∞ω}

variable {f : M → 𝕜} {g : M → F}

/-- info: d[s] f : (x : M) → TangentSpace I x →L[𝕜] 𝕜 -/
#guard_msgs in
#check mvfderivWithin I f s
/-- info: d[s] f x : TangentSpace I x →L[𝕜] 𝕜 -/
#guard_msgs in
#check mvfderivWithin I f s x

/-- info: d[s] f : (x : M) → TangentSpace I x →L[𝕜] 𝕜 -/
#guard_msgs in
#check d[s] f
/-- info: d[s] f x : TangentSpace I x →L[𝕜] 𝕜 -/
#guard_msgs in
#check d[s] f x

/-- info: d[s] g x : TangentSpace I x →L[𝕜] F -/
#guard_msgs in
#check d[s] g x

/-- info: d[s] g : (x : M) → TangentSpace I x →L[𝕜] F -/
#guard_msgs in
#check d[s] g

/-- info: d% f : (x : M) → TangentSpace I x →L[𝕜] 𝕜 -/
#guard_msgs in
#check mvfderiv I f
/-- info: d% f : (x : M) → TangentSpace I x →L[𝕜] 𝕜 -/
#guard_msgs in
#check d% f

/-- info: d% f x : TangentSpace I x →L[𝕜] 𝕜 -/
#guard_msgs in
#check mvfderiv I f x

/-- info: d% f x : TangentSpace I x →L[𝕜] 𝕜 -/
#guard_msgs in
#check d% f x

/-- info: d% g x : TangentSpace I x →L[𝕜] F -/
#guard_msgs in
#check d% g x

/-- info: d% g : (x : M) → TangentSpace I x →L[𝕜] F -/
#guard_msgs in
#check d% g

section no_notation

set_option pp.notation false -- Test the actual elaborators: turn off all notation

/--
info: mvfderivWithin I f s : (x : M) → ContinuousLinearMap (RingHom.id 𝕜) (TangentSpace I x) 𝕜
-/
#guard_msgs in
#check mvfderivWithin I f s
/-- info: mvfderivWithin I f s x : ContinuousLinearMap (RingHom.id 𝕜) (TangentSpace I x) 𝕜 -/
#guard_msgs in
#check mvfderivWithin I f s x

/--
info: mvfderivWithin I f s : (x : M) → ContinuousLinearMap (RingHom.id 𝕜) (TangentSpace I x) 𝕜
-/
#guard_msgs in
#check d[s] f
/-- info: mvfderivWithin I f s x : ContinuousLinearMap (RingHom.id 𝕜) (TangentSpace I x) 𝕜 -/
#guard_msgs in
#check d[s] f x

/-- info: mvfderivWithin I g s x : ContinuousLinearMap (RingHom.id 𝕜) (TangentSpace I x) F -/
#guard_msgs in
#check d[s] g x

/--
info: mvfderivWithin I g s : (x : M) → ContinuousLinearMap (RingHom.id 𝕜) (TangentSpace I x) F
-/
#guard_msgs in
#check d[s] g

/-- info: mvfderiv I f : (x : M) → ContinuousLinearMap (RingHom.id 𝕜) (TangentSpace I x) 𝕜 -/
#guard_msgs in
#check mvfderiv I f
/-- info: mvfderiv I f : (x : M) → ContinuousLinearMap (RingHom.id 𝕜) (TangentSpace I x) 𝕜 -/
#guard_msgs in
#check d% f

/-- info: mvfderiv I f x : ContinuousLinearMap (RingHom.id 𝕜) (TangentSpace I x) 𝕜 -/
#guard_msgs in
#check mvfderiv I f x

/-- info: mvfderiv I f x : ContinuousLinearMap (RingHom.id 𝕜) (TangentSpace I x) 𝕜 -/
#guard_msgs in
#check d% f x

/-- info: mvfderiv I g x : ContinuousLinearMap (RingHom.id 𝕜) (TangentSpace I x) F -/
#guard_msgs in
#check d% g x

/-- info: mvfderiv I g : (x : M) → ContinuousLinearMap (RingHom.id 𝕜) (TangentSpace I x) F -/
#guard_msgs in
#check d% g

end no_notation
