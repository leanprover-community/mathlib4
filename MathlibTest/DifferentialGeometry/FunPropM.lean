
import Mathlib.Geometry.Manifold.Notation
import Mathlib.Geometry.Manifold.Instances.Sphere

/-- error: Goal is not of the form `ModelWithCorners 𝕜 E H` -/
#guard_msgs in
#find_model true

/-- error: Goal is not of the form `ModelWithCorners 𝕜 E H` -/
#guard_msgs in
#find_model (2 + 2 = true)

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞} {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H : Type*}
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

-- TODO: add #find_model as an exception to the hash_command linter,
-- or make #find_model print the model it found!
set_option linter.hashCommand false

/-- error: Goal is not of the form `ModelWithCorners 𝕜 E H` -/
#guard_msgs in
#find_model M

/-- error: Goal is not of the form `ModelWithCorners 𝕜 E H` -/
#guard_msgs in
#find_model (ModelWithCorners 𝕜)

-- Local hypotheses (no matter if these are standard or make sense).
set_option trace.Elab.DiffGeo true in
/--
trace: [Elab.DiffGeo.FunPropM] Searching for some `ModelWithCorners 𝕜 E H`
[Elab.DiffGeo.FunPropM] Trying to solve a goal `ModelWithCorners 𝕜 E H`
[Elab.DiffGeo.MDiff] ✅️ Assumption
  [Elab.DiffGeo.MDiff] Found model: `I`
-/
#guard_msgs in
#find_model ModelWithCorners 𝕜 E H

#guard_msgs in
variable (I : ModelWithCorners 𝕜 (E × E) (H × E)) in
#find_model ModelWithCorners 𝕜 (E × E) (H × E)

#guard_msgs in
variable (I := I.prod I) in
#find_model ModelWithCorners 𝕜 (E × E) (ModelProd H H)

set_option trace.Elab.DiffGeo true in
/--
error: ⏎
---
trace: [Elab.DiffGeo.FunPropM] Searching for some `ModelWithCorners 𝕜 E →L[𝕜] E E →L[𝕜] E`
[Elab.DiffGeo.FunPropM] Trying to solve a goal `ModelWithCorners 𝕜 E →L[𝕜] E E →L[𝕜] E`
[Elab.DiffGeo.MDiff] ❌️ Assumption
  [Elab.DiffGeo.MDiff] Failed with error:
      Couldn't find a `ModelWithCorners 𝕜 E →L[𝕜] E E →L[𝕜] E` in the local context.
[Elab.DiffGeo.MDiff] ❌️ Normed space
  [Elab.DiffGeo.MDiff] Failed with error:
      elaboration function for `Manifold.«term𝓘(_,_)»` has not been implemented
        𝓘(?m✝, ?m✝¹)
-/
#guard_msgs in
#find_model ModelWithCorners 𝕜 (E →L[𝕜] E) (E →L[𝕜] E)

-- TODO: why are the error messages being swallowed?

set_option trace.Elab.DiffGeo true in
/--
error: ⏎
---
trace: [Elab.DiffGeo.FunPropM] Searching for some `ModelWithCorners 𝕜 E H'`
[Elab.DiffGeo.FunPropM] Trying to solve a goal `ModelWithCorners 𝕜 E H'`
[Elab.DiffGeo.MDiff] ❌️ Assumption
  [Elab.DiffGeo.MDiff] Failed with error:
      Couldn't find a `ModelWithCorners 𝕜 E H'` in the local context.
[Elab.DiffGeo.MDiff] ❌️ Normed space
  [Elab.DiffGeo.MDiff] Failed with error:
      `E` is a normed space, but `H'` is not defeq to it
-/
#guard_msgs in
#find_model ModelWithCorners 𝕜 E H'

-- Normed fields: TODO implement this!
/-- error: -/
#guard_msgs in
#find_model ModelWithCorners 𝕜 𝕜 𝕜

/-- error: -/
#guard_msgs in
#find_model ModelWithCorners ℝ ℝ ℝ

/-- error: -/
#guard_msgs in
#find_model ModelWithCorners ℂ ℂ ℂ

-- Euclidean space. (check the hypotheses)

-- what about products? disjoint unions? open subsets?
