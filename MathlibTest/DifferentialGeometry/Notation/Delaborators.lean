import Mathlib.Geometry.Manifold.Notation
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

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
  (f : M → M) (x : M) (s : Set M) (f' : TangentSpace I x →L[ℝ] TangentSpace I (f x))
  (v : (x : M) → TangentSpace I x)

/-- info: MDiff f : Prop -/
#guard_msgs in
#check MDifferentiable I I f

/-- info: MDiff (T% v) : Prop -/
#guard_msgs in
#check MDiff (T% v)

/-- info: MDiffAt f x : Prop -/
#guard_msgs in
#check MDiffAt f x

/-- info: MDiffAt (T% v) x : Prop -/
#guard_msgs in
#check MDiffAt (T% v) x

/-- info: MDiff[s] f : Prop -/
#guard_msgs in
#check MDifferentiableOn I I f s

/-- info: MDiff[s] (T% v) : Prop -/
#guard_msgs in
#check MDifferentiableOn I I.tangent (T% v) s

/-- info: MDiff[s] (T% v) : Prop -/
#guard_msgs in
#check MDiff[s] (T% v)

-- The partially applied form omitting `s` is not delaborated.
/-- info: MDifferentiableOn I I f : Set M → Prop -/
#guard_msgs in
#check MDifferentiableOn I I f

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

/-- info: mfderiv% (T% v) x : TangentSpace I x →L[ℝ] TangentSpace I.tangent ⟨x, v x⟩ -/
#guard_msgs in
#check mfderiv% (T% v) x

/-- info: mfderiv[s] f x : TangentSpace I x →L[ℝ] TangentSpace I (f x) -/
#guard_msgs in
#check mfderivWithin I I f s x

/-- info: mfderiv[s] f x : TangentSpace I x →L[ℝ] TangentSpace I (f x) -/
#guard_msgs in
#check mfderiv[s] f x

/-- info: ⟨x, v x⟩ : TotalSpace E (TangentSpace I) -/
#guard_msgs in
#check TotalSpace.mk' E x (v x)

/-- info: ⟨x, v x⟩ : TotalSpace E (TangentSpace I) -/
#guard_msgs in
#check TotalSpace.mk (F := E) x (v x)

/-- info: UniqueMDiff[s] : Prop -/
#guard_msgs in
#check UniqueMDiffOn I s

/-- info: UniqueMDiffAt[s] : M → Prop -/
#guard_msgs in
#check UniqueMDiffWithinAt I s

/-- info: UniqueMDiffAt[s] x : Prop -/
#guard_msgs in
#check UniqueMDiffWithinAt I s x

/-- info: UniqueMDiffAt[s] : M → Prop -/
#guard_msgs in
#check UniqueMDiffWithinAt (𝕜 := ℝ) I s

/-- info: HasMFDerivAt[s] f x f' : Prop -/
#guard_msgs in
#check HasMFDerivWithinAt I I f s x f'

/-- info: HasMFDerivAt[s] f x f' : Prop -/
#guard_msgs in
#check HasMFDerivAt[s] f x f'

/-- info: HasMFDerivAt% f x f' : Prop -/
#guard_msgs in
#check HasMFDerivAt I I f x f'

/-- info: HasMFDerivAt% f x f' : Prop -/
#guard_msgs in
#check HasMFDerivAt% f x f'

section TotalSpace

variable {𝕜 B : Type*} {E : B → Type*}

variable
  -- Let `E` be a fiber bundle with base `B` and fiber `F` (a vector space over `𝕜`)
  [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
  [NormedAddCommGroup F] [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 F] [FiberBundle F E]
  -- Moreover let `E` be a vector bundle
  [(x : B) → AddCommGroup (E x)] [(x : B) → Module 𝕜 (E x)] [VectorBundle 𝕜 F E]
  -- Let the base `B` be charted over a fixed model space `HB`
  {HB : Type*} [TopologicalSpace HB] [ChartedSpace HB B]
  -- Moreover let `HB` be modelled on a normed space `EB` so that `B` (and hence `E`) have
  -- differentiable structures
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {I : ModelWithCorners 𝕜 EB HB}

variable {f : B → 𝕜} {a : 𝕜} {s : Π x : B, E x} {u : Set B} {x₀ : B}
  {f' : TangentSpace I x₀ →L[𝕜] TangentSpace (I.prod 𝓘(𝕜, F)) (⟨x₀, s x₀⟩ : TotalSpace F E)}

/--
info: mfderiv% (T% s) : (x : B) → TangentSpace I x →L[𝕜] TangentSpace (I.prod 𝓘(𝕜, F)) ⟨x, s x⟩
-/
#guard_msgs in
#check mfderiv I (I.prod 𝓘(𝕜, F)) (T% s)

/--
info: mfderiv% (T% s) : (x : B) → TangentSpace I x →L[𝕜] TangentSpace (I.prod 𝓘(𝕜, F)) ⟨x, s x⟩
-/
#guard_msgs in
#check mfderiv% (T% s)

/-- info: mfderiv[u] (T% s) x₀ : TangentSpace I x₀ →L[𝕜] TangentSpace (I.prod 𝓘(𝕜, F)) ⟨x₀, s x₀⟩ -/
#guard_msgs in
#check mfderivWithin I (I.prod 𝓘(𝕜, F)) (T% s) u x₀

/-- info: mfderiv[u] (T% s) x₀ : TangentSpace I x₀ →L[𝕜] TangentSpace (I.prod 𝓘(𝕜, F)) ⟨x₀, s x₀⟩ -/
#guard_msgs in
#check mfderiv[u] (T% s) x₀

/-- info: MDiff (T% s) : Prop -/
#guard_msgs in
#check MDifferentiable I (I.prod 𝓘(𝕜, F)) (T% s)

/-- info: MDiff (T% s) : Prop -/
#guard_msgs in
#check MDiff (T% s)

/-- info: MDiffAt (T% s) x₀ : Prop -/
#guard_msgs in
#check MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (T% s) x₀

/-- info: MDiffAt (T% s) x₀ : Prop -/
#guard_msgs in
#check MDiffAt (T% s) x₀

/-- info: MDiff[u] (T% s) : Prop -/
#guard_msgs in
#check MDifferentiableOn I (I.prod 𝓘(𝕜, F)) (T% s) u

/-- info: MDiff[u] (T% s) : Prop -/
#guard_msgs in
#check MDiff[u] (T% s)

/-- info: MDiffAt[u] (T% s) x₀ : Prop -/
#guard_msgs in
#check MDifferentiableWithinAt I (I.prod 𝓘(𝕜, F)) (T% s) u x₀

/-- info: MDiffAt[u] (T% s) x₀ : Prop -/
#guard_msgs in
#check MDiffAt[u] (T% s) x₀

/-- info: HasMFDerivAt[u] (T% s) x₀ f' : Prop -/
#guard_msgs in
#check HasMFDerivWithinAt I (I.prod 𝓘(𝕜, F)) (T% s) u x₀ f'

/-- info: HasMFDerivAt[u] (T% s) x₀ f' : Prop -/
#guard_msgs in
#check HasMFDerivAt[u] (T% s) x₀ f'

/-- info: HasMFDerivAt% (T% s) x₀ f' : Prop -/
#guard_msgs in
#check HasMFDerivAt I (I.prod 𝓘(𝕜, F)) (T% s) x₀ f'

/-- info: HasMFDerivAt% (T% s) x₀ f' : Prop -/
#guard_msgs in
#check HasMFDerivAt% (T% s) x₀ f'

end TotalSpace

section ambiguity

variable {g : E × E → M} in
/-- info: MDiff g : Prop -/
#guard_msgs in
#check MDifferentiable 𝓘(ℝ, E × E) I g

variable {g : E × E → M} in
/-- info: MDiff g : Prop -/
#guard_msgs in
#check MDifferentiable ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) I g

-- Note: information about the model with corners is omitted even in ambiguous situations.
variable {g : E × E → E × E}
/-- info: MDiff g : Prop -/
#guard_msgs in
#check MDifferentiable 𝓘(ℝ, E × E) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) g

-- This can yield rather confusing errors
set_option pp.mvars.anonymous false in
/--
error: Tactic `apply` failed: could not unify the conclusion of `@mdifferentiable_id`
  MDiff id
with the goal
  MDiff id

Note: The full type of `@mdifferentiable_id` is
  ∀ {𝕜 : Type _} [inst : NontriviallyNormedField 𝕜] {E : Type _} [inst_1 : NormedAddCommGroup E]
    [inst_2 : NormedSpace 𝕜 E] {H : Type _} [inst_3 : TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type _}
    [inst_4 : TopologicalSpace M] [inst_5 : ChartedSpace H M], MDiff id

E : Type u_1
inst✝⁵ : NormedAddCommGroup E
inst✝⁴ : NormedSpace ℝ E
H : Type u_2
inst✝³ : TopologicalSpace H
I : ModelWithCorners ℝ E H
M : Type u_3
inst✝² : TopologicalSpace M
inst✝¹ : ChartedSpace H M
inst✝ : IsManifold I ∞ M
f : M → M
x : M
s : Set M
f' : TangentSpace I x →L[ℝ] TangentSpace I (f x)
v : (x : M) → TangentSpace I x
g✝ g : E × E → E × E
⊢ MDiff id
-/
#guard_msgs in
example {g : E × E → E × E} : MDifferentiable 𝓘(ℝ, E × E) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (@id (E × E)) := by
  apply mdifferentiable_id

-- However, hovering over the goal in the infoview shows the different models used,
-- so the information is still there (just not presented by default).

-- Disabling the use of notation also displays that two different models with corners are used.
variable {g : E × E → E × E}
/--
info: MDifferentiable (modelWithCornersSelf Real (Prod E E))
  ((modelWithCornersSelf Real E).prod (modelWithCornersSelf Real E)) g : Prop
-/
#guard_msgs in
set_option pp.notation false in
#check MDifferentiable 𝓘(ℝ, E × E) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) g

end ambiguity
