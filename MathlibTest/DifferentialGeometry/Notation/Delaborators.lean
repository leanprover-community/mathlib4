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
