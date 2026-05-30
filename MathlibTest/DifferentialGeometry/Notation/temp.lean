import Mathlib.Geometry.Manifold.Notation
import Mathlib.Geometry.Manifold.VectorBundle.Basic

set_option pp.unicode.fun true

open Bundle Filter Function Topology
open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

section

-- Let `M` and `N` be smooth manifold. Suppose `V` is a vector bundle over `M` with model fiber `F`.
variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners 𝕜 E' H')
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (n : WithTop ℕ∞)
  (V : M → Type*) [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

-- BUG: consider a function from `N` into the total space of `V`.
-- The correct model with corners to infer on the latter is `I.prod (𝓘(𝕜, F))` --- where
-- `I` is the model with corners on the base `M` of `V`.
/-- info: mfderiv% f x : TangentSpace J x →L[𝕜] TangentSpace (I.prod 𝓘(𝕜, F)) (f x) -/
#guard_msgs in
variable {f : N → TotalSpace F V} {x : N} in
#check mfderiv J (I.prod 𝓘(𝕜, F)) f x

-- Currently, the elaborators have a bug: they always use the model on the domain `N` instead of `I`.
-- This works if `f` were a section of `V`, but is incorrect in general!
/--
error: failed to synthesize
  ChartedSpace (ModelProd H' F) (TotalSpace F V)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
variable {f : N → TotalSpace F V} {x : N} in #check mfderiv% f x
