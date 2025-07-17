import Mathlib.Geometry.Manifold.Elaborators

import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorField.LieBracket

set_option pp.unicode.fun true

open Bundle Filter Function Topology

open scoped Bundle Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

section

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  -- `F` model fiber
  (n : WithTop ℕ∞)
  (V : M → Type*) [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  -- `V` vector bundle

-- Tests for the T% elaborator, inserting calls to TotalSpace.mk' automatically.
section TotalSpace

variable {σ : Π x : M, V x}
  {σ' : (x : E) → Trivial E E' x} {σ'' : (y : E) → Trivial E E' y} {s : E → E'}

/-- info: fun x ↦ TotalSpace.mk' F x (σ x) : M → TotalSpace F V -/
#guard_msgs in
#check T% σ

set_option linter.style.commandStart true

-- TODO: investigate this!
/--
error: Application type mismatch: In the application
  MDifferentiableWithinAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (σ x)) Set.univ
the argument
  Set.univ
has type
  Set.{?u.13540} ?m.13541 : Type ?u.13540
but is expected to have type
  Set.{u_4} M : Type u_4
-/
#guard_msgs in
example {x : M} : MDiffAt[Set.univ] (T% σ) x := sorry

-- Interaction with auto-implicits.
/--
error: Application type mismatch: In the application
  MDifferentiableWithinAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (σ x)) Set.univ
the argument
  Set.univ
has type
  Set.{?u.17364} ?m.17365 : Type ?u.17364
but is expected to have type
  Set.{u_4} M : Type u_4
-/
#guard_msgs in
set_option autoImplicit true in
example : MDiffAt[Set.univ] (T% σ) x := sorry

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
example {x : M} : MDiffAt[(Set.univ : Set M)] (T% σ) x := sorry

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
example {u : Set M} {x : M} : CMDiffAt[u] 2 (T% σ) x := sorry

-- Note how the name of the bound variable `x` resp. `y` is preserved.
/-- info: fun x ↦ TotalSpace.mk' E' x (σ' x) : E → TotalSpace E' (Trivial E E') -/
#guard_msgs in
#check T% σ'

/-- info: fun y ↦ TotalSpace.mk' E' y (σ'' y) : E → TotalSpace E' (Trivial E E') -/
#guard_msgs in
#check T% σ''

/-- info: fun a ↦ TotalSpace.mk' E' a (s a) : E → TotalSpace E' (Trivial E E') -/
#guard_msgs in
#check T% s

variable (X : (m : M) → TangentSpace I m) [IsManifold I 1 M]

/-- info: fun m ↦ TotalSpace.mk' E m (X m) : M → TotalSpace E (TangentSpace I) -/
#guard_msgs in
#check T% X

example : (fun m ↦ (X m : TangentBundle I M)) = (fun m ↦ TotalSpace.mk' E m (X m)) := rfl

end TotalSpace

-- Elaborators for MDifferentiable{WithinAt,At,On}.
section differentiability

-- Start with some basic tests: a simple function, both in applied and unapplied form.
variable {EM' : Type*} [NormedAddCommGroup EM']
  [NormedSpace 𝕜 EM'] {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 EM' H')
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

-- General case: a function between two manifolds.
variable {f : M → M'} {s : Set M} {m : M}

/-- info: MDifferentiableWithinAt I I' f s : M → Prop -/
#guard_msgs in
#check MDiffAt[s] f

/-- info: MDifferentiableWithinAt I I' f s m : Prop -/
#guard_msgs in
#check MDiffAt[s] f m

/-- info: MDifferentiableAt I I' f : M → Prop -/
#guard_msgs in
#check MDiffAt f

/-- info: MDifferentiableAt I I' f m : Prop -/
#guard_msgs in
#check MDiffAt f m

/-- info: MDifferentiableOn I I' f s : Prop -/
#guard_msgs in
#check MDiff[s] f

-- XXX: is this expected behaviour or should it be a bug?
/--
error: Function expected at
  MDifferentiableOn I I' f s
but this term has type
  Prop

Note: Expected a function because this term is being applied to the argument
  m
-/
#guard_msgs in
#check MDiff[s] f m

/-- info: MDifferentiable I I' f : Prop -/
#guard_msgs in
#check MDiff f

/--
error: Function expected at
  MDifferentiable I I' f
but this term has type
  Prop

Note: Expected a function because this term is being applied to the argument
  m
-/
#guard_msgs in
#check MDiff f m

-- Function from a manifold into a normed space.
variable {g : M → E}

/-- info: MDifferentiableWithinAt I 𝓘(𝕜, E) g s : M → Prop -/
#guard_msgs in
#check MDiffAt[s] g
/-- info: MDifferentiableWithinAt I 𝓘(𝕜, E) g s m : Prop -/
#guard_msgs in
#check MDiffAt[s] g m
/-- info: MDifferentiableAt I 𝓘(𝕜, E) g : M → Prop -/
#guard_msgs in
#check MDiffAt g
/-- info: MDifferentiableAt I 𝓘(𝕜, E) g m : Prop -/
#guard_msgs in
#check MDiffAt g m
/-- info: MDifferentiableOn I 𝓘(𝕜, E) g s : Prop -/
#guard_msgs in
#check MDiff[s] g
-- TODO: fix and enable! #check MDiff[s] g m
/-- info: MDifferentiable I 𝓘(𝕜, E) g : Prop -/
#guard_msgs in
#check MDiff g
-- TODO: fix and enable! #check MDiff g m

-- From a manifold into a field.
variable {h : M → 𝕜}

/-- info: MDifferentiableWithinAt I 𝓘(𝕜, 𝕜) h s : M → Prop -/
#guard_msgs in
#check MDiffAt[s] h
/-- info: MDifferentiableWithinAt I 𝓘(𝕜, 𝕜) h s m : Prop -/
#guard_msgs in
#check MDiffAt[s] h m
/-- info: MDifferentiableAt I 𝓘(𝕜, 𝕜) h : M → Prop -/
#guard_msgs in
#check MDiffAt h
/-- info: MDifferentiableAt I 𝓘(𝕜, 𝕜) h m : Prop -/
#guard_msgs in
#check MDiffAt h m
/-- info: MDifferentiableOn I 𝓘(𝕜, 𝕜) h s : Prop -/
#guard_msgs in
#check MDiff[s] h
-- TODO: fix and enable! #check MDiff[s] h m
/-- info: MDifferentiable I 𝓘(𝕜, 𝕜) h : Prop -/
#guard_msgs in
#check MDiff h
-- TODO: fix and enable! #check MDiff h m

-- The following tests are more spotty, as most code paths are already covered above.
-- Add further details as necessary.

-- From a normed space into a manifold.
variable {f : E → M'} {s : Set E} {x : E}
/-- info: MDifferentiableWithinAt 𝓘(𝕜, E) I' f s : E → Prop -/
#guard_msgs in
#check MDiffAt[s] f
/-- info: MDifferentiableAt 𝓘(𝕜, E) I' f x : Prop -/
#guard_msgs in
#check MDiffAt f x
-- TODO: fix and enable! #check MDiff[s] f x
/-- info: MDifferentiable 𝓘(𝕜, E) I' f : Prop -/
#guard_msgs in
#check MDiff f
-- TODO: should this error? if not, fix and enable! #check MDiff f x
-- same! #check MDifferentiable% f x

-- Between normed spaces.
variable {f : E → E'} {s : Set E} {x : E}

/-- info: MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x : Prop -/
#guard_msgs in
#check MDiffAt f x
/-- info: MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, E') f : E → Prop -/
#guard_msgs in
#check MDiffAt f
-- should this error or not? #check MDiff[s] f x
/-- info: MDifferentiableWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s : E → Prop -/
#guard_msgs in
#check MDiffAt[s] f
/-- info: MDifferentiableOn 𝓘(𝕜, E) 𝓘(𝕜, E') f s : Prop -/
#guard_msgs in
#check MDiff[s] f


-- Normed space to a field.
variable {f : E → 𝕜} {s : Set E} {x : E}

/-- info: MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, 𝕜) f x : Prop -/
#guard_msgs in
#check MDiffAt f x

-- Field into a manifold.
variable {f : 𝕜 → M'} {u : Set 𝕜} {a : 𝕜}
/-- info: MDifferentiableAt 𝓘(𝕜, 𝕜) I' f a : Prop -/
#guard_msgs in
#check MDiffAt f a
/-- info: MDifferentiableOn 𝓘(𝕜, 𝕜) I' f u : Prop -/
#guard_msgs in
#check MDiff[u] f

-- Field into a normed space.
variable {f : 𝕜 → E'} {u : Set 𝕜} {a : 𝕜}
/-- info: MDifferentiableAt 𝓘(𝕜, 𝕜) 𝓘(𝕜, E') f a : Prop -/
#guard_msgs in
#check MDiffAt f a
/-- info: MDifferentiableOn 𝓘(𝕜, 𝕜) 𝓘(𝕜, E') f u : Prop -/
#guard_msgs in
#check MDiff[u] f

-- On a field.
variable {f : 𝕜 → 𝕜} {u : Set 𝕜} {a : 𝕜}
/-- info: MDifferentiableAt 𝓘(𝕜, 𝕜) 𝓘(𝕜, 𝕜) f a : Prop -/
#guard_msgs in
#check MDiffAt f a
/-- info: MDifferentiableOn 𝓘(𝕜, 𝕜) 𝓘(𝕜, 𝕜) f u : Prop -/
#guard_msgs in
#check MDiff[u] f

-- This elaborator can be combined with the total space elaborator.
-- XXX: these tests might be incomplete; extend as needed!

variable {σ : Π x : M, V x} {σ' : (x : E) → Trivial E E' x} {s : E → E'}
variable (X : (m : M) → TangentSpace I m) [IsManifold I 1 M]

/-- info: MDifferentiableAt I (I.prod 𝓘(𝕜, E)) fun m ↦ TotalSpace.mk' E m (X m) : M → Prop -/
#guard_msgs in
#check MDiffAt (T% X)

/-- info: MDifferentiableAt I (I.prod 𝓘(𝕜, F)) fun x ↦ TotalSpace.mk' F x (σ x) : M → Prop -/
#guard_msgs in
#check MDiffAt (T% σ)

/--
info: MDifferentiableAt 𝓘(𝕜, E) (𝓘(𝕜, E).prod 𝓘(𝕜, E')) fun x ↦ TotalSpace.mk' E' x (σ' x) : E → Prop
-/
#guard_msgs in
#check MDiffAt (T% σ')

/--
info: MDifferentiableAt 𝓘(𝕜, E) (𝓘(𝕜, E).prod 𝓘(𝕜, E')) fun a ↦ TotalSpace.mk' E' a (s a) : E → Prop
-/
#guard_msgs in
#check MDifferentiableAt% (T% s)
/-- info: MDifferentiableAt I (I.prod 𝓘(𝕜, E)) (fun m ↦ TotalSpace.mk' E m (X m)) m : Prop -/
#guard_msgs in
#check MDifferentiableAt% (T% X) m

/-- info: MDifferentiableAt I (I.prod 𝓘(𝕜, E)) fun m ↦ TotalSpace.mk' E m (X m) : M → Prop -/
#guard_msgs in
#check MDifferentiableAt% (T% X)

/-- info: MDifferentiableAt I (I.prod 𝓘(𝕜, E)) (fun m ↦ TotalSpace.mk' E m (X m)) m : Prop -/
#guard_msgs in
#check MDifferentiableAt% (T% X) m

/-- info: MDifferentiableAt I (I.prod 𝓘(𝕜, F)) fun x ↦ TotalSpace.mk' F x (σ x) : M → Prop -/
#guard_msgs in
#check MDifferentiableAt% (T% σ)

/--
info: MDifferentiableAt 𝓘(𝕜, E) (𝓘(𝕜, E).prod 𝓘(𝕜, E')) fun x ↦ TotalSpace.mk' E' x (σ' x) : E → Prop
-/
#guard_msgs in
#check MDifferentiableAt% (T% σ')

/--
info: MDifferentiableAt 𝓘(𝕜, E) (𝓘(𝕜, E).prod 𝓘(𝕜, E')) fun a ↦ TotalSpace.mk' E' a (s a) : E → Prop
-/
#guard_msgs in
#check MDifferentiableAt% (T% s)

end differentiability

section mfderiv

variable {EM' : Type*} [NormedAddCommGroup EM']
  [NormedSpace 𝕜 EM'] {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 EM' H')
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

variable {f : M → M'} {s : Set M} {m : M}

/-- info: mfderiv I I' f : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I' (f x) -/
#guard_msgs in
#check mfderiv% f

/-- info: mfderiv I I' f m : TangentSpace I m →L[𝕜] TangentSpace I' (f m) -/
#guard_msgs in
#check mfderiv% f m

/-- info: mfderivWithin I I' f s : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I' (f x) -/
#guard_msgs in
#check mfderiv[s] f

/-- info: mfderivWithin I I' f s m : TangentSpace I m →L[𝕜] TangentSpace I' (f m) -/
#guard_msgs in
#check mfderiv[s] f m

variable {f : E → EM'} {s : Set E} {m : E}

/--
info: mfderiv 𝓘(𝕜, E) 𝓘(𝕜, EM') f : (x : E) → TangentSpace 𝓘(𝕜, E) x →L[𝕜] TangentSpace 𝓘(𝕜, EM') (f x)
-/
#guard_msgs in
#check mfderiv% f

/--
info: mfderiv 𝓘(𝕜, E) 𝓘(𝕜, EM') f m : TangentSpace 𝓘(𝕜, E) m →L[𝕜] TangentSpace 𝓘(𝕜, EM') (f m)
-/
#guard_msgs in
#check mfderiv% f m

/--
info: mfderivWithin 𝓘(𝕜, E) 𝓘(𝕜, EM') f s : (x : E) → TangentSpace 𝓘(𝕜, E) x →L[𝕜] TangentSpace 𝓘(𝕜, EM') (f x)
-/
#guard_msgs in
#check mfderiv[s] f

/--
info: mfderivWithin 𝓘(𝕜, E) 𝓘(𝕜, EM') f s m : TangentSpace 𝓘(𝕜, E) m →L[𝕜] TangentSpace 𝓘(𝕜, EM') (f m)
-/
#guard_msgs in
#check mfderiv[s] f m

section errors

-- Test an error message, about mismatched types.
variable {s' : Set M} {m' : M}

/--
error: Application type mismatch: In the application
  mfderiv 𝓘(𝕜, E) 𝓘(𝕜, EM') f m'
the argument
  m'
has type
  M : Type u_4
but is expected to have type
  E : Type u_2
---
info: mfderiv 𝓘(𝕜, E) 𝓘(𝕜, EM') f sorry : TangentSpace 𝓘(𝕜, E) sorry →L[𝕜] TangentSpace 𝓘(𝕜, EM') (f sorry)
-/
#guard_msgs in
#check mfderiv% f m'

-- Error messages: argument s has mismatched type.
/--
error: Application type mismatch: In the application
  mfderivWithin 𝓘(𝕜, E) 𝓘(𝕜, EM') f s'
the argument
  s'
has type
  Set.{u_4} M : Type u_4
but is expected to have type
  Set.{u_2} E : Type u_2
-/
#guard_msgs in
#check mfderiv[s'] f

/--
error: Application type mismatch: In the application
  mfderivWithin 𝓘(𝕜, E) 𝓘(𝕜, EM') f s'
the argument
  s'
has type
  Set.{u_4} M : Type u_4
but is expected to have type
  Set.{u_2} E : Type u_2
-/
#guard_msgs in
#check mfderiv[s'] f m

end errors

end mfderiv
