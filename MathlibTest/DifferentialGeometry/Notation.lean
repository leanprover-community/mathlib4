import Mathlib.Geometry.Manifold.Notation
import Mathlib.Geometry.Manifold.VectorBundle.Basic

set_option pp.unicode.fun true

open Bundle Filter Function Topology
open scoped Manifold

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

/-! Tests for the `T%` elaborator, inserting calls to `TotalSpace.mk'` automatically. -/
section TotalSpace

variable {σ : Π x : M, V x}
  {σ' : (x : E) → Trivial E E' x} {σ'' : (y : E) → Trivial E E' y} {s : E → E'}

/-- info: fun x ↦ TotalSpace.mk' F x (σ x) : M → TotalSpace F V -/
#guard_msgs in
#check T% σ

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

variable {x : M}

-- Testing precedence.
section precedence

/-- info: (fun x ↦ TotalSpace.mk' F x (σ x)) x : TotalSpace F V -/
#guard_msgs in
#check (T% σ) x
/-- info: (fun x ↦ TotalSpace.mk' F x (σ x)) x : TotalSpace F V -/
#guard_msgs in
#check T% σ x
-- Nothing happening, as expected.
/-- info: σ x : V x -/
#guard_msgs in
#check T% (σ x)

-- Testing precedence when applied to a family of section.
variable {ι j : Type*}

-- Partially applied.
/--
info: fun a ↦ TotalSpace.mk' ((x : M) → V x) a (s a) : ι → TotalSpace ((x : M) → V x) (Trivial ι ((x : M) → V x))
-/
#guard_msgs in
variable {s : ι → (x : M) → V x} in
#check T% s

/--
info: (fun a ↦ TotalSpace.mk' (ι → (x : M) → V x) a (s a)) i : TotalSpace (ι → (x : M) → V x) (Trivial ι (ι → (x : M) → V x))
-/
#guard_msgs in
variable {s : ι → ι → (x : M) → V x} {i : ι} in
#check T% s i

variable {X : ι → Π x : M, TangentSpace I x} {i : ι}

-- Error message is okay, but not great.
/-- error: Could not find a model with corners for ι -/
#guard_msgs in
#check MDiffAt (T% X) x

end precedence

example : (fun m ↦ (X m : TangentBundle I M)) = (fun m ↦ TotalSpace.mk' E m (X m)) := rfl

-- Applying a section to an argument. TODO: beta-reduce instead!
/-- info: (fun m ↦ TotalSpace.mk' E m (X m)) x : TotalSpace E (TangentSpace I) -/
#guard_msgs in
#check (T% X) x

-- Applying the same elaborator twice is fine (and idempotent).
/-- info: (fun m ↦ TotalSpace.mk' E m (X m)) x : TotalSpace E (TangentSpace I) -/
#guard_msgs in
#check (T% (T% X)) x

end TotalSpace

/-! Tests for the elaborators for `MDifferentiable{WithinAt,At,On}`. -/
section differentiability

variable {EM' : Type*} [NormedAddCommGroup EM']
  [NormedSpace 𝕜 EM'] {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 EM' H')
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

/-! Some basic tests: a simple function, both in applied and unapplied form -/
section basic

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

-- Testing an error message.
section

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

/--
error: Function expected at
  MDifferentiableOn I I' f s
but this term has type
  Prop

Note: Expected a function because this term is being applied to the argument
  m
-/
#guard_msgs in
#check MDifferentiableOn I I' f s m

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

end

-- Testing the precedence of parsing of the "within" set: regression test.
section

variable {ι : Type} {i : ι} {s : ι → Set M}

/-- info: MDifferentiableOn I I' f (s i) : Prop -/
#guard_msgs in
#check MDiff[s i] f
/-- info: MDifferentiableWithinAt I I' f (s i) m : Prop -/
#guard_msgs in
#check MDiffAt[s i] f m
/-- info: ContMDiffOn I I' 2 f (s i) : Prop -/
#guard_msgs in
#check CMDiff[s i] 2 f
/-- info: ContMDiffWithinAt I I' 0 f (s i) m : Prop -/
#guard_msgs in
#check CMDiffAt[s i] 0 f m
/-- info: mfderivWithin I I' f (s i) m : TangentSpace I m →L[𝕜] TangentSpace I' (f m) -/
#guard_msgs in
#check mfderiv[s i] f m

end

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

end basic

variable {σ : Π x : M, V x} {σ' : (x : E) → Trivial E E' x} {s : E → E'}
variable (X : (m : M) → TangentSpace I m) [IsManifold I 1 M]

/-! (Extended) charts -/
section

variable {φ : OpenPartialHomeomorph M H} {ψ : PartialEquiv M E}

/-- info: ContMDiff I I 37 ↑φ : Prop -/
#guard_msgs in
#check CMDiff 37 φ

/-- info: MDifferentiable I I ↑φ : Prop -/
#guard_msgs in
#check MDiff φ

/-- info: MDifferentiable I 𝓘(𝕜, E) ↑ψ : Prop -/
#guard_msgs in
#check MDiff ψ

end

/-! Error messages in case of a forgotten `T%`. -/
section

/--
error: Term X is a dependent function, of type (m : M) → TangentSpace I m
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check MDiff X

/--
error: Term σ is a dependent function, of type (x : M) → V x
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check MDiff σ

/--
error: Term σ' is a dependent function, of type (x : E) → Trivial E E' x
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check MDiff σ'

/--
error: Term σ' is a dependent function, of type (x : E) → Trivial E E' x
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check MDiff[s] σ'

/--
error: Term X is a dependent function, of type (m : M) → TangentSpace I m
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check MDiffAt (X)

/--
error: Term σ is a dependent function, of type (x : M) → V x
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check MDiffAt ((σ))

/--
error: Term σ' is a dependent function, of type (x : E) → Trivial E E' x
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check MDiff[s] σ'

/--
error: Term σ' is a dependent function, of type (x : E) → Trivial E E' x
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check MDiffAt σ'

/--
error: Term σ' is a dependent function, of type (x : E) → Trivial E E' x
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check MDiffAt[s] σ'

end

end differentiability

/-! Tests for the custom elaborators for `ContMDiff{WithinAt,At,On}` -/
section smoothness

-- Copy-pasted the tests for differentiability mutatis mutandis.
-- Start with some basic tests: a simple function, both in applied and unapplied form.
variable {EM' : Type*} [NormedAddCommGroup EM']
  [NormedSpace 𝕜 EM'] {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 EM' H')
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

-- TODO: add tests for the error message when smoothness hypotheses are missing

-- General case: a function between two manifolds.
variable {f : M → M'} {s : Set M} {m : M}

variable [IsManifold I 1 M] [IsManifold I' 1 M']

-- Testing error messages when forgetting the smoothness exponent or swapping arguments.
section error

-- yields a parse error, "unexpected token '/--'; expected term"
-- #check CMDiffAt[s] f

/--
error: Type mismatch
  f
has type
  M → M'
of sort `Type (max u_10 u_4)` but is expected to have type
  WithTop ℕ∞
of sort `Type`
---
error: Expected
  m
of type
  M
to be a function, or to be coercible to a function
-/
#guard_msgs in
#check CMDiffAt[s] f m

/--
error: Type mismatch
  f
has type
  M → M'
of sort `Type (max u_10 u_4)` but is expected to have type
  WithTop ℕ∞
of sort `Type`
---
error: Expected
  m
of type
  M
to be a function, or to be coercible to a function
-/
#guard_msgs in
#check CMDiff[s] f m

-- yields a parse error, "unexpected token '/--'; expected term"
-- #check CMDiffAt f

/--
error: Type mismatch
  f
has type
  M → M'
of sort `Type (max u_10 u_4)` but is expected to have type
  WithTop ℕ∞
of sort `Type`
---
error: Expected
  n
of type
  Option ℕ∞
to be a function, or to be coercible to a function
-/
#guard_msgs in
#check CMDiff f n

end error

/-- info: ContMDiffWithinAt I I' 1 f s : M → Prop -/
#guard_msgs in
#check CMDiffAt[s] 1 f

/-- info: ContMDiffWithinAt I I' 1 f s m : Prop -/
#guard_msgs in
#check CMDiffAt[s] 1 f m

/-- info: ContMDiffWithinAt I I' 1 f s m : Prop -/
#guard_msgs in
#check CMDiffAt[s] 1 f m

/-- info: ContMDiffAt I I' 1 f : M → Prop -/
#guard_msgs in
#check CMDiffAt 1 f

/-- info: ContMDiffAt I I' 2 f m : Prop -/
#guard_msgs in
#check CMDiffAt 2 f m

/-- info: ContMDiffOn I I' 37 f s : Prop -/
#guard_msgs in
#check CMDiff[s] 37 f

-- Testing an error message.
section

/--
error: Function expected at
  ContMDiffOn I I' 2 f s
but this term has type
  Prop

Note: Expected a function because this term is being applied to the argument
  m
-/
#guard_msgs in
#check CMDiff[s] 2 f m

variable {n : WithTop ℕ∞}
/--
error: Function expected at
  ContMDiffOn I I' n f s
but this term has type
  Prop

Note: Expected a function because this term is being applied to the argument
  m
-/
#guard_msgs in
#check ContMDiffOn I I' n f s m

/-- info: MDifferentiable I I' f : Prop -/
#guard_msgs in
#check MDiff f

/--
error: Function expected at
  ContMDiff I I' n f
but this term has type
  Prop

Note: Expected a function because this term is being applied to the argument
  m
-/
#guard_msgs in
#check CMDiff n f m

end

/-! Tests for coercions from `ℕ` or `ℕ∞` to `WithTop ℕ∞` -/
section coercions

variable {k : ℕ} {k' : ℕ∞}

/-- info: ContMDiffWithinAt I I' 0 f s : M → Prop -/
#guard_msgs in
#check CMDiffAt[s] 0 f

/-- info: ContMDiffWithinAt I I' 1 f s : M → Prop -/
#guard_msgs in
#check CMDiffAt[s] 1 f

/-- info: ContMDiffWithinAt I I' 37 f s : M → Prop -/
#guard_msgs in
#check CMDiffAt[s] 37 f

/-- info: ContMDiffWithinAt I I' (↑k) f s : M → Prop -/
#guard_msgs in
#check CMDiffAt[s] k f

/-- info: ContMDiffWithinAt I I' (↑k') f s m : Prop -/
#guard_msgs in
#check CMDiffAt[s] k' f m

/-- info: ContMDiffWithinAt I I' n f s m : Prop -/
#guard_msgs in
#check CMDiffAt[s] n f m

/-- info: ContMDiffAt I I' (↑k) f : M → Prop -/
#guard_msgs in
#check CMDiffAt k f

/-- info: ContMDiffAt I I' (↑k') f m : Prop -/
#guard_msgs in
#check CMDiffAt k' f m

/-- info: ContMDiffOn I I' (↑k) f s : Prop -/
#guard_msgs in
#check CMDiff[s] k f

/--
error: Function expected at
  ContMDiffOn I I' (↑k') f s
but this term has type
  Prop

Note: Expected a function because this term is being applied to the argument
  m
-/
#guard_msgs in
#check CMDiff[s] k' f m

/-- info: ContMDiff I I' (↑k) f : Prop -/
#guard_msgs in
#check CMDiff k f

/--
error: Function expected at
  ContMDiff I I' (↑k') f
but this term has type
  Prop

Note: Expected a function because this term is being applied to the argument
  m
-/
#guard_msgs in
#check CMDiff k' f m

end coercions

/-! Error messages for a missing `T%` elaborator. -/
section dependent

variable {σ : Π x : M, V x} {σ' : (x : E) → Trivial E E' x} {s : E → E'}
variable {ι : Type*} {i : ι} (X : (m : M) → TangentSpace I m) [IsManifold I 1 M]
  (X' : ι → (m : M) → TangentSpace I m)

/--
error: Term X is a dependent function, of type (m : M) → TangentSpace I m
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check CMDiff 0 X

/--
error: Term σ is a dependent function, of type (x : M) → V x
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check CMDiff 0 σ

/--
error: Term σ' is a dependent function, of type (x : E) → Trivial E E' x
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check CMDiff 0 σ'

/--
error: Term σ' is a dependent function, of type (x : E) → Trivial E E' x
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check CMDiff[s] 0 σ'

/--
error: Term X is a dependent function, of type (m : M) → TangentSpace I m
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check CMDiffAt 0 (X)

/--
error: Term σ is a dependent function, of type (x : M) → V x
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check CMDiffAt 0 ((σ))

/--
error: Term σ' is a dependent function, of type (x : E) → Trivial E E' x
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check CMDiff[s] 0 σ'

/--
error: Term σ' is a dependent function, of type (x : E) → Trivial E E' x
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check CMDiffAt 0 σ'

/--
error: Term σ' is a dependent function, of type (x : E) → Trivial E E' x
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check CMDiffAt[s] 0 σ'

/--
error: Term X' i is a dependent function, of type (m : M) → TangentSpace I m
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check MDiffAt ((X' i)) x

-- This error message is not great: this is missing *both* a T% elaborator
-- and an argument i.
/-- error: Could not find a model with corners for ι -/
#guard_msgs in
#check MDiffAt X' x

end dependent

-- Function from a manifold into a normed space.
variable {g : M → E}

/-- info: ContMDiffWithinAt I 𝓘(𝕜, E) 1 g s : M → Prop -/
#guard_msgs in
#check CMDiffAt[s] 1 g
/-- info: ContMDiffWithinAt I 𝓘(𝕜, E) 0 g s m : Prop -/
#guard_msgs in
#check CMDiffAt[s] 0 g m
/-- info: ContMDiffAt I 𝓘(𝕜, E) 1 g : M → Prop -/
#guard_msgs in
#check CMDiffAt 1 g
/-- info: ContMDiffAt I 𝓘(𝕜, E) 1 g m : Prop -/
#guard_msgs in
#check CMDiffAt 1 g m
/-- info: ContMDiffOn I 𝓘(𝕜, E) n g s : Prop -/
#guard_msgs in
#check CMDiff[s] n g
-- TODO: fix and enable! #check CMDiff[s] n g m
/-- info: ContMDiff I 𝓘(𝕜, E) n g : Prop -/
#guard_msgs in
#check CMDiff n g
-- TODO: fix and enable! #check CMDiff n g m

-- From a manifold into a field.
variable {h : M → 𝕜}

/-- info: ContMDiffWithinAt I 𝓘(𝕜, 𝕜) 0 h s : M → Prop -/
#guard_msgs in
#check CMDiffAt[s] 0 h
/-- info: ContMDiffWithinAt I 𝓘(𝕜, 𝕜) 1 h s m : Prop -/
#guard_msgs in
#check CMDiffAt[s] 1 h m
/-- info: ContMDiffAt I 𝓘(𝕜, 𝕜) 2 h : M → Prop -/
#guard_msgs in
#check CMDiffAt 2 h
/-- info: ContMDiffAt I 𝓘(𝕜, 𝕜) n h m : Prop -/
#guard_msgs in
#check CMDiffAt n h m
/-- info: ContMDiffOn I 𝓘(𝕜, 𝕜) n h s : Prop -/
#guard_msgs in
#check CMDiff[s] n h
-- TODO: fix and enable! #check CMDiff[s] n h m
/-- info: ContMDiff I 𝓘(𝕜, 𝕜) 37 h : Prop -/
#guard_msgs in
#check CMDiff 37 h
-- TODO: fix and enable! #check CMDiff 0 h m

-- The following tests are more spotty, as most code paths are already covered above.
-- Add further details as necessary.
-- This list mirrors some of the tests for `MDifferentiable{WithinAt,At,On}`, but not all.

-- From a normed space into a manifold.
variable {f : E → M'} {s : Set E} {x : E}
/-- info: ContMDiffWithinAt 𝓘(𝕜, E) I' 2 f s : E → Prop -/
#guard_msgs in
#check CMDiffAt[s] 2 f
/-- info: ContMDiffAt 𝓘(𝕜, E) I' 3 f x : Prop -/
#guard_msgs in
#check CMDiffAt 3 f x
-- TODO: fix and enable! #check CMDiff[s] 1 f x
/-- info: ContMDiff 𝓘(𝕜, E) I' 1 f : Prop -/
#guard_msgs in
#check CMDiff 1 f
-- TODO: should this error? if not, fix and enable! #check CMDiff 1 f x
-- same! #check MDifferentiable% f x

-- Between normed spaces.
variable {f : E → E'} {s : Set E} {x : E}

/-- info: ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E') 2 f x : Prop -/
#guard_msgs in
#check CMDiffAt 2 f x
/-- info: ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E') 2 f : E → Prop -/
#guard_msgs in
#check CMDiffAt 2 f
-- should this error or not? #check CMDiff[s] 2 f x
/-- info: ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') 2 f s : E → Prop -/
#guard_msgs in
#check CMDiffAt[s] 2 f
/-- info: ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E') 2 f s : Prop -/
#guard_msgs in
#check CMDiff[s] 2 f

end smoothness

/-! Products of models with corners: TODO, add lots of further tests -/
section

variable {EM' : Type*} [NormedAddCommGroup EM']
  [NormedSpace 𝕜 EM'] {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 EM' H')
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {f g : M → M'} {h : M → 𝕜} {h' : E → M'} {k : M × E → M'} {φ : OpenPartialHomeomorph M H}
  {f' : E → M} {g' : EM' → M'} {h' k' : F → M'}

/-- info: MDifferentiable I I' f : Prop -/
#guard_msgs in
#check MDiff f

/-- info: MDifferentiable (I.prod I) (I'.prod I') (Prod.map f g) : Prop -/
#guard_msgs in
#check MDiff (Prod.map f g)

/-- info: MDifferentiable (I.prod I) (I'.prod 𝓘(𝕜, 𝕜)) (Prod.map f h) : Prop -/
#guard_msgs in
#check MDiff (Prod.map f h)

/-- info: MDifferentiable (I.prod I) (I'.prod I) (Prod.map f ↑φ) : Prop -/
#guard_msgs in
#check MDiff (Prod.map f φ)

/-- info: MDifferentiable I (I'.prod I') fun x ↦ (f x, g x) : Prop -/
#guard_msgs in
#check MDiff (fun x ↦ (f x, g x))

/-- info: MDifferentiable (I.prod 𝓘(𝕜, E)) I' k : Prop -/
#guard_msgs in
#check MDiff k

/-- info: ContMDiff 𝓘(𝕜, E) I 2 f' : Prop -/
#guard_msgs in
#check CMDiff 2 f'

-- Several factors
/-- error: Found no model with corners on the second factor M × M -/
#guard_msgs in
#check MDiff (Prod.map f (Prod.map h g))

/-- error: Found no model with corners on first factor M × M -/
#guard_msgs in
#check MDiff (Prod.map (Prod.map f g) h)

/-- error: Found no model with corners on first factor M × M -/
#guard_msgs in
#check MDiff (Prod.map (Prod.map f g) (Prod.map h k))

/-- error: Found no model with corners on first factor (M × M) × M -/
#guard_msgs in
#check MDiff (Prod.map (Prod.map (Prod.map f g) h) k)

/-- error: Found no model with corners on the second factor M × M × M × E -/
#guard_msgs in
#check MDiff (Prod.map f (Prod.map g (Prod.map h k)))

-- Products of normed spaces: TODO this should infer 𝓘(E × F) instead!
-- and perhaps emit a warning about this!
/-- info: ContMDiff (𝓘(𝕜, E).prod 𝓘(𝕜, EM')) (I.prod I') 2 (Prod.map f' g') : Prop -/
#guard_msgs in
#check CMDiff 2 (Prod.map f' g')

/-- error: Found no model with corners on the second factor EM' × F -/
#guard_msgs in
#check CMDiff 2 (Prod.map f' (Prod.map g' h'))

/-- error: Found no model with corners on first factor E × EM' -/
#guard_msgs in
#check CMDiff 2 (Prod.map (Prod.map f' g') h')

/-- error: Found no model with corners on first factor (E × EM') × F -/
#guard_msgs in
#check MDiff (Prod.map (Prod.map (Prod.map f' g') h') k')

/-- error: Found no model with corners on first factor E × EM' -/
#guard_msgs in
#check MDiff (Prod.map (Prod.map f' g') (Prod.map h' k'))

/-- error: Found no model with corners on the second factor EM' × F × F -/
#guard_msgs in
#check MDiff (Prod.map f' (Prod.map g' (Prod.map h' k')))

  -- when having normed space, form the product all the way (not recursively)
  -- i.e., E × E × E gets model 𝓘(𝕜, E × E × E) and similarly for M × E × E × E
  -- also: (M × E) × E × E and (M × E) × (E × E); what are the correct answers here?

  -- when we take the product of two normed spaces, warn about this/print an info line!


-- TODO: add tests for a function on ModelProd H H'
end

section trace

/- Test that basic tracing works. -/

set_option trace.Elab.DiffGeo true

variable {f : Unit → Unit}

/--
error: Could not find a model with corners for Unit
---
trace: [Elab.DiffGeo.MDiff] Finding a model for: Unit
[Elab.DiffGeo.MDiff] ❌️ TotalSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      Unit is not a `Bundle.TotalSpace`.
[Elab.DiffGeo.MDiff] ❌️ TangentBundle
  [Elab.DiffGeo.MDiff] Failed with error:
      Unit is not a `TangentBundle`
[Elab.DiffGeo.MDiff] ❌️ NormedSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      Couldn't find a `NormedSpace` structure on Unit among local instances.
[Elab.DiffGeo.MDiff] ❌️ Manifold
  [Elab.DiffGeo.MDiff] found a `ChartedSpace` instance: `ChartedSpace H M`
  [Elab.DiffGeo.MDiff] Failed with error:
      Couldn't find a `ChartedSpace` structure on Unit among local instances,
      and Unit is not the charted space of some type in the local context either.
[Elab.DiffGeo.MDiff] ❌️ ContinuousLinearMap
  [Elab.DiffGeo.MDiff] Failed with error:
      Unit is not a space of continuous linear maps
[Elab.DiffGeo.MDiff] ❌️ RealInterval
  [Elab.DiffGeo.MDiff] Failed with error:
      Unit is not a coercion of a set to a type
[Elab.DiffGeo.MDiff] ❌️ UpperHalfPlane
  [Elab.DiffGeo.MDiff] Failed with error:
      Unit is not the complex upper half plane
[Elab.DiffGeo.MDiff] ❌️ NormedField
  [Elab.DiffGeo.MDiff] Failed with error:
      failed to synthesize
        NontriviallyNormedField Unit
      ⏎
      Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#check mfderiv% f

/--
info: fun a ↦ TotalSpace.mk' Unit a (f a) : Unit → TotalSpace Unit (Trivial Unit Unit)
---
trace: [Elab.DiffGeo.TotalSpaceMk] Section of a trivial bundle as a non-dependent function
-/
#guard_msgs in
#check T% f

end trace
