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
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']

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

/-- info: fun x ↦ ⟨x, σ x⟩ : M → TotalSpace F V -/
#guard_msgs in
#check T% σ

-- Note how the name of the bound variable `x` resp. `y` is preserved.
/-- info: fun x ↦ ⟨x, σ' x⟩ : E → TotalSpace E' (Trivial E E') -/
#guard_msgs in
#check T% σ'

/-- info: fun y ↦ ⟨y, σ'' y⟩ : E → TotalSpace E' (Trivial E E') -/
#guard_msgs in
#check T% σ''

/-- info: fun a ↦ ⟨a, s a⟩ : E → TotalSpace E' (Trivial E E') -/
#guard_msgs in
#check T% s

variable (X : (m : M) → TangentSpace I m) [IsManifold I 1 M]

/-- info: fun m ↦ ⟨m, X m⟩ : M → TotalSpace E (TangentSpace I) -/
#guard_msgs in
#check T% X

variable {x : M}

-- Testing precedence.
section precedence

/-- info: (fun x ↦ ⟨x, σ x⟩) x : TotalSpace F V -/
#guard_msgs in
#check (T% σ) x
/-- info: (fun x ↦ ⟨x, σ x⟩) x : TotalSpace F V -/
#guard_msgs in
#check T% σ x
-- Nothing happening, as expected.
/-- info: σ x : V x -/
#guard_msgs in
#check T% (σ x)

-- Testing precedence when applied to a family of section.
variable {ι j : Type*}

-- Partially applied.
/-- info: fun a ↦ ⟨a, s a⟩ : ι → TotalSpace ((x : M) → V x) (Trivial ι ((x : M) → V x)) -/
#guard_msgs in
variable {s : ι → (x : M) → V x} in
#check T% s

/-- info: (fun a ↦ ⟨a, s a⟩) i : TotalSpace (ι → (x : M) → V x) (Trivial ι (ι → (x : M) → V x)) -/
#guard_msgs in
variable {s : ι → ι → (x : M) → V x} {i : ι} in
#check T% s i

variable {X : ι → Π x : M, TangentSpace I x} {i : ι}

-- Error message is okay, but not great.
/--
error: Could not find a model with corners for `ι`.

Hint: failures to find a model with corners can be debugged with the command `set_option trace.Elab.DiffGeo.MDiff true`.
-/
#guard_msgs in
#check MDiffAt (T% X) x

end precedence

example : (fun m ↦ (X m : TangentBundle I M)) = (fun m ↦ TotalSpace.mk' E m (X m)) := rfl

-- Applying a section to an argument.
-- This application is not beta-reduced, because of the parentheses around the T%.
/-- info: (fun m ↦ ⟨m, X m⟩) x : TotalSpace E (TangentSpace I) -/
#guard_msgs in
#check (T% X) x

-- We apply head-beta reduction of the applied form: there is nothing to do here.
/-- info: (fun m ↦ ⟨m, X m⟩) x : TotalSpace E (TangentSpace I) -/
#guard_msgs in
#check (T% X x)

-- This variant is beta-reduced.
/-- info: (fun x ↦ ⟨x, X x⟩) x : TotalSpace E (TangentSpace I) -/
#guard_msgs in
#check (T% (fun x ↦ X x) x)

/-- info: fun m ↦ ⟨m, X m⟩ : M → TotalSpace E (TangentSpace I) -/
#guard_msgs in
#check (T% X)

-- As is this version.
/-- info: fun x ↦ ⟨x, X x⟩ : M → TotalSpace E (TangentSpace I) -/
#guard_msgs in
#check (T% (fun x ↦ X x))

-- The term `x` is outside parentheses: the form `x ↦ X x` is still reduced because
-- we apply head beta reduction to the application.
/-- info: (fun x ↦ ⟨x, X x⟩) x : TotalSpace E (TangentSpace I) -/
#guard_msgs in
#check (T% (fun x ↦ X x)) x

-- Parentheses around the argument are not required right now.
/-- info: (fun x ↦ ⟨x, X x⟩) x : TotalSpace E (TangentSpace I) -/
#guard_msgs in
#check T% (fun x ↦ X x) x

-- Applying the same elaborator twice errors.
/--
error: could not find a `FiberBundle` instance on `TotalSpace E`:
`fun m ↦ ⟨m, X m⟩` is a function into `TotalSpace E`

hint: you may be missing suitable typeclass assumptions
-/
#guard_msgs in
#check (T% (T% X))

/--
error: could not find a `FiberBundle` instance on `TotalSpace E`:
`fun m ↦ ⟨m, X m⟩` is a function into `TotalSpace E`

hint: you may be missing suitable typeclass assumptions
-/
#guard_msgs in
#check (T% (T% X)) x

section
-- Check minimal assumptions to find a model fiber.

variable {B F Z : Type*} [TopologicalSpace B] [TopologicalSpace F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] (σ : (b : B) → E b)
/-- info: fun b ↦ ⟨b, σ b⟩ : B → TotalSpace F E -/
#guard_msgs in
#check T% σ

end
-- Error message when missing typeclass assumptions for sections of a fiber bundle.
-- This used to silently do nothing; now there is a helpful error.
section

variable {B F Z : Type*} [TopologicalSpace B] [TopologicalSpace F]
  {E : B → Type*} (σ : (b : B) → E b)
/--
error: could not find a `FiberBundle` instance on `E`:
`σ` is a function into `E`

hint: you may be missing suitable typeclass assumptions
-/
#guard_msgs in
#check T% σ

/-- info: fun b ↦ ⟨b, σ b⟩ : B → TotalSpace F E -/
#guard_msgs in
variable [TopologicalSpace (TotalSpace F E)] [(b : B) → TopologicalSpace (E b)] [FiberBundle F E] in
#check T% σ

end

end TotalSpace

-- We want to capture the output of the custom *elaborators* specifically: turning off all notation
-- deactivates some notation for models with corners, but also the delaborators corresponding
-- to the elaborators.
set_option pp.notation false

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

-- A partial homeomorphism or partial equivalence.
variable {φ : OpenPartialHomeomorph M E} {ψ : PartialEquiv M E}

/-- info: MDifferentiableWithinAt I (modelWithCornersSelf 𝕜 E) (↑φ) s : M → Prop -/
#guard_msgs in
#check MDiffAt[s] φ

/-- info: MDifferentiableWithinAt I (modelWithCornersSelf 𝕜 E) (↑ψ) s : M → Prop -/
#guard_msgs in
#check MDiffAt[s] ψ

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
/--
info: mfderivWithin I I' f (s i) m : ContinuousLinearMap (RingHom.id 𝕜) (TangentSpace I m) (TangentSpace I' (f m))
-/
#guard_msgs in
#check mfderiv[s i] f m

end

-- Function from a manifold into a normed space.
variable {g : M → E}

/-- info: MDifferentiableWithinAt I (modelWithCornersSelf 𝕜 E) g s : M → Prop -/
#guard_msgs in
#check MDiffAt[s] g
/-- info: MDifferentiableWithinAt I (modelWithCornersSelf 𝕜 E) g s m : Prop -/
#guard_msgs in
#check MDiffAt[s] g m
/-- info: MDifferentiableAt I (modelWithCornersSelf 𝕜 E) g : M → Prop -/
#guard_msgs in
#check MDiffAt g
/-- info: MDifferentiableAt I (modelWithCornersSelf 𝕜 E) g m : Prop -/
#guard_msgs in
#check MDiffAt g m
/-- info: MDifferentiableOn I (modelWithCornersSelf 𝕜 E) g s : Prop -/
#guard_msgs in
#check MDiff[s] g
-- TODO: fix and enable! #check MDiff[s] g m
/-- info: MDifferentiable I (modelWithCornersSelf 𝕜 E) g : Prop -/
#guard_msgs in
#check MDiff g
-- TODO: fix and enable! #check MDiff g m

-- From a manifold into a field.
variable {h : M → 𝕜}

/-- info: MDifferentiableWithinAt I (modelWithCornersSelf 𝕜 𝕜) h s : M → Prop -/
#guard_msgs in
#check MDiffAt[s] h
/-- info: MDifferentiableWithinAt I (modelWithCornersSelf 𝕜 𝕜) h s m : Prop -/
#guard_msgs in
#check MDiffAt[s] h m
/-- info: MDifferentiableAt I (modelWithCornersSelf 𝕜 𝕜) h : M → Prop -/
#guard_msgs in
#check MDiffAt h
/-- info: MDifferentiableAt I (modelWithCornersSelf 𝕜 𝕜) h m : Prop -/
#guard_msgs in
#check MDiffAt h m
/-- info: MDifferentiableOn I (modelWithCornersSelf 𝕜 𝕜) h s : Prop -/
#guard_msgs in
#check MDiff[s] h
-- TODO: fix and enable! #check MDiff[s] h m
/-- info: MDifferentiable I (modelWithCornersSelf 𝕜 𝕜) h : Prop -/
#guard_msgs in
#check MDiff h
-- TODO: fix and enable! #check MDiff h m

-- The following tests are more spotty, as most code paths are already covered above.
-- Add further details as necessary.

-- From a normed space into a manifold.
variable {f : E → M'} {s : Set E} {x : E}
/-- info: MDifferentiableWithinAt (modelWithCornersSelf 𝕜 E) I' f s : E → Prop -/
#guard_msgs in
#check MDiffAt[s] f
/-- info: MDifferentiableAt (modelWithCornersSelf 𝕜 E) I' f x : Prop -/
#guard_msgs in
#check MDiffAt f x
-- TODO: fix and enable! #check MDiff[s] f x
/-- info: MDifferentiable (modelWithCornersSelf 𝕜 E) I' f : Prop -/
#guard_msgs in
#check MDiff f
-- TODO: should this error? if not, fix and enable! #check MDiff f x
-- same! #check MDifferentiable% f x

-- Between normed spaces.
variable {f : E → E'} {s : Set E} {x : E}

/-- info: MDifferentiableAt (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E') f x : Prop -/
#guard_msgs in
#check MDiffAt f x
/-- info: MDifferentiableAt (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E') f : E → Prop -/
#guard_msgs in
#check MDiffAt f
-- should this error or not? #check MDiff[s] f x
/--
info: MDifferentiableWithinAt (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E') f s : E → Prop
-/
#guard_msgs in
#check MDiffAt[s] f
/-- info: MDifferentiableOn (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E') f s : Prop -/
#guard_msgs in
#check MDiff[s] f


-- Normed space to a field.
variable {f : E → 𝕜} {s : Set E} {x : E}

/-- info: MDifferentiableAt (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 𝕜) f x : Prop -/
#guard_msgs in
#check MDiffAt f x

-- Field into a manifold.
variable {f : 𝕜 → M'} {u : Set 𝕜} {a : 𝕜}
/-- info: MDifferentiableAt (modelWithCornersSelf 𝕜 𝕜) I' f a : Prop -/
#guard_msgs in
#check MDiffAt f a
/-- info: MDifferentiableOn (modelWithCornersSelf 𝕜 𝕜) I' f u : Prop -/
#guard_msgs in
#check MDiff[u] f

-- Field into a normed space.
variable {f : 𝕜 → E'} {u : Set 𝕜} {a : 𝕜}
/-- info: MDifferentiableAt (modelWithCornersSelf 𝕜 𝕜) (modelWithCornersSelf 𝕜 E') f a : Prop -/
#guard_msgs in
#check MDiffAt f a
/-- info: MDifferentiableOn (modelWithCornersSelf 𝕜 𝕜) (modelWithCornersSelf 𝕜 E') f u : Prop -/
#guard_msgs in
#check MDiff[u] f

-- On a field.
variable {f : 𝕜 → 𝕜} {u : Set 𝕜} {a : 𝕜}
/-- info: MDifferentiableAt (modelWithCornersSelf 𝕜 𝕜) (modelWithCornersSelf 𝕜 𝕜) f a : Prop -/
#guard_msgs in
#check MDiffAt f a
/-- info: MDifferentiableOn (modelWithCornersSelf 𝕜 𝕜) (modelWithCornersSelf 𝕜 𝕜) f u : Prop -/
#guard_msgs in
#check MDiff[u] f

end basic

variable {σ : Π x : M, V x} {σ' : (x : E) → Trivial E E' x} {s : E → E'}
variable (X : (m : M) → TangentSpace I m) [IsManifold I 1 M]

/-! (Extended) charts -/
section

variable {φ : OpenPartialHomeomorph M H} {ψ : PartialEquiv M E} {s : Set M}

/-- info: ContMDiff I I 37 ↑φ : Prop -/
#guard_msgs in
#check CMDiff 37 φ

/-- info: MDifferentiable I I ↑φ : Prop -/
#guard_msgs in
#check MDiff φ

/-- info: MDifferentiable I (modelWithCornersSelf 𝕜 E) ↑ψ : Prop -/
#guard_msgs in
#check MDiff ψ

/-- info: MDifferentiableWithinAt I I (↑φ) s : M → Prop -/
#guard_msgs in
#check MDiffAt[s] φ

/-- info: MDifferentiableWithinAt I (modelWithCornersSelf 𝕜 E) (↑ψ) s : M → Prop -/
#guard_msgs in
#check MDiffAt[s] ψ

end

/-! Error messages in case of a forgotten `T%`. -/
section

/--
error: Term `X` is a dependent function, of type `(m : M) → TangentSpace I m`
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check MDiff X

/--
error: Term `σ` is a dependent function, of type `(x : M) → V x`
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check MDiff σ

/--
error: Term `σ'` is a dependent function, of type `(x : E) → Trivial E E' x`
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check MDiff σ'

/--
error: Term `σ'` is a dependent function, of type `(x : E) → Trivial E E' x`
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check MDiff[s] σ'

/--
error: Term `X` is a dependent function, of type `(m : M) → TangentSpace I m`
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check MDiffAt (X)

/--
error: Term `σ` is a dependent function, of type `(x : M) → V x`
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check MDiffAt ((σ))

/--
error: Term `σ'` is a dependent function, of type `(x : E) → Trivial E E' x`
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check MDiff[s] σ'

/--
error: Term `σ'` is a dependent function, of type `(x : E) → Trivial E E' x`
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check MDiffAt σ'

/--
error: Term `σ'` is a dependent function, of type `(x : E) → Trivial E E' x`
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

set_option pp.notation true

-- yields a parse error, "unexpected token '/--'; expected term"
-- TODO: make this parse, but error in the elaborator
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
error: Term `X` is a dependent function, of type `(m : M) → TangentSpace I m`
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check CMDiff 0 X

/--
error: Term `σ` is a dependent function, of type `(x : M) → V x`
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check CMDiff 0 σ

/--
error: Term `σ'` is a dependent function, of type `(x : E) → Trivial E E' x`
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check CMDiff 0 σ'

/--
error: Term `σ'` is a dependent function, of type `(x : E) → Trivial E E' x`
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check CMDiff[s] 0 σ'

/--
error: Term `X` is a dependent function, of type `(m : M) → TangentSpace I m`
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check CMDiffAt 0 (X)

/--
error: Term `σ` is a dependent function, of type `(x : M) → V x`
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check CMDiffAt 0 ((σ))

/--
error: Term `σ'` is a dependent function, of type `(x : E) → Trivial E E' x`
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check CMDiff[s] 0 σ'

/--
error: Term `σ'` is a dependent function, of type `(x : E) → Trivial E E' x`
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check CMDiffAt 0 σ'

/--
error: Term `σ'` is a dependent function, of type `(x : E) → Trivial E E' x`
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check CMDiffAt[s] 0 σ'

/--
error: Term `X' i` is a dependent function, of type `(m : M) → TangentSpace I m`
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check MDiffAt ((X' i)) x

-- This error message is not great: this is missing *both* a T% elaborator
-- and an argument i.
/--
error: Could not find a model with corners for `ι`.

Hint: failures to find a model with corners can be debugged with the command `set_option trace.Elab.DiffGeo.MDiff true`.
-/
#guard_msgs in
#check MDiffAt X' x

end dependent

-- Function from a manifold into a normed space.
variable {g : M → E}

/-- info: ContMDiffWithinAt I (modelWithCornersSelf 𝕜 E) 1 g s : M → Prop -/
#guard_msgs in
#check CMDiffAt[s] 1 g
/-- info: ContMDiffWithinAt I (modelWithCornersSelf 𝕜 E) 0 g s m : Prop -/
#guard_msgs in
#check CMDiffAt[s] 0 g m
/-- info: ContMDiffAt I (modelWithCornersSelf 𝕜 E) 1 g : M → Prop -/
#guard_msgs in
#check CMDiffAt 1 g
/-- info: ContMDiffAt I (modelWithCornersSelf 𝕜 E) 1 g m : Prop -/
#guard_msgs in
#check CMDiffAt 1 g m
/-- info: ContMDiffOn I (modelWithCornersSelf 𝕜 E) n g s : Prop -/
#guard_msgs in
#check CMDiff[s] n g
-- TODO: fix and enable! #check CMDiff[s] n g m
/-- info: ContMDiff I (modelWithCornersSelf 𝕜 E) n g : Prop -/
#guard_msgs in
#check CMDiff n g
-- TODO: fix and enable! #check CMDiff n g m

-- From a manifold into a field.
variable {h : M → 𝕜}

/-- info: ContMDiffWithinAt I (modelWithCornersSelf 𝕜 𝕜) 0 h s : M → Prop -/
#guard_msgs in
#check CMDiffAt[s] 0 h
/-- info: ContMDiffWithinAt I (modelWithCornersSelf 𝕜 𝕜) 1 h s m : Prop -/
#guard_msgs in
#check CMDiffAt[s] 1 h m
/-- info: ContMDiffAt I (modelWithCornersSelf 𝕜 𝕜) 2 h : M → Prop -/
#guard_msgs in
#check CMDiffAt 2 h
/-- info: ContMDiffAt I (modelWithCornersSelf 𝕜 𝕜) n h m : Prop -/
#guard_msgs in
#check CMDiffAt n h m
/-- info: ContMDiffOn I (modelWithCornersSelf 𝕜 𝕜) n h s : Prop -/
#guard_msgs in
#check CMDiff[s] n h
-- TODO: fix and enable! #check CMDiff[s] n h m
/-- info: ContMDiff I (modelWithCornersSelf 𝕜 𝕜) 37 h : Prop -/
#guard_msgs in
#check CMDiff 37 h
-- TODO: fix and enable! #check CMDiff 0 h m

-- The following tests are more spotty, as most code paths are already covered above.
-- Add further details as necessary.
-- This list mirrors some of the tests for `MDifferentiable{WithinAt,At,On}`, but not all.

-- From a normed space into a manifold.
variable {f : E → M'} {s : Set E} {x : E}
/-- info: ContMDiffWithinAt (modelWithCornersSelf 𝕜 E) I' 2 f s : E → Prop -/
#guard_msgs in
#check CMDiffAt[s] 2 f
/-- info: ContMDiffAt (modelWithCornersSelf 𝕜 E) I' 3 f x : Prop -/
#guard_msgs in
#check CMDiffAt 3 f x
-- TODO: fix and enable! #check CMDiff[s] 1 f x
/-- info: ContMDiff (modelWithCornersSelf 𝕜 E) I' 1 f : Prop -/
#guard_msgs in
#check CMDiff 1 f
-- TODO: should this error? if not, fix and enable! #check CMDiff 1 f x
-- same! #check MDifferentiable% f x

-- Between normed spaces.
variable {f : E → E'} {s : Set E} {x : E}

/-- info: ContMDiffAt (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E') 2 f x : Prop -/
#guard_msgs in
#check CMDiffAt 2 f x
/-- info: ContMDiffAt (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E') 2 f : E → Prop -/
#guard_msgs in
#check CMDiffAt 2 f
-- should this error or not? #check CMDiff[s] 2 f x
/--
info: ContMDiffWithinAt (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E') 2 f s : E → Prop
-/
#guard_msgs in
#check CMDiffAt[s] 2 f
/-- info: ContMDiffOn (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E') 2 f s : Prop -/
#guard_msgs in
#check CMDiff[s] 2 f

end smoothness

-- Inferring the type of `x` for all ContMDiff/MDifferentiable{Within}At elaborators.
section

variable {EM' : Type*} [NormedAddCommGroup EM']
  [NormedSpace 𝕜 EM'] {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 EM' H')
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {f : M → M'} {s : Set M}

/-- info: setOf fun x ↦ MDifferentiableAt I I' f x : Set M -/
#guard_msgs in
#check {x | MDiffAt f x}

/-- info: setOf fun x ↦ MDifferentiableWithinAt I I' f s x : Set M -/
#guard_msgs in
#check {x | MDiffAt[s] f x}

/-- info: setOf fun x ↦ ContMDiffAt I I' Top.top f x : Set M -/
#guard_msgs in
#check {x | CMDiffAt ⊤ f x}

/-- info: setOf fun x ↦ ContMDiffWithinAt I I' 2 f s x : Set M -/
#guard_msgs in
#check {x | CMDiffAt[s] 2 f x}

open ContDiff in -- for the ∞ notation
/-- info: setOf fun x ↦ ContMDiffAt I I' (↑Top.top) f x : Set M -/
#guard_msgs in
#check {x | CMDiffAt ∞ f x}

/-- info: setOf fun x ↦ Injective ⇑(mfderiv I I' f x) : Set M -/
#guard_msgs in
#check {x | Function.Injective (mfderiv% f x) }

/-- info: setOf fun x ↦ Surjective ⇑(mfderivWithin I I' f s x) : Set M -/
#guard_msgs in
#check {x | Function.Surjective (mfderiv[s] f x) }

end

/-! Products of models with corners: TODO, add lots of further tests -/
section

variable {EM' : Type*} [NormedAddCommGroup EM']
  [NormedSpace 𝕜 EM'] {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 EM' H')
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {f g : M → M'} {h h₂ : M → 𝕜} {h' : E → M'} {k k' : M × E → M'} {φ φ' : OpenPartialHomeomorph M H}
  {f' : E → M} {g' : EM' → M'} {h' k' : F → M'}

section sum

/-- info: MDifferentiable I I' (Sum.map f g) : Prop -/
#guard_msgs in
#check MDiff (Sum.map f g)

/-- info: MDifferentiable I (modelWithCornersSelf 𝕜 𝕜) (Sum.map h h₂) : Prop -/
#guard_msgs in
#check MDiff (Sum.map h h₂)

/-- info: MDifferentiable (modelWithCornersSelf 𝕜 F) I' (Sum.map h' k') : Prop -/
#guard_msgs in
#check MDiff (Sum.map h' k')

/-- info: ContMDiff I I 2 Sum.swap : Prop -/
#guard_msgs in
#check CMDiff 2 (@Sum.swap M M)

/-- info: ContMDiff I I 2 Sum.inl : Prop -/
#guard_msgs in
#check CMDiff 2 (@Sum.inl M M)

/-- info: ContMDiff I I 2 Sum.inr : Prop -/
#guard_msgs in
#check CMDiff 2 (@Sum.inr M M)

-- Error messages about mismatched models.
set_option pp.notation true in
/--
error: failed to synthesize
  ChartedSpace H (M ⊕ F)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#check MDiff (Sum.map f h')

set_option pp.notation true in
/--
error: failed to synthesize instance of type class
  ChartedSpace H (M ⊕ F)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#check MDifferentiable I I (Sum.map f h')

-- Nested sums are also supported.
/-- info: MDifferentiable I I' (Sum.map (Sum.map f f) f) : Prop -/
#guard_msgs in
#check MDiff (Sum.map (Sum.map f f) f)

/-- info: MDifferentiable I I' (Sum.map (Sum.map f (Sum.map g g)) f) : Prop -/
#guard_msgs in
#check MDiff (Sum.map (Sum.map f (Sum.map g g)) f)

-- Edge case: we don't care about the second factor.
variable {f : M → M} in
/-- info: MDifferentiable I I (Sum.map f Sum.inr) : Prop -/
#guard_msgs in
#check MDiff (Sum.map f (@Sum.inr M M))

/-- info: MDifferentiable I I' (Sum.map f (Sum.map f (Sum.map g g))) : Prop -/
#guard_msgs in
#check MDiff (Sum.map f (Sum.map f (Sum.map g g)))

end sum

section product

/-- info: MDifferentiable I I' f : Prop -/
#guard_msgs in
#check MDiff f

/-- info: MDifferentiable (I.prod I) (I'.prod I') (Prod.map f g) : Prop -/
#guard_msgs in
#check MDiff (Prod.map f g)

/-- info: MDifferentiable (I.prod I) (I'.prod (modelWithCornersSelf 𝕜 𝕜)) (Prod.map f h) : Prop -/
#guard_msgs in
#check MDiff (Prod.map f h)

/-- info: MDifferentiable (I.prod I) (I'.prod I) (Prod.map f ↑φ) : Prop -/
#guard_msgs in
#check MDiff (Prod.map f φ)

/-- info: MDifferentiable I (I'.prod I') fun x ↦ Prod.mk (f x) (g x) : Prop -/
#guard_msgs in
#check MDiff (fun x ↦ (f x, g x))

/-- info: MDifferentiable (I.prod (modelWithCornersSelf 𝕜 E)) I' k : Prop -/
#guard_msgs in
#check MDiff k

/--
error: `Prod E E` is a product of normed spaces, so there are two potential models with corners
For now, please specify the model by hand.
-/
#guard_msgs in
#check CMDiff 2 (Prod.map f' f')

/-- info: MDifferentiable (I.prod I) (I.prod I) (Prod.map ↑φ ↑φ') : Prop -/
#guard_msgs in
#check MDiff (Prod.map φ φ')

/--
info: MDifferentiable (I.prod (I.prod I)) (I'.prod ((modelWithCornersSelf 𝕜 𝕜).prod I')) (Prod.map f (Prod.map h g)) : Prop
-/
#guard_msgs in
#check MDiff (Prod.map f (Prod.map h g))

/--
info: MDifferentiable ((I.prod I).prod I) ((I'.prod I').prod (modelWithCornersSelf 𝕜 𝕜)) (Prod.map (Prod.map f g) h) : Prop
-/
#guard_msgs in
#check MDiff (Prod.map (Prod.map f g) h)

/--
info: MDifferentiable ((I.prod I).prod (I.prod (I.prod (modelWithCornersSelf 𝕜 E))))
  ((I'.prod I').prod ((modelWithCornersSelf 𝕜 𝕜).prod I')) (Prod.map (Prod.map f g) (Prod.map h k)) : Prop
-/
#guard_msgs in
#check MDiff (Prod.map (Prod.map f g) (Prod.map h k))

/--
info: MDifferentiable (((I.prod I).prod I).prod (I.prod (modelWithCornersSelf 𝕜 E)))
  (((I'.prod I').prod (modelWithCornersSelf 𝕜 𝕜)).prod I') (Prod.map (Prod.map (Prod.map f g) h) k) : Prop
-/
#guard_msgs in
#check MDiff (Prod.map (Prod.map (Prod.map f g) h) k)

/--
info: MDifferentiable (I.prod (I.prod (I.prod (I.prod (modelWithCornersSelf 𝕜 E)))))
  (I'.prod (I'.prod ((modelWithCornersSelf 𝕜 𝕜).prod I'))) (Prod.map f (Prod.map g (Prod.map h k))) : Prop
-/
#guard_msgs in
#check MDiff (Prod.map f (Prod.map g (Prod.map h k)))

section

set_option pp.notation true -- only testing error messages, so nice notation is helpful

/--
error: `EM' × F` is a product of normed spaces, so there are two potential models with corners
For now, please specify the model by hand.
-/
#guard_msgs in
#check CMDiff 2 (Prod.map f' (Prod.map g' h'))

/--
error: `E × EM'` is a product of normed spaces, so there are two potential models with corners
For now, please specify the model by hand.
-/
#guard_msgs in
#check CMDiff 2 (Prod.map (Prod.map f' g') h')

/--
error: `E × EM'` is a product of normed spaces, so there are two potential models with corners
For now, please specify the model by hand.
-/
#guard_msgs in
#check MDiff (Prod.map (Prod.map (Prod.map f' g') h') k')

/--
error: `E × EM'` is a product of normed spaces, so there are two potential models with corners
For now, please specify the model by hand.
-/
#guard_msgs in
#check MDiff (Prod.map (Prod.map f' g') (Prod.map h' k'))

/--
error: `F × F` is a product of normed spaces, so there are two potential models with corners
For now, please specify the model by hand.
-/
#guard_msgs in
#check MDiff (Prod.map f' (Prod.map g' (Prod.map h' k')))

end

variable {f' : E → M} {g' : E' → M'} {h' : F → 𝕜}

/--
error: `Prod E E'` is a product of normed spaces, so there are two potential models with corners
For now, please specify the model by hand.
-/
#guard_msgs in
#check MDiff (Prod.map (Prod.map f' g') h') -- domain E × E' × F

/--
error: `Prod E E'` is a product of normed spaces, so there are two potential models with corners
For now, please specify the model by hand.
-/
#guard_msgs in
#check MDiff (Prod.map (Prod.map f' g') f) -- domain E × E' × M = (E × E') × M

/--
info: MDifferentiable ((modelWithCornersSelf 𝕜 E).prod ((modelWithCornersSelf 𝕜 E).prod I)) (I.prod (I.prod I'))
  (Prod.map f' (Prod.map f' f)) : Prop
-/
#guard_msgs in
#check MDiff (Prod.map f' (Prod.map f' f)) -- domain E × (E' × M)

/--
info: MDifferentiable (I.prod ((modelWithCornersSelf 𝕜 E).prod I)) (I'.prod (I.prod I')) (Prod.map f (Prod.map f' f)) : Prop
-/
#guard_msgs in
#check MDiff (Prod.map f (Prod.map f' f)) -- domain M × (E × M)

/--
error: `Prod E F` is a product of normed spaces, so there are two potential models with corners
For now, please specify the model by hand.
-/
#guard_msgs in
#check MDiff (Prod.map f (Prod.map f' h')) -- domain M × (E × F)

/--
info: MDifferentiable ((I.prod (modelWithCornersSelf 𝕜 E)).prod (modelWithCornersSelf 𝕜 F))
  ((I'.prod I).prod (modelWithCornersSelf 𝕜 𝕜)) (Prod.map (Prod.map f f') h') : Prop
-/
#guard_msgs in
#check MDiff (Prod.map (Prod.map f f') h') -- domain (M × E) × F

/--
info: MDifferentiable (((modelWithCornersSelf 𝕜 E).prod I).prod (modelWithCornersSelf 𝕜 F))
  ((I.prod I').prod (modelWithCornersSelf 𝕜 𝕜)) (Prod.map (Prod.map f' f) h') : Prop
-/
#guard_msgs in
#check MDiff (Prod.map (Prod.map f' f) h') -- domain (E × M) × F

end product

-- Combining sums and products.

variable {f : M → M'} {g : M' → M} {f' g' : E → M} {h' : F → E}

/--
info: MDifferentiable (I'.prod (I.prod I)) (I.prod (I'.prod I')) (Prod.map g (Prod.map f f)) : Prop
-/
#guard_msgs in
#check MDiff (Prod.map g (Prod.map f f))
-- domain M' × (M ⊕ M)

/--
info: MDifferentiable ((modelWithCornersSelf 𝕜 E).prod ((modelWithCornersSelf 𝕜 E).prod I)) (I.prod (I.prod I'))
  (Prod.map f' (Prod.map (Sum.map f' g') f)) : Prop
-/
#guard_msgs in
#check MDiff (Prod.map f' (Prod.map (Sum.map f' g') f)) -- domain E × (E ⊕ E) × M

/--
info: MDifferentiable ((modelWithCornersSelf 𝕜 E).prod I) (I.prod I') (Prod.map (Sum.map f' f') (Sum.map f f)) : Prop
-/
#guard_msgs in
#check MDiff (Prod.map (Sum.map f' f') (Sum.map f f)) -- domain (M ⊕ M) × (E ⊕ E)

/--
info: MDifferentiable (I.prod (modelWithCornersSelf 𝕜 E)) (I'.prod I) (Prod.map (Sum.map f f) (Sum.map f' g')) : Prop
-/
#guard_msgs in
#check MDiff (Prod.map (Sum.map f f) (Sum.map f' g'))

/--
info: MDifferentiable (I.prod (modelWithCornersSelf 𝕜 E)) (I'.prod I)
  (Sum.map (Prod.map (Sum.map f f) (Sum.map f' g')) (Prod.map (Sum.map f f) (Sum.map f' g'))) : Prop
-/
#guard_msgs in
#check MDiff (Sum.map (Prod.map (Sum.map f f) (Sum.map f' g')) (Prod.map (Sum.map f f) (Sum.map f' g'))) -- domain: (M ⊕ M) × (E ⊕ E) ⊕ (M ⊕ M) × (E ⊕ E)

section opens

open TopologicalSpace

variable {s : Opens M} {t : Opens E} {u : Opens M'}

variable {f : s → M'} in
/-- info: MDifferentiable I I' f : Prop -/
#guard_msgs in
#check MDiff f

variable {f : s → u} in
/-- info: MDifferentiable I I' f : Prop -/
#guard_msgs in
#check MDiff f

variable {f : u → M × E} in
/-- info: MDifferentiable I' (I.prod (modelWithCornersSelf 𝕜 E)) f : Prop -/
#guard_msgs in
#check MDiff f

variable {s : Opens (M × E)} {f : s → M × E} in
/--
info: MDifferentiable (I.prod (modelWithCornersSelf 𝕜 E)) (I.prod (modelWithCornersSelf 𝕜 E)) f : Prop
-/
#guard_msgs in
#check MDiff f

variable {s : Opens (M ⊕ M)} {f : s → (M × E) ⊕ (M × E)} in
/-- info: MDifferentiable I (I.prod (modelWithCornersSelf 𝕜 E)) f : Prop -/
#guard_msgs in
#check MDiff f

variable {s : Opens (M ⊕ M)} {f : s → 𝕜 × E}
/-- info: MDifferentiable I ((modelWithCornersSelf 𝕜 𝕜).prod (modelWithCornersSelf 𝕜 E)) f : Prop -/
#guard_msgs in
#check MDiff f

end opens

/-- info: MDifferentiable (I.prod (modelWithCornersSelf 𝕜 E)) I' (Sum.map k k) : Prop -/
#guard_msgs in
#check MDiff (Sum.map k k)

end

section trace

/- Test that basic tracing works. -/

set_option trace.Elab.DiffGeo true

variable {f : Unit → Unit}

/--
error: Could not find a model with corners for `Unit`.
---
trace: [Elab.DiffGeo.MDiff] Finding a model with corners for: `Unit`
[Elab.DiffGeo.MDiff] 💥️ TotalSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      `Unit` is not a `Bundle.TotalSpace`.
[Elab.DiffGeo.MDiff] 💥️ TangentBundle
  [Elab.DiffGeo.MDiff] Failed with error:
      `Unit` is not a `TangentBundle`
[Elab.DiffGeo.MDiff] 💥️ NormedSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      Couldn't find a `NormedSpace` structure on `Unit` among local instances.
[Elab.DiffGeo.MDiff] 💥️ Manifold
  [Elab.DiffGeo.MDiff] considering instance of type `ChartedSpace H M`
  [Elab.DiffGeo.MDiff] Failed with error:
      Couldn't find a `ChartedSpace` structure on `Unit` among local instances, and `Unit` is not the charted space of some type in the local context either.
[Elab.DiffGeo.MDiff] 💥️ ContinuousLinearMap
  [Elab.DiffGeo.MDiff] Failed with error:
      `Unit` is not a space of continuous linear maps
[Elab.DiffGeo.MDiff] 💥️ RealInterval
  [Elab.DiffGeo.MDiff] Failed with error:
      `Unit` is not a coercion of a set to a type
[Elab.DiffGeo.MDiff] 💥️ EuclideanSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      `Unit` is not a Euclidean space, half-space or quadrant
[Elab.DiffGeo.MDiff] 💥️ UpperHalfPlane
  [Elab.DiffGeo.MDiff] Failed with error:
      `Unit` is not the complex upper half plane
[Elab.DiffGeo.MDiff] 💥️ Units of algebra
  [Elab.DiffGeo.MDiff] Failed with error:
      `Unit` is not a set of units, in particular not of a complete normed algebra
[Elab.DiffGeo.MDiff] 💥️ Complex unit circle
  [Elab.DiffGeo.MDiff] Failed with error:
      `Unit` is not the complex unit circle
[Elab.DiffGeo.MDiff] 💥️ Sphere
  [Elab.DiffGeo.MDiff] Failed with error:
      `Unit` is not a coercion of a set to a type
[Elab.DiffGeo.MDiff] 💥️ NormedField
  [Elab.DiffGeo.MDiff] Failed with error:
      failed to synthesize instance of type class
        NontriviallyNormedField Unit
      ⏎
      Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
[Elab.DiffGeo.MDiff] 💥️ InnerProductSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      Couldn't find an `InnerProductSpace` structure on `Unit` among local instances.
-/
#guard_msgs in
#check mfderiv% f

set_option pp.notation true in
/--
info: fun a ↦ ⟨a, f a⟩ : Unit → TotalSpace Unit (Trivial Unit Unit)
---
trace: [Elab.DiffGeo.TotalSpaceMk] Section of a trivial bundle as a non-dependent function
-/
#guard_msgs in
#check T% f

end trace
