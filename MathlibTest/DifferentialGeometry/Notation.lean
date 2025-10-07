import Mathlib.Geometry.Manifold.Notation
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
/-- error: Could not find a model with corners for `ι` -/
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

-- A partial homeomorphism or partial equivalence.
variable {φ : OpenPartialHomeomorph M E} {ψ : PartialEquiv M E}

#check MDifferentiableWithinAt I 𝓘(𝕜, E) ψ
#check MDifferentiableWithinAt I 𝓘(𝕜, E) ψ s
/--
error: Application type mismatch: The argument
  M
has type
  Type u_4
but is expected to have type
  ModelWithCorners ?𝕜 ?E ?H
in the application
  @MDifferentiableWithinAt ?𝕜 ?inst✝ ?E ?inst✝¹ ?inst✝² ?H ?inst✝³ M
-/
#guard_msgs in
#check MDiffAt[s] φ
/--
error: Expected
  ψ
of type
  PartialEquiv M E
to be a function
-/
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

/-! A partial homeomorphism or partial equivalence. More generally, this works for any type
with a coercion to (possibly dependent) functions. -/
section coercion

variable {s : Set M} {m : M}

variable {φ : OpenPartialHomeomorph M E} {ψ : PartialEquiv M E}

/-- info: MDifferentiableWithinAt I 𝓘(𝕜, E) (↑φ) s : M → Prop -/
#guard_msgs in
#check MDiffAt[s] φ

/-- info: MDifferentiableWithinAt I 𝓘(𝕜, E) (↑ψ) s : M → Prop -/
#guard_msgs in
#check MDiffAt[s] ψ

/-- info: MDifferentiableAt I 𝓘(𝕜, E) ↑φ : M → Prop -/
#guard_msgs in
#check MDiffAt φ

/-- info: MDifferentiableAt I 𝓘(𝕜, E) ↑ψ : M → Prop -/
#guard_msgs in
#check MDiffAt ψ

/-- info: MDifferentiableOn I 𝓘(𝕜, E) (↑φ) s : Prop -/
#guard_msgs in
#check MDiff[s] φ

/-- info: MDifferentiableOn I 𝓘(𝕜, E) (↑ψ) s : Prop -/
#guard_msgs in
#check MDiff[s] ψ

/-- info: MDifferentiable I 𝓘(𝕜, E) ↑φ : Prop -/
#guard_msgs in
#check MDiff φ

/-- info: ContMDiffWithinAt I 𝓘(𝕜, E) 2 (↑ψ) s : M → Prop -/
#guard_msgs in
#check CMDiffAt[s] 2 ψ

/-- info: ContMDiffOn I 𝓘(𝕜, E) 2 (↑φ) s : Prop -/
#guard_msgs in
#check CMDiff[s] 2 φ

/-- info: ContMDiffAt I 𝓘(𝕜, E) 2 ↑φ : M → Prop -/
#guard_msgs in
#check CMDiffAt 2 φ

/-- info: ContMDiff I 𝓘(𝕜, E) 2 ↑ψ : Prop -/
#guard_msgs in
#check CMDiff 2 ψ

/-- info: mfderiv I 𝓘(𝕜, E) ↑φ : (x : M) → TangentSpace I x →L[𝕜] TangentSpace 𝓘(𝕜, E) (↑φ x) -/
#guard_msgs in
#check mfderiv% φ

/--
info: mfderivWithin I 𝓘(𝕜, E) (↑ψ) s : (x : M) → TangentSpace I x →L[𝕜] TangentSpace 𝓘(𝕜, E) (↑ψ x)
-/
#guard_msgs in
#check mfderiv[s] ψ

/--
info: mfderivWithin I 𝓘(𝕜, E) (↑ψ) s : (x : M) → TangentSpace I x →L[𝕜] TangentSpace 𝓘(𝕜, E) (↑ψ x)
-/
#guard_msgs in
variable {f : ContMDiffSection I F n V} in
#check mfderiv[s] ψ

/-- info: mfderiv I I' ⇑g : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I' (g x) -/
#guard_msgs in
variable {g : ContMDiffMap I I' M M' n} in
#check mfderiv% g

-- An example of "any type" which coerces to functions.
/-- info: mfderiv I I' ⇑g : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I' (g x) -/
#guard_msgs in
variable {g : Equiv M M'} in
#check mfderiv% g

end coercion

variable {σ : Π x : M, V x} {σ' : (x : E) → Trivial E E' x} {s : E → E'}
variable (X : (m : M) → TangentSpace I m) [IsManifold I 1 M]

/-! These elaborators can be combined with the total space elaborator. -/
section interaction

-- Note: these tests might be incomplete; extend as needed!

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

end interaction

-- Total space over the tangent space and tangent bundle.
section

variable [IsManifold I 2 M]

variable {h : Bundle.TotalSpace F (TangentSpace I : M → Type _) → F} {h' : TangentBundle I M → F}

-- Test the inference of a model with corners on a trivial bundle over the tangent space of a
-- manifold. (This code path is not covered by the other tests, hence should be kept.)
-- Stating smoothness this way does not make sense, but finding a model with corners should work.
/--
error: failed to synthesize
  TopologicalSpace (TotalSpace F (TangentSpace I))

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
---
trace: [Elab.DiffGeo.MDiff] Finding a model for: TotalSpace F (TangentSpace I)
[Elab.DiffGeo.MDiff] ✅️ TotalSpace
  [Elab.DiffGeo.MDiff] ❌️ From base info
    [Elab.DiffGeo.MDiff] Failed with error:
        No `baseInfo` provided
  [Elab.DiffGeo.MDiff] ✅️ TangentSpace
    [Elab.DiffGeo.MDiff] `TangentSpace I` is the total space of the `TangentBundle` of `M`
    [Elab.DiffGeo.MDiff] Found model: `I.prod I.tangent`
  [Elab.DiffGeo.MDiff] Found model: `I.prod I.tangent`
[Elab.DiffGeo.MDiff] Finding a model for: F
[Elab.DiffGeo.MDiff] ❌️ TotalSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      `F` is not a `Bundle.TotalSpace`.
[Elab.DiffGeo.MDiff] ❌️ TangentBundle
  [Elab.DiffGeo.MDiff] Failed with error:
      `F` is not a `TangentBundle`
[Elab.DiffGeo.MDiff] ✅️ NormedSpace
  [Elab.DiffGeo.MDiff] `F` is a normed space over the field `𝕜`
  [Elab.DiffGeo.MDiff] Found model: `𝓘(𝕜, F)`
-/
#guard_msgs in
set_option trace.Elab.DiffGeo true in
#check MDiff h

-- The reason this test fails is that Bundle.TotalSpace F (TangentSpace I : M → Type _) is not
-- the way to state smoothness.
/--
error: failed to synthesize
  TopologicalSpace (TotalSpace F (TangentSpace I))

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth IsManifold I.tangent 1 (Bundle.TotalSpace F (TangentSpace I : M → Type _))

-- The correct way is this.
/-- info: TotalSpace.isManifold E (TangentSpace I) -/
#guard_msgs in
#synth IsManifold I.tangent 1 (TangentBundle I M)

/-- info: MDifferentiable I.tangent 𝓘(𝕜, F) h' : Prop -/
#guard_msgs in
#check MDifferentiable I.tangent 𝓘(𝕜, F) h'

/-- info: MDifferentiable (I.prod 𝓘(𝕜, E)) 𝓘(𝕜, F) h' : Prop -/
#guard_msgs in
#check MDifferentiable (I.prod (𝓘(𝕜, E))) 𝓘(𝕜, F) h'

/-- info: MDifferentiable I.tangent 𝓘(𝕜, F) h' : Prop -/
#guard_msgs in
#check MDiff h'

end

/-! (Extended) charts -/
section

variable {φ : OpenPartialHomeomorph M H} {ψ : PartialEquiv M E} {s : Set M}

/-- info: ContMDiff I I 37 ↑φ : Prop -/
#guard_msgs in
#check CMDiff 37 φ

/-- info: MDifferentiable I I ↑φ : Prop -/
#guard_msgs in
#check MDiff φ

/-- info: MDifferentiable I 𝓘(𝕜, E) ↑ψ : Prop -/
#guard_msgs in
#check MDiff ψ

/-- info: MDifferentiableWithinAt I I (↑φ) s : M → Prop -/
#guard_msgs in
#check MDiffAt[s] φ

/-- info: MDifferentiableWithinAt I 𝓘(𝕜, E) (↑ψ) s : M → Prop -/
#guard_msgs in
#check MDiffAt[s] ψ

end

-- Inferring a model with corners on a space of linear maps between normed spaces
-- is currently not supported.
variable {f : M → E →L[𝕜] E'} in
/-- error: Could not find a model with corners for `E →L[𝕜] E'` -/
#guard_msgs in
#check MDiff f

variable {f : M → E →L[𝕜] E'} in
/-- error: Could not find a model with corners for `E →L[𝕜] E'` -/
#guard_msgs in
#check CMDiff 2 f

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
/-- error: Could not find a model with corners for `ι` -/
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

/-! Tests for the custom elaborators for `mfderiv` and `mfderivWithin` -/
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

variable {σ : Π x : M, V x} {σ' : (x : E) → Trivial E E' x} {s : E → E'}
variable (X : (m : M) → TangentSpace I m) [IsManifold I 1 M] {x : M}

/--
info: mfderiv I (I.prod 𝓘(𝕜, E)) (fun m ↦ TotalSpace.mk' E m (X m))
  x : TangentSpace I x →L[𝕜] TangentSpace (I.prod 𝓘(𝕜, E)) (TotalSpace.mk' E x (X x))
-/
#guard_msgs in
#check mfderiv% (T% X) x

/--
info: mfderiv I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (σ x))
  x : TangentSpace I x →L[𝕜] TangentSpace (I.prod 𝓘(𝕜, F)) (TotalSpace.mk' F x (σ x))
-/
#guard_msgs in
#check mfderiv% (T% σ) x

variable {t : Set E} {p : E}

/--
info: mfderivWithin 𝓘(𝕜, E) (𝓘(𝕜, E).prod 𝓘(𝕜, E')) (fun x ↦ TotalSpace.mk' E' x (σ' x)) t
  p : TangentSpace 𝓘(𝕜, E) p →L[𝕜] TangentSpace (𝓘(𝕜, E).prod 𝓘(𝕜, E')) (TotalSpace.mk' E' p (σ' p))
-/
#guard_msgs in
#check mfderiv[t] (T% σ') p

/--
info: mfderivWithin 𝓘(𝕜, E) (𝓘(𝕜, E).prod 𝓘(𝕜, E')) (fun x ↦ TotalSpace.mk' E' x (σ' x))
  t : (x : E) → TangentSpace 𝓘(𝕜, E) x →L[𝕜] TangentSpace (𝓘(𝕜, E).prod 𝓘(𝕜, E')) (TotalSpace.mk' E' x (σ' x))
-/
#guard_msgs in
#check mfderiv[t] (T% σ')

section errors

-- Test an error message, about mismatched types.
variable {s' : Set M} {m' : M}

/--
error: Application type mismatch: The argument
  m'
has type
  M
of sort `Type u_4` but is expected to have type
  E
of sort `Type u_2` in the application
  mfderiv 𝓘(𝕜, E) 𝓘(𝕜, EM') f m'
---
info: mfderiv 𝓘(𝕜, E) 𝓘(𝕜, EM') f sorry : TangentSpace 𝓘(𝕜, E) sorry →L[𝕜] TangentSpace 𝓘(𝕜, EM') (f sorry)
-/
#guard_msgs in
#check mfderiv% f m'

-- Error messages: argument s has mismatched type.
/--
error: The domain `E` of `f` is not definitionally equal to the carrier type of the set `s'` : `Set M`
-/
#guard_msgs in
#check mfderiv[s'] f

/--
error: The domain `E` of `f` is not definitionally equal to the carrier type of the set `s'` : `Set M`
-/
#guard_msgs in
#check mfderiv[s'] f m

end errors

section

/--
error: Term `X` is a dependent function, of type `(m : M) → TangentSpace I m`
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check mfderiv% X x

/--
error: Term `σ` is a dependent function, of type `(x : M) → V x`
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check mfderiv% σ x

variable {t : Set E} {p : E}

/--
error: Term `σ'` is a dependent function, of type `(x : E) → Trivial E E' x`
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check mfderiv[t] σ' p

/--
error: Term `σ'` is a dependent function, of type `(x : E) → Trivial E E' x`
Hint: you can use the `T%` elaborator to convert a dependent function to a non-dependent one
-/
#guard_msgs in
#check mfderiv[t] σ'

end

end mfderiv

section trace

/- Test that basic tracing works. -/

set_option trace.Elab.DiffGeo true

variable {f : Unit → Unit}

/--
error: Could not find a model with corners for `Unit`
---
trace: [Elab.DiffGeo.MDiff] Finding a model for: Unit
[Elab.DiffGeo.MDiff] ❌️ TotalSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      `Unit` is not a `Bundle.TotalSpace`.
[Elab.DiffGeo.MDiff] ❌️ TangentBundle
  [Elab.DiffGeo.MDiff] Failed with error:
      `Unit` is not a `TangentBundle`
[Elab.DiffGeo.MDiff] ❌️ NormedSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      Couldn't find a `NormedSpace` structure on `Unit` among local instances.
[Elab.DiffGeo.MDiff] ❌️ Manifold
  [Elab.DiffGeo.MDiff] considering instance of type `ChartedSpace H M`
  [Elab.DiffGeo.MDiff] Failed with error:
      Couldn't find a `ChartedSpace` structure on Unit among local instances, and Unit is not the charted space of some type in the local context either.
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
