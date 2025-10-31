import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Notation
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorField.LieBracket

/-!
# Tests for the differential geometry elaborators which require stronger imports
-/

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

/-! Additional tests for the elaborators for `MDifferentiable{WithinAt,At,On}`. -/
section differentiability

variable {EM' : Type*} [NormedAddCommGroup EM']
  [NormedSpace 𝕜 EM'] {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 EM' H')
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

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

-- Inferring a model with corners on a space of continuous linear maps between normed spaces
section

variable {f : M → E →L[𝕜] E'} in
/-- info: MDifferentiable I 𝓘(𝕜, E →L[𝕜] E') f : Prop -/
#guard_msgs in
#check MDiff f

variable {f : M → E →L[𝕜] E'} in
/-- info: ContMDiff I 𝓘(𝕜, E →L[𝕜] E') 2 f : Prop -/
#guard_msgs in
#check CMDiff 2 f

section

-- And the same test if E is a real normed space and E' is a normed space over a field R' which is
-- definitionally equal to ℝ, but not at reducible transparency: this is meant to test the
-- transparency handling in the definitional equality check in the model inference.

def RealCopy := ℝ

noncomputable instance : NormedField RealCopy := inferInstanceAs (NormedField ℝ)

noncomputable instance : NontriviallyNormedField RealCopy := inferInstanceAs (NontriviallyNormedField ℝ)

variable {E'' E''' : Type*} [NormedAddCommGroup E''] [NormedAddCommGroup E''']
  [NormedSpace ℝ E''] [NormedSpace RealCopy E''']

def id' : ℝ →+* RealCopy := RingHom.id ℝ

set_option trace.Elab.DiffGeo.MDiff true in
variable {f : M → E'' →SL[id'] E'''} in
/--
error: Could not find a model with corners for `E'' →SL[id'] E'''`
---
trace: [Elab.DiffGeo.MDiff] Finding a model for: M
[Elab.DiffGeo.MDiff] ❌️ TotalSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      `M` is not a `Bundle.TotalSpace`.
[Elab.DiffGeo.MDiff] ❌️ TangentBundle
  [Elab.DiffGeo.MDiff] Failed with error:
      `M` is not a `TangentBundle`
[Elab.DiffGeo.MDiff] ❌️ NormedSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      Couldn't find a `NormedSpace` structure on `M` among local instances.
[Elab.DiffGeo.MDiff] ✅️ Manifold
  [Elab.DiffGeo.MDiff] considering instance of type `ChartedSpace H M`
  [Elab.DiffGeo.MDiff] `M` is a charted space over `H` via `inst✝²²`
  [Elab.DiffGeo.MDiff] Found model: `I`
[Elab.DiffGeo.MDiff] Finding a model for: E'' →SL[id'] E'''
[Elab.DiffGeo.MDiff] ❌️ TotalSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      `E'' →SL[id'] E'''` is not a `Bundle.TotalSpace`.
[Elab.DiffGeo.MDiff] ❌️ TangentBundle
  [Elab.DiffGeo.MDiff] Failed with error:
      `E'' →SL[id'] E'''` is not a `TangentBundle`
[Elab.DiffGeo.MDiff] ❌️ NormedSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      Couldn't find a `NormedSpace` structure on `E'' →SL[id'] E'''` among local instances.
[Elab.DiffGeo.MDiff] ❌️ Manifold
  [Elab.DiffGeo.MDiff] considering instance of type `ChartedSpace H M`
  [Elab.DiffGeo.MDiff] considering instance of type `ChartedSpace H' M'`
  [Elab.DiffGeo.MDiff] Failed with error:
      Couldn't find a `ChartedSpace` structure on `E'' →SL[id']
        E'''` among local instances, and `E'' →SL[id']
        E'''` is not the charted space of some type in the local context either.
[Elab.DiffGeo.MDiff] ❌️ ContinuousLinearMap
  [Elab.DiffGeo.MDiff] `E'' →SL[id'] E'''` is a space of continuous linear maps
  [Elab.DiffGeo.MDiff] Failed with error:
      Coefficients `ℝ` and `RealCopy` of `E'' →SL[id'] E'''` are not reducibly definitionally equal
[Elab.DiffGeo.MDiff] ❌️ RealInterval
  [Elab.DiffGeo.MDiff] Failed with error:
      `E'' →SL[id'] E'''` is not a coercion of a set to a type
[Elab.DiffGeo.MDiff] ❌️ UpperHalfPlane
  [Elab.DiffGeo.MDiff] Failed with error:
      `E'' →SL[id'] E'''` is not the complex upper half plane
[Elab.DiffGeo.MDiff] ❌️ NormedField
  [Elab.DiffGeo.MDiff] Failed with error:
      failed to synthesize
        NontriviallyNormedField (E'' →SL[id'] E''')
      ⏎
      Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#check MDiff f

variable {f : (E'' →SL[id'] E''') → E''} in
/-- error: Could not find a model with corners for `E'' →SL[id'] E'''` -/
#guard_msgs in
#check MDiff f

variable {f : M → E'' →SL[id'] E'''} in
/-- error: Could not find a model with corners for `E'' →SL[id'] E'''` -/
#guard_msgs in
#check CMDiff 2 f

end

end

/-! Inferring a model with corners on a real interval -/
section interval

-- Make a new real manifold N with model J.
-- TODO: change this line to modify M and E instead (thus testing if everything
-- still works in the presence of two instances over different fields).
variable {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] {J : ModelWithCorners ℝ E'' H}
  {N : Type} [TopologicalSpace N] [ChartedSpace H N] [IsManifold J 2 N]

-- Types match, but no fact x < y can be inferred: mostly testing error messages.
variable {x y : ℝ} {g : Set.Icc x y → N} {h : E'' → Set.Icc x y} {k : Set.Icc x y → ℝ}

/--
error: failed to synthesize
  ChartedSpace (EuclideanHalfSpace 1) ↑(Set.Icc 0 2)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
variable {g : Set.Icc (0 : ℝ) (2 : ℝ) → M} in
#check CMDiff 2 g

/--
error: failed to synthesize
  ChartedSpace (EuclideanHalfSpace 1) ↑(Set.Icc x y)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#check CMDiff 2 g

/--
error: failed to synthesize
  ChartedSpace (EuclideanHalfSpace 1) ↑(Set.Icc x y)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#check MDiffAt h

/--
error: failed to synthesize
  ChartedSpace (EuclideanHalfSpace 1) ↑(Set.Icc x y)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#check MDiffAt k ⟨x, by linarith⟩

-- A singleton interval: this also should not synthesize.
/--
error: failed to synthesize
  ChartedSpace (EuclideanHalfSpace 1) ↑(Set.Icc x x)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
variable {k : Set.Icc x x → ℝ} in
#check MDiff k

/--
error: failed to synthesize
  Preorder α

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
variable {α : Type*} {x' y' : α} {k : Set.Icc x' y' → ℝ} in
#check MDiff k

/-- error: Could not find a model with corners for `↑(Set.Icc x' y')` -/
#guard_msgs in
variable {α : Type*} [Preorder α] {x' y' : α} {k : ℝ → Set.Icc x' y'} in
#check CMDiff 2 k

-- Now, with a fact about x < y: these should behave well.
variable {x y : ℝ} [Fact (x < y)] {g : Set.Icc x y → N} {h : E'' → Set.Icc x y} {k : Set.Icc x y → ℝ}

/-- info: MDifferentiable (𝓡∂ 1) J g : Prop -/
#guard_msgs in
variable [h: Fact ((0 : ℝ) < (2 : ℝ))] {g : Set.Icc (0 : ℝ) (2 : ℝ) → M} in
#check MDiff g

/-- info: MDifferentiable (𝓡∂ 1) J g : Prop -/
#guard_msgs in
#check MDiff g

/-- info: ContMDiff (𝓡∂ 1) J 2 g : Prop -/
#guard_msgs in
#check CMDiff 2 g

/-- info: MDifferentiableAt 𝓘(ℝ, E'') (𝓡∂ 1) h : E'' → Prop -/
#guard_msgs in
#check MDiffAt h

variable (h : x ≤ y) in
/-- info: MDifferentiableAt (𝓡∂ 1) 𝓘(ℝ, ℝ) k ⟨x, ⋯⟩ : Prop -/
#guard_msgs in
#check MDiffAt k ⟨x, by simp; linarith⟩

-- Test for the definitional equality check: for this type, `isDefEq` would succeed, but
-- `withReducible <| isDefEq` does not. We do not want to consider a type synonym the same,
-- so inferring a model with corners in this case should fail.
def RealCopy' := ℝ

instance : Preorder RealCopy' := inferInstanceAs (Preorder ℝ)
instance : TopologicalSpace RealCopy' := inferInstanceAs (TopologicalSpace ℝ)

-- Repeat the same test for an interval in RealCopy.
variable {x y : RealCopy'} {g : Set.Icc x y → N} {h : E'' → Set.Icc x y} {k : Set.Icc x y → ℝ}
  [Fact (x < y)]

noncomputable instance : ChartedSpace (EuclideanHalfSpace 1) ↑(Set.Icc x y) :=
  instIccChartedSpace x y

set_option trace.Elab.DiffGeo.MDiff true in
/--
error: Could not find a model with corners for `↑(Set.Icc x y)`
---
trace: [Elab.DiffGeo.MDiff] Finding a model for: ↑(Set.Icc x y)
[Elab.DiffGeo.MDiff] ❌️ TotalSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      `↑(Set.Icc x y)` is not a `Bundle.TotalSpace`.
[Elab.DiffGeo.MDiff] ❌️ TangentBundle
  [Elab.DiffGeo.MDiff] Failed with error:
      `↑(Set.Icc x y)` is not a `TangentBundle`
[Elab.DiffGeo.MDiff] ❌️ NormedSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      Couldn't find a `NormedSpace` structure on `↑(Set.Icc x y)` among local instances.
[Elab.DiffGeo.MDiff] ❌️ Manifold
  [Elab.DiffGeo.MDiff] considering instance of type `ChartedSpace H M`
  [Elab.DiffGeo.MDiff] considering instance of type `ChartedSpace H' M'`
  [Elab.DiffGeo.MDiff] considering instance of type `ChartedSpace H N`
  [Elab.DiffGeo.MDiff] Failed with error:
      Couldn't find a `ChartedSpace` structure on `↑(Set.Icc x
          y)` among local instances, and `↑(Set.Icc x
          y)` is not the charted space of some type in the local context either.
[Elab.DiffGeo.MDiff] ❌️ ContinuousLinearMap
  [Elab.DiffGeo.MDiff] Failed with error:
      `↑(Set.Icc x y)` is not a space of continuous linear maps
[Elab.DiffGeo.MDiff] ❌️ RealInterval
  [Elab.DiffGeo.MDiff] Failed with error:
      `Set.Icc x y` is a closed interval of type `RealCopy'`, which is not reducibly definitionally equal to ℝ
[Elab.DiffGeo.MDiff] ❌️ UpperHalfPlane
  [Elab.DiffGeo.MDiff] Failed with error:
      `↑(Set.Icc x y)` is not the complex upper half plane
[Elab.DiffGeo.MDiff] ❌️ NormedField
  [Elab.DiffGeo.MDiff] Failed with error:
      failed to synthesize
        NontriviallyNormedField ↑(Set.Icc x y)
      ⏎
      Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#check MDiffAt g
/-- error: Could not find a model with corners for `↑(Set.Icc x y)` -/
#guard_msgs in
#check MDiff h
/-- error: Could not find a model with corners for `↑(Set.Icc x y)` -/
#guard_msgs in
#check CMDiff 2 k

end interval

section UpperHalfPlane

open scoped UpperHalfPlane

-- Make a new complex manifold N with model J.
-- TODO: change this line to modify M and E instead (thus testing if everything
-- still works in the presence of two instances over different fields).
variable {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℂ E''] {J : ModelWithCorners ℂ E'' H}
  {N : Type} [TopologicalSpace N] [ChartedSpace H N] [IsManifold J 2 N]

variable {g : ℍ → N} {h : E'' → ℍ} {k : ℍ → ℂ} {y : ℍ}

/-- info: ContMDiff 𝓘(ℂ, ℂ) J 2 g : Prop -/
#guard_msgs in
variable {g : ℍ → M} in
#check CMDiff 2 g

/-- info: ContMDiff 𝓘(ℂ, ℂ) J 2 g : Prop -/
#guard_msgs in
#check CMDiff 2 g

/-- info: MDifferentiableAt 𝓘(ℂ, E'') 𝓘(ℂ, ℂ) h : E'' → Prop -/
#guard_msgs in
#check MDiffAt h

/-- info: MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) k y : Prop -/
#guard_msgs in
#check MDiffAt k y

end UpperHalfPlane

end differentiability

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

/-! Tests for the custom elaborators for `HasMFDeriv` and `HasMFDerivWithin` -/
section HasMFDeriv

variable {EM' : Type*} [NormedAddCommGroup EM']
  [NormedSpace 𝕜 EM'] {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 EM' H')
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

variable {f : M → M'} {s : Set M} {m : M} {f' : TangentSpace I m →L[𝕜] TangentSpace I' (f m)}

/-- info: HasMFDerivAt I I' f m f' : Prop -/
#guard_msgs in
#check HasMFDerivAt% f m f'

/-- info: HasMFDerivWithinAt I I' f s m f' : Prop -/
#guard_msgs in
#check HasMFDerivAt[s] f m f'

variable {f : E → EM'} {s : Set E} {m : E}
  -- #check mfderiv% f m tells us the type of f :-)
  {f' : TangentSpace 𝓘(𝕜, E) m →L[𝕜] TangentSpace 𝓘(𝕜, EM') (f m)}

/-- info: HasMFDerivAt 𝓘(𝕜, E) 𝓘(𝕜, EM') f m f' : Prop -/
#guard_msgs in
#check HasMFDerivAt% f m f'

/-- info: HasMFDerivWithinAt 𝓘(𝕜, E) 𝓘(𝕜, EM') f s m f' : Prop -/
#guard_msgs in
#check HasMFDerivAt[s] f m f'

variable {σ : Π x : M, V x} {σ' : (x : E) → Trivial E E' x} {s : E → E'}
variable (X : (m : M) → TangentSpace I m) [IsManifold I 1 M] {x : M}

/--
info: mfderiv I (I.prod 𝓘(𝕜, E)) (fun m ↦ TotalSpace.mk' E m (X m))
  x : TangentSpace I x →L[𝕜] TangentSpace (I.prod 𝓘(𝕜, E)) (TotalSpace.mk' E x (X x))
-/
#guard_msgs in
#check mfderiv% (T% X) x

variable {dXm : TangentSpace I x →L[𝕜] TangentSpace (I.prod 𝓘(𝕜, E)) (TotalSpace.mk' E x (X x))}

/-- info: HasMFDerivAt I (I.prod 𝓘(𝕜, E)) (fun m ↦ TotalSpace.mk' E m (X m)) x dXm : Prop -/
#guard_msgs in
#check HasMFDerivAt% (T% X) x dXm

/-- info: HasMFDerivWithinAt I (I.prod 𝓘(𝕜, E)) (fun m ↦ TotalSpace.mk' E m (X m)) t x dXm : Prop -/
#guard_msgs in
variable {t : Set M} in
#check HasMFDerivAt[t] (T% X) x dXm

/--
info: mfderiv I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (σ x))
  x : TangentSpace I x →L[𝕜] TangentSpace (I.prod 𝓘(𝕜, F)) (TotalSpace.mk' F x (σ x))
-/
#guard_msgs in
#check mfderiv% (T% σ) x

variable {dσm : TangentSpace I x →L[𝕜] TangentSpace (I.prod 𝓘(𝕜, F)) (TotalSpace.mk' F x (σ x))}

/-- info: HasMFDerivAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (σ x)) x dσm : Prop -/
#guard_msgs in
#check HasMFDerivAt% (T% σ) x dσm

/-- info: HasMFDerivWithinAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (σ x)) t x dσm : Prop -/
#guard_msgs in
variable {t : Set M} in
#check HasMFDerivAt[t] (T% σ) x dσm

variable {t : Set E} {p : E}

/--
info: mfderivWithin 𝓘(𝕜, E) (𝓘(𝕜, E).prod 𝓘(𝕜, E')) (fun x ↦ TotalSpace.mk' E' x (σ' x)) t
  p : TangentSpace 𝓘(𝕜, E) p →L[𝕜] TangentSpace (𝓘(𝕜, E).prod 𝓘(𝕜, E')) (TotalSpace.mk' E' p (σ' p))
-/
#guard_msgs in
#check mfderiv[t] (T% σ') p

variable {dσ'p : TangentSpace 𝓘(𝕜, E) p →L[𝕜] TangentSpace (𝓘(𝕜, E).prod 𝓘(𝕜, E')) (TotalSpace.mk' E' p (σ' p))}

/--
info: HasMFDerivAt 𝓘(𝕜, E) (𝓘(𝕜, E).prod 𝓘(𝕜, E')) (fun x ↦ TotalSpace.mk' E' x (σ' x)) p dσ'p : Prop
-/
#guard_msgs in
#check HasMFDerivAt% (T% σ') p dσ'p

/--
info: HasMFDerivWithinAt 𝓘(𝕜, E) (𝓘(𝕜, E).prod 𝓘(𝕜, E')) (fun x ↦ TotalSpace.mk' E' x (σ' x)) t p dσ'p : Prop
-/
#guard_msgs in
#check HasMFDerivAt[t] (T% σ') p dσ'p

/--
info: mfderivWithin 𝓘(𝕜, E) (𝓘(𝕜, E).prod 𝓘(𝕜, E')) (fun x ↦ TotalSpace.mk' E' x (σ' x))
  t : (x : E) → TangentSpace 𝓘(𝕜, E) x →L[𝕜] TangentSpace (𝓘(𝕜, E).prod 𝓘(𝕜, E')) (TotalSpace.mk' E' x (σ' x))
-/
#guard_msgs in
#check mfderiv[t] (T% σ')

-- TODO: skipped the test about error messages (analogous to mfderiv(Within))

end HasMFDeriv
