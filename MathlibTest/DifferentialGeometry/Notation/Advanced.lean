import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
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
-- We want to capture the output of the custom *elaborators* specifically: turning off all notation
-- deactivates some notation for models with corners, but also the delaborators corresponding
-- to the elaborators.
set_option pp.notation false

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

section ErrorMetavars -- Test for error messages when the goal still has metavariables.

-- The argument k is deliberately implicit; it should be explicit in a mathlib definition.
def proj : TangentBundle 𝓘(𝕜, 𝕜) 𝕜 → 𝕜 := fun x ↦ x.2

open ContDiff

/--
error: Could not find a model with corners for `TangentBundle (modelWithCornersSelf ?_ ?_) ?_`.

Hint: the expected type contains metavariables, maybe you need to provide an implicit argument
-/
#guard_msgs in
set_option pp.mvars.anonymous false in
lemma contMDiff_proj : CMDiff ∞ (proj) := by
  unfold proj
  exact contMDiff_snd_tangentBundle_modelSpace 𝕜 𝓘(𝕜)

-- Adding the implicit argument k works.
example : CMDiff ∞ (proj (𝕜 := 𝕜)) := by
  unfold proj
  exact contMDiff_snd_tangentBundle_modelSpace 𝕜 𝓘(𝕜)

end ErrorMetavars

/-! Additional tests for the elaborators for `MDifferentiable{WithinAt,At,On}`. -/
section differentiability

variable {EM' : Type*} [NormedAddCommGroup EM']
  [NormedSpace 𝕜 EM'] {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 EM' H')
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

-- From a manifold into an inner product space.
-- Make sure to declare a new field; otherwise we get a type mismatch about 𝕜 being a
-- normed field via being RCLike and via being a nontrivially normed field.
section

variable {k' : Type*} [RCLike k']
  {E'' : Type*} [NormedAddCommGroup E''] [h: InnerProductSpace k' E'']
  {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace k' E']
  [TopologicalSpace H'] [TopologicalSpace M'] [ChartedSpace H' M']
  (I'' : ModelWithCorners k' E' H') {g' : M' → E''}

/-- info: MDifferentiable I'' (modelWithCornersSelf k' E'') g' : Prop -/
#guard_msgs in
#check MDiff g'

/-- info: ContMDiff I'' (modelWithCornersSelf k' E'') n g' : Prop -/
#guard_msgs in
#check CMDiff n g'

end

/-! A partial homeomorphism or partial equivalence. More generally, this works for any type
with a coercion to (possibly dependent) functions. -/
section coercion

variable {s : Set M} {m : M}

variable {φ : OpenPartialHomeomorph M E} {ψ : PartialEquiv M E}

/-- info: MDifferentiableWithinAt I (modelWithCornersSelf 𝕜 E) (↑φ) s : M → Prop -/
#guard_msgs in
#check MDiffAt[s] φ

/-- info: MDifferentiableWithinAt I (modelWithCornersSelf 𝕜 E) (↑ψ) s : M → Prop -/
#guard_msgs in
#check MDiffAt[s] ψ

/-- info: MDifferentiableAt I (modelWithCornersSelf 𝕜 E) ↑φ : M → Prop -/
#guard_msgs in
#check MDiffAt φ

/-- info: MDifferentiableAt I (modelWithCornersSelf 𝕜 E) ↑ψ : M → Prop -/
#guard_msgs in
#check MDiffAt ψ

/-- info: MDifferentiableOn I (modelWithCornersSelf 𝕜 E) (↑φ) s : Prop -/
#guard_msgs in
#check MDiff[s] φ

/-- info: MDifferentiableOn I (modelWithCornersSelf 𝕜 E) (↑ψ) s : Prop -/
#guard_msgs in
#check MDiff[s] ψ

/-- info: MDifferentiable I (modelWithCornersSelf 𝕜 E) ↑φ : Prop -/
#guard_msgs in
#check MDiff φ

/-- info: ContMDiffWithinAt I (modelWithCornersSelf 𝕜 E) 2 (↑ψ) s : M → Prop -/
#guard_msgs in
#check CMDiffAt[s] 2 ψ

/-- info: ContMDiffOn I (modelWithCornersSelf 𝕜 E) 2 (↑φ) s : Prop -/
#guard_msgs in
#check CMDiff[s] 2 φ

/-- info: ContMDiffAt I (modelWithCornersSelf 𝕜 E) 2 ↑φ : M → Prop -/
#guard_msgs in
#check CMDiffAt 2 φ

/-- info: ContMDiff I (modelWithCornersSelf 𝕜 E) 2 ↑ψ : Prop -/
#guard_msgs in
#check CMDiff 2 ψ

/--
info: mfderiv I (modelWithCornersSelf 𝕜 E)
  ↑φ : (x : M) → ContinuousLinearMap (RingHom.id 𝕜) (TangentSpace I x) (TangentSpace (modelWithCornersSelf 𝕜 E) (↑φ x))
-/
#guard_msgs in
#check mfderiv% φ

/--
info: mfderivWithin I (modelWithCornersSelf 𝕜 E) (↑ψ)
  s : (x : M) → ContinuousLinearMap (RingHom.id 𝕜) (TangentSpace I x) (TangentSpace (modelWithCornersSelf 𝕜 E) (↑ψ x))
-/
#guard_msgs in
#check mfderiv[s] ψ

/--
info: mfderivWithin I (modelWithCornersSelf 𝕜 E) (↑ψ)
  s : (x : M) → ContinuousLinearMap (RingHom.id 𝕜) (TangentSpace I x) (TangentSpace (modelWithCornersSelf 𝕜 E) (↑ψ x))
-/
#guard_msgs in
variable {f : ContMDiffSection I F n V} in
#check mfderiv[s] ψ

/--
info: mfderiv I I' ⇑g : (x : M) → ContinuousLinearMap (RingHom.id 𝕜) (TangentSpace I x) (TangentSpace I' (g x))
-/
#guard_msgs in
variable {g : ContMDiffMap I I' M M' n} in
#check mfderiv% g

-- An example of "any type" which coerces to functions.
/--
info: mfderiv I I' ⇑g : (x : M) → ContinuousLinearMap (RingHom.id 𝕜) (TangentSpace I x) (TangentSpace I' (g x))
-/
#guard_msgs in
variable {g : Equiv M M'} in
#check mfderiv% g

end coercion

variable {σ : Π x : M, V x} {σ' : (x : E) → Trivial E E' x} {s : E → E'}
variable (X : (m : M) → TangentSpace I m) [IsManifold I 1 M]

/-! These elaborators can be combined with the total space elaborator. -/
section interaction

-- Note: these tests might be incomplete; extend as needed!

/--
info: MDifferentiableAt I (I.prod (modelWithCornersSelf 𝕜 E)) fun m ↦ TotalSpace.mk' E m (X m) : M → Prop
-/
#guard_msgs in
#check MDiffAt (T% X)

/--
info: MDifferentiableAt I (I.prod (modelWithCornersSelf 𝕜 F)) fun x ↦ TotalSpace.mk' F x (σ x) : M → Prop
-/
#guard_msgs in
#check MDiffAt (T% σ)

/--
info: MDifferentiableAt (modelWithCornersSelf 𝕜 E) ((modelWithCornersSelf 𝕜 E).prod (modelWithCornersSelf 𝕜 E')) fun x ↦
  TotalSpace.mk' E' x (σ' x) : E → Prop
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
trace: [Elab.DiffGeo.MDiff] Finding a model with corners for: `TotalSpace F (TangentSpace I)`
[Elab.DiffGeo.MDiff] ✅️ TotalSpace
  [Elab.DiffGeo.MDiff] 💥️ From base info
    [Elab.DiffGeo.MDiff] Failed with error:
        No `baseInfo` provided
  [Elab.DiffGeo.MDiff] ✅️ TangentSpace
    [Elab.DiffGeo.MDiff] `TangentSpace I` is the total space of the `TangentBundle` of `M`
    [Elab.DiffGeo.MDiff] Found model: `I.prod I.tangent`
  [Elab.DiffGeo.MDiff] Found model: `I.prod I.tangent`
[Elab.DiffGeo.MDiff] Finding a model with corners for: `F`
[Elab.DiffGeo.MDiff] 💥️ TotalSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      `F` is not a `Bundle.TotalSpace`.
[Elab.DiffGeo.MDiff] 💥️ TangentBundle
  [Elab.DiffGeo.MDiff] Failed with error:
      `F` is not a `TangentBundle`
[Elab.DiffGeo.MDiff] ✅️ NormedSpace
  [Elab.DiffGeo.MDiff] `F` is a normed space over the field `𝕜`
  [Elab.DiffGeo.MDiff] Found model: `modelWithCornersSelf 𝕜 F`
  [Elab.DiffGeo.MDiff] This is the trivial model with corners for the normed space `F` over the base field `𝕜`.
-/
#guard_msgs in
set_option trace.Elab.DiffGeo true in
#check MDiff h

-- The reason this test fails is that Bundle.TotalSpace F (TangentSpace I : M → Type _) is not
-- the way to state smoothness.
/--
error: failed to synthesize instance of type class
  TopologicalSpace (TotalSpace F (TangentSpace I))

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#synth IsManifold I.tangent 1 (Bundle.TotalSpace F (TangentSpace I : M → Type _))

-- The correct way is this.
/-- info: TotalSpace.isManifold E (TangentSpace I) -/
#guard_msgs in
#synth IsManifold I.tangent 1 (TangentBundle I M)

/-- info: MDifferentiable I.tangent (modelWithCornersSelf 𝕜 F) h' : Prop -/
#guard_msgs in
#check MDifferentiable I.tangent 𝓘(𝕜, F) h'

/--
info: MDifferentiable (I.prod (modelWithCornersSelf 𝕜 E)) (modelWithCornersSelf 𝕜 F) h' : Prop
-/
#guard_msgs in
#check MDifferentiable (I.prod (𝓘(𝕜, E))) 𝓘(𝕜, F) h'

/-- info: MDifferentiable I.tangent (modelWithCornersSelf 𝕜 F) h' : Prop -/
#guard_msgs in
#check MDiff h'

end

-- Inferring a model with corners on a space of continuous linear maps between normed spaces
section ContinuousLinearMap

variable {f : M → E →L[𝕜] E'} in
/--
info: MDifferentiable I (modelWithCornersSelf 𝕜 (ContinuousLinearMap (RingHom.id 𝕜) E E')) f : Prop
-/
#guard_msgs in
#check MDiff f

variable {f : M → E →L[𝕜] E'} in
/--
info: ContMDiff I (modelWithCornersSelf 𝕜 (ContinuousLinearMap (RingHom.id 𝕜) E E')) 2 f : Prop
-/
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
error: Could not find a model with corners for `ContinuousLinearMap id' E'' E'''`.
---
trace: [Elab.DiffGeo.MDiff] Finding a model with corners for: `M`
[Elab.DiffGeo.MDiff] 💥️ TotalSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      `M` is not a `Bundle.TotalSpace`.
[Elab.DiffGeo.MDiff] 💥️ TangentBundle
  [Elab.DiffGeo.MDiff] Failed with error:
      `M` is not a `TangentBundle`
[Elab.DiffGeo.MDiff] 💥️ NormedSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      Couldn't find a `NormedSpace` structure on `M` among local instances.
[Elab.DiffGeo.MDiff] ✅️ Manifold
  [Elab.DiffGeo.MDiff] considering instance of type `ChartedSpace H M`
  [Elab.DiffGeo.MDiff] `M` is a charted space over `H` via `inst✝²²`
  [Elab.DiffGeo.MDiff] Found model: `I`
[Elab.DiffGeo.MDiff] Finding a model with corners for: `ContinuousLinearMap id' E'' E'''`
[Elab.DiffGeo.MDiff] 💥️ TotalSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      `ContinuousLinearMap id' E'' E'''` is not a `Bundle.TotalSpace`.
[Elab.DiffGeo.MDiff] 💥️ TangentBundle
  [Elab.DiffGeo.MDiff] Failed with error:
      `ContinuousLinearMap id' E'' E'''` is not a `TangentBundle`
[Elab.DiffGeo.MDiff] 💥️ NormedSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      Couldn't find a `NormedSpace` structure on `ContinuousLinearMap id' E'' E'''` among local instances.
[Elab.DiffGeo.MDiff] 💥️ Manifold
  [Elab.DiffGeo.MDiff] considering instance of type `ChartedSpace H M`
  [Elab.DiffGeo.MDiff] considering instance of type `ChartedSpace H' M'`
  [Elab.DiffGeo.MDiff] Failed with error:
      Couldn't find a `ChartedSpace` structure on `ContinuousLinearMap id' E''
        E'''` among local instances, and `ContinuousLinearMap id' E''
        E'''` is not the charted space of some type in the local context either.
[Elab.DiffGeo.MDiff] 💥️ ContinuousLinearMap
  [Elab.DiffGeo.MDiff] `ContinuousLinearMap id' E'' E'''` is a space of continuous (semi-)linear maps
  [Elab.DiffGeo.MDiff] Failed with error:
      Coefficients `Real` and `RealCopy` of `ContinuousLinearMap id' E'' E'''` are not reducibly definitionally equal
[Elab.DiffGeo.MDiff] 💥️ RealInterval
  [Elab.DiffGeo.MDiff] Failed with error:
      `ContinuousLinearMap id' E'' E'''` is not a coercion of a set to a type
[Elab.DiffGeo.MDiff] 💥️ EuclideanSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      `ContinuousLinearMap id' E'' E'''` is not a Euclidean space, half-space or quadrant
[Elab.DiffGeo.MDiff] 💥️ UpperHalfPlane
  [Elab.DiffGeo.MDiff] Failed with error:
      `ContinuousLinearMap id' E'' E'''` is not the complex upper half plane
[Elab.DiffGeo.MDiff] 💥️ Units of algebra
  [Elab.DiffGeo.MDiff] Failed with error:
      `ContinuousLinearMap id' E'' E'''` is not a set of units, in particular not of a complete normed algebra
[Elab.DiffGeo.MDiff] 💥️ Complex unit circle
  [Elab.DiffGeo.MDiff] Failed with error:
      `ContinuousLinearMap id' E'' E'''` is not the complex unit circle
[Elab.DiffGeo.MDiff] 💥️ Sphere
  [Elab.DiffGeo.MDiff] Failed with error:
      `ContinuousLinearMap id' E'' E'''` is not a coercion of a set to a type
[Elab.DiffGeo.MDiff] 💥️ NormedField
  [Elab.DiffGeo.MDiff] Failed with error:
      failed to synthesize instance of type class
        NontriviallyNormedField (ContinuousLinearMap id' E'' E''')
      ⏎
      Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
[Elab.DiffGeo.MDiff] 💥️ InnerProductSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      Couldn't find an `InnerProductSpace` structure on `ContinuousLinearMap id' E'' E'''` among local instances.
-/
#guard_msgs in
#check MDiff f

variable {f : (E'' →SL[id'] E''') → E''} in
/--
error: Could not find a model with corners for `ContinuousLinearMap id' E'' E'''`.

Hint: failures to find a model with corners can be debugged with the command `set_option trace.Elab.DiffGeo.MDiff true`.
-/
#guard_msgs in
#check MDiff f

variable {f : M → E'' →SL[id'] E'''} in
/--
error: Could not find a model with corners for `ContinuousLinearMap id' E'' E'''`.

Hint: failures to find a model with corners can be debugged with the command `set_option trace.Elab.DiffGeo.MDiff true`.
-/
#guard_msgs in
#check CMDiff 2 f

-- Testing the case of a map that is not the identity: we infer a model with corners, but
-- it will not match the desired type exactly.
variable {E'''' : Type*} [NormedAddCommGroup E''''] [NormedSpace ℝ E'''']
  {σ : ℝ →+* ℝ} [RingHomIsometric σ]

variable {f : M → E'' →SL[σ] E''''} in
/--
error: Could not find a model with corners for `ContinuousLinearMap σ E'' E''''`.

Hint: failures to find a model with corners can be debugged with the command `set_option trace.Elab.DiffGeo.MDiff true`.
-/
#guard_msgs in
set_option pp.mvars.anonymous false in
#check CMDiff 2 f

variable {f : M → E'' →SL[σ] E''''} in
/--
error: Could not find a model with corners for `ContinuousLinearMap σ E'' E''''`.
---
trace: [Elab.DiffGeo.MDiff] Finding a model with corners for: `M`
[Elab.DiffGeo.MDiff] 💥️ TotalSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      `M` is not a `Bundle.TotalSpace`.
[Elab.DiffGeo.MDiff] 💥️ TangentBundle
  [Elab.DiffGeo.MDiff] Failed with error:
      `M` is not a `TangentBundle`
[Elab.DiffGeo.MDiff] 💥️ NormedSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      Couldn't find a `NormedSpace` structure on `M` among local instances.
[Elab.DiffGeo.MDiff] ✅️ Manifold
  [Elab.DiffGeo.MDiff] considering instance of type `ChartedSpace H M`
  [Elab.DiffGeo.MDiff] `M` is a charted space over `H` via `inst✝²⁵`
  [Elab.DiffGeo.MDiff] Found model: `I`
[Elab.DiffGeo.MDiff] Finding a model with corners for: `ContinuousLinearMap σ E'' E''''`
[Elab.DiffGeo.MDiff] 💥️ TotalSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      `ContinuousLinearMap σ E'' E''''` is not a `Bundle.TotalSpace`.
[Elab.DiffGeo.MDiff] 💥️ TangentBundle
  [Elab.DiffGeo.MDiff] Failed with error:
      `ContinuousLinearMap σ E'' E''''` is not a `TangentBundle`
[Elab.DiffGeo.MDiff] 💥️ NormedSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      Couldn't find a `NormedSpace` structure on `ContinuousLinearMap σ E'' E''''` among local instances.
[Elab.DiffGeo.MDiff] 💥️ Manifold
  [Elab.DiffGeo.MDiff] considering instance of type `ChartedSpace H M`
  [Elab.DiffGeo.MDiff] considering instance of type `ChartedSpace H' M'`
  [Elab.DiffGeo.MDiff] Failed with error:
      Couldn't find a `ChartedSpace` structure on `ContinuousLinearMap σ E''
        E''''` among local instances, and `ContinuousLinearMap σ E''
        E''''` is not the charted space of some type in the local context either.
[Elab.DiffGeo.MDiff] 💥️ ContinuousLinearMap
  [Elab.DiffGeo.MDiff] `ContinuousLinearMap σ E'' E''''` is a space of continuous (semi-)linear maps
  [Elab.DiffGeo.MDiff] Failed with error:
      `ContinuousLinearMap σ E'' E''''` is a space of continuous (semi-)linear maps over `σ`, which is not the identity
[Elab.DiffGeo.MDiff] 💥️ RealInterval
  [Elab.DiffGeo.MDiff] Failed with error:
      `ContinuousLinearMap σ E'' E''''` is not a coercion of a set to a type
[Elab.DiffGeo.MDiff] 💥️ EuclideanSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      `ContinuousLinearMap σ E'' E''''` is not a Euclidean space, half-space or quadrant
[Elab.DiffGeo.MDiff] 💥️ UpperHalfPlane
  [Elab.DiffGeo.MDiff] Failed with error:
      `ContinuousLinearMap σ E'' E''''` is not the complex upper half plane
[Elab.DiffGeo.MDiff] 💥️ Units of algebra
  [Elab.DiffGeo.MDiff] Failed with error:
      `ContinuousLinearMap σ E'' E''''` is not a set of units, in particular not of a complete normed algebra
[Elab.DiffGeo.MDiff] 💥️ Complex unit circle
  [Elab.DiffGeo.MDiff] Failed with error:
      `ContinuousLinearMap σ E'' E''''` is not the complex unit circle
[Elab.DiffGeo.MDiff] 💥️ Sphere
  [Elab.DiffGeo.MDiff] Failed with error:
      `ContinuousLinearMap σ E'' E''''` is not a coercion of a set to a type
[Elab.DiffGeo.MDiff] 💥️ NormedField
  [Elab.DiffGeo.MDiff] Failed with error:
      failed to synthesize instance of type class
        NontriviallyNormedField (ContinuousLinearMap σ E'' E'''')
      ⏎
      Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
[Elab.DiffGeo.MDiff] 💥️ InnerProductSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      Couldn't find an `InnerProductSpace` structure on `ContinuousLinearMap σ E'' E''''` among local instances.
-/
#guard_msgs in
set_option trace.Elab.DiffGeo.MDiff true in
set_option pp.mvars.anonymous false in
#check CMDiff 2 f

end

end ContinuousLinearMap

/-! Inferring a model with corners on a real interval -/
section RealInterval

-- Make a new real manifold N with model J.
-- TODO: change this line to modify M and E instead (thus testing if everything
-- still works in the presence of two instances over different fields).
variable {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] {J : ModelWithCorners ℝ E'' H}
  {N : Type} [TopologicalSpace N] [ChartedSpace H N] [IsManifold J 2 N]

variable {g : unitInterval → M} in
/-- info: MDifferentiable (modelWithCornersEuclideanHalfSpace 1) J g : Prop -/
#guard_msgs in
#check MDiff g

variable {h : E'' → unitInterval} in
/--
info: MDifferentiable (modelWithCornersSelf Real E'') (modelWithCornersEuclideanHalfSpace 1) h : Prop
-/
#guard_msgs in
#check MDiff h

variable {k : unitInterval → ℝ} in
/--
info: MDifferentiable (modelWithCornersEuclideanHalfSpace 1) (modelWithCornersSelf Real Real) k : Prop
-/
#guard_msgs in
#check MDiff k

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
error: failed to synthesize instance of type class
  Preorder α

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
variable {α : Type*} {x' y' : α} {k : Set.Icc x' y' → ℝ} in
#check MDiff k

/--
error: Could not find a model with corners for `↑(Set.Icc x' y')`.

Hint: failures to find a model with corners can be debugged with the command `set_option trace.Elab.DiffGeo.MDiff true`.
-/
#guard_msgs in
variable {α : Type*} [Preorder α] {x' y' : α} {k : ℝ → Set.Icc x' y'} in
#check CMDiff 2 k

-- Now, with a fact about x < y: these should behave well.
variable {x y : ℝ} [Fact (x < y)] {g : Set.Icc x y → N} {h : E'' → Set.Icc x y} {k : Set.Icc x y → ℝ}

/-- info: MDifferentiable (modelWithCornersEuclideanHalfSpace 1) J g : Prop -/
#guard_msgs in
variable [h: Fact ((0 : ℝ) < (2 : ℝ))] {g : Set.Icc (0 : ℝ) (2 : ℝ) → M} in
#check MDiff g

/-- info: MDifferentiable (modelWithCornersEuclideanHalfSpace 1) J g : Prop -/
#guard_msgs in
#check MDiff g

/-- info: ContMDiff (modelWithCornersEuclideanHalfSpace 1) J 2 g : Prop -/
#guard_msgs in
#check CMDiff 2 g

/--
info: MDifferentiableAt (modelWithCornersSelf Real E'') (modelWithCornersEuclideanHalfSpace 1) h : E'' → Prop
-/
#guard_msgs in
#check MDiffAt h

variable (h : x ≤ y) in
/--
info: MDifferentiableAt (modelWithCornersEuclideanHalfSpace 1) (modelWithCornersSelf Real Real) k ⟨x, ⋯⟩ : Prop
-/
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

set_option backward.isDefEq.respectTransparency false in
noncomputable instance : ChartedSpace (EuclideanHalfSpace 1) ↑(Set.Icc x y) :=
  instIccChartedSpace x y

set_option trace.Elab.DiffGeo.MDiff true in
/--
error: Could not find a model with corners for `↑(Set.Icc x y)`.
---
trace: [Elab.DiffGeo.MDiff] Finding a model with corners for: `↑(Set.Icc x y)`
[Elab.DiffGeo.MDiff] 💥️ TotalSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      `↑(Set.Icc x y)` is not a `Bundle.TotalSpace`.
[Elab.DiffGeo.MDiff] 💥️ TangentBundle
  [Elab.DiffGeo.MDiff] Failed with error:
      `↑(Set.Icc x y)` is not a `TangentBundle`
[Elab.DiffGeo.MDiff] 💥️ NormedSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      Couldn't find a `NormedSpace` structure on `↑(Set.Icc x y)` among local instances.
[Elab.DiffGeo.MDiff] 💥️ Manifold
  [Elab.DiffGeo.MDiff] considering instance of type `ChartedSpace H M`
  [Elab.DiffGeo.MDiff] considering instance of type `ChartedSpace H' M'`
  [Elab.DiffGeo.MDiff] considering instance of type `ChartedSpace H N`
  [Elab.DiffGeo.MDiff] Failed with error:
      Couldn't find a `ChartedSpace` structure on `↑(Set.Icc x
          y)` among local instances, and `↑(Set.Icc x
          y)` is not the charted space of some type in the local context either.
[Elab.DiffGeo.MDiff] 💥️ ContinuousLinearMap
  [Elab.DiffGeo.MDiff] Failed with error:
      `↑(Set.Icc x y)` is not a space of continuous linear maps
[Elab.DiffGeo.MDiff] 💥️ RealInterval
  [Elab.DiffGeo.MDiff] Failed with error:
      `Set.Icc x y` is a closed interval of type `RealCopy'`, which is not reducibly definitionally equal to ℝ
[Elab.DiffGeo.MDiff] 💥️ EuclideanSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      `↑(Set.Icc x y)` is not a Euclidean space, half-space or quadrant
[Elab.DiffGeo.MDiff] 💥️ UpperHalfPlane
  [Elab.DiffGeo.MDiff] Failed with error:
      `↑(Set.Icc x y)` is not the complex upper half plane
[Elab.DiffGeo.MDiff] 💥️ Units of algebra
  [Elab.DiffGeo.MDiff] Failed with error:
      `↑(Set.Icc x y)` is not a set of units, in particular not of a complete normed algebra
[Elab.DiffGeo.MDiff] 💥️ Complex unit circle
  [Elab.DiffGeo.MDiff] Failed with error:
      `↑(Set.Icc x y)` is not the complex unit circle
[Elab.DiffGeo.MDiff] 💥️ Sphere
  [Elab.DiffGeo.MDiff] Failed with error:
      `Set.Icc x y` is not a sphere in a real normed space
[Elab.DiffGeo.MDiff] 💥️ NormedField
  [Elab.DiffGeo.MDiff] Failed with error:
      failed to synthesize instance of type class
        NontriviallyNormedField ↑(Set.Icc x y)
      ⏎
      Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
[Elab.DiffGeo.MDiff] 💥️ InnerProductSpace
  [Elab.DiffGeo.MDiff] Failed with error:
      Couldn't find an `InnerProductSpace` structure on `↑(Set.Icc x y)` among local instances.
-/
#guard_msgs in
#check MDiffAt g
/--
error: Could not find a model with corners for `↑(Set.Icc x y)`.

Hint: failures to find a model with corners can be debugged with the command `set_option trace.Elab.DiffGeo.MDiff true`.
-/
#guard_msgs in
#check MDiff h
/--
error: Could not find a model with corners for `↑(Set.Icc x y)`.

Hint: failures to find a model with corners can be debugged with the command `set_option trace.Elab.DiffGeo.MDiff true`.
-/
#guard_msgs in
#check CMDiff 2 k

end RealInterval

/-! Tests for inferring a model with corners on Euclidean space, half-spaces and quadrants -/
section EuclideanSpace

variable {n m n' m' : ℕ} [NeZero n] [NeZero m] [NeZero n'] [NeZero m']
  {f : EuclideanSpace ℝ (Fin n) → ℝ} {g : EuclideanSpace ℝ (Fin n') → EuclideanSpace ℝ (Fin m')}
  {a b : ℝ} [Fact (a < b)] {h : Set.Icc a b → EuclideanSpace ℝ (Fin m)}

/--
info: MDifferentiable (modelWithCornersSelf Real (EuclideanSpace Real (Fin n))) (modelWithCornersSelf Real Real) f : Prop
-/
#guard_msgs in
#check MDiff f

/--
info: MDifferentiableAt (modelWithCornersSelf Real (EuclideanSpace Real (Fin n')))
  (modelWithCornersSelf Real (EuclideanSpace Real (Fin m'))) g : EuclideanSpace Real (Fin n') → Prop
-/
#guard_msgs in
#check MDiffAt g

/--
info: ContMDiff (modelWithCornersEuclideanHalfSpace 1) (modelWithCornersSelf Real (EuclideanSpace Real (Fin m))) 2 h : Prop
-/
#guard_msgs in
#check CMDiff 2 h

variable {f' : EuclideanHalfSpace 2 → ℝ} {x : EuclideanHalfSpace 2}
  {g' : EuclideanHalfSpace n → EuclideanHalfSpace m} {y : EuclideanHalfSpace n}

/--
info: ContMDiff (modelWithCornersEuclideanHalfSpace 2) (modelWithCornersSelf Real Real) 2 f' : Prop
-/
#guard_msgs in
#check CMDiff 2 f'

/--
info: MDifferentiableAt (modelWithCornersEuclideanHalfSpace 2) (modelWithCornersSelf Real Real) f' x : Prop
-/
#guard_msgs in
#check MDiffAt f' x

/--
info: MDifferentiableAt (modelWithCornersEuclideanHalfSpace n) (modelWithCornersEuclideanHalfSpace m) g' y : Prop
-/
#guard_msgs in
#check MDiffAt g' y

/--
info: ContMDiff (modelWithCornersEuclideanHalfSpace n) (modelWithCornersEuclideanHalfSpace m) 37 g' : Prop
-/
#guard_msgs in
#check CMDiff 37 g'

variable {f : EuclideanHalfSpace 2 → EuclideanSpace ℝ (Fin 37)} in
/--
info: ContMDiff (modelWithCornersEuclideanHalfSpace 2) (modelWithCornersSelf Real (EuclideanSpace Real (Fin 37))) 2 f : Prop
-/
#guard_msgs in
#check CMDiff 2 f

variable {f : EuclideanQuadrant 2 → EuclideanSpace ℝ (Fin 37)} in
/--
info: ContMDiff (modelWithCornersEuclideanQuadrant 2) (modelWithCornersSelf Real (EuclideanSpace Real (Fin 37))) 2 f : Prop
-/
#guard_msgs in
#check CMDiff 2 f

variable {f : EuclideanSpace ℝ (Fin 37) → EuclideanQuadrant m'} in
/--
info: MDifferentiable (modelWithCornersSelf Real (EuclideanSpace Real (Fin 37))) (modelWithCornersEuclideanQuadrant m')
  f : Prop
-/
#guard_msgs in
#check MDiff f

/--
info: ContMDiff
  ((modelWithCornersSelf Real (EuclideanSpace Real (Fin n))).prod
    (modelWithCornersSelf Real (EuclideanSpace Real (Fin n'))))
  ((modelWithCornersSelf Real Real).prod (modelWithCornersSelf Real (EuclideanSpace Real (Fin m')))) 37
  (Prod.map f g) : Prop
-/
#guard_msgs in
#check CMDiff 37 (Prod.map f g)
/--
info: ContMDiff ((modelWithCornersEuclideanHalfSpace 2).prod (modelWithCornersEuclideanHalfSpace n))
  ((modelWithCornersSelf Real Real).prod (modelWithCornersEuclideanHalfSpace m)) 37 (Prod.map f' g') : Prop
-/
#guard_msgs in
#check CMDiff 37 (Prod.map f' g')

end EuclideanSpace

-- See `NotationSphere.lean` for tests for the elaborators for spheres.

section UpperHalfPlane

open scoped UpperHalfPlane

-- Make a new complex manifold N with model J.
-- TODO: change this line to modify M and E instead (thus testing if everything
-- still works in the presence of two instances over different fields).
variable {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℂ E''] {J : ModelWithCorners ℂ E'' H}
  {N : Type} [TopologicalSpace N] [ChartedSpace H N] [IsManifold J 2 N]

variable {g : ℍ → N} {h : E'' → ℍ} {k : ℍ → ℂ} {y : ℍ}

/-- info: ContMDiff (modelWithCornersSelf Complex Complex) J 2 g : Prop -/
#guard_msgs in
variable {g : ℍ → M} in
#check CMDiff 2 g

/-- info: ContMDiff (modelWithCornersSelf Complex Complex) J 2 g : Prop -/
#guard_msgs in
#check CMDiff 2 g

/--
info: MDifferentiableAt (modelWithCornersSelf Complex E'') (modelWithCornersSelf Complex Complex) h : E'' → Prop
-/
#guard_msgs in
#check MDiffAt h

/--
info: MDifferentiableAt (modelWithCornersSelf Complex Complex) (modelWithCornersSelf Complex Complex) k y : Prop
-/
#guard_msgs in
#check MDiffAt k y

end UpperHalfPlane

section units

variable {R : Type*} [NormedRing R] [CompleteSpace R] [NormedAlgebra 𝕜 R]

variable {f : Rˣ → 𝕜} in
/-- info: MDifferentiable (modelWithCornersSelf 𝕜 R) (modelWithCornersSelf 𝕜 𝕜) f : Prop -/
#guard_msgs in
#check MDiff f

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V]

-- #check LieGroup 𝓘(𝕜, V →L[𝕜] V) 2 (V →L[𝕜] V)ˣ passes

/--
info: MDifferentiable (modelWithCornersSelf 𝕜 (ContinuousLinearMap (RingHom.id 𝕜) V V)) (modelWithCornersSelf 𝕜 𝕜) f : Prop
-/
#guard_msgs in
variable {f : (V →L[𝕜] V)ˣ → 𝕜} in
#check MDiff f

variable {α : Type*} [Monoid α] [Ring α]

/--
error: Could not find a model with corners for `Units α`.

Hint: failures to find a model with corners can be debugged with the command `set_option trace.Elab.DiffGeo.MDiff true`.
-/
#guard_msgs in
variable {f : αˣ → 𝕜} in
#check MDiff f

end units

end differentiability

/-! Tests for the custom elaborators for `mfderiv` and `mfderivWithin` -/
section mfderiv

variable {EM' : Type*} [NormedAddCommGroup EM']
  [NormedSpace 𝕜 EM'] {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 EM' H')
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

variable {f : M → M'} {s : Set M} {m : M}

/--
info: mfderiv I I' f : (x : M) → ContinuousLinearMap (RingHom.id 𝕜) (TangentSpace I x) (TangentSpace I' (f x))
-/
#guard_msgs in
#check mfderiv% f

/--
info: mfderiv I I' f m : ContinuousLinearMap (RingHom.id 𝕜) (TangentSpace I m) (TangentSpace I' (f m))
-/
#guard_msgs in
#check mfderiv% f m

/--
info: mfderivWithin I I' f s : (x : M) → ContinuousLinearMap (RingHom.id 𝕜) (TangentSpace I x) (TangentSpace I' (f x))
-/
#guard_msgs in
#check mfderiv[s] f

/--
info: mfderivWithin I I' f s m : ContinuousLinearMap (RingHom.id 𝕜) (TangentSpace I m) (TangentSpace I' (f m))
-/
#guard_msgs in
#check mfderiv[s] f m

variable {f : E → EM'} {s : Set E} {m : E}

/--
info: mfderiv (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 EM')
  f : (x : E) →
  ContinuousLinearMap (RingHom.id 𝕜) (TangentSpace (modelWithCornersSelf 𝕜 E) x)
    (TangentSpace (modelWithCornersSelf 𝕜 EM') (f x))
-/
#guard_msgs in
#check mfderiv% f

/--
info: mfderiv (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 EM') f
  m : ContinuousLinearMap (RingHom.id 𝕜) (TangentSpace (modelWithCornersSelf 𝕜 E) m)
  (TangentSpace (modelWithCornersSelf 𝕜 EM') (f m))
-/
#guard_msgs in
#check mfderiv% f m

/--
info: mfderivWithin (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 EM') f
  s : (x : E) →
  ContinuousLinearMap (RingHom.id 𝕜) (TangentSpace (modelWithCornersSelf 𝕜 E) x)
    (TangentSpace (modelWithCornersSelf 𝕜 EM') (f x))
-/
#guard_msgs in
#check mfderiv[s] f

/--
info: mfderivWithin (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 EM') f s
  m : ContinuousLinearMap (RingHom.id 𝕜) (TangentSpace (modelWithCornersSelf 𝕜 E) m)
  (TangentSpace (modelWithCornersSelf 𝕜 EM') (f m))
-/
#guard_msgs in
#check mfderiv[s] f m

variable {σ : Π x : M, V x} {σ' : (x : E) → Trivial E E' x} {s : E → E'}
variable (X : (m : M) → TangentSpace I m) [IsManifold I 1 M] {x : M}

/--
info: mfderiv I (I.prod (modelWithCornersSelf 𝕜 E)) (fun m ↦ TotalSpace.mk' E m (X m))
  x : ContinuousLinearMap (RingHom.id 𝕜) (TangentSpace I x)
  (TangentSpace (I.prod (modelWithCornersSelf 𝕜 E)) (TotalSpace.mk' E x (X x)))
-/
#guard_msgs in
#check mfderiv% (T% X) x

/--
info: mfderiv I (I.prod (modelWithCornersSelf 𝕜 F)) (fun x ↦ TotalSpace.mk' F x (σ x))
  x : ContinuousLinearMap (RingHom.id 𝕜) (TangentSpace I x)
  (TangentSpace (I.prod (modelWithCornersSelf 𝕜 F)) (TotalSpace.mk' F x (σ x)))
-/
#guard_msgs in
#check mfderiv% (T% σ) x

variable {t : Set E} {p : E}

/--
info: mfderivWithin (modelWithCornersSelf 𝕜 E) ((modelWithCornersSelf 𝕜 E).prod (modelWithCornersSelf 𝕜 E'))
  (fun x ↦ TotalSpace.mk' E' x (σ' x)) t
  p : ContinuousLinearMap (RingHom.id 𝕜) (TangentSpace (modelWithCornersSelf 𝕜 E) p)
  (TangentSpace ((modelWithCornersSelf 𝕜 E).prod (modelWithCornersSelf 𝕜 E')) (TotalSpace.mk' E' p (σ' p)))
-/
#guard_msgs in
#check mfderiv[t] (T% σ') p

/--
info: mfderivWithin (modelWithCornersSelf 𝕜 E) ((modelWithCornersSelf 𝕜 E).prod (modelWithCornersSelf 𝕜 E'))
  (fun x ↦ TotalSpace.mk' E' x (σ' x))
  t : (x : E) →
  ContinuousLinearMap (RingHom.id 𝕜) (TangentSpace (modelWithCornersSelf 𝕜 E) x)
    (TangentSpace ((modelWithCornersSelf 𝕜 E).prod (modelWithCornersSelf 𝕜 E')) (TotalSpace.mk' E' x (σ' x)))
-/
#guard_msgs in
#check mfderiv[t] (T% σ')

section errors

-- Test an error message, about mismatched types.
variable {s' : Set M} {m' : M}

set_option pp.notation true in
/--
error: Application type mismatch: The argument
  m'
has type
  M
of sort `Type u_4` but is expected to have type
  E
of sort `Type u_2` in the application
  mfderiv% f m'
---
info: mfderiv% f sorry : TangentSpace 𝓘(𝕜, E) sorry →L[𝕜] TangentSpace 𝓘(𝕜, EM') (f sorry)
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

/-- info: HasMFDerivAt (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 EM') f m f' : Prop -/
#guard_msgs in
#check HasMFDerivAt% f m f'

/--
info: HasMFDerivWithinAt (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 EM') f s m f' : Prop
-/
#guard_msgs in
#check HasMFDerivAt[s] f m f'

variable {σ : Π x : M, V x} {σ' : (x : E) → Trivial E E' x} {s : E → E'}
variable (X : (m : M) → TangentSpace I m) [IsManifold I 1 M] {x : M}

/--
info: mfderiv I (I.prod (modelWithCornersSelf 𝕜 E)) (fun m ↦ TotalSpace.mk' E m (X m))
  x : ContinuousLinearMap (RingHom.id 𝕜) (TangentSpace I x)
  (TangentSpace (I.prod (modelWithCornersSelf 𝕜 E)) (TotalSpace.mk' E x (X x)))
-/
#guard_msgs in
#check mfderiv% (T% X) x

variable {dXm : TangentSpace I x →L[𝕜] TangentSpace (I.prod 𝓘(𝕜, E)) (TotalSpace.mk' E x (X x))}

/--
info: HasMFDerivAt I (I.prod (modelWithCornersSelf 𝕜 E)) (fun m ↦ TotalSpace.mk' E m (X m)) x dXm : Prop
-/
#guard_msgs in
#check HasMFDerivAt% (T% X) x dXm

/--
info: HasMFDerivWithinAt I (I.prod (modelWithCornersSelf 𝕜 E)) (fun m ↦ TotalSpace.mk' E m (X m)) t x dXm : Prop
-/
#guard_msgs in
variable {t : Set M} in
#check HasMFDerivAt[t] (T% X) x dXm

/--
info: mfderiv I (I.prod (modelWithCornersSelf 𝕜 F)) (fun x ↦ TotalSpace.mk' F x (σ x))
  x : ContinuousLinearMap (RingHom.id 𝕜) (TangentSpace I x)
  (TangentSpace (I.prod (modelWithCornersSelf 𝕜 F)) (TotalSpace.mk' F x (σ x)))
-/
#guard_msgs in
#check mfderiv% (T% σ) x

variable {dσm : TangentSpace I x →L[𝕜] TangentSpace (I.prod 𝓘(𝕜, F)) (TotalSpace.mk' F x (σ x))}

/--
info: HasMFDerivAt I (I.prod (modelWithCornersSelf 𝕜 F)) (fun x ↦ TotalSpace.mk' F x (σ x)) x dσm : Prop
-/
#guard_msgs in
#check HasMFDerivAt% (T% σ) x dσm

/--
info: HasMFDerivWithinAt I (I.prod (modelWithCornersSelf 𝕜 F)) (fun x ↦ TotalSpace.mk' F x (σ x)) t x dσm : Prop
-/
#guard_msgs in
variable {t : Set M} in
#check HasMFDerivAt[t] (T% σ) x dσm

variable {t : Set E} {p : E}

/--
info: mfderivWithin (modelWithCornersSelf 𝕜 E) ((modelWithCornersSelf 𝕜 E).prod (modelWithCornersSelf 𝕜 E'))
  (fun x ↦ TotalSpace.mk' E' x (σ' x)) t
  p : ContinuousLinearMap (RingHom.id 𝕜) (TangentSpace (modelWithCornersSelf 𝕜 E) p)
  (TangentSpace ((modelWithCornersSelf 𝕜 E).prod (modelWithCornersSelf 𝕜 E')) (TotalSpace.mk' E' p (σ' p)))
-/
#guard_msgs in
#check mfderiv[t] (T% σ') p

variable {dσ'p : TangentSpace 𝓘(𝕜, E) p →L[𝕜] TangentSpace (𝓘(𝕜, E).prod 𝓘(𝕜, E')) (TotalSpace.mk' E' p (σ' p))}

/--
info: HasMFDerivAt (modelWithCornersSelf 𝕜 E) ((modelWithCornersSelf 𝕜 E).prod (modelWithCornersSelf 𝕜 E'))
  (fun x ↦ TotalSpace.mk' E' x (σ' x)) p dσ'p : Prop
-/
#guard_msgs in
#check HasMFDerivAt% (T% σ') p dσ'p

/--
info: HasMFDerivWithinAt (modelWithCornersSelf 𝕜 E) ((modelWithCornersSelf 𝕜 E).prod (modelWithCornersSelf 𝕜 E'))
  (fun x ↦ TotalSpace.mk' E' x (σ' x)) t p dσ'p : Prop
-/
#guard_msgs in
#check HasMFDerivAt[t] (T% σ') p dσ'p

/--
info: mfderivWithin (modelWithCornersSelf 𝕜 E) ((modelWithCornersSelf 𝕜 E).prod (modelWithCornersSelf 𝕜 E'))
  (fun x ↦ TotalSpace.mk' E' x (σ' x))
  t : (x : E) →
  ContinuousLinearMap (RingHom.id 𝕜) (TangentSpace (modelWithCornersSelf 𝕜 E) x)
    (TangentSpace ((modelWithCornersSelf 𝕜 E).prod (modelWithCornersSelf 𝕜 E')) (TotalSpace.mk' E' x (σ' x)))
-/
#guard_msgs in
#check mfderiv[t] (T% σ')

-- TODO: skipped the test about error messages (analogous to mfderiv(Within))

end HasMFDeriv
