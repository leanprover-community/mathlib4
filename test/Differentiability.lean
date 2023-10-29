/-
Copyright (c) 2023 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Adomas Baliuka, Moritz Doll
-/
import Mathlib.Tactic.Differentiability
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.ContDiffDef
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Series
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv
import Mathlib.Analysis.Calculus.Conformal.NormedSpace
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Geometry.Manifold.MFDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Geometry.Euclidean.Inversion.Calculus
import Mathlib.NumberTheory.ZetaFunction


/-!

Test suite for tactic `differentiability`.
Adapted from test suite for `continuity`, just as the tactic itself is adapted from `continuity`.

-/

set_option autoImplicit true
section basic

-- @[continuity]
-- theorem continuous_re : Continuous re
-- --
-- @[continuity]
-- theorem continuous_im : Continuous im
--
-- @[continuity]
-- theorem continuous_conj : Continuous (conj : ℂ → ℂ)
-- --
-- @[continuity]
-- theorem continuous_ofReal : Continuous ((↑) : ℝ → ℂ)

attribute [local aesop unsafe 90% apply (rule_sets [Differentiable])]
    Differentiable.sum  -- Mathlib.Analysis.Calculus.FDeriv.Add
    Differentiable.sub  -- Mathlib.Analysis.Calculus.FDeriv.Add
    Differentiable.add  -- Mathlib.Analysis.Calculus.FDeriv.Add
    Differentiable.mul  -- Mathlib.Analysis.Calculus.FDeriv.Mul
    Differentiable.star  -- Mathlib.Analysis.Calculus.FDeriv.Star
    Differentiable.smul  -- Mathlib.Analysis.Calculus.FDeriv.Mul
    Differentiable.comp

attribute [local differentiability]
    -- Differentiable.norm  -- Mathlib.Analysis.InnerProductSpace.Calculus
    Differentiable.norm_sq  -- Mathlib.Analysis.InnerProductSpace.Calculus
    -- SchwartzMap.differentiable  -- Mathlib.Analysis.Distribution.SchwartzSpace
    Differentiable.inner  -- Mathlib.Analysis.InnerProductSpace.Calculus
    -- AffineMap.differentiable  -- Mathlib.Analysis.Calculus.Deriv.AffineMap
    Differentiable.clm_comp  -- Mathlib.Analysis.Calculus.FDeriv.Mul
    Differentiable.clm_apply  -- Mathlib.Analysis.Calculus.FDeriv.Mul
    Differentiable.arsinh  -- Mathlib.Analysis.SpecialFunctions.Arsinh
    Differentiable.exp  -- Mathlib.Analysis.SpecialFunctions.ExpDeriv
    Differentiable.cexp  -- Mathlib.Analysis.SpecialFunctions.ExpDeriv
    Differentiable.log  -- Mathlib.Analysis.SpecialFunctions.Log.Deriv
    Real.differentiable_rpow_const  -- Mathlib.Analysis.SpecialFunctions.Pow.Deriv
    Differentiable.rpow_const  -- Mathlib.Analysis.SpecialFunctions.Pow.Deriv
    Differentiable.sin  -- Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
    Differentiable.cos  -- Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
    Real.differentiable_cos  -- Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
    Real.differentiable_cosh  -- Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
    Real.differentiable_sin  -- Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
    Real.differentiable_sinh  -- Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
    Differentiable.ccos  -- Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
    Differentiable.ccosh  -- Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
    Differentiable.cosh  -- Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
    Differentiable.csin  -- Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
    Differentiable.csinh  -- Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
    Differentiable.sinh  -- Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
    Real.differentiable_arsinh  -- Mathlib.Analysis.SpecialFunctions.Arsinh
    Complex.differentiable_cos  -- Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
    Complex.differentiable_cosh  -- Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
    Complex.differentiable_sin  -- Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
    Complex.differentiable_sinh  -- Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
    Differentiable.sqrt  -- Mathlib.Analysis.SpecialFunctions.Sqrt
    Polynomial.differentiable  -- Mathlib.Analysis.Calculus.Deriv.Polynomial
    Polynomial.differentiable_aeval  -- Mathlib.Analysis.Calculus.Deriv.Polynomial
    differentiable_id
    differentiable_id'
    differentiable_const  -- Mathlib.Analysis.Calculus.FDeriv.Basic
    Differentiable.dist  -- Mathlib.Analysis.InnerProductSpace.Calculus
    differentiable_fst  -- Mathlib.Analysis.Calculus.FDeriv.Prod
    differentiable_snd  -- Mathlib.Analysis.Calculus.FDeriv.Prod
    Differentiable.fst  -- Mathlib.Analysis.Calculus.FDeriv.Prod
    Differentiable.snd  -- Mathlib.Analysis.Calculus.FDeriv.Prod
    Differentiable.const_mul  -- Mathlib.Analysis.Calculus.FDeriv.Mul
    Differentiable.mul_const  -- Mathlib.Analysis.Calculus.FDeriv.Mul
    Differentiable.pow  -- Mathlib.Analysis.Calculus.FDeriv.Mul
    Differentiable.inverse  -- Mathlib.Analysis.Calculus.FDeriv.Mul
    Differentiable.inv'  -- Mathlib.Analysis.Calculus.FDeriv.Mul
    Differentiable.smul_const  -- Mathlib.Analysis.Calculus.FDeriv.Mul
    Differentiable.neg  -- Mathlib.Analysis.Calculus.FDeriv.Add
    Differentiable.const_sub  -- Mathlib.Analysis.Calculus.FDeriv.Add
    Differentiable.sub_const  -- Mathlib.Analysis.Calculus.FDeriv.Add
    Differentiable.add_const  -- Mathlib.Analysis.Calculus.FDeriv.Add
    Differentiable.const_add  -- Mathlib.Analysis.Calculus.FDeriv.Add
    Differentiable.const_smul  -- Mathlib.Analysis.Calculus.FDeriv.Add
    Differentiable.div_const  -- Mathlib.Analysis.Calculus.Deriv.Mul
    Differentiable.inv  -- Mathlib.Analysis.Calculus.Deriv.Inv
    Differentiable.div  -- Mathlib.Analysis.Calculus.Deriv.Inv
    differentiable_neg  -- Mathlib.Analysis.Calculus.Deriv.Add
    Real.differentiable_exp  -- Mathlib.Analysis.SpecialFunctions.ExpDeriv
    Complex.differentiable_exp  -- Mathlib.Analysis.SpecialFunctions.ExpDeriv
    Differentiable.clog  -- Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
    Differentiable.rpow  -- Mathlib.Analysis.SpecialFunctions.Pow.Deriv
    Real.differentiable_arctan  -- Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
    Differentiable.arctan  -- Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv



set_option trace.aesop true

section RealExamplesAndTests
open Real

example : Differentiable ℝ (fun (x : ℝ) ↦ x) := by
    differentiability

example : Differentiable ℝ (fun (x : ℝ) ↦ sin x) := by
    differentiability

example : Differentiable ℝ (fun (x : ℝ) ↦ exp x) := by
    differentiability

example : Differentiable ℝ (fun (x : ℝ) ↦ exp x + sin x) := by
    differentiability

example : Differentiable ℝ (fun x ↦ x * 999 *  cosh x + 3) := by
    differentiability

-- problem: the tactic splits trig functions into complex exponentials
-- and then fails...
example : Differentiable ℝ (fun x ↦ ( sin (sin x))) := by
    differentiability


example : Differentiable ℝ (fun (x : ℝ) ↦
(sin x * exp x + 3) * 999 * (cosh (cos x)))
:= by
    differentiability

-- section ComplexExamplesAndTests
-- open Complex

-- example : Differentiable ℂ (fun (x : ℂ) ↦
-- (sin x * exp x + 3) * 999 * (cosh (cos x)))
-- := by
--     sorry


-- section CopiedOverFromContinuity

-- variable [IsROrC 𝕜]
--     {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
--     {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
--     {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]


-- example : Differentiable 𝕜 (id : E → E) := by differentiability

-- -- example {f : F → G} {g : E → F} (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g) :
-- --   Differentiable 𝕜 (fun x => f (g x)) := by
-- --     differentiability
-- --     sorry

-- -- example {f : X → Y} {g : Y → X} (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g) :
-- --   Differentiable 𝕜 (f ∘ g ∘ f) := by differentiability

-- -- example {f : X → Y} {g : Y → X} (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g) :
-- --   Differentiable 𝕜 (f ∘ g) := by differentiability

-- -- example (y : Y) : Differentiable 𝕜 (fun (_ : X) ↦ y) := by differentiability

-- -- example {f : Y → Y} (y : Y) : Differentiable 𝕜 (f ∘ (fun (_ : X) => y)) := by differentiability

-- -- example {g : X → X} (y : Y) : Differentiable 𝕜 ((fun _ ↦ y) ∘ g) := by differentiability

-- -- example {f : X → Y} (x : X) : Differentiable 𝕜 (fun (_ : X) ↦ f x) := by differentiability


-- -- Todo: more interesting examples


-- example (b : E) : Differentiable 𝕜 (fun _ : F => b) := by differentiability

-- -- example (f : C(X, Y)) (g : C(Y, Z)) : Differentiable 𝕜 (g ∘ f) := by differentiability

-- -- example (f : C(X, Y)) (g : C(X, Z)) : Differentiable 𝕜 (fun x => (f x, g x)) := by differentiability

-- -- example (f : C(X, Y)) (g : C(W, Z)) : Differentiable 𝕜 (Prod.map f g) := --by differentiability
-- --   f.continuous.prod_map g.continuous

-- -- example (f : ∀ i, C(X, X' i)) : Differentiable 𝕜 (fun a i => f i a) := by differentiability

-- -- example (s : Set X) (f : C(X, Y)) : Differentiable 𝕜 (f ∘ ((↑) : s → X)) := by differentiability

-- -- Examples taken from `Topology.CompactOpen`:

-- -- example (b : Y) : Differentiable (Function.const X b) := --by differentiability
-- --   continuous_const

-- -- example (b : Y) : Differentiable (@Prod.mk Y X b) := by differentiability

-- -- example (f : C(X × Y, Z)) (a : X) : Differentiable (Function.curry f a) := --by differentiability
-- --   f.continuous.comp (continuous_const.prod_mk continuous_id)

-- -- /-! Some tests of the `comp_of_eq` lemmas -/

-- -- example {α β : Type _} [TopologicalSpace α] [TopologicalSpace β] {x₀ : α} (f : α → α → β)
-- --   (hf : DifferentiableAt (Function.uncurry f) (x₀, x₀)) :
-- --   DifferentiableAt (λ x ↦ f x x) x₀ := by
-- --   fail_if_success { exact hf.comp (continuousAt_id.prod continuousAt_id) }
-- --   exact hf.comp_of_eq (continuousAt_id.prod continuousAt_id) rfl
