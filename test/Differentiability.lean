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


attribute [local differentiability]
        -- -- Counterexamples/SorgenfreyLine.lean
        -- @[continuity]
        -- theorem continuous_toReal : Continuous toReal := sorry

        -- -- Mathlib/AlgebraicGeometry/Scheme.lean
        -- @[continuity]
        -- lemma Hom.continuous {X Y : Scheme} (f : X ⟶ Y) : Continuous f.1.base := f.1.base.2

        -- -- Mathlib/AlgebraicTopology/FundamentalGroupoid/Basic.lean
        -- @[continuity]
        -- theorem continuous_reflTransSymmAux : Continuous reflTransSymmAux := sorry

        -- @[continuity]
        -- theorem continuous_transReflReparamAux : Continuous transReflReparamAux := sorry

        -- @[continuity]
        -- theorem continuous_transAssocReparamAux : Continuous transAssocReparamAux := sorry

        -- -- Mathlib/AlgebraicTopology/TopologicalSimplex.lean
        -- @[continuity]
        -- theorem continuous_toTopMap {x y : SimplexCategory} (f : x ⟶ y) : Continuous (toTopMap f) := sorry

        -- -- Mathlib/Analysis/Complex/Basic.lean
        -- @[continuity]
        -- theorem continuous_abs : Continuous abs := sorry


    -- TODO reconsider, added without analogue
    Differentiable.norm  -- Mathlib.Analysis.InnerProductSpace.Calculus
-- @[continuity]
-- theorem continuous_normSq : Continuous normSq := sorry
    Differentiable.norm_sq  -- Mathlib.Analysis.InnerProductSpace.Calculus

-- @[continuity]
-- theorem continuous_re : Continuous re := sorry
-- did not find but seems useful as `Differentiable ℝ`?
-- `differentiable_re`

-- @[continuity]
-- theorem continuous_im : Continuous im := sorry
-- did not find but seems useful as `Differentiable ℝ`?
-- `differentiable_im`

-- @[continuity]
-- theorem continuous_conj : Continuous (conj : ℂ → ℂ) := sorry
-- did not find but seems useful as `Differentiable ℝ`?
-- `differentiable_conj`

-- @[continuity]
-- theorem continuous_ofReal : Continuous ((↑) : ℝ → ℂ) := sorry
-- did not find but seems useful as `Differentiable ℝ`?
-- `differentiable_ofReal`

-- Mathlib/Analysis/Distribution/SchwartzSpace.lean
-- @[continuity]
-- protected theorem continuous (f : 𝓢(E, F)) : Continuous f := sorry
    SchwartzMap.differentiable  -- Mathlib.Analysis.Distribution.SchwartzSpace

-- Mathlib/Analysis/Fourier/FourierTransform.lean
-- @[continuity]
-- theorem continuous_fourierChar : Continuous Real.fourierChar := sorry
-- `differentiable_fourierChar`

-- Mathlib/Analysis/InnerProductSpace/Basic.lean
-- @[continuity]
-- theorem Continuous.inner (hf : Continuous f) (hg : Continuous g) : Continuous fun t => ⟪f t, g t⟫ := sorry
    Differentiable.inner  -- Mathlib.Analysis.InnerProductSpace.Calculus

        -- Mathlib/Analysis/Normed/Group/Basic.lean
        -- @[to_additive (attr := continuity) continuous_norm]
        -- theorem continuous_norm' : Continuous fun a : E => ‖a‖ := sorry

        -- @[to_additive (attr := continuity) continuous_nnnorm]
        -- theorem continuous_nnnorm' : Continuous fun a : E => ‖a‖₊ := sorry

        -- -- Mathlib/Analysis/Normed/Group/Hom.lean
        -- @[continuity]
        -- protected theorem continuous (f : NormedAddGroupHom V₁ V₂) : Continuous f := sorry

        -- -- Mathlib/Analysis/NormedSpace/AddTorsorBases.lean
        -- @[continuity]
        -- theorem continuous_barycentric_coord (i : ι) : Continuous (b.coord i) := sorry

-- Mathlib/Analysis/NormedSpace/AffineIsometry.lean
-- @[continuity]
-- protected theorem continuous : Continuous f := sorry
AffineMap.differentiable  -- Mathlib.Analysis.Calculus.Deriv.AffineMap

        -- -- Mathlib/Analysis/NormedSpace/Banach.lean
        -- @[continuity]
        -- theorem continuous_symm (e : E ≃ₗ[𝕜] F) (h : Continuous e) : Continuous e.symm := sorry

-- Mathlib/Analysis/NormedSpace/BoundedLinearMaps.lean
-- @[continuity]
-- theorem Continuous.clm_comp {X} [TopologicalSpace X] {g : X → F →L[𝕜] G} {f : X → E →L[𝕜] F}
    Differentiable.clm_comp  -- Mathlib.Analysis.Calculus.FDeriv.Mul

-- @[continuity]
-- theorem Continuous.clm_apply {X} [TopologicalSpace X] {f : X → (E →L[𝕜] F)} {g : X → E}
    Differentiable.clm_apply  -- Mathlib.Analysis.Calculus.FDeriv.Mul

        -- Mathlib/Analysis/NormedSpace/CompactOperator.lean
        -- @[continuity]
        -- theorem IsCompactOperator.continuous {f : M₁ →ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) :

-- Mathlib/Analysis/NormedSpace/Exponential.lean
-- @[continuity]
-- theorem exp_continuous : Continuous (exp 𝕂 : 𝔸 → 𝔸) := sorry
-- TODO might work, especially in a Banach space? `BanachSpace/NormedSpace.exp_differentiable`

        -- -- Mathlib/Analysis/NormedSpace/HomeomorphBall.lean
        -- @[continuity]
        -- theorem continuous_univBall (c : P) (r : ℝ) : Continuous (univBall c r) := sorry


-- -- Mathlib/Analysis/NormedSpace/LinearIsometry.lean
-- @[continuity]
-- protected theorem continuous [SemilinearIsometryClass 𝓕 σ₁₂ E E₂] (f : 𝓕) : Continuous f := sorry
-- @[continuity]
-- protected theorem continuous : Continuous f := sorry
-- TODO both of these: maybe `BanachSpace/NormedSpace.LinearIsometry.differentiable`?


        -- -- Mathlib/Analysis/NormedSpace/PiLp.lean
        -- @[continuity]
        -- theorem continuous_equiv [∀ i, UniformSpace (β i)] : Continuous (WithLp.equiv p (∀ i, β i)) := sorry

        -- @[continuity]
        -- theorem continuous_equiv_symm [∀ i, UniformSpace (β i)] :

        -- -- Mathlib/Analysis/NormedSpace/ProdLp.lean
        -- @[continuity]
        -- theorem prod_continuous_equiv : Continuous (WithLp.equiv p (α × β)) := sorry

        -- @[continuity]
        -- theorem prod_continuous_equiv_symm : Continuous (WithLp.equiv p (α × β)).symm := sorry

        -- -- Mathlib/Analysis/ODE/PicardLindelof.lean
        -- @[continuity]
        -- theorem continuous_proj : Continuous v.proj := sorry

        -- I don't know (and don't want to study right now) how differentiability works with Quaternions
        -- There don't seem to be any theorems about it at the moment.
        -- -- Mathlib/Analysis/Quaternion.lean
        -- @[continuity]
        -- theorem continuous_coe : Continuous (coe : ℝ → ℍ) := sorry

        -- @[continuity]
        -- theorem continuous_normSq : Continuous (normSq : ℍ → ℝ) := sorry

        -- @[continuity]
        -- theorem continuous_re : Continuous fun q : ℍ => q.re := sorry

        -- @[continuity]
        -- theorem continuous_imI : Continuous fun q : ℍ => q.imI := sorry

        -- @[continuity]
        -- theorem continuous_imJ : Continuous fun q : ℍ => q.imJ := sorry

        -- @[continuity]
        -- theorem continuous_imK : Continuous fun q : ℍ => q.imK := sorry

        -- @[continuity]
        -- theorem continuous_im : Continuous fun q : ℍ => q.im := sorry

-- Mathlib/Analysis/SpecialFunctions/Arsinh.lean
-- @[continuity]
-- theorem continuous_arsinh : Continuous arsinh := sorry
    Differentiable.arsinh  -- Mathlib.Analysis.SpecialFunctions.Arsinh

-- Mathlib/Analysis/SpecialFunctions/Exp.lean
-- @[continuity]
-- theorem continuous_exp : Continuous exp := sorry
-- @[continuity]
-- theorem continuous_exp : Continuous exp := sorry
    Differentiable.exp  -- Mathlib.Analysis.SpecialFunctions.ExpDeriv
    Differentiable.cexp  -- Mathlib.Analysis.SpecialFunctions.ExpDeriv


-- Mathlib/Analysis/SpecialFunctions/Log/Basic.lean
-- @[continuity]
-- theorem continuous_log : Continuous fun x : { x : ℝ // x ≠ 0 } => log x := sorry
-- @[continuity]
-- theorem continuous_log' : Continuous fun x : { x : ℝ // 0 < x } => log x := sorry
    -- TODO check if the `aesop` tactic can make use of this (has hypothesis!)
    Differentiable.log  -- Mathlib.Analysis.SpecialFunctions.Log.Deriv

-- Mathlib/Analysis/SpecialFunctions/Pow/Continuity.lean
-- @[continuity]
-- theorem continuous_rpow_const {y : ℝ} : Continuous fun a : ℝ≥0∞ => a ^ y := sorry
    Real.differentiable_rpow_const  -- Mathlib.Analysis.SpecialFunctions.Pow.Deriv
    Differentiable.rpow_const  -- Mathlib.Analysis.SpecialFunctions.Pow.Deriv

-- -- Mathlib/Analysis/SpecialFunctions/Trigonometric/Angle.lean
-- @[continuity]
-- theorem continuous_coe : Continuous ((↑) : ℝ → Angle) := sorry
-- TODO `Trigonometric.Angle.differentiable_coe`


-- @[continuity]
-- theorem continuous_sin : Continuous sin := sorry
    Differentiable.sin  -- Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

-- @[continuity]
-- theorem continuous_cos : Continuous cos := sorry
    Differentiable.cos  -- Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

-- Mathlib/Analysis/SpecialFunctions/Trigonometric/Arctan.lean
-- @[continuity]
-- theorem continuous_tan : Continuous fun x : {x | cos x ≠ 0} => tan x := sorry

-- @[continuity]
-- theorem continuous_arctan : Continuous arctan := sorry

-- -- Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean
-- @[continuity]
-- theorem continuous_sin : Continuous sin := sorry

-- @[continuity]
-- theorem continuous_cos : Continuous cos := sorry

-- @[continuity]
-- theorem continuous_sinh : Continuous sinh := sorry

-- @[continuity]
-- theorem continuous_cosh : Continuous cosh := sorry

-- @[continuity]
-- theorem continuous_sin : Continuous sin := sorry

-- @[continuity]
-- theorem continuous_cos : Continuous cos := sorry

-- @[continuity]
-- theorem continuous_sinh : Continuous sinh := sorry

-- @[continuity]
-- theorem continuous_cosh : Continuous cosh := sorry

-- Mathlib/Analysis/SpecialFunctions/Trigonometric/Complex.lean
-- @[continuity]
-- theorem continuous_tan : Continuous fun x : {x | cos x ≠ 0} => tan x := sorry

-- Mathlib/Analysis/SpecialFunctions/Trigonometric/Inverse.lean
-- @[continuity]
-- theorem continuous_arcsin : Continuous arcsin := sorry

-- @[continuity]
-- theorem continuous_arccos : Continuous arccos := sorry

-- -- Mathlib/Data/IsROrC/Basic.lean
-- @[continuity]
-- theorem continuous_re : Continuous (re : K → ℝ) := sorry

-- @[continuity]
-- theorem continuous_im : Continuous (im : K → ℝ) := sorry

-- @[continuity]
-- theorem continuous_conj : Continuous (conj : K → K) := sorry

-- @[continuity]
-- theorem continuous_ofReal : Continuous (ofReal : ℝ → K) := sorry

-- @[continuity]
-- theorem continuous_normSq : Continuous (normSq : K → ℝ) := sorry
-- just add all trigonometric ones here
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

-- Mathlib/Data/Real/Sqrt.lean
-- @[continuity]
-- theorem continuous_sqrt : Continuous sqrt := sorry

-- @[continuity]
-- theorem Continuous.sqrt (h : Continuous f) : Continuous fun x => sqrt (f x) := sorry
    Differentiable.sqrt  -- Mathlib.Analysis.SpecialFunctions.Sqrt
    -- TODO check if `aesop` can use

        -- Mathlib/Dynamics/Flow.lean
        -- @[continuity]
        -- protected theorem continuous {β : Type*} [TopologicalSpace β] {t : β → τ} (ht : Continuous t)

        -- @[continuity]
        -- theorem continuous_toFun (t : τ) : Continuous (ϕ.toFun t) := sorry

        -- -- Mathlib/Geometry/Manifold/Diffeomorph.lean
        -- @[continuity]
        -- protected theorem continuous (h : M ≃ₘ^n⟮I, I'⟯ M') : Continuous h := sorry

        -- -- Mathlib/Geometry/Manifold/SmoothManifoldWithCorners.lean
        -- @[continuity]
        -- protected theorem continuous : Continuous I := sorry

        -- @[continuity]
        -- theorem continuous_symm : Continuous I.symm := sorry

        -- -- Mathlib/MeasureTheory/Integral/Bochner.lean
        -- @[continuity]
        -- theorem continuous_integral : Continuous fun f : α →₁[μ] E => integral f := sorry

        -- @[continuity]
        -- theorem continuous_integral : Continuous fun f : α →₁[μ] G => ∫ a, f a ∂μ := sorry

        -- -- Mathlib/MeasureTheory/Integral/CircleIntegral.lean
        -- @[continuity]
        -- theorem continuous_circleMap (c : ℂ) (R : ℝ) : Continuous (circleMap c R) := sorry

        -- -- Mathlib/MeasureTheory/Integral/SetIntegral.lean
        -- @[continuity]
        -- theorem continuous_set_integral [NormedSpace ℝ E] (s : Set α) :

        -- -- Mathlib/MeasureTheory/Integral/SetToL1.lean
        -- @[continuity]
        -- theorem continuous_setToFun (hT : DominatedFinMeasAdditive μ T C) :

        -- -- Mathlib/Topology/Algebra/Affine.lean
        -- @[continuity]
        -- theorem lineMap_continuous [TopologicalSpace R] [ContinuousSMul R F] {p v : F} :

        -- @[continuity]
        -- theorem homothety_continuous (x : F) (t : R) : Continuous <| homothety x t := sorry

        -- -- Mathlib/Topology/Algebra/Algebra.lean
        -- @[continuity]
        -- theorem continuous_algebraMap [ContinuousSMul R A] : Continuous (algebraMap R A) := sorry

        -- -- Mathlib/Topology/Algebra/ConstMulAction.lean
        -- @[to_additive (attr := continuity)]
        -- theorem Continuous.const_smul (hg : Continuous g) (c : M) : Continuous fun x => c • g x := sorry

        -- -- Mathlib/Topology/Algebra/Constructions.lean
        -- @[to_additive (attr := continuity)]
        -- theorem continuous_unop : Continuous (unop : Mᵐᵒᵖ → M) := sorry

        -- @[to_additive (attr := continuity)]
        -- theorem continuous_op : Continuous (op : M → Mᵐᵒᵖ) := sorry

        -- -- Mathlib/Topology/Algebra/ContinuousAffineMap.lean
        -- @[continuity]
        -- protected theorem continuous (f : P →A[R] Q) : Continuous f := f.2

        -- -- Mathlib/Topology/Algebra/Group/Basic.lean
        -- @[to_additive (attr := continuity)]
        -- class ContinuousInv (G : Type u) [TopologicalSpace G] [Inv G] : Prop where

        -- @[to_additive (attr := continuity)]
        -- theorem Continuous.inv (hf : Continuous f) : Continuous fun x => (f x)⁻¹ := sorry

        -- @[to_additive (attr := continuity)]
        -- theorem continuous_zpow : ∀ z : ℤ, Continuous fun a : G => a ^ z

        -- @[to_additive (attr := continuity)]
        -- theorem Continuous.zpow {f : α → G} (h : Continuous f) (z : ℤ) : Continuous fun b => f b ^ z := sorry

        -- @[to_additive (attr := continuity) sub]
        -- theorem Continuous.div' (hf : Continuous f) (hg : Continuous g) : Continuous fun x => f x / g x := sorry

        -- @[to_additive (attr := continuity) continuous_sub_left]
        -- theorem continuous_div_left' (a : G) : Continuous fun b : G => a / b := sorry

        -- @[to_additive (attr := continuity) continuous_sub_right]
        -- theorem continuous_div_right' (a : G) : Continuous fun b : G => b / a := sorry

        -- -- Mathlib/Topology/Algebra/GroupCompletion.lean
        -- @[continuity]
        -- theorem AddMonoidHom.continuous_extension [CompleteSpace β] [SeparatedSpace β] (f : α →+ β)

        -- @[continuity]
        -- theorem AddMonoidHom.continuous_completion (f : α →+ β) (hf : Continuous f) :

        -- -- Mathlib/Topology/Algebra/GroupWithZero.lean
        -- @[continuity]
        -- theorem Continuous.div_const (hf : Continuous f) (y : G₀) : Continuous fun x => f x / y := sorry

        -- @[continuity]
        -- theorem Continuous.inv₀ (hf : Continuous f) (h0 : ∀ x, f x ≠ 0) : Continuous fun x => (f x)⁻¹ := sorry

        -- @[continuity]
        -- theorem Continuous.div (hf : Continuous f) (hg : Continuous g) (h₀ : ∀ x, g x ≠ 0) :

        -- @[continuity]
        -- theorem Continuous.zpow₀ (hf : Continuous f) (m : ℤ) (h0 : ∀ a, f a ≠ 0 ∨ 0 ≤ m) :

        -- -- Mathlib/Topology/Algebra/Module/Alternating.lean
        -- @[continuity]
        -- theorem coe_continuous : Continuous f := f.cont

        -- -- Mathlib/Topology/Algebra/Module/Basic.lean
        -- @[continuity]
        -- protected theorem continuous (f : M₁ →SL[σ₁₂] M₂) : Continuous f := sorry

        -- @[continuity]
        -- protected theorem continuous (e : M₁ ≃SL[σ₁₂] M₂) : Continuous (e : M₁ → M₂) := sorry

        -- -- Mathlib/Topology/Algebra/Module/Multilinear.lean
        -- @[continuity]
        -- theorem coe_continuous : Continuous (f : (∀ i, M₁ i) → M₂) := sorry

        -- -- Mathlib/Topology/Algebra/Monoid.lean
        -- @[to_additive (attr := continuity)]
        -- theorem continuous_one [TopologicalSpace M] [One M] : Continuous (1 : X → M) := sorry

        -- @[to_additive (attr := continuity)]
        -- theorem continuous_mul : Continuous fun p : M × M => p.1 * p.2 := sorry

        -- @[to_additive (attr := continuity)]
        -- theorem Continuous.mul {f g : X → M} (hf : Continuous f) (hg : Continuous g) :

        -- @[to_additive (attr := continuity)]
        -- theorem continuous_mul_left (a : M) : Continuous fun b : M => a * b := sorry

        -- @[to_additive (attr := continuity)]
        -- theorem continuous_mul_right (a : M) : Continuous fun b : M => b * a := sorry

        -- @[to_additive (attr := continuity)]
        -- theorem continuous_list_prod {f : ι → X → M} (l : List ι) (h : ∀ i ∈ l, Continuous (f i)) :

        -- @[to_additive (attr := continuity)]
        -- theorem continuous_pow : ∀ n : ℕ, Continuous fun a : M => a ^ n

        -- @[to_additive (attr := continuity)]
        -- theorem Continuous.pow {f : X → M} (h : Continuous f) (n : ℕ) : Continuous fun b => f b ^ n := sorry

        -- @[to_additive (attr := continuity)]
        -- theorem continuous_multiset_prod {f : ι → X → M} (s : Multiset ι) :

        -- @[to_additive (attr := continuity)]
        -- theorem continuous_finset_prod {f : ι → X → M} (s : Finset ι) :

        -- -- Mathlib/Topology/Algebra/MulAction.lean
        -- @[to_additive (attr := continuity)]
        -- theorem Continuous.smul (hf : Continuous f) (hg : Continuous g) : Continuous fun x => f x • g x := sorry

        -- -- Mathlib/Topology/Algebra/Order/Group.lean
        -- @[continuity]
        -- theorem continuous_abs : Continuous (abs : G → G) := sorry

        -- -- Mathlib/Topology/Algebra/Order/ProjIcc.lean
        -- @[continuity]
        -- theorem continuous_projIcc : Continuous (projIcc a b h) := sorry

        -- @[continuity]
        -- protected theorem Continuous.Icc_extend' {f : Icc a b → β} (hf : Continuous f) :

        -- -- Mathlib/Topology/Algebra/Polynomial.lean
        -- @[continuity]
        -- protected theorem continuous_eval₂ [Semiring S] (p : S[X]) (f : S →+* R) :

-- @[continuity]
-- protected theorem continuous : Continuous fun x => p.eval x := sorry
    Polynomial.differentiable  -- Mathlib.Analysis.Calculus.Deriv.Polynomial

-- @[continuity]
-- protected theorem continuous_aeval : Continuous fun x : A => aeval x p := sorry
    Polynomial.differentiable_aeval  -- Mathlib.Analysis.Calculus.Deriv.Polynomial

-- Mathlib/Topology/Algebra/Star.lean
-- @[continuity]
-- theorem Continuous.star (hf : Continuous f) : Continuous fun x => star (f x) := sorry
    Differentiable.star

-- Mathlib/Topology/Basic.lean
-- @[continuity]
-- theorem continuous_id : Continuous (id : α → α) := sorry
    differentiable_id

-- @[continuity]
-- theorem continuous_id' : Continuous (fun (x : α) => x) := continuous_id
    differentiable_id'

-- @[continuity]
-- theorem Continuous.comp' {g : β → γ} {f : α → β} (hg : Continuous g) (hf : Continuous f) :
    Differentiable.comp

-- @[continuity]
-- theorem continuous_const {b : β} : Continuous fun _ : α => b := sorry
    differentiable_const  -- Mathlib.Analysis.Calculus.FDeriv.Basic


        -- -- Mathlib/Topology/CompactOpen.lean
        -- @[continuity]
        -- theorem continuous_eval_const (a : α) :

        -- -- Mathlib/Topology/Compactification/OnePoint.lean
        -- @[continuity]
        -- theorem continuous_coe : Continuous ((↑) : X → OnePoint X) := sorry

        -- -- Mathlib/Topology/Connected/Basic.lean
        -- @[continuity]
        -- theorem continuous_coe : Continuous (mk : α → ConnectedComponents α) := sorry

        -- -- Mathlib/Topology/Connected/PathConnected.lean
        -- @[continuity]
        -- protected theorem continuous : Continuous γ := sorry

        -- @[continuity]
        -- theorem _root_.Continuous.path_eval {Y} [TopologicalSpace Y] {f : Y → Path x y} {g : Y → I}

        -- @[continuity]
        -- theorem continuous_extend : Continuous γ.extend := sorry

        -- @[continuity]
        -- theorem symm_continuous_family {X ι : Type*} [TopologicalSpace X] [TopologicalSpace ι]

        -- @[continuity]
        -- theorem continuous_symm : Continuous (symm : Path x y → Path y x) := sorry

        -- @[continuity]
        -- theorem continuous_uncurry_extend_of_continuous_family {X ι : Type*} [TopologicalSpace X]

        -- @[continuity]
        -- theorem trans_continuous_family {X ι : Type*} [TopologicalSpace X] [TopologicalSpace ι]

        -- @[continuity]
        -- theorem _root_.Continuous.path_trans {f : Y → Path x y} {g : Y → Path y z} :

        -- @[continuity]
        -- theorem continuous_trans {x y z : X} : Continuous fun ρ : Path x y × Path y z => ρ.1.trans ρ.2 := sorry

        -- @[continuity]
        -- theorem truncate_continuous_family {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b) :

        -- @[continuity]
        -- theorem truncate_const_continuous_family {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b)

        -- -- Mathlib/Topology/Connected/TotallyDisconnected.lean
        -- @[continuity]
        -- theorem Continuous.connectedComponentsLift_continuous (h : Continuous f) :

        -- -- Mathlib/Topology/Constructions.lean
        -- @[continuity]
        -- theorem continuous_fst : Continuous (@Prod.fst α β) := sorry

        -- @[continuity]
        -- theorem continuous_snd : Continuous (@Prod.snd α β) := sorry

        -- @[continuity]
        -- theorem Continuous.prod_mk {f : γ → α} {g : γ → β} (hf : Continuous f) (hg : Continuous g) :

        -- @[continuity]
        -- theorem Continuous.Prod.mk (a : α) : Continuous fun b : β => (a, b) := sorry

        -- @[continuity]
        -- theorem Continuous.Prod.mk_left (b : β) : Continuous fun a : α => (a, b) := sorry

        -- @[continuity]
        -- theorem Continuous.prod_map {f : γ → α} {g : δ → β} (hf : Continuous f) (hg : Continuous g) :

        -- @[continuity]
        -- theorem Continuous.sum_elim {f : α → γ} {g : β → γ} (hf : Continuous f) (hg : Continuous g) :

        -- @[continuity]
        -- theorem continuous_isLeft : Continuous (isLeft : α ⊕ β → Bool) := sorry

        -- @[continuity]
        -- theorem continuous_isRight : Continuous (isRight : α ⊕ β → Bool) := sorry

        -- @[continuity]
        -- -- porting note: the proof was `continuous_sup_rng_left continuous_coinduced_rng`

        -- @[continuity]
        -- -- porting note: the proof was `continuous_sup_rng_right continuous_coinduced_rng`

        -- @[continuity]
        -- theorem Continuous.sum_map {f : α → β} {g : γ → δ} (hf : Continuous f) (hg : Continuous g) :

        -- @[continuity]
        -- theorem continuous_subtype_val : Continuous (@Subtype.val α p) := sorry

        -- @[continuity]
        -- theorem Continuous.subtype_mk {f : β → α} (h : Continuous f) (hp : ∀ x, p (f x)) :

        -- @[continuity]
        -- theorem Continuous.codRestrict {f : α → β} {s : Set β} (hf : Continuous f) (hs : ∀ a, f a ∈ s) :

        -- @[continuity]
        -- theorem Continuous.restrict {f : α → β} {s : Set α} {t : Set β} (h1 : MapsTo f s t)

        -- @[continuity]
        -- theorem Continuous.restrictPreimage {f : α → β} {s : Set β} (h : Continuous f) :

        -- @[continuity]
        -- theorem continuous_quot_mk : Continuous (@Quot.mk α r) := sorry

        -- @[continuity]
        -- theorem continuous_quot_lift {f : α → β} (hr : ∀ a b, r a b → f a = f b) (h : Continuous f) :

        -- @[continuity] theorem Continuous.quotient_map' {t : Setoid β} {f : α → β} (hf : Continuous f)
        --     (H : (s.r ⇒ t.r) f f) : Continuous (Quotient.map' f H) := sorry

        -- @[continuity]
        -- theorem continuous_pi (h : ∀ i, Continuous fun a => f a i) : Continuous f := sorry

        -- @[continuity]
        -- theorem continuous_apply (i : ι) : Continuous fun p : ∀ i, π i => p i := sorry

        -- @[continuity]
        -- theorem continuous_apply_apply {ρ : κ → ι → Type*} [∀ j i, TopologicalSpace (ρ j i)] (j : κ)

        -- @[continuity]
        -- theorem continuous_update [DecidableEq ι] (i : ι) :

        -- -- porting note: todo: restore @[continuity]
        -- @[to_additive "`Pi.single i x` is continuous in `x`."]

        -- @[continuity]
        -- theorem continuous_sigmaMk {i : ι} : Continuous (@Sigma.mk ι σ i) := sorry

        -- @[continuity]
        -- theorem continuous_sigma {f : Sigma σ → α} (hf : ∀ i, Continuous fun a => f ⟨i, a⟩) :

        -- @[continuity]
        -- theorem Continuous.sigma_map {f₁ : ι → κ} {f₂ : ∀ i, σ i → τ (f₁ i)} (hf : ∀ i, Continuous (f₂ i)) :

        -- @[continuity]
        -- theorem continuous_uLift_down [TopologicalSpace α] : Continuous (ULift.down : ULift.{v, u} α → α) := sorry

        -- @[continuity]
        -- theorem continuous_uLift_up [TopologicalSpace α] : Continuous (ULift.up : α → ULift.{v, u} α) := sorry

        -- -- Mathlib/Topology/ContinuousFunction/Basic.lean
        -- @[continuity]
        -- theorem continuous_set_coe (s : Set C(α, β)) (f : s) : Continuous (f : α → β) := sorry

        -- -- Mathlib/Topology/ContinuousFunction/Bounded.lean
        -- @[continuity]
        -- theorem continuous_eval_const {x : α} : Continuous fun f : α →ᵇ β => f x := sorry

        -- @[continuity]
        -- theorem continuous_eval : Continuous fun p : (α →ᵇ β) × α => p.1 p.2 := sorry

        -- -- Mathlib/Topology/ContinuousFunction/Compact.lean
        -- @[continuity]
        -- theorem continuous_eval : Continuous fun p : C(α, β) × α => p.1 p.2 := sorry

-- Mathlib/Topology/FiberBundle/Basic.lean
-- @[continuity]
-- theorem continuous_proj : Continuous (π F E) := sorry
    -- TODO for smooth (or C^k) fiber bundles, this should exist? `FiberBundle.differentiable_proj`

        -- @[continuity]
        -- theorem continuous_totalSpaceMk (b : B) :

        -- @[continuity]
        -- theorem continuous_totalSpaceMk (b : B) :

        -- -- Mathlib/Topology/Filter.lean
        -- @[continuity]
        -- theorem continuous_nhds : Continuous (𝓝 : X → Filter X) := sorry

        -- -- Mathlib/Topology/Homeomorph.lean
        -- @[continuity]
        -- protected theorem continuous (h : X ≃ₜ Y) : Continuous h := sorry

        -- @[continuity]
        -- protected theorem continuous_symm (h : X ≃ₜ Y) : Continuous h.symm := sorry

        -- -- Mathlib/Topology/Homotopy/Basic.lean
        -- @[continuity]
        -- protected theorem continuous (F : HomotopyWith f₀ f₁ P) : Continuous F := sorry

        -- -- Mathlib/Topology/Homotopy/Equiv.lean
        -- @[continuity]
        -- theorem continuous (h : HomotopyEquiv X Y) : Continuous h := sorry

        -- -- Mathlib/Topology/Instances/AddCircle.lean
        -- @[continuity, nolint unusedArguments]
        -- protected theorem continuous_mk' :

        -- @[continuity]
        -- theorem continuous_equivIco_symm : Continuous (equivIco p a).symm := sorry

        -- @[continuity]
        -- theorem continuous_equivIoc_symm : Continuous (equivIoc p a).symm := sorry

-- Mathlib/Topology/Instances/ENNReal.lean
-- @[continuity]
-- theorem continuous_pow (n : ℕ) : Continuous fun a : ℝ≥0∞ => a ^ n := sorry
    differentiable_pow  -- Mathlib.Analysis.Calculus.Deriv.Pow

        -- @[continuity]
        -- theorem Continuous.edist [TopologicalSpace β] {f g : β → α} (hf : Continuous f)

        -- -- Mathlib/Topology/Instances/Matrix.lean
        -- @[continuity]
        -- theorem continuous_matrix [TopologicalSpace α] {f : α → Matrix m n R}

        -- @[continuity]
        -- theorem Continuous.matrix_map [TopologicalSpace S] {A : X → Matrix m n S} {f : S → R}

-- @[continuity]
-- theorem Continuous.matrix_transpose {A : X → Matrix m n R} (hA : Continuous A) :
    -- TODO `Differentiable.matrix_transpose`

-- @[continuity]
-- theorem Continuous.matrix_col {A : X → n → R} (hA : Continuous A) : Continuous fun x => col (A x) := sorry
    -- TODO `Differentiable.matrix_col`

-- @[continuity]
-- theorem Continuous.matrix_row {A : X → n → R} (hA : Continuous A) : Continuous fun x => row (A x) := sorry
    -- TODO `Differentiable.matrix_row`

-- @[continuity]
-- theorem Continuous.matrix_diagonal [Zero R] [DecidableEq n] {A : X → n → R} (hA : Continuous A) :
        -- TODO `Differentiable.matrix_diagonal`

-- @[continuity]
-- theorem Continuous.matrix_dotProduct [Fintype n] [Mul R] [AddCommMonoid R] [ContinuousAdd R]
    -- TODO `Differentiable.matrix_dotProduct`

-- @[continuity]
-- theorem Continuous.matrix_mul [Fintype n] [Mul R] [AddCommMonoid R] [ContinuousAdd R]
    -- TODO `Differentiable.matrix_mul`

-- @[continuity]
-- theorem Continuous.matrix_vecMulVec [Mul R] [ContinuousMul R] {A : X → m → R} {B : X → n → R}
    -- TODO `Differentiable.matrix_vecMulVec`

-- @[continuity]
-- theorem Continuous.matrix_mulVec [NonUnitalNonAssocSemiring R] [ContinuousAdd R] [ContinuousMul R]
    -- TODO `Differentiable.matrix_mulVec`

-- @[continuity]
-- theorem Continuous.matrix_vecMul [NonUnitalNonAssocSemiring R] [ContinuousAdd R] [ContinuousMul R]
    -- TODO `Differentiable.matrix_vecMul`

-- @[continuity]
-- theorem Continuous.matrix_submatrix {A : X → Matrix l n R} (hA : Continuous A) (e₁ : m → l)
    -- TODO `Differentiable.matrix_submatrix`

-- @[continuity]
-- theorem Continuous.matrix_reindex {A : X → Matrix l n R} (hA : Continuous A) (e₁ : l ≃ m)
    -- TODO `Differentiable.matrix_reindex`

-- @[continuity]
-- theorem Continuous.matrix_diag {A : X → Matrix n n R} (hA : Continuous A) :
    -- TODO `Differentiable.matrix_diag`

-- @[continuity]
-- theorem Continuous.matrix_trace [Fintype n] [AddCommMonoid R] [ContinuousAdd R]
    -- TODO `Differentiable.matrix_trace`

-- @[continuity]
-- theorem Continuous.matrix_det [Fintype n] [DecidableEq n] [CommRing R] [TopologicalRing R]
    -- TODO `Differentiable.matrix_det`

-- @[continuity]
-- theorem Continuous.matrix_updateColumn [DecidableEq n] (i : n) {A : X → Matrix m n R}
    -- TODO `Differentiable.matrix_updateColumn`

-- @[continuity]
-- theorem Continuous.matrix_updateRow [DecidableEq m] (i : m) {A : X → Matrix m n R} {B : X → n → R}
    -- TODO `Differentiable.matrix_updateRow`

-- @[continuity]
-- theorem Continuous.matrix_cramer [Fintype n] [DecidableEq n] [CommRing R] [TopologicalRing R]
    -- TODO `Differentiable.matrix_cramer`

-- @[continuity]
-- theorem Continuous.matrix_adjugate [Fintype n] [DecidableEq n] [CommRing R] [TopologicalRing R]
    -- TODO `Differentiable.matrix_adjugate`

-- @[continuity]
-- theorem Continuous.matrix_fromBlocks {A : X → Matrix n l R} {B : X → Matrix n m R}
    -- TODO `Differentiable.matrix_fromBlocks`

-- @[continuity]
-- theorem Continuous.matrix_blockDiagonal [Zero R] [DecidableEq p] {A : X → p → Matrix m n R}
    -- TODO `Differentiable.matrix_blockDiagonal`

-- @[continuity]
-- theorem Continuous.matrix_blockDiag {A : X → Matrix (m × p) (n × p) R} (hA : Continuous A) :
    -- TODO `Differentiable.matrix_blockDiag`

-- @[continuity]
-- theorem Continuous.matrix_blockDiagonal' [Zero R] [DecidableEq l]
    -- TODO `Differentiable.matrix_blockDiagonal'`

-- @[continuity]
-- theorem Continuous.matrix_blockDiag' {A : X → Matrix (Σi, m' i) (Σi, n' i) R} (hA : Continuous A) :
    -- TODO `Differentiable.matrix_blockDiag'`

-- Mathlib/Topology/MetricSpace/Basic.lean
-- @[continuity]
-- theorem continuous_dist : Continuous fun p : α × α => dist p.1 p.2 := sorry
    Differentiable.dist  -- Mathlib.Analysis.InnerProductSpace.Calculus

-- @[continuity]
-- protected theorem Continuous.dist [TopologicalSpace β] {f g : β → α} (hf : Continuous f)

        -- -- Mathlib/Topology/MetricSpace/HausdorffDistance.lean
        -- @[continuity]
        -- theorem continuous_infEdist : Continuous fun x => infEdist x s := sorry

        -- @[continuity]
        -- theorem continuous_infDist_pt : Continuous (infDist · s) := sorry

        -- -- Mathlib/Topology/Order.lean
        -- @[nontriviality, continuity]
        -- theorem continuous_of_discreteTopology [TopologicalSpace β] {f : α → β} : Continuous f := sorry

        -- @[continuity]
        -- theorem continuous_induced_dom {t : TopologicalSpace β} : Continuous[induced f t, t] f := sorry

        -- @[continuity]
        -- theorem continuous_bot {t : TopologicalSpace β} : Continuous[⊥, t] f := sorry

        -- @[continuity]
        -- theorem continuous_top {t : TopologicalSpace α} : Continuous[t, ⊤] f := sorry

        -- -- Mathlib/Topology/Order/Basic.lean
        -- @[continuity]
        -- protected theorem Continuous.min (hf : Continuous f) (hg : Continuous g) :

        -- @[continuity]
        -- protected theorem Continuous.max (hf : Continuous f) (hg : Continuous g) :

        -- -- Mathlib/Topology/Order/Lattice.lean
        -- @[continuity]
        -- theorem continuous_inf [Inf L] [ContinuousInf L] : Continuous fun p : L × L => p.1 ⊓ p.2 := sorry

        -- @[continuity]
        -- theorem Continuous.inf [Inf L] [ContinuousInf L] {f g : X → L} (hf : Continuous f)

        -- @[continuity]
        -- theorem continuous_sup [Sup L] [ContinuousSup L] : Continuous fun p : L × L => p.1 ⊔ p.2 := sorry

        -- @[continuity]
        -- theorem Continuous.sup [Sup L] [ContinuousSup L] {f g : X → L} (hf : Continuous f)

        -- -- Mathlib/Topology/UniformSpace/AbstractCompletion.lean
        -- @[continuity]
        -- theorem continuous_map : Continuous (map f) := sorry

        -- -- Mathlib/Topology/UniformSpace/Completion.lean
        -- @[continuity]
        -- theorem continuous_extension : Continuous (Completion.extension f) := sorry

        -- @[continuity]
        -- theorem continuous_map : Continuous (Completion.map f) := sorry

        -- -- Mathlib/Topology/UniformSpace/Equiv.lean
        -- @[continuity]
        -- protected theorem continuous (h : α ≃ᵤ β) : Continuous h := sorry

        -- @[continuity]
        -- protected theorem continuous_symm (h : α ≃ᵤ β) : Continuous h.symm := sorry

        -- -- Mathlib/Topology/UnitInterval.lean
        -- @[continuity]
        -- theorem continuous_symm : Continuous σ := sorry

        -- -- Mathlib/Topology/VectorBundle/Basic.lean
        -- @[continuity]
        -- theorem continuous_proj : Continuous Z.proj := sorry

        -- @[continuity]
        -- theorem continuous_totalSpaceMk (b : B) :

-- Other potential candidates that did not have an analog

    IsBoundedLinearMap.differentiable  -- Mathlib.Analysis.Calculus.FDeriv.Linear
    ContinuousLinearMap.differentiable  -- Mathlib.Analysis.Calculus.FDeriv.Linear
    Differentiable.iterate  -- Mathlib.Analysis.Calculus.FDeriv.Comp
    differentiable_fst  -- Mathlib.Analysis.Calculus.FDeriv.Prod
    differentiable_snd  -- Mathlib.Analysis.Calculus.FDeriv.Prod
    Differentiable.fst  -- Mathlib.Analysis.Calculus.FDeriv.Prod
    Differentiable.snd  -- Mathlib.Analysis.Calculus.FDeriv.Prod
    Differentiable.prod  -- Mathlib.Analysis.Calculus.FDeriv.Prod
    IsBoundedBilinearMap.differentiable  -- Mathlib.Analysis.Calculus.FDeriv.Bilinear
    Differentiable.const_mul  -- Mathlib.Analysis.Calculus.FDeriv.Mul
    Differentiable.mul_const  -- Mathlib.Analysis.Calculus.FDeriv.Mul
    Differentiable.pow  -- Mathlib.Analysis.Calculus.FDeriv.Mul
    Differentiable.inverse  -- Mathlib.Analysis.Calculus.FDeriv.Mul
    Differentiable.mul  -- Mathlib.Analysis.Calculus.FDeriv.Mul
    Differentiable.inv'  -- Mathlib.Analysis.Calculus.FDeriv.Mul
    Differentiable.smul_const  -- Mathlib.Analysis.Calculus.FDeriv.Mul
    Differentiable.smul  -- Mathlib.Analysis.Calculus.FDeriv.Mul
    Differentiable.neg  -- Mathlib.Analysis.Calculus.FDeriv.Add
    Differentiable.const_sub  -- Mathlib.Analysis.Calculus.FDeriv.Add
    Differentiable.sub_const  -- Mathlib.Analysis.Calculus.FDeriv.Add
    Differentiable.add_const  -- Mathlib.Analysis.Calculus.FDeriv.Add
    Differentiable.const_add  -- Mathlib.Analysis.Calculus.FDeriv.Add
    Differentiable.sum  -- Mathlib.Analysis.Calculus.FDeriv.Add
    Differentiable.sub  -- Mathlib.Analysis.Calculus.FDeriv.Add
    Differentiable.add  -- Mathlib.Analysis.Calculus.FDeriv.Add
    Differentiable.const_smul  -- Mathlib.Analysis.Calculus.FDeriv.Add
    Differentiable.div_const  -- Mathlib.Analysis.Calculus.Deriv.Mul
    Differentiable.restrictScalars  -- Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
    Differentiable.inv  -- Mathlib.Analysis.Calculus.Deriv.Inv
    Differentiable.div  -- Mathlib.Analysis.Calculus.Deriv.Inv
    ContinuousLinearEquiv.differentiable  -- Mathlib.Analysis.Calculus.FDeriv.Equiv
    LinearIsometryEquiv.differentiable  -- Mathlib.Analysis.Calculus.FDeriv.Equiv
    ContDiff.differentiable  -- Mathlib.Analysis.Calculus.ContDiffDef
    ContDiff.differentiable_iteratedFDeriv  -- Mathlib.Analysis.Calculus.ContDiffDef
    HasFTaylorSeriesUpTo.differentiable  -- Mathlib.Analysis.Calculus.ContDiffDef
    differentiable_neg  -- Mathlib.Analysis.Calculus.Deriv.Add
    differentiable_tsum  -- Mathlib.Analysis.Calculus.Series
    differentiable_inner  -- Mathlib.Analysis.InnerProductSpace.Calculus
    ContDiff.differentiable_iteratedDeriv  -- Mathlib.Analysis.Calculus.IteratedDeriv
    Conformal.differentiable  -- Mathlib.Analysis.Calculus.Conformal.NormedSpace
    Real.differentiable_exp  -- Mathlib.Analysis.SpecialFunctions.ExpDeriv
    Complex.differentiable_exp  -- Mathlib.Analysis.SpecialFunctions.ExpDeriv
    expNegInvGlue.differentiable_polynomial_eval_inv_mul  -- Mathlib.Analysis.SpecialFunctions.SmoothTransition
    Differentiable.star  -- Mathlib.Analysis.Calculus.FDeriv.Star
    Differentiable.zpow  -- Mathlib.Analysis.Calculus.Deriv.ZPow
    differentiable_circleMap  -- Mathlib.MeasureTheory.Integral.CircleIntegral
    MDifferentiable.differentiable  -- Mathlib.Geometry.Manifold.MFDeriv
    Differentiable.clog  -- Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
    Differentiable.rpow  -- Mathlib.Analysis.SpecialFunctions.Pow.Deriv
    Real.differentiable_arctan  -- Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
    Differentiable.arctan  -- Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
    Complex.differentiable_one_div_Gamma  -- Mathlib.Analysis.SpecialFunctions.Gamma.Beta
    Differentiable.inversion  -- Mathlib.Geometry.Euclidean.Inversion.Calculus
    differentiable_completed_zeta₀  -- Mathlib.NumberTheory.ZetaFunction
    differentiable_mellin_zetaKernel₂  -- Mathlib.NumberTheory.ZetaFunction



-- set_option trace.aesop true


-- TODO this should work but doesn't, maybe because of search depth or something like that
example : Differentiable ℝ (fun x ↦ x * Real.exp x + 3) := by
    differentiability?

-- Note: aesop's question-mark-mode seems to output things that don't actually close the goal
-- without manually adjusting some things

-- Issue: Large natural powers lead to timeouts.
-- This is due to copied over (from `continuity`) settings of tactic.
-- I'm not sure why those options are used.

example : Differentiable ℝ (fun x ↦
(sin x * exp x + 3) * 999 * (cosh (cos x)))
:= by
    differentiability

example : Differentiable ℂ (fun x ↦
(sin x * exp x + 3) * 999 * (cosh (cos x)))
:= by
    differentiability

section CopiedOverFromContinuity

variable [IsROrC 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]


example : Differentiable 𝕜 (id : E → E) := by differentiability

-- example {f : F → G} {g : E → F} (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g) :
--   Differentiable 𝕜 (fun x => f (g x)) := by
--     differentiability
--     sorry

-- example {f : X → Y} {g : Y → X} (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g) :
--   Differentiable 𝕜 (f ∘ g ∘ f) := by differentiability

-- example {f : X → Y} {g : Y → X} (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g) :
--   Differentiable 𝕜 (f ∘ g) := by differentiability

-- example (y : Y) : Differentiable 𝕜 (fun (_ : X) ↦ y) := by differentiability

-- example {f : Y → Y} (y : Y) : Differentiable 𝕜 (f ∘ (fun (_ : X) => y)) := by differentiability

-- example {g : X → X} (y : Y) : Differentiable 𝕜 ((fun _ ↦ y) ∘ g) := by differentiability

-- example {f : X → Y} (x : X) : Differentiable 𝕜 (fun (_ : X) ↦ f x) := by differentiability


-- Todo: more interesting examples


example (b : E) : Differentiable 𝕜 (fun _ : F => b) := by differentiability

-- example (f : C(X, Y)) (g : C(Y, Z)) : Differentiable 𝕜 (g ∘ f) := by differentiability

-- example (f : C(X, Y)) (g : C(X, Z)) : Differentiable 𝕜 (fun x => (f x, g x)) := by differentiability

-- example (f : C(X, Y)) (g : C(W, Z)) : Differentiable 𝕜 (Prod.map f g) := --by differentiability
--   f.continuous.prod_map g.continuous

-- example (f : ∀ i, C(X, X' i)) : Differentiable 𝕜 (fun a i => f i a) := by differentiability

-- example (s : Set X) (f : C(X, Y)) : Differentiable 𝕜 (f ∘ ((↑) : s → X)) := by differentiability

-- Examples taken from `Topology.CompactOpen`:

-- example (b : Y) : Differentiable (Function.const X b) := --by differentiability
--   continuous_const

-- example (b : Y) : Differentiable (@Prod.mk Y X b) := by differentiability

-- example (f : C(X × Y, Z)) (a : X) : Differentiable (Function.curry f a) := --by differentiability
--   f.continuous.comp (continuous_const.prod_mk continuous_id)

-- /-! Some tests of the `comp_of_eq` lemmas -/

-- example {α β : Type _} [TopologicalSpace α] [TopologicalSpace β] {x₀ : α} (f : α → α → β)
--   (hf : DifferentiableAt (Function.uncurry f) (x₀, x₀)) :
--   DifferentiableAt (λ x ↦ f x x) x₀ := by
--   fail_if_success { exact hf.comp (continuousAt_id.prod continuousAt_id) }
--   exact hf.comp_of_eq (continuousAt_id.prod continuousAt_id) rfl
