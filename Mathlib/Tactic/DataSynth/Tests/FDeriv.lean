import Lean 

import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

import Mathlib.Tactic.DataSynth.Elab
import Mathlib.Tactic.DataSynth.Attr
import Mathlib.Tactic.DataSynth.Tests.FDerivInit

section missing
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

theorem hasFDerivAt_id' (x : E) :
    HasFDerivAt (fun x => x) (ContinuousLinearMap.id 𝕜 E) x := hasFDerivAt_id x

theorem HasFDerivAt.fun_comp
    {f : E → F} {f' : E →L[𝕜] F} {g : F → G} {g' : F →L[𝕜] G} {x : E}
    (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : 
    HasFDerivAt (fun x => g (f x)) (g'.comp f') x :=
  HasFDerivAtFilter.comp x hg hf hf.continuousAt

-- open ContinuousLinearMap in
-- theorem HasFDerivAt.fun_inv {f : E → 𝕜} {f' : E →L[𝕜] 𝕜} {x}
--     (hf : HasFDerivAt f f' x) (ne_zero : f x ≠ 0) :
--     HasFDerivAt (fun x => (f x)⁻¹) (-(f x ^ 2)⁻¹ • f') x := by
--   have h := (hasFDerivAt_inv ne_zero).fun_comp hf
--   apply h.congr_fderiv; ext 
--   simp[mul_comm]

theorem deriv_eq_fderiv {f : 𝕜 → E} {x : 𝕜} {g : 𝕜 →L[𝕜] E} (h : fderiv 𝕜 f x = g) : 
    deriv f x = g 1 := by
  simp[deriv,h]

end missing

attribute [data_synth out f'] HasFDerivAt

attribute [data_synth] 
  hasFDerivAt_id
  hasFDerivAt_id'
  hasFDerivAt_const
  HasFDerivAt.comp
  HasFDerivAt.fun_comp
  HasFDerivAt.fun_add
  HasFDerivAt.fun_sub
  HasFDerivAt.fun_mul
  hasFDerivAt_inv
  hasFDerivAt_exp
  HasFDerivAt.exp
  HasFDerivAt.sin
  HasFDerivAt.cos

set_option pp.proofs false 
variable (x₀ : ℝ)
  (f : ℝ → ℝ) (f' : ℝ → (ℝ →L[ℝ] ℝ)) (hf : ∀ x, HasFDerivAt f (f' x) x)
  (g : ℝ → ℝ) (g' : ℝ → (ℝ →L[ℝ] ℝ)) (hg : ∀ x, HasFDerivAt g (g' x) x)

#check
 (by data_synth :
  HasFDerivAt (𝕜:=ℝ) (fun x : ℝ => x) _ x₀)

#check
 (by data_synth (disch:=skip) (norm:=simp [smul_smul,←add_smul]) :
  HasFDerivAt (𝕜:=ℝ) (fun x : ℝ => x*x*x+x) _ x₀)

#check
 (by data_synth (disch:=skip) (norm:=simp) :
  HasFDerivAt (𝕜:=ℝ) (fun x : ℝ => x*3) _ x₀)

#check
 (by data_synth (disch:=skip) (norm:=simp) :
  HasFDerivAt (𝕜:=ℝ) (fun x : ℝ => (3:ℝ)*x) _ x₀)

#check
 (by data_synth :
  HasFDerivAt (𝕜:=ℝ) f _ x₀)

#check
 (by data_synth :
  HasFDerivAt (𝕜:=ℝ) (fun x => f (f (f x))) _ x₀)

variable (R : Type)

open Lean Meta Mathlib.Meta DataSynth in
simproc_decl fderiv_at_simproc (fderiv _ _ _) := fun e => do

  -- get arguments
  let x := e.appArg!
  let f := e.appFn!.appArg!
  let R := e.getArg! 0

  -- initialize `HasFDerivAt R f ?f' x`
  let hasFDerivAt := ← mkConstWithFreshMVarLevels ``HasFDerivAt
  let (xs,_,_) ← forallMetaTelescope (←inferType hasFDerivAt)
  xs[0]!.mvarId!.assignIfDefEq R
  xs[xs.size-3]!.mvarId!.assignIfDefEq f
  xs[xs.size-1]!.mvarId!.assignIfDefEq x
  let hasFDerivAt := hasFDerivAt.beta xs

  -- call data_synth
  let .some g ← isDataSynthGoal? hasFDerivAt | return .continue
  let cfg ← Simp.getConfig
  let ctx : DataSynth.Context := { 
    config := { cfg with norm_simp := true }
    disch := (← Simp.getMethods).discharge?
  }
  let state : IO.Ref DataSynth.State ← 
    IO.mkRef { theorems := theoremsExt.getState (← getEnv) }
  let .some r ← dataSynth g ctx state | return .continue

  -- produce simp result
  let proof ← mkAppM ``HasFDerivAt.fderiv #[r.proof]
  let f' := r.xs[0]!

  return .visit { expr := f', proof? := proof }


open Lean Meta in
simproc_decl fderiv_simproc (fderiv _ _) := fun e => do
  
  let f := e.appArg!
  let .some (E, _) := (← inferType f).arrow? | return .continue

  -- introduce point where to differentiate
  withLocalDecl `x default E fun x => do

    -- bind the free variable `x` to the result
    let fixResult (r : Simp.Result) : MetaM Simp.Result := do
      return { r with
        expr := ← mkLambdaFVars #[x] r.expr
        proof? := ← r.proof?.mapM (fun p => mkLambdaFVars #[x] p >>= (mkAppM ``funext #[·])) 
      }
    
    -- call simproc for `fderiv R f x` and bind the free variable `x`
    match (← fderiv_at_simproc (e.beta #[x])) with
    | .done r => return .done (← fixResult r)
    | .visit r => return .visit (← fixResult r)
    | .continue (some r) => return .continue (some (← fixResult r))
    | .continue none => return .continue


attribute [deriv_simproc] fderiv_at_simproc fderiv_simproc

variable (x : ℝ)

example (x dx : ℝ) : fderiv ℝ (fun x => x*x) x dx = x*dx+x*dx := by simp[deriv_simproc]

open ContinuousLinearMap

example (x : ℝ) : 
    fderiv ℝ (fun x => x*x) x
    = 
    x • id ℝ ℝ + x • id ℝ ℝ := by simp[deriv_simproc]

example (x : ℝ) :
    fderiv ℝ (fun x : ℝ => x*x)
    = 
    fun x => x • id ℝ ℝ + x • id ℝ ℝ := by 
      simp[deriv_simproc]

example (x : ℝ) (h : x ≠ 0) :
    fderiv ℝ (fun x => x⁻¹) (x^2)
    =
    smulRight (1:ℝ→L[ℝ]ℝ) (-((x ^ 2) ^ 2)⁻¹) := by
  simp (disch:=aesop) only [deriv_simproc]

example (x : ℝ) (h : x ≠ 0) :
    fderiv ℝ (fun x => (x*x)⁻¹) x
    =
    x⁻¹ • smulRight (1:ℝ→L[ℝ]ℝ) (-(x ^ 2)⁻¹) + x⁻¹ • smulRight (1:ℝ→L[ℝ]ℝ) (-(x ^ 2)⁻¹) := by
  simp (disch:=aesop) [deriv_simproc]

open Real in
example (x : ℝ) :
    fderiv ℝ (fun x => (exp x)⁻¹*sin x) x 1
    =
    (rexp x)⁻¹ * cos x + -(sin x * (rexp x * (rexp x ^ 2)⁻¹)) := by
  simp (disch:=aesop) [deriv_simproc]



