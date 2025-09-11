import Lean 

import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic

import Mathlib.Tactic.DataSynth.Elab
import Mathlib.Tactic.DataSynth.Attr
import Mathlib.Tactic.DataSynth.Tests.FDerivInit
import Mathlib.Tactic.DataSynth.Tests.Normalize

section theorems
variable {R : Type*} [NontriviallyNormedField R]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace R E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace R F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace R G]


variable (R) in
@[data_synth out f']
structure HasFwdFDeriv (f : E → F) (f' : E → E → F × F) : Prop where
  deriv : ∀ x, 
    ∃ F, HasFDerivAt (𝕜:=R) f F x
         ∧ 
         F = fun dx => (f' x dx).2
  eval : ∀ dx, f = fun x => (f' x dx).1

@[data_synth]
theorem hasFwdFDeriv_id : HasFwdFDeriv R (fun x : E => x) (fun x dx => (x,dx)) := by
  constructor
  case eval => simp
  case deriv =>
    intro x
    use (ContinuousLinearMap.id R E)
    constructor
    · exact hasFDerivAt_id x
    · rfl
    
-- @[data_synth]
theorem hasFwdFDeriv_comp (g : E → F) (f : F → G) {g' f'}
    (hg : HasFwdFDeriv R g g') (hf : HasFwdFDeriv R f f') :
    HasFwdFDeriv R (fun x => f (g x))
      (fun x dx => 
        let ydy := g' x dx
        let zdz := f' ydy.1 ydy.2
        zdz) := by
  sorry

-- @[data_synth]
theorem hasFwdFDeriv_let (g : E → F) (f : F → E → G) {g' f'}
    (hg : HasFwdFDeriv R g g') (hf : HasFwdFDeriv R (fun x : F×E => f x.1 x.2) f') :
    HasFwdFDeriv R (fun x => let y := g x; f y x)
      (fun x dx => 
        let ydy := g' x dx
        let zdz := f' (ydy.1,x) (ydy.2,dx)
        zdz) := by
  sorry

@[data_synth]
theorem hasFwdFDeriv_mul [NormedSpace ℝ E] (f g : E → ℝ) {f' g'}
    (hf : HasFwdFDeriv ℝ f f') (hg : HasFwdFDeriv ℝ g g') :
    HasFwdFDeriv ℝ (fun x => f x * g x) 
      (fun x dx => 
        let ydy := f' x dx
        let zdz := g' x dx
        let rdr := (ydy.1*zdz.1, ydy.1*zdz.2 + ydy.2*zdz.1)
        rdr) := sorry

@[data_synth]
theorem hasFwdFDeriv_fst (f : E → F×G) {f'} (hf : HasFwdFDeriv R f f') :
    HasFwdFDeriv R (fun x => (f x).1) 
      (fun x dx => 
        let yzdyz := f' x dx
        let ydy := (yzdyz.1.1,yzdyz.2.1)
        ydy) := sorry

@[data_synth]
theorem hasFwdFDeriv_snd (f : E → F×G) {f'} (hf : HasFwdFDeriv R f f') :
    HasFwdFDeriv R (fun x => (f x).2) 
      (fun x dx => 
        let yzdyz := f' x dx
        let zdz := (yzdyz.1.2,yzdyz.2.2)
        zdz) := sorry

@[data_synth]
theorem hasFwdFDeriv_sin :
    HasFwdFDeriv ℝ (fun x => Real.sin x) 
      (fun x dx => (x.sin, dx*x.cos)) := sorry

@[data_synth]
theorem hasFwdFDeriv_cos :
    HasFwdFDeriv ℝ (fun x => Real.cos x) 
      (fun x dx => (x.cos, -dx*x.sin)) := sorry

open Lean Meta

dsimproc_decl hihi (_) := fun e => do
  match e with 
  | .letE n t v b nondep => do
    match ← Simp.dsimp v with 
    | .fvar id => do
      trace[Meta.Tactic.data_synth.normalize] m!"remove let\n{e}"
      return .visit (b.instantiate1 (.fvar id))
    | .letE m t' v' b' nondep' => do
      trace[Meta.Tactic.data_synth.normalize] m!"move let out\n{e}"
      return .visit 
       (.letE m t' v' (nondep:=nondep') <|
        .letE n t b' (b.liftLooseBVars 1 1) nondep)
    | mkApp4 (.const ``Prod.mk lvl) X Y x y => do
      trace[Meta.Tactic.data_synth.normalize] m!"split constructor\n{e}"
      withLetDecl (n.appendAfter "₁") X x fun xvar => do
      withLetDecl (n.appendAfter "₂") Y y fun yvar => do
      let v' := mkApp4 (.const ``Prod.mk lvl) X Y xvar yvar
      -- let b ← Simp.dsimp (b.instantiate1 v')
      return .visit (← mkLambdaFVars #[xvar,yvar] (b.instantiate1 v'))
    | _ => 
      trace[Meta.Tactic.data_synth.normalize]  m!"simplify body\n{e}"
      withLetDecl n t v fun var => do
      return .continue (← mkLambdaFVars #[var] (← Simp.dsimp (b.instantiate1 var)))
      -- return .continue
  | _ =>
    return .continue

set_option pp.proofs false

attribute [simp] hihi

#eval show MetaM Unit from do
  let a ← Simp.getSimprocFromDecl ``hihi
  match a with
  | .inl _ => logInfo "simproc"
  | .inr _ => logInfo "dsimproc"

simproc_decl normalize_v1 (_) := fun e => do
  let e' ← normalizeCore normalizeCache e
  -- logInfo m!"normalization\n{e}\n==>\n{e'}"
  return .continue (some { expr := e'})

open Mathlib.Meta
def norm : DataSynth.Normalize := fun e => do
  let e ← normalizeCore normalizeCache e
  return { expr := e }

set_option pp.funBinderTypes true in
set_option trace.Meta.Tactic.data_synth true in
-- set_option trace.Meta.Tactic.data_synth.normalize true in
#check (by data_synth (disch:=skip) (norm:=skip) [norm] :
  HasFwdFDeriv ℝ (fun x : ℝ => x * x * x) _)


open Mathlib.Meta.FunProp in
/-- Perform non trivial decomposition of `fn = q(fun _ => _)` into 
`f` and `g` such that `fn = f∘g`. -/
def lambdaDecompose (fn : Expr) : MetaM (Option (Expr × Expr)) := do
  let .lam xname xtype b bi := fn
    | return none

  b.withApp fun headFn args => do

    if headFn.hasLooseBVars then return none

    let taggedArgs := Array.range args.size |>.zip args
    let depTaggedArgs := taggedArgs.filter (fun (_, arg) => arg.hasLooseBVar 0)

    if depTaggedArgs.size = 0 then return none

    let gbody ← mkProdElem (depTaggedArgs.map (·.2))
    let g := Expr.lam xname xtype gbody bi
    let .some (_, Y) := (← inferType g).arrow? | return none

    let f ← 
      withLocalDeclD `y Y fun y => do
        let ys ← mkProdSplitElem y depTaggedArgs.size
        
        let mut args' := args
        for (i, _) in depTaggedArgs, yi in ys do
          args' := args'.set! i yi

        mkLambdaFVars #[y] (headFn.beta args')

    -- not non-trivial decomposition
    if ← isDefEq f fn then return none

    return (f, g)

open Mathlib.Meta.DataSynth
#eval do
  let .some s := (dataSynthDeclsExt.getState (← getEnv)).find? ``HasFwdFDeriv
    | throwError "invalid data_synth decl"
  s.customDispatch.set (fun goal => do
    trace[Meta.Tactic.data_synth] m!"calling custom callback for HasFwdFDeriv"
    let (_, e) ← goal.mkFreshProofGoal
    let fn := e.getArg! 8
    match fn with
    | .lam x xtype (binderInfo:=bi)
        (.letE y ytype yval body _) =>

      let f := Expr.lam y ytype (.lam x xtype (body.swapBVars 0 1) bi) bi
      let g := Expr.lam x xtype yval bi

      let letThm ← getTheoremFromConst ``hasFwdFDeriv_let
      let hints := #[(11, g), (12, f)]

      return ← goal.tryTheorem? letThm hints #[]
    | .lam _ _ b _ =>
      match b with
      | .app .. =>
        let .some (f, g) ← lambdaDecompose fn | return none
    
        let compThm ← getTheoremFromConst ``hasFwdFDeriv_comp
        let hints := #[(11, g), (12, f)]

        return ← goal.tryTheorem? compThm hints #[]
      | _ => return none
    | _ => 
      return none)

set_option trace.Meta.Tactic.data_synth true in
#check (by data_synth -zeta (disch:=skip) (norm:=skip) [norm] :
  HasFwdFDeriv ℝ (fun x : ℝ => let y := x * x; let z := y * x; z * y * x * x) _)

set_option trace.Meta.Tactic.data_synth true in
#check (by data_synth -zeta (disch:=skip) (norm:=skip) [norm] :
  HasFwdFDeriv ℝ (fun x : ℝ => Real.sin (x*x)) _)
  

end theorems

open Lean Meta Mathlib Meta DataSynth Std

example (v t : ℝ) : deriv (fun t : ℝ => 1/2 * v * t^2) t = v * t := sorry
example (x : ℝ) (hx : x ≠ 0) : deriv (fun x : ℝ => x⁻¹) x = - x^(-2:ℤ) := sorry
example (x : EuclideanSpace ℝ (Fin 3)) : gradient (fun x => 1/‖x‖) x = -‖x‖^(-3:ℤ)•x := sorry


