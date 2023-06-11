import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Tactic.junkAttribute
import Mathlib.Tactic.RunCmd
import Std.Lean.Expr

open Lean Elab Tactic Meta Parser
noncomputable section

open scoped BigOperators
open MeasureTheory

def getNot : Expr → MetaM (Bool × Expr)
  | x@(.app isNot? unNot) => do
    dbg_trace f!"isNot?: {isNot?}\n"
    dbg_trace f!"\n{(← isDefEq x (mkNot unNot))}\n"
    if (← isDefEq x (mkNot unNot)) then pure (false, unNot) else pure (true, x)
  | x => --dbg_trace "not not"
    pure (true, x)



def myProp : Prop := True
theorem mp (q : myProp) : myProp := q
#check mul_inv_cancel
def getProps (thm : Name) : MetaM (Array Expr) := do
let env := ← getEnv
let c := env.find? thm |>.get!
let cTy := c.instantiateTypeLevelParams (← mkFreshLevelMVars c.numLevelParams)
let y := ← forallTelescopeReducing cTy fun arr _exp => do
  let pfs := ← arr.filterM isProof
  pfs.mapM (inferType ·)
return y
--y.mapM getNot

#check mkNot

#check Expr.const
#check Ne
#check not
#eval do
  let xs := ← getProps `tsum_eq_zero_of_not_summable
  let xs := ← getProps `mp
  let xs := ← getProps `mul_inv_cancel
  dbg_trace f!"The array of `Prop`s has size {xs.size}"
  let x := xs[0]!
  dbg_trace x
/-
  dbg_trace x.ctorName
  let y := ← match ← whnf x with
--    | (.const na _) => dbg_trace "not" ; na
    | (.app isNot? unNot) => do --dbg_trace "not"
      dbg_trace f!"isNot?: {isNot?}\n"
      dbg_trace f!"\n{(← isDefEq x (mkNot unNot))}\n"
      if (← isDefEq x (mkNot unNot)) then pure (false, unNot) else pure (true, x)
    | _ => --dbg_trace "not not"
      pure (true, x)

  dbg_trace y
--  dbg_trace x
--  dbg_trace x
--  let x := ← getProps `mp
  pure ()
-/


universe u v

variable {α : Type u} {E : Type v}

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [MeasureSpace α]

open Lean Elab Tactic Parser Meta Command Expr
#check LocalContext
def ctorRec : Expr → String
  | bvar n    => "bvar" ++ toString n
  | fvar ..    => "fvar"
  | mvar ..    => "mvar"
  | sort ..    => "sort"
  | const ..   => "const"
  | app ..     => "app"
  | lam ..     => "lam"
  | forallE .. => "forallE"
  | letE ..    => "letE"
  | lit ..     => "lit"
  | mdata ..   => "mdata"
  | proj ..    => "proj"

--#check withFVar
#check withDecl
#check mkFreshLevelMVar
attribute [simp] tsum_eq_zero_of_not_summable
attribute [simp] MeasureTheory.integral_undef
attribute [junk] tsum_eq_zero_of_not_summable

--def myProp : Prop := sorry
--theorem mp (q : myProp) : myProp := q

--#eval do run_cmd  do
--  ← Lean.Elab.Command.elabPrint `Nat.zero

#print tsum_eq_zero_of_not_summable
--def dict : Prop →
#check MVarId.withContext
#check Environment.find?
--#check FVarId
def getPropsOld (thm : Name) : MetaM (Array Expr) := do
let env := ← getEnv
--let fd := env.find? thm
--let
--dbg_trace fd.get!.defnInfo
let c := env.find? thm |>.get!
--let cdi := c.toConstantVal
--dbg_trace f!"cdi name: {cdi.name}"
--dbg_trace f!"c.value {(← ppExpr c.value!)}"
let cTy := c.instantiateTypeLevelParams (← mkFreshLevelMVars c.numLevelParams)
--let xarr := ← forallTelescopeReducing cTy fun arr exp => arr.mapM ppExpr
let x := ← forallTelescopeReducing cTy fun arr _exp => do (
  --dbg_trace f!"in telescope: {← ppExpr _exp}"; dbg_trace (arr);
  arr.filterM isProof) --.mapM ppExpr
--/-
let y := ← forallTelescopeReducing cTy fun arr _exp => do
  let pfs := ← arr.filterM isProof
  dbg_trace "prima"
  dbg_trace f!"ppExpr:    {(← (pfs.mapM (ppExpr ·)))}"
  dbg_trace f!"whnf:      {(← (pfs.mapM (whnf ·)))}"
  dbg_trace f!"ctorName:  {((pfs.map (ctorName ·)))}"
  dbg_trace f!"inferType: {(← (pfs.mapM (inferType ·)))}"
  let j := ← mkFreshLevelMVars 2
  dbg_trace (← isDefEq pfs[0]! (.const `Summable j))
  dbg_trace "dopo"
  pfs.mapM (inferType ·)
--/

--logInfo (← ppExpr cTy)
--let x1 := x[0]!
--dbg_trace ← ppExpr x[0]!
--dbg_trace x1.ctorName
--env.withContext do
--let xid := x1.fvarId!
--dbg_trace "here"
--let xt := ← inferType x1
--dbg_trace m!"{xid}"
--logInfo m!"{← ppExpr xt}"
--dbg_trace xarr
--dbg_trace x
--dbg_trace fd
--return x
return y
--return ← x.mapM fun d => do inferType d
--return ← x.mapM fun d => do let wf := (← whnf d); instantiateMVars wf

#eval do
  let x := ← getPropsOld `tsum_eq_zero_of_not_summable
  dbg_trace x
  pure ()

def myProp : Prop := True

theorem mp (q : myProp) : myProp := q

--  Is it possible to write some metaprogram that takes a declaration name as input and
--  returns the Types of the declaration that are in Prop.
--  For instance, with input ``(`mp : Name)`` I would like the output to be ``[`myProp]``


--#exit





#check Expr.toSyntax
open Expr


#check withMVarContext
example {α : Type u_1} {β : Type u_2} [AddCommMonoid α] [TopologicalSpace α] {f : β → α}
  (h : ¬Summable f) : (∑' (b : β), f b) = 0 := by
  run_tac show TacticM _ from do (
      --let env := ← getEnv
      --let fd := Environment.find? env thm
--    (← getEnv).withContext do
      let xx := ← getProps `tsum_eq_zero_of_not_summable
      let yy := ← (xx.mapM fun y => ppExpr y)
      let pp := xx[0]!
      dbg_trace yy
      dbg_trace ← ppExpr pp
      let y := ← inferType pp
--      MVars (← inferType pp)
      dbg_trace ← ppExpr y
      let se := ← xx.mapM fun x => do
        pure y
      --let x := xx[0]!
  --    let syn := ← Expr.toSyntax x
--      dbg_trace (← se.mapM (ppExpr ·))
--      evalTactic (← `(tactic | by_cases $xx ))
      pure ()
  )



#eval do --show MetaM (_) from do
--  let x := []
  let x:= ← getProps `tsum_eq_zero_of_not_summable
  --let z := ← x.mapM (fun y => do ← Expr.toSyntax y)
  pure x
  --dbg_trace x
--  pure ()


#check Environment.evalConst

/-
syntax (name := pass) "pass " term : tactic

elab_rules : tactic
| `(tactic| pass $f:term) => do
  evalTactic (← `(tactic| by_cases h_int : $f))

example (f : α → E) : (∫ a, f a) = 0 ∨ Integrable f := by
  pass Integrable f
  exact Or.inr ‹_›
-/

#check getLocalDeclFromUserName

syntax (name := junkGen) "junk_gen " term (","--(config)? (discharger)? (&" only")?
  simpArgs)? --(location)?
   : tactic
#check LocalDecl
#check getFVarLocalDecl
#check findLocalDecl?
set_option autoImplicit false
--  let localf := ← getFVarLocalDecl ef
#check getMainTarget
elab_rules : tactic
| `(tactic| junk_gen $f:term $[, $sa:simpArgs]?) => do
  dbg_trace ← Mathlib.Tactic.LabelAttr.labelled `junk
  let h := mkIdent `hh
  let ef ← elabTerm f none
  if ef.isFVar then
    --  TODO: instead of the blanket `0`, maybe use a junk value depending on `f`
    evalTactic (← `(tactic| rcases eq_or_ne $f 0 with $h | $h)) <|>
      throwError ("'junk_gen' used `0` as a junk value incorrectly.")
    evalTactic (← `(tactic| subst $h))
--    let gl := ← ppExpr (← getMainTarget)
    let lc := ← getLCtx
    let redOp:= (lc.decls.toList.reduceOption.map LocalDecl.type)
    let gl := ← redOp.mapM (ppExpr ·)
    --dbg_trace (← lc.decls.toList.reduceOption.mapM (fun x => ppExpr (mkFVarEx x.fvarId)))
    evalTactic (← `(tactic| {simp})) <|>
      throwError f!"`simp` could not close the resulting goal, assuming '{← ppExpr ef} = 0'\n" ++
        f!"State:\n{gl}"
  else
  evalTactic (← `(tactic| by_cases $h : $f))
  evalTactic (← `(tactic| (pick_goal 2)))
  let ctx := ← getLCtx
  let decls := ctx.decls.toList.reduceOption
  --let j : Option LocalDecl := ($f).find?
  let k := decls[0]!
--  match ef with
--    | .const _ _ => dbg_trace "const"
--    | .app _ _ => dbg_trace "app"
--    | .fvar _ => dbg_trace "fvar"
--    | .mvar _ => dbg_trace "mvar"
--    | _ => dbg_trace "noconst"
  dbg_trace ef.isFVar
  dbg_trace "here"
--  dbg_trace f!"localf"
--  let lis := decls.filter (LocalDecl.fvarId · == ef)
--    match ef with
--      | x.term => 1
--      | _ => 0
--  if ef.isFVar then dbg_trace f!"fvar: {localf.get!.userName}" else dbg_trace "not fvar"
--  dbg_trace localf.userName
--  dbg_trace lis.find? ()
--  dbg_trace lis.map LocalDecl.userName
  --let j LocalDecl := return (getLocalDeclFromUserName `α₁ <|> pure k) --<|> decls[0]!

  --let j : Name := (← getLocalDeclFromUserName `α₁).userName --<|> `ciao

--  dbg_trace k.userName
  focus do
    let cfg ← elabSimpConfig (⟨.missing⟩ : TSyntax `Lean.Parser.Tactic.config) .simp
    let thms0 ← getSimpTheorems
    let ctx : Simp.Context := {
       simpTheorems := #[thms0]
       congrTheorems := (← getSimpCongrTheorems)
       config := cfg
    }

    let r ← elabSimpArgs (sa.getD ⟨.missing⟩) ctx (eraseLocal := false) .simp
--     <|>
--      evalTactic (← `(tactic| by_cases h_int : Summable $f))
    _ ← simpLocation r.ctx Mathlib.Tactic.FieldSimp.discharge (Location.targets #[] true)
--    done

--elab_rules : tactic
--| `(tactic| junk_gen $f:term) => do

theorem mexample {a : ℚ} : 1 / a = 0 ∨ a ≠ 0 := by
  junk_gen a
  exact Or.inr ‹_›

example (f : Polynomial ℚ) (hf : f.natDegree = 0) : f.degree ≤ 0 := by
  junk_gen f
  rw [Polynomial.degree_eq_natDegree hh, hf]
  exact le_rfl


--#check tsum_mul_left

--#synth (Inhabited Type)
example {ι : Type _} [DivisionSemiring α] [TopologicalSpace α]
    [TopologicalSemiring α] {f : ι → α} {a b : α} [T2Space α] :
    (∑' (x : ι), a * f x) = a * ∑' (x : ι), f x := by
  junk_gen a
  junk_gen Summable f   --, []

  simp
  rcases eq_or_ne a 0 with rfl | ha; simp
--  run_cmd (do
--    let _ := ← #check _
--  )
  #exit
  run_tac show TacticM Unit from (do
    let mv := ← getMainGoal
    let _ := ← run_cmd (

      #check mv
    )
    pure ()
    --#check mv
--    dbg_trace (elabCheckCore true .missing)
    --let x := elabCheckCore true
    --dbg_trace x

  )


  --simp


--/-
example {a : ℚ} : 1 / a = 0 ∨ a ≠ 0 := by
  junk_gen a ≠ 0 , [div_zero, not_ne_iff, *]
  simp only [not_ne_iff, not_ne_iff.mp hh]
  --by_cases a = 0
  exact Or.inr ‹_›
--/

--[MeasureTheory.integral_undef]
example (f : α → E) : (∫ a, f a) = 0 ∨ Integrable f := by
  junk_gen Integrable f , []
  exact Or.inr ‹_›

--[tsum_eq_zero_of_not_summable]
example (f : ℕ → E) : (∑' x, f x) = 0 ∨ Summable f := by
  junk_gen Summable f , []
  exact Or.inr ‹_›



#exit
-- works but takes `f` rather than the `Prop`
syntax (name := junkGen) "junk_gen " ident --(config)? (discharger)? (&" only")?
  (simpArgs)? --(location)?
   : tactic

elab_rules : tactic
| `(tactic| junk_gen $f:ident $[$sa:simpArgs]?) => do
  let cfg ← elabSimpConfig (⟨.missing⟩ : TSyntax `Lean.Parser.Tactic.config) .simp
  let thms0 ← getSimpTheorems
  let ctx : Simp.Context := {
     simpTheorems := #[thms0]
     congrTheorems := (← getSimpCongrTheorems)
     config := cfg
  }
  let r ← elabSimpArgs (sa.getD ⟨.missing⟩) ctx (eraseLocal := false) .simp
  evalTactic (← `(tactic| by_cases h_int : MeasureTheory.Integrable $f)) <|>
    evalTactic (← `(tactic| by_cases h_int : Summable $f))
  evalTactic (← `(tactic| (pick_goal 2)))
  _ ← simpLocation r.ctx Mathlib.Tactic.FieldSimp.discharge (Location.targets #[] true)

macro "unint " f:ident na:simpArg : tactic => do
  (`(tactic| (
      (by_cases h_int : MeasureTheory.Integrable $f)
      (pick_goal 2)
      (simp [h_int, MeasureTheory.integral_undef, $na] <;> done )
    )
  ))

noncomputable section

open scoped BigOperators
open MeasureTheory
#check tsum
universe u v

variable {α : Type u} {E : Type v}
#check simp
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [MeasureSpace α]
--simp " (config)? (discharger)? ("only ")? ("[" simpLemma,* "]")? (location)?
example (f : ℕ → E) : (∑' x, f x) = 0 := by
  simp [tsum_eq_zero_of_not_summable, h_int]
  unsum f
  sorry
--  by_cases h_int : Summable f
--  pick_goal 2
  --simp [h_int, MeasureTheory.integral_undef] <;> done
  --exact h_int

#exit

example (f : α → E) : (∫ a, f a) = 0 := by
  junk_gen

  unint f
  sorry
  /- state:
  α: Type u
  E: Type v
  inst✝³: NormedAddCommGroup E
  inst✝²: NormedSpace ℝ E
  inst✝¹: CompleteSpace E
  inst✝: MeasureSpace α
  f: α → E
  h_int✝: Integrable f
  ⊢ (∫ (a : α), f a) = 0
  -/

#exit
--  by_cases Integrable f
--   --_ => sorry
--  . --_ => sorry
--
--
--     neg =>
--
--  --by_cases Integrable f
--  pick_goal 2
--  . apply integral_undef h


  --rcases eq_or_ne (∫ (a : α), f a) 0 with h | h
--  .
  --nonintegrability
  /-
  new state contains `h : ¬Integrable f`
  -/

--  apply integral_undef h
