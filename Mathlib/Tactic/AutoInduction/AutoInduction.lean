import Mathlib.Tactic.AutoInduction.Attr
-- import Init.Tactics
import Lean
/-!

## TODOS

- check if variable name exists in `autoinduction` attribute


## PROCESS
- `autoinduction x` gets called
- figure out the right induction principle for `x`, say `x_induction`
- run the command `induction x using x_induction`
- for each new goal
  - if the name of the goal matches an argument name provided with the attribute for `x_induction`,
    - try to close the goal by elaborating the provided term-syntax
return new goal state to the user

## Extra specification for more elaborate syntax use
1. `generalizing` clause
  - add the `generalizing` clause to the `induction` call
2. explicit match brackets:
  - pass the match brackets to the `induction` call.
  - In addition, for each argument name provided to the attribute
    - create a match bracket for the case, with the default argument names on the lhs
    - put the provided term-syntax on the rhs. some nuance:
      - if the term `$t` matches `by $tacseq`, return `$tacseq`
      - otherwise, insert `by exact $t`.
      (this might fix expected type issues)

3. add match hypothesis
  - we maybe can pass this option just straight to the `induction` tactic?


## possible issues with this "semi-macro" approach
- It is not clear that there will be an expected type for match brackets.

-/

-- set_option autoImplicit false
set_option linter.unusedTactic false

open Lean Elab Parser Tactic Meta


/--
`autoinduction` effectively calls `induction _ using` with the relevant definition marked with the
`@[autoinduction]` attribute. In addition, it uses the arguments specified at that point to
try to provide a value for the respective argument.
-/
syntax (name := autoinductiontac) "autoinduction" elimTarget+
  (" generalizing" (ppSpace colGt term:max)+)? (inductionAlts)? : tactic


/--
TODO: write doc
-/
def _root_.Lean.Syntax.Term.asTacticSeq {m} [Monad m] [MonadRef m] [MonadQuotation m] :
    Term → m (TSyntax ``tacticSeq)
  | `(by $tseq) => return tseq
  | `(term|$t) => `(tacticSeq|exact $t)


/--
TODO:
- write doc
- look into using Aesop.CtorNames
-/
def generateMatchBranches {m} [Monad m] [MonadControlT MetaM m]
    [MonadLiftT MetaM m] [MonadRef m] [MonadQuotation m] (elimName : Name) (elimInfo : ElimInfo)
    (cfg : AutoIndPrincipleConfig) (userAlts : NameSet):
    m (Array (TSyntax ``inductionAlt)) := do
  let elimInfo ← getElimInfo elimName
  let info ← liftMetaM <| getConstInfo elimName
  let val ← info.getConstantVal?.getDM <| liftMetaM <|
    throwError "Unsupported declaration type."
  forallTelescope val.type (fun ctors _ => do
    let mut altSyntax : Array (TSyntax ``inductionAlt) := #[]
    let validAlts : NameSet := elimInfo.altsInfo.foldl (fun s altInfo =>
      if altInfo.provesMotive then s.insert altInfo.name else s) {}
    for ctorFVar in ctors do
      let ctorId : FVarId := ctorFVar.fvarId!
      let ctorName : Name ← ctorId.getUserName
      if (userAlts.contains ctorName) then
        -- makes sure we're not doubling a user-provided alternative
        continue
      unless validAlts.contains ctorName do
        -- checks the argument is not
        -- - the motive argument
        -- - a target argument
        -- and is
        -- - an explicit argument
        -- - an argument eliminating into motive
        continue
      let ctorType : Expr ← ctorId.getType
      if let .some discharger := cfg.dischargers.find? ctorName then
        let dischargerSeq ← discharger.asTacticSeq
        let argnames ← forallTelescope ctorType (fun args _ => do
          args.filterMapM (fun e => do
            let decl ← e.fvarId!.getDecl
            if decl.binderInfo.isExplicit then -- discard alll implicit arguments
              return Option.some <| Lean.mkIdent (decl.userName)
            else
              return .none))
        let alt ← `( inductionAlt| | @$(Lean.mkIdent ctorName) $[$argnames]* => $dischargerSeq)
          -- try to make this fail graciously?
        altSyntax := altSyntax.push alt
    return altSyntax)

def getBranchNames (alts: Array (TSyntax ``inductionAlt)) : TacticM (NameSet) :=
  alts.foldlM (fun s => fun
  | `(inductionAlt| $[$lhss]* => $_) =>
    lhss.foldlM (fun s' => fun
    | `(inductionAltLHS| | $[@]?$ctor $[$args]*) =>
      return s'.insert ctor.getId
    | `(inductionAltLHS| | _ $[$_]*) => return s'
    -- pattern match should be exhaustive, assuming the syntax is well-kinded
    | _ => throwUnsupportedSyntax) s
  | _ => throwUnsupportedSyntax) NameSet.empty


@[tactic autoinductiontac]
def autoInductOn : Tactic
| `(tactic|autoinduction $[$t]* $[generalizing $[$g]*]? $[with $[$alts?]*]?) => withMainContext do
  let (targets, _toTag) ← elabElimTargets t
  -- let principle? ← getAutoIndPrinciple? targets
  -- unless principle?.isSome do
  if let .some (principleName,cfg) ← getAutoIndPrinciple? targets then
    let elimInfo ← withMainContext <| getElimInfo principleName
    logInfo s!"applying {principleName}"
    if let .some alts := alts? then do
      let blacklist ← getBranchNames alts
      let autoAlts ← generateMatchBranches principleName elimInfo cfg blacklist
      let inductiontac ←
        `(tactic| induction $[$t],* using $(Lean.mkIdent principleName)
          $[generalizing $g*]? with $[$(alts.append autoAlts)]*)
      evalInduction inductiontac
    else do
      let mainGoal ← getMainGoal
      let mainGoalName ← mainGoal.getTag
      let inductiontac ← `(tactic| induction $[$t],* using $(Lean.mkIdent principleName)
        $[generalizing $g*]?)

      let fullNameCfg : NameMap Term :=
        RBMap.fold (fun m n t => m.insert (mainGoalName ++ n) t) {} cfg.dischargers

      evalInduction inductiontac
      let goals ← getGoals
      for goal in goals do
        if let .some t := fullNameCfg.find? (← goal.getTag) then
          goal.withContext do
            focus <| evalTacticSeq (← `(tacticSeq| try $(← t.asTacticSeq)))
  else
    logInfo s!"no induction principle found"
| _ => throwUnsupportedSyntax

example : True := by

  · trivial
  -- trivial

--syntax (name := autoinductiontac) "autoinduction"
