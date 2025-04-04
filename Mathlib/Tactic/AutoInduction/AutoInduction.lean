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
syntax (name := autoinductiontac) "autoinduction" term
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
def AutoIndPrinciple.generateMatchBranches {m} [Monad m] [MonadControlT MetaM m]
    [MonadLiftT MetaM m] [MonadRef m] [MonadQuotation m] (_a : AutoIndPrinciple)
    (blacklist : NameSet):
    m (Array (TSyntax ``inductionAlt)) := do
  forallTelescope _a.target (fun ctors _ => do
    let mut alts : Array (TSyntax ``inductionAlt) := #[]
    for ctorFVar in ctors do
      let ctorId : FVarId := ctorFVar.fvarId!
      let ctorName : Name ← ctorId.getUserName
      let ctorType : Expr ← ctorId.getType
      if let .some discharger := _a.dischargers.find? ctorName then
        if !(blacklist.contains ctorName) then
          let dischargerSeq ← discharger.asTacticSeq
          let argnames ← forallTelescope ctorType (fun args _ => do
            args.mapM (fun e => Lean.mkIdent <$> e.fvarId!.getUserName))
          let alt ← `( inductionAlt| | @$(Lean.mkIdent ctorName) $[$argnames]* => $dischargerSeq)
            -- try to make this fail graciously?
          alts := alts.push alt
    return alts)

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


def AutoIndPrinciple.matches (_a : AutoIndPrinciple) (_e : Expr) : MetaM Bool :=
  pure true


@[tactic autoinductiontac]
def autoInductOn : Tactic
| `(tactic|autoinduction $t $[generalizing $[$g]*]? $[with $[$alts?]*]?) => withMainContext do
  let e ← elabTerm t none
  let ty ← inferType e
  logInfo s!"Found expression {e} with inferred type {ty}."
  let ps ← getAutoIndPrinciples
  let mut principle? : Option AutoIndPrinciple := .none

  -- find an induction principle
  for principle' in ps do
    if (← principle'.matches ty) then
      principle? := .some principle'
      break

  if let .some principle := principle? then
    logInfo s!"applying {principle.name}"
    if let .some alts := alts? then do
      let blacklist ← getBranchNames alts
      let autoAlts ← principle.generateMatchBranches blacklist
      let inductiontac ←
        `(tactic| induction $t:term $[generalizing $g*]?
          with $[$(alts.append autoAlts)]*)
      -- now, run the tactic
      sorry
    else do
      let inductiontac ← `(tactic| induction $t:term $[generalizing $g*]?)
      -- run the tactic
      -- try running dischargers on the appropriate new goals
      sorry



  else
    logInfo s!"no induction principle found"
| _ => throwUnsupportedSyntax

example : True := by
  induction 3 with
  | zero => ?zero'
  | succ n => ?succ'
  · trivial
  · trivial
  -- trivial

--syntax (name := autoinductiontac) "autoinduction"
