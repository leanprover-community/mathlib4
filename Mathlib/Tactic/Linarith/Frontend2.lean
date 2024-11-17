import Mathlib.Tactic.Linarith.Verification2
import Mathlib.Tactic.Linarith.Preprocessing2
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.LinearCombination


set_option autoImplicit true

open Lean Elab Tactic Meta

namespace Linarith


/-! ### Control -/

def getNeg (e : Expr) : MetaM (Expr × Expr) := do
  let (n, t, big, small) ←
  match e.getAppFnArgs with
  | (``LT.lt, #[t, _, a, b]) => pure (``LE.le, t, b, a)
  | (``LE.le, #[t, _, a, b]) => pure (``LT.lt, t, b, a)
  | (``GE.ge, #[t, _, a, b]) => pure (``LE.le, t, a, b)
  | (``GT.gt, #[t, _, a, b]) => pure (``LT.lt, t, a, b)
  | _ => throwError "goal is not a comparison"
  let z : Expr ← mkAppOptM ``OfNat.ofNat #[t, mkConst ``Nat.zero, none]
  let s : Expr ← mkAppM ``HSub.hSub #[big, small]
  pure (← mkAppM n #[s, z], t)

-- FIXME adjust hypotheses
def verifyIneqGoalWithType (g : MVarId) : MetaM (Option (Expr × Expr)) := do
  getNeg (← withReducible g.getType')

def partitionByType2 (l : List (Term × Expr)) : MetaM (ExprMultiMap (Term × Expr)) :=
  l.foldlM (fun m h => do m.insert (← typeOfIneqProof h.2) h) #[]

def runLinarith? (cfg : LinarithConfig) (prefType : Expr) (g : MVarId)
    (hyps : List (Term × Expr)) (phantomHypType : Expr) : TermElabM Syntax.Term := do
  let hyps ← preprocessAugmented defaultPreprocessors2 g hyps
  linarithTraceProofs s!"after preprocessing, linarith has {hyps.length} facts:" (hyps.map Prod.snd)
  g.withContext do
    let hyp_set ← partitionByType2 hyps
    trace[linarith] "hypotheses appear in {hyp_set.size} different types"
    trace[linarith] "preferred type is {prefType}"
    -- discard hypotheses from type other than the preferred type
    let (_, vs) ← hyp_set.find prefType
    trace[linarith] "have discarded everything but {vs}"
    findLinearCombination cfg.transparency cfg.oracle phantomHypType prefType vs

/-- Return local hypotheses which are not "implementation detail", as `Expr`s. -/
def _root_.Lean.getLocalHyps2 [Monad m] [MonadLCtx m] : m (Array (Term × Expr)) := do
  let mut hs := #[]
  for d in ← getLCtx do
    if !d.isImplementationDetail then hs := hs.push ((mkIdent d.userName : Term), d.toExpr)
  return hs

partial def linarith? (g : MVarId) : TermElabM Syntax.Term := g.withContext do
  if (← whnfR (← instantiateMVars (← g.getType))).isEq then
    trace[linarith] "target is an equality: error"
    throwError "linarith's equality proofs cannot be translated to linear_combination proofs; use polyrith instead"

  /- We consider only the linarith functionality of proving a comparison goal. We identify a
    "preferred" type, the type of the goal.
    We also receive a new variable from moving the goal to a hypothesis.
  -/

  let (phantomHypType, target_type) ← match ← verifyIneqGoalWithType g with
  | none =>
      trace[linarith] "target is not an inequality: error"
      throwError "linarith's \"exfalso\" proofs finding an internal contradiction among the hypotheses cannot directly be translated to linear_combination proofs; set up an intermediate goal of 1 < 0 instead"
  | some p => pure p

  g.withContext do
  -- set up the list of hypotheses
    let hyps ← (return (← getLocalHyps2).toList)

    linarithTraceProofs "linarith is running on the following hypotheses:" (hyps.map Prod.snd)
    runLinarith? {} target_type g hyps phantomHypType

end Linarith

/-! ### User facing functions -/

open Parser Tactic Syntax

syntax "linarith?" : tactic

elab_rules : tactic
  | `(tactic| linarith?%$tk) => withMainContext do
    let g ← Lean.Elab.Tactic.getMainGoal
    let arithTerm : Syntax.Term ← Linarith.linarith? g
    let a : Syntax.Tactic := Unhygienic.run `(tactic | linear_combination ($arithTerm))
    TryThis.addSuggestion tk a
    Mathlib.Tactic.LinearCombination.elabLinearCombination missing none none arithTerm
