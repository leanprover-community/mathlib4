import Std.Lean.Parser
import Lean.Meta.Tactic
import Mathlib.Tactic.NormNum.Core
import Mathlib.Tactic.HaveI
import Mathlib.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Invertible
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Qq

namespace Mathlib.Tactic.ByApprox


open Lean hiding Rat
open Std Lean.Parser Parser.Tactic Elab Command Elab.Tactic Meta Qq Term

initialize registerTraceClass `ByApprox

/-- Attribute for identifying `by_approx` extensions. -/
syntax (name := byApproxSyn) "by_approx " term,+ : attr

structure Bounds where
  lb : ℚ
  lb_prf : Option Expr -- : e ≥ ↑{mkRatExpr lb}
  ub : ℚ
  ub_prf : Option Expr -- : e ≤ ↑{mkRatExpr ub}


structure ByApproxExt where
  approximate (precision : ℕ) (includeProof : Bool) (e : Q(ℝ)) : MetaM Bounds

/-- Configuration for `DiscrTree`. -/
def discrTreeConfig : WhnfCoreConfig := {}

/-- Read a `by_approx` extension from a declaration of the right type. -/
def mkByApproxExt (n : Name) : ImportM ByApproxExt := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck ByApproxExt opts ``ByApproxExt n


/-- Each `by_approx` extension is labelled with a collection of patterns
which determine the expressions to which it should be applied. -/
abbrev Entry := Array (Array DiscrTree.Key) × Name

/-- Environment extensions for `by_approx` declarations -/
initialize byApproxExt : PersistentEnvExtension Entry (Entry × ByApproxExt)
    (List Entry × DiscrTree ByApproxExt) ←
  -- we only need this to deduplicate entries in the DiscrTree
  have : BEq ByApproxExt := ⟨fun _ _ => false⟩
  let insert kss v dt := kss.foldl (fun dt ks => dt.insertCore ks v discrTreeConfig) dt
  registerPersistentEnvExtension {
    mkInitial := pure ([], {})
    addImportedFn := fun s => do
      let dt ← s.foldlM (init := {}) fun dt s => s.foldlM (init := dt) fun dt (kss, n) => do
        pure (insert kss (← mkByApproxExt n) dt)
      pure ([], dt)
    addEntryFn := fun (entries, s) ((kss, n), ext) => ((kss, n) :: entries, insert kss ext s)
    exportEntriesFn := fun s => s.1.reverse.toArray
  }

initialize registerBuiltinAttribute {
  name := `byApproxSyn
  descr := "adds a by_approx extension"
  applicationTime := .afterCompilation
  add := fun declName stx kind => match stx with
    | `(attr| by_approx $es,*) => do
      unless kind == AttributeKind.global do
        throwError "invalid attribute by_approx, must be global"
      let env ← getEnv
      unless (env.getModuleIdxFor? declName).isNone do
        throwError "invalid attribute 'by_approx', declaration is in an imported module"
      if (IR.getSorryDep env declName).isSome then return -- ignore in progress definitions
      let ext ← mkByApproxExt declName
      let keys ← MetaM.run' <| es.getElems.mapM fun stx => do
        let e ← TermElabM.run' <| withSaveInfoContext <| withAutoBoundImplicit <|
          withReader ({ · with ignoreTCFailures := true }) do
            let e ← elabTerm stx none
            let (_, _, e) ← lambdaMetaTelescope (← mkLambdaFVars (← getLCtx).getFVars e)
            return e
        DiscrTree.mkPath e discrTreeConfig
      setEnv <| byApproxExt.addEntry env ((keys, declName), ext)
    | _ => throwUnsupportedSyntax
}

private lemma is_rat_to_le {r : ℝ} {n : ℤ} {d : ℕ} (h : NormNum.IsRat r n d) :
    r ≤ (n / d : ℚ) := by
  simp [h.to_raw_eq]

private lemma is_rat_to_ge {r : ℝ} {n : ℤ} {d : ℕ} (h : NormNum.IsRat r n d) :
    r ≥ (n / d : ℚ) := by
  simp [h.to_raw_eq]

partial def approximateNormNum  {α : Q(Type)} (expr : Q($α)) : MetaM Bounds := do
  let divisionRing ← NormNum.inferDivisionRing α
  let result ← Mathlib.Meta.NormNum.derive expr
  let res ← result.toRat'
  -- for some reason pattern matching here breaks lean
  let rat := res.fst
  let is_rat := res.snd.snd.snd

  return ⟨rat, ← mkAppM ``is_rat_to_ge #[is_rat], rat, ← mkAppM ``is_rat_to_le #[is_rat]⟩

partial def approximate (precision : Nat) (includeProof : Bool) (expr : Q(ℝ)) :
    MetaM Bounds := withTraceNode `ByApprox (fun _ => pure m!"Approximating {expr}") do
  try
    let bounds ← approximateNormNum (α := q(ℝ)) expr
    trace[ByApprox] "Got exact value from norm_num {bounds.lb}"
    return bounds
  catch ex => trace[ByApprox] "Failed norm_num {ex.toMessageData}"

  let matchingExtensions := ← (byApproxExt.getState (← getEnv)).2.getMatch expr discrTreeConfig

  if matchingExtensions.size = 0 then
    throwError "Could not find a by_approx extension for {expr}"

  -- TODO maybe run all and take intersection of intersections?
  if matchingExtensions.size > 1 then
    throwError "Found ambiguous by_approx extensions for {expr}"

  for extension in matchingExtensions do
    let bounds ← extension.approximate precision includeProof expr
    trace[ByApprox] "Got bounds {bounds.lb} to {bounds.ub}"
    return bounds

  throwError "todo"
