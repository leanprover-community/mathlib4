import Mathlib.Tactic.Algebra

namespace Mathlib.Tactic.Polynomial

open Lean
open Lean.Meta Qq Lean.Elab Term

/-- Attribute for identifying `polynomial` extensions. -/
syntax (name := polynomialAttr) "polynomial " term,+ : attr

/-- An extension for `polynomial`. -/
structure PolynomialExt where
  /-- Attempts to infer the base `R` of an `Algebra R A` based only on `A`. e.g. returns `R` given
  `Polynomial R`. -/
  infer : Expr → MetaM Expr


/-- Read a `polynomial` extension from a declaration of the right type. -/
def mkPolynomialExt (n : Name) : ImportM PolynomialExt := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck PolynomialExt opts ``PolynomialExt n

/-- Each `polynomial` extension is labelled with a collection of patterns
which determine the expressions to which it should be applied. -/
abbrev Entry := Array (Array DiscrTree.Key) × Name

/-- Environment extensions for `polynomial` declarations -/
initialize polynomialExt : PersistentEnvExtension Entry (Entry × PolynomialExt)
    (List Entry × DiscrTree PolynomialExt) ←
  -- we only need this to deduplicate entries in the DiscrTree
  have : BEq PolynomialExt := ⟨fun _ _ => false⟩
  let insert kss v dt := kss.foldl (fun dt ks => dt.insertCore ks v) dt
  registerPersistentEnvExtension {
    mkInitial := pure ([], {})
    addImportedFn := fun s => do
      let dt ← s.foldlM (init := {}) fun dt s => s.foldlM (init := dt) fun dt (kss, n) => do
        pure (insert kss (← mkPolynomialExt n) dt)
      pure ([], dt)
    addEntryFn := fun (entries, s) ((kss, n), ext) => ((kss, n) :: entries, insert kss ext s)
    exportEntriesFn := fun s => s.1.reverse.toArray
  }

initialize registerBuiltinAttribute {
  name := `polynomialAttr
  descr := "adds a polynomial extension"
  applicationTime := .afterCompilation
  add := fun declName stx kind => match stx with
    | `(attr| polynomial $es,*) => do
      unless kind == AttributeKind.global do
        throwError "invalid attribute 'polynomial', must be global"
      let env ← getEnv
      unless (env.getModuleIdxFor? declName).isNone do
        throwError "invalid attribute 'polynomial', declaration is in an imported module"
      if (IR.getSorryDep env declName).isSome then return -- ignore in progress definitions
      let ext ← mkPolynomialExt declName
      let keys ← MetaM.run' <| es.getElems.mapM fun stx => do
        let e ← TermElabM.run' <| withSaveInfoContext <| withAutoBoundImplicit <|
          withReader ({ · with ignoreTCFailures := true }) do
            let e ← elabTerm stx none
            let (_, _, e) ← lambdaMetaTelescope (← mkLambdaFVars (← getLCtx).getFVars e)
            return e
        DiscrTree.mkPath e
      setEnv <| polynomialExt.addEntry env ((keys, declName), ext)
    | _ => throwUnsupportedSyntax
}


def inferBase (e : Expr) : MetaM Expr := do
  for ext in ← (polynomialExt.getState (← getEnv)).2.getMatch e do
    try
      return ← ext.infer e
    catch _ =>
      continue
  failure

end Mathlib.Tactic.Polynomial
