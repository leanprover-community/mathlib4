/-
Copyright (c) 2025 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
import Lean.Elab.Term.TermElabM
import Lean.Meta.Tactic.Simp.Attr
import Mathlib.Init

/-!
# Setup for the `polynomial` tactic

This file initializes the environment extensions and simp sets used by the `polynomial` tactic.

These extensions let downstream users use their own polynomial-like types (such as `PowerSeries`)
with the `polynomial` tactic suite.

-/
namespace Mathlib.Tactic.Polynomial

open Lean
open Lean.Meta Lean.Elab Term


/-- Attribute for identifying `polynomial` preprocessing extensions. These serve the purpose of
removing any definitions specific to polynomials that `algebra` can't handle.
e.g. `Polynomial.C` and `Polynomial.map` -/
initialize polynomialPreExt : SimpExtension ←
  registerSimpAttr `polynomial_pre "\
    The `polynomial_pre` simp attribute uses preprocessing lemmas \
    to turn specialized functions into `algebraMap`s"

/-- Attribute for identifying `polynomial` postprocessing extensions. Used only by polynomial_nf.
These serve the purpose of rewriting expressions in `algebra` normal form into a more readable form.
e.g. `a • X` -> `algebraMap _ _ a * X` -> `C a * X`. -/
initialize polynomialPostExt : SimpExtension ←
  registerSimpAttr `polynomial_post "\
    The `polynomial_post` simp attribute uses postprocessing lemmas \
    to turn `algebraMap`s into more specialized functions."

/-- Attribute for identifying `polynomial` extensions. Used to tag procedures that infer the base
ring of polynomial-like types. -/
syntax (name := inferPolyBaseAttr) "infer_polynomial_base" : attr

/-- An extension for `polynomial`. -/
structure PolynomialExt where
  /-- Attempts to infer the base `R` of an `Algebra R A` based only on `A`. e.g. returns `R` given
  `Polynomial R`. -/
  infer : Expr → MetaM Expr

/-- Read a `polynomial` extension from a declaration of the right type. -/
def mkPolynomialExt (n : Name) : ImportM PolynomialExt := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck PolynomialExt opts ``PolynomialExt n


/-- Environment extensions for `polynomial` declarations -/
initialize polynomialExt : PersistentEnvExtension Name (Name × PolynomialExt)
    (List Name × List (Name × PolynomialExt)) ←
  registerPersistentEnvExtension {
    mkInitial := pure ([], {})
    addImportedFn := fun s => do
      let dt ← s.foldlM (init := {}) fun dt s => s.foldlM (init := dt) fun dt n => do
        return (n, ← mkPolynomialExt n) :: dt
      pure ([], dt)
    addEntryFn := fun (entries, s) (n, ext) => (n :: entries, (n, ext) :: s)
    exportEntriesFn := fun s => s.1.reverse.toArray
  }

initialize registerBuiltinAttribute {
  name := `inferPolyBaseAttr
  descr := "adds a polynomial extension that infers the base ring of a polynomial-like type"
  applicationTime := .afterCompilation
  add := fun declName stx kind => match stx with
    | `(attr| infer_polynomial_base) => do
      unless kind == AttributeKind.global do
        throwError "invalid attribute infer_polynomial_base', must be global"
      let env ← getEnv
      unless (env.getModuleIdxFor? declName).isNone do
        throwError "invalid attribute 'infer_polynomial_base', declaration is in an imported module"
      if (IR.getSorryDep env declName).isSome then return -- ignore in progress definitions
      let ext ← mkPolynomialExt declName
      setEnv <| polynomialExt.addEntry env (declName, ext)
    | _ => throwUnsupportedSyntax
}

/-- Infer the base ring of `Polynomial`-like types that are registered using the `polynomial`
environment extensions. Includes e.g. `Polynomial` and `MvPolynomial`. -/
def inferBase (e : Expr) : MetaM Expr := do
  for ⟨_, ext⟩ in (polynomialExt.getState (← getEnv)).2 do
    try
      return ← ext.infer e
    catch _ =>
      continue
  failure

end Mathlib.Tactic.Polynomial
