/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public meta import Mathlib.Lean.Meta.Basic
public meta import Mathlib.Lean.Meta.Simp
public import Mathlib.Tactic.Translate.Attributes
public import Mathlib.Util.AddRelatedDecl

/-!
# Transformations of theorem proofs

A registered `Transformation` operates on an elaborated `Proof`, independently of declaration
creation or the scheduling of a family of lemmas. `Proof` retains the intended type: definitional
simplification can change a statement without changing its proof term.

`transform_lemma` and `transform_lemma%` are explicit interfaces to the registry. For example,
`@[transform_lemma map]` uses a transformation registered by importing the category-theory client.
Arguments in `transform_lemma specialize_map[myFunctor]` are names of declarations; interpreting
them belongs to the client. Each request has an identity, arguments, and an optional naming suffix.

Returning `.error reason` means that a transformation is inapplicable. Exceptions are implementation
or elaboration errors and propagate to the caller. Unsuccessful applications restore elaboration
state. Named applications additionally run preparation and finalization, whereas term applications
leave metavariables available to the surrounding elaborator.

For a simple congruence step, `ofTemplate` combines a proof helper with a chosen simplifier.
More involved clients can supply their own operation, for example to specialize parameters.
-/

public meta section

open Lean Meta Elab Term

namespace Mathlib.Tactic.TheoremTransform

/-- An elaborated proof and its intended (possibly normalized) type. -/
structure Proof where
  type : Expr
  value : Expr

/-- Infer the type when first entering the transformation machinery. -/
def Proof.ofExpr (value : Expr) : MetaM Proof := return ⟨← inferType value, value⟩

/-- Preserve the intended type when passing a proof to an expression-only interface. -/
def Proof.toExpr (p : Proof) : MetaM Expr := mkExpectedTypeHint p.value p.type

/-- Apply an operation beneath all forall binders, preserving their binder information. -/
def underForall (p : Proof) (f : Proof → TermElabM (Except MessageData Proof)) :
    TermElabM (Except MessageData Proof) :=
  forallTelescopeReducing p.type (whnfType := true) fun xs type => do
    let type := (← instantiateMVars type).consumeMData
    match ← f ⟨type, mkAppN p.value xs⟩ with
    | .error reason => return .error reason
    | .ok p => return .ok ⟨← mkForallFVars xs p.type, ← mkLambdaFVars xs p.value⟩

/-- Normalize the two sides independently, so a reflexive equality remains an equality. -/
def Proof.simpEq (p : Proof) (simp : Expr → MetaM Simp.Result) : MetaM Proof := do
  let (type, value) ← Meta.simpEq simp p.type p.value
  return ⟨type, value⟩

/-- Normalize with pending instances available locally, then defer any remaining synthesis.
Type hints carry both the proof and its normalized type through temporary local instances. -/
def normalizeWithInstances (p : Proof) (instances : Array MVarId)
    (normalize : Proof → MetaM Proof) : TermElabM Proof := do
  let rec go : List MVarId → MetaM Expr
    | [] => do (← normalize p).toExpr
    | inst :: rest => do
      let (value, ()) ← withEnsuringLocalInstance inst do
        return (← go rest, ())
      return value
  let value ← go instances.toList
  for inst in instances do
    unless ← synthesizeInstMVarCore inst do
      registerSyntheticMVarWithCurrRef inst (.typeClass none)
  Proof.ofExpr value

/-- A transformation request. Arguments and suffix are part of its identity. -/
structure Request where
  transformation : Name
  args : Array Name := #[]
  suffix? : Option String := none
  deriving BEq, Inhabited, Repr

/-- Generalize fresh universe metavariables without renaming source universe parameters. -/
def generalize (p : Proof) (levels : List Name) : TermElabM (Expr × List Name) := do
  let r := (← getMCtx).levelMVarToParam levels.contains (fun _ => false) (← p.toExpr)
  setMCtx r.mctx
  return (r.expr, levels ++ r.newParamNames.toList)

/-- A proof transformation, its default naming policy, and its named-declaration hooks.
Normalization belongs to `apply`; it is independent of registering the result as a simp lemma.
The hooks are not run by the term elaborator. -/
structure Transformation where
  suffix : String
  apply : Request → Proof → TermElabM (Except MessageData Proof)
  prepare : Proof → List Name → TermElabM (Proof × List Name) := fun p levels => pure (p, levels)
  finalize : Proof → List Name → TermElabM (Expr × List Name) := generalize

private initialize transformations : IO.Ref (NameMap Transformation) ← IO.mkRef {}

/-- Register a transformation under a stable name. Registration does not add it to any bundle.
Use this from an `initialize` command, so importing the module also registers the transformation. -/
def register (name : Name) (transformation : Transformation) : IO Unit := do
  if (← transformations.get).contains name then
    throw <| IO.userError s!"theorem transformation '{name}' is already registered"
  transformations.modify (·.insert name transformation)

/-- Look up a transformation explicitly; registry iteration never determines generation order. -/
def getTransformation (name : Name) : CoreM Transformation := do
  let some transformation := (← transformations.get).find? name |
    throwError "unknown theorem transformation '{name}'"
  return transformation

/-- Name one step of a transformation path. -/
def Request.targetName (request : Request) (source : Name) : CoreM Name := do
  let transformation ← getTransformation request.transformation
  return source.appendAfter (request.suffix?.getD transformation.suffix)

/-- Apply once, restoring state on inapplicability or an exception. Only explicit inapplicability
is returned to the scheduler; implementation errors are never interpreted as failed probes. -/
def apply? (request : Request) (p : Proof) : TermElabM (Except MessageData Proof) := do
  let transformation ← getTransformation request.transformation
  let saved ← Term.saveState
  try
    let result ← transformation.apply request p
    if result matches .error _ then saved.restore (restoreInfo := true)
    return result
  catch ex =>
    saved.restore (restoreInfo := true)
    throw ex

/-- An explicit transformation reports why it does not apply. -/
def apply (request : Request) (p : Proof) : TermElabM Proof := do
  match ← apply? request p with
  | .ok p => return p
  | .error reason => throwError reason

/-- Generate a related declaration, constructing the proof only once. Failed applicability does
not create declarations or declaration ranges. `addRelatedDecl` handles collisions, documentation,
protected status, source locations, generated-declaration checks, and attribute propagation. -/
def addDecl? (request : Request) (src : Name) (ref : Syntax) (attrs : TSyntax ``optAttrArg) :
    MetaM (Except MessageData Name) := do
  let transformation ← getTransformation request.transformation
  let info ← withoutExporting <| getConstInfo src
  let result : Except MessageData (Expr × List Name) ← TermElabM.run' <| withSynthesize do
    let saved ← Term.saveState
    let p ← Proof.ofExpr (.const src (info.levelParams.map mkLevelParam))
    let (p, levels) ← transformation.prepare p info.levelParams
    match ← apply? request p with
    | .error reason =>
      saved.restore (restoreInfo := true)
      return .error reason
    | .ok p => return .ok (← transformation.finalize p levels)
  match result with
  | .error reason => return .error reason
  | .ok result =>
    let tgt ← request.targetName src
    addRelatedDecl src tgt ref attrs fun _ _ => pure result
    return .ok tgt

/-- Named interface for explicitly requested transformations. -/
def addDecl (request : Request) (src : Name) (ref : Syntax) (attrs : TSyntax ``optAttrArg) :
    MetaM Name := do
  match ← addDecl? request src ref attrs with
  | .ok name => return name
  | .error reason => throwError reason

/-- Shared term driver. In particular, do not eagerly synthesize all metavariables before a
rewrite target has had a chance to determine the source parameters. -/
def elabTerm (request : Request) (term : Term) : TermElabM Expr := do
  let value ← withSynthesizeLight <| Term.elabTerm term none
  (← apply request (← Proof.ofExpr value)).toExpr

/-- Register a congruence helper and its normalization policy. `proofArg` is the zero-based
position of the proof argument in the helper's telescope; all earlier arguments are inferred.
Any later arguments become binders of the result. Use a custom operation for helpers needing
special instance handling or parameter specialization. -/
def ofTemplate (suffix : String) (helper : Name) (proofArg : Nat)
    (simp : Expr → MetaM Simp.Result) : Transformation where
  suffix := suffix
  apply request p := underForall p fun p => do
    unless request.args.isEmpty do throwError "this proof template takes no arguments"
    let helper ← mkConstWithFreshMVarLevels helper
    let (args, infos, _) ← forallMetaBoundedTelescope (← inferType helper) (proofArg + 1)
    unless args.size == proofArg + 1 do
      throwError "proof argument is outside the helper's telescope"
    let arg := args[proofArg]!
    unless ← isDefEq (← inferType arg) p.type do
      return .error m!"the proof template for '{request.transformation}' does not apply"
    arg.mvarId!.assign p.value
    let mut instances := #[]
    for (arg, info) in args.zip infos do
      if info.isInstImplicit then
        arg.mvarId!.setKind .synthetic
        instances := instances.push arg.mvarId!
    let p ← Proof.ofExpr (mkAppN helper args)
    return .ok (← normalizeWithInstances p instances (·.simpEq simp))

/-- A registered transformation, optional declaration arguments, and an optional suffix. -/
syntax request := ident ("[" ident,* "]")? (atomic(" (" &"suffix" " := " str ")"))?

/-- Resolve declaration arguments without elaborating the source proof again. -/
def elabRequest : TSyntax ``request → TermElabM Request
  | `(request| $name:ident $[[$args:ident,*]]? $[(suffix := $suffix:str)]?) => do
    return { transformation := name.getId
             args := ← args.toArray.flatMap (·.getElems) |>.mapM resolveGlobalConstNoOverload
             suffix? := suffix.map (·.getString) }
  | _ => throwUnsupportedSyntax

/-- Explicitly apply a registered theorem transformation. Additional attributes apply to both
source and result, just as for `reassoc (attr := ...)`. -/
syntax (name := transformLemma) "transform_lemma " request optAttrArg : attr

private def transformLemmaImpl (src : Name) (ref : Syntax) (kind : AttributeKind) : AttrM Name :=
  match ref with
  | `(attr| transform_lemma $request $attrs) => MetaM.run' do
    unless kind == .global do throwAttrMustBeGlobal `transform_lemma kind
    let request ← TermElabM.run' <| elabRequest request
    addDecl request src ref attrs
  | _ => throwUnsupportedSyntax

initialize
  registerGeneratingAttr `transformLemma ((#[·]) <$> transformLemmaImpl · · ·)
  registerBuiltinAttribute {
    name := `transformLemma
    descr := "apply a registered theorem transformation"
    applicationTime := .afterCompilation
    add := fun src ref kind => discard <| transformLemmaImpl src ref kind }

/-- Apply a registered transformation within a proof, including parameterized transformations. -/
elab "transform_lemma% " request:request term:term : term => do
  elabTerm (← elabRequest request) term

end Mathlib.Tactic.TheoremTransform
