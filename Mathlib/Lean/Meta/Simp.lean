/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Gabriel Ebner, Floris van Doorn
-/
import Batteries.Tactic.OpenPrivate
import Lean.Elab.Tactic.Simp
import Lean.Meta.Tactic.NormCast

/-!
# Helper functions for using the simplifier.

[TODO] Needs documentation, cleanup, and possibly reunification of `mkSimpContext'` with core.
-/

set_option autoImplicit true

open Lean Elab.Tactic

def Lean.PHashSet.toList [BEq α] [Hashable α] (s : Lean.PHashSet α) : List α :=
  s.1.toList.map (·.1)

namespace Lean

namespace Meta.Simp
open Elab.Tactic

instance : ToFormat SimpTheorems where
  format s :=
f!"pre:
{s.pre.values.toList}
post:
{s.post.values.toList}
lemmaNames:
{s.lemmaNames.toList.map (·.key)}
toUnfold: {s.toUnfold.toList}
erased: {s.erased.toList.map (·.key)}
toUnfoldThms: {s.toUnfoldThms.toList}"

/--
Constructs a proof that the original expression is true
given a simp result which simplifies the target to `True`.
-/
def Result.ofTrue (r : Simp.Result) : MetaM (Option Expr) :=
  if r.expr.isConstOf ``True then
    some <$> match r.proof? with
    | some proof => mkOfEqTrue proof
    | none => pure (mkConst ``True.intro)
  else
    pure none

/-- Return all propositions in the local context. -/
def getPropHyps : MetaM (Array FVarId) := do
  let mut result := #[]
  for localDecl in (← getLCtx) do
    unless localDecl.isAuxDecl do
      if (← isProp localDecl.type) then
        result := result.push localDecl.fvarId
  return result

export private mkSimpTheoremsFromConst from Lean.Meta.Tactic.Simp.SimpTheorems

/-- Similar to `addSimpTheorem` except that it returns an array of all auto-generated
  simp-theorems. -/
def addSimpTheorem' (ext : SimpExtension) (declName : Name) (post : Bool) (inv : Bool)
    (attrKind : AttributeKind) (prio : Nat) : MetaM (Array Name) := do
  let simpThms ← mkSimpTheoremsFromConst declName post inv prio
  for simpThm in simpThms do
    ext.add (SimpEntry.thm simpThm) attrKind
  return simpThms.filterMap (·.proof.constName?)

/-- Similar to `AttributeImpl.add` in `mkSimpAttr` except that it doesn't require syntax,
  and returns an array of all auto-generated lemmas. -/
def addSimpAttr (declName : Name) (ext : SimpExtension) (attrKind : AttributeKind)
    (post : Bool) (prio : Nat) :
    MetaM (Array Name) := do
  let info ← getConstInfo declName
  if (← isProp info.type) then
    addSimpTheorem' ext declName post (inv := false) attrKind prio
  else if info.hasValue then
    if let some eqns ← getEqnsFor? declName then
      let mut auxNames := #[]
      for eqn in eqns do
        -- Is this list is always empty?
        let newAuxNames ← addSimpTheorem' ext eqn post (inv := false) attrKind prio
        auxNames := auxNames ++ newAuxNames
      ext.add (SimpEntry.toUnfoldThms declName eqns) attrKind
      if hasSmartUnfoldingDecl (← getEnv) declName then
        ext.add (SimpEntry.toUnfold declName) attrKind
      return auxNames
    else
      ext.add (SimpEntry.toUnfold declName) attrKind
      return #[]
  else
    throwError "invalid 'simp', it is not a proposition nor a definition (to unfold)"

/-- Similar to `AttributeImpl.add` in `mkSimpAttr` except that it returns an array of all
  auto-generated lemmas. -/
def addSimpAttrFromSyntax (declName : Name) (ext : SimpExtension) (attrKind : AttributeKind)
    (stx : Syntax) : MetaM (Array Name) := do
  let post := if stx[1].isNone then true else stx[1][0].getKind == ``Lean.Parser.Tactic.simpPost
  let prio ← getAttrParamOptPrio stx[2]
  addSimpAttr declName ext attrKind post prio

end Simp

/- Hack: modify `norm_cast` internals so that they return the generated simp lemmas.
Hopefully Core is willing to upstream this? -/
namespace NormCast

open Simp

/-- `addElim decl` adds `decl` as an `elim` lemma to be used by `norm_cast`. -/
def addElim' (decl : Name)
    (kind := AttributeKind.global) (prio := eval_prio default) : MetaM (Array Name) :=
  addSimpTheorem' normCastExt.up decl (post := true) (inv := false) kind prio

/-- `addMove decl` adds `decl` as a `move` lemma to be used by `norm_cast`. -/
def addMove' (decl : Name)
    (kind := AttributeKind.global) (prio := eval_prio default) : MetaM (Array Name) := do
  let s1 ← addSimpTheorem' pushCastExt decl (post := true) (inv := false) kind prio
  let s2 ← addSimpTheorem' normCastExt.up decl (post := true) (inv := true) kind prio
  let s3 ← addSimpTheorem' normCastExt.down decl (post := true) (inv := false) kind prio
  return s1 ++ s2 ++ s3

/-- `addSquash decl` adds `decl` as a `squash` lemma to be used by `norm_cast`. -/
def addSquash' (decl : Name)
    (kind := AttributeKind.global) (prio := eval_prio default) : MetaM (Array Name) := do
  let s1 ← addSimpTheorem' pushCastExt decl (post := true) (inv := false) kind prio
  let s2 ← addSimpTheorem' normCastExt.squash decl (post := true) (inv := false) kind prio
  let s3 ← addSimpTheorem' normCastExt.down decl (post := true) (inv := false) kind prio
  return s1 ++ s2 ++ s3

/-- `addInfer decl` infers the label of `decl` (`elim`, `move`, or `squash`) and arranges for it to
be used by `norm_cast`.

* elim lemma:   LHS has 0 head coes and ≥ 1 internal coe
* move lemma:   LHS has 1 head coe and 0 internal coes,    RHS has 0 head coes and ≥ 1 internal coes
* squash lemma: LHS has ≥ 1 head coes and 0 internal coes, RHS has fewer head coes
-/
def addInfer' (decl : Name)
    (kind := AttributeKind.global) (prio := eval_prio default) : MetaM (Array Name) := do
  let ty := (← getConstInfo decl).type
  match ← classifyType ty with
  | Label.elim => addElim' decl kind prio
  | Label.squash => addSquash' decl kind prio
  | Label.move => addMove' decl kind prio

/-- Similar to `AttributeImpl.add` in the `norm_cast`-attribute
  except that it returns an array of all auto-generated lemmas. -/
def addNormCastAttrFromSyntax (decl : Name) (kind : AttributeKind)
    (stx : Syntax) : MetaM (Array Name) := do
    let `(attr| norm_cast $[$label:normCastLabel]? $[$prio]?) := stx | unreachable!
    let prio := (prio.bind (·.1.isNatLit?)).getD (eval_prio default)
    match label.bind (·.1.isStrLit?) with
    | "elim" => addElim' decl kind prio
    | "move" => addMove' decl kind prio
    | "squash" => addSquash' decl kind prio
    | none => addInfer' decl kind prio
    | _ => unreachable!

end NormCast

/-- Construct a `SimpTheorems` from a list of names. -/
def simpTheoremsOfNames (lemmas : List Name := []) (simpOnly : Bool := false) :
    MetaM SimpTheorems := do
  lemmas.foldlM (·.addConst ·)
    (← if simpOnly then
      simpOnlyBuiltins.foldlM (·.addConst ·) {}
    else
      getSimpTheorems)

-- TODO We need to write a `mkSimpContext` in `MetaM`
-- that supports all the bells and whistles in `simp`.
-- It should generalize this, and another partial implementation in `Tactic.Simps.Basic`.

/-- Construct a `Simp.Context` from a list of names. -/
def Simp.Context.ofNames (lemmas : List Name := []) (simpOnly : Bool := false)
    (config : Simp.Config := {}) : MetaM Simp.Context := do pure <|
  { simpTheorems := #[← simpTheoremsOfNames lemmas simpOnly],
    congrTheorems := ← Lean.Meta.getSimpCongrTheorems,
    config := config }

/-- Simplify an expression using only a list of lemmas specified by name. -/
def simpOnlyNames (lemmas : List Name) (e : Expr) (config : Simp.Config := {}) :
    MetaM Simp.Result := do
  (·.1) <$> simp e (← Simp.Context.ofNames lemmas true config)

/--
Given a simplifier `S : Expr → MetaM Simp.Result`,
and an expression `e : Expr`, run `S` on the type of `e`, and then
convert `e` into that simplified type,
using a combination of type hints as well as casting if the proof is not definitional `Eq.mp`.

The optional argument `type?`, if present, must be definitionally equal to the type of `e`.
When it is specified we simplify this type rather than the inferred type of `e`.
-/
def simpType (S : Expr → MetaM Simp.Result) (e : Expr) (type? : Option Expr := none) :
    MetaM Expr := do
  let type ← type?.getDM (inferType e)
  match ← S type with
  | ⟨ty', none, _⟩ => mkExpectedTypeHint e ty'
  -- We use `mkExpectedTypeHint` in this branch as well, in order to preserve the binder types.
  | ⟨ty', some prf, _⟩ => mkExpectedTypeHint (← mkEqMP prf e) ty'

/-- Independently simplify both the left-hand side and the right-hand side
of an equality. The equality is allowed to be under binders.
Returns the simplified equality and a proof of it. -/
def simpEq (S : Expr → MetaM Simp.Result) (type pf : Expr) : MetaM (Expr × Expr) := do
  forallTelescope type fun fvars type => do
    let .app (.app (.app (.const `Eq [u]) α) lhs) rhs := type | throwError "simpEq expecting Eq"
    let ⟨lhs', lhspf?, _⟩ ← S lhs
    let ⟨rhs', rhspf?, _⟩ ← S rhs
    let mut pf' := mkAppN pf fvars
    if let some lhspf := lhspf? then
      pf' ← mkEqTrans (← mkEqSymm lhspf) pf'
    if let some rhspf := rhspf? then
      pf' ← mkEqTrans pf' rhspf
    let type' := mkApp3 (mkConst ``Eq [u]) α lhs' rhs'
    return (← mkForallFVars fvars type', ← mkLambdaFVars fvars pf')

/-- Checks whether `declName` is in `SimpTheorems` as either a lemma or definition to unfold. -/
def SimpTheorems.contains (d : SimpTheorems) (declName : Name) :=
  d.isLemma (.decl declName) || d.isDeclToUnfold declName

/-- Tests whether `decl` has `simp`-attribute `simpAttr`. Returns `false` is `simpAttr` is not a
valid simp-attribute. -/
def isInSimpSet (simpAttr decl : Name) : CoreM Bool := do
  let .some simpDecl ← getSimpExtension? simpAttr | return false
  return (← simpDecl.getTheorems).contains decl

/-- Returns all declarations with the `simp`-attribute `simpAttr`.
  Note: this also returns many auxiliary declarations. -/
def getAllSimpDecls (simpAttr : Name) : CoreM (List Name) := do
  let .some simpDecl ← getSimpExtension? simpAttr | return []
  let thms ← simpDecl.getTheorems
  return thms.toUnfold.toList ++ thms.lemmaNames.toList.filterMap fun
    | .decl decl => some decl
    | _ => none

/-- Gets all simp-attributes given to declaration `decl`. -/
def getAllSimpAttrs (decl : Name) : CoreM (Array Name) := do
  let mut simpAttrs := #[]
  for (simpAttr, simpDecl) in (← simpExtensionMapRef.get).toList do
    if (← simpDecl.getTheorems).contains decl then
      simpAttrs := simpAttrs.push simpAttr
  return simpAttrs

end Lean.Meta
