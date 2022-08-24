import Lean
open Lean Meta Std

namespace Tactic.NormCast

inductive CoeFnType
  | coe | coeFn | coeSort
  deriving Inhabited, Repr, DecidableEq

instance : ToExpr CoeFnType where
  toTypeExpr := mkConst ``CoeFnType
  toExpr := open CoeFnType in fun
    | coe => mkConst ``coe
    | coeFn => mkConst ``coeFn
    | coeSort => mkConst ``coeSort

structure CoeFnInfo where
  numArgs : Nat
  coercee : Nat
  type : CoeFnType
  deriving Inhabited, Repr

instance : ToExpr CoeFnInfo where
  toTypeExpr := mkConst ``CoeFnInfo
  toExpr := fun (CoeFnInfo.mk a b c) => mkApp3 (mkConst ``CoeFnInfo.mk) (toExpr a) (toExpr b) (toExpr c)

initialize coeExt : SimpleScopedEnvExtension (Name × CoeFnInfo) (NameMap CoeFnInfo) ←
  registerSimpleScopedEnvExtension {
    name := `coe
    addEntry := fun st (n, i) => st.insert n i
    initial := {}
  }

def getCoeFnInfo? (fn : Name) : CoreM (Option CoeFnInfo) :=
  return (coeExt.getState (← getEnv)).find? fn

open PrettyPrinter.Delaborator SubExpr

def coeDelaborator (info : CoeFnInfo) : Delab := whenPPOption getPPCoercions do
  match info.type with
  | CoeFnType.coeFn =>
    unless (← getExpr).getAppNumArgs > info.numArgs do failure
    let coercee ← withNaryArg info.coercee delab
    let kinds ← getParamKinds
    let mut args := #[]
    for i in [info.numArgs:kinds.size] do
      if (kinds.get? i).all (·.bInfo.isExplicit) then
        args := args.push (← withNaryArg i delab)
    if args.isEmpty then failure
    `($coercee $args*)
  | _ =>
    unless (← getExpr).getAppNumArgs == info.numArgs do failure
    let coercee ← withNaryArg info.coercee delab
    `(↑ $coercee)

def addCoeDelaborator (name : Name) (info : CoeFnInfo) : MetaM Unit := do
  let delabName := name ++ `delaborator
  addAndCompile <| Declaration.defnDecl {
    name := delabName
    levelParams := []
    type := mkConst ``Delab
    value := mkApp (mkConst ``coeDelaborator) (toExpr info)
    hints := ReducibilityHints.opaque
    safety := DefinitionSafety.safe
  }
  let kind := `app ++ name
  Attribute.add delabName `delab (Unhygienic.run `(attr| delab $(mkIdent kind):ident))

def registerCoercion (name : Name) (info : Option CoeFnInfo := none) : MetaM Unit := do
  let info ← match info with | some info => pure info | none => do
    let fnInfo ← getFunInfo (← mkConstWithLevelParams name)
    unless fnInfo.getArity > 0 do throwError "{name} not of function type"
    pure { numArgs := fnInfo.getArity, coercee := fnInfo.getArity - 1, type := CoeFnType.coe }
  modifyEnv (coeExt.addEntry · (name, info))
  addCoeDelaborator name info

namespace Attr
syntax (name := coe) "coe" : attr
end Attr

initialize registerBuiltinAttribute {
  name := `coe
  descr := "Adds a definition as a coercion"
  add := fun decl _stx kind => MetaM.run' do
    unless kind == AttributeKind.global do
      throwError "cannot add local or scoped coe attribute"
    registerCoercion decl
}
