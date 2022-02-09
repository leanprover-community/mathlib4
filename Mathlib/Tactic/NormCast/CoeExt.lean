import Lean
open Lean Meta Std

namespace Tactic.NormCast

structure CoeFnInfo where
  numArgs : Nat
  coercee : Nat
  deriving Inhabited

instance : ToExpr CoeFnInfo where
  toTypeExpr := mkSort levelOne
  toExpr := fun (CoeFnInfo.mk a b) => mkApp2 (mkConst ``CoeFnInfo.mk) (toExpr a) (toExpr b)

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
    pure { numArgs := fnInfo.getArity, coercee := fnInfo.getArity - 1 }
  modifyEnv (coeExt.addEntry · (name, info))
  addCoeDelaborator name info

namespace Attr
syntax (name := coe) "coe" : attr
end Attr

initialize registerBuiltinAttribute {
  name := `coe
  descr := "Adds a definition as a coercion"
  add := fun decl stx kind => MetaM.run' do
    unless kind == AttributeKind.global do
      throwError "cannot add local or scoped coe attribute"
    registerCoercion decl
}
