import Mathlib.Init

set_option autoImplicit false

open Lean Elab

-- #synth Hashable ((TSyntax ``Parser.Tactic.tacticSeq))

def Lean.ConstantInfo.getConstantVal? (info : ConstantInfo) : Option ConstantVal :=
  match info with
  | .thmInfo val => val.toConstantVal
  | .defnInfo val => val.toConstantVal
  | _ => none

structure AutoIndPrincipleConfig where
  dischargers : NameMap Term := default

instance : Repr AutoIndPrincipleConfig where
  reprPrec x := reprPrec x.dischargers.toList

structure AutoIndPrinciple extends AutoIndPrincipleConfig where
  name : Name
  target : Expr
  deriving Repr

instance : ToString AutoIndPrinciple where
  toString := toString ∘ repr

initialize autoIndPrincipleExt :
    SimplePersistentEnvExtension AutoIndPrinciple (Array AutoIndPrinciple) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := Array.flatten
    addEntryFn := Array.push
  }

def addAutoIndPrinciple {m : Type → Type} [MonadEnv m] (a : AutoIndPrinciple) : m Unit :=
  modifyEnv (autoIndPrincipleExt.addEntry · a)

def getAutoIndPrinciples {m : Type → Type} [MonadEnv m] [Monad m] : m (Array AutoIndPrinciple) := do
  let env ← getEnv
  return autoIndPrincipleExt.getState env

open Parser

--syntax autoIndPrinciplesRest := (ppSpace "(" ident " := " term ")")*
syntax autoIndPrinciplesRest := (ppSpace "(" ident " := " term ")" )*

syntax (name := autoinduction) "autoinduction" autoIndPrinciplesRest : attr

open Command

def elabAutoIndPrinciplesRest : Syntax → CommandElabM AutoIndPrincipleConfig
  | `(autoIndPrinciplesRest| $[($ids := $ts)]*) =>
      pure ⟨.fromArray (Array.zip (ids.map fun t ↦ t.getId) ts) _⟩
  | _ => throwUnsupportedSyntax

initialize Lean.registerBuiltinAttribute {
  name := `autoinduction
  descr := "Add autoinduction principle."
  add := fun decl stx _attrKind => do
    match stx with
    | `(attr| autoinduction $c:autoIndPrinciplesRest) =>
      let cfg ← liftCommandElabM <| elabAutoIndPrinciplesRest c
      let info ← getConstInfo decl
      let val ← info.getConstantVal?.getDM <| throwError "Unsupported declaration type."
      let indPrinciple : AutoIndPrinciple :=
        { cfg with name := decl, target := val.type }
      addAutoIndPrinciple indPrinciple
    | _ => throwUnsupportedSyntax
}

elab "#autoindprinciples" : command => do
  logInfo s!"{← getAutoIndPrinciples}"
