import Mathlib.Init
import Lean.Meta.Tactic.ElimInfo

set_option autoImplicit false
set_option linter.unusedVariables false -- TODO : remove

open Lean Elab

-- #synth Hashable ((TSyntax ``Parser.Tactic.tacticSeq))

def Lean.ConstantInfo.getConstantVal? (info : ConstantInfo) : Option ConstantVal :=
  match info with
  | .thmInfo val => val.toConstantVal
  | .defnInfo val => val.toConstantVal
  | _ => none

open Parser Tactic in
structure AutoIndPrincipleConfig where
  dischargers : NameMap (TSyntax ``tacticSeq) := default
deriving Inhabited

instance : Repr AutoIndPrincipleConfig where
  reprPrec x := reprPrec <| x.dischargers.toList.map (fun z => (z.fst,
    toString (Syntax.prettyPrint z.snd)))

-- no need to store the type, we can ask that from the environment when we need it
structure AutoIndPrinciple extends AutoIndPrincipleConfig, Meta.CustomEliminator where
  induction := true
  hinduction : induction = true := by rfl -- for sanity
deriving Repr

instance : Inhabited AutoIndPrinciple where
  default := {(default : Meta.CustomEliminator) with induction := true}

instance : ToString AutoIndPrinciple where
  toString := toString ∘ repr

structure AutoIndPrinciples where
  map : SMap (Array Name) (Name × AutoIndPrincipleConfig) := {}
deriving Inhabited, Repr

instance : ToString AutoIndPrinciples where
  toString := toString ∘ repr


initialize autoIndPrincipleExt :
    SimpleScopedEnvExtension AutoIndPrinciple AutoIndPrinciples ←
  registerSimpleScopedEnvExtension {
    name := `autoIndPrincipleExt
    initial := {}
    addEntry principles principle := {
      map := principles.map.insert
        principle.typeNames ⟨principle.elimName, principle.toAutoIndPrincipleConfig⟩}
    finalizeImport := fun { map := map } => { map := map.switch }
  }

def addAutoIndPrinciple {m : Type → Type} [MonadEnv m] (a : AutoIndPrinciple) : m Unit :=
  modifyEnv (autoIndPrincipleExt.addEntry · a)

open Parser Meta Tactic

syntax autoIndPrinciplesRest := (ppSpace "(" ident " := ""by " tacticSeq ")" )*

syntax (name := autoinduction) "autoinduction" autoIndPrinciplesRest : attr

open Command

def elabAutoIndPrinciplesRest (elimInfo : ElimInfo) : Syntax → CommandElabM AutoIndPrincipleConfig
  | `(autoIndPrinciplesRest| $[($ids := by $ts)]*) => do
    -- let allowedAlts : NameSet := .fromArray
    --   (elimInfo.altsInfo.filter (·.provesMotive) |>.map (·.name)) _
    let mut allowedAlts : NameSet := {}
    for alt in elimInfo.altsInfo do
      if alt.provesMotive then do
        allowedAlts := allowedAlts.insert alt.name
        -- if let .some fullname := alt.declName? then
        --   allowedAlts := allowedAlts.insert fullname

    let mut userArgs : NameMap (TSyntax ``tacticSeq) := {}
    let ts' : Array (TSyntax ``tacticSeq) := ts.map (.mk ·.raw.mkSynthetic)
    for (name, t) in (ids.map (·.getId)).zip ts' do
      unless allowedAlts.contains name do
        throwError s!"{name} is not the name of an induction alternative"
      userArgs := userArgs.insert name t
    return ⟨userArgs⟩
  | _ => throwUnsupportedSyntax

def elabAutoIndPrincipleAttr (elimName : Name) (stx: Syntax) (_kind : AttributeKind) : MetaM Unit:=
  match stx with
  | `(attr | autoinduction $cfgStx) => do
    let elimInfo ← getElimInfo elimName
    let info ← getConstInfo elimName
    let customElim ← mkCustomEliminator elimName (induction := true)
    unless info.getConstantVal?.isSome do
      throwError "Unsupported declaration type."
    -- TODO : Check the right names are used
    let cfg ← liftCommandElabM <| elabAutoIndPrinciplesRest elimInfo cfgStx
    modifyEnv (autoIndPrincipleExt.addEntry · {customElim, cfg with induction := true})
    -- sorry
  | _ => throwUnsupportedSyntax

initialize Lean.registerBuiltinAttribute {
  name := `autoinduction
  descr := "Add autoinduction principle."
  add declName stx _attrKind := do
    -- inspired by how the `induction_eliminator` attribute is defined
    discard <| elabAutoIndPrincipleAttr declName stx _attrKind |>.run {} {}
  }

def getAutoIndPrinciples : CoreM AutoIndPrinciples := do
  return autoIndPrincipleExt.getState (← getEnv)

def getAutoIndPrinciple? (targets : Array Expr) :
    MetaM (Option (Name × AutoIndPrincipleConfig)) := do
  let mut key := #[]
  for target in targets do
    let targetType := (← instantiateMVars (← inferType target)).headBeta
    let .const declName .. := targetType.getAppFn | return none
    key := key.push declName
  logInfo s!"found key{key}"
  return (← getAutoIndPrinciples).map.find? key
  -- let mut key : Array _:= #[]

  -- sorry

elab "#autoindprinciples" : command => do
  logInfo s!"{← liftCoreM getAutoIndPrinciples}"
