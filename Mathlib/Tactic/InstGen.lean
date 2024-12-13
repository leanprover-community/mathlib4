import Batteries.Tactic.ShowUnused
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Tactic.CC.Datatypes

#check Std.HashMap
#check Lean.Meta.isInstance

#check Lean.ConstantInfo.value!

open Lean Elab Command

/-- Given a sequence of nested foralls `(a₁ : α₁) → ... → (aₙ : αₙ) → _`,
returns the names `[a₁, ... aₙ]`. -/
def Lean.Expr.getForallBinderTypes : Expr → List Expr
  | forallE _ t b _ => t :: getForallBinderTypes b
  | _ => []

lemma can_be_improved (F : Type) [Field F] (x y : F) : x + y = y + x := add_comm x y

elab tk:"#instances_used" ids:(ppSpace colGt ident)* : command => do
  let ns ← ids.mapM fun s => liftCoreM <| realizeGlobalConstNoOverloadWithInfo s
  let env ← getEnv
  for n in ns do
    match env.find? n with
    | none => logErrorAt tk s!"unknown constant {n}"
    | some c =>
    let ty_insts ← liftCoreM <| c.type.getUsedConstants.filterM Meta.isInstance
    let tm_insts ← liftCoreM <| c.value?.mapM (·.getUsedConstants.filterM Meta.isInstance)
    logInfoAt tk
      s!"=== {n} ===\n instances in type:\n {ty_insts}\n instances in term:\n {tm_insts.getD #[]}"


#instances_used can_be_improved

structure BoundClass where
  name : Name
  bindings : Array Expr

instance : BEq BoundClass where
  beq b₁ b₂ := b₁.name == b₂.name && b₁.bindings == b₂.bindings

instance : Hashable BoundClass where
  hash b := mixHash (hash b.name) (hash b.bindings)

instance : Inhabited BoundClass where
  default := { name := .anonymous, bindings := #[] }

instance : ToString BoundClass where
  toString b := toString b.name ++ " " ++ toString b.bindings

def Lean.Expr.toBoundClass? (e : Expr) : Option BoundClass := do
  let name ← e.getAppFn.constName?
  let bindings := e.getAppArgs 
  pure ⟨name, bindings⟩ 

def Lean.Expr.toBoundClass! (e : Expr) : BoundClass where
  name := e.getAppFn.constName!
  bindings := e.getAppArgs 

def instanceDAG : CoreM <| Std.HashMap BoundClass (Array BoundClass) := do
  let env ← getEnv
  flip env.constants.foldM default <| fun h n c ↦ do
    if !(← Meta.isInstance n) then return h else
    let ty := c.type
    if !ty.isForall then return h else
    let src ← 
      match ty.getForallBinderTypes.getLast? with
      | none => do
          logWarning s!"instance {n} has no source class (E1)"
          pure default
      | some e => do
          match e.toBoundClass? with
          | none => do
              -- logWarning s!"instance {n} has no source class (E2)"
              pure default
          | some b => pure b
    let tgt ←
      match ty.getForallBody.toBoundClass? with
      | none => do
          logWarning s!"instance {n} has no target class"
          pure default
      | some b => pure b
    match h.get? src with
      | none => pure <| h.insert src #[tgt]
      | some a => pure <| (h.erase src).insert src (a.push tgt)

/- #eval show CoreM Unit from do -/
/-   let dag ← instanceDAG -/
/-   logInfo s!"DAG size: {dag.size}" -/
/-   for (src, tgts) in dag.toArray do -/
/-     logInfo s!"{src} → {tgts}" -/

partial def isInstanceChain (e : Expr) : CoreM Bool := do
  -- if `e` is not an application, it could be the tail end of an instance chain
  if !e.isApp then return true else
  match e.getAppFn.constName? with
  | none => return false -- the head symbol of an application should be a constant
  | some nm => do
    -- and that constant better be an instance
    if !(← Meta.isInstance nm) then return false else
    e.getAppArgs.allM isInstanceChain
































































#eval show CommandElabM Unit from do
  let env ← getEnv
  match env.find? `can_be_improved with
  | none => logError "can_be_improved not found"
  | some c => do
    let e := c.value!
    match e with
    | Expr.lam n t e _ => do
      logInfo s!"can_be_improved:\n{n}\n{t}\n{e}"
      match e with
      | Expr.lam n t e _ => do
        logInfo s!"can_be_improved:\n{n}\n{t}\n{e}"
        match e with
        | Expr.lam n t e _ => do
          logInfo s!"can_be_improved:\n{n}\n{t}\n{e}"
          match e with
          | Expr.lam n t e _ => do
            logInfo s!"can_be_improved:\n{n}\n{t}\n{e}"
            match e with
            | Expr.app f a => do
              logInfo s!"can_be_improved:\n{f}\n{a}"
              match f with
              | Expr.app f a => do
                logInfo s!"can_be_improved:\n{f}\n{a}"
              | _ => logError "can_be_improved is not a app"
            | _ => logError "can_be_improved is not a app"
          | _ => logError "can_be_improved is not a lambda"
        | _ => logError "can_be_improved is not a lambda"
      | _ => logError "can_be_improved is not a lambda"
    | _ => logError "can_be_improved is not a lambda"

