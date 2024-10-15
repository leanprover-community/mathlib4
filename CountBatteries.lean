import Mathlib
import ImportGraph.RequiredModules

open Lean Elab Command Meta

-- Generalized monad for `Lean.Name.isBlackListed`
def Lean.Name.isBlackListed' {m : Type → Type} [Monad m] [MonadEnv m]
    (declName : Name) : m Bool := do
  if declName == ``sorryAx then return true
  if declName matches .str _ "inj" then return true
  if declName matches .str _ "noConfusionType" then return true
  let env ← getEnv
  pure $ declName.isInternalDetail
   || isAuxRecursor env declName
   || isNoConfusion env declName
  <||> isRec declName <||> isMatcher declName

/-- Remove all blacklisted names from the given environment.
This might not be accurate since the blacklist function is a heuristic. -/
def filterNames {m : Type → Type} [Monad m] [MonadEnv m] {α : Type _}
    (env : Std.HashMap Name α) : m (Std.HashMap Name α) := do
  let mut env' := env
  for (n, _) in env do
    if ← n.isBlackListed' then
      env' := env'.erase n
  return env'

elab "#count_batteries" : command => do
    let batteries := Name.mkStr1 "Batteries"
    let mut counts := mkNameMap ℕ
    let env ← filterNames (← getEnv).constants.map₁
    for (n, _) in env do
      let modules ← liftCoreM n.requiredModules
      for module in modules do
        if batteries.isPrefixOf module then
          counts := if let some count := counts.find? module
            then counts.insert module (count + 1)
            else counts.insert module 1
    dbg_trace counts.toList.toArray.qsort (fun (_, c₁) (_, c₂) => c₂ < c₁)

#count_batteries
