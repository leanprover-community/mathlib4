import Lean

open Lean Lean.Meta

deriving instance Inhabited for ConstantInfo -- required for Array.qsort

structure FindOptions where
  stage1       : Bool := true
  checkPrivate : Bool := false

def findCore (ϕ : ConstantInfo → MetaM Bool) (opts : FindOptions := {}) :
  MetaM (Array ConstantInfo) := do
  let matches ← if !opts.stage1 then #[] else (← getEnv).constants.map₁.foldM (init := #[]) check
  (← getEnv).constants.map₂.foldlM (init := matches) check
where
  check matches name cinfo := do
    if opts.checkPrivate || !isPrivateName name then
      if ← ϕ cinfo then matches.push cinfo else matches
    else matches

def find (ϕ : ConstantInfo → MetaM Bool) (opts : FindOptions := {}) : MetaM Unit := do
  let cinfos ← findCore ϕ opts
  let cinfos := cinfos.qsort fun p q => p.name.lt q.name
  for cinfo in cinfos do
    println! "{cinfo.name} : {← Meta.ppExpr cinfo.type}"

macro "#print prefix " name:ident : command =>
  `(#eval find fun cinfo => $(quote name.getId).isPrefixOf cinfo.name)
