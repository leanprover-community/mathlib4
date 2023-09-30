/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam, Daniel Selsam, Mario Carneiro
-/
import Lean.Elab.Command

open Lean Meta Elab Command

namespace Lean
namespace Meta

structure FindOptions where
  stage1       : Bool := true
  checkPrivate : Bool := false

def findCore (ϕ : ConstantInfo → MetaM Bool) (opts : FindOptions := {}) :
    MetaM (Array ConstantInfo) := do
  let matches_ ← if !opts.stage1 then pure #[] else
    (← getEnv).constants.map₁.foldM (init := #[]) check
  (← getEnv).constants.map₂.foldlM (init := matches_) check
where
  check matches_ name cinfo := do
    if opts.checkPrivate || !isPrivateName name then
      if ← ϕ cinfo then pure $ matches_.push cinfo else pure matches_
    else pure matches_

def find (msg : String)
    (ϕ : ConstantInfo → MetaM Bool) (opts : FindOptions := {}) : TermElabM String := do
  let cinfos ← findCore ϕ opts
  let cinfos := cinfos.qsort fun p q ↦ p.name.lt q.name
  let mut msg := msg
  for cinfo in cinfos do
    msg := msg ++ s!"{cinfo.name} : {← Meta.ppExpr cinfo.type}\n"
  pure msg

end Meta

namespace Elab.Command

syntax (name := printPrefix) "#print prefix " ident : command

/--
The command `#print prefix foo` will print all definitions that start with
the namespace `foo`.
-/
@[command_elab printPrefix] def elabPrintPrefix : CommandElab
| `(#print prefix%$tk $name:ident) => do
  let nameId := name.getId
  liftTermElabM do
    let mut msg ← find "" fun cinfo ↦ pure $ nameId.isPrefixOf cinfo.name
    if msg.isEmpty then
      if let [name] ← resolveGlobalConst name then
        msg ← find msg fun cinfo ↦ pure $ name.isPrefixOf cinfo.name
    if !msg.isEmpty then
      logInfoAt tk msg
| _ => throwUnsupportedSyntax

end Elab.Command
end Lean
