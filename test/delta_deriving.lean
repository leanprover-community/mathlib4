import Lean
import Lean.Elab.Command
import Std.Tactic.OpenPrivate

open Lean Parser Command
@[command_parser] def «delta_deriving»     := leading_parser
  "delta_deriving " >> "instance " >> derivingClasses >> " for " >> sepBy1 ident ", "

open Elab Meta Command Term
open private tryApplyDefHandler in elabDeriving
@[command_elab «delta_deriving»] def elabDeltaDeriving : CommandElab
  | `(delta_deriving instance $[$classes $[with $argss?]?],* for $[$declNames],*) => do
     let declNames ← declNames.mapM resolveGlobalConstNoOverloadWithInfo
     for cls in classes, args? in argss? do
       try
         let className ← resolveGlobalConstNoOverloadWithInfo cls
         withRef cls do
           if declNames.size == 1 && args?.isNone then
             if (← tryApplyDefHandler className declNames[0]!) then
               return ()
           applyDerivingHandlers className declNames args?
       catch ex =>
         logException ex
  | _ => throwUnsupportedSyntax

inductive foo | a | b
deriving instance Repr for foo
