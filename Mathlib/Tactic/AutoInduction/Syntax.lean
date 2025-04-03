import Mathlib.Tactic.AutoInduction.Attr
import Lean

set_option autoImplicit false
set_option linter.unusedTactic false

open Lean Elab Parser Tactic Meta

/--
`autoinduction` effectively calls `induction _ using` with the relevant definition marked with the
`@[autoinduction]` attribute. In addition, it uses the arguments specified at that point to
try to provide a value for the respective argument.
-/
syntax (name := autoinductiontac) "autoinduction" elimTarget
  (" generalizing" (ppSpace colGt term:max)+)? (inductionAlts)? : tactic

-- namespace AutoInduction

-- def expandInductionAlts? {m} [Monad m] [MonadRef m] [MonadQuotation m] :
--     TSyntax ``inductionAlts → m (Option (TSyntax ``inductionAlts))
--   | `(inductionAlts | with $[$tac]? $[$[$lhsss]* => $rhss]*) => do
--     let inductionAlts' ← (lhsss.zip rhss).mapM (fun x => do
--       x.fst.mapM (fun lhs => `(inductionAlt|$lhs => $x.snd)))
--     return .some (← `(inductionAlts | with $[$tac]? $[$inductionAlts'.flatten]*))
--   | _ => return .none

-- macro_rules
--   | `(tactic|autoinduction $t $[using $us]? $[generalizing $gen]? $[$inductionAlts]?) => do
--     if let .some alts := inductionAlts then
--       let .some inductionAlts' ← (expandInductionAlts? alts) |
--         withRef alts <| Macro.throwError "not alternative syntax"
--       `(tactic|autoinduction $t $[using $us]? $[generalizing $gen]? $inductionAlts')
--     else
--       `(tactic|autoinduction $t $[using $us]? $[generalizing $gen]?)

-- end AutoInduction
