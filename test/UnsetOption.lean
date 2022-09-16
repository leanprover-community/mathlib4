import Mathlib.Tactic.UnsetOption
import Mathlib.Tactic.RunCmd

set_option pp.all true

example : True := by
  run_tac
    let t : Option Bool := (← Lean.MonadOptions.getOptions).get? `pp.all
    guard (t == true)
  trivial

unset_option pp.all

example : True := by
  run_tac
    let t : Option Bool := (← Lean.MonadOptions.getOptions).get? `pp.all
    guard (t == Option.none)
  trivial
