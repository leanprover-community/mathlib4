import Mathlib.Tactic.UnsetOption

set_option pp.all true

example : True := by
  run_tac
    let t : Option Bool := (← Lean.MonadOptions.getOptions).get? `pp.all
    -- should be true as set
    guard (t == true)
  trivial

section

unset_option pp.all

example : True := by
  run_tac
    let t : Option Bool := (← Lean.MonadOptions.getOptions).get? `pp.all
    -- should be none as unset
    guard (t == Option.none)
  trivial

end

example : True := by
  run_tac
    let t : Option Bool := (← Lean.MonadOptions.getOptions).get? `pp.all
    -- should be true as only unset within section
    guard (t == true)
  trivial
