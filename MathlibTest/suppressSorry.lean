import Lean.Elab.Declaration
import Mathlib.Util.SuppressSorry

namespace ControlGroup

/-- warning: declaration uses 'sorry' -/
#guard_msgs in example : True := sorry
/-- warning: declaration uses 'sorry' -/
#guard_msgs in example : True := by sorry
/-- warning: declaration uses 'sorry' -/
#guard_msgs in example : True := by admit
/-- warning: declaration uses 'sorry' -/
#guard_msgs in example : True := by stop simp

/--
error: type mismatch
  ()
has type
  Unit : Type
but is expected to have type
  Nat : Type
-/
#guard_msgs in def foo₁ : Nat := ()
/-- warning: declaration uses 'sorry' -/
#guard_msgs in def bar₁ := show foo₁ = _ by unfold foo₁; rfl

-- this is probably a bug but not in SuppressSorry, inductives actually produce 7-8 sorry warnings
/--
warning: declaration uses 'sorry'
---
warning: declaration uses 'sorry'
---
warning: declaration uses 'sorry'
---
warning: declaration uses 'sorry'
---
warning: declaration uses 'sorry'
---
warning: declaration uses 'sorry'
---
warning: declaration uses 'sorry'
-/
#guard_msgs in inductive Foo₁ (x : sorry) : Prop

/--
warning: declaration uses 'sorry'
---
warning: declaration uses 'sorry'
---
warning: declaration uses 'sorry'
---
warning: declaration uses 'sorry'
---
warning: declaration uses 'sorry'
---
warning: declaration uses 'sorry'
---
warning: declaration uses 'sorry'
---
warning: declaration uses 'sorry'
-/
#guard_msgs in structure Bar₁ (x : sorry) : Prop

#guard_msgs in variable (x : sorry)
/-- warning: declaration uses 'sorry' -/
#guard_msgs in def y₁ := ((sorry : Nat), x)

elab "#elab_that_skips_elabCommand₁" cmd:command : command =>
  Lean.Elab.Command.elabDeclaration cmd

/-- warning: declaration uses 'sorry' -/
#guard_msgs in #elab_that_skips_elabCommand₁ example : True := sorry

end ControlGroup

---------------------------------------------------------------------------------------

namespace Suppressed

set_option suppressSorry true

#guard_msgs in example : True := sorry
#guard_msgs in example : True := by sorry
#guard_msgs in example : True := by admit
#guard_msgs in example : True := by stop simp

/--
error: type mismatch
  ()
has type
  Unit : Type
but is expected to have type
  Nat : Type
-/
#guard_msgs in def foo₂ : Nat := () -- bad declaration that turns into a synthetic sorry
#guard_msgs in def bar₂ := show foo₂ = _ by unfold foo₂; rfl

#guard_msgs in inductive Foo₂ (x : sorry) : Prop

#guard_msgs in structure Bar₂ (x : sorry) : Prop

#guard_msgs in variable (x : sorry)
#guard_msgs in def y₂ := ((sorry : Nat), x)

elab "#elab_that_skips_elabCommand₂" cmd:command : command =>
  Lean.Elab.Command.elabDeclaration cmd

#guard_msgs in #elab_that_skips_elabCommand₂ example : True := sorry

end Suppressed

---------------------------------------------------------------------------------------

/-- warning: declaration uses 'sorry' -/
#guard_msgs in example : True := sorry
/-- warning: declaration uses 'sorry' -/
#guard_msgs in example : True := by sorry
/-- warning: declaration uses 'sorry' -/
#guard_msgs in example : True := by admit
/-- warning: declaration uses 'sorry' -/
#guard_msgs in example : True := by stop simp

/--
error: type mismatch
  ()
has type
  Unit : Type
but is expected to have type
  Nat : Type
-/
#guard_msgs in def foo₃ : Nat := ()
/-- warning: declaration uses 'sorry' -/
#guard_msgs in def bar₃ := show foo₃ = _ by unfold foo₃; rfl

/--
warning: declaration uses 'sorry'
---
warning: declaration uses 'sorry'
---
warning: declaration uses 'sorry'
---
warning: declaration uses 'sorry'
---
warning: declaration uses 'sorry'
---
warning: declaration uses 'sorry'
---
warning: declaration uses 'sorry'
-/
#guard_msgs in inductive Foo₃ (x : sorry) : Prop

/--
warning: declaration uses 'sorry'
---
warning: declaration uses 'sorry'
---
warning: declaration uses 'sorry'
---
warning: declaration uses 'sorry'
---
warning: declaration uses 'sorry'
---
warning: declaration uses 'sorry'
---
warning: declaration uses 'sorry'
---
warning: declaration uses 'sorry'
-/
#guard_msgs in structure Bar₃ (x : sorry) : Prop

#guard_msgs in variable (x : sorry)
/-- warning: declaration uses 'sorry' -/
#guard_msgs in def y₃ := ((sorry : Nat), x)

elab "#elab_that_skips_elabCommand₃" cmd:command : command =>
  Lean.Elab.Command.elabDeclaration cmd

/-- warning: declaration uses 'sorry' -/
#guard_msgs in #elab_that_skips_elabCommand₃ example : True := sorry
