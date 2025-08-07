import Mathlib.Tactic.TacticAnalysis.Declarations

section rwMerge

def x := 1
def y := 1
def z := 1
theorem xy : x = y := rfl
theorem yz : y = z := rfl

example : x = y := by
  rw [xy]

/--
warning: Try this: rw [xy, yz]

Note: This linter can be disabled with `set_option linter.tactic_analysis false`
-/
#guard_msgs in
example : x = z := by
  rw [xy]
  rw [yz]

end rwMerge

section mergeWithGrind

example : 1 + 1 = 2 := by
  grind

/--
warning: 'have : 1 + 1 < 3 := by omega; grind' can be replaced with 'grind'
---
warning: replace the proof with 'grind': have : 1 + 1 < 3 := by omega;
  grind
-/
#guard_msgs in
example : 1 + 1 = 2 := by
  have : 1 + 1 < 3 := by omega
  grind

end mergeWithGrind

section replaceWithGrind

set_option linter.tacticAnalysis.grindReplacement true

example : 1 + 1 = 2 := by
  grind

/--
warning: replace the proof with 'grind': have : 1 + 1 < 3 := by omega;
  rfl
-/
#guard_msgs in
example : 1 + 1 = 2 := by
  have : 1 + 1 < 3 := by omega
  rfl

end replaceWithGrind
