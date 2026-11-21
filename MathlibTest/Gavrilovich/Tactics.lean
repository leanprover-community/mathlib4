import Mathlib.Tactic.Gavrilovich.Tactics

/-! Tests of the tactics for diagram spaces (`Mathlib.Tactic.Gavrilovich.Tactics`), without the
notation `pt(…)` (from `Mathlib.Tactic.Gavrilovich.Elab.Full`): points are written `Space.mk k _`
or `Space.pt n _`. -/

open Gavrilovich

/-! `simp` puts points in canonical form; the points of `⌜o → c⌟` are sorted by name. -/

example : (Space.pt "o" (by decide) : ⌜o → c⌟) = Space.mk 1 (by decide) := by simp
example : (Space.mk (1 - 1) (by decide) : ⌜o → c⌟) = Space.mk 0 (by decide) := by simp

/-! `gav_decide` and `pt_cases`. -/

example : (Space.mk 0 (by decide) : ⌜o → c⌟) ≠ Space.mk 1 (by decide) := by gav_decide

example (x : ⌜a  b  c⌟) : x = x := by
  pt_cases x
  all_goals rfl

example (x y : ⌜o → c⌟) (h : x ≤ y) : x ≤ y := by
  pt_cases h
  all_goals gav_decide

/-! `Space.hom`, with continuity checked by `gav_monotone`. -/

example : ⌜a  b⌟ ⟶ ⌜o → c⌟ := Space.hom fun _ => Space.mk 0 (by decide)

example (x : ⌜a  b⌟) :
    (Space.hom (fun _ => (Space.mk 0 (by decide) : ⌜o → c⌟)) : ⌜a  b⌟ ⟶ ⌜o → c⌟) x =
      Space.mk 0 (by decide) :=
  rfl
