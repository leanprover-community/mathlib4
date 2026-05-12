import Lean
import Mathlib.Tactic.SimpUtils

/--
Lean.Meta.Grind.simpExists
-/
#guard_msgs (substring := true) in
#simprocs ∃ _, _

/--
Lean.Elab.WF.paramLet
-/
#guard_msgs (substring := true) in
#dsimprocs ∃ _, _

/--
exists_const
-/
#guard_msgs (substring := true) in
#simp_theorems ∃ _, _

/--
dreduceIte
-/
#guard_msgs (substring := true) in
#dsimprocs ite _ _ _

/--
reduceIte
-/
#guard_msgs (substring := true) in
#simprocs ite _ _ _

/--
ite_self
-/
#guard_msgs (substring := true) in
#simp_theorems ite _ _ _

/-- An example of a `simproc_decl`. -/
simproc_decl testingSimproc (_ + _) := fun _ ↦ pure .continue

/--
testingSimproc
-/
#guard_msgs (substring := true) in
#simprocs _ + _
