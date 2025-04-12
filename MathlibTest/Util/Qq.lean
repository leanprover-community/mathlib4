import Mathlib.Util.Qq
import Mathlib.Data.Finset.Basic


open Qq Lean Elab Meta

section mkSetLiteralQ

/--
info: {1, 2, 3}
-/
#guard_msgs in
run_cmd do
  let β := q(Finset ℕ)
  let elems :=  [q(1), q(2), q(3)]
  Lean.logInfo <| ← Command.liftTermElabM (ppExpr (mkSetLiteralQ β elems))


/--
info: {1, 2, 3}
-/
#guard_msgs in
run_cmd do
  let β := q(Multiset ℕ)
  let elems :=  [q(1), q(2), q(3)]
  Lean.logInfo <| ← Command.liftTermElabM (ppExpr (mkSetLiteralQ β elems))


/--
info: {1, 2, 3}
-/
#guard_msgs in
run_cmd do
  let β := q(Set ℕ)
  let elems :=  [q(1), q(2), q(3)]
  Lean.logInfo <| ← Command.liftTermElabM (ppExpr (mkSetLiteralQ β elems))


/--
info: {1, 2, 3}
-/
#guard_msgs in
run_cmd do
  let β := q(List ℕ)
  let elems :=  [q(1), q(2), q(3)]
  Lean.logInfo <| ← Command.liftTermElabM (ppExpr (mkSetLiteralQ β elems))


end mkSetLiteralQ
