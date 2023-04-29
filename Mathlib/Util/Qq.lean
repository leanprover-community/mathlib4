/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Alex J. Best
-/
import Qq

/-!
# Extra `Qq` helpers

This file contains some additional functions for using the quote4 library more conveniently.
-/
open Lean Elab Tactic Meta

namespace Qq

/-- Analogue of `inferTypeQ`, but that gets universe levels right for our application. -/
-- See https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Using.20.60QQ.60.20when.20you.20only.20have.20an.20.60Expr.60/near/303349037
def inferTypeQ' (e : Expr) : MetaM ((u : Level) × (α : Q(Type $u)) × Q($α)) := do
  let α ← inferType e
  let .sort u ← instantiateMVars (← whnf (← inferType α)) | unreachable!
  let some v := u.dec | throwError "not a type{indentExpr α}"
  pure ⟨v, α, e⟩

end Qq
