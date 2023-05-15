/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
import Mathlib.Init.Logic

/-! ### alignments from lean 3 `init.data.prod` -/

universe u_1 u v

section recursor_workarounds

/-- A computable version of `Prod.rec`. Workaround until Lean has native support for this. -/
def Prod.recC {α : Type u} {β : Type v} {motive : α × β → Sort u_1}
  (mk : (fst : α) → (snd : β) → motive (fst, snd)) :
  (t : α × β) → motive t
| (fst, snd) => mk fst snd

@[csimp]
theorem rec_eq_recC : @Prod.rec = @Prod.recC := by
  funext α β motive mk t
  cases t with
  | mk fst snd => rfl

end recursor_workarounds

section

variable {α : Type u} {β : Type v}

@[simp]
theorem Prod.mk.eta : ∀ {p : α × β}, (p.1, p.2) = p
  | (_, _) => rfl

end
