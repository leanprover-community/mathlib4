/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
import Mathlib.Init.Logic

/-! ### alignments from lean 3 `init.data.prod` -/

universe u v

section

variable {α : Type u} {β : Type v}

@[simp]
theorem Prod.mk.eta : ∀ {p : α × β}, (p.1, p.2) = p
  | (_, _) => rfl

end
