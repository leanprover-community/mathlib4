/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad
-/
prelude
import Mathlib.Init.Logic

universe u v

section

variable {α : Type u} {β : Type v}

@[simp]
theorem Prod.mk.eta : ∀ {p : α × β}, (p.1, p.2) = p
  | (_, _) => rfl

end
