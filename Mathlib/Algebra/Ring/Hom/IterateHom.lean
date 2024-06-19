/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.GroupPower.IterateHom

/-!
# Lemma iterates of ring homomorphisms
-/

namespace RingHom

variable {α : Type*} [Semiring α]

theorem coe_pow (f : α →+* α) (n : ℕ) : ⇑(f ^ n) = f^[n] :=
  hom_coe_pow _ rfl (fun _ _ => rfl) f n
#align ring_hom.coe_pow RingHom.coe_pow

end RingHom
