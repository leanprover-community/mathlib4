/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Data.ZMod.Basic

/-!
# The `ZMod n`-algebra structure on rings whose characteristic divides `n`
-/

assert_not_exists TwoSidedIdeal

namespace ZMod

variable (R : Type*) [Ring R]

instance (p : ℕ) : Subsingleton (Algebra (ZMod p) R) :=
  ⟨fun _ _ => Algebra.algebra_ext _ _ <| RingHom.congr_fun <| Subsingleton.elim _ _⟩

section

variable {n : ℕ} (m : ℕ) [CharP R m]

/-- The `ZMod n`-algebra structure on rings whose characteristic `m` divides `n`.
See note [reducible non-instances]. -/
abbrev algebra' (h : m ∣ n) : Algebra (ZMod n) R where
  algebraMap := ZMod.castHom h R
  smul := fun a r => cast a * r
  commutes' := fun a r =>
    show (cast a * r : R) = r * cast a by
      rcases ZMod.intCast_surjective a with ⟨k, rfl⟩
      show ZMod.castHom h R k * r = r * ZMod.castHom h R k
      rw [map_intCast, Int.cast_comm]
  smul_def' := fun _ _ => rfl

end

/-- The `ZMod p`-algebra structure on a ring of characteristic `p`. This is not an
instance since it creates a diamond with `Algebra.id`.
See note [reducible non-instances]. -/
abbrev algebra (p : ℕ) [CharP R p] : Algebra (ZMod p) R :=
  algebra' R p dvd_rfl

end ZMod
