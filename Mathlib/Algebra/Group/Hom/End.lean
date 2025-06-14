/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kevin Buzzard, Kim Morrison, Johan Commelin, Chris Hughes,
  Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Algebra.Ring.Defs

/-!
# Instances on spaces of monoid and group morphisms

This file does two things involving `AddMonoid.End` and `Ring`.
They are separate, and if someone would like to split this file in two that may be helpful.

* We provide the `Ring` structure on `AddMonoid.End`.
* Results about `AddMonoid.End R` when `R` is a ring.
-/


universe uM

variable {M : Type uM}

namespace AddMonoid.End

instance instAddMonoidWithOne (M) [AddCommMonoid M] : AddMonoidWithOne (AddMonoid.End M) where
  natCast n := n • (1 : AddMonoid.End M)
  natCast_zero := AddMonoid.nsmul_zero _
  natCast_succ n := AddMonoid.nsmul_succ n 1

/-- See also `AddMonoid.End.natCast_def`. -/
@[simp]
lemma natCast_apply [AddCommMonoid M] (n : ℕ) (m : M) : (↑n : AddMonoid.End M) m = n • m := rfl

@[simp] lemma ofNat_apply [AddCommMonoid M] (n : ℕ) [n.AtLeastTwo] (m : M) :
    (ofNat(n) : AddMonoid.End M) m = n • m := rfl

instance instSemiring [AddCommMonoid M] : Semiring (AddMonoid.End M) :=
  { AddMonoid.End.instMonoid M,
    AddMonoidHom.instAddCommMonoid,
    AddMonoid.End.instAddMonoidWithOne M with
    zero_mul := fun _ => AddMonoidHom.ext fun _ => rfl,
    mul_zero := fun _ => AddMonoidHom.ext fun _ => AddMonoidHom.map_zero _,
    left_distrib := fun _ _ _ => AddMonoidHom.ext fun _ => AddMonoidHom.map_add _ _ _,
    right_distrib := fun _ _ _ => AddMonoidHom.ext fun _ => rfl }

instance instRing [AddCommGroup M] : Ring (AddMonoid.End M) :=
  { AddMonoid.End.instSemiring, AddMonoid.End.instAddCommGroup with
    intCast := fun z => z • (1 : AddMonoid.End M),
    intCast_ofNat := natCast_zsmul _,
    intCast_negSucc := negSucc_zsmul _ }

end AddMonoid.End
