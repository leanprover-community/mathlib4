/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Eric Wieser
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Facts about algebras when the coefficient ring is a field.
-/

variable (R A : Type*) [CommRing R] [Semiring A] [Algebra R A] [IsSimpleRing R] [Nontrivial A]

instance : FaithfulSMul R A :=
  faithfulSMul_iff_algebraMap_injective R A |>.2 <| RingHom.injective _

namespace algebraMap

@[norm_cast, simp]
theorem coe_inj {a b : R} : (↑a : A) = ↑b ↔ a = b :=
  (algebraMap R A).injective.eq_iff

end algebraMap
