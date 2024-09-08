/-
Copyright (c) XXX. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XXX
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset

/-!
# XXX
-/

namespace algebraMap

section CommSemiringCommSemiring

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] {ι : Type*} {s : Finset ι}

@[norm_cast]
theorem coe_prod (a : ι → R) : (↑(∏ i ∈ s, a i : R) : A) = ∏ i ∈ s, (↑(a i) : A) :=
  map_prod (algebraMap R A) a s

@[norm_cast]
theorem coe_sum (a : ι → R) : ↑(∑ i ∈ s, a i) = ∑ i ∈ s, (↑(a i) : A) :=
  map_sum (algebraMap R A) a s

end CommSemiringCommSemiring

end algebraMap
