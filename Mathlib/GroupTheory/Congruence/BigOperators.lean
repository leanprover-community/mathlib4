/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/

import Mathlib.GroupTheory.Congruence.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

/-!
# Interactions between `∑, ∏` and `(Add)Con`

-/

namespace Con

/-- Multiplicative congruence relations preserve finite product. -/
@[to_additive "Additive congruence relations preserve finite sum."]
protected theorem finset_prod {ι M : Type*} [CommMonoid M] (c : Con M) (s : Finset ι)
    {f g : ι → M} (h : ∀ i ∈ s, c (f i) (g i)) :
    c (s.prod f) (s.prod g) := by
  classical
  induction s using Finset.cons_induction_on with
  | h₁ => simpa using c.refl 1
  | @h₂ i s hi ih =>
    rw [Finset.prod_cons hi, Finset.prod_cons hi]
    exact c.mul (h _ (by simp)) <| ih fun i hi ↦ h _ (by aesop)

end Con
