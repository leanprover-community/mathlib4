/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.ModelTheory.Definability
import Mathlib.ModelTheory.Algebra.Ring.MvPolynomial

/-!

# Definable Subsets in the language of rings

This file proves that the set of zeros of a multivariable polynomial is a definable subset.

-/

namespace FirstOrder

namespace Ring

open MvPolynomial Language

theorem mvPolynomial_zero_set_definable {ι R : Type*} [CommRing R]
    [CompatibleRing R] (p : MvPolynomial ι R) :
    Set.Definable (p.coeff '' p.support : Set R) Language.ring
     { x : ι → R | eval x p = 0 } := by
  rw [Set.definable_iff_exists_formula_sum]
  let p' := genericPolyMap (fun _ : Unit => p.support)
  letI := Classical.decEq R
  letI := Classical.decEq ι
  refine ⟨Term.equal
    ((termOfFreeCommRing (p' ())).relabel
      (Sum.map (fun i => ⟨p.coeff i.2.1, ⟨i.2.1, i.2.2, rfl⟩⟩) id)) 0, ?_⟩
  simp [Formula.Realize, Term.equal, lift_genericPolyMap, Function.comp]

end Ring

end FirstOrder
