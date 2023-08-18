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

theorem mvPolynomial_zero_set_definable {ι κ R : Type*} [CommRing R]
    [CompatibleRing R] [Finite ι] (p : ι → MvPolynomial κ R) :
    Set.Definable (⋃ i : ι, (p i).coeff '' (p i).support : Set R) Language.ring
     { x : κ → R | ∀ i, eval x (p i) = 0 } := by
  rw [Set.definable_iff_exists_formula_sum]
  let p' := genericPolyMap (fun i => (p i).support)
  letI := Fintype.ofFinite ι
  letI := Classical.decEq κ
  letI := Classical.decEq R
  refine ⟨((Finset.univ : Finset ι).toList.map
      (fun i => Term.equal
        ((termOfFreeCommRing (p' i)).relabel
          (Sum.map (fun i => ⟨(p i.1).coeff i.2.1,
            Set.mem_iUnion.2 ⟨i.1, i.2.1, i.2.2, rfl⟩⟩) id)) 0)).foldr
      (. ⊓ .)
      ⊤, ?_⟩
  simp [Formula.Realize, Term.equal, lift_genericPolyMap, Function.comp]

end Ring

end FirstOrder
