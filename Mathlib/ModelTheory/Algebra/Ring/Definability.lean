/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.ModelTheory.Definability
import Mathlib.RingTheory.MvPolynomial.FreeCommRing
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.ModelTheory.Algebra.Ring.FreeCommRing

/-!

# Definable Subsets in the language of rings

This file proves that the set of zeros of a multivariable polynomial is a definable subset.

-/

namespace FirstOrder

namespace Ring

open MvPolynomial Language BoundedFormula

theorem mvPolynomial_zeroLocus_definable {ι K : Type*} [Field K]
    [CompatibleRing K] (S : Finset (MvPolynomial ι K)) :
    Set.Definable (⋃ p ∈ S, p.coeff '' p.support : Set K) Language.ring
      (zeroLocus K (Ideal.span (S : Set (MvPolynomial ι K)))) := by
  rw [Set.definable_iff_exists_formula_sum]
  let p' := genericPolyMap (fun p : S => p.1.support)
  letI := Classical.decEq ι
  letI := Classical.decEq K
  rw [MvPolynomial.zeroLocus_span]
  refine ⟨BoundedFormula.iInf
      (fun i : S => Term.equal
        ((termOfFreeCommRing (p' i)).relabel
          (Sum.map (fun p => ⟨p.1.1.coeff p.2.1, by
            simp only [Set.mem_iUnion]
            exact ⟨p.1.1, p.1.2, Set.mem_image_of_mem _ p.2.2⟩⟩) id)) 0), ?_⟩
  -- Squeezing this simp slows it down significantly. Please measure before removing.
  simp? [Formula.Realize, Term.equal, Function.comp_def, p', MvPolynomial.aeval_eq_eval₂Hom] says
    simp only [Finset.mem_coe, aeval_eq_eval₂Hom, Algebra.algebraMap_self, coe_eval₂Hom, eval₂_id,
      Formula.Realize, Term.equal, Term.relabel_relabel, Function.comp_def, realize_iInf,
      realize_bdEqual, Term.realize_relabel, Sum.elim_inl, realize_termOfFreeCommRing,
      lift_genericPolyMap, Sum.map_inr, id_eq, Sum.elim_inr, Sum.map_inl,
      MvPolynomialSupportLEEquiv_symm_apply_coeff, realize_zero, Subtype.forall, p']

end Ring

end FirstOrder
