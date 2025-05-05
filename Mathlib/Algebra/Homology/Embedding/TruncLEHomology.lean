/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Embedding.TruncGEHomology
import Mathlib.Algebra.Homology.Embedding.TruncLE
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # The homology of a canonical truncation

Given an embedding of complex shapes `e : Embedding c c'`,
we relate the homology of `K : HomologicalComplex C c'` and of
`K.truncLE e : HomologicalComplex C c'`.

The main result is that `K.ιTruncLE e : K.truncLE e ⟶ K` induces a
quasi-isomorphism in degree `e.f i` for all `i`. (Note that the complex
`K.truncLE e` is exact in degrees that are not in the image of `e.f`.)

All the results are obtained by dualising the results in the file `Embedding.TruncGEHomology`.

Moreover, if `C` is an abelian category, we introduce the cokernel
sequence `K.shortComplexTruncLE e` of the monomorphism `K.ιTruncLE e`.

-/

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category C]

section

variable [HasZeroMorphisms C] (K L : HomologicalComplex C c') (φ : K ⟶ L) (e : c.Embedding c')
  [e.IsTruncLE] [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i']

namespace truncLE'

/-- `K.truncLE'ToRestriction e` is a quasi-isomorphism in degrees that are not at the boundary. -/
lemma quasiIsoAt_truncLE'ToRestriction (j : ι) (hj : ¬ e.BoundaryLE j)
    [(K.restriction e).HasHomology j] [(K.truncLE' e).HasHomology j] :
    QuasiIsoAt (K.truncLE'ToRestriction e) j := by
  dsimp only [truncLE'ToRestriction]
  have : (K.op.restriction e.op).HasHomology j :=
    inferInstanceAs ((K.restriction e).op.HasHomology j)
  rw [quasiIsoAt_unopFunctor_map_iff]
  exact truncGE'.quasiIsoAt_restrictionToTruncGE' K.op e.op j (by simpa)

instance truncLE'_hasHomology (i : ι) : (K.truncLE' e).HasHomology i :=
  inferInstanceAs ((K.op.truncGE' e.op).unop.HasHomology i)

end truncLE'

variable [HasZeroObject C]

instance (i' : ι') : (K.truncLE e).HasHomology i' :=
  inferInstanceAs ((K.op.truncGE e.op).unop.HasHomology i')

lemma quasiIsoAt_ιTruncLE {j : ι} {j' : ι'} (hj' : e.f j = j') :
    QuasiIsoAt (K.ιTruncLE e) j' := by
  have := K.op.quasiIsoAt_πTruncGE e.op hj'
  exact inferInstanceAs (QuasiIsoAt ((unopFunctor _ _ ).map (K.op.πTruncGE e.op).op) j')

instance (i : ι) : QuasiIsoAt (K.ιTruncLE e) (e.f i) := K.quasiIsoAt_ιTruncLE e rfl

lemma quasiIso_ιTruncLE_iff_isSupported :
    QuasiIso (K.ιTruncLE e) ↔ K.IsSupported e := by
  rw [← quasiIso_opFunctor_map_iff, ← isSupported_op_iff]
  exact K.op.quasiIso_πTruncGE_iff_isSupported e.op

lemma acyclic_truncLE_iff_isSupportedOutside :
    (K.truncLE e).Acyclic ↔ K.IsSupportedOutside e := by
  rw [← acyclic_op_iff, ← isSupportedOutside_op_iff]
  exact K.op.acyclic_truncGE_iff_isSupportedOutside e.op

variable {K L}

lemma quasiIso_truncLEMap_iff :
    QuasiIso (truncLEMap φ e) ↔ ∀ (i : ι) (i' : ι') (_ : e.f i = i'), QuasiIsoAt φ i' := by
  rw [← quasiIso_opFunctor_map_iff]
  simp only [← quasiIsoAt_opFunctor_map_iff φ]
  apply quasiIso_truncGEMap_iff

end

section

variable [Abelian C] (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsTruncLE]

/-- The cokernel sequence of the monomorphism `K.ιTruncLE e`. -/
@[simps X₁ X₂ f]
noncomputable def shortComplexTruncLE : ShortComplex (HomologicalComplex C c') :=
  ShortComplex.mk (K.ιTruncLE e) _ (cokernel.condition _)

instance : Mono (K.shortComplexTruncLE e).f := by
  dsimp [shortComplexTruncLE]
  infer_instance

instance : Epi (K.shortComplexTruncLE e).g := by
  dsimp [shortComplexTruncLE]
  infer_instance

lemma shortComplexTruncLE_shortExact :
    (K.shortComplexTruncLE e).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)

lemma mono_homologyMap_shortComplexTruncLE_g (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    Mono (homologyMap (K.shortComplexTruncLE e).g i') :=
  ((K.shortComplexTruncLE_shortExact e).homology_exact₂ i').mono_g
    (by apply ((K.truncLE e).exactAt_of_isSupported e i' hi').isZero_homology.eq_of_src)

@[simp]
lemma shortComplexTruncLE_shortExact_δ_eq_zero (i' j' : ι') (hij' : c'.Rel i' j') :
    (K.shortComplexTruncLE_shortExact e).δ i' j' hij' = 0 := by
  by_cases hj : ∃ j, e.f j = j'
  · obtain ⟨j, rfl⟩ := hj
    rw [← cancel_mono (homologyMap (K.ιTruncLE e) (e.f j)), zero_comp]
    exact (K.shortComplexTruncLE_shortExact e).δ_comp i' _ hij'
  · apply ((K.truncLE e).exactAt_of_isSupported e j'
      (by simpa using hj)).isZero_homology.eq_of_tgt

instance epi_homologyMap_shortComplexTruncLE_g (i' : ι') :
    Epi (homologyMap (K.shortComplexTruncLE e).g i') := by
  by_cases hi' : ∃ j', c'.Rel i' j'
  · obtain ⟨j', hj'⟩ := hi'
    exact ((K.shortComplexTruncLE_shortExact e).homology_exact₃ i' j' hj').epi_f (by simp)
  · exact epi_homologyMap_of_epi_of_not_rel _ _ (by simpa using hi')

lemma isIso_homologyMap_shortComplexTruncLE_g (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    IsIso (homologyMap (K.shortComplexTruncLE e).g i') := by
  have := K.mono_homologyMap_shortComplexTruncLE_g e i' hi'
  apply isIso_of_mono_of_epi

lemma quasiIsoAt_shortComplexTruncLE_g (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    QuasiIsoAt (K.shortComplexTruncLE e).g i' := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact K.isIso_homologyMap_shortComplexTruncLE_g e i' hi'

lemma shortComplexTruncLE_X₃_isSupportedOutside :
    (K.shortComplexTruncLE e).X₃.IsSupportedOutside e where
  exactAt i := by
    rw [exactAt_iff_isZero_homology]
    by_cases hi : ∃ j', c'.Rel (e.f i) j'
    · obtain ⟨j', hj'⟩ := hi
      apply ((K.shortComplexTruncLE_shortExact e).homology_exact₃ (e.f i) j' hj').isZero_X₂
      · rw [← cancel_epi (homologyMap (K.ιTruncLE e) (e.f i)), comp_zero]
        dsimp [shortComplexTruncLE]
        rw [← homologyMap_comp, cokernel.condition, homologyMap_zero]
      · simp
    · have : IsIso (homologyMap (K.shortComplexTruncLE e).f (e.f i)) :=
        by dsimp; infer_instance
      rw [IsZero.iff_id_eq_zero, ← cancel_epi (homologyMap (K.shortComplexTruncLE e).g (e.f i)),
        comp_id, comp_zero, ← cancel_epi (homologyMap (K.shortComplexTruncLE e).f (e.f i)),
        comp_zero, ← homologyMap_comp, ShortComplex.zero, homologyMap_zero]

end

end HomologicalComplex
