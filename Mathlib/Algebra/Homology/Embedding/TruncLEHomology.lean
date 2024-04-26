import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.Embedding.TruncGEHomology
import Mathlib.Algebra.Homology.Embedding.TruncLE
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

open CategoryTheory Category Limits

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

namespace HomologicalComplex

section

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
  (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsTruncLE]
  [∀ i', K.HasHomology i']

instance (i : ι) : (K.truncLE' e).HasHomology i :=
  (inferInstance : (K.op.truncGE' e.op).unop.HasHomology i)

instance (i' : ι') : (K.truncLE e).HasHomology i' :=
  (inferInstance : (K.op.truncGE e.op).unop.HasHomology i')

lemma quasiIsoAt_ιTruncLE {j : ι} {j' : ι'} (hj' : e.f j = j') :
    QuasiIsoAt (K.ιTruncLE e) j' := by
  rw [← quasiIsoAt_op_iff]
  exact K.op.quasiIsoAt_πTruncGE e.op hj'

instance (j : ι) : QuasiIsoAt (K.ιTruncLE e) (e.f j) :=
  K.quasiIsoAt_ιTruncLE e rfl

end

section

variable {C : Type*} [Category C] [Abelian C]
  (K L : HomologicalComplex C c') (e : c.Embedding c') [e.IsTruncLE]

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
  by_cases hj'': ∃ j, e.f j = j'
  · obtain ⟨j, rfl⟩ := hj''
    rw [← cancel_mono (homologyMap (K.ιTruncLE e) (e.f j)), zero_comp]
    exact (K.shortComplexTruncLE_shortExact e).δ_comp i' _ hij'
  · apply ((K.truncLE e).exactAt_of_isSupported e j'
      (by simpa using hj'')).isZero_homology.eq_of_tgt

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

lemma quasiIso_ιTruncLE_iff_isSupported :
    QuasiIso (K.ιTruncLE e) ↔ K.IsSupported e := by
  constructor
  · intro
    refine' ⟨fun i' hi' => _⟩
    rw [← exactAt_iff_of_quasiIsoAt (K.ιTruncLE e) i']
    exact (K.truncLE e).exactAt_of_isSupported e i' hi'
  · intro
    rw [quasiIso_iff]
    intro i'
    by_cases hi' : ∃ i, e.f i = i'
    · obtain ⟨i, rfl⟩ := hi'
      infer_instance
    · rw [quasiIsoAt_iff_exactAt (K.ιTruncLE e) i']
      all_goals exact exactAt_of_isSupported _ e i' (by simpa using hi')

lemma acyclic_ιTruncLE_iff_isSupportedOutside :
    (K.truncLE e).Acyclic ↔ K.IsSupportedOutside e := by
  constructor
  · intro hK
    exact ⟨fun i =>
      by simpa only [← exactAt_iff_of_quasiIsoAt (K.ιTruncLE e)] using hK (e.f i)⟩
  · intro hK i'
    by_cases hi' : ∃ i, e.f i = i'
    · obtain ⟨i, rfl⟩ := hi'
      simpa only [exactAt_iff_of_quasiIsoAt (K.ιTruncLE e)] using hK.exactAt i
    · exact exactAt_of_isSupported _ e i' (by simpa using hi')

lemma acyclic_truncLE_iff_isSupportedOutside :
    (K.truncLE e).Acyclic ↔ K.IsSupportedOutside e := by
  constructor
  · intro hK
    exact ⟨fun i => by simpa only [← exactAt_iff_of_quasiIsoAt (K.ιTruncLE e)] using hK (e.f i)⟩
  · intro hK i'
    by_cases hi' : ∃ i, e.f i = i'
    · obtain ⟨i, rfl⟩ := hi'
      simpa only [exactAt_iff_of_quasiIsoAt (K.ιTruncLE e)] using hK.exactAt i
    · exact exactAt_of_isSupported _ e i' (by simpa using hi')

variable {K L}

lemma quasiIso_truncLEMap_iff (φ : K ⟶ L) :
    QuasiIso (truncLEMap φ e) ↔ ∀ (i : ι) (i' : ι') (_ : e.f i = i'), QuasiIsoAt φ i' := by
  refine' Iff.trans _ ((quasiIso_truncGEMap_iff ((opFunctor C c').map φ.op) e.op).trans _)
  · simp only [quasiIso_iff, truncLEMap,
      ← quasiIsoAt_unop_iff (truncGEMap ((opFunctor C c').map φ.op) e.op)]
  · simp only [ComplexShape.Embedding.op_f, ← quasiIsoAt_op_iff φ]

end

end HomologicalComplex
