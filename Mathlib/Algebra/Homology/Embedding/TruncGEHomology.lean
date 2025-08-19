/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.Embedding.TruncGE
import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
import Mathlib.Algebra.Homology.QuasiIso

/-! # The homology of a canonical truncation

Given an embedding of complex shapes `e : Embedding c c'`,
we relate the homology of `K : HomologicalComplex C c'` and of
`K.truncGE e : HomologicalComplex C c'`.

The main result is that `K.πTruncGE e : K ⟶ K.truncGE e` induces a
quasi-isomorphism in degree `e.f i` for all `i`. (Note that the complex
`K.truncGE e` is exact in degrees that are not in the image of `e.f`.)

-/

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category C] [HasZeroMorphisms C]
  (K L : HomologicalComplex C c') (φ : K ⟶ L) (e : c.Embedding c') [e.IsTruncGE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i']

namespace truncGE'

variable (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)

include hi hk in
lemma hasHomology_sc'_of_not_mem_boundary (hj : ¬ e.BoundaryGE j) :
    ((K.truncGE' e).sc' i j k).HasHomology := by
  have : (K.restriction e).HasHomology j :=
    restriction.hasHomology K e i j k hi hk rfl rfl rfl
      (e.prev_f_of_not_boundaryGE hi hj) (e.next_f hk)
  have := ShortComplex.hasHomology_of_iso ((K.restriction e).isoSc' i j k hi hk)
  let φ := (shortComplexFunctor' C c i j k).map (K.restrictionToTruncGE' e)
  have : Epi φ.τ₁ := by dsimp [φ]; infer_instance
  have : IsIso φ.τ₂ := K.isIso_restrictionToTruncGE' e j hj
  have : IsIso φ.τ₃ := K.isIso_restrictionToTruncGE' e k (e.not_boundaryGE_next' hj hk)
  exact ShortComplex.hasHomology_of_epi_of_isIso_of_mono φ

lemma hasHomology_of_not_mem_boundary (hj : ¬ e.BoundaryGE j) :
    (K.truncGE' e).HasHomology j :=
  hasHomology_sc'_of_not_mem_boundary K e _ j _ rfl rfl hj

/-- `K.restrictionToTruncGE' e` is a quasi-isomorphism in degrees that are not at the boundary. -/
lemma quasiIsoAt_restrictionToTruncGE' (hj : ¬ e.BoundaryGE j)
    [(K.restriction e).HasHomology j] [(K.truncGE' e).HasHomology j] :
    QuasiIsoAt (K.restrictionToTruncGE' e) j := by
  rw [quasiIsoAt_iff]
  let φ := (shortComplexFunctor C c j).map (K.restrictionToTruncGE' e)
  have : Epi φ.τ₁ := by dsimp [φ]; infer_instance
  have : IsIso φ.τ₂ := K.isIso_restrictionToTruncGE' e j hj
  have : IsIso φ.τ₃ := K.isIso_restrictionToTruncGE' e _ (e.not_boundaryGE_next' hj rfl)
  exact ShortComplex.quasiIso_of_epi_of_isIso_of_mono φ

section

variable {j' : ι'} (hj' : e.f j = j') (hj : e.BoundaryGE j)

lemma homologyι_truncGE'XIsoOpcycles_inv_d :
    (K.homologyι j' ≫ (K.truncGE'XIsoOpcycles e hj' hj).inv) ≫ (K.truncGE' e).d j k = 0 := by
  by_cases hjk : c.Rel j k
  · rw [K.truncGE'_d_eq_fromOpcycles e hjk hj' rfl hj, assoc, Iso.inv_hom_id_assoc,
    homologyι_comp_fromOpcycles_assoc, zero_comp]
  · rw [shape _ _ _ hjk, comp_zero]

/-- Auxiliary definition for `truncGE'.homologyData`. -/
noncomputable def isLimitKernelFork :
    IsLimit (KernelFork.ofι _ (homologyι_truncGE'XIsoOpcycles_inv_d K e j k hj' hj)) := by
  have hk' : c'.next j' = e.f k := by simpa only [hj'] using e.next_f hk
  by_cases hjk : c.Rel j k
  · let e : parallelPair ((K.truncGE' e).d j k) 0 ≅
        parallelPair (K.fromOpcycles j' (e.f k)) 0 :=
      parallelPair.ext (K.truncGE'XIsoOpcycles e hj' hj)
        (K.truncGE'XIso e rfl (e.not_boundaryGE_next hjk))
        (by simp [K.truncGE'_d_eq_fromOpcycles e hjk hj' rfl hj]) (by simp)
    exact (IsLimit.postcomposeHomEquiv e _).1
      (IsLimit.ofIsoLimit (K.homologyIsKernel _ _ hk')
      (Fork.ext (Iso.refl _) (by simp [e, Fork.ι])))
  · have := K.isIso_homologyι _ _ hk'
      (shape _ _ _ (by simpa only [← hj', e.rel_iff] using hjk))
    exact IsLimit.ofIsoLimit (KernelFork.IsLimit.ofId _ (shape _ _ _ hjk))
      (Fork.ext ((truncGE'XIsoOpcycles K e hj' hj) ≪≫ (asIso (K.homologyι j')).symm))

/-- When `j` is at the boundary of the embedding `e` of complex shapes,
this is a homology data for `K.truncGE' e` in degree `j`: the homology is
given by `K.homology j'` where `e.f j = j'`. -/
noncomputable def homologyData :
    ((K.truncGE' e).sc' i j k).HomologyData :=
  ShortComplex.HomologyData.ofIsLimitKernelFork _
    ((K.truncGE' e).shape _ _ (fun hij ↦ e.not_boundaryGE_next hij hj)) _
    (isLimitKernelFork K e j k hk hj' hj)

/-- Computation of the `right.g'` field of `truncGE'.homologyData K e i j k hk hj' hj`. -/
@[simp]
lemma homologyData_right_g' :
    (homologyData K e i j k hk hj' hj).right.g' = (K.truncGE' e).d j k := rfl

end

instance truncGE'_hasHomology (i : ι) : (K.truncGE' e).HasHomology i := by
  by_cases hi : e.BoundaryGE i
  · exact ShortComplex.HasHomology.mk' (homologyData K e _ _ _ rfl rfl hi)
  · exact hasHomology_of_not_mem_boundary K e i hi

end truncGE'

variable [HasZeroObject C]

namespace truncGE

instance (i' : ι') : (K.truncGE e).HasHomology i' := by
  dsimp [truncGE]
  infer_instance

/-- The right homology data which allows to show that `K.πTruncGE e`
induces an isomorphism in homology in degrees `j'` such that `e.f j = j'` for some `j`. -/
@[simps]
noncomputable def rightHomologyMapData {i j k : ι} {j' : ι'} (hj' : e.f j = j')
    (hi : c.prev j = i) (hk : c.next j = k) (hj : e.BoundaryGE j) :
    ShortComplex.RightHomologyMapData ((shortComplexFunctor C c' j').map (K.πTruncGE e))
    (ShortComplex.RightHomologyData.canonical (K.sc j'))
    (extend.rightHomologyData (K.truncGE' e) e hj' hi rfl hk rfl
      (truncGE'.homologyData K e i j k hk hj' hj).right) where
  φQ := (K.truncGE'XIsoOpcycles e hj' hj).inv
  φH := 𝟙 _
  commp := by
    change K.pOpcycles j' ≫ _ = _
    simp [truncGE'.homologyData, πTruncGE, e.liftExtend_f _ _ hj',
      K.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv e hj' hj]
  commg' := by
    have hk' : e.f k = c'.next j' := by rw [← hj', e.next_f hk]
    dsimp
    rw [extend.rightHomologyData_g' _ _ _ _ _ _ _ _ hk', πTruncGE,
        e.liftExtend_f _ _ hk', truncGE'.homologyData_right_g']
    by_cases hjk : c.Rel j k
    · simp [K.truncGE'_d_eq_fromOpcycles e hjk hj' hk' hj,
        K.restrictionToTruncGE'_f_eq_iso_hom_iso_inv e hk' (e.not_boundaryGE_next hjk)]
      rfl
    · obtain rfl : k = j := by rw [← c.next_eq_self j  (by simpa only [hk] using hjk), hk]
      rw [shape _ _ _ hjk, zero_comp, comp_zero,
        K.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv e hk' hj]
      simp only [restriction_X, restrictionXIso, eqToIso.inv, eqToIso.hom, assoc,
        eqToHom_trans_assoc, eqToHom_refl, id_comp]
      change 0 = K.fromOpcycles _ _ ≫ _
      rw [← cancel_epi (K.pOpcycles _), comp_zero, p_fromOpcycles_assoc,
        d_pOpcycles_assoc, zero_comp]

end truncGE

lemma quasiIsoAt_πTruncGE {j : ι} {j' : ι'} (hj' : e.f j = j') :
    QuasiIsoAt (K.πTruncGE e) j' := by
  rw [quasiIsoAt_iff]
  by_cases hj : e.BoundaryGE j
  · rw [(truncGE.rightHomologyMapData K e hj' rfl rfl hj).quasiIso_iff]
    dsimp
    infer_instance
  · let φ := (shortComplexFunctor C c' j').map (K.πTruncGE e)
    have : Epi φ.τ₁ := by
      by_cases hi : ∃ i, e.f i = c'.prev j'
      · obtain ⟨i, hi⟩ := hi
        dsimp [φ, πTruncGE]
        rw [e.epi_liftExtend_f_iff _ _ hi]
        infer_instance
      · apply IsZero.epi (isZero_extend_X _ _ _ (by simpa using hi))
    have : IsIso φ.τ₂ := by
      dsimp [φ, πTruncGE]
      rw [e.isIso_liftExtend_f_iff _ _ hj']
      exact K.isIso_restrictionToTruncGE' e j hj
    have : IsIso φ.τ₃ := by
      dsimp [φ, πTruncGE]
      have : c'.next j' = e.f (c.next j) := by simpa only [← hj'] using e.next_f rfl
      rw [e.isIso_liftExtend_f_iff _ _ this.symm]
      exact K.isIso_restrictionToTruncGE' e _ (e.not_boundaryGE_next' hj rfl)
    exact ShortComplex.quasiIso_of_epi_of_isIso_of_mono φ

instance (i : ι) : QuasiIsoAt (K.πTruncGE e) (e.f i) := K.quasiIsoAt_πTruncGE e rfl

lemma quasiIso_πTruncGE_iff_isSupported :
    QuasiIso (K.πTruncGE e) ↔ K.IsSupported e := by
  constructor
  · intro
    refine ⟨fun i' hi' ↦ ?_⟩
    rw [exactAt_iff_of_quasiIsoAt (K.πTruncGE e) i']
    exact (K.truncGE e).exactAt_of_isSupported e i' hi'
  · intro
    rw [quasiIso_iff]
    intro i'
    by_cases hi' : ∃ i, e.f i = i'
    · obtain ⟨i, rfl⟩ := hi'
      infer_instance
    · rw [quasiIsoAt_iff_exactAt (K.πTruncGE e) i']
      all_goals exact exactAt_of_isSupported _ e i' (by simpa using hi')

lemma acyclic_truncGE_iff_isSupportedOutside :
    (K.truncGE e).Acyclic ↔ K.IsSupportedOutside e := by
  constructor
  · intro hK
    exact ⟨fun i ↦
      by simpa only [exactAt_iff_of_quasiIsoAt (K.πTruncGE e)] using hK (e.f i)⟩
  · intro hK i'
    by_cases hi' : ∃ i, e.f i = i'
    · obtain ⟨i, rfl⟩ := hi'
      simpa only [← exactAt_iff_of_quasiIsoAt (K.πTruncGE e)] using hK.exactAt i
    · exact exactAt_of_isSupported _ e i' (by simpa using hi')

variable {K L}

lemma quasiIso_truncGEMap_iff :
    QuasiIso (truncGEMap φ e) ↔ ∀ (i : ι) (i' : ι') (_ : e.f i = i'), QuasiIsoAt φ i' := by
  have : ∀ (i : ι) (i' : ι') (_ : e.f i = i'),
      QuasiIsoAt (truncGEMap φ e) i' ↔ QuasiIsoAt φ i' := by
    rintro i _ rfl
    rw [← quasiIsoAt_iff_comp_left (K.πTruncGE e), πTruncGE_naturality φ e,
      quasiIsoAt_iff_comp_right]
  rw [quasiIso_iff]
  constructor
  · intro h i i' hi
    simpa only [← this i i' hi] using h i'
  · intro h i'
    by_cases hi' : ∃ i, e.f i = i'
    · obtain ⟨i, hi⟩ := hi'
      simpa only [this i i' hi] using h i i' hi
    · rw [quasiIsoAt_iff_exactAt]
      all_goals exact exactAt_of_isSupported _ e i' (by simpa using hi')

end HomologicalComplex
