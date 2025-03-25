/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.LinearAlgebra.Matrix.Determinant.Misc
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# Regulator of a number field

We define and prove basic results about the regulator of a number field `K`.

## Main definitions and results

* `NumberField.Units.regOfFamily`: the regulator of a family of units of `K`.

* `NumberField.Units.regulator`: the regulator of the number field `K`.

* `Number.Field.Units.regOfFamily_eq_det`: For any infinite place `w'`, the regulator of the
family `u` is equal to the absolute value of the determinant of the matrix
`(mult w * log w (u i)))_i, w` where `w` runs through the infinite places distinct from `w'`.

## Tags
number field, units, regulator
-/

section index

open Subgroup

@[to_additive]
theorem Subgroup.index_map_equiv {G G' : Type*} [Group G] [Group G']
    (H : Subgroup G) (e : G ≃* G') :
    (map e.toMonoidHom H).index = H.index := sorry

@[to_additive]
theorem Subgroup.relindex_map_equiv {G G' : Type*} [Group G] [Group G'] (H K : Subgroup G) (e : G ≃* G') :
    (map e.toMonoidHom H).relindex (map e.toMonoidHom K) = H.relindex K := sorry

@[to_additive (attr := simp)]
theorem Subgroup.map_comap_map {G G' : Type*} [Group G] [Group G'] (H : Subgroup G) {f : G →* G'} :
    map f (comap f (map f H)) = map f H :=
  (gc_map_comap f).l_u_l_eq_l _

@[to_additive]
theorem Subgroup.relindex_map_map {G G' : Type*} [Group G] [Group G'] (H K : Subgroup G)
    (f : G →* G'):
    (map f H).relindex (map f K) = (H ⊔ f.ker).relindex (K ⊔ f.ker) := by
  rw [← comap_map_eq, ← comap_map_eq, relindex_comap, Subgroup.map_comap_map]

@[to_additive]
lemma Subgroup.index_ne_zero_iff_finite {G : Type*} [Group G] (H : Subgroup G) :
    H.index ≠ 0 ↔ Finite (G ⧸ H) := by
  simp [index_eq_zero_iff_infinite]

theorem Subgroup.closure_toAddSubgroup {G : Type*} [Group G] (s : Set G) :
    (Subgroup.closure s).toAddSubgroup = AddSubgroup.closure (Additive.ofMul '' s) := by
  rw [OrderIso.apply_eq_iff_eq_symm_apply, AddSubgroup.closure,
    OrderIso.map_sInf_eq_sInf_symm_preimage, OrderIso.symm_symm]
  simp_rw [Set.preimage_setOf_eq, coe_toAddSubgroup_apply, Set.preimage_equiv_eq_image_symm,
    Additive.toMul_symm_eq, Set.image_subset_iff, Equiv.preimage_image, closure]

theorem AddSubgroup.closure_toSubgroup {G : Type*} [AddGroup G] (s : Set G) :
    (AddSubgroup.closure s).toSubgroup = Subgroup.closure (Multiplicative.ofAdd '' s) := by
  sorry

end index

section units

open NumberField Units

variable (K : Type*) [Field K] [NumberField K]

theorem zap :
    Subgroup.closure (Set.range (fundSystem K)) ⊔ torsion K = ⊤ := sorry

end units

open scoped NumberField

noncomputable section

namespace NumberField.Units

variable (K : Type*) [Field K]

open MeasureTheory NumberField.InfinitePlace Module Submodule
  NumberField NumberField.Units.dirichletUnitTheorem

variable [NumberField K]

open scoped Classical in
/--
A equiv between `Fin (rank K)`, use to index the family of units, and `{w // w ≠ w₀}` the index of
the `logSpace`.
-/
def equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w ≠ w₀} :=
  Fintype.equivOfCardEq <| by
    rw [Fintype.card_subtype_compl, Fintype.card_ofSubsingleton, Fintype.card_fin, rank]

section regOfFamily

open Matrix

variable {K}

/--
A family of units is of maximal rank if it generates a subgroup of `(𝓞 K)ˣ` of finite index, see
`isMaxRank_iff_closure_finiteIndex`.
-/
abbrev isMaxRank (u : Fin (rank K) → (𝓞 K)ˣ) : Prop :=
  LinearIndependent ℝ (fun i ↦ logEmbedding K (Additive.ofMul (u i)))

/--
The images by `logEmbedding` of a family of units of maximal rank form a basis of `logSpace K`.
-/
def basisOfIsMaxRank {u : Fin (rank K) → (𝓞 K)ˣ} (hu : isMaxRank u) :
    Basis (Fin (rank K)) ℝ (logSpace K) := by
  classical
  exact (basisOfPiSpaceOfLinearIndependent
    ((linearIndependent_equiv (equivFinRank K).symm).mpr hu)).reindex (equivFinRank K).symm

@[simp]
theorem basisOfIsMaxRank_apply {u : Fin (rank K) → (𝓞 K)ˣ} (hu : isMaxRank u) (i : Fin (rank K)) :
    (basisOfIsMaxRank hu) i = logEmbedding K (Additive.ofMul (u i)) := by
  classical
  simp [basisOfIsMaxRank, Basis.coe_reindex,  Equiv.symm_symm, Function.comp_apply,
    coe_basisOfPiSpaceOfLinearIndependent]

theorem finiteIndex_iff_sup_torsion_finiteIndex (s : Subgroup (𝓞 K)ˣ) :
    s.FiniteIndex ↔ (s ⊔ torsion K).FiniteIndex := by
  refine ⟨fun h ↦ Subgroup.finiteIndex_of_le le_sup_left, fun h ↦ ?_⟩
  rw [Subgroup.finiteIndex_iff, ← Subgroup.relindex_mul_index (le_sup_left : s ≤ s ⊔ torsion K)]
  refine Nat.mul_ne_zero ?_ (Subgroup.finiteIndex_iff.mp h)
  rw [Subgroup.relindex_sup_left]
  exact Subgroup.FiniteIndex.finiteIndex

open Subgroup in
/--
A family of units is of maximal rank iff the index of the subgroup it generates has finite index.
-/
theorem isMaxRank_iff_closure_finiteIndex {u : Fin (rank K) → (𝓞 K)ˣ} :
    isMaxRank u ↔ (closure (Set.range u)).FiniteIndex := by
  classical
  have h₁ : (closure (Set.range u) ⊔ torsion K).index ≠ 0 ↔
      Finite (unitLattice K ⧸ span ℤ (Set.range ((logEmbeddingEquiv K) ∘ Additive.toMul.symm ∘
        QuotientGroup.mk ∘ u))) := by
    change _ ↔ Finite ((unitLattice K).toAddSubgroup ⧸ (span ℤ (Set.range _)).toAddSubgroup)
    rw [← AddSubgroup.index_ne_zero_iff_finite]
    have := index_map (closure (Set.range u)) (QuotientGroup.mk' (torsion K))
    rw [QuotientGroup.ker_mk', QuotientGroup.range_mk', index_top, mul_one] at this
    rw [← this, ← index_toAddSubgroup, ← AddSubgroup.index_map_equiv
      _ (logEmbeddingEquiv K).toAddEquiv, Set.range_comp, ← map_span (logEmbeddingEquiv K),
      ← map_coe_toLinearMap, map_toAddSubgroup, span_int_eq_addSubgroup_closure,
      MonoidHom.map_closure, closure_toAddSubgroup, Set.range_comp, Set.range_comp,
      QuotientGroup.coe_mk',  Set.preimage_equiv_eq_image_symm]
    exact Iff.rfl
  have h₂ : DiscreteTopology
      (span ℤ (Set.range fun i ↦ (logEmbedding K) (Additive.ofMul (u i)))) := by
    refine DiscreteTopology.of_subset (inferInstance : DiscreteTopology (unitLattice K)) ?_
    rw [SetLike.coe_subset_coe, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨Additive.ofMul (u i), mem_top, rfl⟩
  rw [finiteIndex_iff_sup_torsion_finiteIndex, finiteIndex_iff, h₁, finiteQuotient_iff,
    unitLattice_rank, ← Set.finrank, isMaxRank, linearIndependent_iff_card_eq_finrank_span,
    Real.finrank_eq_int_finrank_of_discrete h₂, Set.finrank, Set.finrank, ← finrank_map_subtype_eq,
    map_span, ← Set.range_comp', eq_comm]
  simp

/--
The regulator of a family of units of `K`.
-/
def regOfFamily (u : Fin (rank K) → (𝓞 K)ˣ) : ℝ := by
  classical
  by_cases hu : isMaxRank u
  · exact ZLattice.covolume (span ℤ (Set.range (basisOfIsMaxRank  hu)))
  · exact 0

theorem regOfFamily_eq_zero {u : Fin (rank K) → (𝓞 K)ˣ} (hu : ¬ isMaxRank u) :
    regOfFamily u = 0 := by
  rw [regOfFamily, dif_neg hu]

open scoped Classical in
theorem regOfFamily_of_isMaxRank {u : Fin (rank K) → (𝓞 K)ˣ} (hu : isMaxRank u) :
    regOfFamily u = ZLattice.covolume (span ℤ (Set.range (basisOfIsMaxRank  hu))) := by
  rw [regOfFamily, dif_pos hu]

theorem regOfFamily_pos {u : Fin (rank K) → (𝓞 K)ˣ} (hu : isMaxRank u) :
    0 < regOfFamily u := by
  classical
  rw [regOfFamily_of_isMaxRank hu]
  exact ZLattice.covolume_pos _ volume

theorem regOfFamily_ne_zero {u : Fin (rank K) → (𝓞 K)ˣ} (hu : isMaxRank u) :
    regOfFamily u ≠ 0 := (regOfFamily_pos hu).ne'

theorem regOfFamily_ne_zero_iff {u : Fin (rank K) → (𝓞 K)ˣ} :
    regOfFamily u ≠ 0 ↔ isMaxRank u :=
  ⟨by simpa using (fun hu ↦ regOfFamily_eq_zero hu).mt, fun hu ↦ regOfFamily_ne_zero hu⟩

open scoped Classical in
theorem regOfFamily_eq_det' (u : Fin (rank K) → (𝓞 K)ˣ) :
    regOfFamily u =
      |(of fun i ↦ logEmbedding K (Additive.ofMul (u ((equivFinRank K).symm i)))).det| := by
  by_cases hu : isMaxRank u
  · rw [regOfFamily_of_isMaxRank hu, ZLattice.covolume_eq_det _
      (((basisOfIsMaxRank hu).restrictScalars ℤ).reindex (equivFinRank K)), Basis.coe_reindex]
    congr with i
    simp [basisOfIsMaxRank_apply hu]
  · rw [regOfFamily_eq_zero hu, det_eq_zero_of_not_linearIndependent_rows, abs_zero]
    rwa [isMaxRank, ← linearIndependent_equiv (equivFinRank K).symm] at hu

open scoped Classical in
/--
Let `u : Fin (rank K) → (𝓞 K)ˣ` be a family of units and let `w₁` and `w₂` be two infinite
places. Then, the two square matrices with entries `(mult w * log w (u i))_i` where `w ≠ w_j` for
`j = 1, 2` have the same determinant in absolute value.
-/
theorem abs_det_eq_abs_det (u : Fin (rank K) → (𝓞 K)ˣ)
    {w₁ w₂ : InfinitePlace K} (e₁ : {w // w ≠ w₁} ≃ Fin (rank K))
    (e₂ : {w // w ≠ w₂} ≃ Fin (rank K)) :
    |(of fun i w : {w // w ≠ w₁} ↦ (mult w.val : ℝ) * (w.val (u (e₁ i) : K)).log).det| =
    |(of fun i w : {w // w ≠ w₂} ↦ (mult w.val : ℝ) * (w.val (u (e₂ i) : K)).log).det| := by
  -- We construct an equiv `Fin (rank K + 1) ≃ InfinitePlace K` from `e₂.symm`
  let f : Fin (rank K + 1) ≃ InfinitePlace K :=
    (finSuccEquiv _).trans ((Equiv.optionSubtype _).symm e₁.symm).val
  -- And `g` corresponds to the restriction of `f⁻¹` to `{w // w ≠ w₂}`
  let g : {w // w ≠ w₂} ≃ Fin (rank K) :=
    (Equiv.subtypeEquiv f.symm (fun _ ↦ by simp [f])).trans
      (finSuccAboveEquiv (f.symm w₂)).symm
  have h_col := congr_arg abs <| det_permute (g.trans e₂.symm)
    (of fun i w : {w // w ≠ w₂} ↦ (mult w.val : ℝ) * (w.val (u (e₂ i) : K)).log)
  rw [abs_mul, ← Int.cast_abs, Equiv.Perm.sign_abs, Int.cast_one, one_mul] at h_col
  rw [← h_col]
  have h := congr_arg abs <| submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det'
    (of fun i w ↦ (mult (f w) : ℝ) * ((f w) (u i)).log) ?_ 0 (f.symm w₂)
  · rw [← det_reindex_self e₁, ← det_reindex_self g]
    · rw [Units.smul_def, abs_zsmul, Int.abs_negOnePow, one_smul] at h
      convert h
      · ext; simp only [ne_eq, reindex_apply, submatrix_apply, of_apply, Equiv.apply_symm_apply,
          Equiv.trans_apply, Fin.succAbove_zero, id_eq, finSuccEquiv_succ,
          Equiv.optionSubtype_symm_apply_apply_coe, f]
      · ext; simp only [ne_eq, Equiv.coe_trans, reindex_apply, submatrix_apply, Function.comp_apply,
          Equiv.apply_symm_apply, id_eq, of_apply]; rfl
  · intro _
    simp_rw [of_apply, ← Real.log_pow]
    rw [← Real.log_prod, Equiv.prod_comp f (fun w ↦ (w (u _) ^ (mult w))), prod_eq_abs_norm,
      Units.norm, Rat.cast_one, Real.log_one]
    exact fun _ _ ↦ pow_ne_zero _ <| (map_ne_zero _).mpr (coe_ne_zero _)

open scoped Classical in
/--
For any infinite place `w'`, the regulator of the family `u` is equal to the absolute value of
the determinant of the matrix with entries `(mult w * log w (u i))_i` for `w ≠ w'`.
-/
theorem regOfFamily_eq_det (u : Fin (rank K) → (𝓞 K)ˣ) (w' : InfinitePlace K)
    (e : {w // w ≠ w'} ≃ Fin (rank K)) :
    regOfFamily u =
      |(of fun i w : {w // w ≠ w'} ↦ (mult w.val : ℝ) * Real.log (w.val (u (e i) : K))).det| := by
  rw [regOfFamily_eq_det', abs_det_eq_abs_det u e (equivFinRank K).symm]
  simp [logEmbedding]

open scoped Classical in
/--
The degree of `K` times the regulator of the family `u` is equal to the absolute value of the
determinant of the matrix whose columns are
`(mult w * log w (fundSystem K i))_i, w` and the column `(mult w)_w`.
-/
theorem finrank_mul_regOfFamily_eq_det (u : Fin (rank K) → (𝓞 K)ˣ) (w' : InfinitePlace K)
    (e : {w // w ≠ w'} ≃ Fin (rank K)) :
    finrank ℚ K * regOfFamily u =
      |(of (fun i w : InfinitePlace K ↦
        if h : i = w' then (w.mult : ℝ) else w.mult * (w (u (e ⟨i, h⟩))).log)).det| := by
  let f : Fin (rank K + 1) ≃ InfinitePlace K :=
    (finSuccEquiv _).trans ((Equiv.optionSubtype _).symm e.symm).val
  let g : {w // w ≠ w'} ≃ Fin (rank K) :=
    (Equiv.subtypeEquiv f.symm (fun _ ↦ by simp [f])).trans (finSuccAboveEquiv (f.symm w')).symm
  rw [← det_reindex_self f.symm, det_eq_sum_row_mul_submatrix_succAbove_succAbove_det _ (f.symm w')
    (f.symm w'), abs_mul, abs_mul, abs_neg_one_pow, one_mul]
  · simp_rw [reindex_apply, submatrix_submatrix, ← f.symm.sum_comp, f.symm_symm, submatrix_apply,
      Function.comp_def, Equiv.apply_symm_apply, of_apply, dif_pos, ← Nat.cast_sum, sum_mult_eq,
      Nat.abs_cast]
    rw [regOfFamily_eq_det u w' e, ← Matrix.det_reindex_self g]
    congr with i j
    rw [reindex_apply, submatrix_apply, submatrix_apply, of_apply, of_apply, dif_neg]
    rfl
  · simp_rw [Equiv.forall_congr_left f, ← f.symm.sum_comp, reindex_apply, submatrix_apply,
      of_apply, f.symm_symm, f.apply_symm_apply, Finset.sum_dite_irrel, ne_eq,
      EmbeddingLike.apply_eq_iff_eq]
    intro _ h
    rw [dif_neg h, sum_mult_mul_log]

end regOfFamily

section regulator

open scoped Classical in
/-- The regulator of a number field `K`. -/
def regulator : ℝ := ZLattice.covolume (unitLattice K)

theorem isMaxRank_fundSystem :
    isMaxRank (fundSystem K) := by
  classical
  convert ((basisUnitLattice K).ofZLatticeBasis ℝ (unitLattice K)).linearIndependent
  rw [logEmbedding_fundSystem, Basis.ofZLatticeBasis_apply]

open scoped Classical in
theorem basisOfIsMaxRank_fundSystem :
    basisOfIsMaxRank (isMaxRank_fundSystem K) = (basisUnitLattice K).ofZLatticeBasis ℝ := by
  ext
  rw [Basis.ofZLatticeBasis_apply, basisOfIsMaxRank_apply, logEmbedding_fundSystem]

theorem regulator_eq_regOfFamily_fundSystem :
    regulator K = regOfFamily (fundSystem K) := by
  classical
  rw [regOfFamily_of_isMaxRank (isMaxRank_fundSystem K), regulator,
    ← (basisUnitLattice K).ofZLatticeBasis_span ℝ, basisOfIsMaxRank_fundSystem]

theorem regulator_pos : 0 < regulator K :=
  regulator_eq_regOfFamily_fundSystem K ▸ regOfFamily_pos (isMaxRank_fundSystem K)

theorem regulator_ne_zero : regulator K ≠ 0 :=
  (regulator_pos K).ne'

end regulator
section index

open ZLattice

variable {K}

theorem isMaxRank_iff {u : Fin (rank K) → (𝓞 K)ˣ} :
    isMaxRank u ↔ Finite ((𝓞 K)ˣ ⧸  Subgroup.closure (Set.range u)) := by
  classical
--  have : Module.Finite ℤ (logSpace K) := sorry
--  have : Module.Free ℤ (logSpace K) := sorry
  let φ := (logEmbeddingEquiv K) ∘ Additive.ofMul ∘ QuotientGroup.mk
  have h₁ := finiteQuotient_iff (span ℤ (Set.range (φ ∘ u)))
  have h₂ : Finite ((𝓞 K)ˣ ⧸ Subgroup.closure (Set.range u)) ↔
    Finite (unitLattice K ⧸ span ℤ (Set.range (φ ∘ u))) := sorry
  rw [h₂, h₁]
  simp [unitLattice_rank, φ]
  rw [eq_comm]
  have : rank K = Fintype.card (Fin (rank K)) := by exact Eq.symm (Fintype.card_fin (rank K))
  nth_rewrite 1 [this]
  rw [← Set.finrank]


#exit
  rw [isMaxRank, linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin, eq_comm]
  have : Set.finrank ℤ (Set.range ((logEmbeddingEquiv K ∘ ⇑Additive.ofMul ∘ QuotientGroup.mk) ∘ u))
    = Set.finrank ℤ (Set.range (fun i ↦ logEmbedding K (Additive.ofMul (u i)))) := sorry
  rw [← Set.finrank]
  rw?
  sorry
  -- simp only [Fintype.card_fin, ne_eq, φ]
  -- rw [← Set.finrank]
  -- simp
  -- have : Set.finrank ℤ (Set.range ((logEmbeddingEquiv K ∘ ⇑Additive.ofMul ∘ QuotientGroup.mk) ∘ u))
  --   = Set.finrank ℤ (Set.range (fun i ↦ logEmbedding K (Additive.ofMul (u i)))) := sorry
  -- rw [this]
  -- rw [linearIndependent_iff_card_le_finrank_span]
  -- simp

theorem regOfFamily_div_regOfFamily' {u v : Fin (rank K) → (𝓞 K)ˣ} (hu : isMaxRank u)
    (hv : isMaxRank v)
    (h : Subgroup.closure (Set.range u) ≤ Subgroup.closure (Set.range v)) :
    regOfFamily u / regOfFamily v = (Subgroup.closure (Set.range u) ⊔ (torsion K)).relindex
      (Subgroup.closure (Set.range v) ⊔ (torsion K)) := by
  classical
  rw [regOfFamily_of_isMaxRank hu, regOfFamily_of_isMaxRank hv, covolume_div_covolume_eq_relindex,
    span_basisOfIsMaxRank_toAddSubgroup hu,  span_basisOfIsMaxRank_toAddSubgroup hv,
    AddSubgroup.relindex_map_map, logEmbedding_ker, ← OrderIso.map_sup, ← OrderIso.map_sup,
    ← Subgroup.relindex_toAddSubgroup]
  rw [← toAddSubgroup_le, span_basisOfIsMaxRank_toAddSubgroup hu,
    span_basisOfIsMaxRank_toAddSubgroup hv]
  exact AddSubgroup.map_mono (by rwa [OrderIso.le_iff_le])

theorem regOfFamily_div_regulator' {u : Fin (rank K) → (𝓞 K)ˣ} (hu : isMaxRank u) :
    regOfFamily u / regulator K = (Subgroup.closure (Set.range u) ⊔ (torsion K)).index := by
  rw [regulator_eq_regOfFamily_fundSystem, regOfFamily_div_regOfFamily' hu (isMaxRank_fundSystem K),
    zap, Subgroup.relindex_top_right]
  sorry

theorem regOfFamily_div_regOfFamily {u v : Fin (rank K) → (𝓞 K)ˣ} (hv : isMaxRank v)
    (h : Subgroup.closure (Set.range u) ≤ Subgroup.closure (Set.range v)) :
    regOfFamily u / regOfFamily v = (Subgroup.closure (Set.range u) ⊔ (torsion K)).relindex
      (Subgroup.closure (Set.range v) ⊔ (torsion K)) := by
  by_cases hu : isMaxRank u
  · exact regOfFamily_div_regOfFamily' hu hv h
  · rw [regOfFamily_eq_zero hu, zero_div, eq_comm, Nat.cast_eq_zero]
    have h₁ := Subgroup.relindex_mul_index h
    have h₂ := isMaxRank_iff.not.mp hu
    rw [not_finite_iff_infinite, ← Subgroup.index_eq_zero_iff_infinite] at h₂
    rw [h₂] at h₁
    rw [Nat.mul_eq_zero] at h₁







#exit





theorem regOfFamily_div_regOfFamily (u : Fin (rank K) → (𝓞 K)ˣ) (v : Fin (rank K) → (𝓞 K)ˣ)
    (hv : isMaxRank v) (h : Subgroup.closure (Set.range u) ≤ Subgroup.closure (Set.range v)) :
    regOfFamily u / regOfFamily v = (Subgroup.closure (Set.range u) ⊔ (torsion K)).relindex
      (Subgroup.closure (Set.range v) ⊔ (torsion K)) := by
  classical
  by_cases hu : isMaxRank u
  · let U := (Subgroup.closure (Set.range u)).toAddSubgroup
    let V := (Subgroup.closure (Set.range v)).toAddSubgroup
    have hU : (span ℤ (Set.range ⇑(basisOfIsMaxRank hu))).toAddSubgroup =
        AddSubgroup.map (logEmbedding K) U := by
      exact span_basisOfIsMaxRank_toAddSubgroup hu
    have hV : (span ℤ (Set.range ⇑(basisOfIsMaxRank hv))).toAddSubgroup =
      AddSubgroup.map (logEmbedding K) V := by
      exact span_basisOfIsMaxRank_toAddSubgroup hv
    rw [regOfFamily_of_isMaxRank hu, regOfFamily_of_isMaxRank hv, covolume_div_covolume_eq_relindex]
    · rw [hU, hV]
      rw [AddSubgroup.relindex_map_map, logEmbedding_ker]
      unfold U V
      rw [← OrderIso.map_sup, ← OrderIso.map_sup]
      rw [Subgroup.relindex_toAddSubgroup]
    · rw [← Subgroup.toAddSubgroup.le_iff_le] at h
      have := Set.image_mono (f := logEmbedding K) h
      rw [← toAddSubgroup_le, hU, hV]
      exact this
  ·
    rw [regOfFamily_eq_zero hu, zero_div]

    rw [← Subgroup.relindex_toAddSubgroup, OrderIso.map_sup,
      OrderIso.map_sup, ← logEmbedding_ker]
    rw [← AddSubgroup.relindex_map_map]


    rw [Subgroup.closure_toAddSubgroup, Subgroup.closure_toAddSubgroup]
    rw [AddMonoidHom.map_closure, AddMonoidHom.map_closure]
    rw [← Submodule.span_int_eq_addSubgroup_closure, ← Submodule.span_int_eq_addSubgroup_closure]
    rw [eq_comm, Nat.cast_eq_zero]
    -- refine AddSubgroup.relindex_eq_zero_of_le_left (K := ⊤) ?_ ?_
    sorry


#exit


    rw [AddSubgroup.index_eq_zero_iff_infinite]
    rw [← not_finite_iff_infinite]
    rw [finiteQuotient_iff]

#exit

    rw [regOfFamily_eq_zero hu, zero_div]
    rw [← Subgroup.relindex_toAddSubgroup, OrderIso.map_sup,
      OrderIso.map_sup, ← logEmbedding_ker]
    rw [← AddSubgroup.relindex_map_map]
    rw [eq_comm, Nat.cast_eq_zero]
    rw [Subgroup.closure_toAddSubgroup, Subgroup.closure_toAddSubgroup]
    rw [← Submodule.span_int_eq_addSubgroup_closure, ← Submodule.span_int_eq_addSubgroup_closure]
    rw [AddSubgroup.relindex]
    rw [AddSubgroup.index_eq_zero_iff_infinite]
    rw [← not_finite_iff_infinite]
    rw [finiteQuotient_iff]


    sorry

example (u : Fin (rank K) → (𝓞 K)ˣ) :
    isMaxRank u ↔ (Subgroup.closure (Set.range u) ⊔ (torsion K)).index ≠ 0 := by
  rw [← Subgroup.relindex_top_right]
  have : (⊤ : Subgroup (𝓞 K)ˣ) = (Subgroup.closure (Set.range (fundSystem K)) ⊔ (torsion K)) :=
    sorry
  rw [this]
  rw [← Nat.cast_ne_zero (R := ℝ)]
  rw [← regOfFamily_div_regOfFamily]
  simp only [ne_eq, div_eq_zero_iff, not_or]
  rw [← regulator_eq_regOfFamily_fundSystem]
  simp_rw [regulator_ne_zero]
  simp [regOfFamily_ne_zero_iff]
  exact isMaxRank_fundSystem K
  rw [← this]
  exact le_top



#exit

  classical
  let A := AddSubgroup.closure (Set.range (Additive.ofMul ∘ (QuotientGroup.mk' (torsion K)) ∘ u))
  have : Finite ((𝓞 K)ˣ ⧸ Subgroup.closure (Set.range u)) ↔
    A.index ≠ 0 := sorry -- Finite (Additive ((𝓞 K)ˣ ⧸ (torsion K)) ⧸ A) := sorry
  rw [this]
  rw [← AddSubgroup.index_map_equiv _ (logEmbeddingEquiv K).toAddEquiv]
  rw [AddSubgroup.index_ne_zero_iff_finite]
  simp only [ne_eq, LinearEquiv.coe_toAddEquiv, AddEquiv.toAddMonoidHom_eq_coe]
  have : Finite ((unitLattice K) ⧸ AddSubgroup.map ((logEmbeddingEquiv K)) A) ↔
    Finite ((unitLattice K) ⧸ (AddSubgroup.map ((logEmbeddingEquiv K)) A).toIntSubmodule) := sorry
  erw [this]
  rw [finiteQuotient_iff ]
  simp

#exit

  classical
  rw [isMaxRank]
  rw [linearIndependent_iff_card_eq_finrank_span]
  rw [Set.finrank]
  have := unitLattice_rank K
  rw [Fintype.card_fin]
  simp_rw [← this]



#exit

example (u : Fin (rank K) → (𝓞 K)ˣ) :
    (Subgroup.closure (Set.range u)).index ≠ 0 ↔ isMaxRank u :=
  have : (Subgroup.closure (Set.range u)).index = torsionOrder K *

  sorry

example (u : Fin (rank K) → (𝓞 K)ˣ) :
    (Subgroup.closure (Set.range u)).index =
      (torsionOrder K) * regOfFamily u / regulator K := by
--  rw [← Subgroup.relindex_top_right]
  convert_to (AddSubgroup.closure (Set.range (Additive.ofMul ∘ u))).index =
    torsionOrder K * regOfFamily u / regulator K
  sorry
  rw [← AddSubgroup.relindex_top_right]
  rw [← AddSubgroup.relindex_map_of_injective (f := logEmbedding K)]
  have : (AddSubgroup.map (logEmbedding K) ⊤) = (unitLattice K).toAddSubgroup := sorry
  rw [this]
  have : (AddSubgroup.map (logEmbedding K) (AddSubgroup.closure (Set.range (Additive.ofMul ∘ u)))) =
    (span ℤ (Set.range (basisOfIsMaxRank (u := u) sorry))).toAddSubgroup := sorry
  rw [this]
  classical
  rw [← ZLattice.covolume_div_covolume_eq_relindex]
  rw [regOfFamily_of_isMaxRank, regulator]





example (u : Fin (rank K) → (𝓞 K)ˣ) :
  (AddSubgroup.closure (Set.range (Additive.ofMul ∘ QuotientGroup.mk' (torsion K) ∘ u))).index =
    regOfFamily u / regulator K := by
  let v := Additive.ofMul ∘ QuotientGroup.mk' (torsion K) ∘ u

end index

end Units

end NumberField
