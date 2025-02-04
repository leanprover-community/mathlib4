/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.PolarCoord
import Mathlib.NumberTheory.NumberField.Units.Regulator

/-!
# Fundamental Cone : elements of norm ≤ 1

In this file, we study the subset `NormLessThanOne` of the `fundamentalCone` defined as the
subset of elements `x` such that `mixedEmbedding.norm x ≤ 1`.

Mainly, we want to prove that its frontier has volume zero and compute its volume. For this, we
follow mainly the strategy given in [D. Marcus, *Number Fields*][marcus1977number].

## Strategy of proof

-/

variable {K : Type*} [Field K]

namespace NumberField.mixedEmbedding.NormLessThanOne

open Finset NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem

noncomputable section

section toMixedSpace

def toMixedSpace : (InfinitePlace K → ℝ) →ₐ[ℝ] mixedSpace K where
  toFun := fun x ↦ ⟨fun w ↦ x w.1, fun w ↦ x w.1⟩
  map_zero' := sorry
  map_one' := sorry
  map_add' := sorry
  map_mul' := sorry
  commutes' := sorry

theorem toMixedSpace_apply (x : InfinitePlace K → ℝ) :
    toMixedSpace x = ⟨fun w ↦ x w, fun w ↦ x w⟩ := rfl

theorem normAtPlace_toMixedSpace (x : InfinitePlace K → ℝ) (w : InfinitePlace K) :
    normAtPlace w (toMixedSpace x) = ‖x w‖ := by
  obtain hw | hw :=isReal_or_isComplex w
  · rw [toMixedSpace_apply, normAtPlace_apply_isReal hw]
  · rw [toMixedSpace_apply, normAtPlace_apply_isComplex hw, Complex.norm_real]

theorem norm_rpow [NumberField K] {x : InfinitePlace K → ℝ} (hx : ∀ w, 0 ≤ x w) (r : ℝ) :
    mixedEmbedding.norm (toMixedSpace fun w ↦ (x w) ^ r) =
      mixedEmbedding.norm (toMixedSpace x) ^ r := by
  simp_rw [mixedEmbedding.norm_apply, normAtPlace_toMixedSpace, Real.norm_eq_abs,
    Real.abs_rpow_of_nonneg (hx _), Real.rpow_pow_comm (abs_nonneg _)]
  rw [Real.finset_prod_rpow _ _ fun _ _ ↦ pow_nonneg (abs_nonneg _) _]

theorem logMap_rpow [NumberField K] {x : InfinitePlace K → ℝ} (hx : ∀ w, 0 < x w) (r : ℝ) :
    logMap (toMixedSpace fun w ↦ (x w) ^ r) = r • logMap (toMixedSpace  x) := by
  have h : 0 < mixedEmbedding.norm (toMixedSpace x) :=
    lt_of_le_of_ne' (mixedEmbedding.norm_nonneg _) <| mixedEmbedding.norm_ne_zero_iff.mpr fun w ↦
      normAtPlace_toMixedSpace _ w ▸ (norm_ne_zero_iff.mpr (hx _).ne')
  ext
  simp_rw [Pi.smul_def, logMap_apply, normAtPlace_toMixedSpace, Real.norm_eq_abs, Real.log_abs,
    Real.log_rpow (hx _), norm_rpow (fun _ ↦ (hx _).le),  Real.log_rpow h, smul_eq_mul]
  ring

theorem logMap_toMixedSpace [NumberField K] (x : K) :
    logMap (toMixedSpace fun w ↦ w x) = logMap (mixedEmbedding K x) := by
  refine logMap_eq_of_normAtPlace_eq fun w ↦ ?_
  rw [normAtPlace_toMixedSpace, normAtPlace_apply, Real.norm_of_nonneg (apply_nonneg _ _)]

end toMixedSpace

section normMap

def normMap (x : mixedSpace K) : (InfinitePlace K → ℝ) := fun w ↦ normAtPlace w x

theorem normMap_mixedEmbedding (x : K) :
    normMap (mixedEmbedding K x) = fun w ↦ w x := by
  ext
  rw [normMap, normAtPlace_apply]

theorem normAtPlace_normMap (x : mixedSpace K) (w : InfinitePlace K) :
    normAtPlace w (toMixedSpace (normMap x)) = normAtPlace w x := by
  rw [normAtPlace_toMixedSpace, normMap, Real.norm_of_nonneg (normAtPlace_nonneg _ _)]

theorem norm_normMap [NumberField K] (x : mixedSpace K) :
    mixedEmbedding.norm (toMixedSpace (normMap x)) = mixedEmbedding.norm x := by
  simp_rw [mixedEmbedding.norm_apply, normAtPlace_normMap]

end normMap

section privateLemmas

open Classical in
private theorem sum_eq_zero_iff {ι : Type*} [Fintype ι] (i₀ : ι) (x : ι → ℝ) :
    ∑ i, x i = 0 ↔ x i₀ = - ∑ i : {i // i ≠ i₀}, x i := by
  rw [← Finset.univ.add_sum_erase _ (mem_univ i₀), ← eq_neg_iff_add_eq_zero,
    sum_subtype _ (by aesop : ∀ i, i ∈ univ.erase i₀ ↔ i ≠ i₀)]

open Classical in
private theorem sum_dif_eq_zero {ι : Type*} [Fintype ι] {i₀ : ι} {x : {i // i ≠ i₀} → ℝ} :
    ∑ i : ι, (if h : i = i₀ then - ∑ i : { i // i ≠ i₀ }, x i else x ⟨i, h⟩) = 0 := by
  rw [sum_eq_zero_iff i₀, dif_pos rfl, neg_eq_iff_eq_neg, neg_neg]
  exact Finset.sum_congr rfl fun _ _ ↦ by rw [dif_neg]

private theorem sum_log_eq_zero [NumberField K] {x : mixedSpace K}
    (hx : mixedEmbedding.norm x = 1) :
    ∑ w, w.mult * Real.log (normAtPlace w x) = 0 := by
  have h : ∀ w, normAtPlace w x ≠ 0 := by
    contrapose! hx
    simpa only [mixedEmbedding.norm_eq_zero_iff.mpr hx] using zero_ne_one
  simp_rw [← Real.log_pow, ← Real.log_prod _ _ (fun w _ ↦ pow_ne_zero _ (h w)),
    ← mixedEmbedding.norm_apply, hx, Real.log_one]

end privateLemmas

section complete

variable [NumberField K]

open Classical in
/-- DOCSTRING -/
-- This cannot be a `PartiaHomeomorph` because the target is not an open set
-- Does this need to be a partialhomeo and not just a continuous linear map?
@[simps]
def complete : PartialEquiv ({w : InfinitePlace K // w ≠ w₀} → ℝ) (InfinitePlace K → ℝ) where
  toFun := fun x w ↦ if hw : w = w₀ then - ∑ w, x w else x ⟨w, hw⟩
  invFun := fun x w ↦ x w.1
  source := Set.univ
  target := {x | ∑ w, x w = 0}
  map_source' := fun c x ↦ sum_dif_eq_zero
  map_target' := fun _ _ ↦ trivial
  left_inv' := fun _ _ ↦ funext fun w ↦ by simp_rw [dif_neg w.prop]
  right_inv' := fun _ hx ↦ by
    ext w
    by_cases hw : w = w₀
    · dsimp only
      rw [hw, dif_pos rfl, ← sum_subtype _ (by aesop : ∀ w, w ∈ univ.erase w₀ ↔ w ≠ w₀),
        sum_erase_eq_sub (mem_univ w₀), hx, _root_.zero_sub, neg_neg]
    · simp_rw [dif_neg hw]

open Classical in
theorem complete_apply_of_eq (x : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    complete x w₀ = - ∑ w, x w := by
  simp only [complete_apply, reduceDIte]

theorem complete_apply_of_ne (x : {w : InfinitePlace K // w ≠ w₀} → ℝ) {w : InfinitePlace K}
    (hw : w ≠ w₀) : complete x w = x ⟨w, hw⟩ := by
  simp only [complete_apply, hw, reduceDIte]

end complete

section expMap

variable [NumberField K]

@[simps]
def expMap : PartialHomeomorph (InfinitePlace K → ℝ) (InfinitePlace K → ℝ) where
  toFun := fun x w ↦ Real.exp ((w.mult : ℝ)⁻¹ * x w)
  invFun := fun x w ↦ w.mult * Real.log (x w)
  source := Set.univ
  target := {x | ∀ w, 0 < x w}
  open_source := isOpen_univ
  open_target := by
    simp_rw [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun _ ↦ isOpen_lt continuous_const <| continuous_apply _
  continuousOn_toFun := continuousOn_pi'
    fun i ↦ (ContinuousOn.mul continuousOn_const (continuousOn_apply i Set.univ)).rexp
  continuousOn_invFun := continuousOn_const.mul <| continuousOn_pi.mpr
    fun w ↦ Real.continuousOn_log.comp' (continuousOn_apply _ _) (fun _ h ↦ (h w).ne')
  map_source' := fun _ _ _ ↦ Real.exp_pos _
  map_target' := fun _ _ ↦ trivial
  left_inv' := fun _ _ ↦ by simp only [Real.log_exp, mul_inv_cancel_left₀ mult_coe_ne_zero]
  right_inv' := fun _ hx ↦ by simp only [inv_mul_cancel_left₀ mult_coe_ne_zero, Real.exp_log (hx _)]

theorem expMap_apply' (x : InfinitePlace K → ℝ) :
    expMap x = fun w ↦ Real.exp ((w.mult : ℝ)⁻¹ * x w) := rfl

theorem expMap_pos (x : InfinitePlace K → ℝ) (w : InfinitePlace K) :
    0 < expMap x w :=
  Real.exp_pos _

@[simp]
theorem expMap_zero :
    expMap (0 : InfinitePlace K → ℝ) = 1 := by
  simp_rw [expMap_apply', Pi.zero_apply, mul_zero, Real.exp_zero, Pi.one_def]

theorem expMap_add (x y : InfinitePlace K → ℝ) :
    expMap (x + y) = expMap x * expMap y := by
  simp_rw [expMap_apply', Pi.add_apply, mul_add, Real.exp_add, Pi.mul_def]

theorem expMap_sum {ι : Type*} (s : Finset ι) (f : ι → (InfinitePlace K → ℝ)) :
    expMap (∑ i ∈ s, f i) = ∏ i ∈ s, expMap (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp only [sum_empty, expMap_zero, prod_empty]
  | insert hi ind =>
    rw [prod_insert hi, sum_insert hi, expMap_add, ind]

theorem expMap_smul (c : ℝ) (x : InfinitePlace K → ℝ) :
    expMap (c • x) = (expMap x) ^ c := by
  simp_rw [expMap_apply', Pi.smul_apply, smul_eq_mul, mul_comm c _, ← mul_assoc, Real.exp_mul,
    Pi.pow_def]

theorem expMap_logMap {x : mixedSpace K} (hx : mixedEmbedding.norm x = 1) :
    expMap (complete (logMap x)) = fun w ↦ normAtPlace w x := by
  have h {w} : 0 < normAtPlace w x := by
    have : mixedEmbedding.norm x ≠ 0 := by simp [hx]
    rw [mixedEmbedding.norm_ne_zero_iff] at this
    exact lt_of_le_of_ne' (normAtPlace_nonneg _ _) (this _)
  ext w
  by_cases hw : w = w₀
  · simp_rw [expMap_apply, hw, complete_apply_of_eq, logMap_apply_of_norm_one hx,
      ← (sum_eq_zero_iff w₀ _).mp (sum_log_eq_zero hx), inv_mul_cancel_left₀ mult_coe_ne_zero,
      Real.exp_log h]
  · rw [expMap_apply, complete_apply_of_ne _ hw, logMap_apply_of_norm_one hx, inv_mul_cancel_left₀
      mult_coe_ne_zero, Real.exp_log h]

theorem logMap_expMap (x : InfinitePlace K → ℝ) :
    logMap (toMixedSpace (expMap x)) = fun w ↦ Real.log (x w.1) := sorry

theorem expMap_logEmbedding (u : (𝓞 K)ˣ) :
    expMap (complete (logEmbedding K (Additive.ofMul u))) = fun w ↦ w u := by
  simp_rw [← logMap_eq_logEmbedding, expMap_logMap (norm_unit u), normAtPlace_apply]

end expMap
section polarCoord

open MeasureTheory Real

variable (K) in
abbrev polarSpace := (InfinitePlace K → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℝ)

open Classical MeasurableEquiv in
def equivMixedRealSpace₀ : (polarSpace K) ≃ᵐ realMixedSpace K :=
  trans (trans (prodCongr (piEquivPiSubtypeProd _ _) (refl _)) (prodCongr (prodCongr (refl _)
    (arrowCongr' (Equiv.subtypeEquivRight fun _ ↦ not_isReal_iff_isComplex) (refl _))) (refl _)))
      <| prodAssoc.trans <| (prodCongr (refl _) (arrowProdEquivProdArrow ℝ ℝ _)).symm

open Classical in
def equivMixedRealSpace : (polarSpace K) ≃ₜ realMixedSpace K :=
{ equivMixedRealSpace₀ with
  continuous_toFun := by
    change Continuous fun x : polarSpace K ↦
      (⟨fun w ↦ x.1 w.val, fun w ↦ ⟨x.1 w.val, x.2 w⟩⟩ : realMixedSpace K)
    fun_prop
  continuous_invFun := by
    change Continuous fun x : realMixedSpace K ↦  (fun w ↦ if hw : w.IsReal then x.1 ⟨w, hw⟩ else
      (x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩).1, fun w ↦ (x.2 w).2)
    refine continuous_prod_mk.mpr ⟨continuous_pi_iff.mpr fun w ↦ ?_, by fun_prop⟩
    split_ifs <;> fun_prop }

theorem equivMixedRealSpace_apply (x : polarSpace K) :
    equivMixedRealSpace x = (fun w ↦ x.1 w.val, fun w ↦ ⟨x.1 w.val, x.2 w⟩) := rfl

open Classical in
theorem equivMixedRealSpace_symm_apply (x : realMixedSpace K) :
    equivMixedRealSpace.symm x = ⟨fun w ↦ if hw : w.IsReal then x.1 ⟨w, hw⟩ else
      (x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩).1, fun w ↦ (x.2 w).2⟩ := rfl

variable [NumberField K]

open Classical in
theorem volume_preserving_equivMixedRealSpace :
    MeasurePreserving (equivMixedRealSpace : (polarSpace K) ≃ₜ realMixedSpace K) :=
  .trans (.trans (.prod (volume_preserving_piEquivPiSubtypeProd _ _) (.id volume))
      (.prod (.prod (.id volume) (volume_preserving_arrowCongr' _ _ (.id volume))) (.id volume)))
        <| .trans volume_preserving_prodAssoc <|
        .prod (.id volume) (volume_measurePreserving_arrowProdEquivProdArrow _ _ _).symm

def polarCoord : PartialHomeomorph (mixedSpace K) (polarSpace K) :=
  (mixedEmbedding.polarCoord K).transHomeomorph equivMixedRealSpace.symm

theorem polarCoord_symm_apply (x : polarSpace K) :
    polarCoord.symm x =
      (mixedEmbedding.polarCoord K).symm (fun w ↦ x.1 w, fun w ↦ (x.1 w, x.2 w)) := rfl

-- def expMapFull : PartialHomeomorph (N K) (mixedSpace K) :=
--   ((expMap.prod (PartialHomeomorph.refl _)).transHomeomorph expMapFull₀).trans
--     (mixedEmbedding.polarCoord K).symm

-- theorem expMapFull_apply (x : N K) :
--     expMapFull x =
--       ⟨fun w ↦ expMap x.1 w, fun w ↦ Complex.polarCoord.symm (expMap x.1 w, x.2 w)⟩ := rfl

-- theorem normMap_expMapFull (x : N K) :
--     normMap (expMapFull x) = expMap x.1 := by
--   ext w
--   obtain hw | hw := isReal_or_isComplex w
--   · rw [expMapFull_apply, normMap, normAtPlace_apply_isReal hw,
--       Real.norm_of_nonneg (expMap_pos _ _).le]
--   · rw [expMapFull_apply, normMap, normAtPlace_apply_isComplex hw, Complex.norm_eq_abs,
--       Complex.polarCoord_symm_abs, abs_of_pos (expMap_pos _ _)]

-- -- Do you need this?
-- theorem expMapFull_source :
--     expMapFull.source = (Set.univ : Set (N K)) := by
--   unfold expMapFull
--   rw [PartialHomeomorph.trans_source, PartialHomeomorph.transHomeomorph_source,
--     PartialHomeomorph.prod_source, PartialHomeomorph.refl_source, PartialHomeomorph.symm_source,
--     mixedEmbedding.polarCoord_target, expMap_source, Set.univ_prod_univ, Set.univ_inter,
--     PartialHomeomorph.transHomeomorph_apply, PartialHomeomorph.prod_apply,
--     PartialHomeomorph.refl_apply]
--   sorry

-- -- Do you need this?
-- theorem expMapFull_target :
--     expMapFull.target = (Set.univ : Set (mixedSpace K)) := by
--   sorry

end polarCoord

section expMapBasis

variable [NumberField K]

open Classical in
/-- DOCSTRING -/
def equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w ≠ w₀} :=
  Fintype.equivOfCardEq <| by
    rw [Fintype.card_subtype_compl, Fintype.card_ofSubsingleton, Fintype.card_fin, rank]

open Classical in
def completeBasis₀ : InfinitePlace K → InfinitePlace K → ℝ := by
  intro w
  by_cases hw : w = w₀
  · exact fun w ↦ mult w
  · exact complete (((basisUnitLattice K).reindex equivFinRank).ofZLatticeBasis ℝ
      (unitLattice K) ⟨w, hw⟩)

variable (K) in
def completeBasis : Basis (InfinitePlace K) ℝ (InfinitePlace K → ℝ) :=
  Basis.mk (v := completeBasis₀) sorry sorry

theorem completeBasis_apply_of_ne (w : {w : InfinitePlace K // w ≠ w₀}) :
    completeBasis K w =
      complete (logEmbedding K (Additive.ofMul (fundSystem K (equivFinRank.symm w)))) := by
  rw [completeBasis, Basis.mk_apply, completeBasis₀, dif_neg w.prop, Basis.ofZLatticeBasis_apply,
    Basis.coe_reindex, Function.comp_apply, logEmbedding_fundSystem]

theorem completeBasis_apply_of_eq :
    completeBasis K w₀ = fun w ↦ (mult w : ℝ) := by
  rw [completeBasis, Basis.mk_apply, completeBasis₀, dif_pos rfl]

theorem expMap_basis_of_eq :
    expMap (completeBasis K w₀) = fun _ ↦ Real.exp 1 := by
  simp_rw [expMap_apply', completeBasis_apply_of_eq, inv_mul_cancel₀ mult_coe_ne_zero]

theorem expMap_basis_of_ne (i : {w : InfinitePlace K // w ≠ w₀}) :
    expMap (completeBasis K i) = fun w ↦ w (fundSystem K (equivFinRank.symm i) : 𝓞 K) := by
  rw [expMap_apply', completeBasis_apply_of_ne]
  ext w
  by_cases hw : w = w₀
  · rw [hw, complete_apply_of_eq, sum_logEmbedding_component, neg_mul, neg_neg,
      inv_mul_cancel_left₀ mult_coe_ne_zero, Real.exp_log (pos_at_place _ w₀)]
  · rw [complete_apply_of_ne _ hw, logEmbedding_component, inv_mul_cancel_left₀ mult_coe_ne_zero,
      Real.exp_log (pos_at_place _ w)]

theorem norm_expMap_smul_basis_of_ne (c : ℝ) (i : {w : InfinitePlace K // w ≠ w₀}) :
    mixedEmbedding.norm (toMixedSpace (expMap (c • completeBasis K i))) = 1 := by
  rw [expMap_smul, expMap_basis_of_ne, mixedEmbedding.norm_apply]
  simp_rw [normAtPlace_toMixedSpace, Pi.pow_apply, Real.norm_eq_abs,
    Real.abs_rpow_of_nonneg (apply_nonneg _ _), Real.rpow_pow_comm (abs_nonneg _)]
  rw [Real.finset_prod_rpow _ _ fun _ _ ↦ pow_nonneg (abs_nonneg _) _]
  simp_rw [abs_of_nonneg (apply_nonneg _ _), prod_eq_abs_norm, Units.norm,
    Rat.cast_one, Real.one_rpow]

@[simps! source target]
def expMapBasis : PartialHomeomorph (InfinitePlace K → ℝ) (InfinitePlace K → ℝ) :=
  (completeBasis K).equivFunL.symm.toHomeomorph.transPartialHomeomorph expMap

open Classical in
theorem expMapBasis_apply' (x : InfinitePlace K → ℝ) :
    expMapBasis x = Real.exp (x w₀) •
      ∏ w : {w // w ≠ w₀}, expMap (x w • (completeBasis K w.1)) := by
  rw [show expMapBasis x = expMap ((completeBasis K).equivFun.symm x) by rfl,
    Basis.equivFun_symm_apply, expMap_sum, ← Finset.univ.mul_prod_erase _ (mem_univ w₀),
    @prod_subtype _ _ _ _ (Subtype.fintype _) _ (by aesop : ∀ i, i ∈ univ.erase w₀ ↔ i ≠ w₀)]
  simp_rw [expMap_smul, expMap_basis_of_eq, Pi.pow_def, Real.exp_one_rpow, Pi.mul_def,
    Pi.smul_def, smul_eq_mul]

open Classical in
theorem expMapBasis_apply (x : InfinitePlace K → ℝ) :
    expMapBasis x =
      Real.exp (x w₀) •
        (∏ i, fun w : InfinitePlace K ↦ w (fundSystem K (equivFinRank.symm i)) ^ x i) := by
  simp_rw [expMapBasis_apply', expMap_smul, expMap_basis_of_ne]
  rfl

theorem expMapBasis_pos (x : InfinitePlace K → ℝ) (w : InfinitePlace K) :
    0 < expMapBasis x w := Real.exp_pos _

theorem norm_expMapBasis (x : InfinitePlace K → ℝ) :
    mixedEmbedding.norm (toMixedSpace (expMapBasis x)) = Real.exp (x w₀) ^ Module.finrank ℚ K := by
  rw [expMapBasis_apply', map_smul, norm_smul, Real.abs_exp, map_prod, map_prod]
  simp_rw [norm_expMap_smul_basis_of_ne]
  rw [prod_const_one, mul_one]

open Classical in
theorem logMap_expMapBasis (x : InfinitePlace K → ℝ) :
    logMap (toMixedSpace (expMapBasis x)) =
      ∑ w : {w : InfinitePlace K // w ≠ w₀},
        x w • logEmbedding K (Additive.ofMul (fundSystem K (equivFinRank.symm w))) := by
  rw [expMapBasis_apply, map_smul, logMap_real_smul, map_prod, logMap_prod]
  simp_rw [logMap_rpow sorry, logMap_toMixedSpace]
  all_goals sorry

end expMapBasis

section expMapBasisFull

variable [NumberField K]

def expMapBasisFull : PartialHomeomorph (polarSpace K) (mixedSpace K) :=
  (expMapBasis.prod (PartialHomeomorph.refl _)).trans polarCoord.symm

theorem expMapBasisFull_apply (x : polarSpace K) :
    expMapBasisFull x =
      (mixedEmbedding.polarCoord K).symm (fun w ↦ expMapBasis x.1 ↑w,
        fun w ↦ (expMapBasis x.1 ↑w, x.2 w)) := rfl

theorem normAtPlace_expMapBasisFull (x : polarSpace K) (w : InfinitePlace K) :
    normAtPlace w (expMapBasisFull x) = expMapBasis x.1 w := by
  rw [expMapBasisFull_apply]
  obtain hw | hw := isReal_or_isComplex w
  · rw [normAtPlace_polarCoord_symm_of_isReal _ hw, Real.norm_of_nonneg (expMapBasis_pos _ _).le]
  · rw [normAtPlace_polarCoord_symm_of_isComplex _ hw, Real.norm_of_nonneg (expMapBasis_pos _ _).le]

theorem norm_expMapBasisFull (x : polarSpace K) :
    mixedEmbedding.norm (expMapBasisFull x) =
      mixedEmbedding.norm (toMixedSpace (expMapBasis x.1)) := by
  simp_rw [mixedEmbedding.norm_apply, normAtPlace_expMapBasisFull, normAtPlace_toMixedSpace,
    Real.norm_of_nonneg (expMapBasis_pos _ _).le]

end expMapBasisFull

section normLessThanOne

variable [NumberField K]

abbrev normLessThanOne : Set (mixedSpace K) :=
  {x | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ 1}

example :
    expMapBasisFull ⁻¹' {x : mixedSpace K | mixedEmbedding.norm x ≤ 1} = {x | x.1 w₀ ≤ 0} := by
  ext
  rw [Set.preimage_setOf_eq, Set.mem_setOf_eq, Set.mem_setOf_eq, norm_expMapBasisFull,
    norm_expMapBasis, pow_le_one_iff_of_nonneg (Real.exp_nonneg _) Module.finrank_pos.ne',
    Real.exp_le_one_iff]

example :
    expMapBasisFull ⁻¹' (fundamentalCone K) = {x | ∀ w, w ≠ w₀ → x.1 w ∈ Set.Ico 0 1} := by
  classical
  ext x
  have : mixedEmbedding.norm (expMapBasisFull x) ≠ 0 := sorry

  simp_rw [Set.mem_preimage, fundamentalCone, Set.mem_diff, Set.mem_preimage, Set.mem_setOf_eq,
    this, not_false_eq_true, and_true]
  rw [show logMap (expMapBasisFull x) = logMap (toMixedSpace (expMapBasis x.1)) by sorry]
  rw [logMap_expMapBasis]
  rw [← Equiv.sum_comp equivFinRank]
  simp_rw [Equiv.symm_apply_apply]
  simp_rw [ZSpan.mem_fundamentalDomain, logEmbedding_fundSystem]
  simp_rw [map_sum, map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul, sum_apply,
    Pi.smul_apply, Basis.ofZLatticeBasis_repr_apply, Basis.repr_self, smul_eq_mul]
  simp_rw [Finsupp.single_apply, Int.cast_ite, Int.cast_one, Int.cast_zero, mul_ite, mul_one,
    mul_zero,
    Fintype.sum_ite_eq']
  rw [Equiv.forall_congr_left equivFinRank]
  simp_rw [Equiv.apply_symm_apply, Subtype.forall]

end normLessThanOne

end

end NumberField.mixedEmbedding.NormLessThanOne
