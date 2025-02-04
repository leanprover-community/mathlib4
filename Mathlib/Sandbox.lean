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

section misc

variable (G : Type*) [LinearOrderedAddCommGroup G]

@[simps]
def PartialEquiv.abs : PartialEquiv G G where
  toFun := fun x ↦ |x|
  invFun := fun x ↦ x
  source := {x | 0 < x}
  target := {x | 0 < x}
  map_source' := fun _ hx ↦ abs_pos.mpr hx.ne'
  map_target' := fun _ hx ↦ hx
  left_inv' := fun _ hx ↦ abs_of_pos hx
  right_inv' := fun _ hx ↦ abs_of_pos hx

variable [TopologicalSpace G] [OrderTopology G]

@[simps!]
def PartialHomeomorph.abs : PartialHomeomorph G G :=
{ PartialEquiv.abs G with
  open_source := isOpen_lt' 0
  open_target := isOpen_lt' 0
  continuousOn_toFun := continuous_abs.continuousOn
  continuousOn_invFun := continuous_id.continuousOn }

open Classical in
@[to_additive]
theorem Fintype.prod_eq_mul_prod_fintype_ne {α M : Type*} [Fintype α] [CommMonoid M] (f : α → M)
    (a : α) : ∏ i, f i = f a * ∏ i : {i // i ≠ a}, f i.1 := by
  simp_rw [← Equiv.prod_comp (Equiv.optionSubtypeNe a), Fintype.prod_option,
    Equiv.optionSubtypeNe_none,  Equiv.optionSubtypeNe_some]

end misc

variable {K : Type*} [Field K]

namespace NumberField.mixedEmbedding.NormLessThanOne

open Finset NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem
  MeasureTheory

noncomputable section


section normMap

abbrev normMap (x : mixedSpace K) : (InfinitePlace K → ℝ) := fun w ↦ normAtPlace w x

theorem normMap_mixedEmbedding (x : K) :
    normMap (mixedEmbedding K x) = fun w ↦ w x := by
  ext
  rw [normMap, normAtPlace_apply]

theorem norm_eq_prod_normMap [NumberField K] (x : mixedSpace K) :
    mixedEmbedding.norm x = ∏ w, (normMap x w) ^ w.mult := by
  simp_rw [mixedEmbedding.norm_apply]

end normMap

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
  simp_rw [expMap_apply', prod_fn, ← Real.exp_sum, ← Finset.mul_sum, Finset.sum_apply]

theorem expMap_smul (c : ℝ) (x : InfinitePlace K → ℝ) :
    expMap (c • x) = (expMap x) ^ c := by
  simp_rw [expMap_apply', Pi.smul_apply, smul_eq_mul, mul_comm c _, ← mul_assoc, Real.exp_mul,
    Pi.pow_def]

-- That's an awful name
def restMap : (InfinitePlace K → ℝ) →ₗ[ℝ] ({w : InfinitePlace K // w ≠ w₀} → ℝ) where
  toFun := fun x w ↦ x w.1 - w.1.mult * (∑ w', x w') * (Module.finrank ℚ K : ℝ)⁻¹
  map_add' := fun _ _ ↦ funext fun _ ↦ by simpa [Finset.sum_add_distrib] using by ring
  map_smul' := fun _ _ ↦ funext fun _ ↦ by simpa [← Finset.mul_sum] using by ring

-- def restMap : PartialEquiv (InfinitePlace K → ℝ) ({w : InfinitePlace K // w ≠ w₀} → ℝ) where
--   toFun := fun x w ↦ x w.1 - w.1.mult * (∑ w', x w') * (Module.finrank ℚ K : ℝ)⁻¹
--   invFun := sorry
--   source := sorry
--   target := sorry
--   map_source' := sorry
--   map_target' := sorry
--   left_inv' := sorry
--   right_inv' := sorry

theorem restMap_apply (x : InfinitePlace K → ℝ) (w : {w : InfinitePlace K // w ≠ w₀}) :
    restMap x w = x w - w.1.mult * (∑ w', x w') * (Module.finrank ℚ K : ℝ)⁻¹ := rfl

-- def logMap₀ (x : InfinitePlace K → ℝ) := restMap (expMap.symm x)

theorem restMap_expMap_symm_apply (x : InfinitePlace K → ℝ) (w : {w : InfinitePlace K // w ≠ w₀})  :
    restMap (expMap.symm x) w = w.1.mult * (Real.log (x w) -
      (∑ w', w'.mult * Real.log (x w')) * (Module.finrank ℚ K : ℝ)⁻¹) := by
  simp_rw [restMap_apply, expMap_symm_apply, mul_sub]
  rw [← mul_assoc, Finset.mul_sum]

theorem restMap_expMap_symm_normMap {x : mixedSpace K} (hx : mixedEmbedding.norm x ≠ 0) :
    restMap (expMap.symm (normMap x)) = logMap x := by
  have h {w} : (normAtPlace w x) ^ w.mult ≠ 0 :=
    pow_ne_zero _ (mixedEmbedding.norm_ne_zero_iff.mp hx w)
  ext w
  simp_rw [restMap_expMap_symm_apply, normMap, logMap_apply, mixedEmbedding.norm_apply,
    Real.log_prod _ _ fun _ _ ↦ h,  Real.log_pow]

theorem restMap_expMap_symm_place_eval (x : K) (hx : x ≠ 0) :
    restMap (expMap.symm  (fun w ↦ w x)) = logMap (mixedEmbedding K x) := by
  rw [← normMap_mixedEmbedding, restMap_expMap_symm_normMap (by simp [norm_eq_norm, hx])]

-- variable [NumberField K]

open Classical in
/-- DOCSTRING -/
def equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w ≠ w₀} :=
  Fintype.equivOfCardEq <| by
    rw [Fintype.card_subtype_compl, Fintype.card_ofSubsingleton, Fintype.card_fin, rank]

open Classical in
variable (K) in
def completeBasis₀ : InfinitePlace K → InfinitePlace K → ℝ := by
  intro i
  by_cases hi : i = w₀
  · exact fun w ↦ mult w
  · exact expMap.symm (fun w ↦ w (fundSystem K (equivFinRank.symm ⟨i, hi⟩)))

theorem restMap_completeBasis₀_of_eq :
    restMap (completeBasis₀ K w₀) = 0 := by
  ext
  rw [completeBasis₀, dif_pos rfl, restMap_apply, ← Nat.cast_sum, sum_mult_eq, mul_inv_cancel_right₀
    (Nat.cast_ne_zero.mpr Module.finrank_pos.ne'), sub_self, Pi.zero_apply]

theorem restMap_completeBasis₀_of_ne (i : {w : InfinitePlace K // w ≠ w₀}) :
    restMap (completeBasis₀ K i) =
      (logEmbedding K) (Additive.ofMul (fundSystem K (equivFinRank.symm i))) := by
  rw [← logMap_eq_logEmbedding, ← restMap_expMap_symm_place_eval, completeBasis₀, dif_neg]
  exact coe_ne_zero _

variable (K) in
theorem linearIndependent_completeBasis₀ :
    LinearIndependent ℝ (completeBasis₀ K) := by
  classical
  have : LinearIndependent ℝ (fun w : {w // w ≠ w₀} ↦ completeBasis₀ K w.1) := by
    refine LinearIndependent.of_comp restMap ?_
    simp_rw [Function.comp_def, restMap_completeBasis₀_of_ne, logEmbedding_fundSystem]
    have := (((basisUnitLattice K).ofZLatticeBasis ℝ _).reindex equivFinRank).linearIndependent
    convert this
    simp only [ne_eq, Basis.coe_reindex, Function.comp_apply, Basis.ofZLatticeBasis_apply]
  -- Use linearIndependent_option and Equiv.optionSubtypeNe
  sorry

variable (K) in
def completeBasis : Basis (InfinitePlace K) ℝ (InfinitePlace K → ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_completeBasis₀ K)
    (Module.finrank_fintype_fun_eq_card _).symm

theorem completeBasis_apply_of_eq :
    completeBasis K w₀ = fun w ↦ (mult w : ℝ) := by
  rw [completeBasis, coe_basisOfLinearIndependentOfCardEqFinrank, completeBasis₀, dif_pos rfl]

theorem completeBasis_apply_of_ne (i : {w : InfinitePlace K // w ≠ w₀}) :
    completeBasis K i =
      expMap.symm (fun w : InfinitePlace K ↦ w (fundSystem K (equivFinRank.symm i))) := by
  rw [completeBasis, coe_basisOfLinearIndependentOfCardEqFinrank, completeBasis₀, dif_neg]

theorem restMap_completeBasis_of_eq :
    restMap (completeBasis K w₀) = 0 := by
  rw [completeBasis, coe_basisOfLinearIndependentOfCardEqFinrank, restMap_completeBasis₀_of_eq]

theorem restMap_completeBasis_of_ne (i : {w : InfinitePlace K // w ≠ w₀}) :
    restMap (completeBasis K i) =
      (logEmbedding K) (Additive.ofMul (fundSystem K (equivFinRank.symm i))) := by
  rw [completeBasis, coe_basisOfLinearIndependentOfCardEqFinrank, restMap_completeBasis₀_of_ne]

open Classical in
theorem restMap_sum_smul_completeBasis (x : InfinitePlace K → ℝ) :
    restMap (∑ w, x w • completeBasis K w) =
      ∑ i, x (equivFinRank i) • ((basisUnitLattice K).ofZLatticeBasis ℝ _ i) := by
  simp_rw [map_sum, _root_.map_smul, Fintype.sum_eq_add_sum_fintype_ne _ w₀,
    restMap_completeBasis_of_eq, smul_zero, zero_add, restMap_completeBasis_of_ne,
    logEmbedding_fundSystem, ← (basisUnitLattice K).ofZLatticeBasis_apply ℝ,
    ← equivFinRank.sum_comp, Equiv.symm_apply_apply]

open Classical in
theorem completeBasis_repr_eq_unitLatticeBasis_repr (x : InfinitePlace K → ℝ)
    (w : {w // w ≠ w₀}) :
    (completeBasis K).repr x w.1 =
      ((basisUnitLattice K).ofZLatticeBasis ℝ _).repr (restMap x) (equivFinRank.symm w) := by
  have := restMap.congr_arg ((completeBasis K).sum_repr x)
  rw [restMap_sum_smul_completeBasis] at this
  rw [← this]
  simp [Finsupp.single_apply]

theorem expMap_basis_of_eq :
    expMap (completeBasis K w₀) = fun _ ↦ Real.exp 1 := by
  simp_rw [expMap_apply', completeBasis_apply_of_eq, inv_mul_cancel₀ mult_coe_ne_zero]

theorem expMap_basis_of_ne (i : {w : InfinitePlace K // w ≠ w₀}) :
    expMap (completeBasis K i) = fun w ↦ w (fundSystem K (equivFinRank.symm i) : 𝓞 K) := by
  rw [completeBasis_apply_of_ne, PartialHomeomorph.right_inv _ (by simp)]

def expMapBasis : PartialHomeomorph (InfinitePlace K → ℝ) (InfinitePlace K → ℝ) :=
  (completeBasis K).equivFunL.symm.toHomeomorph.transPartialHomeomorph expMap

theorem expMapBasis_apply (x : InfinitePlace K → ℝ) :
    expMapBasis x = expMap ((completeBasis K).equivFun.symm x) := rfl

theorem expMapBasis_source :
    expMapBasis.source = (Set.univ :  Set (InfinitePlace K → ℝ)) := rfl

theorem expMapBasis_target :
    expMapBasis.target =  {x : InfinitePlace K → ℝ | ∀ w, 0 < x w} := rfl

theorem expMapBasis_pos (x : InfinitePlace K → ℝ) (w : InfinitePlace K) :
    0 < expMapBasis x w := expMap_pos _ _

theorem prod_expMapBasis_pow (x : InfinitePlace K → ℝ) :
    ∏ w, (expMapBasis x w) ^ w.mult = Real.exp (x w₀) ^ Module.finrank ℚ K := by
  classical
  simp_rw [expMapBasis_apply]
  simp only [Basis.equivFun_symm_apply, sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [expMap_sum]
  simp_rw [Finset.prod_apply]
  simp_rw [← Finset.prod_pow]
  rw [Finset.prod_comm]
  rw [Fintype.prod_eq_mul_prod_fintype_ne _ w₀]
  simp_rw [expMap_smul]
  simp_rw [expMap_basis_of_eq]
  simp_rw [expMap_basis_of_ne]
  simp only [Pi.pow_apply, Real.exp_one_rpow, prod_const, card_univ]
  simp_rw [Real.rpow_pow_comm (apply_nonneg _ _)]
  simp_rw [Real.finset_prod_rpow _ _ sorry]
  simp_rw [prod_eq_abs_norm]
  simp_rw [Units.norm]
  simp_rw [Rat.cast_one, Real.one_rpow]
  simp_rw [prod_const_one, mul_one]
  simp_rw [← Real.exp_nat_mul]
  rw [← Real.exp_sum]
  rw [← Finset.sum_mul]
  rw [← Nat.cast_sum]
  rw [sum_mult_eq]

theorem norm_expMapBasis {x : mixedSpace K} (hx : mixedEmbedding.norm x ≠ 0) :
    expMapBasis.symm (normMap x) w₀ =
      (Module.finrank ℚ K : ℝ)⁻¹ * Real.log (mixedEmbedding.norm x) := by
  rw [norm_eq_prod_normMap, ← expMapBasis.right_inv (x := normMap x), prod_expMapBasis_pow,
    expMapBasis.left_inv, Real.log_pow, Real.log_exp, inv_mul_cancel_left₀]
  · rw [Nat.cast_ne_zero]
    exact Module.finrank_pos.ne'
  · rw [expMapBasis_source]
    trivial
  · rw [expMapBasis_target]
    intro w
    rw [normMap]
    rw [mixedEmbedding.norm_ne_zero_iff] at hx
    specialize hx w
    refine lt_of_le_of_ne' (normAtPlace_nonneg w x) hx

open Classical in
theorem logMap₀_expMapBasis (x : InfinitePlace K → ℝ) :
    restMap (expMap.symm (expMapBasis x)) =
      ((basisUnitLattice K).ofZLatticeBasis ℝ _).equivFun.symm (fun i ↦ x (equivFinRank i)) := by
  rw [expMapBasis_apply, expMap.left_inv trivial, Basis.equivFun_symm_apply,
    restMap_sum_smul_completeBasis, Basis.equivFun_symm_apply]

  -- Use previous result
  -- simp_rw [logMap₀, expMapBasis_apply, expMap.left_inv trivial, Basis.equivFun_symm_apply,
  --   map_sum, _root_.map_smul, Fintype.sum_eq_add_sum_fintype_ne _ w₀]
  --  ← Finset.univ.add_sum_erase _ (mem_univ w₀),
  --   restMap_completeBasis_of_eq, smul_zero, zero_add]
  -- rw [@sum_subtype _ _ _ _ (Subtype.fintype _) _ (by aesop : ∀ i, i ∈ univ.erase w₀ ↔ i ≠ w₀)]
  -- simp_rw [restMap_completeBasis_of_ne, Basis.ofZLatticeBasis_apply]
  -- simp_rw [← equivFinRank.sum_comp, logEmbedding_fundSystem, Equiv.symm_apply_apply]

-- open Classical in
-- theorem expMapBasis_apply' (x : InfinitePlace K → ℝ) :
--     expMapBasis x = Real.exp (x w₀) •
--       ∏ w : {w // w ≠ w₀}, expMap (x w • (completeBasis K w.1)) := by
--   rw [show expMapBasis x = expMap ((completeBasis K).equivFun.symm x) by rfl,
--     Basis.equivFun_symm_apply, expMap_sum, ← Finset.univ.mul_prod_erase _ (mem_univ w₀),
--     @prod_subtype _ _ _ _ (Subtype.fintype _) _ (by aesop : ∀ i, i ∈ univ.erase w₀ ↔ i ≠ w₀)]
--   simp_rw [expMap_smul, expMap_basis_of_eq, Pi.pow_def, Real.exp_one_rpow, Pi.mul_def,
--     Pi.smul_def, smul_eq_mul]

-- open Classical in
-- theorem expMapBasis_apply (x : InfinitePlace K → ℝ) :
--     expMapBasis x =
--       Real.exp (x w₀) •
--         (∏ i, fun w : InfinitePlace K ↦ w (fundSystem K (equivFinRank.symm i)) ^ x i) := by
--   simp_rw [expMapBasis_apply', expMap_smul, expMap_basis_of_ne]
--   rfl

-- theorem trick (x : InfinitePlace K → ℝ) :
--    x = normMap (fun w ↦ x w.1, fun w ↦ x w.1) := sorry



variable (K) in
abbrev polarSpace := (InfinitePlace K → ℝ) × ({w : InfinitePlace K // w.IsComplex} → ℝ)

open Classical MeasurableEquiv in
def measurableEquivRealMixedSpacePolarSpace : realMixedSpace K ≃ᵐ polarSpace K :=
  MeasurableEquiv.trans (prodCongr (refl _)
    (arrowProdEquivProdArrow ℝ ℝ _)) <|
    MeasurableEquiv.trans prodAssoc.symm <|
      MeasurableEquiv.trans
        (prodCongr (prodCongr (refl _)
          (arrowCongr' (Equiv.subtypeEquivRight (fun _ ↦ not_isReal_iff_isComplex.symm)) (refl _)))
            (refl _))
          (prodCongr (piEquivPiSubtypeProd (fun _ ↦ ℝ) _).symm (refl _))

open Classical in
def homeoRealMixedSpacePolarSpace : realMixedSpace K ≃ₜ polarSpace K :=
{ measurableEquivRealMixedSpacePolarSpace with
  continuous_toFun := by
    change Continuous fun x : realMixedSpace K ↦  (fun w ↦ if hw : w.IsReal then x.1 ⟨w, hw⟩ else
      (x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩).1, fun w ↦ (x.2 w).2)
    refine continuous_prod_mk.mpr ⟨continuous_pi_iff.mpr fun w ↦ ?_, by fun_prop⟩
    split_ifs <;> fun_prop
  continuous_invFun := by
    change Continuous fun x : polarSpace K ↦
      (⟨fun w ↦ x.1 w.val, fun w ↦ ⟨x.1 w.val, x.2 w⟩⟩ : realMixedSpace K)
    fun_prop }

omit [NumberField K] in
@[simp]
theorem homeoRealMixedSpacePolarSpace_symm_apply (x : polarSpace K) :
    homeoRealMixedSpacePolarSpace.symm x = ⟨fun w ↦ x.1 w, fun w ↦ (x.1 w, x.2 w)⟩ := rfl

open Classical in
omit [NumberField K] in
theorem homeoRealMixedSpacePolarSpace_apply (x : realMixedSpace K) :
    homeoRealMixedSpacePolarSpace x =
      ⟨fun w ↦ if hw : w.IsReal then x.1 ⟨w, hw⟩ else
        (x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩).1, fun w ↦ (x.2 w).2⟩ := rfl

open Classical in
theorem volume_preserving_homeoRealMixedSpacePolarSpace :
    MeasurePreserving (homeoRealMixedSpacePolarSpace (K := K)) :=
  ((MeasurePreserving.id volume).prod
    (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ _)).trans <|
      (volume_preserving_prodAssoc.symm).trans <|
        (((MeasurePreserving.id volume).prod (volume_preserving_arrowCongr' _
          (MeasurableEquiv.refl ℝ) (.id volume))).prod (.id volume)).trans <|
            ((volume_preserving_piEquivPiSubtypeProd
              (fun _ : InfinitePlace K ↦ ℝ) (fun w ↦ IsReal w)).symm).prod (.id volume)

@[simps!]
def expMapBasisFull₀ : PartialHomeomorph (mixedSpace K) (mixedSpace K) :=
  (PartialHomeomorph.pi fun _ ↦ .abs ℝ).prod (.refl _)

@[simps!]
def expMapBasisFull₁ : PartialHomeomorph (polarSpace K) (polarSpace K) :=
  expMapBasis.symm.prod (PartialHomeomorph.refl _)

@[simps!]
def polarCoord₀ : PartialHomeomorph (mixedSpace K) (polarSpace K) :=
    (mixedEmbedding.polarCoord K).transHomeomorph homeoRealMixedSpacePolarSpace

def expMapBasisFull : PartialHomeomorph (mixedSpace K) (polarSpace K) :=
  expMapBasisFull₀.trans <| polarCoord₀.trans expMapBasisFull₁

theorem expMapBasisFull_source :
    expMapBasisFull.source =
      {x : mixedSpace K | (∀ w, 0 < x.1 w) ∧ (∀ w, x.2 w ∈ Complex.polarCoord.source)} := by
  simp [expMapBasisFull]
  sorry
  -- unfold expMapBasisFull
  -- rw [PartialHomeomorph.trans_source]
  -- rw [Homeomorph.transPartialHomeomorph_source]
  -- rw [PartialHomeomorph.prod_source]
  -- rw [PartialHomeomorph.refl_source]
  -- have : (mixedEmbedding.polarCoord K).IsImage {x | ∀ w, 0 < x.1 w}
  --     (homeoRealMixedSpacePolarSpace ⁻¹' expMapBasis.symm.source ×ˢ Set.univ) := by
  --   intro x hx
  --   have {w : {w // IsComplex w}} : 0 < ((mixedEmbedding.polarCoord K x).2 w).1 := by
  --     suffices ((mixedEmbedding.polarCoord K x).2 w) ∈ polarCoord.target by
  --       exact this.1
  --     refine PartialHomeomorph.map_source _ ?_
  --     exact hx.2 w (Set.mem_univ _)
  --   simp_rw [Set.mem_preimage, homeoRealMixedSpacePolarSpace_apply, Set.mem_prod, Set.mem_univ,
  --     and_true, PartialHomeomorph.symm_source, expMapBasis_target, Set.mem_setOf_eq]
  --   simp_rw [apply_dite]
  --   simp_rw [this]
  --   simp only [dite_else_true, Subtype.forall]
  --   simp [mixedEmbedding.polarCoord_apply]
  -- rw [this.preimage_eq]
  -- rw [mixedEmbedding.polarCoord_source]
  -- ext
  -- simp [and_comm]

theorem expMapBasisFull_target :
    expMapBasisFull.target = (Set.univ : Set (polarSpace K)) := by
  sorry

open Classical in
theorem expMapBasisFull_apply (x : mixedSpace K) :
    expMapBasisFull x =
      ⟨expMapBasis.symm fun w ↦  normAtPlace w x, fun w ↦ (Complex.polarCoord (x.2 w)).2⟩ := by
  unfold expMapBasisFull
  ext w
  · simp_rw [PartialHomeomorph.coe_trans, Function.comp_apply, expMapBasisFull₀_apply,
      polarCoord₀_apply, Pi.map_apply, PartialHomeomorph.abs_apply, expMapBasisFull₁_apply]
    congr!
    split_ifs with h
    · rw [normAtPlace_apply_isReal h, Real.norm_eq_abs]
    · rw [normAtPlace_apply_isComplex (not_isReal_iff_isComplex.mp h), Complex.polarCoord_apply,
        Complex.norm_eq_abs]
  · simp [homeoRealMixedSpacePolarSpace_apply]

theorem expMapBasisFull_symm_apply (x : polarSpace K) :
    expMapBasisFull.symm x = ⟨fun w ↦ expMapBasis x.1 w,
      fun w ↦ Complex.polarCoord.symm (expMapBasis x.1 w, x.2 w)⟩ := rfl

theorem expMapBasisFull_apply' (x : mixedSpace K) :
    expMapBasisFull x = (expMapBasisFull₁ ∘ homeoRealMixedSpacePolarSpace ∘
      (mixedEmbedding.polarCoord K)) (expMapBasisFull₀ x) := rfl

theorem normMap_expMapBasisFull_symm (x : polarSpace K) :
    normMap (expMapBasisFull.symm x) = expMapBasis x.1 := by
  ext w
  rw [normMap, expMapBasisFull_symm_apply]
  obtain hw | hw := isReal_or_isComplex w
  · rw [normAtPlace_apply_isReal hw, Real.norm_of_nonneg (expMapBasis_pos _ _).le]
  · rw [normAtPlace_apply_isComplex hw, Complex.norm_eq_abs, Complex.abs_polarCoord_symm,
      abs_of_pos (expMapBasis_pos _ _)]

theorem expMapBasisFull_fst {x : mixedSpace K} :
    (expMapBasisFull x).1 = expMapBasis.symm (normMap x) := by
  rw [expMapBasisFull_apply]

theorem part1 :
    {x : mixedSpace K | mixedEmbedding.norm x ∈ Set.Ioc 0 1} =
      {x | mixedEmbedding.norm x ≠ 0} ∩ expMapBasisFull⁻¹' {x | x w₀ ≤ 0} ×ˢ Set.univ := by
  ext x
  by_cases hx : mixedEmbedding.norm x = 0
  · simp [hx]
  · replace hx : 0 < mixedEmbedding.norm x := lt_of_le_of_ne' (mixedEmbedding.norm_nonneg x) hx
    have h : 0 < (Module.finrank ℚ K : ℝ)⁻¹ := by
      rw [inv_pos]
      rw [Nat.cast_pos]
      exact Module.finrank_pos
    simp_rw [Set.mem_Ioc, Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true,
      expMapBasisFull_fst, Set.mem_setOf_eq, hx, ne_eq, hx.ne', not_false_eq_true,
      norm_expMapBasis hx.ne', ← Real.log_nonpos_iff (mixedEmbedding.norm_nonneg x), mul_nonpos_iff,
      h.le, lt_iff_not_le.mp h, true_and, false_and, or_false]

theorem part2 :
    fundamentalCone K =
      {x | mixedEmbedding.norm x ≠ 0} ∩
        expMapBasisFull⁻¹' {x | ∀ w : {w // w ≠ w₀}, x w.1 ∈ Set.Ico 0 1} ×ˢ Set.univ := by
  ext x
  simp only [fundamentalCone, Set.mem_diff, Set.mem_preimage, ZSpan.mem_fundamentalDomain,
    Set.mem_setOf_eq, and_comm, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ,
    true_and, and_congr_right_iff, expMapBasisFull_fst]
  intro hx
  simp_rw [Equiv.forall_congr_left equivFinRank]
  have t1 := completeBasis_repr_eq_unitLatticeBasis_repr (expMap.symm (normMap x))
  have t2 := restMap_expMap_symm_normMap hx
  rw [← t2]
  simp_rw [← t1]
  rfl

variable (K) in
abbrev normLessThanOne : Set (mixedSpace K) :=
  {x | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ 1}

open Classical in
variable (K) in
def paramSet : Set (polarSpace K) :=
  (Set.univ.pi fun w ↦ if w = w₀ then Set.Iic 0 else Set.Ico 0 1) ×ˢ Set.univ

theorem normLessThanOne_eq :
    normLessThanOne K = expMapBasisFull⁻¹' (paramSet K) := by
  sorry

section integrals

open Real ENNReal Classical

theorem setLIntegral_expMapBasis {s : Set (InfinitePlace K → ℝ)} (hs₀ : MeasurableSet s)
    (hs₁ : s ⊆ {x | 0 ≤ x w₀}) (f : (InfinitePlace K → ℝ) → ℝ≥0∞) :
    ∫⁻ x in expMapBasis '' s, f x =
      (2 : ℝ≥0∞)⁻¹ ^ nrComplexPlaces K * ENNReal.ofReal (regulator K) * (Module.finrank ℚ K) *
      ∫⁻ x in s, ENNReal.ofReal |x w₀| ^ rank K *
        .ofReal (∏ i : {w : InfinitePlace K // IsComplex w},
          (expMapBasis (fun w ↦ x w) i))⁻¹ * f (expMapBasis x) := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume]
  all_goals sorry

theorem lintegral_eq_lintegral_polarCoord₀_symm (f : mixedSpace K → ℝ≥0∞) :
    ∫⁻ x, f x = ∫⁻ x in polarCoord₀.target, (∏ w : {w // IsComplex w}, .ofReal (x.1 w.val)) *
      f (polarCoord₀.symm x) := by
  rw [← mixedEmbedding.lintegral_comp_polarCoord_symm,
    ← volume_preserving_homeoRealMixedSpacePolarSpace.setLIntegral_comp_preimage_emb
    measurableEquivRealMixedSpacePolarSpace.measurableEmbedding]
  rw [show (mixedEmbedding.polarCoord K).target =
    homeoRealMixedSpacePolarSpace ⁻¹' polarCoord₀.target by ext; simp]
  congr! with _ _ w
  · simp_rw [homeoRealMixedSpacePolarSpace_apply, dif_neg (not_isReal_iff_isComplex.mpr w.prop)]
  · rw [polarCoord₀, PartialHomeomorph.transHomeomorph_symm_apply, Function.comp_apply,
        Homeomorph.symm_apply_apply]

open Classical in
theorem volume_expMapBasisFull_preimage_set_prod_set {s : Set (InfinitePlace K → ℝ)}
    {t : Set ({w : InfinitePlace K // IsComplex w} → ℝ)} :
    volume (expMapBasisFull⁻¹' (s ×ˢ t)) =
      volume ((Set.univ.pi fun _ ↦ Set.Ioo (-π) π) ∩ t) * ∫⁻ x in expMapBasis⁻¹' s,
        ∏ w : {w : InfinitePlace K // IsComplex w}, (x w).toNNReal := by
  rw [← setLIntegral_one]
  sorry

open Classical in
theorem volume_plusPart_normLessThanOne : volume (plusPart (normLessThanOne K)) =
    NNReal.pi ^ nrComplexPlaces K * (regulator K).toNNReal := by
  sorry

end integrals














#exit
  have := logMap₀_expMapBasis
  sorry


#exit




  unfold expMapBasisFull
  simp_rw [PartialHomeomorph.coe_trans_symm, Homeomorph.transPartialHomeomorph_symm_apply,
    PartialHomeomorph.prod_symm, PartialHomeomorph.refl_symm, PartialHomeomorph.prod_apply,
    PartialHomeomorph.refl_apply, id_eq, Function.comp_apply]
  simp_rw [mixedEmbedding.polarCoord_symm_apply, homeoRealMixedSpacePolarSpace_symm_apply]


  simp only [PartialHomeomorph.coe_trans_symm, Homeomorph.transPartialHomeomorph_symm_apply,
    PartialHomeomorph.prod_symm, PartialHomeomorph.refl_symm, PartialHomeomorph.prod_apply,
    PartialHomeomorph.refl_apply, id_eq, Function.comp_apply]

theorem expMapBasisFull_apply (x : mixedSpace K) :
    expMapBasisFull x = 0 := by
  unfold expMapBasisFull

  simp_rw [PartialHomeomorph.coe_trans, Homeomorph.transPartialHomeomorph_apply,
    PartialHomeomorph.prod_apply, PartialHomeomorph.refl_apply,
    Function.comp_apply]
  dsimp
  simp_rw [homeoRealMixedSpacePolarSpace_apply]







theorem expMapBasisFull_symm_apply (x : polarSpace K) :
    expMapBasisFull.symm x = (expMapBasis.symm x.1, x.2) := rfl

theorem expMapBasisFull_source :
    expMapBasisFull.source = (Set.univ : Set (polarSpace K)) := by
  simp [expMapBasisFull, expMapBasis_source]

theorem expMapBasisFull_target:
    expMapBasisFull.target = ({x | ∀ w, 0 < x w} ×ˢ Set.univ : Set (polarSpace K)) := by
  simp [expMapBasisFull, expMapBasis_target]









#exit


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
