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

In this file, we study the subset `NormLenOne` of the `fundamentalCone` defined as the
subset of elements `x` such that `mixedEmbedding.norm x ≤ 1`.

Mainly, we want to prove that its frontier has volume zero and compute its volume. For this, we
follow mainly the strategy given in [D. Marcus, *Number Fields*][marcus1977number].

## Strategy of proof

-/

section misc

open Set

theorem ContinuousLinearMap.coe_proj {R : Type*} [Semiring R] {ι : Type*} {φ : ι → Type*}
  [(i : ι) → TopologicalSpace (φ i)] [(i : ι) → AddCommMonoid (φ i)] [(i : ι) → Module R (φ i)]
  (i : ι) :
  (ContinuousLinearMap.proj i).toLinearMap = (LinearMap.proj i : ((i : ι) → φ i) →ₗ[R] _) := rfl

theorem MeasureTheory.integral_comp_mul_left_Iio {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : ℝ → E) (a : ℝ) {b : ℝ} (hb : 0 < b) :
    ∫ (x : ℝ) in Set.Iio a, g (b * x) = b⁻¹ • ∫ (x : ℝ) in Set.Iio (b * a), g x := by
  have : ∀ c : ℝ, MeasurableSet (Iio c) := fun c => measurableSet_Iio
  rw [← integral_indicator (this a), ← integral_indicator (this (b * a)),
    ← abs_of_pos (inv_pos.mpr hb), ← Measure.integral_comp_mul_left]
  congr
  ext1 x
  rw [← indicator_comp_right, preimage_const_mul_Iio _ hb, mul_div_cancel_left₀ _ hb.ne']
  rfl

theorem MeasureTheory.integral_comp_mul_right_Iio {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : ℝ → E) (a : ℝ) {b : ℝ} (hb : 0 < b) :
    ∫ (x : ℝ) in Set.Iio a, g (x * b) = b⁻¹ • ∫ (x : ℝ) in Set.Iio (a * b), g x := by
  simpa only [mul_comm] using integral_comp_mul_left_Iio g a hb

theorem MeasureTheory.integrableOn_Iio_comp_mul_left_iff {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E)  (c : ℝ)  {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun (x : ℝ) => f (a * x)) (Set.Iio c) ↔ IntegrableOn f (Set.Iio (a * c)) := by
  rw [← integrable_indicator_iff (measurableSet_Iio : MeasurableSet <| Iio c)]
  rw [← integrable_indicator_iff (measurableSet_Iio : MeasurableSet <| Iio <| a * c)]
  convert integrable_comp_mul_left_iff ((Iio (a * c)).indicator f) ha.ne' using 2
  ext1 x
  rw [← indicator_comp_right, preimage_const_mul_Iio _ ha, mul_comm a c,
    mul_div_cancel_right₀ _ ha.ne']
  rfl

theorem MeasureTheory.integrableOn_Iio_comp_mul_right_iff {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) (c : ℝ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x => f (x * a)) (Iio c) ↔ IntegrableOn f (Iio <| c * a) := by
  simpa only [mul_comm, mul_zero] using integrableOn_Iio_comp_mul_left_iff f c ha

theorem hasDerivAt_const_mul {𝕜 : Type*} [NontriviallyNormedField 𝕜] {x : 𝕜} (c : 𝕜) :
    HasDerivAt (fun (x : 𝕜) => c * x) c x := by
  simpa only [mul_comm] using hasDerivAt_mul_const c

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


section normAtAllPlaces

-- abbrev normMap (x : mixedSpace K) : (InfinitePlace K → ℝ) := fun w ↦ normAtPlace w x

theorem normAtAllPlaces_mixedEmbedding (x : K) :
    normAtAllPlaces (mixedEmbedding K x) = fun w ↦ w x := by
  ext
  rw [normAtAllPlaces_apply, normAtPlace_apply]

theorem norm_eq_prod_normAtAllPlaces [NumberField K] (x : mixedSpace K) :
    mixedEmbedding.norm x = ∏ w, (normAtAllPlaces x w) ^ w.mult := by
  simp_rw [mixedEmbedding.norm_apply]

theorem normAtPlace_mixedSpaceOfRealSpace {x : realSpace K} {w : InfinitePlace K} (hx : 0 ≤ x w) :
    normAtPlace w (mixedSpaceOfRealSpace x) = x w := by
  simp only [mixedSpaceOfRealSpace_apply]
  obtain hw | hw := isReal_or_isComplex w
  · rw [normAtPlace_apply_of_isReal hw, Real.norm_of_nonneg hx]
  · rw [normAtPlace_apply_of_isComplex hw, Complex.norm_eq_abs, Complex.abs_of_nonneg hx]

theorem logMap_normAtAllPlaces [NumberField K] (x : mixedSpace K) :
    logMap (mixedSpaceOfRealSpace (normAtAllPlaces x)) = logMap x :=
  logMap_eq_of_normAtPlace_eq
    fun w ↦ by rw [normAtPlace_mixedSpaceOfRealSpace (normAtPlace_nonneg w x)]

theorem norm_normAtAllPlaces [NumberField K] (x : mixedSpace K) :
    mixedEmbedding.norm (mixedSpaceOfRealSpace (normAtAllPlaces x)) = mixedEmbedding.norm x := by
  simp_rw [mixedEmbedding.norm_apply,
    normAtPlace_mixedSpaceOfRealSpace (normAtAllPlaces_nonneg _ _)]

theorem normAtAllPlaces_mem_fundamentalCone_iff [NumberField K] {x : mixedSpace K} :
    mixedSpaceOfRealSpace (normAtAllPlaces x) ∈ fundamentalCone K ↔ x ∈ fundamentalCone K := by
  simp_rw [fundamentalCone, Set.mem_diff, Set.mem_preimage, logMap_normAtAllPlaces,
    Set.mem_setOf_eq, norm_normAtAllPlaces]

end normAtAllPlaces

section expMap

-- variable [NumberField K]

-- @[simps?]
-- def expMap' : PartialHomeomorph (realSpace K) (realSpace K) where
--   toFun := fun x w ↦ Real.exp ((w.mult : ℝ)⁻¹ * x w)
--   invFun := fun x w ↦ w.mult * Real.log (x w)
--   source := Set.univ
--   target := {x | ∀ w, 0 < x w}
--   open_source := isOpen_univ
--   open_target := by
--     simp_rw [Set.setOf_forall]
--     exact isOpen_iInter_of_finite fun _ ↦ isOpen_lt continuous_const <| continuous_apply _
--   continuousOn_toFun := continuousOn_pi'
--     fun i ↦ (ContinuousOn.mul continuousOn_const (continuousOn_apply i Set.univ)).rexp
--   continuousOn_invFun := continuousOn_const.mul <| continuousOn_pi.mpr
--     fun w ↦ Real.continuousOn_log.comp' (continuousOn_apply _ _) (fun _ h ↦ (h w).ne')
--   map_source' := fun _ _ _ ↦ Real.exp_pos _
--   map_target' := fun _ _ ↦ trivial
--   left_inv' := fun _ _ ↦ by simp only [Real.log_exp, mul_inv_cancel_left₀ mult_coe_ne_zero]
--   right_inv' := fun _ hx ↦ by simp only [inv_mul_cancel_left₀ mult_coe_ne_zero, Real.exp_log (hx _)]

@[simps]
def expMap_single (w : InfinitePlace K) : PartialHomeomorph ℝ ℝ where
  toFun := fun x ↦ Real.exp ((w.mult : ℝ)⁻¹ * x)
  invFun := fun x ↦ w.mult * Real.log x
  source := Set.univ
  target := Set.Ioi 0
  open_source := isOpen_univ
  open_target := isOpen_Ioi
  map_source' _ _ := Real.exp_pos _
  map_target' _ _ := trivial
  left_inv' _ _ := by simp only [Real.log_exp, mul_inv_cancel_left₀ mult_coe_ne_zero]
  right_inv' _ h := by simp only [inv_mul_cancel_left₀ mult_coe_ne_zero, Real.exp_log h]
  continuousOn_toFun := (continuousOn_const.mul continuousOn_id).rexp
  continuousOn_invFun := continuousOn_const.mul (Real.continuousOn_log.mono (by aesop))

abbrev deriv_expMap_single (w : InfinitePlace K) (x : ℝ) : ℝ :=
  (expMap_single w x) * (w.mult : ℝ)⁻¹
--  Real.exp ((w.mult : ℝ)⁻¹ * x) * (w.mult : ℝ)⁻¹

theorem hasDerivAt_expMap_single (w : InfinitePlace K) (x : ℝ) :
    HasDerivAt (expMap_single w) (deriv_expMap_single w x) x := by
  convert (HasDerivAt.comp x (Real.hasDerivAt_exp _) (hasDerivAt_const_mul (w.mult : ℝ)⁻¹)) using 1

variable [NumberField K]

def expMap : PartialHomeomorph (realSpace K) (realSpace K) := by
  refine PartialHomeomorph.pi fun w ↦ expMap_single w

-- open scoped Classical in
-- @[simps]
-- def expMap₀ : PartialHomeomorph (realSpace K) (realSpace K) where
--   toFun := fun x w ↦ if w = w₀ then x w₀ else Real.exp ((w.mult : ℝ)⁻¹ * x w)
--   invFun := fun x w ↦ if w = w₀ then x w₀ else w.mult * Real.log (x w)
--   source := Set.univ
--   target := {x | ∀ w, w ≠ w₀ → 0 < x w}
--   open_source := isOpen_univ
--   open_target := sorry
--   --    simp_rw [Set.setOf_forall]
--   --  exact isOpen_iInter_of_finite fun _ ↦ isOpen_lt continuous_const <| continuous_apply _
--   continuousOn_toFun := sorry
--     -- continuousOn_pi'
--     -- fun i ↦ (ContinuousOn.mul continuousOn_const (continuousOn_apply i Set.univ)).rexp
--   continuousOn_invFun := sorry
--   -- continuousOn_const.mul <| continuousOn_pi.mpr
--   --  fun w ↦ Real.continuousOn_log.comp' (continuousOn_apply _ _) (fun _ h ↦ (h w).ne')
--   map_source' := sorry -- fun _ _ _ ↦ Real.exp_pos _
--   map_target' := sorry -- fun _ _ ↦ trivial
--   left_inv' := fun _ _ ↦ by ext; aesop
--   right_inv' := fun _ hx ↦ by
--     ext w
--     dsimp
--     split_ifs with hw hw
--     · aesop
--     · aesop
--     · simp_all only [inv_mul_cancel_left₀ mult_coe_ne_zero, Real.exp_log (hx w hw)]

@[simp]
theorem expMap_apply (x : realSpace K) (w : InfinitePlace K) :
    expMap x w = Real.exp ((↑w.mult)⁻¹ * x w) := rfl

theorem expMap_apply' (x : realSpace K) :
    expMap x = fun w ↦ Real.exp ((w.mult : ℝ)⁻¹ * x w) := rfl

@[simp]
theorem expMap_symm_apply (x : realSpace K) (w : InfinitePlace K) :
      expMap.symm x w = ↑w.mult * Real.log (x w) := rfl

theorem expMap_pos (x : realSpace K) (w : InfinitePlace K) :
    0 < expMap x w :=
  Real.exp_pos _

variable (K) in
theorem expMap_source :
    expMap.source = (Set.univ : Set (realSpace K)) := by
  simp_rw [expMap, PartialHomeomorph.pi_toPartialEquiv, PartialEquiv.pi_source, expMap_single,
    Set.pi_univ Set.univ]

variable (K) in
theorem expMap_target :
    expMap.target = Set.univ.pi fun (_ : InfinitePlace K) ↦ Set.Ioi 0 := by
  simp_rw [expMap, PartialHomeomorph.pi_toPartialEquiv, PartialEquiv.pi_target, expMap_single]

variable (K) in
theorem continuous_expMap :
    Continuous (expMap : realSpace K → realSpace K) :=
  continuous_iff_continuousOn_univ.mpr <| (expMap_source K) ▸ expMap.continuousOn

theorem injective_expMap :
    Function.Injective (expMap : realSpace K → realSpace K) :=
  Set.injective_iff_injOn_univ.mpr ((expMap_source K) ▸ expMap.injOn)

@[simp]
theorem expMap_zero :
    expMap (0 : realSpace K) = 1 := by
  simp_rw [expMap_apply', Pi.zero_apply, mul_zero, Real.exp_zero, Pi.one_def]

theorem expMap_add (x y : realSpace K) :
    expMap (x + y) = expMap x * expMap y := by
  simp_rw [expMap_apply', Pi.add_apply, mul_add, Real.exp_add, Pi.mul_def]

theorem expMap_sum {ι : Type*} (s : Finset ι) (f : ι → realSpace K) :
    expMap (∑ i ∈ s, f i) = ∏ i ∈ s, expMap (f i) := by
  simp_rw [expMap_apply', prod_fn, ← Real.exp_sum, ← Finset.mul_sum, Finset.sum_apply]

theorem expMap_smul (c : ℝ) (x : realSpace K) :
    expMap (c • x) = (expMap x) ^ c := by
  simp_rw [expMap_apply', Pi.smul_apply, smul_eq_mul, mul_comm c _, ← mul_assoc, Real.exp_mul,
    Pi.pow_def]

def fderiv_expMap (x : realSpace K) : realSpace K →L[ℝ] realSpace K :=
  .pi fun w ↦ (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv_expMap_single w (x w))).comp
    (.proj w)

theorem hasFDerivAt_expMap (x : realSpace K): HasFDerivAt expMap (fderiv_expMap x) x := by
  simpa [expMap, fderiv_expMap, hasFDerivAt_pi', PartialHomeomorph.pi_apply,
    ContinuousLinearMap.proj_pi] using
    fun w ↦ (hasDerivAt_expMap_single w _).hasFDerivAt.comp x (hasFDerivAt_apply w x)

-- That's an awful name
def restMap : realSpace K →ₗ[ℝ] ({w : InfinitePlace K // w ≠ w₀} → ℝ) where
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

theorem restMap_apply (x :realSpace K) (w : {w : InfinitePlace K // w ≠ w₀}) :
    restMap x w = x w - w.1.mult * (∑ w', x w') * (Module.finrank ℚ K : ℝ)⁻¹ := rfl

theorem logMap_expMap {x : realSpace K}
    (hx : mixedEmbedding.norm (mixedSpaceOfRealSpace (expMap x)) = 1) :
    logMap (mixedSpaceOfRealSpace (expMap x)) = fun w ↦ x w.1 := by
  ext
  rw [logMap, normAtPlace_mixedSpaceOfRealSpace (Real.exp_nonneg _), expMap_apply, Real.log_exp,
    mul_sub, mul_inv_cancel_left₀ mult_coe_ne_zero, hx, Real.log_one, zero_mul, mul_zero, sub_zero]

theorem restMap_expMap_symm_apply (x : realSpace K) (w : {w : InfinitePlace K // w ≠ w₀})  :
    restMap (expMap.symm x) w = w.1.mult * (Real.log (x w) -
      (∑ w', w'.mult * Real.log (x w')) * (Module.finrank ℚ K : ℝ)⁻¹) := by
  simp_rw [restMap_apply, expMap_symm_apply, mul_sub]
  rw [← mul_assoc, Finset.mul_sum]

theorem restMap_expMap_symm_normAtAllPlaces {x : mixedSpace K} (hx : mixedEmbedding.norm x ≠ 0) :
    restMap (expMap.symm (normAtAllPlaces x)) = logMap x := by
  have h {w} : (normAtPlace w x) ^ w.mult ≠ 0 :=
    pow_ne_zero _ (mixedEmbedding.norm_ne_zero_iff.mp hx w)
  ext w
  simp_rw [restMap_expMap_symm_apply, normAtAllPlaces_apply, logMap_apply,
    mixedEmbedding.norm_apply, Real.log_prod _ _ fun _ _ ↦ h,  Real.log_pow]

theorem restMap_expMap_symm_place_eval (x : K) (hx : x ≠ 0) :
    restMap (expMap.symm  (fun w ↦ w x)) = logMap (mixedEmbedding K x) := by
  rw [← normAtAllPlaces_mixedEmbedding,
    restMap_expMap_symm_normAtAllPlaces (by simp [norm_eq_norm, hx])]

-- variable [NumberField K]

open scoped Classical in
/-- DOCSTRING -/
def equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w ≠ w₀} :=
  Fintype.equivOfCardEq <| by
    rw [Fintype.card_subtype_compl, Fintype.card_ofSubsingleton, Fintype.card_fin, rank]

-- variable (K) in
-- def basis₀ : {w : InfinitePlace K // w ≠ w₀} → realSpace K := by
--   intro i
--   exact expMap.symm (fun w ↦ w (fundSystem K (equivFinRank.symm i)))

-- theorem restMap_basis₀ (i : {w : InfinitePlace K // w ≠ w₀}) :
--     restMap (basis₀ K i) =
--       (logEmbedding K) (Additive.ofMul (fundSystem K (equivFinRank.symm i))) := by
--   rw [← logMap_eq_logEmbedding, ← restMap_expMap_symm_place_eval, basis₀]
--   exact coe_ne_zero _

-- variable (K) in
-- theorem linearIndependent_basis₀ :
--     LinearIndependent ℝ (basis₀ K) := by
--   classical
--   refine LinearIndependent.of_comp restMap ?_
--   simp_rw [Function.comp_def, restMap_basis₀, logEmbedding_fundSystem]
--   convert (((basisUnitLattice K).ofZLatticeBasis ℝ _).reindex equivFinRank).linearIndependent
--   simp only [ne_eq, Basis.coe_reindex, Function.comp_apply, Basis.ofZLatticeBasis_apply]

-- variable (K) in
-- def basis : Basis {w : InfinitePlace K // w ≠ w₀} ℝ (realSpace K) := by
--   classical
--   have : Nonempty {w : InfinitePlace K // w ≠ w₀} := sorry
--   exact basisOfLinearIndependentOfCardEqFinrank (linearIndependent_basis₀ K)
--     sorry -- (Module.finrank_fintype_fun_eq_card _).symm


open Classical in
variable (K) in
def completeBasis₀ : InfinitePlace K → realSpace K := by
  intro i
  by_cases hi : i = w₀
  · exact fun w ↦ mult w
  · exact expMap.symm (fun w ↦ w (fundSystem K (equivFinRank.symm ⟨i, hi⟩)))

theorem sum_completeBasis₀_of_eq :
    ∑ w : InfinitePlace K, completeBasis₀ K w₀ w = Module.finrank ℚ K := by
  rw [completeBasis₀, dif_pos rfl, ← Nat.cast_sum, sum_mult_eq]

theorem restMap_completeBasis₀_of_eq :
    restMap (completeBasis₀ K w₀) = 0 := by
  ext
  rw [restMap_apply, sum_completeBasis₀_of_eq, completeBasis₀, dif_pos rfl, mul_inv_cancel_right₀
    (Nat.cast_ne_zero.mpr Module.finrank_pos.ne'), sub_self, Pi.zero_apply]

theorem restMap_completeBasis₀_of_ne (i : {w : InfinitePlace K // w ≠ w₀}) :
    restMap (completeBasis₀ K i) =
      (logEmbedding K) (Additive.ofMul (fundSystem K (equivFinRank.symm i))) := by
  rw [← logMap_eq_logEmbedding, ← restMap_expMap_symm_place_eval, completeBasis₀, dif_neg]
  exact coe_ne_zero _

theorem sum_completeBasis₀_of_ne_eq_zero (i : {w // w ≠ w₀}):
    ∑ w : InfinitePlace K, completeBasis₀ K i.1 w = 0 := by
  simp_rw [completeBasis₀, dif_neg i.prop, expMap_symm_apply, ← Real.log_pow]
  rw [← Real.log_prod _ _ (fun _ _ ↦ by simp), prod_eq_abs_norm, Units.norm, Rat.cast_one,
    Real.log_one]

theorem sum_eq_zero_of_mem_span {x : realSpace K}
    (hx : x ∈ Submodule.span ℝ (Set.range fun w : {w // w ≠ w₀} ↦ completeBasis₀ K w.1)) :
    ∑ w, x w = 0 := by
  induction hx using Submodule.span_induction with
  | mem _ h =>
      obtain ⟨w, rfl⟩ := h
      exact sum_completeBasis₀_of_ne_eq_zero w
  | zero => simp
  | add _ _ _ _ hx hy => simp [Finset.sum_add_distrib, hx, hy]
  | smul _ _ _ hx => simp [← Finset.mul_sum, hx]

variable (K) in
theorem linearIndependent_completeBasis₀ :
    LinearIndependent ℝ (completeBasis₀ K) := by
  classical
  have h₁ : LinearIndependent ℝ (fun w : {w // w ≠ w₀} ↦ completeBasis₀ K w.1) := by
    refine LinearIndependent.of_comp restMap ?_
    simp_rw [Function.comp_def, restMap_completeBasis₀_of_ne, logEmbedding_fundSystem]
    have := (((basisUnitLattice K).ofZLatticeBasis ℝ _).reindex equivFinRank).linearIndependent
    convert this
    simp only [ne_eq, Basis.coe_reindex, Function.comp_apply, Basis.ofZLatticeBasis_apply]
  have h₂ : completeBasis₀ K w₀ ∉ Submodule.span ℝ
      (Set.range (fun w : {w // w ≠ w₀} ↦ completeBasis₀ K w.1)) := by
    intro h
    have := sum_eq_zero_of_mem_span h
    rw [sum_completeBasis₀_of_eq, Nat.cast_eq_zero] at this
    exact Module.finrank_pos.ne' this
  rw [← linearIndependent_equiv (Equiv.optionSubtypeNe w₀)]
  rw [linearIndependent_option]
  exact ⟨h₁, h₂⟩

variable (K) in
def completeBasis : Basis (InfinitePlace K) ℝ (realSpace K) :=
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_completeBasis₀ K)
    (Module.finrank_fintype_fun_eq_card _).symm

theorem completeBasis_apply_of_eq :
    completeBasis K w₀ = fun w ↦ (mult w : ℝ) := by
  rw [completeBasis, coe_basisOfLinearIndependentOfCardEqFinrank, completeBasis₀, dif_pos rfl]

theorem completeBasis_apply_of_ne (i : {w : InfinitePlace K // w ≠ w₀}) :
    completeBasis K i =
      expMap.symm (fun w : InfinitePlace K ↦ w (fundSystem K (equivFinRank.symm i))) := by
  rw [completeBasis, coe_basisOfLinearIndependentOfCardEqFinrank, completeBasis₀, dif_neg]

open scoped Classical in
theorem completeBasis_equivFun_symm_apply {x : realSpace K} (hx : x w₀ = 0) (w : {w // w ≠ w₀}) :
  (completeBasis K).equivFun.symm x w.1 =
    ((basisUnitLattice K).ofZLatticeBasis ℝ (unitLattice K)).equivFun.symm
      (fun w ↦ x (equivFinRank w)) w := by
  rw [Basis.equivFun_symm_apply, Basis.equivFun_symm_apply, ← equivFinRank.symm.sum_comp,
    Fintype.sum_eq_add_sum_fintype_ne _ w₀, hx]
  simp [completeBasis_apply_of_ne, ← logEmbedding_fundSystem]

-- theorem restMap_completeBasis_of_eq :
--     restMap (completeBasis K w₀) = 0 := by
--   rw [completeBasis, coe_basisOfLinearIndependentOfCardEqFinrank, restMap_completeBasis₀_of_eq]

-- theorem restMap_completeBasis_of_ne (i : {w : InfinitePlace K // w ≠ w₀}) :
--     restMap (completeBasis K i) =
--       (logEmbedding K) (Additive.ofMul (fundSystem K (equivFinRank.symm i))) := by
--   rw [completeBasis, coe_basisOfLinearIndependentOfCardEqFinrank, restMap_completeBasis₀_of_ne]

-- open Classical in
-- theorem restMap_sum_smul_completeBasis (x : realSpace K) :
--     restMap (∑ w, x w • completeBasis K w) =
--       ∑ i, x (equivFinRank i) • ((basisUnitLattice K).ofZLatticeBasis ℝ _ i) := by
--   simp_rw [map_sum, _root_.map_smul, Fintype.sum_eq_add_sum_fintype_ne _ w₀,
--     restMap_completeBasis_of_eq, smul_zero, zero_add, restMap_completeBasis_of_ne,
--     logEmbedding_fundSystem, ← (basisUnitLattice K).ofZLatticeBasis_apply ℝ,
--     ← equivFinRank.sum_comp, Equiv.symm_apply_apply]

-- open Classical in
-- theorem completeBasis_repr_eq_unitLatticeBasis_repr (x : realSpace K) (w : {w // w ≠ w₀}) :
--     (completeBasis K).repr x w.1 =
--       ((basisUnitLattice K).ofZLatticeBasis ℝ _).repr (restMap x) (equivFinRank.symm w) := by
--   have := restMap.congr_arg ((completeBasis K).sum_repr x)
--   rw [restMap_sum_smul_completeBasis] at this
--   rw [← this]
--   simp [Finsupp.single_apply]

theorem expMap_basis_of_eq :
    expMap (completeBasis K w₀) = fun _ ↦ Real.exp 1 := by
  simp_rw [expMap_apply', completeBasis_apply_of_eq, inv_mul_cancel₀ mult_coe_ne_zero]

theorem expMap_basis_of_ne (i : {w : InfinitePlace K // w ≠ w₀}) :
    expMap (completeBasis K i) = fun w ↦ w (fundSystem K (equivFinRank.symm i) : 𝓞 K) := by
  rw [completeBasis_apply_of_ne, PartialHomeomorph.right_inv _ (by simp [expMap_target])]

def expMapBasis : PartialHomeomorph (realSpace K) (realSpace K) :=
  (completeBasis K).equivFunL.symm.toHomeomorph.transPartialHomeomorph expMap

-- def expMapBasis₀ : PartialHomeomorph (realSpace K) (realSpace K) where
--   toFun := fun x ↦ by

theorem expMapBasis_apply (x : realSpace K) :
    expMapBasis x = expMap ((completeBasis K).equivFun.symm x) := rfl

open scoped Classical in
theorem expMapBasis_apply' (x : realSpace K) :
    expMapBasis x = Real.exp (x w₀) •
      fun w : InfinitePlace K ↦
         ∏ i : {w // w ≠ w₀}, w (fundSystem K (equivFinRank.symm i)) ^ x i := by
  simp_rw [expMapBasis_apply, Basis.equivFun_symm_apply, Fintype.sum_eq_add_sum_fintype_ne _ w₀,
    expMap_add, expMap_smul, expMap_basis_of_eq, Pi.pow_def, Real.exp_one_rpow, Pi.mul_def,
    expMap_sum, expMap_smul, expMap_basis_of_ne, Pi.smul_def, smul_eq_mul, prod_apply, Pi.pow_apply]

open scoped Classical in
theorem expMapBasis_apply'' (x : realSpace K) :
    expMapBasis x = Real.exp (x w₀) •
      expMapBasis (fun i ↦ if i = w₀ then 0 else x i) := by
  rw [expMapBasis_apply', expMapBasis_apply', if_pos rfl, smul_smul, ← Real.exp_add, add_zero]
  conv_rhs =>
    enter [2, w, 2, i]
    rw [if_neg i.prop]

variable (K) in
theorem continuous_expMapBasis :
    Continuous (expMapBasis : realSpace K → realSpace K) :=
  (continuous_expMap K).comp (ContinuousLinearEquiv.continuous _)

-- theorem expMapBasis₀_apply (x : realSpace K) :
--     expMapBasis₀ x = expMap₀ ((completeBasis K).equivFun.symm x) := rfl

theorem expMapBasis_symm_apply (x : realSpace K) :
    expMapBasis.symm x = (completeBasis K).equivFun (expMap.symm x) := by
  simp [expMapBasis]
  rfl

theorem expMapBasis_source :
    expMapBasis.source = (Set.univ :  Set (realSpace K)) := by
  simp [expMapBasis, expMap_source]

theorem expMapBasis_target :
    expMapBasis.target = Set.univ.pi fun (_ : InfinitePlace K) ↦ Set.Ioi 0 := rfl

theorem expMapBasis_pos (x : realSpace K) (w : InfinitePlace K) :
    0 < expMapBasis x w := expMap_pos _ _

-- theorem prod_expMapBasis₀_pow (x : realSpace K) :
--     ∏ w, (expMapBasis₀ x w) ^ w.mult = x w₀ ^ Module.finrank ℚ K := by
--   simp_rw [expMapBasis₀_apply]
--   simp only [Basis.equivFun_symm_apply, sum_apply, Pi.smul_apply, smul_eq_mul]
--   rw [Fintype.sum_eq_add_sum_fintype_ne _ w₀]

theorem prod_expMapBasis_pow (x : realSpace K) :
    ∏ w, (expMapBasis x w) ^ w.mult = Real.exp (x w₀) ^ Module.finrank ℚ K := by
  simp_rw [expMapBasis_apply', Pi.smul_def, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    prod_pow_eq_pow_sum, sum_mult_eq, ← Finset.prod_pow]
  rw [Finset.prod_comm]
  simp_rw [Real.rpow_pow_comm (apply_nonneg _ _), Real.finset_prod_rpow _ _
    fun _ _ ↦ pow_nonneg (apply_nonneg _ _) _, prod_eq_abs_norm, Units.norm, Rat.cast_one,
    Real.one_rpow, prod_const_one, mul_one]

theorem norm_expMapBasis (x : realSpace K) :
    mixedEmbedding.norm (mixedSpaceOfRealSpace (expMapBasis x)) =
      Real.exp (x w₀) ^ Module.finrank ℚ K := by
  simpa only [mixedEmbedding.norm_apply,
    normAtPlace_mixedSpaceOfRealSpace (expMapBasis_pos _ _).le] using prod_expMapBasis_pow x

theorem norm_expMapBasis_ne_zero (x : realSpace K) :
    mixedEmbedding.norm (mixedSpaceOfRealSpace (expMapBasis x)) ≠ 0 :=
  norm_expMapBasis x ▸ pow_ne_zero _ (Real.exp_ne_zero _)

theorem expMapBasis_symm_normAtAllPlaces {x : mixedSpace K} (hx : mixedEmbedding.norm x ≠ 0) :
    expMapBasis.symm (normAtAllPlaces x) w₀ =
      (Module.finrank ℚ K : ℝ)⁻¹ * Real.log (mixedEmbedding.norm x) := by
  rw [norm_eq_prod_normAtAllPlaces, ← expMapBasis.right_inv (x := normAtAllPlaces x),
    prod_expMapBasis_pow, expMapBasis.left_inv, Real.log_pow, Real.log_exp, inv_mul_cancel_left₀]
  · rw [Nat.cast_ne_zero]
    exact Module.finrank_pos.ne'
  · rw [expMapBasis_source]
    trivial
  · rw [expMapBasis_target]
    intro w _
    rw [normAtAllPlaces]
    rw [mixedEmbedding.norm_ne_zero_iff] at hx
    specialize hx w
    refine lt_of_le_of_ne' (normAtPlace_nonneg w x) hx

-- open Classical in
-- theorem logMap₀_expMapBasis (x : realSpace K) :
--     restMap (expMap.symm (expMapBasis x)) =
--       ((basisUnitLattice K).ofZLatticeBasis ℝ _).equivFun.symm (fun i ↦ x (equivFinRank i)) := by
--   rw [expMapBasis_apply, expMap.left_inv trivial, Basis.equivFun_symm_apply,
--     restMap_sum_smul_completeBasis, Basis.equivFun_symm_apply]

-- theorem norm_expMap (x : realSpace K) :
--     mixedEmbedding.norm (mixedSpaceOfRealSpace (expMap x)) = Real.exp (∑ w, x w) := by
--   simp_rw [mixedEmbedding.norm_apply, normAtPlace_mixedSpaceOfRealSpace sorry, expMap_apply,
--     mul_comm, ← Real.rpow_natCast, ← Real.exp_mul, inv_mul_cancel_right₀ sorry, ← Real.exp_sum]

open scoped Classical in
theorem main (x : realSpace K) (w : {w // w ≠ w₀}) :
    ((basisUnitLattice K).ofZLatticeBasis ℝ (unitLattice K)).equivFun
      (logMap (mixedSpaceOfRealSpace (expMapBasis x))) (equivFinRank.symm w) = x w.1 := by
  rw [expMapBasis_apply'', _root_.map_smul, logMap_real_smul (norm_expMapBasis_ne_zero _)
    (Real.exp_ne_zero _), expMapBasis_apply, logMap_expMap]
  · conv_lhs =>
      enter [2, w]
      rw [completeBasis_equivFun_symm_apply (by rw [if_pos rfl])]
    rw [LinearEquiv.apply_symm_apply, Equiv.apply_symm_apply, if_neg w.prop]
  · rw [← expMapBasis_apply, norm_expMapBasis, if_pos rfl, Real.exp_zero, one_pow]

open ENNReal MeasureTheory.Measure

variable (K) in
abbrev fderiv_expMapBasis (x : realSpace K) : realSpace K →L[ℝ] realSpace K :=
  (fderiv_expMap ((completeBasis K).equivFun.symm x)).comp
    (completeBasis K).equivFunL.symm.toContinuousLinearMap

theorem hasFDerivAt_expMapBasis (x : realSpace K) :
    HasFDerivAt expMapBasis (fderiv_expMapBasis K x) x := by
  change HasFDerivAt (expMap ∘ (completeBasis K).equivFunL.symm) (fderiv_expMapBasis K x) x
  exact (hasFDerivAt_expMap _).comp x (completeBasis K).equivFunL.symm.hasFDerivAt

example (x : realSpace K) :
    ∏ w, expMap_single w ((completeBasis K).equivFun.symm x w) =
      ∏ w, (expMapBasis x w) ^ mult w := by
  simp_rw [expMap_single_apply]
  simp_rw [expMapBasis_apply, expMap_apply]


open scoped Classical in
theorem toto (x : realSpace K) :
    ∏ w, deriv_expMap_single w ((completeBasis K).equivFun.symm x w) =
      (∏ w : {w // IsComplex w}, x w.1) * Real.exp (x w₀) ^ Module.finrank ℚ K *
        (2⁻¹) ^ nrComplexPlaces K := by
  simp only [deriv_expMap_single, expMap_single_apply]
  rw [Finset.prod_mul_distrib]
  simp only [← Fintype.prod_subtype_mul_prod_subtype (fun w ↦ IsReal w), ← prod_expMapBasis_pow]
  congr 1
  · simp_rw [expMapBasis_apply, expMap_apply]
    conv_rhs =>
      enter [2, 1, 2, w, 2]
      rw [mult, if_pos w.prop]
    conv_rhs =>
      enter [2, 2, 2, w, 2]
      rw [mult, if_neg w.prop]
    simp_rw [pow_one]
    sorry
  · conv_lhs =>
      enter [1, 2, w]
      rw [mult, if_pos w.prop, Nat.cast_one, inv_one]
    conv_lhs =>
      enter [2, 2, w]
      rw [mult, if_neg w.prop, Nat.cast_ofNat]
    simp

theorem det_fderiv_expMapBasis (x : realSpace K) : (fderiv_expMapBasis K x).det = 1 := by
  rw [fderiv_expMapBasis, ContinuousLinearMap.det, ContinuousLinearMap.coe_comp, LinearMap.det_comp]
  rw [fderiv_expMap]
  simp only [ Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, ContinuousLinearMap.coe_pi, ContinuousLinearMap.coe_comp,
    ContinuousLinearEquiv.det_coe_symm]
  erw [LinearMap.det_pi]
  simp only [LinearMap.det_ring, ContinuousLinearMap.coe_coe, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul, one_mul]
--  simp only [Basis.equivFun_symm_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [deriv_expMap_single]
  rw [Finset.prod_mul_distrib]







  sorry


open scoped Classical in
theorem setLIntegral_expMapBasis {s : Set (realSpace K)} (hs : MeasurableSet s)
    (f : (InfinitePlace K → ℝ) → ℝ≥0∞) :
    ∫⁻ x in expMapBasis '' s, f x =
      (2 : ℝ≥0∞)⁻¹ ^ nrComplexPlaces K * ENNReal.ofReal (regulator K) * (Module.finrank ℚ K) *
      ∫⁻ x in s, ENNReal.ofReal (Real.exp (Module.finrank ℚ K * x w₀)) *
        (∏ i : {w : InfinitePlace K // IsComplex w},
          .ofReal (expMapBasis (fun w ↦ x w) i))⁻¹ * f (expMapBasis x) := by

  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun x _ ↦ (hasFDerivAt_expMapBasis x).hasFDerivWithinAt)]
  ·
    sorry
  · sorry

variable (K) in
abbrev normLeOne : Set (mixedSpace K) :=
  {x | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ 1}

open scoped Classical in
variable (K) in
abbrev paramSet : Set (realSpace K) :=
  Set.univ.pi fun w ↦ if w = w₀ then Set.Iic 0 else Set.Ico 0 1

theorem le_of_mem_paramSet {x : realSpace K} (hx : x ∈ paramSet K) :
    x w₀ ≤ 0 := by
  replace hx := hx w₀ (Set.mem_univ _)
  simpa only [ite_true, Set.mem_Iic] using hx

theorem mem_Ico_of_mem_paramSet {x : realSpace K} (hx : x ∈ paramSet K)
    (w : {w // w ≠ w₀}) :
    x w.1 ∈ Set.Ico 0 1 := by
  replace hx := hx w (Set.mem_univ _)
  simpa only [if_neg w.prop, Set.mem_Iic] using hx

variable (K) in
theorem normAtAllPlaces_normLeOne :
    normAtAllPlaces '' (normLeOne K) = expMapBasis '' (paramSet K) := by
  classical
  ext
  simp only [Set.mem_image, Set.mem_setOf_eq, fundamentalCone, Set.mem_diff, Set.mem_preimage,
    ZSpan.mem_fundamentalDomain, equivFinRank.forall_congr_left]
  refine ⟨?_, ?_⟩
  · rintro ⟨x, ⟨⟨hx₁, hx₂⟩, hx₃⟩, rfl⟩
    have hx₄ : normAtAllPlaces x ∈ expMapBasis.target :=
      fun w _ ↦ lt_of_le_of_ne' (normAtPlace_nonneg w x) (mixedEmbedding.norm_ne_zero_iff.mp hx₂ w)
    refine ⟨?_, ?_, ?_⟩
    · exact expMapBasis.symm (normAtAllPlaces x)
    · intro w _
      by_cases hw : w = w₀
      · simp_rw [hw, expMapBasis_symm_normAtAllPlaces hx₂, if_true, Set.mem_Iic]
        have : 0 < (Module.finrank ℚ K : ℝ)⁻¹ :=
          inv_pos.mpr <| Nat.cast_pos.mpr Module.finrank_pos
        simpa [mul_nonpos_iff_pos_imp_nonpos, this,
          Real.log_nonpos_iff (mixedEmbedding.norm_nonneg _)] using hx₃
      · rw [← main (expMapBasis.symm (normAtAllPlaces x)) ⟨w, hw⟩, expMapBasis.right_inv hx₄,
          logMap_normAtAllPlaces]
        simp_rw [if_neg hw]
        exact hx₁ _
    · rw [expMapBasis.right_inv hx₄]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨mixedSpaceOfRealSpace (expMapBasis x), ⟨⟨?_, norm_expMapBasis_ne_zero x⟩, ?_⟩, ?_⟩
    · intro w
      simp_rw [← Basis.equivFun_apply, main]
      exact mem_Ico_of_mem_paramSet hx w
    · rw [norm_expMapBasis]
      refine (pow_le_one_iff_of_nonneg ?_ ?_).mpr ?_
      · exact Real.exp_nonneg _
      · exact Module.finrank_pos.ne'
      · rw [Real.exp_le_one_iff]
        exact le_of_mem_paramSet hx
    · ext
      rw [normAtAllPlaces_apply, normAtPlace_mixedSpaceOfRealSpace]
      exact (expMapBasis_pos _ _).le

theorem mem_normLeOne_iff (x : mixedSpace K):
    x ∈ normLeOne K ↔ mixedSpaceOfRealSpace (normAtAllPlaces x) ∈ normLeOne K := by
  simp only [normLeOne, Set.mem_setOf_eq, normAtAllPlaces_mem_fundamentalCone_iff,
    norm_normAtAllPlaces]

variable (K) in
theorem normLeOne_eq_primeage_image :
    normLeOne K = normAtAllPlaces⁻¹' (normAtAllPlaces '' (normLeOne K)) :=
  mem_iff_normAtAllPlaces_mem_iff.mp fun x ↦ mem_normLeOne_iff x

variable (K) in
theorem normLeOne_eq :
    normLeOne K = normAtAllPlaces⁻¹' (expMapBasis '' (paramSet K)) := by
  rw [normLeOne_eq_primeage_image, normAtAllPlaces_normLeOne]

open scoped Classical in
variable (K) in
theorem closure_paramSet :
    closure (paramSet K) = Set.univ.pi fun w ↦ if w = w₀ then Set.Iic 0 else Set.Icc 0 1 := by
  simp [closure_pi_set, apply_ite]

open scoped Classical in
variable (K) in
theorem interior_paramSet :
    interior (paramSet K) = Set.univ.pi fun w ↦ if w = w₀ then Set.Iio 0 else Set.Ioo 0 1 := by
  simp [interior_pi_set Set.finite_univ, apply_ite]

open Pointwise Bornology

variable (K) in
open scoped Classical in
theorem expMapBasis_closure_subset :
    expMapBasis '' closure (paramSet K) ⊆ (Set.Icc (0 : ℝ) 1) •
      (expMapBasis '' Set.univ.pi fun w ↦ if w = w₀ then {0} else Set.Icc 0 1) := by
  intro x
  rw [closure_paramSet, Set.mem_image, Set.mem_smul]
  rintro ⟨x, hx, rfl⟩
  refine ⟨Real.exp (x w₀), ?_, expMapBasis fun i ↦ if i = w₀ then 0 else x i, ?_, ?_⟩
  · simpa [Real.exp_nonneg] using hx w₀ (Set.mem_univ _)
  · refine ⟨_, fun w ↦ ?_, rfl⟩
    by_cases hw : w = w₀
    · simp [hw]
    · simpa [hw] using hx w (Set.mem_univ _)
  · rw [expMapBasis_apply'' x]

theorem isBounded_normAtAllPlaces_preimage {s : Set (realSpace K)} (hs : IsBounded s) :
    IsBounded (normAtAllPlaces⁻¹' s) := by
  classical
  rw [isBounded_iff_forall_norm_le] at hs ⊢
  obtain ⟨C, hC⟩ := hs
  refine ⟨C, fun x hx ↦ ?_⟩
  rw [norm_eq_sup'_normAtPlace]
  apply Finset.sup'_le
  intro w _
  rw [Set.mem_preimage] at hx
  have := hC _ hx
  rw [pi_norm_le_iff_of_nonempty] at this
  have := this w
  rwa [normAtAllPlaces_apply, Real.norm_of_nonneg (normAtPlace_nonneg w x)] at this

theorem isBounded_normLeOne : Bornology.IsBounded (normLeOne K) := by
  rw [normLeOne_eq]
  apply isBounded_normAtAllPlaces_preimage
  refine IsBounded.subset ?_ (Set.image_mono subset_closure)
  refine (IsCompact.isBounded ?_).subset (expMapBasis_closure_subset K)
  refine isCompact_Icc.smul_set <| (isCompact_univ_pi fun w ↦ ?_).image_of_continuousOn
    (continuous_expMapBasis K).continuousOn
  split_ifs
  · exact isCompact_singleton
  · exact isCompact_Icc

theorem normAtAllPlaces_image_preimage_expMapBasis (s : Set (realSpace K)) :
    normAtAllPlaces '' (normAtAllPlaces ⁻¹' (expMapBasis '' s)) = expMapBasis '' s := by
  rw [Set.image_preimage_eq_iff]
  rintro _ ⟨x, _, rfl⟩
  refine ⟨mixedSpaceOfRealSpace (expMapBasis x), funext fun x ↦ ?_⟩
  rw [normAtAllPlaces_apply, normAtPlace_mixedSpaceOfRealSpace (expMapBasis_pos _ _).le]

theorem lintegral_paramSet_exp {n : ℕ} (hn : 0 < n) :
    ∫⁻ (x : realSpace K) in paramSet K, ENNReal.ofReal (Real.exp (n * x w₀)) = (n : ℝ≥0∞)⁻¹ := by
  classical
  rw [volume_pi, paramSet, Measure.restrict_pi_pi, lintegral_eq_lmarginal_univ 0,
    lmarginal_erase' _ (by fun_prop) (Finset.mem_univ w₀), if_pos rfl]
  simp_rw [Function.update_self, lmarginal, lintegral_const, Measure.pi_univ, if_neg
    (Finset.ne_of_mem_erase (Subtype.prop _)), restrict_apply_univ, Real.volume_Ico, sub_zero,
    ENNReal.ofReal_one, prod_const_one, mul_one]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [← setIntegral_congr_set Iio_ae_eq_Iic, integral_comp_mul_left_Iio _ _ (Nat.cast_pos.mpr hn),
      mul_zero, setIntegral_congr_set Iio_ae_eq_Iic, integral_exp_Iic, Real.exp_zero, smul_eq_mul,
      mul_one, ENNReal.ofReal_inv_of_pos (Nat.cast_pos.mpr hn), ofReal_natCast]
  · rw [← IntegrableOn, integrableOn_Iic_iff_integrableOn_Iio, integrableOn_Iio_comp_mul_left_iff _
      _ (Nat.cast_pos.mpr hn), mul_zero, ← integrableOn_Iic_iff_integrableOn_Iio]
    exact integrableOn_exp_Iic 0
  · filter_upwards with _ using Real.exp_nonneg _

open scoped Classical in
example : volume (normLeOne K) =
    2 ^ nrRealPlaces K * NNReal.pi ^ nrComplexPlaces K * (regulator K).toNNReal := by
  rw [volume_eq_two_pow_mul_two_pi_pow_mul_integral (fun x ↦ mem_normLeOne_iff x) sorry,
    normLeOne_eq, normAtAllPlaces_image_preimage_expMapBasis, setLIntegral_expMapBasis sorry]
  simp_rw [ENNReal.inv_mul_cancel_right' sorry sorry]
  rw [lintegral_paramSet_exp sorry]
  rw [ofReal_mul, mul_pow, ofReal_ofNat, ENNReal.mul_inv_cancel_right]
  


  sorry


#exit

theorem normAtPlaces_image_preimage_expMapBasis (s : Set (realSpace K)) :
    normAtAllPlaces '' (normAtAllPlaces ⁻¹' (expMapBasis '' s)) = expMapBasis '' s := by
  rw [Set.image_preimage_eq_iff]
  rintro _ ⟨x, _, rfl⟩
  refine ⟨mixedSpaceOfRealSpace (expMapBasis x), funext fun x ↦ ?_⟩
  rw [normAtAllPlaces_apply, normAtPlace_mixedSpaceOfRealSpace (expMapBasis_pos _ _).le]

open ENNReal Bornology

variable [NumberField K]

open scoped Classical in
theorem setLIntegral_expMapBasis {s : Set (realSpace K)} (f : (InfinitePlace K → ℝ) → ℝ≥0∞) :
    ∫⁻ x in expMapBasis '' s, f x =
      (2 : ℝ≥0∞)⁻¹ ^ nrComplexPlaces K * ENNReal.ofReal (regulator K) * (Module.finrank ℚ K) *
      ∫⁻ x in s, ENNReal.ofReal |x w₀| ^ rank K *
        .ofReal (∏ i : {w : InfinitePlace K // IsComplex w},
          (expMapBasis (fun w ↦ x w) i))⁻¹ * f (expMapBasis x) := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume]
  all_goals sorry

open Pointwise in
variable (K) in
theorem aux₀ :
    IsCompact (expMapBasis '' closure (paramSet K)) := by
  classical
  let S : Set (realSpace K) := Set.univ.pi fun w ↦ if w = w₀ then {0} else Set.Icc 0 1
  have : expMapBasis '' closure (paramSet K) = (Set.Icc (0 : ℝ) 1) • (expMapBasis '' S) := sorry
  rw [this]
  refine IsCompact.smul_set ?_ ?_
  · exact isCompact_Icc
  · refine IsCompact.image_of_continuousOn ?_ ?_
    · refine isCompact_univ_pi fun w ↦ ?_
      split_ifs
      · exact isCompact_singleton
      · exact isCompact_Icc
    · exact (continuous_expMapBasis K).continuousOn

theorem aux₀₀ {s : Set (realSpace K)} (hs : IsBounded s) :
    IsBounded (normAtAllPlaces⁻¹' s) := by
  classical
  rw [isBounded_iff_forall_norm_le] at hs ⊢
  obtain ⟨C, hC⟩ := hs
  refine ⟨C, fun x hx ↦ ?_⟩
  rw [norm_eq_sup'_normAtPlace]
  apply Finset.sup'_le
  intro w _
  rw [Set.mem_preimage] at hx
  have := hC _ hx
  rw [pi_norm_le_iff_of_nonempty] at this
  have := this w
  rwa [normAtAllPlaces_apply, Real.norm_of_nonneg (normAtPlace_nonneg w x)] at this

example : Bornology.IsBounded (normLeOne K) := by
  have := aux₀₀ (aux₀ K).isBounded
  refine Bornology.IsBounded.subset this ?_
  rw [normLeOne_eq_preimage]
  apply Set.preimage_mono
  apply Set.image_mono
  exact subset_closure

variable (K) in
theorem aux₁ :
    closure (normLeOne K) ⊆ normAtAllPlaces⁻¹' (expMapBasis '' (closure (paramSet K))) := by
  rw [normLeOne_eq_preimage]
--  rw [PartialHomeomorph.image_eq_target_inter_inv_preimage _ (Set.subset_univ _)]
  have := Continuous.closure_preimage_subset (f := normAtAllPlaces)
    (t := expMapBasis '' (paramSet K)) sorry
  refine this.trans ?_
  refine Set.preimage_mono ?_





--  normLessThanOne_eq K ▸ (continuous_expMapBasisFull K).closure_preimage_subset (paramSet K)

theorem aux₂ : normAtAllPlaces⁻¹' (expMapBasis '' (interior (paramSet K))) ⊆
    interior (normLeOne K) := by
  sorry
-- example : expMapBasisFull⁻¹' (interior (paramSet K)) ⊆ interior (normLessThanOne K) :=
--  normLessThanOne_eq K ▸ preimage_interior_subset_interior_preimage (continuous_expMapBasisFull K)

open scoped Classical in
theorem aux₃ : volume (normAtAllPlaces⁻¹' (expMapBasis '' (interior (paramSet K)))) =
    volume (normAtAllPlaces⁻¹' (expMapBasis '' (closure (paramSet K)))) := by
  rw [volume_eq_two_pow_mul_two_pi_pow_mul_integral, volume_eq_two_pow_mul_two_pi_pow_mul_integral,
    normAtPlaces_image_preimage_expMapBasis, normAtPlaces_image_preimage_expMapBasis,
    setLIntegral_expMapBasis, setLIntegral_expMapBasis]
  · congr 2
    refine setLIntegral_congr ?_
    sorry
  all_goals sorry

open scoped Classical in
example : volume (interior (normLeOne K)) = volume (closure (normLeOne K)) := by
  refine le_antisymm (measure_mono interior_subset_closure) ?_
  exact (aux₃ K ▸ measure_mono (aux₁ K)).trans (measure_mono (aux₂ K))


#exit











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



-- variable (K) in
-- abbrev polarSpace := (realSpace K) × ({w : InfinitePlace K // w.IsComplex} → ℝ)

-- open Classical MeasurableEquiv in
-- def measurableEquivRealMixedSpacePolarSpace : realMixedSpace K ≃ᵐ polarSpace K :=
--   MeasurableEquiv.trans (prodCongr (refl _)
--     (arrowProdEquivProdArrow ℝ ℝ _)) <|
--     MeasurableEquiv.trans prodAssoc.symm <|
--       MeasurableEquiv.trans
--         (prodCongr (prodCongr (refl _)
--           (arrowCongr' (Equiv.subtypeEquivRight (fun _ ↦ not_isReal_iff_isComplex.symm)) (refl _)))
--             (refl _))
--           (prodCongr (piEquivPiSubtypeProd (fun _ ↦ ℝ) _).symm (refl _))

-- open Classical in
-- def homeoRealMixedSpacePolarSpace : realMixedSpace K ≃ₜ polarSpace K :=
-- { measurableEquivRealMixedSpacePolarSpace with
--   continuous_toFun := by
--     change Continuous fun x : realMixedSpace K ↦  (fun w ↦ if hw : w.IsReal then x.1 ⟨w, hw⟩ else
--       (x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩).1, fun w ↦ (x.2 w).2)
--     refine continuous_prod_mk.mpr ⟨continuous_pi_iff.mpr fun w ↦ ?_, by fun_prop⟩
--     split_ifs <;> fun_prop
--   continuous_invFun := by
--     change Continuous fun x : polarSpace K ↦
--       (⟨fun w ↦ x.1 w.val, fun w ↦ ⟨x.1 w.val, x.2 w⟩⟩ : realMixedSpace K)
--     fun_prop }

-- omit [NumberField K] in
-- @[simp]
-- theorem homeoRealMixedSpacePolarSpace_symm_apply (x : polarSpace K) :
--     homeoRealMixedSpacePolarSpace.symm x = ⟨fun w ↦ x.1 w, fun w ↦ (x.1 w, x.2 w)⟩ := rfl

-- open Classical in
-- omit [NumberField K] in
-- theorem homeoRealMixedSpacePolarSpace_apply (x : realMixedSpace K) :
--     homeoRealMixedSpacePolarSpace x =
--       ⟨fun w ↦ if hw : w.IsReal then x.1 ⟨w, hw⟩ else
--         (x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩).1, fun w ↦ (x.2 w).2⟩ := rfl

-- open Classical in
-- theorem volume_preserving_homeoRealMixedSpacePolarSpace :
--     MeasurePreserving (homeoRealMixedSpacePolarSpace (K := K)) :=
--   ((MeasurePreserving.id volume).prod
--     (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ _)).trans <|
--       (volume_preserving_prodAssoc.symm).trans <|
--         (((MeasurePreserving.id volume).prod (volume_preserving_arrowCongr' _
--           (MeasurableEquiv.refl ℝ) (.id volume))).prod (.id volume)).trans <|
--             ((volume_preserving_piEquivPiSubtypeProd
--               (fun _ : InfinitePlace K ↦ ℝ) (fun w ↦ IsReal w)).symm).prod (.id volume)

@[simps!]
def expMapBasisFull₀ : PartialHomeomorph (mixedSpace K) (mixedSpace K) :=
  (PartialHomeomorph.pi fun _ ↦ .abs ℝ).prod (.refl _)

variable (K) in
theorem continuous_expMapBasisFull₀ :
    Continuous (expMapBasisFull₀ : mixedSpace K → mixedSpace K) := sorry

@[simps!]
def expMapBasisFull₁ : PartialHomeomorph (polarSpace K) (polarSpace K) :=
  expMapBasis.symm.prod (PartialHomeomorph.refl _)

-- @[simps!]
-- def polarCoord₀ : PartialHomeomorph (mixedSpace K) (polarSpace K) :=
--     (mixedEmbedding.polarCoord K).transHomeomorph homeoRealMixedSpacePolarSpace

def expMapBasisFull : PartialHomeomorph (mixedSpace K) (polarSpace K) :=
  expMapBasisFull₀.trans <| (polarSpaceCoord K).trans expMapBasisFull₁

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

open scoped Classical in
theorem expMapBasisFull_apply (x : mixedSpace K) :
    expMapBasisFull x =
      ⟨expMapBasis.symm fun w ↦  normAtPlace w x, fun w ↦ (Complex.polarCoord (x.2 w)).2⟩ := by
  unfold expMapBasisFull
  ext w
  · simp_rw [PartialHomeomorph.coe_trans, Function.comp_apply, expMapBasisFull₀_apply,
      polarSpaceCoord_apply,  homeoRealMixedSpacePolarSpace_apply, Pi.map_apply,
      PartialHomeomorph.abs_apply, expMapBasisFull₁_apply]
    congr!
    split_ifs with h
    · rw [normAtPlace_apply_of_isReal h, Real.norm_eq_abs]
    · rw [normAtPlace_apply_of_isComplex (not_isReal_iff_isComplex.mp h), Complex.polarCoord_apply,
        Complex.norm_eq_abs]
  · simp [homeoRealMixedSpacePolarSpace_apply]

variable (K) in
theorem continuous_expMapBasisFull :
    Continuous (expMapBasisFull : mixedSpace K → polarSpace K) := by
  have h₁ : Continuous (expMapBasisFull₀ (K := K)) := sorry
  have h₂ : Continuous (expMapBasisFull₁ (K := K)) := sorry
  have h₃ : Continuous (polarSpaceCoord K) := sorry
  have := Continuous.comp h₂ (Continuous.comp h₃ h₁)
  exact this

theorem expMapBasisFull_symm_apply (x : polarSpace K) :
    expMapBasisFull.symm x = ⟨fun w ↦ expMapBasis x.1 w,
      fun w ↦ Complex.polarCoord.symm (expMapBasis x.1 w, x.2 w)⟩ := rfl

theorem expMapBasisFull_apply' (x : mixedSpace K) :
    expMapBasisFull x = (expMapBasisFull₁ ∘ (homeoRealMixedSpacePolarSpace K) ∘
      (mixedEmbedding.polarCoord K)) (expMapBasisFull₀ x) := rfl

theorem normAtAllPlaces_expMapBasisFull_symm (x : polarSpace K) :
    normAtAllPlaces (expMapBasisFull.symm x) = expMapBasis x.1 := by
  ext w
  rw [normAtAllPlaces_apply, expMapBasisFull_symm_apply]
  obtain hw | hw := isReal_or_isComplex w
  · rw [normAtPlace_apply_of_isReal hw, Real.norm_of_nonneg (expMapBasis_pos _ _).le]
  · rw [normAtPlace_apply_of_isComplex hw, Complex.norm_eq_abs, Complex.polarCoord_symm_abs,
      abs_of_pos (expMapBasis_pos _ _)]

theorem expMapBasisFull_fst {x : mixedSpace K} :
    (expMapBasisFull x).1 = expMapBasis.symm (normAtAllPlaces x) := by
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
      normAtAllPlaces_expMapBasis hx.ne', ← Real.log_nonpos_iff (mixedEmbedding.norm_nonneg x),
      mul_nonpos_iff, h.le, lt_iff_not_le.mp h, true_and, false_and, or_false]

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
  have t1 := completeBasis_repr_eq_unitLatticeBasis_repr (expMap.symm (normAtAllPlaces x))
  have t2 := restMap_expMap_symm_normAtAllPlaces hx
  rw [← t2]
  simp_rw [← t1]
  rfl

variable (K) in
abbrev normLessThanOne : Set (mixedSpace K) :=
  {x | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ 1}

open scoped Classical in
variable (K) in
def paramSet : Set (polarSpace K) :=
  (Set.univ.pi fun w ↦ if w = w₀ then Set.Iic 0 else Set.Ico 0 1) ×ˢ Set.univ

variable (K) in
theorem normLessThanOne_eq :
    normLessThanOne K = expMapBasisFull⁻¹' (paramSet K) := by
  sorry


section integrals

open Real ENNReal

open scoped Classical in
theorem setLIntegral_expMapBasis {s : Set (realSpace K)} (hs₀ : MeasurableSet s)
    (hs₁ : s ⊆ {x | 0 ≤ x w₀}) (f : (InfinitePlace K → ℝ) → ℝ≥0∞) :
    ∫⁻ x in expMapBasis '' s, f x =
      (2 : ℝ≥0∞)⁻¹ ^ nrComplexPlaces K * ENNReal.ofReal (regulator K) * (Module.finrank ℚ K) *
      ∫⁻ x in s, ENNReal.ofReal |x w₀| ^ rank K *
        .ofReal (∏ i : {w : InfinitePlace K // IsComplex w},
          (expMapBasis (fun w ↦ x w) i))⁻¹ * f (expMapBasis x) := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume]
  all_goals sorry

theorem lintegral_eq_lintegral_polarCoord₀_symm (f : mixedSpace K → ℝ≥0∞) :
    ∫⁻ x, f x = ∫⁻ x in (polarSpaceCoord K).target,
      (∏ w : {w // IsComplex w}, .ofReal (x.1 w.val)) * f ((polarSpaceCoord K).symm x) := by
  rw [← mixedEmbedding.lintegral_comp_polarCoord_symm,
    ← (volume_preserving_homeoRealMixedSpacePolarSpace K).setLIntegral_comp_preimage_emb
    (measurableEquivRealMixedSpacePolarSpace K).measurableEmbedding]
  rw [show (mixedEmbedding.polarCoord K).target =
    (homeoRealMixedSpacePolarSpace K) ⁻¹' (polarSpaceCoord K).target by ext; simp]
  congr! with _ _ w
  · simp_rw [homeoRealMixedSpacePolarSpace_apply, dif_neg (not_isReal_iff_isComplex.mpr w.prop)]
  · rw [polarSpaceCoord, PartialHomeomorph.transHomeomorph_symm_apply, Function.comp_apply,
        Homeomorph.symm_apply_apply]

-- open Classical in
-- theorem volume_expMapBasisFull_preimage_set_prod_set {s : Set (realSpace K)}
--     {t : Set ({w : InfinitePlace K // IsComplex w} → ℝ)} :
--     volume (expMapBasisFull⁻¹' (s ×ˢ t)) =
--       volume ((Set.univ.pi fun _ ↦ Set.Ioo (-π) π) ∩ t) * ∫⁻ x in expMapBasis⁻¹' s,
--         ∏ w : {w : InfinitePlace K // IsComplex w}, (x w).toNNReal := by
--   rw [← setLIntegral_one]
--   sorry

open Classical in
theorem volume_plusPart_normLessThanOne : volume (plusPart (normLessThanOne K)) =
    NNReal.pi ^ nrComplexPlaces K * (regulator K).toNNReal := by
  sorry

example : closure (normLessThanOne K) ⊆ expMapBasisFull⁻¹' (closure (paramSet K)) :=
  normLessThanOne_eq K ▸ (continuous_expMapBasisFull K).closure_preimage_subset (paramSet K)

example : expMapBasisFull⁻¹' (interior (paramSet K)) ⊆ interior (normLessThanOne K) :=
  normLessThanOne_eq K ▸ preimage_interior_subset_interior_preimage (continuous_expMapBasisFull K)

example : volume (expMapBasisFull⁻¹' (interior (paramSet K))) =
    volume (expMapBasisFull⁻¹' (closure (paramSet K))) := by

--  refine le_antisymm ?_ ?_
--  · apply measure_mono
--    apply Set.preimage_mono interior_subset_closure

example : volume (interior (normLessThanOne K)) = volume (closure (normLessThanOne K)) := by
  refine le_antisymm (measure_mono interior_subset_closure) ?_

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
