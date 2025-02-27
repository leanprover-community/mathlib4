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

In this file, we study the subset `NormLeOne` of the `fundamentalCone` defined as the
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

namespace NumberField.mixedEmbedding.NormLeOne

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
  · rw [normAtPlace_apply_of_isComplex hw, Complex.norm_of_nonneg hx]

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

variable (K) in
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

variable (K) in
 theorem abs_det_completeBasis_equivFunL_symm :
  |((completeBasis K).equivFunL.symm : realSpace K →L[ℝ] realSpace K).det| =
    Module.finrank ℚ K * regulator K := by
  classical
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (completeBasis K), ← Matrix.det_transpose,
    finrank_mul_regulator_eq_det K w₀ equivFinRank.symm]
  congr 2 with w i
  rw [Matrix.transpose_apply, LinearMap.toMatrix_apply, Matrix.of_apply, ← Basis.equivFunL_apply,
    ContinuousLinearMap.coe_coe, ContinuousLinearEquiv.coe_apply,
    (completeBasis K).equivFunL.apply_symm_apply]
  split_ifs with hw
  · rw [hw, completeBasis_apply_of_eq]
  · rw [completeBasis_apply_of_ne ⟨w, hw⟩, expMap_symm_apply]

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

variable (K) in
theorem injective_expMapBasis :
    Function.Injective (expMapBasis : realSpace K → realSpace K) :=
  (injective_expMap K).comp (completeBasis K).equivFun.symm.injective

theorem expMapBasis_symm_apply (x : realSpace K) :
    expMapBasis.symm x = (completeBasis K).equivFun (expMap.symm x) := by
  simp [expMapBasis]
  rfl

theorem expMapBasis_source :
    expMapBasis.source = (Set.univ : Set (realSpace K)) := by
  simp [expMapBasis, expMap_source]

theorem expMapBasis_target :
    expMapBasis.target = Set.univ.pi fun (_ : InfinitePlace K) ↦ Set.Ioi 0 := rfl

theorem expMapBasis_left_inv (x : realSpace K) :
    expMapBasis.symm (expMapBasis x) = x := by
  rw [expMapBasis.left_inv]
  simp [expMapBasis_source]

theorem expMapBasis_pos (x : realSpace K) (w : InfinitePlace K) :
    0 < expMapBasis x w := expMap_pos _ _

theorem expMapBasis_nonneg (x : realSpace K) (w : InfinitePlace K) :
    0 ≤ expMapBasis x w := (expMap_pos _ _).le

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

-- theorem expMapBasis_symm_normAtAllPlaces {x : mixedSpace K} (hx : mixedEmbedding.norm x ≠ 0) :
--     expMapBasis.symm (normAtAllPlaces x) w₀ =
--       (Module.finrank ℚ K : ℝ)⁻¹ * Real.log (mixedEmbedding.norm x) := by
--   rw [norm_eq_prod_normAtAllPlaces, ← expMapBasis.right_inv (x := normAtAllPlaces x),
--     prod_expMapBasis_pow, expMapBasis.left_inv, Real.log_pow, Real.log_exp, inv_mul_cancel_left₀]
--   · rw [Nat.cast_ne_zero]
--     exact Module.finrank_pos.ne'
--   · rw [expMapBasis_source]
--     trivial
--   · rw [expMapBasis_target]
--     intro w _
--     rw [normAtAllPlaces]
--     rw [mixedEmbedding.norm_ne_zero_iff] at hx
--     specialize hx w
--     refine lt_of_le_of_ne' (normAtPlace_nonneg w x) hx

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

-- open scoped Classical in
-- theorem main (x : realSpace K) (w : {w // w ≠ w₀}) :
--     ((basisUnitLattice K).ofZLatticeBasis ℝ (unitLattice K)).equivFun
--       (logMap (mixedSpaceOfRealSpace (expMapBasis x))) (equivFinRank.symm w) = x w.1 := by
--   rw [expMapBasis_apply'', _root_.map_smul, logMap_real_smul (norm_expMapBasis_ne_zero _)
--     (Real.exp_ne_zero _), expMapBasis_apply, logMap_expMap]
--   · conv_lhs =>
--       enter [2, w]
--       rw [completeBasis_equivFun_symm_apply (by rw [if_pos rfl])]
--     rw [LinearEquiv.apply_symm_apply, Equiv.apply_symm_apply, if_neg w.prop]
--   · rw [← expMapBasis_apply, norm_expMapBasis, if_pos rfl, Real.exp_zero, one_pow]

open ENNReal MeasureTheory.Measure

variable (K) in
abbrev fderiv_expMapBasis (x : realSpace K) : realSpace K →L[ℝ] realSpace K :=
  (fderiv_expMap ((completeBasis K).equivFun.symm x)).comp
    (completeBasis K).equivFunL.symm.toContinuousLinearMap

theorem hasFDerivAt_expMapBasis (x : realSpace K) :
    HasFDerivAt expMapBasis (fderiv_expMapBasis K x) x := by
  change HasFDerivAt (expMap ∘ (completeBasis K).equivFunL.symm) (fderiv_expMapBasis K x) x
  exact (hasFDerivAt_expMap _).comp x (completeBasis K).equivFunL.symm.hasFDerivAt

open scoped Classical in
theorem prod_deriv_expMap_single (x : realSpace K) :
    ∏ w, deriv_expMap_single w ((completeBasis K).equivFun.symm x w) =
      Real.exp (x w₀) ^ Module.finrank ℚ K * (∏ w : {w // IsComplex w}, expMapBasis x w.1)⁻¹ *
        (2⁻¹) ^ nrComplexPlaces K := by
  simp only [deriv_expMap_single, expMap_single_apply]
  rw [Finset.prod_mul_distrib]
  congr 1
  · rw [← prod_expMapBasis_pow, prod_infinitePlaces, prod_infinitePlaces]
    simp_rw [← expMap_apply, ← expMapBasis_apply, mult_ofIsReal, mult_ofIsComplex, pow_one]
    rw [Finset.prod_pow, pow_two, mul_assoc, mul_inv_cancel_right₀]
    exact Finset.prod_ne_zero_iff.mpr <| fun _ _ ↦ (expMapBasis_pos _ _).ne'
  · rw [prod_infinitePlaces]
    simp [mult_ofIsReal, mult_ofIsComplex]

open scoped Classical in
theorem abs_det_fderiv_expMapBasis (x : realSpace K) :
    |(fderiv_expMapBasis K x).det| =
      Real.exp (x w₀ * Module.finrank ℚ K) *
      (∏ w : {w // IsComplex w}, expMapBasis x w.1)⁻¹ * 2⁻¹ ^ nrComplexPlaces K *
      (Module.finrank ℚ K) * regulator K := by
  rw [fderiv_expMapBasis, ContinuousLinearMap.det, ContinuousLinearMap.coe_comp, LinearMap.det_comp]
  rw [fderiv_expMap]
  simp only [ Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, ContinuousLinearMap.coe_pi, ContinuousLinearMap.coe_comp,
    ContinuousLinearEquiv.det_coe_symm]
  erw [LinearMap.det_pi]
  simp only [LinearMap.det_ring, ContinuousLinearMap.coe_coe, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul, one_mul]
  rw [prod_deriv_expMap_single]
  rw [← ContinuousLinearEquiv.det_coe_symm]
  simp_rw [abs_mul]
  rw [abs_det_completeBasis_equivFunL_symm]
  rw [← Real.rpow_natCast, ← Real.exp_mul]
  rw [abs_of_nonneg (by positivity), abs_of_nonneg, abs_of_nonneg (by positivity)]
  · ring
  · exact inv_nonneg.mpr <| Finset.prod_nonneg fun _ _ ↦ (expMapBasis_pos _ _).le

open scoped Classical in
theorem setLIntegral_expMapBasis {s : Set (realSpace K)} (hs : MeasurableSet s)
    {f : (InfinitePlace K → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in expMapBasis '' s, f x =
      (2 : ℝ≥0∞)⁻¹ ^ nrComplexPlaces K * ENNReal.ofReal (regulator K) * (Module.finrank ℚ K) *
      ∫⁻ x in s, ENNReal.ofReal (Real.exp (x w₀ * Module.finrank ℚ K)) *
        (∏ i : {w : InfinitePlace K // IsComplex w},
          .ofReal (expMapBasis (fun w ↦ x w) i))⁻¹ * f (expMapBasis x) := by
  have : Measurable expMapBasis := (continuous_expMapBasis K).measurable
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun x _ ↦ (hasFDerivAt_expMapBasis x).hasFDerivWithinAt) (injective_expMapBasis K).injOn]
  simp_rw [abs_det_fderiv_expMapBasis]
  rw [← lintegral_const_mul _ (by fun_prop)]
  congr with x
  have : 0 ≤ (∏ w : {w // IsComplex w}, expMapBasis x w.1)⁻¹ :=
    inv_nonneg.mpr <| Finset.prod_nonneg fun _ _ ↦ (expMapBasis_pos _ _).le
  rw [ofReal_mul (by positivity), ofReal_mul (by positivity), ofReal_mul (by positivity),
    ofReal_mul (by positivity), ofReal_pow (by positivity), ofReal_inv_of_pos (Finset.prod_pos
    fun _ _ ↦ expMapBasis_pos _ _), ofReal_inv_of_pos zero_lt_two, ofReal_ofNat, ofReal_natCast,
    ofReal_prod_of_nonneg (fun _ _ ↦ (expMapBasis_pos _ _).le)]
  ring

variable (K) in
abbrev normLeOne : Set (mixedSpace K) :=
  {x | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ 1}

variable (K) in
theorem measurableSet_normLeOne :
    MeasurableSet (normLeOne K) :=
  (measurableSet_fundamentalCone K).inter <|
    measurableSet_le (mixedEmbedding.continuous_norm K).measurable measurable_const

open scoped Classical in
variable (K) in
abbrev paramSet : Set (realSpace K) :=
  Set.univ.pi fun w ↦ if w = w₀ then Set.Iic 0 else Set.Ico 0 1

variable (K) in
theorem measurableSet_paramSet :
    MeasurableSet (paramSet K) := by
  refine MeasurableSet.univ_pi fun _ ↦ ?_
  split_ifs
  · exact measurableSet_Iic
  · exact measurableSet_Ico

theorem le_of_mem_paramSet {x : realSpace K} (hx : x ∈ paramSet K) :
    x w₀ ≤ 0 := by
  replace hx := hx w₀ (Set.mem_univ _)
  simpa only [ite_true, Set.mem_Iic] using hx

theorem mem_Ico_of_mem_paramSet {x : realSpace K} (hx : x ∈ paramSet K)
    (w : {w // w ≠ w₀}) :
    x w.1 ∈ Set.Ico 0 1 := by
  replace hx := hx w (Set.mem_univ _)
  simpa only [if_neg w.prop, Set.mem_Iic] using hx

-- def realSpaceNorm (x : realSpace K) : ℝ :=
--     mixedEmbedding.norm (mixedSpaceOfRealSpace x)

-- theorem toto₀ (x : mixedSpace K) {a : realSpace K} :
--     normAtAllPlaces x = expMapBasis a ↔ x = mixedSpaceOfRealSpace (expMapBasis a) := by
--   refine ⟨?_, ?_⟩
--   · intro h
--     rw [← h, mixedSpaceOfRealSpace_apply]
--     sorry
--   · intro h
--     rw [h, normAtAllPlaces_of_nonneg (fun _ ↦ expMapBasis_nonneg _ _)]


-- theorem toto₁ (x : realSpace K) :
--     x ∈ normAtAllPlaces '' (normLeOne K) ↔
--       x ∈ normAtAllPlaces '' (fundamentalCone K) ∧
--         mixedEmbedding.norm (mixedSpaceOfRealSpace x) ≤ 1 := by
--   simp_rw [Set.mem_image, Set.mem_setOf_eq]
--   refine ⟨?_, ?_⟩
--   · rintro ⟨x, ⟨hx₁, hx₂⟩, rfl⟩
--     exact ⟨⟨x, hx₁, rfl⟩, norm_normAtAllPlaces x ▸ hx₂⟩
--   · rintro ⟨⟨x, ⟨hx₁, rfl⟩⟩, hx₂⟩
--     exact ⟨x, ⟨hx₁, norm_normAtAllPlaces x ▸ hx₂⟩, rfl⟩

theorem zap (u : (𝓞 K)ˣ) :
    (fun i ↦ expMap.symm (fun w ↦ w (u : K)) i.1) = logEmbedding K (Additive.ofMul u) := by
  ext
  simp

-- open scoped Classical in
-- theorem toto₀ (x : realSpace K) :
--     x ∈ normAtAllPlaces '' (fundamentalCone K) ↔
--       logMap (mixedSpaceOfRealSpace x) ∈
--         ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ (unitLattice K)) ∧
--         mixedEmbedding.norm (mixedSpaceOfRealSpace x) ≠ 0 := by
--   simp_rw (config := {singlePass := true}) [Set.mem_image, fundamentalCone, Set.mem_diff,
--     Set.mem_preimage, Set.mem_setOf_eq]
--   refine ⟨?_, ?_⟩
--   · rintro ⟨x, hx, rfl⟩
--     rwa [logMap_normAtAllPlaces, norm_normAtAllPlaces]
--   · intro h
--     refine ⟨?_, ?_, ?_⟩

--     sorry

open scoped Classical in
theorem normAtAllPlaces_normLeOne' :
    normAtAllPlaces '' (normLeOne K) = {x | (∀ w, 0 ≤ x w) ∧
      logMap (mixedSpaceOfRealSpace x) ∈
      ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ (unitLattice K)) ∧
      mixedEmbedding.norm (mixedSpaceOfRealSpace x) ≠ 0 ∧
      mixedEmbedding.norm (mixedSpaceOfRealSpace x) ≤ 1} := by
  ext x
  refine ⟨?_, fun ⟨hx₁, hx₂, hx₃, hx₄⟩ ↦ ?_⟩
  · rintro ⟨a, ⟨⟨ha₁, ha₂⟩, ha₃⟩, rfl⟩
    refine ⟨fun w ↦ normAtPlace_nonneg w a, ?_⟩
    exact (logMap_normAtAllPlaces a) ▸ (norm_normAtAllPlaces a) ▸ ⟨ha₁, ha₂, ha₃⟩
  · exact ⟨mixedSpaceOfRealSpace x, ⟨⟨hx₂, hx₃⟩, hx₄⟩, normAtAllPlaces_mixedSpaceOfRealSpace hx₁⟩

open scoped Classical in
theorem logMap_expMapBasis (x : realSpace K) :
    logMap (mixedSpaceOfRealSpace (expMapBasis x)) ∈
        ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ (unitLattice K))
      ↔ ∀ w, w ≠ w₀ → x w ∈ Set.Ico 0 1 := by
  classical
  simp_rw [ZSpan.mem_fundamentalDomain, equivFinRank.forall_congr_left, Subtype.forall]
  refine forall₂_congr fun w hw ↦ ?_
  rw [expMapBasis_apply'', _root_.map_smul, logMap_real_smul (norm_expMapBasis_ne_zero _)
    (Real.exp_ne_zero _), expMapBasis_apply, logMap_expMap (by rw [← expMapBasis_apply,
    norm_expMapBasis, if_pos rfl, Real.exp_zero, one_pow]), Basis.equivFun_symm_apply,
    Fintype.sum_eq_add_sum_fintype_ne _ w₀, if_pos rfl, zero_smul, zero_add]
  conv_lhs =>
    enter [2, 1, 2, w, 2, i]
    rw [if_neg i.prop]
  simp_rw [Finset.sum_apply, ← sum_fn, _root_.map_sum, Pi.smul_apply, ← Pi.smul_def,
    _root_.map_smul, completeBasis_apply_of_ne, zap, logEmbedding_fundSystem,
    Finsupp.coe_finset_sum, Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply,
    Basis.ofZLatticeBasis_repr_apply, Basis.repr_self, Finsupp.single_apply,
    EmbeddingLike.apply_eq_iff_eq, Int.cast_ite, Int.cast_one, Int.cast_zero, smul_ite,
    smul_eq_mul, mul_one, mul_zero, Fintype.sum_ite_eq']

variable (K) in
theorem normAtAllPlaces_normLeOne :
    normAtAllPlaces '' (normLeOne K) = expMapBasis '' (paramSet K) := by
  ext x
  by_cases hx : ∀ w, 0 < x w
  · rw [← expMapBasis.right_inv (Set.mem_univ_pi.mpr hx), (injective_expMapBasis K).mem_set_image]
    simp only [normAtAllPlaces_normLeOne', ne_eq, Set.mem_setOf_eq, expMapBasis_nonneg,
      implies_true, logMap_expMapBasis, norm_expMapBasis, pow_eq_zero_iff', Real.exp_ne_zero,
      false_and, not_false_eq_true, pow_le_one_iff_of_nonneg (Real.exp_nonneg _)
      Module.finrank_pos.ne', Real.exp_le_one_iff, true_and, Set.mem_univ_pi]
    refine ⟨fun ⟨h₁, h₂⟩ w ↦ ?_, fun h ↦ ⟨fun w hw ↦ by simpa [hw] using h w, by simpa using h w₀⟩⟩
    split_ifs with hw
    · exact hw ▸ h₂
    · exact h₁ w hw
  · refine ⟨?_, ?_⟩
    · rintro ⟨a, ⟨ha, _⟩, rfl⟩
      exact (hx fun w ↦ fundamentalCone.normAtPlace_pos_of_mem ha w).elim
    · rintro ⟨a, _, rfl⟩
      exact (hx fun w ↦ expMapBasis_pos a w).elim









theorem toto₂ (x : realSpace K) :
    expMapBasis x ∈ normAtAllPlaces '' (fundamentalCone K) ↔
      ∀ w, w ≠ w₀ → x w ∈ Set.Ico 0 1 := by
  classical
  simp_rw [toto₀, Set.mem_setOf_eq, expMapBasis_nonneg, ne_eq, norm_expMapBasis_ne_zero,
    implies_true, not_false_eq_true, and_true, true_and, ZSpan.mem_fundamentalDomain,
    equivFinRank.forall_congr_left, Subtype.forall]
--  simp_rw [toto₀, ne_eq, norm_expMapBasis_ne_zero, not_false_eq_true, and_true,
--    ZSpan.mem_fundamentalDomain, equivFinRank.forall_congr_left, Subtype.forall]
  -- simp_rw [Set.mem_image, fundamentalCone, Set.mem_diff, Set.mem_preimage, Set.mem_setOf_eq,
  --   toto₀, exists_eq_right,
  --   Set.mem_setOf_eq, norm_expMapBasis_ne_zero, not_false_eq_true, and_true,
  --   ZSpan.mem_fundamentalDomain, equivFinRank.forall_congr_left, Subtype.forall]
  refine forall₂_congr fun w hw ↦ ?_
  rw [expMapBasis_apply'', _root_.map_smul, logMap_real_smul (norm_expMapBasis_ne_zero _)
    (Real.exp_ne_zero _), expMapBasis_apply, logMap_expMap (by rw [← expMapBasis_apply,
    norm_expMapBasis, if_pos rfl, Real.exp_zero, one_pow]), Basis.equivFun_symm_apply,
    Fintype.sum_eq_add_sum_fintype_ne _ w₀, if_pos rfl, zero_smul, zero_add]
  conv_lhs =>
    enter [2, 1, 2, w, 2, i]
    rw [if_neg i.prop]
  simp_rw [Finset.sum_apply, ← sum_fn, _root_.map_sum, Pi.smul_apply, ← Pi.smul_def,
    _root_.map_smul, completeBasis_apply_of_ne, zap, logEmbedding_fundSystem,
    Finsupp.coe_finset_sum, Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply,
    Basis.ofZLatticeBasis_repr_apply, Basis.repr_self, Finsupp.single_apply,
    EmbeddingLike.apply_eq_iff_eq, Int.cast_ite, Int.cast_one, Int.cast_zero, smul_ite,
    smul_eq_mul, mul_one, mul_zero, Fintype.sum_ite_eq']

theorem toto₃ (x : realSpace K) :
    mixedEmbedding.norm (mixedSpaceOfRealSpace (expMapBasis x)) ≤ 1 ↔ x w₀ ≤ 0 := by
  sorry
--  rw [realSpaceNorm, mixedEmbedding.norm_apply]
--  simp_rw [normAtPlace_mixedSpaceOfRealSpace sorry]
--  rw [prod_expMapBasis_pow]
--  sorry

variable (K) in
theorem normAtAllPlaces_normLeOne :
    normAtAllPlaces '' (normLeOne K) = expMapBasis '' (paramSet K) := by
  ext x
  by_cases hx : ∀ w, 0 < x w
  · replace hx : x = expMapBasis (expMapBasis.symm x) := by
      rw [expMapBasis.right_inv]
      rw [expMapBasis_target, Set.mem_univ_pi]
      exact hx
    rw [toto₁, hx, toto₂, toto₃, Function.Injective.mem_set_image, paramSet, Set.mem_univ_pi]
    · refine ⟨?_, ?_⟩
      · intro ⟨h₁, h₂⟩ w
        split_ifs with h
        · rwa [h]
        · exact h₁ w h
      · intro h
        refine ⟨?_, ?_⟩
        · intro w hw
          simpa [hw] using h w
        · simpa using h w₀
    · exact injective_expMapBasis K
  · refine ⟨?_, ?_⟩
    · rintro ⟨a, ⟨ha, _⟩, rfl⟩
      exact (hx fun w ↦ fundamentalCone.normAtPlace_pos_of_mem ha w).elim
    · rintro ⟨a, _, rfl⟩
      exact (hx fun w ↦ expMapBasis_pos a w).elim

-- variable (K) in
-- theorem normAtAllPlaces_normLeOne :
--     normAtAllPlaces '' (normLeOne K) = expMapBasis '' (paramSet K) := by
--   classical
--   ext a
--   simp only [Set.mem_image, Set.mem_setOf_eq, fundamentalCone, Set.mem_diff, Set.mem_preimage,
--     ZSpan.mem_fundamentalDomain, equivFinRank.forall_congr_left]
--   refine ⟨?_, ?_⟩
--   · rintro ⟨x, ⟨⟨hx₁, hx₂⟩, hx₃⟩, rfl⟩
--     have hx₄ : normAtAllPlaces x ∈ expMapBasis.target :=
--       fun w _ ↦ lt_of_le_of_ne' (normAtPlace_nonneg w x) (mixedEmbedding.norm_ne_zero_iff.mp hx₂ w)
--     refine ⟨?_, ?_, ?_⟩
--     · exact expMapBasis.symm (normAtAllPlaces x)
--     · intro w _
--       by_cases hw : w = w₀
--       · simp_rw [hw, expMapBasis_symm_normAtAllPlaces hx₂, if_true, Set.mem_Iic]
--         have : 0 < (Module.finrank ℚ K : ℝ)⁻¹ :=
--           inv_pos.mpr <| Nat.cast_pos.mpr Module.finrank_pos
--         simpa [mul_nonpos_iff_pos_imp_nonpos, this,
--           Real.log_nonpos_iff (mixedEmbedding.norm_nonneg _)] using hx₃
--       · rw [← main (expMapBasis.symm (normAtAllPlaces x)) ⟨w, hw⟩, expMapBasis.right_inv hx₄,
--           logMap_normAtAllPlaces]
--         simp_rw [if_neg hw]
--         exact hx₁ _
--     · rw [expMapBasis.right_inv hx₄]
--   · rintro ⟨x, hx, rfl⟩
--     refine ⟨mixedSpaceOfRealSpace (expMapBasis x), ⟨⟨?_, norm_expMapBasis_ne_zero x⟩, ?_⟩, ?_⟩
--     · intro w
--       simp_rw [← Basis.equivFun_apply, main]
--       exact mem_Ico_of_mem_paramSet hx w
--     · rw [norm_expMapBasis]
--       refine (pow_le_one_iff_of_nonneg ?_ ?_).mpr ?_
--       · exact Real.exp_nonneg _
--       · exact Module.finrank_pos.ne'
--       · rw [Real.exp_le_one_iff]
--         exact le_of_mem_paramSet hx
--     · ext
--       rw [normAtAllPlaces_apply, normAtPlace_mixedSpaceOfRealSpace]
--       exact (expMapBasis_pos _ _).le

theorem mem_normLeOne_iff (x : mixedSpace K):
    x ∈ normLeOne K ↔ mixedSpaceOfRealSpace (normAtAllPlaces x) ∈ normLeOne K := by
  simp only [normLeOne, Set.mem_setOf_eq, normAtAllPlaces_mem_fundamentalCone_iff,
    norm_normAtAllPlaces]

variable (K)

theorem normLeOne_eq_primeage_image :
    normLeOne K = normAtAllPlaces⁻¹' (normAtAllPlaces '' (normLeOne K)) :=
  mem_iff_normAtAllPlaces_mem_iff.mp fun x ↦ mem_normLeOne_iff x

theorem normLeOne_eq :
    normLeOne K = normAtAllPlaces⁻¹' (expMapBasis '' (paramSet K)) := by
  rw [normLeOne_eq_primeage_image, normAtAllPlaces_normLeOne]

open scoped Classical in
theorem closure_paramSet :
    closure (paramSet K) = Set.univ.pi fun w ↦ if w = w₀ then Set.Iic 0 else Set.Icc 0 1 := by
  simp [closure_pi_set, apply_ite]

open scoped Classical in
theorem interior_paramSet :
    interior (paramSet K) = Set.univ.pi fun w ↦ if w = w₀ then Set.Iio 0 else Set.Ioo 0 1 := by
  simp [interior_pi_set Set.finite_univ, apply_ite]

theorem closure_paramSet_eq_interior :
  closure (paramSet K) =ᵐ[volume] interior (paramSet K) := by
  rw [closure_paramSet, interior_paramSet, volume_pi]
  refine ae_eq_set_pi fun w _ ↦ ?_
  split_ifs
  · exact Iio_ae_eq_Iic.symm
  · exact Ioo_ae_eq_Icc.symm

theorem measurableSet_interior_paramSet :
    MeasurableSet (interior (paramSet K)) := by
  rw [interior_paramSet]
  refine MeasurableSet.univ_pi fun _ ↦ ?_
  split_ifs
  · exact measurableSet_Iio
  · exact measurableSet_Ioo

open Pointwise Bornology

open scoped Classical in
abbrev compactSet : Set (realSpace K) :=
  (Set.Icc (0 : ℝ) 1) • (expMapBasis '' Set.univ.pi fun w ↦ if w = w₀ then {0} else Set.Icc 0 1)

theorem isCompact_compactSet :
    IsCompact (compactSet K) := by
  refine isCompact_Icc.smul_set <| (isCompact_univ_pi fun w ↦ ?_).image_of_continuousOn
    (continuous_expMapBasis K).continuousOn
  split_ifs
  · exact isCompact_singleton
  · exact isCompact_Icc

theorem nonneg_of_mem_compactSet {x : realSpace K} (hx : x ∈ compactSet K) (w : InfinitePlace K) :
    0 ≤ x w := by
  obtain ⟨c, hc, ⟨_, ⟨⟨a, ha, rfl⟩, _, rfl⟩⟩⟩ := hx
  exact mul_nonneg hc.1 (expMapBasis_pos _ _).le

theorem compactSet_eq_union :
    compactSet K = (expMapBasis '' closure (paramSet K)) ∪ {0} := by
  classical
  ext x
  by_cases hx₀ : x = 0
  · simp only [hx₀, Set.union_singleton, Set.mem_insert_iff, Set.mem_image, true_or, iff_true]
    refine Set.zero_mem_smul_iff.mpr (Or.inl ?_)
    exact ⟨Set.left_mem_Icc.mpr zero_le_one,
      Set.image_nonempty.mpr (Set.univ_pi_nonempty_iff.mpr (by aesop))⟩
  · simp only [Set.union_singleton, Set.mem_insert_iff, hx₀, false_or, closure_paramSet,
      Set.mem_image, Set.mem_smul]
    refine ⟨?_, ?_⟩
    · rintro ⟨c, hc, ⟨_, ⟨⟨x, hx, rfl⟩, rfl⟩⟩⟩
      refine ⟨fun w ↦ if w = w₀ then Real.log c else x w, ?_, ?_⟩
      · refine Set.mem_univ_pi.mpr fun w ↦ ?_
        split_ifs with h
        · exact (Real.log_nonpos_iff hc.1).mpr hc.2
        · simpa [if_neg h] using hx w (Set.mem_univ _)
      · have hc : 0 < c := by
          contrapose! hx₀
          rw [le_antisymm hx₀ hc.1, zero_smul]
        rw [expMapBasis_apply'', if_pos rfl, Real.exp_log hc]
        congr with w
        split_ifs with h
        · simpa [h, eq_comm] using hx w₀ (Set.mem_univ _)
        · rfl
    · rintro ⟨x, hx, rfl⟩
      refine ⟨Real.exp (x w₀), ?_, expMapBasis fun i ↦ if i = w₀ then 0 else x i, ?_, ?_⟩
      · simpa [Real.exp_nonneg] using hx w₀ (Set.mem_univ _)
      · refine ⟨_, fun w ↦ ?_, rfl⟩
        by_cases hw : w = w₀
        · simp [hw]
        · simpa [hw] using hx w (Set.mem_univ _)
      · rw [expMapBasis_apply'' x]

theorem expMapBasis_closure_subset_compactSet :
    expMapBasis '' closure (paramSet K) ⊆ compactSet K := by
  rw [compactSet_eq_union]
  exact Set.subset_union_left

theorem compactSet_ae :
    compactSet K =ᵐ[volume] expMapBasis '' closure (paramSet K) := by
  rw [compactSet_eq_union]
  exact union_ae_eq_left_of_ae_eq_empty (by simp)

theorem isBounded_normLeOne :
    Bornology.IsBounded (normLeOne K) := by
  classical
  rw [normLeOne_eq]
  suffices IsBounded (expMapBasis '' paramSet K) by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp this
    refine isBounded_iff_forall_norm_le.mpr ⟨C, fun x hx ↦ ?_⟩
    rw [norm_eq_sup'_normAtPlace]
    refine Finset.sup'_le _ _ fun w _ ↦ ?_
    simpa [normAtAllPlaces_apply, Real.norm_of_nonneg (normAtPlace_nonneg w x)]
      using (pi_norm_le_iff_of_nonempty _).mp (hC _ hx) w
  refine IsBounded.subset ?_ (Set.image_mono subset_closure)
  exact (isCompact_compactSet K).isBounded.subset (expMapBasis_closure_subset_compactSet K)

theorem closure_normLeOne_subset :
    closure (normLeOne K) ⊆ normAtAllPlaces⁻¹' (compactSet K) := by
  rw [normLeOne_eq]
  refine ((continuous_normAtAllPlaces K).closure_preimage_subset _).trans (Set.preimage_mono ?_)
  refine (isCompact_compactSet K).isClosed.closure_subset_iff.mpr ?_
  exact (Set.image_mono subset_closure).trans (expMapBasis_closure_subset_compactSet _)

theorem subset_interior_normLeOne :
    normAtAllPlaces⁻¹' (expMapBasis '' interior (paramSet K)) ⊆ interior (normLeOne K) := by
  rw [normLeOne_eq]
  refine subset_trans (Set.preimage_mono ?_)
    <| preimage_interior_subset_interior_preimage (continuous_normAtAllPlaces K)
  have : IsOpen (expMapBasis '' (interior (paramSet K))) :=
    expMapBasis.isOpen_image_of_subset_source isOpen_interior (by simp [expMapBasis_source])
  exact interior_maximal (Set.image_mono interior_subset) this

theorem normAtAllPlaces_image_preimage_expMapBasis (s : Set (realSpace K)) :
    normAtAllPlaces '' (normAtAllPlaces ⁻¹' (expMapBasis '' s)) = expMapBasis '' s := by
  apply normAtAllPlaces_image_preimage_of_nonneg
  rintro _ ⟨x, _, rfl⟩ w
  exact (expMapBasis_pos _ _).le

theorem lintegral_paramSet_exp {n : ℕ} (hn : 0 < n) :
    ∫⁻ (x : realSpace K) in paramSet K, .ofReal (Real.exp (x w₀ * n)) = (n : ℝ≥0∞)⁻¹ := by
  classical
  rw [volume_pi, paramSet, Measure.restrict_pi_pi, lintegral_eq_lmarginal_univ 0,
    lmarginal_erase' _ (by fun_prop) (Finset.mem_univ w₀), if_pos rfl]
  simp_rw [Function.update_self, lmarginal, lintegral_const, Measure.pi_univ, if_neg
    (Finset.ne_of_mem_erase (Subtype.prop _)), restrict_apply_univ, Real.volume_Ico, sub_zero,
    ofReal_one, prod_const_one, mul_one]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [← setIntegral_congr_set Iio_ae_eq_Iic, integral_comp_mul_right_Iio _ _
      (Nat.cast_pos.mpr hn), zero_mul, setIntegral_congr_set Iio_ae_eq_Iic, integral_exp_Iic,
      Real.exp_zero, smul_eq_mul, mul_one, ofReal_inv_of_pos (Nat.cast_pos.mpr hn), ofReal_natCast]
  · rw [← IntegrableOn, integrableOn_Iic_iff_integrableOn_Iio, integrableOn_Iio_comp_mul_right_iff _
      _ (Nat.cast_pos.mpr hn), zero_mul, ← integrableOn_Iic_iff_integrableOn_Iio]
    exact integrableOn_exp_Iic 0
  · filter_upwards with _ using Real.exp_nonneg _

open scoped Classical in
theorem volume_normLeOne : volume (normLeOne K) =
    2 ^ nrRealPlaces K * NNReal.pi ^ nrComplexPlaces K * .ofReal (regulator K) := by
  rw [volume_eq_two_pow_mul_two_pi_pow_mul_integral (fun x ↦ mem_normLeOne_iff x)
    (measurableSet_normLeOne K), normLeOne_eq, normAtAllPlaces_image_preimage_expMapBasis,
    setLIntegral_expMapBasis (measurableSet_paramSet K) (by fun_prop)]
  simp_rw [ENNReal.inv_mul_cancel_right
    (Finset.prod_ne_zero_iff.mpr fun _ _ ↦ ofReal_ne_zero_iff.mpr (expMapBasis_pos _ _))
    (prod_ne_top fun _ _ ↦ ofReal_ne_top)]
  rw [lintegral_paramSet_exp _ Module.finrank_pos, ofReal_mul zero_le_two, mul_pow, ofReal_ofNat,
    ENNReal.mul_inv_cancel_right (Nat.cast_ne_zero.mpr Module.finrank_pos.ne') (natCast_ne_top _),
    coe_nnreal_eq, NNReal.coe_real_pi, mul_mul_mul_comm, ← ENNReal.inv_pow, ← mul_assoc,
    ← mul_assoc, ENNReal.inv_mul_cancel_right (pow_ne_zero _ two_ne_zero)
    (pow_ne_top ENNReal.ofNat_ne_top)]

open scoped Classical in
theorem volume_interior_eq_volume_closure :
    volume (interior (normLeOne K)) = volume (closure (normLeOne K)) := by
  have h₁ : MeasurableSet (normAtAllPlaces ⁻¹' compactSet K) :=
    (isCompact_compactSet K).measurableSet.preimage (continuous_normAtAllPlaces K).measurable
  have h₂ :  MeasurableSet (normAtAllPlaces ⁻¹' (↑expMapBasis '' interior (paramSet K))) := by
    refine MeasurableSet.preimage ?_ (continuous_normAtAllPlaces K).measurable
    refine MeasurableSet.image_of_continuousOn_injOn ?_ (continuous_expMapBasis K).continuousOn
      (injective_expMapBasis K).injOn
    exact measurableSet_interior_paramSet K
  refine le_antisymm (measure_mono interior_subset_closure) ?_
  refine (measure_mono (closure_normLeOne_subset K)).trans ?_
  refine le_of_eq_of_le ?_ (measure_mono (subset_interior_normLeOne K))
  rw [volume_eq_two_pow_mul_two_pi_pow_mul_integral (forall_mem_iff_normAtAllPlaces_mem rfl) h₁,
    normAtAllPlaces_image_preimage_of_nonneg (fun x a w ↦ nonneg_of_mem_compactSet K a w),
    volume_eq_two_pow_mul_two_pi_pow_mul_integral (forall_mem_iff_normAtAllPlaces_mem rfl) h₂,
    normAtAllPlaces_image_preimage_expMapBasis, setLIntegral_congr (compactSet_ae K),
    setLIntegral_expMapBasis measurableSet_closure (by fun_prop),
    setLIntegral_expMapBasis measurableSet_interior (by fun_prop),
    setLIntegral_congr (closure_paramSet_eq_interior K)]

open scoped Classical in
theorem volume_frontier :
     volume (frontier (normLeOne K)) = 0 := by
  rw [frontier, measure_diff, volume_interior_eq_volume_closure, tsub_self]
  · exact interior_subset_closure
  · exact measurableSet_interior.nullMeasurableSet
  · rw [← lt_top_iff_ne_top]
    refine lt_of_le_of_lt (measure_mono interior_subset) ?_
    rw [volume_normLeOne]
    exact Batteries.compareOfLessAndEq_eq_lt.mp rfl


#exit






variable (K) in
open scoped Classical in
theorem aux₂ : (Set.Icc (0 : ℝ) 1) •
      (expMapBasis '' Set.univ.pi
        fun w : InfinitePlace K ↦ if w = w₀ then {0} else Set.Icc 0 1) ⊆
    (expMapBasis ''  Set.univ.pi fun w ↦ if w = w₀ then Set.Iio 0 else Set.Icc 0 1) ∪ {0} := by
  rintro _ ⟨c, ⟨hc, ⟨_, ⟨x, hx, rfl⟩, rfl⟩⟩⟩
  dsimp only
  by_cases h : c = 0
  · sorry
  · left
    refine ⟨fun w ↦ if w = w₀ then Real.log c else x w, ?_, ?_⟩
    sorry
    rw [expMapBasis_apply'', if_pos rfl, Real.exp_log (lt_of_le_of_ne' hc.1 h)]
    · congr with w
      split_ifs with h
      · simpa [h, eq_comm] using hx w₀ (Set.mem_univ w₀)
      · rfl

theorem aux₄ (s : Set (realSpace K)) :
    normAtAllPlaces '' (normAtAllPlaces⁻¹' (s ∪ {0})) =ᵐ[volume]
      normAtAllPlaces '' (normAtAllPlaces⁻¹' s) := sorry

variable (K) in
open scoped Classical in
theorem aux₃ :
    interior (paramSet K) =ᵐ[volume]
      Set.univ.pi fun w ↦ if w = w₀ then Set.Iio 0 else Set.Icc 0 1 := by
  set A : Set (realSpace K) :=
    Set.univ.pi fun w : InfinitePlace K ↦ if w = w₀ then Set.Iio 0 else Set.Icc 0 1 with A_def
  rw [show interior (paramSet K) = interior A by
    rw [A_def, interior_paramSet]
    rw [interior_pi_set Set.finite_univ]
    congr with i
    simp only [Set.mem_pi, Set.mem_univ, forall_const]
    sorry]
  refine interior_ae_eq_of_null_frontier ?_
  refine Convex.addHaar_frontier volume ?_
  rw [A_def]
  refine convex_pi fun _ _ ↦ ?_
  split_ifs
  · exact convex_Iio 0
  · exact convex_Icc 0 1

open scoped Classical in
example : volume (interior (normLeOne K)) = volume (closure (normLeOne K)) := by
  refine le_antisymm ?_ ?_
  · apply measure_mono
    exact interior_subset_closure
  · refine (measure_mono (aux₁ K)).trans ?_
    refine (measure_mono (Set.preimage_mono (aux₂ K))).trans ?_
    rw [normLeOne_eq]
    refine le_trans ?_ (measure_mono (preimage_interior_subset_interior_preimage ?_))
    have : expMapBasis '' (interior (paramSet K)) ⊆ interior (expMapBasis '' paramSet K) := sorry
    refine le_trans ?_ (measure_mono (Set.preimage_mono this))
    refine le_of_eq ?_
    rw [volume_eq_two_pow_mul_two_pi_pow_mul_integral,
      volume_eq_two_pow_mul_two_pi_pow_mul_integral]
    congr 1
    rw [setLIntegral_congr (aux₄ _)]
    rw [normAtAllPlaces_image_preimage_expMapBasis, normAtAllPlaces_image_preimage_expMapBasis]





    sorry



#exit

      fun w : InfinitePlace K ↦ if w = w₀ then Set.Iio 0 else Set.Icc 0 1) := by
    sorry
  rw [interior_paramSet]
  rw [ae_eq_set]
  constructor
  · rw?
    sorry
  · sorry

open scoped Classical in
example : volume (normAtAllPlaces⁻¹'
    (expMapBasis ''  Set.univ.pi
      fun w : InfinitePlace K ↦ if w = w₀ then Set.Iio 0 else Set.Icc 0 1)) = 1 := by
  rw [volume_eq_two_pow_mul_two_pi_pow_mul_integral, normAtAllPlaces_image_preimage_expMapBasis,
    setLIntegral_expMapBasis]
  simp_rw [ENNReal.inv_mul_cancel_right
    (Finset.prod_ne_zero_iff.mpr fun _ _ ↦ ofReal_ne_zero_iff.mpr (expMapBasis_pos _ _))
    (prod_ne_top fun _ _ ↦ ofReal_ne_top)]
  rw [lintegral_paramSet_exp _ Module.finrank_pos]

#exit
  rw [volume_eq_two_pow_mul_two_pi_pow_mul_integral (fun x ↦ mem_normLeOne_iff x)
    (measurableSet_normLeOne K), normLeOne_eq, normAtAllPlaces_image_preimage_expMapBasis,
    setLIntegral_expMapBasis (measurableSet_paramSet K) (by fun_prop)]
  simp_rw [ENNReal.inv_mul_cancel_right
    (Finset.prod_ne_zero_iff.mpr fun _ _ ↦ ofReal_ne_zero_iff.mpr (expMapBasis_pos _ _))
    (prod_ne_top fun _ _ ↦ ofReal_ne_top)]
  rw [lintegral_paramSet_exp _ Module.finrank_pos, ofReal_mul zero_le_two, mul_pow, ofReal_ofNat,
    ENNReal.mul_inv_cancel_right (Nat.cast_ne_zero.mpr Module.finrank_pos.ne') (natCast_ne_top _),
    coe_nnreal_eq, NNReal.coe_real_pi, mul_mul_mul_comm, ← ENNReal.inv_pow, ← mul_assoc,
    ← mul_assoc, ENNReal.inv_mul_cancel_right (pow_ne_zero _ two_ne_zero)
    (pow_ne_top ENNReal.ofNat_ne_top)]






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

end NumberField.mixedEmbedding.NormLeOne
