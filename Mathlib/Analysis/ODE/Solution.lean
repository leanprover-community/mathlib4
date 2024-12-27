/-
Copyright (c) 2024 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Topology.MetricSpace.Contracting

-- remember to fix copyright

/-!
Attempt to unify `Gronwall` and `PicardLindelof` and prepare for `LocalFlow`

Strategy:
* Define new structure `ODESolution v t₀ s x₀` which contains local solutions to the vector field
  `v`.
* Show that under certain conditions, `ODESolution v t₀ s x₀` is equivalent to satisfying an
  integral equation.
* All properties of solutions will be proved using `ODESolution`, rather than extracting `f` from
  `v` every time. <-- this is the key motivation
* Initially, we keep using coercion from `PicardLindelofData` to `ℝ → E → E`, but at some point we
  restrict ourselves to `C^p` vector fields

To consider:
* Time-independent `ODESolution`? Show equivalence?
* Not strictly a generalisation of `PicardLindelof` in cases of closed intervals (how to reconcile?)

-/

open Function Metric Set
open scoped NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-
equivalent integral equation
remark p.67
-/
noncomputable def iterateIntegral (f : ℝ → E → E) (t₀ : ℝ) (x₀ : E) (α : ℝ → E) : ℝ → E :=
  fun t ↦ x₀ + ∫ τ in t₀..t, f τ (α τ)

@[simp]
lemma iterateIntegral_apply {f : ℝ → E → E} {α : ℝ → E} {t₀ : ℝ} {x₀ : E} {t : ℝ} :
    iterateIntegral f t₀ x₀ α t = x₀ + ∫ τ in t₀..t, f τ (α τ) := rfl

-- `fun t ↦ f t (α t)` is C^n if `f` and `α` are C^n
-- rename! this is more general than `Ioo`
lemma contDiffOn_curve_comp {f : ℝ → E → E} {α : ℝ → E} {u : Set E}
    {s : Set ℝ} {n : WithTop ℕ∞}
    (hf : ContDiffOn ℝ n (uncurry f) (s ×ˢ u))
    (hα : ContDiffOn ℝ n α s)
    (hmem : ∀ t ∈ s, α t ∈ u) :
    ContDiffOn ℝ n (fun t ↦ f t (α t)) s := by
  have : (fun t ↦ f t (α t)) = (uncurry f) ∘ fun t ↦ (t, α t) := rfl
  rw [this]
  apply hf.comp <| contDiffOn_id.prod hα
  intro _ ht
  rw [mem_prod]
  exact ⟨ht, hmem _ ht⟩

-- rename!
lemma continuousOn_curve_comp {f : ℝ → E → E} {α : ℝ → E} {u : Set E}
    {s : Set ℝ}
    (hf : ContinuousOn (uncurry f) (s ×ˢ u))
    (hα : ContinuousOn α s)
    (hmem : ∀ t ∈ s, α t ∈ u) :
    ContinuousOn (fun t ↦ f t (α t)) s :=
  contDiffOn_zero.mp <| contDiffOn_curve_comp (contDiffOn_zero.mpr hf) (contDiffOn_zero.mpr hα) hmem

-- the integral equation has derivative `fun t ↦ f t (α t)`
-- TODO: generalise to any convex `s`
lemma hasDerivAt_iterateIntegral_Ioo [CompleteSpace E] (f : ℝ → E → E) (α : ℝ → E) {u : Set E}
    {tmin tmax t₀ : ℝ}
    (hf : ContinuousOn (uncurry f) ((Ioo tmin tmax) ×ˢ u))
    (ht₀ : t₀ ∈ Ioo tmin tmax) (hα : ContinuousOn α (Ioo tmin tmax))
    (hmem : ∀ t ∈ Ioo tmin tmax, α t ∈ u) (x₀ : E)
    {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    HasDerivAt (iterateIntegral f t₀ x₀ α) (f t (α t)) t := by
  unfold iterateIntegral
  apply HasDerivAt.const_add
  apply intervalIntegral.integral_hasDerivAt_right -- need `CompleteSpace E`
  · apply ContinuousOn.intervalIntegrable
    apply continuousOn_curve_comp hf hα hmem |>.mono
    by_cases h : t < t₀
    · rw [uIcc_of_gt h]
      exact Icc_subset_Ioo ht.1 ht₀.2
    · rw [uIcc_of_le (not_lt.mp h)]
      exact Icc_subset_Ioo ht₀.1 ht.2
  · exact continuousOn_curve_comp hf hα hmem |>.stronglyMeasurableAtFilter isOpen_Ioo _ ht
  · exact continuousOn_curve_comp hf hα hmem |>.continuousAt <| Ioo_mem_nhds ht.1 ht.2

-- code duplication with `Ioo` case above
lemma hasDerivWithinAt_iterateIntegral_Icc [CompleteSpace E] (f : ℝ → E → E) (α : ℝ → E) {u : Set E}
    {tmin tmax t₀ : ℝ}
    (hf : ContinuousOn (uncurry f) ((Icc tmin tmax) ×ˢ u))
    (ht₀ : t₀ ∈ Icc tmin tmax) (hα : ContinuousOn α (Icc tmin tmax))
    (hmem : ∀ t ∈ Icc tmin tmax, α t ∈ u) (x₀ : E)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    HasDerivWithinAt (iterateIntegral f t₀ x₀ α) (f t (α t)) (Icc tmin tmax) t := by
  unfold iterateIntegral
  apply HasDerivWithinAt.const_add
  have : Fact (t ∈ Icc tmin tmax) := ⟨ht⟩ -- needed to synthesise FTCFilter for Icc
  apply intervalIntegral.integral_hasDerivWithinAt_right -- need `CompleteSpace E`
  · apply ContinuousOn.intervalIntegrable
    apply continuousOn_curve_comp hf hα hmem |>.mono
    by_cases h : t < t₀
    · rw [uIcc_of_gt h]
      exact Icc_subset_Icc ht.1 ht₀.2
    · rw [uIcc_of_le (not_lt.mp h)]
      exact Icc_subset_Icc ht₀.1 ht.2
  · exact continuousOn_curve_comp hf hα hmem
      |>.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t
  · exact continuousOn_curve_comp hf hα hmem _ ht

lemma deriv_iterateIntegral [CompleteSpace E] (f : ℝ → E → E) (α : ℝ → E) {u : Set E}
    {tmin tmax t₀ : ℝ}
    (hf : ContinuousOn (uncurry f) ((Ioo tmin tmax) ×ˢ u))
    (ht₀ : t₀ ∈ Ioo tmin tmax) (hα : ContinuousOn α (Ioo tmin tmax))
    (hmem : ∀ t ∈ Ioo tmin tmax, α t ∈ u) (x₀ : E)
    {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    deriv (iterateIntegral f t₀ x₀ α) t = f t (α t) := by
  -- use FTC2 `intervalIntegral.deriv_integral_right`
  unfold iterateIntegral -- add _eq lemma
  rw [deriv_const_add']
  -- code duplication below this
  apply intervalIntegral.deriv_integral_right
  · apply ContinuousOn.intervalIntegrable
    apply continuousOn_curve_comp hf hα hmem |>.mono
    by_cases h : t < t₀
    · rw [uIcc_of_gt h]
      exact Icc_subset_Ioo ht.1 ht₀.2
    · rw [uIcc_of_le (not_lt.mp h)]
      exact Icc_subset_Ioo ht₀.1 ht.2
  · exact continuousOn_curve_comp hf hα hmem |>.stronglyMeasurableAtFilter isOpen_Ioo _ ht
  · exact continuousOn_curve_comp hf hα hmem |>.continuousAt <| Ioo_mem_nhds ht.1 ht.2

-- the integral equation transfers smoothness class from `f` to `α`
-- TODO: generalise `n` to `∞` and maybe `ω`
lemma contDiffOn_nat_iterateIntegral_Ioo [CompleteSpace E] (f : ℝ → E → E) (α : ℝ → E) {u : Set E}
    {tmin tmax t₀ : ℝ} {n : ℕ}
    (hf : ContDiffOn ℝ n (uncurry f) ((Ioo tmin tmax) ×ˢ u))
    (ht₀ : t₀ ∈ Ioo tmin tmax) (hα : ContinuousOn α (Ioo tmin tmax))
    (hmem : ∀ t ∈ Ioo tmin tmax, α t ∈ u) (x₀ : E)
    (heqon : ∀ t ∈ Ioo tmin tmax, α t = iterateIntegral f t₀ x₀ α t) :
    ContDiffOn ℝ n (iterateIntegral f t₀ x₀ α) (Ioo tmin tmax) := by
  induction n with
  | zero =>
    simp only [CharP.cast_eq_zero, contDiffOn_zero] at *
    apply HasDerivAt.continuousOn (f' := fun t ↦ f t (α t))
    intro _ ht
    exact hasDerivAt_iterateIntegral_Ioo f α hf ht₀ hα hmem x₀ ht
  | succ n hn =>
    simp only [Nat.cast_add, Nat.cast_one] at *
    rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo] -- check this for generalisation to `ω`
    refine ⟨?_, by simp, ?_⟩
    · intro _ ht
      apply DifferentiableAt.differentiableWithinAt
      exact HasDerivAt.differentiableAt <|
        hasDerivAt_iterateIntegral_Ioo f α hf.continuousOn ht₀ hα hmem x₀ ht
    · have hα' : ContDiffOn ℝ n α (Ioo tmin tmax) := by
        apply ContDiffOn.congr _ heqon
        apply hn
        exact hf.of_succ
      apply contDiffOn_curve_comp hf.of_succ hα' hmem |>.congr
      intro _ ht
      exact deriv_iterateIntegral f α hf.continuousOn ht₀ hα hmem x₀ ht

lemma contDiffOn_enat_iterateIntegral_Ioo [CompleteSpace E] (f : ℝ → E → E) (α : ℝ → E) {u : Set E}
    {tmin tmax t₀ : ℝ} {n : ℕ∞}
    (hf : ContDiffOn ℝ n (uncurry f) ((Ioo tmin tmax) ×ˢ u))
    (ht₀ : t₀ ∈ Ioo tmin tmax) (hα : ContinuousOn α (Ioo tmin tmax))
    (hmem : ∀ t ∈ Ioo tmin tmax, α t ∈ u) (x₀ : E)
    (heqon : ∀ t ∈ Ioo tmin tmax, α t = iterateIntegral f t₀ x₀ α t) :
    ContDiffOn ℝ n (iterateIntegral f t₀ x₀ α) (Ioo tmin tmax) := by
  induction n with
  | top =>
    rw [contDiffOn_infty] at *
    intro k
    exact contDiffOn_nat_iterateIntegral_Ioo _ _ (hf k) ht₀ hα hmem x₀ heqon
  | coe n =>
    simp only [WithTop.coe_natCast] at *
    exact contDiffOn_nat_iterateIntegral_Ioo _ _ hf ht₀ hα hmem _ heqon

-- generalise to `ω`?

/-
prop 1.1 existence of local flow

J : open interval of ℝ containing 0
  `Ioo tmin tmax` containing 0 (generalise to `t₀`?)
U : open in banach space E containing x₀
  `u ∈ 𝓝 x₀`
  but here this is implied by `closedBall x₀ (3 * a) ⊆ u`
  why `0 < a < 1`?
f : J × U → E continuous, K-lipschitz
  `f : ℝ → E → E` with `ContinuousOn (uncurry f) (J × U)`,
  `∀ t ∈ J, LipschitzOnWith (f t) u K`
a : ℝ so that `closedBall x₀ (3 * a) ⊆ u`
b : ℝ so that eventually we get integral curve α : Ioo (-b) b → E
  `b = (tmax - tmin) / 2`
α : α_x (t) is the integral curve starting at x
  `α : E → ℝ → E` with `α x t` meaning `α x` is an integral curve starting at `x`
-/


-- [MetricSpace α] → ContractingWith K f → [inst_1 : Nonempty α] → [inst : CompleteSpace α] → α



/-- The type of continuous maps  -/
-- change order of arguments
-- no need to extend `ContinuousMapClass` because this is a one-time use
@[ext]
structure SpaceOfCurves (x₀ : E) {t₀ tmin tmax : ℝ} (ht : t₀ ∈ Icc tmin tmax) -- need compact domain
    (a : ℝ≥0) extends C(Icc tmin tmax, E) where
  -- this makes future proof obligations simpler syntactically
  mapsTo : ∀ t : Icc tmin tmax, toFun t ∈ closedBall x₀ a -- plug in `a := 2 * a` in proofs
  initial : toFun ⟨t₀, ht⟩ = x₀

namespace SpaceOfCurves

variable (x₀ : E) {t₀ tmin tmax : ℝ} (ht₀ : t₀ ∈ Icc tmin tmax) (a : ℝ≥0)

-- need `toFun_eq_coe`?

instance : CoeFun (SpaceOfCurves x₀ ht₀ a) fun _ ↦ Icc tmin tmax → E := ⟨fun α ↦ α.toFun⟩

instance : Inhabited (SpaceOfCurves x₀ ht₀ a) :=
  ⟨⟨fun _ ↦ x₀, continuous_const⟩, fun _ ↦ mem_closedBall_self a.2, rfl⟩

noncomputable instance : MetricSpace (SpaceOfCurves x₀ ht₀ a) :=
  MetricSpace.induced toContinuousMap (fun _ _ _ ↦ by ext; congr) inferInstance

/-- `iterateIntegral` maps `SpaceOfCurves` to `SpaceOfCurves` -/
-- move `α` to target type to simplify proof syntax?
-- abstract components of this?
-- distill `3 * a` and `2 * a`?
noncomputable def iterate [CompleteSpace E] (f : ℝ → E → E)
    (hf : ContinuousOn (uncurry f) ((Icc tmin tmax) ×ˢ closedBall x₀ (3 * a)))
    -- generalise to `u` containing ball?


    -- copy here assumptions on `f` from below


    (α : SpaceOfCurves x₀ ht₀ (2 * a)) : SpaceOfCurves x₀ ht₀ (2 * a) :=
  { toFun := iterateIntegral f t₀ x₀ (α ∘ (projIcc _ _ (le_trans ht₀.1 ht₀.2))) ∘ Subtype.val
    continuous_toFun := by
      apply ContinuousOn.comp_continuous _ continuous_subtype_val Subtype.coe_prop
      intro t ht
      apply hasDerivWithinAt_iterateIntegral_Icc
        f (α ∘ (projIcc _ _ (le_trans ht₀.1 ht₀.2))) hf ht₀ _ _ _ ht |>.continuousWithinAt
      · exact α.continuous_toFun.comp_continuousOn continuous_projIcc.continuousOn
      · intro t' ht' -- why need to be `3 * a`?
        rw [comp_apply]
        apply mem_of_mem_of_subset (α.mapsTo _) (closedBall_subset_closedBall _)
        rw [NNReal.coe_mul, NNReal.coe_ofNat]
        exact mul_le_mul_of_nonneg_right (by norm_num) a.2
    mapsTo := by
      intro t
      simp only [NNReal.coe_mul, NNReal.coe_ofNat, ContinuousMap.toFun_eq_coe, comp_apply,
        iterateIntegral_apply, mem_closedBall, dist_self_add_left]
      -- inequality of norm of integral

      sorry
    initial := by simp only [ContinuousMap.toFun_eq_coe, comp_apply, iterateIntegral_apply,
        intervalIntegral.integral_same, add_zero] }

end SpaceOfCurves



-- K is NNReal because of LipschitzOnWith
-- prop 1.1 is stated strangely at the end
-- theorem exist_localFlow {tmin tmax L a b : ℝ} {u : Set E} {x₀ : E} (hu : closedBall x₀ (3 * a) ⊆ u)
--     {f : ℝ → E → E} {K : ℝ≥0} (hb : 0 < b)
--     (hcont₁ : ∀ x ∈ u, ContinuousOn (f · x) (Ioo tmin tmax))
--     (hcont₂ : ∀ t ∈ Ioo tmin tmax, ContinuousOn (f t) u)
--     (hle : ∀ t ∈ Ioo tmin tmax, ∀ x ∈ u, ‖f t x‖ ≤ L)
--     (hlip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith K (f t) u)
--     (hlt : b * L * K < a) :
--   ∃ α : E → ℝ → E, ∀ x ∈ closedBall x₀ a, α x 0 = x ∧
--     ∀ t ∈ Ioo (-b) b, α x t ∈ u ∧ HasDerivAt (α x) (f t (α x t)) t := sorry

-- corollary: existence of a single integral curve

theorem exist_localIntegralCurve {tmin tmax L a b : ℝ} {u : Set E} {x₀ : E}
    (hu : closedBall x₀ (3 * a) ⊆ u)
    {f : ℝ → E → E} {K : ℝ≥0} (hb : 0 < b)
    (hcont₁ : ∀ x ∈ u, ContinuousOn (f · x) (Ioo tmin tmax))
    (hcont₂ : ∀ t ∈ Ioo tmin tmax, ContinuousOn (f t) u)
    (hle : ∀ t ∈ Ioo tmin tmax, ∀ x ∈ u, ‖f t x‖ ≤ L)
    (hlip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith K (f t) u)
    (hlt : b * L * K < a) {x : E} (hx : x ∈ closedBall x₀ a) :
  ∃ α : ℝ → E, α 0 = x ∧
    ∀ t ∈ Ioo (-b) b, α t ∈ u ∧ HasDerivAt α (f t (α t)) t := sorry

-- provide the unique fixed point using `fixedPoint`
