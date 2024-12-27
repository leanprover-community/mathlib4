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

open Function MeasureTheory Metric Set
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
structure SpaceOfCurves (u : Set E) (x : E) {t₀ tmin tmax : ℝ} (ht₀ : t₀ ∈ Icc tmin tmax)
    extends C(Icc tmin tmax, E) where -- `Icc` because we need compact domain
  -- this makes future proof obligations simpler syntactically
  mapsTo : ∀ t : Icc tmin tmax, toFun t ∈ u -- plug in `u := closedBall x₀ (2 * a)` in proofs
  initial : toFun ⟨t₀, ht₀⟩ = x

namespace SpaceOfCurves

section

variable (u : Set E) {x : E} (hx : x ∈ u) {t₀ tmin tmax : ℝ} (ht₀ : t₀ ∈ Icc tmin tmax)
  (a : ℝ≥0)

-- need `toFun_eq_coe`?

instance : CoeFun (SpaceOfCurves u x ht₀) fun _ ↦ Icc tmin tmax → E := ⟨fun α ↦ α.toFun⟩

instance : Inhabited (SpaceOfCurves u x ht₀) :=
  ⟨⟨fun _ ↦ x, continuous_const⟩, fun _ ↦ hx, rfl⟩

noncomputable instance : MetricSpace (SpaceOfCurves u x ht₀) :=
  MetricSpace.induced toContinuousMap (fun _ _ _ ↦ by ext; congr) inferInstance

omit [NormedSpace ℝ E] in
lemma isUniformInducing : IsUniformInducing fun α : SpaceOfCurves u x ht₀ ↦ α.toContinuousMap :=
  ⟨rfl⟩

-- this is where we need `u` closed, e.g. closedBall
-- generalise to all closed `u`?
instance [CompleteSpace E] {x₀ : E} {a : ℝ≥0} :
    CompleteSpace (SpaceOfCurves (closedBall x₀ a) x ht₀) := by
  rw [completeSpace_iff_isComplete_range <| isUniformInducing _ ht₀]
  apply IsClosed.isComplete
  -- abstract this
  have : range (fun α : SpaceOfCurves (closedBall x₀ a) x ht₀ ↦ α.toContinuousMap) =
      { α : C(Icc tmin tmax, E) |
        α ⟨t₀, ht₀⟩ = x ∧ ∀ t : Icc tmin tmax, α t ∈ closedBall x₀ a } := by
    ext α; constructor
    · rintro ⟨⟨α, hα1, hα2⟩, rfl⟩
      exact ⟨hα2, hα1⟩
    · rintro ⟨hα1, hα2⟩
      refine ⟨⟨α, hα2, hα1⟩, rfl⟩
  rw [this, setOf_and]
  refine (isClosed_eq (continuous_eval_const _) continuous_const).inter ?_
  have : { α : C(↑(Icc tmin tmax), E) | ∀ (t : ↑(Icc tmin tmax)), α t ∈ closedBall x₀ a } =
      { α : C(↑(Icc tmin tmax), E) | MapsTo α univ (closedBall x₀ a) } := by
    simp only [Subtype.forall, mem_Icc, mapsTo_univ_iff]
  rw [this]
  apply isClosed_ball.setOf_mapsTo
  intro t ht
  exact continuous_eval_const _

end

/-- `iterateIntegral` maps `SpaceOfCurves` to `SpaceOfCurves` -/
-- move `α` to target type to simplify proof syntax?
-- abstract components of this?
--   `α ∘ projIcc`
--   `fun t ↦ `
-- generalise to `Icc`
-- generalise to `u` containing ball?
noncomputable def iterate [CompleteSpace E]
    {t₀ tmin tmax : ℝ}
    (ht₀ : t₀ ∈ Icc tmin tmax)
    {x₀ : E}
    {a : ℝ≥0}
    (f : ℝ → E → E)
    -- {K : ℝ≥0} (hlip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith K (f t) (closedBall x₀ (3 * a)))
    {K : ℝ≥0} (hlip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith K (f t) (closedBall x₀ (2 * a)))
    -- (hcont : ∀ x' ∈ closedBall x₀ (3 * a), ContinuousOn (f · x') (Ioo tmin tmax))
    (hcont : ∀ x' ∈ closedBall x₀ (2 * a), ContinuousOn (f · x') (Icc tmin tmax))
    -- {L : ℝ} (hnorm : ∀ t ∈ Ioo tmin tmax, ∀ x' ∈ closedBall x₀ (3 * a), ‖f t x'‖ ≤ L)
    {L : ℝ≥0} (hnorm : ∀ t ∈ Icc tmin tmax, ∀ x' ∈ closedBall x₀ (2 * a), ‖f t x'‖ ≤ L)
    (h : L * max (tmax - t₀) (t₀ - tmin) ≤ a) -- min a L ?
    {x : E} (hx : x ∈ closedBall x₀ a) -- or open ball as in Lang?
    (α : SpaceOfCurves (closedBall x₀ (2 * a)) x ht₀) :
    SpaceOfCurves (closedBall x₀ (2 * a)) x ht₀ :=
  { toFun := iterateIntegral f t₀ x (α ∘ (projIcc _ _ (le_trans ht₀.1 ht₀.2))) ∘ Subtype.val
    continuous_toFun := by
      apply ContinuousOn.comp_continuous _ continuous_subtype_val Subtype.coe_prop
      intro t ht
      have : ContinuousOn (uncurry f) (Icc tmin tmax ×ˢ (closedBall x₀ (2 * a))) :=
        have : ContinuousOn (uncurry (flip f)) (closedBall x₀ (2 * a) ×ˢ Icc tmin tmax) :=
          continuousOn_prod_of_continuousOn_lipschitzOnWith _ K hcont hlip
        this.comp continuous_swap.continuousOn (preimage_swap_prod _ _).symm.subset
      apply hasDerivWithinAt_iterateIntegral_Icc
        f (α ∘ (projIcc _ _ (le_trans ht₀.1 ht₀.2))) this ht₀ _ _ _ ht |>.continuousWithinAt
      · exact α.continuous_toFun.comp_continuousOn continuous_projIcc.continuousOn
      · intro t' ht' -- why need to be `3 * a`?
        rw [comp_apply]
        apply mem_of_mem_of_subset (α.mapsTo _) (closedBall_subset_closedBall _)
        apply mul_le_mul_of_nonneg_right (by norm_num) a.2
    mapsTo := by
      intro t
      dsimp only
      rw [comp_apply, iterateIntegral_apply, mem_closedBall,
        dist_eq_norm_sub, add_comm, add_sub_assoc]
      calc
        ‖_ + (x - x₀)‖ ≤ ‖_‖ + ‖x - x₀‖ := norm_add_le _ _
        _ ≤ ‖_‖ + a := add_le_add_left (mem_closedBall_iff_norm.mp hx) _
        _ = ‖∫ τ in Ι t₀ t, f τ ((α ∘ projIcc _ _ (le_trans ht₀.1 ht₀.2)) τ)‖ + a := by
          rw [intervalIntegral.norm_intervalIntegral_eq]
        _ ≤ L * ((volume.restrict (Ι t₀ ↑t)) univ).toReal + a := by
          apply add_le_add_right
          have : IsFiniteMeasure (volume.restrict (Ι t₀ ↑t)) := by -- missing lemma?
            rw [uIoc_eq_union]
            exact isFiniteMeasure_of_le _ <| Measure.restrict_union_le _ _
          apply norm_integral_le_of_norm_le_const
          apply (ae_restrict_mem measurableSet_Ioc).mono
          intro t' ht'
          apply hnorm
          · rw [mem_Ioc, inf_lt_iff, le_sup_iff, or_and_right, and_or_left, ← not_lt,
              and_not_self_iff, false_or, and_or_left, ← not_lt (b := t'), and_not_self_iff,
              or_false, not_lt, not_lt] at ht'
            cases ht' with
            | inl ht' => exact ⟨le_of_lt <| lt_of_le_of_lt ht₀.1 ht'.1, le_trans ht'.2 t.2.2⟩
            | inr ht' => exact ⟨le_of_lt <| lt_of_le_of_lt t.2.1 ht'.1, le_trans ht'.2 ht₀.2⟩
          · rw [comp_apply]
            apply mem_of_mem_of_subset (α.mapsTo _) (closedBall_subset_closedBall _)
            rfl
        _ = L * |t - t₀| + a := by
          congr
          rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
          by_cases ht : t₀ < t
          · rw [uIoc_of_le <| le_of_lt ht, Real.volume_Ioc,
              ENNReal.toReal_ofReal <| le_of_lt <| sub_pos_of_lt ht,
              abs_eq_self.mpr <| le_of_lt <| sub_pos_of_lt ht]
          · rw [uIoc_of_ge <| not_lt.mp ht, Real.volume_Ioc,
              ENNReal.toReal_ofReal <| sub_nonneg_of_le <| not_lt.mp ht,
              abs_eq_neg_self.mpr <| sub_nonpos_of_le <| not_lt.mp ht, neg_sub]
        _ ≤ L * max (tmax - t₀) (t₀ - tmin) + a := by
          apply add_le_add_right
          apply mul_le_mul_of_nonneg le_rfl _ L.2
          · rw [le_max_iff]
            apply Or.inl
            exact sub_nonneg_of_le ht₀.2
          · rw [le_max_iff]
            by_cases ht : t₀ < t
            · rw [abs_eq_self.mpr <| le_of_lt <| sub_pos_of_lt ht]
              apply Or.inl
              apply sub_le_sub_right
              exact t.2.2
            · rw [abs_eq_neg_self.mpr <| sub_nonpos_of_le <| not_lt.mp ht, neg_sub]
              apply Or.inr
              apply sub_le_sub_left
              exact t.2.1
        _ ≤ a + a := add_le_add_right h _
        _ = 2 * a := (two_mul _).symm
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
