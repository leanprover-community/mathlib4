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
noncomputable def iterateIntegral (f : ℝ → E → E) (α : ℝ → E) (t₀ : ℝ) (x₀ : E) : ℝ → E :=
  fun t ↦ x₀ + ∫ τ in t₀..t, f τ (α τ)

@[simp]
lemma iterateIntegral_apply {f : ℝ → E → E} {α : ℝ → E} {t₀ : ℝ} {x₀ : E} {t : ℝ} :
    iterateIntegral f α t₀ x₀ t = x₀ + ∫ τ in t₀..t, f τ (α τ) := rfl

-- `fun t ↦ f t (α t)` is C^n if `f` and `α` are C^n
lemma contDiffOn_Ioo {f : ℝ → E → E} {α : ℝ → E} {u : Set E}
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

lemma continuousOn_Ioo {f : ℝ → E → E} {α : ℝ → E} {u : Set E}
    {s : Set ℝ}
    (hf : ContinuousOn (uncurry f) (s ×ˢ u))
    (hα : ContinuousOn α s)
    (hmem : ∀ t ∈ s, α t ∈ u) :
    ContinuousOn (fun t ↦ f t (α t)) s :=
  contDiffOn_zero.mp <| contDiffOn_Ioo (contDiffOn_zero.mpr hf) (contDiffOn_zero.mpr hα) hmem

-- the integral equation has derivative `fun t ↦ f t (α t)`
lemma hasDerivAt_iterateIntegral [CompleteSpace E] (f : ℝ → E → E) (α : ℝ → E) {u : Set E}
    {tmin tmax t₀ : ℝ}
    (hf : ContinuousOn (uncurry f) ((Ioo tmin tmax) ×ˢ u))
    (ht₀ : t₀ ∈ Ioo tmin tmax) (hα : ContinuousOn α (Ioo tmin tmax))
    (hmem : ∀ t ∈ Ioo tmin tmax, α t ∈ u) (x₀ : E)
    {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    HasDerivAt (iterateIntegral f α t₀ x₀) (f t (α t)) t := by
  unfold iterateIntegral
  apply HasDerivAt.const_add
  apply intervalIntegral.integral_hasDerivAt_right -- need `CompleteSpace E`
  · apply ContinuousOn.intervalIntegrable
    apply continuousOn_Ioo hf hα hmem |>.mono
    by_cases h : t < t₀
    · rw [uIcc_of_gt h]
      exact Icc_subset_Ioo ht.1 ht₀.2
    · rw [uIcc_of_le (not_lt.mp h)]
      exact Icc_subset_Ioo ht₀.1 ht.2
  · exact continuousOn_Ioo hf hα hmem |>.stronglyMeasurableAtFilter isOpen_Ioo _ ht
  · exact continuousOn_Ioo hf hα hmem |>.continuousAt <| Ioo_mem_nhds ht.1 ht.2

lemma deriv_iterateIntegral [CompleteSpace E] (f : ℝ → E → E) (α : ℝ → E) {u : Set E}
    {tmin tmax t₀ : ℝ}
    (hf : ContinuousOn (uncurry f) ((Ioo tmin tmax) ×ˢ u))
    (ht₀ : t₀ ∈ Ioo tmin tmax) (hα : ContinuousOn α (Ioo tmin tmax))
    (hmem : ∀ t ∈ Ioo tmin tmax, α t ∈ u) (x₀ : E)
    {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    deriv (iterateIntegral f α t₀ x₀) t = f t (α t) := by
  -- use FTC2 `intervalIntegral.deriv_integral_right`
  unfold iterateIntegral -- add _eq lemma
  rw [deriv_const_add']
  -- code duplication below this
  apply intervalIntegral.deriv_integral_right
  · apply ContinuousOn.intervalIntegrable
    apply continuousOn_Ioo hf hα hmem |>.mono
    by_cases h : t < t₀
    · rw [uIcc_of_gt h]
      exact Icc_subset_Ioo ht.1 ht₀.2
    · rw [uIcc_of_le (not_lt.mp h)]
      exact Icc_subset_Ioo ht₀.1 ht.2
  · exact continuousOn_Ioo hf hα hmem |>.stronglyMeasurableAtFilter isOpen_Ioo _ ht
  · exact continuousOn_Ioo hf hα hmem |>.continuousAt <| Ioo_mem_nhds ht.1 ht.2

-- the integral equation transfers smoothness class from `f` to `α`
-- TODO: generalise `n` to `∞` and maybe `ω`
lemma contDiffOn_nat_iterateIntegral [CompleteSpace E] (f : ℝ → E → E) (α : ℝ → E) {u : Set E}
    {tmin tmax t₀ : ℝ} {n : ℕ}
    (hf : ContDiffOn ℝ n (uncurry f) ((Ioo tmin tmax) ×ˢ u))
    (ht₀ : t₀ ∈ Ioo tmin tmax) (hα : ContinuousOn α (Ioo tmin tmax))
    (hmem : ∀ t ∈ Ioo tmin tmax, α t ∈ u) (x₀ : E)
    (heqon : ∀ t ∈ Ioo tmin tmax, α t = iterateIntegral f α t₀ x₀ t) :
    ContDiffOn ℝ n (iterateIntegral f α t₀ x₀) (Ioo tmin tmax) := by
  induction n with
  | zero =>
    simp only [CharP.cast_eq_zero, contDiffOn_zero] at *
    apply HasDerivAt.continuousOn (f' := fun t ↦ f t (α t))
    intro _ ht
    exact hasDerivAt_iterateIntegral f α hf ht₀ hα hmem x₀ ht
  | succ n hn =>
    simp only [Nat.cast_add, Nat.cast_one] at *
    rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo] -- check this for generalisation to `ω`
    refine ⟨?_, by simp, ?_⟩
    · intro _ ht
      apply DifferentiableAt.differentiableWithinAt
      exact HasDerivAt.differentiableAt <|
        hasDerivAt_iterateIntegral f α hf.continuousOn ht₀ hα hmem x₀ ht
    · have hα' : ContDiffOn ℝ n α (Ioo tmin tmax) := by
        apply ContDiffOn.congr _ heqon
        apply hn
        exact hf.of_succ
      apply contDiffOn_Ioo hf.of_succ hα' hmem |>.congr
      intro _ ht
      exact deriv_iterateIntegral f α hf.continuousOn ht₀ hα hmem x₀ ht

lemma contDiffOn_enat_iterateIntegral [CompleteSpace E] (f : ℝ → E → E) (α : ℝ → E) {u : Set E}
    {tmin tmax t₀ : ℝ} {n : ℕ∞}
    (hf : ContDiffOn ℝ n (uncurry f) ((Ioo tmin tmax) ×ˢ u))
    (ht₀ : t₀ ∈ Ioo tmin tmax) (hα : ContinuousOn α (Ioo tmin tmax))
    (hmem : ∀ t ∈ Ioo tmin tmax, α t ∈ u) (x₀ : E)
    (heqon : ∀ t ∈ Ioo tmin tmax, α t = iterateIntegral f α t₀ x₀ t)
    {t : ℝ} :
    ContDiffOn ℝ n (iterateIntegral f α t₀ x₀) (Ioo tmin tmax) := by
  induction n with
  | top =>
    rw [contDiffOn_infty] at *
    intro k
    exact contDiffOn_nat_iterateIntegral _ _ (hf k) ht₀ hα hmem x₀ heqon
  | coe n =>
    simp only [WithTop.coe_natCast] at *
    exact contDiffOn_nat_iterateIntegral _ _ hf ht₀ hα hmem _ heqon

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
structure SpaceOfCurves (x₀ : E) (t₀ tmin tmax a : ℝ) where
  toFun : Icc tmin tmax → closedBall x₀ (2 * a) -- use `MapsTo`?
  mem_domain : t₀ ∈ Icc tmin tmax
  initial : toFun ⟨t₀, mem_domain⟩ = x₀
  continuous : Continuous toFun

namespace SpaceOfCurves

variable (x₀ : E) (t₀ tmin tmax a : ℝ)

instance : CoeFun (SpaceOfCurves x₀ t₀ tmin tmax a)
    fun _ => Icc tmin tmax → closedBall x₀ (2 * a) := ⟨toFun⟩



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
