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

-/

open Function MeasureTheory Metric Set
open scoped NNReal Topology

-- move to `MeasureTheory/Measure/Lebesgue/Basic`
instance Real.isFiniteMeasure_restrict_uIoc (x y : ℝ) :
    IsFiniteMeasure (volume.restrict (Ι x y)) := by
  rw [uIoc_eq_union]
  exact isFiniteMeasure_of_le _ <| Measure.restrict_union_le _ _

-- move to `MeasureTheory/Measure/Lebesgue/Basic`
@[simp]
lemma Real.volume_uIoc (a b : ℝ) : volume (Ι a b) = ENNReal.ofReal |b - a| := by
  rw [uIoc, volume_Ioc, max_sub_min_eq_abs]

namespace ODE

/-! ## Integral equation

For any time-dependent vector field `f : ℝ → E → E`, we define an integral equation and show that it
is equivalent to the initial value problem defined by `f`. The smoothness class of `f` is
transferred to solutions of the integral equation.
-/

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- equivalent integral equation, remark p.67
/-- The main integral expression on which the Picard-Lindelöf theorem is built. It will be shown
that if `α : ℝ → E` and `iterate f t₀ x₀ α` agree on an interval containing `t₀`, then `α` is a
solution to `f` with `α t₀ = x₀`. -/
noncomputable def iterate (f : ℝ → E → E) (t₀ : ℝ) (x₀ : E) (α : ℝ → E) : ℝ → E :=
  fun t ↦ x₀ + ∫ τ in t₀..t, f τ (α τ)

@[simp]
lemma iterate_apply {f : ℝ → E → E} {α : ℝ → E} {t₀ : ℝ} {x₀ : E} {t : ℝ} :
    iterate f t₀ x₀ α t = x₀ + ∫ τ in t₀..t, f τ (α τ) := rfl

-- use `MapsTo`?
/-- Given a $C^n$ time-dependent vector field `f` and a $C^n$ curve `α`, the composition `f t (α t)`
is $C^n$ in `t`. -/
lemma contDiffOn_comp {n : WithTop ℕ∞} {f : ℝ → E → E} {s : Set ℝ} {u : Set E}
    (hf : ContDiffOn ℝ n (uncurry f) (s ×ˢ u))
    {α : ℝ → E} (hα : ContDiffOn ℝ n α s) (hmem : ∀ t ∈ s, α t ∈ u) :
    ContDiffOn ℝ n (fun t ↦ f t (α t)) s := by
  have : (fun t ↦ f t (α t)) = (uncurry f) ∘ fun t ↦ (t, α t) := rfl -- abstract?
  rw [this]
  apply hf.comp <| contDiffOn_id.prod hα
  intro _ ht
  rw [mem_prod]
  exact ⟨ht, hmem _ ht⟩

-- `hf` could be restated in each component. missing lemma stating their equivalence?
/-- Special case of `contDiffOn_comp` when `n = 0`. -/
lemma continuousOn_comp {f : ℝ → E → E} {α : ℝ → E} {s : Set ℝ} {u : Set E}
    (hf : ContinuousOn (uncurry f) (s ×ˢ u)) (hα : ContinuousOn α s) (hmem : ∀ t ∈ s, α t ∈ u) :
    ContinuousOn (fun t ↦ f t (α t)) s :=
  contDiffOn_zero.mp <| contDiffOn_comp (contDiffOn_zero.mpr hf) (contDiffOn_zero.mpr hα) hmem

variable [CompleteSpace E]

/-- If the time-dependent vector field `f` and the curve `α` are continuous, then `f t (α t)` is the
derivative of `iterate f t₀ x₀ α`. -/
lemma hasDerivAt_iterate_of_isOpen
    {f : ℝ → E → E} {s : Set ℝ} (hs : IsOpen s) {u : Set E}
    (hf : ContinuousOn (uncurry f) (s ×ˢ u))
    {α : ℝ → E} (hα : ContinuousOn α s)
    (hmem : ∀ t ∈ s, α t ∈ u) (x₀ : E)
    {t₀ : ℝ} {t : ℝ} (ht : uIcc t₀ t ⊆ s) :
    HasDerivAt (iterate f t₀ x₀ α) (f t (α t)) t := by
  apply HasDerivAt.const_add
  have ht' : t ∈ s := by -- missing lemmas `mem_Icc_right` etc?
    apply mem_of_mem_of_subset _ ht
    rw [mem_uIcc]
    simp only [le_refl, and_true, true_and]
    exact le_rfl.le_or_le _
  have : Fact (t ∈ s) := ⟨ht'⟩ -- needed to synthesise `FTCFilter` for `Ioo`
  exact intervalIntegral.integral_hasDerivAt_right -- need `CompleteSpace E` and `Icc`
    (continuousOn_comp hf hα hmem |>.mono ht |>.intervalIntegrable)
    (continuousOn_comp hf hα hmem |>.stronglyMeasurableAtFilter hs _ ht')
    (continuousOn_comp hf hα hmem _ ht' |>.continuousAt <| hs.mem_nhds ht')

-- also works for open sets and `Ici` and `Iic`; generalise?
-- another theorem for `(iterate f t₀ x₀ α) t₀ = x₀`?
/-- If the time-dependent vector field `f` and the curve `α` are continuous, then `f t (α t)` is the
derivative of `iterate f t₀ x₀ α`. -/
lemma hasDerivWithinAt_iterate_Icc
    {t₀ tmin tmax : ℝ} (ht₀ : t₀ ∈ Icc tmin tmax)
    {f : ℝ → E → E} {u : Set E} (hf : ContinuousOn (uncurry f) ((Icc tmin tmax) ×ˢ u))
    {α : ℝ → E} (hα : ContinuousOn α (Icc tmin tmax))
    (hmem : ∀ t ∈ Icc tmin tmax, α t ∈ u) (x₀ : E)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    HasDerivWithinAt (iterate f t₀ x₀ α) (f t (α t)) (Icc tmin tmax) t := by
  apply HasDerivWithinAt.const_add
  have : Fact (t ∈ Icc tmin tmax) := ⟨ht⟩ -- needed to synthesise `FTCFilter` for `Icc`
  apply intervalIntegral.integral_hasDerivWithinAt_right _ -- need `CompleteSpace E` and `Icc`
    (continuousOn_comp hf hα hmem |>.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t)
    (continuousOn_comp hf hα hmem _ ht)
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_comp hf hα hmem |>.mono
  by_cases h : t < t₀
  · rw [uIcc_of_gt h]
    exact Icc_subset_Icc ht.1 ht₀.2
  · rw [uIcc_of_le (not_lt.mp h)]
    exact Icc_subset_Icc ht₀.1 ht.2

-- `n = ω`?
-- also works for `Ioi` and `Iio` but not intervals with a closed end due to non-unique diff there
/-- If the time-dependent vector field `f` is $C^n$ and the curve `α` is continuous, then
`interate f t₀ x₀ α` is also $C^n$. This version works for `n : ℕ`. -/
lemma contDiffOn_nat_iterate_Ioo
    {t₀ tmin tmax : ℝ} (ht₀ : t₀ ∈ Ioo tmin tmax) {n : ℕ}
    {f : ℝ → E → E} {u : Set E} (hf : ContDiffOn ℝ n (uncurry f) ((Ioo tmin tmax) ×ˢ u))
    {α : ℝ → E} (hα : ContinuousOn α (Ioo tmin tmax))
    (hmem : ∀ t ∈ Ioo tmin tmax, α t ∈ u) (x₀ : E)
    (heqon : ∀ t ∈ Ioo tmin tmax, α t = iterate f t₀ x₀ α t) :
    ContDiffOn ℝ n (iterate f t₀ x₀ α) (Ioo tmin tmax) := by
  have ht' {t} (ht : t ∈ Ioo tmin tmax) : uIcc t₀ t ⊆ Ioo tmin tmax := by -- missing lemma?
    rw [uIcc_eq_union]
    exact union_subset (Icc_subset_Ioo ht₀.1 ht.2) (Icc_subset_Ioo ht.1 ht₀.2)
  have {t} (ht : t ∈ Ioo tmin tmax) :=
    hasDerivAt_iterate_of_isOpen isOpen_Ioo hf.continuousOn hα hmem x₀ (ht' ht)
  induction n with
  | zero =>
    simp only [CharP.cast_eq_zero, contDiffOn_zero] at *
    exact fun _ ht ↦ this ht |>.continuousAt.continuousWithinAt
  | succ n hn =>
    simp only [Nat.cast_add, Nat.cast_one] at *
    rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo] -- check this for generalisation to `ω`
    refine ⟨fun _ ht ↦ HasDerivAt.differentiableAt (this ht) |>.differentiableWithinAt, by simp, ?_⟩
    have hα' : ContDiffOn ℝ n α (Ioo tmin tmax) := ContDiffOn.congr (hn hf.of_succ) heqon
    exact contDiffOn_comp hf.of_succ hα' hmem |>.congr fun _ ht ↦ HasDerivAt.deriv (this ht)

/-- If the time-dependent vector field `f` is $C^n$ and the curve `α` is continuous, then
`interate f t₀ x₀ α` is also $C^n$.This version works for `n : ℕ∞`. -/
lemma contDiffOn_enat_iterateIntegral_Ioo
    {t₀ tmin tmax : ℝ} (ht₀ : t₀ ∈ Ioo tmin tmax) {n : ℕ∞}
    {f : ℝ → E → E} {u : Set E} (hf : ContDiffOn ℝ n (uncurry f) ((Ioo tmin tmax) ×ˢ u))
    {α : ℝ → E} (hα : ContinuousOn α (Ioo tmin tmax))
    (hmem : ∀ t ∈ Ioo tmin tmax, α t ∈ u) (x₀ : E)
    (heqon : ∀ t ∈ Ioo tmin tmax, α t = iterate f t₀ x₀ α t) :
    ContDiffOn ℝ n (iterate f t₀ x₀ α) (Ioo tmin tmax) := by
  induction n with
  | top =>
    rw [contDiffOn_infty] at *
    intro k
    exact contDiffOn_nat_iterate_Ioo ht₀ (hf k) hα hmem x₀ heqon
  | coe n =>
    simp only [WithTop.coe_natCast] at *
    exact contDiffOn_nat_iterate_Ioo ht₀ hf hα hmem x₀ heqon

end

-- extract variables
lemma continuousOn_iterate_of_lipschitzOnWith_continuousOn
    {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E → E} {s : Set ℝ} {u : Set E}
    {K : ℝ≥0} (hlip : ∀ t ∈ s, LipschitzOnWith K (f t) u)
    (hcont : ∀ x ∈ u, ContinuousOn (f · x) s) :
    ContinuousOn (uncurry f) (s ×ˢ u) :=
  have : ContinuousOn (uncurry (flip f)) (u ×ˢ s) :=
    continuousOn_prod_of_continuousOn_lipschitzOnWith _ K hcont hlip
  this.comp continuous_swap.continuousOn (preimage_swap_prod _ _).symm.subset

/-! ## Space of curves -/

/-- The space of continuous functions `α : Icc tmin tmax → E` whose image is contained in `u` and
which satisfy the initial condition `α t₀ = x`.

This will be shown to be a complete metric space on
which `iterate` is a contracting map, leading to a fixed point `α` that will serve as the solution
to the ODE. -/
-- comment about `x ∈ u`
@[ext]
structure FunSpace {E : Type*} [NormedAddCommGroup E] {t₀ tmin tmax : ℝ}
    (ht₀ : t₀ ∈ Icc tmin tmax) (u : Set E) (x : E) extends C(Icc tmin tmax, E) where
  -- this makes future proof obligations simpler syntactically
  mapsTo : MapsTo toFun univ u -- plug in `u := closedBall x₀ (2 * a)` in proofs
  initial : toFun ⟨t₀, ht₀⟩ = x

namespace FunSpace

variable {E : Type*} [NormedAddCommGroup E]

section

variable {t₀ tmin tmax : ℝ} {ht₀ : t₀ ∈ Icc tmin tmax} {u : Set E} {x : E}

-- need `toFun_eq_coe`?

instance : CoeFun (FunSpace ht₀ u x) fun _ ↦ Icc tmin tmax → E := ⟨fun α ↦ α.toFun⟩

/-- The constant map -/
instance (hx : x ∈ u) : Inhabited (FunSpace ht₀ u x) :=
  ⟨⟨fun _ ↦ x, continuous_const⟩, fun _ _ ↦ hx, rfl⟩

/-- The metric between two curves `α` and `β` is the supremum of the metric between `α t` and `β t`
over all `t` in the domain. This is well defined when the domain is compact, such as a closed
interval in our case. -/
noncomputable instance : MetricSpace (FunSpace ht₀ u x) :=
  MetricSpace.induced toContinuousMap (fun _ _ _ ↦ by ext; congr) inferInstance

lemma isUniformInducing_toContinuousMap :
    IsUniformInducing fun α : FunSpace ht₀ u x ↦ α.toContinuousMap := ⟨rfl⟩

lemma range_toContinuousMap : range (fun α : FunSpace ht₀ u x ↦ α.toContinuousMap) =
    { α : C(Icc tmin tmax, E) | α ⟨t₀, ht₀⟩ = x ∧ MapsTo α univ u } := by
  ext α; constructor
  · rintro ⟨⟨α, hα1, hα2⟩, rfl⟩
    exact ⟨hα2, hα1⟩
  · rintro ⟨hα1, hα2⟩
    refine ⟨⟨α, hα2, hα1⟩, rfl⟩

-- this is where we need `u` closed, e.g. closedBall
-- generalise to all closed `u`?
/-- The space of bounded curves is complete. -/
instance [CompleteSpace E] {x₀ : E} {a : ℝ≥0} :
    CompleteSpace (FunSpace ht₀ (closedBall x₀ a) x) := by
  rw [completeSpace_iff_isComplete_range <| isUniformInducing_toContinuousMap]
  apply IsClosed.isComplete
  rw [range_toContinuousMap, setOf_and]
  apply isClosed_eq (continuous_eval_const _) continuous_const |>.inter
  apply isClosed_ball.setOf_mapsTo
  exact fun _ _ ↦ continuous_eval_const _

end

/-! ### Contracting map on the space of curves -/

section

variable [NormedSpace ℝ E]

lemma norm_intervalIntegral_le_mul_abs {f : ℝ → E → E}
    {t₀ tmin tmax : ℝ} (ht₀ : t₀ ∈ Icc tmin tmax)
    {u : Set E}
    {L : ℝ≥0} (hnorm : ∀ t ∈ Icc tmin tmax, ∀ x ∈ u, ‖f t x‖ ≤ L)
    {x : E} (α : FunSpace ht₀ u x) (t : Icc tmin tmax) :
    ‖∫ (τ : ℝ) in t₀..t, f τ ((α.toFun ∘ projIcc tmin tmax (le_trans ht₀.1 ht₀.2)) τ)‖ ≤
      L * |t - t₀| := by
  calc
    _ ≤ L * ((volume.restrict (Ι t₀ t)) univ).toReal := by
      rw [intervalIntegral.norm_intervalIntegral_eq]
      apply norm_integral_le_of_norm_le_const
      apply ae_restrict_mem measurableSet_Ioc |>.mono
      intro t' ht'
      apply hnorm _ _ _ <| α.mapsTo (mem_univ _)
      rw [← uIoc, uIoc_eq_union] at ht'
      -- why can't these be directly solved with a tactic?
      have ⟨_, _⟩ := ht₀
      have ⟨_, _⟩ := t.2
      refine or_imp.mpr ⟨fun h ↦ ?_, fun h ↦ ?_⟩ ht' <;>
      · have ⟨_, _⟩ := h
        exact ⟨by linarith, by linarith⟩
    _ = L * |t - t₀| := by simp

/-- The contracting map on `FunSpace` defined by `ODE.iterate` -/
protected noncomputable def iterate [CompleteSpace E]
    {t₀ tmin tmax : ℝ} (ht₀ : t₀ ∈ Icc tmin tmax)
    {x₀ : E}
    {a : ℝ≥0}
    {f : ℝ → E → E}
    {K : ℝ≥0} (hlip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith K (f t) (closedBall x₀ (2 * a)))
    (hcont : ∀ x' ∈ closedBall x₀ (2 * a), ContinuousOn (f · x') (Icc tmin tmax))
    {L : ℝ≥0} (hnorm : ∀ t ∈ Icc tmin tmax, ∀ x' ∈ closedBall x₀ (2 * a), ‖f t x'‖ ≤ L)
    (h : L * max (tmax - t₀) (t₀ - tmin) ≤ a) -- weaker condition than in Lang
    {x : E} (hx : x ∈ closedBall x₀ a) -- or open ball as in Lang?
    (α : FunSpace ht₀ (closedBall x₀ (2 * a)) x) : FunSpace ht₀ (closedBall x₀ (2 * a)) x where
  toFun := iterate f t₀ x (α ∘ (projIcc _ _ (le_trans ht₀.1 ht₀.2))) ∘ Subtype.val
  continuous_toFun := by
    apply ContinuousOn.comp_continuous _ continuous_subtype_val Subtype.coe_prop
    have hf := continuousOn_iterate_of_lipschitzOnWith_continuousOn hlip hcont
    have hα : ContinuousOn (α ∘ (projIcc _ _ (le_trans ht₀.1 ht₀.2))) (Icc tmin tmax) :=
      α.continuous_toFun.comp_continuousOn continuous_projIcc.continuousOn
    intro t ht
    apply hasDerivWithinAt_iterate_Icc ht₀ hf hα _ x ht |>.continuousWithinAt
    exact fun _ _ ↦ mem_of_mem_of_subset (α.mapsTo (mem_univ _))
      (closedBall_subset_closedBall le_rfl)
  mapsTo := by
    intro t _ -- this form of FunSpace.mapsTo causes useless assumptions `t ∈ univ`
    dsimp only
    rw [comp_apply, iterate_apply, mem_closedBall, dist_eq_norm, add_comm, add_sub_assoc]
    calc
      ‖_ + (x - x₀)‖ ≤ ‖_‖ + ‖x - x₀‖ := norm_add_le _ _
      _ ≤ ‖_‖ + a := add_le_add_left (mem_closedBall_iff_norm.mp hx) _
      _ ≤ L * |t - t₀| + a := add_le_add_right (norm_intervalIntegral_le_mul_abs _ hnorm ..) _
      _ ≤ L * max (tmax - t₀) (t₀ - tmin) + a := by
        apply add_le_add_right
        apply mul_le_mul_of_nonneg_left _ L.2
        by_cases ht : t₀ < t
        · rw [abs_of_pos <| sub_pos_of_lt ht]
          exact le_max_of_le_left <| sub_le_sub_right t.2.2 _
        · rw [abs_of_nonpos <| sub_nonpos_of_le <| not_lt.mp ht, neg_sub]
          exact le_max_of_le_right <| sub_le_sub_left t.2.1 _
      _ ≤ a + a := add_le_add_right h _
      _ = 2 * a := (two_mul _).symm
  initial := by simp only [ContinuousMap.toFun_eq_coe, comp_apply, iterate_apply,
      intervalIntegral.integral_same, add_zero]


end

end FunSpace

end ODE
