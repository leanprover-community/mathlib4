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
lemma contDiffOn_comp {f : ℝ → E → E} {α : ℝ → E} {s : Set ℝ} {u : Set E} {n : WithTop ℕ∞}
    (hf : ContDiffOn ℝ n (uncurry f) (s ×ˢ u)) (hα : ContDiffOn ℝ n α s) (hmem : ∀ t ∈ s, α t ∈ u) :
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

/-- If the time-dependent vector field `f` and the curve `α` are continuous, then `f t (α t)` is the
derivative of `iterate f t₀ x₀ α`. -/
lemma hasDerivAt_iterate_isOpen [CompleteSpace E] {f : ℝ → E → E} {s : Set ℝ} (hs : IsOpen s)
    {u : Set E} (hf : ContinuousOn (uncurry f) (s ×ˢ u))
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
lemma hasDerivWithinAt_iterate_Icc [CompleteSpace E] {f : ℝ → E → E}
    {t₀ tmin tmax : ℝ} (ht₀ : t₀ ∈ Icc tmin tmax)
    {u : Set E} (hf : ContinuousOn (uncurry f) ((Icc tmin tmax) ×ˢ u))
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
lemma contDiffOn_nat_iterate_Ioo [CompleteSpace E] {f : ℝ → E → E} {u : Set E}
    {t₀ tmin tmax : ℝ} (ht₀ : t₀ ∈ Ioo tmin tmax) {n : ℕ}
    (hf : ContDiffOn ℝ n (uncurry f) ((Ioo tmin tmax) ×ˢ u))
    {α : ℝ → E} (hα : ContinuousOn α (Ioo tmin tmax))
    (hmem : ∀ t ∈ Ioo tmin tmax, α t ∈ u) (x₀ : E)
    (heqon : ∀ t ∈ Ioo tmin tmax, α t = iterate f t₀ x₀ α t) :
    ContDiffOn ℝ n (iterate f t₀ x₀ α) (Ioo tmin tmax) := by
  have ht' {t} (ht : t ∈ Ioo tmin tmax) : uIcc t₀ t ⊆ Ioo tmin tmax := by -- missing lemma?
    rw [uIcc_eq_union]
    exact union_subset (Icc_subset_Ioo ht₀.1 ht.2) (Icc_subset_Ioo ht.1 ht₀.2)
  have {t} (ht : t ∈ Ioo tmin tmax) :=
    hasDerivAt_iterate_isOpen isOpen_Ioo hf.continuousOn hα hmem x₀ (ht' ht)
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
lemma contDiffOn_enat_iterateIntegral_Ioo [CompleteSpace E] {f : ℝ → E → E} {u : Set E}
    {t₀ tmin tmax : ℝ} (ht₀ : t₀ ∈ Ioo tmin tmax) {n : ℕ∞}
    (hf : ContDiffOn ℝ n (uncurry f) ((Ioo tmin tmax) ×ˢ u))
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

/-! ## Space of curves -/

/-- The space of continuous functions `α : Icc tmin tmax → E` whose image is contained in `u` and
which satisfy the initial condition `α t₀ = x`.

This will be shown to be a complete metric space on
which `iterate` is a contracting map, leading to a fixed point `α` that will serve as the solution
to the ODE. -/
@[ext]
structure FunSpace {E : Type*} [NormedAddCommGroup E] (u : Set E) (x : E) {t₀ tmin tmax : ℝ}
    (ht₀ : t₀ ∈ Icc tmin tmax) extends C(Icc tmin tmax, E) where
  -- this makes future proof obligations simpler syntactically
  mapsTo : MapsTo toFun univ u -- plug in `u := closedBall x₀ (2 * a)` in proofs
  initial : toFun ⟨t₀, ht₀⟩ = x

namespace FunSpace

variable {E : Type*} [NormedAddCommGroup E]

section

variable {u : Set E} {x : E} {t₀ tmin tmax : ℝ} {ht₀ : t₀ ∈ Icc tmin tmax}

-- need `toFun_eq_coe`?

instance : CoeFun (FunSpace u x ht₀) fun _ ↦ Icc tmin tmax → E := ⟨fun α ↦ α.toFun⟩

/-- The constant map -/
instance (hx : x ∈ u) : Inhabited (FunSpace u x ht₀) :=
  ⟨⟨fun _ ↦ x, continuous_const⟩, fun _ _ ↦ hx, rfl⟩

/-- The metric between two curves `α` and `β` is the supremum of the metric between `α t` and `β t`
over all `t` in the domain. This is well defined when the domain is compact, such as a closed
interval in our case. -/
noncomputable instance : MetricSpace (FunSpace u x ht₀) :=
  MetricSpace.induced toContinuousMap (fun _ _ _ ↦ by ext; congr) inferInstance

lemma isUniformInducing_toContinuousMap :
    IsUniformInducing fun α : FunSpace u x ht₀ ↦ α.toContinuousMap := ⟨rfl⟩

lemma range_toContinuousMap : range (fun α : FunSpace u x ht₀ ↦ α.toContinuousMap) =
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
    CompleteSpace (FunSpace (closedBall x₀ a) x ht₀) := by
  rw [completeSpace_iff_isComplete_range <| isUniformInducing_toContinuousMap]
  apply IsClosed.isComplete
  rw [range_toContinuousMap, setOf_and]
  apply isClosed_eq (continuous_eval_const _) continuous_const |>.inter
  apply isClosed_ball.setOf_mapsTo
  exact fun _ _ ↦ continuous_eval_const _

end

/-! ### Contracting map on the space of curves -/

section






end

end FunSpace

end ODE
