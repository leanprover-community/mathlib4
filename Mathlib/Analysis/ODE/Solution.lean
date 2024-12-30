/-
Copyright (c) 2024 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.MetricSpace.Contracting

-- remember to fix copyright

/-!
Attempt to unify `Gronwall` and `PicardLindelof` and prepare for `LocalFlow`

Implementation notes:
* Using Lipschitz in `FunSpace` instead of the mapping into a closed ball condition of Lang so that
`CompleteSpace E` can be avoided in most proofs, even though Lipschitz is a stronger condition than
the mapping condition. We also avoid having to carrying around `closedBall x₀ (2 * a)` in the type.
* `ℝ≥0` is used as the type of many constants here to minise proofs for statements like `0 ≤ 2 * a`.
-/

open Function MeasureTheory Metric Set
open scoped Nat NNReal Topology

-- generalise
lemma abs_sub_le_max_sub {a b c : ℝ} (hac : a ≤ b) (hcd : b ≤ c) (d : ℝ) :
    |b - d| ≤ (c - d) ⊔ (d - a) := by
  rcases le_total d b with h | h
  · rw [abs_of_nonneg <| sub_nonneg_of_le h]
    exact le_max_of_le_left <| sub_le_sub_right hcd _
  · rw [abs_of_nonpos <| sub_nonpos_of_le h, neg_sub]
    exact le_max_of_le_right <| sub_le_sub_left hac _

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
that if `α : ℝ → E` and `integral f t₀ x₀ α` agree on an interval containing `t₀`, then `α` is a
solution to `f` with `α t₀ = x₀`. -/
noncomputable def integrate (f : ℝ → E → E) (t₀ : ℝ) (x₀ : E) (α : ℝ → E) : ℝ → E :=
  fun t ↦ x₀ + ∫ τ in t₀..t, f τ (α τ)

@[simp]
lemma integrate_apply {f : ℝ → E → E} {α : ℝ → E} {t₀ : ℝ} {x₀ : E} {t : ℝ} :
    integrate f t₀ x₀ α t = x₀ + ∫ τ in t₀..t, f τ (α τ) := rfl

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
derivative of `integrate f t₀ x₀ α`. -/
lemma hasDerivAt_integrate_of_isOpen
    {f : ℝ → E → E} {s : Set ℝ} (hs : IsOpen s) {u : Set E}
    (hf : ContinuousOn (uncurry f) (s ×ˢ u))
    {α : ℝ → E} (hα : ContinuousOn α s)
    (hmem : ∀ t ∈ s, α t ∈ u) (x₀ : E)
    {t₀ : ℝ} {t : ℝ} (ht : uIcc t₀ t ⊆ s) :
    HasDerivAt (integrate f t₀ x₀ α) (f t (α t)) t := by
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

-- need a `ContinuousOn` version not requiring `CompleteSpace E`
-- also works for open sets and `Ici` and `Iic`; generalise?
-- another theorem for `(integrate f t₀ x₀ α) t₀ = x₀`?
/-- If the time-dependent vector field `f` and the curve `α` are continuous, then `f t (α t)` is the
derivative of `integrate f t₀ x₀ α`. -/
lemma hasDerivWithinAt_integrate_Icc
    {t₀ tmin tmax : ℝ} (ht₀ : t₀ ∈ Icc tmin tmax)
    {f : ℝ → E → E} {u : Set E} (hf : ContinuousOn (uncurry f) ((Icc tmin tmax) ×ˢ u))
    {α : ℝ → E} (hα : ContinuousOn α (Icc tmin tmax))
    (hmem : ∀ t ∈ Icc tmin tmax, α t ∈ u) (x₀ : E)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    HasDerivWithinAt (integrate f t₀ x₀ α) (f t (α t)) (Icc tmin tmax) t := by
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
lemma contDiffOn_nat_integrate_Ioo
    {t₀ tmin tmax : ℝ} (ht₀ : t₀ ∈ Ioo tmin tmax) {n : ℕ}
    {f : ℝ → E → E} {u : Set E} (hf : ContDiffOn ℝ n (uncurry f) ((Ioo tmin tmax) ×ˢ u))
    {α : ℝ → E} (hα : ContinuousOn α (Ioo tmin tmax))
    (hmem : ∀ t ∈ Ioo tmin tmax, α t ∈ u) (x₀ : E)
    (heqon : ∀ t ∈ Ioo tmin tmax, α t = integrate f t₀ x₀ α t) :
    ContDiffOn ℝ n (integrate f t₀ x₀ α) (Ioo tmin tmax) := by
  have ht' {t} (ht : t ∈ Ioo tmin tmax) : uIcc t₀ t ⊆ Ioo tmin tmax := by -- missing lemma?
    rw [uIcc_eq_union]
    exact union_subset (Icc_subset_Ioo ht₀.1 ht.2) (Icc_subset_Ioo ht.1 ht₀.2)
  have {t} (ht : t ∈ Ioo tmin tmax) :=
    hasDerivAt_integrate_of_isOpen isOpen_Ioo hf.continuousOn hα hmem x₀ (ht' ht)
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
lemma contDiffOn_enat_integrateIntegral_Ioo
    {t₀ tmin tmax : ℝ} (ht₀ : t₀ ∈ Ioo tmin tmax) {n : ℕ∞}
    {f : ℝ → E → E} {u : Set E} (hf : ContDiffOn ℝ n (uncurry f) ((Ioo tmin tmax) ×ˢ u))
    {α : ℝ → E} (hα : ContinuousOn α (Ioo tmin tmax))
    (hmem : ∀ t ∈ Ioo tmin tmax, α t ∈ u) (x₀ : E)
    (heqon : ∀ t ∈ Ioo tmin tmax, α t = integrate f t₀ x₀ α t) :
    ContDiffOn ℝ n (integrate f t₀ x₀ α) (Ioo tmin tmax) := by
  induction n with
  | top =>
    rw [contDiffOn_infty] at *
    intro k
    exact contDiffOn_nat_integrate_Ioo ht₀ (hf k) hα hmem x₀ heqon
  | coe n =>
    simp only [WithTop.coe_natCast] at *
    exact contDiffOn_nat_integrate_Ioo ht₀ hf hα hmem x₀ heqon

end

lemma continuousOn_uncurry_of_lipschitzOnWith_continuousOn
    {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E → E} {s : Set ℝ} {u : Set E}
    {K : ℝ≥0} (hlip : ∀ t ∈ s, LipschitzOnWith K (f t) u)
    (hcont : ∀ x ∈ u, ContinuousOn (f · x) s) :
    ContinuousOn (uncurry f) (s ×ˢ u) :=
  have : ContinuousOn (uncurry (flip f)) (u ×ˢ s) :=
    continuousOn_prod_of_continuousOn_lipschitzOnWith _ K hcont hlip
  this.comp continuous_swap.continuousOn (preimage_swap_prod _ _).symm.subset

/-! ## Space of curves -/

/-- The space of `C`-Lipschitz functions `α : Icc tmin tmax → E` satisfying the initial condition
`α t₀ = x`.

This will be shown to be a complete metric space on which `integrate` is a contracting map, leading
to a fixed point that will serve as the solution to the ODE. -/
structure FunSpace {E : Type*} [NormedAddCommGroup E]
    {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (x : E) (C : ℝ≥0) where
  toFun : Icc tmin tmax → E
  initial : toFun t₀ = x
  lipschitz : LipschitzWith C toFun

namespace FunSpace

variable {E : Type*} [NormedAddCommGroup E]

section

variable {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x : E} {C : ℝ≥0}

-- need `toFun_eq_coe`?

instance : CoeFun (FunSpace t₀ x C) fun _ ↦ Icc tmin tmax → E := ⟨fun α ↦ α.toFun⟩

/-- The constant map -/
instance : Inhabited (FunSpace t₀ x C) :=
  ⟨fun _ ↦ x, rfl, (LipschitzWith.const _).weaken (zero_le _)⟩

protected lemma continuous (α : FunSpace t₀ x C) : Continuous α := α.lipschitz.continuous

/-- The embedding of `FunSpace` into the space of continuous maps. -/
def toContinuousMap : FunSpace t₀ x C ↪ C(Icc tmin tmax, E) :=
  ⟨fun α ↦ ⟨α, α.continuous⟩, fun α β h ↦ by cases α; cases β; simpa using h⟩

/-- The metric between two curves `α` and `β` is the supremum of the metric between `α t` and `β t`
over all `t` in the domain. This is finite when the domain is compact, such as a closed
interval in our case. -/
noncomputable instance : MetricSpace (FunSpace t₀ x C) :=
  MetricSpace.induced toContinuousMap toContinuousMap.injective inferInstance

lemma isUniformInducing_toContinuousMap :
    IsUniformInducing fun α : FunSpace t₀ x C ↦ α.toContinuousMap := ⟨rfl⟩

lemma range_toContinuousMap : range (fun α : FunSpace t₀ x C ↦ α.toContinuousMap) =
    { α : C(Icc tmin tmax, E) | α t₀ = x ∧ LipschitzWith C α } := by
  ext α
  constructor
  · rintro ⟨⟨α, hα1, hα2⟩, rfl⟩
    exact ⟨hα1, hα2⟩
  · rintro ⟨hα1, hα2⟩
    exact ⟨⟨α, hα1, hα2⟩, rfl⟩

/-- We show that `FunSpace` is complete in order to apply the contraction mapping theorem. -/
instance [CompleteSpace E] : CompleteSpace (FunSpace t₀ x C) := by
  rw [completeSpace_iff_isComplete_range <| isUniformInducing_toContinuousMap]
  apply IsClosed.isComplete
  rw [range_toContinuousMap, setOf_and]
  apply isClosed_eq (continuous_eval_const _) continuous_const |>.inter
  exact isClosed_setOf_lipschitzWith C |>.preimage continuous_coeFun

protected theorem mem_closedBall (α : FunSpace t₀ x C) {a : ℝ≥0}
  (hle : C * max (tmax - t₀) (t₀ - tmin) ≤ a) (t : Icc tmin tmax) : α t ∈ closedBall x C := by
  rw [mem_closedBall]
  calc
    dist (α t) x = dist (α t) (α t₀) := by rw [α.initial]
    _ ≤ C * dist t t₀ := α.lipschitz.dist_le_mul _ _
    _ ≤ C * max (tmax - t₀) (t₀ - tmin) :=
      mul_le_mul_of_nonneg_left (abs_sub_le_max_sub t.2.1 t.2.2 _) C.2
    _ ≤ a := hle

end

/-! ### Contracting map on the space of curves -/

variable [NormedSpace ℝ E]

lemma norm_intervalIntegral_le_mul_abs {f : ℝ → E → E}
    {t₀ tmin tmax : ℝ} (ht₀ : t₀ ∈ Icc tmin tmax)
    {x₀ : E} {a L : ℝ≥0} (hnorm : ∀ t ∈ Icc tmin tmax, ∀ x ∈ closedBall x₀ a, ‖f t x‖ ≤ L)
    {x : E} {C : ℝ≥0} (α : FunSpace ht₀ x C) (t : Icc tmin tmax) :
    ‖∫ (τ : ℝ) in t₀..t, f τ ((α.toFun ∘ projIcc tmin tmax (le_trans ht₀.1 ht₀.2)) τ)‖ ≤
      L * |t - t₀| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro t' ht'
  apply hnorm _ _ _

  rw [uIoc_eq_union] at ht'
  -- why can't these be directly solved with a tactic?
  have ⟨_, _⟩ := ht₀
  have ⟨_, _⟩ := t.2
  refine or_imp.mpr ⟨fun h ↦ ?_, fun h ↦ ?_⟩ ht' <;>
  · have ⟨_, _⟩ := h
    exact ⟨by linarith, by linarith⟩

variable [CompleteSpace E]

/-- The contracting map on `FunSpace` defined by `ODE.integrate` -/
protected noncomputable def integrate
    {t₀ tmin tmax : ℝ} (ht₀ : t₀ ∈ Icc tmin tmax)
    {x₀ : E}
    {a : ℝ≥0}
    {f : ℝ → E → E}
    {K : ℝ≥0} (hlip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith K (f t) (closedBall x₀ (2 * a)))
    (hcont : ∀ x' ∈ closedBall x₀ (2 * a), ContinuousOn (f · x') (Icc tmin tmax))
    {L : ℝ≥0} (hnorm : ∀ t ∈ Icc tmin tmax, ∀ x' ∈ closedBall x₀ (2 * a), ‖f t x'‖ ≤ L)
    (hle : L * max (tmax - t₀) (t₀ - tmin) ≤ a) -- weaker condition than in Lang
    {x : E} (hx : x ∈ closedBall x₀ a)
    (α : FunSpace ht₀ (closedBall x₀ (2 * a)) x) : FunSpace ht₀ (closedBall x₀ (2 * a)) x where
  toFun := integrate f t₀ x (α ∘ (projIcc _ _ (le_trans ht₀.1 ht₀.2))) ∘ Subtype.val
  continuous_toFun := by
    apply ContinuousOn.comp_continuous _ continuous_subtype_val Subtype.coe_prop
    have hf := continuousOn_uncurry_of_lipschitzOnWith_continuousOn hlip hcont
    have hα : ContinuousOn (α ∘ (projIcc _ _ (le_trans ht₀.1 ht₀.2))) (Icc tmin tmax) :=
      α.continuous_toFun.comp_continuousOn continuous_projIcc.continuousOn
    intro t ht
    apply hasDerivWithinAt_integrate_Icc ht₀ hf hα _ x ht |>.continuousWithinAt
    exact fun _ _ ↦ mem_of_mem_of_subset (α.mapsTo (mem_univ _))
      (closedBall_subset_closedBall le_rfl)
  mapsTo := by
    intro t _ -- this form of FunSpace.mapsTo causes useless assumptions `t ∈ univ`
    dsimp only
    rw [comp_apply, integrate_apply, mem_closedBall, dist_eq_norm, add_comm, add_sub_assoc]
    nth_rw 2 [two_mul]
    apply norm_add_le_of_le _ <| mem_closedBall_iff_norm.mp hx
    calc
      ‖_‖ ≤ L * |t - t₀| := norm_intervalIntegral_le_mul_abs ht₀ hnorm α t
      _ ≤ L * max (tmax - t₀) (t₀ - tmin) :=
        mul_le_mul_of_nonneg_left (abs_sub_le_max_sub t.2.1 t.2.2 _) L.2
      _ ≤ a := hle
  initial := by simp only [ContinuousMap.toFun_eq_coe, comp_apply, integrate_apply,
      intervalIntegral.integral_same, add_zero]

@[simp]
lemma integrate_apply
    {t₀ tmin tmax : ℝ} (ht₀ : t₀ ∈ Icc tmin tmax)
    {x₀ : E}
    {a : ℝ≥0}
    {f : ℝ → E → E}
    {K : ℝ≥0} (hlip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith K (f t) (closedBall x₀ (2 * a)))
    (hcont : ∀ x' ∈ closedBall x₀ (2 * a), ContinuousOn (f · x') (Icc tmin tmax))
    {L : ℝ≥0} (hnorm : ∀ t ∈ Icc tmin tmax, ∀ x' ∈ closedBall x₀ (2 * a), ‖f t x'‖ ≤ L)
    (hle : L * max (tmax - t₀) (t₀ - tmin) ≤ a)
    {x : E} (hx : x ∈ closedBall x₀ a)
    (α : FunSpace ht₀ (closedBall x₀ (2 * a)) x) {t : Icc tmin tmax} :
    α.integrate ht₀ hlip hcont hnorm hle hx t =
      integrate f t₀ x (α ∘ (projIcc _ _ (le_trans ht₀.1 ht₀.2))) t := rfl

/-- A key step in the inductive case of `dist_iterate_integrate_apply_le` -/
lemma dist_comp_iterate_integral_le
    {t₀ tmin tmax : ℝ} (ht₀ : t₀ ∈ Icc tmin tmax)
    {x₀ : E}
    {a : ℝ≥0}
    {f : ℝ → E → E}
    {K : ℝ≥0} (hlip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith K (f t) (closedBall x₀ (2 * a)))
    (hcont : ∀ x' ∈ closedBall x₀ (2 * a), ContinuousOn (f · x') (Icc tmin tmax))
    {L : ℝ≥0} (hnorm : ∀ t ∈ Icc tmin tmax, ∀ x' ∈ closedBall x₀ (2 * a), ‖f t x'‖ ≤ L)
    (hle : L * max (tmax - t₀) (t₀ - tmin) ≤ a)
    {x : E} (hx : x ∈ closedBall x₀ a)
    (α β : FunSpace ht₀ (closedBall x₀ (2 * a)) x) (n : ℕ) (t : Icc tmin tmax)
    (h : dist ((ODE.FunSpace.integrate ht₀ hlip hcont hnorm hle hx)^[n] α t)
        ((ODE.FunSpace.integrate ht₀ hlip hcont hnorm hle hx)^[n] β t) ≤
      (K * |t - t₀|) ^ n / n ! * dist α β) :
    dist (f t ((ODE.FunSpace.integrate ht₀ hlip hcont hnorm hle hx)^[n] α t))
        (f t ((ODE.FunSpace.integrate ht₀ hlip hcont hnorm hle hx)^[n] β t)) ≤
      K ^ (n + 1) * |t - t₀| ^ n / n ! * dist α β :=
  calc
    _ ≤ K * dist _ _ := hlip t.1 t.2 |>.dist_le_mul _ (FunSpace.mapsTo _ (mem_univ _))
        _ (FunSpace.mapsTo _ (mem_univ _))
    _ ≤ K ^ (n + 1) * |t - t₀| ^ n / n ! * dist α β := by
      rw [pow_succ', mul_assoc, mul_div_assoc, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ K.2
      rwa [← mul_pow]

/-- A time-dependent bound on the distance between the `n`-th iterates of `integrate` on two
curves -/
lemma dist_iterate_integrate_apply_le
    {t₀ tmin tmax : ℝ} (ht₀ : t₀ ∈ Icc tmin tmax)
    {x₀ : E}
    {a : ℝ≥0}
    {f : ℝ → E → E}
    {K : ℝ≥0} (hlip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith K (f t) (closedBall x₀ (2 * a)))
    (hcont : ∀ x' ∈ closedBall x₀ (2 * a), ContinuousOn (f · x') (Icc tmin tmax))
    {L : ℝ≥0} (hnorm : ∀ t ∈ Icc tmin tmax, ∀ x' ∈ closedBall x₀ (2 * a), ‖f t x'‖ ≤ L)
    (hle : L * max (tmax - t₀) (t₀ - tmin) ≤ a)
    {x : E} (hx : x ∈ closedBall x₀ a)
    (α β : FunSpace ht₀ (closedBall x₀ (2 * a)) x) (n : ℕ) (t : Icc tmin tmax) :
    dist ((ODE.FunSpace.integrate ht₀ hlip hcont hnorm hle hx)^[n] α t)
        ((ODE.FunSpace.integrate ht₀ hlip hcont hnorm hle hx)^[n] β t) ≤
      (K * |t - t₀|) ^ n / n ! * dist α β := by
  induction n generalizing t with
  | zero => simpa using ContinuousMap.dist_apply_le_dist _
  | succ n hn =>
    rw [iterate_succ_apply', iterate_succ_apply', dist_eq_norm, integrate_apply, integrate_apply,
      ODE.integrate_apply, ODE.integrate_apply, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub]
    · calc
        _ ≤ ∫ τ in Ι t₀ t, K ^ (n + 1) * |τ - t₀| ^ n / n ! * (dist α β) := by
          rw [intervalIntegral.norm_intervalIntegral_eq] -- need because it's ∫ - ∫
          apply norm_integral_le_of_norm_le <| Continuous.integrableOn_uIoc (by fun_prop)
          apply ae_restrict_mem measurableSet_Ioc |>.mono
          intro t' ht'
          have ht' : t' ∈ Icc tmin tmax := by -- duplicated!
            rw [← uIoc, uIoc_eq_union] at ht'
            have ⟨_, _⟩ := ht₀
            have ⟨_, _⟩ := t.2
            refine or_imp.mpr ⟨fun h ↦ ?_, fun h ↦ ?_⟩ ht' <;>
            · have ⟨_, _⟩ := h
              exact ⟨by linarith, by linarith⟩
          have : t' = (⟨t', ht'⟩ : Icc tmin tmax) := rfl
          rw [this, ← dist_eq_norm, comp_apply, comp_apply, projIcc_val]
          apply dist_comp_iterate_integral_le
          exact hn _
        _ ≤ (K * |t - t₀|) ^ (n + 1) / (n + 1) ! * dist α β := by
          apply le_of_abs_le
          rw [← intervalIntegral.abs_intervalIntegral_eq, intervalIntegral.integral_mul_const,
            intervalIntegral.integral_div, intervalIntegral.integral_const_mul, abs_mul, abs_div,
            abs_mul, intervalIntegral.abs_intervalIntegral_eq, integral_pow_abs_sub_uIoc, abs_div,
            abs_pow, abs_pow, abs_dist, NNReal.abs_eq, abs_abs, mul_div, div_div, ← abs_mul,
            ← Nat.cast_succ, ← Nat.cast_mul, ← Nat.factorial_succ, Nat.abs_cast, ← mul_pow]
    · exact continuousOn_comp -- repeats below; abstract out?
          (continuousOn_uncurry_of_lipschitzOnWith_continuousOn hlip hcont)
          (ContinuousMap.continuous_toFun _ |>.comp_continuousOn continuous_projIcc.continuousOn)
          (fun _ _ ↦ FunSpace.mapsTo _ (mem_univ _))
        |>.mono (uIcc_subset_Icc ht₀ t.2) |>.intervalIntegrable
    · exact continuousOn_comp
          (continuousOn_uncurry_of_lipschitzOnWith_continuousOn hlip hcont)
          (ContinuousMap.continuous_toFun _ |>.comp_continuousOn continuous_projIcc.continuousOn)
          (fun _ _ ↦ FunSpace.mapsTo _ (mem_univ _))
        |>.mono (uIcc_subset_Icc ht₀ t.2) |>.intervalIntegrable

/-- The `n`-th iterate of `integrate` has Lipschitz with constant
$(K \max(t_{\mathrm{max}}, t_{\mathrm{min}})^n / n!$. -/
lemma dist_iterate_integrate_le
    {t₀ tmin tmax : ℝ} (ht₀ : t₀ ∈ Icc tmin tmax)
    {x₀ : E}
    {a : ℝ≥0}
    {f : ℝ → E → E}
    {K : ℝ≥0} (hlip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith K (f t) (closedBall x₀ (2 * a)))
    (hcont : ∀ x' ∈ closedBall x₀ (2 * a), ContinuousOn (f · x') (Icc tmin tmax))
    {L : ℝ≥0} (hnorm : ∀ t ∈ Icc tmin tmax, ∀ x' ∈ closedBall x₀ (2 * a), ‖f t x'‖ ≤ L)
    (hle : L * max (tmax - t₀) (t₀ - tmin) ≤ a)
    {x : E} (hx : x ∈ closedBall x₀ a)
    (α β : FunSpace ht₀ (closedBall x₀ (2 * a)) x) (n : ℕ) :
    dist ((ODE.FunSpace.integrate ht₀ hlip hcont hnorm hle hx)^[n] α)
        ((ODE.FunSpace.integrate ht₀ hlip hcont hnorm hle hx)^[n] β) ≤
      (K * max (tmax - t₀) (t₀ - tmin)) ^ n / n ! * dist α β := by
  have (α' β' : FunSpace ht₀ (closedBall x₀ (2 * ↑a)) x) :
    dist α' β' = dist α'.toContinuousMap β'.toContinuousMap := by rfl -- how to remove this?
  rw [this, ContinuousMap.dist_le]
  · intro t
    apply le_trans <| dist_iterate_integrate_apply_le ht₀ hlip hcont hnorm hle hx α β n t
    apply mul_le_mul_of_nonneg_right _ dist_nonneg
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply pow_le_pow_left₀ <| mul_nonneg K.2 (abs_nonneg _)
    exact mul_le_mul_of_nonneg_left (abs_sub_le_max_sub t.2.1 t.2.2 _) K.2
  · apply mul_nonneg _ dist_nonneg
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply pow_nonneg
    apply mul_nonneg K.2
    apply le_max_of_le_left
    exact sub_nonneg_of_le ht₀.2

/-- Some `n`-th iterate of `integrate` is a contracting map. -/
lemma exists_contractingWith_iterate_integral
    {t₀ tmin tmax : ℝ} (ht₀ : t₀ ∈ Icc tmin tmax)
    {x₀ : E}
    {a : ℝ≥0}
    {f : ℝ → E → E}
    {K : ℝ≥0} (hlip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith K (f t) (closedBall x₀ (2 * a)))
    (hcont : ∀ x' ∈ closedBall x₀ (2 * a), ContinuousOn (f · x') (Icc tmin tmax))
    {L : ℝ≥0} (hnorm : ∀ t ∈ Icc tmin tmax, ∀ x' ∈ closedBall x₀ (2 * a), ‖f t x'‖ ≤ L)
    (hle : L * max (tmax - t₀) (t₀ - tmin) ≤ a)
    {x : E} (hx : x ∈ closedBall x₀ a) :
    ∃ (n : ℕ) (C : ℝ≥0),
      ContractingWith C (ODE.FunSpace.integrate ht₀ hlip hcont hnorm hle hx)^[n] := by
  obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop (K * max (tmax - t₀) (t₀ - tmin))
    |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  have : (0 : ℝ) ≤ (K * max (tmax - t₀) (t₀ - tmin)) ^ n / n ! :=
    div_nonneg (pow_nonneg (mul_nonneg K.2 (le_max_iff.2 <| Or.inl <| sub_nonneg.2 ht₀.2)) _)
      (Nat.cast_nonneg _)
  exact ⟨n, ⟨_, this⟩, hn, LipschitzWith.of_dist_le_mul fun α β ↦
    dist_iterate_integrate_le ht₀ hlip hcont hnorm hle hx α β n⟩

lemma exists_funSpace_integrate_eq
    {t₀ tmin tmax : ℝ} (ht₀ : t₀ ∈ Icc tmin tmax)
    {x₀ : E}
    {a : ℝ≥0}
    {f : ℝ → E → E}
    {K : ℝ≥0} (hlip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith K (f t) (closedBall x₀ (2 * a)))
    (hcont : ∀ x' ∈ closedBall x₀ (2 * a), ContinuousOn (f · x') (Icc tmin tmax))
    {L : ℝ≥0} (hnorm : ∀ t ∈ Icc tmin tmax, ∀ x' ∈ closedBall x₀ (2 * a), ‖f t x'‖ ≤ L)
    (hle : L * max (tmax - t₀) (t₀ - tmin) ≤ a)
    {x : E} (hx : x ∈ closedBall x₀ a) :
    ∃ α : FunSpace ht₀ (closedBall x₀ ((2 * a) : ℝ≥0)) x,
      ODE.FunSpace.integrate ht₀ hlip hcont hnorm hle hx α = α :=
  let ⟨_, _, h⟩ := exists_contractingWith_iterate_integral ht₀ hlip hcont hnorm hle hx
  have : Inhabited <| FunSpace ht₀ (closedBall x₀ (2 * a)) x := inhabited <|
    mem_of_mem_of_subset hx <| Metric.closedBall_subset_closedBall <|
    le_mul_of_one_le_left a.2 one_le_two
  ⟨_, h.isFixedPt_fixedPoint_iterate⟩

end FunSpace

end ODE
