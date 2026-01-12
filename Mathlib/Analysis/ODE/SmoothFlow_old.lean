/-
Copyright (c) 2025 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
module

public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Smooth dependence on initial condition

We prove that the solution of a $C^n$ vector field has $C^n$ dependence on the initial condition.

## Main definitions and results



## Implementation notes



## Tags

differential equation, dynamical system, initial value problem

-/

@[expose] public section

open Function intervalIntegral MeasureTheory Metric Set
open scoped Nat NNReal Topology

lemma le_of_Icc {α : Type*} [Preorder α] {a b : α} (c : Icc a b) : a ≤ b :=
  nonempty_Icc.mp ⟨c.val, c.property⟩

namespace SmoothFlow

/-
We want to define a function `f : E × F → F`, where `F = C(Icc tmin tmax, E)`. The form of `f x₀ α`
is `fun t ↦ x₀ - α t + ∫ τ in t₀..t, f (α (projIcc tmin tmax .. τ))`. Since `f` is only assumed to
be ContDiffOn an open `u : Set E`, this is only well defined when the range of `α` is contained in
`u`. Thus, we define `f` as a piecewise function conditioned on whether `x₀` and `α` stay within
`u`.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → E) (u : Set E)
  {tmin tmax : ℝ} (t₀ : Icc tmin tmax)

open Classical in
/-- The function whose zero set contains integral curves to the vector field `f` -/
noncomputable def implicitEquationAux : E × C(Icc tmin tmax, E) → Icc tmin tmax → E :=
  fun ⟨x₀, α⟩ ↦
    if (x₀, α) ∈ u ×ˢ { α : C(Icc tmin tmax, E) | range α ⊆ u }
    then fun t ↦ x₀ - α t + ∫ τ in t₀..t, f (α (projIcc tmin tmax (le_of_Icc t₀) τ))
    else fun _ ↦ 0

variable {f u t₀} in
open Classical in
lemma implicitEquationAux_apply {x₀ : E} {α : C(Icc tmin tmax, E)} :
    implicitEquationAux f u t₀ (x₀, α) =
      if (x₀, α) ∈ u ×ˢ { α : C(Icc tmin tmax, E) | range α ⊆ u }
        then fun t ↦ x₀ - α t + ∫ τ in t₀..t, f (α (projIcc tmin tmax (le_of_Icc t₀) τ))
        else fun _ ↦ 0 := rfl

variable {f u t₀} in
lemma implicitEquationAux_apply_of_mem {x₀ : E} {α : C(Icc tmin tmax, E)}
    (h : (x₀, α) ∈ u ×ˢ { α : C(Icc tmin tmax, E) | range α ⊆ u }) :
    implicitEquationAux f u t₀ (x₀, α) =
      fun t ↦ x₀ - α t + ∫ τ in t₀..t, f (α (projIcc tmin tmax (le_of_Icc t₀) τ)) := by
  rw [implicitEquationAux_apply, if_pos h]

variable {f u t₀} in
lemma implicitEquationAux_apply_of_not_mem {x₀ : E} {α : C(Icc tmin tmax, E)}
    (h : (x₀, α) ∉ u ×ˢ { α : C(Icc tmin tmax, E) | range α ⊆ u }) :
    implicitEquationAux f u t₀ (x₀, α) = fun _ ↦ 0 := by
  rw [implicitEquationAux_apply, if_neg h]

variable {f u} in
lemma continuous_implicitEquationAux (hf : ContinuousOn f u) (x₀ : E) (α : C(Icc tmin tmax, E)) :
    Continuous (implicitEquationAux f u t₀ (x₀, α)) := by
  by_cases h : (x₀, α) ∈ u ×ˢ { α : C(Icc tmin tmax, E) | range α ⊆ u }
  · rw [implicitEquationAux_apply_of_mem h]
    simp_rw [mem_prod, mem_setOf_eq] at h
    obtain ⟨hx, hα⟩ := h
    apply Continuous.add (by fun_prop)
    -- repetition
    have : (fun t : Icc tmin tmax ↦ ∫ τ in t₀..t, f (α (projIcc tmin tmax (le_of_Icc t₀) τ))) =
        (fun t ↦ ∫ τ in t₀..t, f (α (projIcc tmin tmax (le_of_Icc t₀) τ))) ∘
          (fun t : Icc tmin tmax ↦ (t : ℝ)) := by rfl
    rw [this]
    apply ContinuousOn.comp_continuous (s := Icc tmin tmax) _ (by fun_prop) (by simp)
    nth_rw 8 [← Set.uIcc_of_le (le_of_Icc t₀)]
    apply intervalIntegral.continuousOn_primitive_interval'
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.comp' (t := u) hf ((map_continuous α).comp_continuousOn'
        continuous_projIcc.continuousOn)
      intro t ht
      apply hα
      exact mem_range_self _
    · rw [Set.uIcc_of_le (le_of_Icc t₀)]
      exact Subtype.coe_prop _
  · rw [implicitEquationAux_apply_of_not_mem h]
    fun_prop

variable {f u} in
/-- The requisite function defining the implicit equation `E × F → F` whose zero set contains
integral curves to the vector field `f` -/
noncomputable def implicitEquation (hf : ContinuousOn f u) :
    E × C(Icc tmin tmax, E) → C(Icc tmin tmax, E) :=
  fun p ↦ ⟨implicitEquationAux f u t₀ p, continuous_implicitEquationAux t₀ hf p.1 p.2⟩

lemma implicitEquation_def {hf : ContinuousOn f u} :
    implicitEquation t₀ hf = fun p ↦
      ⟨implicitEquationAux f u t₀ p, continuous_implicitEquationAux t₀ hf p.1 p.2⟩ := rfl

set_option linter.unusedVariables false in
/-- The left (`E`) component of the first derivative of the implicit equation, valid when `x ∈ u`
and `range α ⊆ u` -/
def implicitEquation.leftDeriv (x : E) (α : C(Icc tmin tmax, E)) :
    E →L[ℝ] C(Icc tmin tmax, E) where
  toFun dx := ContinuousMap.const (Icc tmin tmax) dx
  map_add' x y := by congr
  map_smul' r x := by congr
  cont := by
    rw [Metric.continuous_iff]
    have : Nonempty (Icc tmin tmax) := ⟨t₀.val, t₀.property⟩
    simp_rw [ContinuousMap.dist_eq_iSup, ContinuousMap.const_apply, ciSup_const]
    exact fun _ ε hε ↦ ⟨ε, hε, fun _ h ↦ h⟩

lemma implicitEquation.leftDeriv_eq {x : E} {α : C(Icc tmin tmax, E)} :
    implicitEquation.leftDeriv t₀ x α = implicitEquation.leftDeriv t₀ 0 0 := rfl

/-
Need to define the right component of the first derivative of `implicitEquation`.
`implicitEquation : E × F → F`, so this would be `E × F → (F →L[ℝ] F)`.
At every point `x : E`, `f` has derivative `f'`, so `f' : E → (E →L[ℝ] E)`.
Since `f` is `C^1`, `f'` is continuous in the first argument.
At any given point `(x, α) : E × F`, write down the function
`C(Icc tmin tmax, E) → Icc tmin tmax → E`, and then show it is continuous when evaluated at every
`α : C(Icc tmin tmax, E)`.
The function is `dα ↦ t ↦ ∫ τ in t₀ .. t, f' (α τ) (dα τ) - dα t`
Showing it is continuous will require the compactness of `Icc`

Then, we need to show that `E × F → (F →L[ℝ] F)` is continuous in `E × F`, so that
`implicitEquation` is C^1. This allows us to apply the implicit function theorem.
-/

set_option linter.unusedVariables false in
open Classical in
noncomputable def implicitEquation.rightDerivAux (f' : E → E →L[ℝ] E) (x : E)
    (α : C(Icc tmin tmax, E)) :
    C(Icc tmin tmax, E) → Icc tmin tmax → E :=
  fun dα ↦
    if range α ⊆ u then
      -dα + fun t : Icc tmin tmax ↦ ∫ τ in t₀..t,
        f' (α (projIcc tmin tmax (le_of_Icc t₀) τ)) (dα (projIcc tmin tmax (le_of_Icc t₀) τ))
    else 0

lemma implicitEquation.intervalIntegrable {f' : E → E →L[ℝ] E} (hf' : ContinuousOn f' u)
    {α : C(Icc tmin tmax, E)} (hα : range α ⊆ u) (dα : C(Icc tmin tmax, E)) (a b : ℝ) :
    IntervalIntegrable (fun τ ↦ (f' (α (projIcc tmin tmax (le_of_Icc t₀) τ))
      (dα (projIcc tmin tmax (le_of_Icc t₀) τ)))) volume a b := by
  apply Continuous.intervalIntegrable
  have h1 : ContinuousOn (fun xx : E × E ↦ f' xx.1 xx.2) (range α ×ˢ univ) := by
    set K := sSup ((fun x ↦ ‖f' x‖₊) '' range α) with hK
    apply continuousOn_prod_of_continuousOn_lipschitzOnWith' _ K
    · intro x hx
      rw [lipschitzOnWith_univ]
      apply ContinuousLinearMap.lipschitz (f' x) |>.weaken
      rw [hK]
      apply le_csSup _ (mem_image_of_mem _ hx)
      apply IsCompact.bddAbove_image (isCompact_range α.continuous) <|
        Continuous.comp_continuousOn continuous_nnnorm (hf'.mono hα)
    · intro x _
      exact ContinuousOn.clm_apply (hf'.mono hα) continuousOn_const
  have h2 :
    (fun τ ↦ f' (α (projIcc tmin tmax (le_of_Icc t₀) τ))
      (dα (projIcc tmin tmax (le_of_Icc t₀) τ))) =
    (fun xx : E × E ↦ f' xx.1 xx.2) ∘ (fun τ ↦ (α (projIcc tmin tmax (le_of_Icc t₀) τ),
      dα (projIcc tmin tmax (le_of_Icc t₀) τ))) := rfl
  rw [h2]
  apply ContinuousOn.comp_continuous h1 (by continuity)
  intro τ
  simp only [mem_prod, mem_univ, and_true]
  simp

variable {u} in
/-- The first term of the right (`F`) component of the first derivative of the implicit equation,
valid when `x ∈ u` and `range α ⊆ u` -/
-- assume `f'` is continuous on `u` because `f'` is the derivative of a `C^1` function `f`
lemma implicitEquation.continuous_rightDerivAux {f' : E → E →L[ℝ] E} (hf' : ContinuousOn f' u)
    (x : E) (α dα : C(Icc tmin tmax, E)) :
    Continuous (implicitEquation.rightDerivAux u t₀ f' x α dα) := by
  by_cases hα : range α ⊆ u
  · rw [implicitEquation.rightDerivAux, if_pos hα]
    apply Continuous.add (Continuous.neg (ContinuousMapClass.map_continuous _))
    have : (fun t : Icc tmin tmax ↦ ∫ τ in t₀..t,
      f' (α (projIcc tmin tmax (le_of_Icc t₀) τ)) (dα (projIcc tmin tmax (le_of_Icc t₀) τ))) =
        (fun t ↦ ∫ τ in t₀..t,
          f' (α (projIcc tmin tmax (le_of_Icc t₀) τ)) (dα (projIcc tmin tmax (le_of_Icc t₀) τ))) ∘
        (fun t : Icc tmin tmax ↦ (t : ℝ)) := by rfl
    rw [this]
    apply ContinuousOn.comp_continuous (s := Icc tmin tmax) _ (by fun_prop) (by simp)
    nth_rw 14 [← Set.uIcc_of_le (le_of_Icc t₀)]
    apply intervalIntegral.continuousOn_primitive_interval'
      (implicitEquation.intervalIntegrable u t₀ hf' hα _ _ _)
    rw [Set.uIcc_of_le (le_of_Icc t₀)]
    exact Subtype.coe_prop _
  · rw [rightDerivAux, if_neg hα]
    exact continuous_zero

variable {u} in
noncomputable def implicitEquation.rightDerivAux' {f' : E → E →L[ℝ] E}
    (hf' : ContinuousOn f' u) (x : E) (α : C(Icc tmin tmax, E)) :
    C(Icc tmin tmax, E) → C(Icc tmin tmax, E) :=
  fun dα ↦ ⟨implicitEquation.rightDerivAux u t₀ f' x α dα,
    implicitEquation.continuous_rightDerivAux t₀ hf' x α dα⟩

variable {u t₀} in
lemma implicitEquation.rightDerivAux'_def {f' : E → E →L[ℝ] E}
    {hf' : ContinuousOn f' u} {x : E} {α : C(Icc tmin tmax, E)} :
    implicitEquation.rightDerivAux' t₀ hf' x α =
      fun dα ↦ ⟨implicitEquation.rightDerivAux u t₀ f' x α dα,
        implicitEquation.continuous_rightDerivAux t₀ hf' x α dα⟩ := rfl

variable {u t₀} in
lemma implicitEquation.rightDerivAux'_eq_zero_of_not_mem {f' : E → E →L[ℝ] E}
    {hf' : ContinuousOn f' u} {x : E} {α : C(Icc tmin tmax, E)} (hα : ¬range α ⊆ u) :
    implicitEquation.rightDerivAux' t₀ hf' x α = 0 := by
  rw [implicitEquation.rightDerivAux'_def]
  simp_rw [implicitEquation.rightDerivAux, if_neg hα]
  rfl

-- map_add, map_smul for implicitEquation.rightDerivAux'
lemma implicitEquation.rightDerivAux'_add {f' : E → E →L[ℝ] E} (hf' : ContinuousOn f' u)
    (x : E) (α dα dα' : C(Icc tmin tmax, E)) :
    implicitEquation.rightDerivAux' t₀ hf' x α (dα + dα') =
      implicitEquation.rightDerivAux' t₀ hf' x α dα +
        implicitEquation.rightDerivAux' t₀ hf' x α dα' := by
  simp only [implicitEquation.rightDerivAux']
  congr
  simp only [ContinuousMap.coe_mk, implicitEquation.rightDerivAux]
  by_cases hα : range α ⊆ u
  · simp only [if_pos hα]
    rw [ContinuousMap.coe_add, neg_add]
    simp_rw [Pi.add_apply, map_add]
    funext t
    simp only [Pi.add_apply, Pi.neg_apply]
    rw [intervalIntegral.integral_add (implicitEquation.intervalIntegrable u t₀ hf' hα _ _ _)
      (implicitEquation.intervalIntegrable u t₀ hf' hα _ _ _), add_add_add_comm]
  · simp [if_neg hα]

lemma implicitEquation.rightDerivAux'_smul {f' : E → E →L[ℝ] E} (hf' : ContinuousOn f' u)
    (x : E) (α : C(Icc tmin tmax, E)) (r : ℝ) (dα : C(Icc tmin tmax, E)) :
    implicitEquation.rightDerivAux' t₀ hf' x α (r • dα) =
      r • implicitEquation.rightDerivAux' t₀ hf' x α dα := by
  simp only [implicitEquation.rightDerivAux']
  congr
  simp only [ContinuousMap.coe_mk, implicitEquation.rightDerivAux]
  by_cases hα : range α ⊆ u
  · simp only [if_pos hα]
    rw [ContinuousMap.coe_smul, ← neg_smul]
    simp_rw [Pi.smul_apply, map_smul]
    funext t
    simp only [Pi.smul_apply, Pi.add_apply, smul_add]
    rw [intervalIntegral.integral_smul]
    simp
  · simp [if_neg hα]

lemma implicitEquation.continuous_rightDerivAux' {f' : E → E →L[ℝ] E} (hf' : ContinuousOn f' u)
    (x : E) (α : C(Icc tmin tmax, E)) :
    Continuous (implicitEquation.rightDerivAux' t₀ hf' x α) := by
  by_cases hα : range α ⊆ u
  · apply ContinuousMap.continuous_of_continuous_uncurry
    rw [implicitEquation.rightDerivAux'_def]
    simp_rw [implicitEquation.rightDerivAux, if_pos hα, ContinuousMap.coe_mk] -- missing lemma
    simp_rw [Pi.add_apply, Pi.neg_apply]
    rw [Function.uncurry_def]
    apply continuous_eval.neg.add
    have heq : (fun p : C(Icc tmin tmax, E) × Icc tmin tmax ↦
      ∫ (τ : ℝ) in t₀..p.2, f' (α (projIcc tmin tmax (le_of_Icc t₀) τ))
        (p.1 (projIcc tmin tmax (le_of_Icc t₀) τ))) = (fun p : C(Icc tmin tmax, E) × ℝ ↦
      ∫ (τ : ℝ) in t₀..p.2, f' (α (projIcc tmin tmax (le_of_Icc t₀) τ))
        (p.1 (projIcc tmin tmax (le_of_Icc t₀) τ))) ∘
      (fun p : C(Icc tmin tmax, E) × Icc tmin tmax ↦ (p.1, (p.2 : ℝ))) := rfl
    have hcont : Continuous (fun p : C(Icc tmin tmax, E) × Icc tmin tmax ↦ (p.1, (p.2 : ℝ))) :=
      continuous_fst.prodMk <| Continuous.comp' continuous_subtype_val continuous_snd
    rw [heq]
    apply Continuous.comp _ hcont
    apply intervalIntegral.continuous_parametric_primitive_of_continuous
      (f := (fun (p1 : C(Icc tmin tmax, E)) (τ : ℝ) ↦
        f' (α (projIcc tmin tmax (le_of_Icc t₀) τ)) (p1 (projIcc tmin tmax (le_of_Icc t₀) τ))))
    rw [Function.uncurry_def]
    apply Continuous.clm_apply
    · apply hf'.comp_continuous (α.continuous.comp' (continuous_projIcc.comp' continuous_snd))
        (fun p ↦ hα (mem_range_self _)) -- extract continuity lemma
    · apply continuous_fst.eval
      exact continuous_projIcc.comp' continuous_snd
  · rw [implicitEquation.rightDerivAux'_eq_zero_of_not_mem hα]
    exact continuous_zero

/-- The left (`E`) part of the first derivative of the implicit equation, valid when `x ∈ u` and
`range α ⊆ u` -/
noncomputable def implicitEquation.rightDerivAux'' {f' : E → E →L[ℝ] E} (hf' : ContinuousOn f' u)
    (x : E) (α : C(Icc tmin tmax, E)) :
    C(Icc tmin tmax, E) →L[ℝ] C(Icc tmin tmax, E) where
  toFun := implicitEquation.rightDerivAux' t₀ hf' x α
  map_add' _ _ := implicitEquation.rightDerivAux'_add ..
  map_smul' _ _ := implicitEquation.rightDerivAux'_smul ..
  cont := implicitEquation.continuous_rightDerivAux' u t₀ hf' x α

-- think about `u`
noncomputable def implicitEquation.rightDeriv (hu : IsOpen u) (hf : ContDiffOn ℝ 1 f u) (x : E)
    (α : C(Icc tmin tmax, E)) : C(Icc tmin tmax, E) →L[ℝ] C(Icc tmin tmax, E) :=
  implicitEquation.rightDerivAux'' u t₀ (hf.continuousOn_fderiv_of_isOpen hu le_rfl) x α

lemma implicitEquation.rightDeriv_eq {hu : IsOpen u} {hf : ContDiffOn ℝ 1 f u} {x : E}
    {α : C(Icc tmin tmax, E)} :
    implicitEquation.rightDeriv f u t₀ hu hf x α = implicitEquation.rightDeriv f u t₀ hu hf 0 α :=
  rfl

lemma implicitEquation.continuousOn_rightDeriv (hu : IsOpen u) (hf : ContDiffOn ℝ 1 f u) (x : E) :
    ContinuousOn (implicitEquation.rightDeriv f u t₀ hu hf x)
      {β : C(Icc tmin tmax, E) | MapsTo β univ u} := by
  sorry

-- probably easier to prove left and right components separately first
lemma hasFDerivAt_implicitEquation (hu : IsOpen u) (hf : ContDiffOn ℝ 1 f u) (x : E)
    (α : C(Icc tmin tmax, E)) :
    HasFDerivAt (implicitEquation t₀ hf.continuousOn)
      ((implicitEquation.leftDeriv t₀ x α).coprod (implicitEquation.rightDeriv f u t₀ hu hf x α))
      (x, α) := by
  sorry

lemma isContDiffImplicitAt_implicitEquation (hu : IsOpen u) (hf : ContDiffOn ℝ 1 f u) {x : E}
    (hx : x ∈ u) {α : C(Icc tmin tmax, E)} (hα : range α ⊆ u) :
    IsContDiffImplicitAt 1 (implicitEquation t₀ hf.continuousOn)
      ((implicitEquation.leftDeriv t₀ x α).coprod (implicitEquation.rightDeriv f u t₀ hu hf x α))
      (x, α) where
  hasFDerivAt := hasFDerivAt_implicitEquation ..
  contDiffAt := by
    rw [contDiffAt_one_iff]
    use fun p ↦ ((implicitEquation.leftDeriv t₀ p.1 p.2).coprod
      (implicitEquation.rightDeriv f u t₀ hu hf p.1 p.2))
    have (p : E × C((Icc tmin tmax), E)) := hasFDerivAt_implicitEquation f u t₀ hu hf p.1 p.2
    use univ ×ˢ {β : C(Icc tmin tmax, E) | MapsTo β univ u}
    refine ⟨?_, ?_, fun p _ ↦ this p⟩
    · apply prod_mem_nhds Filter.univ_mem
      apply (ContinuousMap.isOpen_setOf_mapsTo isCompact_univ hu).mem_nhds
      rw [mem_setOf_eq, mapsTo_univ_iff]
      intro t
      apply hα
      exact mem_range_self _
    · apply ContinuousOn.continuousLinearMapCoprod
      · simp_rw [implicitEquation.leftDeriv_eq]
        exact continuousOn_const
      · simp_rw [implicitEquation.rightDeriv_eq]
        apply ContinuousOn.comp (t := {β : C(Icc tmin tmax, E) | MapsTo β univ u}) _
          continuousOn_snd mapsTo_snd_prod
        apply implicitEquation.continuousOn_rightDeriv _ _ _ hu hf
  bijective := sorry
  ne_zero := by simp

end SmoothFlow
