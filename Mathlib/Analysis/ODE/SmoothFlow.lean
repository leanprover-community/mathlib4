/-
Copyright (c) 2025 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import Mathlib.Analysis.ODE.PicardLindelof

/-!
# Smooth dependence on initial condition

We prove that the solution of a $C^n$ vector field has $C^n$ dependence on the initial condition.

## Main definitions and results



## Implementation notes



## Tags

differential equation, dynamical system, initial value problem

-/

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
      exact Set.mem_range_self _
    · rw [Set.uIcc_of_le (le_of_Icc t₀)]
      exact Subtype.coe_prop _
  · rw [implicitEquationAux_apply_of_not_mem h]
    fun_prop

variable {f u} in
/-- The requisite function defining the implicit equation `E × F → F` whose zero set contains
integral curves to the vector field `f` -/
noncomputable def implicitEquation (hf : ContinuousOn f u) :
    E × C(Icc tmin tmax, E) → C(Icc tmin tmax, E) :=
  fun ⟨x₀, α⟩ ↦ ⟨implicitEquationAux f u t₀ ⟨x₀, α⟩, continuous_implicitEquationAux t₀ hf x₀ α⟩

set_option linter.unusedVariables false in
/-- The left (`E`) part of the first derivative of the implicit equation, valid when `x ∈ u` and
`range α ⊆ u` -/
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

set_option linter.unusedVariables false in
noncomputable def implicitEquation.rightDerivAux (f' : E → E →L[ℝ] E) (x : E)
    (α : C(Icc tmin tmax, E)) :
    C(Icc tmin tmax, E) → Icc tmin tmax → E :=
  fun dα ↦ -dα + fun t : Icc tmin tmax ↦ ∫ τ in t₀..t,
    f' (α (projIcc tmin tmax (le_of_Icc t₀) τ)) (dα (projIcc tmin tmax (le_of_Icc t₀) τ))

-- need that f' is continuous on u
lemma implicitEquation.continuous_rightDerivAux {f' : E → E →L[ℝ] E} (hf' : ContinuousOn f' u)
    (x : E) (α dα : C(Icc tmin tmax, E)) :
    Continuous (implicitEquation.rightDerivAux t₀ f' x α dα) := by
  rw [implicitEquation.rightDerivAux]
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
  · apply ContinuousOn.intervalIntegrable
    -- use Continuous.comp₂ on the uncurry of f', but need to first show that uncurry f' is cont
    have : (fun x ↦ (f' (α (projIcc tmin tmax (le_of_Icc t₀) x)))
          (dα (projIcc tmin tmax (le_of_Icc t₀) x))) =
        fun x ↦ curry (uncurry (fun y y' ↦ f' y y')) (α (projIcc tmin tmax (le_of_Icc t₀) x))
          ((dα (projIcc tmin tmax (le_of_Icc t₀) x))) := by
      rfl
    rw [this]
    apply Continuous.comp_continuousOn'
    ·

      sorry
    · sorry
  · rw [Set.uIcc_of_le (le_of_Icc t₀)]
    exact Subtype.coe_prop _

noncomputable def implicitEquation.rightDerivAux' (f' : E → E →L[ℝ] E) (x : E)
    (α : C(Icc tmin tmax, E)) :
    C(Icc tmin tmax, E) → C(Icc tmin tmax, E) :=
  fun dα ↦ ⟨implicitEquation.rightDerivAux t₀ f' x α dα,
    implicitEquation.continuous_rightDerivAux t₀ f' x α dα⟩

-- map_add, map_smul for implicitEquation.rightDerivAux'

lemma implicitEquation.continuous_rightDerivAux' (f' : E → E →L[ℝ] E) (x : E)
    (α : C(Icc tmin tmax, E)) :
    Continuous (implicitEquation.rightDerivAux' t₀ f' x α) := by sorry

/-- The left (`E`) part of the first derivative of the implicit equation, valid when `x ∈ u` and
`range α ⊆ u` -/
noncomputable def implicitEquation.rightDeriv (f' : E → E →L[ℝ] E) (x : E)
    (α : C(Icc tmin tmax, E)) :
    C(Icc tmin tmax, E) →L[ℝ] C(Icc tmin tmax, E) where
  toFun := implicitEquation.rightDerivAux' t₀ f' x α
  map_add' dα1 dα2 := sorry
  map_smul' r dα := sorry
  cont := implicitEquation.continuous_rightDerivAux' t₀ f' x α


-- namespace test

-- variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
--   {f : E → E} {α : ℝ → E} {s : Set ℝ} {u : Set E} {t₀ tmin tmax : ℝ}

-- /-- We wish to apply the implicit function theorem on an implicit equation `f(x, α) = 0`, where
-- `x : E` and `α : C(Icc tmin tmax, E)`. This `funSpace` is the open subset of `C(Icc tmin tmax, E)`
-- containing curves bounded by `u`. -/
-- def funSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
--   (tmin tmax : ℝ) (u : Set E) := { α : C(Icc tmin tmax, E) | range α ⊆ u }

-- lemma isOpen_funSpace (hu : IsOpen u) : IsOpen (funSpace tmin tmax u) := by
--   simpa [funSpace, range_subset_iff, ← mapsTo_univ_iff] using
--     ContinuousMap.isOpen_setOf_mapsTo isCompact_univ hu

-- /-- The implicit function `f : E × C(Icc tmin tmax, E) → C(Icc tmin tmax, E)`, whose level set of
-- `(x, α)` contains the solutions to the initial value problem. -/
-- noncomputable def implicitFun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → E)
--     {x₀ : E} (hf : ContDiffAt ℝ 1 f x₀) (α : C(Icc tmin tmax, E)) (t₀ : Icc tmin tmax) :
--     C(Icc tmin tmax, E) where
--   toFun := fun t ↦
--     x₀ - α t + ∫ τ in t₀..t, f (α (projIcc tmin tmax (nonempty_Icc.mp ⟨t₀.val, t₀.property⟩) τ))
--   continuous_toFun := by
--     have h : tmin ≤ tmax := nonempty_Icc.mp ⟨t₀.val, t₀.property⟩
--     refine Continuous.add ?_ ?_
--     · exact Continuous.sub continuous_const α.continuous
--     · have : (fun t : Icc tmin tmax ↦ ∫ τ in t₀..t, f (α (projIcc tmin tmax h τ))) =
--           (fun t : ℝ ↦ ∫ τ in t₀..t, f (α (projIcc tmin tmax h τ))) ∘ (fun t : Icc tmin tmax ↦ t) :=
--         rfl
--       rw [this]
--       apply Continuous.comp _ continuous_subtype_val
--       apply intervalIntegral.continuous_primitive
--       intro t₁ t₂
--       apply Continuous.intervalIntegrable
--       apply Continuous.comp hf.continuous
--       -- need `α` to stay within `u` and `f` to be continuous on `u`
--       sorry

-- -- generalise!
-- def fderivImplicitFun₁ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E) :
--     E →L[ℝ] C(Icc tmin tmax, E) where
--   toFun dx := ContinuousMap.const (Icc tmin tmax) dx
--   map_add' x y := by congr
--   map_smul' r x := by congr
--   cont := sorry

-- -- WRITE ALL THIS DOWN SO WE KNOW WHAT'S GOING ON!

-- noncomputable def fderivImplicitFun₂Fun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
--     {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (f' : E → E →L[ℝ] E) (α : C(Icc tmin tmax, E))
--     (dα : C(Icc tmin tmax, E)) : C(Icc tmin tmax, E) where
--   toFun t := -dα t + ∫ τ in t₀..t, f' (α t) (dα t)
--   continuous_toFun := sorry

-- noncomputable def fderivImplicitFun₂ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
--     {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (f' : E → E →L[ℝ] E) (α : C(Icc tmin tmax, E)) :
--     C(Icc tmin tmax, E) →L[ℝ] C(Icc tmin tmax, E) where
--   toFun dα := fderivImplicitFun₂Fun t₀ f' α dα  -- need to define a continuous curve first
--   map_add' α β := sorry
--   map_smul' r α := sorry
--   cont := sorry

-- lemma hasFDerivAt_implicitFun₁ (x₀ : E) (α : C(Icc tmin tmax, E)) (t₀ : Icc tmin tmax) :
--     HasFDerivAt (fun x ↦ implicitFun f x α t₀) (fderivImplicitFun₁ x₀) x₀ := sorry

-- lemma hasFDerivAt_implicitFun₂ {f' : E → E →L[ℝ] E} (hf : ∀ x ∈ u, HasFDerivAt f (f' x) x) (x₀ : E)
--     (α : C(Icc tmin tmax, E)) (t₀ : Icc tmin tmax) :
--     HasFDerivAt (fun α ↦ implicitFun f x₀ α t₀) (fderivImplicitFun₂ t₀ f' α) α := sorry

-- end test

end SmoothFlow
