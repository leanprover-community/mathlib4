/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.TangentCone.Defs
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Sqrt
import Mathlib.Init
import Mathlib.Order.Filter.Prod
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.NhdsWithin

/-!
# The Fréchet derivative: congruence properties

Lemmas about congruence properties of the Fréchet derivative under change of function, set, etc.

## Tags

derivative, differentiable, Fréchet, calculus

-/

public section

open Filter Asymptotics ContinuousLinearMap Set Metric Topology NNReal ENNReal

noncomputable section

section
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

variable {f f₀ f₁ g : E → F}
variable {f' f₀' f₁' g' : E →L[𝕜] F}
variable {x : E}
variable {s t : Set E}
variable {L : Filter (E × E)}

section congr

/-! ### congr properties of the derivative -/

theorem hasFDerivWithinAt_congr_set_nhdsNE (h : s =ᶠ[𝓝[≠] x] t) :
    HasFDerivWithinAt f f' s x ↔ HasFDerivWithinAt f f' t x :=
  calc
    HasFDerivWithinAt f f' s x ↔ HasFDerivWithinAt f f' (s \ {x}) x :=
      hasFDerivWithinAt_diff_singleton_self.symm
    _ ↔ HasFDerivWithinAt f f' (t \ {x}) x := by
      suffices 𝓝[s \ {x}] x = 𝓝[t \ {x}] x by simp only [HasFDerivWithinAt, this]
      simpa only [set_eventuallyEq_iff_inf_principal, ← nhdsWithin_inter', diff_eq, inter_comm]
        using h
    _ ↔ HasFDerivWithinAt f f' t x := hasFDerivWithinAt_diff_singleton_self

theorem hasFDerivWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) :
    HasFDerivWithinAt f f' s x ↔ HasFDerivWithinAt f f' t x :=
  hasFDerivWithinAt_congr_set_nhdsNE <| h.filter_mono inf_le_left

/-- In the case `y = x`, see also `hasFDerivWithinAt_congr_set_nhdsNE`,
which does not require the domain to be a T₁ space. -/
theorem hasFDerivWithinAt_congr_set' [T1Space E] (y : E)
    (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    HasFDerivWithinAt f f' s x ↔ HasFDerivWithinAt f f' t x := by
  rcases eq_or_ne x y with rfl | hne
  · exact hasFDerivWithinAt_congr_set_nhdsNE h
  · rw [hne.nhdsWithin_compl_singleton] at h
    exact hasFDerivWithinAt_congr_set h

theorem differentiableWithinAt_congr_set_nhdsNE (h : s =ᶠ[𝓝[≠] x] t) :
    DifferentiableWithinAt 𝕜 f s x ↔ DifferentiableWithinAt 𝕜 f t x :=
  exists_congr fun _ => hasFDerivWithinAt_congr_set_nhdsNE h

/-- In the case `y = x`, see also `differentiableWithinAt_congr_set_nhdsNE`,
which does not require the domain to be a T₁ space. -/
theorem differentiableWithinAt_congr_set' [T1Space E] (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    DifferentiableWithinAt 𝕜 f s x ↔ DifferentiableWithinAt 𝕜 f t x :=
  exists_congr fun _ => hasFDerivWithinAt_congr_set' _ h

theorem differentiableWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) :
    DifferentiableWithinAt 𝕜 f s x ↔ DifferentiableWithinAt 𝕜 f t x :=
  exists_congr fun _ => hasFDerivWithinAt_congr_set h

theorem fderivWithin_congr_set_nhdsNE (h : s =ᶠ[𝓝[≠] x] t) :
    fderivWithin 𝕜 f s x = fderivWithin 𝕜 f t x := by
  classical
  simp only [fderivWithin, differentiableWithinAt_congr_set_nhdsNE h,
    hasFDerivWithinAt_congr_set_nhdsNE h]

/-- In the case `y = x`, see also `fderivWithin_congr_set_nhdsNE`,
which does not require the domain to be a T₁ space. -/
theorem fderivWithin_congr_set' [T1Space E] (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    fderivWithin 𝕜 f s x = fderivWithin 𝕜 f t x := by
  classical
  simp only [fderivWithin, differentiableWithinAt_congr_set' _ h, hasFDerivWithinAt_congr_set' _ h]

theorem fderivWithin_congr_set (h : s =ᶠ[𝓝 x] t) : fderivWithin 𝕜 f s x = fderivWithin 𝕜 f t x :=
  fderivWithin_congr_set_nhdsNE <| h.filter_mono inf_le_left

theorem fderivWithin_eventually_congr_set' [T1Space E] (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    fderivWithin 𝕜 f s =ᶠ[𝓝 x] fderivWithin 𝕜 f t :=
  (eventually_nhds_nhdsWithin.2 h).mono fun _ => fderivWithin_congr_set' y

theorem fderivWithin_eventually_congr_set (h : s =ᶠ[𝓝 x] t) :
    fderivWithin 𝕜 f s =ᶠ[𝓝 x] fderivWithin 𝕜 f t :=
  (eventually_eventually_nhds.2 h).mono fun _ => fderivWithin_congr_set

theorem Filter.EventuallyEq.hasFDerivAtFilter_iff (h₀ : Prod.map f₀ f₀ =ᶠ[L] Prod.map f₁ f₁)
    (h₁ : ∀ x, f₀' x = f₁' x) : HasFDerivAtFilter f₀ f₀' L ↔ HasFDerivAtFilter f₁ f₁' L := by
  simp only [hasFDerivAtFilter_iff_isLittleOTVS]
  exact isLittleOTVS_congr (h₀.mono fun y hy => by simp_all [Prod.map]) .rfl

theorem Filter.EventuallyEq.hasStrictFDerivAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) (h' : ∀ y, f₀' y = f₁' y) :
    HasStrictFDerivAt f₀ f₀' x ↔ HasStrictFDerivAt f₁ f₁' x :=
  h.prodMap_nhds h |>.hasFDerivAtFilter_iff h'

theorem HasStrictFDerivAt.congr_fderiv (h : HasStrictFDerivAt f f' x) (h' : f' = g') :
    HasStrictFDerivAt f g' x :=
  h' ▸ h

theorem HasFDerivAt.congr_fderiv (h : HasFDerivAt f f' x) (h' : f' = g') : HasFDerivAt f g' x :=
  h' ▸ h

theorem HasFDerivWithinAt.congr_fderiv (h : HasFDerivWithinAt f f' s x) (h' : f' = g') :
    HasFDerivWithinAt f g' s x :=
  h' ▸ h

theorem HasStrictFDerivAt.congr_of_eventuallyEq (h : HasStrictFDerivAt f f' x)
    (h₁ : f =ᶠ[𝓝 x] f₁) : HasStrictFDerivAt f₁ f' x :=
  (h₁.hasStrictFDerivAt_iff fun _ => rfl).1 h

theorem HasFDerivAtFilter.congr_of_eventuallyEq (h : HasFDerivAtFilter f f' L)
    (hL : Prod.map f₁ f₁ =ᶠ[L] Prod.map f f) :
    HasFDerivAtFilter f₁ f' L :=
  (hL.hasFDerivAtFilter_iff fun _ => rfl).2 h

theorem Filter.EventuallyEq.hasFDerivAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) :
    HasFDerivAt f₀ f' x ↔ HasFDerivAt f₁ f' x :=
  h.prodMap (h.filter_mono <| pure_le_nhds _) |>.hasFDerivAtFilter_iff fun _ => rfl

theorem Filter.EventuallyEq.differentiableAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) :
    DifferentiableAt 𝕜 f₀ x ↔ DifferentiableAt 𝕜 f₁ x :=
  exists_congr fun _ => h.hasFDerivAt_iff

theorem Filter.EventuallyEq.hasFDerivWithinAt_iff (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : f₀ x = f₁ x) :
    HasFDerivWithinAt f₀ f' s x ↔ HasFDerivWithinAt f₁ f' s x :=
  h.prodMap (by assumption) |>.hasFDerivAtFilter_iff fun _ => _root_.rfl

theorem Filter.EventuallyEq.hasFDerivWithinAt_iff_of_mem (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : x ∈ s) :
    HasFDerivWithinAt f₀ f' s x ↔ HasFDerivWithinAt f₁ f' s x :=
  h.hasFDerivWithinAt_iff (h.eq_of_nhdsWithin hx)

theorem Filter.EventuallyEq.differentiableWithinAt_iff (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : f₀ x = f₁ x) :
    DifferentiableWithinAt 𝕜 f₀ s x ↔ DifferentiableWithinAt 𝕜 f₁ s x :=
  exists_congr fun _ => h.hasFDerivWithinAt_iff hx

theorem Filter.EventuallyEq.differentiableWithinAt_iff_of_mem (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : x ∈ s) :
    DifferentiableWithinAt 𝕜 f₀ s x ↔ DifferentiableWithinAt 𝕜 f₁ s x :=
  h.differentiableWithinAt_iff (h.eq_of_nhdsWithin hx)

theorem HasFDerivWithinAt.congr_of_eventuallyEq (h : HasFDerivWithinAt f f' s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : HasFDerivWithinAt f₁ f' s x :=
  h₁.hasFDerivWithinAt_iff hx |>.mpr h

theorem HasFDerivWithinAt.congr (h : HasFDerivWithinAt f f' s x) (hs : EqOn f₁ f s)
    (hx : f₁ x = f x) : HasFDerivWithinAt f₁ f' s x :=
  h.congr_of_eventuallyEq hs.eventuallyEq_nhdsWithin hx

theorem HasFDerivWithinAt.congr' (h : HasFDerivWithinAt f f' s x) (hs : EqOn f₁ f s) (hx : x ∈ s) :
    HasFDerivWithinAt f₁ f' s x :=
  h.congr hs (hs hx)

theorem HasFDerivWithinAt.congr_mono (h : HasFDerivWithinAt f f' s x) (ht : EqOn f₁ f t)
    (hx : f₁ x = f x) (h₁ : t ⊆ s) : HasFDerivWithinAt f₁ f' t x :=
  h.mono h₁ |>.congr ht hx

theorem HasFDerivAt.congr_of_eventuallyEq (h : HasFDerivAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f) :
    HasFDerivAt f₁ f' x :=
  h₁.hasFDerivAt_iff.mpr h

theorem DifferentiableWithinAt.congr_mono (h : DifferentiableWithinAt 𝕜 f s x) (ht : EqOn f₁ f t)
    (hx : f₁ x = f x) (h₁ : t ⊆ s) : DifferentiableWithinAt 𝕜 f₁ t x :=
  (HasFDerivWithinAt.congr_mono h.hasFDerivWithinAt ht hx h₁).differentiableWithinAt

theorem DifferentiableWithinAt.congr (h : DifferentiableWithinAt 𝕜 f s x) (ht : ∀ x ∈ s, f₁ x = f x)
    (hx : f₁ x = f x) : DifferentiableWithinAt 𝕜 f₁ s x :=
  DifferentiableWithinAt.congr_mono h ht hx (Subset.refl _)

theorem DifferentiableWithinAt.congr_of_eventuallyEq (h : DifferentiableWithinAt 𝕜 f s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : DifferentiableWithinAt 𝕜 f₁ s x :=
  (h.hasFDerivWithinAt.congr_of_eventuallyEq h₁ hx).differentiableWithinAt

theorem DifferentiableWithinAt.congr_of_eventuallyEq_of_mem (h : DifferentiableWithinAt 𝕜 f s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) : DifferentiableWithinAt 𝕜 f₁ s x :=
  h.congr_of_eventuallyEq h₁ (mem_of_mem_nhdsWithin hx h₁ :)

theorem DifferentiableWithinAt.congr_of_eventuallyEq_insert (h : DifferentiableWithinAt 𝕜 f s x)
    (h₁ : f₁ =ᶠ[𝓝[insert x s] x] f) : DifferentiableWithinAt 𝕜 f₁ s x :=
  (h.insert.congr_of_eventuallyEq_of_mem h₁ (mem_insert _ _)).of_insert

theorem DifferentiableOn.congr_mono (h : DifferentiableOn 𝕜 f s) (h' : ∀ x ∈ t, f₁ x = f x)
    (h₁ : t ⊆ s) : DifferentiableOn 𝕜 f₁ t := fun x hx => (h x (h₁ hx)).congr_mono h' (h' x hx) h₁

theorem DifferentiableOn.congr (h : DifferentiableOn 𝕜 f s) (h' : ∀ x ∈ s, f₁ x = f x) :
    DifferentiableOn 𝕜 f₁ s := fun x hx => (h x hx).congr h' (h' x hx)

theorem differentiableOn_congr (h' : ∀ x ∈ s, f₁ x = f x) :
    DifferentiableOn 𝕜 f₁ s ↔ DifferentiableOn 𝕜 f s :=
  ⟨fun h => DifferentiableOn.congr h fun y hy => (h' y hy).symm, fun h =>
    DifferentiableOn.congr h h'⟩

theorem DifferentiableAt.congr_of_eventuallyEq (h : DifferentiableAt 𝕜 f x) (hL : f₁ =ᶠ[𝓝 x] f) :
    DifferentiableAt 𝕜 f₁ x :=
  hL.differentiableAt_iff.2 h

theorem DifferentiableWithinAt.fderivWithin_congr_mono
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]
    (h : DifferentiableWithinAt 𝕜 f s x)
    (hs : EqOn f₁ f t) (hx : f₁ x = f x) (hxt : UniqueDiffWithinAt 𝕜 t x) (h₁ : t ⊆ s) :
    fderivWithin 𝕜 f₁ t x = fderivWithin 𝕜 f s x :=
  (HasFDerivWithinAt.congr_mono h.hasFDerivWithinAt hs hx h₁).fderivWithin hxt

set_option backward.isDefEq.respectTransparency false in
theorem Filter.EventuallyEq.fderivWithin_eq (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x := by
  classical
  simp only [fderivWithin, DifferentiableWithinAt, hs.hasFDerivWithinAt_iff hx]

theorem Filter.EventuallyEq.fderivWithin_eq_of_mem (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) :
    fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x :=
  hs.fderivWithin_eq (mem_of_mem_nhdsWithin hx hs :)

theorem Filter.EventuallyEq.fderivWithin_eq_of_insert (hs : f₁ =ᶠ[𝓝[insert x s] x] f) :
    fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x := by
  apply Filter.EventuallyEq.fderivWithin_eq (nhdsWithin_mono _ (subset_insert x s) hs)
  exact (mem_of_mem_nhdsWithin (mem_insert x s) hs :)

theorem Filter.EventuallyEq.fderivWithin' (hs : f₁ =ᶠ[𝓝[s] x] f) (ht : t ⊆ s) :
    fderivWithin 𝕜 f₁ t =ᶠ[𝓝[s] x] fderivWithin 𝕜 f t :=
  (eventually_eventually_nhdsWithin.2 hs).mp <|
    eventually_mem_nhdsWithin.mono fun _y hys hs =>
      EventuallyEq.fderivWithin_eq (hs.filter_mono <| nhdsWithin_mono _ ht)
        (hs.self_of_nhdsWithin hys)

protected theorem Filter.EventuallyEq.fderivWithin (hs : f₁ =ᶠ[𝓝[s] x] f) :
    fderivWithin 𝕜 f₁ s =ᶠ[𝓝[s] x] fderivWithin 𝕜 f s :=
  hs.fderivWithin' Subset.rfl

theorem Filter.EventuallyEq.fderivWithin_eq_of_nhds (h : f₁ =ᶠ[𝓝 x] f) :
    fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x :=
  (h.filter_mono nhdsWithin_le_nhds).fderivWithin_eq h.self_of_nhds

theorem fderivWithin_congr (hs : EqOn f₁ f s) (hx : f₁ x = f x) :
    fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x :=
  (hs.eventuallyEq.filter_mono inf_le_right).fderivWithin_eq hx

theorem fderivWithin_congr' (hs : EqOn f₁ f s) (hx : x ∈ s) :
    fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x :=
  fderivWithin_congr hs (hs hx)

theorem Filter.EventuallyEq.fderiv_eq (h : f₁ =ᶠ[𝓝 x] f) : fderiv 𝕜 f₁ x = fderiv 𝕜 f x := by
  rw [← fderivWithin_univ, ← fderivWithin_univ, h.fderivWithin_eq_of_nhds]

protected theorem Filter.EventuallyEq.fderiv (h : f₁ =ᶠ[𝓝 x] f) : fderiv 𝕜 f₁ =ᶠ[𝓝 x] fderiv 𝕜 f :=
  h.eventuallyEq_nhds.mono fun _ h => h.fderiv_eq

end congr

end
