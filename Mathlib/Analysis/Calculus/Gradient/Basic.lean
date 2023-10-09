/-
Copyright (c) 2023 Ziyu Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ziyu Wang, Chenyi Li, Yu Penghao, Cao Zhipeng
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Gradient

## Main Definitions

Let `f` be a function from a Hilbert Space `F` to `𝕜` (`𝕜` is `ℝ` or `ℂ`) , `x` be a point in `F`
and `f'` be a vector in F. Then

  `HasGradientWithinAt f f' s x`

says that `f` has a gradient `f'` at `x`, where the domain of interest
is restricted to `s`. We also have

  `HasGradientAt f f' x := HasGradientWithinAt f f' x univ`

## Main results

This file contains the following parts of gradient.
* the definition of gradient.
* the theorems translating between `HasGradientAtFilter` and `HasFDerivAtFilter`,
  `HasGradientWithinAt` and `HasFDerivWithinAt`, `HasGradientAt` and `HasFDerivAt`,
  `Gradient` and `fderiv`.
* theorems the Uniqueness of Gradient.
* the theorems translating between  `HasGradientAtFilter` and `HasDerivAtFilter`,
  `HasGradientAt` and `HasDerivAt`, `Gradient` and `deriv` when `F = 𝕜`.
* the theorems about the congruence of the gradient.
* the theorems about the gradient of constant function.
* the theorems about the continuity of a function admitting a gradient.
-/

open Topology InnerProductSpace Set

noncomputable section

variable {𝕜 F : Type*} [IsROrC 𝕜]

variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

variable {f : F → 𝕜} {f' x : F}

/-- A function `f` has the gradient `f'` as derivative along the filter `L` if
  `f x' = f x + ⟨f', x' - x⟩ + o (x' - x)` when `x'` converges along the filter `L`.-/
def HasGradientAtFilter (f : F → 𝕜) (f' x : F) (L : Filter F) :=
  HasFDerivAtFilter f (toDual 𝕜 F f') x L

/-- `f` has the gradient `f'` at the point `x` within the subset `s` if
  `f x' = f x + ⟨f', x' - x⟩ + o (x' - x)` where `x'` converges to `x` inside `s`.-/
def HasGradientWithinAt (f : F → 𝕜) (f' : F) (s : Set F) (x : F):=
  HasGradientAtFilter f f' x (𝓝[s] x)

/-- `f` has the gradient `f'` at the point `x` if
  `f x' = f x + ⟨f', x' - x⟩ + o (x' - x)` where `x'` converges to `x`. -/
def HasGradientAt (f : F → 𝕜) (f' x : F) :=
  HasGradientAtFilter f f' x (𝓝 x)

/-- Gradient of `f` at the point `x`, if it exists.  Zero otherwise.
If the derivative exists (i.e., `∃ f', HasGradientAt f f' x`), then
`f x' = f x + ⟨f', x' - x⟩ + o (x' - x)` where `x'` converges to `x`. -/
def gradient (f : F → 𝕜) (x : F) : F := (toDual 𝕜 F).symm (fderiv 𝕜 f x)

local notation "∇" => gradient

variable {s : Set F} {L : Filter F}

theorem HasGradientWithinAt_iff_HasFDerivWithinAt {s : Set F} :
    HasGradientWithinAt f f' s x ↔ HasFDerivWithinAt f (toDual 𝕜 F f') s x := Iff.rfl

theorem HasGradientAt_iff_HasFDerivAt :
    HasGradientAt f f' x ↔ HasFDerivAt f (toDual 𝕜 F f') x := Iff.rfl

theorem HasGradientAt.hasFDerivAt {frechet : F →L[𝕜] 𝕜}
    (h : HasGradientAt f ((toDual 𝕜 F).symm frechet) x) :
    HasFDerivAt f frechet x := by
  rw [← (toDual 𝕜 F).apply_symm_apply frechet]
  exact HasGradientAt_iff_HasFDerivAt.mp h

theorem HasFDerivAt.hasGradientAt {frechet : F →L[𝕜] 𝕜} (h : HasFDerivAt f frechet x) :
    HasGradientAt f ((toDual 𝕜 F).symm frechet) x := by
  rw [← (toDual 𝕜 F).apply_symm_apply frechet] at h
  exact HasGradientAt_iff_HasFDerivAt.mpr h
theorem Gradient_zero_of_not_differentiableAt (h : ¬DifferentiableAt 𝕜 f x) : ∇ f x = 0 := by
  have : (toDual 𝕜 F).symm 0 = 0 := by simp only [map_zero]
  rw [← fderiv_zero_of_not_differentiableAt h] at this
  exact this

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

section GradientUniqueness

variable {gradf gradg : F}

theorem HasGradientAt.unique (hf : HasGradientAt f gradf x) (hg : HasGradientAt f gradg x) :
    gradf = gradg := (toDual 𝕜 F).injective
  ((HasGradientAt_iff_HasFDerivAt.mp hf).unique (HasGradientAt_iff_HasFDerivAt.mp hg))

end GradientUniqueness

theorem HasGradientWithinAt_iff_HasFDerivWithinAt' {s : Set F} {frechet : F →L[𝕜] 𝕜} :
    HasGradientWithinAt f ((toDual 𝕜 F).symm frechet) s x ↔ HasFDerivWithinAt f frechet s x := by
  conv_rhs => rw [← (toDual 𝕜 F).apply_symm_apply frechet]

theorem DifferentiableAt.hasGradientAt (h : DifferentiableAt 𝕜 f x) :
    HasGradientAt f (∇ f x) x := by
  rw [HasGradientAt_iff_HasFDerivAt, gradient, (toDual 𝕜 F).apply_symm_apply (fderiv 𝕜 f x)]
  exact h.hasFDerivAt

theorem HasGradientAt.differentiableAt (h : HasGradientAt f f' x) :
    DifferentiableAt 𝕜 f x := by use ((toDual 𝕜 F) f'); apply HasGradientAt_iff_HasFDerivAt.mp h

theorem HasGradientWithinAt.differentiableWithinAt (h : HasGradientWithinAt f f' s x) :
    DifferentiableWithinAt 𝕜 f s x := HasFDerivWithinAt.differentiableWithinAt h

@[simp]
theorem hasGradientWithinAt_univ : HasGradientWithinAt f f' univ x ↔ HasGradientAt f f' x := by
  rw [HasGradientWithinAt_iff_HasFDerivWithinAt, HasGradientAt_iff_HasFDerivAt]
  rw [hasFDerivWithinAt_univ]

theorem DifferentiableOn.hasGradientAt (h : DifferentiableOn 𝕜 f s) (hs : s ∈ 𝓝 x) :
    HasGradientAt f (∇ f x) x := (h.hasFDerivAt hs).hasGradientAt

theorem HasGradientAt.gradient (h : HasGradientAt f f' x) : ∇ f x = f' :=
  h.differentiableAt.hasGradientAt.unique h

theorem gradient_eq {f' : F → F} (h : ∀ x, HasGradientAt f (f' x) x) : ∇ f = f' :=
  funext fun x => (h x).gradient

variable {g : 𝕜 → 𝕜} {g' u : 𝕜} {L' : Filter 𝕜}

theorem toDual_eq_StarRingEnd : ((toDual 𝕜 𝕜) g') 1 = starRingEnd 𝕜 g' := by simp

theorem StarRingEnd_eq_toDual : ((toDual 𝕜 𝕜) (starRingEnd 𝕜 g')) 1 = g' := by simp

theorem Mul_one_eq_SterRingEnd (g' : 𝕜) : ContinuousLinearMap.smulRight (1 : 𝕜 →L[𝕜] 𝕜)
    (starRingEnd 𝕜 g') = (toDual 𝕜 𝕜) g' := by
  refine Iff.mpr ContinuousLinearMap.ext_iff ?_
  simp; intro v; rw [toDual_apply, IsROrC.inner_apply, mul_comm]

theorem SterRingEnd_eq_Mul_one (g' : 𝕜) : ContinuousLinearMap.smulRight (1 : 𝕜 →L[𝕜] 𝕜)
    g' = (toDual 𝕜 𝕜) (starRingEnd 𝕜 g') := by
  refine Iff.mpr ContinuousLinearMap.ext_iff ?_
  simp; intro; rw [toDual_apply, IsROrC.inner_apply, mul_comm]
  rw [RingHomCompTriple.comp_apply, RingHom.id_apply]

theorem HasGradientAtFilter.hasDerivAtFilter (h : HasGradientAtFilter g g' u L') :
    HasDerivAtFilter g (starRingEnd 𝕜 g') u L' := by
  rw [HasDerivAtFilter, Mul_one_eq_SterRingEnd]; exact h

theorem HasDerivAtFilter.hasGradientAtFilter (h : HasDerivAtFilter g g' u L') :
    HasGradientAtFilter g (starRingEnd 𝕜 g') u L' := by
  rw [HasGradientAtFilter, ← SterRingEnd_eq_Mul_one]; exact h

theorem HasGradientAt.hasDerivAt (h : HasGradientAt g g' u) :
    HasDerivAt g (starRingEnd 𝕜 g') u := by
  rw [HasGradientAt_iff_HasFDerivAt, hasFDerivAt_iff_hasDerivAt, toDual_eq_StarRingEnd] at h
  exact h

theorem HasGradientAt.hasDerivAt' {g : ℝ → ℝ} {g' u: ℝ} (h :HasGradientAt g g' u) :
    HasDerivAt g g' u := h.hasDerivAt

theorem HasDerivAt.hasGradientAt (h : HasDerivAt g g' u) :
    HasGradientAt g (starRingEnd 𝕜 g') u := by
  rw [HasGradientAt_iff_HasFDerivAt, hasFDerivAt_iff_hasDerivAt, StarRingEnd_eq_toDual]
  exact h

theorem HasDerivAt.hasGradientAt' {g : ℝ → ℝ} {g' u: ℝ} (h :HasDerivAt g g' u) :
    HasGradientAt g g' u := h.hasGradientAt

theorem gradient_deriv : ∇ g u = starRingEnd 𝕜 (deriv g u) := by
  by_cases h: DifferentiableAt 𝕜 g u
  · rw [h.hasGradientAt.hasDerivAt.deriv]
    exact Eq.symm (IsROrC.conj_conj (∇ g u))
  · rw [Gradient_zero_of_not_differentiableAt h, deriv_zero_of_not_differentiableAt h]
    exact Eq.symm (RingHom.map_zero (starRingEnd 𝕜))

theorem gradient_deriv' {g : ℝ → ℝ} {u: ℝ} : ∇ g u = deriv g u := gradient_deriv

open Filter

/-- If a function f has a derivative f' at x, a rescaled version of f around x converges to f',
i.e., `n (f (x + (1/n) v) - f x)` converges to `f' v`. More generally, if `c n` tends to infinity
and `c n * d n` tends to `v`, then `c n * (f (x + d n) - f x)` tends to `< f', v >`. This lemma
expresses this fact, for functions having a derivative within a set. Its specific formulation is
useful for tangent cone related discussions. -/
theorem HasGradientWithinAt.lim (h : HasGradientWithinAt f f' s x) {α : Type*} (l : Filter α)
    {c : α → 𝕜} {d : α → F} {v : F} (dtop : ∀ᶠ n in l, x + d n ∈ s)
    (clim : Tendsto (fun n => ‖c n‖) l atTop) (cdlim : Tendsto (fun n => c n • d n) l (𝓝 v)) :
    Tendsto (fun n => c n • (f (x + d n) - f x)) l (𝓝 ⟪f', v⟫) := by
  have : _ := (HasGradientWithinAt_iff_HasFDerivWithinAt.mp h).lim l dtop clim cdlim
  rw [toDual_apply] at this
  exact this

section GradientProperties

theorem hasGradientAtFilter_iff_isLittleO :
    HasGradientAtFilter f f' x L ↔
    (fun x' : F => f x' - f x - ⟪f' , x' - x⟫) =o[L] fun x' => x' - x := Iff.rfl

theorem hasGradientWithinAt_iff_isLittleO :
    HasGradientWithinAt f f' s x ↔
    (fun x' : F => f x' - f x - ⟪f' , x' - x⟫) =o[𝓝[s] x] fun x' => x' - x := Iff.rfl

theorem hasGradientWithinAt_iff_tendsto :
    HasGradientWithinAt f f' s x ↔
    Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - ⟪f' , x' - x⟫‖) (𝓝[s] x) (𝓝 0) :=
  hasFDerivAtFilter_iff_tendsto

theorem hasGradientAt_iff_isLittleO : HasGradientAt f f' x ↔
    (fun x' : F => f x' - f x - ⟪f' , x' - x⟫) =o[𝓝 x] fun x' => x' - x := Iff.rfl

theorem hasGradientAt_iff_tendsto :
    HasGradientAt f f' x ↔
    Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - ⟪f' , x' - x⟫‖) (𝓝 x) (𝓝 0) :=
  hasFDerivAtFilter_iff_tendsto

theorem HasGradientAtFilter.isBigO_sub (h : HasGradientAtFilter f f' x L) :
    (fun x' => f x' - f x) =O[L] fun x' => x' - x := HasFDerivAtFilter.isBigO_sub h

theorem hasGradientWithinAt_congr_set' {s t : Set F} (y : F) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    HasGradientWithinAt f f' s x ↔ HasGradientWithinAt f f' t x := hasFDerivWithinAt_congr_set' y h

theorem hasGradientWithinAt_congr_set {s t : Set F} (h : s =ᶠ[𝓝 x] t) :
    HasGradientWithinAt f f' s x ↔ HasGradientWithinAt f f' t x := hasFDerivWithinAt_congr_set h

theorem hasGradientAt_iff_isLittleO_nhds_zero : HasGradientAt f f' x ↔
    (fun h => f (x + h) - f x - ⟪f' , h⟫)
    =o[𝓝 0] fun h => h := hasFDerivAt_iff_isLittleO_nhds_zero

end GradientProperties

/-! ### Congruence properties of the Gradient -/
section congr

variable {f₀ f₁ : F → 𝕜} {f₀' f₁' : F} {x₀ x₁ : F} {s₀ s₁ t : Set F} {L₀ L₁ : Filter F}

theorem Filter.EventuallyEq.hasGradientAtFilter_iff (h₀ : f₀ =ᶠ[L] f₁) (hx : f₀ x = f₁ x)
    (h₁ : f₀' = f₁') : HasGradientAtFilter f₀ f₀' x L ↔ HasGradientAtFilter f₁ f₁' x L :=
  h₀.hasFDerivAtFilter_iff hx (by simp [h₁])

theorem HasGradientAtFilter.congr_of_eventuallyEq (h : HasGradientAtFilter f f' x L)
    (hL : f₁ =ᶠ[L] f) (hx : f₁ x = f x) : HasGradientAtFilter f₁ f' x L := by
  rwa [hL.hasGradientAtFilter_iff hx rfl]

theorem HasGradientWithinAt.congr_mono (h : HasGradientWithinAt f f' s x) (ht : ∀ x ∈ t, f₁ x = f x)
    (hx : f₁ x = f x) (h₁ : t ⊆ s) : HasGradientWithinAt f₁ f' t x :=
  HasFDerivWithinAt.congr_mono h ht hx h₁

theorem HasGradientWithinAt.congr (h : HasGradientWithinAt f f' s x) (hs : ∀ x ∈ s, f₁ x = f x)
    (hx : f₁ x = f x) : HasGradientWithinAt f₁ f' s x := h.congr_mono hs hx (by tauto)

theorem HasGradientWithinAt.congr_of_mem (h : HasGradientWithinAt f f' s x)
    (hs : ∀ x ∈ s, f₁ x = f x) (hx : x ∈ s) : HasGradientWithinAt f₁ f' s x := h.congr hs (hs _ hx)

theorem HasGradientWithinAt.congr_of_eventuallyEq (h : HasGradientWithinAt f f' s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : HasGradientWithinAt f₁ f' s x :=
  HasGradientAtFilter.congr_of_eventuallyEq h h₁ hx

theorem HasGradientWithinAt.congr_of_eventuallyEq_of_mem (h : HasGradientWithinAt f f' s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) : HasGradientWithinAt f₁ f' s x := by
  apply h.congr_of_eventuallyEq h₁ (h₁.eq_of_nhdsWithin hx)

theorem HasGradientAt.congr_of_eventuallyEq (h : HasGradientAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f) :
    HasGradientAt f₁ f' x := HasGradientAtFilter.congr_of_eventuallyEq h h₁ (mem_of_mem_nhds h₁ : _)

theorem Filter.EventuallyEq.gradient_eq (hL : f₁ =ᶠ[𝓝 x] f) : ∇ f₁ x = ∇ f x := by
  unfold gradient
  rwa [Filter.EventuallyEq.fderiv_eq]

protected theorem Filter.EventuallyEq.gradient (h : f₁ =ᶠ[𝓝 x] f) : ∇ f₁ =ᶠ[𝓝 x] ∇ f :=
  h.eventuallyEq_nhds.mono fun _ h => h.gradient_eq

end congr

/-! ### The Gradient of constant functions -/

section Const

variable (c : 𝕜) (s x L)

theorem hasGradientAtFilter_const : HasGradientAtFilter (fun _ => c) 0 x L := by
  rw [HasGradientAtFilter, map_zero]; apply hasFDerivAtFilter_const c x L

theorem hasGradientWithinAt_const : HasGradientWithinAt (fun _ => c) 0 s x :=
  hasGradientAtFilter_const _ _ _

theorem hasGradientAt_const : HasGradientAt (fun _ => c) 0 x := hasGradientAtFilter_const _ _ _

theorem gradient_const : ∇ (fun _ => c) x = 0 := by
  rw [gradient, fderiv_const, Pi.zero_apply, map_zero]

@[simp]
theorem gradient_const' : (∇ fun _ : 𝕜 => c) = fun _ => 0 := funext fun x => gradient_const x c

end Const

section Continuous

/-! ### Continuity of a function admitting a gradient -/

nonrec theorem HasGradientAtFilter.tendsto_nhds (hL : L ≤ 𝓝 x) (h : HasGradientAtFilter f f' x L) :
    Tendsto f L (𝓝 (f x)) := h.tendsto_nhds hL

theorem HasGradientWithinAt.continuousWithinAt (h : HasGradientWithinAt f f' s x) :
    ContinuousWithinAt f s x := by apply HasGradientAtFilter.tendsto_nhds inf_le_left h

theorem HasGradientAt.continuousAt (h : HasGradientAt f f' x) : ContinuousAt f x :=
  HasGradientAtFilter.tendsto_nhds le_rfl h

protected theorem HasGradientAt.continuousOn {f' : F → F}
    (hderiv : ∀ x ∈ s, HasGradientAt f (f' x) x) :
  ContinuousOn f s := fun x hx => (hderiv x hx).continuousAt.continuousWithinAt

end Continuous