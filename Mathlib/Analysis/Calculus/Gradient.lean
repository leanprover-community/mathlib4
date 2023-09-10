/-
Copyright (c) 2023 Ziyu Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yu Penghao(PKU), Ziyu Wang(PKU), Chenyi Li(PKU), Cao Zhipeng(HUST)
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Gradient

## Main Definitions

Let `f` be a function from `Hilbert Space E` to `ℝ`, `x` be a point in E
and `gradf` be a vector in E. Then

  `HasGradnAt f gradf x`

says that `f` has gradient `gradf'` at `x`, which means:

  `f y - f x = ⟨ gradf , y - x ⟩ + o (y - x)`

Such defintions are based on the definitions of `fderiv`, and can be transformed to each other
for functions `f` from `Hilbert Space E` to `ℝ `.

## Main results

This file contains the following parts of gradient.
* the definition of gradient.
* the theorems translating between `HasGradnAt` and `HasFDerivAt`
* equivalent theorems translating the `LittleO` notation in `HasGradnAt` to
  the language of `ε - δ` convergence, easier to be calculated.
* theorems of the basic calculations of gradient, which can be found as well for `fderiv`.
* theorems connecting `HasGradnAt`, `ContinuousAt` and `ε - δ` convergence.
* theorems showing that for the differiential function,
  the gradient (if exists) at local minima is zero.
-/

open InnerProductSpace
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f: E → ℝ} {f': E → (E →L[ℝ] ℝ)} {x y : E} {s : Set E}
variable {x y gradient : E} {gradient' : E →L[ℝ] ℝ}
local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-
### Definition of gradient
-/
/-- Translate `g` in `Hilbert Space E` to its dual ℝ-ContinuousLinearMap : `⟨ g , ⬝ ⟩`-/
local notation "∇*" gradient  => (toDualMap ℝ _) gradient
/-- Translate the ℝ-ContinuousLinearMap on `Hilbert Space E` to
  its dual element on E by Frechet-Riesz Represent Theorem -/
def grad : (E →L[ℝ] ℝ) → E
  | gradient => ((toDual ℝ E).symm gradient)

theorem grad_equiv :
  ∀ x y :E, inner (grad (f' x)) y = f' x y := by
    intro x y; apply toDual_symm_apply

/-- The gradient of a function `f` from Hilbert Space E to ℝ at a point `x`
    is defined to be the dual of `fderiv` of `f` at `x` -/
def gradn (f : E → ℝ) (x : E) : E := grad (fderiv ℝ f x)

/-- The gradient of a function `f` from ℝ to ℝ at a point `x`
    is defined to be the dual of `fderiv` of `f` at `x` -/
def grad_one (f : ℝ → ℝ) (x : ℝ) : ℝ := (toDual ℝ ℝ).symm (fderiv ℝ f x)

/-- The gradient of a function `f` from Hilbert Space E to ℝ at a point `x` is `grad` 
    defined to be `f` Has `FDeriv` at `x` with the dual ContinuousLinearMap `⟨ gead , ⬝ ⟩`,
    which means `f y - f x = ⟨ gradf , y - x ⟩ + o (y - x)` -/
def HasGradnAt (f : E → ℝ) (grad : E) (x : E) := HasFDerivAt f (∇* grad) x

/-- The gradient of a function `f` from ℝ to ℝ at a point `x` is `grad` 
    defined to be `f` Has `FDeriv` at `x` with the dual ContinuousLinearMap `⟨ gead , ⬝ ⟩`,
    which means `f y - f x = ⟨ gradf , y - x ⟩ + o (y - x)` -/
def HasGradoneAt (f : ℝ → ℝ) (grad : ℝ) (x : ℝ) := HasFDerivAt f (∇* grad) x

/-- The dual of the dual of an element in `(EuclideanSpace ℝ n) →L[ℝ] ℝ` is itself -/
theorem toDual_of_toDual_eq_self (gradient': E →L[ℝ] ℝ): gradient' = ∇* (grad gradient'):= by
  apply ContinuousLinearMap.ext_iff.mpr
  intro x
  have : (∇* (grad gradient')) x = ⟪grad gradient', x⟫ := rfl
  rw [this]
  apply toDual_symm_apply.symm

/-
### Gradient and its `ε - δ` definition
-/
variable {gradf gradg: E}

theorem HasFDeriv_Convergence (h: HasFDerivAt f (f' x) x) :
  ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (x' : E), ‖x - x'‖ ≤ δ
    → ‖f x' - f x - (f' x) (x' - x)‖ ≤ ε * ‖x - x'‖ := by
  rw [HasFDerivAt, HasFDerivAtFilter, Asymptotics.isLittleO_iff] at h
  intro ε epos
  specialize h epos
  rw [Filter.Eventually] at h
  let T := {u | ‖f u - f x - (f' x) (u - x)‖ ≤ ε * ‖u - x‖}
  rcases (Iff.mp Metric.mem_nhds_iff h) with ⟨ε', ε'pos, h⟩
  use (ε' / 2); constructor
  · exact (half_pos ε'pos)
  · intro x' xnhds
    have : x' ∈ Metric.ball x ε':= by
      rw [Metric.mem_ball, dist_comm]
      rw [← dist_eq_norm] at xnhds
      apply lt_of_le_of_lt xnhds (half_lt_self ε'pos)
    have : x' ∈ T := h this
    rw [Set.mem_setOf] at this
    rw [norm_sub_rev x]
    exact this

theorem Convergence_HasFDeriv (h : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (x' : E),
    ‖x - x'‖ ≤ δ → ‖f x' - f x - (f' x) (x' - x)‖ ≤ ε * ‖x - x'‖) :
      HasFDerivAt f (f' x) x := by
  rw [HasFDerivAt, HasFDerivAtFilter, Asymptotics.isLittleO_iff]
  intro ε epos
  rw [Filter.Eventually]
  specialize h ε epos
  rcases h with ⟨δ, dpos, h⟩
  rw [Metric.mem_nhds_iff]
  use δ; constructor
  apply dpos
  intro x' x1mem
  have : ‖x - x'‖ ≤ δ:= by
    rw [Metric.ball, Set.mem_setOf, dist_comm, dist_eq_norm] at x1mem
    exact LT.lt.le x1mem
  rw [Set.mem_setOf, norm_sub_rev x']
  apply h x' this

/- The equivalent statement of `HasFDerivAt` in the `ε - δ` language-/
theorem HasFDeriv_iff_Convergence_Point {gradient' : (E →L[ℝ] ℝ)}:
  HasFDerivAt f (gradient') x ↔ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (x' : E),
     ‖x - x'‖ ≤ δ → ‖f x' - f x - (gradient') (x' - x)‖ ≤ ε * ‖x - x'‖ := by
  constructor
  apply HasFDeriv_Convergence
  apply Convergence_HasFDeriv

theorem HasFDeriv_iff_Convergence :
  HasFDerivAt f (f' x) x ↔ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (x' : E),
     ‖x - x'‖ ≤ δ → ‖f x' - f x - (f' x) (x' - x)‖ ≤ ε * ‖x - x'‖ := by
  constructor
  apply HasFDeriv_Convergence
  apply Convergence_HasFDeriv

/- The equivalent statement of `HasGradnAt` in the `ε - δ` language-/
theorem HasGradnAt_iff_Convergence: HasGradnAt f gradf x ↔
  ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (x' : E),
  ‖x - x'‖ ≤ δ → ‖f x' - f x - ⟪gradf, (x' - x)⟫‖ ≤ ε * ‖x - x'‖ := by
  rw [HasGradnAt, HasFDeriv_iff_Convergence_Point]
  rfl

/- The following theorems are about the translation of `HasFDerivAt` and `HasGradnAt`-/
theorem HasGradn_HasFDeriv  (h: HasGradnAt f gradient x):
  HasFDerivAt f (∇* gradient) x := h

theorem HasFDeriv_HasGradn (h: HasFDerivAt f gradient' x): HasGradnAt f (grad gradient') x := by
  rw [HasGradnAt, HasFDeriv_iff_Convergence_Point]
  rw [HasFDeriv_iff_Convergence_Point] at h
  intro e epos
  rcases (h e epos) with ⟨d, dpos, h⟩
  use d; constructor; exact dpos
  intro x' xle; specialize h x' xle
  rw [← toDual_of_toDual_eq_self]
  exact h

theorem HasFDeriv_HasGradn' (h: HasFDerivAt f (∇* gradient) x):
   HasGradnAt f gradient x := by rw [HasGradnAt]; exact h

theorem HasGradn_HasFDeriv' (h: HasGradnAt f (grad gradient') x): HasFDerivAt f gradient' x := by
  rw [HasFDeriv_iff_Convergence_Point]
  rw [HasGradnAt, HasFDeriv_iff_Convergence_Point ] at h
  intro e epos
  rcases (h e epos) with ⟨d, dpos, h⟩
  use d; constructor; exact dpos
  intro x' xle; specialize h x' xle
  rw [← toDual_of_toDual_eq_self] at h
  exact h

/-
### Calculations on Gradient
-/
variable {g : E → ℝ} {g' : E → (E →L[ℝ] ℝ)}
variable (hf : HasGradnAt f gradf x) (hg : HasGradnAt g gradg x) (c : ℝ)

theorem HasGradnAt.const_smul : HasGradnAt (fun x => c • f x) (c • gradf) x := by
  let f':= ∇* gradf
  have h₁: HasFDerivAt (fun x => c • f x) (c • f') x:= by
    apply HasFDerivAt.const_smul
    apply HasGradn_HasFDeriv hf
  have h₂: c • f' = ∇* (c • gradf) := by
    apply ContinuousLinearMap.ext_iff.mpr; intro x
    have l₁ : (c • f') x = c * (f' x):= by rfl
    have l₂ : (∇* (c • gradf)) x = ⟪c • gradf, x⟫ := by rfl
    have l₃ : ⟪(c • gradf), x⟫ =  c * ⟪gradf, x⟫ := real_inner_smul_left gradf x c
    rw[l₁, l₂, l₃]; rfl
  rw[HasGradnAt, ← h₂]
  exact h₁

theorem HasGradnAt.add : HasGradnAt (fun x => f x + g x) (gradf + gradg) x := by
  let f':= ∇* gradf
  let g':= ∇* gradg
  have h₁: HasFDerivAt (fun x => f x + g x) (f' + g') x := HasFDerivAt.add hf hg
  have h₂: f' + g' = ∇* (gradf + gradg):= by
    apply ContinuousLinearMap.ext_iff.mpr; intro x
    have l₁: (∇* (gradf + gradg)) x = ⟪gradf + gradg, x⟫:= rfl
    have l₂: (f' + g') x = f' x + g' x := rfl
    rw[l₁, l₂, inner_add_left]; rfl
  rw[HasGradnAt, ← h₂]
  apply h₁

theorem HasGradnAt.add_const : HasGradnAt (fun x => f x + c) gradf x := by
  rw [HasGradnAt]; exact HasFDerivAt.add_const hf c

theorem HasGradnAt.const_add : HasGradnAt (fun x => c + f x ) gradf x := by
  rw[HasGradnAt]; exact HasFDerivAt.const_add hf c

open BigOperators
variable {ι : Type _} {u : Finset ι} {A : ι → E → ℝ }
variable {A' : ι → E}

theorem HasGradnAt.sum (h : ∀ i ∈ u, HasGradnAt (A i) (A' i) x) :
    HasGradnAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x := by
  have h₁: HasFDerivAt (fun y => ∑ i in u, A i y)
    (∑ i in u,∇* (A' i)) x :=  HasFDerivAt.sum h
  have h₂: ∑ i in u, (∇* (A' i)) = ∇* (∑ i in u, A' i):= by
    apply ContinuousLinearMap.ext_iff.mpr; intro y
    have l₂: (∑ i in u, ⟪A' i, y⟫) = (∑ i in u, (∇* (A' i)) y) := rfl
    have l₃: (∑ i in u, ⟪A' i, y⟫) = ⟪∑ i in u, (A' i), y⟫ := by rw [sum_inner]
    have l₄: (∇* (∑ i in u, A' i)) y = ⟪∑ i in u, A' i, y⟫ := rfl
    rw[l₄, ← l₃, l₂, ContinuousLinearMap.coe_sum', Finset.sum_apply]
  rw[HasGradnAt, ← h₂]
  apply h₁

theorem HasGradnAt.neg : HasGradnAt (fun x => - f x) (- gradf) x := by
  let f':= ∇* gradf
  have h₁: HasFDerivAt (fun x => - f x) (- f') x := HasFDerivAt.neg hf
  have h₂: (∇* (-gradf)) = - f':= by
    apply ContinuousLinearMap.ext_iff.mpr; intro y
    have l₁: (∇* - gradf) y = ⟪- gradf, y⟫:= rfl
    have l₂: (- f') y= - (f' y):= rfl
    have l₃: f' y = ⟪gradf, y⟫:= rfl
    rw [l₁, l₂, l₃]
    exact inner_neg_left gradf y
  rw [HasGradnAt, h₂]
  apply h₁

theorem HasGradnAt.sub : HasGradnAt (fun x => f x - g x) (gradf - gradg) x := by
  let f' := ∇* gradf
  let g' := ∇* gradg
  have h₁: HasFDerivAt (fun x => f x - g x) (f' - g') x := HasFDerivAt.sub hf hg
  have h₂: f' - g' = ∇* (gradf - gradg):= by
    apply ContinuousLinearMap.ext_iff.mpr; intro x
    have l₁: (∇* (gradf - gradg)) x = ⟪gradf - gradg, x⟫:= rfl
    have l₂: (f' - g') x = f' x - g' x:= rfl
    rw[l₁, l₂, inner_sub_left]; rfl
  rw [HasGradnAt, ← h₂]
  apply h₁

theorem HasGradnAt.sub_const : HasGradnAt (fun x => f x - c) gradf x := by
  rw[HasGradnAt]; exact HasFDerivAt.sub_const hf c

theorem HasGradnAt.const_sub : HasGradnAt (fun x => c - f x) (- gradf) x := by
  let f' := ∇* gradf
  have h₁: HasFDerivAt (fun x => c - f x) (- f') x := by
    apply HasFDerivAt.const_sub hf
  have h₂: (∇* (- gradf)) = - f' := by
    apply ContinuousLinearMap.ext_iff.mpr; intro y
    have l₁: (∇* (-gradf)) y = ⟪-gradf, y⟫ := rfl
    have l₂: (- f') y= - (f' y) := rfl
    have l₃: f' y = ⟪gradf, y⟫ := rfl
    rw [l₁, l₂, l₃]
    exact inner_neg_left gradf y
  rw [HasGradnAt, h₂]
  apply h₁

theorem HasGradnAt.comp {g : ℝ → ℝ} {gradg : ℝ} (hg : HasGradoneAt g gradg (f x)):
   HasGradnAt (g ∘ f) (gradg • gradf) x := by
  let f' := ∇* gradf
  let g' := ∇* gradg
  have h₁: HasFDerivAt (g ∘ f) (g'.comp f') x:= by
    apply HasFDerivAt.comp
    rw [HasGradoneAt] at hg; apply hg
    apply hf
  have h₂ : (∇* (gradg • gradf)) = g'.comp f':= by
    apply ContinuousLinearMap.ext_iff.mpr; intro y
    have l₁: (g'.comp f') y = g' (f' y) := rfl
    have l₂: f' y = ⟪gradf, y⟫ := rfl
    have l₃: g' ⟪gradf, y⟫ = gradg * ⟪gradf, y⟫ := rfl
    have l₄: (∇* (gradg • gradf)) y = ⟪gradg • gradf, y⟫ := rfl
    rw [l₁, l₂, l₃, l₄]
    exact real_inner_smul_left gradf y gradg
  rw [HasGradnAt, h₂]
  apply h₁

theorem HasGradnAt.mul (hf : HasGradnAt f gradf x) (hg : HasGradnAt g gradg x) :
    HasGradnAt (fun y => f y * g y) (f x • gradg + g x • gradf) x := by
  let f':= ∇* gradf
  let g':= ∇* gradg
  have h₁: HasFDerivAt (fun x => f x * g x) (f x • g' + g x • f') x:= by
    apply HasFDerivAt.mul hf hg
  have h₂: f x • g' + g x • f' =  (∇* (f x • gradg + g x • gradf)):= by
    apply ContinuousLinearMap.ext_iff.mpr; intro y
    have l₁: (f x • g' + g x • f') y = (f x • g') y + (g x • f') y:= rfl
    have l₂: (f x • g') y + (g x • f') y = f x * (g' y) + g x * (f' y) := rfl
    have l3: f x * (g' y) + g x * (f' y) = f x * ⟪gradg, y⟫ + g x * ⟪gradf, y⟫ := rfl
    have l4: f x * ⟪gradg, y⟫ + g x * ⟪gradf, y⟫ = ⟪f x • gradg, y⟫ + ⟪g x • gradf, y⟫ := by
      rw [real_inner_smul_left gradg y (f x), real_inner_smul_left gradf y (g x)]
    have l5: ⟪f x • gradg, y⟫ + ⟪g x • gradf, y⟫ = ⟪f x • gradg + g x • gradf, y⟫:= by
      rw [inner_add_left]
    rw [l₁, l₂, l3, l4, l5]
    rfl
  rw [HasGradnAt, ← h₂]
  apply h₁

theorem toDual.unique {f₁ g₁: E} (h: (∇* f₁) = (∇* g₁)): f₁ = g₁ := by
  have h₁: ∀ x : E , (∇* f₁) x = (∇* g₁) x :=
   fun x => congrFun (congrArg FunLike.coe h) x
  specialize h₁ (f₁ - g₁)
  have : (∇* f₁) (f₁ - g₁) = ⟪f₁, f₁ - g₁⟫ := rfl
  rw [this] at h₁
  have : (∇* g₁) (f₁ - g₁) = ⟪g₁, f₁ - g₁⟫ := rfl
  rw [this] at h₁
  have : ⟪f₁, f₁ - g₁⟫ - ⟪g₁, f₁ - g₁⟫ = 0 := by
    rw [h₁, sub_self]
  rw [← inner_sub_left, inner_self_eq_zero, sub_eq_zero] at this
  exact this

theorem HasGradnAt.unique (hf : HasGradnAt f gradf x) (hg : HasGradnAt f gradg x):
  gradf = gradg := by
  rw [HasGradnAt] at hf
  rw [HasGradnAt] at hg
  have : (∇* gradf) = (∇* gradg):= by
    apply HasFDerivAt.unique hf hg
  apply toDual.unique this

theorem HasGradnAt.congr (hf : HasGradnAt f gradf x) (hg : HasGradnAt g gradg x) (equal: f = g):
  gradf = gradg := by
  rw [equal] at hf
  apply HasGradnAt.unique hf hg

theorem HasGradnAt.constant (c : ℝ ) : HasGradnAt (fun (_ : E) => c) 0 x := by
  rw [HasGradnAt_iff_Convergence]
  intro ε epos
  use (1 : ℝ); constructor;
  · exact Real.zero_lt_one
  · intro x' _
    rw [sub_self, inner_zero_left, sub_self, norm_zero]
    apply mul_nonneg (LT.lt.le epos) (norm_nonneg (x - x'))

/-
  The following theorems concerns the relationship of
  `ε - δ` convergence, gradient and continuity.
-/

theorem HasGradnAt.continuousAt (hf: HasGradnAt f gradf x) : ContinuousAt f x:= by
  rw [HasGradnAt] at hf
  apply HasFDerivAt.continuousAt hf

theorem ContinuousAt_Convergence (h : ContinuousAt f x) :
  ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (x' : E), ‖x - x'‖ ≤ δ → ‖f x' - f x‖ ≤ ε := by
  rw [continuousAt_def] at h
  intro ε epos
  let A := Metric.ball (f x) ε
  specialize h A (Metric.ball_mem_nhds (f x) epos)
  rw [Metric.mem_nhds_iff] at h
  rcases h with ⟨δ, dpos, h⟩
  use (δ / 2); constructor
  exact half_pos dpos
  intro x' x1le
  have : x' ∈ Metric.ball x δ := by
    rw [Metric.ball, Set.mem_setOf, dist_comm, dist_eq_norm_sub]
    apply lt_of_le_of_lt x1le
    exact half_lt_self dpos
  exact LT.lt.le (h this)

theorem Convergence_ContinuousAt
  (h: ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (x' : E), ‖x - x'‖ ≤ δ → ‖f x' - f x‖ ≤ ε) :
   ContinuousAt f x := by
  rw [continuousAt_def]
  intro A amem
  rw [Metric.mem_nhds_iff] at amem
  rcases amem with ⟨ε, epos, bmem⟩
  rcases (h (ε / 2) (half_pos epos)) with ⟨δ , dpos, h⟩
  rw [Metric.mem_nhds_iff]
  use δ; constructor
  exact dpos
  rw [Set.subset_def]
  intro x' x1mem
  have : ‖x - x'‖ ≤ δ := by
    rw [Metric.ball, Set.mem_setOf, dist_comm, dist_eq_norm_sub] at x1mem
    exact LT.lt.le x1mem
  specialize h x' this
  have : f x' ∈  Metric.ball (f x) ε := by
    rw [Metric.ball, Set.mem_setOf, dist_eq_norm_sub]
    apply lt_of_le_of_lt h (half_lt_self epos)
  exact bmem this

theorem ContinuousAt_iff_Convergence: ContinuousAt f x ↔ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
    ∀ (x' : E), ‖x - x'‖ ≤ δ → ‖f x' - f x‖ ≤ ε:= by
  constructor
  apply ContinuousAt_Convergence
  apply Convergence_ContinuousAt

theorem ContinuousAt_Convergence_onedim {f : ℝ → ℝ} {x : ℝ} (h : ContinuousAt f x):
 ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (x' : ℝ), ‖x - x'‖ ≤ δ → ‖f x' - f x‖ ≤ ε:= by
  rw [continuousAt_def] at h
  intro ε epos
  let A := Metric.ball (f x) ε
  specialize h A (Metric.ball_mem_nhds (f x) epos)
  rw [Metric.mem_nhds_iff] at h
  rcases h with ⟨δ, dpos, h⟩
  use (δ /2); constructor
  exact half_pos dpos
  intro x' x1le
  have : x' ∈ Metric.ball x δ := by
    rw [Metric.ball, Set.mem_setOf, dist_comm, dist_eq_norm_sub]
    apply lt_of_le_of_lt x1le
    exact half_lt_self dpos
  exact LT.lt.le (h this)

theorem Convergence_ContinuousAt_onedim {f : ℝ → ℝ } {x : ℝ}
  (h: ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (x' : ℝ), ‖x - x'‖ ≤ δ → ‖f x' - f x‖ ≤ ε) :
    ContinuousAt f x := by
  rw [continuousAt_def]
  intro A amem
  rw [Metric.mem_nhds_iff] at amem
  rcases amem with ⟨ε, epos, bmem⟩
  specialize h (ε / 2) (half_pos epos)
  rcases h with ⟨δ , dpos, h⟩
  rw [Metric.mem_nhds_iff]
  use δ; constructor
  · exact dpos
  rw [Set.subset_def]
  intro x' x1mem
  have : ‖x - x'‖ ≤ δ := by
    rw [Metric.ball, Set.mem_setOf, dist_comm, dist_eq_norm_sub] at x1mem
    exact LT.lt.le x1mem
  have : f x' ∈  Metric.ball (f x) ε := by
    rw [Metric.ball, Set.mem_setOf, dist_eq_norm_sub]
    apply lt_of_le_of_lt (h x' this) (half_lt_self epos)
  exact bmem this

theorem ContinuousAt_iff_Convergence_onedim {f : ℝ → ℝ} {x : ℝ} : ContinuousAt f x ↔
 ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (x' : ℝ), ‖x - x'‖ ≤ δ → ‖f x' - f x‖ ≤ ε := by
  constructor
  apply ContinuousAt_Convergence_onedim
  apply Convergence_ContinuousAt_onedim

/-The following theorems prove that the gradient (if exists) at local minima is zero-/

theorem IsMinOn_gradn_eq_zero (h : ∃ (ε : ℝ), ε > 0 ∧ Metric.ball x ε ⊆ s)
 (hmin: IsMinOn f s x) : gradf = 0:= by
  have : IsLocalMin f x:= by
    apply IsMinOn.isLocalMin hmin
    rw [Metric.mem_nhds_iff]
    exact h
  have : (∇* gradf) = 0 := IsLocalMin.hasFDerivAt_eq_zero this hf
  let f1 := (0 : E)
  have : (∇* gradf) = (∇* f1) := by
    rw [this]
    exact Eq.symm (LinearIsometry.map_zero (toDualMap ℝ E))
  exact toDual.unique this

theorem IsLocalMin_gradn_eq_zero (h : IsLocalMin f x) : gradf = 0 := by
  have : (∇* gradf) = 0 := IsLocalMin.hasFDerivAt_eq_zero h hf
  let f1 := (0 : E)
  have : (∇* gradf) = (∇* f1) := by
    rw [this]
    exact Eq.symm (LinearIsometry.map_zero (toDualMap ℝ E))
  exact toDual.unique this