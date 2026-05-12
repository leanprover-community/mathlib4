/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

/-!
# Contour integrals

In this file we specialize the definition of `curveIntegral` to paths in `ℂ`.
In this case, we integrate functions instead of 1-forms,
interpreting a function `f` as the 1-form `f(z)dz`,
written as `ContinuousLinearMap.toSpanSingleton ℂ ∘ f`.
-/


@[expose] public noncomputable section

open AffineMap MeasureTheory
open scoped unitInterval Convex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {a b : ℂ}

/-- A function `f : ℂ → E` is *contour integrable* along a path `γ`,
if the 1-form $f(z)\,dz$ is curve integrable along `γ`.

Equivalently, this means that `φ(t)=γ'(t)•f(γ(t))` is interval integrable on `[0, 1]`. -/
def ContourIntegrable (f : ℂ → E) (γ : Path a b) :=
  CurveIntegrable (.toSpanSingleton ℂ ∘ f) γ

/-- The *contour integral* of a function `f : ℂ → E` along a path `γ`,
defined as the curve integral of $f(z)\,dz$ along `γ`.

Equivalently, this is given by the integral of `γ'(t)•f(t)` along `[0, 1]`. -/
def contourIntegral (f : ℂ → E) (γ : Path a b) : E :=
  ∫ᶜ x in γ, .toSpanSingleton ℂ (f x)

@[inherit_doc contourIntegral]
notation3 "∫ꟲ "(...)" in " γ ", "r:67:(scoped f => contourIntegral f γ) => r

theorem contourIntegral_of_not_completeSpace (h : ¬CompleteSpace E)
    (f : ℂ → E) (γ : Path a b) : ∫ꟲ x in γ, f x = 0 := by
  rw [contourIntegral, curveIntegral_of_not_completeSpace h]

theorem contourIntegral_eq_intervalIntegral_derivWithin_smul (f : ℂ → E) (γ : Path a b) :
    ∫ꟲ x in γ, f x = ∫ t in 0..1, derivWithin γ.extend I t • f (γ.extend t) := by
  simp [contourIntegral, curveIntegral_def, curveIntegralFun_def]

theorem contourIntegral_eq_intervalIntegral_deriv_smul (f : ℂ → E) (γ : Path a b) :
    ∫ꟲ x in γ, f x = ∫ t in 0..1, deriv γ.extend t • f (γ.extend t) := by
  simp [contourIntegral, curveIntegral_eq_intervalIntegral_deriv]

/-!
### Operations on paths
-/

section PathOperations

variable {c d : ℂ} {f : ℂ → E} {γ γab : Path a b} {γbc : Path b c} {t : ℝ}

@[simp]
theorem contourIntegral_refl (f : ℂ → E) (a : ℂ) : ∫ꟲ x in .refl a, f x = 0 := by
  simp [contourIntegral]

@[simp]
theorem ContourIntegrable.refl (f : ℂ → E) (a : ℂ) : ContourIntegrable f (.refl a) :=
  CurveIntegrable.refl ..

@[simp]
theorem contourIntegral_cast (f : ℂ → E) (γ : Path a b) (hc : c = a) (hd : d = b) :
    ∫ꟲ x in γ.cast hc hd, f x = ∫ꟲ x in γ, f x := by
  simp [contourIntegral]

@[simp]
theorem contourIntegrable_cast_iff (hc : c = a) (hd : d = b) :
    ContourIntegrable f (γ.cast hc hd) ↔ ContourIntegrable f γ := by
  simp [ContourIntegrable]

protected alias ⟨_, ContourIntegrable.cast⟩ := curveIntegrable_cast_iff

protected theorem ContourIntegrable.symm (h : ContourIntegrable f γ) :
    ContourIntegrable f γ.symm :=
  CurveIntegrable.symm h

@[simp]
theorem contourIntegrable_symm : ContourIntegrable f γ.symm ↔ ContourIntegrable f γ :=
  ⟨fun h ↦ by simpa using h.symm, .symm⟩

@[simp]
theorem contourIntegral_symm (f : ℂ → E) (γ : Path a b) :
    ∫ꟲ x in γ.symm, f x = -∫ꟲ x in γ, f x := by
  simp [contourIntegral]

protected theorem ContourIntegrable.trans (h₁ : ContourIntegrable f γab)
    (h₂ : ContourIntegrable f γbc) :
    ContourIntegrable f (γab.trans γbc) :=
  CurveIntegrable.trans h₁ h₂

theorem contourIntegral_trans (h₁ : ContourIntegrable f γab) (h₂ : ContourIntegrable f γbc) :
    ∫ꟲ x in γab.trans γbc, f x = (∫ꟲ x in γab, f x) + ∫ꟲ x in γbc, f x :=
  curveIntegral_trans h₁ h₂

theorem contourIntegrable_segment :
    ContourIntegrable f (.segment a b) ↔
      a = b ∨ IntervalIntegrable (fun t ↦ f (lineMap a b t)) volume 0 1 := by
  simp [ContourIntegrable, curveIntegrable_segment, sub_eq_zero, @eq_comm _ a]

theorem contourIntegral_segment (f : ℂ → E) (a b : ℂ) :
    ∫ꟲ x in .segment a b, f x = (b - a) • ∫ t in 0..1, f (lineMap a b t) := by
  simp [contourIntegral, curveIntegral_segment]

@[simp]
theorem contourIntegral_segment_const [CompleteSpace E] (a b : ℂ) (y : E) :
    ∫ꟲ _ in .segment a b, y = (b - a) • y := by
  simp [contourIntegral_segment]

/-- If `‖f z‖ ≤ C` at all points of the segment `[a -[ℝ] b]`,
then the contour integral `∫ꟲ x in .segment a b, f x` has norm at most `C * ‖b - a‖`. -/
theorem norm_contourIntegral_segment_le {C : ℝ} (h : ∀ z ∈ [a -[ℝ] b], ‖f z‖ ≤ C) :
    ‖∫ꟲ x in .segment a b, f x‖ ≤ C * ‖b - a‖ :=
  norm_curveIntegral_segment_le <| by simpa

/-- If a function `f` is continuous on a set `s`,
then it is contour integrable along any $C^1$ path in this set. -/
theorem ContinuousOn.contourIntegrable_of_contDiffOn {s : Set ℂ}
    (hf : ContinuousOn f s) (hγ : ContDiffOn ℝ 1 γ.extend I) (hγs : ∀ t, γ t ∈ s) :
    ContourIntegrable f γ := by
  refine ContinuousOn.curveIntegrable_of_contDiffOn ?_ hγ hγs
  exact ContinuousLinearMap.toSpanSingletonCLE.continuous.comp_continuousOn hf

end PathOperations

/-!
### Algebraic operations on the function
-/

section Algebra

variable {f f₁ f₂ : ℂ → E} {γ : Path a b} {t : ℝ}

@[to_fun]
protected theorem ContourIntegrable.add (h₁ : ContourIntegrable f₁ γ)
    (h₂ : ContourIntegrable f₂ γ) :
    ContourIntegrable (f₁ + f₂) γ := by
  simpa [ContourIntegrable, Function.comp_def, ContinuousLinearMap.toSpanSingleton_add]
    using CurveIntegrable.add h₁ h₂

theorem contourIntegral_add (h₁ : ContourIntegrable f₁ γ) (h₂ : ContourIntegrable f₂ γ) :
    contourIntegral (f₁ + f₂) γ = ∫ꟲ x in γ, f₁ x + ∫ꟲ x in γ, f₂ x := by
  simpa [contourIntegral, ContinuousLinearMap.toSpanSingleton_add] using curveIntegral_add h₁ h₂

theorem contourIntegral_fun_add (h₁ : ContourIntegrable f₁ γ) (h₂ : ContourIntegrable f₂ γ) :
    ∫ꟲ x in γ, (f₁ x + f₂ x) = ∫ꟲ x in γ, f₁ x + ∫ꟲ x in γ, f₂ x :=
  contourIntegral_add h₁ h₂

@[to_fun (attr := simp)]
theorem ContourIntegrable.zero : ContourIntegrable (0 : ℂ → E) γ := by
  simp [ContourIntegrable]

@[simp]
theorem contourIntegral_zero : contourIntegral (0 : ℂ → E) γ = 0 := by simp [contourIntegral]

@[simp]
theorem contourIntegral_fun_zero : ∫ꟲ _ in γ, (0 : E) = 0 := contourIntegral_zero

@[to_fun]
theorem ContourIntegrable.neg (h : ContourIntegrable f γ) : ContourIntegrable (-f) γ := by
  simpa [ContourIntegrable, Function.comp_def, ContinuousLinearMap.toSpanSingleton_neg]
    using CurveIntegrable.neg h

@[simp]
theorem contourIntegrable_neg_iff : ContourIntegrable (-f) γ ↔ ContourIntegrable f γ :=
  ⟨fun h ↦ by simpa using h.neg, .neg⟩

@[simp]
theorem contourIntegrable_fun_neg_iff : ContourIntegrable (-f ·) γ ↔ ContourIntegrable f γ :=
  contourIntegrable_neg_iff

@[simp]
theorem contourIntegral_neg : contourIntegral (-f) γ = -∫ꟲ x in γ, f x := by
  simp [contourIntegral, ContinuousLinearMap.toSpanSingleton_neg]

@[simp]
theorem contourIntegral_fun_neg : ∫ꟲ x in γ, -f x = -∫ꟲ x in γ, f x := contourIntegral_neg

protected theorem ContourIntegrable.sub (h₁ : ContourIntegrable f₁ γ)
    (h₂ : ContourIntegrable f₂ γ) :
    ContourIntegrable (f₁ - f₂) γ :=
  sub_eq_add_neg f₁ f₂ ▸ h₁.add h₂.neg

theorem contourIntegral_sub (h₁ : ContourIntegrable f₁ γ) (h₂ : ContourIntegrable f₂ γ) :
    contourIntegral (f₁ - f₂) γ = ∫ꟲ x in γ, f₁ x - ∫ꟲ x in γ, f₂ x := by
  rw [sub_eq_add_neg, sub_eq_add_neg, contourIntegral_add h₁ h₂.neg, contourIntegral_neg]

theorem contourIntegral_fun_sub (h₁ : ContourIntegrable f₁ γ) (h₂ : ContourIntegrable f₂ γ) :
    ∫ꟲ x in γ, (f₁ x - f₂ x) = ∫ꟲ x in γ, f₁ x - ∫ꟲ x in γ, f₂ x :=
  contourIntegral_sub h₁ h₂

variable {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] [SMulCommClass ℂ 𝕜 E] {c : 𝕜}

@[simp]
theorem contourIntegrable_smul_iff :
    ContourIntegrable (c • f) γ ↔ c = 0 ∨ ContourIntegrable f γ := by
  simp [ContourIntegrable, Function.comp_def, ContinuousLinearMap.toSpanSingleton_smul,
    curveIntegrable_fun_smul_iff]

theorem ContourIntegrable.smul (h : ContourIntegrable f γ) (c : 𝕜) :
    ContourIntegrable (c • f) γ := by
  simp [h]

@[simp]
theorem contourIntegral_smul : contourIntegral (c • f) γ = c • contourIntegral f γ := by
  simp [contourIntegral, ContinuousLinearMap.toSpanSingleton_smul]

@[simp]
theorem contourIntegral_fun_smul : ∫ꟲ x in γ, c • f x = c • ∫ꟲ x in γ, f x := contourIntegral_smul

end Algebra
