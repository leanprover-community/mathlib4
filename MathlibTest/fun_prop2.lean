import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.MeasurableSpace.Basic

import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.Tactic.FunProp.Simproc


noncomputable
def foo (x : ℝ) := x * (Real.log x) ^ 2 - Real.exp x / x

example : ContinuousOn foo {0}ᶜ := by
  unfold foo; fun_prop (disch := aesop)

example (y : ℝ) (hy : y ≠ 0) : ContinuousAt (fun x => x * (Real.log x) ^ 2 - Real.exp x / x) y := by
  fun_prop (disch := aesop)


example : DifferentiableOn ℝ foo {0}ᶜ := by
  fun_prop (disch := aesop) [foo] -- equivalent to `unfold foo; fun_prop (disch := aesop)`

example (y : ℝ) (hy : y ≠ 0) : DifferentiableAt ℝ foo y := by
  unfold foo; fun_prop (disch := aesop)

example {n} : ContDiffOn ℝ n foo {0}ᶜ := by
  unfold foo; fun_prop (disch := aesop)

example {n} (y : ℝ) (hy : y ≠ 0) :
    ContDiffAt ℝ n foo y := by
  unfold foo; fun_prop (disch := aesop)

example : Continuous fun ((x, _, _) : ℝ × ℝ × ℝ) ↦ x := by fun_prop
example : Continuous fun ((_, y, _) : ℝ × ℝ × ℝ) ↦ y := by fun_prop
example : Continuous fun ((_, _, z) : ℝ × ℝ × ℝ) ↦ z := by fun_prop

-- This theorem is meant to work together with `measurable_of_continuousOn_compl_singleton`
-- Unification of `(hf : ContinuousOn f {a}ᶜ)` with this theorem determines the point `a` to be `0`
@[fun_prop]
theorem ContinuousOn.log' : ContinuousOn Real.log {0}ᶜ := ContinuousOn.log (by fun_prop) (by aesop)

-- Notice that no theorems about measurability of log are used. It is inferred from continuity.
example : Measurable (fun x ↦ x * (Real.log x) ^ 2 - Real.exp x / x) := by
  fun_prop

-- Notice that no theorems about measurability of log are used. It is inferred from continuity.
example : AEMeasurable (fun x ↦ x * (Real.log x) ^ 2 - Real.exp x / x) := by
  fun_prop (maxTransitionDepth := 2)



private noncomputable def S (a b c d : ℝ) : ℝ :=
    a / (a + b + d) + b / (a + b + c) +
    c / (b + c + d) + d / (a + c + d)

private noncomputable def T (t : ℝ) : ℝ := S 1 (1 - t) t (t * (1 - t))

example : ContinuousOn T (Set.Icc 0 1) := by
  unfold T S
  fun_prop (disch := (rintro x ⟨a,b⟩; nlinarith))


example : DifferentiableOn ℝ T (Set.Icc 0 1) := by
  unfold T S
  fun_prop (disch := (rintro x ⟨a,b⟩; nlinarith))

example {n}: ContDiffOn ℝ n T (Set.Icc 0 1) := by
  unfold T S
  fun_prop (disch := (rintro x ⟨a,b⟩; nlinarith))

example : Measurable T := by
  unfold T S
  fun_prop

example : AEMeasurable T := by
  unfold T S
  fun_prop


private theorem t1 : (5: ℕ) + (1 : ℕ∞) ≤ (12 : WithTop ℕ∞) := by norm_cast

example {f : ℝ → ℝ} (hf : ContDiff ℝ 12 f) :
    Differentiable ℝ (iteratedDeriv 5 (fun x ↦ f (2 * (f (x + x))) + x)) := by
  fun_prop (disch := (exact t1))

-- This example used to panic due to loose bvars before #31001.
-- TODO: this still fails because `fun_prop` cannot use `hl`.
/--
error: `fun_prop` was unable to prove `MeasureTheory.AEStronglyMeasurable l.prod μ`

Issues:
  No theorems found for `f` in order to prove `MeasureTheory.AEStronglyMeasurable (fun a => f a) μ`
-/
#guard_msgs in
example {α : Type*} {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α} {M : Type*}
    [CommMonoid M] [TopologicalSpace M] [ContinuousMul M] (l : Multiset (α → M))
    (hl : ∀ f ∈ l, MeasureTheory.AEStronglyMeasurable f μ) :
    MeasureTheory.AEStronglyMeasurable l.prod μ := by
  fun_prop (disch := assumption)






variable
  (x₀ : ℝ) (y : ℝ)
  (f : ℝ → ℝ) {f' : ℝ → _} (hf : ∀ x, HasFDerivAt (𝕜:=ℝ) f (f' x) x)
  (g : ℝ → ℝ) {g' : ℝ → _} (hg : ∀ x, HasFDerivAt (𝕜:=ℝ) g (g' x) x)

example : HasFDerivAt (𝕜:=ℝ) (fun x : ℝ => x) (ContinuousLinearMap.id ℝ ℝ) x₀ := by
  apply HasFDerivAt.congr_fderiv
  · fun_prop
  · rfl

example : HasFDerivAt (𝕜:=ℝ) (fun _ : ℝ => y) 0 x₀ := by
  fun_prop

example : HasFDerivAt (𝕜:=ℝ) (fun x : ℝ => f (g x)) ((f' (g x₀)).comp (g' x₀)) x₀ := by
  fun_prop


example : HasFDerivAt (𝕜:=ℝ) (fun x : ℝ => f (f (f (f x))))
    ((f' (f (f (f x₀)))).comp ((f' (f (f x₀))).comp ((f' (f x₀)).comp (f' x₀)))) x₀ := by
  fun_prop

attribute [fun_prop] HasFDerivAt.exp

theorem hasDerivAt_from_hasFDerivAt {f : ℝ → ℝ} {f' : ℝ}
    {f'' : ℝ →L[ℝ] ℝ} {x : ℝ} (hf : HasFDerivAt f f'' x) (h : f' = f'' 1) :
    HasDerivAt f f' x := by
  rw [h]
  exact hasFDerivAt_iff_hasDerivAt.1 hf

example {t x : ℝ} (n : ℕ) :
    HasDerivAt (fun t ↦ x ^ n * Real.exp (t * x)) (x ^ (n + 1) * Real.exp (t * x)) t := by
  apply HasDerivAt.congr_deriv
  · apply HasFDerivAt.hasDerivAt
    fun_prop
  · simp; ring

example : HasFDerivAt (𝕜:=ℝ) (fun x : ℝ => Real.exp (f x)) (Real.exp (f x₀) • f' x₀) x₀ := by
  fun_prop

variable {t x : ℝ} (n : ℕ)

example : HasFDerivAt (fun t ↦ x ^ n * Real.exp (t * x))
    (x ^ n • Real.exp (t * x) • MulOpposite.op x • ContinuousLinearMap.id ℝ ℝ) t := by
  fun_prop

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

@[fun_prop]
theorem hasFDerivAt_fun_id (x : E) : HasFDerivAt (fun x : E => x) (.id 𝕜 E) x :=
  hasFDerivAtFilter_id _

protected theorem HasFDerivAt.fderiv_forall {f : E → F} {f' : E → E →L[𝕜] F}
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]
    (h : ∀ x, HasFDerivAt f (f' x) x) :
    fderiv 𝕜 f = f' := by
  funext x; apply (h x).fderiv

simproc_decl fderiv_simproc_at (fderiv _ _ _) :=
  Mathlib.Meta.FunProp.mkFunPropSimproc decl_name% ``HasFDerivAt.fderiv

simproc_decl fderiv_simproc_forall (fderiv _ _) :=
  Mathlib.Meta.FunProp.mkFunPropSimproc decl_name% ``HasFDerivAt.fderiv_forall

attribute [deriv_simproc] fderiv_simproc_at fderiv_simproc_forall

example (t₀) : fderiv ℝ (fun t ↦ x ^ n * Real.exp (t * x)) t₀ 1
               =
               x ^ (n + 1) * Real.exp (x * t₀) := by
  simp [deriv_simproc]
  ring_nf


variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {x : 𝕜} {s : Set 𝕜}
variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] {c d : 𝕜 → 𝕜'} {c' d'}
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

attribute [fun_prop out f'] HasDerivAt

attribute [fun_prop]
  hasDerivAt_id'
  hasDerivAt_const
  HasDerivAt.comp_hasFDerivAt

  HasDerivAt.fun_add
  HasDerivAt.fun_sub
  HasDerivAt.fun_neg
  HasDerivAt.fun_mul
  HasDerivAt.fun_smul
  HasDerivAt.fun_div
  HasDerivAt.fun_inv

attribute [fun_prop]
  HasFDerivAt.hasDerivAt
  HasDerivAt.hasFDerivAt

theorem HasDerivAt.deriv' (f : 𝕜 → F) {f' : 𝕜 → F} (h : ∀ x, HasDerivAt f (f' x) x) : _root_.deriv f = f' := by
  funext x
  apply HasDerivAt.deriv (h x)


simproc_decl deriv_simproc_at (deriv _ _) :=
  Mathlib.Meta.FunProp.mkFunPropSimproc decl_name% ``HasDerivAt.deriv

simproc_decl deriv_simproc_forall (deriv _) :=
  Mathlib.Meta.FunProp.mkFunPropSimproc decl_name% ``HasDerivAt.deriv'

attribute [deriv_simproc] deriv_simproc_at deriv_simproc_forall

attribute [fun_prop] HasDerivAt.exp

example (x : ℝ) :
    deriv (fun t : ℝ ↦ x ^ n * Real.exp (t * x))
    =
    fun t => x ^ (n + 1) * Real.exp (x * t) := by
  simp only [deriv_simproc]
  simp; ring_nf
example : HasDerivAt (fun x : ℝ => x * x) (1 * x₀ + x₀ * 1) x₀ := by
  fun_prop

example (f : ℝ → ℝ) (f' : ℝ) (hf : HasDerivAt (𝕜:=ℝ) f f' x₀) : HasFDerivAt (𝕜:=ℝ) f (ContinuousLinearMap.toSpanSingleton ℝ f') x₀ := by
  apply HasFDerivAt.congr_fderiv
  · fun_prop
  · rfl

example (f : ℝ → ℝ) (f' : ℝ) (hf : HasDerivAt (𝕜:=ℝ) f f' x₀) :
    fderiv ℝ (fun x => f x) x₀ 1 = f' := by
  simp only [deriv_simproc]
  simp

example (g : ℝ → ℝ) (g' : ℝ →L[ℝ] ℝ) (hf : HasFDerivAt g g' x₀): HasDerivAt (𝕜:=ℝ) g (g' 1) x₀ := by
  apply HasDerivAt.congr_deriv
  · fun_prop
  · rfl

example (f : ℝ → ℝ) (f' : ℝ →L[ℝ] ℝ) (hf : HasFDerivAt (𝕜:=ℝ) f f' x₀) :
    deriv f x₀ = f' 1 := by
  simp only [deriv_simproc]

example (hx₀ : x₀ > 0) : HasFDerivAt (𝕜:=ℝ) (fun x : ℝ => 1 / x)
    (ContinuousLinearMap.toSpanSingleton ℝ ((0 * x₀ - 1 * 1) / x₀ ^ 2)) x₀ := by
  apply HasDerivAt.hasFDerivAt
  fun_prop (disch := positivity)

example (hx₀ : x₀ > 0) : DifferentiableAt ℝ (fun x : ℝ => (x * x) / (x + 3 * x + x * x)) x₀ := by
  fun_prop (disch := positivity)

example (hx₀ : x₀ > 0) :
        deriv (fun x : ℝ => (x*x) / (x + 3 * x + x*x)) x₀
        =
        x₀ ^ 2 * (x₀ ^ 2 * 16 + x₀ ^ 3 * 8 + x₀ ^ 4)⁻¹ * 4 := by
  simp (disch := positivity) [deriv_simproc]
  ring

example (hx₀ : x₀ > 0) : deriv (fun x : ℝ => 1 / x) x₀ = - 1 / x₀^2 := by
  simp (disch:= grind) only [deriv_simproc]
  simp

example (hx₀ : x₀ ∈ Set.Ioo 0 1) : deriv T x₀ =
  (x₀ + (x₀ - 1) + 1) / (1 + (1 - x₀) + x₀ * (1 - x₀)) ^ 2 + (-x₀ + (x₀ - 1 + -1)) / (1 + (1 - x₀) + x₀) ^ 2 +
        (1 + x₀ * (1 - x₀) - x₀ * (1 - x₀ + -x₀)) / (1 + x₀ * (1 - x₀)) ^ 2 +
      ((1 - x₀ + -x₀) * (1 + x₀ + x₀ * (1 - x₀)) - x₀ * (1 - x₀) * (1 + (1 - x₀ + -x₀))) / (1 + x₀ + x₀ * (1 - x₀)) ^ 2 := by
  unfold T S
  have ⟨_,_⟩ := hx₀
  simp (disch := nlinarith) [deriv_simproc]
