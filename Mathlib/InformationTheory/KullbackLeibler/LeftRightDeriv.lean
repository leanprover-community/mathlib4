/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.RCLike.Basic

/-!
# Left and right derivatives of real functions

TODO: do we keep those definitions?

## Main definitions

* `rightDeriv f x`: right derivative of `f` at `x` if it exists, 0 otherwise.
  Defined as `derivWithin f (Ioi x) x`.

## Main statements

* `fooBar_unique`

-/


open Set Filter Topology

open scoped ENNReal NNReal

variable {f : ℝ → ℝ} {s : Set ℝ} {x y : ℝ}

lemma Filter.EventuallyEq.derivWithin_eq_nhds {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f₁ f : 𝕜 → F} {x : 𝕜} {s : Set 𝕜}
    (h : f₁ =ᶠ[𝓝 x] f) :
    derivWithin f₁ s x = derivWithin f s x := by
  simp_rw [derivWithin]
  rw [Filter.EventuallyEq.fderivWithin_eq_nhds h]




/-- The right derivative of a real function. -/
noncomputable
def rightDeriv (f : ℝ → ℝ) : ℝ → ℝ := fun x ↦ derivWithin f (Ioi x) x

lemma rightDeriv_def (f : ℝ → ℝ) (x : ℝ) : rightDeriv f x = derivWithin f (Ioi x) x := rfl

/-- The left derivative of a real function. -/
noncomputable
def leftDeriv (f : ℝ → ℝ) : ℝ → ℝ := fun x ↦ derivWithin f (Iio x) x

lemma leftDeriv_def (f : ℝ → ℝ) (x : ℝ) : leftDeriv f x = derivWithin f (Iio x) x := rfl

lemma rightDeriv_of_not_differentiableWithinAt (hf : ¬ DifferentiableWithinAt ℝ f (Ioi x) x) :
    rightDeriv f x = 0 := by
  rw [rightDeriv_def, derivWithin_zero_of_not_differentiableWithinAt hf]

lemma leftDeriv_of_not_differentiableWithinAt (hf : ¬ DifferentiableWithinAt ℝ f (Iio x) x) :
    leftDeriv f x = 0 := by
  rw [leftDeriv_def, derivWithin_zero_of_not_differentiableWithinAt hf]

lemma rightDeriv_eq_neg_leftDeriv_neg_apply (f : ℝ → ℝ) (x : ℝ) :
    rightDeriv f x = - leftDeriv (fun x ↦ f (-x)) (-x) := by
  change rightDeriv f x = -leftDeriv (f ∘ Neg.neg) (-x)
  have h_map : MapsTo Neg.neg (Iio (-x)) (Ioi x) := fun _ (h : _ < -x) ↦ lt_neg_of_lt_neg h
  have h_map' : MapsTo Neg.neg (Ioi x) (Iio (-x)) := fun _ (h : x < _) ↦ neg_lt_neg h
  by_cases hf_diff : DifferentiableWithinAt ℝ f (Ioi x) x
  swap
  · rw [rightDeriv_def, leftDeriv_def, derivWithin_zero_of_not_differentiableWithinAt hf_diff,
      derivWithin_zero_of_not_differentiableWithinAt, neg_zero]
    contrapose! hf_diff
    convert DifferentiableWithinAt.comp x hf_diff ((differentiable_neg _).differentiableWithinAt)
      h_map' using 1
    simp [Function.comp_assoc]
  · simp_rw [leftDeriv]
    rw [derivWithin_comp _ ((neg_neg x).symm ▸ hf_diff)
        (differentiable_neg _).differentiableWithinAt h_map,
      neg_neg, ← rightDeriv_def, derivWithin_neg _ _ (uniqueDiffWithinAt_Iio _)]
    simp only [mul_neg, mul_one, neg_neg]

lemma leftDeriv_eq_neg_rightDeriv_neg_apply (f : ℝ → ℝ) (x : ℝ) :
    leftDeriv f x = - rightDeriv (fun y ↦ f (-y)) (-x) := by
  simp [rightDeriv_eq_neg_leftDeriv_neg_apply, Function.comp_assoc]

lemma rightDeriv_eq_neg_leftDeriv_neg (f : ℝ → ℝ) :
    rightDeriv f = fun x ↦ - leftDeriv (fun y ↦ f (-y)) (-x) := by
  ext x
  simp [rightDeriv_eq_neg_leftDeriv_neg_apply]

lemma leftDeriv_eq_neg_rightDeriv_neg (f : ℝ → ℝ) :
    leftDeriv f = fun x ↦ - rightDeriv (fun y ↦ f (-y)) (-x) := by
  ext x
  simp [leftDeriv_eq_neg_rightDeriv_neg_apply]

lemma rightDeriv_congr {f g : ℝ → ℝ} {x : ℝ} (h : f =ᶠ[𝓝[>] x] g) (hx : f x = g x) :
    rightDeriv f x = rightDeriv g x := h.derivWithin_eq hx

lemma leftDeriv_congr {f g : ℝ → ℝ} {x : ℝ} (h : f =ᶠ[𝓝[<] x] g) (hx : f x = g x) :
    leftDeriv f x = leftDeriv g x := h.derivWithin_eq hx

lemma Filter.EventuallyEq.rightDeriv_eq_nhds {g : ℝ → ℝ} (h : f =ᶠ[𝓝 x] g) :
    rightDeriv f x = rightDeriv g x := h.derivWithin_eq_nhds

lemma Filter.EventuallyEq.leftDeriv_eq_nhds {g : ℝ → ℝ} (h : f =ᶠ[𝓝 x] g) :
    leftDeriv f x = leftDeriv g x := h.derivWithin_eq_nhds

lemma rightDeriv_congr_atTop {g : ℝ → ℝ} (h : f =ᶠ[atTop] g) :
    rightDeriv f =ᶠ[atTop] rightDeriv g := by
  have h' : ∀ᶠ x in atTop, f =ᶠ[𝓝 x] g := by
    -- todo: replace by clean filter proof?
    simp only [Filter.EventuallyEq, eventually_atTop, ge_iff_le] at h ⊢
    obtain ⟨a, ha⟩ := h
    refine ⟨a + 1, fun b hab ↦ ?_⟩
    have h_ge : ∀ᶠ x in 𝓝 b, a ≤ x := eventually_ge_nhds ((lt_add_one _).trans_le hab)
    filter_upwards [h_ge] using ha
  filter_upwards [h'] with a ha using ha.rightDeriv_eq_nhds

lemma HasDerivWithinAt.rightDeriv {f' : ℝ} (h : HasDerivWithinAt f f' (Ioi x) x) :
    rightDeriv f x = f' := h.derivWithin (uniqueDiffWithinAt_Ioi x)

lemma HasDerivWithinAt.leftDeriv {f' : ℝ} (h : HasDerivWithinAt f f' (Iio x) x) :
    leftDeriv f x = f' := h.derivWithin (uniqueDiffWithinAt_Iio x)

lemma HasDerivAt.rightDeriv {f' : ℝ} (h : HasDerivAt f f' x) :
    rightDeriv f x = f' := h.hasDerivWithinAt.rightDeriv

lemma HasDerivAt.leftDeriv {f' : ℝ} (h : HasDerivAt f f' x) :
    leftDeriv f x = f' := h.hasDerivWithinAt.leftDeriv

@[simp]
lemma rightDeriv_zero : rightDeriv 0 = 0 := by ext; simp [rightDeriv_def]

@[simp]
lemma rightDeriv_const (c : ℝ) : rightDeriv (fun _ ↦ c) = 0 := by ext; simp [rightDeriv_def]

@[simp]
lemma leftDeriv_const (c : ℝ) : leftDeriv (fun _ ↦ c) = 0 := by ext; simp [leftDeriv_def]

@[simp]
lemma rightDeriv_const_mul (a : ℝ) :
    rightDeriv (fun x ↦ a * f x) = fun x ↦ a * rightDeriv f x := by
  ext; exact derivWithin_const_mul_field a

@[simp]
lemma leftDeriv_const_mul (a : ℝ) :
    leftDeriv (fun x ↦ a * f x) = fun x ↦ a * leftDeriv f x := by
  simp_rw [leftDeriv_eq_neg_rightDeriv_neg, rightDeriv_const_mul, neg_mul_eq_mul_neg]

@[simp]
lemma rightDeriv_neg : rightDeriv (fun x ↦ - f x) = fun x ↦ - rightDeriv f x := by
  simp_rw [← neg_one_mul (f _), rightDeriv_const_mul, neg_one_mul]

@[simp]
lemma leftDeriv_neg : leftDeriv (fun x ↦ - f x) = fun x ↦ - leftDeriv f x := by
  simp [leftDeriv_eq_neg_rightDeriv_neg]

@[simp]
lemma rightDeriv_id : rightDeriv id = fun _ ↦ 1 := by
  ext x
  rw [rightDeriv_def, derivWithin_id _ _ (uniqueDiffWithinAt_Ioi x)]

@[simp]
lemma rightDeriv_id' : rightDeriv (fun x ↦ x) = fun _ ↦ 1 := rightDeriv_id

@[simp]
lemma leftDeriv_id : leftDeriv id = fun _ ↦ 1 := by
  ext x
  rw [leftDeriv_def, derivWithin_id _ _ (uniqueDiffWithinAt_Iio x)]

@[simp]
lemma leftDeriv_id' : leftDeriv (fun x ↦ x) = fun _ ↦ 1 := leftDeriv_id

@[simp]
lemma rightDeriv_neg_id {y : ℝ} : rightDeriv (fun x ↦ - x) y = - 1 := (hasDerivAt_neg _).rightDeriv

@[simp]
lemma leftDeriv_neg_id {y : ℝ} : leftDeriv (fun x ↦ - x) y = - 1 := (hasDerivAt_neg _).leftDeriv

lemma rightDeriv_add_apply {f g : ℝ → ℝ} {x : ℝ} (hf : DifferentiableWithinAt ℝ f (Ioi x) x)
    (hg : DifferentiableWithinAt ℝ g (Ioi x) x) :
    rightDeriv (f + g) x = rightDeriv f x + rightDeriv g x := by
  simp_rw [rightDeriv_def, ← derivWithin_add hf hg]
  rfl

lemma rightDeriv_add_apply' {f g : ℝ → ℝ} {x : ℝ} (hf : DifferentiableWithinAt ℝ f (Ioi x) x)
    (hg : DifferentiableWithinAt ℝ g (Ioi x) x) :
    rightDeriv (fun x ↦ f x + g x) x = rightDeriv f x + rightDeriv g x := by
  simp_rw [rightDeriv_def, ← derivWithin_add hf hg]

lemma rightDeriv_add {f g : ℝ → ℝ} (hf : ∀ x, DifferentiableWithinAt ℝ f (Ioi x) x)
    (hg : ∀ x, DifferentiableWithinAt ℝ g (Ioi x) x) :
    rightDeriv (f + g) = fun x ↦ rightDeriv f x + rightDeriv g x := by
  ext x; exact rightDeriv_add_apply (hf x) (hg x)

lemma rightDeriv_add' {f g : ℝ → ℝ} (hf : ∀ x, DifferentiableWithinAt ℝ f (Ioi x) x)
    (hg : ∀ x, DifferentiableWithinAt ℝ g (Ioi x) x) :
    rightDeriv (fun x ↦ f x + g x) = fun x ↦ rightDeriv f x + rightDeriv g x := by
  simp_rw [← Pi.add_apply f g, rightDeriv_add hf hg]

lemma leftDeriv_add_apply {f g : ℝ → ℝ} {x : ℝ} (hf : DifferentiableWithinAt ℝ f (Iio x) x)
    (hg : DifferentiableWithinAt ℝ g (Iio x) x) :
    leftDeriv (f + g) x = leftDeriv f x + leftDeriv g x := by
  simp_rw [leftDeriv_def, ← derivWithin_add hf hg]
  rfl

lemma leftDeriv_add_apply' {f g : ℝ → ℝ} {x : ℝ} (hf : DifferentiableWithinAt ℝ f (Iio x) x)
    (hg : DifferentiableWithinAt ℝ g (Iio x) x) :
    leftDeriv (fun x ↦ f x + g x) x = leftDeriv f x + leftDeriv g x := by
  simp_rw [leftDeriv_def, ← derivWithin_add hf hg]

lemma leftDeriv_add {f g : ℝ → ℝ} (hf : ∀ x, DifferentiableWithinAt ℝ f (Iio x) x)
    (hg : ∀ x, DifferentiableWithinAt ℝ g (Iio x) x) :
    leftDeriv (f + g) = fun x ↦ leftDeriv f x + leftDeriv g x := by
  ext x; exact leftDeriv_add_apply (hf x) (hg x)

lemma leftDeriv_add' {f g : ℝ → ℝ} (hf : ∀ x, DifferentiableWithinAt ℝ f (Iio x) x)
    (hg : ∀ x, DifferentiableWithinAt ℝ g (Iio x) x) :
    leftDeriv (fun x ↦ f x + g x) = fun x ↦ leftDeriv f x + leftDeriv g x := by
  simp_rw [← Pi.add_apply f g, leftDeriv_add hf hg]

lemma rightDeriv_add_const_apply (hf : DifferentiableWithinAt ℝ f (Ioi x) x) (c : ℝ) :
    rightDeriv (fun x ↦ f x + c) x = rightDeriv f x := by
  rw [rightDeriv_add_apply' hf (differentiableWithinAt_const c), rightDeriv_const,
    Pi.zero_apply, add_zero]

lemma rightDeriv_add_const (hf : ∀ x, DifferentiableWithinAt ℝ f (Ioi x) x) (c : ℝ) :
    rightDeriv (fun x ↦ f x + c) = rightDeriv f := by
  ext x; exact rightDeriv_add_const_apply (hf x) c

lemma leftDeriv_add_const_apply (hf : DifferentiableWithinAt ℝ f (Iio x) x) (c : ℝ) :
    leftDeriv (fun x ↦ f x + c) x = leftDeriv f x := by
  rw [leftDeriv_add_apply' hf (differentiableWithinAt_const c), leftDeriv_const,
    Pi.zero_apply, add_zero]

lemma leftDeriv_add_const (hf : ∀ x, DifferentiableWithinAt ℝ f (Iio x) x) (c : ℝ) :
    leftDeriv (fun x ↦ f x + c) = leftDeriv f := by
  ext x; exact leftDeriv_add_const_apply (hf x) c

lemma rightDeriv_add_linear_apply (hf : DifferentiableWithinAt ℝ f (Ioi x) x) (a : ℝ) :
    rightDeriv (fun x ↦ f x + a * x) x = rightDeriv f x + a := by
  rw [rightDeriv_add_apply' hf (by fun_prop), rightDeriv_const_mul, rightDeriv_id']
  simp

lemma rightDeriv_add_linear (hf : ∀ x, DifferentiableWithinAt ℝ f (Ioi x) x) (a : ℝ) :
    rightDeriv (fun x ↦ f x + a * x) = rightDeriv f + fun _ ↦ a := by
  ext x; exact rightDeriv_add_linear_apply (hf x) a

lemma leftDeriv_add_linear_apply (hf : DifferentiableWithinAt ℝ f (Iio x) x) (a : ℝ) :
    leftDeriv (fun x ↦ f x + a * x) x = leftDeriv f x + a := by
  rw [leftDeriv_add_apply' hf (by fun_prop), leftDeriv_const_mul, leftDeriv_id']
  simp

lemma leftDeriv_add_linear (hf : ∀ x, DifferentiableWithinAt ℝ f (Iio x) x) (a : ℝ) :
    leftDeriv (fun x ↦ f x + a * x) = leftDeriv f + fun _ ↦ a := by
  ext x; exact leftDeriv_add_linear_apply (hf x) a
