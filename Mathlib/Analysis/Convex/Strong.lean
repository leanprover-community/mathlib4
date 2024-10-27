/-
Copyright (c) 2023 Yaël Dillies, Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li, Ziyu Wang, Yaël Dillies
-/
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Uniformly and strongly convex functions

In this file, we define uniformly convex functions and strongly convex functions.

For a real normed space `E`, a uniformly convex function with modulus `φ : ℝ → ℝ` is a function
`f : E → ℝ` such that `f (t • x + (1 - t) • y) ≤ t • f x + (1 - t) • f y - t * (1 - t) * φ ‖x - y‖`
for all `t ∈ [0, 1]`.

A `m`-strongly convex function is a uniformly convex function with modulus `fun r ↦ m / 2 * r ^ 2`.
If `E` is an inner product space, this is equivalent to `x ↦ f x - m / 2 * ‖x‖ ^ 2` being convex.

## TODO

Prove derivative properties of strongly convex functions.
-/

open Real

variable {E : Type*} [NormedAddCommGroup E]

section NormedSpace
variable [NormedSpace ℝ E] {φ ψ : ℝ → ℝ} {s : Set E} {a b m : ℝ} {x y : E} {f g : E → ℝ}

/-- A function `f` from a real normed space is uniformly convex with modulus `φ` if
`f (t • x + (1 - t) • y) ≤ t • f x + (1 - t) • f y - t * (1 - t) * φ ‖x - y‖` for all `t ∈ [0, 1]`.

`φ` is usually taken to be a monotone function such that `φ r = 0 ↔ r = 0`. -/
def UniformConvexOn (s : Set E) (φ : ℝ → ℝ) (f : E → ℝ) : Prop :=
  Convex ℝ s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    f (a • x + b • y) ≤ a • f x + b • f y - a * b * φ ‖x - y‖

/-- A function `f` from a real normed space is uniformly concave with modulus `φ` if
`t • f x + (1 - t) • f y + t * (1 - t) * φ ‖x - y‖ ≤ f (t • x + (1 - t) • y)` for all `t ∈ [0, 1]`.

`φ` is usually taken to be a monotone function such that `φ r = 0 ↔ r = 0`. -/
def UniformConcaveOn (s : Set E) (φ : ℝ → ℝ) (f : E → ℝ) : Prop :=
  Convex ℝ s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    a • f x + b • f y + a * b * φ ‖x - y‖ ≤ f (a • x + b • y)

@[simp] lemma uniformConvexOn_zero : UniformConvexOn s 0 f ↔ ConvexOn ℝ s f := by
  simp [UniformConvexOn, ConvexOn]

@[simp] lemma uniformConcaveOn_zero : UniformConcaveOn s 0 f ↔ ConcaveOn ℝ s f := by
  simp [UniformConcaveOn, ConcaveOn]

protected alias ⟨_, ConvexOn.uniformConvexOn_zero⟩ := uniformConvexOn_zero
protected alias ⟨_, ConcaveOn.uniformConcaveOn_zero⟩ := uniformConcaveOn_zero

lemma UniformConvexOn.mono (hψφ : ψ ≤ φ) (hf : UniformConvexOn s φ f) : UniformConvexOn s ψ f :=
  ⟨hf.1, fun x hx y hy a b ha hb hab ↦ (hf.2 hx hy ha hb hab).trans <| by gcongr; apply hψφ⟩

lemma UniformConcaveOn.mono (hψφ : ψ ≤ φ) (hf : UniformConcaveOn s φ f) : UniformConcaveOn s ψ f :=
  ⟨hf.1, fun x hx y hy a b ha hb hab ↦ (hf.2 hx hy ha hb hab).trans' <| by gcongr; apply hψφ⟩

lemma UniformConvexOn.convexOn (hf : UniformConvexOn s φ f) (hφ : 0 ≤ φ) : ConvexOn ℝ s f := by
  simpa using hf.mono hφ

lemma UniformConcaveOn.concaveOn (hf : UniformConcaveOn s φ f) (hφ : 0 ≤ φ) : ConcaveOn ℝ s f := by
  simpa using hf.mono hφ

lemma UniformConvexOn.strictConvexOn (hf : UniformConvexOn s φ f) (hφ : ∀ r, r ≠ 0 → 0 < φ r) :
    StrictConvexOn ℝ s f := by
  refine ⟨hf.1, fun x hx y hy hxy a b ha hb hab ↦ (hf.2 hx hy ha.le hb.le hab).trans_lt <|
    sub_lt_self _ ?_⟩
  rw [← sub_ne_zero, ← norm_pos_iff] at hxy
  have := hφ _ hxy.ne'
  positivity

lemma UniformConcaveOn.strictConcaveOn (hf : UniformConcaveOn s φ f) (hφ : ∀ r, r ≠ 0 → 0 < φ r) :
    StrictConcaveOn ℝ s f := by
  refine ⟨hf.1, fun x hx y hy hxy a b ha hb hab ↦ (hf.2 hx hy ha.le hb.le hab).trans_lt' <|
    lt_add_of_pos_right _ ?_⟩
  rw [← sub_ne_zero, ← norm_pos_iff] at hxy
  have := hφ _ hxy.ne'
  positivity

lemma UniformConvexOn.add (hf : UniformConvexOn s φ f) (hg : UniformConvexOn s ψ g) :
    UniformConvexOn s (φ + ψ) (f + g) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab ↦ ?_⟩
  simpa [mul_add, add_add_add_comm, sub_add_sub_comm]
    using add_le_add (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)

lemma UniformConcaveOn.add (hf : UniformConcaveOn s φ f) (hg : UniformConcaveOn s ψ g) :
    UniformConcaveOn s (φ + ψ) (f + g) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab ↦ ?_⟩
  simpa [mul_add, add_add_add_comm] using add_le_add (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)

lemma UniformConvexOn.neg (hf : UniformConvexOn s φ f) : UniformConcaveOn s φ (-f) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab ↦ le_of_neg_le_neg ?_⟩
  simpa [add_comm, -neg_le_neg_iff, le_sub_iff_add_le'] using hf.2 hx hy ha hb hab

lemma UniformConcaveOn.neg (hf : UniformConcaveOn s φ f) : UniformConvexOn s φ (-f) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab ↦ le_of_neg_le_neg ?_⟩
  simpa [add_comm, -neg_le_neg_iff, ← le_sub_iff_add_le', sub_eq_add_neg, neg_add]
    using hf.2 hx hy ha hb hab

lemma UniformConvexOn.sub (hf : UniformConvexOn s φ f) (hg : UniformConcaveOn s ψ g) :
    UniformConvexOn s (φ + ψ) (f - g) := by simpa using hf.add hg.neg

lemma UniformConcaveOn.sub (hf : UniformConcaveOn s φ f) (hg : UniformConvexOn s ψ g) :
    UniformConcaveOn s (φ + ψ) (f - g) := by simpa using hf.add hg.neg

/-- A function `f` from a real normed space is `m`-strongly convex if it is uniformly convex with
modulus `φ(r) = m / 2 * r ^ 2`.

In an inner product space, this is equivalent to `x ↦ f x - m / 2 * ‖x‖ ^ 2` being convex. -/
def StrongConvexOn (s : Set E) (m : ℝ) : (E → ℝ) → Prop :=
  UniformConvexOn s fun r ↦ m / (2 : ℝ) * r ^ 2

/-- A function `f` from a real normed space is `m`-strongly concave if is strongly concave with
modulus `φ(r) = m / 2 * r ^ 2`.

In an inner product space, this is equivalent to `x ↦ f x + m / 2 * ‖x‖ ^ 2` being concave. -/
def StrongConcaveOn (s : Set E) (m : ℝ) : (E → ℝ) → Prop :=
  UniformConcaveOn s fun r ↦ m / (2 : ℝ) * r ^ 2

variable {s : Set E} {f : E → ℝ} {m n : ℝ}

nonrec lemma StrongConvexOn.mono (hmn : m ≤ n) (hf : StrongConvexOn s n f) : StrongConvexOn s m f :=
  hf.mono fun r ↦ by gcongr

nonrec lemma StrongConcaveOn.mono (hmn : m ≤ n) (hf : StrongConcaveOn s n f) :
    StrongConcaveOn s m f := hf.mono fun r ↦ by gcongr

@[simp] lemma strongConvexOn_zero : StrongConvexOn s 0 f ↔ ConvexOn ℝ s f := by
  simp [StrongConvexOn, ← Pi.zero_def]

@[simp] lemma strongConcaveOn_zero : StrongConcaveOn s 0 f ↔ ConcaveOn ℝ s f := by
  simp [StrongConcaveOn, ← Pi.zero_def]

nonrec lemma StrongConvexOn.strictConvexOn (hf : StrongConvexOn s m f) (hm : 0 < m) :
    StrictConvexOn ℝ s f := hf.strictConvexOn fun r hr ↦ by positivity

nonrec lemma StrongConcaveOn.strictConcaveOn (hf : StrongConcaveOn s m f) (hm : 0 < m) :
    StrictConcaveOn ℝ s f := hf.strictConcaveOn fun r hr ↦ by positivity

end NormedSpace

section InnerProductSpace
variable [InnerProductSpace ℝ E] {φ ψ : ℝ → ℝ} {s : Set E} {a b m : ℝ} {x y : E} {f : E → ℝ}

private lemma aux_sub (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * (f x - m / (2 : ℝ) * ‖x‖ ^ 2) + b * (f y - m / (2 : ℝ) * ‖y‖ ^ 2) +
      m / (2 : ℝ) * ‖a • x + b • y‖ ^ 2
      = a * f x + b * f y - m / (2 : ℝ) * a * b * ‖x - y‖ ^ 2 := by
  rw [norm_add_sq_real, norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left,
    inner_smul_right, norm_of_nonneg ha, norm_of_nonneg hb, mul_pow, mul_pow]
  obtain rfl := eq_sub_of_add_eq hab
  ring_nf

private lemma aux_add (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * (f x + m / (2 : ℝ) * ‖x‖ ^ 2) + b * (f y + m / (2 : ℝ) * ‖y‖ ^ 2) -
      m / (2 : ℝ) * ‖a • x + b • y‖ ^ 2
      = a * f x + b * f y + m / (2 : ℝ) * a * b * ‖x - y‖ ^ 2 := by
  simpa [neg_div] using aux_sub (E := E) (m := -m) ha hb hab

lemma strongConvexOn_iff_convex :
    StrongConvexOn s m f ↔ ConvexOn ℝ s fun x ↦ f x - m / (2 : ℝ) * ‖x‖ ^ 2 := by
  refine and_congr_right fun _ ↦ forall₄_congr fun x _ y _ ↦ forall₅_congr fun a b ha hb hab ↦ ?_
  simp_rw [sub_le_iff_le_add, smul_eq_mul, aux_sub ha hb hab, mul_assoc, mul_left_comm]

lemma strongConcaveOn_iff_convex :
    StrongConcaveOn s m f ↔ ConcaveOn ℝ s fun x ↦ f x + m / (2 : ℝ) * ‖x‖ ^ 2 := by
  refine and_congr_right fun _ ↦ forall₄_congr fun x _ y _ ↦ forall₅_congr fun a b ha hb hab ↦ ?_
  simp_rw [← sub_le_iff_le_add, smul_eq_mul, aux_add ha hb hab, mul_assoc, mul_left_comm]

end InnerProductSpace
