/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.Convex.NNReal

/-!
# Hölder continuous functions

In this file we define Hölder continuity on a set and on the whole space. We also prove some basic
properties of Hölder continuous functions.

## Main definitions

* `HolderOnWith`: `f : X → Y` is said to be *Hölder continuous* with constant `C : ℝ≥0` and
  exponent `r : ℝ≥0` on a set `s`, if `edist (f x) (f y) ≤ C * edist x y ^ r` for all `x y ∈ s`;
* `HolderWith`: `f : X → Y` is said to be *Hölder continuous* with constant `C : ℝ≥0` and exponent
  `r : ℝ≥0`, if `edist (f x) (f y) ≤ C * edist x y ^ r` for all `x y : X`.

## Implementation notes

We use the type `ℝ≥0` (a.k.a. `NNReal`) for `C` because this type has coercion both to `ℝ` and
`ℝ≥0∞`, so it can be easily used both in inequalities about `dist` and `edist`. We also use `ℝ≥0`
for `r` to ensure that `d ^ r` is monotone in `d`. It might be a good idea to use
`ℝ>0` for `r` but we don't have this type in `mathlib` (yet).

## Tags

Hölder continuity, Lipschitz continuity

-/

@[expose] public section


variable {X Y Z : Type*}

open Filter Set Metric
open scoped NNReal ENNReal Topology

section EMetric

variable [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [PseudoEMetricSpace Z]

/-- A function `f : X → Y` between two `PseudoEMetricSpace`s is Hölder continuous with constant
`C : ℝ≥0` and exponent `r : ℝ≥0`, if `edist (f x) (f y) ≤ C * edist x y ^ r` for all `x y : X`. -/
def HolderWith (C r : ℝ≥0) (f : X → Y) : Prop :=
  ∀ x y, edist (f x) (f y) ≤ (C : ℝ≥0∞) * edist x y ^ (r : ℝ)

/-- A function `f : X → Y` between two `PseudoEMetricSpace`s is Hölder continuous with constant
`C : ℝ≥0` and exponent `r : ℝ≥0` on a set `s : Set X`, if `edist (f x) (f y) ≤ C * edist x y ^ r`
for all `x y ∈ s`. -/
def HolderOnWith (C r : ℝ≥0) (f : X → Y) (s : Set X) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, edist (f x) (f y) ≤ (C : ℝ≥0∞) * edist x y ^ (r : ℝ)

@[simp]
theorem holderOnWith_empty (C r : ℝ≥0) (f : X → Y) : HolderOnWith C r f ∅ := fun _ hx => hx.elim

@[simp]
theorem holderOnWith_singleton (C r : ℝ≥0) (f : X → Y) (x : X) : HolderOnWith C r f {x} := by
  rintro a (rfl : a = x) b (rfl : b = a)
  rw [edist_self]
  exact zero_le _

theorem Set.Subsingleton.holderOnWith {s : Set X} (hs : s.Subsingleton) (C r : ℝ≥0) (f : X → Y) :
    HolderOnWith C r f s :=
  hs.induction_on (holderOnWith_empty C r f) (holderOnWith_singleton C r f)

theorem holderOnWith_univ {C r : ℝ≥0} {f : X → Y} : HolderOnWith C r f univ ↔ HolderWith C r f := by
  simp only [HolderOnWith, HolderWith, mem_univ, true_imp_iff]

@[simp]
theorem holderOnWith_one {C : ℝ≥0} {f : X → Y} {s : Set X} :
    HolderOnWith C 1 f s ↔ LipschitzOnWith C f s := by
  simp only [HolderOnWith, LipschitzOnWith, NNReal.coe_one, ENNReal.rpow_one]

alias ⟨_, LipschitzOnWith.holderOnWith⟩ := holderOnWith_one

@[simp]
theorem holderWith_one {C : ℝ≥0} {f : X → Y} : HolderWith C 1 f ↔ LipschitzWith C f :=
  holderOnWith_univ.symm.trans <| holderOnWith_one.trans lipschitzOnWith_univ

alias ⟨_, LipschitzWith.holderWith⟩ := holderWith_one

theorem holderWith_id : HolderWith 1 1 (id : X → X) :=
  LipschitzWith.id.holderWith

protected theorem HolderWith.holderOnWith {C r : ℝ≥0} {f : X → Y} (h : HolderWith C r f)
    (s : Set X) : HolderOnWith C r f s := fun x _ y _ => h x y

namespace HolderOnWith

variable {C r : ℝ≥0} {f : X → Y} {s t : Set X}

theorem edist_le (h : HolderOnWith C r f s) {x y : X} (hx : x ∈ s) (hy : y ∈ s) :
    edist (f x) (f y) ≤ (C : ℝ≥0∞) * edist x y ^ (r : ℝ) :=
  h x hx y hy

theorem edist_le_of_le (h : HolderOnWith C r f s) {x y : X} (hx : x ∈ s) (hy : y ∈ s) {d : ℝ≥0∞}
    (hd : edist x y ≤ d) : edist (f x) (f y) ≤ (C : ℝ≥0∞) * d ^ (r : ℝ) :=
  (h.edist_le hx hy).trans <| by gcongr

theorem comp {Cg rg : ℝ≥0} {g : Y → Z} {t : Set Y} (hg : HolderOnWith Cg rg g t) {Cf rf : ℝ≥0}
    {f : X → Y} (hf : HolderOnWith Cf rf f s) (hst : MapsTo f s t) :
    HolderOnWith (Cg * Cf ^ (rg : ℝ)) (rg * rf) (g ∘ f) s := by
  intro x hx y hy
  rw [ENNReal.coe_mul, mul_comm rg, NNReal.coe_mul, ENNReal.rpow_mul, mul_assoc,
    ENNReal.coe_rpow_of_nonneg _ rg.coe_nonneg, ← ENNReal.mul_rpow_of_nonneg _ _ rg.coe_nonneg]
  exact hg.edist_le_of_le (hst hx) (hst hy) (hf.edist_le hx hy)

theorem comp_holderWith {Cg rg : ℝ≥0} {g : Y → Z} {t : Set Y} (hg : HolderOnWith Cg rg g t)
    {Cf rf : ℝ≥0} {f : X → Y} (hf : HolderWith Cf rf f) (ht : ∀ x, f x ∈ t) :
    HolderWith (Cg * Cf ^ (rg : ℝ)) (rg * rf) (g ∘ f) :=
  holderOnWith_univ.mp <| hg.comp (hf.holderOnWith univ) fun x _ => ht x

/-- A Hölder continuous function is uniformly continuous -/
protected theorem uniformContinuousOn (hf : HolderOnWith C r f s) (h0 : 0 < r) :
    UniformContinuousOn f s := by
  refine EMetric.uniformContinuousOn_iff.2 fun ε εpos => ?_
  have : Tendsto (fun d : ℝ≥0∞ => (C : ℝ≥0∞) * d ^ (r : ℝ)) (𝓝 0) (𝓝 0) :=
    ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos ENNReal.coe_ne_top h0
  rcases ENNReal.nhds_zero_basis.mem_iff.1 (this (gt_mem_nhds εpos)) with ⟨δ, δ0, H⟩
  exact ⟨δ, δ0, fun hx y hy h => (hf.edist_le hx hy).trans_lt (H h)⟩

protected theorem continuousOn (hf : HolderOnWith C r f s) (h0 : 0 < r) : ContinuousOn f s :=
  (hf.uniformContinuousOn h0).continuousOn

protected theorem mono (hf : HolderOnWith C r f s) (ht : t ⊆ s) : HolderOnWith C r f t :=
  fun _ hx _ hy => hf.edist_le (ht hx) (ht hy)

theorem ediam_image_le_of_le (hf : HolderOnWith C r f s) {d : ℝ≥0∞} (hd : ediam s ≤ d) :
    ediam (f '' s) ≤ (C : ℝ≥0∞) * d ^ (r : ℝ) :=
  ediam_image_le_iff.2 fun _ hx _ hy =>
    hf.edist_le_of_le hx hy <| (edist_le_ediam_of_mem hx hy).trans hd

theorem ediam_image_le (hf : HolderOnWith C r f s) :
    ediam (f '' s) ≤ (C : ℝ≥0∞) * ediam s ^ (r : ℝ) :=
  hf.ediam_image_le_of_le le_rfl

theorem ediam_image_le_of_subset (hf : HolderOnWith C r f s) (ht : t ⊆ s) :
    ediam (f '' t) ≤ (C : ℝ≥0∞) * ediam t ^ (r : ℝ) :=
  (hf.mono ht).ediam_image_le

theorem ediam_image_le_of_subset_of_le (hf : HolderOnWith C r f s) (ht : t ⊆ s) {d : ℝ≥0∞}
    (hd : ediam t ≤ d) : ediam (f '' t) ≤ (C : ℝ≥0∞) * d ^ (r : ℝ) :=
  (hf.mono ht).ediam_image_le_of_le hd

theorem ediam_image_inter_le_of_le (hf : HolderOnWith C r f s) {d : ℝ≥0∞}
    (hd : ediam t ≤ d) : ediam (f '' (t ∩ s)) ≤ (C : ℝ≥0∞) * d ^ (r : ℝ) :=
  hf.ediam_image_le_of_subset_of_le inter_subset_right <|
    (ediam_mono inter_subset_left).trans hd

theorem ediam_image_inter_le (hf : HolderOnWith C r f s) (t : Set X) :
    ediam (f '' (t ∩ s)) ≤ (C : ℝ≥0∞) * ediam t ^ (r : ℝ) :=
  hf.ediam_image_inter_le_of_le le_rfl

/-- If a function is `(C₁, r)`-Hölder and `(C₂, s)`-Hölder, then it is
`(C₁ ^ t₁ * C₂ ^ t₂, r * t₁ + s * t₂)`-Hölder for all `t₁ t₂ : ℝ≥0` such that
`t₁ + t₂ = 1`. -/
lemma interpolate {C₁ C₂ s t₁ t₂ : ℝ≥0} {A : Set X}
    (hf₁ : HolderOnWith C₁ r f A) (hf₂ : HolderOnWith C₂ s f A) (ht : t₁ + t₂ = 1) :
    HolderOnWith (C₁ ^ (t₁ : ℝ) * C₂ ^ (t₂ : ℝ)) (r * t₁ + s * t₂) f A := by
  intro x hx y hy
  calc edist (f x) (f y)
      = (edist (f x) (f y)) ^ (t₁ : ℝ) * (edist (f x) (f y)) ^ (t₂ : ℝ) := by
        simp [← ENNReal.rpow_add_of_nonneg, ← NNReal.coe_add, ht]
    _ ≤ (C₁ * (edist x y) ^ (r : ℝ)) ^ (t₁ : ℝ) * (C₂ * (edist x y) ^ (s : ℝ)) ^ (t₂ : ℝ) := by
        nth_grw 1 [hf₁ x hx y hy, hf₂ x hx y hy]
    _ = ↑(C₁ ^ (t₁ : ℝ) * C₂ ^ (t₂ : ℝ)) * (edist x y) ^ (↑(r * t₁ + s * t₂) : ℝ) := by
        push_cast
        simp (discharger := positivity) only [ENNReal.mul_rpow_of_nonneg,
          ENNReal.rpow_add_of_nonneg, ENNReal.rpow_mul, ENNReal.coe_rpow_of_nonneg]
        ring

/-- If a function is Hölder over a bounded set, then it is bounded. -/
lemma holderOnWith_zero_of_bounded {C D : ℝ≥0} {A : Set X}
    (hA : ∀ x ∈ A, ∀ y ∈ A, edist x y ≤ D) (hf : HolderOnWith C r f A) :
    HolderOnWith (C * D ^ (r : ℝ)) 0 f A := by
  intro x hx y hy
  simp only [NNReal.coe_zero, ENNReal.rpow_zero, mul_one]
  grw [hf x hx y hy, hA x hx y hy, ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg _ (by simp)]

/-- If a function is `r`-Hölder over a bounded set, then it is also `s`-Hölder when `s ≤ r`. -/
lemma of_le {C D s : ℝ≥0} {A : Set X}
    (hA : ∀ x ∈ A, ∀ y ∈ A, edist x y ≤ D) (hf : HolderOnWith C r f A) (hsr : s ≤ r) :
    HolderOnWith (C * D ^ (r - s : ℝ)) s f A := by
  obtain rfl | ht := eq_zero_or_pos s
  · simpa using hf.holderOnWith_zero_of_bounded hA
  have hr : 0 < r := ht.trans_le hsr
  rw [← NNReal.coe_le_coe] at hsr
  rw [← NNReal.coe_pos] at hr
  set θ₁ : ℝ≥0 := .mk (s / r) (by positivity)
  set θ₂ : ℝ≥0 := .mk (1 - s / r) (by simpa using div_le_one_of_le₀ hsr (by positivity))
  have hθ : θ₁ + θ₂ = 1 := by ext; simp [θ₁, θ₂]
  have hθt : r * θ₁ + 0 * θ₂ = s := by ext; simp [θ₁, mul_div_cancel₀ _ hr.ne']
  have hθC : C * D ^ (r - s : ℝ) = C ^ (θ₁ : ℝ) * (C * D ^ (r : ℝ)) ^ (θ₂ : ℝ) := by
    simp (discharger := positivity) only [NNReal.mul_rpow, ← mul_assoc,
      ← NNReal.rpow_add_of_nonneg, ← NNReal.rpow_mul, ← NNReal.coe_add, hθ, NNReal.coe_one,
      NNReal.rpow_one]
    congr
    simp [mul_sub, θ₂, mul_div_cancel₀ _ hr.ne']
  rw [hθC, ← hθt]
  exact hf.interpolate (hf.holderOnWith_zero_of_bounded hA) hθ

lemma mono_const {C₁ C₂ : ℝ≥0} {A : Set X} (hf : HolderOnWith C₁ r f A)
    (hC : C₁ ≤ C₂) : HolderOnWith C₂ r f A := by
  intro x hx y hy
  grw [← hC]
  exact hf x hx y hy

/-- If a function is `(C, r)`-Hölder and `(C, s)`-Hölder,
then it is `(C, r * t₁ + s * t₂)`-Hölder for all `t₁ t₂ : ℝ≥0` such that
`t₁ + t₂ = 1`. -/
lemma interpolate_const {C s t₁ t₂ : ℝ≥0} {A : Set X}
    (hf₁ : HolderOnWith C r f A) (hf₂ : HolderOnWith C s f A) (ht : t₁ + t₂ = 1) :
    HolderOnWith C (r * t₁ + s * t₂) f A := by
  convert hf₁.interpolate hf₂ ht
  simp [← NNReal.rpow_add_of_nonneg, ← NNReal.coe_add, ht]

variable (f) in
/-- For fixed `f : X → Y`, `A : Set X` and `C : ℝ≥0`, the set of all parameters `r : ℝ≥0` such that
`f` is `(C, r)`-Hölder on `A` is convex. -/
lemma _root_.convex_setOf_holderOnWith (C : ℝ≥0) (A : Set X) :
    Convex ℝ≥0 {r | HolderOnWith C r f A} := by
  intro r hr s hs _ _ _ _ ht
  rw [smul_eq_mul, smul_eq_mul, ← mul_comm r, ← mul_comm s]
  exact hr.interpolate_const hs ht

lemma of_le_of_le {C₁ C₂ s t : ℝ≥0} {A : Set X}
    (hf₁ : HolderOnWith C₁ r f A) (hf₂ : HolderOnWith C₂ s f A) (hrt : r ≤ t)
    (hts : t ≤ s) : HolderOnWith (max C₁ C₂) t f A := by
  replace hf₁ := hf₁.mono_const (le_max_left C₁ C₂)
  replace hf₂ := hf₂.mono_const (le_max_right C₁ C₂)
  exact convex_setOf_holderOnWith f (max C₁ C₂) A |>.segment_subset hf₁ hf₂
    (NNReal.Icc_subset_segment ⟨hrt, hts⟩)

end HolderOnWith

namespace HolderWith

variable {C r : ℝ≥0} {f : X → Y}

theorem restrict_iff {s : Set X} : HolderWith C r (s.restrict f) ↔ HolderOnWith C r f s := by
  simp [HolderWith, HolderOnWith]

protected alias ⟨_, _root_.HolderOnWith.holderWith⟩ := restrict_iff

theorem edist_le (h : HolderWith C r f) (x y : X) :
    edist (f x) (f y) ≤ (C : ℝ≥0∞) * edist x y ^ (r : ℝ) :=
  h x y

theorem edist_le_of_le (h : HolderWith C r f) {x y : X} {d : ℝ≥0∞} (hd : edist x y ≤ d) :
    edist (f x) (f y) ≤ (C : ℝ≥0∞) * d ^ (r : ℝ) :=
  (h.holderOnWith univ).edist_le_of_le trivial trivial hd

theorem comp {Cg rg : ℝ≥0} {g : Y → Z} (hg : HolderWith Cg rg g) {Cf rf : ℝ≥0} {f : X → Y}
    (hf : HolderWith Cf rf f) : HolderWith (Cg * Cf ^ (rg : ℝ)) (rg * rf) (g ∘ f) :=
  (hg.holderOnWith univ).comp_holderWith hf fun _ => trivial

theorem comp_holderOnWith {Cg rg : ℝ≥0} {g : Y → Z} (hg : HolderWith Cg rg g) {Cf rf : ℝ≥0}
    {f : X → Y} {s : Set X} (hf : HolderOnWith Cf rf f s) :
    HolderOnWith (Cg * Cf ^ (rg : ℝ)) (rg * rf) (g ∘ f) s :=
  (hg.holderOnWith univ).comp hf fun _ _ => trivial

/-- A Hölder continuous function is uniformly continuous -/
protected theorem uniformContinuous (hf : HolderWith C r f) (h0 : 0 < r) : UniformContinuous f :=
  uniformContinuousOn_univ.mp <| (hf.holderOnWith univ).uniformContinuousOn h0

protected theorem continuous (hf : HolderWith C r f) (h0 : 0 < r) : Continuous f :=
  (hf.uniformContinuous h0).continuous

theorem ediam_image_le (hf : HolderWith C r f) (s : Set X) :
    ediam (f '' s) ≤ (C : ℝ≥0∞) * ediam s ^ (r : ℝ) :=
  ediam_image_le_iff.2 fun _ hx _ hy => hf.edist_le_of_le <| edist_le_ediam_of_mem hx hy

lemma const {y : Y} :
    HolderWith C r (Function.const X y) := fun x₁ x₂ => by
  simp only [Function.const_apply, edist_self, zero_le]

lemma zero [Zero Y] : HolderWith C r (0 : X → Y) := .const

lemma of_isEmpty [IsEmpty X] : HolderWith C r f := isEmptyElim

lemma mono {C' : ℝ≥0} (hf : HolderWith C r f) (h : C ≤ C') :
    HolderWith C' r f :=
  fun x₁ x₂ ↦ (hf x₁ x₂).trans (by gcongr)

/-- If a function is `(C₁, r)`-Hölder and `(C₂, s)`-Hölder, then it is
`(C₁ ^ t₁ * C₂ ^ t₂, r * t₁ + s * t₂)`-Hölder for all `t₁ t₂ : ℝ≥0` such that
`t₁ + t₂ = 1`. -/
lemma interpolate {C₁ C₂ s t₁ t₂ : ℝ≥0}
    (hf₁ : HolderWith C₁ r f) (hf₂ : HolderWith C₂ s f) (ht : t₁ + t₂ = 1) :
    HolderWith (C₁ ^ (t₁ : ℝ) * C₂ ^ (t₂ : ℝ)) (r * t₁ + s * t₂) f :=
  holderOnWith_univ.1 ((holderOnWith_univ.2 hf₁).interpolate (holderOnWith_univ.2 hf₂) ht)

/-- If a function is Hölder over a bounded space, then it is bounded. -/
lemma holderWith_zero_of_bounded {C D : ℝ≥0}
    (h : ∀ x y : X, edist x y ≤ D) (hf : HolderWith C r f) :
    HolderWith (C * D ^ (r : ℝ)) 0 f :=
  holderOnWith_univ.1 ((holderOnWith_univ.2 hf).holderOnWith_zero_of_bounded (fun x _ y _ ↦ h x y))

/-- If a function is `r`-Hölder over a bounded space, then it is also `s`-Hölder when `s ≤ r`. -/
lemma of_le {C D s : ℝ≥0} (h : ∀ x y : X, edist x y ≤ D) (hf : HolderWith C r f) (hsr : s ≤ r) :
    HolderWith (C * D ^ (r - s : ℝ)) s f :=
  holderOnWith_univ.1 ((holderOnWith_univ.2 hf).of_le (fun x _ y _ ↦ h x y) hsr)

/-- If a function is `(C, r)`-Hölder and `(C, s)`-Hölder,
then it is `(C, r * t₁ + s * t₂)`-Hölder for all `t₁ t₂ : ℝ≥0` such that
`t₁ + t₂ = 1`. -/
lemma interpolate_const {C s t₁ t₂ : ℝ≥0}
    (hf₁ : HolderWith C r f) (hf₂ : HolderWith C s f) (ht : t₁ + t₂ = 1) :
    HolderWith C (r * t₁ + s * t₂) f :=
  holderOnWith_univ.1 ((holderOnWith_univ.2 hf₁).interpolate_const (holderOnWith_univ.2 hf₂) ht)

variable (f) in
/-- For fixed `f : X → Y` and `C : ℝ≥0`, the set of all parameters `r : ℝ≥0` such that
`f` is `(C, r)`-Hölder is convex. -/
lemma _root_.convex_setOf_holderWith (C : ℝ≥0) :
    Convex ℝ≥0 {r | HolderWith C r f} := by
  simp_rw [← holderOnWith_univ]
  exact convex_setOf_holderOnWith f C _

lemma of_le_of_le {C₁ C₂ s t : ℝ≥0}
    (hf₁ : HolderWith C₁ r f) (hf₂ : HolderWith C₂ s f) (hrt : r ≤ t)
    (hts : t ≤ s) : HolderWith (max C₁ C₂) t f :=
  holderOnWith_univ.1 ((holderOnWith_univ.2 hf₁).of_le_of_le (holderOnWith_univ.2 hf₂) hrt hts)

end HolderWith

end EMetric

section PseudoMetric

variable [PseudoMetricSpace X] [PseudoMetricSpace Y] {C r : ℝ≥0} {f : X → Y} {s : Set X} {x y : X}

namespace HolderOnWith

theorem nndist_le_of_le (hf : HolderOnWith C r f s) (hx : x ∈ s) (hy : y ∈ s)
    {d : ℝ≥0} (hd : nndist x y ≤ d) : nndist (f x) (f y) ≤ C * d ^ (r : ℝ) := by
  rw [← ENNReal.coe_le_coe, ← edist_nndist, ENNReal.coe_mul,
    ENNReal.coe_rpow_of_nonneg _ r.coe_nonneg]
  apply hf.edist_le_of_le hx hy
  rwa [edist_nndist, ENNReal.coe_le_coe]

theorem nndist_le (hf : HolderOnWith C r f s) (hx : x ∈ s) (hy : y ∈ s) :
    nndist (f x) (f y) ≤ C * nndist x y ^ (r : ℝ) :=
  hf.nndist_le_of_le hx hy le_rfl

theorem dist_le_of_le (hf : HolderOnWith C r f s) (hx : x ∈ s) (hy : y ∈ s)
    {d : ℝ} (hd : dist x y ≤ d) : dist (f x) (f y) ≤ C * d ^ (r : ℝ) := by
  lift d to ℝ≥0 using dist_nonneg.trans hd
  rw [dist_nndist] at hd ⊢
  norm_cast at hd ⊢
  exact hf.nndist_le_of_le hx hy hd

theorem dist_le (hf : HolderOnWith C r f s) (hx : x ∈ s) (hy : y ∈ s) :
    dist (f x) (f y) ≤ C * dist x y ^ (r : ℝ) :=
  hf.dist_le_of_le hx hy le_rfl

end HolderOnWith

namespace HolderWith

theorem nndist_le_of_le (hf : HolderWith C r f) {x y : X} {d : ℝ≥0} (hd : nndist x y ≤ d) :
    nndist (f x) (f y) ≤ C * d ^ (r : ℝ) :=
  (hf.holderOnWith univ).nndist_le_of_le (mem_univ x) (mem_univ y) hd

theorem nndist_le (hf : HolderWith C r f) (x y : X) :
    nndist (f x) (f y) ≤ C * nndist x y ^ (r : ℝ) :=
  hf.nndist_le_of_le le_rfl

theorem dist_le_of_le (hf : HolderWith C r f) {x y : X} {d : ℝ} (hd : dist x y ≤ d) :
    dist (f x) (f y) ≤ C * d ^ (r : ℝ) :=
  (hf.holderOnWith univ).dist_le_of_le (mem_univ x) (mem_univ y) hd

theorem dist_le (hf : HolderWith C r f) (x y : X) : dist (f x) (f y) ≤ C * dist x y ^ (r : ℝ) :=
  hf.dist_le_of_le le_rfl

end HolderWith

end PseudoMetric

section Metric

variable [PseudoMetricSpace X] [MetricSpace Y] {r : ℝ≥0} {f : X → Y}

@[simp]
lemma holderWith_zero_iff : HolderWith 0 r f ↔ ∀ x₁ x₂, f x₁ = f x₂ := by
  refine ⟨fun h x₁ x₂ => ?_, fun h x₁ x₂ => h x₁ x₂ ▸ ?_⟩
  · specialize h x₁ x₂
    simp [ENNReal.coe_zero, zero_mul, nonpos_iff_eq_zero, edist_eq_zero] at h
    assumption
  · simp only [edist_self, ENNReal.coe_zero, zero_mul, le_refl]

end Metric

section SeminormedAddCommGroup

variable [PseudoMetricSpace X] [SeminormedAddCommGroup Y] {C C' r : ℝ≥0} {f g : X → Y}

namespace HolderWith

lemma add (hf : HolderWith C r f) (hg : HolderWith C' r g) :
    HolderWith (C + C') r (f + g) := by
  intro x₁ x₂
  simp only [Pi.add_apply, ENNReal.coe_add]
  grw [edist_add_add_le, hf x₁ x₂, hg x₁ x₂]
  rw [add_mul]

lemma smul {α} [SeminormedAddCommGroup α] [SMulZeroClass α Y] [IsBoundedSMul α Y] (a : α)
    (hf : HolderWith C r f) : HolderWith (C * ‖a‖₊) r (a • f) := fun x₁ x₂ => by
  refine edist_smul_le _ _ _ |>.trans ?_
  rw [ENNReal.coe_mul, ENNReal.smul_def, smul_eq_mul, mul_comm (C : ℝ≥0∞), mul_assoc]
  gcongr
  exact hf x₁ x₂

lemma smul_iff {α} [SeminormedRing α] [Module α Y] [NormSMulClass α Y] (a : α)
    (ha : ‖a‖₊ ≠ 0) :
    HolderWith (C * ‖a‖₊) r (a • f) ↔ HolderWith C r f := by
  simp_rw [HolderWith, ENNReal.coe_mul, Pi.smul_apply, edist_smul₀, ENNReal.smul_def, smul_eq_mul,
    mul_comm (C : ℝ≥0∞), mul_assoc,
    ENNReal.mul_le_mul_iff_right (ENNReal.coe_ne_zero.mpr ha) ENNReal.coe_ne_top, mul_comm]

end HolderWith

end SeminormedAddCommGroup
