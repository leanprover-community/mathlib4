/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne, David Loeffler
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Continuity of power functions

This file contains lemmas about continuity of the power functions on `ℂ`, `ℝ`, `ℝ≥0`, and `ℝ≥0∞`.
-/


noncomputable section

open Real Topology NNReal ENNReal Filter ComplexConjugate Finset Set

section CpowLimits

/-!
## Continuity for complex powers
-/


open Complex

variable {α : Type*}

theorem zero_cpow_eq_nhds {b : ℂ} (hb : b ≠ 0) : (fun x : ℂ => (0 : ℂ) ^ x) =ᶠ[𝓝 b] 0 := by
  suffices ∀ᶠ x : ℂ in 𝓝 b, x ≠ 0 from
    this.mono fun x hx ↦ by
      dsimp only
      rw [zero_cpow hx, Pi.zero_apply]
  exact IsOpen.eventually_mem isOpen_ne hb

theorem cpow_eq_nhds {a b : ℂ} (ha : a ≠ 0) :
    (fun x => x ^ b) =ᶠ[𝓝 a] fun x => exp (log x * b) := by
  suffices ∀ᶠ x : ℂ in 𝓝 a, x ≠ 0 from
    this.mono fun x hx ↦ by
      dsimp only
      rw [cpow_def_of_ne_zero hx]
  exact IsOpen.eventually_mem isOpen_ne ha

theorem cpow_eq_nhds' {p : ℂ × ℂ} (hp_fst : p.fst ≠ 0) :
    (fun x => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) := by
  suffices ∀ᶠ x : ℂ × ℂ in 𝓝 p, x.1 ≠ 0 from
    this.mono fun x hx ↦ by
      dsimp only
      rw [cpow_def_of_ne_zero hx]
  refine IsOpen.eventually_mem ?_ hp_fst
  change IsOpen { x : ℂ × ℂ | x.1 = 0 }ᶜ
  rw [isOpen_compl_iff]
  exact isClosed_eq continuous_fst continuous_const

-- Continuity of `fun x => a ^ x`: union of these two lemmas is optimal.
theorem continuousAt_const_cpow {a b : ℂ} (ha : a ≠ 0) : ContinuousAt (fun x : ℂ => a ^ x) b := by
  have cpow_eq : (fun x : ℂ => a ^ x) = fun x => exp (log a * x) := by
    ext1 b
    rw [cpow_def_of_ne_zero ha]
  rw [cpow_eq]
  exact continuous_exp.continuousAt.comp (ContinuousAt.mul continuousAt_const continuousAt_id)

theorem continuousAt_const_cpow' {a b : ℂ} (h : b ≠ 0) : ContinuousAt (fun x : ℂ => a ^ x) b := by
  by_cases ha : a = 0
  · rw [ha, continuousAt_congr (zero_cpow_eq_nhds h)]
    exact continuousAt_const
  · exact continuousAt_const_cpow ha

/-- The function `z ^ w` is continuous in `(z, w)` provided that `z` does not belong to the interval
`(-∞, 0]` on the real line. See also `Complex.continuousAt_cpow_zero_of_re_pos` for a version that
works for `z = 0` but assumes `0 < re w`. -/
theorem continuousAt_cpow {p : ℂ × ℂ} (hp_fst : p.fst ∈ slitPlane) :
    ContinuousAt (fun x : ℂ × ℂ => x.1 ^ x.2) p := by
  rw [continuousAt_congr (cpow_eq_nhds' <| slitPlane_ne_zero hp_fst)]
  refine continuous_exp.continuousAt.comp ?_
  exact
    ContinuousAt.mul
      (ContinuousAt.comp (continuousAt_clog hp_fst) continuous_fst.continuousAt)
      continuous_snd.continuousAt

theorem continuousAt_cpow_const {a b : ℂ} (ha : a ∈ slitPlane) :
    ContinuousAt (· ^ b) a :=
  Tendsto.comp (@continuousAt_cpow (a, b) ha) (continuousAt_id.prodMk continuousAt_const)

theorem Filter.Tendsto.cpow {l : Filter α} {f g : α → ℂ} {a b : ℂ} (hf : Tendsto f l (𝓝 a))
    (hg : Tendsto g l (𝓝 b)) (ha : a ∈ slitPlane) :
    Tendsto (fun x => f x ^ g x) l (𝓝 (a ^ b)) :=
  (@continuousAt_cpow (a, b) ha).tendsto.comp (hf.prodMk_nhds hg)

theorem Filter.Tendsto.const_cpow {l : Filter α} {f : α → ℂ} {a b : ℂ} (hf : Tendsto f l (𝓝 b))
    (h : a ≠ 0 ∨ b ≠ 0) : Tendsto (fun x => a ^ f x) l (𝓝 (a ^ b)) := by
  cases h with
  | inl h => exact (continuousAt_const_cpow h).tendsto.comp hf
  | inr h => exact (continuousAt_const_cpow' h).tendsto.comp hf

variable [TopologicalSpace α] {f g : α → ℂ} {s : Set α} {a : α}

nonrec theorem ContinuousWithinAt.cpow (hf : ContinuousWithinAt f s a)
    (hg : ContinuousWithinAt g s a) (h0 : f a ∈ slitPlane) :
    ContinuousWithinAt (fun x => f x ^ g x) s a :=
  hf.cpow hg h0

nonrec theorem ContinuousWithinAt.const_cpow {b : ℂ} (hf : ContinuousWithinAt f s a)
    (h : b ≠ 0 ∨ f a ≠ 0) : ContinuousWithinAt (fun x => b ^ f x) s a :=
  hf.const_cpow h

nonrec theorem ContinuousAt.cpow (hf : ContinuousAt f a) (hg : ContinuousAt g a)
    (h0 : f a ∈ slitPlane) : ContinuousAt (fun x => f x ^ g x) a :=
  hf.cpow hg h0

nonrec theorem ContinuousAt.const_cpow {b : ℂ} (hf : ContinuousAt f a) (h : b ≠ 0 ∨ f a ≠ 0) :
    ContinuousAt (fun x => b ^ f x) a :=
  hf.const_cpow h

theorem ContinuousOn.cpow (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (h0 : ∀ a ∈ s, f a ∈ slitPlane) : ContinuousOn (fun x => f x ^ g x) s := fun a ha =>
  (hf a ha).cpow (hg a ha) (h0 a ha)

theorem ContinuousOn.const_cpow {b : ℂ} (hf : ContinuousOn f s) (h : b ≠ 0 ∨ ∀ a ∈ s, f a ≠ 0) :
    ContinuousOn (fun x => b ^ f x) s := fun a ha => (hf a ha).const_cpow (h.imp id fun h => h a ha)

theorem Continuous.cpow (hf : Continuous f) (hg : Continuous g)
    (h0 : ∀ a, f a ∈ slitPlane) : Continuous fun x => f x ^ g x :=
  continuous_iff_continuousAt.2 fun a => hf.continuousAt.cpow hg.continuousAt (h0 a)

theorem Continuous.const_cpow {b : ℂ} (hf : Continuous f) (h : b ≠ 0 ∨ ∀ a, f a ≠ 0) :
    Continuous fun x => b ^ f x :=
  continuous_iff_continuousAt.2 fun a => hf.continuousAt.const_cpow <| h.imp id fun h => h a

theorem ContinuousOn.cpow_const {b : ℂ} (hf : ContinuousOn f s)
    (h : ∀ a : α, a ∈ s → f a ∈ slitPlane) : ContinuousOn (fun x => f x ^ b) s :=
  hf.cpow continuousOn_const h

@[fun_prop]
lemma continuous_const_cpow (z : ℂ) [NeZero z] : Continuous fun s : ℂ ↦ z ^ s :=
  continuous_id.const_cpow (.inl <| NeZero.ne z)

end CpowLimits

section RpowLimits

/-!
## Continuity for real powers
-/


namespace Real

theorem continuousAt_const_rpow {a b : ℝ} (h : a ≠ 0) : ContinuousAt (a ^ ·) b := by
  simp only [rpow_def]
  refine Complex.continuous_re.continuousAt.comp ?_
  refine (continuousAt_const_cpow ?_).comp Complex.continuous_ofReal.continuousAt
  norm_cast

theorem continuousAt_const_rpow' {a b : ℝ} (h : b ≠ 0) : ContinuousAt (a ^ ·) b := by
  simp only [rpow_def]
  refine Complex.continuous_re.continuousAt.comp ?_
  refine (continuousAt_const_cpow' ?_).comp Complex.continuous_ofReal.continuousAt
  norm_cast

theorem rpow_eq_nhds_of_neg {p : ℝ × ℝ} (hp_fst : p.fst < 0) :
    (fun x : ℝ × ℝ => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) * cos (x.2 * π) := by
  suffices ∀ᶠ x : ℝ × ℝ in 𝓝 p, x.1 < 0 from
    this.mono fun x hx ↦ by
      dsimp only
      rw [rpow_def_of_neg hx]
  exact IsOpen.eventually_mem (isOpen_lt continuous_fst continuous_const) hp_fst

theorem rpow_eq_nhds_of_pos {p : ℝ × ℝ} (hp_fst : 0 < p.fst) :
    (fun x : ℝ × ℝ => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) := by
  suffices ∀ᶠ x : ℝ × ℝ in 𝓝 p, 0 < x.1 from
    this.mono fun x hx ↦ by
      dsimp only
      rw [rpow_def_of_pos hx]
  exact IsOpen.eventually_mem (isOpen_lt continuous_const continuous_fst) hp_fst

theorem continuousAt_rpow_of_ne (p : ℝ × ℝ) (hp : p.1 ≠ 0) :
    ContinuousAt (fun p : ℝ × ℝ => p.1 ^ p.2) p := by
  rw [ne_iff_lt_or_gt] at hp
  cases hp with
  | inl hp =>
    rw [continuousAt_congr (rpow_eq_nhds_of_neg hp)]
    refine ContinuousAt.mul ?_ (continuous_cos.continuousAt.comp ?_)
    · refine continuous_exp.continuousAt.comp (ContinuousAt.mul ?_ continuous_snd.continuousAt)
      refine (continuousAt_log ?_).comp continuous_fst.continuousAt
      exact hp.ne
    · exact continuous_snd.continuousAt.mul continuousAt_const
  | inr hp =>
    rw [continuousAt_congr (rpow_eq_nhds_of_pos hp)]
    refine continuous_exp.continuousAt.comp (ContinuousAt.mul ?_ continuous_snd.continuousAt)
    refine (continuousAt_log ?_).comp continuous_fst.continuousAt
    exact hp.ne'

theorem continuousAt_rpow_of_pos (p : ℝ × ℝ) (hp : 0 < p.2) :
    ContinuousAt (fun p : ℝ × ℝ => p.1 ^ p.2) p := by
  obtain ⟨x, y⟩ := p
  dsimp only at hp
  obtain hx | rfl := ne_or_eq x 0
  · exact continuousAt_rpow_of_ne (x, y) hx
  have A : Tendsto (fun p : ℝ × ℝ => exp (log p.1 * p.2)) (𝓝[≠] 0 ×ˢ 𝓝 y) (𝓝 0) :=
    tendsto_exp_atBot.comp
      ((tendsto_log_nhdsNE_zero.comp tendsto_fst).atBot_mul_pos hp tendsto_snd)
  have B : Tendsto (fun p : ℝ × ℝ => p.1 ^ p.2) (𝓝[≠] 0 ×ˢ 𝓝 y) (𝓝 0) :=
    squeeze_zero_norm (fun p => abs_rpow_le_exp_log_mul p.1 p.2) A
  have C : Tendsto (fun p : ℝ × ℝ => p.1 ^ p.2) (𝓝[{0}] 0 ×ˢ 𝓝 y) (pure 0) := by
    rw [nhdsWithin_singleton, tendsto_pure, pure_prod, eventually_map]
    exact (lt_mem_nhds hp).mono fun y hy => zero_rpow hy.ne'
  simpa only [← sup_prod, ← nhdsWithin_union, compl_union_self, nhdsWithin_univ, nhds_prod_eq,
    ContinuousAt, zero_rpow hp.ne'] using B.sup (C.mono_right (pure_le_nhds _))

theorem continuousAt_rpow (p : ℝ × ℝ) (h : p.1 ≠ 0 ∨ 0 < p.2) :
    ContinuousAt (fun p : ℝ × ℝ => p.1 ^ p.2) p :=
  h.elim (fun h => continuousAt_rpow_of_ne p h) fun h => continuousAt_rpow_of_pos p h

@[fun_prop]
theorem continuousAt_rpow_const (x : ℝ) (q : ℝ) (h : x ≠ 0 ∨ 0 ≤ q) :
    ContinuousAt (fun x : ℝ => x ^ q) x := by
  rw [le_iff_lt_or_eq, ← or_assoc] at h
  obtain h|rfl := h
  · exact (continuousAt_rpow (x, q) h).comp₂ continuousAt_id continuousAt_const
  · simp_rw [rpow_zero]; exact continuousAt_const

@[fun_prop]
theorem continuous_rpow_const {q : ℝ} (h : 0 ≤ q) : Continuous (fun x : ℝ => x ^ q) :=
  continuous_iff_continuousAt.mpr fun x ↦ continuousAt_rpow_const x q (.inr h)

@[fun_prop]
lemma continuous_const_rpow {a : ℝ} (h : a ≠ 0) : Continuous (fun x : ℝ ↦ a ^ x) :=
  continuous_iff_continuousAt.mpr fun _ ↦ continuousAt_const_rpow h

end Real

section

variable {α : Type*}

theorem Filter.Tendsto.rpow {l : Filter α} {f g : α → ℝ} {x y : ℝ} (hf : Tendsto f l (𝓝 x))
    (hg : Tendsto g l (𝓝 y)) (h : x ≠ 0 ∨ 0 < y) : Tendsto (fun t => f t ^ g t) l (𝓝 (x ^ y)) :=
  (Real.continuousAt_rpow (x, y) h).tendsto.comp (hf.prodMk_nhds hg)

theorem Filter.Tendsto.rpow_const {l : Filter α} {f : α → ℝ} {x p : ℝ} (hf : Tendsto f l (𝓝 x))
    (h : x ≠ 0 ∨ 0 ≤ p) : Tendsto (fun a => f a ^ p) l (𝓝 (x ^ p)) :=
  if h0 : 0 = p then h0 ▸ by simp [tendsto_const_nhds]
  else hf.rpow tendsto_const_nhds (h.imp id fun h' => h'.lt_of_ne h0)

variable [TopologicalSpace α] {f g : α → ℝ} {s : Set α} {x : α} {p : ℝ}

nonrec theorem ContinuousAt.rpow (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (h : f x ≠ 0 ∨ 0 < g x) : ContinuousAt (fun t => f t ^ g t) x :=
  hf.rpow hg h

nonrec theorem ContinuousWithinAt.rpow (hf : ContinuousWithinAt f s x)
    (hg : ContinuousWithinAt g s x) (h : f x ≠ 0 ∨ 0 < g x) :
    ContinuousWithinAt (fun t => f t ^ g t) s x :=
  hf.rpow hg h

theorem ContinuousOn.rpow (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (h : ∀ x ∈ s, f x ≠ 0 ∨ 0 < g x) : ContinuousOn (fun t => f t ^ g t) s := fun t ht =>
  (hf t ht).rpow (hg t ht) (h t ht)

theorem Continuous.rpow (hf : Continuous f) (hg : Continuous g) (h : ∀ x, f x ≠ 0 ∨ 0 < g x) :
    Continuous fun x => f x ^ g x :=
  continuous_iff_continuousAt.2 fun x => hf.continuousAt.rpow hg.continuousAt (h x)

nonrec theorem ContinuousWithinAt.rpow_const (hf : ContinuousWithinAt f s x) (h : f x ≠ 0 ∨ 0 ≤ p) :
    ContinuousWithinAt (fun x => f x ^ p) s x :=
  hf.rpow_const h

nonrec theorem ContinuousAt.rpow_const (hf : ContinuousAt f x) (h : f x ≠ 0 ∨ 0 ≤ p) :
    ContinuousAt (fun x => f x ^ p) x :=
  hf.rpow_const h

theorem ContinuousOn.rpow_const (hf : ContinuousOn f s) (h : ∀ x ∈ s, f x ≠ 0 ∨ 0 ≤ p) :
    ContinuousOn (fun x => f x ^ p) s := fun x hx => (hf x hx).rpow_const (h x hx)

theorem Continuous.rpow_const (hf : Continuous f) (h : ∀ x, f x ≠ 0 ∨ 0 ≤ p) :
    Continuous fun x => f x ^ p :=
  continuous_iff_continuousAt.2 fun x => hf.continuousAt.rpow_const (h x)

end

end RpowLimits

/-! ## Continuity results for `cpow`, part II

These results involve relating real and complex powers, so cannot be done higher up.
-/


section CpowLimits2

namespace Complex

/-- See also `continuousAt_cpow` and `Complex.continuousAt_cpow_of_re_pos`. -/
theorem continuousAt_cpow_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    ContinuousAt (fun x : ℂ × ℂ => x.1 ^ x.2) (0, z) := by
  have hz₀ : z ≠ 0 := ne_of_apply_ne re hz.ne'
  rw [ContinuousAt, zero_cpow hz₀, tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun _ => norm_cpow_le _ _) ?_
  simp only [div_eq_mul_inv, ← Real.exp_neg]
  refine Tendsto.zero_mul_isBoundedUnder_le ?_ ?_
  · convert
        (continuous_fst.norm.tendsto ((0 : ℂ), z)).rpow
          ((continuous_re.comp continuous_snd).tendsto _) _ <;>
      simp [hz, Real.zero_rpow hz.ne']
  · simp only [Function.comp_def, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rcases exists_gt |im z| with ⟨C, hC⟩
    refine ⟨Real.exp (π * C), eventually_map.2 ?_⟩
    refine
      (((continuous_im.comp continuous_snd).abs.tendsto (_, z)).eventually (gt_mem_nhds hC)).mono
        fun z hz => Real.exp_le_exp.2 <| (neg_le_abs _).trans ?_
    rw [_root_.abs_mul]
    exact
      mul_le_mul (abs_le.2 ⟨(neg_pi_lt_arg _).le, arg_le_pi _⟩) hz.le (_root_.abs_nonneg _)
        Real.pi_pos.le

open ComplexOrder in
/-- See also `continuousAt_cpow` for a version that assumes `p.1 ≠ 0` but makes no
assumptions about `p.2`. -/
theorem continuousAt_cpow_of_re_pos {p : ℂ × ℂ} (h₁ : 0 ≤ p.1.re ∨ p.1.im ≠ 0) (h₂ : 0 < p.2.re) :
    ContinuousAt (fun x : ℂ × ℂ => x.1 ^ x.2) p := by
  obtain ⟨z, w⟩ := p
  rw [← not_lt_zero_iff, lt_iff_le_and_ne, not_and_or, Ne, Classical.not_not,
    not_le_zero_iff] at h₁
  rcases h₁ with (h₁ | (rfl : z = 0))
  exacts [continuousAt_cpow h₁, continuousAt_cpow_zero_of_re_pos h₂]

/-- See also `continuousAt_cpow_const` for a version that assumes `z ≠ 0` but makes no
assumptions about `w`. -/
theorem continuousAt_cpow_const_of_re_pos {z w : ℂ} (hz : 0 ≤ re z ∨ im z ≠ 0) (hw : 0 < re w) :
    ContinuousAt (fun x => x ^ w) z :=
  Tendsto.comp (@continuousAt_cpow_of_re_pos (z, w) hz hw)
    (continuousAt_id.prodMk continuousAt_const)

/-- Continuity of `(x, y) ↦ x ^ y` as a function on `ℝ × ℂ`. -/
theorem continuousAt_ofReal_cpow (x : ℝ) (y : ℂ) (h : 0 < y.re ∨ x ≠ 0) :
    ContinuousAt (fun p => (p.1 : ℂ) ^ p.2 : ℝ × ℂ → ℂ) (x, y) := by
  rcases lt_trichotomy (0 : ℝ) x with (hx | rfl | hx)
  · -- x > 0 : easy case
    have : ContinuousAt (fun p => ⟨↑p.1, p.2⟩ : ℝ × ℂ → ℂ × ℂ) (x, y) := by fun_prop
    refine (continuousAt_cpow (Or.inl ?_)).comp this
    rwa [ofReal_re]
  · -- x = 0 : reduce to continuousAt_cpow_zero_of_re_pos
    have A : ContinuousAt (fun p => p.1 ^ p.2 : ℂ × ℂ → ℂ) ⟨↑(0 : ℝ), y⟩ := by
      rw [ofReal_zero]
      apply continuousAt_cpow_zero_of_re_pos
      tauto
    have B : ContinuousAt (fun p => ⟨↑p.1, p.2⟩ : ℝ × ℂ → ℂ × ℂ) ⟨0, y⟩ := by fun_prop
    exact A.comp_of_eq B rfl
  · -- x < 0 : difficult case
    suffices ContinuousAt (fun p => (-(p.1 : ℂ)) ^ p.2 * exp (π * I * p.2) : ℝ × ℂ → ℂ) (x, y) by
      refine this.congr (eventually_of_mem (prod_mem_nhds (Iio_mem_nhds hx) univ_mem) ?_)
      exact fun p hp => (ofReal_cpow_of_nonpos (le_of_lt hp.1) p.2).symm
    have A : ContinuousAt (fun p => ⟨-↑p.1, p.2⟩ : ℝ × ℂ → ℂ × ℂ) (x, y) := by fun_prop
    apply ContinuousAt.mul
    · refine (continuousAt_cpow (Or.inl ?_)).comp A
      rwa [neg_re, ofReal_re, neg_pos]
    · exact (continuous_exp.comp (continuous_const.mul continuous_snd)).continuousAt

theorem continuousAt_ofReal_cpow_const (x : ℝ) (y : ℂ) (h : 0 < y.re ∨ x ≠ 0) :
    ContinuousAt (fun a => (a : ℂ) ^ y : ℝ → ℂ) x :=
  (continuousAt_ofReal_cpow x y h).comp₂_of_eq (by fun_prop) (by fun_prop) rfl

theorem continuous_ofReal_cpow_const {y : ℂ} (hs : 0 < y.re) :
    Continuous (fun x => (x : ℂ) ^ y : ℝ → ℂ) :=
  continuous_iff_continuousAt.mpr fun x => continuousAt_ofReal_cpow_const x y (Or.inl hs)

end Complex

end CpowLimits2

/-! ## Limits and continuity for `ℝ≥0` powers -/


namespace NNReal

theorem continuousAt_rpow {x : ℝ≥0} {y : ℝ} (h : x ≠ 0 ∨ 0 < y) :
    ContinuousAt (fun p : ℝ≥0 × ℝ => p.1 ^ p.2) (x, y) := by
  have :
    (fun p : ℝ≥0 × ℝ => p.1 ^ p.2) =
      Real.toNNReal ∘ (fun p : ℝ × ℝ => p.1 ^ p.2) ∘ fun p : ℝ≥0 × ℝ => (p.1.1, p.2) := by
    ext p
    simp only [coe_rpow, val_eq_coe, Function.comp_apply, coe_toNNReal', left_eq_sup]
    exact_mod_cast zero_le (p.1 ^ p.2)
  rw [this]
  refine continuous_real_toNNReal.continuousAt.comp (ContinuousAt.comp ?_ ?_)
  · apply Real.continuousAt_rpow
    simpa using h
  · fun_prop

theorem eventually_pow_one_div_le (x : ℝ≥0) {y : ℝ≥0} (hy : 1 < y) :
    ∀ᶠ n : ℕ in atTop, x ^ (1 / n : ℝ) ≤ y := by
  obtain ⟨m, hm⟩ := add_one_pow_unbounded_of_pos x (tsub_pos_of_lt hy)
  rw [tsub_add_cancel_of_le hy.le] at hm
  refine eventually_atTop.2 ⟨m + 1, fun n hn => ?_⟩
  simp only [one_div]
  simpa only [NNReal.rpow_inv_le_iff (Nat.cast_pos.2 <| m.succ_pos.trans_le hn),
    NNReal.rpow_natCast] using hm.le.trans (pow_right_mono₀ hy.le (m.le_succ.trans hn))

end NNReal

open Filter

theorem Filter.Tendsto.nnrpow {α : Type*} {f : Filter α} {u : α → ℝ≥0} {v : α → ℝ} {x : ℝ≥0}
    {y : ℝ} (hx : Tendsto u f (𝓝 x)) (hy : Tendsto v f (𝓝 y)) (h : x ≠ 0 ∨ 0 < y) :
    Tendsto (fun a => u a ^ v a) f (𝓝 (x ^ y)) :=
  Tendsto.comp (NNReal.continuousAt_rpow h) (hx.prodMk_nhds hy)

namespace NNReal

theorem continuousAt_rpow_const {x : ℝ≥0} {y : ℝ} (h : x ≠ 0 ∨ 0 ≤ y) :
    ContinuousAt (fun z => z ^ y) x :=
  h.elim (fun h => tendsto_id.nnrpow tendsto_const_nhds (Or.inl h)) fun h =>
    h.eq_or_lt.elim (fun h => h ▸ by simp only [rpow_zero, continuousAt_const]) fun h =>
      tendsto_id.nnrpow tendsto_const_nhds (Or.inr h)

@[fun_prop]
theorem continuous_rpow_const {y : ℝ} (h : 0 ≤ y) : Continuous fun x : ℝ≥0 => x ^ y :=
  continuous_iff_continuousAt.2 fun _ => continuousAt_rpow_const (Or.inr h)

@[fun_prop]
theorem continuousOn_rpow_const_compl_zero {r : ℝ} :
    ContinuousOn (fun z : ℝ≥0 => z ^ r) {0}ᶜ :=
  fun _ h => ContinuousAt.continuousWithinAt <| NNReal.continuousAt_rpow_const (.inl h)

-- even though this follows from `ContinuousOn.mono` and the previous lemma, we include it for
-- automation purposes with `fun_prop`, because the side goal `0 ∉ s ∨ 0 ≤ r` is often easy to check
@[fun_prop]
theorem continuousOn_rpow_const {r : ℝ} {s : Set ℝ≥0}
    (h : 0 ∉ s ∨ 0 ≤ r) : ContinuousOn (fun z : ℝ≥0 => z ^ r) s :=
  h.elim (fun _ ↦ ContinuousOn.mono (s := {0}ᶜ) (by fun_prop) (by aesop))
    (NNReal.continuous_rpow_const · |>.continuousOn)

end NNReal

/-! ## Continuity for `ℝ≥0∞` powers -/


namespace ENNReal

theorem eventually_pow_one_div_le {x : ℝ≥0∞} (hx : x ≠ ∞) {y : ℝ≥0∞} (hy : 1 < y) :
    ∀ᶠ n : ℕ in atTop, x ^ (1 / n : ℝ) ≤ y := by
  lift x to ℝ≥0 using hx
  by_cases h : y = ∞
  · exact Eventually.of_forall fun n => h.symm ▸ le_top
  · lift y to ℝ≥0 using h
    have := NNReal.eventually_pow_one_div_le x (mod_cast hy : 1 < y)
    refine this.congr (Eventually.of_forall fun n => ?_)
    rw [← coe_rpow_of_nonneg x (by positivity : 0 ≤ (1 / n : ℝ)), coe_le_coe]

private theorem continuousAt_rpow_const_of_pos {x : ℝ≥0∞} {y : ℝ} (h : 0 < y) :
    ContinuousAt (fun a : ℝ≥0∞ => a ^ y) x := by
  by_cases hx : x = ⊤
  · rw [hx, ContinuousAt]
    convert ENNReal.tendsto_rpow_at_top h
    simp [h]
  lift x to ℝ≥0 using hx
  rw [continuousAt_coe_iff]
  convert continuous_coe.continuousAt.comp (NNReal.continuousAt_rpow_const (Or.inr h.le)) using 1
  ext1 x
  simp [← coe_rpow_of_nonneg _ h.le]

@[continuity, fun_prop]
theorem continuous_rpow_const {y : ℝ} : Continuous fun a : ℝ≥0∞ => a ^ y := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  rcases lt_trichotomy (0 : ℝ) y with (hy | rfl | hy)
  · exact continuousAt_rpow_const_of_pos hy
  · simp only [rpow_zero]
    exact continuousAt_const
  · obtain ⟨z, hz⟩ : ∃ z, y = -z := ⟨-y, (neg_neg _).symm⟩
    have z_pos : 0 < z := by simpa [hz] using hy
    simp_rw [hz, rpow_neg]
    exact continuous_inv.continuousAt.comp (continuousAt_rpow_const_of_pos z_pos)

theorem tendsto_const_mul_rpow_nhds_zero_of_pos {c : ℝ≥0∞} (hc : c ≠ ∞) {y : ℝ} (hy : 0 < y) :
    Tendsto (fun x : ℝ≥0∞ => c * x ^ y) (𝓝 0) (𝓝 0) := by
  convert ENNReal.Tendsto.const_mul (ENNReal.continuous_rpow_const.tendsto 0) _
  · simp [hy]
  · exact Or.inr hc

end ENNReal

theorem Filter.Tendsto.ennrpow_const {α : Type*} {f : Filter α} {m : α → ℝ≥0∞} {a : ℝ≥0∞} (r : ℝ)
    (hm : Tendsto m f (𝓝 a)) : Tendsto (fun x => m x ^ r) f (𝓝 (a ^ r)) :=
  (ENNReal.continuous_rpow_const.tendsto a).comp hm
