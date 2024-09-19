/-
Copyright (c) 2024 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.Topology.MetricSpace.Hoelder

/-!
# Hölder norm

This file defines the Hölder (semi-)norm for Hölder functions alongside some basic properties.
The `r`-Hölder norm of a function `f : X → Y` between two metric spaces is the least non-negative
real number `C` for which `f` is `r`-Hölder continuous with constant `C`, i.e. it is the least `C`
for which `WithHoelder C r f` is true.

## Main definitions

* `eHoelderNorm r f`: `r`-Hölder (semi-)norm in `ℝ≥0∞` of a function `f`.
* `nnHoelderNorm r f`: `r`-Hölder (semi-)norm in `ℝ≥0` of a function `f`.
* `MemHoelder r f`: Predicate for a function `f` being `r`-Hölder continuous.

## Main results

* `eHoelderNorm_eq_zero`: the Hölder norm of a function is zero if and only if it is constant.
* `MemHoelder.hoelderWith`: The Hölder norm of a Hölder function `f` is a Hölder constant of `f`.

## Tags

Hölder norm, Hoeder norm

-/

variable {X Y Z : Type*}

open Filter Set

open NNReal ENNReal Topology

section PseudoEMetricSpace

variable [PseudoEMetricSpace X] [PseudoEMetricSpace Y] {r : ℝ≥0} {f : X → Y}

/-- The `r`-Hölder (semi-)norm in `ℝ≥0∞` of a function `f` is the least non-negative real
number `C` for which `f` is `r`-Hölder continuous with constant `C`. This is `∞` if no such
non-negative real exists. -/
noncomputable
def eHoelderNorm (r : ℝ≥0) (f : X → Y) : ℝ≥0∞ := ⨅ (C) (_ : HoelderWith C r f), C

/-- The `r`-Hölder (semi)norm in `ℝ≥0`. -/
noncomputable
def nnHoelderNorm (r : ℝ≥0) (f : X → Y) : ℝ≥0 := (eHoelderNorm r f).toNNReal

/-- A function `f` is `MemHoelder r f` if it is Hölder continuous. Namely, `f` has a finite
`r`-Hölder constant. This is equivalent to `f` having finite Hölder norm.
c.f. `memHoelder_iff`. -/
def MemHoelder (r : ℝ≥0) (f : X → Y) : Prop := ∃ C, HoelderWith C r f

lemma HoelderWith.memHoelder {C : ℝ≥0} (hf : HoelderWith C r f) : MemHoelder r f := ⟨C, hf⟩

@[simp] lemma eHoelderNorm_lt_top_iff : eHoelderNorm r f < ∞ ↔ MemHoelder r f := by
  refine ⟨fun h => ?_,
    fun hf => let ⟨C, hC⟩ := hf; iInf_lt_top.2 ⟨C, iInf_lt_top.2 ⟨hC, coe_lt_top⟩⟩⟩
  simp_rw [eHoelderNorm, iInf_lt_top] at h
  exact let ⟨C, hC, _⟩ := h; ⟨C, hC⟩

lemma eHoelderNorm_ne_top_iff : eHoelderNorm r f ≠ ∞ ↔ MemHoelder r f := by
  rw [← eHoelderNorm_lt_top_iff, lt_top_iff_ne_top]

@[simp] lemma eHoelderNorm_eq_top : eHoelderNorm r f = ∞ ↔ ¬ MemHoelder r f := by
  rw [← eHoelderNorm_ne_top_iff, not_not]

protected alias ⟨_, MemHoelder.eHoelderNorm_lt_top⟩ := eHoelderNorm_lt_top_iff
protected alias ⟨_, MemHoelder.eHoelderNorm_ne_top⟩ := eHoelderNorm_ne_top_iff

variable (X) in
lemma eHoelderNorm_const (r : ℝ≥0) (c : Y) : eHoelderNorm r (Function.const X c) = 0 := by
  rw [eHoelderNorm, ← ENNReal.bot_eq_zero, iInf₂_eq_bot]
  exact fun C' hC' => ⟨0, .const, hC'⟩

variable (X) in
lemma eHoelderNorm_zero [Zero Y] (r : ℝ≥0) : eHoelderNorm r (0 : X → Y) = 0 :=
  eHoelderNorm_const X r 0

attribute [simp] eHoelderNorm_const eHoelderNorm_zero

lemma eHoelderNorm_of_isEmpty [hX : IsEmpty X] :
    eHoelderNorm r f = 0 := by
  rw [eHoelderNorm, ← ENNReal.bot_eq_zero, iInf₂_eq_bot]
  exact fun ε hε => ⟨0, .of_isEmpty, hε⟩

lemma HoelderWith.eHoelderNorm_le {C : ℝ≥0} (hf : HoelderWith C r f) :
    eHoelderNorm r f ≤ C :=
  iInf₂_le C hf

@[simp]
lemma memHoelder_const {c : Y} : MemHoelder r (Function.const X c) :=
  (HoelderWith.const (C := 0)).memHoelder

@[simp]
lemma memHoelder_zero [Zero Y] : MemHoelder r (0 : X → Y) :=
  memHoelder_const

end PseudoEMetricSpace

section MetricSpace

variable [MetricSpace X] [EMetricSpace Y]

lemma eHoelderNorm_eq_zero {r : ℝ≥0} {f : X → Y} :
    eHoelderNorm r f = 0 ↔ ∀ x₁ x₂, f x₁ = f x₂ := by
  constructor
  · refine fun h x₁ x₂ => ?_
    by_cases hx : x₁ = x₂
    · rw [hx]
    · rw [eHoelderNorm, ← ENNReal.bot_eq_zero, iInf₂_eq_bot] at h
      rw [← edist_eq_zero, ← le_zero_iff]
      refine le_of_forall_lt' fun b hb => ?_
      obtain ⟨C, hC, hC'⟩ := h (b / edist x₁ x₂ ^ (r : ℝ))
        (ENNReal.div_pos hb.ne.symm (ENNReal.rpow_lt_top_of_nonneg zero_le_coe
          (edist_lt_top x₁ x₂).ne).ne)
      exact lt_of_le_of_lt (hC x₁ x₂) <| ENNReal.mul_lt_of_lt_div hC'
  · intro h
    cases' isEmpty_or_nonempty X with hX hX
    · haveI := hX
      exact eHoelderNorm_of_isEmpty
    · rw [← eHoelderNorm_const X r (f hX.some)]
      congr
      simp [funext_iff, h _ hX.some]

lemma MemHoelder.hoelderWith {r : ℝ≥0} {f : X → Y} (hf : MemHoelder r f) :
    HoelderWith (nnHoelderNorm r f) r f := by
  intros x₁ x₂
  by_cases hx : x₁ = x₂
  · simp only [hx, edist_self, zero_le]
  rw [nnHoelderNorm, eHoelderNorm, coe_toNNReal]
  swap; exact hf.eHoelderNorm_lt_top.ne
  have h₁ : edist x₁ x₂ ^ (r : ℝ) ≠ 0 :=
    (Ne.symm <| ne_of_lt <| ENNReal.rpow_pos (edist_pos.2 hx) (edist_lt_top x₁ x₂).ne)
  have h₂ : edist x₁ x₂ ^ (r : ℝ) ≠ ∞ := by
    simp [(edist_lt_top x₁ x₂).ne]
  rw [← ENNReal.div_le_iff h₁ h₂]
  refine le_iInf₂ fun C hC => ?_
  rw [ENNReal.div_le_iff h₁ h₂]
  exact hC x₁ x₂

lemma memHoelder_iff_hoelderWith {r : ℝ≥0} {f : X → Y} :
    MemHoelder r f ↔ HoelderWith (nnHoelderNorm r f) r f :=
  ⟨MemHoelder.hoelderWith, HoelderWith.memHoelder⟩

lemma coe_nnHoelderNorm_le_eHoelderNorm {r : ℝ≥0} {f : X → Y} :
    (nnHoelderNorm r f : ℝ≥0∞) ≤ eHoelderNorm r f :=
  coe_toNNReal_le_self

lemma HoelderWith.coe_nnHoelderNorm_eq_eHoelderNorm
    {C r : ℝ≥0} {f : X → Y} (hf : HoelderWith C r f) :
    (nnHoelderNorm r f : ℝ≥0∞) = eHoelderNorm r f := by
  rw [nnHoelderNorm, coe_toNNReal]
  exact ne_of_lt <| lt_of_le_of_lt hf.eHoelderNorm_le <| coe_lt_top (r := C)

lemma MemHoelder.coe_nnHoelderNorm_eq_eHoelderNorm
    {r : ℝ≥0} {f : X → Y} (hf : MemHoelder r f) :
    (nnHoelderNorm r f : ℝ≥0∞) = eHoelderNorm r f :=
  hf.hoelderWith.coe_nnHoelderNorm_eq_eHoelderNorm

lemma HoelderWith.nnhoelderNorm_le {C r : ℝ≥0} {f : X → Y} (hf : HoelderWith C r f) :
    nnHoelderNorm r f ≤ C := by
  rw [← ENNReal.coe_le_coe, hf.coe_nnHoelderNorm_eq_eHoelderNorm]
  exact hf.eHoelderNorm_le

lemma MemHoelder.comp {r s : ℝ≥0} {Z : Type*} [MetricSpace Z] {f : Z → X} {g : X → Y}
    (hf : MemHoelder r f) (hg : MemHoelder s g) : MemHoelder (s * r) (g ∘ f) :=
  (hg.hoelderWith.comp hf.hoelderWith).memHoelder

end MetricSpace

section SeminormedAddCommGroup

variable [MetricSpace X] [NormedAddCommGroup Y]
variable {C r : ℝ≥0} {f g : X → Y}

lemma MemHoelder.add (hf : MemHoelder r f) (hg : MemHoelder r g) : MemHoelder r (f + g) :=
  (hf.hoelderWith.add hg.hoelderWith).memHoelder

lemma MemHoelder.smul {𝕜} [NormedDivisionRing 𝕜] [Module 𝕜 Y] [BoundedSMul 𝕜 Y]
    {c : 𝕜} (hf : MemHoelder r f) : MemHoelder r (c • f) :=
  (hf.hoelderWith.smul c).memHoelder

lemma eHoelderNorm_add_le :
    eHoelderNorm r (f + g) ≤ eHoelderNorm r f + eHoelderNorm r g := by
  by_cases hfg : MemHoelder r f  ∧ MemHoelder r g
  · obtain ⟨hf, hg⟩ := hfg
    rw [← hf.coe_nnHoelderNorm_eq_eHoelderNorm, ← hg.coe_nnHoelderNorm_eq_eHoelderNorm, ← coe_add]
    exact (hf.add hg).hoelderWith.eHoelderNorm_le.trans <|
      coe_le_coe.2 (hf.hoelderWith.add hg.hoelderWith).nnhoelderNorm_le
  · rw [Classical.not_and_iff_or_not_not, ← eHoelderNorm_eq_top, ← eHoelderNorm_eq_top] at hfg
    obtain (h | h) := hfg
    all_goals simp [h]

lemma eHoelderNorm_smul {α} [NormedDivisionRing α] [Module α Y] [BoundedSMul α Y] (c : α) :
    eHoelderNorm r (c • f) = ‖c‖₊ * eHoelderNorm r f := by
  by_cases hc : ‖c‖₊ = 0
  · rw [nnnorm_eq_zero] at hc
    simp [hc]
  by_cases hf : MemHoelder r f
  · refine le_antisymm ((hf.hoelderWith.smul c).eHoelderNorm_le.trans ?_) <| mul_le_of_le_div' ?_
    · rw [coe_mul, hf.coe_nnHoelderNorm_eq_eHoelderNorm, mul_comm]
    · rw [← (hf.hoelderWith.smul c).coe_nnHoelderNorm_eq_eHoelderNorm, ← coe_div hc]
      refine HoelderWith.eHoelderNorm_le fun x₁ x₂ => ?_
      rw [coe_div hc, ← ENNReal.mul_div_right_comm,
        ENNReal.le_div_iff_mul_le (Or.inl <| coe_ne_zero.2 hc) <| Or.inl coe_ne_top,
        mul_comm, ← smul_eq_mul, ← ENNReal.smul_def, ← edist_smul₀, ← Pi.smul_apply,
        ← Pi.smul_apply]
      exact hf.smul.hoelderWith x₁ x₂
  · rw [← eHoelderNorm_eq_top] at hf
    rw [hf, mul_top <| coe_ne_zero.2 hc, eHoelderNorm_eq_top]
    rw [nnnorm_eq_zero] at hc
    intro h
    have := h.smul (c := c⁻¹)
    rw [inv_smul_smul₀ hc] at this
    exact this.eHoelderNorm_lt_top.ne hf

lemma eHoelderNorm_nsmul [Module ℝ Y] [BoundedSMul ℝ Y] (n : ℕ) :
    eHoelderNorm r (n • f) = n • eHoelderNorm r f := by
  simp [← Nat.cast_smul_eq_nsmul (R := ℝ), eHoelderNorm_smul]

end SeminormedAddCommGroup
