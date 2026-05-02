/-
Copyright (c) 2024 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Topology.MetricSpace.Holder

/-!
# Hölder norm

This file defines the Hölder (semi-)norm for Hölder functions alongside some basic properties.
The `r`-Hölder norm of a function `f : X → Y` between two metric spaces is the least non-negative
real number `C` for which `f` is `r`-Hölder continuous with constant `C`, i.e. it is the least `C`
for which `WithHolder C r f` is true.

## Main definitions

* `eHolderNorm r f`: `r`-Hölder (semi-)norm in `ℝ≥0∞` of a function `f`.
* `nnHolderNorm r f`: `r`-Hölder (semi-)norm in `ℝ≥0` of a function `f`.
* `MemHolder r f`: Predicate for a function `f` being `r`-Hölder continuous.

## Main results

* `eHolderNorm_eq_zero`: the Hölder norm of a function is zero if and only if it is constant.
* `MemHolder.holderWith`: The Hölder norm of a Hölder function `f` is a Hölder constant of `f`.

## Tags

Hölder norm, Hoelder norm, Holder norm

-/

@[expose] public section

variable {X Y : Type*}

open Filter Set

open NNReal ENNReal Topology

section PseudoEMetricSpace

variable [PseudoEMetricSpace X] [PseudoEMetricSpace Y] {r : ℝ≥0} {f : X → Y}

/-- The `r`-Hölder (semi-)norm in `ℝ≥0∞` of a function `f` is the least non-negative real
number `C` for which `f` is `r`-Hölder continuous with constant `C`. This is `∞` if no such
non-negative real exists. -/
noncomputable
def eHolderNorm (r : ℝ≥0) (f : X → Y) : ℝ≥0∞ := ⨅ (C) (_ : HolderWith C r f), C

/-- The `r`-Hölder (semi)norm in `ℝ≥0`. -/
noncomputable
def nnHolderNorm (r : ℝ≥0) (f : X → Y) : ℝ≥0 := (eHolderNorm r f).toNNReal

/-- A function `f` is `MemHolder r f` if it is Hölder continuous. Namely, `f` has a finite
`r`-Hölder constant. This is equivalent to `f` having finite Hölder norm.
c.f. `memHolder_iff`. -/
def MemHolder (r : ℝ≥0) (f : X → Y) : Prop := ∃ C, HolderWith C r f

lemma HolderWith.memHolder {C : ℝ≥0} (hf : HolderWith C r f) : MemHolder r f := ⟨C, hf⟩

@[simp] lemma eHolderNorm_lt_top : eHolderNorm r f < ∞ ↔ MemHolder r f := by
  refine ⟨fun h => ?_,
    fun hf => let ⟨C, hC⟩ := hf; iInf_lt_top.2 ⟨C, iInf_lt_top.2 ⟨hC, coe_lt_top⟩⟩⟩
  simp_rw [eHolderNorm, iInf_lt_top] at h
  let ⟨C, hC, _⟩ := h
  exact ⟨C, hC⟩

lemma eHolderNorm_ne_top : eHolderNorm r f ≠ ∞ ↔ MemHolder r f := by
  rw [← eHolderNorm_lt_top, lt_top_iff_ne_top]

@[simp] lemma eHolderNorm_eq_top : eHolderNorm r f = ∞ ↔ ¬ MemHolder r f := by
  rw [← eHolderNorm_ne_top, not_not]

protected alias ⟨_, MemHolder.eHolderNorm_lt_top⟩ := eHolderNorm_lt_top
protected alias ⟨_, MemHolder.eHolderNorm_ne_top⟩ := eHolderNorm_ne_top

lemma coe_nnHolderNorm_le_eHolderNorm {r : ℝ≥0} {f : X → Y} :
    (nnHolderNorm r f : ℝ≥0∞) ≤ eHolderNorm r f :=
  coe_toNNReal_le_self

variable (X) in
@[simp]
lemma eHolderNorm_const (r : ℝ≥0) (c : Y) : eHolderNorm r (Function.const X c) = 0 := by
  rw [eHolderNorm, ← ENNReal.bot_eq_zero, iInf₂_eq_bot]
  exact fun C' hC' => ⟨0, .const, hC'⟩

variable (X) in
@[simp]
lemma eHolderNorm_zero [Zero Y] (r : ℝ≥0) : eHolderNorm r (0 : X → Y) = 0 :=
  eHolderNorm_const X r 0

variable (X) in
@[simp]
lemma nnHolderNorm_const (r : ℝ≥0) (c : Y) : nnHolderNorm r (Function.const X c) = 0 := by
  rw [← nonpos_iff_eq_zero, ← ENNReal.coe_le_coe, ENNReal.coe_zero, ← eHolderNorm_const X r c]
  exact coe_nnHolderNorm_le_eHolderNorm

variable (X) in
@[simp]
lemma nnHolderNorm_zero [Zero Y] (r : ℝ≥0) : nnHolderNorm r (0 : X → Y) = 0 :=
  nnHolderNorm_const X r 0

attribute [simp] eHolderNorm_const eHolderNorm_zero

lemma eHolderNorm_of_isEmpty [hX : IsEmpty X] :
    eHolderNorm r f = 0 := by
  rw [eHolderNorm, ← ENNReal.bot_eq_zero, iInf₂_eq_bot]
  exact fun ε hε => ⟨0, .of_isEmpty, hε⟩

lemma HolderWith.eHolderNorm_le {C : ℝ≥0} (hf : HolderWith C r f) :
    eHolderNorm r f ≤ C :=
  iInf₂_le C hf

/-- See also `memHolder_const` for the version with the spelling `fun _ ↦ c`. -/
@[simp]
lemma memHolder_const {c : Y} : MemHolder r (Function.const X c) :=
  (HolderWith.const (C := 0)).memHolder

/-- Version of `memHolder_const` with the spelling `fun _ ↦ c` for the constant function. -/
@[simp]
lemma memHolder_const' {c : Y} : MemHolder r (fun _ ↦ c : X → Y) :=
  memHolder_const

@[simp]
lemma memHolder_zero [Zero Y] : MemHolder r (0 : X → Y) :=
  memHolder_const

section Monotonicity

open Bornology

/-- If a function is `r`-Hölder over a bounded space, then it is also `s`-Hölder when `s ≤ r`.
See `MemHolder.of_le'` for the version in a pseudoemetric space. -/
lemma MemHolder.of_le {X : Type*} [PseudoMetricSpace X] [hX : BoundedSpace X]
    {f : X → Y} {s : ℝ≥0} (hf : MemHolder r f) (hs : s ≤ r) :
    MemHolder s f := by
  obtain ⟨C, hf⟩ := hf
  obtain ⟨C', hC'⟩ := Metric.boundedSpace_iff_edist.1 hX
  exact ⟨C * C' ^ (r - s : ℝ),
    holderOnWith_univ.1 <| (holderOnWith_univ.2 hf).of_le (fun x _ y _ ↦ hC' x y) hs⟩

/-- If a function is `r`-Hölder over a bounded space, then it is also `s`-Hölder when `s ≤ r`.
See `MemHolder.of_le` for the version in a pseudometric space. -/
lemma MemHolder.of_le' {s : ℝ≥0} (hf : MemHolder r f) (hs : s ≤ r)
    (hX : ∃ C : ℝ≥0, ∀ x y : X, edist x y ≤ C) :
    MemHolder s f := by
  obtain ⟨C, hX⟩ := hX
  letI := PseudoEMetricSpace.toPseudoMetricSpace
    fun x y ↦ ne_top_of_le_ne_top ENNReal.coe_ne_top (hX x y)
  have := Metric.boundedSpace_iff_edist.2 ⟨C, hX⟩
  exact hf.of_le hs

/-- If a function is `r`-Hölder over a bounded set, then it is also `s`-Hölder over this set
when `s ≤ r`. See `HolderOnWith.exists_holderOnWith_of_le'`
for the version in a pseudoemetric space. -/
lemma HolderOnWith.exists_holderOnWith_of_le {X : Type*} [PseudoMetricSpace X]
    {f : X → Y} {s : ℝ≥0} {A : Set X} (hf : ∃ C, HolderOnWith C r f A) (hs : s ≤ r)
    (hA : IsBounded A) : ∃ C, HolderOnWith C s f A := by
  simp_rw [← HolderWith.restrict_iff] at *
  have : BoundedSpace A := boundedSpace_val_set_iff.2 hA
  exact MemHolder.of_le hf hs

/-- If a function is `r`-Hölder over a bounded set,
then it is also `s`-Hölder over this set when `s ≤ r`. See `HolderOnWith.exists_holderOnWith_of_le`
for the version in a pseudometric space. -/
lemma HolderOnWith.exists_holderOnWith_of_le' {D s : ℝ≥0} {A : Set X}
    (hf : ∃ C, HolderOnWith C r f A) (hs : s ≤ r)
    (hA : ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ A → edist x y ≤ D) :
    ∃ C, HolderOnWith C s f A := by
  simp_rw [← HolderWith.restrict_iff] at *
  letI := PseudoEMetricSpace.toPseudoMetricSpace
    fun x y : A ↦ ne_top_of_le_ne_top ENNReal.coe_ne_top (hA x.2 y.2)
  have : BoundedSpace A := Metric.boundedSpace_iff_edist.2 ⟨D, fun x y ↦ hA x.2 y.2⟩
  exact MemHolder.of_le hf hs

/-- If a function is locally `r`-Hölder and locally `t`-Hölder,
then it is locally `s`-Hölder for `r ≤ s ≤ t`. -/
lemma HolderOnWith.exists_holderOnWith_of_le_of_le {s t : ℝ≥0} {A : Set X}
    (hf₁ : ∃ C, HolderOnWith C r f A) (hf₂ : ∃ C, HolderOnWith C t f A)
    (hrs : r ≤ s) (hst : s ≤ t) : ∃ C, HolderOnWith C s f A := by
  obtain ⟨C₁, hf₁⟩ := hf₁
  obtain ⟨C₂, hf₂⟩ := hf₂
  exact ⟨max C₁ C₂, hf₁.of_le_of_le hf₂ hrs hst⟩

/-- If a function is `r`-Hölder and `t`-Hölder, then it is `s`-Hölder for `r ≤ s ≤ t`. -/
lemma MemHolder.memHolder_of_le_of_le {s t : ℝ≥0} (hf₁ : MemHolder r f) (hf₂ : MemHolder t f)
    (hrs : r ≤ s) (hst : s ≤ t) : MemHolder s f := by
  simp_rw [MemHolder, ← holderOnWith_univ] at *
  exact HolderOnWith.exists_holderOnWith_of_le_of_le hf₁ hf₂ hrs hst

end Monotonicity

end PseudoEMetricSpace

section MetricSpace

variable [MetricSpace X] [EMetricSpace Y]

lemma eHolderNorm_eq_zero {r : ℝ≥0} {f : X → Y} :
    eHolderNorm r f = 0 ↔ ∀ x₁ x₂, f x₁ = f x₂ := by
  constructor
  · refine fun h x₁ x₂ => ?_
    by_cases hx : x₁ = x₂
    · rw [hx]
    · rw [eHolderNorm, ← ENNReal.bot_eq_zero, iInf₂_eq_bot] at h
      rw [← edist_eq_zero, ← nonpos_iff_eq_zero]
      refine le_of_forall_gt fun b hb => ?_
      obtain ⟨C, hC, hC'⟩ := h (b / edist x₁ x₂ ^ (r : ℝ))
        (ENNReal.div_pos hb.ne.symm (ENNReal.rpow_lt_top_of_nonneg zero_le_coe
          (edist_lt_top x₁ x₂).ne).ne)
      exact lt_of_le_of_lt (hC x₁ x₂) <| ENNReal.mul_lt_of_lt_div hC'
  · intro h
    rcases isEmpty_or_nonempty X with hX | hX
    · exact eHolderNorm_of_isEmpty
    · rw [← eHolderNorm_const X r (f hX.some)]
      congr
      simp [funext_iff, h _ hX.some]

lemma MemHolder.holderWith {r : ℝ≥0} {f : X → Y} (hf : MemHolder r f) :
    HolderWith (nnHolderNorm r f) r f := by
  intro x₁ x₂
  by_cases hx : x₁ = x₂
  · simp only [hx, edist_self, zero_le]
  rw [nnHolderNorm, eHolderNorm, coe_toNNReal]
  on_goal 2 => exact hf.eHolderNorm_lt_top.ne
  have h₁ : edist x₁ x₂ ^ (r : ℝ) ≠ 0 :=
    (Ne.symm <| ne_of_lt <| ENNReal.rpow_pos (edist_pos.2 hx) (edist_lt_top x₁ x₂).ne)
  have h₂ : edist x₁ x₂ ^ (r : ℝ) ≠ ∞ := by
    simp [(edist_lt_top x₁ x₂).ne]
  rw [← ENNReal.div_le_iff h₁ h₂]
  refine le_iInf₂ fun C hC => ?_
  rw [ENNReal.div_le_iff h₁ h₂]
  exact hC x₁ x₂

lemma memHolder_iff_holderWith {r : ℝ≥0} {f : X → Y} :
    MemHolder r f ↔ HolderWith (nnHolderNorm r f) r f :=
  ⟨MemHolder.holderWith, HolderWith.memHolder⟩

lemma MemHolder.coe_nnHolderNorm_eq_eHolderNorm
    {r : ℝ≥0} {f : X → Y} (hf : MemHolder r f) :
    (nnHolderNorm r f : ℝ≥0∞) = eHolderNorm r f := by
  rw [nnHolderNorm, coe_toNNReal]
  exact ne_of_lt <| lt_of_le_of_lt hf.holderWith.eHolderNorm_le <| coe_lt_top

lemma HolderWith.nnholderNorm_le {C r : ℝ≥0} {f : X → Y} (hf : HolderWith C r f) :
    nnHolderNorm r f ≤ C := by
  rw [← ENNReal.coe_le_coe, hf.memHolder.coe_nnHolderNorm_eq_eHolderNorm]
  exact hf.eHolderNorm_le

lemma MemHolder.comp {r s : ℝ≥0} {Z : Type*} [MetricSpace Z] {f : Z → X} {g : X → Y}
    (hf : MemHolder r f) (hg : MemHolder s g) : MemHolder (s * r) (g ∘ f) :=
  (hg.holderWith.comp hf.holderWith).memHolder

lemma MemHolder.nnHolderNorm_eq_zero {r : ℝ≥0} {f : X → Y} (hf : MemHolder r f) :
    nnHolderNorm r f = 0 ↔ ∀ x₁ x₂, f x₁ = f x₂ := by
  rw [← ENNReal.coe_eq_zero, hf.coe_nnHolderNorm_eq_eHolderNorm, eHolderNorm_eq_zero]

end MetricSpace

section SeminormedAddCommGroup

variable [MetricSpace X] [NormedAddCommGroup Y]
variable {r : ℝ≥0} {f g : X → Y}

lemma MemHolder.add (hf : MemHolder r f) (hg : MemHolder r g) : MemHolder r (f + g) :=
  (hf.holderWith.add hg.holderWith).memHolder

lemma MemHolder.smul {𝕜} [SeminormedRing 𝕜] [Module 𝕜 Y] [IsBoundedSMul 𝕜 Y]
    {c : 𝕜} (hf : MemHolder r f) : MemHolder r (c • f) :=
  (hf.holderWith.smul c).memHolder

lemma MemHolder.smul_iff {𝕜} [SeminormedRing 𝕜] [Module 𝕜 Y] [NormSMulClass 𝕜 Y]
    {c : 𝕜} (hc : ‖c‖₊ ≠ 0) : MemHolder r (c • f) ↔ MemHolder r f := by
  refine ⟨fun ⟨h, hh⟩ => ⟨h * ‖c‖₊⁻¹, ?_⟩, .smul⟩
  rw [← HolderWith.smul_iff _ hc, inv_mul_cancel_right₀ hc]
  exact hh

lemma MemHolder.nsmul [NormedSpace ℝ Y] (n : ℕ) (hf : MemHolder r f) :
    MemHolder r (n • f) := by
  simp [← Nat.cast_smul_eq_nsmul (R := ℝ), hf.smul]

lemma MemHolder.nnHolderNorm_add_le (hf : MemHolder r f) (hg : MemHolder r g) :
    nnHolderNorm r (f + g) ≤ nnHolderNorm r f + nnHolderNorm r g :=
  (hf.add hg).holderWith.nnholderNorm_le.trans (hf.holderWith.add hg.holderWith).nnholderNorm_le

lemma eHolderNorm_add_le :
    eHolderNorm r (f + g) ≤ eHolderNorm r f + eHolderNorm r g := by
  by_cases hfg : MemHolder r f ∧ MemHolder r g
  · obtain ⟨hf, hg⟩ := hfg
    rw [← hf.coe_nnHolderNorm_eq_eHolderNorm, ← hg.coe_nnHolderNorm_eq_eHolderNorm,
      ← (hf.add hg).coe_nnHolderNorm_eq_eHolderNorm, ← coe_add, ENNReal.coe_le_coe]
    exact hf.nnHolderNorm_add_le hg
  · rw [Classical.not_and_iff_not_or_not, ← eHolderNorm_eq_top, ← eHolderNorm_eq_top] at hfg
    obtain (h | h) := hfg
    all_goals simp [h]

lemma eHolderNorm_smul {α} [NormedRing α] [Module α Y] [NormSMulClass α Y] (c : α) :
    eHolderNorm r (c • f) = ‖c‖₊ * eHolderNorm r f := by
  by_cases hc : ‖c‖₊ = 0
  · rw [nnnorm_eq_zero] at hc
    simp [hc]
  by_cases hf : MemHolder r f
  · refine le_antisymm ((hf.holderWith.smul c).eHolderNorm_le.trans ?_) <| mul_le_of_le_div' ?_
    · rw [coe_mul, hf.coe_nnHolderNorm_eq_eHolderNorm, mul_comm]
    · rw [← (hf.holderWith.smul c).memHolder.coe_nnHolderNorm_eq_eHolderNorm, ← coe_div hc]
      refine HolderWith.eHolderNorm_le fun x₁ x₂ => ?_
      rw [coe_div hc, ← ENNReal.mul_div_right_comm,
        ENNReal.le_div_iff_mul_le (Or.inl <| coe_ne_zero.2 hc) <| Or.inl coe_ne_top,
        mul_comm, ← smul_eq_mul, ← ENNReal.smul_def, ← edist_smul₀, ← Pi.smul_apply,
        ← Pi.smul_apply]
      exact hf.smul.holderWith x₁ x₂
  · rw [← eHolderNorm_eq_top] at hf
    rw [hf, mul_top <| coe_ne_zero.2 hc, eHolderNorm_eq_top, MemHolder.smul_iff hc]
    rw [nnnorm_eq_zero] at hc
    intro h
    exact h.eHolderNorm_lt_top.ne hf

lemma MemHolder.nnHolderNorm_smul {α} [NormedRing α] [Module α Y] [NormSMulClass α Y]
    (hf : MemHolder r f) (c : α) :
    nnHolderNorm r (c • f) = ‖c‖₊ * nnHolderNorm r f := by
  rw [← ENNReal.coe_inj, coe_mul, hf.coe_nnHolderNorm_eq_eHolderNorm,
    hf.smul.coe_nnHolderNorm_eq_eHolderNorm, eHolderNorm_smul]

lemma eHolderNorm_nsmul [NormedSpace ℝ Y] (n : ℕ) :
    eHolderNorm r (n • f) = n • eHolderNorm r f := by
  simp [← Nat.cast_smul_eq_nsmul (R := ℝ), eHolderNorm_smul]

lemma MemHolder.nnHolderNorm_nsmul [NormedSpace ℝ Y] (n : ℕ) (hf : MemHolder r f) :
    nnHolderNorm r (n • f) = n • nnHolderNorm r f := by
  simp [← Nat.cast_smul_eq_nsmul (R := ℝ), hf.nnHolderNorm_smul]

end SeminormedAddCommGroup
