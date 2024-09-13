/-
Copyright (c) 2024 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.Topology.MetricSpace.Holder

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

* `eHolderNorm_eq_zero_iff`: the Hölder norm of a function is zero if and only if it is constant.
* `MemHolder.holderWith`: The Hölder norm of a Hölder function `f` is a Hölder constant of `f`.

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
def eHolderNorm (r : ℝ≥0) (f : X → Y) : ℝ≥0∞ := ⨅ (C) (_ : HolderWith C r f), C

/-- The `r`-Hölder (semi)norm in `ℝ≥0`. -/
noncomputable
def nnHolderNorm (r : ℝ≥0) (f : X → Y) : ℝ≥0 := (eHolderNorm r f).toNNReal

/-- A function `f` is `MemHolder r f` if it is Hölder continuous. Namely, `f` has a finite
`r`-Hölder constant. This is equivalent to `f` having finite Hölder norm.
c.f. `memHolder_iff`. -/
def MemHolder (r : ℝ≥0) (f : X → Y) : Prop := ∃ C, HolderWith C r f

lemma HolderWith.memHolder {C : ℝ≥0} (hf : HolderWith C r f) : MemHolder r f := ⟨C, hf⟩

lemma MemHolder.eHolderNorm_lt_top (hf : MemHolder r f) : eHolderNorm r f < ∞ :=
  let ⟨C, hC⟩ := hf; iInf_lt_top.2 ⟨C, iInf_lt_top.2 ⟨hC, coe_lt_top⟩⟩

lemma memHolder_iff : MemHolder r f ↔ eHolderNorm r f < ∞ := by
  refine ⟨MemHolder.eHolderNorm_lt_top, fun h => ?_⟩
  simp_rw [eHolderNorm, iInf_lt_top] at h
  exact let ⟨C, hC, _⟩ := h; ⟨C, hC⟩

lemma memHolder_iff' : MemHolder r f ↔ eHolderNorm r f ≠ ∞ := by
  rw [memHolder_iff, lt_top_iff_ne_top]

lemma not_memHolder : ¬ MemHolder r f ↔ eHolderNorm r f = ∞ := by
  rw [memHolder_iff', not_not]

lemma MemHolder.lt_top (hf : MemHolder r f) : eHolderNorm r f < ∞ :=
  hf.eHolderNorm_lt_top

lemma MemHolder.ne_top (hf : MemHolder r f) : eHolderNorm r f ≠ ∞ :=
  hf.eHolderNorm_lt_top.ne

variable (X) in
lemma eHolderNorm_const (r : ℝ≥0) (c : Y) : eHolderNorm r (Function.const X c) = 0 := by
  rw [eHolderNorm, ← ENNReal.bot_eq_zero, iInf₂_eq_bot]
  exact fun C' hC' => ⟨0, .const, hC'⟩

variable (X) in
lemma eHolderNorm_zero [Zero Y] (r : ℝ≥0) : eHolderNorm r (0 : X → Y) = 0 :=
  eHolderNorm_const X r 0

attribute [simp] eHolderNorm_const eHolderNorm_zero

lemma eHolderNorm_of_isEmpty [hX : IsEmpty X] :
    eHolderNorm r f = 0 := by
  rw [eHolderNorm, ← ENNReal.bot_eq_zero, iInf₂_eq_bot]
  exact fun ε hε => ⟨0, .of_isEmpty, hε⟩

lemma HolderWith.eHolderNorm_le {C : ℝ≥0} (hf : HolderWith C r f) :
    eHolderNorm r f ≤ C :=
  iInf₂_le C hf

variable (X) in
lemma memHolder_const {c : Y} : MemHolder r (Function.const X c) :=
  (HolderWith.const (C := 0)).memHolder

variable (X) in
lemma memHolder_zero [Zero Y] : MemHolder r (0 : X → Y) :=
  memHolder_const X

end PseudoEMetricSpace

section MetricSpace

variable [MetricSpace X] [EMetricSpace Y]

lemma eHolderNorm_eq_zero_iff {r : ℝ≥0} {f : X → Y} :
    eHolderNorm r f = 0 ↔ ∀ x₁ x₂, f x₁ = f x₂ := by
  constructor
  · refine fun h x₁ x₂ => ?_
    by_cases hx : x₁ = x₂
    · rw [hx]
    · rw [eHolderNorm, ← ENNReal.bot_eq_zero, iInf₂_eq_bot] at h
      rw [← edist_eq_zero, ← le_zero_iff]
      refine le_of_forall_lt' fun b hb => ?_
      obtain ⟨C, hC, hC'⟩ := h (b / edist x₁ x₂ ^ (r : ℝ))
        (ENNReal.div_pos hb.ne.symm (ENNReal.rpow_lt_top_of_nonneg zero_le_coe
          (edist_lt_top x₁ x₂).ne).ne)
      exact lt_of_le_of_lt (hC x₁ x₂) <| ENNReal.mul_lt_of_lt_div hC'
  · intro h
    cases' isEmpty_or_nonempty X with hX hX
    · haveI := hX
      exact eHolderNorm_of_isEmpty
    · rw [← eHolderNorm_const X r (f hX.some)]
      congr
      simp [funext_iff, h _ hX.some]

lemma MemHolder.holderWith {r : ℝ≥0} {f : X → Y} (hf : MemHolder r f) :
    HolderWith (nnHolderNorm r f) r f := by
  intros x₁ x₂
  by_cases hx : x₁ = x₂
  · simp only [hx, edist_self, zero_le]
  rw [nnHolderNorm, eHolderNorm, coe_toNNReal]
  swap; exact hf.eHolderNorm_lt_top.ne
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

lemma coe_nnHolderNorm_le_eHolderNorm {r : ℝ≥0} {f : X → Y} :
    (nnHolderNorm r f : ℝ≥0∞) ≤ eHolderNorm r f :=
  coe_toNNReal_le_self

lemma HolderWith.coe_nnHolderNorm_eq_eHolderNorm
    {C r : ℝ≥0} {f : X → Y} (hf : HolderWith C r f) :
    (nnHolderNorm r f : ℝ≥0∞) = eHolderNorm r f := by
  rw [nnHolderNorm, coe_toNNReal]
  exact ne_of_lt <| lt_of_le_of_lt hf.eHolderNorm_le <| coe_lt_top (r := C)

lemma MemHolder.coe_nnHolderNorm_eq_eHolderNorm
    {r : ℝ≥0} {f : X → Y} (hf : MemHolder r f) :
    (nnHolderNorm r f : ℝ≥0∞) = eHolderNorm r f :=
  hf.holderWith.coe_nnHolderNorm_eq_eHolderNorm

lemma HolderWith.nnholderNorm_le {C r : ℝ≥0} {f : X → Y} (hf : HolderWith C r f) :
    nnHolderNorm r f ≤ C := by
  rw [← ENNReal.coe_le_coe, hf.coe_nnHolderNorm_eq_eHolderNorm]
  exact hf.eHolderNorm_le

lemma MemHolder.comp {r : ℝ≥0} {Z : Type*} [MetricSpace Z] {f : Z → X} {g : X → Y}
    (hf : MemHolder r f) (hg : MemHolder r g) : MemHolder (r * r) (g ∘ f) :=
  (hg.holderWith.comp hf.holderWith).memHolder

end MetricSpace

section SeminormedAddCommGroup

variable [MetricSpace X] [NormedAddCommGroup Y]
variable {C r : ℝ≥0} {f g : X → Y}

lemma MemHolder.add (hf : MemHolder r f) (hg : MemHolder r g) : MemHolder r (f + g) :=
  (hf.holderWith.add hg.holderWith).memHolder

lemma MemHolder.smul {α} [NormedDivisionRing α] [Module α Y] [BoundedSMul α Y]
    (c : α) (hf : MemHolder r f) : MemHolder r (c • f) :=
  (hf.holderWith.smul c).memHolder

variable (r f g) in
lemma eHolderNorm_add :
    eHolderNorm r (f + g) ≤ eHolderNorm r f + eHolderNorm r g := by
  by_cases hfg : MemHolder r f  ∧ MemHolder r g
  · obtain ⟨hf, hg⟩ := hfg
    rw [← hf.coe_nnHolderNorm_eq_eHolderNorm, ← hg.coe_nnHolderNorm_eq_eHolderNorm, ← coe_add]
    exact (hf.add hg).holderWith.eHolderNorm_le.trans <|
      coe_le_coe.2 (hf.holderWith.add hg.holderWith).nnholderNorm_le
  · rw [Classical.not_and_iff_or_not_not, not_memHolder, not_memHolder] at hfg
    obtain (h | h) := hfg
    all_goals simp [h]

lemma eHolderNorm_smul {α} [NormedDivisionRing α] [Module α Y] [BoundedSMul α Y] (c : α) :
    eHolderNorm r (c • f) = ‖c‖₊ * eHolderNorm r f := by
  by_cases hc : ‖c‖₊ = 0
  · rw [nnnorm_eq_zero] at hc
    simp [hc]
  by_cases hf : MemHolder r f
  · refine le_antisymm ((hf.holderWith.smul c).eHolderNorm_le.trans ?_) <| mul_le_of_le_div' ?_
    · rw [coe_mul, hf.coe_nnHolderNorm_eq_eHolderNorm, mul_comm]
    · rw [← (hf.holderWith.smul c).coe_nnHolderNorm_eq_eHolderNorm, ← coe_div hc]
      refine HolderWith.eHolderNorm_le fun x₁ x₂ => ?_
      rw [coe_div hc, ← ENNReal.mul_div_right_comm,
        ENNReal.le_div_iff_mul_le (Or.inl <| coe_ne_zero.2 hc) <| Or.inl coe_ne_top,
        mul_comm, ← smul_eq_mul, ← ENNReal.smul_def, ← edist_smul₀, ← Pi.smul_apply,
        ← Pi.smul_apply]
      exact (hf.smul c).holderWith x₁ x₂
  · rw [not_memHolder] at hf
    rw [hf, mul_top <| coe_ne_zero.2 hc, ← not_memHolder]
    rw [nnnorm_eq_zero] at hc
    intro h
    have := h.smul c⁻¹
    rw [inv_smul_smul₀ hc] at this
    exact this.eHolderNorm_lt_top.ne hf

end SeminormedAddCommGroup
