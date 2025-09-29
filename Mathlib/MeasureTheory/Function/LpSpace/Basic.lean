/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Lp space

This file provides the space `Lp E p μ` as the subtype of elements of `α →ₘ[μ] E`
(see `MeasureTheory.AEEqFun`) such that `eLpNorm f p μ` is finite.
For `1 ≤ p`, `eLpNorm` defines a norm and `Lp` is a complete metric space
(the latter is proved at `Mathlib/MeasureTheory/Function/LpSpace/Complete.lean`).

## Main definitions

* `Lp E p μ` : elements of `α →ₘ[μ] E` such that `eLpNorm f p μ` is finite.
  Defined as an `AddSubgroup` of `α →ₘ[μ] E`.

Lipschitz functions vanishing at zero act by composition on `Lp`. We define this action, and prove
that it is continuous. In particular,
* `ContinuousLinearMap.compLp` defines the action on `Lp` of a continuous linear map.
* `Lp.posPart` is the positive part of an `Lp` function.
* `Lp.negPart` is the negative part of an `Lp` function.

## Notations

* `α →₁[μ] E` : the type `Lp E 1 μ`.
* `α →₂[μ] E` : the type `Lp E 2 μ`.

## Implementation

Since `Lp` is defined as an `AddSubgroup`, dot notation does not work. Use `Lp.Measurable f` to
say that the coercion of `f` to a genuine function is measurable, instead of the non-working
`f.Measurable`.

To prove that two `Lp` elements are equal, it suffices to show that their coercions to functions
coincide almost everywhere (this is registered as an `ext` rule). This can often be done using
`filter_upwards`. For instance, a proof from first principles that `f + (g + h) = (f + g) + h`
could read (in the `Lp` namespace)
```
example (f g h : Lp E p μ) : (f + g) + h = f + (g + h) := by
  ext1
  filter_upwards [coeFn_add (f + g) h, coeFn_add f g, coeFn_add f (g + h), coeFn_add g h]
    with _ ha1 ha2 ha3 ha4
  simp only [ha1, ha2, ha3, ha4, add_assoc]
```
The lemma `coeFn_add` states that the coercion of `f + g` coincides almost everywhere with the sum
of the coercions of `f` and `g`. All such lemmas use `coeFn` in their name, to distinguish the
function coercion from the coercion to almost everywhere defined functions.
-/

noncomputable section

open MeasureTheory Filter
open scoped NNReal ENNReal

variable {α 𝕜 𝕜' E F : Type*} {m : MeasurableSpace α} {p : ℝ≥0∞} {μ : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F]

namespace MeasureTheory

/-!
### Lp space

The space of equivalence classes of measurable functions for which `eLpNorm f p μ < ∞`.
-/

@[simp]
theorem eLpNorm_aeeqFun {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    {p : ℝ≥0∞} {f : α → E} (hf : AEStronglyMeasurable f μ) :
    eLpNorm (AEEqFun.mk f hf) p μ = eLpNorm f p μ :=
  eLpNorm_congr_ae (AEEqFun.coeFn_mk _ _)

theorem MemLp.eLpNorm_mk_lt_top {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {p : ℝ≥0∞} {f : α → E} (hfp : MemLp f p μ) :
    eLpNorm (AEEqFun.mk f hfp.1) p μ < ∞ := by simp [hfp.2]

/-- Lp space -/
def Lp {α} (E : Type*) {m : MeasurableSpace α} [NormedAddCommGroup E] (p : ℝ≥0∞)
    (μ : Measure α := by volume_tac) : AddSubgroup (α →ₘ[μ] E) where
  carrier := { f | eLpNorm f p μ < ∞ }
  zero_mem' := by simp [eLpNorm_congr_ae AEEqFun.coeFn_zero, eLpNorm_zero]
  add_mem' {f g} hf hg := by
    simp [eLpNorm_congr_ae (AEEqFun.coeFn_add f g),
      eLpNorm_add_lt_top ⟨f.aestronglyMeasurable, hf⟩ ⟨g.aestronglyMeasurable, hg⟩]
  neg_mem' {f} hf := by rwa [Set.mem_setOf_eq, eLpNorm_congr_ae (AEEqFun.coeFn_neg f), eLpNorm_neg]

/-- `α →₁[μ] E` is the type of `L¹` or integrable functions from `α` to `E`. -/
scoped notation:25 α' " →₁[" μ "] " E => MeasureTheory.Lp (α := α') E 1 μ
/-- `α →₂[μ] E` is the type of `L²` or square-integrable functions from `α` to `E`. -/
scoped notation:25 α' " →₂[" μ "] " E => MeasureTheory.Lp (α := α') E 2 μ

namespace MemLp

/-- make an element of Lp from a function verifying `MemLp` -/
def toLp (f : α → E) (h_mem_ℒp : MemLp f p μ) : Lp E p μ :=
  ⟨AEEqFun.mk f h_mem_ℒp.1, h_mem_ℒp.eLpNorm_mk_lt_top⟩

theorem toLp_val {f : α → E} (h : MemLp f p μ) : (toLp f h).1 = AEEqFun.mk f h.1 := rfl

theorem coeFn_toLp {f : α → E} (hf : MemLp f p μ) : hf.toLp f =ᵐ[μ] f :=
  AEEqFun.coeFn_mk _ _

theorem toLp_congr {f g : α → E} (hf : MemLp f p μ) (hg : MemLp g p μ) (hfg : f =ᵐ[μ] g) :
    hf.toLp f = hg.toLp g := by simp [toLp, hfg]

@[simp]
theorem toLp_eq_toLp_iff {f g : α → E} (hf : MemLp f p μ) (hg : MemLp g p μ) :
    hf.toLp f = hg.toLp g ↔ f =ᵐ[μ] g := by simp [toLp]

@[simp]
theorem toLp_zero (h : MemLp (0 : α → E) p μ) : h.toLp 0 = 0 :=
  rfl

theorem toLp_add {f g : α → E} (hf : MemLp f p μ) (hg : MemLp g p μ) :
    (hf.add hg).toLp (f + g) = hf.toLp f + hg.toLp g :=
  rfl

theorem toLp_neg {f : α → E} (hf : MemLp f p μ) : hf.neg.toLp (-f) = -hf.toLp f :=
  rfl

theorem toLp_sub {f g : α → E} (hf : MemLp f p μ) (hg : MemLp g p μ) :
    (hf.sub hg).toLp (f - g) = hf.toLp f - hg.toLp g :=
  rfl

end MemLp

namespace Lp

instance instCoeFun : CoeFun (Lp E p μ) (fun _ => α → E) :=
  ⟨fun f => ((f : α →ₘ[μ] E) : α → E)⟩

@[ext high]
theorem ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g := by
  cases f
  cases g
  simp only [Subtype.mk_eq_mk]
  exact AEEqFun.ext h

theorem mem_Lp_iff_eLpNorm_lt_top {f : α →ₘ[μ] E} : f ∈ Lp E p μ ↔ eLpNorm f p μ < ∞ := Iff.rfl

theorem mem_Lp_iff_memLp {f : α →ₘ[μ] E} : f ∈ Lp E p μ ↔ MemLp f p μ := by
  simp [mem_Lp_iff_eLpNorm_lt_top, MemLp, f.stronglyMeasurable.aestronglyMeasurable]

protected theorem antitone [IsFiniteMeasure μ] {p q : ℝ≥0∞} (hpq : p ≤ q) : Lp E q μ ≤ Lp E p μ :=
  fun f hf => (MemLp.mono_exponent ⟨f.aestronglyMeasurable, hf⟩ hpq).2

@[simp]
theorem coeFn_mk {f : α →ₘ[μ] E} (hf : eLpNorm f p μ < ∞) : ((⟨f, hf⟩ : Lp E p μ) : α → E) = f :=
  rfl

-- not @[simp] because dsimp can prove this
theorem coe_mk {f : α →ₘ[μ] E} (hf : eLpNorm f p μ < ∞) : ((⟨f, hf⟩ : Lp E p μ) : α →ₘ[μ] E) = f :=
  rfl

@[simp]
theorem toLp_coeFn (f : Lp E p μ) (hf : MemLp f p μ) : hf.toLp f = f := by
  simp [MemLp.toLp]

theorem eLpNorm_lt_top (f : Lp E p μ) : eLpNorm f p μ < ∞ :=
  f.prop

@[aesop (rule_sets := [finiteness]) safe apply]
theorem eLpNorm_ne_top (f : Lp E p μ) : eLpNorm f p μ ≠ ∞ :=
  (eLpNorm_lt_top f).ne

@[fun_prop, measurability]
protected theorem stronglyMeasurable (f : Lp E p μ) : StronglyMeasurable f :=
  f.val.stronglyMeasurable

@[fun_prop, measurability]
protected theorem aestronglyMeasurable (f : Lp E p μ) : AEStronglyMeasurable f μ :=
  f.val.aestronglyMeasurable

protected theorem memLp (f : Lp E p μ) : MemLp f p μ :=
  ⟨Lp.aestronglyMeasurable f, f.prop⟩

variable (E p μ)

theorem coeFn_zero : ⇑(0 : Lp E p μ) =ᵐ[μ] 0 :=
  AEEqFun.coeFn_zero

variable {E p μ}

theorem coeFn_neg (f : Lp E p μ) : ⇑(-f) =ᵐ[μ] -f :=
  AEEqFun.coeFn_neg _

theorem coeFn_add (f g : Lp E p μ) : ⇑(f + g) =ᵐ[μ] f + g :=
  AEEqFun.coeFn_add _ _

theorem coeFn_sub (f g : Lp E p μ) : ⇑(f - g) =ᵐ[μ] f - g :=
  AEEqFun.coeFn_sub _ _

theorem const_mem_Lp (α) {_ : MeasurableSpace α} (μ : Measure α) (c : E) [IsFiniteMeasure μ] :
    @AEEqFun.const α _ _ μ _ c ∈ Lp E p μ :=
  (memLp_const c).eLpNorm_mk_lt_top

instance instNorm : Norm (Lp E p μ) where norm f := ENNReal.toReal (eLpNorm f p μ)

-- note: we need this to be defeq to the instance from `SeminormedAddGroup.toNNNorm`, so
-- can't use `ENNReal.toNNReal (eLpNorm f p μ)`
instance instNNNorm : NNNorm (Lp E p μ) where nnnorm f := ⟨‖f‖, ENNReal.toReal_nonneg⟩

instance instDist : Dist (Lp E p μ) where dist f g := ‖f - g‖

instance instEDist : EDist (Lp E p μ) where edist f g := eLpNorm (⇑f - ⇑g) p μ

theorem norm_def (f : Lp E p μ) : ‖f‖ = ENNReal.toReal (eLpNorm f p μ) :=
  rfl

theorem nnnorm_def (f : Lp E p μ) : ‖f‖₊ = ENNReal.toNNReal (eLpNorm f p μ) :=
  rfl

@[simp, norm_cast]
protected theorem coe_nnnorm (f : Lp E p μ) : (‖f‖₊ : ℝ) = ‖f‖ :=
  rfl

@[simp]
theorem enorm_def (f : Lp E p μ) : ‖f‖ₑ = eLpNorm f p μ :=
  ENNReal.coe_toNNReal <| Lp.eLpNorm_ne_top f

@[simp]
lemma norm_toLp (f : α → E) (hf : MemLp f p μ) : ‖hf.toLp f‖ = ENNReal.toReal (eLpNorm f p μ) := by
  rw [norm_def, eLpNorm_congr_ae (MemLp.coeFn_toLp hf)]

@[simp]
theorem nnnorm_toLp (f : α → E) (hf : MemLp f p μ) :
    ‖hf.toLp f‖₊ = ENNReal.toNNReal (eLpNorm f p μ) :=
  NNReal.eq <| norm_toLp f hf

lemma enorm_toLp {f : α → E} (hf : MemLp f p μ) : ‖hf.toLp f‖ₑ = eLpNorm f p μ := by
  simp [enorm, nnnorm_toLp f hf, ENNReal.coe_toNNReal hf.2.ne]

theorem dist_def (f g : Lp E p μ) : dist f g = (eLpNorm (⇑f - ⇑g) p μ).toReal := by
  simp_rw [dist, norm_def]
  refine congr_arg _ ?_
  apply eLpNorm_congr_ae (coeFn_sub _ _)

theorem edist_def (f g : Lp E p μ) : edist f g = eLpNorm (⇑f - ⇑g) p μ :=
  rfl

protected theorem edist_dist (f g : Lp E p μ) : edist f g = .ofReal (dist f g) := by
  rw [edist_def, dist_def, ← eLpNorm_congr_ae (coeFn_sub _ _),
    ENNReal.ofReal_toReal (eLpNorm_ne_top (f - g))]

protected theorem dist_edist (f g : Lp E p μ) : dist f g = (edist f g).toReal :=
  MeasureTheory.Lp.dist_def ..

theorem dist_eq_norm (f g : Lp E p μ) : dist f g = ‖f - g‖ := rfl

@[simp]
theorem edist_toLp_toLp (f g : α → E) (hf : MemLp f p μ) (hg : MemLp g p μ) :
    edist (hf.toLp f) (hg.toLp g) = eLpNorm (f - g) p μ := by
  rw [edist_def]
  exact eLpNorm_congr_ae (hf.coeFn_toLp.sub hg.coeFn_toLp)

@[simp]
theorem edist_toLp_zero (f : α → E) (hf : MemLp f p μ) : edist (hf.toLp f) 0 = eLpNorm f p μ := by
  simpa using edist_toLp_toLp f 0 hf MemLp.zero

@[simp]
theorem nnnorm_zero : ‖(0 : Lp E p μ)‖₊ = 0 := by
  rw [nnnorm_def]
  change (eLpNorm (⇑(0 : α →ₘ[μ] E)) p μ).toNNReal = 0
  simp [eLpNorm_congr_ae AEEqFun.coeFn_zero, eLpNorm_zero]

@[simp]
theorem norm_zero : ‖(0 : Lp E p μ)‖ = 0 :=
  congr_arg ((↑) : ℝ≥0 → ℝ) nnnorm_zero

@[simp]
theorem norm_measure_zero (f : Lp E p (0 : MeasureTheory.Measure α)) : ‖f‖ = 0 := by
  -- Squeezed for performance reasons
  simp only [norm_def, eLpNorm_measure_zero, ENNReal.toReal_zero]

@[simp] theorem norm_exponent_zero (f : Lp E 0 μ) : ‖f‖ = 0 := by
  -- Squeezed for performance reasons
  simp only [norm_def, eLpNorm_exponent_zero, ENNReal.toReal_zero]

theorem nnnorm_eq_zero_iff {f : Lp E p μ} (hp : 0 < p) : ‖f‖₊ = 0 ↔ f = 0 := by
  refine ⟨fun hf => ?_, fun hf => by simp [hf]⟩
  rw [nnnorm_def, ENNReal.toNNReal_eq_zero_iff] at hf
  cases hf with
  | inl hf =>
    rw [eLpNorm_eq_zero_iff (Lp.aestronglyMeasurable f) hp.ne.symm] at hf
    exact Subtype.eq (AEEqFun.ext (hf.trans AEEqFun.coeFn_zero.symm))
  | inr hf =>
    exact absurd hf (eLpNorm_ne_top f)

theorem norm_eq_zero_iff {f : Lp E p μ} (hp : 0 < p) : ‖f‖ = 0 ↔ f = 0 :=
  NNReal.coe_eq_zero.trans (nnnorm_eq_zero_iff hp)

theorem eq_zero_iff_ae_eq_zero {f : Lp E p μ} : f = 0 ↔ f =ᵐ[μ] 0 := by
  rw [← (Lp.memLp f).toLp_eq_toLp_iff MemLp.zero, MemLp.toLp_zero, toLp_coeFn]

@[simp]
theorem nnnorm_neg (f : Lp E p μ) : ‖-f‖₊ = ‖f‖₊ := by
  rw [nnnorm_def, nnnorm_def, eLpNorm_congr_ae (coeFn_neg _), eLpNorm_neg]

@[simp]
theorem norm_neg (f : Lp E p μ) : ‖-f‖ = ‖f‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) (nnnorm_neg f)

theorem nnnorm_le_mul_nnnorm_of_ae_le_mul {c : ℝ≥0} {f : Lp E p μ} {g : Lp F p μ}
    (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊) : ‖f‖₊ ≤ c * ‖g‖₊ := by
  simp only [nnnorm_def]
  have := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul h p
  rwa [← ENNReal.toNNReal_le_toNNReal, ENNReal.smul_def, smul_eq_mul, ENNReal.toNNReal_mul,
    ENNReal.toNNReal_coe] at this
  · finiteness
  · exact ENNReal.mul_ne_top ENNReal.coe_ne_top (by finiteness)

theorem norm_le_mul_norm_of_ae_le_mul {c : ℝ} {f : Lp E p μ} {g : Lp F p μ}
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) : ‖f‖ ≤ c * ‖g‖ := by
  rcases le_or_gt 0 c with hc | hc
  · lift c to ℝ≥0 using hc
    exact NNReal.coe_le_coe.mpr (nnnorm_le_mul_nnnorm_of_ae_le_mul h)
  · simp only [norm_def]
    have := eLpNorm_eq_zero_and_zero_of_ae_le_mul_neg h hc p
    simp [this]

theorem norm_le_norm_of_ae_le {f : Lp E p μ} {g : Lp F p μ} (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
    ‖f‖ ≤ ‖g‖ := by
  rw [norm_def, norm_def]
  exact ENNReal.toReal_mono (by finiteness) (eLpNorm_mono_ae h)

theorem mem_Lp_of_nnnorm_ae_le_mul {c : ℝ≥0} {f : α →ₘ[μ] E} {g : Lp F p μ}
    (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊) : f ∈ Lp E p μ :=
  mem_Lp_iff_memLp.2 <| MemLp.of_nnnorm_le_mul (Lp.memLp g) f.aestronglyMeasurable h

theorem mem_Lp_of_ae_le_mul {c : ℝ} {f : α →ₘ[μ] E} {g : Lp F p μ}
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) : f ∈ Lp E p μ :=
  mem_Lp_iff_memLp.2 <| MemLp.of_le_mul (Lp.memLp g) f.aestronglyMeasurable h

theorem mem_Lp_of_nnnorm_ae_le {f : α →ₘ[μ] E} {g : Lp F p μ} (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ ‖g x‖₊) :
    f ∈ Lp E p μ :=
  mem_Lp_iff_memLp.2 <| MemLp.of_le (Lp.memLp g) f.aestronglyMeasurable h

theorem mem_Lp_of_ae_le {f : α →ₘ[μ] E} {g : Lp F p μ} (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
    f ∈ Lp E p μ :=
  mem_Lp_of_nnnorm_ae_le h

theorem mem_Lp_of_ae_nnnorm_bound [IsFiniteMeasure μ] {f : α →ₘ[μ] E} (C : ℝ≥0)
    (hfC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) : f ∈ Lp E p μ :=
  mem_Lp_iff_memLp.2 <| MemLp.of_bound f.aestronglyMeasurable _ hfC

theorem mem_Lp_of_ae_bound [IsFiniteMeasure μ] {f : α →ₘ[μ] E} (C : ℝ) (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    f ∈ Lp E p μ :=
  mem_Lp_iff_memLp.2 <| MemLp.of_bound f.aestronglyMeasurable _ hfC

theorem nnnorm_le_of_ae_bound [IsFiniteMeasure μ] {f : Lp E p μ} {C : ℝ≥0}
    (hfC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) : ‖f‖₊ ≤ measureUnivNNReal μ ^ p.toReal⁻¹ * C := by
  by_cases hμ : μ = 0
  · by_cases hp : p.toReal⁻¹ = 0
    · simp [hp, hμ, nnnorm_def]
    · simp [hμ, nnnorm_def]
  rw [← ENNReal.coe_le_coe, nnnorm_def, ENNReal.coe_toNNReal (eLpNorm_ne_top _)]
  refine (eLpNorm_le_of_ae_nnnorm_bound hfC).trans_eq ?_
  rw [← coe_measureUnivNNReal μ, ← ENNReal.coe_rpow_of_ne_zero (measureUnivNNReal_pos hμ).ne',
    ENNReal.coe_mul, mul_comm, ENNReal.smul_def, smul_eq_mul]

theorem norm_le_of_ae_bound [IsFiniteMeasure μ] {f : Lp E p μ} {C : ℝ} (hC : 0 ≤ C)
    (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : ‖f‖ ≤ measureUnivNNReal μ ^ p.toReal⁻¹ * C := by
  lift C to ℝ≥0 using hC
  have := nnnorm_le_of_ae_bound hfC
  rwa [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_rpow] at this

instance instNormedAddCommGroup [hp : Fact (1 ≤ p)] : NormedAddCommGroup (Lp E p μ) :=
  { AddGroupNorm.toNormedAddCommGroup
      { toFun := (norm : Lp E p μ → ℝ)
        map_zero' := norm_zero
        neg' := by simp only [norm_neg, implies_true] -- squeezed for performance reasons
        add_le' := fun f g => by
          suffices ‖f + g‖ₑ ≤ ‖f‖ₑ + ‖g‖ₑ by
            -- Squeezed for performance reasons
            simpa only [ge_iff_le, enorm, ←ENNReal.coe_add, ENNReal.coe_le_coe] using this
          simp only [Lp.enorm_def]
          exact (eLpNorm_congr_ae (AEEqFun.coeFn_add _ _)).trans_le
            (eLpNorm_add_le (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _) hp.out)
        eq_zero_of_map_eq_zero' := fun _ =>
          (norm_eq_zero_iff <| zero_lt_one.trans_le hp.1).1 } with
    edist := edist
    edist_dist := Lp.edist_dist }

-- check no diamond is created
example [Fact (1 ≤ p)] : PseudoEMetricSpace.toEDist = (Lp.instEDist : EDist (Lp E p μ)) := by
  with_reducible_and_instances rfl

example [Fact (1 ≤ p)] : SeminormedAddGroup.toNNNorm = (Lp.instNNNorm : NNNorm (Lp E p μ)) := by
  with_reducible_and_instances rfl

section IsBoundedSMul

variable [NormedRing 𝕜] [NormedRing 𝕜'] [Module 𝕜 E] [Module 𝕜' E]
variable [IsBoundedSMul 𝕜 E] [IsBoundedSMul 𝕜' E]

theorem const_smul_mem_Lp (c : 𝕜) (f : Lp E p μ) : c • (f : α →ₘ[μ] E) ∈ Lp E p μ := by
  rw [mem_Lp_iff_eLpNorm_lt_top, eLpNorm_congr_ae (AEEqFun.coeFn_smul _ _)]
  exact eLpNorm_const_smul_le.trans_lt <| (by finiteness)

variable (𝕜 E p μ)

/-- The `𝕜`-submodule of elements of `α →ₘ[μ] E` whose `Lp` norm is finite.  This is `Lp E p μ`,
with extra structure. -/
def LpSubmodule : Submodule 𝕜 (α →ₘ[μ] E) :=
  { Lp E p μ with smul_mem' := fun c f hf => by simpa using const_smul_mem_Lp c ⟨f, hf⟩ }

variable {𝕜 E p μ}

theorem coe_LpSubmodule : (LpSubmodule 𝕜 E p μ).toAddSubgroup = Lp E p μ :=
  rfl

instance instModule : Module 𝕜 (Lp E p μ) :=
  { (LpSubmodule 𝕜 E p μ).module with }

theorem coeFn_smul (c : 𝕜) (f : Lp E p μ) : ⇑(c • f) =ᵐ[μ] c • ⇑f :=
  AEEqFun.coeFn_smul _ _

instance instIsCentralScalar [Module 𝕜ᵐᵒᵖ E] [IsBoundedSMul 𝕜ᵐᵒᵖ E] [IsCentralScalar 𝕜 E] :
    IsCentralScalar 𝕜 (Lp E p μ) where
  op_smul_eq_smul k f := Subtype.ext <| op_smul_eq_smul k (f : α →ₘ[μ] E)

instance instSMulCommClass [SMulCommClass 𝕜 𝕜' E] : SMulCommClass 𝕜 𝕜' (Lp E p μ) where
  smul_comm k k' f := Subtype.ext <| smul_comm k k' (f : α →ₘ[μ] E)

instance instIsScalarTower [SMul 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' E] : IsScalarTower 𝕜 𝕜' (Lp E p μ) where
  smul_assoc k k' f := Subtype.ext <| smul_assoc k k' (f : α →ₘ[μ] E)

instance instIsBoundedSMul [Fact (1 ≤ p)] : IsBoundedSMul 𝕜 (Lp E p μ) :=
  IsBoundedSMul.of_enorm_smul_le fun r f => by
    simpa only [eLpNorm_congr_ae (coeFn_smul _ _), enorm_def]
      using eLpNorm_const_smul_le (c := r) (f := f) (p := p)

end IsBoundedSMul

section NormedSpace

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]

instance instNormedSpace [Fact (1 ≤ p)] : NormedSpace 𝕜 (Lp E p μ) where
  norm_smul_le _ _ := norm_smul_le _ _

end NormedSpace

end Lp

namespace MemLp

variable {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

theorem toLp_const_smul {f : α → E} (c : 𝕜) (hf : MemLp f p μ) :
    (hf.const_smul c).toLp (c • f) = c • hf.toLp f :=
  rfl

end MemLp

variable {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]

theorem MemLp.enorm_rpow_div {f : α → ε} (hf : MemLp f p μ) (q : ℝ≥0∞) :
    MemLp (‖f ·‖ₑ ^ q.toReal) (p / q) μ := by
  refine ⟨(hf.1.enorm.pow_const q.toReal).aestronglyMeasurable, ?_⟩
  by_cases q_top : q = ∞
  · simp [q_top]
  by_cases q_zero : q = 0
  · simp only [q_zero, ENNReal.toReal_zero]
    by_cases p_zero : p = 0
    · simp [p_zero]
    rw [ENNReal.div_zero p_zero]
    simpa only [ENNReal.rpow_zero, eLpNorm_exponent_top] using (memLp_top_const_enorm (by simp)).2
  rw [eLpNorm_enorm_rpow _ (ENNReal.toReal_pos q_zero q_top)]
  apply ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg
  rw [ENNReal.ofReal_toReal q_top, div_eq_mul_inv, mul_assoc, ENNReal.inv_mul_cancel q_zero q_top,
    mul_one]
  exact hf.2.ne

theorem MemLp.norm_rpow_div {f : α → E} (hf : MemLp f p μ) (q : ℝ≥0∞) :
    MemLp (fun x : α => ‖f x‖ ^ q.toReal) (p / q) μ := by
  refine ⟨(hf.1.norm.aemeasurable.pow_const q.toReal).aestronglyMeasurable, ?_⟩
  by_cases q_top : q = ∞
  · simp [q_top]
  by_cases q_zero : q = 0
  · simp only [q_zero, ENNReal.toReal_zero, Real.rpow_zero]
    by_cases p_zero : p = 0
    · simp [p_zero]
    rw [ENNReal.div_zero p_zero]
    exact (memLp_top_const (1 : ℝ)).2
  rw [eLpNorm_norm_rpow _ (ENNReal.toReal_pos q_zero q_top)]
  apply ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg
  rw [ENNReal.ofReal_toReal q_top, div_eq_mul_inv, mul_assoc, ENNReal.inv_mul_cancel q_zero q_top,
    mul_one]
  exact hf.2.ne

theorem memLp_enorm_rpow_iff {q : ℝ≥0∞} {f : α → ε} (hf : AEStronglyMeasurable f μ) (q_zero : q ≠ 0)
    (q_top : q ≠ ∞) : MemLp (‖f ·‖ₑ ^ q.toReal) (p / q) μ ↔ MemLp f p μ := by
  refine ⟨fun h => ?_, fun h => h.enorm_rpow_div q⟩
  apply (memLp_enorm_iff hf).1
  convert h.enorm_rpow_div q⁻¹ using 1
  · ext x
    have : q.toReal * q.toReal⁻¹ = 1 :=
      CommGroupWithZero.mul_inv_cancel q.toReal <| ENNReal.toReal_ne_zero.mpr ⟨q_zero, q_top⟩
    simp [← ENNReal.rpow_mul, this, ENNReal.rpow_one]
  · rw [div_eq_mul_inv, inv_inv, div_eq_mul_inv, mul_assoc, ENNReal.inv_mul_cancel q_zero q_top,
      mul_one]

theorem memLp_norm_rpow_iff {q : ℝ≥0∞} {f : α → E} (hf : AEStronglyMeasurable f μ) (q_zero : q ≠ 0)
    (q_top : q ≠ ∞) : MemLp (fun x : α => ‖f x‖ ^ q.toReal) (p / q) μ ↔ MemLp f p μ := by
  refine ⟨fun h => ?_, fun h => h.norm_rpow_div q⟩
  apply (memLp_norm_iff hf).1
  convert h.norm_rpow_div q⁻¹ using 1
  · ext x
    rw [Real.norm_eq_abs, Real.abs_rpow_of_nonneg (norm_nonneg _), ← Real.rpow_mul (abs_nonneg _),
      ENNReal.toReal_inv, mul_inv_cancel₀, abs_of_nonneg (norm_nonneg _), Real.rpow_one]
    simp [ENNReal.toReal_eq_zero_iff, q_zero, q_top]
  · rw [div_eq_mul_inv, inv_inv, div_eq_mul_inv, mul_assoc, ENNReal.inv_mul_cancel q_zero q_top,
      mul_one]

theorem MemLp.enorm_rpow {f : α → ε} (hf : MemLp f p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    MemLp (fun x : α => ‖f x‖ₑ ^ p.toReal) 1 μ := by
  convert hf.enorm_rpow_div p
  rw [div_eq_mul_inv, ENNReal.mul_inv_cancel hp_ne_zero hp_ne_top]

theorem MemLp.norm_rpow {f : α → E} (hf : MemLp f p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    MemLp (fun x : α => ‖f x‖ ^ p.toReal) 1 μ := by
  convert hf.norm_rpow_div p
  rw [div_eq_mul_inv, ENNReal.mul_inv_cancel hp_ne_zero hp_ne_top]

theorem AEEqFun.compMeasurePreserving_mem_Lp {β : Type*} [MeasurableSpace β]
    {μb : MeasureTheory.Measure β} {g : β →ₘ[μb] E} (hg : g ∈ Lp E p μb) {f : α → β}
    (hf : MeasurePreserving f μ μb) :
    g.compMeasurePreserving f hf ∈ Lp E p μ := by
  rw [Lp.mem_Lp_iff_eLpNorm_lt_top] at hg ⊢
  rwa [eLpNorm_compMeasurePreserving]

namespace Lp

/-! ### Composition with a measure preserving function -/

variable {β : Type*} [MeasurableSpace β] {μb : MeasureTheory.Measure β} {f : α → β}

/-- Composition of an `L^p` function with a measure preserving function is an `L^p` function. -/
def compMeasurePreserving (f : α → β) (hf : MeasurePreserving f μ μb) :
    Lp E p μb →+ Lp E p μ where
  toFun g := ⟨g.1.compMeasurePreserving f hf, g.1.compMeasurePreserving_mem_Lp g.2 hf⟩
  map_zero' := rfl
  map_add' := by rintro ⟨⟨_⟩, _⟩ ⟨⟨_⟩, _⟩; rfl

@[simp]
theorem compMeasurePreserving_val (g : Lp E p μb) (hf : MeasurePreserving f μ μb) :
    (compMeasurePreserving f hf g).1 = g.1.compMeasurePreserving f hf :=
  rfl

theorem coeFn_compMeasurePreserving (g : Lp E p μb) (hf : MeasurePreserving f μ μb) :
    compMeasurePreserving f hf g =ᵐ[μ] g ∘ f :=
  g.1.coeFn_compMeasurePreserving hf

@[simp]
theorem norm_compMeasurePreserving (g : Lp E p μb) (hf : MeasurePreserving f μ μb) :
    ‖compMeasurePreserving f hf g‖ = ‖g‖ :=
  congr_arg ENNReal.toReal <| g.1.eLpNorm_compMeasurePreserving hf

theorem isometry_compMeasurePreserving [Fact (1 ≤ p)] (hf : MeasurePreserving f μ μb) :
    Isometry (compMeasurePreserving f hf : Lp E p μb → Lp E p μ) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_compMeasurePreserving · hf)

theorem toLp_compMeasurePreserving {g : β → E} (hg : MemLp g p μb) (hf : MeasurePreserving f μ μb) :
    compMeasurePreserving f hf (hg.toLp g) = (hg.comp_measurePreserving hf).toLp _ := rfl

variable (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- `MeasureTheory.Lp.compMeasurePreserving` as a linear map. -/
@[simps]
def compMeasurePreservingₗ (f : α → β) (hf : MeasurePreserving f μ μb) :
    Lp E p μb →ₗ[𝕜] Lp E p μ where
  __ := compMeasurePreserving f hf
  map_smul' c g := by rcases g with ⟨⟨_⟩, _⟩; rfl

/-- `MeasureTheory.Lp.compMeasurePreserving` as a linear isometry. -/
@[simps!]
def compMeasurePreservingₗᵢ [Fact (1 ≤ p)] (f : α → β) (hf : MeasurePreserving f μ μb) :
    Lp E p μb →ₗᵢ[𝕜] Lp E p μ where
  toLinearMap := compMeasurePreservingₗ 𝕜 f hf
  norm_map' := (norm_compMeasurePreserving · hf)

end Lp

end MeasureTheory

open MeasureTheory

/-!
### Composition on `L^p`

We show that Lipschitz functions vanishing at zero act by composition on `L^p`, and specialize
this to the composition with continuous linear maps, and to the definition of the positive
part of an `L^p` function.
-/


section Composition

variable {g : E → F} {c : ℝ≥0}

theorem LipschitzWith.comp_memLp {α E F} {K} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedAddCommGroup F] {f : α → E} {g : E → F} (hg : LipschitzWith K g)
    (g0 : g 0 = 0) (hL : MemLp f p μ) : MemLp (g ∘ f) p μ :=
  have : ∀ x, ‖g (f x)‖ ≤ K * ‖f x‖ := fun x ↦ by
    -- TODO: add `LipschitzWith.nnnorm_sub_le` and `LipschitzWith.nnnorm_le`
    simpa [g0] using hg.norm_sub_le (f x) 0
  hL.of_le_mul (hg.continuous.comp_aestronglyMeasurable hL.1) (Eventually.of_forall this)

theorem MeasureTheory.MemLp.of_comp_antilipschitzWith {α E F} {K'} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup E] [NormedAddCommGroup F] {f : α → E} {g : E → F}
    (hL : MemLp (g ∘ f) p μ) (hg : UniformContinuous g) (hg' : AntilipschitzWith K' g)
    (g0 : g 0 = 0) : MemLp f p μ := by
  have A : ∀ x, ‖f x‖ ≤ K' * ‖g (f x)‖ := by
    intro x
    -- TODO: add `AntilipschitzWith.le_mul_nnnorm_sub` and `AntilipschitzWith.le_mul_norm`
    rw [← dist_zero_right, ← dist_zero_right, ← g0]
    apply hg'.le_mul_dist
  have B : AEStronglyMeasurable f μ :=
    (hg'.isUniformEmbedding hg).isEmbedding.aestronglyMeasurable_comp_iff.1 hL.1
  exact hL.of_le_mul B (Filter.Eventually.of_forall A)

lemma MeasureTheory.MemLp.continuousLinearMap_comp [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] {f : α → E}
    (h_Lp : MemLp f p μ) (L : E →L[𝕜] F) :
    MemLp (fun x ↦ L (f x)) p μ :=
  LipschitzWith.comp_memLp L.lipschitz (by simp) h_Lp

namespace LipschitzWith

theorem memLp_comp_iff_of_antilipschitz {α E F} {K K'} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedAddCommGroup F] {f : α → E} {g : E → F} (hg : LipschitzWith K g)
    (hg' : AntilipschitzWith K' g) (g0 : g 0 = 0) : MemLp (g ∘ f) p μ ↔ MemLp f p μ :=
  ⟨fun h => h.of_comp_antilipschitzWith hg.uniformContinuous hg' g0, fun h => hg.comp_memLp g0 h⟩

/-- When `g` is a Lipschitz function sending `0` to `0` and `f` is in `Lp`, then `g ∘ f` is well
defined as an element of `Lp`. -/
def compLp (hg : LipschitzWith c g) (g0 : g 0 = 0) (f : Lp E p μ) : Lp F p μ :=
  ⟨AEEqFun.comp g hg.continuous (f : α →ₘ[μ] E), by
    suffices ∀ᵐ x ∂μ, ‖AEEqFun.comp g hg.continuous (f : α →ₘ[μ] E) x‖ ≤ c * ‖f x‖ from
      Lp.mem_Lp_of_ae_le_mul this
    filter_upwards [AEEqFun.coeFn_comp g hg.continuous (f : α →ₘ[μ] E)] with a ha
    simp only [ha]
    rw [← dist_zero_right, ← dist_zero_right, ← g0]
    exact hg.dist_le_mul (f a) 0⟩

theorem coeFn_compLp (hg : LipschitzWith c g) (g0 : g 0 = 0) (f : Lp E p μ) :
    hg.compLp g0 f =ᵐ[μ] g ∘ f :=
  AEEqFun.coeFn_comp _ hg.continuous _

@[simp]
theorem compLp_zero (hg : LipschitzWith c g) (g0 : g 0 = 0) : hg.compLp g0 (0 : Lp E p μ) = 0 := by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  apply (coeFn_compLp _ _ _).trans
  filter_upwards [Lp.coeFn_zero E p μ] with _ ha
  simp only [ha, g0, Function.comp_apply, Pi.zero_apply]

theorem norm_compLp_sub_le (hg : LipschitzWith c g) (g0 : g 0 = 0) (f f' : Lp E p μ) :
    ‖hg.compLp g0 f - hg.compLp g0 f'‖ ≤ c * ‖f - f'‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hg.coeFn_compLp g0 f, hg.coeFn_compLp g0 f',
    Lp.coeFn_sub (hg.compLp g0 f) (hg.compLp g0 f'), Lp.coeFn_sub f f'] with a ha1 ha2 ha3 ha4
  simp only [ha1, ha2, ha3, ha4, ← dist_eq_norm, Pi.sub_apply, Function.comp_apply]
  exact hg.dist_le_mul (f a) (f' a)

theorem norm_compLp_le (hg : LipschitzWith c g) (g0 : g 0 = 0) (f : Lp E p μ) :
    ‖hg.compLp g0 f‖ ≤ c * ‖f‖ := by
  -- squeezed for performance reasons
  simpa only [compLp_zero, sub_zero] using hg.norm_compLp_sub_le g0 f 0

theorem lipschitzWith_compLp [Fact (1 ≤ p)] (hg : LipschitzWith c g) (g0 : g 0 = 0) :
    LipschitzWith c (hg.compLp g0 : Lp E p μ → Lp F p μ) :=
  -- squeezed for performance reasons
  LipschitzWith.of_dist_le_mul fun f g => by simp only [dist_eq_norm, norm_compLp_sub_le]

theorem continuous_compLp [Fact (1 ≤ p)] (hg : LipschitzWith c g) (g0 : g 0 = 0) :
    Continuous (hg.compLp g0 : Lp E p μ → Lp F p μ) :=
  (lipschitzWith_compLp hg g0).continuous

end LipschitzWith

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

/-- Composing `f : Lp` with `L : E →L[𝕜] F`. -/
def compLp (L : E →L[𝕜] F) (f : Lp E p μ) : Lp F p μ :=
  L.lipschitz.compLp (map_zero L) f

theorem coeFn_compLp (L : E →L[𝕜] F) (f : Lp E p μ) : ∀ᵐ a ∂μ, (L.compLp f) a = L (f a) :=
  LipschitzWith.coeFn_compLp _ _ _

theorem coeFn_compLp' (L : E →L[𝕜] F) (f : Lp E p μ) : L.compLp f =ᵐ[μ] fun a => L (f a) :=
  L.coeFn_compLp f

theorem comp_memLp (L : E →L[𝕜] F) (f : Lp E p μ) : MemLp (L ∘ f) p μ :=
  (Lp.memLp (L.compLp f)).ae_eq (L.coeFn_compLp' f)

theorem comp_memLp' (L : E →L[𝕜] F) {f : α → E} (hf : MemLp f p μ) : MemLp (L ∘ f) p μ :=
  (L.comp_memLp (hf.toLp f)).ae_eq (EventuallyEq.fun_comp hf.coeFn_toLp _)

section RCLike

variable {K : Type*} [RCLike K]

theorem _root_.MeasureTheory.MemLp.ofReal {f : α → ℝ} (hf : MemLp f p μ) :
    MemLp (fun x => (f x : K)) p μ :=
  (@RCLike.ofRealCLM K _).comp_memLp' hf

theorem _root_.MeasureTheory.memLp_re_im_iff {f : α → K} :
    MemLp (fun x ↦ RCLike.re (f x)) p μ ∧ MemLp (fun x ↦ RCLike.im (f x)) p μ ↔
      MemLp f p μ := by
  refine ⟨?_, fun hf => ⟨hf.re, hf.im⟩⟩
  rintro ⟨hre, him⟩
  convert MeasureTheory.MemLp.add (ε := K) hre.ofReal (him.ofReal.const_mul RCLike.I)
  ext1 x
  rw [Pi.add_apply, mul_comm, RCLike.re_add_im]

end RCLike

theorem add_compLp (L L' : E →L[𝕜] F) (f : Lp E p μ) :
    (L + L').compLp f = L.compLp f + L'.compLp f := by
  ext1
  grw [Lp.coeFn_add, coeFn_compLp']
  refine
    EventuallyEq.trans ?_ (EventuallyEq.fun_add (L.coeFn_compLp' f).symm (L'.coeFn_compLp' f).symm)
  filter_upwards with x
  rw [coe_add', Pi.add_def]

theorem smul_compLp {𝕜'} [NormedRing 𝕜'] [Module 𝕜' F] [IsBoundedSMul 𝕜' F] [SMulCommClass 𝕜 𝕜' F]
    (c : 𝕜') (L : E →L[𝕜] F) (f : Lp E p μ) : (c • L).compLp f = c • L.compLp f := by
  ext1
  grw [Lp.coeFn_smul, coeFn_compLp']
  refine (L.coeFn_compLp' f).mono fun x hx => ?_
  rw [Pi.smul_apply, hx, coe_smul', Pi.smul_def]

theorem norm_compLp_le (L : E →L[𝕜] F) (f : Lp E p μ) : ‖L.compLp f‖ ≤ ‖L‖ * ‖f‖ :=
  LipschitzWith.norm_compLp_le _ _ _

variable (μ p)

/-- Composing `f : Lp E p μ` with `L : E →L[𝕜] F`, seen as a `𝕜`-linear map on `Lp E p μ`. -/
def compLpₗ (L : E →L[𝕜] F) : Lp E p μ →ₗ[𝕜] Lp F p μ where
  toFun f := L.compLp f
  map_add' f g := by
    ext1
    filter_upwards [Lp.coeFn_add f g, coeFn_compLp L (f + g), coeFn_compLp L f,
      coeFn_compLp L g, Lp.coeFn_add (L.compLp f) (L.compLp g)]
    intro a ha1 ha2 ha3 ha4 ha5
    simp only [ha1, ha2, ha3, ha4, ha5, map_add, Pi.add_apply]
  map_smul' c f := by
    dsimp
    ext1
    filter_upwards [Lp.coeFn_smul c f, coeFn_compLp L (c • f), Lp.coeFn_smul c (L.compLp f),
      coeFn_compLp L f] with _ ha1 ha2 ha3 ha4
    simp only [ha1, ha2, ha3, ha4, map_smul, Pi.smul_apply]

/-- Composing `f : Lp E p μ` with `L : E →L[𝕜] F`, seen as a continuous `𝕜`-linear map on
`Lp E p μ`. See also the similar
* `LinearMap.compLeft` for functions,
* `ContinuousLinearMap.compLeftContinuous` for continuous functions,
* `ContinuousLinearMap.compLeftContinuousBounded` for bounded continuous functions,
* `ContinuousLinearMap.compLeftContinuousCompact` for continuous functions on compact spaces.
-/
def compLpL [Fact (1 ≤ p)] (L : E →L[𝕜] F) : Lp E p μ →L[𝕜] Lp F p μ :=
  LinearMap.mkContinuous (L.compLpₗ p μ) ‖L‖ L.norm_compLp_le

variable {μ p}

theorem coeFn_compLpL [Fact (1 ≤ p)] (L : E →L[𝕜] F) (f : Lp E p μ) :
    L.compLpL p μ f =ᵐ[μ] fun a => L (f a) :=
  L.coeFn_compLp f

theorem add_compLpL [Fact (1 ≤ p)] (L L' : E →L[𝕜] F) :
    (L + L').compLpL p μ = L.compLpL p μ + L'.compLpL p μ := by ext1 f; exact add_compLp L L' f

theorem smul_compLpL [Fact (1 ≤ p)] {𝕜'} [NormedRing 𝕜'] [Module 𝕜' F] [IsBoundedSMul 𝕜' F]
    [SMulCommClass 𝕜 𝕜' F] (c : 𝕜') (L : E →L[𝕜] F) : (c • L).compLpL p μ = c • L.compLpL p μ := by
  ext1 f; exact smul_compLp c L f

theorem norm_compLpL_le [Fact (1 ≤ p)] (L : E →L[𝕜] F) : ‖L.compLpL p μ‖ ≤ ‖L‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

end ContinuousLinearMap

namespace MeasureTheory.Lp

section PosPart

theorem lipschitzWith_pos_part : LipschitzWith 1 fun x : ℝ => max x 0 :=
  LipschitzWith.id.max_const _

theorem _root_.MeasureTheory.MemLp.pos_part {f : α → ℝ} (hf : MemLp f p μ) :
    MemLp (fun x => max (f x) 0) p μ :=
  lipschitzWith_pos_part.comp_memLp (max_eq_right le_rfl) hf

theorem _root_.MeasureTheory.MemLp.neg_part {f : α → ℝ} (hf : MemLp f p μ) :
    MemLp (fun x => max (-f x) 0) p μ :=
  lipschitzWith_pos_part.comp_memLp (max_eq_right le_rfl) hf.neg

/-- Positive part of a function in `L^p`. -/
def posPart (f : Lp ℝ p μ) : Lp ℝ p μ :=
  lipschitzWith_pos_part.compLp (max_eq_right le_rfl) f

/-- Negative part of a function in `L^p`. -/
def negPart (f : Lp ℝ p μ) : Lp ℝ p μ :=
  posPart (-f)

@[norm_cast]
theorem coe_posPart (f : Lp ℝ p μ) : (posPart f : α →ₘ[μ] ℝ) = (f : α →ₘ[μ] ℝ).posPart :=
  rfl

theorem coeFn_posPart (f : Lp ℝ p μ) : ⇑(posPart f) =ᵐ[μ] fun a => max (f a) 0 :=
  AEEqFun.coeFn_posPart _

theorem coeFn_negPart_eq_max (f : Lp ℝ p μ) : ∀ᵐ a ∂μ, negPart f a = max (-f a) 0 := by
  rw [negPart]
  filter_upwards [coeFn_posPart (-f), coeFn_neg f] with _ h₁ h₂
  rw [h₁, h₂, Pi.neg_apply]

theorem coeFn_negPart (f : Lp ℝ p μ) : ∀ᵐ a ∂μ, negPart f a = -min (f a) 0 :=
  (coeFn_negPart_eq_max f).mono fun a h => by rw [h, ← max_neg_neg, neg_zero]

theorem continuous_posPart [Fact (1 ≤ p)] : Continuous fun f : Lp ℝ p μ => posPart f :=
  LipschitzWith.continuous_compLp _ _

theorem continuous_negPart [Fact (1 ≤ p)] : Continuous fun f : Lp ℝ p μ => negPart f := by
  unfold negPart
  exact continuous_posPart.comp continuous_neg

end PosPart

end MeasureTheory.Lp

end Composition

namespace MeasureTheory.Lp

/-- A version of **Markov's inequality** with elements of Lp. -/
lemma pow_mul_meas_ge_le_enorm (f : Lp E p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) (ε : ℝ≥0∞) :
    (ε * μ {x | ε ≤ ‖f x‖ₑ ^ p.toReal}) ^ (1 / p.toReal) ≤ ENNReal.ofReal ‖f‖ :=
  (ENNReal.ofReal_toReal (eLpNorm_ne_top f)).symm ▸
    pow_mul_meas_ge_le_eLpNorm μ hp_ne_zero hp_ne_top (Lp.aestronglyMeasurable f) ε

/-- A version of **Markov's inequality** with elements of Lp. -/
lemma mul_meas_ge_le_pow_enorm (f : Lp E p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) (ε : ℝ≥0∞) :
    ε * μ {x | ε ≤ ‖f x‖ₑ ^ p.toReal} ≤ ENNReal.ofReal ‖f‖ ^ p.toReal :=
  (ENNReal.ofReal_toReal (eLpNorm_ne_top f)).symm ▸
    mul_meas_ge_le_pow_eLpNorm μ hp_ne_zero hp_ne_top (Lp.aestronglyMeasurable f) ε

/-- A version of **Markov's inequality** with elements of Lp. -/
theorem mul_meas_ge_le_pow_enorm' (f : Lp E p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (ε : ℝ≥0∞) : ε ^ p.toReal * μ {x | ε ≤ ‖f x‖₊ } ≤ ENNReal.ofReal ‖f‖ ^ p.toReal :=
  (ENNReal.ofReal_toReal (eLpNorm_ne_top f)).symm ▸
    mul_meas_ge_le_pow_eLpNorm' μ hp_ne_zero hp_ne_top (Lp.aestronglyMeasurable f) ε

/-- A version of **Markov's inequality** with elements of Lp. -/
theorem meas_ge_le_mul_pow_enorm (f : Lp E p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) {ε : ℝ≥0∞}
    (hε : ε ≠ 0) : μ {x | ε ≤ ‖f x‖₊} ≤ ε⁻¹ ^ p.toReal * ENNReal.ofReal ‖f‖ ^ p.toReal :=
  (ENNReal.ofReal_toReal (eLpNorm_ne_top f)).symm ▸
    meas_ge_le_mul_pow_eLpNorm_enorm μ hp_ne_zero hp_ne_top (Lp.aestronglyMeasurable f) hε (by simp)

section Star

variable {R : Type*} [NormedAddCommGroup R] [StarAddMonoid R] [NormedStarGroup R]

protected noncomputable instance {p : ℝ≥0∞} : Star (Lp R p μ) where
  star f := ⟨star (f : α →ₘ[μ] R),
    by simpa [Lp.mem_Lp_iff_eLpNorm_lt_top] using Lp.eLpNorm_lt_top f⟩

lemma coeFn_star {p : ℝ≥0∞} (f : Lp R p μ) : (star f : Lp R p μ) =ᵐ[μ] star f :=
    (f : α →ₘ[μ] R).coeFn_star

noncomputable instance {p : ℝ≥0∞} : InvolutiveStar (Lp R p μ) where
  star_involutive _ := Subtype.ext <| star_involutive _

noncomputable instance [TrivialStar R] {p : ℝ≥0∞} : TrivialStar (Lp R p μ) where
  star_trivial _ := Subtype.ext <| star_trivial _

end Star

end MeasureTheory.Lp
