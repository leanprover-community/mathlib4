/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
import Mathlib.Analysis.Normed.Group.Hom
import Mathlib.Analysis.NormedSpace.IndicatorFunction
import Mathlib.Analysis.NormedSpace.OperatorNorm.NNNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Order.Filter.IndicatorFunction

/-!
# Lp space

This file provides the space `Lp E p μ` as the subtype of elements of `α →ₘ[μ] E` (see ae_eq_fun)
such that `eLpNorm f p μ` is finite. For `1 ≤ p`, `eLpNorm` defines a norm and `Lp` is a complete
metric space.

## Main definitions

* `Lp E p μ` : elements of `α →ₘ[μ] E` (see ae_eq_fun) such that `eLpNorm f p μ` is finite. Defined
  as an `AddSubgroup` of `α →ₘ[μ] E`.

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

open TopologicalSpace MeasureTheory Filter
open scoped NNReal ENNReal Topology symmDiff

variable {α 𝕜 𝕜' E F G : Type*} {m m0 : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ} {μ ν : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]

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

@[deprecated (since := "2025-02-21")]
alias Memℒp.eLpNorm_mk_lt_top := MemLp.eLpNorm_mk_lt_top

/-- Lp space -/
def Lp {α} (E : Type*) {m : MeasurableSpace α} [NormedAddCommGroup E] (p : ℝ≥0∞)
    (μ : Measure α := by volume_tac) : AddSubgroup (α →ₘ[μ] E) where
  carrier := { f | eLpNorm f p μ < ∞ }
  zero_mem' := by simp [eLpNorm_congr_ae AEEqFun.coeFn_zero, eLpNorm_zero]
  add_mem' {f g} hf hg := by
    simp [eLpNorm_congr_ae (AEEqFun.coeFn_add f g),
      eLpNorm_add_lt_top ⟨f.aestronglyMeasurable, hf⟩ ⟨g.aestronglyMeasurable, hg⟩]
  neg_mem' {f} hf := by rwa [Set.mem_setOf_eq, eLpNorm_congr_ae (AEEqFun.coeFn_neg f), eLpNorm_neg]

scoped notation:25 α' " →₁[" μ "] " E => MeasureTheory.Lp (α := α') E 1 μ
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

@[deprecated (since := "2025-02-21")]
alias mem_Lp_iff_memℒp := mem_Lp_iff_memLp

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
  cases f
  simp [MemLp.toLp]

theorem eLpNorm_lt_top (f : Lp E p μ) : eLpNorm f p μ < ∞ :=
  f.prop

theorem eLpNorm_ne_top (f : Lp E p μ) : eLpNorm f p μ ≠ ∞ :=
  (eLpNorm_lt_top f).ne

@[measurability]
protected theorem stronglyMeasurable (f : Lp E p μ) : StronglyMeasurable f :=
  f.val.stronglyMeasurable

@[measurability]
protected theorem aestronglyMeasurable (f : Lp E p μ) : AEStronglyMeasurable f μ :=
  f.val.aestronglyMeasurable

protected theorem memLp (f : Lp E p μ) : MemLp f p μ :=
  ⟨Lp.aestronglyMeasurable f, f.prop⟩

@[deprecated (since := "2025-02-21")]
alias memℒp := Lp.memLp

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

@[deprecated (since := "2025-01-20")] alias nnnorm_coe_ennreal := enorm_def

@[simp]
lemma norm_toLp (f : α → E) (hf : MemLp f p μ) : ‖hf.toLp f‖ = ENNReal.toReal (eLpNorm f p μ) := by
  rw [norm_def, eLpNorm_congr_ae (MemLp.coeFn_toLp hf)]

@[simp]
theorem nnnorm_toLp (f : α → E) (hf : MemLp f p μ) :
    ‖hf.toLp f‖₊ = ENNReal.toNNReal (eLpNorm f p μ) :=
  NNReal.eq <| norm_toLp f hf

lemma enorm_toLp {f : α → E} (hf : MemLp f p μ) : ‖hf.toLp f‖ₑ = eLpNorm f p μ := by
  simp [enorm, nnnorm_toLp f hf, ENNReal.coe_toNNReal hf.2.ne]

@[deprecated (since := "2025-01-20")] alias coe_nnnorm_toLp := enorm_toLp

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
  · exact (Lp.memLp _).eLpNorm_ne_top
  · exact ENNReal.mul_ne_top ENNReal.coe_ne_top (Lp.memLp _).eLpNorm_ne_top

theorem norm_le_mul_norm_of_ae_le_mul {c : ℝ} {f : Lp E p μ} {g : Lp F p μ}
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) : ‖f‖ ≤ c * ‖g‖ := by
  rcases le_or_lt 0 c with hc | hc
  · lift c to ℝ≥0 using hc
    exact NNReal.coe_le_coe.mpr (nnnorm_le_mul_nnnorm_of_ae_le_mul h)
  · simp only [norm_def]
    have := eLpNorm_eq_zero_and_zero_of_ae_le_mul_neg h hc p
    simp [this]

theorem norm_le_norm_of_ae_le {f : Lp E p μ} {g : Lp F p μ} (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
    ‖f‖ ≤ ‖g‖ := by
  rw [norm_def, norm_def]
  exact ENNReal.toReal_mono (eLpNorm_ne_top _) (eLpNorm_mono_ae h)

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
    · simp [hμ, nnnorm_def, Real.zero_rpow hp]
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
  exact eLpNorm_const_smul_le.trans_lt <| ENNReal.mul_lt_top ENNReal.coe_lt_top f.prop

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
  -- TODO: add `IsBoundedSMul.of_nnnorm_smul_le`
  IsBoundedSMul.of_norm_smul_le fun r f => by
    suffices ‖r • f‖ₑ ≤ ‖r‖ₑ * ‖f‖ₑ by
      -- squeezed for performance reasons
      simpa only [ge_iff_le, enorm, ←ENNReal.coe_mul, ENNReal.coe_le_coe] using this
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

/-! ### Indicator of a set as an element of Lᵖ

For a set `s` with `(hs : MeasurableSet s)` and `(hμs : μ s < ∞)`, we build
`indicatorConstLp p hs hμs c`, the element of `Lp` corresponding to `s.indicator (fun _ => c)`.
-/

/-- The `ℒ^p` norm of the indicator of a set is uniformly small if the set itself has small measure,
for any `p < ∞`. Given here as an existential `∀ ε > 0, ∃ η > 0, ...` to avoid later
management of `ℝ≥0∞`-arithmetic. -/
theorem exists_eLpNorm_indicator_le (hp : p ≠ ∞) (c : E) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ η : ℝ≥0, 0 < η ∧ ∀ s : Set α, μ s ≤ η → eLpNorm (s.indicator fun _ => c) p μ ≤ ε := by
  rcases eq_or_ne p 0 with (rfl | h'p)
  · exact ⟨1, zero_lt_one, fun s _ => by simp⟩
  have hp₀ : 0 < p := bot_lt_iff_ne_bot.2 h'p
  have hp₀' : 0 ≤ 1 / p.toReal := div_nonneg zero_le_one ENNReal.toReal_nonneg
  have hp₀'' : 0 < p.toReal := ENNReal.toReal_pos hp₀.ne' hp
  obtain ⟨η, hη_pos, hη_le⟩ : ∃ η : ℝ≥0, 0 < η ∧ ‖c‖ₑ * (η : ℝ≥0∞) ^ (1 / p.toReal) ≤ ε := by
    have :
      Filter.Tendsto (fun x : ℝ≥0 => ((‖c‖₊ * x ^ (1 / p.toReal) : ℝ≥0) : ℝ≥0∞)) (𝓝 0)
        (𝓝 (0 : ℝ≥0)) := by
      rw [ENNReal.tendsto_coe]
      convert (NNReal.continuousAt_rpow_const (Or.inr hp₀')).tendsto.const_mul _
      simp [hp₀''.ne']
    have hε' : 0 < ε := hε.bot_lt
    obtain ⟨δ, hδ, hδε'⟩ := NNReal.nhds_zero_basis.eventually_iff.mp (this.eventually_le_const hε')
    obtain ⟨η, hη, hηδ⟩ := exists_between hδ
    refine ⟨η, hη, ?_⟩
    simpa only [← ENNReal.coe_rpow_of_nonneg _ hp₀', enorm, ← ENNReal.coe_mul] using hδε' hηδ
  refine ⟨η, hη_pos, fun s hs => ?_⟩
  refine (eLpNorm_indicator_const_le _ _).trans (le_trans ?_ hη_le)
  exact mul_le_mul_left' (ENNReal.rpow_le_rpow hs hp₀') _

section Topology
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ]

/-- A bounded measurable function with compact support is in L^p. -/
theorem _root_.HasCompactSupport.memLp_of_bound {f : X → E} (hf : HasCompactSupport f)
    (h2f : AEStronglyMeasurable f μ) (C : ℝ) (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : MemLp f p μ := by
  have := memLp_top_of_bound h2f C hfC
  exact this.mono_exponent_of_measure_support_ne_top
    (fun x ↦ image_eq_zero_of_nmem_tsupport) (hf.measure_lt_top.ne) le_top

@[deprecated (since := "2025-02-21")]
alias _root_.HasCompactSupport.memℒp_of_bound := _root_.HasCompactSupport.memLp_of_bound

/-- A continuous function with compact support is in L^p. -/
theorem _root_.Continuous.memLp_of_hasCompactSupport [OpensMeasurableSpace X]
    {f : X → E} (hf : Continuous f) (h'f : HasCompactSupport f) : MemLp f p μ := by
  have := hf.memLp_top_of_hasCompactSupport h'f μ
  exact this.mono_exponent_of_measure_support_ne_top
    (fun x ↦ image_eq_zero_of_nmem_tsupport) (h'f.measure_lt_top.ne) le_top

@[deprecated (since := "2025-02-21")]
alias _root_.Continuous.memℒp_of_hasCompactSupport := _root_.Continuous.memLp_of_hasCompactSupport

end Topology

section IndicatorConstLp

open Set Function

variable {s : Set α} {hs : MeasurableSet s} {hμs : μ s ≠ ∞} {c : E}

/-- Indicator of a set as an element of `Lp`. -/
def indicatorConstLp (p : ℝ≥0∞) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) : Lp E p μ :=
  MemLp.toLp (s.indicator fun _ => c) (memLp_indicator_const p hs c (Or.inr hμs))

/-- A version of `Set.indicator_add` for `MeasureTheory.indicatorConstLp` -/
theorem indicatorConstLp_add {c' : E} :
    indicatorConstLp p hs hμs c + indicatorConstLp p hs hμs c' =
    indicatorConstLp p hs hμs (c + c') := by
  simp_rw [indicatorConstLp, ← MemLp.toLp_add, indicator_add]
  rfl

/-- A version of `Set.indicator_sub` for `MeasureTheory.indicatorConstLp` -/
theorem indicatorConstLp_sub {c' : E} :
    indicatorConstLp p hs hμs c - indicatorConstLp p hs hμs c' =
    indicatorConstLp p hs hμs (c - c') := by
  simp_rw [indicatorConstLp, ← MemLp.toLp_sub, indicator_sub]
  rfl

theorem indicatorConstLp_coeFn : ⇑(indicatorConstLp p hs hμs c) =ᵐ[μ] s.indicator fun _ => c :=
  MemLp.coeFn_toLp (memLp_indicator_const p hs c (Or.inr hμs))

theorem indicatorConstLp_coeFn_mem : ∀ᵐ x : α ∂μ, x ∈ s → indicatorConstLp p hs hμs c x = c :=
  indicatorConstLp_coeFn.mono fun _x hx hxs => hx.trans (Set.indicator_of_mem hxs _)

theorem indicatorConstLp_coeFn_nmem : ∀ᵐ x : α ∂μ, x ∉ s → indicatorConstLp p hs hμs c x = 0 :=
  indicatorConstLp_coeFn.mono fun _x hx hxs => hx.trans (Set.indicator_of_not_mem hxs _)

theorem norm_indicatorConstLp (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    ‖indicatorConstLp p hs hμs c‖ = ‖c‖ * (μ s).toReal ^ (1 / p.toReal) := by
  rw [Lp.norm_def, eLpNorm_congr_ae indicatorConstLp_coeFn,
    eLpNorm_indicator_const hs hp_ne_zero hp_ne_top, ENNReal.toReal_mul, ENNReal.toReal_rpow,
    toReal_enorm]

theorem norm_indicatorConstLp_top (hμs_ne_zero : μ s ≠ 0) :
    ‖indicatorConstLp ∞ hs hμs c‖ = ‖c‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae indicatorConstLp_coeFn,
    eLpNorm_indicator_const' hs hμs_ne_zero ENNReal.top_ne_zero, ENNReal.toReal_top,
    _root_.div_zero, ENNReal.rpow_zero, mul_one, toReal_enorm]

theorem norm_indicatorConstLp' (hp_pos : p ≠ 0) (hμs_pos : μ s ≠ 0) :
    ‖indicatorConstLp p hs hμs c‖ = ‖c‖ * (μ s).toReal ^ (1 / p.toReal) := by
  by_cases hp_top : p = ∞
  · rw [hp_top, ENNReal.toReal_top, _root_.div_zero, Real.rpow_zero, mul_one]
    exact norm_indicatorConstLp_top hμs_pos
  · exact norm_indicatorConstLp hp_pos hp_top

theorem norm_indicatorConstLp_le :
    ‖indicatorConstLp p hs hμs c‖ ≤ ‖c‖ * (μ s).toReal ^ (1 / p.toReal) := by
  rw [indicatorConstLp, Lp.norm_toLp]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  refine (eLpNorm_indicator_const_le _ _).trans_eq ?_
  rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ENNReal.toReal_rpow, ENNReal.ofReal_toReal]
  exact ENNReal.rpow_ne_top_of_nonneg (by positivity) hμs

theorem nnnorm_indicatorConstLp_le :
    ‖indicatorConstLp p hs hμs c‖₊ ≤ ‖c‖₊ * (μ s).toNNReal ^ (1 / p.toReal) :=
  norm_indicatorConstLp_le

theorem enorm_indicatorConstLp_le :
    ‖indicatorConstLp p hs hμs c‖ₑ ≤ ‖c‖ₑ * μ s ^ (1 / p.toReal) := by
  simpa [ENNReal.coe_rpow_of_nonneg, ENNReal.coe_toNNReal hμs, Lp.enorm_def, ← enorm_eq_nnnorm]
    using ENNReal.coe_le_coe.2 <| nnnorm_indicatorConstLp_le (c := c) (hμs := hμs)

@[deprecated (since := "2025-01-20")] alias ennnorm_indicatorConstLp_le := enorm_indicatorConstLp_le

theorem edist_indicatorConstLp_eq_enorm {t : Set α} {ht : MeasurableSet t} {hμt : μ t ≠ ∞} :
    edist (indicatorConstLp p hs hμs c) (indicatorConstLp p ht hμt c) =
      ‖indicatorConstLp p (hs.symmDiff ht) (measure_symmDiff_ne_top hμs hμt) c‖ₑ := by
  unfold indicatorConstLp
  rw [Lp.edist_toLp_toLp, eLpNorm_indicator_sub_indicator, Lp.enorm_toLp]

@[deprecated (since := "2025-01-20")]
alias edist_indicatorConstLp_eq_nnnorm := edist_indicatorConstLp_eq_enorm

theorem dist_indicatorConstLp_eq_norm {t : Set α} {ht : MeasurableSet t} {hμt : μ t ≠ ∞} :
    dist (indicatorConstLp p hs hμs c) (indicatorConstLp p ht hμt c) =
      ‖indicatorConstLp p (hs.symmDiff ht) (measure_symmDiff_ne_top hμs hμt) c‖ := by
  -- Squeezed for performance reasons
  simp only [Lp.dist_edist, edist_indicatorConstLp_eq_enorm, enorm, ENNReal.coe_toReal,
    Lp.coe_nnnorm]

/-- A family of `indicatorConstLp` functions tends to an `indicatorConstLp`,
if the underlying sets tend to the set in the sense of the measure of the symmetric difference. -/
theorem tendsto_indicatorConstLp_set [hp₁ : Fact (1 ≤ p)] {β : Type*} {l : Filter β} {t : β → Set α}
    {ht : ∀ b, MeasurableSet (t b)} {hμt : ∀ b, μ (t b) ≠ ∞} (hp : p ≠ ∞)
    (h : Tendsto (fun b ↦ μ (t b ∆ s)) l (𝓝 0)) :
    Tendsto (fun b ↦ indicatorConstLp p (ht b) (hμt b) c) l (𝓝 (indicatorConstLp p hs hμs c)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hp₀ : p ≠ 0 := (one_pos.trans_le hp₁.out).ne'
  simp only [dist_indicatorConstLp_eq_norm, norm_indicatorConstLp hp₀ hp]
  convert tendsto_const_nhds.mul
    (((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h).rpow_const _)
  · simp [Real.rpow_eq_zero_iff_of_nonneg, ENNReal.toReal_eq_zero_iff, hp, hp₀]
  · simp

/-- A family of `indicatorConstLp` functions is continuous in the parameter,
if `μ (s y ∆ s x)` tends to zero as `y` tends to `x` for all `x`. -/
theorem continuous_indicatorConstLp_set [Fact (1 ≤ p)] {X : Type*} [TopologicalSpace X]
    {s : X → Set α} {hs : ∀ x, MeasurableSet (s x)} {hμs : ∀ x, μ (s x) ≠ ∞} (hp : p ≠ ∞)
    (h : ∀ x, Tendsto (fun y ↦ μ (s y ∆ s x)) (𝓝 x) (𝓝 0)) :
    Continuous fun x ↦ indicatorConstLp p (hs x) (hμs x) c :=
  continuous_iff_continuousAt.2 fun x ↦ tendsto_indicatorConstLp_set hp (h x)

@[simp]
theorem indicatorConstLp_empty :
    indicatorConstLp p MeasurableSet.empty (by simp : μ ∅ ≠ ∞) c = 0 := by
  simp only [indicatorConstLp, Set.indicator_empty', MemLp.toLp_zero]

theorem indicatorConstLp_inj {s t : Set α} (hs : MeasurableSet s) (hsμ : μ s ≠ ∞)
    (ht : MeasurableSet t) (htμ : μ t ≠ ∞) {c : E} (hc : c ≠ 0) :
    indicatorConstLp p hs hsμ c = indicatorConstLp p ht htμ c ↔ s =ᵐ[μ] t := by
  simp_rw [← indicator_const_eventuallyEq hc, indicatorConstLp, MemLp.toLp_eq_toLp_iff]

theorem memLp_add_of_disjoint {f g : α → E} (h : Disjoint (support f) (support g))
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    MemLp (f + g) p μ ↔ MemLp f p μ ∧ MemLp g p μ := by
  borelize E
  refine ⟨fun hfg => ⟨?_, ?_⟩, fun h => h.1.add h.2⟩
  · rw [← Set.indicator_add_eq_left h]; exact hfg.indicator (measurableSet_support hf.measurable)
  · rw [← Set.indicator_add_eq_right h]; exact hfg.indicator (measurableSet_support hg.measurable)

@[deprecated (since := "2025-02-21")]
alias memℒp_add_of_disjoint := memLp_add_of_disjoint

/-- The indicator of a disjoint union of two sets is the sum of the indicators of the sets. -/
theorem indicatorConstLp_disjoint_union {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) (hst : Disjoint s t) (c : E) :
    indicatorConstLp p (hs.union ht) (measure_union_ne_top hμs hμt) c =
      indicatorConstLp p hs hμs c + indicatorConstLp p ht hμt c := by
  ext1
  refine indicatorConstLp_coeFn.trans (EventuallyEq.trans ?_ (Lp.coeFn_add _ _).symm)
  refine
    EventuallyEq.trans ?_
      (EventuallyEq.add indicatorConstLp_coeFn.symm indicatorConstLp_coeFn.symm)
  rw [Set.indicator_union_of_disjoint hst]

end IndicatorConstLp

section const

variable (μ p)
variable [IsFiniteMeasure μ] (c : E)

/-- Constant function as an element of `MeasureTheory.Lp` for a finite measure. -/
protected def Lp.const : E →+ Lp E p μ where
  toFun c := ⟨AEEqFun.const α c, const_mem_Lp α μ c⟩
  map_zero' := rfl
  map_add' _ _ := rfl

lemma Lp.coeFn_const : Lp.const p μ c =ᵐ[μ] Function.const α c :=
  AEEqFun.coeFn_const α c

@[simp] lemma Lp.const_val : (Lp.const p μ c).1 = AEEqFun.const α c := rfl

@[simp]
lemma MemLp.toLp_const : MemLp.toLp _ (memLp_const c) = Lp.const p μ c := rfl

@[deprecated (since := "2025-02-21")]
alias Memℒp.toLp_const := MemLp.toLp_const

@[simp]
lemma indicatorConstLp_univ :
    indicatorConstLp p .univ (measure_ne_top μ _) c = Lp.const p μ c := by
  rw [← MemLp.toLp_const, indicatorConstLp]
  simp only [Set.indicator_univ, Function.const]

theorem Lp.norm_const [NeZero μ] (hp_zero : p ≠ 0) :
    ‖Lp.const p μ c‖ = ‖c‖ * (μ Set.univ).toReal ^ (1 / p.toReal) := by
  have := NeZero.ne μ
  rw [← MemLp.toLp_const, Lp.norm_toLp, eLpNorm_const] <;> try assumption
  rw [ENNReal.toReal_mul, toReal_enorm, ← ENNReal.toReal_rpow]

theorem Lp.norm_const' (hp_zero : p ≠ 0) (hp_top : p ≠ ∞) :
    ‖Lp.const p μ c‖ = ‖c‖ * (μ Set.univ).toReal ^ (1 / p.toReal) := by
  rw [← MemLp.toLp_const, Lp.norm_toLp, eLpNorm_const'] <;> try assumption
  rw [ENNReal.toReal_mul, toReal_enorm, ← ENNReal.toReal_rpow]

theorem Lp.norm_const_le : ‖Lp.const p μ c‖ ≤ ‖c‖ * (μ Set.univ).toReal ^ (1 / p.toReal) := by
  rw [← indicatorConstLp_univ]
  exact norm_indicatorConstLp_le

/-- `MeasureTheory.Lp.const` as a `LinearMap`. -/
@[simps] protected def Lp.constₗ (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] :
    E →ₗ[𝕜] Lp E p μ where
  toFun := Lp.const p μ
  map_add' := map_add _
  map_smul' _ _ := rfl

@[simps! apply]
protected def Lp.constL (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 E] [Fact (1 ≤ p)] :
    E →L[𝕜] Lp E p μ :=
  (Lp.constₗ p μ 𝕜).mkContinuous ((μ Set.univ).toReal ^ (1 / p.toReal)) fun _ ↦
    (Lp.norm_const_le _ _ _).trans_eq (mul_comm _ _)

theorem Lp.norm_constL_le (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
    [Fact (1 ≤ p)] :
    ‖(Lp.constL p μ 𝕜 : E →L[𝕜] Lp E p μ)‖ ≤ (μ Set.univ).toReal ^ (1 / p.toReal) :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

end const

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

@[deprecated (since := "2025-02-21")]
alias Memℒp.norm_rpow_div := MemLp.norm_rpow_div

theorem memLp_norm_rpow_iff {q : ℝ≥0∞} {f : α → E} (hf : AEStronglyMeasurable f μ) (q_zero : q ≠ 0)
    (q_top : q ≠ ∞) : MemLp (fun x : α => ‖f x‖ ^ q.toReal) (p / q) μ ↔ MemLp f p μ := by
  refine ⟨fun h => ?_, fun h => h.norm_rpow_div q⟩
  apply (memLp_norm_iff hf).1
  convert h.norm_rpow_div q⁻¹ using 1
  · ext x
    rw [Real.norm_eq_abs, Real.abs_rpow_of_nonneg (norm_nonneg _), ← Real.rpow_mul (abs_nonneg _),
      ENNReal.toReal_inv, mul_inv_cancel₀, abs_of_nonneg (norm_nonneg _), Real.rpow_one]
    simp [ENNReal.toReal_eq_zero_iff, not_or, q_zero, q_top]
  · rw [div_eq_mul_inv, inv_inv, div_eq_mul_inv, mul_assoc, ENNReal.inv_mul_cancel q_zero q_top,
      mul_one]

@[deprecated (since := "2025-02-21")]
alias memℒp_norm_rpow_iff := memLp_norm_rpow_iff

theorem MemLp.norm_rpow {f : α → E} (hf : MemLp f p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    MemLp (fun x : α => ‖f x‖ ^ p.toReal) 1 μ := by
  convert hf.norm_rpow_div p
  rw [div_eq_mul_inv, ENNReal.mul_inv_cancel hp_ne_zero hp_ne_top]

@[deprecated (since := "2025-02-21")]
alias Memℒp.norm_rpow := MemLp.norm_rpow

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

theorem indicatorConstLp_compMeasurePreserving {s : Set β} (hs : MeasurableSet s)
    (hμs : μb s ≠ ∞) (c : E) (hf : MeasurePreserving f μ μb) :
    Lp.compMeasurePreserving f hf (indicatorConstLp p hs hμs c) =
      indicatorConstLp p (hs.preimage hf.measurable)
        (by rwa [hf.measure_preimage hs.nullMeasurableSet]) c :=
  rfl

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

@[deprecated (since := "2025-02-21")]
alias LipschitzWith.comp_memℒp := LipschitzWith.comp_memLp

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

@[deprecated (since := "2025-02-21")]
alias MeasureTheory.Memℒp.of_comp_antilipschitzWith := MeasureTheory.MemLp.of_comp_antilipschitzWith

namespace LipschitzWith

theorem memLp_comp_iff_of_antilipschitz {α E F} {K K'} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedAddCommGroup F] {f : α → E} {g : E → F} (hg : LipschitzWith K g)
    (hg' : AntilipschitzWith K' g) (g0 : g 0 = 0) : MemLp (g ∘ f) p μ ↔ MemLp f p μ :=
  ⟨fun h => h.of_comp_antilipschitzWith hg.uniformContinuous hg' g0, fun h => hg.comp_memLp g0 h⟩

@[deprecated (since := "2025-02-21")]
alias memℒp_comp_iff_of_antilipschitz := memLp_comp_iff_of_antilipschitz

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

@[deprecated (since := "2025-02-21")]
alias comp_memℒp := comp_memLp

theorem comp_memLp' (L : E →L[𝕜] F) {f : α → E} (hf : MemLp f p μ) : MemLp (L ∘ f) p μ :=
  (L.comp_memLp (hf.toLp f)).ae_eq (EventuallyEq.fun_comp hf.coeFn_toLp _)

@[deprecated (since := "2025-02-21")]
alias comp_memℒp' := comp_memLp'

section RCLike

variable {K : Type*} [RCLike K]

theorem _root_.MeasureTheory.MemLp.ofReal {f : α → ℝ} (hf : MemLp f p μ) :
    MemLp (fun x => (f x : K)) p μ :=
  (@RCLike.ofRealCLM K _).comp_memLp' hf

@[deprecated (since := "2025-02-21")]
alias _root_.MeasureTheory.Memℒp.ofReal := _root_.MeasureTheory.MemLp.ofReal

theorem _root_.MeasureTheory.memLp_re_im_iff {f : α → K} :
    MemLp (fun x ↦ RCLike.re (f x)) p μ ∧ MemLp (fun x ↦ RCLike.im (f x)) p μ ↔
      MemLp f p μ := by
  refine ⟨?_, fun hf => ⟨hf.re, hf.im⟩⟩
  rintro ⟨hre, him⟩
  convert MeasureTheory.MemLp.add (E := K) hre.ofReal (him.ofReal.const_mul RCLike.I)
  ext1 x
  rw [Pi.add_apply, mul_comm, RCLike.re_add_im]

@[deprecated (since := "2025-02-21")]
alias _root_.MeasureTheory.memℒp_re_im_iff := _root_.MeasureTheory.memLp_re_im_iff

end RCLike

theorem add_compLp (L L' : E →L[𝕜] F) (f : Lp E p μ) :
    (L + L').compLp f = L.compLp f + L'.compLp f := by
  ext1
  refine (coeFn_compLp' (L + L') f).trans ?_
  refine EventuallyEq.trans ?_ (Lp.coeFn_add _ _).symm
  refine
    EventuallyEq.trans ?_ (EventuallyEq.add (L.coeFn_compLp' f).symm (L'.coeFn_compLp' f).symm)
  filter_upwards with x
  rw [coe_add', Pi.add_def]

theorem smul_compLp {𝕜'} [NormedRing 𝕜'] [Module 𝕜' F] [IsBoundedSMul 𝕜' F] [SMulCommClass 𝕜 𝕜' F]
    (c : 𝕜') (L : E →L[𝕜] F) (f : Lp E p μ) : (c • L).compLp f = c • L.compLp f := by
  ext1
  refine (coeFn_compLp' (c • L) f).trans ?_
  refine EventuallyEq.trans ?_ (Lp.coeFn_smul _ _).symm
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

namespace MeasureTheory

theorem indicatorConstLp_eq_toSpanSingleton_compLp {s : Set α} [NormedSpace ℝ F]
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : F) :
    indicatorConstLp 2 hs hμs x =
      (ContinuousLinearMap.toSpanSingleton ℝ x).compLp (indicatorConstLp 2 hs hμs (1 : ℝ)) := by
  ext1
  refine indicatorConstLp_coeFn.trans ?_
  have h_compLp :=
    (ContinuousLinearMap.toSpanSingleton ℝ x).coeFn_compLp (indicatorConstLp 2 hs hμs (1 : ℝ))
  rw [← EventuallyEq] at h_compLp
  refine EventuallyEq.trans ?_ h_compLp.symm
  refine (@indicatorConstLp_coeFn _ _ _ 2 μ _ s hs hμs (1 : ℝ)).mono fun y hy => ?_
  dsimp only
  rw [hy]
  simp_rw [ContinuousLinearMap.toSpanSingleton_apply]
  by_cases hy_mem : y ∈ s <;> simp [hy_mem]

namespace Lp

section PosPart

theorem lipschitzWith_pos_part : LipschitzWith 1 fun x : ℝ => max x 0 :=
  LipschitzWith.id.max_const _

theorem _root_.MeasureTheory.MemLp.pos_part {f : α → ℝ} (hf : MemLp f p μ) :
    MemLp (fun x => max (f x) 0) p μ :=
  lipschitzWith_pos_part.comp_memLp (max_eq_right le_rfl) hf

@[deprecated (since := "2025-02-21")]
alias _root_.MeasureTheory.Memℒp.pos_part := _root_.MeasureTheory.MemLp.pos_part

theorem _root_.MeasureTheory.MemLp.neg_part {f : α → ℝ} (hf : MemLp f p μ) :
    MemLp (fun x => max (-f x) 0) p μ :=
  lipschitzWith_pos_part.comp_memLp (max_eq_right le_rfl) hf.neg

@[deprecated (since := "2025-02-21")]
alias _root_.MeasureTheory.Memℒp.neg_part := _root_.MeasureTheory.MemLp.neg_part

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

end Lp

end MeasureTheory

end Composition

/-!
## `L^p` is a complete space

We show that `L^p` is a complete space for `1 ≤ p`.
-/

section CompleteSpace

namespace MeasureTheory

namespace Lp

theorem eLpNorm'_lim_eq_lintegral_liminf {ι} [Nonempty ι] [LinearOrder ι] {f : ι → α → G} {p : ℝ}
    {f_lim : α → G} (h_lim : ∀ᵐ x : α ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))) :
    eLpNorm' f_lim p μ = (∫⁻ a, atTop.liminf (‖f · a‖ₑ ^ p) ∂μ) ^ (1 / p) := by
  suffices h_no_pow : (∫⁻ a, ‖f_lim a‖ₑ ^ p ∂μ) = ∫⁻ a, atTop.liminf fun m => ‖f m a‖ₑ ^ p ∂μ by
    rw [eLpNorm'_eq_lintegral_enorm, h_no_pow]
  refine lintegral_congr_ae (h_lim.mono fun a ha => ?_)
  dsimp only
  rw [Tendsto.liminf_eq]
  refine (ENNReal.continuous_rpow_const.tendsto ‖f_lim a‖₊).comp ?_
  exact (continuous_enorm.tendsto (f_lim a)).comp ha

theorem eLpNorm'_lim_le_liminf_eLpNorm' {E} [NormedAddCommGroup E] {f : ℕ → α → E} {p : ℝ}
    (hp_pos : 0 < p) (hf : ∀ n, AEStronglyMeasurable (f n) μ) {f_lim : α → E}
    (h_lim : ∀ᵐ x : α ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))) :
    eLpNorm' f_lim p μ ≤ atTop.liminf fun n => eLpNorm' (f n) p μ := by
  rw [eLpNorm'_lim_eq_lintegral_liminf h_lim]
  rw [one_div, ← ENNReal.le_rpow_inv_iff (by simp [hp_pos] : 0 < p⁻¹), inv_inv]
  refine (lintegral_liminf_le' fun m => (hf m).enorm.pow_const _).trans_eq ?_
  have h_pow_liminf :
    atTop.liminf (fun n ↦ eLpNorm' (f n) p μ) ^ p
      = atTop.liminf fun n ↦ eLpNorm' (f n) p μ ^ p := by
    have h_rpow_mono := ENNReal.strictMono_rpow_of_pos hp_pos
    have h_rpow_surj := (ENNReal.rpow_left_bijective hp_pos.ne.symm).2
    refine (h_rpow_mono.orderIsoOfSurjective _ h_rpow_surj).liminf_apply ?_ ?_ ?_ ?_
    all_goals isBoundedDefault
  rw [h_pow_liminf]
  simp_rw [eLpNorm'_eq_lintegral_enorm, ← ENNReal.rpow_mul, one_div,
    inv_mul_cancel₀ hp_pos.ne.symm, ENNReal.rpow_one]

theorem eLpNorm_exponent_top_lim_eq_essSup_liminf {ι} [Nonempty ι] [LinearOrder ι] {f : ι → α → G}
    {f_lim : α → G} (h_lim : ∀ᵐ x : α ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))) :
    eLpNorm f_lim ∞ μ = essSup (fun x => atTop.liminf fun m => ‖f m x‖ₑ) μ := by
  rw [eLpNorm_exponent_top, eLpNormEssSup_eq_essSup_enorm]
  refine essSup_congr_ae (h_lim.mono fun x hx => ?_)
  dsimp only
  apply (Tendsto.liminf_eq ..).symm
  exact (continuous_enorm.tendsto (f_lim x)).comp hx

theorem eLpNorm_exponent_top_lim_le_liminf_eLpNorm_exponent_top {ι} [Nonempty ι] [Countable ι]
    [LinearOrder ι] {f : ι → α → F} {f_lim : α → F}
    (h_lim : ∀ᵐ x : α ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))) :
    eLpNorm f_lim ∞ μ ≤ atTop.liminf fun n => eLpNorm (f n) ∞ μ := by
  rw [eLpNorm_exponent_top_lim_eq_essSup_liminf h_lim]
  simp_rw [eLpNorm_exponent_top, eLpNormEssSup]
  exact ENNReal.essSup_liminf_le _

theorem eLpNorm_lim_le_liminf_eLpNorm {E} [NormedAddCommGroup E] {f : ℕ → α → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (f_lim : α → E)
    (h_lim : ∀ᵐ x : α ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))) :
    eLpNorm f_lim p μ ≤ atTop.liminf fun n => eLpNorm (f n) p μ := by
  obtain rfl|hp0 := eq_or_ne p 0
  · simp
  by_cases hp_top : p = ∞
  · simp_rw [hp_top]
    exact eLpNorm_exponent_top_lim_le_liminf_eLpNorm_exponent_top h_lim
  simp_rw [eLpNorm_eq_eLpNorm' hp0 hp_top]
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  exact eLpNorm'_lim_le_liminf_eLpNorm' hp_pos hf h_lim

/-! ### `Lp` is complete iff Cauchy sequences of `ℒp` have limits in `ℒp` -/


theorem tendsto_Lp_iff_tendsto_eLpNorm' {ι} {fi : Filter ι} [Fact (1 ≤ p)] (f : ι → Lp E p μ)
    (f_lim : Lp E p μ) :
    fi.Tendsto f (𝓝 f_lim) ↔ fi.Tendsto (fun n => eLpNorm (⇑(f n) - ⇑f_lim) p μ) (𝓝 0) := by
  rw [tendsto_iff_dist_tendsto_zero]
  simp_rw [dist_def]
  rw [← ENNReal.toReal_zero, ENNReal.tendsto_toReal_iff (fun n => ?_) ENNReal.zero_ne_top]
  rw [eLpNorm_congr_ae (Lp.coeFn_sub _ _).symm]
  exact Lp.eLpNorm_ne_top _

@[deprecated (since := "2025-02-21")]
alias tendsto_Lp_iff_tendsto_ℒp' := tendsto_Lp_iff_tendsto_eLpNorm'

theorem tendsto_Lp_iff_tendsto_eLpNorm {ι} {fi : Filter ι} [Fact (1 ≤ p)] (f : ι → Lp E p μ)
    (f_lim : α → E) (f_lim_ℒp : MemLp f_lim p μ) :
    fi.Tendsto f (𝓝 (f_lim_ℒp.toLp f_lim)) ↔
      fi.Tendsto (fun n => eLpNorm (⇑(f n) - f_lim) p μ) (𝓝 0) := by
  rw [tendsto_Lp_iff_tendsto_eLpNorm']
  suffices h_eq :
      (fun n => eLpNorm (⇑(f n) - ⇑(MemLp.toLp f_lim f_lim_ℒp)) p μ) =
        (fun n => eLpNorm (⇑(f n) - f_lim) p μ) by
    rw [h_eq]
  exact funext fun n => eLpNorm_congr_ae (EventuallyEq.rfl.sub (MemLp.coeFn_toLp f_lim_ℒp))

@[deprecated (since := "2025-02-21")]
alias tendsto_Lp_iff_tendsto_ℒp := tendsto_Lp_iff_tendsto_eLpNorm

theorem tendsto_Lp_iff_tendsto_eLpNorm'' {ι} {fi : Filter ι} [Fact (1 ≤ p)] (f : ι → α → E)
    (f_ℒp : ∀ n, MemLp (f n) p μ) (f_lim : α → E) (f_lim_ℒp : MemLp f_lim p μ) :
    fi.Tendsto (fun n => (f_ℒp n).toLp (f n)) (𝓝 (f_lim_ℒp.toLp f_lim)) ↔
      fi.Tendsto (fun n => eLpNorm (f n - f_lim) p μ) (𝓝 0) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun n => (f_ℒp n).toLp (f n)) (f_lim_ℒp.toLp f_lim)]
  refine Filter.tendsto_congr fun n => ?_
  apply eLpNorm_congr_ae
  filter_upwards [((f_ℒp n).sub f_lim_ℒp).coeFn_toLp,
    Lp.coeFn_sub ((f_ℒp n).toLp (f n)) (f_lim_ℒp.toLp f_lim)] with _ hx₁ hx₂
  rw [← hx₂]
  exact hx₁

@[deprecated (since := "2025-02-21")]
alias tendsto_Lp_iff_tendsto_ℒp'' := tendsto_Lp_iff_tendsto_eLpNorm''


theorem tendsto_Lp_of_tendsto_eLpNorm {ι} {fi : Filter ι} [Fact (1 ≤ p)] {f : ι → Lp E p μ}
    (f_lim : α → E) (f_lim_ℒp : MemLp f_lim p μ)
    (h_tendsto : fi.Tendsto (fun n => eLpNorm (⇑(f n) - f_lim) p μ) (𝓝 0)) :
    fi.Tendsto f (𝓝 (f_lim_ℒp.toLp f_lim)) :=
  (tendsto_Lp_iff_tendsto_eLpNorm f f_lim f_lim_ℒp).mpr h_tendsto

@[deprecated (since := "2025-02-21")]
alias tendsto_Lp_of_tendsto_ℒp := tendsto_Lp_of_tendsto_eLpNorm

theorem cauchySeq_Lp_iff_cauchySeq_eLpNorm {ι} [Nonempty ι] [SemilatticeSup ι] [hp : Fact (1 ≤ p)]
    (f : ι → Lp E p μ) :
    CauchySeq f ↔ Tendsto (fun n : ι × ι => eLpNorm (⇑(f n.fst) - ⇑(f n.snd)) p μ) atTop (𝓝 0) := by
  simp_rw [cauchySeq_iff_tendsto_dist_atTop_0, dist_def]
  rw [← ENNReal.toReal_zero, ENNReal.tendsto_toReal_iff (fun n => ?_) ENNReal.zero_ne_top]
  rw [eLpNorm_congr_ae (Lp.coeFn_sub _ _).symm]
  exact eLpNorm_ne_top _

@[deprecated (since := "2025-02-21")]
alias cauchySeq_Lp_iff_cauchySeq_ℒp := cauchySeq_Lp_iff_cauchySeq_eLpNorm

theorem completeSpace_lp_of_cauchy_complete_eLpNorm [hp : Fact (1 ≤ p)]
    (H :
      ∀ (f : ℕ → α → E) (_ : ∀ n, MemLp (f n) p μ) (B : ℕ → ℝ≥0∞) (_ : ∑' i, B i < ∞)
        (_ : ∀ N n m : ℕ, N ≤ n → N ≤ m → eLpNorm (f n - f m) p μ < B N),
        ∃ (f_lim : α → E), MemLp f_lim p μ ∧
          atTop.Tendsto (fun n => eLpNorm (f n - f_lim) p μ) (𝓝 0)) :
    CompleteSpace (Lp E p μ) := by
  let B := fun n : ℕ => ((1 : ℝ) / 2) ^ n
  have hB_pos : ∀ n, 0 < B n := fun n => pow_pos (div_pos zero_lt_one zero_lt_two) n
  refine Metric.complete_of_convergent_controlled_sequences B hB_pos fun f hf => ?_
  rsuffices ⟨f_lim, hf_lim_meas, h_tendsto⟩ :
    ∃ (f_lim : α → E), MemLp f_lim p μ ∧
      atTop.Tendsto (fun n => eLpNorm (⇑(f n) - f_lim) p μ) (𝓝 0)
  · exact ⟨hf_lim_meas.toLp f_lim, tendsto_Lp_of_tendsto_eLpNorm f_lim hf_lim_meas h_tendsto⟩
  obtain ⟨M, hB⟩ : Summable B := summable_geometric_two
  let B1 n := ENNReal.ofReal (B n)
  have hB1_has : HasSum B1 (ENNReal.ofReal M) := by
    have h_tsum_B1 : ∑' i, B1 i = ENNReal.ofReal M := by
      change (∑' n : ℕ, ENNReal.ofReal (B n)) = ENNReal.ofReal M
      rw [← hB.tsum_eq]
      exact (ENNReal.ofReal_tsum_of_nonneg (fun n => le_of_lt (hB_pos n)) hB.summable).symm
    have h_sum := (@ENNReal.summable _ B1).hasSum
    rwa [h_tsum_B1] at h_sum
  have hB1 : ∑' i, B1 i < ∞ := by
    rw [hB1_has.tsum_eq]
    exact ENNReal.ofReal_lt_top
  let f1 : ℕ → α → E := fun n => f n
  refine H f1 (fun n => Lp.memLp (f n)) B1 hB1 fun N n m hn hm => ?_
  specialize hf N n m hn hm
  rw [dist_def] at hf
  dsimp only [f1]
  rwa [ENNReal.lt_ofReal_iff_toReal_lt]
  rw [eLpNorm_congr_ae (Lp.coeFn_sub _ _).symm]
  exact Lp.eLpNorm_ne_top _

@[deprecated (since := "2025-02-21")]
alias completeSpace_lp_of_cauchy_complete_ℒp := completeSpace_lp_of_cauchy_complete_eLpNorm

/-! ### Prove that controlled Cauchy sequences of `ℒp` have limits in `ℒp` -/

private theorem eLpNorm'_sum_norm_sub_le_tsum_of_cauchy_eLpNorm' {f : ℕ → α → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) {p : ℝ} (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞}
    (h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m → eLpNorm' (f n - f m) p μ < B N) (n : ℕ) :
    eLpNorm' (fun x => ∑ i ∈ Finset.range (n + 1), ‖f (i + 1) x - f i x‖) p μ ≤ ∑' i, B i := by
  let f_norm_diff i x := ‖f (i + 1) x - f i x‖
  have hgf_norm_diff :
    ∀ n,
      (fun x => ∑ i ∈ Finset.range (n + 1), ‖f (i + 1) x - f i x‖) =
        ∑ i ∈ Finset.range (n + 1), f_norm_diff i :=
    fun n => funext fun x => by simp [f_norm_diff]
  rw [hgf_norm_diff]
  refine (eLpNorm'_sum_le (fun i _ => ((hf (i + 1)).sub (hf i)).norm) hp1).trans ?_
  simp_rw [eLpNorm'_norm]
  refine (Finset.sum_le_sum ?_).trans (sum_le_tsum _ (fun m _ => zero_le _) ENNReal.summable)
  exact fun m _ => (h_cau m (m + 1) m (Nat.le_succ m) (le_refl m)).le

private theorem lintegral_rpow_sum_enorm_sub_le_rpow_tsum
    {f : ℕ → α → E} {p : ℝ} (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞} (n : ℕ)
    (hn : eLpNorm' (fun x => ∑ i ∈ Finset.range (n + 1), ‖f (i + 1) x - f i x‖) p μ ≤ ∑' i, B i) :
    (∫⁻ a, (∑ i ∈ Finset.range (n + 1), ‖f (i + 1) a - f i a‖ₑ) ^ p ∂μ) ≤ (∑' i, B i) ^ p := by
  have hp_pos : 0 < p := zero_lt_one.trans_le hp1
  rw [← inv_inv p, @ENNReal.le_rpow_inv_iff _ _ p⁻¹ (by simp [hp_pos]), inv_inv p]
  simp_rw [eLpNorm'_eq_lintegral_enorm, one_div] at hn
  have h_nnnorm_nonneg :
    (fun a => ‖∑ i ∈ Finset.range (n + 1), ‖f (i + 1) a - f i a‖‖ₑ ^ p) = fun a =>
      (∑ i ∈ Finset.range (n + 1), ‖f (i + 1) a - f i a‖ₑ) ^ p := by
    ext1 a
    congr
    simp_rw [← ofReal_norm_eq_enorm]
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · rw [Real.norm_of_nonneg _]
      exact Finset.sum_nonneg fun x _ => norm_nonneg _
    · exact fun x _ => norm_nonneg _
  rwa [h_nnnorm_nonneg] at hn

private theorem lintegral_rpow_tsum_coe_enorm_sub_le_tsum {f : ℕ → α → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) {p : ℝ} (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞}
    (h : ∀ n, ∫⁻ a, (∑ i ∈ Finset.range (n + 1), ‖f (i + 1) a - f i a‖ₑ) ^ p ∂μ ≤ (∑' i, B i) ^ p) :
    (∫⁻ a, (∑' i, ‖f (i + 1) a - f i a‖ₑ) ^ p ∂μ) ^ (1 / p) ≤ ∑' i, B i := by
  have hp_pos : 0 < p := zero_lt_one.trans_le hp1
  suffices h_pow : (∫⁻ a, (∑' i, ‖f (i + 1) a - f i a‖ₑ) ^ p ∂μ) ≤ (∑' i, B i) ^ p by
      rwa [one_div, ← ENNReal.le_rpow_inv_iff (by simp [hp_pos] : 0 < p⁻¹), inv_inv]
  have h_tsum_1 :
    ∀ g : ℕ → ℝ≥0∞, ∑' i, g i = atTop.liminf fun n => ∑ i ∈ Finset.range (n + 1), g i := by
    intro g
    rw [ENNReal.tsum_eq_liminf_sum_nat, ← liminf_nat_add _ 1]
  simp_rw [h_tsum_1 _]
  rw [← h_tsum_1]
  have h_liminf_pow :
    ∫⁻ a, (atTop.liminf fun n => ∑ i ∈ Finset.range (n + 1), ‖f (i + 1) a - f i a‖ₑ) ^ p ∂μ =
      ∫⁻ a, atTop.liminf fun n => (∑ i ∈ Finset.range (n + 1), ‖f (i + 1) a - f i a‖ₑ) ^ p ∂μ := by
    refine lintegral_congr fun x => ?_
    have h_rpow_mono := ENNReal.strictMono_rpow_of_pos (zero_lt_one.trans_le hp1)
    have h_rpow_surj := (ENNReal.rpow_left_bijective hp_pos.ne.symm).2
    refine (h_rpow_mono.orderIsoOfSurjective _ h_rpow_surj).liminf_apply ?_ ?_ ?_ ?_
    all_goals isBoundedDefault
  rw [h_liminf_pow]
  refine (lintegral_liminf_le' fun n ↦ ?_).trans <| liminf_le_of_frequently_le' <| .of_forall h
  exact ((Finset.range _).aemeasurable_sum fun i _ ↦ ((hf _).sub (hf i)).enorm).pow_const _

private theorem tsum_enorm_sub_ae_lt_top {f : ℕ → α → E} (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    {p : ℝ} (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞} (hB : ∑' i, B i ≠ ∞)
    (h : (∫⁻ a, (∑' i, ‖f (i + 1) a - f i a‖ₑ) ^ p ∂μ) ^ (1 / p) ≤ ∑' i, B i) :
    ∀ᵐ x ∂μ, ∑' i, ‖f (i + 1) x - f i x‖ₑ < ∞ := by
  have hp_pos : 0 < p := zero_lt_one.trans_le hp1
  have h_integral : ∫⁻ a, (∑' i, ‖f (i + 1) a - f i a‖ₑ) ^ p ∂μ < ∞ := by
    have h_tsum_lt_top : (∑' i, B i) ^ p < ∞ := ENNReal.rpow_lt_top_of_nonneg hp_pos.le hB
    refine lt_of_le_of_lt ?_ h_tsum_lt_top
    rwa [one_div, ← ENNReal.le_rpow_inv_iff (by simp [hp_pos] : 0 < p⁻¹), inv_inv] at h
  have rpow_ae_lt_top : ∀ᵐ x ∂μ, (∑' i, ‖f (i + 1) x - f i x‖ₑ) ^ p < ∞ := by
    refine ae_lt_top' (AEMeasurable.pow_const ?_ _) h_integral.ne
    exact AEMeasurable.ennreal_tsum fun n => ((hf (n + 1)).sub (hf n)).enorm
  refine rpow_ae_lt_top.mono fun x hx => ?_
  rwa [← ENNReal.lt_rpow_inv_iff hp_pos,
    ENNReal.top_rpow_of_pos (by simp [hp_pos] : 0 < p⁻¹)] at hx

theorem ae_tendsto_of_cauchy_eLpNorm' [CompleteSpace E] {f : ℕ → α → E} {p : ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞} (hB : ∑' i, B i ≠ ∞)
    (h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m → eLpNorm' (f n - f m) p μ < B N) :
    ∀ᵐ x ∂μ, ∃ l : E, atTop.Tendsto (fun n => f n x) (𝓝 l) := by
  have h_summable : ∀ᵐ x ∂μ, Summable fun i : ℕ => f (i + 1) x - f i x := by
    have h1 :
      ∀ n, eLpNorm' (fun x => ∑ i ∈ Finset.range (n + 1), ‖f (i + 1) x - f i x‖) p μ ≤ ∑' i, B i :=
      eLpNorm'_sum_norm_sub_le_tsum_of_cauchy_eLpNorm' hf hp1 h_cau
    have h2 n :
        ∫⁻ a, (∑ i ∈ Finset.range (n + 1), ‖f (i + 1) a - f i a‖ₑ) ^ p ∂μ ≤ (∑' i, B i) ^ p :=
      lintegral_rpow_sum_enorm_sub_le_rpow_tsum hp1 n (h1 n)
    have h3 : (∫⁻ a, (∑' i, ‖f (i + 1) a - f i a‖ₑ) ^ p ∂μ) ^ (1 / p) ≤ ∑' i, B i :=
      lintegral_rpow_tsum_coe_enorm_sub_le_tsum hf hp1 h2
    have h4 : ∀ᵐ x ∂μ, ∑' i, ‖f (i + 1) x - f i x‖ₑ < ∞ :=
      tsum_enorm_sub_ae_lt_top hf hp1 hB h3
    exact h4.mono fun x hx => .of_nnnorm <| ENNReal.tsum_coe_ne_top_iff_summable.mp hx.ne
  have h :
    ∀ᵐ x ∂μ, ∃ l : E,
      atTop.Tendsto (fun n => ∑ i ∈ Finset.range n, (f (i + 1) x - f i x)) (𝓝 l) := by
    refine h_summable.mono fun x hx => ?_
    let hx_sum := hx.hasSum.tendsto_sum_nat
    exact ⟨∑' i, (f (i + 1) x - f i x), hx_sum⟩
  refine h.mono fun x hx => ?_
  obtain ⟨l, hx⟩ := hx
  have h_rw_sum :
      (fun n => ∑ i ∈ Finset.range n, (f (i + 1) x - f i x)) = fun n => f n x - f 0 x := by
    ext1 n
    change
      (∑ i ∈ Finset.range n, ((fun m => f m x) (i + 1) - (fun m => f m x) i)) = f n x - f 0 x
    rw [Finset.sum_range_sub (fun m => f m x)]
  rw [h_rw_sum] at hx
  have hf_rw : (fun n => f n x) = fun n => f n x - f 0 x + f 0 x := by
    ext1 n
    abel
  rw [hf_rw]
  exact ⟨l + f 0 x, Tendsto.add_const _ hx⟩

theorem ae_tendsto_of_cauchy_eLpNorm [CompleteSpace E] {f : ℕ → α → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hp : 1 ≤ p) {B : ℕ → ℝ≥0∞} (hB : ∑' i, B i ≠ ∞)
    (h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m → eLpNorm (f n - f m) p μ < B N) :
    ∀ᵐ x ∂μ, ∃ l : E, atTop.Tendsto (fun n => f n x) (𝓝 l) := by
  by_cases hp_top : p = ∞
  · simp_rw [hp_top] at *
    have h_cau_ae : ∀ᵐ x ∂μ, ∀ N n m, N ≤ n → N ≤ m → ‖(f n - f m) x‖ₑ < B N := by
      simp_rw [ae_all_iff]
      exact fun N n m hnN hmN => ae_lt_of_essSup_lt (h_cau N n m hnN hmN)
    simp_rw [eLpNorm_exponent_top, eLpNormEssSup] at h_cau
    refine h_cau_ae.mono fun x hx => cauchySeq_tendsto_of_complete ?_
    refine cauchySeq_of_le_tendsto_0 (fun n => (B n).toReal) ?_ ?_
    · intro n m N hnN hmN
      specialize hx N n m hnN hmN
      rw [_root_.dist_eq_norm,
        ← ENNReal.ofReal_le_iff_le_toReal (ENNReal.ne_top_of_tsum_ne_top hB N),
        ofReal_norm_eq_enorm]
      exact hx.le
    · rw [← ENNReal.toReal_zero]
      exact
        Tendsto.comp (g := ENNReal.toReal) (ENNReal.tendsto_toReal ENNReal.zero_ne_top)
          (ENNReal.tendsto_atTop_zero_of_tsum_ne_top hB)
  have hp1 : 1 ≤ p.toReal := by
    rw [← ENNReal.ofReal_le_iff_le_toReal hp_top, ENNReal.ofReal_one]
    exact hp
  have h_cau' : ∀ N n m : ℕ, N ≤ n → N ≤ m → eLpNorm' (f n - f m) p.toReal μ < B N := by
    intro N n m hn hm
    specialize h_cau N n m hn hm
    rwa [eLpNorm_eq_eLpNorm' (zero_lt_one.trans_le hp).ne.symm hp_top] at h_cau
  exact ae_tendsto_of_cauchy_eLpNorm' hf hp1 hB h_cau'

theorem cauchy_tendsto_of_tendsto {f : ℕ → α → E} (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (f_lim : α → E) {B : ℕ → ℝ≥0∞} (hB : ∑' i, B i ≠ ∞)
    (h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m → eLpNorm (f n - f m) p μ < B N)
    (h_lim : ∀ᵐ x : α ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))) :
    atTop.Tendsto (fun n => eLpNorm (f n - f_lim) p μ) (𝓝 0) := by
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  have h_B : ∃ N : ℕ, B N ≤ ε := by
    suffices h_tendsto_zero : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → B n ≤ ε from
      ⟨h_tendsto_zero.choose, h_tendsto_zero.choose_spec _ le_rfl⟩
    exact (ENNReal.tendsto_atTop_zero.mp (ENNReal.tendsto_atTop_zero_of_tsum_ne_top hB)) ε hε
  obtain ⟨N, h_B⟩ := h_B
  refine ⟨N, fun n hn => ?_⟩
  have h_sub : eLpNorm (f n - f_lim) p μ ≤ atTop.liminf fun m => eLpNorm (f n - f m) p μ := by
    refine eLpNorm_lim_le_liminf_eLpNorm (fun m => (hf n).sub (hf m)) (f n - f_lim) ?_
    refine h_lim.mono fun x hx => ?_
    simp_rw [sub_eq_add_neg]
    exact Tendsto.add tendsto_const_nhds (Tendsto.neg hx)
  refine h_sub.trans ?_
  refine liminf_le_of_frequently_le' (frequently_atTop.mpr ?_)
  refine fun N1 => ⟨max N N1, le_max_right _ _, ?_⟩
  exact (h_cau N n (max N N1) hn (le_max_left _ _)).le.trans h_B

theorem memLp_of_cauchy_tendsto (hp : 1 ≤ p) {f : ℕ → α → E} (hf : ∀ n, MemLp (f n) p μ)
    (f_lim : α → E) (h_lim_meas : AEStronglyMeasurable f_lim μ)
    (h_tendsto : atTop.Tendsto (fun n => eLpNorm (f n - f_lim) p μ) (𝓝 0)) : MemLp f_lim p μ := by
  refine ⟨h_lim_meas, ?_⟩
  rw [ENNReal.tendsto_atTop_zero] at h_tendsto
  obtain ⟨N, h_tendsto_1⟩ := h_tendsto 1 zero_lt_one
  specialize h_tendsto_1 N (le_refl N)
  have h_add : f_lim = f_lim - f N + f N := by abel
  rw [h_add]
  refine lt_of_le_of_lt (eLpNorm_add_le (h_lim_meas.sub (hf N).1) (hf N).1 hp) ?_
  rw [ENNReal.add_lt_top]
  constructor
  · refine lt_of_le_of_lt ?_ ENNReal.one_lt_top
    have h_neg : f_lim - f N = -(f N - f_lim) := by simp
    rwa [h_neg, eLpNorm_neg]
  · exact (hf N).2

@[deprecated (since := "2025-02-21")]
alias memℒp_of_cauchy_tendsto := memLp_of_cauchy_tendsto

theorem cauchy_complete_eLpNorm [CompleteSpace E] (hp : 1 ≤ p) {f : ℕ → α → E}
    (hf : ∀ n, MemLp (f n) p μ) {B : ℕ → ℝ≥0∞} (hB : ∑' i, B i ≠ ∞)
    (h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m → eLpNorm (f n - f m) p μ < B N) :
    ∃ (f_lim : α → E), MemLp f_lim p μ ∧
      atTop.Tendsto (fun n => eLpNorm (f n - f_lim) p μ) (𝓝 0) := by
  obtain ⟨f_lim, h_f_lim_meas, h_lim⟩ :
      ∃ f_lim : α → E, StronglyMeasurable f_lim ∧
        ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x)) :=
    exists_stronglyMeasurable_limit_of_tendsto_ae (fun n => (hf n).1)
      (ae_tendsto_of_cauchy_eLpNorm (fun n => (hf n).1) hp hB h_cau)
  have h_tendsto' : atTop.Tendsto (fun n => eLpNorm (f n - f_lim) p μ) (𝓝 0) :=
    cauchy_tendsto_of_tendsto (fun m => (hf m).1) f_lim hB h_cau h_lim
  have h_ℒp_lim : MemLp f_lim p μ :=
    memLp_of_cauchy_tendsto hp hf f_lim h_f_lim_meas.aestronglyMeasurable h_tendsto'
  exact ⟨f_lim, h_ℒp_lim, h_tendsto'⟩

@[deprecated (since := "2025-02-21")]
alias cauchy_complete_ℒp := cauchy_complete_eLpNorm

/-! ### `Lp` is complete for `1 ≤ p` -/

instance instCompleteSpace [CompleteSpace E] [hp : Fact (1 ≤ p)] : CompleteSpace (Lp E p μ) :=
  completeSpace_lp_of_cauchy_complete_eLpNorm fun _f hf _B hB h_cau =>
    cauchy_complete_eLpNorm hp.elim hf hB.ne h_cau

end Lp

end MeasureTheory

end CompleteSpace

namespace MeasureTheory

namespace Lp

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
    meas_ge_le_mul_pow_eLpNorm μ hp_ne_zero hp_ne_top (Lp.aestronglyMeasurable f) hε

@[deprecated (since := "2025-01-20")] alias pow_mul_meas_ge_le_norm := pow_mul_meas_ge_le_enorm
@[deprecated (since := "2025-01-20")] alias mul_meas_ge_le_pow_norm := mul_meas_ge_le_pow_enorm
@[deprecated (since := "2025-01-20")] alias mul_meas_ge_le_pow_norm' := mul_meas_ge_le_pow_enorm'
@[deprecated (since := "2025-01-20")] alias meas_ge_le_mul_pow_norm := meas_ge_le_mul_pow_enorm

end Lp

end MeasureTheory

set_option linter.style.longFile 1700
