/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel

! This file was ported from Lean 3 source module measure_theory.function.lp_space
! leanprover-community/mathlib commit c4015acc0a223449d44061e27ddac1835a3852b9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Normed.Group.Hom
import Mathbin.MeasureTheory.Function.LpSeminorm
import Mathbin.Topology.ContinuousFunction.Compact

/-!
# Lp space

This file provides the space `Lp E p μ` as the subtype of elements of `α →ₘ[μ] E` (see ae_eq_fun)
such that `snorm f p μ` is finite. For `1 ≤ p`, `snorm` defines a norm and `Lp` is a complete metric
space.

## Main definitions

* `Lp E p μ` : elements of `α →ₘ[μ] E` (see ae_eq_fun) such that `snorm f p μ` is finite. Defined
  as an `add_subgroup` of `α →ₘ[μ] E`.

Lipschitz functions vanishing at zero act by composition on `Lp`. We define this action, and prove
that it is continuous. In particular,
* `continuous_linear_map.comp_Lp` defines the action on `Lp` of a continuous linear map.
* `Lp.pos_part` is the positive part of an `Lp` function.
* `Lp.neg_part` is the negative part of an `Lp` function.

When `α` is a topological space equipped with a finite Borel measure, there is a bounded linear map
from the normed space of bounded continuous functions (`α →ᵇ E`) to `Lp E p μ`.  We construct this
as `bounded_continuous_function.to_Lp`.

## Notations

* `α →₁[μ] E` : the type `Lp E 1 μ`.
* `α →₂[μ] E` : the type `Lp E 2 μ`.

## Implementation

Since `Lp` is defined as an `add_subgroup`, dot notation does not work. Use `Lp.measurable f` to
say that the coercion of `f` to a genuine function is measurable, instead of the non-working
`f.measurable`.

To prove that two `Lp` elements are equal, it suffices to show that their coercions to functions
coincide almost everywhere (this is registered as an `ext` rule). This can often be done using
`filter_upwards`. For instance, a proof from first principles that `f + (g + h) = (f + g) + h`
could read (in the `Lp` namespace)
```
example (f g h : Lp E p μ) : (f + g) + h = f + (g + h) :=
begin
  ext1,
  filter_upwards [coe_fn_add (f + g) h, coe_fn_add f g, coe_fn_add f (g + h), coe_fn_add g h]
    with _ ha1 ha2 ha3 ha4,
  simp only [ha1, ha2, ha3, ha4, add_assoc],
end
```
The lemma `coe_fn_add` states that the coercion of `f + g` coincides almost everywhere with the sum
of the coercions of `f` and `g`. All such lemmas use `coe_fn` in their name, to distinguish the
function coercion from the coercion to almost everywhere defined functions.
-/


noncomputable section

open TopologicalSpace MeasureTheory Filter

open scoped NNReal ENNReal BigOperators Topology MeasureTheory

variable {α E F G : Type _} {m m0 : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ} {μ ν : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]

namespace MeasureTheory

/-!
### Lp space

The space of equivalence classes of measurable functions for which `snorm f p μ < ∞`.
-/


@[simp]
theorem snorm_aEEqFun {α E : Type _} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    {p : ℝ≥0∞} {f : α → E} (hf : AEStronglyMeasurable f μ) :
    snorm (AEEqFun.mk f hf) p μ = snorm f p μ :=
  snorm_congr_ae (AEEqFun.coeFn_mk _ _)
#align measure_theory.snorm_ae_eq_fun MeasureTheory.snorm_aEEqFun

theorem Memℒp.snorm_mk_lt_top {α E : Type _} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {p : ℝ≥0∞} {f : α → E} (hfp : Memℒp f p μ) :
    snorm (AEEqFun.mk f hfp.1) p μ < ∞ := by simp [hfp.2]
#align measure_theory.mem_ℒp.snorm_mk_lt_top MeasureTheory.Memℒp.snorm_mk_lt_top

/-- Lp space -/
def lp {α} (E : Type _) {m : MeasurableSpace α} [NormedAddCommGroup E] (p : ℝ≥0∞)
    (μ : Measure α := by exact MeasureTheory.MeasureSpace.volume) : AddSubgroup (α →ₘ[μ] E)
    where
  carrier := { f | snorm f p μ < ∞ }
  zero_mem' := by simp [snorm_congr_ae ae_eq_fun.coe_fn_zero, snorm_zero]
  add_mem' f g hf hg := by
    simp [snorm_congr_ae (ae_eq_fun.coe_fn_add _ _),
      snorm_add_lt_top ⟨f.ae_strongly_measurable, hf⟩ ⟨g.ae_strongly_measurable, hg⟩]
  neg_mem' f hf := by rwa [Set.mem_setOf_eq, snorm_congr_ae (ae_eq_fun.coe_fn_neg _), snorm_neg]
#align measure_theory.Lp MeasureTheory.lp

-- mathport name: measure_theory.L1
scoped notation:25 α " →₁[" μ "] " E => MeasureTheory.lp E 1 μ

-- mathport name: measure_theory.L2
scoped notation:25 α " →₂[" μ "] " E => MeasureTheory.lp E 2 μ

namespace Memℒp

/-- make an element of Lp from a function verifying `mem_ℒp` -/
def toLp (f : α → E) (h_mem_ℒp : Memℒp f p μ) : lp E p μ :=
  ⟨AEEqFun.mk f h_mem_ℒp.1, h_mem_ℒp.snorm_mk_lt_top⟩
#align measure_theory.mem_ℒp.to_Lp MeasureTheory.Memℒp.toLp

theorem coeFn_toLp {f : α → E} (hf : Memℒp f p μ) : hf.toLp f =ᵐ[μ] f :=
  AEEqFun.coeFn_mk _ _
#align measure_theory.mem_ℒp.coe_fn_to_Lp MeasureTheory.Memℒp.coeFn_toLp

theorem toLp_congr {f g : α → E} (hf : Memℒp f p μ) (hg : Memℒp g p μ) (hfg : f =ᵐ[μ] g) :
    hf.toLp f = hg.toLp g := by simp [to_Lp, hfg]
#align measure_theory.mem_ℒp.to_Lp_congr MeasureTheory.Memℒp.toLp_congr

@[simp]
theorem toLp_eq_toLp_iff {f g : α → E} (hf : Memℒp f p μ) (hg : Memℒp g p μ) :
    hf.toLp f = hg.toLp g ↔ f =ᵐ[μ] g := by simp [to_Lp]
#align measure_theory.mem_ℒp.to_Lp_eq_to_Lp_iff MeasureTheory.Memℒp.toLp_eq_toLp_iff

@[simp]
theorem toLp_zero (h : Memℒp (0 : α → E) p μ) : h.toLp 0 = 0 :=
  rfl
#align measure_theory.mem_ℒp.to_Lp_zero MeasureTheory.Memℒp.toLp_zero

theorem toLp_add {f g : α → E} (hf : Memℒp f p μ) (hg : Memℒp g p μ) :
    (hf.add hg).toLp (f + g) = hf.toLp f + hg.toLp g :=
  rfl
#align measure_theory.mem_ℒp.to_Lp_add MeasureTheory.Memℒp.toLp_add

theorem toLp_neg {f : α → E} (hf : Memℒp f p μ) : hf.neg.toLp (-f) = -hf.toLp f :=
  rfl
#align measure_theory.mem_ℒp.to_Lp_neg MeasureTheory.Memℒp.toLp_neg

theorem toLp_sub {f g : α → E} (hf : Memℒp f p μ) (hg : Memℒp g p μ) :
    (hf.sub hg).toLp (f - g) = hf.toLp f - hg.toLp g :=
  rfl
#align measure_theory.mem_ℒp.to_Lp_sub MeasureTheory.Memℒp.toLp_sub

end Memℒp

namespace Lp

instance : CoeFun (lp E p μ) fun _ => α → E :=
  ⟨fun f => ((f : α →ₘ[μ] E) : α → E)⟩

@[ext]
theorem ext {f g : lp E p μ} (h : f =ᵐ[μ] g) : f = g :=
  by
  cases f
  cases g
  simp only [Subtype.mk_eq_mk]
  exact ae_eq_fun.ext h
#align measure_theory.Lp.ext MeasureTheory.lp.ext

theorem ext_iff {f g : lp E p μ} : f = g ↔ f =ᵐ[μ] g :=
  ⟨fun h => by rw [h], fun h => ext h⟩
#align measure_theory.Lp.ext_iff MeasureTheory.lp.ext_iff

theorem mem_lp_iff_snorm_lt_top {f : α →ₘ[μ] E} : f ∈ lp E p μ ↔ snorm f p μ < ∞ :=
  Iff.refl _
#align measure_theory.Lp.mem_Lp_iff_snorm_lt_top MeasureTheory.lp.mem_lp_iff_snorm_lt_top

theorem mem_lp_iff_memℒp {f : α →ₘ[μ] E} : f ∈ lp E p μ ↔ Memℒp f p μ := by
  simp [mem_Lp_iff_snorm_lt_top, mem_ℒp, f.strongly_measurable.ae_strongly_measurable]
#align measure_theory.Lp.mem_Lp_iff_mem_ℒp MeasureTheory.lp.mem_lp_iff_memℒp

protected theorem antitone [FiniteMeasure μ] {p q : ℝ≥0∞} (hpq : p ≤ q) : lp E q μ ≤ lp E p μ :=
  fun f hf => (Memℒp.memℒp_of_exponent_le ⟨f.AEStronglyMeasurable, hf⟩ hpq).2
#align measure_theory.Lp.antitone MeasureTheory.lp.antitone

@[simp]
theorem coeFn_mk {f : α →ₘ[μ] E} (hf : snorm f p μ < ∞) : ((⟨f, hf⟩ : lp E p μ) : α → E) = f :=
  rfl
#align measure_theory.Lp.coe_fn_mk MeasureTheory.lp.coeFn_mk

@[simp]
theorem coe_mk {f : α →ₘ[μ] E} (hf : snorm f p μ < ∞) : ((⟨f, hf⟩ : lp E p μ) : α →ₘ[μ] E) = f :=
  rfl
#align measure_theory.Lp.coe_mk MeasureTheory.lp.coe_mk

@[simp]
theorem toLp_coeFn (f : lp E p μ) (hf : Memℒp f p μ) : hf.toLp f = f := by cases f;
  simp [mem_ℒp.to_Lp]
#align measure_theory.Lp.to_Lp_coe_fn MeasureTheory.lp.toLp_coeFn

theorem snorm_lt_top (f : lp E p μ) : snorm f p μ < ∞ :=
  f.Prop
#align measure_theory.Lp.snorm_lt_top MeasureTheory.lp.snorm_lt_top

theorem snorm_ne_top (f : lp E p μ) : snorm f p μ ≠ ∞ :=
  (snorm_lt_top f).Ne
#align measure_theory.Lp.snorm_ne_top MeasureTheory.lp.snorm_ne_top

@[measurability]
protected theorem stronglyMeasurable (f : lp E p μ) : StronglyMeasurable f :=
  f.val.StronglyMeasurable
#align measure_theory.Lp.strongly_measurable MeasureTheory.lp.stronglyMeasurable

@[measurability]
protected theorem aEStronglyMeasurable (f : lp E p μ) : AEStronglyMeasurable f μ :=
  f.val.AEStronglyMeasurable
#align measure_theory.Lp.ae_strongly_measurable MeasureTheory.lp.aEStronglyMeasurable

protected theorem memℒp (f : lp E p μ) : Memℒp f p μ :=
  ⟨lp.aEStronglyMeasurable f, f.Prop⟩
#align measure_theory.Lp.mem_ℒp MeasureTheory.lp.memℒp

variable (E p μ)

theorem coeFn_zero : ⇑(0 : lp E p μ) =ᵐ[μ] 0 :=
  AEEqFun.coeFn_zero
#align measure_theory.Lp.coe_fn_zero MeasureTheory.lp.coeFn_zero

variable {E p μ}

theorem coeFn_neg (f : lp E p μ) : ⇑(-f) =ᵐ[μ] -f :=
  AEEqFun.coeFn_neg _
#align measure_theory.Lp.coe_fn_neg MeasureTheory.lp.coeFn_neg

theorem coeFn_add (f g : lp E p μ) : ⇑(f + g) =ᵐ[μ] f + g :=
  AEEqFun.coeFn_add _ _
#align measure_theory.Lp.coe_fn_add MeasureTheory.lp.coeFn_add

theorem coeFn_sub (f g : lp E p μ) : ⇑(f - g) =ᵐ[μ] f - g :=
  AEEqFun.coeFn_sub _ _
#align measure_theory.Lp.coe_fn_sub MeasureTheory.lp.coeFn_sub

theorem mem_lp_const (α) {m : MeasurableSpace α} (μ : Measure α) (c : E) [FiniteMeasure μ] :
    @AEEqFun.const α _ _ μ _ c ∈ lp E p μ :=
  (memℒp_const c).snorm_mk_lt_top
#align measure_theory.Lp.mem_Lp_const MeasureTheory.lp.mem_lp_const

instance : Norm (lp E p μ) where norm f := ENNReal.toReal (snorm f p μ)

-- note: we need this to be defeq to the instance from `seminormed_add_group.to_has_nnnorm`, so
-- can't use `ennreal.to_nnreal (snorm f p μ)`
instance : NNNorm (lp E p μ) where nnnorm f := ⟨‖f‖, ENNReal.toReal_nonneg⟩

instance : Dist (lp E p μ) where dist f g := ‖f - g‖

instance : EDist (lp E p μ) where edist f g := snorm (f - g) p μ

theorem norm_def (f : lp E p μ) : ‖f‖ = ENNReal.toReal (snorm f p μ) :=
  rfl
#align measure_theory.Lp.norm_def MeasureTheory.lp.norm_def

theorem nnnorm_def (f : lp E p μ) : ‖f‖₊ = ENNReal.toNNReal (snorm f p μ) :=
  Subtype.eta _ _
#align measure_theory.Lp.nnnorm_def MeasureTheory.lp.nnnorm_def

@[simp, norm_cast]
protected theorem coe_nnnorm (f : lp E p μ) : (‖f‖₊ : ℝ) = ‖f‖ :=
  rfl
#align measure_theory.Lp.coe_nnnorm MeasureTheory.lp.coe_nnnorm

@[simp]
theorem norm_toLp (f : α → E) (hf : Memℒp f p μ) : ‖hf.toLp f‖ = ENNReal.toReal (snorm f p μ) := by
  rw [norm_def, snorm_congr_ae (mem_ℒp.coe_fn_to_Lp hf)]
#align measure_theory.Lp.norm_to_Lp MeasureTheory.lp.norm_toLp

@[simp]
theorem nnnorm_toLp (f : α → E) (hf : Memℒp f p μ) :
    ‖hf.toLp f‖₊ = ENNReal.toNNReal (snorm f p μ) :=
  NNReal.eq <| norm_toLp f hf
#align measure_theory.Lp.nnnorm_to_Lp MeasureTheory.lp.nnnorm_toLp

theorem dist_def (f g : lp E p μ) : dist f g = (snorm (f - g) p μ).toReal :=
  by
  simp_rw [dist, norm_def]
  congr 1
  apply snorm_congr_ae (coe_fn_sub _ _)
#align measure_theory.Lp.dist_def MeasureTheory.lp.dist_def

theorem edist_def (f g : lp E p μ) : edist f g = snorm (f - g) p μ :=
  rfl
#align measure_theory.Lp.edist_def MeasureTheory.lp.edist_def

@[simp]
theorem edist_toLp_toLp (f g : α → E) (hf : Memℒp f p μ) (hg : Memℒp g p μ) :
    edist (hf.toLp f) (hg.toLp g) = snorm (f - g) p μ := by rw [edist_def];
  exact snorm_congr_ae (hf.coe_fn_to_Lp.sub hg.coe_fn_to_Lp)
#align measure_theory.Lp.edist_to_Lp_to_Lp MeasureTheory.lp.edist_toLp_toLp

@[simp]
theorem edist_toLp_zero (f : α → E) (hf : Memℒp f p μ) : edist (hf.toLp f) 0 = snorm f p μ := by
  convert edist_to_Lp_to_Lp f 0 hf zero_mem_ℒp; simp
#align measure_theory.Lp.edist_to_Lp_zero MeasureTheory.lp.edist_toLp_zero

@[simp]
theorem nnnorm_zero : ‖(0 : lp E p μ)‖₊ = 0 :=
  by
  rw [nnnorm_def]
  change (snorm (⇑(0 : α →ₘ[μ] E)) p μ).toNNReal = 0
  simp [snorm_congr_ae ae_eq_fun.coe_fn_zero, snorm_zero]
#align measure_theory.Lp.nnnorm_zero MeasureTheory.lp.nnnorm_zero

@[simp]
theorem norm_zero : ‖(0 : lp E p μ)‖ = 0 :=
  congr_arg coe nnnorm_zero
#align measure_theory.Lp.norm_zero MeasureTheory.lp.norm_zero

theorem nnnorm_eq_zero_iff {f : lp E p μ} (hp : 0 < p) : ‖f‖₊ = 0 ↔ f = 0 :=
  by
  refine' ⟨fun hf => _, fun hf => by simp [hf]⟩
  rw [nnnorm_def, ENNReal.toNNReal_eq_zero_iff] at hf
  cases hf
  · rw [snorm_eq_zero_iff (Lp.ae_strongly_measurable f) hp.ne.symm] at hf
    exact Subtype.eq (ae_eq_fun.ext (hf.trans ae_eq_fun.coe_fn_zero.symm))
  · exact absurd hf (snorm_ne_top f)
#align measure_theory.Lp.nnnorm_eq_zero_iff MeasureTheory.lp.nnnorm_eq_zero_iff

theorem norm_eq_zero_iff {f : lp E p μ} (hp : 0 < p) : ‖f‖ = 0 ↔ f = 0 :=
  Iff.symm <| (nnnorm_eq_zero_iff hp).symm.trans <| (NNReal.coe_eq_zero _).symm
#align measure_theory.Lp.norm_eq_zero_iff MeasureTheory.lp.norm_eq_zero_iff

theorem eq_zero_iff_ae_eq_zero {f : lp E p μ} : f = 0 ↔ f =ᵐ[μ] 0 :=
  by
  constructor
  · intro h
    rw [h]
    exact ae_eq_fun.coe_fn_const _ _
  · intro h
    ext1
    filter_upwards [h, ae_eq_fun.coe_fn_const α (0 : E)]with _ ha h'a
    rw [ha]
    exact h'a.symm
#align measure_theory.Lp.eq_zero_iff_ae_eq_zero MeasureTheory.lp.eq_zero_iff_ae_eq_zero

@[simp]
theorem nnnorm_neg (f : lp E p μ) : ‖-f‖₊ = ‖f‖₊ := by
  rw [nnnorm_def, nnnorm_def, snorm_congr_ae (coe_fn_neg _), snorm_neg]
#align measure_theory.Lp.nnnorm_neg MeasureTheory.lp.nnnorm_neg

@[simp]
theorem norm_neg (f : lp E p μ) : ‖-f‖ = ‖f‖ :=
  (congr_arg (coe : ℝ≥0 → ℝ) (nnnorm_neg f) : _)
#align measure_theory.Lp.norm_neg MeasureTheory.lp.norm_neg

theorem nnnorm_le_mul_nnnorm_of_ae_le_mul {c : ℝ≥0} {f : lp E p μ} {g : lp F p μ}
    (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊) : ‖f‖₊ ≤ c * ‖g‖₊ :=
  by
  simp only [nnnorm_def]
  have := snorm_le_nnreal_smul_snorm_of_ae_le_mul h p
  rwa [← ENNReal.toNNReal_le_toNNReal, ENNReal.smul_def, smul_eq_mul, ENNReal.toNNReal_mul,
    ENNReal.toNNReal_coe] at this
  · exact (Lp.mem_ℒp _).snorm_ne_top
  · exact ENNReal.mul_ne_top ENNReal.coe_ne_top (Lp.mem_ℒp _).snorm_ne_top
#align measure_theory.Lp.nnnorm_le_mul_nnnorm_of_ae_le_mul MeasureTheory.lp.nnnorm_le_mul_nnnorm_of_ae_le_mul

theorem norm_le_mul_norm_of_ae_le_mul {c : ℝ} {f : lp E p μ} {g : lp F p μ}
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) : ‖f‖ ≤ c * ‖g‖ :=
  by
  cases' le_or_lt 0 c with hc hc
  · lift c to ℝ≥0 using hc
    exact nnreal.coe_le_coe.mpr (nnnorm_le_mul_nnnorm_of_ae_le_mul h)
  · simp only [norm_def]
    have := snorm_eq_zero_and_zero_of_ae_le_mul_neg h hc p
    simp [this]
#align measure_theory.Lp.norm_le_mul_norm_of_ae_le_mul MeasureTheory.lp.norm_le_mul_norm_of_ae_le_mul

theorem norm_le_norm_of_ae_le {f : lp E p μ} {g : lp F p μ} (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
    ‖f‖ ≤ ‖g‖ :=
  by
  rw [norm_def, norm_def, ENNReal.toReal_le_toReal (snorm_ne_top _) (snorm_ne_top _)]
  exact snorm_mono_ae h
#align measure_theory.Lp.norm_le_norm_of_ae_le MeasureTheory.lp.norm_le_norm_of_ae_le

theorem mem_lp_of_nnnorm_ae_le_mul {c : ℝ≥0} {f : α →ₘ[μ] E} {g : lp F p μ}
    (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊) : f ∈ lp E p μ :=
  mem_lp_iff_memℒp.2 <| Memℒp.of_nnnorm_le_mul (lp.memℒp g) f.AEStronglyMeasurable h
#align measure_theory.Lp.mem_Lp_of_nnnorm_ae_le_mul MeasureTheory.lp.mem_lp_of_nnnorm_ae_le_mul

theorem mem_lp_of_ae_le_mul {c : ℝ} {f : α →ₘ[μ] E} {g : lp F p μ}
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) : f ∈ lp E p μ :=
  mem_lp_iff_memℒp.2 <| Memℒp.of_le_mul (lp.memℒp g) f.AEStronglyMeasurable h
#align measure_theory.Lp.mem_Lp_of_ae_le_mul MeasureTheory.lp.mem_lp_of_ae_le_mul

theorem mem_lp_of_nnnorm_ae_le {f : α →ₘ[μ] E} {g : lp F p μ} (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ ‖g x‖₊) :
    f ∈ lp E p μ :=
  mem_lp_iff_memℒp.2 <| Memℒp.of_le (lp.memℒp g) f.AEStronglyMeasurable h
#align measure_theory.Lp.mem_Lp_of_nnnorm_ae_le MeasureTheory.lp.mem_lp_of_nnnorm_ae_le

theorem mem_lp_of_ae_le {f : α →ₘ[μ] E} {g : lp F p μ} (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
    f ∈ lp E p μ :=
  mem_lp_of_nnnorm_ae_le h
#align measure_theory.Lp.mem_Lp_of_ae_le MeasureTheory.lp.mem_lp_of_ae_le

theorem mem_lp_of_ae_nnnorm_bound [FiniteMeasure μ] {f : α →ₘ[μ] E} (C : ℝ≥0)
    (hfC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) : f ∈ lp E p μ :=
  mem_lp_iff_memℒp.2 <| Memℒp.of_bound f.AEStronglyMeasurable _ hfC
#align measure_theory.Lp.mem_Lp_of_ae_nnnorm_bound MeasureTheory.lp.mem_lp_of_ae_nnnorm_bound

theorem mem_lp_of_ae_bound [FiniteMeasure μ] {f : α →ₘ[μ] E} (C : ℝ) (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    f ∈ lp E p μ :=
  mem_lp_iff_memℒp.2 <| Memℒp.of_bound f.AEStronglyMeasurable _ hfC
#align measure_theory.Lp.mem_Lp_of_ae_bound MeasureTheory.lp.mem_lp_of_ae_bound

theorem nnnorm_le_of_ae_bound [FiniteMeasure μ] {f : lp E p μ} {C : ℝ≥0}
    (hfC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) : ‖f‖₊ ≤ measureUnivNNReal μ ^ p.toReal⁻¹ * C :=
  by
  by_cases hμ : μ = 0
  · by_cases hp : p.to_real⁻¹ = 0
    · simp [hp, hμ, nnnorm_def]
    · simp [hμ, nnnorm_def, Real.zero_rpow hp]
  rw [← ENNReal.coe_le_coe, nnnorm_def, ENNReal.coe_toNNReal (snorm_ne_top _)]
  refine' (snorm_le_of_ae_nnnorm_bound hfC).trans_eq _
  rw [← coe_measure_univ_nnreal μ, ENNReal.coe_rpow_of_ne_zero (measure_univ_nnreal_pos hμ).ne',
    ENNReal.coe_mul, mul_comm, ENNReal.smul_def, smul_eq_mul]
#align measure_theory.Lp.nnnorm_le_of_ae_bound MeasureTheory.lp.nnnorm_le_of_ae_bound

theorem norm_le_of_ae_bound [FiniteMeasure μ] {f : lp E p μ} {C : ℝ} (hC : 0 ≤ C)
    (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : ‖f‖ ≤ measureUnivNNReal μ ^ p.toReal⁻¹ * C :=
  by
  lift C to ℝ≥0 using hC
  have := nnnorm_le_of_ae_bound hfC
  rwa [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_rpow] at this
#align measure_theory.Lp.norm_le_of_ae_bound MeasureTheory.lp.norm_le_of_ae_bound

instance [hp : Fact (1 ≤ p)] : NormedAddCommGroup (lp E p μ) :=
  {
    AddGroupNorm.toNormedAddCommGroup
      { toFun := (norm : lp E p μ → ℝ)
        map_zero' := norm_zero
        neg' := by simp
        add_le' := fun f g => by
          simp only [norm_def]
          rw [← ENNReal.toReal_add (snorm_ne_top f) (snorm_ne_top g)]
          suffices h_snorm : snorm (⇑(f + g)) p μ ≤ snorm (⇑f) p μ + snorm (⇑g) p μ
          · rwa [ENNReal.toReal_le_toReal (snorm_ne_top (f + g))]
            exact ennreal.add_ne_top.mpr ⟨snorm_ne_top f, snorm_ne_top g⟩
          rw [snorm_congr_ae (coe_fn_add _ _)]
          exact snorm_add_le (Lp.ae_strongly_measurable f) (Lp.ae_strongly_measurable g) hp.1
        eq_zero_of_map_eq_zero' := fun f =>
          (norm_eq_zero_iff <|
              zero_lt_one.trans_le hp.1).1 } with
    edist := edist
    edist_dist := fun f g => by
      rw [edist_def, dist_def, ← snorm_congr_ae (coe_fn_sub _ _),
        ENNReal.ofReal_toReal (snorm_ne_top (f - g))] }

-- check no diamond is created
example [Fact (1 ≤ p)] : PseudoEMetricSpace.toHasEdist = (lp.hasEdist : EDist (lp E p μ)) :=
  rfl

example [Fact (1 ≤ p)] : SeminormedAddGroup.toNNNorm = (lp.hasNnnorm : NNNorm (lp E p μ)) :=
  rfl

section BoundedSMul

variable {𝕜 𝕜' : Type _}

variable [NormedRing 𝕜] [NormedRing 𝕜'] [Module 𝕜 E] [Module 𝕜' E]

variable [BoundedSMul 𝕜 E] [BoundedSMul 𝕜' E]

theorem mem_lp_const_smul (c : 𝕜) (f : lp E p μ) : c • ↑f ∈ lp E p μ :=
  by
  rw [mem_Lp_iff_snorm_lt_top, snorm_congr_ae (ae_eq_fun.coe_fn_smul _ _)]
  refine' (snorm_const_smul_le _ _).trans_lt _
  rw [ENNReal.smul_def, smul_eq_mul, ENNReal.mul_lt_top_iff]
  exact Or.inl ⟨ENNReal.coe_lt_top, f.prop⟩
#align measure_theory.Lp.mem_Lp_const_smul MeasureTheory.lp.mem_lp_const_smul

variable (E p μ 𝕜)

/-- The `𝕜`-submodule of elements of `α →ₘ[μ] E` whose `Lp` norm is finite.  This is `Lp E p μ`,
with extra structure. -/
def lpSubmodule : Submodule 𝕜 (α →ₘ[μ] E) :=
  { lp E p μ with smul_mem' := fun c f hf => by simpa using mem_Lp_const_smul c ⟨f, hf⟩ }
#align measure_theory.Lp.Lp_submodule MeasureTheory.lp.lpSubmodule

variable {E p μ 𝕜}

theorem coe_lpSubmodule : (lpSubmodule E p μ 𝕜).toAddSubgroup = lp E p μ :=
  rfl
#align measure_theory.Lp.coe_Lp_submodule MeasureTheory.lp.coe_lpSubmodule

instance : Module 𝕜 (lp E p μ) :=
  { (lpSubmodule E p μ 𝕜).Module with }

theorem coeFn_smul (c : 𝕜) (f : lp E p μ) : ⇑(c • f) =ᵐ[μ] c • f :=
  AEEqFun.coeFn_smul _ _
#align measure_theory.Lp.coe_fn_smul MeasureTheory.lp.coeFn_smul

instance [Module 𝕜ᵐᵒᵖ E] [BoundedSMul 𝕜ᵐᵒᵖ E] [IsCentralScalar 𝕜 E] : IsCentralScalar 𝕜 (lp E p μ)
    where op_smul_eq_smul k f := Subtype.ext <| op_smul_eq_smul k (f : α →ₘ[μ] E)

instance [SMulCommClass 𝕜 𝕜' E] : SMulCommClass 𝕜 𝕜' (lp E p μ)
    where smul_comm k k' f := Subtype.ext <| smul_comm k k' (f : α →ₘ[μ] E)

instance [SMul 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' E] : IsScalarTower 𝕜 𝕜' (lp E p μ)
    where smul_assoc k k' f := Subtype.ext <| smul_assoc k k' (f : α →ₘ[μ] E)

instance [Fact (1 ≤ p)] : BoundedSMul 𝕜 (lp E p μ) :=
  -- TODO: add `has_bounded_smul.of_nnnorm_smul_le
    BoundedSMul.of_norm_smul_le
    fun r f => by
    suffices (‖r • f‖₊ : ℝ≥0∞) ≤ ‖r‖₊ * ‖f‖₊ by exact_mod_cast this
    rw [nnnorm_def, nnnorm_def, ENNReal.coe_toNNReal (Lp.snorm_ne_top _),
      snorm_congr_ae (coe_fn_smul _ _), ENNReal.coe_toNNReal (Lp.snorm_ne_top _)]
    exact snorm_const_smul_le r f

end BoundedSMul

section NormedSpace

variable {𝕜 : Type _} [NormedField 𝕜] [NormedSpace 𝕜 E]

instance [Fact (1 ≤ p)] : NormedSpace 𝕜 (lp E p μ) where norm_smul_le _ _ := norm_smul_le _ _

end NormedSpace

end Lp

namespace Memℒp

variable {𝕜 : Type _} [NormedRing 𝕜] [Module 𝕜 E] [BoundedSMul 𝕜 E]

theorem toLp_const_smul {f : α → E} (c : 𝕜) (hf : Memℒp f p μ) :
    (hf.const_smul c).toLp (c • f) = c • hf.toLp f :=
  rfl
#align measure_theory.mem_ℒp.to_Lp_const_smul MeasureTheory.Memℒp.toLp_const_smul

end Memℒp

/-! ### Indicator of a set as an element of Lᵖ

For a set `s` with `(hs : measurable_set s)` and `(hμs : μ s < ∞)`, we build
`indicator_const_Lp p hs hμs c`, the element of `Lp` corresponding to `s.indicator (λ x, c)`.
-/


section Indicator

variable {s : Set α} {hs : MeasurableSet s} {c : E} {f : α → E} {hf : AEStronglyMeasurable f μ}

theorem snormEssSup_indicator_le (s : Set α) (f : α → G) :
    snormEssSup (s.indicator f) μ ≤ snormEssSup f μ :=
  by
  refine' essSup_mono_ae (eventually_of_forall fun x => _)
  rw [ENNReal.coe_le_coe, nnnorm_indicator_eq_indicator_nnnorm]
  exact Set.indicator_le_self s _ x
#align measure_theory.snorm_ess_sup_indicator_le MeasureTheory.snormEssSup_indicator_le

theorem snormEssSup_indicator_const_le (s : Set α) (c : G) :
    snormEssSup (s.indicator fun x : α => c) μ ≤ ‖c‖₊ :=
  by
  by_cases hμ0 : μ = 0
  · rw [hμ0, snorm_ess_sup_measure_zero]
    exact zero_le _
  · exact (snorm_ess_sup_indicator_le s fun x => c).trans (snorm_ess_sup_const c hμ0).le
#align measure_theory.snorm_ess_sup_indicator_const_le MeasureTheory.snormEssSup_indicator_const_le

theorem snormEssSup_indicator_const_eq (s : Set α) (c : G) (hμs : μ s ≠ 0) :
    snormEssSup (s.indicator fun x : α => c) μ = ‖c‖₊ :=
  by
  refine' le_antisymm (snorm_ess_sup_indicator_const_le s c) _
  by_contra' h
  have h' := ae_iff.mp (ae_lt_of_essSup_lt h)
  push_neg  at h'
  refine' hμs (measure_mono_null (fun x hx_mem => _) h')
  rw [Set.mem_setOf_eq, Set.indicator_of_mem hx_mem]
  exact le_rfl
#align measure_theory.snorm_ess_sup_indicator_const_eq MeasureTheory.snormEssSup_indicator_const_eq

variable (hs)

theorem snorm_indicator_le {E : Type _} [NormedAddCommGroup E] (f : α → E) :
    snorm (s.indicator f) p μ ≤ snorm f p μ :=
  by
  refine' snorm_mono_ae (eventually_of_forall fun x => _)
  suffices ‖s.indicator f x‖₊ ≤ ‖f x‖₊ by exact NNReal.coe_mono this
  rw [nnnorm_indicator_eq_indicator_nnnorm]
  exact s.indicator_le_self _ x
#align measure_theory.snorm_indicator_le MeasureTheory.snorm_indicator_le

variable {hs}

theorem snorm_indicator_const {c : G} (hs : MeasurableSet s) (hp : p ≠ 0) (hp_top : p ≠ ∞) :
    snorm (s.indicator fun x => c) p μ = ‖c‖₊ * μ s ^ (1 / p.toReal) :=
  by
  have hp_pos : 0 < p.to_real := ENNReal.toReal_pos hp hp_top
  rw [snorm_eq_lintegral_rpow_nnnorm hp hp_top]
  simp_rw [nnnorm_indicator_eq_indicator_nnnorm, ENNReal.coe_indicator]
  have h_indicator_pow :
    (fun a : α => s.indicator (fun x : α => (‖c‖₊ : ℝ≥0∞)) a ^ p.to_real) =
      s.indicator fun x : α => ↑‖c‖₊ ^ p.to_real :=
    by
    rw [Set.comp_indicator_const (‖c‖₊ : ℝ≥0∞) (fun x => x ^ p.to_real) _]
    simp [hp_pos]
  rw [h_indicator_pow, lintegral_indicator _ hs, set_lintegral_const, ENNReal.mul_rpow_of_nonneg]
  · rw [← ENNReal.rpow_mul, mul_one_div_cancel hp_pos.ne.symm, ENNReal.rpow_one]
  · simp [hp_pos.le]
#align measure_theory.snorm_indicator_const MeasureTheory.snorm_indicator_const

theorem snorm_indicator_const' {c : G} (hs : MeasurableSet s) (hμs : μ s ≠ 0) (hp : p ≠ 0) :
    snorm (s.indicator fun _ => c) p μ = ‖c‖₊ * μ s ^ (1 / p.toReal) :=
  by
  by_cases hp_top : p = ∞
  · simp [hp_top, snorm_ess_sup_indicator_const_eq s c hμs]
  · exact snorm_indicator_const hs hp hp_top
#align measure_theory.snorm_indicator_const' MeasureTheory.snorm_indicator_const'

theorem snorm_indicator_const_le (c : G) (p : ℝ≥0∞) :
    snorm (s.indicator fun x => c) p μ ≤ ‖c‖₊ * μ s ^ (1 / p.toReal) :=
  by
  rcases eq_or_ne p 0 with (rfl | hp)
  · simp only [snorm_exponent_zero, zero_le']
  rcases eq_or_ne p ∞ with (rfl | h'p)
  · simp only [snorm_exponent_top, ENNReal.top_toReal, div_zero, ENNReal.rpow_zero, mul_one]
    exact snorm_ess_sup_indicator_const_le _ _
  let t := to_measurable μ s
  calc
    snorm (s.indicator fun x => c) p μ ≤ snorm (t.indicator fun x => c) p μ :=
      snorm_mono (norm_indicator_le_of_subset (subset_to_measurable _ _) _)
    _ = ‖c‖₊ * μ t ^ (1 / p.to_real) :=
      (snorm_indicator_const (measurable_set_to_measurable _ _) hp h'p)
    _ = ‖c‖₊ * μ s ^ (1 / p.to_real) := by rw [measure_to_measurable]
    
#align measure_theory.snorm_indicator_const_le MeasureTheory.snorm_indicator_const_le

theorem Memℒp.indicator (hs : MeasurableSet s) (hf : Memℒp f p μ) : Memℒp (s.indicator f) p μ :=
  ⟨hf.AEStronglyMeasurable.indicator hs, lt_of_le_of_lt (snorm_indicator_le f) hf.snorm_lt_top⟩
#align measure_theory.mem_ℒp.indicator MeasureTheory.Memℒp.indicator

theorem snormEssSup_indicator_eq_snormEssSup_restrict {f : α → F} (hs : MeasurableSet s) :
    snormEssSup (s.indicator f) μ = snormEssSup f (μ.restrict s) :=
  by
  simp_rw [snorm_ess_sup, nnnorm_indicator_eq_indicator_nnnorm, ENNReal.coe_indicator]
  by_cases hs_null : μ s = 0
  · rw [measure.restrict_zero_set hs_null]
    simp only [essSup_measure_zero, ENNReal.essSup_eq_zero_iff, ENNReal.bot_eq_zero]
    have hs_empty : s =ᵐ[μ] (∅ : Set α) := by rw [ae_eq_set]; simpa using hs_null
    refine' (indicator_ae_eq_of_ae_eq_set hs_empty).trans _
    rw [Set.indicator_empty]
    rfl
  rw [essSup_indicator_eq_essSup_restrict (eventually_of_forall fun x => _) hs hs_null]
  rw [Pi.zero_apply]
  exact zero_le _
#align measure_theory.snorm_ess_sup_indicator_eq_snorm_ess_sup_restrict MeasureTheory.snormEssSup_indicator_eq_snormEssSup_restrict

theorem snorm_indicator_eq_snorm_restrict {f : α → F} (hs : MeasurableSet s) :
    snorm (s.indicator f) p μ = snorm f p (μ.restrict s) :=
  by
  by_cases hp_zero : p = 0
  · simp only [hp_zero, snorm_exponent_zero]
  by_cases hp_top : p = ∞
  · simp_rw [hp_top, snorm_exponent_top]
    exact snorm_ess_sup_indicator_eq_snorm_ess_sup_restrict hs
  simp_rw [snorm_eq_lintegral_rpow_nnnorm hp_zero hp_top]
  suffices (∫⁻ x, ‖s.indicator f x‖₊ ^ p.to_real ∂μ) = ∫⁻ x in s, ‖f x‖₊ ^ p.to_real ∂μ by rw [this]
  rw [← lintegral_indicator _ hs]
  congr
  simp_rw [nnnorm_indicator_eq_indicator_nnnorm, ENNReal.coe_indicator]
  have h_zero : (fun x => x ^ p.to_real) (0 : ℝ≥0∞) = 0 := by
    simp [ENNReal.toReal_pos hp_zero hp_top]
  exact (Set.indicator_comp_of_zero h_zero).symm
#align measure_theory.snorm_indicator_eq_snorm_restrict MeasureTheory.snorm_indicator_eq_snorm_restrict

theorem memℒp_indicator_iff_restrict (hs : MeasurableSet s) :
    Memℒp (s.indicator f) p μ ↔ Memℒp f p (μ.restrict s) := by
  simp [mem_ℒp, aestronglyMeasurable_indicator_iff hs, snorm_indicator_eq_snorm_restrict hs]
#align measure_theory.mem_ℒp_indicator_iff_restrict MeasureTheory.memℒp_indicator_iff_restrict

theorem memℒp_indicator_const (p : ℝ≥0∞) (hs : MeasurableSet s) (c : E) (hμsc : c = 0 ∨ μ s ≠ ∞) :
    Memℒp (s.indicator fun _ => c) p μ :=
  by
  rw [mem_ℒp_indicator_iff_restrict hs]
  by_cases hp_zero : p = 0
  · rw [hp_zero]; exact mem_ℒp_zero_iff_ae_strongly_measurable.mpr ae_strongly_measurable_const
  by_cases hp_top : p = ∞
  · rw [hp_top]
    exact
      mem_ℒp_top_of_bound ae_strongly_measurable_const ‖c‖ (eventually_of_forall fun x => le_rfl)
  rw [mem_ℒp_const_iff hp_zero hp_top, measure.restrict_apply_univ]
  cases hμsc
  · exact Or.inl hμsc
  · exact Or.inr hμsc.lt_top
#align measure_theory.mem_ℒp_indicator_const MeasureTheory.memℒp_indicator_const

/-- The `ℒ^p` norm of the indicator of a set is uniformly small if the set itself has small measure,
for any `p < ∞`. Given here as an existential `∀ ε > 0, ∃ η > 0, ...` to avoid later
management of `ℝ≥0∞`-arithmetic. -/
theorem exists_snorm_indicator_le (hp : p ≠ ∞) (c : E) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ η : ℝ≥0, 0 < η ∧ ∀ s : Set α, μ s ≤ η → snorm (s.indicator fun x => c) p μ ≤ ε :=
  by
  rcases eq_or_ne p 0 with (rfl | h'p)
  · exact ⟨1, zero_lt_one, fun s hs => by simp⟩
  have hp₀ : 0 < p := bot_lt_iff_ne_bot.2 h'p
  have hp₀' : 0 ≤ 1 / p.to_real := div_nonneg zero_le_one ENNReal.toReal_nonneg
  have hp₀'' : 0 < p.to_real := by
    simpa [← ENNReal.toReal_lt_toReal ENNReal.zero_ne_top hp] using hp₀
  obtain ⟨η, hη_pos, hη_le⟩ : ∃ η : ℝ≥0, 0 < η ∧ (‖c‖₊ * η ^ (1 / p.to_real) : ℝ≥0∞) ≤ ε :=
    by
    have :
      Filter.Tendsto (fun x : ℝ≥0 => ((‖c‖₊ * x ^ (1 / p.to_real) : ℝ≥0) : ℝ≥0∞)) (𝓝 0)
        (𝓝 (0 : ℝ≥0)) :=
      by
      rw [ENNReal.tendsto_coe]
      convert(NNReal.continuousAt_rpow_const (Or.inr hp₀')).Tendsto.const_mul _
      simp [hp₀''.ne']
    have hε' : 0 < ε := hε.bot_lt
    obtain ⟨δ, hδ, hδε'⟩ :=
      nnreal.nhds_zero_basis.eventually_iff.mp (eventually_le_of_tendsto_lt hε' this)
    obtain ⟨η, hη, hηδ⟩ := exists_between hδ
    refine' ⟨η, hη, _⟩
    rw [ENNReal.coe_rpow_of_nonneg _ hp₀', ← ENNReal.coe_mul]
    exact hδε' hηδ
  refine' ⟨η, hη_pos, fun s hs => _⟩
  refine' (snorm_indicator_const_le _ _).trans (le_trans _ hη_le)
  exact mul_le_mul_left' (ENNReal.rpow_le_rpow hs hp₀') _
#align measure_theory.exists_snorm_indicator_le MeasureTheory.exists_snorm_indicator_le

end Indicator

section IndicatorConstLp

open Set Function

variable {s : Set α} {hs : MeasurableSet s} {hμs : μ s ≠ ∞} {c : E}

/-- Indicator of a set as an element of `Lp`. -/
def indicatorConstLp (p : ℝ≥0∞) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) : lp E p μ :=
  Memℒp.toLp (s.indicator fun _ => c) (memℒp_indicator_const p hs c (Or.inr hμs))
#align measure_theory.indicator_const_Lp MeasureTheory.indicatorConstLp

theorem indicatorConstLp_coeFn : ⇑(indicatorConstLp p hs hμs c) =ᵐ[μ] s.indicator fun _ => c :=
  Memℒp.coeFn_toLp (memℒp_indicator_const p hs c (Or.inr hμs))
#align measure_theory.indicator_const_Lp_coe_fn MeasureTheory.indicatorConstLp_coeFn

theorem indicatorConstLp_coeFn_mem : ∀ᵐ x : α ∂μ, x ∈ s → indicatorConstLp p hs hμs c x = c :=
  indicatorConstLp_coeFn.mono fun x hx hxs => hx.trans (Set.indicator_of_mem hxs _)
#align measure_theory.indicator_const_Lp_coe_fn_mem MeasureTheory.indicatorConstLp_coeFn_mem

theorem indicatorConstLp_coeFn_nmem : ∀ᵐ x : α ∂μ, x ∉ s → indicatorConstLp p hs hμs c x = 0 :=
  indicatorConstLp_coeFn.mono fun x hx hxs => hx.trans (Set.indicator_of_not_mem hxs _)
#align measure_theory.indicator_const_Lp_coe_fn_nmem MeasureTheory.indicatorConstLp_coeFn_nmem

theorem norm_indicatorConstLp (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    ‖indicatorConstLp p hs hμs c‖ = ‖c‖ * (μ s).toReal ^ (1 / p.toReal) := by
  rw [Lp.norm_def, snorm_congr_ae indicator_const_Lp_coe_fn,
    snorm_indicator_const hs hp_ne_zero hp_ne_top, ENNReal.toReal_mul, ENNReal.toReal_rpow,
    ENNReal.coe_toReal, coe_nnnorm]
#align measure_theory.norm_indicator_const_Lp MeasureTheory.norm_indicatorConstLp

theorem norm_indicatorConstLp_top (hμs_ne_zero : μ s ≠ 0) : ‖indicatorConstLp ∞ hs hμs c‖ = ‖c‖ :=
  by
  rw [Lp.norm_def, snorm_congr_ae indicator_const_Lp_coe_fn,
    snorm_indicator_const' hs hμs_ne_zero ENNReal.top_ne_zero, ENNReal.top_toReal, div_zero,
    ENNReal.rpow_zero, mul_one, ENNReal.coe_toReal, coe_nnnorm]
#align measure_theory.norm_indicator_const_Lp_top MeasureTheory.norm_indicatorConstLp_top

theorem norm_indicator_const_Lp' (hp_pos : p ≠ 0) (hμs_pos : μ s ≠ 0) :
    ‖indicatorConstLp p hs hμs c‖ = ‖c‖ * (μ s).toReal ^ (1 / p.toReal) :=
  by
  by_cases hp_top : p = ∞
  · rw [hp_top, ENNReal.top_toReal, div_zero, Real.rpow_zero, mul_one]
    exact norm_indicator_const_Lp_top hμs_pos
  · exact norm_indicator_const_Lp hp_pos hp_top
#align measure_theory.norm_indicator_const_Lp' MeasureTheory.norm_indicator_const_Lp'

@[simp]
theorem indicator_const_empty : indicatorConstLp p MeasurableSet.empty (by simp : μ ∅ ≠ ∞) c = 0 :=
  by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  convert indicator_const_Lp_coe_fn
  simp [Set.indicator_empty']
#align measure_theory.indicator_const_empty MeasureTheory.indicator_const_empty

theorem memℒp_add_of_disjoint {f g : α → E} (h : Disjoint (support f) (support g))
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    Memℒp (f + g) p μ ↔ Memℒp f p μ ∧ Memℒp g p μ :=
  by
  borelize E
  refine' ⟨fun hfg => ⟨_, _⟩, fun h => h.1.add h.2⟩
  · rw [← indicator_add_eq_left h]; exact hfg.indicator (measurableSet_support hf.measurable)
  · rw [← indicator_add_eq_right h]; exact hfg.indicator (measurableSet_support hg.measurable)
#align measure_theory.mem_ℒp_add_of_disjoint MeasureTheory.memℒp_add_of_disjoint

/-- The indicator of a disjoint union of two sets is the sum of the indicators of the sets. -/
theorem indicatorConstLp_disjoint_union {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) (hst : s ∩ t = ∅) (c : E) :
    indicatorConstLp p (hs.union ht)
        ((measure_union_le s t).trans_lt
            (lt_top_iff_ne_top.mpr (ENNReal.add_ne_top.mpr ⟨hμs, hμt⟩))).Ne
        c =
      indicatorConstLp p hs hμs c + indicatorConstLp p ht hμt c :=
  by
  ext1
  refine' indicator_const_Lp_coe_fn.trans (eventually_eq.trans _ (Lp.coe_fn_add _ _).symm)
  refine'
    eventually_eq.trans _
      (eventually_eq.add indicator_const_Lp_coe_fn.symm indicator_const_Lp_coe_fn.symm)
  rw [Set.indicator_union_of_disjoint (set.disjoint_iff_inter_eq_empty.mpr hst) _]
#align measure_theory.indicator_const_Lp_disjoint_union MeasureTheory.indicatorConstLp_disjoint_union

end IndicatorConstLp

theorem Memℒp.norm_rpow_div {f : α → E} (hf : Memℒp f p μ) (q : ℝ≥0∞) :
    Memℒp (fun x : α => ‖f x‖ ^ q.toReal) (p / q) μ :=
  by
  refine' ⟨(hf.1.norm.AEMeasurable.pow_const q.to_real).AEStronglyMeasurable, _⟩
  by_cases q_top : q = ∞; · simp [q_top]
  by_cases q_zero : q = 0
  · simp [q_zero]
    by_cases p_zero : p = 0; · simp [p_zero]
    rw [ENNReal.div_zero p_zero]
    exact (mem_ℒp_top_const (1 : ℝ)).2
  rw [snorm_norm_rpow _ (ENNReal.toReal_pos q_zero q_top)]
  apply ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg
  rw [ENNReal.ofReal_toReal q_top, div_eq_mul_inv, mul_assoc, ENNReal.inv_mul_cancel q_zero q_top,
    mul_one]
  exact hf.2.Ne
#align measure_theory.mem_ℒp.norm_rpow_div MeasureTheory.Memℒp.norm_rpow_div

theorem memℒp_norm_rpow_iff {q : ℝ≥0∞} {f : α → E} (hf : AEStronglyMeasurable f μ) (q_zero : q ≠ 0)
    (q_top : q ≠ ∞) : Memℒp (fun x : α => ‖f x‖ ^ q.toReal) (p / q) μ ↔ Memℒp f p μ :=
  by
  refine' ⟨fun h => _, fun h => h.norm_rpow_div q⟩
  apply (mem_ℒp_norm_iff hf).1
  convert h.norm_rpow_div q⁻¹
  · ext x
    rw [Real.norm_eq_abs, Real.abs_rpow_of_nonneg (norm_nonneg _), ← Real.rpow_mul (abs_nonneg _),
      ENNReal.toReal_inv, mul_inv_cancel, abs_of_nonneg (norm_nonneg _), Real.rpow_one]
    simp [ENNReal.toReal_eq_zero_iff, not_or, q_zero, q_top]
  ·
    rw [div_eq_mul_inv, inv_inv, div_eq_mul_inv, mul_assoc, ENNReal.inv_mul_cancel q_zero q_top,
      mul_one]
#align measure_theory.mem_ℒp_norm_rpow_iff MeasureTheory.memℒp_norm_rpow_iff

theorem Memℒp.norm_rpow {f : α → E} (hf : Memℒp f p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    Memℒp (fun x : α => ‖f x‖ ^ p.toReal) 1 μ :=
  by
  convert hf.norm_rpow_div p
  rw [div_eq_mul_inv, ENNReal.mul_inv_cancel hp_ne_zero hp_ne_top]
#align measure_theory.mem_ℒp.norm_rpow MeasureTheory.Memℒp.norm_rpow

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

theorem LipschitzWith.comp_memℒp {α E F} {K} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedAddCommGroup F] {f : α → E} {g : E → F} (hg : LipschitzWith K g)
    (g0 : g 0 = 0) (hL : Memℒp f p μ) : Memℒp (g ∘ f) p μ :=
  haveI : ∀ x, ‖g (f x)‖ ≤ K * ‖f x‖ := by
    intro a
    -- TODO: add `lipschitz_with.nnnorm_sub_le` and `lipschitz_with.nnnorm_le`
    simpa [g0] using hg.norm_sub_le (f a) 0
  hL.of_le_mul (hg.continuous.comp_ae_strongly_measurable hL.1) (eventually_of_forall this)
#align lipschitz_with.comp_mem_ℒp LipschitzWith.comp_memℒp

theorem MeasureTheory.Memℒp.of_comp_antilipschitzWith {α E F} {K'} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup E] [NormedAddCommGroup F] {f : α → E} {g : E → F}
    (hL : Memℒp (g ∘ f) p μ) (hg : UniformContinuous g) (hg' : AntilipschitzWith K' g)
    (g0 : g 0 = 0) : Memℒp f p μ :=
  by
  have A : ∀ x, ‖f x‖ ≤ K' * ‖g (f x)‖ := by
    intro x
    -- TODO: add `antilipschitz_with.le_mul_nnnorm_sub` and `antilipschitz_with.le_mul_norm`
    rw [← dist_zero_right, ← dist_zero_right, ← g0]
    apply hg'.le_mul_dist
  have B : ae_strongly_measurable f μ :=
    (hg'.uniform_embedding hg).Embedding.aestronglyMeasurable_comp_iff.1 hL.1
  exact hL.of_le_mul B (Filter.eventually_of_forall A)
#align measure_theory.mem_ℒp.of_comp_antilipschitz_with MeasureTheory.Memℒp.of_comp_antilipschitzWith

namespace LipschitzWith

theorem memℒp_comp_iff_of_antilipschitz {α E F} {K K'} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedAddCommGroup F] {f : α → E} {g : E → F} (hg : LipschitzWith K g)
    (hg' : AntilipschitzWith K' g) (g0 : g 0 = 0) : Memℒp (g ∘ f) p μ ↔ Memℒp f p μ :=
  ⟨fun h => h.of_comp_antilipschitzWith hg.UniformContinuous hg' g0, fun h => hg.comp_memℒp g0 h⟩
#align lipschitz_with.mem_ℒp_comp_iff_of_antilipschitz LipschitzWith.memℒp_comp_iff_of_antilipschitz

/-- When `g` is a Lipschitz function sending `0` to `0` and `f` is in `Lp`, then `g ∘ f` is well
defined as an element of `Lp`. -/
def compLp (hg : LipschitzWith c g) (g0 : g 0 = 0) (f : lp E p μ) : lp F p μ :=
  ⟨AEEqFun.comp g hg.Continuous (f : α →ₘ[μ] E),
    by
    suffices ∀ᵐ x ∂μ, ‖ae_eq_fun.comp g hg.continuous (f : α →ₘ[μ] E) x‖ ≤ c * ‖f x‖ by
      exact Lp.mem_Lp_of_ae_le_mul this
    filter_upwards [ae_eq_fun.coe_fn_comp g hg.continuous (f : α →ₘ[μ] E)]with a ha
    simp only [ha]
    rw [← dist_zero_right, ← dist_zero_right, ← g0]
    exact hg.dist_le_mul (f a) 0⟩
#align lipschitz_with.comp_Lp LipschitzWith.compLp

theorem coeFn_compLp (hg : LipschitzWith c g) (g0 : g 0 = 0) (f : lp E p μ) :
    hg.compLp g0 f =ᵐ[μ] g ∘ f :=
  AEEqFun.coeFn_comp _ _ _
#align lipschitz_with.coe_fn_comp_Lp LipschitzWith.coeFn_compLp

@[simp]
theorem compLp_zero (hg : LipschitzWith c g) (g0 : g 0 = 0) : hg.compLp g0 (0 : lp E p μ) = 0 :=
  by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  apply (coe_fn_comp_Lp _ _ _).trans
  filter_upwards [Lp.coe_fn_zero E p μ]with _ ha
  simp [ha, g0]
#align lipschitz_with.comp_Lp_zero LipschitzWith.compLp_zero

theorem norm_compLp_sub_le (hg : LipschitzWith c g) (g0 : g 0 = 0) (f f' : lp E p μ) :
    ‖hg.compLp g0 f - hg.compLp g0 f'‖ ≤ c * ‖f - f'‖ :=
  by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hg.coe_fn_comp_Lp g0 f, hg.coe_fn_comp_Lp g0 f',
    Lp.coe_fn_sub (hg.comp_Lp g0 f) (hg.comp_Lp g0 f'), Lp.coe_fn_sub f f']with a ha1 ha2 ha3 ha4
  simp [ha1, ha2, ha3, ha4, ← dist_eq_norm]
  exact hg.dist_le_mul (f a) (f' a)
#align lipschitz_with.norm_comp_Lp_sub_le LipschitzWith.norm_compLp_sub_le

theorem norm_compLp_le (hg : LipschitzWith c g) (g0 : g 0 = 0) (f : lp E p μ) :
    ‖hg.compLp g0 f‖ ≤ c * ‖f‖ := by simpa using hg.norm_comp_Lp_sub_le g0 f 0
#align lipschitz_with.norm_comp_Lp_le LipschitzWith.norm_compLp_le

theorem lipschitzWith_compLp [Fact (1 ≤ p)] (hg : LipschitzWith c g) (g0 : g 0 = 0) :
    LipschitzWith c (hg.compLp g0 : lp E p μ → lp F p μ) :=
  LipschitzWith.of_dist_le_mul fun f g => by simp [dist_eq_norm, norm_comp_Lp_sub_le]
#align lipschitz_with.lipschitz_with_comp_Lp LipschitzWith.lipschitzWith_compLp

theorem continuous_compLp [Fact (1 ≤ p)] (hg : LipschitzWith c g) (g0 : g 0 = 0) :
    Continuous (hg.compLp g0 : lp E p μ → lp F p μ) :=
  (lipschitzWith_compLp hg g0).Continuous
#align lipschitz_with.continuous_comp_Lp LipschitzWith.continuous_compLp

end LipschitzWith

namespace ContinuousLinearMap

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

/-- Composing `f : Lp ` with `L : E →L[𝕜] F`. -/
def compLp (L : E →L[𝕜] F) (f : lp E p μ) : lp F p μ :=
  L.lipschitz.compLp (map_zero L) f
#align continuous_linear_map.comp_Lp ContinuousLinearMap.compLp

theorem coeFn_compLp (L : E →L[𝕜] F) (f : lp E p μ) : ∀ᵐ a ∂μ, (L.compLp f) a = L (f a) :=
  LipschitzWith.coeFn_compLp _ _ _
#align continuous_linear_map.coe_fn_comp_Lp ContinuousLinearMap.coeFn_compLp

theorem coeFn_comp_Lp' (L : E →L[𝕜] F) (f : lp E p μ) : L.compLp f =ᵐ[μ] fun a => L (f a) :=
  L.coeFn_compLp f
#align continuous_linear_map.coe_fn_comp_Lp' ContinuousLinearMap.coeFn_comp_Lp'

theorem comp_memℒp (L : E →L[𝕜] F) (f : lp E p μ) : Memℒp (L ∘ f) p μ :=
  (lp.memℒp (L.compLp f)).ae_eq (L.coeFn_comp_Lp' f)
#align continuous_linear_map.comp_mem_ℒp ContinuousLinearMap.comp_memℒp

theorem comp_mem_ℒp' (L : E →L[𝕜] F) {f : α → E} (hf : Memℒp f p μ) : Memℒp (L ∘ f) p μ :=
  (L.comp_memℒp (hf.toLp f)).ae_eq (EventuallyEq.fun_comp hf.coeFn_toLp _)
#align continuous_linear_map.comp_mem_ℒp' ContinuousLinearMap.comp_mem_ℒp'

section IsROrC

variable {K : Type _} [IsROrC K]

theorem MeasureTheory.Memℒp.of_real {f : α → ℝ} (hf : Memℒp f p μ) :
    Memℒp (fun x => (f x : K)) p μ :=
  (@IsROrC.ofRealClm K _).comp_mem_ℒp' hf
#align measure_theory.mem_ℒp.of_real MeasureTheory.Memℒp.of_real

theorem MeasureTheory.memℒp_re_im_iff {f : α → K} :
    Memℒp (fun x => IsROrC.re (f x)) p μ ∧ Memℒp (fun x => IsROrC.im (f x)) p μ ↔ Memℒp f p μ :=
  by
  refine' ⟨_, fun hf => ⟨hf.re, hf.im⟩⟩
  rintro ⟨hre, him⟩
  convert hre.of_real.add (him.of_real.const_mul IsROrC.i)
  · ext1 x
    rw [Pi.add_apply, mul_comm, IsROrC.re_add_im]
  all_goals infer_instance
#align measure_theory.mem_ℒp_re_im_iff MeasureTheory.memℒp_re_im_iff

end IsROrC

theorem add_compLp (L L' : E →L[𝕜] F) (f : lp E p μ) :
    (L + L').compLp f = L.compLp f + L'.compLp f :=
  by
  ext1
  refine' (coe_fn_comp_Lp' (L + L') f).trans _
  refine' eventually_eq.trans _ (Lp.coe_fn_add _ _).symm
  refine'
    eventually_eq.trans _ (eventually_eq.add (L.coe_fn_comp_Lp' f).symm (L'.coe_fn_comp_Lp' f).symm)
  refine' eventually_of_forall fun x => _
  rfl
#align continuous_linear_map.add_comp_Lp ContinuousLinearMap.add_compLp

theorem smul_compLp {𝕜'} [NormedRing 𝕜'] [Module 𝕜' F] [BoundedSMul 𝕜' F] [SMulCommClass 𝕜 𝕜' F]
    (c : 𝕜') (L : E →L[𝕜] F) (f : lp E p μ) : (c • L).compLp f = c • L.compLp f :=
  by
  ext1
  refine' (coe_fn_comp_Lp' (c • L) f).trans _
  refine' eventually_eq.trans _ (Lp.coe_fn_smul _ _).symm
  refine' (L.coe_fn_comp_Lp' f).mono fun x hx => _
  rw [Pi.smul_apply, hx]
  rfl
#align continuous_linear_map.smul_comp_Lp ContinuousLinearMap.smul_compLp

theorem norm_compLp_le (L : E →L[𝕜] F) (f : lp E p μ) : ‖L.compLp f‖ ≤ ‖L‖ * ‖f‖ :=
  LipschitzWith.norm_compLp_le _ _ _
#align continuous_linear_map.norm_comp_Lp_le ContinuousLinearMap.norm_compLp_le

variable (μ p)

/-- Composing `f : Lp E p μ` with `L : E →L[𝕜] F`, seen as a `𝕜`-linear map on `Lp E p μ`. -/
def compLpₗ (L : E →L[𝕜] F) : lp E p μ →ₗ[𝕜] lp F p μ
    where
  toFun f := L.compLp f
  map_add' := by
    intro f g
    ext1
    filter_upwards [Lp.coe_fn_add f g, coe_fn_comp_Lp L (f + g), coe_fn_comp_Lp L f,
      coe_fn_comp_Lp L g, Lp.coe_fn_add (L.comp_Lp f) (L.comp_Lp g)]
    intro a ha1 ha2 ha3 ha4 ha5
    simp only [ha1, ha2, ha3, ha4, ha5, map_add, Pi.add_apply]
  map_smul' := by
    intro c f
    dsimp
    ext1
    filter_upwards [Lp.coe_fn_smul c f, coe_fn_comp_Lp L (c • f), Lp.coe_fn_smul c (L.comp_Lp f),
      coe_fn_comp_Lp L f]with _ ha1 ha2 ha3 ha4
    simp only [ha1, ha2, ha3, ha4, SMulHomClass.map_smul, Pi.smul_apply]
#align continuous_linear_map.comp_Lpₗ ContinuousLinearMap.compLpₗ

/-- Composing `f : Lp E p μ` with `L : E →L[𝕜] F`, seen as a continuous `𝕜`-linear map on
`Lp E p μ`. See also the similar
* `linear_map.comp_left` for functions,
* `continuous_linear_map.comp_left_continuous` for continuous functions,
* `continuous_linear_map.comp_left_continuous_bounded` for bounded continuous functions,
* `continuous_linear_map.comp_left_continuous_compact` for continuous functions on compact spaces.
-/
def compLpL [Fact (1 ≤ p)] (L : E →L[𝕜] F) : lp E p μ →L[𝕜] lp F p μ :=
  LinearMap.mkContinuous (L.compLpₗ p μ) ‖L‖ L.norm_compLp_le
#align continuous_linear_map.comp_LpL ContinuousLinearMap.compLpL

variable {μ p}

theorem coeFn_compLpL [Fact (1 ≤ p)] (L : E →L[𝕜] F) (f : lp E p μ) :
    L.compLpL p μ f =ᵐ[μ] fun a => L (f a) :=
  L.coeFn_compLp f
#align continuous_linear_map.coe_fn_comp_LpL ContinuousLinearMap.coeFn_compLpL

theorem add_compLpL [Fact (1 ≤ p)] (L L' : E →L[𝕜] F) :
    (L + L').compLpL p μ = L.compLpL p μ + L'.compLpL p μ := by ext1 f; exact add_comp_Lp L L' f
#align continuous_linear_map.add_comp_LpL ContinuousLinearMap.add_compLpL

theorem smul_compLpL [Fact (1 ≤ p)] {𝕜'} [NormedRing 𝕜'] [Module 𝕜' F] [BoundedSMul 𝕜' F]
    [SMulCommClass 𝕜 𝕜' F] (c : 𝕜') (L : E →L[𝕜] F) : (c • L).compLpL p μ = c • L.compLpL p μ := by
  ext1 f; exact smul_comp_Lp c L f
#align continuous_linear_map.smul_comp_LpL ContinuousLinearMap.smul_compLpL

theorem norm_compLpL_le [Fact (1 ≤ p)] (L : E →L[𝕜] F) : ‖L.compLpL p μ‖ ≤ ‖L‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
#align continuous_linear_map.norm_compLpL_le ContinuousLinearMap.norm_compLpL_le

end ContinuousLinearMap

namespace MeasureTheory

theorem indicatorConstLp_eq_toSpanSingleton_compLp {s : Set α} [NormedSpace ℝ F]
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : F) :
    indicatorConstLp 2 hs hμs x =
      (ContinuousLinearMap.toSpanSingleton ℝ x).compLp (indicatorConstLp 2 hs hμs (1 : ℝ)) :=
  by
  ext1
  refine' indicator_const_Lp_coe_fn.trans _
  have h_comp_Lp :=
    (ContinuousLinearMap.toSpanSingleton ℝ x).coeFn_compLp (indicator_const_Lp 2 hs hμs (1 : ℝ))
  rw [← eventually_eq] at h_comp_Lp
  refine' eventually_eq.trans _ h_comp_Lp.symm
  refine' (@indicator_const_Lp_coe_fn _ _ _ 2 μ _ s hs hμs (1 : ℝ)).mono fun y hy => _
  dsimp only
  rw [hy]
  simp_rw [ContinuousLinearMap.toSpanSingleton_apply]
  by_cases hy_mem : y ∈ s <;> simp [hy_mem, ContinuousLinearMap.lsmul_apply]
#align measure_theory.indicator_const_Lp_eq_to_span_singleton_comp_Lp MeasureTheory.indicatorConstLp_eq_toSpanSingleton_compLp

namespace Lp

section PosPart

theorem lipschitzWith_pos_part : LipschitzWith 1 fun x : ℝ => max x 0 :=
  LipschitzWith.of_dist_le_mul fun x y => by simp [Real.dist_eq, abs_max_sub_max_le_abs]
#align measure_theory.Lp.lipschitz_with_pos_part MeasureTheory.lp.lipschitzWith_pos_part

theorem MeasureTheory.Memℒp.pos_part {f : α → ℝ} (hf : Memℒp f p μ) :
    Memℒp (fun x => max (f x) 0) p μ :=
  lipschitzWith_pos_part.comp_memℒp (max_eq_right le_rfl) hf
#align measure_theory.mem_ℒp.pos_part MeasureTheory.Memℒp.pos_part

theorem MeasureTheory.Memℒp.neg_part {f : α → ℝ} (hf : Memℒp f p μ) :
    Memℒp (fun x => max (-f x) 0) p μ :=
  lipschitzWith_pos_part.comp_memℒp (max_eq_right le_rfl) hf.neg
#align measure_theory.mem_ℒp.neg_part MeasureTheory.Memℒp.neg_part

/-- Positive part of a function in `L^p`. -/
def posPart (f : lp ℝ p μ) : lp ℝ p μ :=
  lipschitzWith_pos_part.compLp (max_eq_right le_rfl) f
#align measure_theory.Lp.pos_part MeasureTheory.lp.posPart

/-- Negative part of a function in `L^p`. -/
def negPart (f : lp ℝ p μ) : lp ℝ p μ :=
  posPart (-f)
#align measure_theory.Lp.neg_part MeasureTheory.lp.negPart

@[norm_cast]
theorem coe_posPart (f : lp ℝ p μ) : (posPart f : α →ₘ[μ] ℝ) = (f : α →ₘ[μ] ℝ).posPart :=
  rfl
#align measure_theory.Lp.coe_pos_part MeasureTheory.lp.coe_posPart

theorem coeFn_posPart (f : lp ℝ p μ) : ⇑(posPart f) =ᵐ[μ] fun a => max (f a) 0 :=
  AEEqFun.coeFn_posPart _
#align measure_theory.Lp.coe_fn_pos_part MeasureTheory.lp.coeFn_posPart

theorem coeFn_negPart_eq_max (f : lp ℝ p μ) : ∀ᵐ a ∂μ, negPart f a = max (-f a) 0 :=
  by
  rw [neg_part]
  filter_upwards [coe_fn_pos_part (-f), coe_fn_neg f]with _ h₁ h₂
  rw [h₁, h₂, Pi.neg_apply]
#align measure_theory.Lp.coe_fn_neg_part_eq_max MeasureTheory.lp.coeFn_negPart_eq_max

theorem coeFn_negPart (f : lp ℝ p μ) : ∀ᵐ a ∂μ, negPart f a = -min (f a) 0 :=
  (coeFn_negPart_eq_max f).mono fun a h => by rw [h, ← max_neg_neg, neg_zero]
#align measure_theory.Lp.coe_fn_neg_part MeasureTheory.lp.coeFn_negPart

theorem continuous_posPart [Fact (1 ≤ p)] : Continuous fun f : lp ℝ p μ => posPart f :=
  LipschitzWith.continuous_compLp _ _
#align measure_theory.Lp.continuous_pos_part MeasureTheory.lp.continuous_posPart

theorem continuous_negPart [Fact (1 ≤ p)] : Continuous fun f : lp ℝ p μ => negPart f :=
  by
  have eq : (fun f : lp ℝ p μ => negPart f) = fun f : lp ℝ p μ => posPart (-f) := rfl
  rw [Eq]
  exact continuous_pos_part.comp continuous_neg
#align measure_theory.Lp.continuous_neg_part MeasureTheory.lp.continuous_negPart

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

theorem snorm'_lim_eq_lintegral_liminf {ι} [Nonempty ι] [LinearOrder ι] {f : ι → α → G} {p : ℝ}
    (hp_nonneg : 0 ≤ p) {f_lim : α → G}
    (h_lim : ∀ᵐ x : α ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))) :
    snorm' f_lim p μ = (∫⁻ a, atTop.liminf fun m => (‖f m a‖₊ : ℝ≥0∞) ^ p ∂μ) ^ (1 / p) :=
  by
  suffices h_no_pow :
    (∫⁻ a, ‖f_lim a‖₊ ^ p ∂μ) = ∫⁻ a, at_top.liminf fun m => (‖f m a‖₊ : ℝ≥0∞) ^ p ∂μ
  · rw [snorm', h_no_pow]
  refine' lintegral_congr_ae (h_lim.mono fun a ha => _)
  rw [tendsto.liminf_eq]
  simp_rw [ENNReal.coe_rpow_of_nonneg _ hp_nonneg, ENNReal.tendsto_coe]
  refine' ((NNReal.continuous_rpow_const hp_nonneg).Tendsto ‖f_lim a‖₊).comp _
  exact (continuous_nnnorm.tendsto (f_lim a)).comp ha
#align measure_theory.Lp.snorm'_lim_eq_lintegral_liminf MeasureTheory.lp.snorm'_lim_eq_lintegral_liminf

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic filter.is_bounded_default -/
theorem snorm'_lim_le_liminf_snorm' {E} [NormedAddCommGroup E] {f : ℕ → α → E} {p : ℝ}
    (hp_pos : 0 < p) (hf : ∀ n, AEStronglyMeasurable (f n) μ) {f_lim : α → E}
    (h_lim : ∀ᵐ x : α ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))) :
    snorm' f_lim p μ ≤ atTop.liminf fun n => snorm' (f n) p μ :=
  by
  rw [snorm'_lim_eq_lintegral_liminf hp_pos.le h_lim]
  rw [← ENNReal.le_rpow_one_div_iff (by simp [hp_pos] : 0 < 1 / p), one_div_one_div]
  refine' (lintegral_liminf_le' fun m => (hf m).ennnorm.pow_const _).trans_eq _
  have h_pow_liminf :
    (at_top.liminf fun n => snorm' (f n) p μ) ^ p = at_top.liminf fun n => snorm' (f n) p μ ^ p :=
    by
    have h_rpow_mono := ENNReal.strictMono_rpow_of_pos hp_pos
    have h_rpow_surj := (ENNReal.rpow_left_bijective hp_pos.ne.symm).2
    refine' (h_rpow_mono.order_iso_of_surjective _ h_rpow_surj).liminf_apply _ _ _ _
    all_goals
      run_tac
        is_bounded_default
  rw [h_pow_liminf]
  simp_rw [snorm', ← ENNReal.rpow_mul, one_div, inv_mul_cancel hp_pos.ne.symm, ENNReal.rpow_one]
#align measure_theory.Lp.snorm'_lim_le_liminf_snorm' MeasureTheory.lp.snorm'_lim_le_liminf_snorm'

theorem snorm_exponent_top_lim_eq_essSup_liminf {ι} [Nonempty ι] [LinearOrder ι] {f : ι → α → G}
    {f_lim : α → G} (h_lim : ∀ᵐ x : α ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))) :
    snorm f_lim ∞ μ = essSup (fun x => atTop.liminf fun m => (‖f m x‖₊ : ℝ≥0∞)) μ :=
  by
  rw [snorm_exponent_top, snorm_ess_sup]
  refine' essSup_congr_ae (h_lim.mono fun x hx => _)
  rw [tendsto.liminf_eq]
  rw [ENNReal.tendsto_coe]
  exact (continuous_nnnorm.tendsto (f_lim x)).comp hx
#align measure_theory.Lp.snorm_exponent_top_lim_eq_ess_sup_liminf MeasureTheory.lp.snorm_exponent_top_lim_eq_essSup_liminf

theorem snorm_exponent_top_lim_le_liminf_snorm_exponent_top {ι} [Nonempty ι] [Countable ι]
    [LinearOrder ι] {f : ι → α → F} {f_lim : α → F}
    (h_lim : ∀ᵐ x : α ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))) :
    snorm f_lim ∞ μ ≤ atTop.liminf fun n => snorm (f n) ∞ μ :=
  by
  rw [snorm_exponent_top_lim_eq_ess_sup_liminf h_lim]
  simp_rw [snorm_exponent_top, snorm_ess_sup]
  exact ENNReal.essSup_liminf_le fun n => fun x => (‖f n x‖₊ : ℝ≥0∞)
#align measure_theory.Lp.snorm_exponent_top_lim_le_liminf_snorm_exponent_top MeasureTheory.lp.snorm_exponent_top_lim_le_liminf_snorm_exponent_top

theorem snorm_lim_le_liminf_snorm {E} [NormedAddCommGroup E] {f : ℕ → α → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (f_lim : α → E)
    (h_lim : ∀ᵐ x : α ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))) :
    snorm f_lim p μ ≤ atTop.liminf fun n => snorm (f n) p μ :=
  by
  by_cases hp0 : p = 0
  · simp [hp0]
  rw [← Ne.def] at hp0
  by_cases hp_top : p = ∞
  · simp_rw [hp_top]
    exact snorm_exponent_top_lim_le_liminf_snorm_exponent_top h_lim
  simp_rw [snorm_eq_snorm' hp0 hp_top]
  have hp_pos : 0 < p.to_real := ENNReal.toReal_pos hp0 hp_top
  exact snorm'_lim_le_liminf_snorm' hp_pos hf h_lim
#align measure_theory.Lp.snorm_lim_le_liminf_snorm MeasureTheory.lp.snorm_lim_le_liminf_snorm

/-! ### `Lp` is complete iff Cauchy sequences of `ℒp` have limits in `ℒp` -/


theorem tendsto_lp_iff_tendsto_ℒp' {ι} {fi : Filter ι} [Fact (1 ≤ p)] (f : ι → lp E p μ)
    (f_lim : lp E p μ) :
    fi.Tendsto f (𝓝 f_lim) ↔ fi.Tendsto (fun n => snorm (f n - f_lim) p μ) (𝓝 0) :=
  by
  rw [tendsto_iff_dist_tendsto_zero]
  simp_rw [dist_def]
  rw [← ENNReal.zero_toReal, ENNReal.tendsto_toReal_iff (fun n => _) ENNReal.zero_ne_top]
  rw [snorm_congr_ae (Lp.coe_fn_sub _ _).symm]
  exact Lp.snorm_ne_top _
#align measure_theory.Lp.tendsto_Lp_iff_tendsto_ℒp' MeasureTheory.lp.tendsto_lp_iff_tendsto_ℒp'

theorem tendsto_lp_iff_tendsto_ℒp {ι} {fi : Filter ι} [Fact (1 ≤ p)] (f : ι → lp E p μ)
    (f_lim : α → E) (f_lim_ℒp : Memℒp f_lim p μ) :
    fi.Tendsto f (𝓝 (f_lim_ℒp.toLp f_lim)) ↔ fi.Tendsto (fun n => snorm (f n - f_lim) p μ) (𝓝 0) :=
  by
  rw [tendsto_Lp_iff_tendsto_ℒp']
  suffices h_eq :
    (fun n => snorm (f n - mem_ℒp.to_Lp f_lim f_lim_ℒp) p μ) = fun n => snorm (f n - f_lim) p μ
  · rw [h_eq]
  exact funext fun n => snorm_congr_ae (eventually_eq.rfl.sub (mem_ℒp.coe_fn_to_Lp f_lim_ℒp))
#align measure_theory.Lp.tendsto_Lp_iff_tendsto_ℒp MeasureTheory.lp.tendsto_lp_iff_tendsto_ℒp

theorem tendsto_lp_iff_tendsto_ℒp'' {ι} {fi : Filter ι} [Fact (1 ≤ p)] (f : ι → α → E)
    (f_ℒp : ∀ n, Memℒp (f n) p μ) (f_lim : α → E) (f_lim_ℒp : Memℒp f_lim p μ) :
    fi.Tendsto (fun n => (f_ℒp n).toLp (f n)) (𝓝 (f_lim_ℒp.toLp f_lim)) ↔
      fi.Tendsto (fun n => snorm (f n - f_lim) p μ) (𝓝 0) :=
  by
  convert Lp.tendsto_Lp_iff_tendsto_ℒp' _ _
  ext1 n
  apply snorm_congr_ae
  filter_upwards [((f_ℒp n).sub f_lim_ℒp).coeFn_toLp,
    Lp.coe_fn_sub ((f_ℒp n).toLp (f n)) (f_lim_ℒp.to_Lp f_lim)]with _ hx₁ hx₂
  rw [← hx₂]
  exact hx₁.symm
#align measure_theory.Lp.tendsto_Lp_iff_tendsto_ℒp'' MeasureTheory.lp.tendsto_lp_iff_tendsto_ℒp''

theorem tendsto_lp_of_tendsto_ℒp {ι} {fi : Filter ι} [hp : Fact (1 ≤ p)] {f : ι → lp E p μ}
    (f_lim : α → E) (f_lim_ℒp : Memℒp f_lim p μ)
    (h_tendsto : fi.Tendsto (fun n => snorm (f n - f_lim) p μ) (𝓝 0)) :
    fi.Tendsto f (𝓝 (f_lim_ℒp.toLp f_lim)) :=
  (tendsto_lp_iff_tendsto_ℒp f f_lim f_lim_ℒp).mpr h_tendsto
#align measure_theory.Lp.tendsto_Lp_of_tendsto_ℒp MeasureTheory.lp.tendsto_lp_of_tendsto_ℒp

theorem cauchySeq_lp_iff_cauchySeq_ℒp {ι} [Nonempty ι] [SemilatticeSup ι] [hp : Fact (1 ≤ p)]
    (f : ι → lp E p μ) :
    CauchySeq f ↔ Tendsto (fun n : ι × ι => snorm (f n.fst - f n.snd) p μ) atTop (𝓝 0) :=
  by
  simp_rw [cauchySeq_iff_tendsto_dist_atTop_0, dist_def]
  rw [← ENNReal.zero_toReal, ENNReal.tendsto_toReal_iff (fun n => _) ENNReal.zero_ne_top]
  rw [snorm_congr_ae (Lp.coe_fn_sub _ _).symm]
  exact snorm_ne_top _
#align measure_theory.Lp.cauchy_seq_Lp_iff_cauchy_seq_ℒp MeasureTheory.lp.cauchySeq_lp_iff_cauchySeq_ℒp

theorem completeSpace_lp_of_cauchy_complete_ℒp [hp : Fact (1 ≤ p)]
    (H :
      ∀ (f : ℕ → α → E) (hf : ∀ n, Memℒp (f n) p μ) (B : ℕ → ℝ≥0∞) (hB : (∑' i, B i) < ∞)
        (h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m → snorm (f n - f m) p μ < B N),
        ∃ (f_lim : α → E)(hf_lim_meas : Memℒp f_lim p μ),
          atTop.Tendsto (fun n => snorm (f n - f_lim) p μ) (𝓝 0)) :
    CompleteSpace (lp E p μ) :=
  by
  let B := fun n : ℕ => ((1 : ℝ) / 2) ^ n
  have hB_pos : ∀ n, 0 < B n := fun n => pow_pos (div_pos zero_lt_one zero_lt_two) n
  refine' Metric.complete_of_convergent_controlled_sequences B hB_pos fun f hf => _
  rsuffices ⟨f_lim, hf_lim_meas, h_tendsto⟩ :
    ∃ (f_lim : α → E)(hf_lim_meas : mem_ℒp f_lim p μ),
      at_top.tendsto (fun n => snorm (f n - f_lim) p μ) (𝓝 0)
  · exact ⟨hf_lim_meas.to_Lp f_lim, tendsto_Lp_of_tendsto_ℒp f_lim hf_lim_meas h_tendsto⟩
  have hB : Summable B := summable_geometric_two
  cases' hB with M hB
  let B1 n := ENNReal.ofReal (B n)
  have hB1_has : HasSum B1 (ENNReal.ofReal M) :=
    by
    have h_tsum_B1 : (∑' i, B1 i) = ENNReal.ofReal M :=
      by
      change (∑' n : ℕ, ENNReal.ofReal (B n)) = ENNReal.ofReal M
      rw [← hB.tsum_eq]
      exact (ENNReal.ofReal_tsum_of_nonneg (fun n => le_of_lt (hB_pos n)) hB.summable).symm
    have h_sum := (@ENNReal.summable _ B1).HasSum
    rwa [h_tsum_B1] at h_sum
  have hB1 : (∑' i, B1 i) < ∞ := by rw [hB1_has.tsum_eq]; exact ENNReal.ofReal_lt_top
  let f1 : ℕ → α → E := fun n => f n
  refine' H f1 (fun n => Lp.mem_ℒp (f n)) B1 hB1 fun N n m hn hm => _
  specialize hf N n m hn hm
  rw [dist_def] at hf
  simp_rw [f1, B1]
  rwa [ENNReal.lt_ofReal_iff_toReal_lt]
  rw [snorm_congr_ae (Lp.coe_fn_sub _ _).symm]
  exact Lp.snorm_ne_top _
#align measure_theory.Lp.complete_space_Lp_of_cauchy_complete_ℒp MeasureTheory.lp.completeSpace_lp_of_cauchy_complete_ℒp

/-! ### Prove that controlled Cauchy sequences of `ℒp` have limits in `ℒp` -/


private theorem snorm'_sum_norm_sub_le_tsum_of_cauchy_snorm' {f : ℕ → α → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) {p : ℝ} (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞}
    (h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m → snorm' (f n - f m) p μ < B N) (n : ℕ) :
    snorm' (fun x => ∑ i in Finset.range (n + 1), ‖f (i + 1) x - f i x‖) p μ ≤ ∑' i, B i :=
  by
  let f_norm_diff i x := ‖f (i + 1) x - f i x‖
  have hgf_norm_diff :
    ∀ n,
      (fun x => ∑ i in Finset.range (n + 1), ‖f (i + 1) x - f i x‖) =
        ∑ i in Finset.range (n + 1), f_norm_diff i :=
    fun n => funext fun x => by simp [f_norm_diff]
  rw [hgf_norm_diff]
  refine' (snorm'_sum_le (fun i _ => ((hf (i + 1)).sub (hf i)).norm) hp1).trans _
  simp_rw [← Pi.sub_apply, snorm'_norm]
  refine' (Finset.sum_le_sum _).trans (sum_le_tsum _ (fun m _ => zero_le _) ENNReal.summable)
  exact fun m _ => (h_cau m (m + 1) m (Nat.le_succ m) (le_refl m)).le

private theorem lintegral_rpow_sum_coe_nnnorm_sub_le_rpow_tsum {f : ℕ → α → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) {p : ℝ} (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞} (n : ℕ)
    (hn : snorm' (fun x => ∑ i in Finset.range (n + 1), ‖f (i + 1) x - f i x‖) p μ ≤ ∑' i, B i) :
    (∫⁻ a, (∑ i in Finset.range (n + 1), ‖f (i + 1) a - f i a‖₊ : ℝ≥0∞) ^ p ∂μ) ≤ (∑' i, B i) ^ p :=
  by
  have hp_pos : 0 < p := zero_lt_one.trans_le hp1
  rw [← one_div_one_div p, @ENNReal.le_rpow_one_div_iff _ _ (1 / p) (by simp [hp_pos]),
    one_div_one_div p]
  simp_rw [snorm'] at hn
  have h_nnnorm_nonneg :
    (fun a => (‖∑ i in Finset.range (n + 1), ‖f (i + 1) a - f i a‖‖₊ : ℝ≥0∞) ^ p) = fun a =>
      (∑ i in Finset.range (n + 1), (‖f (i + 1) a - f i a‖₊ : ℝ≥0∞)) ^ p :=
    by
    ext1 a
    congr
    simp_rw [← ofReal_norm_eq_coe_nnnorm]
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · rw [Real.norm_of_nonneg _]
      exact Finset.sum_nonneg fun x hx => norm_nonneg _
    · exact fun x hx => norm_nonneg _
  change
    (∫⁻ a, (fun x => ↑‖∑ i in Finset.range (n + 1), ‖f (i + 1) x - f i x‖‖₊ ^ p) a ∂μ) ^ (1 / p) ≤
      ∑' i, B i at
    hn
  rwa [h_nnnorm_nonneg] at hn

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic filter.is_bounded_default -/
private theorem lintegral_rpow_tsum_coe_nnnorm_sub_le_tsum {f : ℕ → α → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) {p : ℝ} (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞}
    (h :
      ∀ n,
        (∫⁻ a, (∑ i in Finset.range (n + 1), ‖f (i + 1) a - f i a‖₊ : ℝ≥0∞) ^ p ∂μ) ≤
          (∑' i, B i) ^ p) :
    (∫⁻ a, (∑' i, ‖f (i + 1) a - f i a‖₊ : ℝ≥0∞) ^ p ∂μ) ^ (1 / p) ≤ ∑' i, B i :=
  by
  have hp_pos : 0 < p := zero_lt_one.trans_le hp1
  suffices h_pow : (∫⁻ a, (∑' i, ‖f (i + 1) a - f i a‖₊ : ℝ≥0∞) ^ p ∂μ) ≤ (∑' i, B i) ^ p
  · rwa [← ENNReal.le_rpow_one_div_iff (by simp [hp_pos] : 0 < 1 / p), one_div_one_div]
  have h_tsum_1 :
    ∀ g : ℕ → ℝ≥0∞, (∑' i, g i) = at_top.liminf fun n => ∑ i in Finset.range (n + 1), g i := by
    intro g; rw [ENNReal.tsum_eq_liminf_sum_nat, ← liminf_nat_add _ 1]
  simp_rw [h_tsum_1 _]
  rw [← h_tsum_1]
  have h_liminf_pow :
    (∫⁻ a, (at_top.liminf fun n => ∑ i in Finset.range (n + 1), ‖f (i + 1) a - f i a‖₊) ^ p ∂μ) =
      ∫⁻ a, at_top.liminf fun n => (∑ i in Finset.range (n + 1), ‖f (i + 1) a - f i a‖₊) ^ p ∂μ :=
    by
    refine' lintegral_congr fun x => _
    have h_rpow_mono := ENNReal.strictMono_rpow_of_pos (zero_lt_one.trans_le hp1)
    have h_rpow_surj := (ENNReal.rpow_left_bijective hp_pos.ne.symm).2
    refine' (h_rpow_mono.order_iso_of_surjective _ h_rpow_surj).liminf_apply _ _ _ _
    all_goals
      run_tac
        is_bounded_default
  rw [h_liminf_pow]
  refine' (lintegral_liminf_le' _).trans _
  ·
    exact fun n =>
      (Finset.aemeasurable_sum (Finset.range (n + 1)) fun i _ =>
            ((hf (i + 1)).sub (hf i)).ennnorm).pow_const
        _
  · exact liminf_le_of_frequently_le' (frequently_of_forall h)

private theorem tsum_nnnorm_sub_ae_lt_top {f : ℕ → α → E} (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    {p : ℝ} (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞} (hB : (∑' i, B i) ≠ ∞)
    (h : (∫⁻ a, (∑' i, ‖f (i + 1) a - f i a‖₊ : ℝ≥0∞) ^ p ∂μ) ^ (1 / p) ≤ ∑' i, B i) :
    ∀ᵐ x ∂μ, (∑' i, ‖f (i + 1) x - f i x‖₊ : ℝ≥0∞) < ∞ :=
  by
  have hp_pos : 0 < p := zero_lt_one.trans_le hp1
  have h_integral : (∫⁻ a, (∑' i, ‖f (i + 1) a - f i a‖₊ : ℝ≥0∞) ^ p ∂μ) < ∞ :=
    by
    have h_tsum_lt_top : (∑' i, B i) ^ p < ∞ := ENNReal.rpow_lt_top_of_nonneg hp_pos.le hB
    refine' lt_of_le_of_lt _ h_tsum_lt_top
    rwa [← ENNReal.le_rpow_one_div_iff (by simp [hp_pos] : 0 < 1 / p), one_div_one_div] at h
  have rpow_ae_lt_top : ∀ᵐ x ∂μ, (∑' i, ‖f (i + 1) x - f i x‖₊ : ℝ≥0∞) ^ p < ∞ :=
    by
    refine' ae_lt_top' (AEMeasurable.pow_const _ _) h_integral.ne
    exact AEMeasurable.ennreal_tsum fun n => ((hf (n + 1)).sub (hf n)).ennnorm
  refine' rpow_ae_lt_top.mono fun x hx => _
  rwa [← ENNReal.lt_rpow_one_div_iff hp_pos,
    ENNReal.top_rpow_of_pos (by simp [hp_pos] : 0 < 1 / p)] at hx

theorem ae_tendsto_of_cauchy_snorm' [CompleteSpace E] {f : ℕ → α → E} {p : ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞} (hB : (∑' i, B i) ≠ ∞)
    (h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m → snorm' (f n - f m) p μ < B N) :
    ∀ᵐ x ∂μ, ∃ l : E, atTop.Tendsto (fun n => f n x) (𝓝 l) :=
  by
  have h_summable : ∀ᵐ x ∂μ, Summable fun i : ℕ => f (i + 1) x - f i x :=
    by
    have h1 :
      ∀ n, snorm' (fun x => ∑ i in Finset.range (n + 1), ‖f (i + 1) x - f i x‖) p μ ≤ ∑' i, B i :=
      snorm'_sum_norm_sub_le_tsum_of_cauchy_snorm' hf hp1 h_cau
    have h2 :
      ∀ n,
        (∫⁻ a, (∑ i in Finset.range (n + 1), ‖f (i + 1) a - f i a‖₊ : ℝ≥0∞) ^ p ∂μ) ≤
          (∑' i, B i) ^ p :=
      fun n => lintegral_rpow_sum_coe_nnnorm_sub_le_rpow_tsum hf hp1 n (h1 n)
    have h3 : (∫⁻ a, (∑' i, ‖f (i + 1) a - f i a‖₊ : ℝ≥0∞) ^ p ∂μ) ^ (1 / p) ≤ ∑' i, B i :=
      lintegral_rpow_tsum_coe_nnnorm_sub_le_tsum hf hp1 h2
    have h4 : ∀ᵐ x ∂μ, (∑' i, ‖f (i + 1) x - f i x‖₊ : ℝ≥0∞) < ∞ :=
      tsum_nnnorm_sub_ae_lt_top hf hp1 hB h3
    exact
      h4.mono fun x hx =>
        summable_of_summable_nnnorm
          (ennreal.tsum_coe_ne_top_iff_summable.mp (lt_top_iff_ne_top.mp hx))
  have h :
    ∀ᵐ x ∂μ, ∃ l : E, at_top.tendsto (fun n => ∑ i in Finset.range n, f (i + 1) x - f i x) (𝓝 l) :=
    by
    refine' h_summable.mono fun x hx => _
    let hx_sum := hx.has_sum.tendsto_sum_nat
    exact ⟨∑' i, f (i + 1) x - f i x, hx_sum⟩
  refine' h.mono fun x hx => _
  cases' hx with l hx
  have h_rw_sum : (fun n => ∑ i in Finset.range n, f (i + 1) x - f i x) = fun n => f n x - f 0 x :=
    by
    ext1 n
    change
      (∑ i : ℕ in Finset.range n, (fun m => f m x) (i + 1) - (fun m => f m x) i) = f n x - f 0 x
    rw [Finset.sum_range_sub]
  rw [h_rw_sum] at hx
  have hf_rw : (fun n => f n x) = fun n => f n x - f 0 x + f 0 x := by ext1 n; abel
  rw [hf_rw]
  exact ⟨l + f 0 x, tendsto.add_const _ hx⟩
#align measure_theory.Lp.ae_tendsto_of_cauchy_snorm' MeasureTheory.lp.ae_tendsto_of_cauchy_snorm'

theorem ae_tendsto_of_cauchy_snorm [CompleteSpace E] {f : ℕ → α → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hp : 1 ≤ p) {B : ℕ → ℝ≥0∞} (hB : (∑' i, B i) ≠ ∞)
    (h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m → snorm (f n - f m) p μ < B N) :
    ∀ᵐ x ∂μ, ∃ l : E, atTop.Tendsto (fun n => f n x) (𝓝 l) :=
  by
  by_cases hp_top : p = ∞
  · simp_rw [hp_top] at *
    have h_cau_ae : ∀ᵐ x ∂μ, ∀ N n m, N ≤ n → N ≤ m → (‖(f n - f m) x‖₊ : ℝ≥0∞) < B N :=
      by
      simp_rw [ae_all_iff]
      exact fun N n m hnN hmN => ae_lt_of_essSup_lt (h_cau N n m hnN hmN)
    simp_rw [snorm_exponent_top, snorm_ess_sup] at h_cau
    refine' h_cau_ae.mono fun x hx => cauchySeq_tendsto_of_complete _
    refine' cauchySeq_of_le_tendsto_0 (fun n => (B n).toReal) _ _
    · intro n m N hnN hmN
      specialize hx N n m hnN hmN
      rw [dist_eq_norm, ← ENNReal.toReal_ofReal (norm_nonneg _),
        ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (ENNReal.ne_top_of_tsum_ne_top hB N)]
      rw [← ofReal_norm_eq_coe_nnnorm] at hx
      exact hx.le
    · rw [← ENNReal.zero_toReal]
      exact
        tendsto.comp (ENNReal.tendsto_toReal ENNReal.zero_ne_top)
          (ENNReal.tendsto_atTop_zero_of_tsum_ne_top hB)
  have hp1 : 1 ≤ p.to_real :=
    by
    rw [← ENNReal.ofReal_le_iff_le_toReal hp_top, ENNReal.ofReal_one]
    exact hp
  have h_cau' : ∀ N n m : ℕ, N ≤ n → N ≤ m → snorm' (f n - f m) p.to_real μ < B N :=
    by
    intro N n m hn hm
    specialize h_cau N n m hn hm
    rwa [snorm_eq_snorm' (zero_lt_one.trans_le hp).Ne.symm hp_top] at h_cau
  exact ae_tendsto_of_cauchy_snorm' hf hp1 hB h_cau'
#align measure_theory.Lp.ae_tendsto_of_cauchy_snorm MeasureTheory.lp.ae_tendsto_of_cauchy_snorm

theorem cauchy_tendsto_of_tendsto {f : ℕ → α → E} (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (f_lim : α → E) {B : ℕ → ℝ≥0∞} (hB : (∑' i, B i) ≠ ∞)
    (h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m → snorm (f n - f m) p μ < B N)
    (h_lim : ∀ᵐ x : α ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))) :
    atTop.Tendsto (fun n => snorm (f n - f_lim) p μ) (𝓝 0) :=
  by
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  have h_B : ∃ N : ℕ, B N ≤ ε :=
    by
    suffices h_tendsto_zero : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → B n ≤ ε
    exact ⟨h_tendsto_zero.some, h_tendsto_zero.some_spec _ le_rfl⟩
    exact (ennreal.tendsto_at_top_zero.mp (ENNReal.tendsto_atTop_zero_of_tsum_ne_top hB)) ε hε
  cases' h_B with N h_B
  refine' ⟨N, fun n hn => _⟩
  have h_sub : snorm (f n - f_lim) p μ ≤ at_top.liminf fun m => snorm (f n - f m) p μ :=
    by
    refine' snorm_lim_le_liminf_snorm (fun m => (hf n).sub (hf m)) (f n - f_lim) _
    refine' h_lim.mono fun x hx => _
    simp_rw [sub_eq_add_neg]
    exact tendsto.add tendsto_const_nhds (tendsto.neg hx)
  refine' h_sub.trans _
  refine' liminf_le_of_frequently_le' (frequently_at_top.mpr _)
  refine' fun N1 => ⟨max N N1, le_max_right _ _, _⟩
  exact (h_cau N n (max N N1) hn (le_max_left _ _)).le.trans h_B
#align measure_theory.Lp.cauchy_tendsto_of_tendsto MeasureTheory.lp.cauchy_tendsto_of_tendsto

theorem memℒp_of_cauchy_tendsto (hp : 1 ≤ p) {f : ℕ → α → E} (hf : ∀ n, Memℒp (f n) p μ)
    (f_lim : α → E) (h_lim_meas : AEStronglyMeasurable f_lim μ)
    (h_tendsto : atTop.Tendsto (fun n => snorm (f n - f_lim) p μ) (𝓝 0)) : Memℒp f_lim p μ :=
  by
  refine' ⟨h_lim_meas, _⟩
  rw [ENNReal.tendsto_atTop_zero] at h_tendsto
  cases' h_tendsto 1 zero_lt_one with N h_tendsto_1
  specialize h_tendsto_1 N (le_refl N)
  have h_add : f_lim = f_lim - f N + f N := by abel
  rw [h_add]
  refine' lt_of_le_of_lt (snorm_add_le (h_lim_meas.sub (hf N).1) (hf N).1 hp) _
  rw [ENNReal.add_lt_top]
  constructor
  · refine' lt_of_le_of_lt _ ENNReal.one_lt_top
    have h_neg : f_lim - f N = -(f N - f_lim) := by simp
    rwa [h_neg, snorm_neg]
  · exact (hf N).2
#align measure_theory.Lp.mem_ℒp_of_cauchy_tendsto MeasureTheory.lp.memℒp_of_cauchy_tendsto

theorem cauchy_complete_ℒp [CompleteSpace E] (hp : 1 ≤ p) {f : ℕ → α → E}
    (hf : ∀ n, Memℒp (f n) p μ) {B : ℕ → ℝ≥0∞} (hB : (∑' i, B i) ≠ ∞)
    (h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m → snorm (f n - f m) p μ < B N) :
    ∃ (f_lim : α → E)(hf_lim_meas : Memℒp f_lim p μ),
      atTop.Tendsto (fun n => snorm (f n - f_lim) p μ) (𝓝 0) :=
  by
  obtain ⟨f_lim, h_f_lim_meas, h_lim⟩ :
    ∃ (f_lim : α → E)(hf_lim_meas : strongly_measurable f_lim),
      ∀ᵐ x ∂μ, tendsto (fun n => f n x) at_top (nhds (f_lim x))
  exact
    exists_stronglyMeasurable_limit_of_tendsto_ae (fun n => (hf n).1)
      (ae_tendsto_of_cauchy_snorm (fun n => (hf n).1) hp hB h_cau)
  have h_tendsto' : at_top.tendsto (fun n => snorm (f n - f_lim) p μ) (𝓝 0) :=
    cauchy_tendsto_of_tendsto (fun m => (hf m).1) f_lim hB h_cau h_lim
  have h_ℒp_lim : mem_ℒp f_lim p μ :=
    mem_ℒp_of_cauchy_tendsto hp hf f_lim h_f_lim_meas.ae_strongly_measurable h_tendsto'
  exact ⟨f_lim, h_ℒp_lim, h_tendsto'⟩
#align measure_theory.Lp.cauchy_complete_ℒp MeasureTheory.lp.cauchy_complete_ℒp

/-! ### `Lp` is complete for `1 ≤ p` -/


instance [CompleteSpace E] [hp : Fact (1 ≤ p)] : CompleteSpace (lp E p μ) :=
  completeSpace_lp_of_cauchy_complete_ℒp fun f hf B hB h_cau =>
    cauchy_complete_ℒp hp.elim hf hB.Ne h_cau

end Lp

end MeasureTheory

end CompleteSpace

/-! ### Continuous functions in `Lp` -/


open scoped BoundedContinuousFunction

open BoundedContinuousFunction

section

variable [TopologicalSpace α] [BorelSpace α] [SecondCountableTopologyEither α E]

variable (E p μ)

/-- An additive subgroup of `Lp E p μ`, consisting of the equivalence classes which contain a
bounded continuous representative. -/
def MeasureTheory.lp.boundedContinuousFunction : AddSubgroup (lp E p μ) :=
  AddSubgroup.addSubgroupOf
    ((ContinuousMap.toAEEqFunAddHom μ).comp (toContinuousMapAddHom α E)).range (lp E p μ)
#align measure_theory.Lp.bounded_continuous_function MeasureTheory.lp.boundedContinuousFunction

variable {E p μ}

/-- By definition, the elements of `Lp.bounded_continuous_function E p μ` are the elements of
`Lp E p μ` which contain a bounded continuous representative. -/
theorem MeasureTheory.lp.mem_boundedContinuousFunction_iff {f : lp E p μ} :
    f ∈ MeasureTheory.lp.boundedContinuousFunction E p μ ↔
      ∃ f₀ : α →ᵇ E, f₀.toContinuousMap.toAEEqFun μ = (f : α →ₘ[μ] E) :=
  AddSubgroup.mem_addSubgroupOf
#align measure_theory.Lp.mem_bounded_continuous_function_iff MeasureTheory.lp.mem_boundedContinuousFunction_iff

namespace BoundedContinuousFunction

variable [FiniteMeasure μ]

/-- A bounded continuous function on a finite-measure space is in `Lp`. -/
theorem mem_lp (f : α →ᵇ E) : f.toContinuousMap.toAEEqFun μ ∈ lp E p μ :=
  by
  refine' Lp.mem_Lp_of_ae_bound ‖f‖ _
  filter_upwards [f.to_continuous_map.coe_fn_to_ae_eq_fun μ]with x _
  convert f.norm_coe_le_norm x
#align bounded_continuous_function.mem_Lp BoundedContinuousFunction.mem_lp

/-- The `Lp`-norm of a bounded continuous function is at most a constant (depending on the measure
of the whole space) times its sup-norm. -/
theorem lp_nnnorm_le (f : α →ᵇ E) :
    ‖(⟨f.toContinuousMap.toAEEqFun μ, mem_lp f⟩ : lp E p μ)‖₊ ≤
      measureUnivNNReal μ ^ p.toReal⁻¹ * ‖f‖₊ :=
  by
  apply Lp.nnnorm_le_of_ae_bound
  refine' (f.to_continuous_map.coe_fn_to_ae_eq_fun μ).mono _
  intro x hx
  rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
  convert f.norm_coe_le_norm x
#align bounded_continuous_function.Lp_nnnorm_le BoundedContinuousFunction.lp_nnnorm_le

/-- The `Lp`-norm of a bounded continuous function is at most a constant (depending on the measure
of the whole space) times its sup-norm. -/
theorem lp_norm_le (f : α →ᵇ E) :
    ‖(⟨f.toContinuousMap.toAEEqFun μ, mem_lp f⟩ : lp E p μ)‖ ≤
      measureUnivNNReal μ ^ p.toReal⁻¹ * ‖f‖ :=
  lp_nnnorm_le f
#align bounded_continuous_function.Lp_norm_le BoundedContinuousFunction.lp_norm_le

variable (p μ)

/-- The normed group homomorphism of considering a bounded continuous function on a finite-measure
space as an element of `Lp`. -/
def toLpHom [Fact (1 ≤ p)] : NormedAddGroupHom (α →ᵇ E) (lp E p μ) :=
  {
    AddMonoidHom.codRestrict ((ContinuousMap.toAEEqFunAddHom μ).comp (toContinuousMapAddHom α E))
      (lp E p μ) mem_lp with
    bound' := ⟨_, lp_norm_le⟩ }
#align bounded_continuous_function.to_Lp_hom BoundedContinuousFunction.toLpHom

theorem range_toLpHom [Fact (1 ≤ p)] :
    ((toLpHom p μ).range : AddSubgroup (lp E p μ)) =
      MeasureTheory.lp.boundedContinuousFunction E p μ :=
  by
  symm
  convert AddMonoidHom.addSubgroupOf_range_eq_of_le
      ((ContinuousMap.toAEEqFunAddHom μ).comp (to_continuous_map_add_hom α E))
      (by rintro - ⟨f, rfl⟩; exact mem_Lp f : _ ≤ Lp E p μ)
#align bounded_continuous_function.range_to_Lp_hom BoundedContinuousFunction.range_toLpHom

variable (𝕜 : Type _) [Fact (1 ≤ p)]

/-- The bounded linear map of considering a bounded continuous function on a finite-measure space
as an element of `Lp`. -/
def toLp [NormedField 𝕜] [NormedSpace 𝕜 E] : (α →ᵇ E) →L[𝕜] lp E p μ :=
  LinearMap.mkContinuous
    (LinearMap.codRestrict (lp.lpSubmodule E p μ 𝕜)
      ((ContinuousMap.toAEEqFunLinearMap μ).comp (toContinuousMapLinearMap α E 𝕜)) mem_lp)
    _ lp_norm_le
#align bounded_continuous_function.to_Lp BoundedContinuousFunction.toLp

theorem coeFn_toLp [NormedField 𝕜] [NormedSpace 𝕜 E] (f : α →ᵇ E) : toLp p μ 𝕜 f =ᵐ[μ] f :=
  AEEqFun.coeFn_mk f _
#align bounded_continuous_function.coe_fn_to_Lp BoundedContinuousFunction.coeFn_toLp

variable {𝕜}

theorem range_toLp [NormedField 𝕜] [NormedSpace 𝕜 E] :
    (LinearMap.range (toLp p μ 𝕜 : (α →ᵇ E) →L[𝕜] lp E p μ)).toAddSubgroup =
      MeasureTheory.lp.boundedContinuousFunction E p μ :=
  range_toLpHom p μ
#align bounded_continuous_function.range_to_Lp BoundedContinuousFunction.range_toLp

variable {p}

theorem toLp_norm_le [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] :
    ‖(toLp p μ 𝕜 : (α →ᵇ E) →L[𝕜] lp E p μ)‖ ≤ measureUnivNNReal μ ^ p.toReal⁻¹ :=
  LinearMap.mkContinuous_norm_le _ (measureUnivNNReal μ ^ p.toReal⁻¹).coe_nonneg _
#align bounded_continuous_function.to_Lp_norm_le BoundedContinuousFunction.toLp_norm_le

theorem toLp_inj {f g : α →ᵇ E} [μ.OpenPosMeasure] [NormedField 𝕜] [NormedSpace 𝕜 E] :
    toLp p μ 𝕜 f = toLp p μ 𝕜 g ↔ f = g :=
  by
  refine' ⟨fun h => _, by tauto⟩
  rw [← FunLike.coe_fn_eq, ← (map_continuous f).ae_eq_iff_eq μ (map_continuous g)]
  refine' (coe_fn_to_Lp p μ 𝕜 f).symm.trans (eventually_eq.trans _ <| coe_fn_to_Lp p μ 𝕜 g)
  rw [h]
#align bounded_continuous_function.to_Lp_inj BoundedContinuousFunction.toLp_inj

theorem toLp_injective [μ.OpenPosMeasure] [NormedField 𝕜] [NormedSpace 𝕜 E] :
    Function.Injective ⇑(toLp p μ 𝕜 : (α →ᵇ E) →L[𝕜] lp E p μ) := fun f g hfg => (toLp_inj μ).mp hfg
#align bounded_continuous_function.to_Lp_injective BoundedContinuousFunction.toLp_injective

end BoundedContinuousFunction

namespace ContinuousMap

variable [CompactSpace α] [FiniteMeasure μ]

variable (𝕜 : Type _) (p μ) [Fact (1 ≤ p)]

/-- The bounded linear map of considering a continuous function on a compact finite-measure
space `α` as an element of `Lp`.  By definition, the norm on `C(α, E)` is the sup-norm, transferred
from the space `α →ᵇ E` of bounded continuous functions, so this construction is just a matter of
transferring the structure from `bounded_continuous_function.to_Lp` along the isometry. -/
def toLp [NormedField 𝕜] [NormedSpace 𝕜 E] : C(α, E) →L[𝕜] lp E p μ :=
  (BoundedContinuousFunction.toLp p μ 𝕜).comp
    (linearIsometryBoundedOfCompact α E 𝕜).toLinearIsometry.toContinuousLinearMap
#align continuous_map.to_Lp ContinuousMap.toLp

variable {𝕜}

theorem range_toLp [NormedField 𝕜] [NormedSpace 𝕜 E] :
    (LinearMap.range (toLp p μ 𝕜 : C(α, E) →L[𝕜] lp E p μ)).toAddSubgroup =
      MeasureTheory.lp.boundedContinuousFunction E p μ :=
  by
  refine' SetLike.ext' _
  have := (linear_isometry_bounded_of_compact α E 𝕜).Surjective
  convert Function.Surjective.range_comp this (BoundedContinuousFunction.toLp p μ 𝕜)
  rw [← BoundedContinuousFunction.range_toLp p μ]
  rfl
#align continuous_map.range_to_Lp ContinuousMap.range_toLp

variable {p}

theorem coeFn_toLp [NormedField 𝕜] [NormedSpace 𝕜 E] (f : C(α, E)) : toLp p μ 𝕜 f =ᵐ[μ] f :=
  AEEqFun.coeFn_mk f _
#align continuous_map.coe_fn_to_Lp ContinuousMap.coeFn_toLp

theorem toLp_def [NormedField 𝕜] [NormedSpace 𝕜 E] (f : C(α, E)) :
    toLp p μ 𝕜 f = BoundedContinuousFunction.toLp p μ 𝕜 (linearIsometryBoundedOfCompact α E 𝕜 f) :=
  rfl
#align continuous_map.to_Lp_def ContinuousMap.toLp_def

@[simp]
theorem toLp_comp_toContinuousMap [NormedField 𝕜] [NormedSpace 𝕜 E] (f : α →ᵇ E) :
    toLp p μ 𝕜 f.toContinuousMap = BoundedContinuousFunction.toLp p μ 𝕜 f :=
  rfl
#align continuous_map.to_Lp_comp_to_continuous_map ContinuousMap.toLp_comp_toContinuousMap

@[simp]
theorem coe_toLp [NormedField 𝕜] [NormedSpace 𝕜 E] (f : C(α, E)) :
    (toLp p μ 𝕜 f : α →ₘ[μ] E) = f.toAEEqFun μ :=
  rfl
#align continuous_map.coe_to_Lp ContinuousMap.coe_toLp

theorem toLp_injective [μ.OpenPosMeasure] [NormedField 𝕜] [NormedSpace 𝕜 E] :
    Function.Injective ⇑(toLp p μ 𝕜 : C(α, E) →L[𝕜] lp E p μ) :=
  (BoundedContinuousFunction.toLp_injective _).comp (linearIsometryBoundedOfCompact α E 𝕜).Injective
#align continuous_map.to_Lp_injective ContinuousMap.toLp_injective

theorem toLp_inj {f g : C(α, E)} [μ.OpenPosMeasure] [NormedField 𝕜] [NormedSpace 𝕜 E] :
    toLp p μ 𝕜 f = toLp p μ 𝕜 g ↔ f = g :=
  (toLp_injective μ).eq_iff
#align continuous_map.to_Lp_inj ContinuousMap.toLp_inj

variable {μ}

/-- If a sum of continuous functions `g n` is convergent, and the same sum converges in `Lᵖ` to `h`,
then in fact `g n` converges uniformly to `h`.  -/
theorem hasSum_of_hasSum_lp {β : Type _} [μ.OpenPosMeasure] [NormedField 𝕜] [NormedSpace 𝕜 E]
    {g : β → C(α, E)} {f : C(α, E)} (hg : Summable g)
    (hg2 : HasSum (toLp p μ 𝕜 ∘ g) (toLp p μ 𝕜 f)) : HasSum g f :=
  by
  convert Summable.hasSum hg
  exact to_Lp_injective μ (hg2.unique ((to_Lp p μ 𝕜).HasSum <| Summable.hasSum hg))
#align continuous_map.has_sum_of_has_sum_Lp ContinuousMap.hasSum_of_hasSum_lp

variable (μ) [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]

theorem toLp_norm_eq_toLp_norm_coe :
    ‖(toLp p μ 𝕜 : C(α, E) →L[𝕜] lp E p μ)‖ =
      ‖(BoundedContinuousFunction.toLp p μ 𝕜 : (α →ᵇ E) →L[𝕜] lp E p μ)‖ :=
  ContinuousLinearMap.op_norm_comp_linearIsometryEquiv _ _
#align continuous_map.to_Lp_norm_eq_to_Lp_norm_coe ContinuousMap.toLp_norm_eq_toLp_norm_coe

/-- Bound for the operator norm of `continuous_map.to_Lp`. -/
theorem toLp_norm_le : ‖(toLp p μ 𝕜 : C(α, E) →L[𝕜] lp E p μ)‖ ≤ measureUnivNNReal μ ^ p.toReal⁻¹ :=
  by rw [to_Lp_norm_eq_to_Lp_norm_coe]; exact BoundedContinuousFunction.toLp_norm_le μ
#align continuous_map.to_Lp_norm_le ContinuousMap.toLp_norm_le

end ContinuousMap

end

namespace MeasureTheory

namespace Lp

theorem pow_mul_meas_ge_le_norm (f : lp E p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) (ε : ℝ≥0∞) :
    (ε * μ { x | ε ≤ ‖f x‖₊ ^ p.toReal }) ^ (1 / p.toReal) ≤ ENNReal.ofReal ‖f‖ :=
  (ENNReal.ofReal_toReal (snorm_ne_top f)).symm ▸
    pow_mul_meas_ge_le_snorm μ hp_ne_zero hp_ne_top (lp.aEStronglyMeasurable f) ε
#align measure_theory.Lp.pow_mul_meas_ge_le_norm MeasureTheory.lp.pow_mul_meas_ge_le_norm

theorem mul_meas_ge_le_pow_norm (f : lp E p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) (ε : ℝ≥0∞) :
    ε * μ { x | ε ≤ ‖f x‖₊ ^ p.toReal } ≤ ENNReal.ofReal ‖f‖ ^ p.toReal :=
  (ENNReal.ofReal_toReal (snorm_ne_top f)).symm ▸
    mul_meas_ge_le_pow_snorm μ hp_ne_zero hp_ne_top (lp.aEStronglyMeasurable f) ε
#align measure_theory.Lp.mul_meas_ge_le_pow_norm MeasureTheory.lp.mul_meas_ge_le_pow_norm

/-- A version of Markov's inequality with elements of Lp. -/
theorem mul_meas_ge_le_pow_norm' (f : lp E p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (ε : ℝ≥0∞) : ε ^ p.toReal * μ { x | ε ≤ ‖f x‖₊ } ≤ ENNReal.ofReal ‖f‖ ^ p.toReal :=
  (ENNReal.ofReal_toReal (snorm_ne_top f)).symm ▸
    mul_meas_ge_le_pow_snorm' μ hp_ne_zero hp_ne_top (lp.aEStronglyMeasurable f) ε
#align measure_theory.Lp.mul_meas_ge_le_pow_norm' MeasureTheory.lp.mul_meas_ge_le_pow_norm'

theorem meas_ge_le_mul_pow_norm (f : lp E p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) {ε : ℝ≥0∞}
    (hε : ε ≠ 0) : μ { x | ε ≤ ‖f x‖₊ } ≤ ε⁻¹ ^ p.toReal * ENNReal.ofReal ‖f‖ ^ p.toReal :=
  (ENNReal.ofReal_toReal (snorm_ne_top f)).symm ▸
    meas_ge_le_mul_pow_snorm μ hp_ne_zero hp_ne_top (lp.aEStronglyMeasurable f) hε
#align measure_theory.Lp.meas_ge_le_mul_pow_norm MeasureTheory.lp.meas_ge_le_mul_pow_norm

end Lp

end MeasureTheory

