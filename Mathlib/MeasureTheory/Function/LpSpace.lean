/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
import Mathlib.Analysis.Normed.Group.Hom
import Mathlib.MeasureTheory.Function.LpSeminorm
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.ContinuousFunction.Compact

#align_import measure_theory.function.lp_space from "leanprover-community/mathlib"@"c4015acc0a223449d44061e27ddac1835a3852b9"

/-!
# Lp space

This file provides the space `Lp E p μ` as the subtype of elements of `α →ₘ[μ] E` (see ae_eq_fun)
such that `snorm f p μ` is finite. For `1 ≤ p`, `snorm` defines a norm and `Lp` is a complete metric
space.

## Main definitions

* `Lp E p μ` : elements of `α →ₘ[μ] E` (see ae_eq_fun) such that `snorm f p μ` is finite. Defined
  as an `AddSubgroup` of `α →ₘ[μ] E`.

Lipschitz functions vanishing at zero act by composition on `Lp`. We define this action, and prove
that it is continuous. In particular,
* `ContinuousLinearMap.compLp` defines the action on `Lp` of a continuous linear map.
* `Lp.posPart` is the positive part of an `Lp` function.
* `Lp.negPart` is the negative part of an `Lp` function.

When `α` is a topological space equipped with a finite Borel measure, there is a bounded linear map
from the normed space of bounded continuous functions (`α →ᵇ E`) to `Lp E p μ`.  We construct this
as `BoundedContinuousFunction.toLp`.

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

set_option linter.uppercaseLean3 false

open TopologicalSpace MeasureTheory Filter

open NNReal ENNReal BigOperators Topology MeasureTheory

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

variable {α E F G : Type*} {m m0 : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ} {μ ν : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]

namespace MeasureTheory

/-!
### Lp space

The space of equivalence classes of measurable functions for which `snorm f p μ < ∞`.
-/


@[simp]
theorem snorm_aeeqFun {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    {p : ℝ≥0∞} {f : α → E} (hf : AEStronglyMeasurable f μ) :
    snorm (AEEqFun.mk f hf) p μ = snorm f p μ :=
  snorm_congr_ae (AEEqFun.coeFn_mk _ _)
#align measure_theory.snorm_ae_eq_fun MeasureTheory.snorm_aeeqFun

theorem Memℒp.snorm_mk_lt_top {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {p : ℝ≥0∞} {f : α → E} (hfp : Memℒp f p μ) :
    snorm (AEEqFun.mk f hfp.1) p μ < ∞ := by simp [hfp.2]
                                             -- 🎉 no goals
#align measure_theory.mem_ℒp.snorm_mk_lt_top MeasureTheory.Memℒp.snorm_mk_lt_top

/-- Lp space -/
def Lp {α} (E : Type*) {m : MeasurableSpace α} [NormedAddCommGroup E] (p : ℝ≥0∞)
    (μ : Measure α := by volume_tac) : AddSubgroup (α →ₘ[μ] E) where
  carrier := { f | snorm f p μ < ∞ }
  zero_mem' := by simp [snorm_congr_ae AEEqFun.coeFn_zero, snorm_zero]
                  -- 🎉 no goals
  add_mem' {f g} hf hg := by
    simp [snorm_congr_ae (AEEqFun.coeFn_add f g),
      snorm_add_lt_top ⟨f.aestronglyMeasurable, hf⟩ ⟨g.aestronglyMeasurable, hg⟩]
  neg_mem' {f} hf := by rwa [Set.mem_setOf_eq, snorm_congr_ae (AEEqFun.coeFn_neg f), snorm_neg]
                        -- 🎉 no goals
#align measure_theory.Lp MeasureTheory.Lp

-- Porting note: calling the first argument `α` breaks the `(α := ·)` notation
scoped notation:25 α' " →₁[" μ "] " E => MeasureTheory.Lp (α := α') E 1 μ
scoped notation:25 α' " →₂[" μ "] " E => MeasureTheory.Lp (α := α') E 2 μ

namespace Memℒp

/-- make an element of Lp from a function verifying `Memℒp` -/
def toLp (f : α → E) (h_mem_ℒp : Memℒp f p μ) : Lp E p μ :=
  ⟨AEEqFun.mk f h_mem_ℒp.1, h_mem_ℒp.snorm_mk_lt_top⟩
#align measure_theory.mem_ℒp.to_Lp MeasureTheory.Memℒp.toLp

theorem coeFn_toLp {f : α → E} (hf : Memℒp f p μ) : hf.toLp f =ᵐ[μ] f :=
  AEEqFun.coeFn_mk _ _
#align measure_theory.mem_ℒp.coe_fn_to_Lp MeasureTheory.Memℒp.coeFn_toLp

theorem toLp_congr {f g : α → E} (hf : Memℒp f p μ) (hg : Memℒp g p μ) (hfg : f =ᵐ[μ] g) :
    hf.toLp f = hg.toLp g := by simp [toLp, hfg]
                                -- 🎉 no goals
#align measure_theory.mem_ℒp.to_Lp_congr MeasureTheory.Memℒp.toLp_congr

@[simp]
theorem toLp_eq_toLp_iff {f g : α → E} (hf : Memℒp f p μ) (hg : Memℒp g p μ) :
    hf.toLp f = hg.toLp g ↔ f =ᵐ[μ] g := by simp [toLp]
                                            -- 🎉 no goals
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

instance instCoeFun : CoeFun (Lp E p μ) (fun _ => α → E) :=
  ⟨fun f => ((f : α →ₘ[μ] E) : α → E)⟩
#align measure_theory.Lp.has_coe_to_fun MeasureTheory.Lp.instCoeFun

@[ext high]
theorem ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g := by
  cases f
  -- ⊢ { val := val✝, property := property✝ } = g
  cases g
  -- ⊢ { val := val✝¹, property := property✝¹ } = { val := val✝, property := proper …
  simp only [Subtype.mk_eq_mk]
  -- ⊢ val✝¹ = val✝
  exact AEEqFun.ext h
  -- 🎉 no goals
#align measure_theory.Lp.ext MeasureTheory.Lp.ext

theorem ext_iff {f g : Lp E p μ} : f = g ↔ f =ᵐ[μ] g :=
  ⟨fun h => by rw [h], fun h => ext h⟩
               -- 🎉 no goals
#align measure_theory.Lp.ext_iff MeasureTheory.Lp.ext_iff

theorem mem_Lp_iff_snorm_lt_top {f : α →ₘ[μ] E} : f ∈ Lp E p μ ↔ snorm f p μ < ∞ :=
  Iff.refl _
#align measure_theory.Lp.mem_Lp_iff_snorm_lt_top MeasureTheory.Lp.mem_Lp_iff_snorm_lt_top

theorem mem_Lp_iff_memℒp {f : α →ₘ[μ] E} : f ∈ Lp E p μ ↔ Memℒp f p μ := by
  simp [mem_Lp_iff_snorm_lt_top, Memℒp, f.stronglyMeasurable.aestronglyMeasurable]
  -- 🎉 no goals
#align measure_theory.Lp.mem_Lp_iff_mem_ℒp MeasureTheory.Lp.mem_Lp_iff_memℒp

protected theorem antitone [IsFiniteMeasure μ] {p q : ℝ≥0∞} (hpq : p ≤ q) : Lp E q μ ≤ Lp E p μ :=
  fun f hf => (Memℒp.memℒp_of_exponent_le ⟨f.aestronglyMeasurable, hf⟩ hpq).2
#align measure_theory.Lp.antitone MeasureTheory.Lp.antitone

@[simp]
theorem coeFn_mk {f : α →ₘ[μ] E} (hf : snorm f p μ < ∞) : ((⟨f, hf⟩ : Lp E p μ) : α → E) = f :=
  rfl
#align measure_theory.Lp.coe_fn_mk MeasureTheory.Lp.coeFn_mk

-- @[simp] -- Porting note: dsimp can prove this
theorem coe_mk {f : α →ₘ[μ] E} (hf : snorm f p μ < ∞) : ((⟨f, hf⟩ : Lp E p μ) : α →ₘ[μ] E) = f :=
  rfl
#align measure_theory.Lp.coe_mk MeasureTheory.Lp.coe_mk

@[simp]
theorem toLp_coeFn (f : Lp E p μ) (hf : Memℒp f p μ) : hf.toLp f = f := by
  cases f
  -- ⊢ Memℒp.toLp (↑↑{ val := val✝, property := property✝ }) hf = { val := val✝, pr …
  simp [Memℒp.toLp]
  -- 🎉 no goals
#align measure_theory.Lp.to_Lp_coe_fn MeasureTheory.Lp.toLp_coeFn

theorem snorm_lt_top (f : Lp E p μ) : snorm f p μ < ∞ :=
  f.prop
#align measure_theory.Lp.snorm_lt_top MeasureTheory.Lp.snorm_lt_top

theorem snorm_ne_top (f : Lp E p μ) : snorm f p μ ≠ ∞ :=
  (snorm_lt_top f).ne
#align measure_theory.Lp.snorm_ne_top MeasureTheory.Lp.snorm_ne_top

@[measurability]
protected theorem stronglyMeasurable (f : Lp E p μ) : StronglyMeasurable f :=
  f.val.stronglyMeasurable
#align measure_theory.Lp.strongly_measurable MeasureTheory.Lp.stronglyMeasurable

@[measurability]
protected theorem aestronglyMeasurable (f : Lp E p μ) : AEStronglyMeasurable f μ :=
  f.val.aestronglyMeasurable
#align measure_theory.Lp.ae_strongly_measurable MeasureTheory.Lp.aestronglyMeasurable

protected theorem memℒp (f : Lp E p μ) : Memℒp f p μ :=
  ⟨Lp.aestronglyMeasurable f, f.prop⟩
#align measure_theory.Lp.mem_ℒp MeasureTheory.Lp.memℒp

variable (E p μ)

theorem coeFn_zero : ⇑(0 : Lp E p μ) =ᵐ[μ] 0 :=
  AEEqFun.coeFn_zero
#align measure_theory.Lp.coe_fn_zero MeasureTheory.Lp.coeFn_zero

variable {E p μ}

theorem coeFn_neg (f : Lp E p μ) : ⇑(-f) =ᵐ[μ] -f :=
  AEEqFun.coeFn_neg _
#align measure_theory.Lp.coe_fn_neg MeasureTheory.Lp.coeFn_neg

theorem coeFn_add (f g : Lp E p μ) : ⇑(f + g) =ᵐ[μ] f + g :=
  AEEqFun.coeFn_add _ _
#align measure_theory.Lp.coe_fn_add MeasureTheory.Lp.coeFn_add

theorem coeFn_sub (f g : Lp E p μ) : ⇑(f - g) =ᵐ[μ] f - g :=
  AEEqFun.coeFn_sub _ _
#align measure_theory.Lp.coe_fn_sub MeasureTheory.Lp.coeFn_sub

theorem const_mem_Lp (α) {_ : MeasurableSpace α} (μ : Measure α) (c : E) [IsFiniteMeasure μ] :
    @AEEqFun.const α _ _ μ _ c ∈ Lp E p μ :=
  (memℒp_const c).snorm_mk_lt_top
#align measure_theory.Lp.mem_Lp_const MeasureTheory.Lp.const_mem_Lp

instance instNorm : Norm (Lp E p μ) where norm f := ENNReal.toReal (snorm f p μ)
#align measure_theory.Lp.has_norm MeasureTheory.Lp.instNorm

-- note: we need this to be defeq to the instance from `SeminormedAddGroup.toNNNorm`, so
-- can't use `ENNReal.toNNReal (snorm f p μ)`
instance instNNNorm : NNNorm (Lp E p μ) where nnnorm f := ⟨‖f‖, ENNReal.toReal_nonneg⟩
#align measure_theory.Lp.has_nnnorm MeasureTheory.Lp.instNNNorm

instance instDist : Dist (Lp E p μ) where dist f g := ‖f - g‖
#align measure_theory.Lp.has_dist MeasureTheory.Lp.instDist

instance instEDist : EDist (Lp E p μ) where edist f g := snorm (⇑f - ⇑g) p μ
#align measure_theory.Lp.has_edist MeasureTheory.Lp.instEDist

theorem norm_def (f : Lp E p μ) : ‖f‖ = ENNReal.toReal (snorm f p μ) :=
  rfl
#align measure_theory.Lp.norm_def MeasureTheory.Lp.norm_def

theorem nnnorm_def (f : Lp E p μ) : ‖f‖₊ = ENNReal.toNNReal (snorm f p μ) :=
  rfl
#align measure_theory.Lp.nnnorm_def MeasureTheory.Lp.nnnorm_def

@[simp, norm_cast]
protected theorem coe_nnnorm (f : Lp E p μ) : (‖f‖₊ : ℝ) = ‖f‖ :=
  rfl
#align measure_theory.Lp.coe_nnnorm MeasureTheory.Lp.coe_nnnorm

@[simp]
theorem norm_toLp (f : α → E) (hf : Memℒp f p μ) : ‖hf.toLp f‖ = ENNReal.toReal (snorm f p μ) := by
  erw [norm_def, snorm_congr_ae (Memℒp.coeFn_toLp hf)]
  -- 🎉 no goals
#align measure_theory.Lp.norm_to_Lp MeasureTheory.Lp.norm_toLp

@[simp]
theorem nnnorm_toLp (f : α → E) (hf : Memℒp f p μ) :
    ‖hf.toLp f‖₊ = ENNReal.toNNReal (snorm f p μ) :=
  NNReal.eq <| norm_toLp f hf
#align measure_theory.Lp.nnnorm_to_Lp MeasureTheory.Lp.nnnorm_toLp

theorem coe_nnnorm_toLp {f : α → E} (hf : Memℒp f p μ) : (‖hf.toLp f‖₊ : ℝ≥0∞) = snorm f p μ := by
  rw [nnnorm_toLp f hf, ENNReal.coe_toNNReal hf.2.ne]
  -- 🎉 no goals

theorem dist_def (f g : Lp E p μ) : dist f g = (snorm (⇑f - ⇑g) p μ).toReal := by
  simp_rw [dist, norm_def]
  -- ⊢ ENNReal.toReal (snorm (↑↑(f - g)) p μ) = ENNReal.toReal (snorm (↑↑f - ↑↑g) p …
  refine congr_arg _ ?_
  -- ⊢ snorm (↑↑(f - g)) p μ = snorm (↑↑f - ↑↑g) p μ
  apply snorm_congr_ae (coeFn_sub _ _)
  -- 🎉 no goals
#align measure_theory.Lp.dist_def MeasureTheory.Lp.dist_def

theorem edist_def (f g : Lp E p μ) : edist f g = snorm (⇑f - ⇑g) p μ :=
  rfl
#align measure_theory.Lp.edist_def MeasureTheory.Lp.edist_def

protected theorem edist_dist (f g : Lp E p μ) : edist f g = .ofReal (dist f g) := by
  rw [edist_def, dist_def, ← snorm_congr_ae (coeFn_sub _ _),
    ENNReal.ofReal_toReal (snorm_ne_top (f - g))]

protected theorem dist_edist (f g : Lp E p μ) : dist f g = (edist f g).toReal :=
  MeasureTheory.Lp.dist_def ..

@[simp]
theorem edist_toLp_toLp (f g : α → E) (hf : Memℒp f p μ) (hg : Memℒp g p μ) :
    edist (hf.toLp f) (hg.toLp g) = snorm (f - g) p μ := by
  rw [edist_def]
  -- ⊢ snorm (↑↑(Memℒp.toLp f hf) - ↑↑(Memℒp.toLp g hg)) p μ = snorm (f - g) p μ
  exact snorm_congr_ae (hf.coeFn_toLp.sub hg.coeFn_toLp)
  -- 🎉 no goals
#align measure_theory.Lp.edist_to_Lp_to_Lp MeasureTheory.Lp.edist_toLp_toLp

@[simp]
theorem edist_toLp_zero (f : α → E) (hf : Memℒp f p μ) : edist (hf.toLp f) 0 = snorm f p μ := by
  convert edist_toLp_toLp f 0 hf zero_memℒp
  -- ⊢ f = f - 0
  simp
  -- 🎉 no goals
#align measure_theory.Lp.edist_to_Lp_zero MeasureTheory.Lp.edist_toLp_zero

@[simp]
theorem nnnorm_zero : ‖(0 : Lp E p μ)‖₊ = 0 := by
  rw [nnnorm_def]
  -- ⊢ ENNReal.toNNReal (snorm (↑↑0) p μ) = 0
  change (snorm (⇑(0 : α →ₘ[μ] E)) p μ).toNNReal = 0
  -- ⊢ ENNReal.toNNReal (snorm (↑0) p μ) = 0
  simp [snorm_congr_ae AEEqFun.coeFn_zero, snorm_zero]
  -- 🎉 no goals
#align measure_theory.Lp.nnnorm_zero MeasureTheory.Lp.nnnorm_zero

@[simp]
theorem norm_zero : ‖(0 : Lp E p μ)‖ = 0 :=
  congr_arg ((↑) : ℝ≥0 → ℝ) nnnorm_zero
#align measure_theory.Lp.norm_zero MeasureTheory.Lp.norm_zero

@[simp]
theorem norm_measure_zero (f : Lp E p (0 : MeasureTheory.Measure α)) : ‖f‖ = 0 := by
  simp [norm_def]
  -- 🎉 no goals

@[simp] theorem norm_exponent_zero (f : Lp E 0 μ) : ‖f‖ = 0 := by simp [norm_def]
                                                                  -- 🎉 no goals

theorem nnnorm_eq_zero_iff {f : Lp E p μ} (hp : 0 < p) : ‖f‖₊ = 0 ↔ f = 0 := by
  refine' ⟨fun hf => _, fun hf => by simp [hf]⟩
  -- ⊢ f = 0
  rw [nnnorm_def, ENNReal.toNNReal_eq_zero_iff] at hf
  -- ⊢ f = 0
  cases hf with
  | inl hf =>
    rw [snorm_eq_zero_iff (Lp.aestronglyMeasurable f) hp.ne.symm] at hf
    exact Subtype.eq (AEEqFun.ext (hf.trans AEEqFun.coeFn_zero.symm))
  | inr hf =>
    exact absurd hf (snorm_ne_top f)
#align measure_theory.Lp.nnnorm_eq_zero_iff MeasureTheory.Lp.nnnorm_eq_zero_iff

theorem norm_eq_zero_iff {f : Lp E p μ} (hp : 0 < p) : ‖f‖ = 0 ↔ f = 0 :=
  Iff.symm <| (nnnorm_eq_zero_iff hp).symm.trans <| (NNReal.coe_eq_zero _).symm
#align measure_theory.Lp.norm_eq_zero_iff MeasureTheory.Lp.norm_eq_zero_iff

theorem eq_zero_iff_ae_eq_zero {f : Lp E p μ} : f = 0 ↔ f =ᵐ[μ] 0 := by
  rw [← (Lp.memℒp f).toLp_eq_toLp_iff zero_memℒp, Memℒp.toLp_zero, toLp_coeFn]
  -- 🎉 no goals
#align measure_theory.Lp.eq_zero_iff_ae_eq_zero MeasureTheory.Lp.eq_zero_iff_ae_eq_zero

@[simp]
theorem nnnorm_neg (f : Lp E p μ) : ‖-f‖₊ = ‖f‖₊ := by
  rw [nnnorm_def, nnnorm_def, snorm_congr_ae (coeFn_neg _), snorm_neg]
  -- 🎉 no goals
#align measure_theory.Lp.nnnorm_neg MeasureTheory.Lp.nnnorm_neg

@[simp]
theorem norm_neg (f : Lp E p μ) : ‖-f‖ = ‖f‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) (nnnorm_neg f)
#align measure_theory.Lp.norm_neg MeasureTheory.Lp.norm_neg

theorem nnnorm_le_mul_nnnorm_of_ae_le_mul {c : ℝ≥0} {f : Lp E p μ} {g : Lp F p μ}
    (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊) : ‖f‖₊ ≤ c * ‖g‖₊ := by
  simp only [nnnorm_def]
  -- ⊢ ENNReal.toNNReal (snorm (↑↑f) p μ) ≤ c * ENNReal.toNNReal (snorm (↑↑g) p μ)
  have := snorm_le_nnreal_smul_snorm_of_ae_le_mul h p
  -- ⊢ ENNReal.toNNReal (snorm (↑↑f) p μ) ≤ c * ENNReal.toNNReal (snorm (↑↑g) p μ)
  rwa [← ENNReal.toNNReal_le_toNNReal, ENNReal.smul_def, smul_eq_mul, ENNReal.toNNReal_mul,
    ENNReal.toNNReal_coe] at this
  · exact (Lp.memℒp _).snorm_ne_top
    -- 🎉 no goals
  · exact ENNReal.mul_ne_top ENNReal.coe_ne_top (Lp.memℒp _).snorm_ne_top
    -- 🎉 no goals
#align measure_theory.Lp.nnnorm_le_mul_nnnorm_of_ae_le_mul MeasureTheory.Lp.nnnorm_le_mul_nnnorm_of_ae_le_mul

theorem norm_le_mul_norm_of_ae_le_mul {c : ℝ} {f : Lp E p μ} {g : Lp F p μ}
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) : ‖f‖ ≤ c * ‖g‖ := by
  cases' le_or_lt 0 c with hc hc
  -- ⊢ ‖f‖ ≤ c * ‖g‖
  · lift c to ℝ≥0 using hc
    -- ⊢ ‖f‖ ≤ ↑c * ‖g‖
    exact NNReal.coe_le_coe.mpr (nnnorm_le_mul_nnnorm_of_ae_le_mul h)
    -- 🎉 no goals
  · simp only [norm_def]
    -- ⊢ ENNReal.toReal (snorm (↑↑f) p μ) ≤ c * ENNReal.toReal (snorm (↑↑g) p μ)
    have := snorm_eq_zero_and_zero_of_ae_le_mul_neg h hc p
    -- ⊢ ENNReal.toReal (snorm (↑↑f) p μ) ≤ c * ENNReal.toReal (snorm (↑↑g) p μ)
    simp [this]
    -- 🎉 no goals
#align measure_theory.Lp.norm_le_mul_norm_of_ae_le_mul MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul

theorem norm_le_norm_of_ae_le {f : Lp E p μ} {g : Lp F p μ} (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
    ‖f‖ ≤ ‖g‖ := by
  rw [norm_def, norm_def, ENNReal.toReal_le_toReal (snorm_ne_top _) (snorm_ne_top _)]
  -- ⊢ snorm (↑↑f) p μ ≤ snorm (↑↑g) p μ
  exact snorm_mono_ae h
  -- 🎉 no goals
#align measure_theory.Lp.norm_le_norm_of_ae_le MeasureTheory.Lp.norm_le_norm_of_ae_le

theorem mem_Lp_of_nnnorm_ae_le_mul {c : ℝ≥0} {f : α →ₘ[μ] E} {g : Lp F p μ}
    (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊) : f ∈ Lp E p μ :=
  mem_Lp_iff_memℒp.2 <| Memℒp.of_nnnorm_le_mul (Lp.memℒp g) f.aestronglyMeasurable h
#align measure_theory.Lp.mem_Lp_of_nnnorm_ae_le_mul MeasureTheory.Lp.mem_Lp_of_nnnorm_ae_le_mul

theorem mem_Lp_of_ae_le_mul {c : ℝ} {f : α →ₘ[μ] E} {g : Lp F p μ}
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) : f ∈ Lp E p μ :=
  mem_Lp_iff_memℒp.2 <| Memℒp.of_le_mul (Lp.memℒp g) f.aestronglyMeasurable h
#align measure_theory.Lp.mem_Lp_of_ae_le_mul MeasureTheory.Lp.mem_Lp_of_ae_le_mul

theorem mem_Lp_of_nnnorm_ae_le {f : α →ₘ[μ] E} {g : Lp F p μ} (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ ‖g x‖₊) :
    f ∈ Lp E p μ :=
  mem_Lp_iff_memℒp.2 <| Memℒp.of_le (Lp.memℒp g) f.aestronglyMeasurable h
#align measure_theory.Lp.mem_Lp_of_nnnorm_ae_le MeasureTheory.Lp.mem_Lp_of_nnnorm_ae_le

theorem mem_Lp_of_ae_le {f : α →ₘ[μ] E} {g : Lp F p μ} (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
    f ∈ Lp E p μ :=
  mem_Lp_of_nnnorm_ae_le h
#align measure_theory.Lp.mem_Lp_of_ae_le MeasureTheory.Lp.mem_Lp_of_ae_le

theorem mem_Lp_of_ae_nnnorm_bound [IsFiniteMeasure μ] {f : α →ₘ[μ] E} (C : ℝ≥0)
    (hfC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) : f ∈ Lp E p μ :=
  mem_Lp_iff_memℒp.2 <| Memℒp.of_bound f.aestronglyMeasurable _ hfC
#align measure_theory.Lp.mem_Lp_of_ae_nnnorm_bound MeasureTheory.Lp.mem_Lp_of_ae_nnnorm_bound

theorem mem_Lp_of_ae_bound [IsFiniteMeasure μ] {f : α →ₘ[μ] E} (C : ℝ) (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    f ∈ Lp E p μ :=
  mem_Lp_iff_memℒp.2 <| Memℒp.of_bound f.aestronglyMeasurable _ hfC
#align measure_theory.Lp.mem_Lp_of_ae_bound MeasureTheory.Lp.mem_Lp_of_ae_bound

theorem nnnorm_le_of_ae_bound [IsFiniteMeasure μ] {f : Lp E p μ} {C : ℝ≥0}
    (hfC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) : ‖f‖₊ ≤ measureUnivNNReal μ ^ p.toReal⁻¹ * C := by
  by_cases hμ : μ = 0
  -- ⊢ ‖f‖₊ ≤ measureUnivNNReal μ ^ (ENNReal.toReal p)⁻¹ * C
  · by_cases hp : p.toReal⁻¹ = 0
    -- ⊢ ‖f‖₊ ≤ measureUnivNNReal μ ^ (ENNReal.toReal p)⁻¹ * C
    · simp [hp, hμ, nnnorm_def]
      -- 🎉 no goals
    · simp [hμ, nnnorm_def, Real.zero_rpow hp]
      -- 🎉 no goals
  rw [← ENNReal.coe_le_coe, nnnorm_def, ENNReal.coe_toNNReal (snorm_ne_top _)]
  -- ⊢ snorm (↑↑f) p μ ≤ ↑(measureUnivNNReal μ ^ (ENNReal.toReal p)⁻¹ * C)
  refine' (snorm_le_of_ae_nnnorm_bound hfC).trans_eq _
  -- ⊢ C • ↑↑μ Set.univ ^ (ENNReal.toReal p)⁻¹ = ↑(measureUnivNNReal μ ^ (ENNReal.t …
  rw [← coe_measureUnivNNReal μ, ENNReal.coe_rpow_of_ne_zero (measureUnivNNReal_pos hμ).ne',
    ENNReal.coe_mul, mul_comm, ENNReal.smul_def, smul_eq_mul]
#align measure_theory.Lp.nnnorm_le_of_ae_bound MeasureTheory.Lp.nnnorm_le_of_ae_bound

theorem norm_le_of_ae_bound [IsFiniteMeasure μ] {f : Lp E p μ} {C : ℝ} (hC : 0 ≤ C)
    (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : ‖f‖ ≤ measureUnivNNReal μ ^ p.toReal⁻¹ * C := by
  lift C to ℝ≥0 using hC
  -- ⊢ ‖f‖ ≤ ↑(measureUnivNNReal μ ^ (ENNReal.toReal p)⁻¹) * ↑C
  have := nnnorm_le_of_ae_bound hfC
  -- ⊢ ‖f‖ ≤ ↑(measureUnivNNReal μ ^ (ENNReal.toReal p)⁻¹) * ↑C
  rwa [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_rpow] at this
  -- 🎉 no goals
#align measure_theory.Lp.norm_le_of_ae_bound MeasureTheory.Lp.norm_le_of_ae_bound

instance instNormedAddCommGroup [hp : Fact (1 ≤ p)] : NormedAddCommGroup (Lp E p μ) :=
  { AddGroupNorm.toNormedAddCommGroup
      { toFun := (norm : Lp E p μ → ℝ)
        map_zero' := norm_zero
        neg' := by simp
                   -- 🎉 no goals
        add_le' := fun f g => by
          -- ⊢ ENNReal.toReal (snorm (↑↑(f + g)) p μ) ≤ ENNReal.toReal (snorm (↑↑f) p μ) +  …
          simp only [norm_def]
          -- ⊢ ENNReal.toReal (snorm (↑↑(f + g)) p μ) ≤ ENNReal.toReal (snorm (↑↑f) p μ + s …
          rw [← ENNReal.toReal_add (snorm_ne_top f) (snorm_ne_top g)]
          -- ⊢ ENNReal.toReal (snorm (↑↑(f + g)) p μ) ≤ ENNReal.toReal (snorm (↑↑f) p μ + s …
          suffices h_snorm : snorm (⇑(f + g)) p μ ≤ snorm (⇑f) p μ + snorm (⇑g) p μ
            -- ⊢ snorm (↑↑f) p μ + snorm (↑↑g) p μ ≠ ⊤
          · rwa [ENNReal.toReal_le_toReal (snorm_ne_top (f + g))]
            -- 🎉 no goals
            exact ENNReal.add_ne_top.mpr ⟨snorm_ne_top f, snorm_ne_top g⟩
          -- ⊢ snorm (↑↑f + ↑↑g) p μ ≤ snorm (↑↑f) p μ + snorm (↑↑g) p μ
          rw [snorm_congr_ae (coeFn_add _ _)]
          -- 🎉 no goals
          exact snorm_add_le (Lp.aestronglyMeasurable f) (Lp.aestronglyMeasurable g) hp.1
        eq_zero_of_map_eq_zero' := fun f =>
          (norm_eq_zero_iff <| zero_lt_one.trans_le hp.1).1 } with
    edist := edist
    edist_dist := Lp.edist_dist }
#align measure_theory.Lp.normed_add_comm_group MeasureTheory.Lp.instNormedAddCommGroup

-- check no diamond is created
example [Fact (1 ≤ p)] : PseudoEMetricSpace.toEDist = (Lp.instEDist : EDist (Lp E p μ)) :=
  rfl

example [Fact (1 ≤ p)] : SeminormedAddGroup.toNNNorm = (Lp.instNNNorm : NNNorm (Lp E p μ)) :=
  rfl

section BoundedSMul

variable {𝕜 𝕜' : Type*}

variable [NormedRing 𝕜] [NormedRing 𝕜'] [Module 𝕜 E] [Module 𝕜' E]

variable [BoundedSMul 𝕜 E] [BoundedSMul 𝕜' E]

theorem const_smul_mem_Lp (c : 𝕜) (f : Lp E p μ) : c • (f : α →ₘ[μ] E) ∈ Lp E p μ := by
  rw [mem_Lp_iff_snorm_lt_top, snorm_congr_ae (AEEqFun.coeFn_smul _ _)]
  -- ⊢ snorm (c • ↑↑f) p μ < ⊤
  refine' (snorm_const_smul_le _ _).trans_lt _
  -- ⊢ ‖c‖₊ • snorm (↑↑f) p μ < ⊤
  rw [ENNReal.smul_def, smul_eq_mul, ENNReal.mul_lt_top_iff]
  -- ⊢ ↑‖c‖₊ < ⊤ ∧ snorm (↑↑f) p μ < ⊤ ∨ ↑‖c‖₊ = 0 ∨ snorm (↑↑f) p μ = 0
  exact Or.inl ⟨ENNReal.coe_lt_top, f.prop⟩
  -- 🎉 no goals
#align measure_theory.Lp.mem_Lp_const_smul MeasureTheory.Lp.const_smul_mem_Lp

variable (E p μ 𝕜)

/-- The `𝕜`-submodule of elements of `α →ₘ[μ] E` whose `Lp` norm is finite.  This is `Lp E p μ`,
with extra structure. -/
def LpSubmodule : Submodule 𝕜 (α →ₘ[μ] E) :=
  { Lp E p μ with smul_mem' := fun c f hf => by simpa using const_smul_mem_Lp c ⟨f, hf⟩ }
                                                -- 🎉 no goals
#align measure_theory.Lp.Lp_submodule MeasureTheory.Lp.LpSubmodule

variable {E p μ 𝕜}

theorem coe_LpSubmodule : (LpSubmodule E p μ 𝕜).toAddSubgroup = Lp E p μ :=
  rfl
#align measure_theory.Lp.coe_Lp_submodule MeasureTheory.Lp.coe_LpSubmodule

instance instModule : Module 𝕜 (Lp E p μ) :=
  { (LpSubmodule E p μ 𝕜).module with }
#align measure_theory.Lp.module MeasureTheory.Lp.instModule

theorem coeFn_smul (c : 𝕜) (f : Lp E p μ) : ⇑(c • f) =ᵐ[μ] c • ⇑f :=
  AEEqFun.coeFn_smul _ _
#align measure_theory.Lp.coe_fn_smul MeasureTheory.Lp.coeFn_smul

instance instIsCentralScalar [Module 𝕜ᵐᵒᵖ E] [BoundedSMul 𝕜ᵐᵒᵖ E] [IsCentralScalar 𝕜 E] :
    IsCentralScalar 𝕜 (Lp E p μ) where
  op_smul_eq_smul k f := Subtype.ext <| op_smul_eq_smul k (f : α →ₘ[μ] E)
#align measure_theory.Lp.is_central_scalar MeasureTheory.Lp.instIsCentralScalar

instance instSMulCommClass [SMulCommClass 𝕜 𝕜' E] : SMulCommClass 𝕜 𝕜' (Lp E p μ) where
  smul_comm k k' f := Subtype.ext <| smul_comm k k' (f : α →ₘ[μ] E)
#align measure_theory.Lp.smul_comm_class MeasureTheory.Lp.instSMulCommClass

instance instIsScalarTower [SMul 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' E] : IsScalarTower 𝕜 𝕜' (Lp E p μ) where
  smul_assoc k k' f := Subtype.ext <| smul_assoc k k' (f : α →ₘ[μ] E)

instance instBoundedSMul [Fact (1 ≤ p)] : BoundedSMul 𝕜 (Lp E p μ) :=
  -- TODO: add `BoundedSMul.of_nnnorm_smul_le`
  BoundedSMul.of_norm_smul_le fun r f => by
    suffices (‖r • f‖₊ : ℝ≥0∞) ≤ ‖r‖₊ * ‖f‖₊ by exact_mod_cast this
    -- ⊢ ↑‖r • f‖₊ ≤ ↑‖r‖₊ * ↑‖f‖₊
    rw [nnnorm_def, nnnorm_def, ENNReal.coe_toNNReal (Lp.snorm_ne_top _),
      snorm_congr_ae (coeFn_smul _ _), ENNReal.coe_toNNReal (Lp.snorm_ne_top _)]
    exact snorm_const_smul_le r f
    -- 🎉 no goals
#align measure_theory.Lp.has_bounded_smul MeasureTheory.Lp.instBoundedSMul

end BoundedSMul

section NormedSpace

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]

set_option synthInstance.maxHeartbeats 30000 in
instance instNormedSpace [Fact (1 ≤ p)] : NormedSpace 𝕜 (Lp E p μ) where
  norm_smul_le _ _ := norm_smul_le _ _
#align measure_theory.Lp.normed_space MeasureTheory.Lp.instNormedSpace

end NormedSpace

end Lp

namespace Memℒp

variable {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [BoundedSMul 𝕜 E]

theorem toLp_const_smul {f : α → E} (c : 𝕜) (hf : Memℒp f p μ) :
    (hf.const_smul c).toLp (c • f) = c • hf.toLp f :=
  rfl
#align measure_theory.mem_ℒp.to_Lp_const_smul MeasureTheory.Memℒp.toLp_const_smul

end Memℒp

/-! ### Indicator of a set as an element of Lᵖ

For a set `s` with `(hs : MeasurableSet s)` and `(hμs : μ s < ∞)`, we build
`indicatorConstLp p hs hμs c`, the element of `Lp` corresponding to `s.indicator (fun _ => c)`.
-/


section Indicator

set_option autoImplicit true

variable {c : E} {f : α → E} {hf : AEStronglyMeasurable f μ}

theorem snormEssSup_indicator_le (s : Set α) (f : α → G) :
    snormEssSup (s.indicator f) μ ≤ snormEssSup f μ := by
  refine' essSup_mono_ae (eventually_of_forall fun x => _)
  -- ⊢ (fun x => ↑‖Set.indicator s f x‖₊) x ≤ (fun x => ↑‖f x‖₊) x
  rw [ENNReal.coe_le_coe, nnnorm_indicator_eq_indicator_nnnorm]
  -- ⊢ Set.indicator s (fun a => ‖f a‖₊) x ≤ ‖f x‖₊
  exact Set.indicator_le_self s _ x
  -- 🎉 no goals
#align measure_theory.snorm_ess_sup_indicator_le MeasureTheory.snormEssSup_indicator_le

theorem snormEssSup_indicator_const_le (s : Set α) (c : G) :
    snormEssSup (s.indicator fun _ : α => c) μ ≤ ‖c‖₊ := by
  by_cases hμ0 : μ = 0
  -- ⊢ snormEssSup (Set.indicator s fun x => c) μ ≤ ↑‖c‖₊
  · rw [hμ0, snormEssSup_measure_zero]
    -- ⊢ 0 ≤ ↑‖c‖₊
    exact zero_le _
    -- 🎉 no goals
  · exact (snormEssSup_indicator_le s fun _ => c).trans (snormEssSup_const c hμ0).le
    -- 🎉 no goals
#align measure_theory.snorm_ess_sup_indicator_const_le MeasureTheory.snormEssSup_indicator_const_le

theorem snormEssSup_indicator_const_eq (s : Set α) (c : G) (hμs : μ s ≠ 0) :
    snormEssSup (s.indicator fun _ : α => c) μ = ‖c‖₊ := by
  refine' le_antisymm (snormEssSup_indicator_const_le s c) _
  -- ⊢ ↑‖c‖₊ ≤ snormEssSup (Set.indicator s fun x => c) μ
  by_contra' h
  -- ⊢ False
  have h' := ae_iff.mp (ae_lt_of_essSup_lt h)
  -- ⊢ False
  push_neg at h'
  -- ⊢ False
  refine' hμs (measure_mono_null (fun x hx_mem => _) h')
  -- ⊢ x ∈ {a | ↑‖c‖₊ ≤ ↑‖Set.indicator s (fun x => c) a‖₊}
  rw [Set.mem_setOf_eq, Set.indicator_of_mem hx_mem]
  -- 🎉 no goals
#align measure_theory.snorm_ess_sup_indicator_const_eq MeasureTheory.snormEssSup_indicator_const_eq

theorem snorm_indicator_le (f : α → E) {s : Set α} :
    snorm (s.indicator f) p μ ≤ snorm f p μ := by
  refine' snorm_mono_ae (eventually_of_forall fun x => _)
  -- ⊢ ‖Set.indicator s f x‖ ≤ ‖f x‖
  suffices ‖s.indicator f x‖₊ ≤ ‖f x‖₊ by exact NNReal.coe_mono this
  -- ⊢ ‖Set.indicator s f x‖₊ ≤ ‖f x‖₊
  rw [nnnorm_indicator_eq_indicator_nnnorm]
  -- ⊢ Set.indicator s (fun a => ‖f a‖₊) x ≤ ‖f x‖₊
  exact s.indicator_le_self _ x
  -- 🎉 no goals
#align measure_theory.snorm_indicator_le MeasureTheory.snorm_indicator_le

theorem snorm_indicator_const₀ {c : G} (hs : NullMeasurableSet s μ) (hp : p ≠ 0) (hp_top : p ≠ ∞) :
    snorm (s.indicator fun _ => c) p μ = ‖c‖₊ * μ s ^ (1 / p.toReal) :=
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp hp_top
  calc
    snorm (s.indicator fun _ => c) p μ
      = (∫⁻ x, ((‖(s.indicator fun _ ↦ c) x‖₊ : ℝ≥0∞) ^ p.toReal) ∂μ) ^ (1 / p.toReal) :=
          snorm_eq_lintegral_rpow_nnnorm hp hp_top
    _ = (∫⁻ x, (s.indicator fun _ ↦ (‖c‖₊ : ℝ≥0∞) ^ p.toReal) x ∂μ) ^ (1 / p.toReal) := by
      congr 2
      -- ⊢ (fun x => ↑‖Set.indicator s (fun x => c) x‖₊ ^ ENNReal.toReal p) = fun x =>  …
      refine (Set.comp_indicator_const c (fun x : G ↦ (‖x‖₊ : ℝ≥0∞) ^ p.toReal) ?_)
      -- ⊢ (fun x => ↑‖x‖₊ ^ ENNReal.toReal p) 0 = 0
      simp [hp_pos]
      -- 🎉 no goals
    _ = ‖c‖₊ * μ s ^ (1 / p.toReal) := by
      rw [lintegral_indicator_const₀ hs, ENNReal.mul_rpow_of_nonneg, ← ENNReal.rpow_mul,
        mul_one_div_cancel hp_pos.ne', ENNReal.rpow_one]
      positivity
      -- 🎉 no goals

theorem snorm_indicator_const {c : G} (hs : MeasurableSet s) (hp : p ≠ 0) (hp_top : p ≠ ∞) :
    snorm (s.indicator fun _ => c) p μ = ‖c‖₊ * μ s ^ (1 / p.toReal) :=
  snorm_indicator_const₀ hs.nullMeasurableSet hp hp_top
#align measure_theory.snorm_indicator_const MeasureTheory.snorm_indicator_const

theorem snorm_indicator_const' {c : G} (hs : MeasurableSet s) (hμs : μ s ≠ 0) (hp : p ≠ 0) :
    snorm (s.indicator fun _ => c) p μ = ‖c‖₊ * μ s ^ (1 / p.toReal) := by
  by_cases hp_top : p = ∞
  -- ⊢ snorm (Set.indicator s fun x => c) p μ = ↑‖c‖₊ * ↑↑μ s ^ (1 / ENNReal.toReal …
  · simp [hp_top, snormEssSup_indicator_const_eq s c hμs]
    -- 🎉 no goals
  · exact snorm_indicator_const hs hp hp_top
    -- 🎉 no goals
#align measure_theory.snorm_indicator_const' MeasureTheory.snorm_indicator_const'

theorem snorm_indicator_const_le (c : G) (p : ℝ≥0∞) :
    snorm (s.indicator fun _ => c) p μ ≤ ‖c‖₊ * μ s ^ (1 / p.toReal) := by
  rcases eq_or_ne p 0 with (rfl | hp)
  -- ⊢ snorm (Set.indicator s fun x => c) 0 μ ≤ ↑‖c‖₊ * ↑↑μ s ^ (1 / ENNReal.toReal …
  · simp only [snorm_exponent_zero, zero_le']
    -- 🎉 no goals
  rcases eq_or_ne p ∞ with (rfl | h'p)
  -- ⊢ snorm (Set.indicator s fun x => c) ⊤ μ ≤ ↑‖c‖₊ * ↑↑μ s ^ (1 / ENNReal.toReal …
  · simp only [snorm_exponent_top, ENNReal.top_toReal, _root_.div_zero, ENNReal.rpow_zero, mul_one]
    -- ⊢ snormEssSup (Set.indicator s fun x => c) μ ≤ ↑‖c‖₊
    exact snormEssSup_indicator_const_le _ _
    -- 🎉 no goals
  let t := toMeasurable μ s
  -- ⊢ snorm (Set.indicator s fun x => c) p μ ≤ ↑‖c‖₊ * ↑↑μ s ^ (1 / ENNReal.toReal …
  calc
    snorm (s.indicator fun _ => c) p μ ≤ snorm (t.indicator fun _ => c) p μ :=
      snorm_mono (norm_indicator_le_of_subset (subset_toMeasurable _ _) _)
    _ = ‖c‖₊ * μ t ^ (1 / p.toReal) :=
      (snorm_indicator_const (measurableSet_toMeasurable _ _) hp h'p)
    _ = ‖c‖₊ * μ s ^ (1 / p.toReal) := by rw [measure_toMeasurable]
#align measure_theory.snorm_indicator_const_le MeasureTheory.snorm_indicator_const_le

theorem Memℒp.indicator (hs : MeasurableSet s) (hf : Memℒp f p μ) : Memℒp (s.indicator f) p μ :=
  ⟨hf.aestronglyMeasurable.indicator hs, lt_of_le_of_lt (snorm_indicator_le f) hf.snorm_lt_top⟩
#align measure_theory.mem_ℒp.indicator MeasureTheory.Memℒp.indicator

theorem snormEssSup_indicator_eq_snormEssSup_restrict {f : α → F} (hs : MeasurableSet s) :
    snormEssSup (s.indicator f) μ = snormEssSup f (μ.restrict s) := by
  simp_rw [snormEssSup, nnnorm_indicator_eq_indicator_nnnorm, ENNReal.coe_indicator]
  -- ⊢ essSup (fun x => Set.indicator s (fun x => ↑‖f x‖₊) x) μ = essSup (fun x =>  …
  by_cases hs_null : μ s = 0
  -- ⊢ essSup (fun x => Set.indicator s (fun x => ↑‖f x‖₊) x) μ = essSup (fun x =>  …
  · rw [Measure.restrict_zero_set hs_null]
    -- ⊢ essSup (fun x => Set.indicator s (fun x => ↑‖f x‖₊) x) μ = essSup (fun x =>  …
    simp only [essSup_measure_zero, ENNReal.essSup_eq_zero_iff, ENNReal.bot_eq_zero]
    -- ⊢ (fun x => Set.indicator s (fun x => ↑‖f x‖₊) x) =ᵐ[μ] 0
    have hs_empty : s =ᵐ[μ] (∅ : Set α) := by rw [ae_eq_set]; simpa using hs_null
    -- ⊢ (fun x => Set.indicator s (fun x => ↑‖f x‖₊) x) =ᵐ[μ] 0
    refine' (indicator_ae_eq_of_ae_eq_set hs_empty).trans _
    -- ⊢ (Set.indicator ∅ fun x => ↑‖f x‖₊) =ᵐ[μ] 0
    rw [Set.indicator_empty]
    -- ⊢ (fun x => 0) =ᵐ[μ] 0
    rfl
    -- 🎉 no goals
  rw [essSup_indicator_eq_essSup_restrict (eventually_of_forall fun x => ?_) hs hs_null]
  -- ⊢ OfNat.ofNat 0 x ≤ ↑‖f x‖₊
  rw [Pi.zero_apply]
  -- ⊢ 0 ≤ ↑‖f x‖₊
  exact zero_le _
  -- 🎉 no goals
#align measure_theory.snorm_ess_sup_indicator_eq_snorm_ess_sup_restrict MeasureTheory.snormEssSup_indicator_eq_snormEssSup_restrict

theorem snorm_indicator_eq_snorm_restrict {f : α → F} (hs : MeasurableSet s) :
    snorm (s.indicator f) p μ = snorm f p (μ.restrict s) := by
  by_cases hp_zero : p = 0
  -- ⊢ snorm (Set.indicator s f) p μ = snorm f p (Measure.restrict μ s)
  · simp only [hp_zero, snorm_exponent_zero]
    -- 🎉 no goals
  by_cases hp_top : p = ∞
  -- ⊢ snorm (Set.indicator s f) p μ = snorm f p (Measure.restrict μ s)
  · simp_rw [hp_top, snorm_exponent_top]
    -- ⊢ snormEssSup (Set.indicator s f) μ = snormEssSup f (Measure.restrict μ s)
    exact snormEssSup_indicator_eq_snormEssSup_restrict hs
    -- 🎉 no goals
  simp_rw [snorm_eq_lintegral_rpow_nnnorm hp_zero hp_top]
  -- ⊢ (∫⁻ (x : α), ↑‖Set.indicator s f x‖₊ ^ ENNReal.toReal p ∂μ) ^ (1 / ENNReal.t …
  suffices (∫⁻ x, (‖s.indicator f x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ) =
      ∫⁻ x in s, (‖f x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ by rw [this]
  rw [← lintegral_indicator _ hs]
  -- ⊢ ∫⁻ (x : α), ↑‖Set.indicator s f x‖₊ ^ ENNReal.toReal p ∂μ = ∫⁻ (a : α), Set. …
  congr
  -- ⊢ (fun x => ↑‖Set.indicator s f x‖₊ ^ ENNReal.toReal p) = fun a => Set.indicat …
  simp_rw [nnnorm_indicator_eq_indicator_nnnorm, ENNReal.coe_indicator]
  -- ⊢ (fun x => Set.indicator s (fun x => ↑‖f x‖₊) x ^ ENNReal.toReal p) = fun a = …
  have h_zero : (fun x => x ^ p.toReal) (0 : ℝ≥0∞) = 0 := by
    simp [ENNReal.toReal_pos hp_zero hp_top]
  -- Porting note: The implicit argument should be specified because the elaborator can't deal with
  --               `∘` well.
  exact (Set.indicator_comp_of_zero (g := fun x : ℝ≥0∞ => x ^ p.toReal) h_zero).symm
  -- 🎉 no goals
#align measure_theory.snorm_indicator_eq_snorm_restrict MeasureTheory.snorm_indicator_eq_snorm_restrict

theorem memℒp_indicator_iff_restrict (hs : MeasurableSet s) :
    Memℒp (s.indicator f) p μ ↔ Memℒp f p (μ.restrict s) := by
  simp [Memℒp, aestronglyMeasurable_indicator_iff hs, snorm_indicator_eq_snorm_restrict hs]
  -- 🎉 no goals
#align measure_theory.mem_ℒp_indicator_iff_restrict MeasureTheory.memℒp_indicator_iff_restrict

theorem memℒp_indicator_const (p : ℝ≥0∞) (hs : MeasurableSet s) (c : E) (hμsc : c = 0 ∨ μ s ≠ ∞) :
    Memℒp (s.indicator fun _ => c) p μ := by
  rw [memℒp_indicator_iff_restrict hs]
  -- ⊢ Memℒp (fun x => c) p
  rcases hμsc with rfl | hμ
  -- ⊢ Memℒp (fun x => 0) p
  · exact zero_memℒp
    -- 🎉 no goals
  · have := Fact.mk hμ.lt_top
    -- ⊢ Memℒp (fun x => c) p
    apply memℒp_const
    -- 🎉 no goals
#align measure_theory.mem_ℒp_indicator_const MeasureTheory.memℒp_indicator_const

/-- The `ℒ^p` norm of the indicator of a set is uniformly small if the set itself has small measure,
for any `p < ∞`. Given here as an existential `∀ ε > 0, ∃ η > 0, ...` to avoid later
management of `ℝ≥0∞`-arithmetic. -/
theorem exists_snorm_indicator_le (hp : p ≠ ∞) (c : E) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ η : ℝ≥0, 0 < η ∧ ∀ s : Set α, μ s ≤ η → snorm (s.indicator fun _ => c) p μ ≤ ε := by
  rcases eq_or_ne p 0 with (rfl | h'p)
  -- ⊢ ∃ η, 0 < η ∧ ∀ (s : Set α), ↑↑μ s ≤ ↑η → snorm (Set.indicator s fun x => c)  …
  · exact ⟨1, zero_lt_one, fun s _ => by simp⟩
    -- 🎉 no goals
  have hp₀ : 0 < p := bot_lt_iff_ne_bot.2 h'p
  -- ⊢ ∃ η, 0 < η ∧ ∀ (s : Set α), ↑↑μ s ≤ ↑η → snorm (Set.indicator s fun x => c)  …
  have hp₀' : 0 ≤ 1 / p.toReal := div_nonneg zero_le_one ENNReal.toReal_nonneg
  -- ⊢ ∃ η, 0 < η ∧ ∀ (s : Set α), ↑↑μ s ≤ ↑η → snorm (Set.indicator s fun x => c)  …
  have hp₀'' : 0 < p.toReal := by
    simpa [← ENNReal.toReal_lt_toReal ENNReal.zero_ne_top hp] using hp₀
  obtain ⟨η, hη_pos, hη_le⟩ :
      ∃ η : ℝ≥0, 0 < η ∧ (‖c‖₊ : ℝ≥0∞) * (η : ℝ≥0∞) ^ (1 / p.toReal) ≤ ε := by
    have :
      Filter.Tendsto (fun x : ℝ≥0 => ((‖c‖₊ * x ^ (1 / p.toReal) : ℝ≥0) : ℝ≥0∞)) (𝓝 0)
        (𝓝 (0 : ℝ≥0)) := by
      rw [ENNReal.tendsto_coe]
      convert(NNReal.continuousAt_rpow_const (Or.inr hp₀')).tendsto.const_mul _
      simp [hp₀''.ne']
    have hε' : 0 < ε := hε.bot_lt
    obtain ⟨δ, hδ, hδε'⟩ :=
      NNReal.nhds_zero_basis.eventually_iff.mp (eventually_le_of_tendsto_lt hε' this)
    obtain ⟨η, hη, hηδ⟩ := exists_between hδ
    refine' ⟨η, hη, _⟩
    rw [ENNReal.coe_rpow_of_nonneg _ hp₀', ← ENNReal.coe_mul]
    exact hδε' hηδ
  refine' ⟨η, hη_pos, fun s hs => _⟩
  -- ⊢ snorm (Set.indicator s fun x => c) p μ ≤ ε
  refine' (snorm_indicator_const_le _ _).trans (le_trans _ hη_le)
  -- ⊢ ↑‖c‖₊ * ↑↑μ s ^ (1 / ENNReal.toReal p) ≤ ↑‖c‖₊ * ↑η ^ (1 / ENNReal.toReal p)
  exact mul_le_mul_left' (ENNReal.rpow_le_rpow hs hp₀') _
  -- 🎉 no goals
#align measure_theory.exists_snorm_indicator_le MeasureTheory.exists_snorm_indicator_le

end Indicator

section IndicatorConstLp

open Set Function

variable {s : Set α} {hs : MeasurableSet s} {hμs : μ s ≠ ∞} {c : E}

/-- Indicator of a set as an element of `Lp`. -/
def indicatorConstLp (p : ℝ≥0∞) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) : Lp E p μ :=
  Memℒp.toLp (s.indicator fun _ => c) (memℒp_indicator_const p hs c (Or.inr hμs))
#align measure_theory.indicator_const_Lp MeasureTheory.indicatorConstLp

theorem indicatorConstLp_coeFn : ⇑(indicatorConstLp p hs hμs c) =ᵐ[μ] s.indicator fun _ => c :=
  Memℒp.coeFn_toLp (memℒp_indicator_const p hs c (Or.inr hμs))
#align measure_theory.indicator_const_Lp_coe_fn MeasureTheory.indicatorConstLp_coeFn

theorem indicatorConstLp_coeFn_mem : ∀ᵐ x : α ∂μ, x ∈ s → indicatorConstLp p hs hμs c x = c :=
  indicatorConstLp_coeFn.mono fun _x hx hxs => hx.trans (Set.indicator_of_mem hxs _)
#align measure_theory.indicator_const_Lp_coe_fn_mem MeasureTheory.indicatorConstLp_coeFn_mem

theorem indicatorConstLp_coeFn_nmem : ∀ᵐ x : α ∂μ, x ∉ s → indicatorConstLp p hs hμs c x = 0 :=
  indicatorConstLp_coeFn.mono fun _x hx hxs => hx.trans (Set.indicator_of_not_mem hxs _)
#align measure_theory.indicator_const_Lp_coe_fn_nmem MeasureTheory.indicatorConstLp_coeFn_nmem

theorem norm_indicatorConstLp (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    ‖indicatorConstLp p hs hμs c‖ = ‖c‖ * (μ s).toReal ^ (1 / p.toReal) := by
  rw [Lp.norm_def, snorm_congr_ae indicatorConstLp_coeFn,
    snorm_indicator_const hs hp_ne_zero hp_ne_top, ENNReal.toReal_mul, ENNReal.toReal_rpow,
    ENNReal.coe_toReal, coe_nnnorm]
#align measure_theory.norm_indicator_const_Lp MeasureTheory.norm_indicatorConstLp

theorem norm_indicatorConstLp_top (hμs_ne_zero : μ s ≠ 0) :
    ‖indicatorConstLp ∞ hs hμs c‖ = ‖c‖ := by
  rw [Lp.norm_def, snorm_congr_ae indicatorConstLp_coeFn,
    snorm_indicator_const' hs hμs_ne_zero ENNReal.top_ne_zero, ENNReal.top_toReal, _root_.div_zero,
    ENNReal.rpow_zero, mul_one, ENNReal.coe_toReal, coe_nnnorm]
#align measure_theory.norm_indicator_const_Lp_top MeasureTheory.norm_indicatorConstLp_top

theorem norm_indicatorConstLp' (hp_pos : p ≠ 0) (hμs_pos : μ s ≠ 0) :
    ‖indicatorConstLp p hs hμs c‖ = ‖c‖ * (μ s).toReal ^ (1 / p.toReal) := by
  by_cases hp_top : p = ∞
  -- ⊢ ‖indicatorConstLp p hs hμs c‖ = ‖c‖ * ENNReal.toReal (↑↑μ s) ^ (1 / ENNReal. …
  · rw [hp_top, ENNReal.top_toReal, _root_.div_zero, Real.rpow_zero, mul_one]
    -- ⊢ ‖indicatorConstLp ⊤ hs hμs c‖ = ‖c‖
    exact norm_indicatorConstLp_top hμs_pos
    -- 🎉 no goals
  · exact norm_indicatorConstLp hp_pos hp_top
    -- 🎉 no goals
#align measure_theory.norm_indicator_const_Lp' MeasureTheory.norm_indicatorConstLp'

theorem norm_indicatorConstLp_le :
    ‖indicatorConstLp p hs hμs c‖ ≤ ‖c‖ * (μ s).toReal ^ (1 / p.toReal) := by
  rw [indicatorConstLp, Lp.norm_toLp]
  -- ⊢ ENNReal.toReal (snorm (indicator s fun x => c) p μ) ≤ ‖c‖ * ENNReal.toReal ( …
  refine toReal_le_of_le_ofReal (by positivity) ?_
  -- ⊢ snorm (indicator s fun x => c) p μ ≤ ENNReal.ofReal (‖c‖ * ENNReal.toReal (↑ …
  refine (snorm_indicator_const_le _ _).trans_eq ?_
  -- ⊢ ↑‖c‖₊ * ↑↑μ s ^ (1 / ENNReal.toReal p) = ENNReal.ofReal (‖c‖ * ENNReal.toRea …
  rw [← coe_nnnorm, ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal,
    ENNReal.toReal_rpow, ENNReal.ofReal_toReal]
  exact ENNReal.rpow_ne_top_of_nonneg (by positivity) hμs
  -- 🎉 no goals

theorem edist_indicatorConstLp_eq_nnnorm {t : Set α} (ht : MeasurableSet t) (hμt : μ t ≠ ∞) :
    edist (indicatorConstLp p hs hμs c) (indicatorConstLp p ht hμt c) =
      ‖indicatorConstLp p (hs.symmDiff ht) (measure_symmDiff_ne_top hμs hμt) c‖₊ := by
  unfold indicatorConstLp
  -- ⊢ edist (Memℒp.toLp (indicator s fun x => c) (_ : Memℒp (indicator s fun x =>  …
  rw [Lp.edist_toLp_toLp, snorm_indicator_sub_indicator, Lp.coe_nnnorm_toLp]
  -- 🎉 no goals

theorem dist_indicatorConstLp_eq_norm {t : Set α} (ht : MeasurableSet t) (hμt : μ t ≠ ∞) :
    dist (indicatorConstLp p hs hμs c) (indicatorConstLp p ht hμt c) =
      ‖indicatorConstLp p (hs.symmDiff ht) (measure_symmDiff_ne_top hμs hμt) c‖ := by
  rw [Lp.dist_edist, edist_indicatorConstLp_eq_nnnorm, ENNReal.coe_toReal, Lp.coe_nnnorm]
  -- 🎉 no goals

@[simp]
theorem indicatorConstLp_empty :
    indicatorConstLp p MeasurableSet.empty (by simp : μ ∅ ≠ ∞) c = 0 := by
                                               -- 🎉 no goals
  rw [Lp.eq_zero_iff_ae_eq_zero]
  -- ⊢ ↑↑(indicatorConstLp p (_ : MeasurableSet ∅) (_ : ↑↑μ ∅ ≠ ⊤) c) =ᵐ[μ] 0
  convert indicatorConstLp_coeFn (E := E)
  -- ⊢ 0 = indicator ∅ fun x => c
  simp [Set.indicator_empty']
  -- ⊢ 0 = fun x => 0
  rfl
  -- 🎉 no goals
#align measure_theory.indicator_const_empty MeasureTheory.indicatorConstLp_empty

theorem memℒp_add_of_disjoint {f g : α → E} (h : Disjoint (support f) (support g))
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    Memℒp (f + g) p μ ↔ Memℒp f p μ ∧ Memℒp g p μ := by
  borelize E
  -- ⊢ Memℒp (f + g) p ↔ Memℒp f p ∧ Memℒp g p
  refine' ⟨fun hfg => ⟨_, _⟩, fun h => h.1.add h.2⟩
  -- ⊢ Memℒp f p
  · rw [← Set.indicator_add_eq_left h]; exact hfg.indicator (measurableSet_support hf.measurable)
    -- ⊢ Memℒp (indicator (support f) (f + g)) p
                                        -- 🎉 no goals
  · rw [← Set.indicator_add_eq_right h]; exact hfg.indicator (measurableSet_support hg.measurable)
    -- ⊢ Memℒp (indicator (support g) (f + g)) p
                                         -- 🎉 no goals
#align measure_theory.mem_ℒp_add_of_disjoint MeasureTheory.memℒp_add_of_disjoint

/-- The indicator of a disjoint union of two sets is the sum of the indicators of the sets. -/
theorem indicatorConstLp_disjoint_union {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) (hst : s ∩ t = ∅) (c : E) :
    indicatorConstLp p (hs.union ht) (measure_union_ne_top hμs hμt) c =
      indicatorConstLp p hs hμs c + indicatorConstLp p ht hμt c := by
  ext1
  -- ⊢ ↑↑(indicatorConstLp p (_ : MeasurableSet (s ∪ t)) (_ : ↑↑μ (s ∪ t) ≠ ⊤) c) = …
  refine' indicatorConstLp_coeFn.trans (EventuallyEq.trans _ (Lp.coeFn_add _ _).symm)
  -- ⊢ (indicator (s ∪ t) fun x => c) =ᵐ[μ] ↑↑(indicatorConstLp p hs hμs c) + ↑↑(in …
  refine'
    EventuallyEq.trans _
      (EventuallyEq.add indicatorConstLp_coeFn.symm indicatorConstLp_coeFn.symm)
  rw [Set.indicator_union_of_disjoint (Set.disjoint_iff_inter_eq_empty.mpr hst) _]
  -- 🎉 no goals
#align measure_theory.indicator_const_Lp_disjoint_union MeasureTheory.indicatorConstLp_disjoint_union

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
lemma Memℒp.toLp_const : Memℒp.toLp _ (memℒp_const c) = Lp.const p μ c := rfl

@[simp]
lemma indicatorConstLp_univ :
    indicatorConstLp p .univ (measure_ne_top μ _) c = Lp.const p μ c := by
  rw [← Memℒp.toLp_const, indicatorConstLp]
  -- ⊢ Memℒp.toLp (Set.indicator Set.univ fun x => c) (_ : Memℒp (Set.indicator Set …
  simp only [Set.indicator_univ, Function.const]
  -- 🎉 no goals

theorem Lp.norm_const [NeZero μ] (hp_zero : p ≠ 0) :
    ‖Lp.const p μ c‖ = ‖c‖ * (μ Set.univ).toReal ^ (1 / p.toReal) := by
  have := NeZero.ne μ
  -- ⊢ ‖↑(Lp.const p μ) c‖ = ‖c‖ * ENNReal.toReal (↑↑μ Set.univ) ^ (1 / ENNReal.toR …
  rw [← Memℒp.toLp_const, Lp.norm_toLp, snorm_const] <;> try assumption
                                                         -- ⊢ ENNReal.toReal (↑‖c‖₊ * ↑↑μ Set.univ ^ (1 / ENNReal.toReal p)) = ‖c‖ * ENNRe …
                                                         -- 🎉 no goals
                                                         -- 🎉 no goals
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, ← ENNReal.toReal_rpow, coe_nnnorm]
  -- 🎉 no goals

theorem Lp.norm_const' (hp_zero : p ≠ 0) (hp_top : p ≠ ∞) :
    ‖Lp.const p μ c‖ = ‖c‖ * (μ Set.univ).toReal ^ (1 / p.toReal) := by
  rw [← Memℒp.toLp_const, Lp.norm_toLp, snorm_const'] <;> try assumption
                                                          -- ⊢ ENNReal.toReal (↑‖c‖₊ * ↑↑μ Set.univ ^ (1 / ENNReal.toReal p)) = ‖c‖ * ENNRe …
                                                          -- 🎉 no goals
                                                          -- 🎉 no goals
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, ← ENNReal.toReal_rpow, coe_nnnorm]
  -- 🎉 no goals

theorem Lp.norm_const_le : ‖Lp.const p μ c‖ ≤ ‖c‖ * (μ Set.univ).toReal ^ (1 / p.toReal) := by
  rw [← indicatorConstLp_univ]
  -- ⊢ ‖indicatorConstLp p (_ : MeasurableSet Set.univ) (_ : ↑↑μ Set.univ ≠ ⊤) c‖ ≤ …
  exact norm_indicatorConstLp_le
  -- 🎉 no goals

/-- `MeasureTheory.Lp.const` as a `LinearMap`. -/
@[simps] protected def Lp.constₗ (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [BoundedSMul 𝕜 E] :
    E →ₗ[𝕜] Lp E p μ where
  toFun := Lp.const p μ
  map_add' := map_add _
  map_smul' _ _ := rfl

@[simps! apply]
protected def Lp.constL (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 E] [Fact (1 ≤ p)] :
    E →L[𝕜] Lp E p μ :=
  (Lp.constₗ p μ 𝕜).mkContinuous ((μ Set.univ).toReal ^ (1 / p.toReal)) <| fun _ ↦
    (Lp.norm_const_le _ _ _).trans_eq (mul_comm _ _)

theorem Lp.norm_constL_le (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
    [Fact (1 ≤ p)] :
    ‖(Lp.constL p μ 𝕜 : E →L[𝕜] Lp E p μ)‖ ≤ (μ Set.univ).toReal ^ (1 / p.toReal) :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _
                                       -- 🎉 no goals

end const

theorem Memℒp.norm_rpow_div {f : α → E} (hf : Memℒp f p μ) (q : ℝ≥0∞) :
    Memℒp (fun x : α => ‖f x‖ ^ q.toReal) (p / q) μ := by
  refine' ⟨(hf.1.norm.aemeasurable.pow_const q.toReal).aestronglyMeasurable, _⟩
  -- ⊢ snorm (fun x => ‖f x‖ ^ ENNReal.toReal q) (p / q) μ < ⊤
  by_cases q_top : q = ∞; · simp [q_top]
  -- ⊢ snorm (fun x => ‖f x‖ ^ ENNReal.toReal q) (p / q) μ < ⊤
                            -- 🎉 no goals
  by_cases q_zero : q = 0
  -- ⊢ snorm (fun x => ‖f x‖ ^ ENNReal.toReal q) (p / q) μ < ⊤
  · simp [q_zero]
    -- ⊢ snorm (fun x => 1) (p / 0) μ < ⊤
    by_cases p_zero : p = 0
    -- ⊢ snorm (fun x => 1) (p / 0) μ < ⊤
    · simp [p_zero]
      -- 🎉 no goals
    rw [ENNReal.div_zero p_zero]
    -- ⊢ snorm (fun x => 1) ⊤ μ < ⊤
    exact (memℒp_top_const (1 : ℝ)).2
    -- 🎉 no goals
  rw [snorm_norm_rpow _ (ENNReal.toReal_pos q_zero q_top)]
  -- ⊢ snorm (fun x => f x) (p / q * ENNReal.ofReal (ENNReal.toReal q)) μ ^ ENNReal …
  apply ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg
  -- ⊢ snorm (fun x => f x) (p / q * ENNReal.ofReal (ENNReal.toReal q)) μ ≠ ⊤
  rw [ENNReal.ofReal_toReal q_top, div_eq_mul_inv, mul_assoc, ENNReal.inv_mul_cancel q_zero q_top,
    mul_one]
  exact hf.2.ne
  -- 🎉 no goals
#align measure_theory.mem_ℒp.norm_rpow_div MeasureTheory.Memℒp.norm_rpow_div

theorem memℒp_norm_rpow_iff {q : ℝ≥0∞} {f : α → E} (hf : AEStronglyMeasurable f μ) (q_zero : q ≠ 0)
    (q_top : q ≠ ∞) : Memℒp (fun x : α => ‖f x‖ ^ q.toReal) (p / q) μ ↔ Memℒp f p μ := by
  refine' ⟨fun h => _, fun h => h.norm_rpow_div q⟩
  -- ⊢ Memℒp f p
  apply (memℒp_norm_iff hf).1
  -- ⊢ Memℒp (fun x => ‖f x‖) p
  convert h.norm_rpow_div q⁻¹ using 1
  -- ⊢ (fun x => ‖f x‖) = fun x => ‖‖f x‖ ^ ENNReal.toReal q‖ ^ ENNReal.toReal q⁻¹
  · ext x
    -- ⊢ ‖f x‖ = ‖‖f x‖ ^ ENNReal.toReal q‖ ^ ENNReal.toReal q⁻¹
    rw [Real.norm_eq_abs, Real.abs_rpow_of_nonneg (norm_nonneg _), ← Real.rpow_mul (abs_nonneg _),
      ENNReal.toReal_inv, mul_inv_cancel, abs_of_nonneg (norm_nonneg _), Real.rpow_one]
    simp [ENNReal.toReal_eq_zero_iff, not_or, q_zero, q_top]
    -- 🎉 no goals
  · rw [div_eq_mul_inv, inv_inv, div_eq_mul_inv, mul_assoc, ENNReal.inv_mul_cancel q_zero q_top,
      mul_one]
#align measure_theory.mem_ℒp_norm_rpow_iff MeasureTheory.memℒp_norm_rpow_iff

theorem Memℒp.norm_rpow {f : α → E} (hf : Memℒp f p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    Memℒp (fun x : α => ‖f x‖ ^ p.toReal) 1 μ := by
  convert hf.norm_rpow_div p
  -- ⊢ 1 = p / p
  rw [div_eq_mul_inv, ENNReal.mul_inv_cancel hp_ne_zero hp_ne_top]
  -- 🎉 no goals
#align measure_theory.mem_ℒp.norm_rpow MeasureTheory.Memℒp.norm_rpow

theorem AEEqFun.compMeasurePreserving_mem_Lp {β : Type*} [MeasurableSpace β]
    {μb : MeasureTheory.Measure β} {g : β →ₘ[μb] E} (hg : g ∈ Lp E p μb) {f : α → β}
    (hf : MeasurePreserving f μ μb) :
    g.compMeasurePreserving f hf ∈ Lp E p μ := by
  rw [Lp.mem_Lp_iff_snorm_lt_top] at hg ⊢
  -- ⊢ snorm (↑(compMeasurePreserving g f hf)) p μ < ⊤
  rwa [snorm_compMeasurePreserving]
  -- 🎉 no goals

namespace Lp

/-! ### Composition with a measure preserving function -/

variable {β : Type*} [MeasurableSpace β] {μb : MeasureTheory.Measure β} {f : α → β}

/-- Composition of an `L^p` function with a measure preserving function is an `L^p` function. -/
def compMeasurePreserving (f : α → β) (hf : MeasurePreserving f μ μb) :
    Lp E p μb →+ Lp E p μ where
  toFun g := ⟨g.1.compMeasurePreserving f hf, g.1.compMeasurePreserving_mem_Lp g.2 hf⟩
  map_zero' := rfl
  map_add' := by rintro ⟨⟨_⟩, _⟩ ⟨⟨_⟩, _⟩; rfl
                 -- ⊢ ZeroHom.toFun { toFun := fun g => { val := AEEqFun.compMeasurePreserving (↑g …
                                           -- 🎉 no goals

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
  congr_arg ENNReal.toReal <| g.1.snorm_compMeasurePreserving hf

variable (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [BoundedSMul 𝕜 E]

/-- `MeasureTheory.Lp.compMeasurePreserving` as a linear map. -/
@[simps]
def compMeasurePreservingₗ (f : α → β) (hf : MeasurePreserving f μ μb) :
    Lp E p μb →ₗ[𝕜] Lp E p μ where
  __ := compMeasurePreserving f hf
  map_smul' c g := by rcases g with ⟨⟨_⟩, _⟩; rfl
                      -- ⊢ AddHom.toFun { toFun := src✝.toFun, map_add' := (_ : ∀ (x y : { x // x ∈ Lp  …
                                              -- 🎉 no goals

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

theorem LipschitzWith.comp_memℒp {α E F} {K} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedAddCommGroup F] {f : α → E} {g : E → F} (hg : LipschitzWith K g)
    (g0 : g 0 = 0) (hL : Memℒp f p μ) : Memℒp (g ∘ f) p μ :=
  haveI : ∀ x, ‖g (f x)‖ ≤ K * ‖f x‖ := by
    intro a
    -- ⊢ ‖g (f a)‖ ≤ ↑K * ‖f a‖
    -- TODO: add `LipschitzWith.nnnorm_sub_le` and `LipschitzWith.nnnorm_le`
    simpa [g0] using hg.norm_sub_le (f a) 0
    -- 🎉 no goals
  hL.of_le_mul (hg.continuous.comp_aestronglyMeasurable hL.1) (eventually_of_forall this)
#align lipschitz_with.comp_mem_ℒp LipschitzWith.comp_memℒp

theorem MeasureTheory.Memℒp.of_comp_antilipschitzWith {α E F} {K'} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup E] [NormedAddCommGroup F] {f : α → E} {g : E → F}
    (hL : Memℒp (g ∘ f) p μ) (hg : UniformContinuous g) (hg' : AntilipschitzWith K' g)
    (g0 : g 0 = 0) : Memℒp f p μ := by
  have A : ∀ x, ‖f x‖ ≤ K' * ‖g (f x)‖ := by
    intro x
    -- TODO: add `AntilipschitzWith.le_mul_nnnorm_sub` and `AntilipschitzWith.le_mul_norm`
    rw [← dist_zero_right, ← dist_zero_right, ← g0]
    apply hg'.le_mul_dist
  have B : AEStronglyMeasurable f μ :=
    (hg'.uniformEmbedding hg).embedding.aestronglyMeasurable_comp_iff.1 hL.1
  exact hL.of_le_mul B (Filter.eventually_of_forall A)
  -- 🎉 no goals
#align measure_theory.mem_ℒp.of_comp_antilipschitz_with MeasureTheory.Memℒp.of_comp_antilipschitzWith

namespace LipschitzWith

theorem memℒp_comp_iff_of_antilipschitz {α E F} {K K'} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedAddCommGroup F] {f : α → E} {g : E → F} (hg : LipschitzWith K g)
    (hg' : AntilipschitzWith K' g) (g0 : g 0 = 0) : Memℒp (g ∘ f) p μ ↔ Memℒp f p μ :=
  ⟨fun h => h.of_comp_antilipschitzWith hg.uniformContinuous hg' g0, fun h => hg.comp_memℒp g0 h⟩
#align lipschitz_with.mem_ℒp_comp_iff_of_antilipschitz LipschitzWith.memℒp_comp_iff_of_antilipschitz

/-- When `g` is a Lipschitz function sending `0` to `0` and `f` is in `Lp`, then `g ∘ f` is well
defined as an element of `Lp`. -/
def compLp (hg : LipschitzWith c g) (g0 : g 0 = 0) (f : Lp E p μ) : Lp F p μ :=
  ⟨AEEqFun.comp g hg.continuous (f : α →ₘ[μ] E), by
    suffices ∀ᵐ x ∂μ, ‖AEEqFun.comp g hg.continuous (f : α →ₘ[μ] E) x‖ ≤ c * ‖f x‖ by
      exact Lp.mem_Lp_of_ae_le_mul this
    filter_upwards [AEEqFun.coeFn_comp g hg.continuous (f : α →ₘ[μ] E)]with a ha
    -- ⊢ ‖↑(AEEqFun.comp g (_ : Continuous g) ↑f) a‖ ≤ ↑c * ‖↑↑f a‖
    simp only [ha]
    -- ⊢ ‖(g ∘ ↑↑f) a‖ ≤ ↑c * ‖↑↑f a‖
    rw [← dist_zero_right, ← dist_zero_right, ← g0]
    -- ⊢ dist ((g ∘ ↑↑f) a) (g 0) ≤ ↑c * dist (↑↑f a) 0
    exact hg.dist_le_mul (f a) 0⟩
    -- 🎉 no goals
#align lipschitz_with.comp_Lp LipschitzWith.compLp

theorem coeFn_compLp (hg : LipschitzWith c g) (g0 : g 0 = 0) (f : Lp E p μ) :
    hg.compLp g0 f =ᵐ[μ] g ∘ f :=
  AEEqFun.coeFn_comp _ hg.continuous _
#align lipschitz_with.coe_fn_comp_Lp LipschitzWith.coeFn_compLp

@[simp]
theorem compLp_zero (hg : LipschitzWith c g) (g0 : g 0 = 0) : hg.compLp g0 (0 : Lp E p μ) = 0 := by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  -- ⊢ ↑↑(compLp hg g0 0) =ᵐ[μ] 0
  apply (coeFn_compLp _ _ _).trans
  -- ⊢ g ∘ ↑↑0 =ᵐ[μ] 0
  filter_upwards [Lp.coeFn_zero E p μ] with _ ha
  -- ⊢ (g ∘ ↑↑0) a✝ = OfNat.ofNat 0 a✝
  simp only [ha, g0, Function.comp_apply, Pi.zero_apply]
  -- 🎉 no goals
#align lipschitz_with.comp_Lp_zero LipschitzWith.compLp_zero

theorem norm_compLp_sub_le (hg : LipschitzWith c g) (g0 : g 0 = 0) (f f' : Lp E p μ) :
    ‖hg.compLp g0 f - hg.compLp g0 f'‖ ≤ c * ‖f - f'‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  -- ⊢ ∀ᵐ (x : α) ∂μ, ‖↑↑(compLp hg g0 f - compLp hg g0 f') x‖ ≤ ↑c * ‖↑↑(f - f') x‖
  filter_upwards [hg.coeFn_compLp g0 f, hg.coeFn_compLp g0 f',
    Lp.coeFn_sub (hg.compLp g0 f) (hg.compLp g0 f'), Lp.coeFn_sub f f'] with a ha1 ha2 ha3 ha4
  simp only [ha1, ha2, ha3, ha4, ← dist_eq_norm, Pi.sub_apply, Function.comp_apply]
  -- ⊢ dist (g (↑↑f a)) (g (↑↑f' a)) ≤ ↑c * dist (↑↑f a) (↑↑f' a)
  exact hg.dist_le_mul (f a) (f' a)
  -- 🎉 no goals
#align lipschitz_with.norm_comp_Lp_sub_le LipschitzWith.norm_compLp_sub_le

theorem norm_compLp_le (hg : LipschitzWith c g) (g0 : g 0 = 0) (f : Lp E p μ) :
    ‖hg.compLp g0 f‖ ≤ c * ‖f‖ := by simpa using hg.norm_compLp_sub_le g0 f 0
                                     -- 🎉 no goals
#align lipschitz_with.norm_comp_Lp_le LipschitzWith.norm_compLp_le

theorem lipschitzWith_compLp [Fact (1 ≤ p)] (hg : LipschitzWith c g) (g0 : g 0 = 0) :
    LipschitzWith c (hg.compLp g0 : Lp E p μ → Lp F p μ) :=
  LipschitzWith.of_dist_le_mul fun f g => by simp [dist_eq_norm, norm_compLp_sub_le]
                                             -- 🎉 no goals
#align lipschitz_with.lipschitz_with_comp_Lp LipschitzWith.lipschitzWith_compLp

theorem continuous_compLp [Fact (1 ≤ p)] (hg : LipschitzWith c g) (g0 : g 0 = 0) :
    Continuous (hg.compLp g0 : Lp E p μ → Lp F p μ) :=
  (lipschitzWith_compLp hg g0).continuous
#align lipschitz_with.continuous_comp_Lp LipschitzWith.continuous_compLp

end LipschitzWith

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

/-- Composing `f : Lp ` with `L : E →L[𝕜] F`. -/
def compLp (L : E →L[𝕜] F) (f : Lp E p μ) : Lp F p μ :=
  L.lipschitz.compLp (map_zero L) f
#align continuous_linear_map.comp_Lp ContinuousLinearMap.compLp

theorem coeFn_compLp (L : E →L[𝕜] F) (f : Lp E p μ) : ∀ᵐ a ∂μ, (L.compLp f) a = L (f a) :=
  LipschitzWith.coeFn_compLp _ _ _
#align continuous_linear_map.coe_fn_comp_Lp ContinuousLinearMap.coeFn_compLp

theorem coeFn_compLp' (L : E →L[𝕜] F) (f : Lp E p μ) : L.compLp f =ᵐ[μ] fun a => L (f a) :=
  L.coeFn_compLp f
#align continuous_linear_map.coe_fn_comp_Lp' ContinuousLinearMap.coeFn_compLp'

theorem comp_memℒp (L : E →L[𝕜] F) (f : Lp E p μ) : Memℒp (L ∘ f) p μ :=
  (Lp.memℒp (L.compLp f)).ae_eq (L.coeFn_compLp' f)
#align continuous_linear_map.comp_mem_ℒp ContinuousLinearMap.comp_memℒp

theorem comp_memℒp' (L : E →L[𝕜] F) {f : α → E} (hf : Memℒp f p μ) : Memℒp (L ∘ f) p μ :=
  (L.comp_memℒp (hf.toLp f)).ae_eq (EventuallyEq.fun_comp hf.coeFn_toLp _)
#align continuous_linear_map.comp_mem_ℒp' ContinuousLinearMap.comp_memℒp'

section IsROrC

variable {K : Type*} [IsROrC K]

theorem _root_.MeasureTheory.Memℒp.ofReal {f : α → ℝ} (hf : Memℒp f p μ) :
    Memℒp (fun x => (f x : K)) p μ :=
  (@IsROrC.ofRealClm K _).comp_memℒp' hf
#align measure_theory.mem_ℒp.of_real MeasureTheory.Memℒp.ofReal

theorem _root_.MeasureTheory.memℒp_re_im_iff {f : α → K} :
    Memℒp (fun x => IsROrC.re (f x)) p μ ∧ Memℒp (fun x => IsROrC.im (f x)) p μ ↔ Memℒp f p μ := by
  refine' ⟨_, fun hf => ⟨hf.re, hf.im⟩⟩
  -- ⊢ Memℒp (fun x => ↑IsROrC.re (f x)) p ∧ Memℒp (fun x => ↑IsROrC.im (f x)) p →  …
  rintro ⟨hre, him⟩
  -- ⊢ Memℒp f p
  convert MeasureTheory.Memℒp.add (E := K) hre.ofReal (him.ofReal.const_mul IsROrC.I)
  -- ⊢ f = (fun x => ↑(↑IsROrC.re (f x))) + fun x => IsROrC.I * ↑(↑IsROrC.im (f x))
  · ext1 x
    -- ⊢ f x = ((fun x => ↑(↑IsROrC.re (f x))) + fun x => IsROrC.I * ↑(↑IsROrC.im (f  …
    rw [Pi.add_apply, mul_comm, IsROrC.re_add_im]
    -- 🎉 no goals
#align measure_theory.mem_ℒp_re_im_iff MeasureTheory.memℒp_re_im_iff

end IsROrC

theorem add_compLp (L L' : E →L[𝕜] F) (f : Lp E p μ) :
    (L + L').compLp f = L.compLp f + L'.compLp f := by
  ext1
  -- ⊢ ↑↑(compLp (L + L') f) =ᵐ[μ] ↑↑(compLp L f + compLp L' f)
  refine' (coeFn_compLp' (L + L') f).trans _
  -- ⊢ (fun a => ↑(L + L') (↑↑f a)) =ᵐ[μ] ↑↑(compLp L f + compLp L' f)
  refine' EventuallyEq.trans _ (Lp.coeFn_add _ _).symm
  -- ⊢ (fun a => ↑(L + L') (↑↑f a)) =ᵐ[μ] ↑↑(compLp L f) + ↑↑(compLp L' f)
  refine'
    EventuallyEq.trans _ (EventuallyEq.add (L.coeFn_compLp' f).symm (L'.coeFn_compLp' f).symm)
  refine' eventually_of_forall fun x => _
  -- ⊢ (fun a => ↑(L + L') (↑↑f a)) x = (fun x => ↑L (↑↑f x) + ↑L' (↑↑f x)) x
  rfl
  -- 🎉 no goals
#align continuous_linear_map.add_comp_Lp ContinuousLinearMap.add_compLp

theorem smul_compLp {𝕜'} [NormedRing 𝕜'] [Module 𝕜' F] [BoundedSMul 𝕜' F] [SMulCommClass 𝕜 𝕜' F]
    (c : 𝕜') (L : E →L[𝕜] F) (f : Lp E p μ) : (c • L).compLp f = c • L.compLp f := by
  ext1
  -- ⊢ ↑↑(compLp (c • L) f) =ᵐ[μ] ↑↑(c • compLp L f)
  refine' (coeFn_compLp' (c • L) f).trans _
  -- ⊢ (fun a => ↑(c • L) (↑↑f a)) =ᵐ[μ] ↑↑(c • compLp L f)
  refine' EventuallyEq.trans _ (Lp.coeFn_smul _ _).symm
  -- ⊢ (fun a => ↑(c • L) (↑↑f a)) =ᵐ[μ] c • ↑↑(compLp L f)
  refine' (L.coeFn_compLp' f).mono fun x hx => _
  -- ⊢ (fun a => ↑(c • L) (↑↑f a)) x = (c • ↑↑(compLp L f)) x
  rw [Pi.smul_apply, hx]
  -- ⊢ (fun a => ↑(c • L) (↑↑f a)) x = c • (fun a => ↑L (↑↑f a)) x
  rfl
  -- 🎉 no goals
#align continuous_linear_map.smul_comp_Lp ContinuousLinearMap.smul_compLp

theorem norm_compLp_le (L : E →L[𝕜] F) (f : Lp E p μ) : ‖L.compLp f‖ ≤ ‖L‖ * ‖f‖ :=
  LipschitzWith.norm_compLp_le _ _ _
#align continuous_linear_map.norm_comp_Lp_le ContinuousLinearMap.norm_compLp_le

variable (μ p)

/-- Composing `f : Lp E p μ` with `L : E →L[𝕜] F`, seen as a `𝕜`-linear map on `Lp E p μ`. -/
def compLpₗ (L : E →L[𝕜] F) : Lp E p μ →ₗ[𝕜] Lp F p μ where
  toFun f := L.compLp f
  map_add' := by
    intro f g
    -- ⊢ (fun f => compLp L f) (f + g) = (fun f => compLp L f) f + (fun f => compLp L …
    ext1
    -- ⊢ ↑↑((fun f => compLp L f) (f + g)) =ᵐ[μ] ↑↑((fun f => compLp L f) f + (fun f  …
    filter_upwards [Lp.coeFn_add f g, coeFn_compLp L (f + g), coeFn_compLp L f,
      coeFn_compLp L g, Lp.coeFn_add (L.compLp f) (L.compLp g)]
    intro a ha1 ha2 ha3 ha4 ha5
    -- ⊢ ↑↑(compLp L (f + g)) a = ↑↑(compLp L f + compLp L g) a
    simp only [ha1, ha2, ha3, ha4, ha5, map_add, Pi.add_apply]
    -- 🎉 no goals
  map_smul' := by
    intro c f
    -- ⊢ AddHom.toFun { toFun := fun f => compLp L f, map_add' := (_ : ∀ (f g : { x / …
    dsimp
    -- ⊢ compLp L (c • f) = c • compLp L f
    ext1
    -- ⊢ ↑↑(compLp L (c • f)) =ᵐ[μ] ↑↑(c • compLp L f)
    filter_upwards [Lp.coeFn_smul c f, coeFn_compLp L (c • f), Lp.coeFn_smul c (L.compLp f),
      coeFn_compLp L f] with _ ha1 ha2 ha3 ha4
    simp only [ha1, ha2, ha3, ha4, SMulHomClass.map_smul, Pi.smul_apply]
    -- 🎉 no goals
#align continuous_linear_map.comp_Lpₗ ContinuousLinearMap.compLpₗ

/-- Composing `f : Lp E p μ` with `L : E →L[𝕜] F`, seen as a continuous `𝕜`-linear map on
`Lp E p μ`. See also the similar
* `LinearMap.compLeft` for functions,
* `ContinuousLinearMap.compLeftContinuous` for continuous functions,
* `ContinuousLinearMap.compLeftContinuousBounded` for bounded continuous functions,
* `ContinuousLinearMap.compLeftContinuousCompact` for continuous functions on compact spaces.
-/
def compLpL [Fact (1 ≤ p)] (L : E →L[𝕜] F) : Lp E p μ →L[𝕜] Lp F p μ :=
  LinearMap.mkContinuous (L.compLpₗ p μ) ‖L‖ L.norm_compLp_le
#align continuous_linear_map.comp_LpL ContinuousLinearMap.compLpL

variable {μ p}

theorem coeFn_compLpL [Fact (1 ≤ p)] (L : E →L[𝕜] F) (f : Lp E p μ) :
    L.compLpL p μ f =ᵐ[μ] fun a => L (f a) :=
  L.coeFn_compLp f
#align continuous_linear_map.coe_fn_comp_LpL ContinuousLinearMap.coeFn_compLpL

theorem add_compLpL [Fact (1 ≤ p)] (L L' : E →L[𝕜] F) :
    (L + L').compLpL p μ = L.compLpL p μ + L'.compLpL p μ := by ext1 f; exact add_compLp L L' f
                                                                -- ⊢ ↑(compLpL p μ (L + L')) f = ↑(compLpL p μ L + compLpL p μ L') f
                                                                        -- 🎉 no goals
#align continuous_linear_map.add_comp_LpL ContinuousLinearMap.add_compLpL

set_option synthInstance.maxHeartbeats 30000 in
theorem smul_compLpL [Fact (1 ≤ p)] {𝕜'} [NormedRing 𝕜'] [Module 𝕜' F] [BoundedSMul 𝕜' F]
    [SMulCommClass 𝕜 𝕜' F] (c : 𝕜') (L : E →L[𝕜] F) : (c • L).compLpL p μ = c • L.compLpL p μ := by
  ext1 f; exact smul_compLp c L f
  -- ⊢ ↑(compLpL p μ (c • L)) f = ↑(c • compLpL p μ L) f
          -- 🎉 no goals
#align continuous_linear_map.smul_comp_LpL ContinuousLinearMap.smul_compLpL

theorem norm_compLpL_le [Fact (1 ≤ p)] (L : E →L[𝕜] F) : ‖L.compLpL p μ‖ ≤ ‖L‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
#align continuous_linear_map.norm_compLpL_le ContinuousLinearMap.norm_compLpL_le

end ContinuousLinearMap

namespace MeasureTheory

theorem indicatorConstLp_eq_toSpanSingleton_compLp {s : Set α} [NormedSpace ℝ F]
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : F) :
    indicatorConstLp 2 hs hμs x =
      (ContinuousLinearMap.toSpanSingleton ℝ x).compLp (indicatorConstLp 2 hs hμs (1 : ℝ)) := by
  ext1
  -- ⊢ ↑↑(indicatorConstLp 2 hs hμs x) =ᵐ[μ] ↑↑(ContinuousLinearMap.compLp (Continu …
  refine' indicatorConstLp_coeFn.trans _
  -- ⊢ (Set.indicator s fun x_1 => x) =ᵐ[μ] ↑↑(ContinuousLinearMap.compLp (Continuo …
  have h_compLp :=
    (ContinuousLinearMap.toSpanSingleton ℝ x).coeFn_compLp (indicatorConstLp 2 hs hμs (1 : ℝ))
  rw [← EventuallyEq] at h_compLp
  -- ⊢ (Set.indicator s fun x_1 => x) =ᵐ[μ] ↑↑(ContinuousLinearMap.compLp (Continuo …
  refine' EventuallyEq.trans _ h_compLp.symm
  -- ⊢ (Set.indicator s fun x_1 => x) =ᵐ[μ] fun a => ↑(ContinuousLinearMap.toSpanSi …
  refine' (@indicatorConstLp_coeFn _ _ _ 2 μ _ s hs hμs (1 : ℝ)).mono fun y hy => _
  -- ⊢ Set.indicator s (fun x_1 => x) y = (fun a => ↑(ContinuousLinearMap.toSpanSin …
  dsimp only
  -- ⊢ Set.indicator s (fun x_1 => x) y = ↑(ContinuousLinearMap.toSpanSingleton ℝ x …
  rw [hy]
  -- ⊢ Set.indicator s (fun x_1 => x) y = ↑(ContinuousLinearMap.toSpanSingleton ℝ x …
  simp_rw [ContinuousLinearMap.toSpanSingleton_apply]
  -- ⊢ Set.indicator s (fun x_1 => x) y = Set.indicator s (fun x => 1) y • x
  by_cases hy_mem : y ∈ s <;> simp [hy_mem, ContinuousLinearMap.lsmul_apply]
  -- ⊢ Set.indicator s (fun x_1 => x) y = Set.indicator s (fun x => 1) y • x
                              -- 🎉 no goals
                              -- 🎉 no goals
#align measure_theory.indicator_const_Lp_eq_to_span_singleton_comp_Lp MeasureTheory.indicatorConstLp_eq_toSpanSingleton_compLp

namespace Lp

section PosPart

theorem lipschitzWith_pos_part : LipschitzWith 1 fun x : ℝ => max x 0 :=
  LipschitzWith.of_dist_le_mul fun x y => by simp [Real.dist_eq, abs_max_sub_max_le_abs]
                                             -- 🎉 no goals
#align measure_theory.Lp.lipschitz_with_pos_part MeasureTheory.Lp.lipschitzWith_pos_part

theorem _root_.MeasureTheory.Memℒp.pos_part {f : α → ℝ} (hf : Memℒp f p μ) :
    Memℒp (fun x => max (f x) 0) p μ :=
  lipschitzWith_pos_part.comp_memℒp (max_eq_right le_rfl) hf
#align measure_theory.mem_ℒp.pos_part MeasureTheory.Memℒp.pos_part

theorem _root_.MeasureTheory.Memℒp.neg_part {f : α → ℝ} (hf : Memℒp f p μ) :
    Memℒp (fun x => max (-f x) 0) p μ :=
  lipschitzWith_pos_part.comp_memℒp (max_eq_right le_rfl) hf.neg
#align measure_theory.mem_ℒp.neg_part MeasureTheory.Memℒp.neg_part

/-- Positive part of a function in `L^p`. -/
def posPart (f : Lp ℝ p μ) : Lp ℝ p μ :=
  lipschitzWith_pos_part.compLp (max_eq_right le_rfl) f
#align measure_theory.Lp.pos_part MeasureTheory.Lp.posPart

/-- Negative part of a function in `L^p`. -/
def negPart (f : Lp ℝ p μ) : Lp ℝ p μ :=
  posPart (-f)
#align measure_theory.Lp.neg_part MeasureTheory.Lp.negPart

@[norm_cast]
theorem coe_posPart (f : Lp ℝ p μ) : (posPart f : α →ₘ[μ] ℝ) = (f : α →ₘ[μ] ℝ).posPart :=
  rfl
#align measure_theory.Lp.coe_pos_part MeasureTheory.Lp.coe_posPart

theorem coeFn_posPart (f : Lp ℝ p μ) : ⇑(posPart f) =ᵐ[μ] fun a => max (f a) 0 :=
  AEEqFun.coeFn_posPart _
#align measure_theory.Lp.coe_fn_pos_part MeasureTheory.Lp.coeFn_posPart

theorem coeFn_negPart_eq_max (f : Lp ℝ p μ) : ∀ᵐ a ∂μ, negPart f a = max (-f a) 0 := by
  rw [negPart]
  -- ⊢ ∀ᵐ (a : α) ∂μ, ↑↑(posPart (-f)) a = max (-↑↑f a) 0
  filter_upwards [coeFn_posPart (-f), coeFn_neg f] with _ h₁ h₂
  -- ⊢ ↑↑(posPart (-f)) a✝ = max (-↑↑f a✝) 0
  rw [h₁, h₂, Pi.neg_apply]
  -- 🎉 no goals
#align measure_theory.Lp.coe_fn_neg_part_eq_max MeasureTheory.Lp.coeFn_negPart_eq_max

theorem coeFn_negPart (f : Lp ℝ p μ) : ∀ᵐ a ∂μ, negPart f a = -min (f a) 0 :=
  (coeFn_negPart_eq_max f).mono fun a h => by rw [h, ← max_neg_neg, neg_zero]
                                              -- 🎉 no goals
#align measure_theory.Lp.coe_fn_neg_part MeasureTheory.Lp.coeFn_negPart

theorem continuous_posPart [Fact (1 ≤ p)] : Continuous fun f : Lp ℝ p μ => posPart f :=
  LipschitzWith.continuous_compLp _ _
#align measure_theory.Lp.continuous_pos_part MeasureTheory.Lp.continuous_posPart

theorem continuous_negPart [Fact (1 ≤ p)] : Continuous fun f : Lp ℝ p μ => negPart f := by
  have eq : (fun f : Lp ℝ p μ => negPart f) = fun f : Lp ℝ p μ => posPart (-f) := rfl
  -- ⊢ Continuous fun f => negPart f
  rw [eq]
  -- ⊢ Continuous fun f => posPart (-f)
  exact continuous_posPart.comp continuous_neg
  -- 🎉 no goals
#align measure_theory.Lp.continuous_neg_part MeasureTheory.Lp.continuous_negPart

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
    snorm' f_lim p μ = (∫⁻ a, atTop.liminf fun m => (‖f m a‖₊ : ℝ≥0∞) ^ p ∂μ) ^ (1 / p) := by
  suffices h_no_pow :
    (∫⁻ a, (‖f_lim a‖₊ : ℝ≥0∞) ^ p ∂μ) = ∫⁻ a, atTop.liminf fun m => (‖f m a‖₊ : ℝ≥0∞) ^ p ∂μ
  · rw [snorm', h_no_pow]
    -- 🎉 no goals
  refine' lintegral_congr_ae (h_lim.mono fun a ha => _)
  -- ⊢ (fun a => ↑‖f_lim a‖₊ ^ p) a = (fun a => liminf (fun m => ↑‖f m a‖₊ ^ p) atT …
  dsimp only
  -- ⊢ ↑‖f_lim a‖₊ ^ p = liminf (fun m => ↑‖f m a‖₊ ^ p) atTop
  rw [Tendsto.liminf_eq]
  -- ⊢ Tendsto (fun m => ↑‖f m a‖₊ ^ p) atTop (𝓝 (↑‖f_lim a‖₊ ^ p))
  simp_rw [ENNReal.coe_rpow_of_nonneg _ hp_nonneg, ENNReal.tendsto_coe]
  -- ⊢ Tendsto (fun a_1 => ‖f a_1 a‖₊ ^ p) atTop (𝓝 (‖f_lim a‖₊ ^ p))
  refine' ((NNReal.continuous_rpow_const hp_nonneg).tendsto ‖f_lim a‖₊).comp _
  -- ⊢ Tendsto (fun a_1 => ‖f a_1 a‖₊) atTop (𝓝 ‖f_lim a‖₊)
  exact (continuous_nnnorm.tendsto (f_lim a)).comp ha
  -- 🎉 no goals
#align measure_theory.Lp.snorm'_lim_eq_lintegral_liminf MeasureTheory.Lp.snorm'_lim_eq_lintegral_liminf

theorem snorm'_lim_le_liminf_snorm' {E} [NormedAddCommGroup E] {f : ℕ → α → E} {p : ℝ}
    (hp_pos : 0 < p) (hf : ∀ n, AEStronglyMeasurable (f n) μ) {f_lim : α → E}
    (h_lim : ∀ᵐ x : α ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))) :
    snorm' f_lim p μ ≤ atTop.liminf fun n => snorm' (f n) p μ := by
  rw [snorm'_lim_eq_lintegral_liminf hp_pos.le h_lim]
  -- ⊢ (∫⁻ (a : α), liminf (fun m => ↑‖f m a‖₊ ^ p) atTop ∂μ) ^ (1 / p) ≤ liminf (f …
  rw [← ENNReal.le_rpow_one_div_iff (by simp [hp_pos] : 0 < 1 / p), one_div_one_div]
  -- ⊢ ∫⁻ (a : α), liminf (fun m => ↑‖f m a‖₊ ^ p) atTop ∂μ ≤ liminf (fun n => snor …
  refine (lintegral_liminf_le' fun m => (hf m).ennnorm.pow_const _).trans_eq ?_
  -- ⊢ liminf (fun n => ∫⁻ (a : α), ↑‖f n a‖₊ ^ p ∂μ) atTop = liminf (fun n => snor …
  have h_pow_liminf :
    (atTop.liminf fun n => snorm' (f n) p μ) ^ p = atTop.liminf fun n => snorm' (f n) p μ ^ p := by
    have h_rpow_mono := ENNReal.strictMono_rpow_of_pos hp_pos
    have h_rpow_surj := (ENNReal.rpow_left_bijective hp_pos.ne.symm).2
    refine' (h_rpow_mono.orderIsoOfSurjective _ h_rpow_surj).liminf_apply _ _ _ _
    all_goals isBoundedDefault
  rw [h_pow_liminf]
  -- ⊢ liminf (fun n => ∫⁻ (a : α), ↑‖f n a‖₊ ^ p ∂μ) atTop = liminf (fun n => snor …
  simp_rw [snorm', ← ENNReal.rpow_mul, one_div, inv_mul_cancel hp_pos.ne.symm, ENNReal.rpow_one]
  -- 🎉 no goals
#align measure_theory.Lp.snorm'_lim_le_liminf_snorm' MeasureTheory.Lp.snorm'_lim_le_liminf_snorm'

theorem snorm_exponent_top_lim_eq_essSup_liminf {ι} [Nonempty ι] [LinearOrder ι] {f : ι → α → G}
    {f_lim : α → G} (h_lim : ∀ᵐ x : α ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))) :
    snorm f_lim ∞ μ = essSup (fun x => atTop.liminf fun m => (‖f m x‖₊ : ℝ≥0∞)) μ := by
  rw [snorm_exponent_top, snormEssSup]
  -- ⊢ essSup (fun x => ↑‖f_lim x‖₊) μ = essSup (fun x => liminf (fun m => ↑‖f m x‖ …
  refine' essSup_congr_ae (h_lim.mono fun x hx => _)
  -- ⊢ (fun x => ↑‖f_lim x‖₊) x = (fun x => liminf (fun m => ↑‖f m x‖₊) atTop) x
  dsimp only
  -- ⊢ ↑‖f_lim x‖₊ = liminf (fun m => ↑‖f m x‖₊) atTop
  rw [Tendsto.liminf_eq]
  -- ⊢ Tendsto (fun m => ↑‖f m x‖₊) atTop (𝓝 ↑‖f_lim x‖₊)
  rw [ENNReal.tendsto_coe]
  -- ⊢ Tendsto (fun m => ‖f m x‖₊) atTop (𝓝 ‖f_lim x‖₊)
  exact (continuous_nnnorm.tendsto (f_lim x)).comp hx
  -- 🎉 no goals
#align measure_theory.Lp.snorm_exponent_top_lim_eq_ess_sup_liminf MeasureTheory.Lp.snorm_exponent_top_lim_eq_essSup_liminf

theorem snorm_exponent_top_lim_le_liminf_snorm_exponent_top {ι} [Nonempty ι] [Countable ι]
    [LinearOrder ι] {f : ι → α → F} {f_lim : α → F}
    (h_lim : ∀ᵐ x : α ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))) :
    snorm f_lim ∞ μ ≤ atTop.liminf fun n => snorm (f n) ∞ μ := by
  rw [snorm_exponent_top_lim_eq_essSup_liminf h_lim]
  -- ⊢ essSup (fun x => liminf (fun m => ↑‖f m x‖₊) atTop) μ ≤ liminf (fun n => sno …
  simp_rw [snorm_exponent_top, snormEssSup]
  -- ⊢ essSup (fun x => liminf (fun m => ↑‖f m x‖₊) atTop) μ ≤ liminf (fun n => ess …
  exact ENNReal.essSup_liminf_le fun n => fun x => (‖f n x‖₊ : ℝ≥0∞)
  -- 🎉 no goals
#align measure_theory.Lp.snorm_exponent_top_lim_le_liminf_snorm_exponent_top MeasureTheory.Lp.snorm_exponent_top_lim_le_liminf_snorm_exponent_top

theorem snorm_lim_le_liminf_snorm {E} [NormedAddCommGroup E] {f : ℕ → α → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (f_lim : α → E)
    (h_lim : ∀ᵐ x : α ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))) :
    snorm f_lim p μ ≤ atTop.liminf fun n => snorm (f n) p μ := by
  by_cases hp0 : p = 0
  -- ⊢ snorm f_lim p μ ≤ liminf (fun n => snorm (f n) p μ) atTop
  · simp [hp0]
    -- 🎉 no goals
  rw [← Ne.def] at hp0
  -- ⊢ snorm f_lim p μ ≤ liminf (fun n => snorm (f n) p μ) atTop
  by_cases hp_top : p = ∞
  -- ⊢ snorm f_lim p μ ≤ liminf (fun n => snorm (f n) p μ) atTop
  · simp_rw [hp_top]
    -- ⊢ snorm f_lim ⊤ μ ≤ liminf (fun n => snorm (f n) ⊤ μ) atTop
    exact snorm_exponent_top_lim_le_liminf_snorm_exponent_top h_lim
    -- 🎉 no goals
  simp_rw [snorm_eq_snorm' hp0 hp_top]
  -- ⊢ snorm' f_lim (ENNReal.toReal p) μ ≤ liminf (fun n => snorm' (f n) (ENNReal.t …
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  -- ⊢ snorm' f_lim (ENNReal.toReal p) μ ≤ liminf (fun n => snorm' (f n) (ENNReal.t …
  exact snorm'_lim_le_liminf_snorm' hp_pos hf h_lim
  -- 🎉 no goals
#align measure_theory.Lp.snorm_lim_le_liminf_snorm MeasureTheory.Lp.snorm_lim_le_liminf_snorm

/-! ### `Lp` is complete iff Cauchy sequences of `ℒp` have limits in `ℒp` -/


theorem tendsto_Lp_iff_tendsto_ℒp' {ι} {fi : Filter ι} [Fact (1 ≤ p)] (f : ι → Lp E p μ)
    (f_lim : Lp E p μ) :
    fi.Tendsto f (𝓝 f_lim) ↔ fi.Tendsto (fun n => snorm (⇑(f n) - ⇑f_lim) p μ) (𝓝 0) := by
  rw [tendsto_iff_dist_tendsto_zero]
  -- ⊢ Tendsto (fun b => dist (f b) f_lim) fi (𝓝 0) ↔ Tendsto (fun n => snorm (↑↑(f …
  simp_rw [dist_def]
  -- ⊢ Tendsto (fun b => ENNReal.toReal (snorm (↑↑(f b) - ↑↑f_lim) p μ)) fi (𝓝 0) ↔ …
  rw [← ENNReal.zero_toReal, ENNReal.tendsto_toReal_iff (fun n => ?_) ENNReal.zero_ne_top]
  -- ⊢ snorm (↑↑(f n) - ↑↑f_lim) p μ ≠ ⊤
  rw [snorm_congr_ae (Lp.coeFn_sub _ _).symm]
  -- ⊢ snorm (↑↑(f n - f_lim)) p μ ≠ ⊤
  exact Lp.snorm_ne_top _
  -- 🎉 no goals
#align measure_theory.Lp.tendsto_Lp_iff_tendsto_ℒp' MeasureTheory.Lp.tendsto_Lp_iff_tendsto_ℒp'

theorem tendsto_Lp_iff_tendsto_ℒp {ι} {fi : Filter ι} [Fact (1 ≤ p)] (f : ι → Lp E p μ)
    (f_lim : α → E) (f_lim_ℒp : Memℒp f_lim p μ) :
    fi.Tendsto f (𝓝 (f_lim_ℒp.toLp f_lim)) ↔
      fi.Tendsto (fun n => snorm (⇑(f n) - f_lim) p μ) (𝓝 0) := by
  rw [tendsto_Lp_iff_tendsto_ℒp']
  -- ⊢ Tendsto (fun n => snorm (↑↑(f n) - ↑↑(Memℒp.toLp f_lim f_lim_ℒp)) p μ) fi (𝓝 …
  suffices h_eq :
    (fun n => snorm (⇑(f n) - ⇑(Memℒp.toLp f_lim f_lim_ℒp)) p μ) =
      (fun n => snorm (⇑(f n) - f_lim) p μ)
  · rw [h_eq]
    -- 🎉 no goals
  exact funext fun n => snorm_congr_ae (EventuallyEq.rfl.sub (Memℒp.coeFn_toLp f_lim_ℒp))
  -- 🎉 no goals
#align measure_theory.Lp.tendsto_Lp_iff_tendsto_ℒp MeasureTheory.Lp.tendsto_Lp_iff_tendsto_ℒp

theorem tendsto_Lp_iff_tendsto_ℒp'' {ι} {fi : Filter ι} [Fact (1 ≤ p)] (f : ι → α → E)
    (f_ℒp : ∀ n, Memℒp (f n) p μ) (f_lim : α → E) (f_lim_ℒp : Memℒp f_lim p μ) :
    fi.Tendsto (fun n => (f_ℒp n).toLp (f n)) (𝓝 (f_lim_ℒp.toLp f_lim)) ↔
      fi.Tendsto (fun n => snorm (f n - f_lim) p μ) (𝓝 0) := by
  rw [Lp.tendsto_Lp_iff_tendsto_ℒp' (fun n => (f_ℒp n).toLp (f n)) (f_lim_ℒp.toLp f_lim)]
  -- ⊢ Tendsto (fun n => snorm (↑↑(Memℒp.toLp (f n) (_ : Memℒp (f n) p)) - ↑↑(Memℒp …
  refine Filter.tendsto_congr fun n => ?_
  -- ⊢ snorm (↑↑(Memℒp.toLp (f n) (_ : Memℒp (f n) p)) - ↑↑(Memℒp.toLp f_lim f_lim_ …
  apply snorm_congr_ae
  -- ⊢ ↑↑(Memℒp.toLp (f n) (_ : Memℒp (f n) p)) - ↑↑(Memℒp.toLp f_lim f_lim_ℒp) =ᵐ[ …
  filter_upwards [((f_ℒp n).sub f_lim_ℒp).coeFn_toLp,
    Lp.coeFn_sub ((f_ℒp n).toLp (f n)) (f_lim_ℒp.toLp f_lim)] with _ hx₁ hx₂
  rw [← hx₂]
  -- ⊢ ↑↑(Memℒp.toLp (f n) (_ : Memℒp (f n) p) - Memℒp.toLp f_lim f_lim_ℒp) a✝ = (f …
  exact hx₁
  -- 🎉 no goals
#align measure_theory.Lp.tendsto_Lp_iff_tendsto_ℒp'' MeasureTheory.Lp.tendsto_Lp_iff_tendsto_ℒp''

theorem tendsto_Lp_of_tendsto_ℒp {ι} {fi : Filter ι} [Fact (1 ≤ p)] {f : ι → Lp E p μ}
    (f_lim : α → E) (f_lim_ℒp : Memℒp f_lim p μ)
    (h_tendsto : fi.Tendsto (fun n => snorm (⇑(f n) - f_lim) p μ) (𝓝 0)) :
    fi.Tendsto f (𝓝 (f_lim_ℒp.toLp f_lim)) :=
  (tendsto_Lp_iff_tendsto_ℒp f f_lim f_lim_ℒp).mpr h_tendsto
#align measure_theory.Lp.tendsto_Lp_of_tendsto_ℒp MeasureTheory.Lp.tendsto_Lp_of_tendsto_ℒp

theorem cauchySeq_Lp_iff_cauchySeq_ℒp {ι} [Nonempty ι] [SemilatticeSup ι] [hp : Fact (1 ≤ p)]
    (f : ι → Lp E p μ) :
    CauchySeq f ↔ Tendsto (fun n : ι × ι => snorm (⇑(f n.fst) - ⇑(f n.snd)) p μ) atTop (𝓝 0) := by
  simp_rw [cauchySeq_iff_tendsto_dist_atTop_0, dist_def]
  -- ⊢ Tendsto (fun n => ENNReal.toReal (snorm (↑↑(f n.fst) - ↑↑(f n.snd)) p μ)) at …
  rw [← ENNReal.zero_toReal, ENNReal.tendsto_toReal_iff (fun n => ?_) ENNReal.zero_ne_top]
  -- ⊢ snorm (↑↑(f n.fst) - ↑↑(f n.snd)) p μ ≠ ⊤
  rw [snorm_congr_ae (Lp.coeFn_sub _ _).symm]
  -- ⊢ snorm (↑↑(f n.fst - f n.snd)) p μ ≠ ⊤
  exact snorm_ne_top _
  -- 🎉 no goals
#align measure_theory.Lp.cauchy_seq_Lp_iff_cauchy_seq_ℒp MeasureTheory.Lp.cauchySeq_Lp_iff_cauchySeq_ℒp

theorem completeSpace_lp_of_cauchy_complete_ℒp [hp : Fact (1 ≤ p)]
    (H :
      ∀ (f : ℕ → α → E) (hf : ∀ n, Memℒp (f n) p μ) (B : ℕ → ℝ≥0∞) (hB : ∑' i, B i < ∞)
        (h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m → snorm (f n - f m) p μ < B N),
        ∃ (f_lim : α → E), Memℒp f_lim p μ ∧
          atTop.Tendsto (fun n => snorm (f n - f_lim) p μ) (𝓝 0)) :
    CompleteSpace (Lp E p μ) := by
  let B := fun n : ℕ => ((1 : ℝ) / 2) ^ n
  -- ⊢ CompleteSpace { x // x ∈ Lp E p }
  have hB_pos : ∀ n, 0 < B n := fun n => pow_pos (div_pos zero_lt_one zero_lt_two) n
  -- ⊢ CompleteSpace { x // x ∈ Lp E p }
  refine' Metric.complete_of_convergent_controlled_sequences B hB_pos fun f hf => _
  -- ⊢ ∃ x, Tendsto f atTop (𝓝 x)
  rsuffices ⟨f_lim, hf_lim_meas, h_tendsto⟩ :
    ∃ (f_lim : α → E), Memℒp f_lim p μ ∧
      atTop.Tendsto (fun n => snorm (⇑(f n) - f_lim) p μ) (𝓝 0)
  · exact ⟨hf_lim_meas.toLp f_lim, tendsto_Lp_of_tendsto_ℒp f_lim hf_lim_meas h_tendsto⟩
    -- 🎉 no goals
  have hB : Summable B := summable_geometric_two
  -- ⊢ ∃ f_lim, Memℒp f_lim p ∧ Tendsto (fun n => snorm (↑↑(f n) - f_lim) p μ) atTo …
  cases' hB with M hB
  -- ⊢ ∃ f_lim, Memℒp f_lim p ∧ Tendsto (fun n => snorm (↑↑(f n) - f_lim) p μ) atTo …
  let B1 n := ENNReal.ofReal (B n)
  -- ⊢ ∃ f_lim, Memℒp f_lim p ∧ Tendsto (fun n => snorm (↑↑(f n) - f_lim) p μ) atTo …
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
  -- ⊢ ∃ f_lim, Memℒp f_lim p ∧ Tendsto (fun n => snorm (↑↑(f n) - f_lim) p μ) atTo …
  refine' H f1 (fun n => Lp.memℒp (f n)) B1 hB1 fun N n m hn hm => _
  -- ⊢ snorm (f1 n - f1 m) p μ < B1 N
  specialize hf N n m hn hm
  -- ⊢ snorm (f1 n - f1 m) p μ < B1 N
  rw [dist_def] at hf
  -- ⊢ snorm (f1 n - f1 m) p μ < B1 N
  dsimp only
  -- ⊢ snorm (↑↑(f n) - ↑↑(f m)) p μ < ENNReal.ofReal ((1 / 2) ^ N)
  rwa [ENNReal.lt_ofReal_iff_toReal_lt]
  -- ⊢ snorm (↑↑(f n) - ↑↑(f m)) p μ ≠ ⊤
  rw [snorm_congr_ae (Lp.coeFn_sub _ _).symm]
  -- ⊢ snorm (↑↑(f n - f m)) p μ ≠ ⊤
  exact Lp.snorm_ne_top _
  -- 🎉 no goals
#align measure_theory.Lp.complete_space_Lp_of_cauchy_complete_ℒp MeasureTheory.Lp.completeSpace_lp_of_cauchy_complete_ℒp

/-! ### Prove that controlled Cauchy sequences of `ℒp` have limits in `ℒp` -/


private theorem snorm'_sum_norm_sub_le_tsum_of_cauchy_snorm' {f : ℕ → α → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) {p : ℝ} (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞}
    (h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m → snorm' (f n - f m) p μ < B N) (n : ℕ) :
    snorm' (fun x => ∑ i in Finset.range (n + 1), ‖f (i + 1) x - f i x‖) p μ ≤ ∑' i, B i := by
  let f_norm_diff i x := ‖f (i + 1) x - f i x‖
  -- ⊢ snorm' (fun x => ∑ i in Finset.range (n + 1), ‖f (i + 1) x - f i x‖) p μ ≤ ∑ …
  have hgf_norm_diff :
    ∀ n,
      (fun x => ∑ i in Finset.range (n + 1), ‖f (i + 1) x - f i x‖) =
        ∑ i in Finset.range (n + 1), f_norm_diff i :=
    fun n => funext fun x => by simp
  rw [hgf_norm_diff]
  -- ⊢ snorm' (∑ i in Finset.range (n + 1), f_norm_diff i) p μ ≤ ∑' (i : ℕ), B i
  refine' (snorm'_sum_le (fun i _ => ((hf (i + 1)).sub (hf i)).norm) hp1).trans _
  -- ⊢ ∑ i in Finset.range (n + 1), snorm' (fun x => ‖(f (i + 1) - f i) x‖) p μ ≤ ∑ …
  simp_rw [snorm'_norm]
  -- ⊢ ∑ x in Finset.range (n + 1), snorm' (fun a => (f (x + 1) - f x) a) p μ ≤ ∑'  …
  refine' (Finset.sum_le_sum _).trans (sum_le_tsum _ (fun m _ => zero_le _) ENNReal.summable)
  -- ⊢ ∀ (i : ℕ), i ∈ Finset.range (n + 1) → snorm' (fun a => (f (i + 1) - f i) a)  …
  exact fun m _ => (h_cau m (m + 1) m (Nat.le_succ m) (le_refl m)).le
  -- 🎉 no goals

private theorem lintegral_rpow_sum_coe_nnnorm_sub_le_rpow_tsum
    {f : ℕ → α → E} {p : ℝ} (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞} (n : ℕ)
    (hn : snorm' (fun x => ∑ i in Finset.range (n + 1), ‖f (i + 1) x - f i x‖) p μ ≤ ∑' i, B i) :
    (∫⁻ a, (∑ i in Finset.range (n + 1), ‖f (i + 1) a - f i a‖₊ : ℝ≥0∞) ^ p ∂μ) ≤
      (∑' i, B i) ^ p := by
  have hp_pos : 0 < p := zero_lt_one.trans_le hp1
  -- ⊢ ∫⁻ (a : α), (∑ i in Finset.range (n + 1), ↑‖f (i + 1) a - f i a‖₊) ^ p ∂μ ≤  …
  rw [← one_div_one_div p, @ENNReal.le_rpow_one_div_iff _ _ (1 / p) (by simp [hp_pos]),
    one_div_one_div p]
  simp_rw [snorm'] at hn
  -- ⊢ (∫⁻ (a : α), (∑ i in Finset.range (n + 1), ↑‖f (i + 1) a - f i a‖₊) ^ p ∂μ)  …
  have h_nnnorm_nonneg :
    (fun a => (‖∑ i in Finset.range (n + 1), ‖f (i + 1) a - f i a‖‖₊ : ℝ≥0∞) ^ p) = fun a =>
      (∑ i in Finset.range (n + 1), (‖f (i + 1) a - f i a‖₊ : ℝ≥0∞)) ^ p := by
    ext1 a
    congr
    simp_rw [← ofReal_norm_eq_coe_nnnorm]
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · rw [Real.norm_of_nonneg _]
      exact Finset.sum_nonneg fun x _ => norm_nonneg _
    · exact fun x _ => norm_nonneg _
  change
    (∫⁻ a, (fun x => ↑‖∑ i in Finset.range (n + 1), ‖f (i + 1) x - f i x‖‖₊ ^ p) a ∂μ) ^ (1 / p) ≤
      ∑' i, B i at hn
  rwa [h_nnnorm_nonneg] at hn
  -- 🎉 no goals

private theorem lintegral_rpow_tsum_coe_nnnorm_sub_le_tsum {f : ℕ → α → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) {p : ℝ} (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞}
    (h :
      ∀ n,
        (∫⁻ a, (∑ i in Finset.range (n + 1), ‖f (i + 1) a - f i a‖₊ : ℝ≥0∞) ^ p ∂μ) ≤
          (∑' i, B i) ^ p) :
    (∫⁻ a, (∑' i, ‖f (i + 1) a - f i a‖₊ : ℝ≥0∞) ^ p ∂μ) ^ (1 / p) ≤ ∑' i, B i := by
  have hp_pos : 0 < p := zero_lt_one.trans_le hp1
  -- ⊢ (∫⁻ (a : α), (∑' (i : ℕ), ↑‖f (i + 1) a - f i a‖₊) ^ p ∂μ) ^ (1 / p) ≤ ∑' (i …
  suffices h_pow : (∫⁻ a, (∑' i, ‖f (i + 1) a - f i a‖₊ : ℝ≥0∞) ^ p ∂μ) ≤ (∑' i, B i) ^ p
  -- ⊢ (∫⁻ (a : α), (∑' (i : ℕ), ↑‖f (i + 1) a - f i a‖₊) ^ p ∂μ) ^ (1 / p) ≤ ∑' (i …
  · rwa [← ENNReal.le_rpow_one_div_iff (by simp [hp_pos] : 0 < 1 / p), one_div_one_div]
    -- 🎉 no goals
  have h_tsum_1 :
    ∀ g : ℕ → ℝ≥0∞, ∑' i, g i = atTop.liminf fun n => ∑ i in Finset.range (n + 1), g i := by
    intro g
    rw [ENNReal.tsum_eq_liminf_sum_nat, ← liminf_nat_add _ 1]
  simp_rw [h_tsum_1 _]
  -- ⊢ ∫⁻ (a : α), liminf (fun n => ∑ i in Finset.range (n + 1), ↑‖f (i + 1) a - f  …
  rw [← h_tsum_1]
  -- ⊢ ∫⁻ (a : α), liminf (fun n => ∑ i in Finset.range (n + 1), ↑‖f (i + 1) a - f  …
  have h_liminf_pow :
    (∫⁻ a, (atTop.liminf
      fun n => ∑ i in Finset.range (n + 1), (‖f (i + 1) a - f i a‖₊ : ℝ≥0∞)) ^ p ∂μ) =
      ∫⁻ a, atTop.liminf
        fun n => (∑ i in Finset.range (n + 1), (‖f (i + 1) a - f i a‖₊ : ℝ≥0∞)) ^ p ∂μ := by
    refine' lintegral_congr fun x => _
    have h_rpow_mono := ENNReal.strictMono_rpow_of_pos (zero_lt_one.trans_le hp1)
    have h_rpow_surj := (ENNReal.rpow_left_bijective hp_pos.ne.symm).2
    refine' (h_rpow_mono.orderIsoOfSurjective _ h_rpow_surj).liminf_apply _ _ _ _
    all_goals isBoundedDefault
  rw [h_liminf_pow]
  -- ⊢ ∫⁻ (a : α), liminf (fun n => (∑ i in Finset.range (n + 1), ↑‖f (i + 1) a - f …
  refine' (lintegral_liminf_le' _).trans _
  -- ⊢ ∀ (n : ℕ), AEMeasurable fun a => (∑ i in Finset.range (n + 1), ↑‖f (i + 1) a …
  · exact fun n =>
      (Finset.aemeasurable_sum (Finset.range (n + 1)) fun i _ =>
            ((hf (i + 1)).sub (hf i)).ennnorm).pow_const
        _
  · exact liminf_le_of_frequently_le' (frequently_of_forall h)
    -- 🎉 no goals

private theorem tsum_nnnorm_sub_ae_lt_top {f : ℕ → α → E} (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    {p : ℝ} (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞} (hB : ∑' i, B i ≠ ∞)
    (h : (∫⁻ a, (∑' i, ‖f (i + 1) a - f i a‖₊ : ℝ≥0∞) ^ p ∂μ) ^ (1 / p) ≤ ∑' i, B i) :
    ∀ᵐ x ∂μ, (∑' i, ‖f (i + 1) x - f i x‖₊ : ℝ≥0∞) < ∞ := by
  have hp_pos : 0 < p := zero_lt_one.trans_le hp1
  -- ⊢ ∀ᵐ (x : α) ∂μ, ∑' (i : ℕ), ↑‖f (i + 1) x - f i x‖₊ < ⊤
  have h_integral : (∫⁻ a, (∑' i, ‖f (i + 1) a - f i a‖₊ : ℝ≥0∞) ^ p ∂μ) < ∞ := by
    have h_tsum_lt_top : (∑' i, B i) ^ p < ∞ := ENNReal.rpow_lt_top_of_nonneg hp_pos.le hB
    refine' lt_of_le_of_lt _ h_tsum_lt_top
    rwa [← ENNReal.le_rpow_one_div_iff (by simp [hp_pos] : 0 < 1 / p), one_div_one_div] at h
  have rpow_ae_lt_top : ∀ᵐ x ∂μ, (∑' i, ‖f (i + 1) x - f i x‖₊ : ℝ≥0∞) ^ p < ∞ := by
    refine' ae_lt_top' (AEMeasurable.pow_const _ _) h_integral.ne
    exact AEMeasurable.ennreal_tsum fun n => ((hf (n + 1)).sub (hf n)).ennnorm
  refine' rpow_ae_lt_top.mono fun x hx => _
  -- ⊢ ∑' (i : ℕ), ↑‖f (i + 1) x - f i x‖₊ < ⊤
  rwa [← ENNReal.lt_rpow_one_div_iff hp_pos,
    ENNReal.top_rpow_of_pos (by simp [hp_pos] : 0 < 1 / p)] at hx

theorem ae_tendsto_of_cauchy_snorm' [CompleteSpace E] {f : ℕ → α → E} {p : ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞} (hB : ∑' i, B i ≠ ∞)
    (h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m → snorm' (f n - f m) p μ < B N) :
    ∀ᵐ x ∂μ, ∃ l : E, atTop.Tendsto (fun n => f n x) (𝓝 l) := by
  have h_summable : ∀ᵐ x ∂μ, Summable fun i : ℕ => f (i + 1) x - f i x := by
    have h1 :
      ∀ n, snorm' (fun x => ∑ i in Finset.range (n + 1), ‖f (i + 1) x - f i x‖) p μ ≤ ∑' i, B i :=
      snorm'_sum_norm_sub_le_tsum_of_cauchy_snorm' hf hp1 h_cau
    have h2 :
      ∀ n,
        (∫⁻ a, (∑ i in Finset.range (n + 1), ‖f (i + 1) a - f i a‖₊ : ℝ≥0∞) ^ p ∂μ) ≤
          (∑' i, B i) ^ p :=
      fun n => lintegral_rpow_sum_coe_nnnorm_sub_le_rpow_tsum hp1 n (h1 n)
    have h3 : (∫⁻ a, (∑' i, ‖f (i + 1) a - f i a‖₊ : ℝ≥0∞) ^ p ∂μ) ^ (1 / p) ≤ ∑' i, B i :=
      lintegral_rpow_tsum_coe_nnnorm_sub_le_tsum hf hp1 h2
    have h4 : ∀ᵐ x ∂μ, (∑' i, ‖f (i + 1) x - f i x‖₊ : ℝ≥0∞) < ∞ :=
      tsum_nnnorm_sub_ae_lt_top hf hp1 hB h3
    exact
      h4.mono fun x hx =>
        summable_of_summable_nnnorm
          (ENNReal.tsum_coe_ne_top_iff_summable.mp (lt_top_iff_ne_top.mp hx))
  have h :
    ∀ᵐ x ∂μ, ∃ l : E,
      atTop.Tendsto (fun n => ∑ i in Finset.range n, (f (i + 1) x - f i x)) (𝓝 l) := by
    refine' h_summable.mono fun x hx => _
    let hx_sum := hx.hasSum.tendsto_sum_nat
    exact ⟨∑' i, (f (i + 1) x - f i x), hx_sum⟩
  refine' h.mono fun x hx => _
  -- ⊢ ∃ l, Tendsto (fun n => f n x) atTop (𝓝 l)
  cases' hx with l hx
  -- ⊢ ∃ l, Tendsto (fun n => f n x) atTop (𝓝 l)
  have h_rw_sum :
      (fun n => ∑ i in Finset.range n, (f (i + 1) x - f i x)) = fun n => f n x - f 0 x := by
    ext1 n
    change
      (∑ i : ℕ in Finset.range n, ((fun m => f m x) (i + 1) - (fun m => f m x) i)) = f n x - f 0 x
    rw [Finset.sum_range_sub (fun m => f m x)]
  rw [h_rw_sum] at hx
  -- ⊢ ∃ l, Tendsto (fun n => f n x) atTop (𝓝 l)
  have hf_rw : (fun n => f n x) = fun n => f n x - f 0 x + f 0 x := by
    ext1 n
    abel
  rw [hf_rw]
  -- ⊢ ∃ l, Tendsto (fun n => f n x - f 0 x + f 0 x) atTop (𝓝 l)
  exact ⟨l + f 0 x, Tendsto.add_const _ hx⟩
  -- 🎉 no goals
#align measure_theory.Lp.ae_tendsto_of_cauchy_snorm' MeasureTheory.Lp.ae_tendsto_of_cauchy_snorm'

theorem ae_tendsto_of_cauchy_snorm [CompleteSpace E] {f : ℕ → α → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hp : 1 ≤ p) {B : ℕ → ℝ≥0∞} (hB : ∑' i, B i ≠ ∞)
    (h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m → snorm (f n - f m) p μ < B N) :
    ∀ᵐ x ∂μ, ∃ l : E, atTop.Tendsto (fun n => f n x) (𝓝 l) := by
  by_cases hp_top : p = ∞
  -- ⊢ ∀ᵐ (x : α) ∂μ, ∃ l, Tendsto (fun n => f n x) atTop (𝓝 l)
  · simp_rw [hp_top] at *
    -- ⊢ ∀ᵐ (x : α) ∂μ, ∃ l, Tendsto (fun n => f n x) atTop (𝓝 l)
    have h_cau_ae : ∀ᵐ x ∂μ, ∀ N n m, N ≤ n → N ≤ m → (‖(f n - f m) x‖₊ : ℝ≥0∞) < B N := by
      simp_rw [ae_all_iff]
      exact fun N n m hnN hmN => ae_lt_of_essSup_lt (h_cau N n m hnN hmN)
    simp_rw [snorm_exponent_top, snormEssSup] at h_cau
    -- ⊢ ∀ᵐ (x : α) ∂μ, ∃ l, Tendsto (fun n => f n x) atTop (𝓝 l)
    refine' h_cau_ae.mono fun x hx => cauchySeq_tendsto_of_complete _
    -- ⊢ CauchySeq fun n => f n x
    refine' cauchySeq_of_le_tendsto_0 (fun n => (B n).toReal) _ _
    -- ⊢ ∀ (n m N : ℕ), N ≤ n → N ≤ m → dist (f n x) (f m x) ≤ (fun n => ENNReal.toRe …
    · intro n m N hnN hmN
      -- ⊢ dist (f n x) (f m x) ≤ (fun n => ENNReal.toReal (B n)) N
      specialize hx N n m hnN hmN
      -- ⊢ dist (f n x) (f m x) ≤ (fun n => ENNReal.toReal (B n)) N
      rw [dist_eq_norm, ← ENNReal.toReal_ofReal (norm_nonneg _),
        ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (ENNReal.ne_top_of_tsum_ne_top hB N)]
      rw [← ofReal_norm_eq_coe_nnnorm] at hx
      -- ⊢ ENNReal.ofReal ‖f n x - f m x‖ ≤ B N
      exact hx.le
      -- 🎉 no goals
    · rw [← ENNReal.zero_toReal]
      -- ⊢ Tendsto (fun n => ENNReal.toReal (B n)) atTop (𝓝 (ENNReal.toReal 0))
      exact
        Tendsto.comp (g := ENNReal.toReal) (ENNReal.tendsto_toReal ENNReal.zero_ne_top)
          (ENNReal.tendsto_atTop_zero_of_tsum_ne_top hB)
  have hp1 : 1 ≤ p.toReal := by
    rw [← ENNReal.ofReal_le_iff_le_toReal hp_top, ENNReal.ofReal_one]
    exact hp
  have h_cau' : ∀ N n m : ℕ, N ≤ n → N ≤ m → snorm' (f n - f m) p.toReal μ < B N := by
    intro N n m hn hm
    specialize h_cau N n m hn hm
    rwa [snorm_eq_snorm' (zero_lt_one.trans_le hp).ne.symm hp_top] at h_cau
  exact ae_tendsto_of_cauchy_snorm' hf hp1 hB h_cau'
  -- 🎉 no goals
#align measure_theory.Lp.ae_tendsto_of_cauchy_snorm MeasureTheory.Lp.ae_tendsto_of_cauchy_snorm

theorem cauchy_tendsto_of_tendsto {f : ℕ → α → E} (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (f_lim : α → E) {B : ℕ → ℝ≥0∞} (hB : ∑' i, B i ≠ ∞)
    (h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m → snorm (f n - f m) p μ < B N)
    (h_lim : ∀ᵐ x : α ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))) :
    atTop.Tendsto (fun n => snorm (f n - f_lim) p μ) (𝓝 0) := by
  rw [ENNReal.tendsto_atTop_zero]
  -- ⊢ ∀ (ε : ℝ≥0∞), ε > 0 → ∃ N, ∀ (n : ℕ), n ≥ N → snorm (f n - f_lim) p μ ≤ ε
  intro ε hε
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → snorm (f n - f_lim) p μ ≤ ε
  have h_B : ∃ N : ℕ, B N ≤ ε := by
    suffices h_tendsto_zero : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → B n ≤ ε
    exact ⟨h_tendsto_zero.choose, h_tendsto_zero.choose_spec _ le_rfl⟩
    exact (ENNReal.tendsto_atTop_zero.mp (ENNReal.tendsto_atTop_zero_of_tsum_ne_top hB)) ε hε
  cases' h_B with N h_B
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → snorm (f n - f_lim) p μ ≤ ε
  refine' ⟨N, fun n hn => _⟩
  -- ⊢ snorm (f n - f_lim) p μ ≤ ε
  have h_sub : snorm (f n - f_lim) p μ ≤ atTop.liminf fun m => snorm (f n - f m) p μ := by
    refine' snorm_lim_le_liminf_snorm (fun m => (hf n).sub (hf m)) (f n - f_lim) _
    refine' h_lim.mono fun x hx => _
    simp_rw [sub_eq_add_neg]
    exact Tendsto.add tendsto_const_nhds (Tendsto.neg hx)
  refine' h_sub.trans _
  -- ⊢ liminf (fun m => snorm (f n - f m) p μ) atTop ≤ ε
  refine' liminf_le_of_frequently_le' (frequently_atTop.mpr _)
  -- ⊢ ∀ (a : ℕ), ∃ b, b ≥ a ∧ snorm (f n - f b) p μ ≤ ε
  refine' fun N1 => ⟨max N N1, le_max_right _ _, _⟩
  -- ⊢ snorm (f n - f (max N N1)) p μ ≤ ε
  exact (h_cau N n (max N N1) hn (le_max_left _ _)).le.trans h_B
  -- 🎉 no goals
#align measure_theory.Lp.cauchy_tendsto_of_tendsto MeasureTheory.Lp.cauchy_tendsto_of_tendsto

theorem memℒp_of_cauchy_tendsto (hp : 1 ≤ p) {f : ℕ → α → E} (hf : ∀ n, Memℒp (f n) p μ)
    (f_lim : α → E) (h_lim_meas : AEStronglyMeasurable f_lim μ)
    (h_tendsto : atTop.Tendsto (fun n => snorm (f n - f_lim) p μ) (𝓝 0)) : Memℒp f_lim p μ := by
  refine' ⟨h_lim_meas, _⟩
  -- ⊢ snorm f_lim p μ < ⊤
  rw [ENNReal.tendsto_atTop_zero] at h_tendsto
  -- ⊢ snorm f_lim p μ < ⊤
  cases' h_tendsto 1 zero_lt_one with N h_tendsto_1
  -- ⊢ snorm f_lim p μ < ⊤
  specialize h_tendsto_1 N (le_refl N)
  -- ⊢ snorm f_lim p μ < ⊤
  have h_add : f_lim = f_lim - f N + f N := by abel
  -- ⊢ snorm f_lim p μ < ⊤
  rw [h_add]
  -- ⊢ snorm (f_lim - f N + f N) p μ < ⊤
  refine' lt_of_le_of_lt (snorm_add_le (h_lim_meas.sub (hf N).1) (hf N).1 hp) _
  -- ⊢ snorm (f_lim - f N) p μ + snorm (f N) p μ < ⊤
  rw [ENNReal.add_lt_top]
  -- ⊢ snorm (f_lim - f N) p μ < ⊤ ∧ snorm (f N) p μ < ⊤
  constructor
  -- ⊢ snorm (f_lim - f N) p μ < ⊤
  · refine' lt_of_le_of_lt _ ENNReal.one_lt_top
    -- ⊢ snorm (f_lim - f N) p μ ≤ 1
    have h_neg : f_lim - f N = -(f N - f_lim) := by simp
    -- ⊢ snorm (f_lim - f N) p μ ≤ 1
    rwa [h_neg, snorm_neg]
    -- 🎉 no goals
  · exact (hf N).2
    -- 🎉 no goals
#align measure_theory.Lp.mem_ℒp_of_cauchy_tendsto MeasureTheory.Lp.memℒp_of_cauchy_tendsto

theorem cauchy_complete_ℒp [CompleteSpace E] (hp : 1 ≤ p) {f : ℕ → α → E}
    (hf : ∀ n, Memℒp (f n) p μ) {B : ℕ → ℝ≥0∞} (hB : ∑' i, B i ≠ ∞)
    (h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m → snorm (f n - f m) p μ < B N) :
    ∃ (f_lim : α → E), Memℒp f_lim p μ ∧
      atTop.Tendsto (fun n => snorm (f n - f_lim) p μ) (𝓝 0) := by
  obtain ⟨f_lim, h_f_lim_meas, h_lim⟩ :
    ∃ (f_lim : α → E) (_ : StronglyMeasurable f_lim),
      ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (nhds (f_lim x))
  exact
    exists_stronglyMeasurable_limit_of_tendsto_ae (fun n => (hf n).1)
      (ae_tendsto_of_cauchy_snorm (fun n => (hf n).1) hp hB h_cau)
  have h_tendsto' : atTop.Tendsto (fun n => snorm (f n - f_lim) p μ) (𝓝 0) :=
    cauchy_tendsto_of_tendsto (fun m => (hf m).1) f_lim hB h_cau h_lim
  have h_ℒp_lim : Memℒp f_lim p μ :=
    memℒp_of_cauchy_tendsto hp hf f_lim h_f_lim_meas.aestronglyMeasurable h_tendsto'
  exact ⟨f_lim, h_ℒp_lim, h_tendsto'⟩
  -- 🎉 no goals
#align measure_theory.Lp.cauchy_complete_ℒp MeasureTheory.Lp.cauchy_complete_ℒp

/-! ### `Lp` is complete for `1 ≤ p` -/

instance instCompleteSpace [CompleteSpace E] [hp : Fact (1 ≤ p)] : CompleteSpace (Lp E p μ) :=
  completeSpace_lp_of_cauchy_complete_ℒp fun _f hf _B hB h_cau =>
    cauchy_complete_ℒp hp.elim hf hB.ne h_cau
#align measure_theory.Lp.complete_space MeasureTheory.Lp.instCompleteSpace

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
def MeasureTheory.Lp.boundedContinuousFunction : AddSubgroup (Lp E p μ) :=
  AddSubgroup.addSubgroupOf
    ((ContinuousMap.toAEEqFunAddHom μ).comp (toContinuousMapAddHom α E)).range (Lp E p μ)
#align measure_theory.Lp.bounded_continuous_function MeasureTheory.Lp.boundedContinuousFunction

variable {E p μ}

/-- By definition, the elements of `Lp.boundedContinuousFunction E p μ` are the elements of
`Lp E p μ` which contain a bounded continuous representative. -/
theorem MeasureTheory.Lp.mem_boundedContinuousFunction_iff {f : Lp E p μ} :
    f ∈ MeasureTheory.Lp.boundedContinuousFunction E p μ ↔
      ∃ f₀ : α →ᵇ E, f₀.toContinuousMap.toAEEqFun μ = (f : α →ₘ[μ] E) :=
  AddSubgroup.mem_addSubgroupOf
#align measure_theory.Lp.mem_bounded_continuous_function_iff MeasureTheory.Lp.mem_boundedContinuousFunction_iff

namespace BoundedContinuousFunction

variable [IsFiniteMeasure μ]

/-- A bounded continuous function on a finite-measure space is in `Lp`. -/
theorem mem_Lp (f : α →ᵇ E) : f.toContinuousMap.toAEEqFun μ ∈ Lp E p μ := by
  refine' Lp.mem_Lp_of_ae_bound ‖f‖ _
  -- ⊢ ∀ᵐ (x : α) ∂μ, ‖↑(ContinuousMap.toAEEqFun μ f.toContinuousMap) x‖ ≤ ‖f‖
  filter_upwards [f.toContinuousMap.coeFn_toAEEqFun μ] with x _
  -- ⊢ ‖↑(ContinuousMap.toAEEqFun μ f.toContinuousMap) x‖ ≤ ‖f‖
  convert f.norm_coe_le_norm x using 2
  -- 🎉 no goals
#align bounded_continuous_function.mem_Lp BoundedContinuousFunction.mem_Lp

/-- The `Lp`-norm of a bounded continuous function is at most a constant (depending on the measure
of the whole space) times its sup-norm. -/
theorem Lp_nnnorm_le (f : α →ᵇ E) :
    ‖(⟨f.toContinuousMap.toAEEqFun μ, mem_Lp f⟩ : Lp E p μ)‖₊ ≤
      measureUnivNNReal μ ^ p.toReal⁻¹ * ‖f‖₊ := by
  apply Lp.nnnorm_le_of_ae_bound
  -- ⊢ ∀ᵐ (x : α) ∂μ, ‖↑↑{ val := ContinuousMap.toAEEqFun μ f.toContinuousMap, prop …
  refine' (f.toContinuousMap.coeFn_toAEEqFun μ).mono _
  -- ⊢ ∀ (x : α), ↑(ContinuousMap.toAEEqFun μ f.toContinuousMap) x = ↑f.toContinuou …
  intro x hx
  -- ⊢ ‖↑↑{ val := ContinuousMap.toAEEqFun μ f.toContinuousMap, property := (_ : Co …
  rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
  -- ⊢ ‖↑↑{ val := ContinuousMap.toAEEqFun μ f.toContinuousMap, property := (_ : Co …
  convert f.norm_coe_le_norm x using 2
  -- 🎉 no goals
#align bounded_continuous_function.Lp_nnnorm_le BoundedContinuousFunction.Lp_nnnorm_le

/-- The `Lp`-norm of a bounded continuous function is at most a constant (depending on the measure
of the whole space) times its sup-norm. -/
theorem Lp_norm_le (f : α →ᵇ E) :
    ‖(⟨f.toContinuousMap.toAEEqFun μ, mem_Lp f⟩ : Lp E p μ)‖ ≤
      measureUnivNNReal μ ^ p.toReal⁻¹ * ‖f‖ :=
  Lp_nnnorm_le f
#align bounded_continuous_function.Lp_norm_le BoundedContinuousFunction.Lp_norm_le

variable (p μ)

/-- The normed group homomorphism of considering a bounded continuous function on a finite-measure
space as an element of `Lp`. -/
def toLpHom [Fact (1 ≤ p)] : NormedAddGroupHom (α →ᵇ E) (Lp E p μ) :=
  { AddMonoidHom.codRestrict ((ContinuousMap.toAEEqFunAddHom μ).comp (toContinuousMapAddHom α E))
      (Lp E p μ) mem_Lp with
    bound' := ⟨_, Lp_norm_le⟩ }
#align bounded_continuous_function.to_Lp_hom BoundedContinuousFunction.toLpHom

theorem range_toLpHom [Fact (1 ≤ p)] :
    ((toLpHom p μ).range : AddSubgroup (Lp E p μ)) =
      MeasureTheory.Lp.boundedContinuousFunction E p μ := by
  symm
  -- ⊢ Lp.boundedContinuousFunction E p μ = NormedAddGroupHom.range (toLpHom p μ)
  convert AddMonoidHom.addSubgroupOf_range_eq_of_le
      ((ContinuousMap.toAEEqFunAddHom μ).comp (toContinuousMapAddHom α E))
      (by rintro - ⟨f, rfl⟩; exact mem_Lp f : _ ≤ Lp E p μ)
#align bounded_continuous_function.range_to_Lp_hom BoundedContinuousFunction.range_toLpHom

variable (𝕜 : Type*) [Fact (1 ≤ p)]

/-- The bounded linear map of considering a bounded continuous function on a finite-measure space
as an element of `Lp`. -/
def toLp [NormedField 𝕜] [NormedSpace 𝕜 E] : (α →ᵇ E) →L[𝕜] Lp E p μ :=
  LinearMap.mkContinuous
    (LinearMap.codRestrict (Lp.LpSubmodule E p μ 𝕜)
      ((ContinuousMap.toAEEqFunLinearMap μ).comp (toContinuousMapLinearMap α E 𝕜)) mem_Lp)
    _ Lp_norm_le
#align bounded_continuous_function.to_Lp BoundedContinuousFunction.toLp

theorem coeFn_toLp [NormedField 𝕜] [NormedSpace 𝕜 E] (f : α →ᵇ E) :
    toLp (E := E) p μ 𝕜 f =ᵐ[μ] f :=
  AEEqFun.coeFn_mk f _
#align bounded_continuous_function.coe_fn_to_Lp BoundedContinuousFunction.coeFn_toLp

variable {𝕜}

theorem range_toLp [NormedField 𝕜] [NormedSpace 𝕜 E] :
    (LinearMap.range (toLp p μ 𝕜 : (α →ᵇ E) →L[𝕜] Lp E p μ)).toAddSubgroup =
      MeasureTheory.Lp.boundedContinuousFunction E p μ :=
  range_toLpHom p μ
#align bounded_continuous_function.range_to_Lp BoundedContinuousFunction.range_toLp

variable {p}

theorem toLp_norm_le [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] :
    ‖(toLp p μ 𝕜 : (α →ᵇ E) →L[𝕜] Lp E p μ)‖ ≤ measureUnivNNReal μ ^ p.toReal⁻¹ :=
  LinearMap.mkContinuous_norm_le _ (measureUnivNNReal μ ^ p.toReal⁻¹).coe_nonneg _
#align bounded_continuous_function.to_Lp_norm_le BoundedContinuousFunction.toLp_norm_le

theorem toLp_inj {f g : α →ᵇ E} [μ.IsOpenPosMeasure] [NormedField 𝕜] [NormedSpace 𝕜 E] :
    toLp (E := E) p μ 𝕜 f = toLp (E := E) p μ 𝕜 g ↔ f = g := by
  refine' ⟨fun h => _, by tauto⟩
  -- ⊢ f = g
  rw [← FunLike.coe_fn_eq, ← (map_continuous f).ae_eq_iff_eq μ (map_continuous g)]
  -- ⊢ ↑f =ᵐ[μ] ↑g
  refine' (coeFn_toLp p μ 𝕜 f).symm.trans (EventuallyEq.trans _ <| coeFn_toLp p μ 𝕜 g)
  -- ⊢ ↑↑(↑(toLp p μ 𝕜) f) =ᵐ[μ] ↑↑(↑(toLp p μ 𝕜) g)
  rw [h]
  -- 🎉 no goals
#align bounded_continuous_function.to_Lp_inj BoundedContinuousFunction.toLp_inj

theorem toLp_injective [μ.IsOpenPosMeasure] [NormedField 𝕜] [NormedSpace 𝕜 E] :
    Function.Injective (⇑(toLp p μ 𝕜 : (α →ᵇ E) →L[𝕜] Lp E p μ)) :=
  fun _f _g hfg => (toLp_inj μ).mp hfg
#align bounded_continuous_function.to_Lp_injective BoundedContinuousFunction.toLp_injective

end BoundedContinuousFunction

namespace ContinuousMap

variable [CompactSpace α] [IsFiniteMeasure μ]

variable (𝕜 : Type*) (p μ) [Fact (1 ≤ p)]

/-- The bounded linear map of considering a continuous function on a compact finite-measure
space `α` as an element of `Lp`.  By definition, the norm on `C(α, E)` is the sup-norm, transferred
from the space `α →ᵇ E` of bounded continuous functions, so this construction is just a matter of
transferring the structure from `BoundedContinuousFunction.toLp` along the isometry. -/
def toLp [NormedField 𝕜] [NormedSpace 𝕜 E] : C(α, E) →L[𝕜] Lp E p μ :=
  (BoundedContinuousFunction.toLp p μ 𝕜).comp
    (linearIsometryBoundedOfCompact α E 𝕜).toLinearIsometry.toContinuousLinearMap
#align continuous_map.to_Lp ContinuousMap.toLp

variable {𝕜}

theorem range_toLp [NormedField 𝕜] [NormedSpace 𝕜 E] :
    (LinearMap.range (toLp p μ 𝕜 : C(α, E) →L[𝕜] Lp E p μ)).toAddSubgroup =
      MeasureTheory.Lp.boundedContinuousFunction E p μ := by
  refine' SetLike.ext' _
  -- ⊢ ↑(Submodule.toAddSubgroup (LinearMap.range (toLp p μ 𝕜))) = ↑(Lp.boundedCont …
  have := (linearIsometryBoundedOfCompact α E 𝕜).surjective
  -- ⊢ ↑(Submodule.toAddSubgroup (LinearMap.range (toLp p μ 𝕜))) = ↑(Lp.boundedCont …
  convert Function.Surjective.range_comp this (BoundedContinuousFunction.toLp (E := E) p μ 𝕜)
  -- ⊢ ↑(Lp.boundedContinuousFunction E p μ) = Set.range ↑(BoundedContinuousFunctio …
  rw [← BoundedContinuousFunction.range_toLp p μ (𝕜 := 𝕜)]
  -- ⊢ ↑(Submodule.toAddSubgroup (LinearMap.range (BoundedContinuousFunction.toLp p …
  rfl
  -- 🎉 no goals
#align continuous_map.range_to_Lp ContinuousMap.range_toLp

variable {p}

theorem coeFn_toLp [NormedField 𝕜] [NormedSpace 𝕜 E] (f : C(α, E)) :
    toLp (E := E) p μ 𝕜 f =ᵐ[μ] f :=
  AEEqFun.coeFn_mk f _
#align continuous_map.coe_fn_to_Lp ContinuousMap.coeFn_toLp

theorem toLp_def [NormedField 𝕜] [NormedSpace 𝕜 E] (f : C(α, E)) :
    toLp (E := E) p μ 𝕜 f =
      BoundedContinuousFunction.toLp (E := E) p μ 𝕜 (linearIsometryBoundedOfCompact α E 𝕜 f) :=
  rfl
#align continuous_map.to_Lp_def ContinuousMap.toLp_def

@[simp]
theorem toLp_comp_toContinuousMap [NormedField 𝕜] [NormedSpace 𝕜 E] (f : α →ᵇ E) :
    toLp (E := E) p μ 𝕜 f.toContinuousMap = BoundedContinuousFunction.toLp (E := E) p μ 𝕜 f :=
  rfl
#align continuous_map.to_Lp_comp_to_continuous_map ContinuousMap.toLp_comp_toContinuousMap

@[simp]
theorem coe_toLp [NormedField 𝕜] [NormedSpace 𝕜 E] (f : C(α, E)) :
    (toLp (E := E) p μ 𝕜 f : α →ₘ[μ] E) = f.toAEEqFun μ :=
  rfl
#align continuous_map.coe_to_Lp ContinuousMap.coe_toLp

theorem toLp_injective [μ.IsOpenPosMeasure] [NormedField 𝕜] [NormedSpace 𝕜 E] :
    Function.Injective (⇑(toLp p μ 𝕜 : C(α, E) →L[𝕜] Lp E p μ)) :=
  (BoundedContinuousFunction.toLp_injective _).comp (linearIsometryBoundedOfCompact α E 𝕜).injective
#align continuous_map.to_Lp_injective ContinuousMap.toLp_injective

theorem toLp_inj {f g : C(α, E)} [μ.IsOpenPosMeasure] [NormedField 𝕜] [NormedSpace 𝕜 E] :
    toLp (E := E) p μ 𝕜 f = toLp (E := E) p μ 𝕜 g ↔ f = g :=
  (toLp_injective μ).eq_iff
#align continuous_map.to_Lp_inj ContinuousMap.toLp_inj

variable {μ}

/-- If a sum of continuous functions `g n` is convergent, and the same sum converges in `Lᵖ` to `h`,
then in fact `g n` converges uniformly to `h`.  -/
theorem hasSum_of_hasSum_Lp {β : Type*} [μ.IsOpenPosMeasure] [NormedField 𝕜] [NormedSpace 𝕜 E]
    {g : β → C(α, E)} {f : C(α, E)} (hg : Summable g)
    (hg2 : HasSum (toLp (E := E) p μ 𝕜 ∘ g) (toLp (E := E) p μ 𝕜 f)) : HasSum g f := by
  convert Summable.hasSum hg
  -- ⊢ f = ∑' (b : β), g b
  exact toLp_injective μ (hg2.unique ((toLp p μ 𝕜).hasSum <| Summable.hasSum hg))
  -- 🎉 no goals
#align continuous_map.has_sum_of_has_sum_Lp ContinuousMap.hasSum_of_hasSum_Lp

variable (μ) [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]

theorem toLp_norm_eq_toLp_norm_coe :
    ‖(toLp p μ 𝕜 : C(α, E) →L[𝕜] Lp E p μ)‖ =
      ‖(BoundedContinuousFunction.toLp p μ 𝕜 : (α →ᵇ E) →L[𝕜] Lp E p μ)‖ :=
  ContinuousLinearMap.op_norm_comp_linearIsometryEquiv _ _
#align continuous_map.to_Lp_norm_eq_to_Lp_norm_coe ContinuousMap.toLp_norm_eq_toLp_norm_coe

/-- Bound for the operator norm of `ContinuousMap.toLp`. -/
theorem toLp_norm_le :
    ‖(toLp p μ 𝕜 : C(α, E) →L[𝕜] Lp E p μ)‖ ≤ measureUnivNNReal μ ^ p.toReal⁻¹ := by
  rw [toLp_norm_eq_toLp_norm_coe]
  -- ⊢ ‖BoundedContinuousFunction.toLp p μ 𝕜‖ ≤ ↑(measureUnivNNReal μ ^ (ENNReal.to …
  exact BoundedContinuousFunction.toLp_norm_le μ
  -- 🎉 no goals
#align continuous_map.to_Lp_norm_le ContinuousMap.toLp_norm_le

end ContinuousMap

end

namespace MeasureTheory

namespace Lp

theorem pow_mul_meas_ge_le_norm (f : Lp E p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) (ε : ℝ≥0∞) :
    (ε * μ { x | ε ≤ (‖f x‖₊ : ℝ≥0∞) ^ p.toReal }) ^ (1 / p.toReal) ≤ ENNReal.ofReal ‖f‖ :=
  (ENNReal.ofReal_toReal (snorm_ne_top f)).symm ▸
    pow_mul_meas_ge_le_snorm μ hp_ne_zero hp_ne_top (Lp.aestronglyMeasurable f) ε
#align measure_theory.Lp.pow_mul_meas_ge_le_norm MeasureTheory.Lp.pow_mul_meas_ge_le_norm

theorem mul_meas_ge_le_pow_norm (f : Lp E p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) (ε : ℝ≥0∞) :
    ε * μ { x | ε ≤ (‖f x‖₊ : ℝ≥0∞) ^ p.toReal } ≤ ENNReal.ofReal ‖f‖ ^ p.toReal :=
  (ENNReal.ofReal_toReal (snorm_ne_top f)).symm ▸
    mul_meas_ge_le_pow_snorm μ hp_ne_zero hp_ne_top (Lp.aestronglyMeasurable f) ε
#align measure_theory.Lp.mul_meas_ge_le_pow_norm MeasureTheory.Lp.mul_meas_ge_le_pow_norm

/-- A version of Markov's inequality with elements of Lp. -/
theorem mul_meas_ge_le_pow_norm' (f : Lp E p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (ε : ℝ≥0∞) : ε ^ p.toReal * μ { x | ε ≤ ‖f x‖₊ } ≤ ENNReal.ofReal ‖f‖ ^ p.toReal :=
  (ENNReal.ofReal_toReal (snorm_ne_top f)).symm ▸
    mul_meas_ge_le_pow_snorm' μ hp_ne_zero hp_ne_top (Lp.aestronglyMeasurable f) ε
#align measure_theory.Lp.mul_meas_ge_le_pow_norm' MeasureTheory.Lp.mul_meas_ge_le_pow_norm'

theorem meas_ge_le_mul_pow_norm (f : Lp E p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) {ε : ℝ≥0∞}
    (hε : ε ≠ 0) : μ { x | ε ≤ ‖f x‖₊ } ≤ ε⁻¹ ^ p.toReal * ENNReal.ofReal ‖f‖ ^ p.toReal :=
  (ENNReal.ofReal_toReal (snorm_ne_top f)).symm ▸
    meas_ge_le_mul_pow_snorm μ hp_ne_zero hp_ne_top (Lp.aestronglyMeasurable f) hε
#align measure_theory.Lp.meas_ge_le_mul_pow_norm MeasureTheory.Lp.meas_ge_le_mul_pow_norm

end Lp

end MeasureTheory
