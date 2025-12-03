/-
Copyright (c) 2025 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio, Michael Rothgang, Floris van Doorn
-/
module

public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Attempts for Sobolev Space definitions
-/

@[expose] public noncomputable section

open Function Seminorm SeminormFamily Set TopologicalSpace TestFunction MeasureTheory Distribution
open scoped BoundedContinuousFunction ENNReal Topology Distributions

variable {𝕜 𝕂 : Type*} [NontriviallyNormedField 𝕜] --[RCLike 𝕂]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  /- probably `Ω` should have type `Set E` and moved after the argument `f` in declarations -/
  {Ω : Opens E}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedSpace 𝕜 F'] [SMulCommClass ℝ 𝕜 F']
    -- [NormedSpace 𝕂 F]
  {f f' : E → F} {n : ℕ∞} {k : ℕ∞} {p : ℝ≥0∞} {μ : Measure E}

namespace Distribution

/- maybe inline this definition in `HasWeakDeriv`? -/
structure IsRepresentedBy (T : 𝓓'(Ω, F)) (f : E → F) (μ : Measure E) : Prop where
  locallyIntegrable : LocallyIntegrableOn f Ω μ
  eq_ofFun : T = ofFun Ω f μ

end Distribution
open Distribution

section FinDim
variable [FiniteDimensional ℝ E]

/- maybe inline this definition when used -/
variable (Ω) in
def weakDeriv (f : E → F) (μ : Measure E) : 𝓓'(Ω, E →L[ℝ] F) :=
  fderivCLM (ofFun Ω f μ)

-- /-- `g` represents distribution `f` and is in `L^p`. -/
-- structure Distribution.MemLpWith (f : 𝓓'(Ω, F)) (g : E → F) (p : ℝ≥0∞) (μ : Measure E) :
--     Prop where
--   isRegular : IsRepresentedBy f g μ
--   memLp : MeasureTheory.MemLp g p μ

-- variable (Ω) in
-- /-- `f` is in `W^{1, p}` and has weak derivative represented by `g`. -/
-- structure MemSobolev1With (f : E → F) (g : E → E →L[ℝ] F) (p : ℝ≥0∞) (μ : Measure E) : Prop where
--   memLp : MemLp f p (μ.restrict Ω)
--   memLp_weakDeriv : (weakDeriv Ω f μ).MemLpWith g p μ

variable (Ω) in
/-- `f` has weak derivative represented by `g`. -/
def HasWeakDeriv (f : E → F) (g : E → E →L[ℝ] F) (μ : Measure E) : Prop :=
  IsRepresentedBy (weakDeriv Ω f μ) g μ

namespace HasWeakDeriv

variable {g g' : E → E →L[ℝ] F} {c : ℝ}

lemma add (hf : HasWeakDeriv Ω f g μ) (hg : HasWeakDeriv Ω f' g' μ) :
    HasWeakDeriv Ω (f + f') (g + g') μ := by
  sorry

lemma neg (hf : HasWeakDeriv Ω f g μ) : HasWeakDeriv Ω (-f) (-g) μ := by
  sorry

lemma sub (hf : HasWeakDeriv Ω f g μ) (hg : HasWeakDeriv Ω f' g' μ) :
    HasWeakDeriv Ω (f - f') (g - g') μ := by
  sorry

lemma smul (hf : HasWeakDeriv Ω f g μ) : HasWeakDeriv Ω (c • f) (c • g) μ := by
  sorry

@[simp]
lemma zero : HasWeakDeriv Ω (0 : E → F) 0 μ := by
  sorry

end HasWeakDeriv

variable (Ω) in
/-- `f` has "weak taylor series" g, which are all L^p
k currently can be `∞`. Do we want that? -/
structure HasWTaylorSeriesUpTo (f : E → F) (g : E → FormalMultilinearSeries ℝ E F)
    (k : ℕ∞) (p : ℝ≥0∞) (μ : Measure E) : Prop where
  zero_eq : ∀ x, (g x 0).curry0 = f x
  hasWeakDeriv : ∀ m : ℕ, m < k → HasWeakDeriv Ω (g · m) (g · m.succ |>.curryLeft) μ
  memLp : ∀ m : ℕ, m ≤ k → MemLp (g · m) p μ

namespace HasWTaylorSeriesUpTo

-- add basic lemmas: add, neg, sub and smul

@[simp]
lemma zero : HasWTaylorSeriesUpTo Ω 0 (0 : E → FormalMultilinearSeries ℝ E F) k p μ := by
  sorry

end HasWTaylorSeriesUpTo

variable (Ω) in
def MemSobolev (f : E → F) (k : ℕ∞) (p : ℝ≥0∞) (μ : Measure E) : Prop :=
  ∃ g : E → FormalMultilinearSeries ℝ E F, HasWTaylorSeriesUpTo Ω f g k p μ

namespace MemSobolev

variable {g : E → F} {c : ℝ}

lemma add (hf : MemSobolev Ω f k p μ) (hg : MemSobolev Ω g k p μ) : MemSobolev Ω (f + g) k p μ := by
  sorry

lemma neg (hf : MemSobolev Ω f k p μ) : MemSobolev Ω (-f) k p μ := by
  sorry

lemma sub (hf : MemSobolev Ω f k p μ) (hg : MemSobolev Ω g k p μ) : MemSobolev Ω (f - g) k p μ := by
  sorry

lemma smul (hf : MemSobolev Ω f k p μ) : MemSobolev Ω (c • f) k p μ := by
  sorry

@[simp]
lemma zero : MemSobolev Ω (0 : E → F) k p μ := by
  use 0
  simp

end MemSobolev

/- to do: the Norm instance on PiLp also induces a non-defeq ENorm on PiLp, we maybe should
disable the Norm → ENorm instance. -/
/- to do: the EDist instance on PiLp for p = 0 is wrong. -/
/- to do: move this -/
/- to do: do we indeed want this for non-fintypes? -/
instance PiLp.instENorm (p : ℝ≥0∞) {ι : Type*} (β : ι → Type*) [(i : ι) → ENorm (β i)] :
    ENorm (PiLp p β) where
  enorm f :=
    if p = 0 then {i | ‖f i‖ₑ ≠ 0}.encard
    else if p = ∞ then ⨆ i, ‖f i‖ₑ else (∑' i, ‖f i‖ₑ ^ p.toReal) ^ (1 / p.toReal)

open Finset in
/-- Only used to write API. Use `sobolevNorm` instead. -/
/- to do: this feels natural for `k = ∞`, but might not give the desired result. -/
def sobolevNormAux (g : E → FormalMultilinearSeries ℝ E F) (k : ℕ∞) (p : ℝ≥0∞) (μ : Measure E) :
    ℝ≥0∞ :=
  ‖WithLp.toLp p fun i : {i : ℕ // i ≤ k} ↦ eLpNorm (g · i) p μ‖ₑ

open Classical Finset in
/-- This definition is different than in (most) textbooks, since we use the `L^p`-norm of the total
derivative instead of the `L^p`-norm of partial derivatives. These definitions are equivalent
for finite dimensional `E` and `k < ∞` [argument todo]. -/
def sobolevNorm (f : E → F) (k : ℕ∞) (p : ℝ≥0∞) (μ : Measure E) : ℝ≥0∞ :=
  if h : MemSobolev Ω f k p μ then sobolevNormAux h.choose k p μ else ∞

end FinDim

/-! potential alternative definition -/
namespace Distribution

def IsRegular (T : 𝓓'(Ω, F)) (μ : Measure E) : Prop :=
  ∃ (f : E → F), LocallyIntegrableOn f Ω μ ∧ T = ofFun Ω f μ

namespace IsRegular

variable {T T₁ T₂ : 𝓓'(Ω, F)}

lemma add (hT₁ : IsRegular T₁ μ) (hT₂ : IsRegular T₂ μ) : IsRegular (T₁ + T₂) μ := by
  obtain ⟨f, hf, rfl⟩ := hT₁
  obtain ⟨g, hg, rfl⟩ := hT₂
  exact ⟨f + g, hf.add hg, ofFun_add hf hg |>.symm⟩


lemma smul (hT : IsRegular T μ) (c : ℝ) : IsRegular (c • T) μ := by
  obtain ⟨f, hf, rfl⟩ := hT
  exact ⟨c • f, hf.smul c, ofFun_smul c |>.symm⟩

end IsRegular

open Classical in
/-- A representative of a regular distribution, chosen so that it is 0 outside `Ω`.
Has junk-value `0` for non-regular distributions. -/
def out (T : 𝓓'(Ω, F)) (μ : Measure E) : E → F :=
  if h : IsRegular T μ then Ω.1.indicator h.choose else 0

lemma ofFun_inj {f f' : E → F} (h : ofFun Ω f μ = ofFun Ω f' μ) : f =ᵐ[μ.restrict Ω] f' := sorry

structure MemLp (T : 𝓓'(Ω, F)) (p : ℝ≥0∞) (μ : Measure E) : Prop where
  isRegular : IsRegular T μ
  memLp : MeasureTheory.MemLp (T.out μ) p μ

variable [FiniteDimensional ℝ E]

def MemSobolev (T : 𝓓'(Ω, F)) (k : ℕ∞) (p : ℝ≥0∞) (μ : Measure E) : Prop :=
  ∀ m : ℕ, m ≤ k → (iteratedFDerivCLM (E := E) (F := F) m T).MemLp p μ

open Classical Finset in
/-- This definition is different than in (most) textbooks, since we use the `L^p`-norm of the total
derivative instead of the `L^p`-norm of partial derivatives. These definitions are equivalent
for finite dimensional `E` and `k < ∞` [argument todo]. -/
def sobolevNorm (T : 𝓓'(Ω, F)) (k : ℕ) (p : ℝ≥0∞) (μ : Measure E) : ℝ≥0∞ :=
  if MemSobolev T k p μ then
    sobolevNormAux (fun x i ↦ (iteratedFDerivCLM (E := E) (F := F) i T).out μ x) k p μ
  else ∞

end Distribution



variable [FiniteDimensional ℝ E]

lemma memSobolev_congr_ae (h : f =ᵐ[μ.restrict Ω] f') :
    MemSobolev Ω f k p μ ↔ MemSobolev Ω f' k p μ := by
  sorry

lemma MemSobolev.ae_eq (h : f =ᵐ[μ.restrict Ω] f') (hf : MemSobolev Ω f k p μ) :
    MemSobolev Ω f' k p μ :=
  memSobolev_congr_ae h |>.mp hf

variable (Ω) in
def SobolevSpace (k : ℕ∞) (p : ℝ≥0∞) (μ : Measure E := by volume_tac) :
    AddSubgroup (E →ₘ[μ] F) where
  carrier := { f | MemSobolev Ω f k p μ }
  zero_mem' := by simp [memSobolev_congr_ae AEEqFun.coeFn_zero.restrict, MemSobolev.zero]
  add_mem' {f g} hf hg := by
    simp [memSobolev_congr_ae (AEEqFun.coeFn_add f g).restrict, hf.add hg]
  neg_mem' {f} hf := by simp [memSobolev_congr_ae (AEEqFun.coeFn_neg f).restrict, hf.neg]

namespace MemSobolev

-- /-- make an element of Lp from a function verifying `MemSobolev` -/
-- def toSobolev (f : E → F) (h_mem_ℒp : MemSobolev Ω f k p μ) : Lp E p μ :=
--   ⟨AEEqFun.mk f h_mem_ℒp.1, h_mem_ℒp.eLpNorm_mk_lt_top⟩

-- theorem toSobolev_val {f : E → F} (h : MemSobolev Ω f k p μ) : (toSobolev f h).1 = AEEqFun.mk f h.1 := rfl

-- theorem coeFn_toSobolev {f : E → F} (hf : MemSobolev Ω f k p μ) : hf.toSobolev f =ᵐ[μ] f :=
--   AEEqFun.coeFn_mk _ _

-- theorem toSobolev_congr {f g : E → F} (hf : MemSobolev Ω f k p μ) (hg : MemSobolev g p μ) (hfg : f =ᵐ[μ] g) :
--     hf.toSobolev f = hg.toSobolev g := by simp [toSobolev, hfg]

-- @[simp]
-- theorem toSobolev_eq_toSobolev_iff {f g : E → F} (hf : MemSobolev Ω f k p μ) (hg : MemSobolev g p μ) :
--     hf.toSobolev f = hg.toSobolev g ↔ f =ᵐ[μ] g := by simp [toSobolev]

-- @[simp]
-- theorem toSobolev_zero (h : MemSobolev (0 : E → F) p μ) : h.toSobolev 0 = 0 :=
--   rfl

-- theorem toSobolev_add {f g : E → F} (hf : MemSobolev Ω f k p μ) (hg : MemSobolev g p μ) :
--     (hf.add hg).toSobolev (f + g) = hf.toSobolev f + hg.toSobolev g :=
--   rfl

-- theorem toSobolev_neg {f : E → F} (hf : MemSobolev Ω f k p μ) : hf.neg.toSobolev (-f) = -hf.toSobolev f :=
--   rfl

-- theorem toSobolev_sub {f g : E → F} (hf : MemSobolev Ω f k p μ) (hg : MemSobolev g p μ) :
--     (hf.sub hg).toSobolev (f - g) = hf.toSobolev f - hg.toSobolev g :=
--   rfl

-- end MemSobolev

-- namespace Lp

-- instance instCoeFun : CoeFun (Lp E p μ) (fun _ => E → F) :=
--   ⟨fun f => ((f : α →ₘ[μ] E) : E → F)⟩

-- @[ext high]
-- theorem ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g := by
--   ext
--   exact h

-- theorem mem_Lp_iff_eLpNorm_lt_top {f : α →ₘ[μ] E} : f ∈ Lp E p μ ↔ eLpNorm f p μ < ∞ := Iff.rfl

-- theorem mem_Lp_iff_memSobolev {f : α →ₘ[μ] E} : f ∈ Lp E p μ ↔ MemSobolev Ω f k p μ := by
--   simp [mem_Lp_iff_eLpNorm_lt_top, MemSobolev, f.stronglyMeasurable.aestronglyMeasurable]

-- protected theorem antitone [IsFiniteMeasure μ] {p q : ℝ≥0∞} (hpq : p ≤ q) : Lp E q μ ≤ Lp E p μ :=
--   fun f hf => (MemSobolev.mono_exponent ⟨f.aestronglyMeasurable, hf⟩ hpq).2

-- @[simp]
-- theorem coeFn_mk {f : α →ₘ[μ] E} (hf : eLpNorm f p μ < ∞) : ((⟨f, hf⟩ : Lp E p μ) : E → F) = f :=
--   rfl

-- -- not @[simp] because dsimp can prove this
-- theorem coe_mk {f : α →ₘ[μ] E} (hf : eLpNorm f p μ < ∞) : ((⟨f, hf⟩ : Lp E p μ) : α →ₘ[μ] E) = f :=
--   rfl

-- @[simp]
-- theorem toSobolev_coeFn (f : Lp E p μ) (hf : MemSobolev Ω f k p μ) : hf.toSobolev f = f := by
--   simp [MemSobolev.toSobolev]

-- theorem eLpNorm_lt_top (f : Lp E p μ) : eLpNorm f p μ < ∞ :=
--   f.prop

-- @[aesop (rule_sets := [finiteness]) safe apply]
-- theorem eLpNorm_ne_top (f : Lp E p μ) : eLpNorm f p μ ≠ ∞ :=
--   (eLpNorm_lt_top f).ne

-- @[fun_prop, measurability]
-- protected theorem stronglyMeasurable (f : Lp E p μ) : StronglyMeasurable f :=
--   f.val.stronglyMeasurable

-- @[fun_prop, measurability]
-- protected theorem aestronglyMeasurable (f : Lp E p μ) : AEStronglyMeasurable f μ :=
--   f.val.aestronglyMeasurable

-- protected theorem memSobolev (f : Lp E p μ) : MemSobolev Ω f k p μ :=
--   ⟨Lp.aestronglyMeasurable f, f.prop⟩

-- variable (E p μ)

-- theorem coeFn_zero : ⇑(0 : Lp E p μ) =ᵐ[μ] 0 :=
--   AEEqFun.coeFn_zero

-- variable {E p μ}

-- theorem coeFn_neg (f : Lp E p μ) : ⇑(-f) =ᵐ[μ] -f :=
--   AEEqFun.coeFn_neg _

-- theorem coeFn_add (f g : Lp E p μ) : ⇑(f + g) =ᵐ[μ] f + g :=
--   AEEqFun.coeFn_add _ _

-- theorem coeFn_sub (f g : Lp E p μ) : ⇑(f - g) =ᵐ[μ] f - g :=
--   AEEqFun.coeFn_sub _ _

-- theorem const_mem_Lp (α) {_ : MeasurableSpace α} (μ : Measure α) (c : E) [IsFiniteMeasure μ] :
--     @AEEqFun.const α _ _ μ _ c ∈ Lp E p μ :=
--   (memSobolev_const c).eLpNorm_mk_lt_top

-- instance instNorm : Norm (Lp E p μ) where norm f := ENNReal.toReal (eLpNorm f p μ)

-- -- note: we need this to be defeq to the instance from `SeminormedAddGroup.toNNNorm`, so
-- -- can't use `ENNReal.toNNReal (eLpNorm f p μ)`
-- instance instNNNorm : NNNorm (Lp E p μ) where nnnorm f := ⟨‖f‖, ENNReal.toReal_nonneg⟩

-- instance instDist : Dist (Lp E p μ) where dist f g := ‖f - g‖

-- instance instEDist : EDist (Lp E p μ) where edist f g := eLpNorm (⇑f - ⇑g) p μ

-- theorem norm_def (f : Lp E p μ) : ‖f‖ = ENNReal.toReal (eLpNorm f p μ) :=
--   rfl

-- theorem nnnorm_def (f : Lp E p μ) : ‖f‖₊ = ENNReal.toNNReal (eLpNorm f p μ) :=
--   rfl

-- @[simp, norm_cast]
-- protected theorem coe_nnnorm (f : Lp E p μ) : (‖f‖₊ : ℝ) = ‖f‖ :=
--   rfl

-- @[simp]
-- theorem enorm_def (f : Lp E p μ) : ‖f‖ₑ = eLpNorm f p μ :=
--   ENNReal.coe_toNNReal <| Lp.eLpNorm_ne_top f

-- @[simp]
-- lemma norm_toSobolev (f : E → F) (hf : MemSobolev Ω f k p μ) : ‖hf.toSobolev f‖ = ENNReal.toReal (eLpNorm f p μ) := by
--   rw [norm_def, eLpNorm_congr_ae (MemSobolev.coeFn_toSobolev hf)]

-- @[simp]
-- theorem nnnorm_toSobolev (f : E → F) (hf : MemSobolev Ω f k p μ) :
--     ‖hf.toSobolev f‖₊ = ENNReal.toNNReal (eLpNorm f p μ) :=
--   NNReal.eq <| norm_toSobolev f hf

-- lemma enorm_toSobolev {f : E → F} (hf : MemSobolev Ω f k p μ) : ‖hf.toSobolev f‖ₑ = eLpNorm f p μ := by
--   simp [enorm, nnnorm_toSobolev f hf, ENNReal.coe_toNNReal hf.2.ne]

-- theorem dist_def (f g : Lp E p μ) : dist f g = (eLpNorm (⇑f - ⇑g) p μ).toReal := by
--   simp_rw [dist, norm_def]
--   refine congr_arg _ ?_
--   apply eLpNorm_congr_ae (coeFn_sub _ _)

-- theorem edist_def (f g : Lp E p μ) : edist f g = eLpNorm (⇑f - ⇑g) p μ :=
--   rfl

-- protected theorem edist_dist (f g : Lp E p μ) : edist f g = .ofReal (dist f g) := by
--   rw [edist_def, dist_def, ← eLpNorm_congr_ae (coeFn_sub _ _),
--     ENNReal.ofReal_toReal (eLpNorm_ne_top (f - g))]

-- protected theorem dist_edist (f g : Lp E p μ) : dist f g = (edist f g).toReal :=
--   MeasureTheory.Lp.dist_def ..

-- theorem dist_eq_norm (f g : Lp E p μ) : dist f g = ‖f - g‖ := rfl

-- @[simp]
-- theorem edist_toSobolev_toSobolev (f g : E → F) (hf : MemSobolev Ω f k p μ) (hg : MemSobolev g p μ) :
--     edist (hf.toSobolev f) (hg.toSobolev g) = eLpNorm (f - g) p μ := by
--   rw [edist_def]
--   exact eLpNorm_congr_ae (hf.coeFn_toSobolev.sub hg.coeFn_toSobolev)

-- @[simp]
-- theorem edist_toSobolev_zero (f : E → F) (hf : MemSobolev Ω f k p μ) : edist (hf.toSobolev f) 0 = eLpNorm f p μ := by
--   simpa using edist_toSobolev_toSobolev f 0 hf MemSobolev.zero

-- @[simp]
-- theorem nnnorm_zero : ‖(0 : Lp E p μ)‖₊ = 0 := by
--   rw [nnnorm_def]
--   change (eLpNorm (⇑(0 : α →ₘ[μ] E)) p μ).toNNReal = 0
--   simp [eLpNorm_congr_ae AEEqFun.coeFn_zero, eLpNorm_zero]

-- @[simp]
-- theorem norm_zero : ‖(0 : Lp E p μ)‖ = 0 :=
--   congr_arg ((↑) : ℝ≥0 → ℝ) nnnorm_zero

-- @[simp]
-- theorem norm_measure_zero (f : Lp E p (0 : MeasureTheory.Measure α)) : ‖f‖ = 0 := by
--   -- Squeezed for performance reasons
--   simp only [norm_def, eLpNorm_measure_zero, ENNReal.toReal_zero]

-- @[simp] theorem norm_exponent_zero (f : Lp E 0 μ) : ‖f‖ = 0 := by
--   -- Squeezed for performance reasons
--   simp only [norm_def, eLpNorm_exponent_zero, ENNReal.toReal_zero]

-- theorem nnnorm_eq_zero_iff {f : Lp E p μ} (hp : 0 < p) : ‖f‖₊ = 0 ↔ f = 0 := by
--   refine ⟨fun hf => ?_, fun hf => by simp [hf]⟩
--   rw [nnnorm_def, ENNReal.toNNReal_eq_zero_iff] at hf
--   cases hf with
--   | inl hf =>
--     rw [eLpNorm_eq_zero_iff (Lp.aestronglyMeasurable f) hp.ne.symm] at hf
--     exact Subtype.ext (AEEqFun.ext (hf.trans AEEqFun.coeFn_zero.symm))
--   | inr hf =>
--     exact absurd hf (eLpNorm_ne_top f)

-- theorem norm_eq_zero_iff {f : Lp E p μ} (hp : 0 < p) : ‖f‖ = 0 ↔ f = 0 :=
--   NNReal.coe_eq_zero.trans (nnnorm_eq_zero_iff hp)

-- theorem eq_zero_iff_ae_eq_zero {f : Lp E p μ} : f = 0 ↔ f =ᵐ[μ] 0 := by
--   rw [← (Lp.memSobolev f).toSobolev_eq_toSobolev_iff MemSobolev.zero, MemSobolev.toSobolev_zero, toSobolev_coeFn]

-- @[simp]
-- theorem nnnorm_neg (f : Lp E p μ) : ‖-f‖₊ = ‖f‖₊ := by
--   rw [nnnorm_def, nnnorm_def, eLpNorm_congr_ae (coeFn_neg _), eLpNorm_neg]

-- @[simp]
-- theorem norm_neg (f : Lp E p μ) : ‖-f‖ = ‖f‖ :=
--   congr_arg ((↑) : ℝ≥0 → ℝ) (nnnorm_neg f)

-- theorem nnnorm_le_mul_nnnorm_of_ae_le_mul {c : ℝ≥0} {f : Lp E p μ} {g : Lp F p μ}
--     (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊) : ‖f‖₊ ≤ c * ‖g‖₊ := by
--   simp only [nnnorm_def]
--   have := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul h p
--   rwa [← ENNReal.toNNReal_le_toNNReal, ENNReal.smul_def, smul_eq_mul, ENNReal.toNNReal_mul,
--     ENNReal.toNNReal_coe] at this
--   · finiteness
--   · exact ENNReal.mul_ne_top ENNReal.coe_ne_top (by finiteness)

-- theorem norm_le_mul_norm_of_ae_le_mul {c : ℝ} {f : Lp E p μ} {g : Lp F p μ}
--     (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) : ‖f‖ ≤ c * ‖g‖ := by
--   rcases le_or_gt 0 c with hc | hc
--   · lift c to ℝ≥0 using hc
--     exact NNReal.coe_le_coe.mpr (nnnorm_le_mul_nnnorm_of_ae_le_mul h)
--   · simp only [norm_def]
--     have := eLpNorm_eq_zero_and_zero_of_ae_le_mul_neg h hc p
--     simp [this]

-- theorem norm_le_norm_of_ae_le {f : Lp E p μ} {g : Lp F p μ} (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
--     ‖f‖ ≤ ‖g‖ := by
--   rw [norm_def, norm_def]
--   exact ENNReal.toReal_mono (by finiteness) (eLpNorm_mono_ae h)

-- theorem mem_Lp_of_nnnorm_ae_le_mul {c : ℝ≥0} {f : α →ₘ[μ] E} {g : Lp F p μ}
--     (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊) : f ∈ Lp E p μ :=
--   mem_Lp_iff_memSobolev.2 <| MemSobolev.of_nnnorm_le_mul (Lp.memSobolev g) f.aestronglyMeasurable h

-- theorem mem_Lp_of_ae_le_mul {c : ℝ} {f : α →ₘ[μ] E} {g : Lp F p μ}
--     (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) : f ∈ Lp E p μ :=
--   mem_Lp_iff_memSobolev.2 <| MemSobolev.of_le_mul (Lp.memSobolev g) f.aestronglyMeasurable h

-- theorem mem_Lp_of_nnnorm_ae_le {f : α →ₘ[μ] E} {g : Lp F p μ} (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ ‖g x‖₊) :
--     f ∈ Lp E p μ :=
--   mem_Lp_iff_memSobolev.2 <| MemSobolev.of_le (Lp.memSobolev g) f.aestronglyMeasurable h

-- theorem mem_Lp_of_ae_le {f : α →ₘ[μ] E} {g : Lp F p μ} (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
--     f ∈ Lp E p μ :=
--   mem_Lp_of_nnnorm_ae_le h

-- theorem mem_Lp_of_ae_nnnorm_bound [IsFiniteMeasure μ] {f : α →ₘ[μ] E} (C : ℝ≥0)
--     (hfC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) : f ∈ Lp E p μ :=
--   mem_Lp_iff_memSobolev.2 <| MemSobolev.of_bound f.aestronglyMeasurable _ hfC

-- theorem mem_Lp_of_ae_bound [IsFiniteMeasure μ] {f : α →ₘ[μ] E} (C : ℝ) (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
--     f ∈ Lp E p μ :=
--   mem_Lp_iff_memSobolev.2 <| MemSobolev.of_bound f.aestronglyMeasurable _ hfC

-- theorem nnnorm_le_of_ae_bound [IsFiniteMeasure μ] {f : Lp E p μ} {C : ℝ≥0}
--     (hfC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) : ‖f‖₊ ≤ measureUnivNNReal μ ^ p.toReal⁻¹ * C := by
--   by_cases hμ : μ = 0
--   · by_cases hp : p.toReal⁻¹ = 0
--     · simp [hp, hμ, nnnorm_def]
--     · simp [hμ, nnnorm_def]
--   rw [← ENNReal.coe_le_coe, nnnorm_def, ENNReal.coe_toNNReal (eLpNorm_ne_top _)]
--   refine (eLpNorm_le_of_ae_nnnorm_bound hfC).trans_eq ?_
--   rw [← coe_measureUnivNNReal μ, ← ENNReal.coe_rpow_of_ne_zero (measureUnivNNReal_pos hμ).ne',
--     ENNReal.coe_mul, mul_comm, ENNReal.smul_def, smul_eq_mul]

-- theorem norm_le_of_ae_bound [IsFiniteMeasure μ] {f : Lp E p μ} {C : ℝ} (hC : 0 ≤ C)
--     (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : ‖f‖ ≤ measureUnivNNReal μ ^ p.toReal⁻¹ * C := by
--   lift C to ℝ≥0 using hC
--   have := nnnorm_le_of_ae_bound hfC
--   rwa [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_rpow] at this

-- instance instNormedAddCommGroup [hp : Fact (1 ≤ p)] : NormedAddCommGroup (Lp E p μ) :=
--   { AddGroupNorm.toNormedAddCommGroup
--       { toFun := (norm : Lp E p μ → ℝ)
--         map_zero' := norm_zero
--         neg' := by simp only [norm_neg, implies_true] -- squeezed for performance reasons
--         add_le' := fun f g => by
--           suffices ‖f + g‖ₑ ≤ ‖f‖ₑ + ‖g‖ₑ by
--             -- Squeezed for performance reasons
--             simpa only [ge_iff_le, enorm, ←ENNReal.coe_add, ENNReal.coe_le_coe] using this
--           simp only [Lp.enorm_def]
--           exact (eLpNorm_congr_ae (AEEqFun.coeFn_add _ _)).trans_le
--             (eLpNorm_add_le (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _) hp.out)
--         eq_zero_of_map_eq_zero' := fun _ =>
--           (norm_eq_zero_iff <| zero_lt_one.trans_le hp.1).1 } with
--     edist := edist
--     edist_dist := Lp.edist_dist }


/-
To do:
1. Basic lemmas (closure under `+`, `•`, ...)
2. define Sobolev spaces
3. [Adams, Th 3.3] prove Banach space
4. monotonicity in `k` and (if `Ω` is bounded) in `p`.
5. [Adams, Cor 3.4] C^k functions are contained in W^{k, p}
6. [Adams, Th 3.6] separable, uniform convexity
7. [Adams, Th 3.15-3.17] density of smooth functions in W^{k, p}
8. [Adams, Ch 4] Sobolev embedding theorem
-/
