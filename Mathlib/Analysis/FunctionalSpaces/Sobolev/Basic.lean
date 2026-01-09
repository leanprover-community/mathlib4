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

lemma isRepresentedBy_of_ae (T : 𝓓'(Ω, F)) (h : f =ᵐ[μ.restrict Ω] f')
    (hf : IsRepresentedBy T f μ) : IsRepresentedBy T f' μ := by
  rcases hf with ⟨h1, h2⟩
  refine ⟨fun x hx ↦ ?_, by rwa [h2, ofFun_ae_congr]⟩
  obtain ⟨s, hs, hsf⟩ := h1 x hx
  refine ⟨s ∩ Ω, Filter.inter_mem hs self_mem_nhdsWithin, ?_⟩
  apply (hsf.mono_set inter_subset_left).congr_fun_ae
  have : ae (μ.restrict (s ∩ Ω)) ≤ ae (μ.restrict Ω) := by
    rw [Measure.ae_le_iff_absolutelyContinuous]
    exact (Measure.restrict_mono inter_subset_right (by rfl)).absolutelyContinuous
  exact h.filter_mono this

lemma isRepresentedBy_congr_ae (T : 𝓓'(Ω, F)) (hf : f =ᵐ[μ.restrict Ω] f') :
    IsRepresentedBy T f μ ↔ IsRepresentedBy T f' μ :=
  ⟨isRepresentedBy_of_ae T hf, isRepresentedBy_of_ae T hf.symm⟩

lemma isRepresentedBy_zero : IsRepresentedBy (0 : 𝓓'(Ω, F)) (0 : E → F) μ where
  locallyIntegrable := locallyIntegrable_zero.locallyIntegrableOn _
  eq_ofFun := by simp

namespace IsRepresentedBy

variable {T T' : 𝓓'(Ω, F)} {f f' : E → F} {c : ℝ}

lemma add (hT : IsRepresentedBy T f μ) (hT' : IsRepresentedBy T' f' μ) :
    IsRepresentedBy (T + T') (f + f') μ where
  locallyIntegrable := hT.locallyIntegrable.add hT'.locallyIntegrable
  eq_ofFun := by
    simp [hT.eq_ofFun, hT'.eq_ofFun, ofFun_add hT.locallyIntegrable hT'.locallyIntegrable]

lemma neg (hT : IsRepresentedBy T f μ) : IsRepresentedBy (-T) (-f) μ where
  locallyIntegrable := hT.locallyIntegrable.neg
  eq_ofFun := by simp [hT.eq_ofFun, ofFun_neg]

lemma sub (hT : IsRepresentedBy T f μ) (hT' : IsRepresentedBy T' f' μ) :
    IsRepresentedBy (T - T') (f - f') μ := by
  rw [sub_eq_add_neg T T', sub_eq_add_neg]
  exact hT.add hT'.neg

lemma smul (hT : IsRepresentedBy T f μ) : IsRepresentedBy (c • T) (c • f) μ where
  locallyIntegrable := hT.locallyIntegrable.smul c
  eq_ofFun := by simp [hT.eq_ofFun]

end IsRepresentedBy

end Distribution
open Distribution

section FinDim
variable [FiniteDimensional ℝ E]

/- maybe inline this definition when used -/
variable (Ω) in
/-- The weak or distributional derivative of a function:
this is 0 if the function is not locally integrable -/
def weakDeriv (f : E → F) (μ : Measure E) : 𝓓'(Ω, E →L[ℝ] F) :=
  fderivCLM (ofFun Ω f μ)

lemma weakDeriv_congr_ae /- (f f' : E → F) -/ (μ : Measure E) (h : f =ᵐ[μ] f') :
    weakDeriv Ω f μ = weakDeriv Ω f' μ :=
  sorry


-- useful on its own?
lemma weakDeriv_of_not_locallyIntegrableOn {f : E → F} (hf : ¬LocallyIntegrableOn f Ω μ) :
    weakDeriv Ω f μ = 0 := by
  simp [weakDeriv, ofFun_of_not_locallyIntegrable hf]

-- XXX: where should the minus sign go?
lemma weakDeriv_apply {f : E → F} (hf : LocallyIntegrableOn f Ω μ) (φ : 𝓓(Ω, ℝ)) (x : E) :
    weakDeriv Ω f μ φ x = ∫ (y : E), -(fderiv ℝ φ y) x • f y ∂μ := by
  simp only [weakDeriv, Distribution.fderivCLM]
  -- XXX: why do I need the dsimp step?
  dsimp
  simp [ofFun_apply hf, TestFunction.lineDerivCLM, TestFunction.fderivCLM]
  congr

@[simp]
lemma weakDeriv_add (hf : LocallyIntegrableOn f Ω μ) (hf' : LocallyIntegrableOn f' Ω μ) :
    weakDeriv Ω (f + f') μ = weakDeriv Ω f μ + weakDeriv Ω f' μ := by
  ext φ
  simp [weakDeriv, ofFun_add hf hf']

@[simp]
lemma weakDeriv_neg : weakDeriv Ω (-f) μ = -weakDeriv Ω f μ := by
  ext φ
  by_cases hf : LocallyIntegrableOn f Ω μ; swap
  · have hf' : ¬LocallyIntegrableOn (-f) Ω μ := by rwa [locallyIntegrableOn_neg_iff]
    simp [weakDeriv, *, ofFun_of_not_locallyIntegrable]
  simp [weakDeriv, ofFun_neg]

@[simp]
lemma weakDeriv_sub (hf : LocallyIntegrableOn f Ω μ) (hf' : LocallyIntegrableOn f' Ω μ) :
    weakDeriv Ω (f - f') μ = weakDeriv Ω f μ - weakDeriv Ω f' μ := by
  simp [sub_eq_add_neg, weakDeriv_add hf hf'.neg]

@[simp]
lemma weakDeriv_smul (c : ℝ) : weakDeriv Ω (c • f) μ = c • weakDeriv Ω f μ := by
  ext φ
  simp [weakDeriv]

lemma weakDeriv_zero : weakDeriv Ω (0 : E → F) μ = 0 := by simp [weakDeriv]

lemma weakDeriv_const (a : F) : weakDeriv Ω (fun _ : E ↦ a) μ = 0 := by
  by_cases hf : LocallyIntegrableOn (fun _ : E ↦ a) Ω μ; swap
  · exact weakDeriv_of_not_locallyIntegrableOn hf
  ext φ
  rw [weakDeriv_apply hf]
  -- now integrate by parts...
  sorry


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

lemma hasWeakDeriv_of_ae (h : f =ᵐ[μ.restrict Ω] f') (g : E → E →L[ℝ] F)
    (hf : HasWeakDeriv Ω f g μ) : HasWeakDeriv Ω f' g μ := by
  sorry

lemma hasWeakDeriv_congr_ae (h : f =ᵐ[μ.restrict Ω] f') (g : E → E →L[ℝ] F) :
    HasWeakDeriv Ω f g μ ↔ HasWeakDeriv Ω f' g μ :=
  ⟨fun hf ↦ hasWeakDeriv_of_ae h g hf, fun hf ↦ hasWeakDeriv_of_ae h.symm g hf⟩

@[simp]
lemma hasWeakDeriv_zero : HasWeakDeriv Ω (0 : E → F) 0 μ := by
  simp [HasWeakDeriv, weakDeriv_zero, isRepresentedBy_zero]

@[simp]
lemma hasWeakderiv_const {a : F} : HasWeakDeriv Ω (fun _ : E ↦ a) 0 μ := by
  simp [HasWeakDeriv, weakDeriv_const, isRepresentedBy_zero]

namespace HasWeakDeriv

variable {g g' : E → E →L[ℝ] F} {c : ℝ}

lemma add (hf : HasWeakDeriv Ω f g μ) (hf' : HasWeakDeriv Ω f' g' μ)
    (hfint : LocallyIntegrableOn f Ω μ) (hfint' : LocallyIntegrableOn f' Ω μ) :
    HasWeakDeriv Ω (f + f') (g + g') μ := by
  simp only [HasWeakDeriv] at hf hf' ⊢
  simp [weakDeriv_add hfint hfint', hf.add hf']

lemma neg (hf : HasWeakDeriv Ω f g μ) : HasWeakDeriv Ω (-f) (-g) μ := by
  simp only [HasWeakDeriv] at hf ⊢
  simpa [weakDeriv_neg] using hf.neg

lemma sub (hf : HasWeakDeriv Ω f g μ) (hg : HasWeakDeriv Ω f' g' μ)
    (hfint : LocallyIntegrableOn f Ω μ) (hfint' : LocallyIntegrableOn f' Ω μ) :
    HasWeakDeriv Ω (f - f') (g - g') μ := by
  simpa [sub_eq_add_neg] using hf.add hg.neg hfint hfint'.neg

lemma smul (hf : HasWeakDeriv Ω f g μ) : HasWeakDeriv Ω (c • f) (c • g) μ := by
  simp only [HasWeakDeriv] at hf ⊢
  simpa [weakDeriv_smul] using hf.smul

end HasWeakDeriv

variable (Ω) in
/-- `f` has "weak taylor series" g, which are all L^p
k currently can be `∞`. Do we want that? -/
structure HasWTaylorSeriesUpTo (f : E → F) (g : E → FormalMultilinearSeries ℝ E F)
    (k : ℕ∞) (p : ℝ≥0∞) (μ : Measure E) : Prop where
  zero_eq : ∀ x, (g x 0).curry0 = f x
  hasWeakDeriv : ∀ m : ℕ, m < k → HasWeakDeriv Ω (g · m) (g · m.succ |>.curryLeft) μ
  memLp : ∀ m : ℕ, m ≤ k → MemLp (g · m) p (μ.restrict Ω)

lemma hasWTaylorSeriesUpTo_congr_ae (h : f =ᵐ[μ.restrict Ω] f')
  (g : E → FormalMultilinearSeries ℝ E F) (k : ℕ∞) (μ : Measure E) :
    HasWTaylorSeriesUpTo Ω f g k p μ ↔ HasWTaylorSeriesUpTo Ω f' g k p μ := by
  sorry

namespace HasWTaylorSeriesUpTo

variable {g g' : E → FormalMultilinearSeries ℝ E F} {c : ℝ}

-- TODO: add a version assuming just finite-dimensionality of `E`, without the hypothesis on `μ`
/-- If `f` has weak Taylor series `g` on `Ω`, then `f` is locally integrable on `Ω`.
This version assumes `p ≥ 1` and `μ` having locally finite measure on `Ω`. -/
lemma locallyIntegrableOn_zero [IsLocallyFiniteMeasure (μ.restrict Ω)]
    (hf : HasWTaylorSeriesUpTo Ω f g k p μ) (hp : 1 ≤ p) :
    LocallyIntegrableOn (g · 0) Ω μ :=
  locallyIntegrableOn_of_locallyIntegrable_restrict <|
    (hf.memLp _ (by positivity)).locallyIntegrable hp

lemma locallyIntegrableOn_succ [IsLocallyFiniteMeasure (μ.restrict Ω)]
    (hf : HasWTaylorSeriesUpTo Ω f g k p μ) (n : ℕ) (hn : (n + 1) < k) (hp : 1 ≤ p) :
    LocallyIntegrableOn (fun x ↦ g x (n + 1)) Ω μ := by
  have aux : n < k := by
    apply lt_trans ?_ hn
    norm_cast
    omega
  have := hf.hasWeakDeriv n aux
  have := this.locallyIntegrable -- almost what we want:
  sorry
  -- need to translate some currying
  -- have (x) : (fun x ↦ g x (n + 1)) = (fun x ↦ (g x n.succ).curryLeft) := sorry

lemma mono {k' : ℕ∞} (hf : HasWTaylorSeriesUpTo Ω f g k p μ) (hk : k' ≤ k) :
    HasWTaylorSeriesUpTo Ω f g k' p μ where
  zero_eq := hf.zero_eq
  hasWeakDeriv m hm := hf.hasWeakDeriv m (lt_of_lt_of_le hm hk)
  memLp m hm := hf.memLp m (le_trans hm hk)

-- TODO: add doc-string!
def shrink_measure (hf : HasWTaylorSeriesUpTo Ω f g k p μ) {ν : Measure E}
    (hν : (ν.restrict Ω) ≤ (μ.restrict Ω)) : E → FormalMultilinearSeries ℝ E F := by
  intro x k
  have aux := g x k
  sorry -- define a new power series, which are the weak derivatives w.r.t. ν instead

lemma mono_measure (hf : HasWTaylorSeriesUpTo Ω f g k p μ)
    {ν : Measure E} (hν : (ν.restrict Ω) ≤ (μ.restrict Ω)) :
    HasWTaylorSeriesUpTo Ω f (hf.shrink_measure hν) k p ν where
  zero_eq := sorry -- hf.zero_eq
  hasWeakDeriv m hm := by sorry -- should follow by construction
  memLp m hm := sorry -- should follow by MemLp.mono_measure and the construction

lemma mono_exponent [IsFiniteMeasure μ] (hf : HasWTaylorSeriesUpTo Ω f g k p μ)
    {p' : ℝ≥0∞} (hp' : p' ≤ p) : HasWTaylorSeriesUpTo Ω f g k p' μ where
  zero_eq := hf.zero_eq
  hasWeakDeriv := hf.hasWeakDeriv
  memLp m hm := (hf.memLp m hm).mono_exponent hp'

lemma add (hf : HasWTaylorSeriesUpTo Ω f g k p μ) (hf' : HasWTaylorSeriesUpTo Ω f' g' k p μ)
    (hg : ∀ {m : ℕ}, m < k → LocallyIntegrableOn (fun x ↦ g x m) Ω μ)
    (hg' : ∀ {m : ℕ}, m < k → LocallyIntegrableOn (fun x ↦ g' x m) Ω μ) :
    HasWTaylorSeriesUpTo Ω (f + f') (g + g') k p μ where
  zero_eq x := by simp [← hf.zero_eq, ← hf'.zero_eq]
  hasWeakDeriv m hm := (hf.hasWeakDeriv m hm).add (hf'.hasWeakDeriv m hm) (hg hm) (hg' hm)
  memLp m hm := (hf.memLp m hm).add (hf'.memLp m hm)

lemma neg (hf : HasWTaylorSeriesUpTo Ω f g k p μ) :
    HasWTaylorSeriesUpTo Ω (-f) (-g) k p μ where
  zero_eq x := by simp [← hf.zero_eq]
  hasWeakDeriv m hm := (hf.hasWeakDeriv m hm).neg
  memLp m hm := (hf.memLp m hm).neg

@[simp]
lemma _root_.hasWTaylorSeriesUpTo_neg :
    HasWTaylorSeriesUpTo Ω (-f) (-g) k p μ ↔ HasWTaylorSeriesUpTo Ω f g k p μ :=
  ⟨fun hf ↦ by simpa using hf.neg, fun hf ↦ hf.neg⟩

lemma sub (hf : HasWTaylorSeriesUpTo Ω f g k p μ) (hf' : HasWTaylorSeriesUpTo Ω f' g' k p μ)
    (hg : ∀ {m : ℕ}, m < k → LocallyIntegrableOn (fun x ↦ g x m) Ω μ)
    (hg' : ∀ {m : ℕ}, m < k → LocallyIntegrableOn (fun x ↦ g' x m) Ω μ) :
    HasWTaylorSeriesUpTo Ω (f - f') (g - g') k p μ := by
  rw [sub_eq_add_neg f f', sub_eq_add_neg g g']
  exact hf.add hf'.neg hg (fun m ↦ (hg' m).neg)

lemma smul (hf : HasWTaylorSeriesUpTo Ω f g k p μ) :
    HasWTaylorSeriesUpTo Ω (c • f) (c • g) k p μ where
  zero_eq x := by simp [← hf.zero_eq]
  hasWeakDeriv m hm := (hf.hasWeakDeriv m hm).smul
  memLp m hm := (hf.memLp m hm).const_smul c

@[simp]
lemma zero : HasWTaylorSeriesUpTo Ω 0 (0 : E → FormalMultilinearSeries ℝ E F) k p μ where
  zero_eq := by simp
  hasWeakDeriv m hm := by simpa using hasWeakDeriv_zero
  memLp m hm := by simp

end HasWTaylorSeriesUpTo

variable (Ω) in
def MemSobolev (f : E → F) (k : ℕ∞) (p : ℝ≥0∞) (μ : Measure E) : Prop :=
  ∃ g : E → FormalMultilinearSeries ℝ E F, HasWTaylorSeriesUpTo Ω f g k p μ

namespace MemSobolev

variable {c : ℝ}

section monotonicity

lemma memLp (hf : MemSobolev Ω f 0 p μ) : MemLp f p (μ.restrict Ω) := by
  obtain ⟨g, hg⟩ := hf
  have aux' : (fun x ↦ (g x 0).curry0) = f := by
    ext x
    exact hg.zero_eq x
  simp_rw [← aux']
  have := hg.memLp 0 (by simp)
  -- TODO: curry0 is linear, so this is fine here?
  sorry

lemma memSobolev_zero :
    MemSobolev Ω f 0 p μ ↔ MemLp f p (μ.restrict Ω) := by
  refine ⟨fun hf ↦ hf.memLp, fun hf ↦ ?_⟩
  let S : E → FormalMultilinearSeries ℝ E F := fun x k ↦
    if hk : k = 0 then
      sorry --f.curry0--fun _a ↦ sorry
    else 0
  use S
  refine {
    zero_eq x := sorry -- should be true by definition
    hasWeakDeriv := by
      intro m hm
      apply False.elim
      simp_all
    memLp m hm := by
      simp only [nonpos_iff_eq_zero, Nat.cast_eq_zero] at hm
      rw [hm]
      sorry -- similar to the step above: hf should imply this...
  }

/-- `MemSobolev Ω f k p μ` is monotone in `k`:
if `f ∈ W^{k,p}(Ω)` and `k' ≤ k`, then also `f ∈ W^{k',p}(Ω)`. -/
lemma mono_k {k' : ℕ∞} (hf : MemSobolev Ω f k p μ) (hk' : k' ≤ k) : MemSobolev Ω f k' p μ := by
  revert hf
  exact fun ⟨g, hg⟩ ↦ ⟨g, hg.mono hk'⟩

/-- `MemSobolev Ω f k p μ` is monotone in the measure `μ`:
if `ν ≤ μ` on `Ω`, then `MemSobolev Ω f k p μ` implies `MemSobolev Ω f k p ν`. -/
lemma mono_measure (hf : MemSobolev Ω f k p μ)
    {ν : Measure E} (hν : (ν.restrict Ω) ≤ (μ.restrict Ω)) : MemSobolev Ω f k p ν := by
  revert hf
  exact fun ⟨g, hg⟩ ↦ ⟨hg.shrink_measure hν, hg.mono_measure hν⟩

/-- If `Ω` is bounded, `MemSobolev Ω f k p μ` is monotone in `p`:
`f ∈ W^{k,p}(Ω)` and `q ≤ p`, then also `f ∈ W^{k,q}(Ω)`. -/
lemma mono_p_of_measure_lt_top [IsFiniteMeasure μ] (hf : MemSobolev Ω f k p μ)
    {p' : ℝ≥0∞} (hp' : p' ≤ p) : MemSobolev Ω f k p' μ := by
  revert hf
  exact fun ⟨g, hg⟩ ↦ ⟨g, hg.mono_exponent hp'⟩

end monotonicity

-- TODO: move to the appropriate location!
instance [hμ : IsLocallyFiniteMeasure μ] : IsLocallyFiniteMeasure (μ.restrict Ω) where
  finiteAtNhds x := by
    obtain ⟨s, hs, hmus⟩ := hμ.finiteAtNhds x
    exact ⟨s, hs, lt_of_le_of_lt (Measure.restrict_apply_le Ω s) hmus⟩

lemma add [IsLocallyFiniteMeasure μ] [hp : Fact (1 ≤ p)]
    (hf : MemSobolev Ω f k p μ) (hf' : MemSobolev Ω f' k p μ) :
    MemSobolev Ω (f + f') k p μ := by
  obtain ⟨g, hg⟩ := hf
  obtain ⟨g', hg'⟩ := hf'
  refine ⟨g + g', hg.add hg' ?_ ?_⟩
  · intro m hm
    cases m with
    | zero => exact hg.locallyIntegrableOn_zero hp.out
    | succ n => exact hg.locallyIntegrableOn_succ _ hm hp.out
  · intro m hm
    cases m with
    | zero => exact hg'.locallyIntegrableOn_zero hp.out
    | succ n => exact hg'.locallyIntegrableOn_succ _ hm hp.out

lemma neg (hf : MemSobolev Ω f k p μ) : MemSobolev Ω (-f) k p μ := by
  obtain ⟨g, hg⟩ := hf
  exact ⟨-g, hg.neg⟩

lemma sub [IsLocallyFiniteMeasure μ] [hp : Fact (1 ≤ p)]
    (hf : MemSobolev Ω f k p μ) (hf' : MemSobolev Ω f' k p μ) : MemSobolev Ω (f - f') k p μ := by
  obtain ⟨g, hg⟩ := hf
  obtain ⟨g', hg'⟩ := hf'
  refine ⟨g - g', hg.sub hg' ?_ ?_⟩
  · intro m hm
    cases m with
    | zero => exact hg.locallyIntegrableOn_zero hp.out
    | succ n => exact hg.locallyIntegrableOn_succ _ hm hp.out
  · intro m hm
    cases m with
    | zero => exact hg'.locallyIntegrableOn_zero hp.out
    | succ n => exact hg'.locallyIntegrableOn_succ _ hm hp.out

lemma smul (hf : MemSobolev Ω f k p μ) : MemSobolev Ω (c • f) k p μ := by
  obtain ⟨g, hg⟩ := hf
  exact ⟨c • g, hg.smul⟩

@[simp]
lemma zero : MemSobolev Ω (0 : E → F) k p μ := ⟨0, by simp⟩

-- TODO: probably, the hypothesis can be weakened!
lemma const (a : F) [IsFiniteMeasure μ] : MemSobolev Ω (fun _ : E ↦ a) k p μ := by
  -- TODO: better test for MemSobolev: e.g. from being Lp and the weakderiv being nice
  sorry

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
variable (Ω) in
/-- This definition is different than in (most) textbooks, since we use the `L^p`-norm of the total
derivative instead of the `L^p`-norm of partial derivatives. These definitions are equivalent
for finite dimensional `E` and `k < ∞` [argument todo]. -/
def sobolevNorm (f : E → F) (k : ℕ∞) (p : ℝ≥0∞) (μ : Measure E) : ℝ≥0∞ :=
  if h : MemSobolev Ω f k p μ then sobolevNormAux h.choose k p μ else ∞

lemma sobolevNorm_lt_top_iff : sobolevNorm Ω f k p μ < ∞ ↔ MemSobolev Ω f k p μ := by sorry

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


/- Add analogous lemmas for RepresentedBy and HasWeakDeriv-/
lemma memSobolev_congr_ae (h : f =ᵐ[μ.restrict Ω] f') :
    MemSobolev Ω f k p μ ↔ MemSobolev Ω f' k p μ := by
  sorry

lemma MemSobolev.ae_eq (h : f =ᵐ[μ.restrict Ω] f') (hf : MemSobolev Ω f k p μ) :
    MemSobolev Ω f' k p μ :=
  memSobolev_congr_ae h |>.mp hf

lemma MemSobolev.aestronglyMeasurable (hf : MemSobolev Ω f k p μ) :
  AEStronglyMeasurable f (μ.restrict Ω) := sorry

lemma MemSobolev.indicator {s : Set E} (hs : MeasurableSet s) (hf : MemSobolev Ω f k p μ) :
  MemSobolev Ω (s.indicator f) k p μ := sorry

lemma MemSobolev.restrict {s : Set E} (hs : MeasurableSet s) (hf : MemSobolev Ω f k p μ) :
  MemSobolev Ω f k p (μ.restrict s) := sorry

-- todo: move
lemma MeasureTheory.ae_eq_iff {α β : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → β} :
    f =ᵐ[μ] g ↔ μ {x | f x ≠ g x} = 0 := by
  rfl

-- todo: move
lemma Set.EqOn.ae_eq {α β : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    {f g : α → β} (h : s.EqOn f g) (h2 : μ sᶜ = 0) : f =ᵐ[μ] g :=
  Measure.mono_null (fun _x hx h2x ↦ hx (h h2x)) h2

-- todo: move
lemma Set.EqOn.ae_eq_restrict {α β : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    {f g : α → β} (h : s.EqOn f g) (hs : MeasurableSet s) : f =ᵐ[μ.restrict s] g :=
  h.ae_eq <| (Measure.restrict_apply_eq_zero' hs).mpr (by simp)

variable (Ω F) in
def Sobolev (k : ℕ∞) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] (μ : Measure E := by volume_tac)
    [IsLocallyFiniteMeasure μ] :
    AddSubgroup (E →ₘ[μ.restrict Ω] F) where
  carrier := {f | MemSobolev Ω f k p μ}
  zero_mem' := by simp [memSobolev_congr_ae AEEqFun.coeFn_zero, MemSobolev.zero]
  add_mem' {f g} hf hg := by simp [memSobolev_congr_ae (AEEqFun.coeFn_add f g), hf.add hg]
  neg_mem' {f} hf := by simp [memSobolev_congr_ae (AEEqFun.coeFn_neg f), hf.neg]

open AEEqFun

variable {g : E → F}
namespace MemSobolev

variable [IsLocallyFiniteMeasure μ] [Fact (1 ≤ p)]

-- AEStronglyMeasurable f (μ.restrict Ω)
/-- make an element of Lp from a function verifying `MemSobolev` -/
def toSobolev (f : E → F) (hf : MemSobolev Ω f k p μ) : Sobolev Ω F k p μ :=
  ⟨AEEqFun.mk f hf.aestronglyMeasurable, hf.ae_eq (coeFn_mk f hf.aestronglyMeasurable).symm⟩

theorem toSobolev_val {f : E → F} (hf : MemSobolev Ω f k p μ) :
    (toSobolev f hf).1 = AEEqFun.mk f hf.aestronglyMeasurable := rfl

theorem coeFn_toSobolev {f : E → F} (hf : MemSobolev Ω f k p μ) :
    hf.toSobolev f =ᵐ[μ.restrict Ω] f :=
  coeFn_mk f hf.aestronglyMeasurable

theorem toSobolev_congr (hf : MemSobolev Ω f k p μ) (hg : MemSobolev Ω g k p μ)
    (hfg : f =ᵐ[μ.restrict Ω] g) : hf.toSobolev f = hg.toSobolev g := by
  simp [toSobolev, hfg]

@[simp]
theorem toSobolev_eq_toSobolev_iff
    (hf : MemSobolev Ω f k p μ) (hg : MemSobolev Ω g k p μ) :
    hf.toSobolev f = hg.toSobolev g ↔ f =ᵐ[μ.restrict Ω] g := by simp [toSobolev]

@[simp]
theorem toSobolev_zero (h : MemSobolev Ω (0 : E → F) k p μ) : h.toSobolev 0 = 0 :=
  rfl

theorem toSobolev_add {f g : E → F} (hf : MemSobolev Ω f k p μ) (hg : MemSobolev Ω g k p μ) :
    (hf.add hg).toSobolev (f + g) = hf.toSobolev f + hg.toSobolev g :=
  rfl

theorem toSobolev_neg {f : E → F} (hf : MemSobolev Ω f k p μ) :
    hf.neg.toSobolev (-f) = -hf.toSobolev f :=
  rfl

theorem toSobolev_sub {f g : E → F}
    (hf : MemSobolev Ω f k p μ) (hg : MemSobolev Ω g k p μ) :
    (hf.sub hg).toSobolev (f - g) = hf.toSobolev f - hg.toSobolev g :=
  rfl

end MemSobolev

namespace Sobolev

variable [IsLocallyFiniteMeasure μ] [Fact (1 ≤ p)]

instance instCoeFun : CoeFun (Sobolev Ω F k p μ) (fun _ => E → F) :=
  ⟨fun f => ((f : E →ₘ[μ.restrict Ω] F) : E → F)⟩

@[ext high]
theorem ext {f g : Sobolev Ω F k p μ} (h : f =ᵐ[μ.restrict Ω] g) : f = g := by
  ext
  exact h

theorem mem_sobolev_iff_memSobolev {f : E →ₘ[μ.restrict Ω] F} :
    f ∈ Sobolev Ω F k p μ ↔ MemSobolev Ω f k p μ := by rfl

theorem mem_sobolev_iff_sobolevNorm_lt_top {f : E →ₘ[μ.restrict Ω] F} :
    f ∈ Sobolev Ω F k p μ ↔ sobolevNorm Ω f k p μ < ∞ := by
  rw [mem_sobolev_iff_memSobolev, sobolevNorm_lt_top_iff]

-- protected theorem antitone [IsFiniteMeasure μ] {p q : ℝ≥0∞} (hpq : p ≤ q) :
--     Sobolev Ω F k q μ ≤ Sobolev Ω F k p μ :=
--   fun f hf => (MemSobolev.mono_exponent ⟨f.aestronglyMeasurable, hf⟩ hpq).2

@[simp]
theorem coeFn_mk {f : E →ₘ[μ.restrict Ω] F} (hf : MemSobolev Ω f k p μ) :
    ((⟨f, hf⟩ : Sobolev Ω F k p μ) : E → F) = f := by
  rfl

-- not @[simp] because dsimp can prove this
theorem coe_mk {f : E →ₘ[μ.restrict Ω] F} (hf : MemSobolev Ω f k p μ) :
    ((⟨f, hf⟩ : Sobolev Ω F k p μ) : E →ₘ[μ.restrict Ω] F) = f := by
  rfl

@[simp]
theorem toSobolev_coeFn (f : Sobolev Ω F k p μ) (hf : MemSobolev Ω f k p μ) :
    hf.toSobolev f = f := by
  simp [MemSobolev.toSobolev]

theorem memSobolev (f : Sobolev Ω F k p μ) : MemSobolev Ω f k p μ :=
  f.prop

-- theorem sobolevNorm_lt_top (f : Sobolev Ω F k p μ) : sobolevNorm Ω f k p μ < ∞ :=
--   f.prop

-- @[aesop (rule_sets := [finiteness]) safe apply]
-- theorem sobolevNorm_ne_top (f : Sobolev Ω F k p μ) : sobolevNorm Ω f k p μ ≠ ∞ :=
--   (sobolevNorm_lt_top f).ne

-- @[fun_prop, measurability]
-- protected theorem stronglyMeasurable (f : Sobolev Ω F k p μ) : StronglyMeasurable f :=
--   f.val.stronglyMeasurable

-- @[fun_prop, measurability]
-- protected theorem aestronglyMeasurable (f : Sobolev Ω F k p μ) : AEStronglyMeasurable f μ :=
--   f.val.aestronglyMeasurable

-- protected theorem memSobolev (f : Sobolev Ω F k p μ) : MemSobolev Ω f k p μ :=
--   ⟨Lp.aestronglyMeasurable f, f.prop⟩

-- variable (E p μ)

-- theorem coeFn_zero : ⇑(0 : Sobolev Ω F k p μ) =ᵐ[μ.restrict Ω] 0 :=
--   AEEqFun.coeFn_zero

-- variable {E p μ}

-- theorem coeFn_neg (f : Sobolev Ω F k p μ) : ⇑(-f) =ᵐ[μ.restrict Ω] -f :=
--   AEEqFun.coeFn_neg _

-- theorem coeFn_add (f g : Sobolev Ω F k p μ) : ⇑(f + g) =ᵐ[μ.restrict Ω] f + g :=
--   AEEqFun.coeFn_add _ _

-- theorem coeFn_sub (f g : Sobolev Ω F k p μ) : ⇑(f - g) =ᵐ[μ.restrict Ω] f - g :=
--   AEEqFun.coeFn_sub _ _

-- theorem const_mem_sobolev (α) {_ : MeasurableSpace α} (μ : Measure α) (c : E) [IsFiniteMeasure μ] :
--     @AEEqFun.const α _ _ μ _ c ∈ Sobolev Ω F k p μ :=
--   (memSobolev_const c).sobolevNorm_mk_lt_top

-- instance instNorm : Norm (Sobolev Ω F k p μ) where norm f := ENNReal.toReal (sobolevNorm Ω f k p μ)

-- -- note: we need this to be defeq to the instance from `SeminormedAddGroup.toNNNorm`, so
-- -- can't use `ENNReal.toNNReal (sobolevNorm Ω f k p μ)`
-- instance instNNNorm : NNNorm (Sobolev Ω F k p μ) where nnnorm f := ⟨‖f‖, ENNReal.toReal_nonneg⟩

-- instance instDist : Dist (Sobolev Ω F k p μ) where dist f g := ‖f - g‖

-- instance instEDist : EDist (Sobolev Ω F k p μ) where edist f g := sobolevNorm (⇑f - ⇑g) p μ

-- theorem norm_def (f : Sobolev Ω F k p μ) : ‖f‖ = ENNReal.toReal (sobolevNorm Ω f k p μ) :=
--   rfl

-- theorem nnnorm_def (f : Sobolev Ω F k p μ) : ‖f‖₊ = ENNReal.toNNReal (sobolevNorm Ω f k p μ) :=
--   rfl

-- @[simp, norm_cast]
-- protected theorem coe_nnnorm (f : Sobolev Ω F k p μ) : (‖f‖₊ : ℝ) = ‖f‖ :=
--   rfl

-- @[simp]
-- theorem enorm_def (f : Sobolev Ω F k p μ) : ‖f‖ₑ = sobolevNorm Ω f k p μ :=
--   ENNReal.coe_toNNReal <| Lp.sobolevNorm_ne_top f

-- @[simp]
-- lemma norm_toSobolev (f : E → F) (hf : MemSobolev Ω f k p μ) : ‖hf.toSobolev f‖ = ENNReal.toReal (sobolevNorm Ω f k p μ) := by
--   rw [norm_def, sobolevNorm_congr_ae (MemSobolev.coeFn_toSobolev hf)]

-- @[simp]
-- theorem nnnorm_toSobolev (f : E → F) (hf : MemSobolev Ω f k p μ) :
--     ‖hf.toSobolev f‖₊ = ENNReal.toNNReal (sobolevNorm Ω f k p μ) :=
--   NNReal.eq <| norm_toSobolev f hf

-- lemma enorm_toSobolev {f : E → F} (hf : MemSobolev Ω f k p μ) : ‖hf.toSobolev f‖ₑ = sobolevNorm Ω f k p μ := by
--   simp [enorm, nnnorm_toSobolev f hf, ENNReal.coe_toNNReal hf.2.ne]

-- theorem dist_def (f g : Sobolev Ω F k p μ) : dist f g = (sobolevNorm (⇑f - ⇑g) p μ).toReal := by
--   simp_rw [dist, norm_def]
--   refine congr_arg _ ?_
--   apply sobolevNorm_congr_ae (coeFn_sub _ _)

-- theorem edist_def (f g : Sobolev Ω F k p μ) : edist f g = sobolevNorm (⇑f - ⇑g) p μ :=
--   rfl

-- protected theorem edist_dist (f g : Sobolev Ω F k p μ) : edist f g = .ofReal (dist f g) := by
--   rw [edist_def, dist_def, ← sobolevNorm_congr_ae (coeFn_sub _ _),
--     ENNReal.ofReal_toReal (sobolevNorm_ne_top (f - g))]

-- protected theorem dist_edist (f g : Sobolev Ω F k p μ) : dist f g = (edist f g).toReal :=
--   MeasureTheory.Lp.dist_def ..

-- theorem dist_eq_norm (f g : Sobolev Ω F k p μ) : dist f g = ‖f - g‖ := rfl

-- @[simp]
-- theorem edist_toSobolev_toSobolev (f g : E → F) (hf : MemSobolev Ω f k p μ) (hg : MemSobolev Ω g k p μ) :
--     edist (hf.toSobolev f) (hg.toSobolev g) = sobolevNorm (f - g) p μ := by
--   rw [edist_def]
--   exact sobolevNorm_congr_ae (hf.coeFn_toSobolev.sub hg.coeFn_toSobolev)

-- @[simp]
-- theorem edist_toSobolev_zero (f : E → F) (hf : MemSobolev Ω f k p μ) : edist (hf.toSobolev f) 0 = sobolevNorm Ω f k p μ := by
--   simpa using edist_toSobolev_toSobolev f 0 hf MemSobolev.zero

-- @[simp]
-- theorem nnnorm_zero : ‖(0 : Sobolev Ω F k p μ)‖₊ = 0 := by
--   rw [nnnorm_def]
--   change (sobolevNorm (⇑(0 : E →ₘ[μ.restrict Ω] F)) p μ).toNNReal = 0
--   simp [sobolevNorm_congr_ae AEEqFun.coeFn_zero, sobolevNorm_zero]

-- @[simp]
-- theorem norm_zero : ‖(0 : Sobolev Ω F k p μ)‖ = 0 :=
--   congr_arg ((↑) : ℝ≥0 → ℝ) nnnorm_zero

-- @[simp]
-- theorem norm_measure_zero (f : Lp E p (0 : MeasureTheory.Measure α)) : ‖f‖ = 0 := by
--   -- Squeezed for performance reasons
--   simp only [norm_def, sobolevNorm_measure_zero, ENNReal.toReal_zero]

-- @[simp] theorem norm_exponent_zero (f : Lp E 0 μ) : ‖f‖ = 0 := by
--   -- Squeezed for performance reasons
--   simp only [norm_def, sobolevNorm_exponent_zero, ENNReal.toReal_zero]

-- theorem nnnorm_eq_zero_iff {f : Sobolev Ω F k p μ} (hp : 0 < p) : ‖f‖₊ = 0 ↔ f = 0 := by
--   refine ⟨fun hf => ?_, fun hf => by simp [hf]⟩
--   rw [nnnorm_def, ENNReal.toNNReal_eq_zero_iff] at hf
--   cases hf with
--   | inl hf =>
--     rw [sobolevNorm_eq_zero_iff (Lp.aestronglyMeasurable f) hp.ne.symm] at hf
--     exact Subtype.ext (AEEqFun.ext (hf.trans AEEqFun.coeFn_zero.symm))
--   | inr hf =>
--     exact absurd hf (sobolevNorm_ne_top f)

-- theorem norm_eq_zero_iff {f : Sobolev Ω F k p μ} (hp : 0 < p) : ‖f‖ = 0 ↔ f = 0 :=
--   NNReal.coe_eq_zero.trans (nnnorm_eq_zero_iff hp)

-- theorem eq_zero_iff_ae_eq_zero {f : Sobolev Ω F k p μ} : f = 0 ↔ f =ᵐ[μ.restrict Ω] 0 := by
--   rw [← (Lp.memSobolev f).toSobolev_eq_toSobolev_iff MemSobolev.zero, MemSobolev.toSobolev_zero, toSobolev_coeFn]

-- @[simp]
-- theorem nnnorm_neg (f : Sobolev Ω F k p μ) : ‖-f‖₊ = ‖f‖₊ := by
--   rw [nnnorm_def, nnnorm_def, sobolevNorm_congr_ae (coeFn_neg _), sobolevNorm_neg]

-- @[simp]
-- theorem norm_neg (f : Sobolev Ω F k p μ) : ‖-f‖ = ‖f‖ :=
--   congr_arg ((↑) : ℝ≥0 → ℝ) (nnnorm_neg f)

-- theorem nnnorm_le_mul_nnnorm_of_ae_le_mul {c : ℝ≥0} {f : Sobolev Ω F k p μ} {g : Lp F p μ}
--     (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊) : ‖f‖₊ ≤ c * ‖g‖₊ := by
--   simp only [nnnorm_def]
--   have := sobolevNorm_le_nnreal_smul_sobolevNorm_of_ae_le_mul h p
--   rwa [← ENNReal.toNNReal_le_toNNReal, ENNReal.smul_def, smul_eq_mul, ENNReal.toNNReal_mul,
--     ENNReal.toNNReal_coe] at this
--   · finiteness
--   · exact ENNReal.mul_ne_top ENNReal.coe_ne_top (by finiteness)

-- theorem norm_le_mul_norm_of_ae_le_mul {c : ℝ} {f : Sobolev Ω F k p μ} {g : Lp F p μ}
--     (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) : ‖f‖ ≤ c * ‖g‖ := by
--   rcases le_or_gt 0 c with hc | hc
--   · lift c to ℝ≥0 using hc
--     exact NNReal.coe_le_coe.mpr (nnnorm_le_mul_nnnorm_of_ae_le_mul h)
--   · simp only [norm_def]
--     have := sobolevNorm_eq_zero_and_zero_of_ae_le_mul_neg h hc p
--     simp [this]

-- theorem norm_le_norm_of_ae_le {f : Sobolev Ω F k p μ} {g : Lp F p μ} (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
--     ‖f‖ ≤ ‖g‖ := by
--   rw [norm_def, norm_def]
--   exact ENNReal.toReal_mono (by finiteness) (sobolevNorm_mono_ae h)

-- theorem mem_sobolev_of_nnnorm_ae_le_mul {c : ℝ≥0} {f : E →ₘ[μ.restrict Ω] F} {g : Lp F p μ}
--     (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊) : f ∈ Sobolev Ω F k p μ :=
--   mem_sobolev_iff_memSobolev.2 <| MemSobolev.of_nnnorm_le_mul (Lp.memSobolev g) f.aestronglyMeasurable h

-- theorem mem_sobolev_of_ae_le_mul {c : ℝ} {f : E →ₘ[μ.restrict Ω] F} {g : Lp F p μ}
--     (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) : f ∈ Sobolev Ω F k p μ :=
--   mem_sobolev_iff_memSobolev.2 <| MemSobolev.of_le_mul (Lp.memSobolev g) f.aestronglyMeasurable h

-- theorem mem_sobolev_of_nnnorm_ae_le {f : E →ₘ[μ.restrict Ω] F} {g : Lp F p μ} (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ ‖g x‖₊) :
--     f ∈ Sobolev Ω F k p μ :=
--   mem_sobolev_iff_memSobolev.2 <| MemSobolev.of_le (Lp.memSobolev g) f.aestronglyMeasurable h

-- theorem mem_sobolev_of_ae_le {f : E →ₘ[μ.restrict Ω] F} {g : Lp F p μ} (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
--     f ∈ Sobolev Ω F k p μ :=
--   mem_sobolev_of_nnnorm_ae_le h

-- theorem mem_sobolev_of_ae_nnnorm_bound [IsFiniteMeasure μ] {f : E →ₘ[μ.restrict Ω] F} (C : ℝ≥0)
--     (hfC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) : f ∈ Sobolev Ω F k p μ :=
--   mem_sobolev_iff_memSobolev.2 <| MemSobolev.of_bound f.aestronglyMeasurable _ hfC

-- theorem mem_sobolev_of_ae_bound [IsFiniteMeasure μ] {f : E →ₘ[μ.restrict Ω] F} (C : ℝ) (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
--     f ∈ Sobolev Ω F k p μ :=
--   mem_sobolev_iff_memSobolev.2 <| MemSobolev.of_bound f.aestronglyMeasurable _ hfC

-- theorem nnnorm_le_of_ae_bound [IsFiniteMeasure μ] {f : Sobolev Ω F k p μ} {C : ℝ≥0}
--     (hfC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) : ‖f‖₊ ≤ measureUnivNNReal μ ^ p.toReal⁻¹ * C := by
--   by_cases hμ : μ = 0
--   · by_cases hp : p.toReal⁻¹ = 0
--     · simp [hp, hμ, nnnorm_def]
--     · simp [hμ, nnnorm_def]
--   rw [← ENNReal.coe_le_coe, nnnorm_def, ENNReal.coe_toNNReal (sobolevNorm_ne_top _)]
--   refine (sobolevNorm_le_of_ae_nnnorm_bound hfC).trans_eq ?_
--   rw [← coe_measureUnivNNReal μ, ← ENNReal.coe_rpow_of_ne_zero (measureUnivNNReal_pos hμ).ne',
--     ENNReal.coe_mul, mul_comm, ENNReal.smul_def, smul_eq_mul]

-- theorem norm_le_of_ae_bound [IsFiniteMeasure μ] {f : Sobolev Ω F k p μ} {C : ℝ} (hC : 0 ≤ C)
--     (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : ‖f‖ ≤ measureUnivNNReal μ ^ p.toReal⁻¹ * C := by
--   lift C to ℝ≥0 using hC
--   have := nnnorm_le_of_ae_bound hfC
--   rwa [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_rpow] at this

-- instance instNormedAddCommGroup [hp : Fact (1 ≤ p)] : NormedAddCommGroup (Sobolev Ω F k p μ) :=
--   { AddGroupNorm.toNormedAddCommGroup
--       { toFun := (norm : Sobolev Ω F k p μ → ℝ)
--         map_zero' := norm_zero
--         neg' := by simp only [norm_neg, implies_true] -- squeezed for performance reasons
--         add_le' := fun f g => by
--           suffices ‖f + g‖ₑ ≤ ‖f‖ₑ + ‖g‖ₑ by
--             -- Squeezed for performance reasons
--             simpa only [ge_iff_le, enorm, ←ENNReal.coe_add, ENNReal.coe_le_coe] using this
--           simp only [Lp.enorm_def]
--           exact (sobolevNorm_congr_ae (AEEqFun.coeFn_add _ _)).trans_le
--             (sobolevNorm_add_le (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _) hp.out)
--         eq_zero_of_map_eq_zero' := fun _ =>
--           (norm_eq_zero_iff <| zero_lt_one.trans_le hp.1).1 } with
--     edist := edist
--     edist_dist := Lp.edist_dist }

end Sobolev

/-
To do:
1. Basic lemmas (closure under `+`, `•`, ...)                   basically done
2. define Sobolev spaces
2'. relate MemSobolev and finite Sobolev norm                   TODO
3. [Adams, Th 3.3] prove Banach space
4. monotonicity in `k` and (if `Ω` is bounded) in `p`.          basically done; μ could be added
4'. relate W^{0,p} and L^p                                      TODO!
5. [Adams, Cor 3.4] C^k functions are contained in W^{k, p}
6. [Adams, Th 3.6] separable, uniform convexity
7. [Adams, Th 3.15-3.17] density of smooth functions in W^{k, p}
8. [Adams, Ch 4] Sobolev embedding theorem
-/
