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

end HasWeakDeriv

variable (Ω) in
/-- `f` has "weak taylor series" g, which are all L^p
k currently can be `∞`. Do we want that? -/
structure HasWTaylorSeriesUpTo (f : E → F) (g : E → FormalMultilinearSeries ℝ E F)
    (k : ℕ∞) (p : ℝ≥0∞) (μ : Measure E) : Prop where
  zero_eq : ∀ x, (g x 0).curry0 = f x
  hasWeakDeriv : ∀ m : ℕ, m < k → HasWeakDeriv Ω (g · m) (g · m.succ |>.curryLeft) μ
  memLp : ∀ m : ℕ, m ≤ k → MemLp (g · m) p μ

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
