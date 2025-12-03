module

-- public import Mathlib.Analysis.Distribution.WeakDeriv
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

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
  {n : ℕ∞} {μ : Measure E}

namespace Distribution

def IsRepresentedBy (f : 𝓓'(Ω, F)) (g : E → F) (μ : Measure E) : Prop :=
  LocallyIntegrableOn g Ω μ ∧ f = ofFun Ω g μ

def IsRegular (f : 𝓓'(Ω, F)) (μ : Measure E) : Prop :=
  ∃ (g : E → F), LocallyIntegrableOn g Ω μ ∧ f = ofFun Ω g μ

namespace IsRegular

variable {f g : 𝓓'(Ω, F)}

lemma add (hf : IsRegular f μ) (hg : IsRegular g μ) : IsRegular (f + g) μ := by
  obtain ⟨f₀, hf₀, hf⟩ := hf
  obtain ⟨g₀, hg₀, hg⟩ := hg
  refine ⟨f₀ + g₀, hf₀.add hg₀, ?_⟩
  rw [ofFun_add hf₀ hg₀, hf, hg]

lemma smul (hf : IsRegular f μ) (c : ℝ) : IsRegular (c • f) μ := by
  obtain ⟨f₀, hf₀, hf⟩ := hf
  refine ⟨c • f₀, hf₀.smul c, ?_⟩
  rw [ofFun_smul, hf]

end IsRegular

open Classical in
/-- A representative of a regular distribution, chosen so that it is 0 outside `Ω`.
Has junk-value `0` for non-regular distributions. -/
def out (f : 𝓓'(Ω, F)) (μ : Measure E) : E → F :=
  if h : IsRegular f μ then
    Ω.1.indicator h.choose
  else
    0

lemma ofFun_inj {g g' : E → F} (h : ofFun Ω g μ = ofFun Ω g' μ) : g =ᵐ[μ.restrict Ω] g' := sorry

structure MemLp (f : 𝓓'(Ω, F)) (p : ℝ≥0∞) (μ : Measure E) : Prop where
  isRegular : IsRegular f μ
  memLp : MeasureTheory.MemLp (f.out μ) p μ

end Distribution
open Distribution

variable [FiniteDimensional ℝ E]

variable (Ω) in
def weakDeriv (f : E → F) (μ : Measure E) : 𝓓'(Ω, E →L[ℝ] F) :=
  fderivCLM (ofFun Ω f μ)

-- not so nice
variable (Ω) in
/- `f` is in W^{1,p}, i.e. `f` is L^p with a weak derivative that is L^p -/
structure MemSobolev1 (f : E → F) (p : ℝ≥0∞) (μ : Measure E) : Prop where
  memLp : MemLp f p (μ.restrict Ω)
  memLp_weakDeriv : (weakDeriv Ω f μ).MemLp p μ

-- not so nice
variable (Ω) in
/- `f` is in W^{k,p} -/
-- issue with universes
def MemSobolev (f : E → F) (k : ℕ) (p : ℝ≥0∞) (μ : Measure E) : Prop :=
  match k with
  | 0     => MemLp f p (μ.restrict Ω)
  | 1     => MemSobolev1 Ω f p μ
  | k + 2 => MemLp f p μ ∧ DifferentiableOn ℝ f Ω ∧ ∀ v, MemSobolev (lineDeriv ℝ f v) (k + 1) p μ

/- this doesn't work easily -/
-- variable (Ω) in
-- def MemSobolev' (f : E → F) (k : ℕ) (p : ℝ≥0∞) (μ : Measure E) : Prop :=
--   match k with
--   | 0     => MemLp f p (μ.restrict Ω)
--   | k + 1 => MemLp f p μ ∧ (weakDeriv Ω f μ).IsRegular μ ∧ MemSobolev' ((weakDeriv Ω f μ).out μ) p μ

/-- `g` represents distribution `f` and is in `L^p`. -/
structure Distribution.MemLpWith (f : 𝓓'(Ω, F)) (g : E → F) (p : ℝ≥0∞) (μ : Measure E) : Prop where
  isRegular : IsRepresentedBy f g μ
  memLp : MeasureTheory.MemLp g p μ

variable (Ω) in
/-- `f` is in `W^{1, p}` and has weak derivative represented by `g`. -/
structure MemSobolev1With (f : E → F) (g : E → E →L[ℝ] F) (p : ℝ≥0∞) (μ : Measure E) : Prop where
  memLp : MemLp f p (μ.restrict Ω)
  memLp_weakDeriv : (weakDeriv Ω f μ).MemLpWith g p μ

variable (Ω) in
/-- `f` has weak derivative represented by `g`. -/
def HasWeakDeriv (f : E → F) (g : E → E →L[ℝ] F) (μ : Measure E) : Prop :=
  IsRepresentedBy (weakDeriv Ω f μ) g μ

#check HasFTaylorSeriesUpTo
#check FormalMultilinearSeries

variable (Ω) in
/-- `f` has "weak taylor series" g
k currently can be `∞`. Do we want that? -/
structure MemSobolevWith (f : E → F) (g : E → FormalMultilinearSeries ℝ E F) (k : ℕ∞) (p : ℝ≥0∞)
    (μ : Measure E) : Prop where
  zero_eq : ∀ x, (g x 0).curry0 = f x
  fderiv : ∀ m : ℕ, m < k → MemSobolev1With Ω (fun y => g y m) (fun x ↦ (g x m.succ).curryLeft) p μ
  -- cont : ∀ m : ℕ, m ≤ n → Continuous fun x => g x m

variable (Ω) in
/-- `f` has "weak taylor series" g, which are all L^p
k currently can be `∞`. Do we want that? -/
structure MemSobolevWith' (f : E → F) (g : E → FormalMultilinearSeries ℝ E F) (k : ℕ∞) (p : ℝ≥0∞)
    (μ : Measure E) : Prop where
  zero_eq : ∀ x, (g x 0).curry0 = f x
  hasWeakDeriv : ∀ m : ℕ, m < k → HasWeakDeriv Ω (g · m) (g · m.succ |>.curryLeft) μ
  memLp : ∀ m : ℕ, m ≤ k → MemLp (g · m) p μ

variable (Ω) in
def MemSobolev'' (f : E → F) (k : ℕ) (p : ℝ≥0∞) (μ : Measure E) : Prop :=
  ∃ g : E → FormalMultilinearSeries ℝ E F, MemSobolevWith' Ω f g k p μ

/- to try: define MemSobolev on distributions. -/


namespace Distribution

def MemSobolev (f : 𝓓'(Ω, F)) (k : ℕ∞) (p : ℝ≥0∞) (μ : Measure E) : Prop :=
  ∀ m : ℕ, m ≤ k → (iteratedFDerivCLM (E := E) (F := F) m f).MemLp p μ

variable (F Ω) in
@[nolint unusedArguments]
def FormalDistributionSeries := ∀ n : ℕ, 𝓓'(Ω, E[×n]→L[ℝ] F)

def comp (f : 𝓓'(Ω, F)) (g : F →L[ℝ] F') : 𝓓'(Ω, F') := sorry
def curry0 (f : 𝓓'(Ω, E [×0]→L[ℝ] F)) : 𝓓'(Ω, F) :=
  f.comp (continuousMultilinearCurryFin0 ℝ E F |>.toContinuousLinearEquiv.toContinuousLinearMap)
def curryLeft {n} (f : 𝓓'(Ω, E [×(n + 1)]→L[ℝ] F)) : 𝓓'(Ω, E →L[ℝ] E [×n]→L[ℝ] F) :=
  f.comp
    (continuousMultilinearCurryLeftEquiv ℝ _ F |>.toContinuousLinearEquiv.toContinuousLinearMap)

-- not so nice
structure MemSobolevWith' (f : 𝓓'(Ω, F)) (g : FormalDistributionSeries Ω F) (k : ℕ∞) (p : ℝ≥0∞)
    (μ : Measure E) : Prop where
  zero_eq : (g 0).curry0 = f
  hasWeakDeriv : ∀ m : ℕ, m < k → fderivCLM (g m) = (g m.succ).curryLeft
  memLp : ∀ m : ℕ, m ≤ k → (g m).MemLp p μ

-- not so nice
structure MemSobolevWith'' (f : 𝓓'(Ω, F)) (g : FormalDistributionSeries Ω F) (k : ℕ∞) (p : ℝ≥0∞)
    (μ : Measure E) : Prop where
  hasWeakDeriv : ∀ m : ℕ, m ≤ k → iteratedFDerivCLM (E := E) (F := F) m f = g m
  memLp : ∀ m : ℕ, m ≤ k → (g m).MemLp p μ

end Distribution






/-
Maybe:
package all the derivatives together in the arguments.
-/
