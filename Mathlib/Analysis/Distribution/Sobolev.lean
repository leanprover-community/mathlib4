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
  {Ω : Opens E} /- probably should have type `Set E` -/
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedSpace 𝕜 F'] [SMulCommClass ℝ 𝕜 F']
    -- [NormedSpace 𝕂 F]
  {n : ℕ∞} {μ : Measure E}

namespace Distribution

-- def IsRepresentedBy (f : 𝓓'(Ω, F)) (g : E → F) (μ : Measure E) : Prop :=
--   LocallyIntegrableOn g Ω μ ∧ f = ofFun Ω g μ

def IsRegular (f : 𝓓'(Ω, F)) (μ : Measure E) : Prop :=
  ∃ (g : E → F), LocallyIntegrableOn g Ω μ ∧ f = ofFun Ω g μ

open Classical in
def out (f : 𝓓'(Ω, F)) (μ : Measure E) : E → F :=
  if h : IsRegular f μ then
    Ω.1.indicator h.choose
  else
    0

lemma ofFun_inj {g g' : E → F} (h : ofFun Ω g μ = ofFun Ω g' μ) : g =ᵐ[μ.restrict Ω] g' := sorry

structure MemLp' (f : 𝓓'(Ω, F)) (g : E → F) (p : ℝ≥0∞) (μ : Measure E) : Prop where
  isRegular : IsRegular f μ
  memLp : MeasureTheory.MemLp (f.out μ) p μ


structure MemLp (f : 𝓓'(Ω, F)) (p : ℝ≥0∞) (μ : Measure E) : Prop where
  isRegular : IsRegular f μ
  memLp : MeasureTheory.MemLp (f.out μ) p μ

end Distribution
open Distribution

variable [FiniteDimensional ℝ E]

variable (Ω) in
def weakDeriv (f : E → F) (μ : Measure E) : 𝓓'(Ω, E →L[ℝ] F) :=
  fderivCLM (ofFun Ω f μ)

/- `f` has a weak derivative that is L^p -/
structure IsW1 (f : E → F) (p : ℝ≥0∞) (μ : Measure E) : Prop where
  memLp : MemLp f p μ
  memLp_weakDeriv : (weakDeriv Ω f μ).MemLp p μ


/-
Maybe:
package all the derivatives together in the arguments.
-/
