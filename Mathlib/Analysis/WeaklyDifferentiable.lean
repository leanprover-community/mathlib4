import Mathlib.Analysis.Calculus.ContDiff
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Marginal

open scoped Classical BigOperators Topology ENNReal
open Filter MeasureTheory NormedSpace

noncomputable section

variable? [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [BorelSpace W] => [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W]
  [BorelSpace W]
variable {U : Set V}

attribute [local instance] fact_one_le_two_ennreal
-- attribute [local instance]
/-!
ideally: define a sequence of Hilbert spaces recursively: H 0 = ℝ, H (n + 1) = Hilbert-Schmidt
maps from V to H n.  Then  SobolevSpaceAux n will be the PiLp of (fun i : Fin n ↦ H i)
-/

instance (i : Bool) :
  NormedAddCommGroup <|
    Bool.rec (V →₂[volume.restrict U] ℝ : Type _) (V →₂[volume.restrict U] /-Dual ℝ-/ V) i := by
  cases i <;> infer_instance

instance (i : Bool) :
  InnerProductSpace ℝ <|
    Bool.rec (V →₂[volume.restrict U] ℝ : Type _) (V →₂[volume.restrict U] V) i := by
  cases i <;> dsimp <;> infer_instance

instance (i : Bool) :
  CompleteSpace <|
    Bool.rec (V →₂[volume.restrict U] ℝ : Type _) (V →₂[volume.restrict U] V) i := by
  cases i <;> dsimp <;> infer_instance

variable (U)
def SobolevSpaceAux : Type _ :=
  PiLp 2 <| Bool.rec (V →₂[volume.restrict U] ℝ : Type _) (V →₂[volume.restrict U] V)
  -- deriving NormedAddCommGroup

instance : NormedAddCommGroup (SobolevSpaceAux U) := by
  dsimp only [SobolevSpaceAux]
  infer_instance

instance : InnerProductSpace ℝ (SobolevSpaceAux U) := by
  dsimp only [SobolevSpaceAux]
  infer_instance

instance : CompleteSpace (SobolevSpaceAux U) := by
  dsimp only [SobolevSpaceAux]
  exact Pi.complete .. -- todo: infer_instance

instance [MeasurableSpace α] [TopologicalSpace α] {μ : Measure α} [IsLocallyFiniteMeasure μ] :
    IsLocallyFiniteMeasure (μ.restrict A) :=
  sorry

variable {U}
namespace SobolevSpaceAux

def pr0 : SobolevSpaceAux U →L[ℝ] V →₂[volume.restrict U] ℝ where
  toLinearMap := LinearMap.proj false ∘ₗ (WithLp.linearEquiv _ _ _).toLinearMap
  cont := sorry

def pr1 : SobolevSpaceAux U →L[ℝ] V →₂[volume.restrict U] V where
  toLinearMap := LinearMap.proj true ∘ₗ (WithLp.linearEquiv _ _ _).toLinearMap
  cont := sorry

end SobolevSpaceAux
/- These conditions can be weakened to ϕ bounded in sup-norm and continuous -/
def HasCompactSupport.toLp {μ : Measure V} [IsLocallyFiniteMeasure μ] {ϕ : V → W}
    (h1 : Continuous ϕ) (h2 : HasCompactSupport ϕ) :
    V →₂[μ] W :=
Memℒp.toLp ϕ sorry

def AAux (ϕ : V → ℝ) (u : SobolevSpaceAux U) : V :=
  ∫ x in U, SobolevSpaceAux.pr0 (U := U) u x • (InnerProductSpace.toDual ℝ _).symm (fderiv ℝ ϕ x) +
  ∫ x in U, ϕ x • SobolevSpaceAux.pr1 (U := U) u x

def A {ϕ : V → ℝ} (h1 : ContDiff ℝ ⊤ ϕ) (h2 : HasCompactSupport ϕ) :
    SobolevSpaceAux U →L[ℝ] V where
  toFun := AAux ϕ
  map_add' := sorry
  map_smul' := sorry
  cont := sorry

variable (U)
def SobolevSpace : Submodule ℝ (SobolevSpaceAux U) :=
  ⨅ (ϕ : V → ℝ), ⨅ (h1 : ContDiff ℝ ⊤ ϕ), ⨅ (h2 : HasCompactSupport ϕ), LinearMap.ker (A h1 h2)

variable {U}
lemma closed_sobolevSpace : IsClosed (SobolevSpace U : Set (SobolevSpaceAux U)) := sorry

instance : NormedAddCommGroup (SobolevSpace U) := by infer_instance

instance : InnerProductSpace ℝ (SobolevSpace U) := by infer_instance

instance : CompleteSpace (SobolevSpace U) :=
  closed_sobolevSpace.completeSpace_coe




-- def A {ϕ : V → ℝ} (h1 : ContDiff ℝ ⊤ ϕ) (h2 : HasCompactSupport ϕ) : SobolevSpaceAux U →L[ℝ] V :=
--   _ + --InnerProductSpace.toDual ℝ _ _ ∘L SobolevSpaceAux.pr0 +
--   ∫ x in U, ϕ x • u --InnerProductSpace.toDual ℝ _ (h2.toLp h1.continuous) ∘L SobolevSpaceAux.pr1
