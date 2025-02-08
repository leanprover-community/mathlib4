import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Order.CompletePartialOrder

open ENNReal

class ENNReal.HolderTriple (r : semiOutParam ℝ≥0∞) (p q : ℝ≥0∞) : Prop where
  one_div_add_eq : 1 / r = 1 / p + 1 / q

lemma ENNReal.HolderTriple.eq {p q r : ℝ≥0∞} [ENNReal.HolderTriple r p q] :
    1 / r = 1 / p + 1 / q :=
  one_div_add_eq

instance : HolderTriple 1 2 2 where
  one_div_add_eq := by
    rw [← two_mul, mul_div, mul_one, div_one, ENNReal.div_self]
    all_goals norm_num

/- This instance causes a trivial loop, but this is exactly the kind of loop that
Lean should be able to detect and avoid. -/
instance {p q r : ℝ≥0∞} [hpqr : HolderTriple r p q] : HolderTriple r q p where
  one_div_add_eq := add_comm (1 / p) (1 / q) ▸ hpqr.eq

instance {p : ℝ≥0∞} : HolderTriple p p ∞ where
  one_div_add_eq := by simp

instance {p : ℝ≥0∞} : HolderTriple 0 p 0 where
  one_div_add_eq := by simp

noncomputable section

namespace MeasureTheory
namespace Lp

section NormedRing

variable {α R : Type*} {m : MeasurableSpace α} [NormedRing R]
    {p q r : ℝ≥0∞} {μ : Measure α} [hpqr : HolderTriple r p q]

-- should this be a `HSMul` instance instead? We could then get `SMulCommClass` and `IsScalarTower`
-- instances.
/-- Heterogeneous multiplication of `MeasureTheory.Lp` functions. -/
instance : HMul (Lp R p μ) (Lp R q μ) (Lp R r μ) where
  hMul f g := (Lp.memℒp g).mul (Lp.memℒp f) hpqr.eq |>.toLp (f * g)

lemma mul_def {f : Lp R p μ} {g : Lp R q μ} :
    f * g = ((Lp.memℒp g).mul (Lp.memℒp f) hpqr.eq).toLp (⇑f * ⇑g) :=
  rfl

lemma coeFn_mul (f : Lp R p μ) (g : Lp R q μ) :
    (f * g : Lp R r μ) =ᵐ[μ] f * g := by
  rw [mul_def]
  exact MeasureTheory.Memℒp.coeFn_toLp _

protected lemma norm_mul_le (f : Lp R p μ) (g : Lp R q μ) :
    ‖f * g‖ ≤ ‖f‖ * ‖g‖ := by
  simp only [Lp.norm_def, ← ENNReal.toReal_mul, coeFn_mul]
  refine ENNReal.toReal_mono ?_ ?_
  · exact ENNReal.mul_ne_top (eLpNorm_ne_top f) (eLpNorm_ne_top g)
  · rw [eLpNorm_congr_ae (coeFn_mul f g), ← smul_eq_mul]
    exact MeasureTheory.eLpNorm_smul_le_mul_eLpNorm (Lp.aestronglyMeasurable g)
      (Lp.aestronglyMeasurable f) hpqr.eq

protected lemma mul_add (f₁ f₂ : Lp R p μ) (g : Lp R q μ) :
    (f₁ + f₂) * g = f₁ * g + f₂ * g := by
  simp only [mul_def, ← Memℒp.toLp_add]
  apply Memℒp.toLp_congr
  filter_upwards [AEEqFun.coeFn_add f₁.val f₂.val] with x hx
  simp [hx, add_mul]

protected lemma add_mul (f : Lp R p μ) (g₁ g₂  : Lp R q μ) :
    f * (g₁ + g₂) = f * g₁ + f * g₂ := by
  simp only [mul_def, ← Memℒp.toLp_add]
  apply Memℒp.toLp_congr _ _ ?_
  filter_upwards [AEEqFun.coeFn_add g₁.val g₂.val] with x hx
  simp [hx, mul_add]

protected lemma mul_comm {R : Type*} [NormedCommRing R] (f : Lp R p μ) (g : Lp R q μ) :
    f * g = g * f := by
  ext1
  -- the specification of `r` below is necessary because it is a `semiOutParam`.
  filter_upwards [coeFn_mul (r := r) f g, coeFn_mul (r := r) g f] with x hx₁ hx₂
  simp [hx₁, hx₂, mul_comm]

end NormedRing

section LinearMap

variable {𝕜 α A : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
    {p q r : ℝ≥0∞} [HolderTriple r p q]

protected lemma smul_mul_assoc (c : 𝕜) (f : Lp A p μ) (g : Lp A q μ) :
    (c • f) * g = c • (f * g) := by
  simp only [mul_def, ← Memℒp.toLp_const_smul]
  apply Memℒp.toLp_congr
  filter_upwards [Lp.coeFn_smul c f] with x hx
  simp [hx]

protected lemma mul_smul_comm (c : 𝕜) (f : Lp A p μ) (g : Lp A q μ) :
    f * (c • g) = c • (f * g) := by
  simp only [mul_def, ← Memℒp.toLp_const_smul]
  apply Memℒp.toLp_congr
  filter_upwards [Lp.coeFn_smul c g] with x hx
  simp [hx]

/-- Heterogeneous multiplication of `MeasureTheory.Lp` functions as a bilinear map. -/
def lmul : Lp A p μ →ₗ[𝕜] Lp A q μ →ₗ[𝕜] Lp A r μ :=
  LinearMap.mk₂ 𝕜 (· * ·) Lp.mul_add Lp.smul_mul_assoc Lp.add_mul Lp.mul_smul_comm

end LinearMap

section ContinuousLinearMap

variable {𝕜 α A : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [NontriviallyNormedField 𝕜][NormedRing A] [NormedAlgebra 𝕜 A]
    {p q r : ℝ≥0∞} [HolderTriple r p q] [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]

variable (𝕜 A μ p q r) in
/-- Heterogeneous multiplication of `MeasureTheory.Lp` functions as a continuous bilinear map. -/
def Lmul : Lp A p μ →L[𝕜] Lp A q μ →L[𝕜] Lp A r μ :=
  LinearMap.mkContinuous₂ lmul 1 fun f g ↦
    one_mul (_ : ℝ) ▸ MeasureTheory.Lp.norm_mul_le f g

-- this is necessary :(
set_option maxSynthPendingDepth 2 in
lemma norm_Lmul : ‖Lmul 𝕜 A μ p q r‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

end ContinuousLinearMap

section Dual

variable {𝕜 α A : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
    {p q : ℝ≥0∞} [HolderTriple 1 p q] [Fact (1 ≤ p)] [Fact (1 ≤ q)]

variable (𝕜 A μ p q) in
/-- The integral of the product of Hölder conjugate functions.

When `A := 𝕜`, this is the natural map `Lp 𝕜 q μ → NormedSpace.Dual 𝕜 (Lp 𝕜 r μ)`.
See `MeasureTheory.Lp.toDual`. -/
def integralLMul [NormedSpace ℝ A] [SMulCommClass ℝ 𝕜 A] [CompleteSpace A] :
    Lp A p μ →L[𝕜] Lp A q μ →L[𝕜] A :=
  (L1.integralCLM' 𝕜 |>.postcomp <| Lp A q μ) ∘L (Lmul 𝕜 A μ p q 1)

variable (𝕜 μ p q) in
/-- The natural map from `Lp 𝕜 q μ` to `NormedSpace.Dual 𝕜 (Lp 𝕜 r μ)` for  a Hölder conjugate pair
`q r : ℝ≥0∞` given by integrating the product of the two functions. This is a special case of
`MeasureTheory.Lp.integralLMul`. -/
def toDualCLM (𝕜 : Type*) [RCLike 𝕜]:
    Lp 𝕜 p μ →L[𝕜] NormedSpace.Dual 𝕜 (Lp 𝕜 q μ) :=
  integralLMul 𝕜 𝕜 μ p q

end Dual

end Lp
end MeasureTheory
