import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Order.CompletePartialOrder

open ENNReal

namespace ENNReal

/-- A class stating that `p q r : ℝ≥0∞` satisfy `p⁻¹ + q⁻¹ = r⁻¹`.
This is exactly the condition for which **Hölder's inequality** is valid
(see `MeasureTheory.Memℒp.smul`).

When `r := 1`, one generally says that `p q` are **Hölder conjugate**.

This class exists so that we can define a heterogeneous multiplication
on `MeasureTheory.Lp`, and this is why `r` must be marked as a
`semiOutParam`. We don't mark it as an `outParam` because this would
prevent Lean from using `HolderTriple p q r` and `HolderTriple p q r'`
within a single proof, as may be occasionally convenient. -/
class HolderTriple (p q : ℝ≥0∞) (r : semiOutParam ℝ≥0∞) : Prop where
  inv_add_inv : p⁻¹ + q⁻¹ = r⁻¹

namespace HolderTriple

lemma eq {p q r : ℝ≥0∞} [ENNReal.HolderTriple p q r] :
    p⁻¹ + q⁻¹ = r⁻¹ :=
  inv_add_inv

lemma div_eq {p q r : ℝ≥0∞} [ENNReal.HolderTriple p q r] :
    1 / p + 1 / q = 1 / r := by
  simpa using eq

lemma div_eq' {p q r : ℝ≥0∞} [ENNReal.HolderTriple p q r] :
    1 / r = 1 / p + 1 / q :=
  div_eq.symm

lemma inv_inv_add_inv (p q r : ℝ≥0∞) [ENNReal.HolderTriple p q r] :
    (p⁻¹ + q⁻¹)⁻¹ = r := by
  simp [@eq p q r]

/-- This is not marked as an instance so that Lean doesn't always find this one
and a more canonical value of `r` can be used. -/
lemma of (p q : ℝ≥0∞) : HolderTriple p q (p⁻¹ + q⁻¹)⁻¹ where
  inv_add_inv := inv_inv _ |>.symm

#exit

instance instTwoTwoOne : HolderTriple 2 2 1 where
  inv_add_inv := by
    rw [← two_mul, ENNReal.mul_inv_cancel]
    all_goals norm_num

/- This instance causes a trivial loop, but this is exactly the kind of loop that
Lean should be able to detect and avoid. -/
instance symm {p q r : ℝ≥0∞} [hpqr : HolderTriple p q r] : HolderTriple q p r where
  inv_add_inv := add_comm p⁻¹ q⁻¹ ▸ hpqr.eq

instance instInfty {p : ℝ≥0∞} : HolderTriple p ∞ p where
  inv_add_inv := by simp

instance instZero {p : ℝ≥0∞} : HolderTriple p 0 0 where
  inv_add_inv := by simp

end HolderTriple
end ENNReal

noncomputable section

namespace MeasureTheory
namespace Lp

section SMul

variable {α 𝕜' 𝕜 E : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {p q r : ℝ≥0∞} [hpqr : HolderTriple p q r]

section MulActionWithZero

variable [NormedRing 𝕜] [NormedAddCommGroup E] [MulActionWithZero 𝕜 E] [BoundedSMul 𝕜 E]

/-- Heterogeneous scalar multiplication of `MeasureTheory.Lp` functions by `MeasureTheory.Lp`
functions when the exponents satisfy `ENNReal.HolderTriple p q r`. -/
instance : HSMul (Lp 𝕜 p μ) (Lp E q μ) (Lp E r μ) where
  hSMul f g := (Lp.memℒp g).smul (Lp.memℒp f) hpqr.div_eq' |>.toLp (⇑f • ⇑g)

lemma smul_def {f : Lp 𝕜 p μ} {g : Lp E q μ} :
    f • g = ((Lp.memℒp g).smul (Lp.memℒp f) hpqr.div_eq').toLp (⇑f • ⇑g) :=
  rfl

lemma coeFn_lp_smul (f : Lp 𝕜 p μ) (g : Lp E q μ) :
    (f • g : Lp E r μ) =ᵐ[μ] ⇑f • g := by
  rw [smul_def]
  exact Memℒp.coeFn_toLp _

protected lemma norm_smul_le (f : Lp 𝕜 p μ) (g : Lp E q μ) :
    ‖f • g‖ ≤ ‖f‖ * ‖g‖ := by
  simp only [Lp.norm_def, ← ENNReal.toReal_mul, coeFn_lp_smul]
  refine ENNReal.toReal_mono ?_ ?_
  · exact ENNReal.mul_ne_top (eLpNorm_ne_top f) (eLpNorm_ne_top g)
  · rw [eLpNorm_congr_ae (coeFn_lp_smul f g)]
    exact eLpNorm_smul_le_mul_eLpNorm (Lp.aestronglyMeasurable g)
      (Lp.aestronglyMeasurable f) hpqr.div_eq'

end MulActionWithZero

section Module

variable [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E] [BoundedSMul 𝕜 E]

protected lemma smul_add (f₁ f₂ : Lp 𝕜 p μ) (g : Lp E q μ) :
    (f₁ + f₂) • g = f₁ • g + f₂ • g := by
  simp only [smul_def, ← Memℒp.toLp_add]
  apply Memℒp.toLp_congr
  filter_upwards [AEEqFun.coeFn_add f₁.val f₂.val] with x hx
  simp [hx, add_smul]

protected lemma add_smul (f : Lp 𝕜 p μ) (g₁ g₂  : Lp E q μ) :
    f • (g₁ + g₂) = f • g₁ + f • g₂ := by
  simp only [smul_def, ← Memℒp.toLp_add]
  apply Memℒp.toLp_congr _ _ ?_
  filter_upwards [AEEqFun.coeFn_add g₁.val g₂.val] with x hx
  simp [hx, smul_add]

variable (E q) in
@[simp]
protected lemma smul_zero (f : Lp 𝕜 p μ) :
    f • (0 : Lp E q μ) = (0 : Lp E r μ) := by
  convert Memℒp.zero.toLp_zero
  apply Memℒp.toLp_congr _ _ ?_
  filter_upwards [Lp.coeFn_zero E q μ] with x hx
  rw [Pi.smul_apply', hx]
  simp

variable (𝕜 p) in
@[simp]
protected lemma zero_smul (f : Lp E q μ) :
    (0 : Lp 𝕜 p μ) • f = (0 : Lp E r μ) := by
  convert Memℒp.zero.toLp_zero
  apply Memℒp.toLp_congr _ _ ?_
  filter_upwards [Lp.coeFn_zero 𝕜 p μ] with x hx
  rw [Pi.smul_apply', hx]
  simp

@[simp]
protected lemma smul_neg (f : Lp 𝕜 p μ) (g : Lp E q μ) :
    f • -g = -(f • g) := by
  simp [eq_neg_iff_add_eq_zero, ← Lp.add_smul]

@[simp]
protected lemma neg_smul (f : Lp 𝕜 p μ) (g : Lp E q μ) :
    -f • g = -(f • g) := by
  simp [eq_neg_iff_add_eq_zero, ← Lp.smul_add]

protected lemma neg_smul_neg (f : Lp 𝕜 p μ) (g : Lp E q μ) :
    -f • -g = f • g := by
  simp

variable [NormedRing 𝕜'] [Module 𝕜' E] [Module 𝕜' 𝕜] [BoundedSMul 𝕜' E] [BoundedSMul 𝕜' 𝕜]

protected lemma smul_smul_assoc [IsScalarTower 𝕜' 𝕜 E]
    (c : 𝕜') (f : Lp 𝕜 p μ) (g : Lp E q μ) :
    (c • f) • g = c • (f • g) := by
  simp only [smul_def, ← Memℒp.toLp_const_smul]
  apply Memℒp.toLp_congr
  filter_upwards [Lp.coeFn_smul c f] with x hx
  simp [- smul_eq_mul, hx]

protected lemma smul_comm [SMulCommClass 𝕜' 𝕜 E]
    (c : 𝕜') (f : Lp 𝕜 p μ) (g : Lp E q μ) :
    c • f • g = f • c • g := by
  simp only [smul_def, ← Memℒp.toLp_const_smul]
  apply Memℒp.toLp_congr
  filter_upwards [Lp.coeFn_smul c f, Lp.coeFn_smul c g] with x hfx hgx
  simp [smul_comm, hfx, hgx]

-- we have no instance `One (Lp 𝕜 p μ)` under the assumption
-- variable [IsFiniteMeasure μ]


end Module

section LinearMap

variable {𝕜 𝕜' α E : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {p q r : ℝ≥0∞} [HolderTriple p q r]
    [NormedField 𝕜'] [NormedRing 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜' 𝕜] [Module 𝕜 E] [BoundedSMul 𝕜 E]
    [NormedSpace 𝕜' E] [IsScalarTower 𝕜' 𝕜 E] [SMulCommClass 𝕜' 𝕜 E]

variable (𝕜' 𝕜 E μ p q r) in
/-- Heterogeneous multiplication of `MeasureTheory.Lp` functions as a bilinear map. -/
def lsmul : Lp 𝕜 p μ →ₗ[𝕜'] Lp E q μ →ₗ[𝕜'] Lp E r μ :=
  .mk₂ 𝕜' (· • ·) Lp.smul_add Lp.smul_smul_assoc Lp.add_smul <| (Lp.smul_comm · · · |>.symm)

end LinearMap

section ContinuousLinearMap

variable {𝕜 𝕜' α E : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {p q r : ℝ≥0∞} [HolderTriple p q r]
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
    [NontriviallyNormedField 𝕜'] [NormedRing 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜' 𝕜] [Module 𝕜 E] [BoundedSMul 𝕜 E]
    [NormedSpace 𝕜' E] [IsScalarTower 𝕜' 𝕜 E] [SMulCommClass 𝕜' 𝕜 E]

variable (𝕜' 𝕜 E μ p q r) in
/-- Heterogeneous multiplication of `MeasureTheory.Lp` functions as a continuous bilinear map. -/
def Lsmul : Lp 𝕜 p μ →L[𝕜'] Lp E q μ →L[𝕜'] Lp E r μ :=
  LinearMap.mkContinuous₂ (lsmul 𝕜 𝕜' E μ p q r) 1 fun f g ↦
    one_mul (_ : ℝ) ▸ MeasureTheory.Lp.norm_smul_le f g

lemma norm_Lsmul : ‖Lsmul 𝕜 𝕜' E μ p q r‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

end ContinuousLinearMap

section Dual

open NormedSpace

variable {𝕜 α E : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {p q : ℝ≥0∞} [HolderTriple p q 1] [Fact (1 ≤ p)] [Fact (1 ≤ q)]

def dualMap : Lp (Dual 𝕜 E) p μ →L[𝕜] Lp E q μ →L[𝕜] Lp 𝕜 1 μ := sorry


#exit
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

#exit
variable (𝕜 μ p q) in
/-- The natural map from `Lp 𝕜 q μ` to `NormedSpace.Dual 𝕜 (Lp 𝕜 r μ)` for  a Hölder conjugate pair
`q r : ℝ≥0∞` given by integrating the product of the two functions. This is a special case of
`MeasureTheory.Lp.integralLMul`. -/
def toDualCLM (𝕜 : Type*) [RCLike 𝕜]:
    Lp 𝕜 p μ →L[𝕜] NormedSpace.Dual 𝕜 (Lp 𝕜 q μ) :=
  integralLMul 𝕜 𝕜 μ p q

end Dual
#exit
end SMul
section NormedRing

variable {α R : Type*} {m : MeasurableSpace α} [NormedRing R]
    {p q r : ℝ≥0∞} {μ : Measure α} [hpqr : HolderTriple p q r]

/-- Heterogeneous scalar multiplication of `MeasureTheory.Lp` functions. -/
instance : HMul (Lp R p μ) (Lp R q μ) (Lp R r μ) where
  hMul f g := (Lp.memℒp g).mul (Lp.memℒp f) (hpqr.div_eq (r := r)).symm |>.toLp (f * g)

lemma mul_def {f : Lp R p μ} {g : Lp R q μ} :
    f * g = ((Lp.memℒp g).mul (Lp.memℒp f) (hpqr.div_eq (r := r)).symm).toLp (⇑f * ⇑g) :=
  rfl

#exit
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
      (Lp.aestronglyMeasurable f) (by simpa using hpqr.eq.symm)

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
/-- Heterogeneous multiplication of `MeasureTheory.Lp` functions as a bilinear map. -/
def lmul : Lp A p μ →ₗ[𝕜] Lp A q μ →ₗ[𝕜] Lp A r μ :=
  LinearMap.mk₂ 𝕜 (· * ·) Lp.mul_add Lp.smul_mul_assoc Lp.add_mul Lp.mul_smul_comm

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
    [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
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
