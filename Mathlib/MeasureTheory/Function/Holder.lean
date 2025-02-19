/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Order.CompletePartialOrder

/-! # Continuous bilinear maps on `MeasureTheory.Lp` spaces

Given a continuous bilinear map `B : E →L[𝕜] F →L[𝕜] G`, we define an associated map
`ContinuousLinearMap.holder : Lp E p μ → Lp F q μ → Lp G r μ` where `p q r` are a Hölder triple.
We bundle this into a bilinear map `ContinuousLinearMap.holderₗ` and a continuous
bilinear map `ContinuousLinearMap.holderL` under some additional assumptions.

We also declare a heterogeneous scalar multiplication (`HSMul`) instance on `MeasureTheory.Lp`
spaces. Although this could use the `ContinuousLinearMap.holder` construction above, we opt not to
do so in order to minimize the necessary type class assumptions.

When `p q : ℝ≥0∞` are Hölder conjugate (i.e., `HolderConjugate p q`), we also construct the
natural map `MeasureTheory.Lp.toDualCLM : Lp (Dual 𝕜 E) p μ →L[𝕜] Dual 𝕜 (Lp E q μ)` given by
`fun φ f ↦ ∫ x, (φ x) (f x) ∂μ`.
 -/

open ENNReal MeasureTheory Lp
open scoped NNReal

noncomputable section

/-! ### Induced bilinear maps -/

section Bilinear

variable {α 𝕜 E F G : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {p q r : ENNReal} [hpqr : HolderTriple p q r] [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]
    (B : E →L[𝕜] F →L[𝕜] G)

namespace ContinuousLinearMap

/-- The map between `MeasuryTheory.Lp` spaces satisfying `ENNReal.HolderTriple`
induced by a continuous bilinear map on the underlying spaces. -/
def holder (f : Lp E p μ) (g : Lp F q μ) : Lp G r μ :=
  Memℒp.toLp (fun x ↦ B (f x) (g x)) <| by
    refine .of_bilin (B · ·) ‖B‖₊ (Lp.memℒp f) (Lp.memℒp g) ?_ <|
      .of_forall fun _ ↦ B.le_opNorm₂ _ _
    exact B.aestronglyMeasurable_comp₂ (Lp.memℒp f).1 (Lp.memℒp g).1

lemma coeFn_holder (f : Lp E p μ) (g : Lp F q μ) :
    (B.holder f g : Lp G r μ) =ᵐ[μ] fun x ↦ B (f x) (g x) := by
  rw [holder]
  exact Memℒp.coeFn_toLp _

lemma nnnorm_holder_apply_apply_le (f : Lp E p μ) (g : Lp F q μ) :
    ‖(B.holder f g : Lp G r μ)‖₊ ≤ ‖B‖₊ * ‖f‖₊ * ‖g‖₊ := by
  simp_rw [← ENNReal.coe_le_coe, ENNReal.coe_mul, ← enorm_eq_nnnorm, Lp.enorm_def]
  apply eLpNorm_congr_ae (coeFn_holder B f g) |>.trans_le
  exact eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (Lp.memℒp f).1 (Lp.memℒp g).1 (B · ·) ‖B‖₊
    (.of_forall fun _ ↦ B.le_opNorm₂ _ _)

lemma norm_holder_apply_apply_le (f : Lp E p μ) (g : Lp F q μ) :
    ‖(B.holder f g : Lp G r μ)‖ ≤ ‖B‖ * ‖f‖ * ‖g‖ :=
  NNReal.coe_le_coe.mpr <| nnnorm_holder_apply_apply_le B f g

lemma holder_add_left (f₁ f₂ : Lp E p μ) (g : Lp F q μ) :
    (B.holder (f₁ + f₂) g : Lp G r μ) = B.holder f₁ g + B.holder f₂ g := by
  simp only [holder, ← Memℒp.toLp_add]
  apply Memℒp.toLp_congr
  filter_upwards [AEEqFun.coeFn_add f₁.val f₂.val] with x hx
  simp [hx]

lemma holder_add_right (f : Lp E p μ) (g₁ g₂ : Lp F q μ) :
    (B.holder f (g₁ + g₂) : Lp G r μ) = B.holder f g₁ + B.holder f g₂ := by
  simp only [holder, ← Memℒp.toLp_add]
  apply Memℒp.toLp_congr
  filter_upwards [AEEqFun.coeFn_add g₁.val g₂.val] with x hx
  simp [hx]

lemma holder_smul_left (c : 𝕜) (f : Lp E p μ) (g : Lp F q μ) :
    (B.holder (c • f) g : Lp G r μ) = c • B.holder f g := by
  simp only [holder, ← Memℒp.toLp_const_smul]
  apply Memℒp.toLp_congr
  filter_upwards [Lp.coeFn_smul c f] with x hx
  simp [hx]

lemma holder_smul_right (c : 𝕜) (f : Lp E p μ) (g : Lp F q μ) :
    (B.holder f (c • g) : Lp G r μ) = c • B.holder f g := by
  simp only [holder, ← Memℒp.toLp_const_smul]
  apply Memℒp.toLp_congr
  filter_upwards [Lp.coeFn_smul c g] with x hx
  simp [hx]

variable (μ p q r) in
/-- `MeasureTheory.Lp.holder` as a bilinear map. -/
@[simps! apply_apply]
def _root_.ContinuousLinearMap.holderₗ : Lp E p μ →ₗ[𝕜] Lp F q μ →ₗ[𝕜] Lp G r μ :=
  .mk₂ 𝕜 B.holder B.holder_add_left B.holder_smul_left
    B.holder_add_right B.holder_smul_right

variable [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]

variable (μ p q r) in
/-- `MeasureTheory.Lp.holder` as a continuous bilinear map. -/
@[simps! apply_apply]
def _root_.ContinuousLinearMap.holderL : Lp E p μ →L[𝕜] Lp F q μ →L[𝕜] Lp G r μ :=
  LinearMap.mkContinuous₂ (B.holderₗ μ p q r) ‖B‖ (norm_holder_apply_apply_le B)

lemma _root_.ContinuousLinearMap.norm_holderL_le : ‖(B.holderL μ p q r)‖ ≤ ‖B‖ :=
  LinearMap.mkContinuous₂_norm_le _ (norm_nonneg B) _

end ContinuousLinearMap

end Bilinear

namespace MeasureTheory
namespace Lp

section Dual

open NormedSpace

variable {α 𝕜 E : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {p q : ℝ≥0∞} [hpqr : HolderTriple p q 1] [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The natural continuous linear map `Lp (Dual 𝕜 E) p μ` into the dual of `Lp E q μ` given by
integrating the evaluation of the linear functionals at the corresponding points. That is,
`fun (φ : Lp (Dual 𝕜 E) p μ) (f : Lp E q μ) ↦ ∫ x, φ x (f x) ∂μ`. -/
@[simps!]
def MeasureTheory.Lp.toDualCLM : Lp (Dual 𝕜 E) p μ →L[𝕜] Dual 𝕜 (Lp E q μ) :=
  (L1.integralCLM' 𝕜 |>.postcomp <| Lp E q μ) ∘L ((inclusionInDoubleDual 𝕜 E).flip.holderL μ p q 1)

lemma MeasureTheory.Lp.toDualCLM_eq_integral (φ : Lp (Dual 𝕜 E) p μ) (f : Lp E q μ) :
    toDualCLM φ f = ∫ x, φ x (f x) ∂μ := by
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  show L1.integralCLM _ = _
  rw [← L1.integral_def, L1.integral_eq_integral]
  exact integral_congr_ae <| (inclusionInDoubleDual 𝕜 E).flip.coeFn_holder _ _

end Dual


/-! ### Heterogeneous scalar multiplication

While the previous section is *nominally* more general than this one, and indeed, we could
use the constructions of the previous section to define the scalar multiplication herein,
we would lose some slight generality as we would need to require that `𝕜` is a nontrivially
normed field everywhere. Moreover, it would only simplify a few proofs.
-/

section SMul

variable {α 𝕜' 𝕜 E : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {p q r : ℝ≥0∞} [hpqr : HolderTriple p q r]

section MulActionWithZero

variable [NormedRing 𝕜] [NormedAddCommGroup E] [MulActionWithZero 𝕜 E] [BoundedSMul 𝕜 E]

/-- Heterogeneous scalar multiplication of `MeasureTheory.Lp` functions by `MeasureTheory.Lp`
functions when the exponents satisfy `ENNReal.HolderTriple p q r`. -/
instance : HSMul (Lp 𝕜 p μ) (Lp E q μ) (Lp E r μ) where
  hSMul f g := (Lp.memℒp g).smul (Lp.memℒp f) |>.toLp (⇑f • ⇑g)

lemma smul_def {f : Lp 𝕜 p μ} {g : Lp E q μ} :
    f • g = ((Lp.memℒp g).smul (Lp.memℒp f)).toLp (⇑f • ⇑g) :=
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
    exact eLpNorm_smul_le_mul_eLpNorm (Lp.aestronglyMeasurable g) (Lp.aestronglyMeasurable f)

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

end Module

end SMul

end Lp
end MeasureTheory
