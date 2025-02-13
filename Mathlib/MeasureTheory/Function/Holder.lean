/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Order.CompletePartialOrder

/-! # Hölder triples and actions on `MeasureTheory.Lp` spaces

This file defines a new class: `ENNReal.HolderTriple` which takes arguments `p q r : ℝ≥0∞`,
with `r` marked as a `semiOutParam`, and states that `p⁻¹ + q⁻¹ = r⁻¹`. This is exactly the
condition for which **Hölder's inequality** is valid (see `MeasureTheory.Memℒp.smul`).
This allows us to declare a heterogeneous scalar multiplication (`HSMul`) instance on
`MeasureTheory.Lp` spaces.

More generally, given a continuous bilinear map `B : E →L[𝕜] F →L[𝕜] G`, we define an
associated map `MeasureTheory.Lp.ofBilin : Lp E p μ → Lp F q μ → Lp G r μ` where `p q r` are
a Hölder triple. We bundle this into a bilinear map `ContinuousLinearMap.holderₗ` and a continuous
bilinear map `ContinuousLinearMap.holderL`.

When `p q : ℝ≥0∞` are Hölder conjugate (i.e., `HolderTriple p q 1`), we can construct the
natural continuous linear map `Lp.toDualCLM : Lp (Dual 𝕜 E) p μ →L[𝕜] Dual 𝕜 (Lp E q μ)` given by
`fun φ f ↦ ∫ x, (φ x) (f x) ∂μ`.
 -/

open ENNReal

/-! ### Hölder triples -/

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

/-! ### Induced bilinear maps -/

section Bilinear

open scoped NNReal

variable {α 𝕜 E F G : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {p q r : ENNReal} [hpqr : HolderTriple p q r] [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]

theorem _root_.MeasureTheory.Memℒp.of_bilin (b : E → F → G) (c : ℝ≥0)
    {f : α → E} {g : α → F} (hf : Memℒp f p μ) (hg : Memℒp g q μ)
    (h : AEStronglyMeasurable (fun x ↦ b (f x) (g x)) μ)
    (hb : ∀ᵐ (x : α) ∂μ, ‖b (f x) (g x)‖₊ ≤ c * ‖f x‖₊ * ‖g x‖₊) :
    Memℒp (fun x ↦ b (f x) (g x)) r μ :=
  .intro h <| (eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hf.1 hg.1 b c hb hpqr.div_eq').trans_lt <|
    by have := hf.2; have := hg.2; finiteness

variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]
    (B : E →L[𝕜] F →L[𝕜] G)

/-- The map between `MeasuryTheory.Lp` spaces satisfying the `ENNReal.HolderTriple`
condition induced by a continuous bilinear map on the underlying spaces. -/
def ofBilin (f : Lp E p μ) (g : Lp F q μ) : Lp G r μ :=
  Memℒp.toLp (fun x ↦ B (f x) (g x)) <| by
    refine .of_bilin (B · ·) ‖B‖₊ (Lp.memℒp f) (Lp.memℒp g) ?_ <|
      .of_forall fun _ ↦ B.le_opNorm₂ _ _
    exact B.aestronglyMeasurable_comp₂ (Lp.memℒp f).1 (Lp.memℒp g).1

lemma coeFn_ofBilin (f : Lp E p μ) (g : Lp F q μ) :
    (ofBilin B f g : Lp G r μ) =ᵐ[μ] fun x ↦ B (f x) (g x) := by
  rw [ofBilin]
  exact Memℒp.coeFn_toLp _

lemma nnnorm_ofBilin_apply_apply_le (f : Lp E p μ) (g : Lp F q μ) :
    ‖(ofBilin B f g : Lp G r μ)‖₊ ≤ ‖B‖₊ * ‖f‖₊ * ‖g‖₊ := by
  simp_rw [← ENNReal.coe_le_coe, ENNReal.coe_mul, ← enorm_eq_nnnorm, Lp.enorm_def]
  apply eLpNorm_congr_ae (coeFn_ofBilin B f g) |>.trans_le
  exact eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (Lp.memℒp f).1 (Lp.memℒp g).1 (B · ·) ‖B‖₊
    (.of_forall fun _ ↦ B.le_opNorm₂ _ _) hpqr.div_eq'

lemma norm_ofBilin_apply_apply_le (f : Lp E p μ) (g : Lp F q μ) :
    ‖(ofBilin B f g : Lp G r μ)‖ ≤ ‖B‖ * ‖f‖ * ‖g‖ :=
  NNReal.coe_le_coe.mpr <| nnnorm_ofBilin_apply_apply_le B f g

lemma ofBilin_add_left (f₁ f₂ : Lp E p μ) (g : Lp F q μ) :
    (ofBilin B (f₁ + f₂) g : Lp G r μ) = ofBilin B f₁ g + ofBilin B f₂ g := by
  simp only [ofBilin, ← Memℒp.toLp_add]
  apply Memℒp.toLp_congr
  filter_upwards [AEEqFun.coeFn_add f₁.val f₂.val] with x hx
  simp [hx]

lemma ofBilin_add_right (f : Lp E p μ) (g₁ g₂ : Lp F q μ) :
    (ofBilin B f (g₁ + g₂) : Lp G r μ) = ofBilin B f g₁ + ofBilin B f g₂ := by
  simp only [ofBilin, ← Memℒp.toLp_add]
  apply Memℒp.toLp_congr
  filter_upwards [AEEqFun.coeFn_add g₁.val g₂.val] with x hx
  simp [hx]

lemma ofBilin_smul_left (c : 𝕜) (f : Lp E p μ) (g : Lp F q μ) :
    (ofBilin B (c • f) g : Lp G r μ) = c • ofBilin B f g := by
  simp only [ofBilin, ← Memℒp.toLp_const_smul]
  apply Memℒp.toLp_congr
  filter_upwards [Lp.coeFn_smul c f] with x hx
  simp [hx]

lemma ofBilin_smul_right (c : 𝕜) (f : Lp E p μ) (g : Lp F q μ) :
    (ofBilin B f (c • g) : Lp G r μ) = c • ofBilin B f g := by
  simp only [ofBilin, ← Memℒp.toLp_const_smul]
  apply Memℒp.toLp_congr
  filter_upwards [Lp.coeFn_smul c g] with x hx
  simp [hx]

variable (μ p q r) in
/-- `MeasureTheory.Lp.ofBilin` as a bilinear map. -/
@[simps! apply_apply]
def _root_.ContinuousLinearMap.holderₗ : Lp E p μ →ₗ[𝕜] Lp F q μ →ₗ[𝕜] Lp G r μ :=
  .mk₂ 𝕜 (ofBilin B) (ofBilin_add_left B) (ofBilin_smul_left B)
    (ofBilin_add_right B) (ofBilin_smul_right B)

variable [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]

variable (μ p q r) in
/-- `MeasureTheory.Lp.ofBilin` as a continuous bilinear map. -/
@[simps! apply_apply]
def _root_.ContinuousLinearMap.holderL : Lp E p μ →L[𝕜] Lp F q μ →L[𝕜] Lp G r μ :=
  LinearMap.mkContinuous₂ (B.holderₗ μ p q r) ‖B‖ (norm_ofBilin_apply_apply_le B)

lemma _root_.ContinuousLinearMap.norm_holderL_le : ‖(B.holderL μ p q r)‖ ≤ ‖B‖ :=
  LinearMap.mkContinuous₂_norm_le _ (norm_nonneg B) _

end Bilinear

section Dual

open NormedSpace

variable {α 𝕜 E : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {p q : ENNReal} [hpqr : HolderTriple p q 1] [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable (𝕜 μ p q E) in
@[simps!]
def toDualCLM : Lp (Dual 𝕜 E) p μ →L[𝕜] Dual 𝕜 (Lp E q μ) :=
  (L1.integralCLM' 𝕜 |>.postcomp <| Lp E q μ) ∘L ((inclusionInDoubleDual 𝕜 E).flip.holderL μ p q 1)

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

end Module

end SMul

end Lp
end MeasureTheory
