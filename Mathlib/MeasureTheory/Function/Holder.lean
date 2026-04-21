/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Continuous bilinear maps on `MeasureTheory.Lp` spaces

Given a continuous bilinear map `B : E →L[𝕜] F →L[𝕜] G`, we define an associated map
`ContinuousLinearMap.holder : Lp E p μ → Lp F q μ → Lp G r μ` where `p q r` are a Hölder triple.
We bundle this into a bilinear map `ContinuousLinearMap.holderₗ` and a continuous
bilinear map `ContinuousLinearMap.holderL` under some additional assumptions.

We also declare a heterogeneous scalar multiplication (`HSMul`) instance on `MeasureTheory.Lp`
spaces. Although this could use the `ContinuousLinearMap.holder` construction above, we opt not to
do so in order to minimize the necessary type class assumptions.

When `p q : ℝ≥0∞` are Hölder conjugate (i.e., `HolderConjugate p q`), we also construct the
natural map `ContinuousLinearMap.lpPairing : Lp E p μ →L[𝕜] Lp F q μ →L[𝕜] G` given by
`fun f g ↦ ∫ x, B (f x) (g x) ∂μ`. When `B := (NormedSpace.inclusionInDoubleDual 𝕜 E).flip`, this
is the natural map `Lp (StrongDual 𝕜 E) p μ →L[𝕜] StrongDual 𝕜 (Lp E q μ)`.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

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

variable (r) in
theorem memLp_of_bilin {f : α → E} {g : α → F} (hf : MemLp f p μ) (hg : MemLp g q μ) :
    MemLp (fun x ↦ B (f x) (g x)) r μ :=
  MeasureTheory.MemLp.of_bilin (r := r) (B · ·) ‖B‖₊ hf hg
    (B.aestronglyMeasurable_comp₂ hf.1 hg.1) (.of_forall fun _ ↦ B.le_opNorm₂ _ _)

theorem integrable_of_bilin_of_bdd_left {f : α → E} {g : α → F} (C : ℝ)
    (hf1 : AEStronglyMeasurable f μ) (hf2 : ∀ᵐ a ∂μ, ‖f a‖ ≤ C) (hg : Integrable g μ) :
    Integrable (fun x ↦ B (f x) (g x)) μ :=
  memLp_one_iff_integrable.1 <| B.memLp_of_bilin 1 (memLp_top_of_bound hf1 C hf2)
    (memLp_one_iff_integrable.2 hg)

theorem integrable_of_bilin_of_bdd_right {f : α → E} {g : α → F} (C : ℝ)
    (hf : Integrable f μ) (hg1 : AEStronglyMeasurable g μ) (hg2 : ∀ᵐ a ∂μ, ‖g a‖ ≤ C) :
    Integrable (fun x ↦ B (f x) (g x)) μ :=
  B.flip.integrable_of_bilin_of_bdd_left C hg1 hg2 hf

variable (r) in
/-- The map between `MeasureTheory.Lp` spaces satisfying `ENNReal.HolderTriple`
induced by a continuous bilinear map on the underlying spaces. -/
def holder (f : Lp E p μ) (g : Lp F q μ) : Lp G r μ :=
  (B.memLp_of_bilin r (Lp.memLp f) (Lp.memLp g)).toLp

lemma coeFn_holder (f : Lp E p μ) (g : Lp F q μ) :
    B.holder r f g =ᵐ[μ] fun x ↦ B (f x) (g x) := by
  rw [holder]
  exact MemLp.coeFn_toLp _

lemma nnnorm_holder_apply_apply_le (f : Lp E p μ) (g : Lp F q μ) :
    ‖B.holder r f g‖₊ ≤ ‖B‖₊ * ‖f‖₊ * ‖g‖₊ := by
  simp_rw [← ENNReal.coe_le_coe, ENNReal.coe_mul, ← enorm_eq_nnnorm, Lp.enorm_def]
  apply eLpNorm_congr_ae (coeFn_holder B f g) |>.trans_le
  exact eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (Lp.memLp f).1 (Lp.memLp g).1 (B · ·) ‖B‖₊
    (.of_forall fun _ ↦ B.le_opNorm₂ _ _)

lemma norm_holder_apply_apply_le (f : Lp E p μ) (g : Lp F q μ) :
    ‖B.holder r f g‖ ≤ ‖B‖ * ‖f‖ * ‖g‖ :=
  NNReal.coe_le_coe.mpr <| nnnorm_holder_apply_apply_le B f g

lemma holder_add_left (f₁ f₂ : Lp E p μ) (g : Lp F q μ) :
    B.holder r (f₁ + f₂) g = B.holder r f₁ g + B.holder r f₂ g := by
  simp only [holder, ← MemLp.toLp_add]
  apply MemLp.toLp_congr
  filter_upwards [AEEqFun.coeFn_add f₁.val f₂.val] with x hx
  simp [hx]

lemma holder_add_right (f : Lp E p μ) (g₁ g₂ : Lp F q μ) :
    B.holder r f (g₁ + g₂) = B.holder r f g₁ + B.holder r f g₂ := by
  simp only [holder, ← MemLp.toLp_add]
  apply MemLp.toLp_congr
  filter_upwards [AEEqFun.coeFn_add g₁.val g₂.val] with x hx
  simp [hx]

lemma holder_smul_left (c : 𝕜) (f : Lp E p μ) (g : Lp F q μ) :
    B.holder r (c • f) g = c • B.holder r f g := by
  simp only [holder, ← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  filter_upwards [Lp.coeFn_smul c f] with x hx
  simp [hx]

lemma holder_smul_right (c : 𝕜) (f : Lp E p μ) (g : Lp F q μ) :
    B.holder r f (c • g) = c • B.holder r f g := by
  simp only [holder, ← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  filter_upwards [Lp.coeFn_smul c g] with x hx
  simp [hx]

variable (μ p q r) in
/-- `MeasureTheory.Lp.holder` as a bilinear map. -/
@[simps! apply_apply]
def holderₗ : Lp E p μ →ₗ[𝕜] Lp F q μ →ₗ[𝕜] Lp G r μ :=
  .mk₂ 𝕜 (B.holder r) B.holder_add_left B.holder_smul_left
    B.holder_add_right B.holder_smul_right

variable [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]

variable (μ p q r) in
/-- `MeasureTheory.Lp.holder` as a continuous bilinear map. -/
@[simps! apply_apply]
def holderL : Lp E p μ →L[𝕜] Lp F q μ →L[𝕜] Lp G r μ :=
  LinearMap.mkContinuous₂ (B.holderₗ μ p q r) ‖B‖ (norm_holder_apply_apply_le B)

lemma norm_holderL_le : ‖(B.holderL μ p q r)‖ ≤ ‖B‖ :=
  LinearMap.mkContinuous₂_norm_le _ (norm_nonneg B) _

variable [HolderConjugate p q] [NormedSpace ℝ G] [SMulCommClass ℝ 𝕜 G] [CompleteSpace G]

variable (μ p q) in
/-- The natural pairing between `Lp E p μ` and `Lp F q μ` (for Hölder conjugate `p q : ℝ≥0∞`) with
values in a space `G` induced by a bilinear map `B : E →L[𝕜] F →L[𝕜] G`.

This is given by `∫ x, B (f x) (g x) ∂μ`.

In the special case when `B := (NormedSpace.inclusionInDoubleDual 𝕜 E).flip`, which is
definitionally the same as `B := ContinuousLinearMap.id 𝕜 (E →L[𝕜] 𝕜)`, this is the
natural map `Lp (StrongDual 𝕜 E) p μ →L[𝕜] StrongDual 𝕜 (Lp E q μ)`. -/
def lpPairing (B : E →L[𝕜] F →L[𝕜] G) : Lp E p μ →L[𝕜] Lp F q μ →L[𝕜] G :=
  (L1.integralCLM' 𝕜 |>.postcomp <| Lp F q μ) ∘L (B.holderL μ p q 1)

lemma lpPairing_eq_integral (f : Lp E p μ) (g : Lp F q μ) :
    B.lpPairing μ p q f g = ∫ x, B (f x) (g x) ∂μ := by
  simpa [lpPairing, ← L1.integral_eq', L1.integral_eq_integral] using
    integral_congr_ae <| B.coeFn_holder _ _

end ContinuousLinearMap

end Bilinear

namespace MeasureTheory
namespace Lp

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

variable [NormedRing 𝕜] [NormedAddCommGroup E] [MulActionWithZero 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- Heterogeneous scalar multiplication of `MeasureTheory.Lp` functions by `MeasureTheory.Lp`
functions when the exponents satisfy `ENNReal.HolderTriple p q r`. -/
instance : HSMul (Lp 𝕜 p μ) (Lp E q μ) (Lp E r μ) where
  hSMul f g := (Lp.memLp g).smul (Lp.memLp f) |>.toLp (⇑f • ⇑g)

lemma smul_def {f : Lp 𝕜 p μ} {g : Lp E q μ} :
    f • g = ((Lp.memLp g).smul (Lp.memLp f)).toLp (⇑f • ⇑g) :=
  rfl

lemma coeFn_lpSMul (f : Lp 𝕜 p μ) (g : Lp E q μ) :
    (f • g : Lp E r μ) =ᵐ[μ] ⇑f • g := by
  rw [smul_def]
  exact MemLp.coeFn_toLp _

protected lemma norm_smul_le (f : Lp 𝕜 p μ) (g : Lp E q μ) :
    ‖f • g‖ ≤ ‖f‖ * ‖g‖ := by
  simp only [Lp.norm_def, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (by finiteness) ?_
  rw [eLpNorm_congr_ae (coeFn_lpSMul f g)]
  exact eLpNorm_smul_le_mul_eLpNorm (Lp.aestronglyMeasurable g) (Lp.aestronglyMeasurable f)

end MulActionWithZero

section Module

variable [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

protected lemma smul_add (f₁ f₂ : Lp 𝕜 p μ) (g : Lp E q μ) :
    (f₁ + f₂) • g = f₁ • g + f₂ • g := by
  simp only [smul_def, ← MemLp.toLp_add]
  apply MemLp.toLp_congr
  filter_upwards [AEEqFun.coeFn_add f₁.val f₂.val] with x hx
  simp [hx, add_smul]

protected lemma add_smul (f : Lp 𝕜 p μ) (g₁ g₂ : Lp E q μ) :
    f • (g₁ + g₂) = f • g₁ + f • g₂ := by
  simp only [smul_def, ← MemLp.toLp_add]
  apply MemLp.toLp_congr _ _ ?_
  filter_upwards [AEEqFun.coeFn_add g₁.val g₂.val] with x hx
  simp [hx, smul_add]

variable (E q) in
@[simp]
protected lemma smul_zero (f : Lp 𝕜 p μ) :
    f • (0 : Lp E q μ) = (0 : Lp E r μ) := by
  convert MemLp.zero (ε := E) |>.toLp_zero
  apply MemLp.toLp_congr _ _ ?_
  filter_upwards [Lp.coeFn_zero E q μ] with x hx
  rw [Pi.smul_apply', hx]
  simp

variable (𝕜 p) in
@[simp]
protected lemma zero_smul (f : Lp E q μ) :
    (0 : Lp 𝕜 p μ) • f = (0 : Lp E r μ) := by
  convert MemLp.zero (ε := E) |>.toLp_zero
  apply MemLp.toLp_congr _ _ ?_
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

variable [NormedRing 𝕜'] [Module 𝕜' E] [Module 𝕜' 𝕜] [IsBoundedSMul 𝕜' E] [IsBoundedSMul 𝕜' 𝕜]

protected lemma smul_assoc [IsScalarTower 𝕜' 𝕜 E]
    (c : 𝕜') (f : Lp 𝕜 p μ) (g : Lp E q μ) :
    (c • f) • g = c • (f • g) := by
  simp only [smul_def, ← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  filter_upwards [Lp.coeFn_smul c f] with x hx
  simp [-smul_eq_mul, hx]

protected lemma smul_comm [SMulCommClass 𝕜' 𝕜 E]
    (c : 𝕜') (f : Lp 𝕜 p μ) (g : Lp E q μ) :
    c • f • g = f • c • g := by
  simp only [smul_def, ← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  filter_upwards [Lp.coeFn_smul c f, Lp.coeFn_smul c g] with x hfx hgx
  simp [smul_comm, hgx]

end Module

end SMul

end Lp
end MeasureTheory
