/-
Copyright (c) 2026 Tjeerd Jan Heeringa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tjeerd Jan Heeringa
-/
module

public import Mathlib.Analysis.InnerProductSpace.Reproducing.Operations

/-!
# Operations on RKHS
This file implements ..

## main definitions
..

## Implemenation notes
The `toSubmodule` stuff below likely shouldn't be in a separate namespace, but it is now to now
conflict with the duplicate (for the time this is a WIP) definition in the higher-level file.

-/

public noncomputable section

open InnerProductSpace Submodule RKHS

namespace RKHS

namespace toSubmodule

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable (H' : Type*) [NormedAddCommGroup H'] [InnerProductSpace 𝕜 H'] [CompleteSpace H']

variable (K K' : Matrix X X (V →L[𝕜] V))
variable [Fact K.PosSemidef] [Fact K'.PosSemidef]

/-- The submodule of `X→V` by embedding `OfKernel K` into `X→V`. -/
def toSubmodule : Submodule 𝕜 (X → V) := (coeCLM 𝕜 (H := OfKernel K)).range

variable {K K'} in
lemma toSubmodule_congr (h : K = K') : toSubmodule K = toSubmodule K' := by
  subst h; rfl

lemma toSubmodule_add : toSubmodule (K + K') = toSubmodule K + toSubmodule K' := by
  unfold toSubmodule
  calc
    (coeCLM 𝕜 (H := OfKernel (K + K'))).range
        = (coeCLM 𝕜 (H := Add.sumSpace (OfKernel K) (OfKernel K'))).range := by
      apply le_antisymm
      · rintro _ ⟨f, rfl⟩
        exact ⟨Add.OfKernelAddEquiv K K' f, by simp⟩
      · rintro _ ⟨g, rfl⟩
        obtain ⟨f, rfl⟩ := (Add.OfKernelAddEquiv K K').surjective g
        exact ⟨f, by simp⟩
    _ = (Add.generator (OfKernel K) (OfKernel K')).range := by
      change ((Add.generator (OfKernel K) (OfKernel K')).ker.liftQL _ (le_refl _)).range = _
      exact Submodule.range_liftQ _ _ _
    _ = ((coeCLM 𝕜)).range + ((coeCLM 𝕜)).range := Add.range_generator (OfKernel K) (OfKernel K')

lemma toSubmodule_smul (c : ℝ) (hc : c ≠ 0) : toSubmodule ((c : 𝕜) ^ 2 • K) = toSubmodule K := by
  have h : (‖(c : 𝕜)‖ : 𝕜) ^ 2 • K = (c : 𝕜) ^ 2 • K := by
    norm_cast
    simp
  rw [← toSubmodule_congr h]
  unfold toSubmodule
  calc
    (coeCLM 𝕜 (H := OfKernel ((‖(c : 𝕜)‖ : 𝕜) ^ 2 • K))).range
        = (coeCLM 𝕜 (H := SMul.smulSpace (OfKernel K) (c : 𝕜))).range := by
      apply le_antisymm
      · rintro _ ⟨f, rfl⟩
        exact ⟨SMul.OfKernelSMulEquiv K (c : 𝕜) f, by simp⟩
      · rintro _ ⟨g, rfl⟩
        obtain ⟨f, rfl⟩ := (SMul.OfKernelSMulEquiv K (c : 𝕜)).surjective g
        exact ⟨f, by simp⟩
    _ = (SMul.generator (OfKernel K) (c : 𝕜)).range := by
      change ((SMul.generator (OfKernel K) (c : 𝕜)).ker.liftQL _ (le_refl _)).range = _
      exact Submodule.range_liftQ _ _ _
    _ = (coeCLM 𝕜 (H := OfKernel K)).range := by
      apply le_antisymm
      · rintro _ ⟨x, rfl⟩
        exact ⟨(c : 𝕜) • x, by
          ext
          simp [SMul.generator_apply]⟩
      · rintro _ ⟨x, rfl⟩
        exact ⟨(c : 𝕜)⁻¹ • x, by
          ext
          simp [SMul.generator_apply, map_smul, inv_smul_smul₀ (a := (c : 𝕜)) (by simp [hc]) (x _)]⟩

open ComplexOrder in
lemma Matrix.PosSemidef.eq_zero_of_neg {M : Matrix X X (V →L[𝕜] V)}
    (hM : M.PosSemidef) (hM' : (-M).PosSemidef) : M = 0 := by
  classical
  ext i j
  have hdiag i : M i i = 0 :=
    le_antisymm (by simpa using hM'.diag_nonneg) (by simpa using hM.diag_nonneg)
  have h1 := hM.2 (.single i 1 + .single j (M j i))
  have h2 := hM'.2 (.single i 1 + .single j (M j i))
  simp [Finsupp.sum_add_index, mul_add, add_mul,
    -neg_add_rev, hdiag, ← hM.1.apply j i, -RCLike.star_def] at h1 h2
  have h3 : M i j * star (M i j) + M i j * star (M i j) = 0 := le_antisymm h2 h1
  simp_rw +singlePass [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def,
    ← two_smul 𝕜, ← ContinuousLinearMap.opNorm_zero_iff, norm_smul, mul_eq_zero,
    ContinuousLinearMap.norm_self_comp_adjoint] at h3
  simp_all

lemma mem_toSubmodule_outerKernel (f : X → V) : f ∈ toSubmodule (outerKernel 𝕜 f) := by
  by_cases hf : f = (0 : X → V)
  · simp [hf, zero_mem]
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hf
  use (1 / (‖f x‖ : 𝕜) ^ 2) • (kerFun (OfKernel (outerKernel 𝕜 f)) x) (f x)
  ext
  have : (‖f x‖ ^ 2 : 𝕜) ≠ 0 := by simpa
  simp [inv_smul_smul₀ this]

variable {K} in
lemma mem_toSubmodule {f : X → V} {c : ℝ}
    (h : ((c : 𝕜) ^ 2 • K - outerKernel 𝕜 f).PosSemidef) : f ∈ toSubmodule K := by
  by_cases hc : c = 0
  · simp only [hc, map_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_smul,
      zero_sub] at h
    have ho : outerKernel 𝕜 f = 0 := Matrix.PosSemidef.eq_zero_of_neg (posSemidef_outerKernel 𝕜 f) h
    simp only [outerKernel_def, ← Matrix.ext_iff, Matrix.of_apply, Matrix.zero_apply,
      rankOne_eq_zero] at ho
    have hf : f = 0 := by
      ext x
      rw [Pi.zero_apply, ← or_self (f x = 0)]
      exact ho x x
    simp_rw [hf, zero_mem]
  rw [← ne_eq c 0] at hc
  let : Fact ((c : 𝕜) ^ 2 • K - outerKernel 𝕜 f).PosSemidef := by simp [fact_iff, h]
  have h2 : (c : 𝕜) ^ 2 • K = ((c : 𝕜) ^ 2 • K - outerKernel 𝕜 f) + outerKernel 𝕜 f := by simp
  simp_rw +singlePass  [← toSubmodule_smul K c hc, h2, toSubmodule_add, Submodule.add_eq_sup]
  exact Submodule.mem_sup_right (mem_toSubmodule_outerKernel f)

theorem mem_toSubmodule_iff (f : X → V) : f ∈ toSubmodule K ↔
    ∃ (c : ℝ), 0 ≤ c ∧ ((c : 𝕜)^2 • K - outerKernel 𝕜 f).PosSemidef :=
  ⟨fun ⟨g, hg⟩ => ⟨‖g‖, norm_nonneg _, hg ▸ posSemidef_norm_sq_smul_kernel_sub_outerKernel g⟩,
   fun ⟨_, _, h⟩ => mem_toSubmodule h⟩

theorem exists_OfKernel_eq {f : X → V} (hf : f ∈ toSubmodule K) : ∃ (f' : OfKernel K), ↑f' = f :=
  Set.mem_range.mp hf

end toSubmodule

end RKHS
