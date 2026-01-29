/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth
-/
module

public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.Analysis.Normed.Module.RCLike.Extend
public import Mathlib.Analysis.RCLike.Lemmas

/-!
# Extension Hahn-Banach theorem

In this file we prove the analytic Hahn-Banach theorem. For any continuous linear function on a
subspace, we can extend it to a function on the entire space without changing its norm.

We prove
* `Real.exists_extension_norm_eq`: Hahn-Banach theorem for continuous linear functions on normed
  spaces over `ℝ`.
* `exists_extension_norm_eq`: Hahn-Banach theorem for continuous linear functions on normed spaces
  over `ℝ` or `ℂ`.

In order to state and prove the corollaries uniformly, we prove the statements for a field `𝕜`
satisfying `RCLike 𝕜`.

In this setting, `exists_dual_vector` states that, for any nonzero `x`, there exists a continuous
linear form `g` of norm `1` with `g x = ‖x‖` (where the norm has to be interpreted as an element
of `𝕜`).
-/

public section


universe u v

namespace Real

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Hahn-Banach theorem** for continuous linear functions over `ℝ`.
See also `exists_extension_norm_eq` in the root namespace for a more general version
that works both for `ℝ` and `ℂ`. -/
theorem exists_extension_norm_eq (p : Subspace ℝ E) (f : StrongDual ℝ p) :
    ∃ g : StrongDual ℝ E, (∀ x : p, g x = f x) ∧ ‖g‖ = ‖f‖ := by
  rcases exists_extension_of_le_sublinear ⟨p, f⟩ (fun x => ‖f‖ * ‖x‖)
      (fun c hc x => by simp only [norm_smul c x, Real.norm_eq_abs, abs_of_pos hc, mul_left_comm])
      (fun x y => by
        rw [← left_distrib]
        exact mul_le_mul_of_nonneg_left (norm_add_le x y) (@norm_nonneg _ _ f))
      fun x => le_trans (le_abs_self _) (f.le_opNorm _) with ⟨g, g_eq, g_le⟩
  set g' :=
    g.mkContinuous ‖f‖ fun x => abs_le.2 ⟨neg_le.1 <| g.map_neg x ▸ norm_neg x ▸ g_le (-x), g_le x⟩
  refine ⟨g', g_eq, ?_⟩
  apply le_antisymm (g.mkContinuous_norm_le (norm_nonneg f) _)
  refine f.opNorm_le_bound (norm_nonneg _) fun x => ?_
  dsimp at g_eq
  rw [← g_eq]
  apply g'.le_opNorm

end Real

section RCLike

open RCLike

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] {E F : Type*}
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Hahn-Banach theorem** for continuous linear functions over `𝕜`
satisfying `IsRCLikeNormedField 𝕜`. -/
theorem exists_extension_norm_eq (p : Subspace 𝕜 E) (f : StrongDual 𝕜 p) :
    ∃ g : StrongDual 𝕜 E, (∀ x : p, g x = f x) ∧ ‖g‖ = ‖f‖ := by
  letI : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  letI : Module ℝ E := RestrictScalars.module ℝ 𝕜 E
  letI : IsScalarTower ℝ 𝕜 E := RestrictScalars.isScalarTower _ _ _
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars _ 𝕜 _
  -- Let `fr: StrongDual ℝ p` be the real part of `f`.
  let fr := reCLM.comp (f.restrictScalars ℝ)
  -- Use the real version to get a norm-preserving extension of `fr`, which
  -- we'll call `g : StrongDual ℝ E`.
  rcases Real.exists_extension_norm_eq (p.restrictScalars ℝ) fr with ⟨g, ⟨hextends, hnormeq⟩⟩
  -- Now `g` can be extended to the `StrongDual 𝕜 E` we need.
  refine ⟨g.extendTo𝕜, ?_⟩
  -- It is an extension of `f`.
  have h : ∀ x : p, g.extendTo𝕜 x = f x := by
    intro x
    rw [ContinuousLinearMap.extendTo𝕜_apply, ← Submodule.coe_smul]
    -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
    -- The goal has a coercion from `RestrictScalars ℝ 𝕜 StrongDual ℝ E`, but
    -- `hextends` involves a coercion from `StrongDual ℝ E`.
    erw [hextends]
    erw [hextends]
    have :
        (fr x : 𝕜) - I * ↑(fr ((I : 𝕜) • x)) = (re (f x) : 𝕜) - (I : 𝕜) * re (f ((I : 𝕜) • x)) := by
      rfl
    -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
    erw [this]
    apply ext
    · simp only [add_zero, smul_eq_mul, I_re, ofReal_im, map_add, zero_sub,
        I_im', zero_mul, ofReal_re, sub_zero, mul_neg, ofReal_neg,
        mul_re, mul_zero, sub_neg_eq_add, map_smul]
    · simp only [smul_eq_mul, I_re, ofReal_im, map_add, zero_sub, I_im',
        zero_mul, ofReal_re, mul_neg, mul_im, zero_add, ofReal_neg, mul_re,
        sub_neg_eq_add, map_smul]
  -- And we derive the equality of the norms by bounding on both sides.
  refine ⟨h, le_antisymm ?_ ?_⟩
  · calc
      ‖g.extendTo𝕜‖ = ‖g‖ := g.norm_extendTo𝕜
      _ = ‖fr‖ := hnormeq
      _ ≤ ‖reCLM‖ * ‖f‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖f‖ := by rw [reCLM_norm, one_mul]
  · exact f.opNorm_le_bound g.extendTo𝕜.opNorm_nonneg fun x => h x ▸ g.extendTo𝕜.le_opNorm x

open Module

/-- Corollary of the **Hahn-Banach theorem**: if `f : p → F` is a continuous linear map
from a submodule of a normed space `E` over `𝕜`, `𝕜 = ℝ` or `𝕜 = ℂ`,
with a finite-dimensional range, then `f` admits an extension to a continuous linear map `E → F`.

Note that contrary to the case `F = 𝕜`, see `exists_extension_norm_eq`,
we provide no estimates on the norm of the extension.
-/
lemma ContinuousLinearMap.exist_extension_of_finiteDimensional_range {p : Submodule 𝕜 E}
    (f : p →L[𝕜] F) [FiniteDimensional 𝕜 f.range] :
    ∃ g : E →L[𝕜] F, f = g.comp p.subtypeL := by
  letI : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  set b := Module.finBasis 𝕜 f.range
  set e := b.equivFunL
  set fi := fun i ↦ (LinearMap.toContinuousLinearMap (b.coord i)).comp
    (f.codRestrict _ <| LinearMap.mem_range_self _)
  choose gi hgf _ using fun i ↦ exists_extension_norm_eq p (fi i)
  use f.range.subtypeL.comp <| e.symm.toContinuousLinearMap.comp (.pi gi)
  ext x
  simp [fi, e, hgf]

/-- A finite-dimensional submodule over `ℝ` or `ℂ` is `Submodule.ClosedComplemented`. -/
lemma Submodule.ClosedComplemented.of_finiteDimensional (p : Submodule 𝕜 F)
    [FiniteDimensional 𝕜 p] : p.ClosedComplemented :=
  let ⟨g, hg⟩ := (ContinuousLinearMap.id 𝕜 p).exist_extension_of_finiteDimensional_range
  ⟨g, DFunLike.congr_fun hg.symm⟩

end RCLike

section DualVector

variable (𝕜 : Type v) [RCLike 𝕜]

open ContinuousLinearEquiv Submodule

section Seminormed

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Variant of Hahn-Banach, eliminating the hypothesis that `x` be nonzero, but only ensuring that
the dual element has norm at most `1` (this cannot be improved for the trivial
vector space). Valid for seminormed spaces. -/
theorem exists_dual_vector'' (x : E) : ∃ g : StrongDual 𝕜 E, ‖g‖ ≤ 1 ∧ g x = ‖x‖ := by
  by_cases hx : 0 < ‖x‖
  · have hnz : x ≠ 0 := by intro; simp_all
    have h_homothety := LinearEquiv.toSpanNonzeroSingleton_homothety 𝕜 x hnz
    let coord := (ofHomothety _ _ hx h_homothety).symm.toContinuousLinearMap
    obtain ⟨g, hg⟩ := exists_extension_norm_eq (𝕜 ∙ x) ((‖x‖ : 𝕜) • coord)
    refine ⟨g, ?_, ?_⟩
    · grw [hg.right, algebraMap_smul, norm_smul, norm_norm, coord.opNorm_le_bound (by positivity)
        (fun x ↦ (homothety_inverse _ hx _ h_homothety x).le), mul_inv_cancel₀ hx.ne']
    · have hgx : g x = g (⟨x, by simp⟩ : 𝕜 ∙ x) := by rw [Submodule.coe_mk]
      have hcx : coord ⟨x, _⟩ = 1 := LinearEquiv.coord_self 𝕜 E x hnz
      simp [-algebraMap_smul, hgx, ↓hg.left, hcx]
  · exact ⟨0, by simp, by simp [le_antisymm (not_lt.mp hx) (norm_nonneg x)]⟩

end Seminormed

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

@[deprecated (since := "2026-01-29")] alias coord_norm' := ContinuousLinearEquiv.coord_norm'

/-- Corollary of Hahn-Banach. Given a nonzero element `x` of a normed space, there exists an
element of the dual space, of norm `1`, whose value on `x` is `‖x‖`. -/
theorem exists_dual_vector (x : E) (h : x ≠ 0) : ∃ g : StrongDual 𝕜 E, ‖g‖ = 1 ∧ g x = ‖x‖ := by
  obtain ⟨g, hg⟩ := exists_dual_vector'' 𝕜 x
  refine ⟨g, le_antisymm hg.left ?_, hg.right⟩
  have := g.le_opNorm x
  simp_all

/-- Variant of Hahn-Banach, eliminating the hypothesis that `x` be nonzero, and choosing
the dual element arbitrarily when `x = 0`. -/
theorem exists_dual_vector' [Nontrivial E] (x : E) : ∃ g : StrongDual 𝕜 E, ‖g‖ = 1 ∧ g x = ‖x‖ := by
  by_cases hx : x = 0
  · obtain ⟨y, hy⟩ := exists_ne (0 : E)
    obtain ⟨g, hg⟩ : ∃ g : StrongDual 𝕜 E, ‖g‖ = 1 ∧ g y = ‖y‖ := exists_dual_vector 𝕜 y hy
    exact ⟨g, hg.left, by simp [hx]⟩
  · exact exists_dual_vector 𝕜 x hx

end DualVector
