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

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
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
  -- the type ascription on `hextends` is necessary to make sure the quantification
  -- happens over `x : p` instead of `x : p.restrictScalars ℝ`.
  obtain ⟨g, ⟨(hextends : ∀ x : p, g x = fr x), hnormeq⟩⟩ :=
    Real.exists_extension_norm_eq (p.restrictScalars ℝ) fr
  -- Now `g` can be extended to the `StrongDual 𝕜 E` we need.
  refine ⟨g.extendRCLike, ?_⟩
  -- It is an extension of `f`.
  have h (x : p) : g.extendRCLike x = f x := by
    rw [g.extendRCLike_apply, ← Submodule.coe_smul,
      hextends, hextends]
    simp [fr, RCLike.algebraMap_eq_ofReal, mul_comm I, RCLike.re_add_im]
  -- And we derive the equality of the norms by bounding on both sides.
  refine ⟨h, le_antisymm ?_ ?_⟩
  · calc
      ‖g.extendRCLike‖ = ‖g‖ := g.norm_extendRCLike
      _ = ‖fr‖ := hnormeq
      _ ≤ ‖reCLM‖ * ‖f‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖f‖ := by rw [reCLM_norm, one_mul]
  · exact f.opNorm_le_bound (g.extendRCLike (𝕜 := 𝕜)).opNorm_nonneg
      fun x ↦ h x ▸ (g.extendRCLike (𝕜 := 𝕜) |>.le_opNorm x)

open Module

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
/-- Corollary of Hahn-Banach. Given an element `x` of a normed space with `‖x‖ ≠ 0`, there
exists an element of the dual space, of norm `1`, whose value on `x` is `‖x‖`. -/
theorem exists_dual_vector (x : E) (h : ‖x‖ ≠ 0) : ∃ g : StrongDual 𝕜 E, ‖g‖ = 1 ∧ g x = ‖x‖ := by
  have hhomothety := LinearEquiv.toSpanNonzeroSingleton_homothety 𝕜 x (ne_zero_of_norm_ne_zero h)
  let coord : span 𝕜 {x} →L[𝕜] 𝕜 := (ofHomothety _ _ (by positivity) hhomothety).symm
  obtain ⟨g, hg⟩ := exists_extension_norm_eq (span 𝕜 {x}) ((‖x‖ : 𝕜) • coord)
  have hval : g x = ‖x‖ := by
    have hgx : g x = g (⟨x, by simp⟩ : span 𝕜 {x}) := by rw [Submodule.coe_mk]
    have hcx : coord ⟨x, _⟩ = 1 := LinearEquiv.coord_self 𝕜 E x (ne_zero_of_norm_ne_zero h)
    simp [-algebraMap_smul, hgx, ↓hg.left, hcx]
  refine ⟨g, le_antisymm ?_ ?_, hval⟩
  · simp only [hg.right, norm_smul, norm_algebraMap', norm_norm]
    grw [coord.opNorm_le_bound (by positivity)
      (fun y ↦ (homothety_inverse _ (by positivity) _ hhomothety y).le), mul_inv_cancel₀ h]
  · have hle := g.le_opNorm x
    simp only [hval, norm_algebraMap', norm_norm] at hle
    exact one_le_of_le_mul_right₀ (by positivity) hle

/-- Variant of Hahn-Banach, eliminating the hypothesis that `x` be nonzero, but only ensuring that
the dual element has norm at most `1` (this cannot be improved for the trivial
vector space). -/
theorem exists_dual_vector'' (x : E) : ∃ g : StrongDual 𝕜 E, ‖g‖ ≤ 1 ∧ g x = ‖x‖ := by
  by_cases hx : ‖x‖ = 0
  · exact ⟨0, by simp, by simp [hx]⟩
  · obtain ⟨g, hg⟩ := exists_dual_vector 𝕜 x hx
    exact ⟨g, hg.left.le, hg.right⟩

end Seminormed

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Variant of Hahn-Banach, eliminating the hypothesis that `x` be nonzero, and choosing
the dual element arbitrarily when `x = 0`. -/
theorem exists_dual_vector' [Nontrivial E] (x : E) : ∃ g : StrongDual 𝕜 E, ‖g‖ = 1 ∧ g x = ‖x‖ := by
  by_cases hx : x = 0
  · obtain ⟨y, hy⟩ := exists_norm_ne_zero E
    obtain ⟨g, hg⟩ := exists_dual_vector 𝕜 y hy
    exact ⟨g, hg.left, by simp [hx]⟩
  · exact exists_dual_vector 𝕜 x (norm_ne_zero_iff.mpr hx)

end DualVector
