/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inverse

#align_import analysis.calculus.cont_diff from "leanprover-community/mathlib"@"3bce8d800a6f2b8f63fe1e588fd76a9ff4adcebe"

/-!
# Higher differentiability of usual operations

We prove that the usual operations (addition, multiplication, difference, composition, and
so on) preserve `C^n` functions. We also expand the API around `C^n` functions.

## Main results

* `ContDiff.comp` states that the composition of two `C^n` functions is `C^n`.

Similar results are given for `C^n` functions on domains.

## Notations

We use the notation `E [×n]→L[𝕜] F` for the space of continuous multilinear maps on `E^n` with
values in `F`. This is the space in which the `n`-th derivative of a function from `E` to `F` lives.

In this file, we denote `⊤ : ℕ∞` with `∞`.

## Tags

derivative, differentiability, higher derivative, `C^n`, multilinear, Taylor series, formal series
-/


noncomputable section

open scoped Classical NNReal Nat

local notation "∞" => (⊤ : ℕ∞)

universe u v w uD uE uF uG

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule' AddCommGroup.toAddCommMonoid

open Set Fin Filter Function

open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {D : Type uD} [NormedAddCommGroup D]
  [NormedSpace 𝕜 D] {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type uF}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type uG} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] {s s₁ t u : Set E} {f f₁ : E → F}
  {g : F → G} {x x₀ : E} {c : F} {b : E × F → G} {m n : ℕ∞} {p : E → FormalMultilinearSeries 𝕜 E F}

/-! ### Constants -/

@[simp]
theorem iteratedFDerivWithin_zero_fun (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) {i : ℕ} :
    iteratedFDerivWithin 𝕜 i (fun _ : E ↦ (0 : F)) s x = 0 := by
  induction i generalizing x with
  | zero => ext; simp
  | succ i IH =>
    ext m
    rw [iteratedFDerivWithin_succ_apply_left, fderivWithin_congr (fun _ ↦ IH) (IH hx)]
    rw [fderivWithin_const_apply _ (hs x hx)]
    rfl

@[simp]
theorem iteratedFDeriv_zero_fun {n : ℕ} : (iteratedFDeriv 𝕜 n fun _ : E ↦ (0 : F)) = 0 :=
  funext fun x ↦ by simpa [← iteratedFDerivWithin_univ] using
    iteratedFDerivWithin_zero_fun uniqueDiffOn_univ (mem_univ x)
#align iterated_fderiv_zero_fun iteratedFDeriv_zero_fun

theorem contDiff_zero_fun : ContDiff 𝕜 n fun _ : E => (0 : F) :=
  contDiff_of_differentiable_iteratedFDeriv fun m _ => by
    rw [iteratedFDeriv_zero_fun]
    exact differentiable_const (0 : E[×m]→L[𝕜] F)
#align cont_diff_zero_fun contDiff_zero_fun

/-- Constants are `C^∞`.
-/
theorem contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c := by
  suffices h : ContDiff 𝕜 ∞ fun _ : E => c from h.of_le le_top
  rw [contDiff_top_iff_fderiv]
  refine ⟨differentiable_const c, ?_⟩
  rw [fderiv_const]
  exact contDiff_zero_fun
#align cont_diff_const contDiff_const

theorem contDiffOn_const {c : F} {s : Set E} : ContDiffOn 𝕜 n (fun _ : E => c) s :=
  contDiff_const.contDiffOn
#align cont_diff_on_const contDiffOn_const

theorem contDiffAt_const {c : F} : ContDiffAt 𝕜 n (fun _ : E => c) x :=
  contDiff_const.contDiffAt
#align cont_diff_at_const contDiffAt_const

theorem contDiffWithinAt_const {c : F} : ContDiffWithinAt 𝕜 n (fun _ : E => c) s x :=
  contDiffAt_const.contDiffWithinAt
#align cont_diff_within_at_const contDiffWithinAt_const

@[nontriviality]
theorem contDiff_of_subsingleton [Subsingleton F] : ContDiff 𝕜 n f := by
  rw [Subsingleton.elim f fun _ => 0]; exact contDiff_const
#align cont_diff_of_subsingleton contDiff_of_subsingleton

@[nontriviality]
theorem contDiffAt_of_subsingleton [Subsingleton F] : ContDiffAt 𝕜 n f x := by
  rw [Subsingleton.elim f fun _ => 0]; exact contDiffAt_const
#align cont_diff_at_of_subsingleton contDiffAt_of_subsingleton

@[nontriviality]
theorem contDiffWithinAt_of_subsingleton [Subsingleton F] : ContDiffWithinAt 𝕜 n f s x := by
  rw [Subsingleton.elim f fun _ => 0]; exact contDiffWithinAt_const
#align cont_diff_within_at_of_subsingleton contDiffWithinAt_of_subsingleton

@[nontriviality]
theorem contDiffOn_of_subsingleton [Subsingleton F] : ContDiffOn 𝕜 n f s := by
  rw [Subsingleton.elim f fun _ => 0]; exact contDiffOn_const
#align cont_diff_on_of_subsingleton contDiffOn_of_subsingleton

theorem iteratedFDerivWithin_succ_const (n : ℕ) (c : F) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    iteratedFDerivWithin 𝕜 (n + 1) (fun _ : E ↦ c) s x = 0 := by
  ext m
  rw [iteratedFDerivWithin_succ_apply_right hs hx]
  rw [iteratedFDerivWithin_congr (fun y hy ↦ fderivWithin_const_apply c (hs y hy)) hx]
  rw [iteratedFDerivWithin_zero_fun hs hx]
  simp [ContinuousMultilinearMap.zero_apply (R := 𝕜)]

theorem iteratedFDeriv_succ_const (n : ℕ) (c : F) :
    (iteratedFDeriv 𝕜 (n + 1) fun _ : E ↦ c) = 0 :=
  funext fun x ↦ by simpa [← iteratedFDerivWithin_univ] using
    iteratedFDerivWithin_succ_const n c uniqueDiffOn_univ (mem_univ x)
#align iterated_fderiv_succ_const iteratedFDeriv_succ_const

theorem iteratedFDerivWithin_const_of_ne {n : ℕ} (hn : n ≠ 0) (c : F)
    (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    iteratedFDerivWithin 𝕜 n (fun _ : E ↦ c) s x = 0 := by
  cases n with
  | zero => contradiction
  | succ n => exact iteratedFDerivWithin_succ_const n c hs hx

theorem iteratedFDeriv_const_of_ne {n : ℕ} (hn : n ≠ 0) (c : F) :
    (iteratedFDeriv 𝕜 n fun _ : E ↦ c) = 0 :=
  funext fun x ↦ by simpa [← iteratedFDerivWithin_univ] using
    iteratedFDerivWithin_const_of_ne hn c uniqueDiffOn_univ (mem_univ x)
#align iterated_fderiv_const_of_ne iteratedFDeriv_const_of_ne

/-! ### Smoothness of linear functions -/

/-- Unbundled bounded linear functions are `C^∞`.
-/
theorem IsBoundedLinearMap.contDiff (hf : IsBoundedLinearMap 𝕜 f) : ContDiff 𝕜 n f := by
  suffices h : ContDiff 𝕜 ∞ f from h.of_le le_top
  rw [contDiff_top_iff_fderiv]
  refine ⟨hf.differentiable, ?_⟩
  simp_rw [hf.fderiv]
  exact contDiff_const
#align is_bounded_linear_map.cont_diff IsBoundedLinearMap.contDiff

theorem ContinuousLinearMap.contDiff (f : E →L[𝕜] F) : ContDiff 𝕜 n f :=
  f.isBoundedLinearMap.contDiff
#align continuous_linear_map.cont_diff ContinuousLinearMap.contDiff

theorem ContinuousLinearEquiv.contDiff (f : E ≃L[𝕜] F) : ContDiff 𝕜 n f :=
  (f : E →L[𝕜] F).contDiff
#align continuous_linear_equiv.cont_diff ContinuousLinearEquiv.contDiff

theorem LinearIsometry.contDiff (f : E →ₗᵢ[𝕜] F) : ContDiff 𝕜 n f :=
  f.toContinuousLinearMap.contDiff
#align linear_isometry.cont_diff LinearIsometry.contDiff

theorem LinearIsometryEquiv.contDiff (f : E ≃ₗᵢ[𝕜] F) : ContDiff 𝕜 n f :=
  (f : E →L[𝕜] F).contDiff
#align linear_isometry_equiv.cont_diff LinearIsometryEquiv.contDiff

/-- The identity is `C^∞`.
-/
theorem contDiff_id : ContDiff 𝕜 n (id : E → E) :=
  IsBoundedLinearMap.id.contDiff
#align cont_diff_id contDiff_id

theorem contDiffWithinAt_id {s x} : ContDiffWithinAt 𝕜 n (id : E → E) s x :=
  contDiff_id.contDiffWithinAt
#align cont_diff_within_at_id contDiffWithinAt_id

theorem contDiffAt_id {x} : ContDiffAt 𝕜 n (id : E → E) x :=
  contDiff_id.contDiffAt
#align cont_diff_at_id contDiffAt_id

theorem contDiffOn_id {s} : ContDiffOn 𝕜 n (id : E → E) s :=
  contDiff_id.contDiffOn
#align cont_diff_on_id contDiffOn_id

/-- Bilinear functions are `C^∞`.
-/
theorem IsBoundedBilinearMap.contDiff (hb : IsBoundedBilinearMap 𝕜 b) : ContDiff 𝕜 n b := by
  suffices h : ContDiff 𝕜 ∞ b from h.of_le le_top
  rw [contDiff_top_iff_fderiv]
  refine ⟨hb.differentiable, ?_⟩
  simp only [hb.fderiv]
  exact hb.isBoundedLinearMap_deriv.contDiff
#align is_bounded_bilinear_map.cont_diff IsBoundedBilinearMap.contDiff

/-- If `f` admits a Taylor series `p` in a set `s`, and `g` is linear, then `g ∘ f` admits a Taylor
series whose `k`-th term is given by `g ∘ (p k)`. -/
theorem HasFTaylorSeriesUpToOn.continuousLinearMap_comp (g : F →L[𝕜] G)
    (hf : HasFTaylorSeriesUpToOn n f p s) :
    HasFTaylorSeriesUpToOn n (g ∘ f) (fun x k => g.compContinuousMultilinearMap (p x k)) s where
  zero_eq x hx := congr_arg g (hf.zero_eq x hx)
  fderivWithin m hm x hx := (ContinuousLinearMap.compContinuousMultilinearMapL 𝕜
    (fun _ : Fin m => E) F G g).hasFDerivAt.comp_hasFDerivWithinAt x (hf.fderivWithin m hm x hx)
  cont m hm := (ContinuousLinearMap.compContinuousMultilinearMapL 𝕜
    (fun _ : Fin m => E) F G g).continuous.comp_continuousOn (hf.cont m hm)
#align has_ftaylor_series_up_to_on.continuous_linear_map_comp HasFTaylorSeriesUpToOn.continuousLinearMap_comp

/-- Composition by continuous linear maps on the left preserves `C^n` functions in a domain
at a point. -/
theorem ContDiffWithinAt.continuousLinearMap_comp (g : F →L[𝕜] G)
    (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWithinAt 𝕜 n (g ∘ f) s x := fun m hm ↦ by
  rcases hf m hm with ⟨u, hu, p, hp⟩
  exact ⟨u, hu, _, hp.continuousLinearMap_comp g⟩
#align cont_diff_within_at.continuous_linear_map_comp ContDiffWithinAt.continuousLinearMap_comp

/-- Composition by continuous linear maps on the left preserves `C^n` functions in a domain
at a point. -/
theorem ContDiffAt.continuousLinearMap_comp (g : F →L[𝕜] G) (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (g ∘ f) x :=
  ContDiffWithinAt.continuousLinearMap_comp g hf
#align cont_diff_at.continuous_linear_map_comp ContDiffAt.continuousLinearMap_comp

/-- Composition by continuous linear maps on the left preserves `C^n` functions on domains. -/
theorem ContDiffOn.continuousLinearMap_comp (g : F →L[𝕜] G) (hf : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (g ∘ f) s := fun x hx => (hf x hx).continuousLinearMap_comp g
#align cont_diff_on.continuous_linear_map_comp ContDiffOn.continuousLinearMap_comp

/-- Composition by continuous linear maps on the left preserves `C^n` functions. -/
theorem ContDiff.continuousLinearMap_comp {f : E → F} (g : F →L[𝕜] G) (hf : ContDiff 𝕜 n f) :
    ContDiff 𝕜 n fun x => g (f x) :=
  contDiffOn_univ.1 <| ContDiffOn.continuousLinearMap_comp _ (contDiffOn_univ.2 hf)
#align cont_diff.continuous_linear_map_comp ContDiff.continuousLinearMap_comp

/-- The iterated derivative within a set of the composition with a linear map on the left is
obtained by applying the linear map to the iterated derivative. -/
theorem ContinuousLinearMap.iteratedFDerivWithin_comp_left {f : E → F} (g : F →L[𝕜] G)
    (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) {i : ℕ} (hi : (i : ℕ∞) ≤ n) :
    iteratedFDerivWithin 𝕜 i (g ∘ f) s x =
      g.compContinuousMultilinearMap (iteratedFDerivWithin 𝕜 i f s x) :=
  (((hf.ftaylorSeriesWithin hs).continuousLinearMap_comp g).eq_iteratedFDerivWithin_of_uniqueDiffOn
    hi hs hx).symm
#align continuous_linear_map.iterated_fderiv_within_comp_left ContinuousLinearMap.iteratedFDerivWithin_comp_left

/-- The iterated derivative of the composition with a linear map on the left is
obtained by applying the linear map to the iterated derivative. -/
theorem ContinuousLinearMap.iteratedFDeriv_comp_left {f : E → F} (g : F →L[𝕜] G)
    (hf : ContDiff 𝕜 n f) (x : E) {i : ℕ} (hi : (i : ℕ∞) ≤ n) :
    iteratedFDeriv 𝕜 i (g ∘ f) x = g.compContinuousMultilinearMap (iteratedFDeriv 𝕜 i f x) := by
  simp only [← iteratedFDerivWithin_univ]
  exact g.iteratedFDerivWithin_comp_left hf.contDiffOn uniqueDiffOn_univ (mem_univ x) hi
#align continuous_linear_map.iterated_fderiv_comp_left ContinuousLinearMap.iteratedFDeriv_comp_left

/-- The iterated derivative within a set of the composition with a linear equiv on the left is
obtained by applying the linear equiv to the iterated derivative. This is true without
differentiability assumptions. -/
theorem ContinuousLinearEquiv.iteratedFDerivWithin_comp_left (g : F ≃L[𝕜] G) (f : E → F)
    (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (i : ℕ) :
    iteratedFDerivWithin 𝕜 i (g ∘ f) s x =
      (g : F →L[𝕜] G).compContinuousMultilinearMap (iteratedFDerivWithin 𝕜 i f s x) := by
  induction' i with i IH generalizing x
  · ext1 m
    simp only [Nat.zero_eq, iteratedFDerivWithin_zero_apply, comp_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, coe_coe]
  · ext1 m
    rw [iteratedFDerivWithin_succ_apply_left]
    have Z : fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 i (g ∘ f) s) s x =
        fderivWithin 𝕜 (g.compContinuousMultilinearMapL (fun _ : Fin i => E) ∘
          iteratedFDerivWithin 𝕜 i f s) s x :=
      fderivWithin_congr' (@IH) hx
    simp_rw [Z]
    rw [(g.compContinuousMultilinearMapL fun _ : Fin i => E).comp_fderivWithin (hs x hx)]
    simp only [ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe, comp_apply,
      ContinuousLinearEquiv.compContinuousMultilinearMapL_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, EmbeddingLike.apply_eq_iff_eq]
    rw [iteratedFDerivWithin_succ_apply_left]
#align continuous_linear_equiv.iterated_fderiv_within_comp_left ContinuousLinearEquiv.iteratedFDerivWithin_comp_left

/-- Composition with a linear isometry on the left preserves the norm of the iterated
derivative within a set. -/
theorem LinearIsometry.norm_iteratedFDerivWithin_comp_left {f : E → F} (g : F →ₗᵢ[𝕜] G)
    (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) {i : ℕ} (hi : (i : ℕ∞) ≤ n) :
    ‖iteratedFDerivWithin 𝕜 i (g ∘ f) s x‖ = ‖iteratedFDerivWithin 𝕜 i f s x‖ := by
  have :
    iteratedFDerivWithin 𝕜 i (g ∘ f) s x =
      g.toContinuousLinearMap.compContinuousMultilinearMap (iteratedFDerivWithin 𝕜 i f s x) :=
    g.toContinuousLinearMap.iteratedFDerivWithin_comp_left hf hs hx hi
  rw [this]
  apply LinearIsometry.norm_compContinuousMultilinearMap
#align linear_isometry.norm_iterated_fderiv_within_comp_left LinearIsometry.norm_iteratedFDerivWithin_comp_left

/-- Composition with a linear isometry on the left preserves the norm of the iterated
derivative. -/
theorem LinearIsometry.norm_iteratedFDeriv_comp_left {f : E → F} (g : F →ₗᵢ[𝕜] G)
    (hf : ContDiff 𝕜 n f) (x : E) {i : ℕ} (hi : (i : ℕ∞) ≤ n) :
    ‖iteratedFDeriv 𝕜 i (g ∘ f) x‖ = ‖iteratedFDeriv 𝕜 i f x‖ := by
  simp only [← iteratedFDerivWithin_univ]
  exact g.norm_iteratedFDerivWithin_comp_left hf.contDiffOn uniqueDiffOn_univ (mem_univ x) hi
#align linear_isometry.norm_iterated_fderiv_comp_left LinearIsometry.norm_iteratedFDeriv_comp_left

/-- Composition with a linear isometry equiv on the left preserves the norm of the iterated
derivative within a set. -/
theorem LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_left (g : F ≃ₗᵢ[𝕜] G) (f : E → F)
    (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (i : ℕ) :
    ‖iteratedFDerivWithin 𝕜 i (g ∘ f) s x‖ = ‖iteratedFDerivWithin 𝕜 i f s x‖ := by
  have :
    iteratedFDerivWithin 𝕜 i (g ∘ f) s x =
      (g : F →L[𝕜] G).compContinuousMultilinearMap (iteratedFDerivWithin 𝕜 i f s x) :=
    g.toContinuousLinearEquiv.iteratedFDerivWithin_comp_left f hs hx i
  rw [this]
  apply LinearIsometry.norm_compContinuousMultilinearMap g.toLinearIsometry
#align linear_isometry_equiv.norm_iterated_fderiv_within_comp_left LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_left

/-- Composition with a linear isometry equiv on the left preserves the norm of the iterated
derivative. -/
theorem LinearIsometryEquiv.norm_iteratedFDeriv_comp_left (g : F ≃ₗᵢ[𝕜] G) (f : E → F) (x : E)
    (i : ℕ) : ‖iteratedFDeriv 𝕜 i (g ∘ f) x‖ = ‖iteratedFDeriv 𝕜 i f x‖ := by
  rw [← iteratedFDerivWithin_univ, ← iteratedFDerivWithin_univ]
  apply g.norm_iteratedFDerivWithin_comp_left f uniqueDiffOn_univ (mem_univ x) i
#align linear_isometry_equiv.norm_iterated_fderiv_comp_left LinearIsometryEquiv.norm_iteratedFDeriv_comp_left

/-- Composition by continuous linear equivs on the left respects higher differentiability at a
point in a domain. -/
theorem ContinuousLinearEquiv.comp_contDiffWithinAt_iff (e : F ≃L[𝕜] G) :
    ContDiffWithinAt 𝕜 n (e ∘ f) s x ↔ ContDiffWithinAt 𝕜 n f s x :=
  ⟨fun H => by
    simpa only [(· ∘ ·), e.symm.coe_coe, e.symm_apply_apply] using
      H.continuousLinearMap_comp (e.symm : G →L[𝕜] F),
    fun H => H.continuousLinearMap_comp (e : F →L[𝕜] G)⟩
#align continuous_linear_equiv.comp_cont_diff_within_at_iff ContinuousLinearEquiv.comp_contDiffWithinAt_iff

/-- Composition by continuous linear equivs on the left respects higher differentiability at a
point. -/
theorem ContinuousLinearEquiv.comp_contDiffAt_iff (e : F ≃L[𝕜] G) :
    ContDiffAt 𝕜 n (e ∘ f) x ↔ ContDiffAt 𝕜 n f x := by
  simp only [← contDiffWithinAt_univ, e.comp_contDiffWithinAt_iff]
#align continuous_linear_equiv.comp_cont_diff_at_iff ContinuousLinearEquiv.comp_contDiffAt_iff

/-- Composition by continuous linear equivs on the left respects higher differentiability on
domains. -/
theorem ContinuousLinearEquiv.comp_contDiffOn_iff (e : F ≃L[𝕜] G) :
    ContDiffOn 𝕜 n (e ∘ f) s ↔ ContDiffOn 𝕜 n f s := by
  simp [ContDiffOn, e.comp_contDiffWithinAt_iff]
#align continuous_linear_equiv.comp_cont_diff_on_iff ContinuousLinearEquiv.comp_contDiffOn_iff

/-- Composition by continuous linear equivs on the left respects higher differentiability. -/
theorem ContinuousLinearEquiv.comp_contDiff_iff (e : F ≃L[𝕜] G) :
    ContDiff 𝕜 n (e ∘ f) ↔ ContDiff 𝕜 n f := by
  simp only [← contDiffOn_univ, e.comp_contDiffOn_iff]
#align continuous_linear_equiv.comp_cont_diff_iff ContinuousLinearEquiv.comp_contDiff_iff

/-- If `f` admits a Taylor series `p` in a set `s`, and `g` is linear, then `f ∘ g` admits a Taylor
series in `g ⁻¹' s`, whose `k`-th term is given by `p k (g v₁, ..., g vₖ)` . -/
theorem HasFTaylorSeriesUpToOn.compContinuousLinearMap (hf : HasFTaylorSeriesUpToOn n f p s)
    (g : G →L[𝕜] E) :
    HasFTaylorSeriesUpToOn n (f ∘ g) (fun x k => (p (g x) k).compContinuousLinearMap fun _ => g)
      (g ⁻¹' s) := by
  let A : ∀ m : ℕ, (E[×m]→L[𝕜] F) → G[×m]→L[𝕜] F := fun m h => h.compContinuousLinearMap fun _ => g
  have hA : ∀ m, IsBoundedLinearMap 𝕜 (A m) := fun m =>
    isBoundedLinearMap_continuousMultilinearMap_comp_linear g
  constructor
  · intro x hx
    simp only [(hf.zero_eq (g x) hx).symm, Function.comp_apply]
    change (p (g x) 0 fun _ : Fin 0 => g 0) = p (g x) 0 0
    rw [ContinuousLinearMap.map_zero]
    rfl
  · intro m hm x hx
    convert (hA m).hasFDerivAt.comp_hasFDerivWithinAt x
        ((hf.fderivWithin m hm (g x) hx).comp x g.hasFDerivWithinAt (Subset.refl _))
    ext y v
    change p (g x) (Nat.succ m) (g ∘ cons y v) = p (g x) m.succ (cons (g y) (g ∘ v))
    rw [comp_cons]
  · intro m hm
    exact (hA m).continuous.comp_continuousOn <| (hf.cont m hm).comp g.continuous.continuousOn <|
      Subset.refl _
#align has_ftaylor_series_up_to_on.comp_continuous_linear_map HasFTaylorSeriesUpToOn.compContinuousLinearMap

/-- Composition by continuous linear maps on the right preserves `C^n` functions at a point on
a domain. -/
theorem ContDiffWithinAt.comp_continuousLinearMap {x : G} (g : G →L[𝕜] E)
    (hf : ContDiffWithinAt 𝕜 n f s (g x)) : ContDiffWithinAt 𝕜 n (f ∘ g) (g ⁻¹' s) x := by
  intro m hm
  rcases hf m hm with ⟨u, hu, p, hp⟩
  refine ⟨g ⁻¹' u, ?_, _, hp.compContinuousLinearMap g⟩
  refine g.continuous.continuousWithinAt.tendsto_nhdsWithin ?_ hu
  exact (mapsTo_singleton.2 <| mem_singleton _).union_union (mapsTo_preimage _ _)
#align cont_diff_within_at.comp_continuous_linear_map ContDiffWithinAt.comp_continuousLinearMap

/-- Composition by continuous linear maps on the right preserves `C^n` functions on domains. -/
theorem ContDiffOn.comp_continuousLinearMap (hf : ContDiffOn 𝕜 n f s) (g : G →L[𝕜] E) :
    ContDiffOn 𝕜 n (f ∘ g) (g ⁻¹' s) := fun x hx => (hf (g x) hx).comp_continuousLinearMap g
#align cont_diff_on.comp_continuous_linear_map ContDiffOn.comp_continuousLinearMap

/-- Composition by continuous linear maps on the right preserves `C^n` functions. -/
theorem ContDiff.comp_continuousLinearMap {f : E → F} {g : G →L[𝕜] E} (hf : ContDiff 𝕜 n f) :
    ContDiff 𝕜 n (f ∘ g) :=
  contDiffOn_univ.1 <| ContDiffOn.comp_continuousLinearMap (contDiffOn_univ.2 hf) _
#align cont_diff.comp_continuous_linear_map ContDiff.comp_continuousLinearMap

/-- The iterated derivative within a set of the composition with a linear map on the right is
obtained by composing the iterated derivative with the linear map. -/
theorem ContinuousLinearMap.iteratedFDerivWithin_comp_right {f : E → F} (g : G →L[𝕜] E)
    (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s) (h's : UniqueDiffOn 𝕜 (g ⁻¹' s)) {x : G}
    (hx : g x ∈ s) {i : ℕ} (hi : (i : ℕ∞) ≤ n) :
    iteratedFDerivWithin 𝕜 i (f ∘ g) (g ⁻¹' s) x =
      (iteratedFDerivWithin 𝕜 i f s (g x)).compContinuousLinearMap fun _ => g :=
  (((hf.ftaylorSeriesWithin hs).compContinuousLinearMap g).eq_iteratedFDerivWithin_of_uniqueDiffOn
    hi h's hx).symm
#align continuous_linear_map.iterated_fderiv_within_comp_right ContinuousLinearMap.iteratedFDerivWithin_comp_right

/-- The iterated derivative within a set of the composition with a linear equiv on the right is
obtained by composing the iterated derivative with the linear equiv. -/
theorem ContinuousLinearEquiv.iteratedFDerivWithin_comp_right (g : G ≃L[𝕜] E) (f : E → F)
    (hs : UniqueDiffOn 𝕜 s) {x : G} (hx : g x ∈ s) (i : ℕ) :
    iteratedFDerivWithin 𝕜 i (f ∘ g) (g ⁻¹' s) x =
      (iteratedFDerivWithin 𝕜 i f s (g x)).compContinuousLinearMap fun _ => g := by
  induction' i with i IH generalizing x
  · ext1
    simp only [Nat.zero_eq, iteratedFDerivWithin_zero_apply, comp_apply,
     ContinuousMultilinearMap.compContinuousLinearMap_apply]
  · ext1 m
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousLinearEquiv.coe_coe, iteratedFDerivWithin_succ_apply_left]
    have : fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 i (f ∘ g) (g ⁻¹' s)) (g ⁻¹' s) x =
        fderivWithin 𝕜
          (ContinuousMultilinearMap.compContinuousLinearMapEquivL _ (fun _x : Fin i => g) ∘
            (iteratedFDerivWithin 𝕜 i f s ∘ g)) (g ⁻¹' s) x :=
      fderivWithin_congr' (@IH) hx
    rw [this, ContinuousLinearEquiv.comp_fderivWithin _ (g.uniqueDiffOn_preimage_iff.2 hs x hx)]
    simp only [ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe, comp_apply,
      ContinuousMultilinearMap.compContinuousLinearMapEquivL_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
    rw [ContinuousLinearEquiv.comp_right_fderivWithin _ (g.uniqueDiffOn_preimage_iff.2 hs x hx),
      ContinuousLinearMap.coe_comp', coe_coe, comp_apply, tail_def, tail_def]
#align continuous_linear_equiv.iterated_fderiv_within_comp_right ContinuousLinearEquiv.iteratedFDerivWithin_comp_right

/-- The iterated derivative of the composition with a linear map on the right is
obtained by composing the iterated derivative with the linear map. -/
theorem ContinuousLinearMap.iteratedFDeriv_comp_right (g : G →L[𝕜] E) {f : E → F}
    (hf : ContDiff 𝕜 n f) (x : G) {i : ℕ} (hi : (i : ℕ∞) ≤ n) :
    iteratedFDeriv 𝕜 i (f ∘ g) x =
      (iteratedFDeriv 𝕜 i f (g x)).compContinuousLinearMap fun _ => g := by
  simp only [← iteratedFDerivWithin_univ]
  exact g.iteratedFDerivWithin_comp_right hf.contDiffOn uniqueDiffOn_univ uniqueDiffOn_univ
      (mem_univ _) hi
#align continuous_linear_map.iterated_fderiv_comp_right ContinuousLinearMap.iteratedFDeriv_comp_right

/-- Composition with a linear isometry on the right preserves the norm of the iterated derivative
within a set. -/
theorem LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_right (g : G ≃ₗᵢ[𝕜] E) (f : E → F)
    (hs : UniqueDiffOn 𝕜 s) {x : G} (hx : g x ∈ s) (i : ℕ) :
    ‖iteratedFDerivWithin 𝕜 i (f ∘ g) (g ⁻¹' s) x‖ = ‖iteratedFDerivWithin 𝕜 i f s (g x)‖ := by
  have : iteratedFDerivWithin 𝕜 i (f ∘ g) (g ⁻¹' s) x =
      (iteratedFDerivWithin 𝕜 i f s (g x)).compContinuousLinearMap fun _ => g :=
    g.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right f hs hx i
  rw [this, ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv]
#align linear_isometry_equiv.norm_iterated_fderiv_within_comp_right LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_right

/-- Composition with a linear isometry on the right preserves the norm of the iterated derivative
within a set. -/
theorem LinearIsometryEquiv.norm_iteratedFDeriv_comp_right (g : G ≃ₗᵢ[𝕜] E) (f : E → F) (x : G)
    (i : ℕ) : ‖iteratedFDeriv 𝕜 i (f ∘ g) x‖ = ‖iteratedFDeriv 𝕜 i f (g x)‖ := by
  simp only [← iteratedFDerivWithin_univ]
  apply g.norm_iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (mem_univ (g x)) i
#align linear_isometry_equiv.norm_iterated_fderiv_comp_right LinearIsometryEquiv.norm_iteratedFDeriv_comp_right

/-- Composition by continuous linear equivs on the right respects higher differentiability at a
point in a domain. -/
theorem ContinuousLinearEquiv.contDiffWithinAt_comp_iff (e : G ≃L[𝕜] E) :
    ContDiffWithinAt 𝕜 n (f ∘ e) (e ⁻¹' s) (e.symm x) ↔ ContDiffWithinAt 𝕜 n f s x := by
  constructor
  · intro H
    simpa [← preimage_comp, (· ∘ ·)] using H.comp_continuousLinearMap (e.symm : E →L[𝕜] G)
  · intro H
    rw [← e.apply_symm_apply x, ← e.coe_coe] at H
    exact H.comp_continuousLinearMap _
#align continuous_linear_equiv.cont_diff_within_at_comp_iff ContinuousLinearEquiv.contDiffWithinAt_comp_iff

/-- Composition by continuous linear equivs on the right respects higher differentiability at a
point. -/
theorem ContinuousLinearEquiv.contDiffAt_comp_iff (e : G ≃L[𝕜] E) :
    ContDiffAt 𝕜 n (f ∘ e) (e.symm x) ↔ ContDiffAt 𝕜 n f x := by
  rw [← contDiffWithinAt_univ, ← contDiffWithinAt_univ, ← preimage_univ]
  exact e.contDiffWithinAt_comp_iff
#align continuous_linear_equiv.cont_diff_at_comp_iff ContinuousLinearEquiv.contDiffAt_comp_iff

/-- Composition by continuous linear equivs on the right respects higher differentiability on
domains. -/
theorem ContinuousLinearEquiv.contDiffOn_comp_iff (e : G ≃L[𝕜] E) :
    ContDiffOn 𝕜 n (f ∘ e) (e ⁻¹' s) ↔ ContDiffOn 𝕜 n f s :=
  ⟨fun H => by simpa [(· ∘ ·)] using H.comp_continuousLinearMap (e.symm : E →L[𝕜] G), fun H =>
    H.comp_continuousLinearMap (e : G →L[𝕜] E)⟩
#align continuous_linear_equiv.cont_diff_on_comp_iff ContinuousLinearEquiv.contDiffOn_comp_iff

/-- Composition by continuous linear equivs on the right respects higher differentiability. -/
theorem ContinuousLinearEquiv.contDiff_comp_iff (e : G ≃L[𝕜] E) :
    ContDiff 𝕜 n (f ∘ e) ↔ ContDiff 𝕜 n f := by
  rw [← contDiffOn_univ, ← contDiffOn_univ, ← preimage_univ]
  exact e.contDiffOn_comp_iff
#align continuous_linear_equiv.cont_diff_comp_iff ContinuousLinearEquiv.contDiff_comp_iff

/-- If two functions `f` and `g` admit Taylor series `p` and `q` in a set `s`, then the cartesian
product of `f` and `g` admits the cartesian product of `p` and `q` as a Taylor series. -/
theorem HasFTaylorSeriesUpToOn.prod (hf : HasFTaylorSeriesUpToOn n f p s) {g : E → G}
    {q : E → FormalMultilinearSeries 𝕜 E G} (hg : HasFTaylorSeriesUpToOn n g q s) :
    HasFTaylorSeriesUpToOn n (fun y => (f y, g y)) (fun y k => (p y k).prod (q y k)) s := by
  set L := fun m => ContinuousMultilinearMap.prodL 𝕜 (fun _ : Fin m => E) F G
  constructor
  · intro x hx; rw [← hf.zero_eq x hx, ← hg.zero_eq x hx]; rfl
  · intro m hm x hx
    convert (L m).hasFDerivAt.comp_hasFDerivWithinAt x
        ((hf.fderivWithin m hm x hx).prod (hg.fderivWithin m hm x hx))
  · intro m hm
    exact (L m).continuous.comp_continuousOn ((hf.cont m hm).prod (hg.cont m hm))
#align has_ftaylor_series_up_to_on.prod HasFTaylorSeriesUpToOn.prod

/-- The cartesian product of `C^n` functions at a point in a domain is `C^n`. -/
theorem ContDiffWithinAt.prod {s : Set E} {f : E → F} {g : E → G} (hf : ContDiffWithinAt 𝕜 n f s x)
    (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWithinAt 𝕜 n (fun x : E => (f x, g x)) s x := by
  intro m hm
  rcases hf m hm with ⟨u, hu, p, hp⟩
  rcases hg m hm with ⟨v, hv, q, hq⟩
  exact
    ⟨u ∩ v, Filter.inter_mem hu hv, _,
      (hp.mono inter_subset_left).prod (hq.mono inter_subset_right)⟩
#align cont_diff_within_at.prod ContDiffWithinAt.prod

/-- The cartesian product of `C^n` functions on domains is `C^n`. -/
theorem ContDiffOn.prod {s : Set E} {f : E → F} {g : E → G} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x : E => (f x, g x)) s := fun x hx =>
  (hf x hx).prod (hg x hx)
#align cont_diff_on.prod ContDiffOn.prod

/-- The cartesian product of `C^n` functions at a point is `C^n`. -/
theorem ContDiffAt.prod {f : E → F} {g : E → G} (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun x : E => (f x, g x)) x :=
  contDiffWithinAt_univ.1 <|
    ContDiffWithinAt.prod (contDiffWithinAt_univ.2 hf) (contDiffWithinAt_univ.2 hg)
#align cont_diff_at.prod ContDiffAt.prod

/-- The cartesian product of `C^n` functions is `C^n`. -/
theorem ContDiff.prod {f : E → F} {g : E → G} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n fun x : E => (f x, g x) :=
  contDiffOn_univ.1 <| ContDiffOn.prod (contDiffOn_univ.2 hf) (contDiffOn_univ.2 hg)
#align cont_diff.prod ContDiff.prod

/-!
### Composition of `C^n` functions

We show that the composition of `C^n` functions is `C^n`. One way to prove it would be to write
the `n`-th derivative of the composition (this is Faà di Bruno's formula) and check its continuity,
but this is very painful. Instead, we go for a simple inductive proof. Assume it is done for `n`.
Then, to check it for `n+1`, one needs to check that the derivative of `g ∘ f` is `C^n`, i.e.,
that `Dg(f x) ⬝ Df(x)` is `C^n`. The term `Dg (f x)` is the composition of two `C^n` functions, so
it is `C^n` by the inductive assumption. The term `Df(x)` is also `C^n`. Then, the matrix
multiplication is the application of a bilinear map (which is `C^∞`, and therefore `C^n`) to
`x ↦ (Dg(f x), Df x)`. As the composition of two `C^n` maps, it is again `C^n`, and we are done.

There is a subtlety in this argument: we apply the inductive assumption to functions on other Banach
spaces. In maths, one would say: prove by induction over `n` that, for all `C^n` maps between all
pairs of Banach spaces, their composition is `C^n`. In Lean, this is fine as long as the spaces
stay in the same universe. This is not the case in the above argument: if `E` lives in universe `u`
and `F` lives in universe `v`, then linear maps from `E` to `F` (to which the derivative of `f`
belongs) is in universe `max u v`. If one could quantify over finitely many universes, the above
proof would work fine, but this is not the case. One could still write the proof considering spaces
in any universe in `u, v, w, max u v, max v w, max u v w`, but it would be extremely tedious and
lead to a lot of duplication. Instead, we formulate the above proof when all spaces live in the same
universe (where everything is fine), and then we deduce the general result by lifting all our spaces
to a common universe through `ULift`. This lifting is done through a continuous linear equiv.
We have already proved that composing with such a linear equiv does not change the fact of
being `C^n`, which concludes the proof.
-/


/-- Auxiliary lemma proving that the composition of `C^n` functions on domains is `C^n` when all
spaces live in the same universe. Use instead `ContDiffOn.comp` which removes the universe
assumption (but is deduced from this one). -/
private theorem ContDiffOn.comp_same_univ {Eu : Type u} [NormedAddCommGroup Eu] [NormedSpace 𝕜 Eu]
    {Fu : Type u} [NormedAddCommGroup Fu] [NormedSpace 𝕜 Fu] {Gu : Type u} [NormedAddCommGroup Gu]
    [NormedSpace 𝕜 Gu] {s : Set Eu} {t : Set Fu} {g : Fu → Gu} {f : Eu → Fu}
    (hg : ContDiffOn 𝕜 n g t) (hf : ContDiffOn 𝕜 n f s) (st : s ⊆ f ⁻¹' t) :
    ContDiffOn 𝕜 n (g ∘ f) s := by
  induction' n using ENat.nat_induction with n IH Itop generalizing Eu Fu Gu
  · rw [contDiffOn_zero] at hf hg ⊢
    exact ContinuousOn.comp hg hf st
  · rw [contDiffOn_succ_iff_hasFDerivWithinAt] at hg ⊢
    intro x hx
    rcases (contDiffOn_succ_iff_hasFDerivWithinAt.1 hf) x hx with ⟨u, hu, f', hf', f'_diff⟩
    rcases hg (f x) (st hx) with ⟨v, hv, g', hg', g'_diff⟩
    rw [insert_eq_of_mem hx] at hu ⊢
    have xu : x ∈ u := mem_of_mem_nhdsWithin hx hu
    let w := s ∩ (u ∩ f ⁻¹' v)
    have wv : w ⊆ f ⁻¹' v := fun y hy => hy.2.2
    have wu : w ⊆ u := fun y hy => hy.2.1
    have ws : w ⊆ s := fun y hy => hy.1
    refine ⟨w, ?_, fun y => (g' (f y)).comp (f' y), ?_, ?_⟩
    · show w ∈ 𝓝[s] x
      apply Filter.inter_mem self_mem_nhdsWithin
      apply Filter.inter_mem hu
      apply ContinuousWithinAt.preimage_mem_nhdsWithin'
      · rw [← continuousWithinAt_inter' hu]
        exact (hf' x xu).differentiableWithinAt.continuousWithinAt.mono inter_subset_right
      · apply nhdsWithin_mono _ _ hv
        exact Subset.trans (image_subset_iff.mpr st) (subset_insert (f x) t)
    · show ∀ y ∈ w, HasFDerivWithinAt (g ∘ f) ((g' (f y)).comp (f' y)) w y
      rintro y ⟨-, yu, yv⟩
      exact (hg' (f y) yv).comp y ((hf' y yu).mono wu) wv
    · show ContDiffOn 𝕜 n (fun y => (g' (f y)).comp (f' y)) w
      have A : ContDiffOn 𝕜 n (fun y => g' (f y)) w :=
        IH g'_diff ((hf.of_le (WithTop.coe_le_coe.2 (Nat.le_succ n))).mono ws) wv
      have B : ContDiffOn 𝕜 n f' w := f'_diff.mono wu
      have C : ContDiffOn 𝕜 n (fun y => (g' (f y), f' y)) w := A.prod B
      have D : ContDiffOn 𝕜 n (fun p : (Fu →L[𝕜] Gu) × (Eu →L[𝕜] Fu) => p.1.comp p.2) univ :=
        isBoundedBilinearMap_comp.contDiff.contDiffOn
      exact IH D C (subset_univ _)
  · rw [contDiffOn_top] at hf hg ⊢
    exact fun n => Itop n (hg n) (hf n) st

/-- The composition of `C^n` functions on domains is `C^n`. -/
theorem ContDiffOn.comp {s : Set E} {t : Set F} {g : F → G} {f : E → F} (hg : ContDiffOn 𝕜 n g t)
    (hf : ContDiffOn 𝕜 n f s) (st : s ⊆ f ⁻¹' t) : ContDiffOn 𝕜 n (g ∘ f) s := by
  /- we lift all the spaces to a common universe, as we have already proved the result in this
    situation. -/
  let Eu : Type max uE uF uG := ULift.{max uF uG} E
  let Fu : Type max uE uF uG := ULift.{max uE uG} F
  let Gu : Type max uE uF uG := ULift.{max uE uF} G
  -- declare the isomorphisms
  have isoE : Eu ≃L[𝕜] E := ContinuousLinearEquiv.ulift
  have isoF : Fu ≃L[𝕜] F := ContinuousLinearEquiv.ulift
  have isoG : Gu ≃L[𝕜] G := ContinuousLinearEquiv.ulift
  -- lift the functions to the new spaces, check smoothness there, and then go back.
  let fu : Eu → Fu := (isoF.symm ∘ f) ∘ isoE
  have fu_diff : ContDiffOn 𝕜 n fu (isoE ⁻¹' s) := by
    rwa [isoE.contDiffOn_comp_iff, isoF.symm.comp_contDiffOn_iff]
  let gu : Fu → Gu := (isoG.symm ∘ g) ∘ isoF
  have gu_diff : ContDiffOn 𝕜 n gu (isoF ⁻¹' t) := by
    rwa [isoF.contDiffOn_comp_iff, isoG.symm.comp_contDiffOn_iff]
  have main : ContDiffOn 𝕜 n (gu ∘ fu) (isoE ⁻¹' s) := by
    apply ContDiffOn.comp_same_univ gu_diff fu_diff
    intro y hy
    simp only [fu, ContinuousLinearEquiv.coe_apply, Function.comp_apply, mem_preimage]
    rw [isoF.apply_symm_apply (f (isoE y))]
    exact st hy
  have : gu ∘ fu = (isoG.symm ∘ g ∘ f) ∘ isoE := by
    ext y
    simp only [fu, gu, Function.comp_apply]
    rw [isoF.apply_symm_apply (f (isoE y))]
  rwa [this, isoE.contDiffOn_comp_iff, isoG.symm.comp_contDiffOn_iff] at main
#align cont_diff_on.comp ContDiffOn.comp

/-- The composition of `C^n` functions on domains is `C^n`. -/
theorem ContDiffOn.comp' {s : Set E} {t : Set F} {g : F → G} {f : E → F} (hg : ContDiffOn 𝕜 n g t)
    (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 n (g ∘ f) (s ∩ f ⁻¹' t) :=
  hg.comp (hf.mono inter_subset_left) inter_subset_right
#align cont_diff_on.comp' ContDiffOn.comp'

/-- The composition of a `C^n` function on a domain with a `C^n` function is `C^n`. -/
theorem ContDiff.comp_contDiffOn {s : Set E} {g : F → G} {f : E → F} (hg : ContDiff 𝕜 n g)
    (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 n (g ∘ f) s :=
  (contDiffOn_univ.2 hg).comp hf subset_preimage_univ
#align cont_diff.comp_cont_diff_on ContDiff.comp_contDiffOn

/-- The composition of `C^n` functions is `C^n`. -/
theorem ContDiff.comp {g : F → G} {f : E → F} (hg : ContDiff 𝕜 n g) (hf : ContDiff 𝕜 n f) :
    ContDiff 𝕜 n (g ∘ f) :=
  contDiffOn_univ.1 <| ContDiffOn.comp (contDiffOn_univ.2 hg) (contDiffOn_univ.2 hf) (subset_univ _)
#align cont_diff.comp ContDiff.comp

/-- The composition of `C^n` functions at points in domains is `C^n`. -/
theorem ContDiffWithinAt.comp {s : Set E} {t : Set F} {g : F → G} {f : E → F} (x : E)
    (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) (st : s ⊆ f ⁻¹' t) :
    ContDiffWithinAt 𝕜 n (g ∘ f) s x := by
  intro m hm
  rcases hg.contDiffOn hm with ⟨u, u_nhd, _, hu⟩
  rcases hf.contDiffOn hm with ⟨v, v_nhd, vs, hv⟩
  have xmem : x ∈ f ⁻¹' u ∩ v :=
    ⟨(mem_of_mem_nhdsWithin (mem_insert (f x) _) u_nhd : _),
      mem_of_mem_nhdsWithin (mem_insert x s) v_nhd⟩
  have : f ⁻¹' u ∈ 𝓝[insert x s] x := by
    apply hf.continuousWithinAt.insert_self.preimage_mem_nhdsWithin'
    apply nhdsWithin_mono _ _ u_nhd
    rw [image_insert_eq]
    exact insert_subset_insert (image_subset_iff.mpr st)
  have Z :=
    (hu.comp (hv.mono inter_subset_right) inter_subset_left).contDiffWithinAt
      xmem m le_rfl
  have : 𝓝[f ⁻¹' u ∩ v] x = 𝓝[insert x s] x := by
    have A : f ⁻¹' u ∩ v = insert x s ∩ (f ⁻¹' u ∩ v) := by
      apply Subset.antisymm _ inter_subset_right
      rintro y ⟨hy1, hy2⟩
      simpa only [mem_inter_iff, mem_preimage, hy2, and_true, true_and, vs hy2] using hy1
    rw [A, ← nhdsWithin_restrict'']
    exact Filter.inter_mem this v_nhd
  rwa [insert_eq_of_mem xmem, this] at Z
#align cont_diff_within_at.comp ContDiffWithinAt.comp

/-- The composition of `C^n` functions at points in domains is `C^n`,
  with a weaker condition on `s` and `t`. -/
theorem ContDiffWithinAt.comp_of_mem {s : Set E} {t : Set F} {g : F → G} {f : E → F} (x : E)
    (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x)
    (hs : t ∈ 𝓝[f '' s] f x) : ContDiffWithinAt 𝕜 n (g ∘ f) s x :=
  (hg.mono_of_mem hs).comp x hf (subset_preimage_image f s)
#align cont_diff_within_at.comp_of_mem ContDiffWithinAt.comp_of_mem

/-- The composition of `C^n` functions at points in domains is `C^n`. -/
theorem ContDiffWithinAt.comp' {s : Set E} {t : Set F} {g : F → G} {f : E → F} (x : E)
    (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) :
    ContDiffWithinAt 𝕜 n (g ∘ f) (s ∩ f ⁻¹' t) x :=
  hg.comp x (hf.mono inter_subset_left) inter_subset_right
#align cont_diff_within_at.comp' ContDiffWithinAt.comp'

theorem ContDiffAt.comp_contDiffWithinAt {n} (x : E) (hg : ContDiffAt 𝕜 n g (f x))
    (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWithinAt 𝕜 n (g ∘ f) s x :=
  hg.comp x hf (mapsTo_univ _ _)
#align cont_diff_at.comp_cont_diff_within_at ContDiffAt.comp_contDiffWithinAt

/-- The composition of `C^n` functions at points is `C^n`. -/
nonrec theorem ContDiffAt.comp (x : E) (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (g ∘ f) x :=
  hg.comp x hf subset_preimage_univ
#align cont_diff_at.comp ContDiffAt.comp

theorem ContDiff.comp_contDiffWithinAt {g : F → G} {f : E → F} (h : ContDiff 𝕜 n g)
    (hf : ContDiffWithinAt 𝕜 n f t x) : ContDiffWithinAt 𝕜 n (g ∘ f) t x :=
  haveI : ContDiffWithinAt 𝕜 n g univ (f x) := h.contDiffAt.contDiffWithinAt
  this.comp x hf (subset_univ _)
#align cont_diff.comp_cont_diff_within_at ContDiff.comp_contDiffWithinAt

theorem ContDiff.comp_contDiffAt {g : F → G} {f : E → F} (x : E) (hg : ContDiff 𝕜 n g)
    (hf : ContDiffAt 𝕜 n f x) : ContDiffAt 𝕜 n (g ∘ f) x :=
  hg.comp_contDiffWithinAt hf
#align cont_diff.comp_cont_diff_at ContDiff.comp_contDiffAt

/-!
### Smoothness of projections
-/

/-- The first projection in a product is `C^∞`. -/
theorem contDiff_fst : ContDiff 𝕜 n (Prod.fst : E × F → E) :=
  IsBoundedLinearMap.contDiff IsBoundedLinearMap.fst
#align cont_diff_fst contDiff_fst

/-- Postcomposing `f` with `Prod.fst` is `C^n` -/
theorem ContDiff.fst {f : E → F × G} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x => (f x).1 :=
  contDiff_fst.comp hf
#align cont_diff.fst ContDiff.fst

/-- Precomposing `f` with `Prod.fst` is `C^n` -/
theorem ContDiff.fst' {f : E → G} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x : E × F => f x.1 :=
  hf.comp contDiff_fst
#align cont_diff.fst' ContDiff.fst'

/-- The first projection on a domain in a product is `C^∞`. -/
theorem contDiffOn_fst {s : Set (E × F)} : ContDiffOn 𝕜 n (Prod.fst : E × F → E) s :=
  ContDiff.contDiffOn contDiff_fst
#align cont_diff_on_fst contDiffOn_fst

theorem ContDiffOn.fst {f : E → F × G} {s : Set E} (hf : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (fun x => (f x).1) s :=
  contDiff_fst.comp_contDiffOn hf
#align cont_diff_on.fst ContDiffOn.fst

/-- The first projection at a point in a product is `C^∞`. -/
theorem contDiffAt_fst {p : E × F} : ContDiffAt 𝕜 n (Prod.fst : E × F → E) p :=
  contDiff_fst.contDiffAt
#align cont_diff_at_fst contDiffAt_fst

/-- Postcomposing `f` with `Prod.fst` is `C^n` at `(x, y)` -/
theorem ContDiffAt.fst {f : E → F × G} {x : E} (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun x => (f x).1) x :=
  contDiffAt_fst.comp x hf
#align cont_diff_at.fst ContDiffAt.fst

/-- Precomposing `f` with `Prod.fst` is `C^n` at `(x, y)` -/
theorem ContDiffAt.fst' {f : E → G} {x : E} {y : F} (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun x : E × F => f x.1) (x, y) :=
  ContDiffAt.comp (x, y) hf contDiffAt_fst
#align cont_diff_at.fst' ContDiffAt.fst'

/-- Precomposing `f` with `Prod.fst` is `C^n` at `x : E × F` -/
theorem ContDiffAt.fst'' {f : E → G} {x : E × F} (hf : ContDiffAt 𝕜 n f x.1) :
    ContDiffAt 𝕜 n (fun x : E × F => f x.1) x :=
  hf.comp x contDiffAt_fst
#align cont_diff_at.fst'' ContDiffAt.fst''

/-- The first projection within a domain at a point in a product is `C^∞`. -/
theorem contDiffWithinAt_fst {s : Set (E × F)} {p : E × F} :
    ContDiffWithinAt 𝕜 n (Prod.fst : E × F → E) s p :=
  contDiff_fst.contDiffWithinAt
#align cont_diff_within_at_fst contDiffWithinAt_fst

/-- The second projection in a product is `C^∞`. -/
theorem contDiff_snd : ContDiff 𝕜 n (Prod.snd : E × F → F) :=
  IsBoundedLinearMap.contDiff IsBoundedLinearMap.snd
#align cont_diff_snd contDiff_snd

/-- Postcomposing `f` with `Prod.snd` is `C^n` -/
theorem ContDiff.snd {f : E → F × G} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x => (f x).2 :=
  contDiff_snd.comp hf
#align cont_diff.snd ContDiff.snd

/-- Precomposing `f` with `Prod.snd` is `C^n` -/
theorem ContDiff.snd' {f : F → G} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x : E × F => f x.2 :=
  hf.comp contDiff_snd
#align cont_diff.snd' ContDiff.snd'

/-- The second projection on a domain in a product is `C^∞`. -/
theorem contDiffOn_snd {s : Set (E × F)} : ContDiffOn 𝕜 n (Prod.snd : E × F → F) s :=
  ContDiff.contDiffOn contDiff_snd
#align cont_diff_on_snd contDiffOn_snd

theorem ContDiffOn.snd {f : E → F × G} {s : Set E} (hf : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (fun x => (f x).2) s :=
  contDiff_snd.comp_contDiffOn hf
#align cont_diff_on.snd ContDiffOn.snd

/-- The second projection at a point in a product is `C^∞`. -/
theorem contDiffAt_snd {p : E × F} : ContDiffAt 𝕜 n (Prod.snd : E × F → F) p :=
  contDiff_snd.contDiffAt
#align cont_diff_at_snd contDiffAt_snd

/-- Postcomposing `f` with `Prod.snd` is `C^n` at `x` -/
theorem ContDiffAt.snd {f : E → F × G} {x : E} (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun x => (f x).2) x :=
  contDiffAt_snd.comp x hf
#align cont_diff_at.snd ContDiffAt.snd

/-- Precomposing `f` with `Prod.snd` is `C^n` at `(x, y)` -/
theorem ContDiffAt.snd' {f : F → G} {x : E} {y : F} (hf : ContDiffAt 𝕜 n f y) :
    ContDiffAt 𝕜 n (fun x : E × F => f x.2) (x, y) :=
  ContDiffAt.comp (x, y) hf contDiffAt_snd
#align cont_diff_at.snd' ContDiffAt.snd'

/-- Precomposing `f` with `Prod.snd` is `C^n` at `x : E × F` -/
theorem ContDiffAt.snd'' {f : F → G} {x : E × F} (hf : ContDiffAt 𝕜 n f x.2) :
    ContDiffAt 𝕜 n (fun x : E × F => f x.2) x :=
  hf.comp x contDiffAt_snd
#align cont_diff_at.snd'' ContDiffAt.snd''

/-- The second projection within a domain at a point in a product is `C^∞`. -/
theorem contDiffWithinAt_snd {s : Set (E × F)} {p : E × F} :
    ContDiffWithinAt 𝕜 n (Prod.snd : E × F → F) s p :=
  contDiff_snd.contDiffWithinAt
#align cont_diff_within_at_snd contDiffWithinAt_snd

section NAry

variable {E₁ E₂ E₃ E₄ : Type*}
variable [NormedAddCommGroup E₁] [NormedAddCommGroup E₂] [NormedAddCommGroup E₃]
  [NormedAddCommGroup E₄] [NormedSpace 𝕜 E₁] [NormedSpace 𝕜 E₂] [NormedSpace 𝕜 E₃]
  [NormedSpace 𝕜 E₄]

theorem ContDiff.comp₂ {g : E₁ × E₂ → G} {f₁ : F → E₁} {f₂ : F → E₂} (hg : ContDiff 𝕜 n g)
    (hf₁ : ContDiff 𝕜 n f₁) (hf₂ : ContDiff 𝕜 n f₂) : ContDiff 𝕜 n fun x => g (f₁ x, f₂ x) :=
  hg.comp <| hf₁.prod hf₂
#align cont_diff.comp₂ ContDiff.comp₂

theorem ContDiff.comp₃ {g : E₁ × E₂ × E₃ → G} {f₁ : F → E₁} {f₂ : F → E₂} {f₃ : F → E₃}
    (hg : ContDiff 𝕜 n g) (hf₁ : ContDiff 𝕜 n f₁) (hf₂ : ContDiff 𝕜 n f₂) (hf₃ : ContDiff 𝕜 n f₃) :
    ContDiff 𝕜 n fun x => g (f₁ x, f₂ x, f₃ x) :=
  hg.comp₂ hf₁ <| hf₂.prod hf₃
#align cont_diff.comp₃ ContDiff.comp₃

theorem ContDiff.comp_contDiff_on₂ {g : E₁ × E₂ → G} {f₁ : F → E₁} {f₂ : F → E₂} {s : Set F}
    (hg : ContDiff 𝕜 n g) (hf₁ : ContDiffOn 𝕜 n f₁ s) (hf₂ : ContDiffOn 𝕜 n f₂ s) :
    ContDiffOn 𝕜 n (fun x => g (f₁ x, f₂ x)) s :=
  hg.comp_contDiffOn <| hf₁.prod hf₂
#align cont_diff.comp_cont_diff_on₂ ContDiff.comp_contDiff_on₂

theorem ContDiff.comp_contDiff_on₃ {g : E₁ × E₂ × E₃ → G} {f₁ : F → E₁} {f₂ : F → E₂} {f₃ : F → E₃}
    {s : Set F} (hg : ContDiff 𝕜 n g) (hf₁ : ContDiffOn 𝕜 n f₁ s) (hf₂ : ContDiffOn 𝕜 n f₂ s)
    (hf₃ : ContDiffOn 𝕜 n f₃ s) : ContDiffOn 𝕜 n (fun x => g (f₁ x, f₂ x, f₃ x)) s :=
  hg.comp_contDiff_on₂ hf₁ <| hf₂.prod hf₃
#align cont_diff.comp_cont_diff_on₃ ContDiff.comp_contDiff_on₃

end NAry

section SpecificBilinearMaps

theorem ContDiff.clm_comp {g : X → F →L[𝕜] G} {f : X → E →L[𝕜] F} (hg : ContDiff 𝕜 n g)
    (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x => (g x).comp (f x) :=
  isBoundedBilinearMap_comp.contDiff.comp₂ hg hf
#align cont_diff.clm_comp ContDiff.clm_comp

theorem ContDiffOn.clm_comp {g : X → F →L[𝕜] G} {f : X → E →L[𝕜] F} {s : Set X}
    (hg : ContDiffOn 𝕜 n g s) (hf : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (fun x => (g x).comp (f x)) s :=
  isBoundedBilinearMap_comp.contDiff.comp_contDiff_on₂ hg hf
#align cont_diff_on.clm_comp ContDiffOn.clm_comp

theorem ContDiff.clm_apply {f : E → F →L[𝕜] G} {g : E → F} {n : ℕ∞} (hf : ContDiff 𝕜 n f)
    (hg : ContDiff 𝕜 n g) : ContDiff 𝕜 n fun x => (f x) (g x) :=
  isBoundedBilinearMap_apply.contDiff.comp₂ hf hg
#align cont_diff.clm_apply ContDiff.clm_apply

theorem ContDiffOn.clm_apply {f : E → F →L[𝕜] G} {g : E → F} {n : ℕ∞} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x => (f x) (g x)) s :=
  isBoundedBilinearMap_apply.contDiff.comp_contDiff_on₂ hf hg
#align cont_diff_on.clm_apply ContDiffOn.clm_apply

-- Porting note: In Lean 3 we had to give implicit arguments in proofs like the following,
-- to speed up elaboration. In Lean 4 this isn't necessary anymore.
theorem ContDiff.smulRight {f : E → F →L[𝕜] 𝕜} {g : E → G} {n : ℕ∞} (hf : ContDiff 𝕜 n f)
    (hg : ContDiff 𝕜 n g) : ContDiff 𝕜 n fun x => (f x).smulRight (g x) :=
  isBoundedBilinearMap_smulRight.contDiff.comp₂ hf hg
#align cont_diff.smul_right ContDiff.smulRight

end SpecificBilinearMaps

section ClmApplyConst

/-- Application of a `ContinuousLinearMap` to a constant commutes with `iteratedFDerivWithin`. -/
theorem iteratedFDerivWithin_clm_apply_const_apply
    {s : Set E} (hs : UniqueDiffOn 𝕜 s) {n : ℕ∞} {c : E → F →L[𝕜] G} (hc : ContDiffOn 𝕜 n c s)
    {i : ℕ} (hi : i ≤ n) {x : E} (hx : x ∈ s) {u : F} {m : Fin i → E} :
    (iteratedFDerivWithin 𝕜 i (fun y ↦ (c y) u) s x) m = (iteratedFDerivWithin 𝕜 i c s x) m u := by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
    replace hi : i < n := lt_of_lt_of_le (by norm_cast; simp) hi
    have h_deriv_apply : DifferentiableOn 𝕜 (iteratedFDerivWithin 𝕜 i (fun y ↦ (c y) u) s) s :=
      (hc.clm_apply contDiffOn_const).differentiableOn_iteratedFDerivWithin hi hs
    have h_deriv : DifferentiableOn 𝕜 (iteratedFDerivWithin 𝕜 i c s) s :=
      hc.differentiableOn_iteratedFDerivWithin hi hs
    simp only [iteratedFDerivWithin_succ_apply_left]
    rw [← fderivWithin_continuousMultilinear_apply_const_apply (hs x hx) (h_deriv_apply x hx)]
    rw [fderivWithin_congr' (fun x hx ↦ ih hi.le hx) hx]
    rw [fderivWithin_clm_apply (hs x hx) (h_deriv.continuousMultilinear_apply_const _ x hx)
      (differentiableWithinAt_const u)]
    rw [fderivWithin_const_apply _ (hs x hx)]
    simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_zero, zero_add]
    rw [fderivWithin_continuousMultilinear_apply_const_apply (hs x hx) (h_deriv x hx)]

/-- Application of a `ContinuousLinearMap` to a constant commutes with `iteratedFDeriv`. -/
theorem iteratedFDeriv_clm_apply_const_apply
    {n : ℕ∞} {c : E → F →L[𝕜] G} (hc : ContDiff 𝕜 n c)
    {i : ℕ} (hi : i ≤ n) {x : E} {u : F} {m : Fin i → E} :
    (iteratedFDeriv 𝕜 i (fun y ↦ (c y) u) x) m = (iteratedFDeriv 𝕜 i c x) m u := by
  simp only [← iteratedFDerivWithin_univ]
  exact iteratedFDerivWithin_clm_apply_const_apply uniqueDiffOn_univ hc.contDiffOn hi (mem_univ _)

end ClmApplyConst

/-- The natural equivalence `(E × F) × G ≃ E × (F × G)` is smooth.

Warning: if you think you need this lemma, it is likely that you can simplify your proof by
reformulating the lemma that you're applying next using the tips in
Note [continuity lemma statement]
-/
theorem contDiff_prodAssoc : ContDiff 𝕜 ⊤ <| Equiv.prodAssoc E F G :=
  (LinearIsometryEquiv.prodAssoc 𝕜 E F G).contDiff
#align cont_diff_prod_assoc contDiff_prodAssoc

/-- The natural equivalence `E × (F × G) ≃ (E × F) × G` is smooth.

Warning: see remarks attached to `contDiff_prodAssoc`
-/
theorem contDiff_prodAssoc_symm : ContDiff 𝕜 ⊤ <| (Equiv.prodAssoc E F G).symm :=
  (LinearIsometryEquiv.prodAssoc 𝕜 E F G).symm.contDiff
#align cont_diff_prod_assoc_symm contDiff_prodAssoc_symm

/-! ### Bundled derivatives are smooth -/

/-- One direction of `contDiffWithinAt_succ_iff_hasFDerivWithinAt`, but where all derivatives
taken within the same set. Version for partial derivatives / functions with parameters.  `f x` is a
`C^n+1` family of functions and `g x` is a `C^n` family of points, then the derivative of `f x` at
`g x` depends in a `C^n` way on `x`. We give a general version of this fact relative to sets which
may not have unique derivatives, in the following form.  If `f : E × F → G` is `C^n+1` at
`(x₀, g(x₀))` in `(s ∪ {x₀}) × t ⊆ E × F` and `g : E → F` is `C^n` at `x₀` within some set `s ⊆ E`,
then there is a function `f' : E → F →L[𝕜] G` that is `C^n` at `x₀` within `s` such that for all `x`
sufficiently close to `x₀` within `s ∪ {x₀}` the function `y ↦ f x y` has derivative `f' x` at `g x`
within `t ⊆ F`.  For convenience, we return an explicit set of `x`'s where this holds that is a
subset of `s ∪ {x₀}`.  We need one additional condition, namely that `t` is a neighborhood of
`g(x₀)` within `g '' s`.  -/
theorem ContDiffWithinAt.hasFDerivWithinAt_nhds {f : E → F → G} {g : E → F} {t : Set F} {n : ℕ}
    {x₀ : E} (hf : ContDiffWithinAt 𝕜 (n + 1) (uncurry f) (insert x₀ s ×ˢ t) (x₀, g x₀))
    (hg : ContDiffWithinAt 𝕜 n g s x₀) (hgt : t ∈ 𝓝[g '' s] g x₀) :
    ∃ v ∈ 𝓝[insert x₀ s] x₀, v ⊆ insert x₀ s ∧ ∃ f' : E → F →L[𝕜] G,
      (∀ x ∈ v, HasFDerivWithinAt (f x) (f' x) t (g x)) ∧
        ContDiffWithinAt 𝕜 n (fun x => f' x) s x₀ := by
  have hst : insert x₀ s ×ˢ t ∈ 𝓝[(fun x => (x, g x)) '' s] (x₀, g x₀) := by
    refine nhdsWithin_mono _ ?_ (nhdsWithin_prod self_mem_nhdsWithin hgt)
    simp_rw [image_subset_iff, mk_preimage_prod, preimage_id', subset_inter_iff, subset_insert,
      true_and_iff, subset_preimage_image]
  obtain ⟨v, hv, hvs, f', hvf', hf'⟩ := contDiffWithinAt_succ_iff_hasFDerivWithinAt'.mp hf
  refine
    ⟨(fun z => (z, g z)) ⁻¹' v ∩ insert x₀ s, ?_, inter_subset_right, fun z =>
      (f' (z, g z)).comp (ContinuousLinearMap.inr 𝕜 E F), ?_, ?_⟩
  · refine inter_mem ?_ self_mem_nhdsWithin
    have := mem_of_mem_nhdsWithin (mem_insert _ _) hv
    refine mem_nhdsWithin_insert.mpr ⟨this, ?_⟩
    refine (continuousWithinAt_id.prod hg.continuousWithinAt).preimage_mem_nhdsWithin' ?_
    rw [← nhdsWithin_le_iff] at hst hv ⊢
    exact (hst.trans <| nhdsWithin_mono _ <| subset_insert _ _).trans hv
  · intro z hz
    have := hvf' (z, g z) hz.1
    refine this.comp _ (hasFDerivAt_prod_mk_right _ _).hasFDerivWithinAt ?_
    exact mapsTo'.mpr (image_prod_mk_subset_prod_right hz.2)
  · exact (hf'.continuousLinearMap_comp <| (ContinuousLinearMap.compL 𝕜 F (E × F) G).flip
      (ContinuousLinearMap.inr 𝕜 E F)).comp_of_mem x₀ (contDiffWithinAt_id.prod hg) hst
#align cont_diff_within_at.has_fderiv_within_at_nhds ContDiffWithinAt.hasFDerivWithinAt_nhds

/-- The most general lemma stating that `x ↦ fderivWithin 𝕜 (f x) t (g x)` is `C^n`
at a point within a set.
To show that `x ↦ D_yf(x,y)g(x)` (taken within `t`) is `C^m` at `x₀` within `s`, we require that
* `f` is `C^n` at `(x₀, g(x₀))` within `(s ∪ {x₀}) × t` for `n ≥ m+1`.
* `g` is `C^m` at `x₀` within `s`;
* Derivatives are unique at `g(x)` within `t` for `x` sufficiently close to `x₀` within `s ∪ {x₀}`;
* `t` is a neighborhood of `g(x₀)` within `g '' s`; -/
theorem ContDiffWithinAt.fderivWithin'' {f : E → F → G} {g : E → F} {t : Set F} {n : ℕ∞}
    (hf : ContDiffWithinAt 𝕜 n (Function.uncurry f) (insert x₀ s ×ˢ t) (x₀, g x₀))
    (hg : ContDiffWithinAt 𝕜 m g s x₀)
    (ht : ∀ᶠ x in 𝓝[insert x₀ s] x₀, UniqueDiffWithinAt 𝕜 t (g x)) (hmn : m + 1 ≤ n)
    (hgt : t ∈ 𝓝[g '' s] g x₀) :
    ContDiffWithinAt 𝕜 m (fun x => fderivWithin 𝕜 (f x) t (g x)) s x₀ := by
  have : ∀ k : ℕ, (k : ℕ∞) ≤ m →
      ContDiffWithinAt 𝕜 k (fun x => fderivWithin 𝕜 (f x) t (g x)) s x₀ := fun k hkm ↦ by
    obtain ⟨v, hv, -, f', hvf', hf'⟩ :=
      (hf.of_le <| (add_le_add_right hkm 1).trans hmn).hasFDerivWithinAt_nhds (hg.of_le hkm) hgt
    refine hf'.congr_of_eventuallyEq_insert ?_
    filter_upwards [hv, ht]
    exact fun y hy h2y => (hvf' y hy).fderivWithin h2y
  induction' m with m
  · obtain rfl := eq_top_iff.mpr hmn
    rw [contDiffWithinAt_top]
    exact fun m => this m le_top
  exact this _ le_rfl
#align cont_diff_within_at.fderiv_within'' ContDiffWithinAt.fderivWithin''

/-- A special case of `ContDiffWithinAt.fderivWithin''` where we require that `s ⊆ g⁻¹(t)`. -/
theorem ContDiffWithinAt.fderivWithin' {f : E → F → G} {g : E → F} {t : Set F} {n : ℕ∞}
    (hf : ContDiffWithinAt 𝕜 n (Function.uncurry f) (insert x₀ s ×ˢ t) (x₀, g x₀))
    (hg : ContDiffWithinAt 𝕜 m g s x₀)
    (ht : ∀ᶠ x in 𝓝[insert x₀ s] x₀, UniqueDiffWithinAt 𝕜 t (g x)) (hmn : m + 1 ≤ n)
    (hst : s ⊆ g ⁻¹' t) : ContDiffWithinAt 𝕜 m (fun x => fderivWithin 𝕜 (f x) t (g x)) s x₀ :=
  hf.fderivWithin'' hg ht hmn <| mem_of_superset self_mem_nhdsWithin <| image_subset_iff.mpr hst
#align cont_diff_within_at.fderiv_within' ContDiffWithinAt.fderivWithin'

/-- A special case of `ContDiffWithinAt.fderivWithin'` where we require that `x₀ ∈ s` and there
are unique derivatives everywhere within `t`. -/
protected theorem ContDiffWithinAt.fderivWithin {f : E → F → G} {g : E → F} {t : Set F} {n : ℕ∞}
    (hf : ContDiffWithinAt 𝕜 n (Function.uncurry f) (s ×ˢ t) (x₀, g x₀))
    (hg : ContDiffWithinAt 𝕜 m g s x₀) (ht : UniqueDiffOn 𝕜 t) (hmn : m + 1 ≤ n) (hx₀ : x₀ ∈ s)
    (hst : s ⊆ g ⁻¹' t) : ContDiffWithinAt 𝕜 m (fun x => fderivWithin 𝕜 (f x) t (g x)) s x₀ := by
  rw [← insert_eq_self.mpr hx₀] at hf
  refine hf.fderivWithin' hg ?_ hmn hst
  rw [insert_eq_self.mpr hx₀]
  exact eventually_of_mem self_mem_nhdsWithin fun x hx => ht _ (hst hx)
#align cont_diff_within_at.fderiv_within ContDiffWithinAt.fderivWithin

/-- `x ↦ fderivWithin 𝕜 (f x) t (g x) (k x)` is smooth at a point within a set. -/
theorem ContDiffWithinAt.fderivWithin_apply {f : E → F → G} {g k : E → F} {t : Set F} {n : ℕ∞}
    (hf : ContDiffWithinAt 𝕜 n (Function.uncurry f) (s ×ˢ t) (x₀, g x₀))
    (hg : ContDiffWithinAt 𝕜 m g s x₀) (hk : ContDiffWithinAt 𝕜 m k s x₀) (ht : UniqueDiffOn 𝕜 t)
    (hmn : m + 1 ≤ n) (hx₀ : x₀ ∈ s) (hst : s ⊆ g ⁻¹' t) :
    ContDiffWithinAt 𝕜 m (fun x => fderivWithin 𝕜 (f x) t (g x) (k x)) s x₀ :=
  (contDiff_fst.clm_apply contDiff_snd).contDiffAt.comp_contDiffWithinAt x₀
    ((hf.fderivWithin hg ht hmn hx₀ hst).prod hk)
#align cont_diff_within_at.fderiv_within_apply ContDiffWithinAt.fderivWithin_apply

/-- `fderivWithin 𝕜 f s` is smooth at `x₀` within `s`. -/
theorem ContDiffWithinAt.fderivWithin_right (hf : ContDiffWithinAt 𝕜 n f s x₀)
    (hs : UniqueDiffOn 𝕜 s) (hmn : (m + 1 : ℕ∞) ≤ n) (hx₀s : x₀ ∈ s) :
    ContDiffWithinAt 𝕜 m (fderivWithin 𝕜 f s) s x₀ :=
  ContDiffWithinAt.fderivWithin
    (ContDiffWithinAt.comp (x₀, x₀) hf contDiffWithinAt_snd <| prod_subset_preimage_snd s s)
    contDiffWithinAt_id hs hmn hx₀s (by rw [preimage_id'])
#align cont_diff_within_at.fderiv_within_right ContDiffWithinAt.fderivWithin_right

-- TODO: can we make a version of `ContDiffWithinAt.fderivWithin` for iterated derivatives?
theorem ContDiffWithinAt.iteratedFderivWithin_right {i : ℕ} (hf : ContDiffWithinAt 𝕜 n f s x₀)
    (hs : UniqueDiffOn 𝕜 s) (hmn : (m + i : ℕ∞) ≤ n) (hx₀s : x₀ ∈ s) :
    ContDiffWithinAt 𝕜 m (iteratedFDerivWithin 𝕜 i f s) s x₀ := by
  induction' i with i hi generalizing m
  · rw [ENat.coe_zero, add_zero] at hmn
    exact (hf.of_le hmn).continuousLinearMap_comp
      ((continuousMultilinearCurryFin0 𝕜 E F).symm : _ →L[𝕜] E [×0]→L[𝕜] F)
  · rw [Nat.cast_succ, add_comm _ 1, ← add_assoc] at hmn
    exact ((hi hmn).fderivWithin_right hs le_rfl hx₀s).continuousLinearMap_comp
      (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (i+1) ↦ E) F : _ →L[𝕜] E [×(i+1)]→L[𝕜] F)

/-- `x ↦ fderiv 𝕜 (f x) (g x)` is smooth at `x₀`. -/
protected theorem ContDiffAt.fderiv {f : E → F → G} {g : E → F} {n : ℕ∞}
    (hf : ContDiffAt 𝕜 n (Function.uncurry f) (x₀, g x₀)) (hg : ContDiffAt 𝕜 m g x₀)
    (hmn : m + 1 ≤ n) : ContDiffAt 𝕜 m (fun x => fderiv 𝕜 (f x) (g x)) x₀ := by
  simp_rw [← fderivWithin_univ]
  refine (ContDiffWithinAt.fderivWithin hf.contDiffWithinAt hg.contDiffWithinAt uniqueDiffOn_univ
    hmn (mem_univ x₀) ?_).contDiffAt univ_mem
  rw [preimage_univ]
#align cont_diff_at.fderiv ContDiffAt.fderiv

/-- `fderiv 𝕜 f` is smooth at `x₀`. -/
theorem ContDiffAt.fderiv_right (hf : ContDiffAt 𝕜 n f x₀) (hmn : (m + 1 : ℕ∞) ≤ n) :
    ContDiffAt 𝕜 m (fderiv 𝕜 f) x₀ :=
  ContDiffAt.fderiv (ContDiffAt.comp (x₀, x₀) hf contDiffAt_snd) contDiffAt_id hmn
#align cont_diff_at.fderiv_right ContDiffAt.fderiv_right

theorem ContDiffAt.iteratedFDeriv_right {i : ℕ} (hf : ContDiffAt 𝕜 n f x₀)
    (hmn : (m + i : ℕ∞) ≤ n) : ContDiffAt 𝕜 m (iteratedFDeriv 𝕜 i f) x₀ := by
  rw [← iteratedFDerivWithin_univ, ← contDiffWithinAt_univ] at *
  exact hf.iteratedFderivWithin_right uniqueDiffOn_univ hmn trivial

/-- `x ↦ fderiv 𝕜 (f x) (g x)` is smooth. -/
protected theorem ContDiff.fderiv {f : E → F → G} {g : E → F} {n m : ℕ∞}
    (hf : ContDiff 𝕜 m <| Function.uncurry f) (hg : ContDiff 𝕜 n g) (hnm : n + 1 ≤ m) :
    ContDiff 𝕜 n fun x => fderiv 𝕜 (f x) (g x) :=
  contDiff_iff_contDiffAt.mpr fun _ => hf.contDiffAt.fderiv hg.contDiffAt hnm
#align cont_diff.fderiv ContDiff.fderiv

/-- `fderiv 𝕜 f` is smooth. -/
theorem ContDiff.fderiv_right (hf : ContDiff 𝕜 n f) (hmn : (m + 1 : ℕ∞) ≤ n) :
    ContDiff 𝕜 m (fderiv 𝕜 f) :=
  contDiff_iff_contDiffAt.mpr fun _x => hf.contDiffAt.fderiv_right hmn
#align cont_diff.fderiv_right ContDiff.fderiv_right

theorem ContDiff.iteratedFDeriv_right {i : ℕ} (hf : ContDiff 𝕜 n f)
    (hmn : (m + i : ℕ∞) ≤ n) : ContDiff 𝕜 m (iteratedFDeriv 𝕜 i f) :=
  contDiff_iff_contDiffAt.mpr fun _x => hf.contDiffAt.iteratedFDeriv_right hmn

/-- `x ↦ fderiv 𝕜 (f x) (g x)` is continuous. -/
theorem Continuous.fderiv {f : E → F → G} {g : E → F} {n : ℕ∞}
    (hf : ContDiff 𝕜 n <| Function.uncurry f) (hg : Continuous g) (hn : 1 ≤ n) :
    Continuous fun x => fderiv 𝕜 (f x) (g x) :=
  (hf.fderiv (contDiff_zero.mpr hg) hn).continuous
#align continuous.fderiv Continuous.fderiv

/-- `x ↦ fderiv 𝕜 (f x) (g x) (k x)` is smooth. -/
theorem ContDiff.fderiv_apply {f : E → F → G} {g k : E → F} {n m : ℕ∞}
    (hf : ContDiff 𝕜 m <| Function.uncurry f) (hg : ContDiff 𝕜 n g) (hk : ContDiff 𝕜 n k)
    (hnm : n + 1 ≤ m) : ContDiff 𝕜 n fun x => fderiv 𝕜 (f x) (g x) (k x) :=
  (hf.fderiv hg hnm).clm_apply hk
#align cont_diff.fderiv_apply ContDiff.fderiv_apply

/-- The bundled derivative of a `C^{n+1}` function is `C^n`. -/
theorem contDiffOn_fderivWithin_apply {m n : ℕ∞} {s : Set E} {f : E → F} (hf : ContDiffOn 𝕜 n f s)
    (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 ≤ n) :
    ContDiffOn 𝕜 m (fun p : E × E => (fderivWithin 𝕜 f s p.1 : E →L[𝕜] F) p.2) (s ×ˢ univ) :=
  ((hf.fderivWithin hs hmn).comp contDiffOn_fst (prod_subset_preimage_fst _ _)).clm_apply
    contDiffOn_snd
#align cont_diff_on_fderiv_within_apply contDiffOn_fderivWithin_apply

/-- If a function is at least `C^1`, its bundled derivative (mapping `(x, v)` to `Df(x) v`) is
continuous. -/
theorem ContDiffOn.continuousOn_fderivWithin_apply (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
    (hn : 1 ≤ n) :
    ContinuousOn (fun p : E × E => (fderivWithin 𝕜 f s p.1 : E → F) p.2) (s ×ˢ univ) :=
  (contDiffOn_fderivWithin_apply hf hs <| by rwa [zero_add]).continuousOn
#align cont_diff_on.continuous_on_fderiv_within_apply ContDiffOn.continuousOn_fderivWithin_apply

/-- The bundled derivative of a `C^{n+1}` function is `C^n`. -/
theorem ContDiff.contDiff_fderiv_apply {f : E → F} (hf : ContDiff 𝕜 n f) (hmn : m + 1 ≤ n) :
    ContDiff 𝕜 m fun p : E × E => (fderiv 𝕜 f p.1 : E →L[𝕜] F) p.2 := by
  rw [← contDiffOn_univ] at hf ⊢
  rw [← fderivWithin_univ, ← univ_prod_univ]
  exact contDiffOn_fderivWithin_apply hf uniqueDiffOn_univ hmn
#align cont_diff.cont_diff_fderiv_apply ContDiff.contDiff_fderiv_apply

/-!
### Smoothness of functions `f : E → Π i, F' i`
-/

section Pi

variable {ι ι' : Type*} [Fintype ι] [Fintype ι'] {F' : ι → Type*} [∀ i, NormedAddCommGroup (F' i)]
  [∀ i, NormedSpace 𝕜 (F' i)] {φ : ∀ i, E → F' i} {p' : ∀ i, E → FormalMultilinearSeries 𝕜 E (F' i)}
  {Φ : E → ∀ i, F' i} {P' : E → FormalMultilinearSeries 𝕜 E (∀ i, F' i)}

theorem hasFTaylorSeriesUpToOn_pi :
    HasFTaylorSeriesUpToOn n (fun x i => φ i x)
        (fun x m => ContinuousMultilinearMap.pi fun i => p' i x m) s ↔
      ∀ i, HasFTaylorSeriesUpToOn n (φ i) (p' i) s := by
  set pr := @ContinuousLinearMap.proj 𝕜 _ ι F' _ _ _
  letI : ∀ (m : ℕ) (i : ι), NormedSpace 𝕜 (E[×m]→L[𝕜] F' i) := fun m i => inferInstance
  set L : ∀ m : ℕ, (∀ i, E[×m]→L[𝕜] F' i) ≃ₗᵢ[𝕜] E[×m]→L[𝕜] ∀ i, F' i := fun m =>
    ContinuousMultilinearMap.piₗᵢ _ _
  refine ⟨fun h i => ?_, fun h => ⟨fun x hx => ?_, ?_, ?_⟩⟩
  · convert h.continuousLinearMap_comp (pr i)
  · ext1 i
    exact (h i).zero_eq x hx
  · intro m hm x hx
    have := hasFDerivWithinAt_pi.2 fun i => (h i).fderivWithin m hm x hx
    convert (L m).hasFDerivAt.comp_hasFDerivWithinAt x this
  · intro m hm
    have := continuousOn_pi.2 fun i => (h i).cont m hm
    convert (L m).continuous.comp_continuousOn this
#align has_ftaylor_series_up_to_on_pi hasFTaylorSeriesUpToOn_pi

@[simp]
theorem hasFTaylorSeriesUpToOn_pi' :
    HasFTaylorSeriesUpToOn n Φ P' s ↔
      ∀ i, HasFTaylorSeriesUpToOn n (fun x => Φ x i)
        (fun x m => (@ContinuousLinearMap.proj 𝕜 _ ι F' _ _ _ i).compContinuousMultilinearMap
          (P' x m)) s := by
  convert hasFTaylorSeriesUpToOn_pi (𝕜 := 𝕜) (φ := fun i x ↦ Φ x i); ext; rfl
#align has_ftaylor_series_up_to_on_pi' hasFTaylorSeriesUpToOn_pi'

theorem contDiffWithinAt_pi :
    ContDiffWithinAt 𝕜 n Φ s x ↔ ∀ i, ContDiffWithinAt 𝕜 n (fun x => Φ x i) s x := by
  set pr := @ContinuousLinearMap.proj 𝕜 _ ι F' _ _ _
  refine ⟨fun h i => h.continuousLinearMap_comp (pr i), fun h m hm => ?_⟩
  choose u hux p hp using fun i => h i m hm
  exact ⟨⋂ i, u i, Filter.iInter_mem.2 hux, _,
    hasFTaylorSeriesUpToOn_pi.2 fun i => (hp i).mono <| iInter_subset _ _⟩
#align cont_diff_within_at_pi contDiffWithinAt_pi

theorem contDiffOn_pi : ContDiffOn 𝕜 n Φ s ↔ ∀ i, ContDiffOn 𝕜 n (fun x => Φ x i) s :=
  ⟨fun h _ x hx => contDiffWithinAt_pi.1 (h x hx) _, fun h x hx =>
    contDiffWithinAt_pi.2 fun i => h i x hx⟩
#align cont_diff_on_pi contDiffOn_pi

theorem contDiffAt_pi : ContDiffAt 𝕜 n Φ x ↔ ∀ i, ContDiffAt 𝕜 n (fun x => Φ x i) x :=
  contDiffWithinAt_pi
#align cont_diff_at_pi contDiffAt_pi

theorem contDiff_pi : ContDiff 𝕜 n Φ ↔ ∀ i, ContDiff 𝕜 n fun x => Φ x i := by
  simp only [← contDiffOn_univ, contDiffOn_pi]
#align cont_diff_pi contDiff_pi

theorem contDiff_update [DecidableEq ι] (k : ℕ∞) (x : ∀ i, F' i) (i : ι) :
    ContDiff 𝕜 k (update x i) := by
  rw [contDiff_pi]
  intro j
  dsimp [Function.update]
  split_ifs with h
  · subst h
    exact contDiff_id
  · exact contDiff_const

variable (F') in
theorem contDiff_single [DecidableEq ι] (k : ℕ∞) (i : ι) :
    ContDiff 𝕜 k (Pi.single i : F' i → ∀ i, F' i) :=
  contDiff_update k 0 i

variable (𝕜 E)

theorem contDiff_apply (i : ι) : ContDiff 𝕜 n fun f : ι → E => f i :=
  contDiff_pi.mp contDiff_id i
#align cont_diff_apply contDiff_apply

theorem contDiff_apply_apply (i : ι) (j : ι') : ContDiff 𝕜 n fun f : ι → ι' → E => f i j :=
  contDiff_pi.mp (contDiff_apply 𝕜 (ι' → E) i) j
#align cont_diff_apply_apply contDiff_apply_apply

end Pi

/-! ### Sum of two functions -/

section Add

theorem HasFTaylorSeriesUpToOn.add {q g} (hf : HasFTaylorSeriesUpToOn n f p s)
    (hg : HasFTaylorSeriesUpToOn n g q s) : HasFTaylorSeriesUpToOn n (f + g) (p + q) s := by
  convert HasFTaylorSeriesUpToOn.continuousLinearMap_comp
    (ContinuousLinearMap.fst 𝕜 F F + .snd 𝕜 F F) (hf.prod hg)

-- The sum is smooth.
theorem contDiff_add : ContDiff 𝕜 n fun p : F × F => p.1 + p.2 :=
  (IsBoundedLinearMap.fst.add IsBoundedLinearMap.snd).contDiff
#align cont_diff_add contDiff_add

/-- The sum of two `C^n` functions within a set at a point is `C^n` within this set
at this point. -/
theorem ContDiffWithinAt.add {s : Set E} {f g : E → F} (hf : ContDiffWithinAt 𝕜 n f s x)
    (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWithinAt 𝕜 n (fun x => f x + g x) s x :=
  contDiff_add.contDiffWithinAt.comp x (hf.prod hg) subset_preimage_univ
#align cont_diff_within_at.add ContDiffWithinAt.add

/-- The sum of two `C^n` functions at a point is `C^n` at this point. -/
theorem ContDiffAt.add {f g : E → F} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    ContDiffAt 𝕜 n (fun x => f x + g x) x := by
  rw [← contDiffWithinAt_univ] at *; exact hf.add hg
#align cont_diff_at.add ContDiffAt.add

/-- The sum of two `C^n`functions is `C^n`. -/
theorem ContDiff.add {f g : E → F} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n fun x => f x + g x :=
  contDiff_add.comp (hf.prod hg)
#align cont_diff.add ContDiff.add

/-- The sum of two `C^n` functions on a domain is `C^n`. -/
theorem ContDiffOn.add {s : Set E} {f g : E → F} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x => f x + g x) s := fun x hx =>
  (hf x hx).add (hg x hx)
#align cont_diff_on.add ContDiffOn.add

variable {i : ℕ}

/-- The iterated derivative of the sum of two functions is the sum of the iterated derivatives.
See also `iteratedFDerivWithin_add_apply'`, which uses the spelling `(fun x ↦ f x + g x)`
instead of `f + g`. -/
theorem iteratedFDerivWithin_add_apply {f g : E → F} (hf : ContDiffOn 𝕜 i f s)
    (hg : ContDiffOn 𝕜 i g s) (hu : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    iteratedFDerivWithin 𝕜 i (f + g) s x =
      iteratedFDerivWithin 𝕜 i f s x + iteratedFDerivWithin 𝕜 i g s x :=
  Eq.symm <| ((hf.ftaylorSeriesWithin hu).add
    (hg.ftaylorSeriesWithin hu)).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl hu hx
#align iterated_fderiv_within_add_apply iteratedFDerivWithin_add_apply

/-- The iterated derivative of the sum of two functions is the sum of the iterated derivatives.
This is the same as `iteratedFDerivWithin_add_apply`, but using the spelling `(fun x ↦ f x + g x)`
instead of `f + g`, which can be handy for some rewrites.
TODO: use one form consistently. -/
theorem iteratedFDerivWithin_add_apply' {f g : E → F} (hf : ContDiffOn 𝕜 i f s)
    (hg : ContDiffOn 𝕜 i g s) (hu : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    iteratedFDerivWithin 𝕜 i (fun x => f x + g x) s x =
      iteratedFDerivWithin 𝕜 i f s x + iteratedFDerivWithin 𝕜 i g s x :=
  iteratedFDerivWithin_add_apply hf hg hu hx
#align iterated_fderiv_within_add_apply' iteratedFDerivWithin_add_apply'

theorem iteratedFDeriv_add_apply {i : ℕ} {f g : E → F} (hf : ContDiff 𝕜 i f) (hg : ContDiff 𝕜 i g) :
    iteratedFDeriv 𝕜 i (f + g) x = iteratedFDeriv 𝕜 i f x + iteratedFDeriv 𝕜 i g x := by
  simp_rw [← contDiffOn_univ, ← iteratedFDerivWithin_univ] at hf hg ⊢
  exact iteratedFDerivWithin_add_apply hf hg uniqueDiffOn_univ (Set.mem_univ _)
#align iterated_fderiv_add_apply iteratedFDeriv_add_apply

theorem iteratedFDeriv_add_apply' {i : ℕ} {f g : E → F} (hf : ContDiff 𝕜 i f)
    (hg : ContDiff 𝕜 i g) :
    iteratedFDeriv 𝕜 i (fun x => f x + g x) x = iteratedFDeriv 𝕜 i f x + iteratedFDeriv 𝕜 i g x :=
  iteratedFDeriv_add_apply hf hg
#align iterated_fderiv_add_apply' iteratedFDeriv_add_apply'

end Add

/-! ### Negative -/

section Neg

-- The negative is smooth.
theorem contDiff_neg : ContDiff 𝕜 n fun p : F => -p :=
  IsBoundedLinearMap.id.neg.contDiff
#align cont_diff_neg contDiff_neg

/-- The negative of a `C^n` function within a domain at a point is `C^n` within this domain at
this point. -/
theorem ContDiffWithinAt.neg {s : Set E} {f : E → F} (hf : ContDiffWithinAt 𝕜 n f s x) :
    ContDiffWithinAt 𝕜 n (fun x => -f x) s x :=
  contDiff_neg.contDiffWithinAt.comp x hf subset_preimage_univ
#align cont_diff_within_at.neg ContDiffWithinAt.neg

/-- The negative of a `C^n` function at a point is `C^n` at this point. -/
theorem ContDiffAt.neg {f : E → F} (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun x => -f x) x := by rw [← contDiffWithinAt_univ] at *; exact hf.neg
#align cont_diff_at.neg ContDiffAt.neg

/-- The negative of a `C^n`function is `C^n`. -/
theorem ContDiff.neg {f : E → F} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x => -f x :=
  contDiff_neg.comp hf
#align cont_diff.neg ContDiff.neg

/-- The negative of a `C^n` function on a domain is `C^n`. -/
theorem ContDiffOn.neg {s : Set E} {f : E → F} (hf : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (fun x => -f x) s := fun x hx => (hf x hx).neg
#align cont_diff_on.neg ContDiffOn.neg

variable {i : ℕ}

-- Porting note (#11215): TODO: define `Neg` instance on `ContinuousLinearEquiv`,
-- prove it from `ContinuousLinearEquiv.iteratedFDerivWithin_comp_left`
theorem iteratedFDerivWithin_neg_apply {f : E → F} (hu : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    iteratedFDerivWithin 𝕜 i (-f) s x = -iteratedFDerivWithin 𝕜 i f s x := by
  induction' i with i hi generalizing x
  · ext; simp
  · ext h
    calc
      iteratedFDerivWithin 𝕜 (i + 1) (-f) s x h =
          fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 i (-f) s) s x (h 0) (Fin.tail h) :=
        rfl
      _ = fderivWithin 𝕜 (-iteratedFDerivWithin 𝕜 i f s) s x (h 0) (Fin.tail h) := by
        rw [fderivWithin_congr' (@hi) hx]; rfl
      _ = -(fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 i f s) s) x (h 0) (Fin.tail h) := by
        rw [Pi.neg_def, fderivWithin_neg (hu x hx)]; rfl
      _ = -(iteratedFDerivWithin 𝕜 (i + 1) f s) x h := rfl
#align iterated_fderiv_within_neg_apply iteratedFDerivWithin_neg_apply

theorem iteratedFDeriv_neg_apply {i : ℕ} {f : E → F} :
    iteratedFDeriv 𝕜 i (-f) x = -iteratedFDeriv 𝕜 i f x := by
  simp_rw [← iteratedFDerivWithin_univ]
  exact iteratedFDerivWithin_neg_apply uniqueDiffOn_univ (Set.mem_univ _)
#align iterated_fderiv_neg_apply iteratedFDeriv_neg_apply

end Neg

/-! ### Subtraction -/

/-- The difference of two `C^n` functions within a set at a point is `C^n` within this set
at this point. -/
theorem ContDiffWithinAt.sub {s : Set E} {f g : E → F} (hf : ContDiffWithinAt 𝕜 n f s x)
    (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWithinAt 𝕜 n (fun x => f x - g x) s x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
#align cont_diff_within_at.sub ContDiffWithinAt.sub

/-- The difference of two `C^n` functions at a point is `C^n` at this point. -/
theorem ContDiffAt.sub {f g : E → F} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    ContDiffAt 𝕜 n (fun x => f x - g x) x := by simpa only [sub_eq_add_neg] using hf.add hg.neg
#align cont_diff_at.sub ContDiffAt.sub

/-- The difference of two `C^n` functions on a domain is `C^n`. -/
theorem ContDiffOn.sub {s : Set E} {f g : E → F} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x => f x - g x) s := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
#align cont_diff_on.sub ContDiffOn.sub

/-- The difference of two `C^n` functions is `C^n`. -/
theorem ContDiff.sub {f g : E → F} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n fun x => f x - g x := by simpa only [sub_eq_add_neg] using hf.add hg.neg
#align cont_diff.sub ContDiff.sub

/-! ### Sum of finitely many functions -/

theorem ContDiffWithinAt.sum {ι : Type*} {f : ι → E → F} {s : Finset ι} {t : Set E} {x : E}
    (h : ∀ i ∈ s, ContDiffWithinAt 𝕜 n (fun x => f i x) t x) :
    ContDiffWithinAt 𝕜 n (fun x => ∑ i ∈ s, f i x) t x := by
  classical
    induction' s using Finset.induction_on with i s is IH
    · simp [contDiffWithinAt_const]
    · simp only [is, Finset.sum_insert, not_false_iff]
      exact (h _ (Finset.mem_insert_self i s)).add
        (IH fun j hj => h _ (Finset.mem_insert_of_mem hj))
#align cont_diff_within_at.sum ContDiffWithinAt.sum

theorem ContDiffAt.sum {ι : Type*} {f : ι → E → F} {s : Finset ι} {x : E}
    (h : ∀ i ∈ s, ContDiffAt 𝕜 n (fun x => f i x) x) :
    ContDiffAt 𝕜 n (fun x => ∑ i ∈ s, f i x) x := by
  rw [← contDiffWithinAt_univ] at *; exact ContDiffWithinAt.sum h
#align cont_diff_at.sum ContDiffAt.sum

theorem ContDiffOn.sum {ι : Type*} {f : ι → E → F} {s : Finset ι} {t : Set E}
    (h : ∀ i ∈ s, ContDiffOn 𝕜 n (fun x => f i x) t) :
    ContDiffOn 𝕜 n (fun x => ∑ i ∈ s, f i x) t := fun x hx =>
  ContDiffWithinAt.sum fun i hi => h i hi x hx
#align cont_diff_on.sum ContDiffOn.sum

theorem ContDiff.sum {ι : Type*} {f : ι → E → F} {s : Finset ι}
    (h : ∀ i ∈ s, ContDiff 𝕜 n fun x => f i x) : ContDiff 𝕜 n fun x => ∑ i ∈ s, f i x := by
  simp only [← contDiffOn_univ] at *; exact ContDiffOn.sum h
#align cont_diff.sum ContDiff.sum

theorem iteratedFDerivWithin_sum_apply {ι : Type*} {f : ι → E → F} {u : Finset ι} {i : ℕ} {x : E}
    (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (h : ∀ j ∈ u, ContDiffOn 𝕜 i (f j) s) :
    iteratedFDerivWithin 𝕜 i (∑ j ∈ u, f j ·) s x =
      ∑ j ∈ u, iteratedFDerivWithin 𝕜 i (f j) s x := by
  induction u using Finset.cons_induction with
  | empty => ext; simp [hs, hx]
  | cons a u ha IH =>
    simp only [Finset.mem_cons, forall_eq_or_imp] at h
    simp only [Finset.sum_cons]
    rw [iteratedFDerivWithin_add_apply' h.1 (ContDiffOn.sum h.2) hs hx, IH h.2]

theorem iteratedFDeriv_sum {ι : Type*} {f : ι → E → F} {u : Finset ι} {i : ℕ}
    (h : ∀ j ∈ u, ContDiff 𝕜 i (f j)) :
    iteratedFDeriv 𝕜 i (∑ j ∈ u, f j ·) = ∑ j ∈ u, iteratedFDeriv 𝕜 i (f j) :=
  funext fun x ↦ by simpa [iteratedFDerivWithin_univ] using
    iteratedFDerivWithin_sum_apply uniqueDiffOn_univ (mem_univ x) fun j hj ↦ (h j hj).contDiffOn

/-! ### Product of two functions -/

section MulProd

variable {𝔸 𝔸' ι 𝕜' : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸] [NormedCommRing 𝔸']
  [NormedAlgebra 𝕜 𝔸'] [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']

-- The product is smooth.
theorem contDiff_mul : ContDiff 𝕜 n fun p : 𝔸 × 𝔸 => p.1 * p.2 :=
  (ContinuousLinearMap.mul 𝕜 𝔸).isBoundedBilinearMap.contDiff
#align cont_diff_mul contDiff_mul

/-- The product of two `C^n` functions within a set at a point is `C^n` within this set
at this point. -/
theorem ContDiffWithinAt.mul {s : Set E} {f g : E → 𝔸} (hf : ContDiffWithinAt 𝕜 n f s x)
    (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWithinAt 𝕜 n (fun x => f x * g x) s x :=
  contDiff_mul.comp_contDiffWithinAt (hf.prod hg)
#align cont_diff_within_at.mul ContDiffWithinAt.mul

/-- The product of two `C^n` functions at a point is `C^n` at this point. -/
nonrec theorem ContDiffAt.mul {f g : E → 𝔸} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    ContDiffAt 𝕜 n (fun x => f x * g x) x :=
  hf.mul hg
#align cont_diff_at.mul ContDiffAt.mul

/-- The product of two `C^n` functions on a domain is `C^n`. -/
theorem ContDiffOn.mul {f g : E → 𝔸} (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s) :
    ContDiffOn 𝕜 n (fun x => f x * g x) s := fun x hx => (hf x hx).mul (hg x hx)
#align cont_diff_on.mul ContDiffOn.mul

/-- The product of two `C^n`functions is `C^n`. -/
theorem ContDiff.mul {f g : E → 𝔸} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n fun x => f x * g x :=
  contDiff_mul.comp (hf.prod hg)
#align cont_diff.mul ContDiff.mul

theorem contDiffWithinAt_prod' {t : Finset ι} {f : ι → E → 𝔸'}
    (h : ∀ i ∈ t, ContDiffWithinAt 𝕜 n (f i) s x) : ContDiffWithinAt 𝕜 n (∏ i ∈ t, f i) s x :=
  Finset.prod_induction f (fun f => ContDiffWithinAt 𝕜 n f s x) (fun _ _ => ContDiffWithinAt.mul)
    (contDiffWithinAt_const (c := 1)) h
#align cont_diff_within_at_prod' contDiffWithinAt_prod'

theorem contDiffWithinAt_prod {t : Finset ι} {f : ι → E → 𝔸'}
    (h : ∀ i ∈ t, ContDiffWithinAt 𝕜 n (f i) s x) :
    ContDiffWithinAt 𝕜 n (fun y => ∏ i ∈ t, f i y) s x := by
  simpa only [← Finset.prod_apply] using contDiffWithinAt_prod' h
#align cont_diff_within_at_prod contDiffWithinAt_prod

theorem contDiffAt_prod' {t : Finset ι} {f : ι → E → 𝔸'} (h : ∀ i ∈ t, ContDiffAt 𝕜 n (f i) x) :
    ContDiffAt 𝕜 n (∏ i ∈ t, f i) x :=
  contDiffWithinAt_prod' h
#align cont_diff_at_prod' contDiffAt_prod'

theorem contDiffAt_prod {t : Finset ι} {f : ι → E → 𝔸'} (h : ∀ i ∈ t, ContDiffAt 𝕜 n (f i) x) :
    ContDiffAt 𝕜 n (fun y => ∏ i ∈ t, f i y) x :=
  contDiffWithinAt_prod h
#align cont_diff_at_prod contDiffAt_prod

theorem contDiffOn_prod' {t : Finset ι} {f : ι → E → 𝔸'} (h : ∀ i ∈ t, ContDiffOn 𝕜 n (f i) s) :
    ContDiffOn 𝕜 n (∏ i ∈ t, f i) s := fun x hx => contDiffWithinAt_prod' fun i hi => h i hi x hx
#align cont_diff_on_prod' contDiffOn_prod'

theorem contDiffOn_prod {t : Finset ι} {f : ι → E → 𝔸'} (h : ∀ i ∈ t, ContDiffOn 𝕜 n (f i) s) :
    ContDiffOn 𝕜 n (fun y => ∏ i ∈ t, f i y) s := fun x hx =>
  contDiffWithinAt_prod fun i hi => h i hi x hx
#align cont_diff_on_prod contDiffOn_prod

theorem contDiff_prod' {t : Finset ι} {f : ι → E → 𝔸'} (h : ∀ i ∈ t, ContDiff 𝕜 n (f i)) :
    ContDiff 𝕜 n (∏ i ∈ t, f i) :=
  contDiff_iff_contDiffAt.mpr fun _ => contDiffAt_prod' fun i hi => (h i hi).contDiffAt
#align cont_diff_prod' contDiff_prod'

theorem contDiff_prod {t : Finset ι} {f : ι → E → 𝔸'} (h : ∀ i ∈ t, ContDiff 𝕜 n (f i)) :
    ContDiff 𝕜 n fun y => ∏ i ∈ t, f i y :=
  contDiff_iff_contDiffAt.mpr fun _ => contDiffAt_prod fun i hi => (h i hi).contDiffAt
#align cont_diff_prod contDiff_prod

theorem ContDiff.pow {f : E → 𝔸} (hf : ContDiff 𝕜 n f) : ∀ m : ℕ, ContDiff 𝕜 n fun x => f x ^ m
  | 0 => by simpa using contDiff_const
  | m + 1 => by simpa [pow_succ] using (hf.pow m).mul hf
#align cont_diff.pow ContDiff.pow

theorem ContDiffWithinAt.pow {f : E → 𝔸} (hf : ContDiffWithinAt 𝕜 n f s x) (m : ℕ) :
    ContDiffWithinAt 𝕜 n (fun y => f y ^ m) s x :=
  (contDiff_id.pow m).comp_contDiffWithinAt hf
#align cont_diff_within_at.pow ContDiffWithinAt.pow

nonrec theorem ContDiffAt.pow {f : E → 𝔸} (hf : ContDiffAt 𝕜 n f x) (m : ℕ) :
    ContDiffAt 𝕜 n (fun y => f y ^ m) x :=
  hf.pow m
#align cont_diff_at.pow ContDiffAt.pow

theorem ContDiffOn.pow {f : E → 𝔸} (hf : ContDiffOn 𝕜 n f s) (m : ℕ) :
    ContDiffOn 𝕜 n (fun y => f y ^ m) s := fun y hy => (hf y hy).pow m
#align cont_diff_on.pow ContDiffOn.pow

theorem ContDiffWithinAt.div_const {f : E → 𝕜'} {n} (hf : ContDiffWithinAt 𝕜 n f s x) (c : 𝕜') :
    ContDiffWithinAt 𝕜 n (fun x => f x / c) s x := by
  simpa only [div_eq_mul_inv] using hf.mul contDiffWithinAt_const
#align cont_diff_within_at.div_const ContDiffWithinAt.div_const

nonrec theorem ContDiffAt.div_const {f : E → 𝕜'} {n} (hf : ContDiffAt 𝕜 n f x) (c : 𝕜') :
    ContDiffAt 𝕜 n (fun x => f x / c) x :=
  hf.div_const c
#align cont_diff_at.div_const ContDiffAt.div_const

theorem ContDiffOn.div_const {f : E → 𝕜'} {n} (hf : ContDiffOn 𝕜 n f s) (c : 𝕜') :
    ContDiffOn 𝕜 n (fun x => f x / c) s := fun x hx => (hf x hx).div_const c
#align cont_diff_on.div_const ContDiffOn.div_const

theorem ContDiff.div_const {f : E → 𝕜'} {n} (hf : ContDiff 𝕜 n f) (c : 𝕜') :
    ContDiff 𝕜 n fun x => f x / c := by simpa only [div_eq_mul_inv] using hf.mul contDiff_const
#align cont_diff.div_const ContDiff.div_const

end MulProd

/-! ### Scalar multiplication -/

section SMul

-- The scalar multiplication is smooth.
theorem contDiff_smul : ContDiff 𝕜 n fun p : 𝕜 × F => p.1 • p.2 :=
  isBoundedBilinearMap_smul.contDiff
#align cont_diff_smul contDiff_smul

/-- The scalar multiplication of two `C^n` functions within a set at a point is `C^n` within this
set at this point. -/
theorem ContDiffWithinAt.smul {s : Set E} {f : E → 𝕜} {g : E → F} (hf : ContDiffWithinAt 𝕜 n f s x)
    (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWithinAt 𝕜 n (fun x => f x • g x) s x :=
  contDiff_smul.contDiffWithinAt.comp x (hf.prod hg) subset_preimage_univ
#align cont_diff_within_at.smul ContDiffWithinAt.smul

/-- The scalar multiplication of two `C^n` functions at a point is `C^n` at this point. -/
theorem ContDiffAt.smul {f : E → 𝕜} {g : E → F} (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun x => f x • g x) x := by
  rw [← contDiffWithinAt_univ] at *; exact hf.smul hg
#align cont_diff_at.smul ContDiffAt.smul

/-- The scalar multiplication of two `C^n` functions is `C^n`. -/
theorem ContDiff.smul {f : E → 𝕜} {g : E → F} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n fun x => f x • g x :=
  contDiff_smul.comp (hf.prod hg)
#align cont_diff.smul ContDiff.smul

/-- The scalar multiplication of two `C^n` functions on a domain is `C^n`. -/
theorem ContDiffOn.smul {s : Set E} {f : E → 𝕜} {g : E → F} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x => f x • g x) s := fun x hx =>
  (hf x hx).smul (hg x hx)
#align cont_diff_on.smul ContDiffOn.smul

end SMul

/-! ### Constant scalar multiplication

Porting note (#11215): TODO: generalize results in this section.

1. It should be possible to assume `[Monoid R] [DistribMulAction R F] [SMulCommClass 𝕜 R F]`.
2. If `c` is a unit (or `R` is a group), then one can drop `ContDiff*` assumptions in some
  lemmas.
-/

section ConstSMul

variable {R : Type*} [Semiring R] [Module R F] [SMulCommClass 𝕜 R F]
variable [ContinuousConstSMul R F]

-- The scalar multiplication with a constant is smooth.
theorem contDiff_const_smul (c : R) : ContDiff 𝕜 n fun p : F => c • p :=
  (c • ContinuousLinearMap.id 𝕜 F).contDiff
#align cont_diff_const_smul contDiff_const_smul

/-- The scalar multiplication of a constant and a `C^n` function within a set at a point is `C^n`
within this set at this point. -/
theorem ContDiffWithinAt.const_smul {s : Set E} {f : E → F} {x : E} (c : R)
    (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWithinAt 𝕜 n (fun y => c • f y) s x :=
  (contDiff_const_smul c).contDiffAt.comp_contDiffWithinAt x hf
#align cont_diff_within_at.const_smul ContDiffWithinAt.const_smul

/-- The scalar multiplication of a constant and a `C^n` function at a point is `C^n` at this
point. -/
theorem ContDiffAt.const_smul {f : E → F} {x : E} (c : R) (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun y => c • f y) x := by
  rw [← contDiffWithinAt_univ] at *; exact hf.const_smul c
#align cont_diff_at.const_smul ContDiffAt.const_smul

/-- The scalar multiplication of a constant and a `C^n` function is `C^n`. -/
theorem ContDiff.const_smul {f : E → F} (c : R) (hf : ContDiff 𝕜 n f) :
    ContDiff 𝕜 n fun y => c • f y :=
  (contDiff_const_smul c).comp hf
#align cont_diff.const_smul ContDiff.const_smul

/-- The scalar multiplication of a constant and a `C^n` on a domain is `C^n`. -/
theorem ContDiffOn.const_smul {s : Set E} {f : E → F} (c : R) (hf : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (fun y => c • f y) s := fun x hx => (hf x hx).const_smul c
#align cont_diff_on.const_smul ContDiffOn.const_smul

variable {i : ℕ} {a : R}

theorem iteratedFDerivWithin_const_smul_apply (hf : ContDiffOn 𝕜 i f s) (hu : UniqueDiffOn 𝕜 s)
    (hx : x ∈ s) : iteratedFDerivWithin 𝕜 i (a • f) s x = a • iteratedFDerivWithin 𝕜 i f s x :=
  (a • (1 : F →L[𝕜] F)).iteratedFDerivWithin_comp_left hf hu hx le_rfl
#align iterated_fderiv_within_const_smul_apply iteratedFDerivWithin_const_smul_apply

theorem iteratedFDeriv_const_smul_apply {x : E} (hf : ContDiff 𝕜 i f) :
    iteratedFDeriv 𝕜 i (a • f) x = a • iteratedFDeriv 𝕜 i f x := by
  simp_rw [← contDiffOn_univ, ← iteratedFDerivWithin_univ] at *
  exact iteratedFDerivWithin_const_smul_apply hf uniqueDiffOn_univ (Set.mem_univ _)
#align iterated_fderiv_const_smul_apply iteratedFDeriv_const_smul_apply

theorem iteratedFDeriv_const_smul_apply' {x : E} (hf : ContDiff 𝕜 i f) :
    iteratedFDeriv 𝕜 i (fun x ↦ a • f x) x = a • iteratedFDeriv 𝕜 i f x :=
  iteratedFDeriv_const_smul_apply hf

end ConstSMul

/-! ### Cartesian product of two functions -/

section prodMap

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
theorem ContDiffWithinAt.prod_map' {s : Set E} {t : Set E'} {f : E → F} {g : E' → F'} {p : E × E'}
    (hf : ContDiffWithinAt 𝕜 n f s p.1) (hg : ContDiffWithinAt 𝕜 n g t p.2) :
    ContDiffWithinAt 𝕜 n (Prod.map f g) (s ×ˢ t) p :=
  (hf.comp p contDiffWithinAt_fst (prod_subset_preimage_fst _ _)).prod
    (hg.comp p contDiffWithinAt_snd (prod_subset_preimage_snd _ _))
#align cont_diff_within_at.prod_map' ContDiffWithinAt.prod_map'

theorem ContDiffWithinAt.prod_map {s : Set E} {t : Set E'} {f : E → F} {g : E' → F'} {x : E}
    {y : E'} (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g t y) :
    ContDiffWithinAt 𝕜 n (Prod.map f g) (s ×ˢ t) (x, y) :=
  ContDiffWithinAt.prod_map' hf hg
#align cont_diff_within_at.prod_map ContDiffWithinAt.prod_map

/-- The product map of two `C^n` functions on a set is `C^n` on the product set. -/
theorem ContDiffOn.prod_map {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {F' : Type*}
    [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {s : Set E} {t : Set E'} {f : E → F} {g : E' → F'}
    (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g t) : ContDiffOn 𝕜 n (Prod.map f g) (s ×ˢ t) :=
  (hf.comp contDiffOn_fst (prod_subset_preimage_fst _ _)).prod
    (hg.comp contDiffOn_snd (prod_subset_preimage_snd _ _))
#align cont_diff_on.prod_map ContDiffOn.prod_map

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
theorem ContDiffAt.prod_map {f : E → F} {g : E' → F'} {x : E} {y : E'} (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g y) : ContDiffAt 𝕜 n (Prod.map f g) (x, y) := by
  rw [ContDiffAt] at *
  convert hf.prod_map hg
  simp only [univ_prod_univ]
#align cont_diff_at.prod_map ContDiffAt.prod_map

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
theorem ContDiffAt.prod_map' {f : E → F} {g : E' → F'} {p : E × E'} (hf : ContDiffAt 𝕜 n f p.1)
    (hg : ContDiffAt 𝕜 n g p.2) : ContDiffAt 𝕜 n (Prod.map f g) p := by
  rcases p with ⟨⟩
  exact ContDiffAt.prod_map hf hg
#align cont_diff_at.prod_map' ContDiffAt.prod_map'

/-- The product map of two `C^n` functions is `C^n`. -/
theorem ContDiff.prod_map {f : E → F} {g : E' → F'} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n (Prod.map f g) := by
  rw [contDiff_iff_contDiffAt] at *
  exact fun ⟨x, y⟩ => (hf x).prod_map (hg y)
#align cont_diff.prod_map ContDiff.prod_map

theorem contDiff_prod_mk_left (f₀ : F) : ContDiff 𝕜 n fun e : E => (e, f₀) :=
  contDiff_id.prod contDiff_const
#align cont_diff_prod_mk_left contDiff_prod_mk_left

theorem contDiff_prod_mk_right (e₀ : E) : ContDiff 𝕜 n fun f : F => (e₀, f) :=
  contDiff_const.prod contDiff_id
#align cont_diff_prod_mk_right contDiff_prod_mk_right

end prodMap

/-! ### Inversion in a complete normed algebra -/

section AlgebraInverse

variable (𝕜) {R : Type*} [NormedRing R]
-- Porting note: this couldn't be on the same line as the binder type update of `𝕜`
variable [NormedAlgebra 𝕜 R]

open NormedRing ContinuousLinearMap Ring

/-- In a complete normed algebra, the operation of inversion is `C^n`, for all `n`, at each
invertible element.  The proof is by induction, bootstrapping using an identity expressing the
derivative of inversion as a bilinear map of inversion itself. -/
theorem contDiffAt_ring_inverse [CompleteSpace R] (x : Rˣ) :
    ContDiffAt 𝕜 n Ring.inverse (x : R) := by
  induction' n using ENat.nat_induction with n IH Itop
  · intro m hm
    refine ⟨{ y : R | IsUnit y }, ?_, ?_⟩
    · simp [nhdsWithin_univ]
      exact x.nhds
    · use ftaylorSeriesWithin 𝕜 inverse univ
      rw [le_antisymm hm bot_le, hasFTaylorSeriesUpToOn_zero_iff]
      constructor
      · rintro _ ⟨x', rfl⟩
        exact (inverse_continuousAt x').continuousWithinAt
      · simp [ftaylorSeriesWithin]
  · rw [contDiffAt_succ_iff_hasFDerivAt]
    refine ⟨fun x : R => -mulLeftRight 𝕜 R (inverse x) (inverse x), ?_, ?_⟩
    · refine ⟨{ y : R | IsUnit y }, x.nhds, ?_⟩
      rintro _ ⟨y, rfl⟩
      simp_rw [inverse_unit]
      exact hasFDerivAt_ring_inverse y
    · convert (mulLeftRight_isBoundedBilinear 𝕜 R).contDiff.neg.comp_contDiffAt (x : R)
        (IH.prod IH)
  · exact contDiffAt_top.mpr Itop
#align cont_diff_at_ring_inverse contDiffAt_ring_inverse

variable {𝕜' : Type*} [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [CompleteSpace 𝕜']

theorem contDiffAt_inv {x : 𝕜'} (hx : x ≠ 0) {n} : ContDiffAt 𝕜 n Inv.inv x := by
  simpa only [Ring.inverse_eq_inv'] using contDiffAt_ring_inverse 𝕜 (Units.mk0 x hx)
#align cont_diff_at_inv contDiffAt_inv

theorem contDiffOn_inv {n} : ContDiffOn 𝕜 n (Inv.inv : 𝕜' → 𝕜') {0}ᶜ := fun _ hx =>
  (contDiffAt_inv 𝕜 hx).contDiffWithinAt
#align cont_diff_on_inv contDiffOn_inv

variable {𝕜}

-- TODO: the next few lemmas don't need `𝕜` or `𝕜'` to be complete
-- A good way to show this is to generalize `contDiffAt_ring_inverse` to the setting
-- of a function `f` such that `∀ᶠ x in 𝓝 a, x * f x = 1`.
theorem ContDiffWithinAt.inv {f : E → 𝕜'} {n} (hf : ContDiffWithinAt 𝕜 n f s x) (hx : f x ≠ 0) :
    ContDiffWithinAt 𝕜 n (fun x => (f x)⁻¹) s x :=
  (contDiffAt_inv 𝕜 hx).comp_contDiffWithinAt x hf
#align cont_diff_within_at.inv ContDiffWithinAt.inv

theorem ContDiffOn.inv {f : E → 𝕜'} {n} (hf : ContDiffOn 𝕜 n f s) (h : ∀ x ∈ s, f x ≠ 0) :
    ContDiffOn 𝕜 n (fun x => (f x)⁻¹) s := fun x hx => (hf.contDiffWithinAt hx).inv (h x hx)
#align cont_diff_on.inv ContDiffOn.inv

nonrec theorem ContDiffAt.inv {f : E → 𝕜'} {n} (hf : ContDiffAt 𝕜 n f x) (hx : f x ≠ 0) :
    ContDiffAt 𝕜 n (fun x => (f x)⁻¹) x :=
  hf.inv hx
#align cont_diff_at.inv ContDiffAt.inv

theorem ContDiff.inv {f : E → 𝕜'} {n} (hf : ContDiff 𝕜 n f) (h : ∀ x, f x ≠ 0) :
    ContDiff 𝕜 n fun x => (f x)⁻¹ := by
  rw [contDiff_iff_contDiffAt]; exact fun x => hf.contDiffAt.inv (h x)
#align cont_diff.inv ContDiff.inv

-- TODO: generalize to `f g : E → 𝕜'`
theorem ContDiffWithinAt.div [CompleteSpace 𝕜] {f g : E → 𝕜} {n} (hf : ContDiffWithinAt 𝕜 n f s x)
    (hg : ContDiffWithinAt 𝕜 n g s x) (hx : g x ≠ 0) :
    ContDiffWithinAt 𝕜 n (fun x => f x / g x) s x := by
  simpa only [div_eq_mul_inv] using hf.mul (hg.inv hx)
#align cont_diff_within_at.div ContDiffWithinAt.div

theorem ContDiffOn.div [CompleteSpace 𝕜] {f g : E → 𝕜} {n} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g s) (h₀ : ∀ x ∈ s, g x ≠ 0) : ContDiffOn 𝕜 n (f / g) s := fun x hx =>
  (hf x hx).div (hg x hx) (h₀ x hx)
#align cont_diff_on.div ContDiffOn.div

nonrec theorem ContDiffAt.div [CompleteSpace 𝕜] {f g : E → 𝕜} {n} (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g x) (hx : g x ≠ 0) : ContDiffAt 𝕜 n (fun x => f x / g x) x :=
  hf.div hg hx
#align cont_diff_at.div ContDiffAt.div

theorem ContDiff.div [CompleteSpace 𝕜] {f g : E → 𝕜} {n} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g)
    (h0 : ∀ x, g x ≠ 0) : ContDiff 𝕜 n fun x => f x / g x := by
  simp only [contDiff_iff_contDiffAt] at *
  exact fun x => (hf x).div (hg x) (h0 x)
#align cont_diff.div ContDiff.div

end AlgebraInverse

/-! ### Inversion of continuous linear maps between Banach spaces -/

section MapInverse

open ContinuousLinearMap

/-- At a continuous linear equivalence `e : E ≃L[𝕜] F` between Banach spaces, the operation of
inversion is `C^n`, for all `n`. -/
theorem contDiffAt_map_inverse [CompleteSpace E] (e : E ≃L[𝕜] F) :
    ContDiffAt 𝕜 n inverse (e : E →L[𝕜] F) := by
  nontriviality E
  -- first, we use the lemma `to_ring_inverse` to rewrite in terms of `Ring.inverse` in the ring
  -- `E →L[𝕜] E`
  let O₁ : (E →L[𝕜] E) → F →L[𝕜] E := fun f => f.comp (e.symm : F →L[𝕜] E)
  let O₂ : (E →L[𝕜] F) → E →L[𝕜] E := fun f => (e.symm : F →L[𝕜] E).comp f
  have : ContinuousLinearMap.inverse = O₁ ∘ Ring.inverse ∘ O₂ := funext (to_ring_inverse e)
  rw [this]
  -- `O₁` and `O₂` are `ContDiff`,
  -- so we reduce to proving that `Ring.inverse` is `ContDiff`
  have h₁ : ContDiff 𝕜 n O₁ := contDiff_id.clm_comp contDiff_const
  have h₂ : ContDiff 𝕜 n O₂ := contDiff_const.clm_comp contDiff_id
  refine h₁.contDiffAt.comp _ (ContDiffAt.comp _ ?_ h₂.contDiffAt)
  convert contDiffAt_ring_inverse 𝕜 (1 : (E →L[𝕜] E)ˣ)
  simp [O₂, one_def]
#align cont_diff_at_map_inverse contDiffAt_map_inverse

end MapInverse

section FunctionInverse

open ContinuousLinearMap

/-- If `f` is a local homeomorphism and the point `a` is in its target,
and if `f` is `n` times continuously differentiable at `f.symm a`,
and if the derivative at `f.symm a` is a continuous linear equivalence,
then `f.symm` is `n` times continuously differentiable at the point `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem PartialHomeomorph.contDiffAt_symm [CompleteSpace E] (f : PartialHomeomorph E F)
    {f₀' : E ≃L[𝕜] F} {a : F} (ha : a ∈ f.target)
    (hf₀' : HasFDerivAt f (f₀' : E →L[𝕜] F) (f.symm a)) (hf : ContDiffAt 𝕜 n f (f.symm a)) :
    ContDiffAt 𝕜 n f.symm a := by
  -- We prove this by induction on `n`
  induction' n using ENat.nat_induction with n IH Itop
  · rw [contDiffAt_zero]
    exact ⟨f.target, IsOpen.mem_nhds f.open_target ha, f.continuousOn_invFun⟩
  · obtain ⟨f', ⟨u, hu, hff'⟩, hf'⟩ := contDiffAt_succ_iff_hasFDerivAt.mp hf
    rw [contDiffAt_succ_iff_hasFDerivAt]
    -- For showing `n.succ` times continuous differentiability (the main inductive step), it
    -- suffices to produce the derivative and show that it is `n` times continuously differentiable
    have eq_f₀' : f' (f.symm a) = f₀' := (hff' (f.symm a) (mem_of_mem_nhds hu)).unique hf₀'
    -- This follows by a bootstrapping formula expressing the derivative as a function of `f` itself
    refine ⟨inverse ∘ f' ∘ f.symm, ?_, ?_⟩
    · -- We first check that the derivative of `f` is that formula
      have h_nhds : { y : E | ∃ e : E ≃L[𝕜] F, ↑e = f' y } ∈ 𝓝 (f.symm a) := by
        have hf₀' := f₀'.nhds
        rw [← eq_f₀'] at hf₀'
        exact hf'.continuousAt.preimage_mem_nhds hf₀'
      obtain ⟨t, htu, ht, htf⟩ := mem_nhds_iff.mp (Filter.inter_mem hu h_nhds)
      use f.target ∩ f.symm ⁻¹' t
      refine ⟨IsOpen.mem_nhds ?_ ?_, ?_⟩
      · exact f.isOpen_inter_preimage_symm ht
      · exact mem_inter ha (mem_preimage.mpr htf)
      intro x hx
      obtain ⟨hxu, e, he⟩ := htu hx.2
      have h_deriv : HasFDerivAt f (e : E →L[𝕜] F) (f.symm x) := by
        rw [he]
        exact hff' (f.symm x) hxu
      convert f.hasFDerivAt_symm hx.1 h_deriv
      simp [← he]
    · -- Then we check that the formula, being a composition of `ContDiff` pieces, is
      -- itself `ContDiff`
      have h_deriv₁ : ContDiffAt 𝕜 n inverse (f' (f.symm a)) := by
        rw [eq_f₀']
        exact contDiffAt_map_inverse _
      have h_deriv₂ : ContDiffAt 𝕜 n f.symm a := by
        refine IH (hf.of_le ?_)
        norm_cast
        exact Nat.le_succ n
      exact (h_deriv₁.comp _ hf').comp _ h_deriv₂
  · refine contDiffAt_top.mpr ?_
    intro n
    exact Itop n (contDiffAt_top.mp hf n)
#align local_homeomorph.cont_diff_at_symm PartialHomeomorph.contDiffAt_symm

/-- If `f` is an `n` times continuously differentiable homeomorphism,
and if the derivative of `f` at each point is a continuous linear equivalence,
then `f.symm` is `n` times continuously differentiable.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem Homeomorph.contDiff_symm [CompleteSpace E] (f : E ≃ₜ F) {f₀' : E → E ≃L[𝕜] F}
    (hf₀' : ∀ a, HasFDerivAt f (f₀' a : E →L[𝕜] F) a) (hf : ContDiff 𝕜 n (f : E → F)) :
    ContDiff 𝕜 n (f.symm : F → E) :=
  contDiff_iff_contDiffAt.2 fun x =>
    f.toPartialHomeomorph.contDiffAt_symm (mem_univ x) (hf₀' _) hf.contDiffAt
#align homeomorph.cont_diff_symm Homeomorph.contDiff_symm

/-- Let `f` be a local homeomorphism of a nontrivially normed field, let `a` be a point in its
target. if `f` is `n` times continuously differentiable at `f.symm a`, and if the derivative at
`f.symm a` is nonzero, then `f.symm` is `n` times continuously differentiable at the point `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem PartialHomeomorph.contDiffAt_symm_deriv [CompleteSpace 𝕜] (f : PartialHomeomorph 𝕜 𝕜)
    {f₀' a : 𝕜} (h₀ : f₀' ≠ 0) (ha : a ∈ f.target) (hf₀' : HasDerivAt f f₀' (f.symm a))
    (hf : ContDiffAt 𝕜 n f (f.symm a)) : ContDiffAt 𝕜 n f.symm a :=
  f.contDiffAt_symm ha (hf₀'.hasFDerivAt_equiv h₀) hf
#align local_homeomorph.cont_diff_at_symm_deriv PartialHomeomorph.contDiffAt_symm_deriv

/-- Let `f` be an `n` times continuously differentiable homeomorphism of a nontrivially normed
field.  Suppose that the derivative of `f` is never equal to zero. Then `f.symm` is `n` times
continuously differentiable.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem Homeomorph.contDiff_symm_deriv [CompleteSpace 𝕜] (f : 𝕜 ≃ₜ 𝕜) {f' : 𝕜 → 𝕜}
    (h₀ : ∀ x, f' x ≠ 0) (hf' : ∀ x, HasDerivAt f (f' x) x) (hf : ContDiff 𝕜 n (f : 𝕜 → 𝕜)) :
    ContDiff 𝕜 n (f.symm : 𝕜 → 𝕜) :=
  contDiff_iff_contDiffAt.2 fun x =>
    f.toPartialHomeomorph.contDiffAt_symm_deriv (h₀ _) (mem_univ x) (hf' _) hf.contDiffAt
#align homeomorph.cont_diff_symm_deriv Homeomorph.contDiff_symm_deriv

namespace PartialHomeomorph

variable (𝕜)

/-- Restrict a partial homeomorphism to the subsets of the source and target
that consist of points `x ∈ f.source`, `y = f x ∈ f.target`
such that `f` is `C^n` at `x` and `f.symm` is `C^n` at `y`.

Note that `n` is a natural number, not `∞`,
because the set of points of `C^∞`-smoothness of `f` is not guaranteed to be open. -/
@[simps! apply symm_apply source target]
def restrContDiff (f : PartialHomeomorph E F) (n : ℕ) : PartialHomeomorph E F :=
  haveI H : f.IsImage {x | ContDiffAt 𝕜 n f x ∧ ContDiffAt 𝕜 n f.symm (f x)}
      {y | ContDiffAt 𝕜 n f.symm y ∧ ContDiffAt 𝕜 n f (f.symm y)} := fun x hx ↦ by
    simp [hx, and_comm]
  H.restr <| isOpen_iff_mem_nhds.2 fun x ⟨hxs, hxf, hxf'⟩ ↦
    inter_mem (f.open_source.mem_nhds hxs) <| hxf.eventually.and <|
    f.continuousAt hxs hxf'.eventually

lemma contDiffOn_restrContDiff_source (f : PartialHomeomorph E F) (n : ℕ) :
    ContDiffOn 𝕜 n f (f.restrContDiff 𝕜 n).source := fun _x hx ↦ hx.2.1.contDiffWithinAt

lemma contDiffOn_restrContDiff_target (f : PartialHomeomorph E F) (n : ℕ) :
    ContDiffOn 𝕜 n f.symm (f.restrContDiff 𝕜 n).target := fun _x hx ↦ hx.2.1.contDiffWithinAt

end PartialHomeomorph

end FunctionInverse

section deriv

/-!
### One dimension

All results up to now have been expressed in terms of the general Fréchet derivative `fderiv`. For
maps defined on the field, the one-dimensional derivative `deriv` is often easier to use. In this
paragraph, we reformulate some higher smoothness results in terms of `deriv`.
-/


variable {f₂ : 𝕜 → F} {s₂ : Set 𝕜}

open ContinuousLinearMap (smulRight)

/-- A function is `C^(n + 1)` on a domain with unique derivatives if and only if it is
differentiable there, and its derivative (formulated with `derivWithin`) is `C^n`. -/
theorem contDiffOn_succ_iff_derivWithin {n : ℕ} (hs : UniqueDiffOn 𝕜 s₂) :
    ContDiffOn 𝕜 (n + 1 : ℕ) f₂ s₂ ↔
      DifferentiableOn 𝕜 f₂ s₂ ∧ ContDiffOn 𝕜 n (derivWithin f₂ s₂) s₂ := by
  rw [contDiffOn_succ_iff_fderivWithin hs, and_congr_right_iff]
  intro _
  constructor
  · intro h
    have : derivWithin f₂ s₂ = (fun u : 𝕜 →L[𝕜] F => u 1) ∘ fderivWithin 𝕜 f₂ s₂ := by
      ext x; rfl
    simp_rw [this]
    apply ContDiff.comp_contDiffOn _ h
    exact (isBoundedBilinearMap_apply.isBoundedLinearMap_left _).contDiff
  · intro h
    have : fderivWithin 𝕜 f₂ s₂ = smulRight (1 : 𝕜 →L[𝕜] 𝕜) ∘ derivWithin f₂ s₂ := by
      ext x; simp [derivWithin]
    simp only [this]
    apply ContDiff.comp_contDiffOn _ h
    have : IsBoundedBilinearMap 𝕜 fun _ : (𝕜 →L[𝕜] 𝕜) × F => _ := isBoundedBilinearMap_smulRight
    exact (this.isBoundedLinearMap_right _).contDiff
#align cont_diff_on_succ_iff_deriv_within contDiffOn_succ_iff_derivWithin

/-- A function is `C^(n + 1)` on an open domain if and only if it is
differentiable there, and its derivative (formulated with `deriv`) is `C^n`. -/
theorem contDiffOn_succ_iff_deriv_of_isOpen {n : ℕ} (hs : IsOpen s₂) :
    ContDiffOn 𝕜 (n + 1 : ℕ) f₂ s₂ ↔ DifferentiableOn 𝕜 f₂ s₂ ∧ ContDiffOn 𝕜 n (deriv f₂) s₂ := by
  rw [contDiffOn_succ_iff_derivWithin hs.uniqueDiffOn]
  exact Iff.rfl.and (contDiffOn_congr fun _ => derivWithin_of_isOpen hs)
#align cont_diff_on_succ_iff_deriv_of_open contDiffOn_succ_iff_deriv_of_isOpen

/-- A function is `C^∞` on a domain with unique derivatives if and only if it is differentiable
there, and its derivative (formulated with `derivWithin`) is `C^∞`. -/
theorem contDiffOn_top_iff_derivWithin (hs : UniqueDiffOn 𝕜 s₂) :
    ContDiffOn 𝕜 ∞ f₂ s₂ ↔ DifferentiableOn 𝕜 f₂ s₂ ∧ ContDiffOn 𝕜 ∞ (derivWithin f₂ s₂) s₂ := by
  constructor
  · intro h
    refine ⟨h.differentiableOn le_top, ?_⟩
    refine contDiffOn_top.2 fun n => ((contDiffOn_succ_iff_derivWithin hs).1 ?_).2
    exact h.of_le le_top
  · intro h
    refine contDiffOn_top.2 fun n => ?_
    have A : (n : ℕ∞) ≤ ∞ := le_top
    apply ((contDiffOn_succ_iff_derivWithin hs).2 ⟨h.1, h.2.of_le A⟩).of_le
    exact WithTop.coe_le_coe.2 (Nat.le_succ n)
#align cont_diff_on_top_iff_deriv_within contDiffOn_top_iff_derivWithin

/-- A function is `C^∞` on an open domain if and only if it is differentiable
there, and its derivative (formulated with `deriv`) is `C^∞`. -/
theorem contDiffOn_top_iff_deriv_of_isOpen (hs : IsOpen s₂) :
    ContDiffOn 𝕜 ∞ f₂ s₂ ↔ DifferentiableOn 𝕜 f₂ s₂ ∧ ContDiffOn 𝕜 ∞ (deriv f₂) s₂ := by
  rw [contDiffOn_top_iff_derivWithin hs.uniqueDiffOn]
  exact Iff.rfl.and <| contDiffOn_congr fun _ => derivWithin_of_isOpen hs
#align cont_diff_on_top_iff_deriv_of_open contDiffOn_top_iff_deriv_of_isOpen

protected theorem ContDiffOn.derivWithin (hf : ContDiffOn 𝕜 n f₂ s₂) (hs : UniqueDiffOn 𝕜 s₂)
    (hmn : m + 1 ≤ n) : ContDiffOn 𝕜 m (derivWithin f₂ s₂) s₂ := by
  cases m
  · change ∞ + 1 ≤ n at hmn
    have : n = ∞ := by simpa using hmn
    rw [this] at hf
    exact ((contDiffOn_top_iff_derivWithin hs).1 hf).2
  · change (Nat.succ _ : ℕ∞) ≤ n at hmn
    exact ((contDiffOn_succ_iff_derivWithin hs).1 (hf.of_le hmn)).2
#align cont_diff_on.deriv_within ContDiffOn.derivWithin

theorem ContDiffOn.deriv_of_isOpen (hf : ContDiffOn 𝕜 n f₂ s₂) (hs : IsOpen s₂) (hmn : m + 1 ≤ n) :
    ContDiffOn 𝕜 m (deriv f₂) s₂ :=
  (hf.derivWithin hs.uniqueDiffOn hmn).congr fun _ hx => (derivWithin_of_isOpen hs hx).symm
#align cont_diff_on.deriv_of_open ContDiffOn.deriv_of_isOpen

theorem ContDiffOn.continuousOn_derivWithin (h : ContDiffOn 𝕜 n f₂ s₂) (hs : UniqueDiffOn 𝕜 s₂)
    (hn : 1 ≤ n) : ContinuousOn (derivWithin f₂ s₂) s₂ :=
  ((contDiffOn_succ_iff_derivWithin hs).1 (h.of_le hn)).2.continuousOn
#align cont_diff_on.continuous_on_deriv_within ContDiffOn.continuousOn_derivWithin

theorem ContDiffOn.continuousOn_deriv_of_isOpen (h : ContDiffOn 𝕜 n f₂ s₂) (hs : IsOpen s₂)
    (hn : 1 ≤ n) : ContinuousOn (deriv f₂) s₂ :=
  ((contDiffOn_succ_iff_deriv_of_isOpen hs).1 (h.of_le hn)).2.continuousOn
#align cont_diff_on.continuous_on_deriv_of_open ContDiffOn.continuousOn_deriv_of_isOpen

/-- A function is `C^(n + 1)` if and only if it is differentiable,
  and its derivative (formulated in terms of `deriv`) is `C^n`. -/
theorem contDiff_succ_iff_deriv {n : ℕ} :
    ContDiff 𝕜 (n + 1 : ℕ) f₂ ↔ Differentiable 𝕜 f₂ ∧ ContDiff 𝕜 n (deriv f₂) := by
  simp only [← contDiffOn_univ, contDiffOn_succ_iff_deriv_of_isOpen, isOpen_univ,
    differentiableOn_univ]
#align cont_diff_succ_iff_deriv contDiff_succ_iff_deriv

theorem contDiff_one_iff_deriv : ContDiff 𝕜 1 f₂ ↔ Differentiable 𝕜 f₂ ∧ Continuous (deriv f₂) :=
  contDiff_succ_iff_deriv.trans <| Iff.rfl.and contDiff_zero
#align cont_diff_one_iff_deriv contDiff_one_iff_deriv

/-- A function is `C^∞` if and only if it is differentiable,
and its derivative (formulated in terms of `deriv`) is `C^∞`. -/
theorem contDiff_top_iff_deriv :
    ContDiff 𝕜 ∞ f₂ ↔ Differentiable 𝕜 f₂ ∧ ContDiff 𝕜 ∞ (deriv f₂) := by
  simp only [← contDiffOn_univ, ← differentiableOn_univ, ← derivWithin_univ]
  rw [contDiffOn_top_iff_derivWithin uniqueDiffOn_univ]
#align cont_diff_top_iff_deriv contDiff_top_iff_deriv

theorem ContDiff.continuous_deriv (h : ContDiff 𝕜 n f₂) (hn : 1 ≤ n) : Continuous (deriv f₂) :=
  (contDiff_succ_iff_deriv.mp (h.of_le hn)).2.continuous
#align cont_diff.continuous_deriv ContDiff.continuous_deriv

theorem ContDiff.iterate_deriv :
    ∀ (n : ℕ) {f₂ : 𝕜 → F}, ContDiff 𝕜 ∞ f₂ → ContDiff 𝕜 ∞ (deriv^[n] f₂)
  | 0,     _, hf => hf
  | n + 1, _, hf => ContDiff.iterate_deriv n (contDiff_top_iff_deriv.mp hf).2
#align cont_diff.iterate_deriv ContDiff.iterate_deriv

theorem ContDiff.iterate_deriv' (n : ℕ) :
    ∀ (k : ℕ) {f₂ : 𝕜 → F}, ContDiff 𝕜 (n + k : ℕ) f₂ → ContDiff 𝕜 n (deriv^[k] f₂)
  | 0,     _, hf => hf
  | k + 1, _, hf => ContDiff.iterate_deriv' _ k (contDiff_succ_iff_deriv.mp hf).2
#align cont_diff.iterate_deriv' ContDiff.iterate_deriv'

end deriv

section RestrictScalars

/-!
### Restricting from `ℂ` to `ℝ`, or generally from `𝕜'` to `𝕜`

If a function is `n` times continuously differentiable over `ℂ`, then it is `n` times continuously
differentiable over `ℝ`. In this paragraph, we give variants of this statement, in the general
situation where `ℂ` and `ℝ` are replaced respectively by `𝕜'` and `𝕜` where `𝕜'` is a normed algebra
over `𝕜`.
-/


variable (𝕜) {𝕜' : Type*} [NontriviallyNormedField 𝕜']
-- Porting note: this couldn't be on the same line as the binder type update of `𝕜`
variable [NormedAlgebra 𝕜 𝕜']
variable [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E]
variable [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]
variable {p' : E → FormalMultilinearSeries 𝕜' E F}

theorem HasFTaylorSeriesUpToOn.restrictScalars (h : HasFTaylorSeriesUpToOn n f p' s) :
    HasFTaylorSeriesUpToOn n f (fun x => (p' x).restrictScalars 𝕜) s where
  zero_eq x hx := h.zero_eq x hx
  fderivWithin m hm x hx := by
    simpa only using -- Porting note: added `by simpa only using`
      (ContinuousMultilinearMap.restrictScalarsLinear 𝕜).hasFDerivAt.comp_hasFDerivWithinAt x <|
        (h.fderivWithin m hm x hx).restrictScalars 𝕜
  cont m hm := ContinuousMultilinearMap.continuous_restrictScalars.comp_continuousOn (h.cont m hm)
#align has_ftaylor_series_up_to_on.restrict_scalars HasFTaylorSeriesUpToOn.restrictScalars

theorem ContDiffWithinAt.restrict_scalars (h : ContDiffWithinAt 𝕜' n f s x) :
    ContDiffWithinAt 𝕜 n f s x := fun m hm ↦ by
  rcases h m hm with ⟨u, u_mem, p', hp'⟩
  exact ⟨u, u_mem, _, hp'.restrictScalars _⟩
#align cont_diff_within_at.restrict_scalars ContDiffWithinAt.restrict_scalars

theorem ContDiffOn.restrict_scalars (h : ContDiffOn 𝕜' n f s) : ContDiffOn 𝕜 n f s := fun x hx =>
  (h x hx).restrict_scalars _
#align cont_diff_on.restrict_scalars ContDiffOn.restrict_scalars

theorem ContDiffAt.restrict_scalars (h : ContDiffAt 𝕜' n f x) : ContDiffAt 𝕜 n f x :=
  contDiffWithinAt_univ.1 <| h.contDiffWithinAt.restrict_scalars _
#align cont_diff_at.restrict_scalars ContDiffAt.restrict_scalars

theorem ContDiff.restrict_scalars (h : ContDiff 𝕜' n f) : ContDiff 𝕜 n f :=
  contDiff_iff_contDiffAt.2 fun _ => h.contDiffAt.restrict_scalars _
#align cont_diff.restrict_scalars ContDiff.restrict_scalars

end RestrictScalars
