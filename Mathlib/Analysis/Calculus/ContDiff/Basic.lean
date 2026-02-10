/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Affine

/-!
# Basic properties of continuously-differentiable functions

This file continues the development of the API for `ContDiff`, `ContDiffAt`, etc, covering
constants, products, composition with linear maps, etc.

## Tags

derivative, differentiability, higher derivative, `C^n`, multilinear, Taylor series, formal series
-/

public noncomputable section

open Set Fin Filter Function

open scoped Topology ContDiff

attribute [local instance 1001] NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {s t : Set E} {f : E → F} {x : E} {b : E × F → G} {m n : WithTop ℕ∞}
  {p : E → FormalMultilinearSeries 𝕜 E F}

/-! ### Constants -/
section constants

theorem iteratedFDerivWithin_succ_const (n : ℕ) (c : F) :
    iteratedFDerivWithin 𝕜 (n + 1) (fun _ : E ↦ c) s = 0 := by
  induction n with
  | zero =>
    ext1
    simp [iteratedFDerivWithin_succ_eq_comp_left, iteratedFDerivWithin_zero_eq_comp, comp_def]
  | succ n IH =>
    rw [iteratedFDerivWithin_succ_eq_comp_left, IH]
    simp only [Pi.zero_def, comp_def, fderivWithin_fun_const, map_zero]

@[simp]
theorem iteratedFDerivWithin_zero_fun {i : ℕ} :
    iteratedFDerivWithin 𝕜 i (fun _ : E ↦ (0 : F)) s = 0 := by
  cases i with
  | zero => ext; simp
  | succ i => apply iteratedFDerivWithin_succ_const

@[simp]
theorem iteratedFDeriv_zero_fun {n : ℕ} : (iteratedFDeriv 𝕜 n fun _ : E ↦ (0 : F)) = 0 :=
  funext fun x ↦ by simp only [← iteratedFDerivWithin_univ, iteratedFDerivWithin_zero_fun]

theorem contDiff_zero_fun : ContDiff 𝕜 n fun _ : E => (0 : F) :=
  analyticOnNhd_const.contDiff

/-- Constants are `C^∞`. -/
@[fun_prop]
theorem contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c :=
  analyticOnNhd_const.contDiff

@[fun_prop]
theorem contDiffOn_const {c : F} {s : Set E} : ContDiffOn 𝕜 n (fun _ : E => c) s :=
  contDiff_const.contDiffOn

@[fun_prop]
theorem contDiffAt_const {c : F} : ContDiffAt 𝕜 n (fun _ : E => c) x :=
  contDiff_const.contDiffAt

@[fun_prop]
theorem contDiffWithinAt_const {c : F} : ContDiffWithinAt 𝕜 n (fun _ : E => c) s x :=
  contDiffAt_const.contDiffWithinAt

@[nontriviality]
theorem contDiff_of_subsingleton [Subsingleton F] : ContDiff 𝕜 n f := by
  rw [Subsingleton.elim f fun _ => 0]; exact contDiff_const

@[nontriviality]
theorem contDiffAt_of_subsingleton [Subsingleton F] : ContDiffAt 𝕜 n f x := by
  rw [Subsingleton.elim f fun _ => 0]; exact contDiffAt_const

@[nontriviality]
theorem contDiffWithinAt_of_subsingleton [Subsingleton F] : ContDiffWithinAt 𝕜 n f s x := by
  rw [Subsingleton.elim f fun _ => 0]; exact contDiffWithinAt_const

@[nontriviality]
theorem contDiffOn_of_subsingleton [Subsingleton F] : ContDiffOn 𝕜 n f s := by
  rw [Subsingleton.elim f fun _ => 0]; exact contDiffOn_const

theorem iteratedFDerivWithin_const_of_ne {n : ℕ} (hn : n ≠ 0) (c : F) (s : Set E) :
    iteratedFDerivWithin 𝕜 n (fun _ : E ↦ c) s = 0 := by
  cases n with
  | zero => contradiction
  | succ n => exact iteratedFDerivWithin_succ_const n c

theorem iteratedFDeriv_const_of_ne {n : ℕ} (hn : n ≠ 0) (c : F) :
    (iteratedFDeriv 𝕜 n fun _ : E ↦ c) = 0 := by
  simp only [← iteratedFDerivWithin_univ, iteratedFDerivWithin_const_of_ne hn]

theorem iteratedFDeriv_succ_const (n : ℕ) (c : F) :
    (iteratedFDeriv 𝕜 (n + 1) fun _ : E ↦ c) = 0 :=
  iteratedFDeriv_const_of_ne (by simp) _

theorem contDiffWithinAt_singleton : ContDiffWithinAt 𝕜 n f {x} x :=
  (contDiffWithinAt_const (c := f x)).congr (by simp) rfl

end constants

/-! ### Smoothness of linear functions -/
section linear

/-- Unbundled bounded linear functions are `C^n`. -/
theorem IsBoundedLinearMap.contDiff (hf : IsBoundedLinearMap 𝕜 f) : ContDiff 𝕜 n f :=
  (ContinuousLinearMap.analyticOnNhd hf.toContinuousLinearMap univ).contDiff

@[fun_prop]
theorem ContinuousLinearMap.contDiff (f : E →L[𝕜] F) : ContDiff 𝕜 n f :=
  f.isBoundedLinearMap.contDiff

@[fun_prop]
theorem ContinuousLinearEquiv.contDiff (f : E ≃L[𝕜] F) : ContDiff 𝕜 n f :=
  (f : E →L[𝕜] F).contDiff

@[fun_prop]
theorem LinearIsometry.contDiff (f : E →ₗᵢ[𝕜] F) : ContDiff 𝕜 n f :=
  f.toContinuousLinearMap.contDiff

@[fun_prop]
theorem LinearIsometryEquiv.contDiff (f : E ≃ₗᵢ[𝕜] F) : ContDiff 𝕜 n f :=
  (f : E →L[𝕜] F).contDiff

/-- The identity is `C^n`. -/
theorem contDiff_id : ContDiff 𝕜 n (id : E → E) :=
  IsBoundedLinearMap.id.contDiff

@[fun_prop]
theorem contDiff_fun_id : ContDiff 𝕜 n (fun x : E => x) :=
  IsBoundedLinearMap.id.contDiff

theorem contDiffWithinAt_id {s x} : ContDiffWithinAt 𝕜 n (id : E → E) s x :=
  contDiff_id.contDiffWithinAt

@[fun_prop]
theorem contDiffWithinAt_fun_id {s x} : ContDiffWithinAt 𝕜 n (fun x : E => x) s x :=
  contDiff_id.contDiffWithinAt

theorem contDiffAt_id {x} : ContDiffAt 𝕜 n (id : E → E) x :=
  contDiff_id.contDiffAt

@[fun_prop]
theorem contDiffAt_fun_id {x} : ContDiffAt 𝕜 n (fun x : E => x) x :=
  contDiff_id.contDiffAt

theorem contDiffOn_id {s} : ContDiffOn 𝕜 n (id : E → E) s :=
  contDiff_id.contDiffOn

@[fun_prop]
theorem contDiffOn_fun_id {s} : ContDiffOn 𝕜 n (fun x : E => x) s :=
  contDiff_id.contDiffOn

/-- Bilinear functions are `C^n`. -/
theorem IsBoundedBilinearMap.contDiff (hb : IsBoundedBilinearMap 𝕜 b) : ContDiff 𝕜 n b :=
  (hb.toContinuousLinearMap.analyticOnNhd_bilinear _).contDiff

/-- If `f` admits a Taylor series `p` in a set `s`, and `g` is linear, then `g ∘ f` admits a Taylor
series whose `k`-th term is given by `g ∘ (p k)`. -/
theorem HasFTaylorSeriesUpToOn.continuousLinearMap_comp {n : WithTop ℕ∞} (g : F →L[𝕜] G)
    (hf : HasFTaylorSeriesUpToOn n f p s) :
    HasFTaylorSeriesUpToOn n (g ∘ f) (fun x k => g.compContinuousMultilinearMap (p x k)) s where
  zero_eq x hx := congr_arg g (hf.zero_eq x hx)
  fderivWithin m hm x hx := (ContinuousLinearMap.compContinuousMultilinearMapL 𝕜
    (fun _ : Fin m => E) F G g).hasFDerivAt.comp_hasFDerivWithinAt x (hf.fderivWithin m hm x hx)
  cont m hm := (ContinuousLinearMap.compContinuousMultilinearMapL 𝕜
    (fun _ : Fin m => E) F G g).continuous.comp_continuousOn (hf.cont m hm)

/-- Composition by continuous linear maps on the left preserves `C^n` functions in a domain
at a point. -/
theorem ContDiffWithinAt.continuousLinearMap_comp (g : F →L[𝕜] G)
    (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWithinAt 𝕜 n (g ∘ f) s x := by
  match n with
  | ω =>
    obtain ⟨u, hu, p, hp, h'p⟩ := hf
    refine ⟨u, hu, _, hp.continuousLinearMap_comp g, fun i ↦ ?_⟩
    change AnalyticOn 𝕜
      (fun x ↦ (ContinuousLinearMap.compContinuousMultilinearMapL 𝕜
      (fun _ : Fin i ↦ E) F G g) (p x i)) u
    apply AnalyticOnNhd.comp_analyticOn _ (h'p i) (Set.mapsTo_univ _ _)
    exact ContinuousLinearMap.analyticOnNhd _ _
  | (n : ℕ∞) =>
    intro m hm
    rcases hf m hm with ⟨u, hu, p, hp⟩
    exact ⟨u, hu, _, hp.continuousLinearMap_comp g⟩

/-- Composition by continuous linear maps on the left preserves `C^n` functions in a domain
at a point. -/
theorem ContDiffAt.continuousLinearMap_comp (g : F →L[𝕜] G) (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (g ∘ f) x :=
  ContDiffWithinAt.continuousLinearMap_comp g hf

/-- Composition by continuous linear maps on the left preserves `C^n` functions on domains. -/
theorem ContDiffOn.continuousLinearMap_comp (g : F →L[𝕜] G) (hf : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (g ∘ f) s := fun x hx => (hf x hx).continuousLinearMap_comp g

/-- Composition by continuous linear maps on the left preserves `C^n` functions. -/
theorem ContDiff.continuousLinearMap_comp {f : E → F} (g : F →L[𝕜] G) (hf : ContDiff 𝕜 n f) :
    ContDiff 𝕜 n fun x => g (f x) :=
  contDiffOn_univ.1 <| ContDiffOn.continuousLinearMap_comp _ (contDiffOn_univ.2 hf)

/-- The iterated derivative within a set of the composition with a linear map on the left is
obtained by applying the linear map to the iterated derivative. -/
theorem ContinuousLinearMap.iteratedFDerivWithin_comp_left {f : E → F} (g : F →L[𝕜] G)
    (hf : ContDiffWithinAt 𝕜 n f s x) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) {i : ℕ} (hi : i ≤ n) :
    iteratedFDerivWithin 𝕜 i (g ∘ f) s x =
      g.compContinuousMultilinearMap (iteratedFDerivWithin 𝕜 i f s x) := by
  rcases hf.contDiffOn' hi (by simp) with ⟨U, hU, hxU, hfU⟩
  rw [← iteratedFDerivWithin_inter_open hU hxU, ← iteratedFDerivWithin_inter_open (f := f) hU hxU]
  rw [insert_eq_of_mem hx] at hfU
  exact .symm <| (hfU.ftaylorSeriesWithin (hs.inter hU)).continuousLinearMap_comp g
    |>.eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl (hs.inter hU) ⟨hx, hxU⟩

/-- The iterated derivative of the composition with a linear map on the left is
obtained by applying the linear map to the iterated derivative. -/
theorem ContinuousLinearMap.iteratedFDeriv_comp_left {f : E → F} (g : F →L[𝕜] G)
    (hf : ContDiffAt 𝕜 n f x) {i : ℕ} (hi : i ≤ n) :
    iteratedFDeriv 𝕜 i (g ∘ f) x = g.compContinuousMultilinearMap (iteratedFDeriv 𝕜 i f x) := by
  simp only [← iteratedFDerivWithin_univ]
  exact g.iteratedFDerivWithin_comp_left hf.contDiffWithinAt uniqueDiffOn_univ (mem_univ x) hi

/-- The iterated derivative within a set of the composition with a linear equiv on the left is
obtained by applying the linear equiv to the iterated derivative. This is true without
differentiability assumptions. -/
theorem ContinuousLinearEquiv.iteratedFDerivWithin_comp_left (g : F ≃L[𝕜] G) (f : E → F)
    (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (i : ℕ) :
    iteratedFDerivWithin 𝕜 i (g ∘ f) s x =
      (g : F →L[𝕜] G).compContinuousMultilinearMap (iteratedFDerivWithin 𝕜 i f s x) := by
  induction i generalizing x with ext1 m
  | zero =>
    simp only [iteratedFDerivWithin_zero_apply, comp_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, coe_coe]
  | succ i IH =>
    rw [iteratedFDerivWithin_succ_apply_left]
    have Z : fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 i (g ∘ f) s) s x =
        fderivWithin 𝕜 (g.continuousMultilinearMapCongrRight (fun _ : Fin i => E) ∘
          iteratedFDerivWithin 𝕜 i f s) s x :=
      fderivWithin_congr' (@IH) hx
    simp_rw [Z]
    rw [(g.continuousMultilinearMapCongrRight fun _ : Fin i => E).comp_fderivWithin (hs x hx)]
    simp only [ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe, comp_apply,
      ContinuousLinearEquiv.continuousMultilinearMapCongrRight_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, EmbeddingLike.apply_eq_iff_eq]
    rw [iteratedFDerivWithin_succ_apply_left]

/-- Iterated derivatives commute with left composition by continuous linear equivalences. -/
theorem ContinuousLinearEquiv.iteratedFDeriv_comp_left {f : E → F} {x : E} (g : F ≃L[𝕜] G) {i : ℕ} :
    iteratedFDeriv 𝕜 i (g ∘ f) x =
      g.toContinuousLinearMap.compContinuousMultilinearMap (iteratedFDeriv 𝕜 i f x) := by
  simp only [← iteratedFDerivWithin_univ]
  apply g.iteratedFDerivWithin_comp_left f uniqueDiffOn_univ trivial

/-- Composition with a linear isometry on the left preserves the norm of the iterated
derivative within a set. -/
theorem LinearIsometry.norm_iteratedFDerivWithin_comp_left {f : E → F} (g : F →ₗᵢ[𝕜] G)
    (hf : ContDiffWithinAt 𝕜 n f s x) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) {i : ℕ} (hi : i ≤ n) :
    ‖iteratedFDerivWithin 𝕜 i (g ∘ f) s x‖ = ‖iteratedFDerivWithin 𝕜 i f s x‖ := by
  have :
    iteratedFDerivWithin 𝕜 i (g ∘ f) s x =
      g.toContinuousLinearMap.compContinuousMultilinearMap (iteratedFDerivWithin 𝕜 i f s x) :=
    g.toContinuousLinearMap.iteratedFDerivWithin_comp_left hf hs hx hi
  rw [this]
  apply LinearIsometry.norm_compContinuousMultilinearMap

/-- Composition with a linear isometry on the left preserves the norm of the iterated
derivative. -/
theorem LinearIsometry.norm_iteratedFDeriv_comp_left {f : E → F} (g : F →ₗᵢ[𝕜] G)
    (hf : ContDiffAt 𝕜 n f x) {i : ℕ} (hi : i ≤ n) :
    ‖iteratedFDeriv 𝕜 i (g ∘ f) x‖ = ‖iteratedFDeriv 𝕜 i f x‖ := by
  simp only [← iteratedFDerivWithin_univ]
  exact g.norm_iteratedFDerivWithin_comp_left hf.contDiffWithinAt uniqueDiffOn_univ (mem_univ x) hi

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

/-- Composition with a linear isometry equiv on the left preserves the norm of the iterated
derivative. -/
theorem LinearIsometryEquiv.norm_iteratedFDeriv_comp_left (g : F ≃ₗᵢ[𝕜] G) (f : E → F) (x : E)
    (i : ℕ) : ‖iteratedFDeriv 𝕜 i (g ∘ f) x‖ = ‖iteratedFDeriv 𝕜 i f x‖ := by
  rw [← iteratedFDerivWithin_univ, ← iteratedFDerivWithin_univ]
  apply g.norm_iteratedFDerivWithin_comp_left f uniqueDiffOn_univ (mem_univ x) i

/-- Composition by continuous linear equivs on the left respects higher differentiability at a
point in a domain. -/
theorem ContinuousLinearEquiv.comp_contDiffWithinAt_iff (e : F ≃L[𝕜] G) :
    ContDiffWithinAt 𝕜 n (e ∘ f) s x ↔ ContDiffWithinAt 𝕜 n f s x :=
  ⟨fun H => by
    simpa only [Function.comp_def, e.symm.coe_coe, e.symm_apply_apply] using
      H.continuousLinearMap_comp (e.symm : G →L[𝕜] F),
    fun H => H.continuousLinearMap_comp (e : F →L[𝕜] G)⟩

/-- Composition by continuous linear equivs on the left respects higher differentiability at a
point. -/
theorem ContinuousLinearEquiv.comp_contDiffAt_iff (e : F ≃L[𝕜] G) :
    ContDiffAt 𝕜 n (e ∘ f) x ↔ ContDiffAt 𝕜 n f x := by
  simp only [← contDiffWithinAt_univ, e.comp_contDiffWithinAt_iff]

/-- Composition by continuous linear equivs on the left respects higher differentiability on
domains. -/
theorem ContinuousLinearEquiv.comp_contDiffOn_iff (e : F ≃L[𝕜] G) :
    ContDiffOn 𝕜 n (e ∘ f) s ↔ ContDiffOn 𝕜 n f s := by
  simp [ContDiffOn, e.comp_contDiffWithinAt_iff]

/-- Composition by continuous linear equivs on the left respects higher differentiability. -/
theorem ContinuousLinearEquiv.comp_contDiff_iff (e : F ≃L[𝕜] G) :
    ContDiff 𝕜 n (e ∘ f) ↔ ContDiff 𝕜 n f := by
  simp only [← contDiffOn_univ, e.comp_contDiffOn_iff]

/-- If `f` admits a Taylor series `p` in a set `s`, and `g` is affine, then `f ∘ g` admits a Taylor
series in `g ⁻¹' s`, whose `k`-th term at `x` is given
by `p (g x) k (g.contLinear v₁, ..., g.contLinear vₖ)` . -/
theorem HasFTaylorSeriesUpToOn.comp_continuousAffineMap
    (hf : HasFTaylorSeriesUpToOn n f p s) (g : G →ᴬ[𝕜] E) :
    HasFTaylorSeriesUpToOn n (f ∘ g)
      (fun x k => (p (g x) k).compContinuousLinearMap fun _ => g.contLinear) (g ⁻¹' s) := by
  let A : ∀ m : ℕ, (E [×m]→L[𝕜] F) → G [×m]→L[𝕜] F :=
    fun m h ↦ h.compContinuousLinearMap fun _ ↦ g.contLinear
  have hA : ∀ m, IsBoundedLinearMap 𝕜 (A m) := fun m =>
    isBoundedLinearMap_continuousMultilinearMap_comp_linear g.contLinear
  constructor
  · intro x hx
    simp only [(hf.zero_eq (g x) hx).symm, Function.comp_apply]
    change (p (g x) 0 fun _ : Fin 0 => g.contLinear 0) = p (g x) 0 0
    rw [map_zero]
    rfl
  · intro m hm x hx
    convert (hA m).hasFDerivAt.comp_hasFDerivWithinAt x
        ((hf.fderivWithin m hm (g x) hx).comp x g.hasFDerivWithinAt (Subset.refl _))
    ext y v
    change p (g x) (Nat.succ m) (g.contLinear ∘ cons y v)
      = p (g x) m.succ (cons (g.contLinear y) (g.contLinear ∘ v))
    rw [comp_cons]
  · intro m hm
    exact (hA m).continuous.comp_continuousOn <| (hf.cont m hm).comp g.continuous.continuousOn <|
      Subset.refl _

/-- If `f` admits a Taylor series `p` in a set `s`, and `g` is linear, then `f ∘ g` admits a Taylor
series in `g ⁻¹' s`, whose `k`-th term at `x` is given by `p (g x) k (g v₁, ..., g vₖ)` . -/
theorem HasFTaylorSeriesUpToOn.compContinuousLinearMap
    (hf : HasFTaylorSeriesUpToOn n f p s) (g : G →L[𝕜] E) :
    HasFTaylorSeriesUpToOn n (f ∘ g)
      (fun x k => (p (g x) k).compContinuousLinearMap fun _ => g) (g ⁻¹' s) :=
  hf.comp_continuousAffineMap g.toContinuousAffineMap

/-- Composition by continuous linear maps on the right preserves `C^n` functions at a point on
a domain. -/
theorem ContDiffWithinAt.comp_continuousLinearMap {x : G} (g : G →L[𝕜] E)
    (hf : ContDiffWithinAt 𝕜 n f s (g x)) : ContDiffWithinAt 𝕜 n (f ∘ g) (g ⁻¹' s) x := by
  match n with
  | ω =>
    obtain ⟨u, hu, p, hp, h'p⟩ := hf
    refine ⟨g ⁻¹' u, ?_, _, hp.compContinuousLinearMap g, ?_⟩
    · refine g.continuous.continuousWithinAt.tendsto_nhdsWithin ?_ hu
      exact (mapsTo_singleton.2 <| mem_singleton _).union_union (mapsTo_preimage _ _)
    · intro i
      change AnalyticOn 𝕜 (fun x ↦
        ContinuousMultilinearMap.compContinuousLinearMapL (fun _ ↦ g) (p (g x) i)) (⇑g ⁻¹' u)
      apply AnalyticOn.comp _ _ (Set.mapsTo_univ _ _)
      · exact ContinuousLinearMap.analyticOn _ _
      · exact (h'p i).comp (g.analyticOn _) (mapsTo_preimage _ _)
  | (n : ℕ∞) =>
    intro m hm
    rcases hf m hm with ⟨u, hu, p, hp⟩
    refine ⟨g ⁻¹' u, ?_, _, hp.compContinuousLinearMap g⟩
    refine g.continuous.continuousWithinAt.tendsto_nhdsWithin ?_ hu
    exact (mapsTo_singleton.2 <| mem_singleton _).union_union (mapsTo_preimage _ _)

/-- Composition by continuous linear maps on the right preserves `C^n` functions on domains. -/
theorem ContDiffOn.comp_continuousLinearMap (hf : ContDiffOn 𝕜 n f s) (g : G →L[𝕜] E) :
    ContDiffOn 𝕜 n (f ∘ g) (g ⁻¹' s) := fun x hx => (hf (g x) hx).comp_continuousLinearMap g

/-- Composition by continuous linear maps on the right preserves `C^n` functions. -/
theorem ContDiff.comp_continuousLinearMap {f : E → F} {g : G →L[𝕜] E} (hf : ContDiff 𝕜 n f) :
    ContDiff 𝕜 n (f ∘ g) :=
  contDiffOn_univ.1 <| ContDiffOn.comp_continuousLinearMap (contDiffOn_univ.2 hf) _

/-- The iterated derivative within a set of the composition with a linear map on the right is
obtained by composing the iterated derivative with the linear map. -/
theorem ContinuousLinearMap.iteratedFDerivWithin_comp_right {f : E → F} (g : G →L[𝕜] E)
    (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s) (h's : UniqueDiffOn 𝕜 (g ⁻¹' s)) {x : G}
    (hx : g x ∈ s) {i : ℕ} (hi : i ≤ n) :
    iteratedFDerivWithin 𝕜 i (f ∘ g) (g ⁻¹' s) x =
      (iteratedFDerivWithin 𝕜 i f s (g x)).compContinuousLinearMap fun _ => g :=
  ((((hf.of_le hi).ftaylorSeriesWithin hs).compContinuousLinearMap
    g).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl h's hx).symm

/-- The iterated derivative within a set of the composition with a linear equiv on the right is
obtained by composing the iterated derivative with the linear equiv. -/
theorem ContinuousLinearEquiv.iteratedFDerivWithin_comp_right (g : G ≃L[𝕜] E) (f : E → F)
    (hs : UniqueDiffOn 𝕜 s) {x : G} (hx : g x ∈ s) (i : ℕ) :
    iteratedFDerivWithin 𝕜 i (f ∘ g) (g ⁻¹' s) x =
      (iteratedFDerivWithin 𝕜 i f s (g x)).compContinuousLinearMap fun _ => g := by
  induction i generalizing x with ext1 m
  | zero =>
    simp only [iteratedFDerivWithin_zero_apply, comp_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
  | succ i IH =>
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousLinearEquiv.coe_coe, iteratedFDerivWithin_succ_apply_left]
    have : fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 i (f ∘ g) (g ⁻¹' s)) (g ⁻¹' s) x =
        fderivWithin 𝕜
          (ContinuousLinearEquiv.continuousMultilinearMapCongrLeft _ (fun _x : Fin i => g) ∘
            (iteratedFDerivWithin 𝕜 i f s ∘ g)) (g ⁻¹' s) x :=
      fderivWithin_congr' (@IH) hx
    rw [this, ContinuousLinearEquiv.comp_fderivWithin _ (g.uniqueDiffOn_preimage_iff.2 hs x hx)]
    simp only [ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe, comp_apply,
      ContinuousLinearEquiv.continuousMultilinearMapCongrLeft_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
    rw [ContinuousLinearEquiv.comp_right_fderivWithin _ (g.uniqueDiffOn_preimage_iff.2 hs x hx),
      ContinuousLinearMap.coe_comp', coe_coe, comp_apply, tail_def, tail_def]

/-- The iterated derivative of the composition with a linear map on the right is
obtained by composing the iterated derivative with the linear map. -/
theorem ContinuousLinearMap.iteratedFDeriv_comp_right (g : G →L[𝕜] E) {f : E → F}
    (hf : ContDiff 𝕜 n f) (x : G) {i : ℕ} (hi : i ≤ n) :
    iteratedFDeriv 𝕜 i (f ∘ g) x =
      (iteratedFDeriv 𝕜 i f (g x)).compContinuousLinearMap fun _ => g := by
  simp only [← iteratedFDerivWithin_univ]
  exact g.iteratedFDerivWithin_comp_right hf.contDiffOn uniqueDiffOn_univ uniqueDiffOn_univ
      (mem_univ _) hi

/-- Composition with a linear isometry on the right preserves the norm of the iterated derivative
within a set. -/
theorem LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_right (g : G ≃ₗᵢ[𝕜] E) (f : E → F)
    (hs : UniqueDiffOn 𝕜 s) {x : G} (hx : g x ∈ s) (i : ℕ) :
    ‖iteratedFDerivWithin 𝕜 i (f ∘ g) (g ⁻¹' s) x‖ = ‖iteratedFDerivWithin 𝕜 i f s (g x)‖ := by
  have : iteratedFDerivWithin 𝕜 i (f ∘ g) (g ⁻¹' s) x =
      (iteratedFDerivWithin 𝕜 i f s (g x)).compContinuousLinearMap fun _ => g :=
    g.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right f hs hx i
  rw [this, ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv]

/-- Composition with a linear isometry on the right preserves the norm of the iterated derivative
within a set. -/
theorem LinearIsometryEquiv.norm_iteratedFDeriv_comp_right (g : G ≃ₗᵢ[𝕜] E) (f : E → F) (x : G)
    (i : ℕ) : ‖iteratedFDeriv 𝕜 i (f ∘ g) x‖ = ‖iteratedFDeriv 𝕜 i f (g x)‖ := by
  simp only [← iteratedFDerivWithin_univ]
  apply g.norm_iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (mem_univ (g x)) i

/-- Composition by continuous linear equivs on the right respects higher differentiability at a
point in a domain. -/
theorem ContinuousLinearEquiv.contDiffWithinAt_comp_iff (e : G ≃L[𝕜] E) :
    ContDiffWithinAt 𝕜 n (f ∘ e) (e ⁻¹' s) (e.symm x) ↔ ContDiffWithinAt 𝕜 n f s x := by
  constructor
  · intro H
    simpa [← preimage_comp, Function.comp_def] using H.comp_continuousLinearMap (e.symm : E →L[𝕜] G)
  · intro H
    rw [← e.apply_symm_apply x, ← e.coe_coe] at H
    exact H.comp_continuousLinearMap _

/-- Composition by continuous linear equivs on the right respects higher differentiability at a
point. -/
theorem ContinuousLinearEquiv.contDiffAt_comp_iff (e : G ≃L[𝕜] E) :
    ContDiffAt 𝕜 n (f ∘ e) (e.symm x) ↔ ContDiffAt 𝕜 n f x := by
  rw [← contDiffWithinAt_univ, ← contDiffWithinAt_univ, ← preimage_univ]
  exact e.contDiffWithinAt_comp_iff

/-- Composition by continuous linear equivs on the right respects higher differentiability on
domains. -/
theorem ContinuousLinearEquiv.contDiffOn_comp_iff (e : G ≃L[𝕜] E) :
    ContDiffOn 𝕜 n (f ∘ e) (e ⁻¹' s) ↔ ContDiffOn 𝕜 n f s :=
  ⟨fun H => by simpa [Function.comp_def] using H.comp_continuousLinearMap (e.symm : E →L[𝕜] G),
    fun H => H.comp_continuousLinearMap (e : G →L[𝕜] E)⟩

/-- Composition by continuous linear equivs on the right respects higher differentiability. -/
theorem ContinuousLinearEquiv.contDiff_comp_iff (e : G ≃L[𝕜] E) :
    ContDiff 𝕜 n (f ∘ e) ↔ ContDiff 𝕜 n f := by
  rw [← contDiffOn_univ, ← contDiffOn_univ, ← preimage_univ]
  exact e.contDiffOn_comp_iff

end linear

/-! ### The Cartesian product of two C^n functions is C^n. -/
section prod

/-- If two functions `f` and `g` admit Taylor series `p` and `q` in a set `s`, then the Cartesian
product of `f` and `g` admits the Cartesian product of `p` and `q` as a Taylor series. -/
theorem HasFTaylorSeriesUpToOn.prodMk {n : WithTop ℕ∞}
    (hf : HasFTaylorSeriesUpToOn n f p s) {g : E → G}
    {q : E → FormalMultilinearSeries 𝕜 E G} (hg : HasFTaylorSeriesUpToOn n g q s) :
    HasFTaylorSeriesUpToOn n (fun y => (f y, g y)) (fun y k => (p y k).prod (q y k)) s := by
  set L := fun m => ContinuousMultilinearMap.prodL 𝕜 (fun _ : Fin m => E) F G
  constructor
  · intro x hx; rw [← hf.zero_eq x hx, ← hg.zero_eq x hx]; rfl
  · intro m hm x hx
    convert (L m).hasFDerivAt.comp_hasFDerivWithinAt x
        ((hf.fderivWithin m hm x hx).prodMk (hg.fderivWithin m hm x hx))
  · intro m hm
    exact (L m).continuous.comp_continuousOn ((hf.cont m hm).prodMk (hg.cont m hm))

/-- The Cartesian product of `C^n` functions at a point in a domain is `C^n`. -/
@[fun_prop]
theorem ContDiffWithinAt.prodMk {s : Set E} {f : E → F} {g : E → G}
    (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) :
    ContDiffWithinAt 𝕜 n (fun x : E => (f x, g x)) s x := by
  match n with
  | ω =>
    obtain ⟨u, hu, p, hp, h'p⟩ := hf
    obtain ⟨v, hv, q, hq, h'q⟩ := hg
    refine ⟨u ∩ v, Filter.inter_mem hu hv, _,
      (hp.mono inter_subset_left).prodMk (hq.mono inter_subset_right), fun i ↦ ?_⟩
    change AnalyticOn 𝕜 (fun x ↦ ContinuousMultilinearMap.prodL _ _ _ _ (p x i, q x i)) (u ∩ v)
    apply (LinearIsometryEquiv.analyticOnNhd _ _).comp_analyticOn _ (Set.mapsTo_univ _ _)
    exact ((h'p i).mono inter_subset_left).prod ((h'q i).mono inter_subset_right)
  | (n : ℕ∞) =>
    intro m hm
    rcases hf m hm with ⟨u, hu, p, hp⟩
    rcases hg m hm with ⟨v, hv, q, hq⟩
    exact ⟨u ∩ v, Filter.inter_mem hu hv, _,
      (hp.mono inter_subset_left).prodMk (hq.mono inter_subset_right)⟩

/-- The Cartesian product of `C^n` functions on domains is `C^n`. -/
@[fun_prop]
theorem ContDiffOn.prodMk {s : Set E} {f : E → F} {g : E → G} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x : E => (f x, g x)) s := fun x hx =>
  (hf x hx).prodMk (hg x hx)

/-- The Cartesian product of `C^n` functions at a point is `C^n`. -/
@[fun_prop]
theorem ContDiffAt.prodMk {f : E → F} {g : E → G} (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun x : E => (f x, g x)) x :=
  contDiffWithinAt_univ.1 <| hf.contDiffWithinAt.prodMk hg.contDiffWithinAt

/-- The Cartesian product of `C^n` functions is `C^n`. -/
@[fun_prop]
theorem ContDiff.prodMk {f : E → F} {g : E → G} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n fun x : E => (f x, g x) :=
  contDiffOn_univ.1 <| hf.contDiffOn.prodMk hg.contDiffOn

theorem iteratedFDerivWithin_prodMk {f : E → F} {g : E → G} (hf : ContDiffWithinAt 𝕜 n f s x)
    (hg : ContDiffWithinAt 𝕜 n g s x) (hs : UniqueDiffOn 𝕜 s) (ha : x ∈ s) {i : ℕ} (hi : i ≤ n) :
    iteratedFDerivWithin 𝕜 i (fun x ↦ (f x, g x)) s x =
      (iteratedFDerivWithin 𝕜 i f s x).prod (iteratedFDerivWithin 𝕜 i g s x) := by
  ext <;>
  · rw [← ContinuousLinearMap.iteratedFDerivWithin_comp_left _ (hf.prodMk hg) hs ha hi]
    simp [Function.comp_def]

theorem iteratedFDeriv_prodMk {f : E → F} {g : E → G} (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g x) {i : ℕ} (hi : i ≤ n) :
    iteratedFDeriv 𝕜 i (fun x ↦ (f x, g x)) x =
      (iteratedFDeriv 𝕜 i f x).prod (iteratedFDeriv 𝕜 i g x) := by
  simp only [← iteratedFDerivWithin_univ]
  exact iteratedFDerivWithin_prodMk hf.contDiffWithinAt hg.contDiffWithinAt uniqueDiffOn_univ
    (Set.mem_univ _) hi

end prod

/-! ### Being `C^k` on a union of open sets can be tested on each set -/
section contDiffOn_union

/-- If a function is `C^k` on two open sets, it is also `C^n` on their union. -/
lemma ContDiffOn.union_of_isOpen (hf : ContDiffOn 𝕜 n f s) (hf' : ContDiffOn 𝕜 n f t)
    (hs : IsOpen s) (ht : IsOpen t) :
    ContDiffOn 𝕜 n f (s ∪ t) := by
  rintro x (hx | hx)
  · exact (hf x hx).contDiffAt (hs.mem_nhds hx) |>.contDiffWithinAt
  · exact (hf' x hx).contDiffAt (ht.mem_nhds hx) |>.contDiffWithinAt

/-- A function is `C^k` on two open sets iff it is `C^k` on their union. -/
lemma contDiffOn_union_iff_of_isOpen (hs : IsOpen s) (ht : IsOpen t) :
    ContDiffOn 𝕜 n f (s ∪ t) ↔ ContDiffOn 𝕜 n f s ∧ ContDiffOn 𝕜 n f t :=
  ⟨fun h ↦ ⟨h.mono subset_union_left, h.mono subset_union_right⟩,
   fun ⟨hfs, hft⟩ ↦ ContDiffOn.union_of_isOpen hfs hft hs ht⟩

lemma contDiff_of_contDiffOn_union_of_isOpen (hf : ContDiffOn 𝕜 n f s)
    (hf' : ContDiffOn 𝕜 n f t) (hst : s ∪ t = univ) (hs : IsOpen s) (ht : IsOpen t) :
    ContDiff 𝕜 n f := by
  rw [← contDiffOn_univ, ← hst]
  exact hf.union_of_isOpen hf' hs ht

/-- If a function is `C^k` on open sets `s i`, it is `C^k` on their union -/
lemma ContDiffOn.iUnion_of_isOpen {ι : Type*} {s : ι → Set E}
    (hf : ∀ i : ι, ContDiffOn 𝕜 n f (s i)) (hs : ∀ i, IsOpen (s i)) :
    ContDiffOn 𝕜 n f (⋃ i, s i) := by
  rintro x ⟨si, ⟨i, rfl⟩, hxsi⟩
  exact (hf i).contDiffAt ((hs i).mem_nhds hxsi) |>.contDiffWithinAt

/-- A function is `C^k` on a union of open sets `s i` iff it is `C^k` on each `s i`. -/
lemma contDiffOn_iUnion_iff_of_isOpen {ι : Type*} {s : ι → Set E}
    (hs : ∀ i, IsOpen (s i)) :
    ContDiffOn 𝕜 n f (⋃ i, s i) ↔ ∀ i : ι, ContDiffOn 𝕜 n f (s i) :=
  ⟨fun h i ↦ h.mono <| subset_iUnion_of_subset i fun _ a ↦ a,
   fun h ↦ ContDiffOn.iUnion_of_isOpen h hs⟩

lemma contDiff_of_contDiffOn_iUnion_of_isOpen {ι : Type*} {s : ι → Set E}
    (hf : ∀ i : ι, ContDiffOn 𝕜 n f (s i)) (hs : ∀ i, IsOpen (s i)) (hs' : ⋃ i, s i = univ) :
    ContDiff 𝕜 n f := by
  rw [← contDiffOn_univ, ← hs']
  exact ContDiffOn.iUnion_of_isOpen hf hs

end contDiffOn_union

/-- The natural equivalence `(E × F) × G ≃ E × (F × G)` is smooth.

Warning: if you think you need this lemma, it is likely that you can simplify your proof by
reformulating the lemma that you're applying next using the tips in
Note [continuity lemma statement]
-/
theorem contDiff_prodAssoc {n : WithTop ℕ∞} : ContDiff 𝕜 n <| Equiv.prodAssoc E F G :=
  (LinearIsometryEquiv.prodAssoc 𝕜 E F G).contDiff

/-- The natural equivalence `E × (F × G) ≃ (E × F) × G` is smooth.

Warning: see remarks attached to `contDiff_prodAssoc`
-/
theorem contDiff_prodAssoc_symm {n : WithTop ℕ∞} : ContDiff 𝕜 n <| (Equiv.prodAssoc E F G).symm :=
  (LinearIsometryEquiv.prodAssoc 𝕜 E F G).symm.contDiff
