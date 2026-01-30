/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
public import Mathlib.Analysis.Calculus.FDeriv.Affine
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Higher differentiability of composition

We prove that the composition of `C^n` functions is `C^n`.
We also expand the API around `C^n` functions.

## Main results

* `ContDiff.comp` states that the composition of two `C^n` functions is `C^n`.

Similar results are given for `C^n` functions on domains.

## Notation

We use the notation `E [×n]→L[𝕜] F` for the space of continuous multilinear maps on `E^n` with
values in `F`. This is the space in which the `n`-th derivative of a function from `E` to `F` lives.

In this file, we denote `WithTop ℕ∞` with `ℕ∞ω`, `(⊤ : ℕ∞) : ℕ∞ω` with `∞` and `⊤ : ℕ∞ω` with `ω`.

## Tags

derivative, differentiability, higher derivative, `C^n`, multilinear, Taylor series, formal series
-/

public section

noncomputable section

open scoped NNReal Nat ContDiff

universe u uE uF uG

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

open Set Fin Filter Function

open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type uF}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type uG} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] {s t : Set E} {f : E → F}
  {g : F → G} {x x₀ : E} {b : E × F → G} {m n : ℕ∞ω} {p : E → FormalMultilinearSeries 𝕜 E F}

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
theorem HasFTaylorSeriesUpToOn.continuousLinearMap_comp {n : ℕ∞ω} (g : F →L[𝕜] G)
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
theorem HasFTaylorSeriesUpToOn.prodMk {n : ℕ∞ω}
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

section comp

/-!
### Composition of `C^n` functions

We show that the composition of `C^n` functions is `C^n`. One way to do this would be to
use the following simple inductive proof. Assume it is done for `n`.
Then, to check it for `n+1`, one needs to check that the derivative of `g ∘ f` is `C^n`, i.e.,
that `Dg(f x) ⬝ Df(x)` is `C^n`. The term `Dg (f x)` is the composition of two `C^n` functions, so
it is `C^n` by the inductive assumption. The term `Df(x)` is also `C^n`. Then, the matrix
multiplication is the application of a bilinear map (which is `C^∞`, and therefore `C^n`) to
`x ↦ (Dg(f x), Df x)`. As the composition of two `C^n` maps, it is again `C^n`, and we are done.

There are two difficulties in this proof.

The first one is that it is an induction over all Banach
spaces. In Lean, this is only possible if they belong to a fixed universe. One could formalize this
by first proving the statement in this case, and then extending the result to general universes
by embedding all the spaces we consider in a common universe through `ULift`.

The second one is that it does not work cleanly for analytic maps: for this case, we need to
exhibit a whole sequence of derivatives which are all analytic, not just finitely many of them, so
an induction is never enough at a finite step.

Both these difficulties can be overcome with some cost. However, we choose a different path: we
write down an explicit formula for the `n`-th derivative of `g ∘ f` in terms of derivatives of
`g` and `f` (this is the formula of Faa-Di Bruno) and use this formula to get a suitable Taylor
expansion for `g ∘ f`. Writing down the formula of Faa-Di Bruno is not easy as the formula is quite
intricate, but it is also useful for other purposes and once available it makes the proof here
essentially trivial.
-/

/-- The composition of `C^n` functions at points in domains is `C^n`. -/
theorem ContDiffWithinAt.comp {s : Set E} {t : Set F} {g : F → G} {f : E → F} (x : E)
    (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) (st : MapsTo f s t) :
    ContDiffWithinAt 𝕜 n (g ∘ f) s x := by
  match n with
  | ω =>
    have h'f : ContDiffWithinAt 𝕜 ω f s x := hf
    obtain ⟨u, hu, p, hp, h'p⟩ := h'f
    obtain ⟨v, hv, q, hq, h'q⟩ := hg
    let w := insert x s ∩ (u ∩ f ⁻¹' v)
    have wv : w ⊆ f ⁻¹' v := fun y hy => hy.2.2
    have wu : w ⊆ u := fun y hy => hy.2.1
    refine ⟨w, ?_, fun y ↦ (q (f y)).taylorComp (p y), hq.comp (hp.mono wu) wv, ?_⟩
    · apply inter_mem self_mem_nhdsWithin (inter_mem hu ?_)
      apply (continuousWithinAt_insert_self.2 hf.continuousWithinAt).preimage_mem_nhdsWithin'
      apply nhdsWithin_mono _ _ hv
      simp only [image_insert_eq]
      apply insert_subset_insert
      exact image_subset_iff.mpr st
    · have : AnalyticOn 𝕜 f w := by
        have : AnalyticOn 𝕜 (fun y ↦ (continuousMultilinearCurryFin0 𝕜 E F).symm (f y)) w :=
          ((h'p 0).mono wu).congr fun y hy ↦ (hp.zero_eq' (wu hy)).symm
        have : AnalyticOn 𝕜 (fun y ↦ (continuousMultilinearCurryFin0 𝕜 E F)
            ((continuousMultilinearCurryFin0 𝕜 E F).symm (f y))) w :=
          AnalyticOnNhd.comp_analyticOn (LinearIsometryEquiv.analyticOnNhd _ _) this
          (mapsTo_univ _ _)
        simpa using this
      exact analyticOn_taylorComp h'q (fun n ↦ (h'p n).mono wu) this wv
  | (n : ℕ∞) =>
    intro m hm
    rcases hf m hm with ⟨u, hu, p, hp⟩
    rcases hg m hm with ⟨v, hv, q, hq⟩
    let w := insert x s ∩ (u ∩ f ⁻¹' v)
    have wv : w ⊆ f ⁻¹' v := fun y hy => hy.2.2
    have wu : w ⊆ u := fun y hy => hy.2.1
    refine ⟨w, ?_, fun y ↦ (q (f y)).taylorComp (p y), hq.comp (hp.mono wu) wv⟩
    apply inter_mem self_mem_nhdsWithin (inter_mem hu ?_)
    apply (continuousWithinAt_insert_self.2 hf.continuousWithinAt).preimage_mem_nhdsWithin'
    apply nhdsWithin_mono _ _ hv
    simp only [image_insert_eq]
    apply insert_subset_insert
    exact image_subset_iff.mpr st

/-- The composition of `C^n` functions on domains is `C^n`. -/
theorem ContDiffOn.comp {s : Set E} {t : Set F} {g : F → G} {f : E → F} (hg : ContDiffOn 𝕜 n g t)
    (hf : ContDiffOn 𝕜 n f s) (st : MapsTo f s t) : ContDiffOn 𝕜 n (g ∘ f) s :=
  fun x hx ↦ ContDiffWithinAt.comp x (hg (f x) (st hx)) (hf x hx) st

/-- The composition of `C^n` functions on domains is `C^n`. -/
theorem ContDiffOn.comp_inter
    {s : Set E} {t : Set F} {g : F → G} {f : E → F} (hg : ContDiffOn 𝕜 n g t)
    (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 n (g ∘ f) (s ∩ f ⁻¹' t) :=
  hg.comp (hf.mono inter_subset_left) inter_subset_right

/-- The composition of a `C^n` function on a domain with a `C^n` function is `C^n`. -/
theorem ContDiff.comp_contDiffOn {s : Set E} {g : F → G} {f : E → F} (hg : ContDiff 𝕜 n g)
    (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 n (g ∘ f) s :=
  (contDiffOn_univ.2 hg).comp hf (mapsTo_univ _ _)

@[fun_prop]
theorem ContDiff.fun_comp_contDiffOn {s : Set E} {g : F → G} {f : E → F} (hg : ContDiff 𝕜 n g)
    (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 n (fun x => g (f x)) s :=
  (contDiffOn_univ.2 hg).comp hf (mapsTo_univ _ _)

theorem ContDiffOn.comp_contDiff {s : Set F} {g : F → G} {f : E → F} (hg : ContDiffOn 𝕜 n g s)
    (hf : ContDiff 𝕜 n f) (hs : ∀ x, f x ∈ s) : ContDiff 𝕜 n (g ∘ f) := by
  rw [← contDiffOn_univ] at *
  exact hg.comp hf fun x _ => hs x

theorem ContDiffOn.image_comp_contDiff {s : Set E} {g : F → G} {f : E → F}
    (hg : ContDiffOn 𝕜 n g (f '' s)) (hf : ContDiff 𝕜 n f) : ContDiffOn 𝕜 n (g ∘ f) s :=
  hg.comp hf.contDiffOn (s.mapsTo_image f)

/-- The composition of `C^n` functions is `C^n`. -/
theorem ContDiff.comp {g : F → G} {f : E → F} (hg : ContDiff 𝕜 n g) (hf : ContDiff 𝕜 n f) :
    ContDiff 𝕜 n (g ∘ f) :=
  contDiffOn_univ.1 <| ContDiffOn.comp (contDiffOn_univ.2 hg) (contDiffOn_univ.2 hf) (subset_univ _)

@[fun_prop]
theorem ContDiff.fun_comp {g : F → G} {f : E → F} (hg : ContDiff 𝕜 n g) (hf : ContDiff 𝕜 n f) :
    ContDiff 𝕜 n (fun x => g (f x)) := hg.comp hf

/-- The composition of `C^n` functions at points in domains is `C^n`. -/
theorem ContDiffWithinAt.comp_of_eq {s : Set E} {t : Set F} {g : F → G} {f : E → F} {y : F} (x : E)
    (hg : ContDiffWithinAt 𝕜 n g t y) (hf : ContDiffWithinAt 𝕜 n f s x) (st : MapsTo f s t)
    (hy : f x = y) :
    ContDiffWithinAt 𝕜 n (g ∘ f) s x := by
  subst hy; exact hg.comp x hf st

/-- The composition of `C^n` functions at points in domains is `C^n`,
  with a weaker condition on `s` and `t`. -/
theorem ContDiffWithinAt.comp_of_mem_nhdsWithin_image
    {s : Set E} {t : Set F} {g : F → G} {f : E → F} (x : E)
    (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x)
    (hs : t ∈ 𝓝[f '' s] f x) : ContDiffWithinAt 𝕜 n (g ∘ f) s x :=
  (hg.mono_of_mem_nhdsWithin hs).comp x hf (subset_preimage_image f s)

/-- The composition of `C^n` functions at points in domains is `C^n`,
  with a weaker condition on `s` and `t`. -/
theorem ContDiffWithinAt.comp_of_mem_nhdsWithin_image_of_eq
    {s : Set E} {t : Set F} {g : F → G} {f : E → F} {y : F} (x : E)
    (hg : ContDiffWithinAt 𝕜 n g t y) (hf : ContDiffWithinAt 𝕜 n f s x)
    (hs : t ∈ 𝓝[f '' s] f x) (hy : f x = y) : ContDiffWithinAt 𝕜 n (g ∘ f) s x := by
  subst hy; exact hg.comp_of_mem_nhdsWithin_image x hf hs

/-- The composition of `C^n` functions at points in domains is `C^n`. -/
theorem ContDiffWithinAt.comp_inter {s : Set E} {t : Set F} {g : F → G} {f : E → F} (x : E)
    (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) :
    ContDiffWithinAt 𝕜 n (g ∘ f) (s ∩ f ⁻¹' t) x :=
  hg.comp x (hf.mono inter_subset_left) inter_subset_right

/-- The composition of `C^n` functions at points in domains is `C^n`. -/
theorem ContDiffWithinAt.comp_inter_of_eq {s : Set E} {t : Set F} {g : F → G} {f : E → F} {y : F}
    (x : E) (hg : ContDiffWithinAt 𝕜 n g t y) (hf : ContDiffWithinAt 𝕜 n f s x) (hy : f x = y) :
    ContDiffWithinAt 𝕜 n (g ∘ f) (s ∩ f ⁻¹' t) x := by
  subst hy; exact hg.comp_inter x hf

/-- The composition of `C^n` functions at points in domains is `C^n`,
  with a weaker condition on `s` and `t`. -/
theorem ContDiffWithinAt.comp_of_preimage_mem_nhdsWithin
    {s : Set E} {t : Set F} {g : F → G} {f : E → F} (x : E)
    (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x)
    (hs : f ⁻¹' t ∈ 𝓝[s] x) : ContDiffWithinAt 𝕜 n (g ∘ f) s x :=
  (hg.comp_inter x hf).mono_of_mem_nhdsWithin (inter_mem self_mem_nhdsWithin hs)

/-- The composition of `C^n` functions at points in domains is `C^n`,
  with a weaker condition on `s` and `t`. -/
theorem ContDiffWithinAt.comp_of_preimage_mem_nhdsWithin_of_eq
    {s : Set E} {t : Set F} {g : F → G} {f : E → F} {y : F} (x : E)
    (hg : ContDiffWithinAt 𝕜 n g t y) (hf : ContDiffWithinAt 𝕜 n f s x)
    (hs : f ⁻¹' t ∈ 𝓝[s] x) (hy : f x = y) : ContDiffWithinAt 𝕜 n (g ∘ f) s x := by
  subst hy; exact hg.comp_of_preimage_mem_nhdsWithin x hf hs

theorem ContDiffAt.comp_contDiffWithinAt (x : E) (hg : ContDiffAt 𝕜 n g (f x))
    (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWithinAt 𝕜 n (g ∘ f) s x :=
  hg.comp x hf (mapsTo_univ _ _)

theorem ContDiffAt.comp_contDiffWithinAt_of_eq {y : F} (x : E) (hg : ContDiffAt 𝕜 n g y)
    (hf : ContDiffWithinAt 𝕜 n f s x) (hy : f x = y) : ContDiffWithinAt 𝕜 n (g ∘ f) s x := by
  subst hy; exact hg.comp_contDiffWithinAt x hf

/-- The composition of `C^n` functions at points is `C^n`. -/
nonrec theorem ContDiffAt.comp (x : E) (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (g ∘ f) x :=
  hg.comp x hf (mapsTo_univ _ _)

@[fun_prop]
theorem ContDiffAt.fun_comp (x : E) (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun x => g (f x)) x := hg.comp x hf

theorem ContDiff.comp_contDiffWithinAt {g : F → G} {f : E → F} (h : ContDiff 𝕜 n g)
    (hf : ContDiffWithinAt 𝕜 n f t x) : ContDiffWithinAt 𝕜 n (g ∘ f) t x :=
  haveI : ContDiffWithinAt 𝕜 n g univ (f x) := h.contDiffAt.contDiffWithinAt
  this.comp x hf (subset_univ _)

theorem ContDiff.comp_contDiffAt {g : F → G} {f : E → F} (x : E) (hg : ContDiff 𝕜 n g)
    (hf : ContDiffAt 𝕜 n f x) : ContDiffAt 𝕜 n (g ∘ f) x :=
  hg.comp_contDiffWithinAt hf

theorem iteratedFDerivWithin_comp_of_eventually_mem {t : Set F}
    (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hxs : x ∈ s) (hst : ∀ᶠ y in 𝓝[s] x, f y ∈ t)
    {i : ℕ} (hi : i ≤ n) :
    iteratedFDerivWithin 𝕜 i (g ∘ f) s x =
      (ftaylorSeriesWithin 𝕜 g t (f x)).taylorComp (ftaylorSeriesWithin 𝕜 f s x) i := by
  obtain ⟨u, hxu, huo, hfu, hgu⟩ : ∃ u, x ∈ u ∧ IsOpen u ∧
      HasFTaylorSeriesUpToOn i f (ftaylorSeriesWithin 𝕜 f s) (s ∩ u) ∧
      HasFTaylorSeriesUpToOn i g (ftaylorSeriesWithin 𝕜 g t) (f '' (s ∩ u)) := by
    have hxt : f x ∈ t := hst.self_of_nhdsWithin hxs
    have hf_tendsto : Tendsto f (𝓝[s] x) (𝓝[t] (f x)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hf.continuousWithinAt, hst⟩
    have H₁ : ∀ᶠ u in (𝓝[s] x).smallSets,
        HasFTaylorSeriesUpToOn i f (ftaylorSeriesWithin 𝕜 f s) u :=
      hf.eventually_hasFTaylorSeriesUpToOn hs hxs hi
    have H₂ : ∀ᶠ u in (𝓝[s] x).smallSets,
        HasFTaylorSeriesUpToOn i g (ftaylorSeriesWithin 𝕜 g t) (f '' u) :=
      hf_tendsto.image_smallSets.eventually (hg.eventually_hasFTaylorSeriesUpToOn ht hxt hi)
    rcases (nhdsWithin_basis_open _ _).smallSets.eventually_iff.mp (H₁.and H₂)
      with ⟨u, ⟨hxu, huo⟩, hu⟩
    exact ⟨u, hxu, huo, hu (by simp [inter_comm])⟩
  exact .symm <| (hgu.comp hfu (mapsTo_image _ _)).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl
    (hs.inter huo) ⟨hxs, hxu⟩ |>.trans <| iteratedFDerivWithin_inter_open huo hxu

theorem iteratedFDerivWithin_comp {t : Set F} (hg : ContDiffWithinAt 𝕜 n g t (f x))
    (hf : ContDiffWithinAt 𝕜 n f s x) (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s)
    (hx : x ∈ s) (hst : MapsTo f s t) {i : ℕ} (hi : i ≤ n) :
    iteratedFDerivWithin 𝕜 i (g ∘ f) s x =
      (ftaylorSeriesWithin 𝕜 g t (f x)).taylorComp (ftaylorSeriesWithin 𝕜 f s x) i :=
  iteratedFDerivWithin_comp_of_eventually_mem hg hf ht hs hx (eventually_mem_nhdsWithin.mono hst) hi

theorem iteratedFDeriv_comp (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffAt 𝕜 n f x)
    {i : ℕ} (hi : i ≤ n) :
    iteratedFDeriv 𝕜 i (g ∘ f) x =
      (ftaylorSeries 𝕜 g (f x)).taylorComp (ftaylorSeries 𝕜 f x) i := by
  simp only [← iteratedFDerivWithin_univ, ← ftaylorSeriesWithin_univ]
  exact iteratedFDerivWithin_comp hg.contDiffWithinAt hf.contDiffWithinAt
    uniqueDiffOn_univ uniqueDiffOn_univ (mem_univ _) (mapsTo_univ _ _) hi

end comp

/-!
### Smoothness of projections
-/

/-- The first projection in a product is `C^∞`. -/
@[fun_prop]
theorem contDiff_fst : ContDiff 𝕜 n (Prod.fst : E × F → E) :=
  IsBoundedLinearMap.contDiff IsBoundedLinearMap.fst

/-- Postcomposing `f` with `Prod.fst` is `C^n` -/
@[fun_prop]
theorem ContDiff.fst {f : E → F × G} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x => (f x).1 :=
  contDiff_fst.comp hf

/-- Precomposing `f` with `Prod.fst` is `C^n` -/
theorem ContDiff.fst' {f : E → G} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x : E × F => f x.1 :=
  hf.comp contDiff_fst

/-- The first projection on a domain in a product is `C^∞`. -/
@[fun_prop]
theorem contDiffOn_fst {s : Set (E × F)} : ContDiffOn 𝕜 n (Prod.fst : E × F → E) s :=
  ContDiff.contDiffOn contDiff_fst

@[fun_prop]
theorem ContDiffOn.fst {f : E → F × G} {s : Set E} (hf : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (fun x => (f x).1) s :=
  contDiff_fst.comp_contDiffOn hf

/-- The first projection at a point in a product is `C^∞`. -/
@[fun_prop]
theorem contDiffAt_fst {p : E × F} : ContDiffAt 𝕜 n (Prod.fst : E × F → E) p :=
  contDiff_fst.contDiffAt

/-- Postcomposing `f` with `Prod.fst` is `C^n` at `(x, y)` -/
@[fun_prop]
theorem ContDiffAt.fst {f : E → F × G} {x : E} (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun x => (f x).1) x :=
  contDiffAt_fst.comp x hf

/-- Precomposing `f` with `Prod.fst` is `C^n` at `(x, y)` -/
theorem ContDiffAt.fst' {f : E → G} {x : E} {y : F} (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun x : E × F => f x.1) (x, y) :=
  ContDiffAt.comp (x, y) hf contDiffAt_fst

/-- Precomposing `f` with `Prod.fst` is `C^n` at `x : E × F` -/
theorem ContDiffAt.fst'' {f : E → G} {x : E × F} (hf : ContDiffAt 𝕜 n f x.1) :
    ContDiffAt 𝕜 n (fun x : E × F => f x.1) x :=
  hf.comp x contDiffAt_fst

/-- The first projection within a domain at a point in a product is `C^∞`. -/
@[fun_prop]
theorem contDiffWithinAt_fst {s : Set (E × F)} {p : E × F} :
    ContDiffWithinAt 𝕜 n (Prod.fst : E × F → E) s p :=
  contDiff_fst.contDiffWithinAt

/-- The second projection in a product is `C^∞`. -/
@[fun_prop]
theorem contDiff_snd : ContDiff 𝕜 n (Prod.snd : E × F → F) :=
  IsBoundedLinearMap.contDiff IsBoundedLinearMap.snd

/-- Postcomposing `f` with `Prod.snd` is `C^n` -/
@[fun_prop]
theorem ContDiff.snd {f : E → F × G} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x => (f x).2 :=
  contDiff_snd.comp hf

/-- Precomposing `f` with `Prod.snd` is `C^n` -/
theorem ContDiff.snd' {f : F → G} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x : E × F => f x.2 :=
  hf.comp contDiff_snd

/-- The second projection on a domain in a product is `C^∞`. -/
@[fun_prop]
theorem contDiffOn_snd {s : Set (E × F)} : ContDiffOn 𝕜 n (Prod.snd : E × F → F) s :=
  ContDiff.contDiffOn contDiff_snd

@[fun_prop]
theorem ContDiffOn.snd {f : E → F × G} {s : Set E} (hf : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (fun x => (f x).2) s :=
  contDiff_snd.comp_contDiffOn hf

/-- The second projection at a point in a product is `C^∞`. -/
@[fun_prop]
theorem contDiffAt_snd {p : E × F} : ContDiffAt 𝕜 n (Prod.snd : E × F → F) p :=
  contDiff_snd.contDiffAt

/-- Postcomposing `f` with `Prod.snd` is `C^n` at `x` -/
@[fun_prop]
theorem ContDiffAt.snd {f : E → F × G} {x : E} (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun x => (f x).2) x :=
  contDiffAt_snd.comp x hf

/-- Precomposing `f` with `Prod.snd` is `C^n` at `(x, y)` -/
theorem ContDiffAt.snd' {f : F → G} {x : E} {y : F} (hf : ContDiffAt 𝕜 n f y) :
    ContDiffAt 𝕜 n (fun x : E × F => f x.2) (x, y) :=
  ContDiffAt.comp (x, y) hf contDiffAt_snd

/-- Precomposing `f` with `Prod.snd` is `C^n` at `x : E × F` -/
theorem ContDiffAt.snd'' {f : F → G} {x : E × F} (hf : ContDiffAt 𝕜 n f x.2) :
    ContDiffAt 𝕜 n (fun x : E × F => f x.2) x :=
  hf.comp x contDiffAt_snd

/-- The second projection within a domain at a point in a product is `C^∞`. -/
@[fun_prop]
theorem contDiffWithinAt_snd {s : Set (E × F)} {p : E × F} :
    ContDiffWithinAt 𝕜 n (Prod.snd : E × F → F) s p :=
  contDiff_snd.contDiffWithinAt

section NAry

variable {E₁ E₂ E₃ : Type*}
variable [NormedAddCommGroup E₁] [NormedAddCommGroup E₂] [NormedAddCommGroup E₃]
  [NormedSpace 𝕜 E₁] [NormedSpace 𝕜 E₂] [NormedSpace 𝕜 E₃]

theorem ContDiff.comp₂ {g : E₁ × E₂ → G} {f₁ : F → E₁} {f₂ : F → E₂} (hg : ContDiff 𝕜 n g)
    (hf₁ : ContDiff 𝕜 n f₁) (hf₂ : ContDiff 𝕜 n f₂) : ContDiff 𝕜 n fun x => g (f₁ x, f₂ x) :=
  hg.comp <| hf₁.prodMk hf₂

theorem ContDiffAt.comp₂ {g : E₁ × E₂ → G} {f₁ : F → E₁} {f₂ : F → E₂} {x : F}
    (hg : ContDiffAt 𝕜 n g (f₁ x, f₂ x))
    (hf₁ : ContDiffAt 𝕜 n f₁ x) (hf₂ : ContDiffAt 𝕜 n f₂ x) :
    ContDiffAt 𝕜 n (fun x => g (f₁ x, f₂ x)) x :=
  hg.comp x (hf₁.prodMk hf₂)

theorem ContDiffAt.comp₂_contDiffWithinAt {g : E₁ × E₂ → G} {f₁ : F → E₁} {f₂ : F → E₂}
    {s : Set F} {x : F} (hg : ContDiffAt 𝕜 n g (f₁ x, f₂ x))
    (hf₁ : ContDiffWithinAt 𝕜 n f₁ s x) (hf₂ : ContDiffWithinAt 𝕜 n f₂ s x) :
    ContDiffWithinAt 𝕜 n (fun x => g (f₁ x, f₂ x)) s x :=
  hg.comp_contDiffWithinAt x (hf₁.prodMk hf₂)

theorem ContDiff.comp₂_contDiffAt {g : E₁ × E₂ → G} {f₁ : F → E₁} {f₂ : F → E₂} {x : F}
    (hg : ContDiff 𝕜 n g) (hf₁ : ContDiffAt 𝕜 n f₁ x) (hf₂ : ContDiffAt 𝕜 n f₂ x) :
    ContDiffAt 𝕜 n (fun x => g (f₁ x, f₂ x)) x :=
  hg.contDiffAt.comp₂ hf₁ hf₂

theorem ContDiff.comp₂_contDiffWithinAt {g : E₁ × E₂ → G} {f₁ : F → E₁} {f₂ : F → E₂}
    {s : Set F} {x : F} (hg : ContDiff 𝕜 n g)
    (hf₁ : ContDiffWithinAt 𝕜 n f₁ s x) (hf₂ : ContDiffWithinAt 𝕜 n f₂ s x) :
    ContDiffWithinAt 𝕜 n (fun x => g (f₁ x, f₂ x)) s x :=
  hg.contDiffAt.comp_contDiffWithinAt x (hf₁.prodMk hf₂)

theorem ContDiff.comp₂_contDiffOn {g : E₁ × E₂ → G} {f₁ : F → E₁} {f₂ : F → E₂} {s : Set F}
    (hg : ContDiff 𝕜 n g) (hf₁ : ContDiffOn 𝕜 n f₁ s) (hf₂ : ContDiffOn 𝕜 n f₂ s) :
    ContDiffOn 𝕜 n (fun x => g (f₁ x, f₂ x)) s :=
  hg.comp_contDiffOn <| hf₁.prodMk hf₂

theorem ContDiff.comp₃ {g : E₁ × E₂ × E₃ → G} {f₁ : F → E₁} {f₂ : F → E₂} {f₃ : F → E₃}
    (hg : ContDiff 𝕜 n g) (hf₁ : ContDiff 𝕜 n f₁) (hf₂ : ContDiff 𝕜 n f₂) (hf₃ : ContDiff 𝕜 n f₃) :
    ContDiff 𝕜 n fun x => g (f₁ x, f₂ x, f₃ x) :=
  hg.comp₂ hf₁ <| hf₂.prodMk hf₃

theorem ContDiff.comp₃_contDiffOn {g : E₁ × E₂ × E₃ → G} {f₁ : F → E₁} {f₂ : F → E₂} {f₃ : F → E₃}
    {s : Set F} (hg : ContDiff 𝕜 n g) (hf₁ : ContDiffOn 𝕜 n f₁ s) (hf₂ : ContDiffOn 𝕜 n f₂ s)
    (hf₃ : ContDiffOn 𝕜 n f₃ s) : ContDiffOn 𝕜 n (fun x => g (f₁ x, f₂ x, f₃ x)) s :=
  hg.comp₂_contDiffOn hf₁ <| hf₂.prodMk hf₃

end NAry

section SpecificBilinearMaps

@[fun_prop]
theorem ContDiff.clm_comp {g : X → F →L[𝕜] G} {f : X → E →L[𝕜] F} (hg : ContDiff 𝕜 n g)
    (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x => (g x).comp (f x) :=
  isBoundedBilinearMap_comp.contDiff.comp₂ (g := fun p => p.1.comp p.2) hg hf

@[fun_prop]
theorem ContDiffOn.clm_comp {g : X → F →L[𝕜] G} {f : X → E →L[𝕜] F} {s : Set X}
    (hg : ContDiffOn 𝕜 n g s) (hf : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (fun x => (g x).comp (f x)) s :=
  (isBoundedBilinearMap_comp (E := E) (F := F) (G := G)).contDiff.comp₂_contDiffOn hg hf

@[fun_prop]
theorem ContDiffAt.clm_comp {g : X → F →L[𝕜] G} {f : X → E →L[𝕜] F} {x : X}
    (hg : ContDiffAt 𝕜 n g x) (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun x => (g x).comp (f x)) x :=
  (isBoundedBilinearMap_comp (E := E) (G := G)).contDiff.comp₂_contDiffAt hg hf

@[fun_prop]
theorem ContDiffWithinAt.clm_comp {g : X → F →L[𝕜] G} {f : X → E →L[𝕜] F} {s : Set X} {x : X}
    (hg : ContDiffWithinAt 𝕜 n g s x) (hf : ContDiffWithinAt 𝕜 n f s x) :
    ContDiffWithinAt 𝕜 n (fun x => (g x).comp (f x)) s x :=
  (isBoundedBilinearMap_comp (E := E) (G := G)).contDiff.comp₂_contDiffWithinAt hg hf

@[fun_prop]
theorem ContDiff.clm_apply {f : E → F →L[𝕜] G} {g : E → F} (hf : ContDiff 𝕜 n f)
    (hg : ContDiff 𝕜 n g) : ContDiff 𝕜 n fun x => (f x) (g x) :=
  isBoundedBilinearMap_apply.contDiff.comp₂ hf hg

@[fun_prop]
theorem ContDiffOn.clm_apply {f : E → F →L[𝕜] G} {g : E → F} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x => (f x) (g x)) s :=
  isBoundedBilinearMap_apply.contDiff.comp₂_contDiffOn hf hg

@[fun_prop]
theorem ContDiffAt.clm_apply {f : E → F →L[𝕜] G} {g : E → F} (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun x => (f x) (g x)) x :=
  isBoundedBilinearMap_apply.contDiff.comp₂_contDiffAt hf hg

@[fun_prop]
theorem ContDiffWithinAt.clm_apply {f : E → F →L[𝕜] G} {g : E → F}
    (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) :
    ContDiffWithinAt 𝕜 n (fun x => (f x) (g x)) s x :=
  isBoundedBilinearMap_apply.contDiff.comp₂_contDiffWithinAt hf hg

@[fun_prop]
theorem ContDiff.smulRight {f : E → StrongDual 𝕜 F} {g : E → G} (hf : ContDiff 𝕜 n f)
    (hg : ContDiff 𝕜 n g) : ContDiff 𝕜 n fun x => (f x).smulRight (g x) :=
  isBoundedBilinearMap_smulRight.contDiff.comp₂ (g := fun p => p.1.smulRight p.2) hf hg

@[fun_prop]
theorem ContDiffOn.smulRight {f : E → StrongDual 𝕜 F} {g : E → G} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x => (f x).smulRight (g x)) s :=
  (isBoundedBilinearMap_smulRight (E := F)).contDiff.comp₂_contDiffOn hf hg

@[fun_prop]
theorem ContDiffAt.smulRight {f : E → StrongDual 𝕜 F} {g : E → G} (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun x => (f x).smulRight (g x)) x :=
  (isBoundedBilinearMap_smulRight (E := F)).contDiff.comp₂_contDiffAt hf hg

@[fun_prop]
theorem ContDiffWithinAt.smulRight {f : E → StrongDual 𝕜 F} {g : E → G}
    (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) :
    ContDiffWithinAt 𝕜 n (fun x => (f x).smulRight (g x)) s x :=
  (isBoundedBilinearMap_smulRight (E := F)).contDiff.comp₂_contDiffWithinAt hf hg

end SpecificBilinearMaps

section ClmApplyConst

/-- Application of a `ContinuousLinearMap` to a constant commutes with `iteratedFDerivWithin`. -/
theorem iteratedFDerivWithin_clm_apply_const_apply
    {s : Set E} (hs : UniqueDiffOn 𝕜 s) {c : E → F →L[𝕜] G}
    (hc : ContDiffOn 𝕜 n c s) {i : ℕ} (hi : i ≤ n) {x : E} (hx : x ∈ s) {u : F} {m : Fin i → E} :
    (iteratedFDerivWithin 𝕜 i (fun y ↦ (c y) u) s x) m = (iteratedFDerivWithin 𝕜 i c s x) m u := by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
    replace hi : (i : ℕ∞ω) < n := lt_of_lt_of_le (by norm_cast; simp) hi
    have h_deriv_apply : DifferentiableOn 𝕜 (iteratedFDerivWithin 𝕜 i (fun y ↦ (c y) u) s) s :=
      (hc.clm_apply contDiffOn_const).differentiableOn_iteratedFDerivWithin hi hs
    have h_deriv : DifferentiableOn 𝕜 (iteratedFDerivWithin 𝕜 i c s) s :=
      hc.differentiableOn_iteratedFDerivWithin hi hs
    simp only [iteratedFDerivWithin_succ_apply_left]
    rw [← fderivWithin_continuousMultilinear_apply_const_apply (hs x hx) (h_deriv_apply x hx)]
    rw [fderivWithin_congr' (fun x hx ↦ ih hi.le hx) hx]
    rw [fderivWithin_clm_apply (hs x hx) (h_deriv.continuousMultilinear_apply_const _ x hx)
      (differentiableWithinAt_const u)]
    rw [fderivWithin_const_apply]
    simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_zero, zero_add]
    rw [fderivWithin_continuousMultilinear_apply_const_apply (hs x hx) (h_deriv x hx)]

/-- Application of a `ContinuousLinearMap` to a constant commutes with `iteratedFDeriv`. -/
theorem iteratedFDeriv_clm_apply_const_apply
    {c : E → F →L[𝕜] G} (hc : ContDiff 𝕜 n c)
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
theorem contDiff_prodAssoc {n : ℕ∞ω} : ContDiff 𝕜 n <| Equiv.prodAssoc E F G :=
  (LinearIsometryEquiv.prodAssoc 𝕜 E F G).contDiff

/-- The natural equivalence `E × (F × G) ≃ (E × F) × G` is smooth.

Warning: see remarks attached to `contDiff_prodAssoc`
-/
theorem contDiff_prodAssoc_symm {n : ℕ∞ω} : ContDiff 𝕜 n <| (Equiv.prodAssoc E F G).symm :=
  (LinearIsometryEquiv.prodAssoc 𝕜 E F G).symm.contDiff

/-! ### Bundled derivatives are smooth -/
section bundled

/-- One direction of `contDiffWithinAt_succ_iff_hasFDerivWithinAt`, but where all derivatives are
taken within the same set. Version for partial derivatives / functions with parameters. If `f x` is
a `C^n+1` family of functions and `g x` is a `C^n` family of points, then the derivative of `f x` at
`g x` depends in a `C^n` way on `x`. We give a general version of this fact relative to sets which
may not have unique derivatives, in the following form.  If `f : E × F → G` is `C^n+1` at
`(x₀, g(x₀))` in `(s ∪ {x₀}) × t ⊆ E × F` and `g : E → F` is `C^n` at `x₀` within some set `s ⊆ E`,
then there is a function `f' : E → F →L[𝕜] G` that is `C^n` at `x₀` within `s` such that for all `x`
sufficiently close to `x₀` within `s ∪ {x₀}` the function `y ↦ f x y` has derivative `f' x` at `g x`
within `t ⊆ F`.  For convenience, we return an explicit set of `x`'s where this holds that is a
subset of `s ∪ {x₀}`.  We need one additional condition, namely that `t` is a neighborhood of
`g(x₀)` within `g '' s`. -/
theorem ContDiffWithinAt.hasFDerivWithinAt_nhds {f : E → F → G} {g : E → F} {t : Set F} (hn : n ≠ ∞)
    {x₀ : E} (hf : ContDiffWithinAt 𝕜 (n + 1) (uncurry f) (insert x₀ s ×ˢ t) (x₀, g x₀))
    (hg : ContDiffWithinAt 𝕜 n g s x₀) (hgt : t ∈ 𝓝[g '' s] g x₀) :
    ∃ v ∈ 𝓝[insert x₀ s] x₀, v ⊆ insert x₀ s ∧ ∃ f' : E → F →L[𝕜] G,
      (∀ x ∈ v, HasFDerivWithinAt (f x) (f' x) t (g x)) ∧
        ContDiffWithinAt 𝕜 n (fun x => f' x) s x₀ := by
  have hst : insert x₀ s ×ˢ t ∈ 𝓝[(fun x => (x, g x)) '' s] (x₀, g x₀) := by
    refine nhdsWithin_mono _ ?_ (nhdsWithin_prod self_mem_nhdsWithin hgt)
    simp_rw [image_subset_iff, mk_preimage_prod, preimage_id', subset_inter_iff, subset_insert,
      true_and, subset_preimage_image]
  obtain ⟨v, hv, hvs, f_an, f', hvf', hf'⟩ :=
    (contDiffWithinAt_succ_iff_hasFDerivWithinAt' hn).mp hf
  refine
    ⟨(fun z => (z, g z)) ⁻¹' v ∩ insert x₀ s, ?_, inter_subset_right, fun z =>
      (f' (z, g z)).comp (ContinuousLinearMap.inr 𝕜 E F), ?_, ?_⟩
  · refine inter_mem ?_ self_mem_nhdsWithin
    have := mem_of_mem_nhdsWithin (mem_insert _ _) hv
    refine mem_nhdsWithin_insert.mpr ⟨this, ?_⟩
    refine (continuousWithinAt_id.prodMk hg.continuousWithinAt).preimage_mem_nhdsWithin' ?_
    rw [← nhdsWithin_le_iff] at hst hv ⊢
    exact (hst.trans <| nhdsWithin_mono _ <| subset_insert _ _).trans hv
  · intro z hz
    have := hvf' (z, g z) hz.1
    refine this.comp _ (hasFDerivAt_prodMk_right _ _).hasFDerivWithinAt ?_
    exact mapsTo_iff_image_subset.mpr (image_prodMk_subset_prod_right hz.2)
  · exact (hf'.continuousLinearMap_comp <| (ContinuousLinearMap.compL 𝕜 F (E × F) G).flip
      (ContinuousLinearMap.inr 𝕜 E F)).comp_of_mem_nhdsWithin_image x₀
      (contDiffWithinAt_id.prodMk hg) hst

/-- The most general lemma stating that `x ↦ fderivWithin 𝕜 (f x) t (g x)` is `C^n`
at a point within a set.
To show that `x ↦ D_yf(x,y)g(x)` (taken within `t`) is `C^m` at `x₀` within `s`, we require that
* `f` is `C^n` at `(x₀, g(x₀))` within `(s ∪ {x₀}) × t` for `n ≥ m+1`.
* `g` is `C^m` at `x₀` within `s`;
* Derivatives are unique at `g(x)` within `t` for `x` sufficiently close to `x₀` within `s ∪ {x₀}`;
* `t` is a neighborhood of `g(x₀)` within `g '' s`; -/
theorem ContDiffWithinAt.fderivWithin'' {f : E → F → G} {g : E → F} {t : Set F}
    (hf : ContDiffWithinAt 𝕜 n (Function.uncurry f) (insert x₀ s ×ˢ t) (x₀, g x₀))
    (hg : ContDiffWithinAt 𝕜 m g s x₀)
    (ht : ∀ᶠ x in 𝓝[insert x₀ s] x₀, UniqueDiffWithinAt 𝕜 t (g x)) (hmn : m + 1 ≤ n)
    (hgt : t ∈ 𝓝[g '' s] g x₀) :
    ContDiffWithinAt 𝕜 m (fun x => fderivWithin 𝕜 (f x) t (g x)) s x₀ := by
  have : ∀ k : ℕ, k ≤ m → ContDiffWithinAt 𝕜 k (fun x => fderivWithin 𝕜 (f x) t (g x)) s x₀ := by
    intro k hkm
    obtain ⟨v, hv, -, f', hvf', hf'⟩ :=
      (hf.of_le <| by grw [hkm, hmn]).hasFDerivWithinAt_nhds (by simp) (hg.of_le hkm) hgt
    refine hf'.congr_of_eventuallyEq_insert ?_
    filter_upwards [hv, ht]
    exact fun y hy h2y => (hvf' y hy).fderivWithin h2y
  match m with
  | ω =>
    obtain rfl : n = ω := by simpa using hmn
    obtain ⟨v, hv, -, f', hvf', hf'⟩ := hf.hasFDerivWithinAt_nhds (by simp) hg hgt
    refine hf'.congr_of_eventuallyEq_insert ?_
    filter_upwards [hv, ht]
    exact fun y hy h2y => (hvf' y hy).fderivWithin h2y
  | ∞ =>
    rw [contDiffWithinAt_infty]
    exact fun k ↦ this k (by exact_mod_cast le_top)
  | (m : ℕ) => exact this _ le_rfl

/-- A special case of `ContDiffWithinAt.fderivWithin''` where we require that `s ⊆ g⁻¹(t)`. -/
theorem ContDiffWithinAt.fderivWithin' {f : E → F → G} {g : E → F} {t : Set F}
    (hf : ContDiffWithinAt 𝕜 n (Function.uncurry f) (insert x₀ s ×ˢ t) (x₀, g x₀))
    (hg : ContDiffWithinAt 𝕜 m g s x₀)
    (ht : ∀ᶠ x in 𝓝[insert x₀ s] x₀, UniqueDiffWithinAt 𝕜 t (g x)) (hmn : m + 1 ≤ n)
    (hst : s ⊆ g ⁻¹' t) : ContDiffWithinAt 𝕜 m (fun x => fderivWithin 𝕜 (f x) t (g x)) s x₀ :=
  hf.fderivWithin'' hg ht hmn <| mem_of_superset self_mem_nhdsWithin <| image_subset_iff.mpr hst

/-- A special case of `ContDiffWithinAt.fderivWithin'` where we require that `x₀ ∈ s` and there
are unique derivatives everywhere within `t`. -/
protected theorem ContDiffWithinAt.fderivWithin {f : E → F → G} {g : E → F} {t : Set F}
    (hf : ContDiffWithinAt 𝕜 n (Function.uncurry f) (s ×ˢ t) (x₀, g x₀))
    (hg : ContDiffWithinAt 𝕜 m g s x₀) (ht : UniqueDiffOn 𝕜 t) (hmn : m + 1 ≤ n) (hx₀ : x₀ ∈ s)
    (hst : s ⊆ g ⁻¹' t) : ContDiffWithinAt 𝕜 m (fun x => fderivWithin 𝕜 (f x) t (g x)) s x₀ := by
  rw [← insert_eq_self.mpr hx₀] at hf
  refine hf.fderivWithin' hg ?_ hmn hst
  rw [insert_eq_self.mpr hx₀]
  exact eventually_of_mem self_mem_nhdsWithin fun x hx => ht _ (hst hx)

/-- `x ↦ fderivWithin 𝕜 (f x) t (g x) (k x)` is smooth at a point within a set. -/
theorem ContDiffWithinAt.fderivWithin_apply {f : E → F → G} {g k : E → F} {t : Set F}
    (hf : ContDiffWithinAt 𝕜 n (Function.uncurry f) (s ×ˢ t) (x₀, g x₀))
    (hg : ContDiffWithinAt 𝕜 m g s x₀) (hk : ContDiffWithinAt 𝕜 m k s x₀) (ht : UniqueDiffOn 𝕜 t)
    (hmn : m + 1 ≤ n) (hx₀ : x₀ ∈ s) (hst : s ⊆ g ⁻¹' t) :
    ContDiffWithinAt 𝕜 m (fun x => fderivWithin 𝕜 (f x) t (g x) (k x)) s x₀ :=
  (contDiff_fst.clm_apply contDiff_snd).contDiffAt.comp_contDiffWithinAt x₀
    ((hf.fderivWithin hg ht hmn hx₀ hst).prodMk hk)

/-- `fderivWithin 𝕜 f s` is smooth at `x₀` within `s`. -/
theorem ContDiffWithinAt.fderivWithin_right (hf : ContDiffWithinAt 𝕜 n f s x₀)
    (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 ≤ n) (hx₀s : x₀ ∈ s) :
    ContDiffWithinAt 𝕜 m (fderivWithin 𝕜 f s) s x₀ :=
  ContDiffWithinAt.fderivWithin
    (ContDiffWithinAt.comp (x₀, x₀) hf contDiffWithinAt_snd <| prod_subset_preimage_snd s s)
    contDiffWithinAt_id hs hmn hx₀s (by rw [preimage_id'])

/-- `x ↦ fderivWithin 𝕜 f s x (k x)` is smooth at `x₀` within `s`. -/
theorem ContDiffWithinAt.fderivWithin_right_apply
    {f : F → G} {k : F → F} {s : Set F} {x₀ : F}
    (hf : ContDiffWithinAt 𝕜 n f s x₀) (hk : ContDiffWithinAt 𝕜 m k s x₀)
    (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 ≤ n) (hx₀s : x₀ ∈ s) :
    ContDiffWithinAt 𝕜 m (fun x => fderivWithin 𝕜 f s x (k x)) s x₀ :=
  ContDiffWithinAt.fderivWithin_apply
    (ContDiffWithinAt.comp (x₀, x₀) hf contDiffWithinAt_snd <| prod_subset_preimage_snd s s)
    contDiffWithinAt_id hk hs hmn hx₀s (by rw [preimage_id'])

-- TODO: can we make a version of `ContDiffWithinAt.fderivWithin` for iterated derivatives?
theorem ContDiffWithinAt.iteratedFDerivWithin_right {i : ℕ} (hf : ContDiffWithinAt 𝕜 n f s x₀)
    (hs : UniqueDiffOn 𝕜 s) (hmn : m + i ≤ n) (hx₀s : x₀ ∈ s) :
    ContDiffWithinAt 𝕜 m (iteratedFDerivWithin 𝕜 i f s) s x₀ := by
  induction i generalizing m with
  | zero =>
    simp only [CharP.cast_eq_zero, add_zero] at hmn
    exact (hf.of_le hmn).continuousLinearMap_comp
      ((continuousMultilinearCurryFin0 𝕜 E F).symm : _ →L[𝕜] E [×0]→L[𝕜] F)
  | succ i hi =>
    rw [Nat.cast_succ, add_comm _ 1, ← add_assoc] at hmn
    exact ((hi hmn).fderivWithin_right hs le_rfl hx₀s).continuousLinearMap_comp
      ((continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (i + 1) ↦ E) F).symm :
        _ →L[𝕜] E [×(i + 1)]→L[𝕜] F)

/-- `x ↦ fderiv 𝕜 (f x) (g x)` is smooth at `x₀`. -/
protected theorem ContDiffAt.fderiv {f : E → F → G} {g : E → F}
    (hf : ContDiffAt 𝕜 n (Function.uncurry f) (x₀, g x₀)) (hg : ContDiffAt 𝕜 m g x₀)
    (hmn : m + 1 ≤ n) : ContDiffAt 𝕜 m (fun x => fderiv 𝕜 (f x) (g x)) x₀ := by
  simp_rw [← fderivWithin_univ]
  refine (ContDiffWithinAt.fderivWithin hf.contDiffWithinAt hg.contDiffWithinAt uniqueDiffOn_univ
    hmn (mem_univ x₀) ?_).contDiffAt univ_mem
  rw [preimage_univ]

@[fun_prop]
protected theorem ContDiffAt.fderiv_succ {f : E → F → G} {g : E → F}
    (hf : ContDiffAt 𝕜 (m + 1) (Function.uncurry f) (x₀, g x₀)) (hg : ContDiffAt 𝕜 m g x₀) :
    ContDiffAt 𝕜 m (fun x => fderiv 𝕜 (f x) (g x)) x₀ :=
  ContDiffAt.fderiv hf hg (le_refl _)

/-- `fderiv 𝕜 f` is smooth at `x₀`. -/
theorem ContDiffAt.fderiv_right (hf : ContDiffAt 𝕜 n f x₀) (hmn : m + 1 ≤ n) :
    ContDiffAt 𝕜 m (fderiv 𝕜 f) x₀ :=
  ContDiffAt.fderiv (ContDiffAt.comp (x₀, x₀) hf contDiffAt_snd) contDiffAt_id hmn

theorem ContDiffAt.fderiv_right_succ (hf : ContDiffAt 𝕜 (n + 1) f x₀) :
    ContDiffAt 𝕜 n (fderiv 𝕜 f) x₀ :=
  ContDiffAt.fderiv (ContDiffAt.comp (x₀, x₀) hf contDiffAt_snd) contDiffAt_id (le_refl (n + 1))

theorem ContDiffAt.iteratedFDeriv_right {i : ℕ} (hf : ContDiffAt 𝕜 n f x₀)
    (hmn : m + i ≤ n) : ContDiffAt 𝕜 m (iteratedFDeriv 𝕜 i f) x₀ := by
  rw [← iteratedFDerivWithin_univ, ← contDiffWithinAt_univ] at *
  exact hf.iteratedFDerivWithin_right uniqueDiffOn_univ hmn trivial

/-- `x ↦ fderiv 𝕜 (f x) (g x)` is smooth. -/
protected theorem ContDiff.fderiv {f : E → F → G} {g : E → F}
    (hf : ContDiff 𝕜 m <| Function.uncurry f) (hg : ContDiff 𝕜 n g) (hnm : n + 1 ≤ m) :
    ContDiff 𝕜 n fun x => fderiv 𝕜 (f x) (g x) :=
  contDiff_iff_contDiffAt.mpr fun _ => hf.contDiffAt.fderiv hg.contDiffAt hnm

@[fun_prop]
protected theorem ContDiff.fderiv_succ {f : E → F → G} {g : E → F}
    (hf : ContDiff 𝕜 (n + 1) <| Function.uncurry f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n fun x => fderiv 𝕜 (f x) (g x) :=
  contDiff_iff_contDiffAt.mpr fun _ => hf.contDiffAt.fderiv hg.contDiffAt (le_refl (n + 1))

/-- `fderiv 𝕜 f` is smooth. -/
theorem ContDiff.fderiv_right (hf : ContDiff 𝕜 n f) (hmn : m + 1 ≤ n) :
    ContDiff 𝕜 m (fderiv 𝕜 f) :=
  contDiff_iff_contDiffAt.mpr fun _x => hf.contDiffAt.fderiv_right hmn

theorem ContDiff.iteratedFDeriv_right {i : ℕ} (hf : ContDiff 𝕜 n f)
    (hmn : m + i ≤ n) : ContDiff 𝕜 m (iteratedFDeriv 𝕜 i f) :=
  contDiff_iff_contDiffAt.mpr fun _x => hf.contDiffAt.iteratedFDeriv_right hmn

@[fun_prop]
theorem ContDiff.iteratedFDeriv_right' {i : ℕ} (hf : ContDiff 𝕜 (m + i) f) :
    ContDiff 𝕜 m (iteratedFDeriv 𝕜 i f) :=
  contDiff_iff_contDiffAt.mpr fun _x => hf.contDiffAt.iteratedFDeriv_right (le_refl _)

/-- `x ↦ fderiv 𝕜 (f x) (g x)` is continuous. -/
theorem Continuous.fderiv {f : E → F → G} {g : E → F}
    (hf : ContDiff 𝕜 n <| Function.uncurry f) (hg : Continuous g) (hn : 1 ≤ n) :
    Continuous fun x => fderiv 𝕜 (f x) (g x) :=
  (hf.fderiv (contDiff_zero.mpr hg) hn).continuous

@[fun_prop]
theorem Continuous.fderiv_one {f : E → F → G} {g : E → F}
    (hf : ContDiff 𝕜 1 <| Function.uncurry f) (hg : Continuous g) :
    Continuous fun x => _root_.fderiv 𝕜 (f x) (g x) :=
  (hf.fderiv (contDiff_zero.mpr hg) (le_refl 1)).continuous

@[fun_prop]
protected theorem Differentiable.fderiv_two {f : E → F → G} {g : E → F}
    (hf : ContDiff 𝕜 2 <| Function.uncurry f) (hg : ContDiff 𝕜 1 g) :
    Differentiable 𝕜 fun x => fderiv 𝕜 (f x) (g x) :=
  ContDiff.differentiable
    (contDiff_iff_contDiffAt.mpr fun _ => hf.contDiffAt.fderiv hg.contDiffAt (le_refl 2))
    one_ne_zero

/-- `x ↦ fderiv 𝕜 (f x) (g x) (k x)` is smooth. -/
theorem ContDiff.fderiv_apply {f : E → F → G} {g k : E → F}
    (hf : ContDiff 𝕜 m <| Function.uncurry f) (hg : ContDiff 𝕜 n g) (hk : ContDiff 𝕜 n k)
    (hnm : n + 1 ≤ m) : ContDiff 𝕜 n fun x => fderiv 𝕜 (f x) (g x) (k x) :=
  (hf.fderiv hg hnm).clm_apply hk

/-- The bundled derivative of a `C^{n+1}` function is `C^n`. -/
theorem contDiffOn_fderivWithin_apply {s : Set E} {f : E → F} (hf : ContDiffOn 𝕜 n f s)
    (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 ≤ n) :
    ContDiffOn 𝕜 m (fun p : E × E => (fderivWithin 𝕜 f s p.1 : E →L[𝕜] F) p.2) (s ×ˢ univ) :=
  ((hf.fderivWithin hs hmn).comp contDiffOn_fst (prod_subset_preimage_fst _ _)).clm_apply
    contDiffOn_snd

/-- If a function is at least `C^1`, its bundled derivative (mapping `(x, v)` to `Df(x) v`) is
continuous. -/
theorem ContDiffOn.continuousOn_fderivWithin_apply (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
    (hn : 1 ≤ n) :
    ContinuousOn (fun p : E × E => (fderivWithin 𝕜 f s p.1 : E → F) p.2) (s ×ˢ univ) :=
  (contDiffOn_fderivWithin_apply (m := 0) hf hs hn).continuousOn

/-- The bundled derivative of a `C^{n+1}` function is `C^n`. -/
theorem ContDiff.contDiff_fderiv_apply {f : E → F} (hf : ContDiff 𝕜 n f) (hmn : m + 1 ≤ n) :
    ContDiff 𝕜 m fun p : E × E => (fderiv 𝕜 f p.1 : E →L[𝕜] F) p.2 := by
  rw [← contDiffOn_univ] at hf ⊢
  rw [← fderivWithin_univ, ← univ_prod_univ]
  exact contDiffOn_fderivWithin_apply hf uniqueDiffOn_univ hmn

theorem ContDiffWithinAt.continuousWithinAt_fderivWithin
    (hf : ContDiffWithinAt 𝕜 n f s x) (hs : UniqueDiffOn 𝕜 s) (hn : n ≠ 0) (hx : x ∈ s) :
    ContinuousWithinAt (fderivWithin 𝕜 f s) s x :=
  hf.fderivWithin_right (m := 0) hs (by simpa [ENat.one_le_iff_ne_zero_withTop]) hx
    |>.continuousWithinAt

theorem ContDiffAt.continuousAt_fderiv (hf : ContDiffAt 𝕜 n f x) (hn : n ≠ 0) :
    ContinuousAt (fderiv 𝕜 f) x :=
  hf.fderiv_right (m := 0) (by simpa [ENat.one_le_iff_ne_zero_withTop]) |>.continuousAt

theorem ContDiffWithinAt.continuousWithinAt_iteratedFDerivWithin {k : ℕ}
    (hf : ContDiffWithinAt 𝕜 n f s x) (hs : UniqueDiffOn 𝕜 s) (hk : k ≤ n) (hx : x ∈ s) :
    ContinuousWithinAt (iteratedFDerivWithin 𝕜 k f s) s x :=
  hf.iteratedFDerivWithin_right (m := 0) hs (by simpa) hx |>.continuousWithinAt

theorem ContinuousOn.continuousOn_iteratedFDerivWithin {k : ℕ}
    (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s) (hk : k ≤ n) :
    ContinuousOn (iteratedFDerivWithin 𝕜 k f s) s :=
  fun _x hx ↦ hf.contDiffWithinAt hx |>.continuousWithinAt_iteratedFDerivWithin hs hk hx

theorem ContDiffAt.continuousAt_iteratedFDeriv {k : ℕ} (hf : ContDiffAt 𝕜 n f x) (hk : k ≤ n) :
    ContinuousAt (iteratedFDeriv 𝕜 k f) x :=
  hf.iteratedFDeriv_right (m := 0) (by simpa) |>.continuousAt

theorem ContinuousOn.continuousOn_iteratedFDeriv {k : ℕ}
    (hf : ContDiffOn 𝕜 n f s) (hs : IsOpen s) (hk : k ≤ n) :
    ContinuousOn (iteratedFDeriv 𝕜 k f) s :=
  fun _x hx ↦ hf.contDiffAt (hs.mem_nhds hx) |>.continuousAt_iteratedFDeriv hk |>.continuousWithinAt

end bundled

section deriv

/-!
### One dimension

All results up to now have been expressed in terms of the general Fréchet derivative `fderiv`. For
maps defined on the field, the one-dimensional derivative `deriv` is often easier to use. In this
paragraph, we reformulate some higher smoothness results in terms of `deriv`.
-/


variable {f₂ : 𝕜 → F} {s₂ : Set 𝕜}

/-- A function is `C^(n + 1)` on a domain with unique derivatives if and only if it is
differentiable there, and its derivative (formulated with `derivWithin`) is `C^n`. -/
theorem contDiffOn_succ_iff_derivWithin (hs : UniqueDiffOn 𝕜 s₂) :
    ContDiffOn 𝕜 (n + 1) f₂ s₂ ↔
      DifferentiableOn 𝕜 f₂ s₂ ∧ (n = ω → AnalyticOn 𝕜 f₂ s₂) ∧
        ContDiffOn 𝕜 n (derivWithin f₂ s₂) s₂ := by
  have : derivWithin f₂ s₂ =
      ContinuousLinearMap.toSpanSingletonCLE.symm ∘ fderivWithin 𝕜 f₂ s₂ := by
    ext; simp [← fderivWithin_derivWithin]
  simp [contDiffOn_succ_iff_fderivWithin hs, this, ContinuousLinearEquiv.comp_contDiffOn_iff]

theorem contDiffOn_infty_iff_derivWithin (hs : UniqueDiffOn 𝕜 s₂) :
    ContDiffOn 𝕜 ∞ f₂ s₂ ↔ DifferentiableOn 𝕜 f₂ s₂ ∧ ContDiffOn 𝕜 ∞ (derivWithin f₂ s₂) s₂ := by
  rw [show ∞ = ∞ + 1 by rfl, contDiffOn_succ_iff_derivWithin hs]
  simp

/-- A function is `C^(n + 1)` on an open domain if and only if it is
differentiable there, and its derivative (formulated with `deriv`) is `C^n`. -/
theorem contDiffOn_succ_iff_deriv_of_isOpen (hs : IsOpen s₂) :
    ContDiffOn 𝕜 (n + 1) f₂ s₂ ↔
      DifferentiableOn 𝕜 f₂ s₂ ∧ (n = ω → AnalyticOn 𝕜 f₂ s₂) ∧
        ContDiffOn 𝕜 n (deriv f₂) s₂ := by
  rw [contDiffOn_succ_iff_derivWithin hs.uniqueDiffOn]
  exact Iff.rfl.and (Iff.rfl.and (contDiffOn_congr fun _ => derivWithin_of_isOpen hs))

theorem contDiffOn_infty_iff_deriv_of_isOpen (hs : IsOpen s₂) :
    ContDiffOn 𝕜 ∞ f₂ s₂ ↔ DifferentiableOn 𝕜 f₂ s₂ ∧ ContDiffOn 𝕜 ∞ (deriv f₂) s₂ := by
  rw [show ∞ = ∞ + 1 by rfl, contDiffOn_succ_iff_deriv_of_isOpen hs]
  simp

protected theorem ContDiffOn.derivWithin (hf : ContDiffOn 𝕜 n f₂ s₂) (hs : UniqueDiffOn 𝕜 s₂)
    (hmn : m + 1 ≤ n) : ContDiffOn 𝕜 m (derivWithin f₂ s₂) s₂ :=
  ((contDiffOn_succ_iff_derivWithin hs).1 (hf.of_le hmn)).2.2

theorem ContDiffOn.deriv_of_isOpen (hf : ContDiffOn 𝕜 n f₂ s₂) (hs : IsOpen s₂) (hmn : m + 1 ≤ n) :
    ContDiffOn 𝕜 m (deriv f₂) s₂ :=
  (hf.derivWithin hs.uniqueDiffOn hmn).congr fun _ hx => (derivWithin_of_isOpen hs hx).symm

theorem ContDiffOn.continuousOn_derivWithin (h : ContDiffOn 𝕜 n f₂ s₂) (hs : UniqueDiffOn 𝕜 s₂)
    (hn : 1 ≤ n) : ContinuousOn (derivWithin f₂ s₂) s₂ := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl] at hn
  exact ((contDiffOn_succ_iff_derivWithin hs).1 (h.of_le hn)).2.2.continuousOn

theorem ContDiffOn.continuousOn_deriv_of_isOpen (h : ContDiffOn 𝕜 n f₂ s₂) (hs : IsOpen s₂)
    (hn : 1 ≤ n) : ContinuousOn (deriv f₂) s₂ := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl] at hn
  exact ((contDiffOn_succ_iff_deriv_of_isOpen hs).1 (h.of_le hn)).2.2.continuousOn

@[fun_prop]
protected lemma ContDiffWithinAt.derivWithin {x : 𝕜}
    (H : ContDiffWithinAt 𝕜 n f₂ s₂ x) (hs : UniqueDiffOn 𝕜 s₂)
    (hmn : m + 1 ≤ n) (hx : x ∈ s₂) :
    ContDiffWithinAt 𝕜 m (derivWithin f₂ s₂) s₂ x := by
  exact ContDiffWithinAt.comp _ (by fun_prop) (g := fun f ↦ f 1) (t := .univ)
    (H.fderivWithin_right hs hmn hx) (fun _ _ ↦ trivial)

/-- A function is `C^(n + 1)` if and only if it is differentiable,
  and its derivative (formulated in terms of `deriv`) is `C^n`. -/
theorem contDiff_succ_iff_deriv :
    ContDiff 𝕜 (n + 1) f₂ ↔ Differentiable 𝕜 f₂ ∧ (n = ω → AnalyticOn 𝕜 f₂ univ) ∧
      ContDiff 𝕜 n (deriv f₂) := by
  simp only [← contDiffOn_univ, contDiffOn_succ_iff_deriv_of_isOpen, isOpen_univ,
    differentiableOn_univ]

theorem contDiff_one_iff_deriv :
    ContDiff 𝕜 1 f₂ ↔ Differentiable 𝕜 f₂ ∧ Continuous (deriv f₂) := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl, contDiff_succ_iff_deriv]
  simp

theorem contDiff_infty_iff_deriv :
    ContDiff 𝕜 ∞ f₂ ↔ Differentiable 𝕜 f₂ ∧ ContDiff 𝕜 ∞ (deriv f₂) := by
  rw [show (∞ : ℕ∞ω) = ∞ + 1 from rfl, contDiff_succ_iff_deriv]
  simp

theorem ContDiff.continuous_deriv (h : ContDiff 𝕜 n f₂) (hn : 1 ≤ n) : Continuous (deriv f₂) := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl] at hn
  exact (contDiff_succ_iff_deriv.mp (h.of_le hn)).2.2.continuous

@[fun_prop]
theorem ContDiff.continuous_deriv_one (h : ContDiff 𝕜 1 f₂) : Continuous (deriv f₂) :=
  ContDiff.continuous_deriv h (le_refl 1)

@[fun_prop]
theorem ContDiff.differentiable_deriv_two (h : ContDiff 𝕜 2 f₂) : Differentiable 𝕜 (deriv f₂) := by
  unfold deriv; fun_prop

@[fun_prop]
protected lemma ContDiffAt.derivWithin {x : 𝕜} (H : ContDiffAt 𝕜 n f₂ x) (hmn : m + 1 ≤ n) :
    ContDiffAt 𝕜 m (deriv f₂) x := by
  simpa using ContDiffWithinAt.derivWithin (s₂ := .univ) H.contDiffWithinAt (by simp) hmn

@[fun_prop]
theorem ContDiff.deriv' (h : ContDiff 𝕜 (n + 1) f₂) : ContDiff 𝕜 n (deriv f₂) := by
  unfold deriv; fun_prop

@[fun_prop]
theorem ContDiff.iterate_deriv :
    ∀ (n : ℕ) {f₂ : 𝕜 → F}, ContDiff 𝕜 ∞ f₂ → ContDiff 𝕜 ∞ (deriv^[n] f₂)
  | 0, _, hf => hf
  | n + 1, _, hf => ContDiff.iterate_deriv n (contDiff_infty_iff_deriv.mp hf).2

@[fun_prop]
theorem ContDiff.iterate_deriv' (n : ℕ) :
    ∀ (k : ℕ) {f₂ : 𝕜 → F}, ContDiff 𝕜 (n + k : ℕ) f₂ → ContDiff 𝕜 n (deriv^[k] f₂)
  | 0, _, hf => hf
  | k + 1, _, hf => ContDiff.iterate_deriv' _ k (contDiff_succ_iff_deriv.mp hf).2.2

end deriv

set_option linter.style.longFile 1700
