/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inverse

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

In this file, we denote `(⊤ : ℕ∞) : WithTop ℕ∞` with `∞` and `⊤ : WithTop ℕ∞` with `ω`.

## Tags

derivative, differentiability, higher derivative, `C^n`, multilinear, Taylor series, formal series
-/

noncomputable section

open scoped NNReal Nat ContDiff

universe u uE uF uG

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule' AddCommGroup.toAddCommMonoid

open Set Fin Filter Function

open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type uF}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type uG} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] {s t : Set E} {f : E → F}
  {g : F → G} {x x₀ : E} {b : E × F → G} {m n : WithTop ℕ∞} {p : E → FormalMultilinearSeries 𝕜 E F}

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

theorem contDiff_zero_fun : ContDiff 𝕜 n fun _ : E => (0 : F) :=
  analyticOnNhd_const.contDiff

/-- Constants are `C^∞`.
-/
theorem contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c :=
  analyticOnNhd_const.contDiff

theorem contDiffOn_const {c : F} {s : Set E} : ContDiffOn 𝕜 n (fun _ : E => c) s :=
  contDiff_const.contDiffOn

theorem contDiffAt_const {c : F} : ContDiffAt 𝕜 n (fun _ : E => c) x :=
  contDiff_const.contDiffAt

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

theorem contDiffWithinAt_singleton : ContDiffWithinAt 𝕜 n f {x} x :=
  (contDiffWithinAt_const (c := f x)).congr (by simp) rfl

/-! ### Smoothness of linear functions -/

/-- Unbundled bounded linear functions are `C^n`.
-/
theorem IsBoundedLinearMap.contDiff (hf : IsBoundedLinearMap 𝕜 f) : ContDiff 𝕜 n f :=
  (ContinuousLinearMap.analyticOnNhd hf.toContinuousLinearMap univ).contDiff

theorem ContinuousLinearMap.contDiff (f : E →L[𝕜] F) : ContDiff 𝕜 n f :=
  f.isBoundedLinearMap.contDiff

theorem ContinuousLinearEquiv.contDiff (f : E ≃L[𝕜] F) : ContDiff 𝕜 n f :=
  (f : E →L[𝕜] F).contDiff

theorem LinearIsometry.contDiff (f : E →ₗᵢ[𝕜] F) : ContDiff 𝕜 n f :=
  f.toContinuousLinearMap.contDiff

theorem LinearIsometryEquiv.contDiff (f : E ≃ₗᵢ[𝕜] F) : ContDiff 𝕜 n f :=
  (f : E →L[𝕜] F).contDiff

/-- The identity is `C^n`.
-/
theorem contDiff_id : ContDiff 𝕜 n (id : E → E) :=
  IsBoundedLinearMap.id.contDiff

theorem contDiffWithinAt_id {s x} : ContDiffWithinAt 𝕜 n (id : E → E) s x :=
  contDiff_id.contDiffWithinAt

theorem contDiffAt_id {x} : ContDiffAt 𝕜 n (id : E → E) x :=
  contDiff_id.contDiffAt

theorem contDiffOn_id {s} : ContDiffOn 𝕜 n (id : E → E) s :=
  contDiff_id.contDiffOn

/-- Bilinear functions are `C^n`.
-/
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
    (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) {i : ℕ} (hi : i ≤ n) :
    iteratedFDerivWithin 𝕜 i (g ∘ f) s x =
      g.compContinuousMultilinearMap (iteratedFDerivWithin 𝕜 i f s x) :=
  ((((hf.of_le hi).ftaylorSeriesWithin hs).continuousLinearMap_comp
    g).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl hs hx).symm

/-- The iterated derivative of the composition with a linear map on the left is
obtained by applying the linear map to the iterated derivative. -/
theorem ContinuousLinearMap.iteratedFDeriv_comp_left {f : E → F} (g : F →L[𝕜] G)
    (hf : ContDiff 𝕜 n f) (x : E) {i : ℕ} (hi : i ≤ n) :
    iteratedFDeriv 𝕜 i (g ∘ f) x = g.compContinuousMultilinearMap (iteratedFDeriv 𝕜 i f x) := by
  simp only [← iteratedFDerivWithin_univ]
  exact g.iteratedFDerivWithin_comp_left hf.contDiffOn uniqueDiffOn_univ (mem_univ x) hi

/-- The iterated derivative within a set of the composition with a linear equiv on the left is
obtained by applying the linear equiv to the iterated derivative. This is true without
differentiability assumptions. -/
theorem ContinuousLinearEquiv.iteratedFDerivWithin_comp_left (g : F ≃L[𝕜] G) (f : E → F)
    (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (i : ℕ) :
    iteratedFDerivWithin 𝕜 i (g ∘ f) s x =
      (g : F →L[𝕜] G).compContinuousMultilinearMap (iteratedFDerivWithin 𝕜 i f s x) := by
  induction' i with i IH generalizing x
  · ext1 m
    simp only [iteratedFDerivWithin_zero_apply, comp_apply,
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

/-- Composition with a linear isometry on the left preserves the norm of the iterated
derivative within a set. -/
theorem LinearIsometry.norm_iteratedFDerivWithin_comp_left {f : E → F} (g : F →ₗᵢ[𝕜] G)
    (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) {i : ℕ} (hi : i ≤ n) :
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
    (hf : ContDiff 𝕜 n f) (x : E) {i : ℕ} (hi : i ≤ n) :
    ‖iteratedFDeriv 𝕜 i (g ∘ f) x‖ = ‖iteratedFDeriv 𝕜 i f x‖ := by
  simp only [← iteratedFDerivWithin_univ]
  exact g.norm_iteratedFDerivWithin_comp_left hf.contDiffOn uniqueDiffOn_univ (mem_univ x) hi

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

/-- If `f` admits a Taylor series `p` in a set `s`, and `g` is linear, then `f ∘ g` admits a Taylor
series in `g ⁻¹' s`, whose `k`-th term is given by `p k (g v₁, ..., g vₖ)` . -/
theorem HasFTaylorSeriesUpToOn.compContinuousLinearMap
    (hf : HasFTaylorSeriesUpToOn n f p s) (g : G →L[𝕜] E) :
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
      · exact ContinuousLinearEquiv.analyticOn _ _
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
  induction' i with i IH generalizing x
  · ext1
    simp only [iteratedFDerivWithin_zero_apply, comp_apply,
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

/-- If two functions `f` and `g` admit Taylor series `p` and `q` in a set `s`, then the cartesian
product of `f` and `g` admits the cartesian product of `p` and `q` as a Taylor series. -/
theorem HasFTaylorSeriesUpToOn.prod {n : WithTop ℕ∞}
    (hf : HasFTaylorSeriesUpToOn n f p s) {g : E → G}
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

/-- The cartesian product of `C^n` functions at a point in a domain is `C^n`. -/
theorem ContDiffWithinAt.prod {s : Set E} {f : E → F} {g : E → G} (hf : ContDiffWithinAt 𝕜 n f s x)
    (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWithinAt 𝕜 n (fun x : E => (f x, g x)) s x := by
  match n with
  | ω =>
    obtain ⟨u, hu, p, hp, h'p⟩ := hf
    obtain ⟨v, hv, q, hq, h'q⟩ := hg
    refine ⟨u ∩ v, Filter.inter_mem hu hv, _,
      (hp.mono inter_subset_left).prod (hq.mono inter_subset_right), fun i ↦ ?_⟩
    change AnalyticOn 𝕜 (fun x ↦ ContinuousMultilinearMap.prodL _ _ _ _ (p x i, q x i))
      (u ∩ v)
    apply AnalyticOnNhd.comp_analyticOn (LinearIsometryEquiv.analyticOnNhd _ _) _
      (Set.mapsTo_univ _ _)
    exact ((h'p i).mono inter_subset_left).prod ((h'q i).mono inter_subset_right)
  | (n : ℕ∞) =>
    intro m hm
    rcases hf m hm with ⟨u, hu, p, hp⟩
    rcases hg m hm with ⟨v, hv, q, hq⟩
    exact
      ⟨u ∩ v, Filter.inter_mem hu hv, _,
        (hp.mono inter_subset_left).prod (hq.mono inter_subset_right)⟩

/-- The cartesian product of `C^n` functions on domains is `C^n`. -/
theorem ContDiffOn.prod {s : Set E} {f : E → F} {g : E → G} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x : E => (f x, g x)) s := fun x hx =>
  (hf x hx).prod (hg x hx)

/-- The cartesian product of `C^n` functions at a point is `C^n`. -/
theorem ContDiffAt.prod {f : E → F} {g : E → G} (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun x : E => (f x, g x)) x :=
  contDiffWithinAt_univ.1 <|
    ContDiffWithinAt.prod (contDiffWithinAt_univ.2 hf) (contDiffWithinAt_univ.2 hg)

/-- The cartesian product of `C^n` functions is `C^n`. -/
theorem ContDiff.prod {f : E → F} {g : E → G} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n fun x : E => (f x, g x) :=
  contDiffOn_univ.1 <| ContDiffOn.prod (contDiffOn_univ.2 hf) (contDiffOn_univ.2 hg)

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
          ((h'p 0).mono wu).congr  fun y hy ↦ (hp.zero_eq' (wu hy)).symm
        have : AnalyticOn 𝕜 (fun y ↦ (continuousMultilinearCurryFin0 𝕜 E F)
            ((continuousMultilinearCurryFin0 𝕜 E F).symm (f y))) w :=
          AnalyticOnNhd.comp_analyticOn (LinearIsometryEquiv.analyticOnNhd _ _ ) this
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

@[deprecated (since := "2024-10-30")] alias ContDiffOn.comp' := ContDiffOn.comp_inter

/-- The composition of a `C^n` function on a domain with a `C^n` function is `C^n`. -/
theorem ContDiff.comp_contDiffOn {s : Set E} {g : F → G} {f : E → F} (hg : ContDiff 𝕜 n g)
    (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 n (g ∘ f) s :=
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

@[deprecated (since := "2024-10-18")]
alias ContDiffWithinAt.comp_of_mem := ContDiffWithinAt.comp_of_mem_nhdsWithin_image

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

@[deprecated (since := "2024-10-18")]
alias ContDiffWithinAt.comp' := ContDiffWithinAt.comp_inter

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

theorem ContDiff.comp_contDiffWithinAt {g : F → G} {f : E → F} (h : ContDiff 𝕜 n g)
    (hf : ContDiffWithinAt 𝕜 n f t x) : ContDiffWithinAt 𝕜 n (g ∘ f) t x :=
  haveI : ContDiffWithinAt 𝕜 n g univ (f x) := h.contDiffAt.contDiffWithinAt
  this.comp x hf (subset_univ _)

theorem ContDiff.comp_contDiffAt {g : F → G} {f : E → F} (x : E) (hg : ContDiff 𝕜 n g)
    (hf : ContDiffAt 𝕜 n f x) : ContDiffAt 𝕜 n (g ∘ f) x :=
  hg.comp_contDiffWithinAt hf

/-!
### Smoothness of projections
-/

/-- The first projection in a product is `C^∞`. -/
theorem contDiff_fst : ContDiff 𝕜 n (Prod.fst : E × F → E) :=
  IsBoundedLinearMap.contDiff IsBoundedLinearMap.fst

/-- Postcomposing `f` with `Prod.fst` is `C^n` -/
theorem ContDiff.fst {f : E → F × G} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x => (f x).1 :=
  contDiff_fst.comp hf

/-- Precomposing `f` with `Prod.fst` is `C^n` -/
theorem ContDiff.fst' {f : E → G} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x : E × F => f x.1 :=
  hf.comp contDiff_fst

/-- The first projection on a domain in a product is `C^∞`. -/
theorem contDiffOn_fst {s : Set (E × F)} : ContDiffOn 𝕜 n (Prod.fst : E × F → E) s :=
  ContDiff.contDiffOn contDiff_fst

theorem ContDiffOn.fst {f : E → F × G} {s : Set E} (hf : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (fun x => (f x).1) s :=
  contDiff_fst.comp_contDiffOn hf

/-- The first projection at a point in a product is `C^∞`. -/
theorem contDiffAt_fst {p : E × F} : ContDiffAt 𝕜 n (Prod.fst : E × F → E) p :=
  contDiff_fst.contDiffAt

/-- Postcomposing `f` with `Prod.fst` is `C^n` at `(x, y)` -/
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
theorem contDiffWithinAt_fst {s : Set (E × F)} {p : E × F} :
    ContDiffWithinAt 𝕜 n (Prod.fst : E × F → E) s p :=
  contDiff_fst.contDiffWithinAt

/-- The second projection in a product is `C^∞`. -/
theorem contDiff_snd : ContDiff 𝕜 n (Prod.snd : E × F → F) :=
  IsBoundedLinearMap.contDiff IsBoundedLinearMap.snd

/-- Postcomposing `f` with `Prod.snd` is `C^n` -/
theorem ContDiff.snd {f : E → F × G} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x => (f x).2 :=
  contDiff_snd.comp hf

/-- Precomposing `f` with `Prod.snd` is `C^n` -/
theorem ContDiff.snd' {f : F → G} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x : E × F => f x.2 :=
  hf.comp contDiff_snd

/-- The second projection on a domain in a product is `C^∞`. -/
theorem contDiffOn_snd {s : Set (E × F)} : ContDiffOn 𝕜 n (Prod.snd : E × F → F) s :=
  ContDiff.contDiffOn contDiff_snd

theorem ContDiffOn.snd {f : E → F × G} {s : Set E} (hf : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (fun x => (f x).2) s :=
  contDiff_snd.comp_contDiffOn hf

/-- The second projection at a point in a product is `C^∞`. -/
theorem contDiffAt_snd {p : E × F} : ContDiffAt 𝕜 n (Prod.snd : E × F → F) p :=
  contDiff_snd.contDiffAt

/-- Postcomposing `f` with `Prod.snd` is `C^n` at `x` -/
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
theorem contDiffWithinAt_snd {s : Set (E × F)} {p : E × F} :
    ContDiffWithinAt 𝕜 n (Prod.snd : E × F → F) s p :=
  contDiff_snd.contDiffWithinAt

section NAry

variable {E₁ E₂ E₃ : Type*}
variable [NormedAddCommGroup E₁] [NormedAddCommGroup E₂] [NormedAddCommGroup E₃]
  [NormedSpace 𝕜 E₁] [NormedSpace 𝕜 E₂] [NormedSpace 𝕜 E₃]

theorem ContDiff.comp₂ {g : E₁ × E₂ → G} {f₁ : F → E₁} {f₂ : F → E₂} (hg : ContDiff 𝕜 n g)
    (hf₁ : ContDiff 𝕜 n f₁) (hf₂ : ContDiff 𝕜 n f₂) : ContDiff 𝕜 n fun x => g (f₁ x, f₂ x) :=
  hg.comp <| hf₁.prod hf₂

theorem ContDiffAt.comp₂ {g : E₁ × E₂ → G} {f₁ : F → E₁} {f₂ : F → E₂} {x : F}
    (hg : ContDiffAt 𝕜 n g (f₁ x, f₂ x))
    (hf₁ : ContDiffAt 𝕜 n f₁ x) (hf₂ : ContDiffAt 𝕜 n f₂ x) :
    ContDiffAt 𝕜 n (fun x => g (f₁ x, f₂ x)) x :=
  hg.comp x (hf₁.prod hf₂)

theorem ContDiffAt.comp₂_contDiffWithinAt {g : E₁ × E₂ → G} {f₁ : F → E₁} {f₂ : F → E₂}
    {s : Set F} {x : F} (hg : ContDiffAt 𝕜 n g (f₁ x, f₂ x))
    (hf₁ : ContDiffWithinAt 𝕜 n f₁ s x) (hf₂ : ContDiffWithinAt 𝕜 n f₂ s x) :
    ContDiffWithinAt 𝕜 n (fun x => g (f₁ x, f₂ x)) s x :=
  hg.comp_contDiffWithinAt x (hf₁.prod hf₂)

@[deprecated (since := "2024-10-30")]
alias ContDiffAt.comp_contDiffWithinAt₂ := ContDiffAt.comp₂_contDiffWithinAt

theorem ContDiff.comp₂_contDiffAt {g : E₁ × E₂ → G} {f₁ : F → E₁} {f₂ : F → E₂} {x : F}
    (hg : ContDiff 𝕜 n g) (hf₁ : ContDiffAt 𝕜 n f₁ x) (hf₂ : ContDiffAt 𝕜 n f₂ x) :
    ContDiffAt 𝕜 n (fun x => g (f₁ x, f₂ x)) x :=
  hg.contDiffAt.comp₂ hf₁ hf₂

@[deprecated (since := "2024-10-30")]
alias ContDiff.comp_contDiffAt₂ := ContDiff.comp₂_contDiffAt

theorem ContDiff.comp₂_contDiffWithinAt {g : E₁ × E₂ → G} {f₁ : F → E₁} {f₂ : F → E₂}
    {s : Set F} {x : F} (hg : ContDiff 𝕜 n g)
    (hf₁ : ContDiffWithinAt 𝕜 n f₁ s x) (hf₂ : ContDiffWithinAt 𝕜 n f₂ s x) :
    ContDiffWithinAt 𝕜 n (fun x => g (f₁ x, f₂ x)) s x :=
  hg.contDiffAt.comp_contDiffWithinAt x  (hf₁.prod hf₂)

@[deprecated (since := "2024-10-30")]
alias ContDiff.comp_contDiffWithinAt₂ := ContDiff.comp₂_contDiffWithinAt

theorem ContDiff.comp₂_contDiffOn {g : E₁ × E₂ → G} {f₁ : F → E₁} {f₂ : F → E₂} {s : Set F}
    (hg : ContDiff 𝕜 n g) (hf₁ : ContDiffOn 𝕜 n f₁ s) (hf₂ : ContDiffOn 𝕜 n f₂ s) :
    ContDiffOn 𝕜 n (fun x => g (f₁ x, f₂ x)) s :=
  hg.comp_contDiffOn <| hf₁.prod hf₂

@[deprecated (since := "2024-10-10")] alias ContDiff.comp_contDiff_on₂ := ContDiff.comp₂_contDiffOn

@[deprecated (since := "2024-10-30")]
alias ContDiff.comp_contDiffOn₂ := ContDiff.comp₂_contDiffOn

theorem ContDiff.comp₃ {g : E₁ × E₂ × E₃ → G} {f₁ : F → E₁} {f₂ : F → E₂} {f₃ : F → E₃}
    (hg : ContDiff 𝕜 n g) (hf₁ : ContDiff 𝕜 n f₁) (hf₂ : ContDiff 𝕜 n f₂) (hf₃ : ContDiff 𝕜 n f₃) :
    ContDiff 𝕜 n fun x => g (f₁ x, f₂ x, f₃ x) :=
  hg.comp₂ hf₁ <| hf₂.prod hf₃

theorem ContDiff.comp₃_contDiffOn {g : E₁ × E₂ × E₃ → G} {f₁ : F → E₁} {f₂ : F → E₂} {f₃ : F → E₃}
    {s : Set F} (hg : ContDiff 𝕜 n g) (hf₁ : ContDiffOn 𝕜 n f₁ s) (hf₂ : ContDiffOn 𝕜 n f₂ s)
    (hf₃ : ContDiffOn 𝕜 n f₃ s) : ContDiffOn 𝕜 n (fun x => g (f₁ x, f₂ x, f₃ x)) s :=
  hg.comp₂_contDiffOn hf₁ <| hf₂.prod hf₃

@[deprecated (since := "2024-10-10")] alias ContDiff.comp_contDiff_on₃ := ContDiff.comp₃_contDiffOn

@[deprecated (since := "2024-10-30")]
alias ContDiff.comp_contDiffOn₃ := ContDiff.comp₃_contDiffOn

end NAry

section SpecificBilinearMaps

theorem ContDiff.clm_comp {g : X → F →L[𝕜] G} {f : X → E →L[𝕜] F} (hg : ContDiff 𝕜 n g)
    (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x => (g x).comp (f x) :=
  isBoundedBilinearMap_comp.contDiff.comp₂ (g := fun p => p.1.comp p.2) hg hf

theorem ContDiffOn.clm_comp {g : X → F →L[𝕜] G} {f : X → E →L[𝕜] F} {s : Set X}
    (hg : ContDiffOn 𝕜 n g s) (hf : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (fun x => (g x).comp (f x)) s :=
  (isBoundedBilinearMap_comp (E := E) (F := F) (G := G)).contDiff.comp₂_contDiffOn hg hf

theorem ContDiffAt.clm_comp {g : X → F →L[𝕜] G} {f : X → E →L[𝕜] F} {x : X}
    (hg : ContDiffAt 𝕜 n g x) (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun x => (g x).comp (f x)) x :=
  (isBoundedBilinearMap_comp (E := E) (G := G)).contDiff.comp₂_contDiffAt hg hf

theorem ContDiffWithinAt.clm_comp {g : X → F →L[𝕜] G} {f : X → E →L[𝕜] F} {s : Set X} {x : X}
    (hg : ContDiffWithinAt 𝕜 n g s x) (hf : ContDiffWithinAt 𝕜 n f s x) :
    ContDiffWithinAt 𝕜 n (fun x => (g x).comp (f x)) s x :=
  (isBoundedBilinearMap_comp (E := E) (G := G)).contDiff.comp₂_contDiffWithinAt hg hf

theorem ContDiff.clm_apply {f : E → F →L[𝕜] G} {g : E → F} (hf : ContDiff 𝕜 n f)
    (hg : ContDiff 𝕜 n g) : ContDiff 𝕜 n fun x => (f x) (g x) :=
  isBoundedBilinearMap_apply.contDiff.comp₂ hf hg

theorem ContDiffOn.clm_apply {f : E → F →L[𝕜] G} {g : E → F} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x => (f x) (g x)) s :=
  isBoundedBilinearMap_apply.contDiff.comp₂_contDiffOn hf hg

theorem ContDiffAt.clm_apply {f : E → F →L[𝕜] G} {g : E → F} (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun x => (f x) (g x)) x :=
  isBoundedBilinearMap_apply.contDiff.comp₂_contDiffAt hf hg

theorem ContDiffWithinAt.clm_apply {f : E → F →L[𝕜] G} {g : E → F}
    (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) :
    ContDiffWithinAt 𝕜 n (fun x => (f x) (g x)) s x :=
  isBoundedBilinearMap_apply.contDiff.comp₂_contDiffWithinAt hf hg

-- Porting note: In Lean 3 we had to give implicit arguments in proofs like the following,
-- to speed up elaboration. In Lean 4 this isn't necessary anymore.
theorem ContDiff.smulRight {f : E → F →L[𝕜] 𝕜} {g : E → G} (hf : ContDiff 𝕜 n f)
    (hg : ContDiff 𝕜 n g) : ContDiff 𝕜 n fun x => (f x).smulRight (g x) :=
  isBoundedBilinearMap_smulRight.contDiff.comp₂ (g := fun p => p.1.smulRight p.2) hf hg

theorem ContDiffOn.smulRight {f : E → F →L[𝕜] 𝕜} {g : E → G} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x => (f x).smulRight (g x)) s :=
  (isBoundedBilinearMap_smulRight (E := F)).contDiff.comp₂_contDiffOn hf hg

theorem ContDiffAt.smulRight {f : E → F →L[𝕜] 𝕜} {g : E → G} (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun x => (f x).smulRight (g x)) x :=
  (isBoundedBilinearMap_smulRight (E := F)).contDiff.comp₂_contDiffAt hf hg

theorem ContDiffWithinAt.smulRight {f : E → F →L[𝕜] 𝕜} {g : E → G}
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
    replace hi : (i : WithTop ℕ∞) < n := lt_of_lt_of_le (by norm_cast; simp) hi
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
theorem contDiff_prodAssoc : ContDiff 𝕜 ω <| Equiv.prodAssoc E F G :=
  (LinearIsometryEquiv.prodAssoc 𝕜 E F G).contDiff

/-- The natural equivalence `E × (F × G) ≃ (E × F) × G` is smooth.

Warning: see remarks attached to `contDiff_prodAssoc`
-/
theorem contDiff_prodAssoc_symm : ContDiff 𝕜 ω <| (Equiv.prodAssoc E F G).symm :=
  (LinearIsometryEquiv.prodAssoc 𝕜 E F G).symm.contDiff

/-! ### Bundled derivatives are smooth -/

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
    refine (continuousWithinAt_id.prod hg.continuousWithinAt).preimage_mem_nhdsWithin' ?_
    rw [← nhdsWithin_le_iff] at hst hv ⊢
    exact (hst.trans <| nhdsWithin_mono _ <| subset_insert _ _).trans hv
  · intro z hz
    have := hvf' (z, g z) hz.1
    refine this.comp _ (hasFDerivAt_prod_mk_right _ _).hasFDerivWithinAt ?_
    exact mapsTo'.mpr (image_prod_mk_subset_prod_right hz.2)
  · exact (hf'.continuousLinearMap_comp <| (ContinuousLinearMap.compL 𝕜 F (E × F) G).flip
      (ContinuousLinearMap.inr 𝕜 E F)).comp_of_mem_nhdsWithin_image x₀
      (contDiffWithinAt_id.prod hg) hst

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
      (hf.of_le <| (add_le_add_right hkm 1).trans hmn).hasFDerivWithinAt_nhds (by simp)
        (hg.of_le hkm) hgt
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
    ((hf.fderivWithin hg ht hmn hx₀ hst).prod hk)

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
theorem ContDiffWithinAt.iteratedFderivWithin_right {i : ℕ} (hf : ContDiffWithinAt 𝕜 n f s x₀)
    (hs : UniqueDiffOn 𝕜 s) (hmn : m + i ≤ n) (hx₀s : x₀ ∈ s) :
    ContDiffWithinAt 𝕜 m (iteratedFDerivWithin 𝕜 i f s) s x₀ := by
  induction' i with i hi generalizing m
  · simp only [CharP.cast_eq_zero, add_zero] at hmn
    exact (hf.of_le hmn).continuousLinearMap_comp
      ((continuousMultilinearCurryFin0 𝕜 E F).symm : _ →L[𝕜] E [×0]→L[𝕜] F)
  · rw [Nat.cast_succ, add_comm _ 1, ← add_assoc] at hmn
    exact ((hi hmn).fderivWithin_right hs le_rfl hx₀s).continuousLinearMap_comp
      ((continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (i+1) ↦ E) F).symm :
        _ →L[𝕜] E [×(i+1)]→L[𝕜] F)

/-- `x ↦ fderiv 𝕜 (f x) (g x)` is smooth at `x₀`. -/
protected theorem ContDiffAt.fderiv {f : E → F → G} {g : E → F}
    (hf : ContDiffAt 𝕜 n (Function.uncurry f) (x₀, g x₀)) (hg : ContDiffAt 𝕜 m g x₀)
    (hmn : m + 1 ≤ n) : ContDiffAt 𝕜 m (fun x => fderiv 𝕜 (f x) (g x)) x₀ := by
  simp_rw [← fderivWithin_univ]
  refine (ContDiffWithinAt.fderivWithin hf.contDiffWithinAt hg.contDiffWithinAt uniqueDiffOn_univ
    hmn (mem_univ x₀) ?_).contDiffAt univ_mem
  rw [preimage_univ]

/-- `fderiv 𝕜 f` is smooth at `x₀`. -/
theorem ContDiffAt.fderiv_right (hf : ContDiffAt 𝕜 n f x₀) (hmn : m + 1 ≤ n) :
    ContDiffAt 𝕜 m (fderiv 𝕜 f) x₀ :=
  ContDiffAt.fderiv (ContDiffAt.comp (x₀, x₀) hf contDiffAt_snd) contDiffAt_id hmn

theorem ContDiffAt.iteratedFDeriv_right {i : ℕ} (hf : ContDiffAt 𝕜 n f x₀)
    (hmn : m + i ≤ n) : ContDiffAt 𝕜 m (iteratedFDeriv 𝕜 i f) x₀ := by
  rw [← iteratedFDerivWithin_univ, ← contDiffWithinAt_univ] at *
  exact hf.iteratedFderivWithin_right uniqueDiffOn_univ hmn trivial

/-- `x ↦ fderiv 𝕜 (f x) (g x)` is smooth. -/
protected theorem ContDiff.fderiv {f : E → F → G} {g : E → F}
    (hf : ContDiff 𝕜 m <| Function.uncurry f) (hg : ContDiff 𝕜 n g) (hnm : n + 1 ≤ m) :
    ContDiff 𝕜 n fun x => fderiv 𝕜 (f x) (g x) :=
  contDiff_iff_contDiffAt.mpr fun _ => hf.contDiffAt.fderiv hg.contDiffAt hnm

/-- `fderiv 𝕜 f` is smooth. -/
theorem ContDiff.fderiv_right (hf : ContDiff 𝕜 n f) (hmn : m + 1 ≤ n) :
    ContDiff 𝕜 m (fderiv 𝕜 f) :=
  contDiff_iff_contDiffAt.mpr fun _x => hf.contDiffAt.fderiv_right hmn

theorem ContDiff.iteratedFDeriv_right {i : ℕ} (hf : ContDiff 𝕜 n f)
    (hmn : m + i ≤ n) : ContDiff 𝕜 m (iteratedFDeriv 𝕜 i f) :=
  contDiff_iff_contDiffAt.mpr fun _x => hf.contDiffAt.iteratedFDeriv_right hmn

/-- `x ↦ fderiv 𝕜 (f x) (g x)` is continuous. -/
theorem Continuous.fderiv {f : E → F → G} {g : E → F}
    (hf : ContDiff 𝕜 n <| Function.uncurry f) (hg : Continuous g) (hn : 1 ≤ n) :
    Continuous fun x => fderiv 𝕜 (f x) (g x) :=
  (hf.fderiv (contDiff_zero.mpr hg) hn).continuous

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

/-!
### Smoothness of functions `f : E → Π i, F' i`
-/

section Pi

variable {ι ι' : Type*} [Fintype ι] [Fintype ι'] {F' : ι → Type*} [∀ i, NormedAddCommGroup (F' i)]
  [∀ i, NormedSpace 𝕜 (F' i)] {φ : ∀ i, E → F' i} {p' : ∀ i, E → FormalMultilinearSeries 𝕜 E (F' i)}
  {Φ : E → ∀ i, F' i} {P' : E → FormalMultilinearSeries 𝕜 E (∀ i, F' i)}

theorem hasFTaylorSeriesUpToOn_pi {n : WithTop ℕ∞} :
    HasFTaylorSeriesUpToOn n (fun x i => φ i x)
        (fun x m => ContinuousMultilinearMap.pi fun i => p' i x m) s ↔
      ∀ i, HasFTaylorSeriesUpToOn n (φ i) (p' i) s := by
  set pr := @ContinuousLinearMap.proj 𝕜 _ ι F' _ _ _
  set L : ∀ m : ℕ, (∀ i, E[×m]→L[𝕜] F' i) ≃ₗᵢ[𝕜] E[×m]→L[𝕜] ∀ i, F' i := fun m =>
    ContinuousMultilinearMap.piₗᵢ _ _
  refine ⟨fun h i => ?_, fun h => ⟨fun x hx => ?_, ?_, ?_⟩⟩
  · exact h.continuousLinearMap_comp (pr i)
  · ext1 i
    exact (h i).zero_eq x hx
  · intro m hm x hx
    exact (L m).hasFDerivAt.comp_hasFDerivWithinAt x <|
      hasFDerivWithinAt_pi.2 fun i => (h i).fderivWithin m hm x hx
  · intro m hm
    exact (L m).continuous.comp_continuousOn <| continuousOn_pi.2 fun i => (h i).cont m hm

@[simp]
theorem hasFTaylorSeriesUpToOn_pi' {n : WithTop ℕ∞} :
    HasFTaylorSeriesUpToOn n Φ P' s ↔
      ∀ i, HasFTaylorSeriesUpToOn n (fun x => Φ x i)
        (fun x m => (@ContinuousLinearMap.proj 𝕜 _ ι F' _ _ _ i).compContinuousMultilinearMap
          (P' x m)) s := by
  convert hasFTaylorSeriesUpToOn_pi (𝕜 := 𝕜) (φ := fun i x ↦ Φ x i); ext; rfl

theorem contDiffWithinAt_pi :
    ContDiffWithinAt 𝕜 n Φ s x ↔ ∀ i, ContDiffWithinAt 𝕜 n (fun x => Φ x i) s x := by
  set pr := @ContinuousLinearMap.proj 𝕜 _ ι F' _ _ _
  refine ⟨fun h i => h.continuousLinearMap_comp (pr i), fun h ↦ ?_⟩
  match n with
  | ω =>
    choose u hux p hp h'p using h
    refine ⟨⋂ i, u i, Filter.iInter_mem.2 hux, _,
      hasFTaylorSeriesUpToOn_pi.2 fun i => (hp i).mono <| iInter_subset _ _, fun m ↦ ?_⟩
    set L : (∀ i, E[×m]→L[𝕜] F' i) ≃ₗᵢ[𝕜] E[×m]→L[𝕜] ∀ i, F' i :=
      ContinuousMultilinearMap.piₗᵢ _ _
    change AnalyticOn 𝕜 (fun x ↦ L (fun i ↦ p i x m)) (⋂ i, u i)
    apply (L.analyticOnNhd univ).comp_analyticOn ?_ (mapsTo_univ _ _)
    exact AnalyticOn.pi (fun i ↦ (h'p i m).mono (iInter_subset _ _))
  | (n : ℕ∞) =>
    intro m hm
    choose u hux p hp using fun i => h i m hm
    exact ⟨⋂ i, u i, Filter.iInter_mem.2 hux, _,
      hasFTaylorSeriesUpToOn_pi.2 fun i => (hp i).mono <| iInter_subset _ _⟩

theorem contDiffOn_pi : ContDiffOn 𝕜 n Φ s ↔ ∀ i, ContDiffOn 𝕜 n (fun x => Φ x i) s :=
  ⟨fun h _ x hx => contDiffWithinAt_pi.1 (h x hx) _, fun h x hx =>
    contDiffWithinAt_pi.2 fun i => h i x hx⟩

theorem contDiffAt_pi : ContDiffAt 𝕜 n Φ x ↔ ∀ i, ContDiffAt 𝕜 n (fun x => Φ x i) x :=
  contDiffWithinAt_pi

theorem contDiff_pi : ContDiff 𝕜 n Φ ↔ ∀ i, ContDiff 𝕜 n fun x => Φ x i := by
  simp only [← contDiffOn_univ, contDiffOn_pi]

theorem contDiff_update [DecidableEq ι] (k : WithTop ℕ∞) (x : ∀ i, F' i) (i : ι) :
    ContDiff 𝕜 k (update x i) := by
  rw [contDiff_pi]
  intro j
  dsimp [Function.update]
  split_ifs with h
  · subst h
    exact contDiff_id
  · exact contDiff_const

variable (F') in
theorem contDiff_single [DecidableEq ι] (k : WithTop ℕ∞) (i : ι) :
    ContDiff 𝕜 k (Pi.single i : F' i → ∀ i, F' i) :=
  contDiff_update k 0 i

variable (𝕜 E)

theorem contDiff_apply (i : ι) : ContDiff 𝕜 n fun f : ι → E => f i :=
  contDiff_pi.mp contDiff_id i

theorem contDiff_apply_apply (i : ι) (j : ι') : ContDiff 𝕜 n fun f : ι → ι' → E => f i j :=
  contDiff_pi.mp (contDiff_apply 𝕜 (ι' → E) i) j

end Pi

/-! ### Sum of two functions -/

section Add

theorem HasFTaylorSeriesUpToOn.add {n : WithTop ℕ∞} {q g} (hf : HasFTaylorSeriesUpToOn n f p s)
    (hg : HasFTaylorSeriesUpToOn n g q s) : HasFTaylorSeriesUpToOn n (f + g) (p + q) s := by
  exact HasFTaylorSeriesUpToOn.continuousLinearMap_comp
    (ContinuousLinearMap.fst 𝕜 F F + .snd 𝕜 F F) (hf.prod hg)

-- The sum is smooth.
theorem contDiff_add : ContDiff 𝕜 n fun p : F × F => p.1 + p.2 :=
  (IsBoundedLinearMap.fst.add IsBoundedLinearMap.snd).contDiff

/-- The sum of two `C^n` functions within a set at a point is `C^n` within this set
at this point. -/
theorem ContDiffWithinAt.add {s : Set E} {f g : E → F} (hf : ContDiffWithinAt 𝕜 n f s x)
    (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWithinAt 𝕜 n (fun x => f x + g x) s x :=
  contDiff_add.contDiffWithinAt.comp x (hf.prod hg) subset_preimage_univ

/-- The sum of two `C^n` functions at a point is `C^n` at this point. -/
theorem ContDiffAt.add {f g : E → F} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    ContDiffAt 𝕜 n (fun x => f x + g x) x := by
  rw [← contDiffWithinAt_univ] at *; exact hf.add hg

/-- The sum of two `C^n`functions is `C^n`. -/
theorem ContDiff.add {f g : E → F} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n fun x => f x + g x :=
  contDiff_add.comp (hf.prod hg)

/-- The sum of two `C^n` functions on a domain is `C^n`. -/
theorem ContDiffOn.add {s : Set E} {f g : E → F} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x => f x + g x) s := fun x hx =>
  (hf x hx).add (hg x hx)

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

/-- The iterated derivative of the sum of two functions is the sum of the iterated derivatives.
This is the same as `iteratedFDerivWithin_add_apply`, but using the spelling `(fun x ↦ f x + g x)`
instead of `f + g`, which can be handy for some rewrites.
TODO: use one form consistently. -/
theorem iteratedFDerivWithin_add_apply' {f g : E → F} (hf : ContDiffOn 𝕜 i f s)
    (hg : ContDiffOn 𝕜 i g s) (hu : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    iteratedFDerivWithin 𝕜 i (fun x => f x + g x) s x =
      iteratedFDerivWithin 𝕜 i f s x + iteratedFDerivWithin 𝕜 i g s x :=
  iteratedFDerivWithin_add_apply hf hg hu hx

theorem iteratedFDeriv_add_apply {i : ℕ} {f g : E → F} (hf : ContDiff 𝕜 i f) (hg : ContDiff 𝕜 i g) :
    iteratedFDeriv 𝕜 i (f + g) x = iteratedFDeriv 𝕜 i f x + iteratedFDeriv 𝕜 i g x := by
  simp_rw [← contDiffOn_univ, ← iteratedFDerivWithin_univ] at hf hg ⊢
  exact iteratedFDerivWithin_add_apply hf hg uniqueDiffOn_univ (Set.mem_univ _)

theorem iteratedFDeriv_add_apply' {i : ℕ} {f g : E → F} (hf : ContDiff 𝕜 i f)
    (hg : ContDiff 𝕜 i g) :
    iteratedFDeriv 𝕜 i (fun x => f x + g x) x = iteratedFDeriv 𝕜 i f x + iteratedFDeriv 𝕜 i g x :=
  iteratedFDeriv_add_apply hf hg

end Add

/-! ### Negative -/

section Neg

-- The negative is smooth.
theorem contDiff_neg : ContDiff 𝕜 n fun p : F => -p :=
  IsBoundedLinearMap.id.neg.contDiff

/-- The negative of a `C^n` function within a domain at a point is `C^n` within this domain at
this point. -/
theorem ContDiffWithinAt.neg {s : Set E} {f : E → F} (hf : ContDiffWithinAt 𝕜 n f s x) :
    ContDiffWithinAt 𝕜 n (fun x => -f x) s x :=
  contDiff_neg.contDiffWithinAt.comp x hf subset_preimage_univ

/-- The negative of a `C^n` function at a point is `C^n` at this point. -/
theorem ContDiffAt.neg {f : E → F} (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun x => -f x) x := by rw [← contDiffWithinAt_univ] at *; exact hf.neg

/-- The negative of a `C^n`function is `C^n`. -/
theorem ContDiff.neg {f : E → F} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x => -f x :=
  contDiff_neg.comp hf

/-- The negative of a `C^n` function on a domain is `C^n`. -/
theorem ContDiffOn.neg {s : Set E} {f : E → F} (hf : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (fun x => -f x) s := fun x hx => (hf x hx).neg

variable {i : ℕ}

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: define `Neg` instance on `ContinuousLinearEquiv`,
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

theorem iteratedFDeriv_neg_apply {i : ℕ} {f : E → F} :
    iteratedFDeriv 𝕜 i (-f) x = -iteratedFDeriv 𝕜 i f x := by
  simp_rw [← iteratedFDerivWithin_univ]
  exact iteratedFDerivWithin_neg_apply uniqueDiffOn_univ (Set.mem_univ _)

end Neg

/-! ### Subtraction -/

/-- The difference of two `C^n` functions within a set at a point is `C^n` within this set
at this point. -/
theorem ContDiffWithinAt.sub {s : Set E} {f g : E → F} (hf : ContDiffWithinAt 𝕜 n f s x)
    (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWithinAt 𝕜 n (fun x => f x - g x) s x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- The difference of two `C^n` functions at a point is `C^n` at this point. -/
theorem ContDiffAt.sub {f g : E → F} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    ContDiffAt 𝕜 n (fun x => f x - g x) x := by simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- The difference of two `C^n` functions on a domain is `C^n`. -/
theorem ContDiffOn.sub {s : Set E} {f g : E → F} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x => f x - g x) s := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- The difference of two `C^n` functions is `C^n`. -/
theorem ContDiff.sub {f g : E → F} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n fun x => f x - g x := by simpa only [sub_eq_add_neg] using hf.add hg.neg

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

theorem ContDiffAt.sum {ι : Type*} {f : ι → E → F} {s : Finset ι} {x : E}
    (h : ∀ i ∈ s, ContDiffAt 𝕜 n (fun x => f i x) x) :
    ContDiffAt 𝕜 n (fun x => ∑ i ∈ s, f i x) x := by
  rw [← contDiffWithinAt_univ] at *; exact ContDiffWithinAt.sum h

theorem ContDiffOn.sum {ι : Type*} {f : ι → E → F} {s : Finset ι} {t : Set E}
    (h : ∀ i ∈ s, ContDiffOn 𝕜 n (fun x => f i x) t) :
    ContDiffOn 𝕜 n (fun x => ∑ i ∈ s, f i x) t := fun x hx =>
  ContDiffWithinAt.sum fun i hi => h i hi x hx

theorem ContDiff.sum {ι : Type*} {f : ι → E → F} {s : Finset ι}
    (h : ∀ i ∈ s, ContDiff 𝕜 n fun x => f i x) : ContDiff 𝕜 n fun x => ∑ i ∈ s, f i x := by
  simp only [← contDiffOn_univ] at *; exact ContDiffOn.sum h

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

/-- The product of two `C^n` functions within a set at a point is `C^n` within this set
at this point. -/
theorem ContDiffWithinAt.mul {s : Set E} {f g : E → 𝔸} (hf : ContDiffWithinAt 𝕜 n f s x)
    (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWithinAt 𝕜 n (fun x => f x * g x) s x :=
  contDiff_mul.comp_contDiffWithinAt (hf.prod hg)

/-- The product of two `C^n` functions at a point is `C^n` at this point. -/
nonrec theorem ContDiffAt.mul {f g : E → 𝔸} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    ContDiffAt 𝕜 n (fun x => f x * g x) x :=
  hf.mul hg

/-- The product of two `C^n` functions on a domain is `C^n`. -/
theorem ContDiffOn.mul {f g : E → 𝔸} (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s) :
    ContDiffOn 𝕜 n (fun x => f x * g x) s := fun x hx => (hf x hx).mul (hg x hx)

/-- The product of two `C^n`functions is `C^n`. -/
theorem ContDiff.mul {f g : E → 𝔸} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n fun x => f x * g x :=
  contDiff_mul.comp (hf.prod hg)

theorem contDiffWithinAt_prod' {t : Finset ι} {f : ι → E → 𝔸'}
    (h : ∀ i ∈ t, ContDiffWithinAt 𝕜 n (f i) s x) : ContDiffWithinAt 𝕜 n (∏ i ∈ t, f i) s x :=
  Finset.prod_induction f (fun f => ContDiffWithinAt 𝕜 n f s x) (fun _ _ => ContDiffWithinAt.mul)
    (contDiffWithinAt_const (c := 1)) h

theorem contDiffWithinAt_prod {t : Finset ι} {f : ι → E → 𝔸'}
    (h : ∀ i ∈ t, ContDiffWithinAt 𝕜 n (f i) s x) :
    ContDiffWithinAt 𝕜 n (fun y => ∏ i ∈ t, f i y) s x := by
  simpa only [← Finset.prod_apply] using contDiffWithinAt_prod' h

theorem contDiffAt_prod' {t : Finset ι} {f : ι → E → 𝔸'} (h : ∀ i ∈ t, ContDiffAt 𝕜 n (f i) x) :
    ContDiffAt 𝕜 n (∏ i ∈ t, f i) x :=
  contDiffWithinAt_prod' h

theorem contDiffAt_prod {t : Finset ι} {f : ι → E → 𝔸'} (h : ∀ i ∈ t, ContDiffAt 𝕜 n (f i) x) :
    ContDiffAt 𝕜 n (fun y => ∏ i ∈ t, f i y) x :=
  contDiffWithinAt_prod h

theorem contDiffOn_prod' {t : Finset ι} {f : ι → E → 𝔸'} (h : ∀ i ∈ t, ContDiffOn 𝕜 n (f i) s) :
    ContDiffOn 𝕜 n (∏ i ∈ t, f i) s := fun x hx => contDiffWithinAt_prod' fun i hi => h i hi x hx

theorem contDiffOn_prod {t : Finset ι} {f : ι → E → 𝔸'} (h : ∀ i ∈ t, ContDiffOn 𝕜 n (f i) s) :
    ContDiffOn 𝕜 n (fun y => ∏ i ∈ t, f i y) s := fun x hx =>
  contDiffWithinAt_prod fun i hi => h i hi x hx

theorem contDiff_prod' {t : Finset ι} {f : ι → E → 𝔸'} (h : ∀ i ∈ t, ContDiff 𝕜 n (f i)) :
    ContDiff 𝕜 n (∏ i ∈ t, f i) :=
  contDiff_iff_contDiffAt.mpr fun _ => contDiffAt_prod' fun i hi => (h i hi).contDiffAt

theorem contDiff_prod {t : Finset ι} {f : ι → E → 𝔸'} (h : ∀ i ∈ t, ContDiff 𝕜 n (f i)) :
    ContDiff 𝕜 n fun y => ∏ i ∈ t, f i y :=
  contDiff_iff_contDiffAt.mpr fun _ => contDiffAt_prod fun i hi => (h i hi).contDiffAt

theorem ContDiff.pow {f : E → 𝔸} (hf : ContDiff 𝕜 n f) : ∀ m : ℕ, ContDiff 𝕜 n fun x => f x ^ m
  | 0 => by simpa using contDiff_const
  | m + 1 => by simpa [pow_succ] using (hf.pow m).mul hf

theorem ContDiffWithinAt.pow {f : E → 𝔸} (hf : ContDiffWithinAt 𝕜 n f s x) (m : ℕ) :
    ContDiffWithinAt 𝕜 n (fun y => f y ^ m) s x :=
  (contDiff_id.pow m).comp_contDiffWithinAt hf

nonrec theorem ContDiffAt.pow {f : E → 𝔸} (hf : ContDiffAt 𝕜 n f x) (m : ℕ) :
    ContDiffAt 𝕜 n (fun y => f y ^ m) x :=
  hf.pow m

theorem ContDiffOn.pow {f : E → 𝔸} (hf : ContDiffOn 𝕜 n f s) (m : ℕ) :
    ContDiffOn 𝕜 n (fun y => f y ^ m) s := fun y hy => (hf y hy).pow m

theorem ContDiffWithinAt.div_const {f : E → 𝕜'} {n} (hf : ContDiffWithinAt 𝕜 n f s x) (c : 𝕜') :
    ContDiffWithinAt 𝕜 n (fun x => f x / c) s x := by
  simpa only [div_eq_mul_inv] using hf.mul contDiffWithinAt_const

nonrec theorem ContDiffAt.div_const {f : E → 𝕜'} {n} (hf : ContDiffAt 𝕜 n f x) (c : 𝕜') :
    ContDiffAt 𝕜 n (fun x => f x / c) x :=
  hf.div_const c

theorem ContDiffOn.div_const {f : E → 𝕜'} {n} (hf : ContDiffOn 𝕜 n f s) (c : 𝕜') :
    ContDiffOn 𝕜 n (fun x => f x / c) s := fun x hx => (hf x hx).div_const c

theorem ContDiff.div_const {f : E → 𝕜'} {n} (hf : ContDiff 𝕜 n f) (c : 𝕜') :
    ContDiff 𝕜 n fun x => f x / c := by simpa only [div_eq_mul_inv] using hf.mul contDiff_const

end MulProd

/-! ### Scalar multiplication -/

section SMul

-- The scalar multiplication is smooth.
theorem contDiff_smul : ContDiff 𝕜 n fun p : 𝕜 × F => p.1 • p.2 :=
  isBoundedBilinearMap_smul.contDiff

/-- The scalar multiplication of two `C^n` functions within a set at a point is `C^n` within this
set at this point. -/
theorem ContDiffWithinAt.smul {s : Set E} {f : E → 𝕜} {g : E → F} (hf : ContDiffWithinAt 𝕜 n f s x)
    (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWithinAt 𝕜 n (fun x => f x • g x) s x :=
  contDiff_smul.contDiffWithinAt.comp x (hf.prod hg) subset_preimage_univ

/-- The scalar multiplication of two `C^n` functions at a point is `C^n` at this point. -/
theorem ContDiffAt.smul {f : E → 𝕜} {g : E → F} (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun x => f x • g x) x := by
  rw [← contDiffWithinAt_univ] at *; exact hf.smul hg

/-- The scalar multiplication of two `C^n` functions is `C^n`. -/
theorem ContDiff.smul {f : E → 𝕜} {g : E → F} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n fun x => f x • g x :=
  contDiff_smul.comp (hf.prod hg)

/-- The scalar multiplication of two `C^n` functions on a domain is `C^n`. -/
theorem ContDiffOn.smul {s : Set E} {f : E → 𝕜} {g : E → F} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x => f x • g x) s := fun x hx =>
  (hf x hx).smul (hg x hx)

end SMul

/-! ### Constant scalar multiplication

Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: generalize results in this section.

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

/-- The scalar multiplication of a constant and a `C^n` function within a set at a point is `C^n`
within this set at this point. -/
theorem ContDiffWithinAt.const_smul {s : Set E} {f : E → F} {x : E} (c : R)
    (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWithinAt 𝕜 n (fun y => c • f y) s x :=
  (contDiff_const_smul c).contDiffAt.comp_contDiffWithinAt x hf

/-- The scalar multiplication of a constant and a `C^n` function at a point is `C^n` at this
point. -/
theorem ContDiffAt.const_smul {f : E → F} {x : E} (c : R) (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun y => c • f y) x := by
  rw [← contDiffWithinAt_univ] at *; exact hf.const_smul c

/-- The scalar multiplication of a constant and a `C^n` function is `C^n`. -/
theorem ContDiff.const_smul {f : E → F} (c : R) (hf : ContDiff 𝕜 n f) :
    ContDiff 𝕜 n fun y => c • f y :=
  (contDiff_const_smul c).comp hf

/-- The scalar multiplication of a constant and a `C^n` on a domain is `C^n`. -/
theorem ContDiffOn.const_smul {s : Set E} {f : E → F} (c : R) (hf : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (fun y => c • f y) s := fun x hx => (hf x hx).const_smul c

variable {i : ℕ} {a : R}

theorem iteratedFDerivWithin_const_smul_apply (hf : ContDiffOn 𝕜 i f s) (hu : UniqueDiffOn 𝕜 s)
    (hx : x ∈ s) : iteratedFDerivWithin 𝕜 i (a • f) s x = a • iteratedFDerivWithin 𝕜 i f s x :=
  (a • (1 : F →L[𝕜] F)).iteratedFDerivWithin_comp_left hf hu hx le_rfl

theorem iteratedFDeriv_const_smul_apply {x : E} (hf : ContDiff 𝕜 i f) :
    iteratedFDeriv 𝕜 i (a • f) x = a • iteratedFDeriv 𝕜 i f x := by
  simp_rw [← contDiffOn_univ, ← iteratedFDerivWithin_univ] at *
  exact iteratedFDerivWithin_const_smul_apply hf uniqueDiffOn_univ (Set.mem_univ _)

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

theorem ContDiffWithinAt.prod_map {s : Set E} {t : Set E'} {f : E → F} {g : E' → F'} {x : E}
    {y : E'} (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g t y) :
    ContDiffWithinAt 𝕜 n (Prod.map f g) (s ×ˢ t) (x, y) :=
  ContDiffWithinAt.prod_map' hf hg

/-- The product map of two `C^n` functions on a set is `C^n` on the product set. -/
theorem ContDiffOn.prod_map {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {F' : Type*}
    [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {s : Set E} {t : Set E'} {f : E → F} {g : E' → F'}
    (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g t) : ContDiffOn 𝕜 n (Prod.map f g) (s ×ˢ t) :=
  (hf.comp contDiffOn_fst (prod_subset_preimage_fst _ _)).prod
    (hg.comp contDiffOn_snd (prod_subset_preimage_snd _ _))

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
theorem ContDiffAt.prod_map {f : E → F} {g : E' → F'} {x : E} {y : E'} (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g y) : ContDiffAt 𝕜 n (Prod.map f g) (x, y) := by
  rw [ContDiffAt] at *
  convert hf.prod_map hg
  simp only [univ_prod_univ]

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
theorem ContDiffAt.prod_map' {f : E → F} {g : E' → F'} {p : E × E'} (hf : ContDiffAt 𝕜 n f p.1)
    (hg : ContDiffAt 𝕜 n g p.2) : ContDiffAt 𝕜 n (Prod.map f g) p := by
  rcases p with ⟨⟩
  exact ContDiffAt.prod_map hf hg

/-- The product map of two `C^n` functions is `C^n`. -/
theorem ContDiff.prod_map {f : E → F} {g : E' → F'} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n (Prod.map f g) := by
  rw [contDiff_iff_contDiffAt] at *
  exact fun ⟨x, y⟩ => (hf x).prod_map (hg y)

theorem contDiff_prod_mk_left (f₀ : F) : ContDiff 𝕜 n fun e : E => (e, f₀) :=
  contDiff_id.prod contDiff_const

theorem contDiff_prod_mk_right (e₀ : E) : ContDiff 𝕜 n fun f : F => (e₀, f) :=
  contDiff_const.prod contDiff_id

end prodMap

/-!
### Inversion in a complete normed algebra (or more generally with summable geometric series)
-/

section AlgebraInverse

variable (𝕜)
variable {R : Type*} [NormedRing R] [NormedAlgebra 𝕜 R]

open NormedRing ContinuousLinearMap Ring

/-- In a complete normed algebra, the operation of inversion is `C^n`, for all `n`, at each
invertible element, as it is analytic. -/
theorem contDiffAt_ring_inverse [HasSummableGeomSeries R] (x : Rˣ) :
    ContDiffAt 𝕜 n Ring.inverse (x : R) := by
  have := AnalyticOnNhd.contDiffOn (analyticOnNhd_inverse (𝕜 := 𝕜) (A := R)) (n := n)
    Units.isOpen.uniqueDiffOn x x.isUnit
  exact this.contDiffAt (Units.isOpen.mem_nhds x.isUnit)

variable {𝕜' : Type*} [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']

theorem contDiffAt_inv {x : 𝕜'} (hx : x ≠ 0) {n} : ContDiffAt 𝕜 n Inv.inv x := by
  simpa only [Ring.inverse_eq_inv'] using contDiffAt_ring_inverse 𝕜 (Units.mk0 x hx)

theorem contDiffOn_inv {n} : ContDiffOn 𝕜 n (Inv.inv : 𝕜' → 𝕜') {0}ᶜ := fun _ hx =>
  (contDiffAt_inv 𝕜 hx).contDiffWithinAt

variable {𝕜}

theorem ContDiffWithinAt.inv {f : E → 𝕜'} {n} (hf : ContDiffWithinAt 𝕜 n f s x) (hx : f x ≠ 0) :
    ContDiffWithinAt 𝕜 n (fun x => (f x)⁻¹) s x :=
  (contDiffAt_inv 𝕜 hx).comp_contDiffWithinAt x hf

theorem ContDiffOn.inv {f : E → 𝕜'} (hf : ContDiffOn 𝕜 n f s) (h : ∀ x ∈ s, f x ≠ 0) :
    ContDiffOn 𝕜 n (fun x => (f x)⁻¹) s := fun x hx => (hf.contDiffWithinAt hx).inv (h x hx)

nonrec theorem ContDiffAt.inv {f : E → 𝕜'} (hf : ContDiffAt 𝕜 n f x) (hx : f x ≠ 0) :
    ContDiffAt 𝕜 n (fun x => (f x)⁻¹) x :=
  hf.inv hx

theorem ContDiff.inv {f : E → 𝕜'} (hf : ContDiff 𝕜 n f) (h : ∀ x, f x ≠ 0) :
    ContDiff 𝕜 n fun x => (f x)⁻¹ := by
  rw [contDiff_iff_contDiffAt]; exact fun x => hf.contDiffAt.inv (h x)

-- TODO: generalize to `f g : E → 𝕜'`
theorem ContDiffWithinAt.div {f g : E → 𝕜} {n} (hf : ContDiffWithinAt 𝕜 n f s x)
    (hg : ContDiffWithinAt 𝕜 n g s x) (hx : g x ≠ 0) :
    ContDiffWithinAt 𝕜 n (fun x => f x / g x) s x := by
  simpa only [div_eq_mul_inv] using hf.mul (hg.inv hx)

theorem ContDiffOn.div {f g : E → 𝕜} {n} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g s) (h₀ : ∀ x ∈ s, g x ≠ 0) : ContDiffOn 𝕜 n (f / g) s := fun x hx =>
  (hf x hx).div (hg x hx) (h₀ x hx)

nonrec theorem ContDiffAt.div {f g : E → 𝕜} {n} (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g x) (hx : g x ≠ 0) : ContDiffAt 𝕜 n (fun x => f x / g x) x :=
  hf.div hg hx

theorem ContDiff.div {f g : E → 𝕜} {n} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g)
    (h0 : ∀ x, g x ≠ 0) : ContDiff 𝕜 n fun x => f x / g x := by
  simp only [contDiff_iff_contDiffAt] at *
  exact fun x => (hf x).div (hg x) (h0 x)

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

/-- At an invertible map `e : M →L[R] M₂` between Banach spaces, the operation of
inversion is `C^n`, for all `n`. -/
theorem ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse [CompleteSpace E] {e : E →L[𝕜] F}
    (he : e.IsInvertible) {n : ℕ∞} :
    ContDiffAt 𝕜 n inverse e := by
  rcases he with ⟨M, rfl⟩
  exact _root_.contDiffAt_map_inverse M

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
  match n with
  | ω =>
    apply AnalyticAt.contDiffAt
    exact f.analyticAt_symm ha hf.analyticAt hf₀'.fderiv
  | (n : ℕ∞) =>
    -- We prove this by induction on `n`
    induction' n using ENat.nat_induction with n IH Itop
    · apply contDiffAt_zero.2
      exact ⟨f.target, IsOpen.mem_nhds f.open_target ha, f.continuousOn_invFun⟩
    · obtain ⟨f', ⟨u, hu, hff'⟩, hf'⟩ := contDiffAt_succ_iff_hasFDerivAt.mp hf
      apply contDiffAt_succ_iff_hasFDerivAt.2
      -- For showing `n.succ` times continuous differentiability (the main inductive step), it
      -- suffices to produce the derivative and show that it is `n` times continuously
      -- differentiable
      have eq_f₀' : f' (f.symm a) = f₀' := (hff' (f.symm a) (mem_of_mem_nhds hu)).unique hf₀'
      -- This follows by a bootstrapping formula expressing the derivative as a
      -- function of `f` itself
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
    · refine contDiffAt_infty.mpr ?_
      intro n
      exact Itop n (contDiffAt_infty.mp hf n)

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

/-- Let `f` be a local homeomorphism of a nontrivially normed field, let `a` be a point in its
target. if `f` is `n` times continuously differentiable at `f.symm a`, and if the derivative at
`f.symm a` is nonzero, then `f.symm` is `n` times continuously differentiable at the point `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem PartialHomeomorph.contDiffAt_symm_deriv [CompleteSpace 𝕜] (f : PartialHomeomorph 𝕜 𝕜)
    {f₀' a : 𝕜} (h₀ : f₀' ≠ 0) (ha : a ∈ f.target) (hf₀' : HasDerivAt f f₀' (f.symm a))
    (hf : ContDiffAt 𝕜 n f (f.symm a)) : ContDiffAt 𝕜 n f.symm a :=
  f.contDiffAt_symm ha (hf₀'.hasFDerivAt_equiv h₀) hf

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

namespace PartialHomeomorph

variable (𝕜)

/-- Restrict a partial homeomorphism to the subsets of the source and target
that consist of points `x ∈ f.source`, `y = f x ∈ f.target`
such that `f` is `C^n` at `x` and `f.symm` is `C^n` at `y`.

Note that `n` is a natural number or `ω`, but not `∞`,
because the set of points of `C^∞`-smoothness of `f` is not guaranteed to be open. -/
@[simps! apply symm_apply source target]
def restrContDiff (f : PartialHomeomorph E F) (n : WithTop ℕ∞) (hn : n ≠ ∞) :
    PartialHomeomorph E F :=
  haveI H : f.IsImage {x | ContDiffAt 𝕜 n f x ∧ ContDiffAt 𝕜 n f.symm (f x)}
      {y | ContDiffAt 𝕜 n f.symm y ∧ ContDiffAt 𝕜 n f (f.symm y)} := fun x hx ↦ by
    simp [hx, and_comm]
  H.restr <| isOpen_iff_mem_nhds.2 fun _ ⟨hxs, hxf, hxf'⟩ ↦
    inter_mem (f.open_source.mem_nhds hxs) <| (hxf.eventually hn).and <|
    f.continuousAt hxs (hxf'.eventually hn)

lemma contDiffOn_restrContDiff_source (f : PartialHomeomorph E F) {n : WithTop ℕ∞} (hn : n ≠ ∞) :
    ContDiffOn 𝕜 n f (f.restrContDiff 𝕜 n hn).source := fun _x hx ↦ hx.2.1.contDiffWithinAt

lemma contDiffOn_restrContDiff_target (f : PartialHomeomorph E F) {n : WithTop ℕ∞} (hn : n ≠ ∞) :
    ContDiffOn 𝕜 n f.symm (f.restrContDiff 𝕜 n hn).target := fun _x hx ↦ hx.2.1.contDiffWithinAt

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
theorem contDiffOn_succ_iff_derivWithin (hs : UniqueDiffOn 𝕜 s₂) :
    ContDiffOn 𝕜 (n + 1) f₂ s₂ ↔
      DifferentiableOn 𝕜 f₂ s₂ ∧ (n = ω → AnalyticOn 𝕜 f₂ s₂) ∧
        ContDiffOn 𝕜 n (derivWithin f₂ s₂) s₂ := by
  rw [contDiffOn_succ_iff_fderivWithin hs, and_congr_right_iff]
  intro _
  constructor
  · rintro ⟨h', h⟩
    refine ⟨h', ?_⟩
    have : derivWithin f₂ s₂ = (fun u : 𝕜 →L[𝕜] F => u 1) ∘ fderivWithin 𝕜 f₂ s₂ := by
      ext x; rfl
    simp_rw [this]
    apply ContDiff.comp_contDiffOn _ h
    exact (isBoundedBilinearMap_apply.isBoundedLinearMap_left _).contDiff
  · rintro ⟨h', h⟩
    refine ⟨h', ?_⟩
    have : fderivWithin 𝕜 f₂ s₂ = smulRight (1 : 𝕜 →L[𝕜] 𝕜) ∘ derivWithin f₂ s₂ := by
      ext x; simp [derivWithin]
    simp only [this]
    apply ContDiff.comp_contDiffOn _ h
    have : IsBoundedBilinearMap 𝕜 fun _ : (𝕜 →L[𝕜] 𝕜) × F => _ := isBoundedBilinearMap_smulRight
    exact (this.isBoundedLinearMap_right _).contDiff

theorem contDiffOn_infty_iff_derivWithin (hs : UniqueDiffOn 𝕜 s₂) :
    ContDiffOn 𝕜 ∞ f₂ s₂ ↔ DifferentiableOn 𝕜 f₂ s₂ ∧ ContDiffOn 𝕜 ∞ (derivWithin f₂ s₂) s₂ := by
  rw [show ∞ = ∞ + 1 by rfl, contDiffOn_succ_iff_derivWithin hs]
  simp

@[deprecated (since := "2024-11-27")]
alias contDiffOn_top_iff_derivWithin := contDiffOn_infty_iff_derivWithin

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

@[deprecated (since := "2024-11-27")]
alias contDiffOn_top_iff_deriv_of_isOpen := contDiffOn_infty_iff_deriv_of_isOpen

protected theorem ContDiffOn.derivWithin (hf : ContDiffOn 𝕜 n f₂ s₂) (hs : UniqueDiffOn 𝕜 s₂)
    (hmn : m + 1 ≤ n) : ContDiffOn 𝕜 m (derivWithin f₂ s₂) s₂ :=
  ((contDiffOn_succ_iff_derivWithin hs).1 (hf.of_le hmn)).2.2

theorem ContDiffOn.deriv_of_isOpen (hf : ContDiffOn 𝕜 n f₂ s₂) (hs : IsOpen s₂) (hmn : m + 1 ≤ n) :
    ContDiffOn 𝕜 m (deriv f₂) s₂ :=
  (hf.derivWithin hs.uniqueDiffOn hmn).congr fun _ hx => (derivWithin_of_isOpen hs hx).symm

theorem ContDiffOn.continuousOn_derivWithin (h : ContDiffOn 𝕜 n f₂ s₂) (hs : UniqueDiffOn 𝕜 s₂)
    (hn : 1 ≤ n) : ContinuousOn (derivWithin f₂ s₂) s₂ := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl] at hn
  exact ((contDiffOn_succ_iff_derivWithin hs).1 (h.of_le hn)).2.2.continuousOn

theorem ContDiffOn.continuousOn_deriv_of_isOpen (h : ContDiffOn 𝕜 n f₂ s₂) (hs : IsOpen s₂)
    (hn : 1 ≤ n) : ContinuousOn (deriv f₂) s₂ := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl] at hn
  exact ((contDiffOn_succ_iff_deriv_of_isOpen hs).1 (h.of_le hn)).2.2.continuousOn

/-- A function is `C^(n + 1)` if and only if it is differentiable,
  and its derivative (formulated in terms of `deriv`) is `C^n`. -/
theorem contDiff_succ_iff_deriv :
    ContDiff 𝕜 (n + 1) f₂ ↔ Differentiable 𝕜 f₂ ∧ (n = ω → AnalyticOn 𝕜 f₂ univ) ∧
      ContDiff 𝕜 n (deriv f₂) := by
  simp only [← contDiffOn_univ, contDiffOn_succ_iff_deriv_of_isOpen, isOpen_univ,
    differentiableOn_univ]

theorem contDiff_one_iff_deriv :
    ContDiff 𝕜 1 f₂ ↔ Differentiable 𝕜 f₂ ∧ Continuous (deriv f₂) := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiff_succ_iff_deriv]
  simp

theorem contDiff_infty_iff_deriv :
    ContDiff 𝕜 ∞ f₂ ↔ Differentiable 𝕜 f₂ ∧ ContDiff 𝕜 ∞ (deriv f₂) := by
  rw [show (∞ : WithTop ℕ∞) = ∞ + 1 from rfl, contDiff_succ_iff_deriv]
  simp

@[deprecated (since := "2024-11-27")] alias contDiff_top_iff_deriv := contDiff_infty_iff_deriv

theorem ContDiff.continuous_deriv (h : ContDiff 𝕜 n f₂) (hn : 1 ≤ n) : Continuous (deriv f₂) := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl] at hn
  exact (contDiff_succ_iff_deriv.mp (h.of_le hn)).2.2.continuous

theorem ContDiff.iterate_deriv :
    ∀ (n : ℕ) {f₂ : 𝕜 → F}, ContDiff 𝕜 ∞ f₂ → ContDiff 𝕜 ∞ (deriv^[n] f₂)
  | 0,     _, hf => hf
  | n + 1, _, hf => ContDiff.iterate_deriv n (contDiff_infty_iff_deriv.mp hf).2

theorem ContDiff.iterate_deriv' (n : ℕ) :
    ∀ (k : ℕ) {f₂ : 𝕜 → F}, ContDiff 𝕜 (n + k : ℕ) f₂ → ContDiff 𝕜 n (deriv^[k] f₂)
  | 0,     _, hf => hf
  | k + 1, _, hf => ContDiff.iterate_deriv' _ k (contDiff_succ_iff_deriv.mp hf).2.2

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

theorem HasFTaylorSeriesUpToOn.restrictScalars {n : WithTop ℕ∞}
    (h : HasFTaylorSeriesUpToOn n f p' s) :
    HasFTaylorSeriesUpToOn n f (fun x => (p' x).restrictScalars 𝕜) s where
  zero_eq x hx := h.zero_eq x hx
  fderivWithin m hm x hx := by
    simpa only using -- Porting note: added `by simpa only using`
      (ContinuousMultilinearMap.restrictScalarsLinear 𝕜).hasFDerivAt.comp_hasFDerivWithinAt x <|
        (h.fderivWithin m hm x hx).restrictScalars 𝕜
  cont m hm := ContinuousMultilinearMap.continuous_restrictScalars.comp_continuousOn (h.cont m hm)

theorem ContDiffWithinAt.restrict_scalars (h : ContDiffWithinAt 𝕜' n f s x) :
    ContDiffWithinAt 𝕜 n f s x := by
  match n with
  | ω =>
    obtain ⟨u, u_mem, p', hp', Hp'⟩ := h
    refine ⟨u, u_mem, _, hp'.restrictScalars _, fun i ↦ ?_⟩
    change AnalyticOn 𝕜 (fun x ↦ ContinuousMultilinearMap.restrictScalarsLinear 𝕜 (p' x i)) u
    apply AnalyticOnNhd.comp_analyticOn _ (Hp' i).restrictScalars (Set.mapsTo_univ _ _)
    exact ContinuousLinearMap.analyticOnNhd _ _
  | (n : ℕ∞) =>
    intro m hm
    rcases h m hm with ⟨u, u_mem, p', hp'⟩
    exact ⟨u, u_mem, _, hp'.restrictScalars _⟩

theorem ContDiffOn.restrict_scalars (h : ContDiffOn 𝕜' n f s) : ContDiffOn 𝕜 n f s := fun x hx =>
  (h x hx).restrict_scalars _

theorem ContDiffAt.restrict_scalars (h : ContDiffAt 𝕜' n f x) : ContDiffAt 𝕜 n f x :=
  contDiffWithinAt_univ.1 <| h.contDiffWithinAt.restrict_scalars _

theorem ContDiff.restrict_scalars (h : ContDiff 𝕜' n f) : ContDiff 𝕜 n f :=
  contDiff_iff_contDiffAt.2 fun _ => h.contDiffAt.restrict_scalars _

end RestrictScalars

set_option linter.style.longFile 2200
