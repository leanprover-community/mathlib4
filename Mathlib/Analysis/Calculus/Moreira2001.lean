/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Util.Superscript
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Moreira's version of Sard's Theorem
-/

open Set Function Asymptotics MeasureTheory Metric Filter
open scoped Topology NNReal ENNReal unitInterval
open Module (finrank)

section NormedField

variable {𝕜 E F G : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

@[simp]
theorem dist_iteratedFDerivWithin_zero (f : E → F) (s : Set E) (x : E)
    (g : E → F) (t : Set E) (y : E) :
    dist (iteratedFDerivWithin 𝕜 0 f s x) (iteratedFDerivWithin 𝕜 0 g t y) = dist (f x) (g y) := by
  simp only [iteratedFDerivWithin_zero_eq_comp, comp_apply, LinearIsometryEquiv.dist_map]

@[simp]
theorem dist_iteratedFDerivWithin_one (f g : E → F) {s t : Set E} {x y : E}
    (hsx : UniqueDiffWithinAt 𝕜 s x) (hyt : UniqueDiffWithinAt 𝕜 t y) :
    dist (iteratedFDerivWithin 𝕜 1 f s x) (iteratedFDerivWithin 𝕜 1 g t y)
      = dist (fderivWithin 𝕜 f s x) (fderivWithin 𝕜 g t y) := by
  simp only [iteratedFDerivWithin_succ_eq_comp_left, comp_apply,
    LinearIsometryEquiv.dist_map, iteratedFDerivWithin_zero_eq_comp,
    LinearIsometryEquiv.comp_fderivWithin, hsx, hyt]
  apply (continuousMultilinearCurryFin0 𝕜 E F).symm.toLinearIsometry.postcomp.dist_map

@[simp]
theorem norm_iteratedFDerivWithin_one (f : E → F) {s : Set E} {x : E}
    (h : UniqueDiffWithinAt 𝕜 s x) :
    ‖iteratedFDerivWithin 𝕜 1 f s x‖ = ‖fderivWithin 𝕜 f s x‖ := by
  simp only [← norm_fderivWithin_iteratedFDerivWithin,
    iteratedFDerivWithin_zero_eq_comp, LinearIsometryEquiv.comp_fderivWithin _ h]
  apply (continuousMultilinearCurryFin0 𝕜 E F).symm.toLinearIsometry.norm_toContinuousLinearMap_comp

end NormedField

local macro:max "ℝ"n:superscript(term) : term => `(Fin $(⟨n.raw[0]⟩) → ℝ)

namespace Moreira2001

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem isBigO_dist_mul_of_fderiv {f : E → F} {x₀ : E} {g : ℝ → ℝ}
    (hg : MonotoneOn (|g ·|) (Ici 0))
    (hfd : ∀ᶠ x in 𝓝 x₀, DifferentiableAt ℝ f x)
    (hfO : fderiv ℝ f =O[𝓝 x₀] (g <| dist · x₀)) :
    (f · - f x₀) =O[𝓝 x₀] fun x ↦ dist x x₀ * g (dist x x₀) := by
  rcases hfO.exists_pos with ⟨C, hC₀, hC⟩
  refine .of_bound C ?_
  choose r hr₀ hd hfC using Metric.eventually_nhds_iff_ball.mp (hfd.and hC.bound)
  filter_upwards [ball_mem_nhds _ hr₀] with x hx
  rw [norm_mul, Real.norm_of_nonneg dist_nonneg, ← mul_assoc, mul_right_comm]
  have hsub : closedBall x₀ (dist x x₀) ⊆ ball x₀ r := closedBall_subset_ball hx
  convert (convex_closedBall _ _).norm_image_sub_le_of_norm_fderiv_le
    (fun z hz ↦ hd z (hsub hz)) _ _ _ using 1
  · rw [← dist_eq_norm]
  · intro z hz
    refine (hfC z <| hsub hz).trans ?_
    gcongr
    exact hg dist_nonneg dist_nonneg hz
  · simp [dist_nonneg]
  · exact le_refl (dist x x₀)

theorem iteratedFDeriv_comp {f : F → G} {g : E → F} {x : E} {n : ℕ}
    (hf : ContDiffAt ℝ n f (g x)) (hg : ContDiffAt ℝ n g x) :
    iteratedFDeriv ℝ n (f ∘ g) x = ∑ c : OrderedFinpartition n,
      c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length f (g x))
        (fun m ↦ iteratedFDeriv ℝ (c.partSize m) g x) := by
  rcases hf.contDiffOn' le_rfl (by simp) with ⟨U, hUo, hxU, hf⟩
  

structure ContDiffHolder (k : ℕ) (α : I) (f : E → F) (K U : Set E) : Prop where
  contDiffOn : ContDiffOn ℝ k f U
  isBigO : ∀ x ∈ K, (iteratedFDeriv ℝ k f · - iteratedFDeriv ℝ k f x) =O[𝓝 x] (dist · x ^ (α : ℝ))

namespace ContDiffHolder

variable {f : E → F} {k : ℕ} {α : I} {K U : Set E}

theorem subset_left {K'} (h : ContDiffHolder k α f K U) (h' : K' ⊆ K) :
    ContDiffHolder k α f K' U :=
  ⟨h.1, fun x hx ↦ h.2 x (h' hx)⟩

theorem subset_right {U'} (h : ContDiffHolder k α f K U) (h' : U' ⊆ U) :
    ContDiffHolder k α f K U' :=
  ⟨h.1.mono h', h.2⟩

theorem comp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {g : F → G} {V L : Set F}
    (hg : ContDiffHolder k α g L V) (hf : ContDiffHolder k α f K U) (hUV : MapsTo f U V) :
    ContDiffHolder k α (g ∘ f) K U where
  contDiffOn := hg.contDiffOn.comp hf.contDiffOn hUV
  isBigO := by
    intro x hx
    

end ContDiffHolder

structure Chart {m p : ℕ} (f : ℝᵐ × ℝᵖ → ℝ) (r : ℝ) where
  d : ℕ
  toFun : ℝᵈ × ℝᵖ → ℝᵐ × ℝᵖ
  apply_snd : ∀ x, (toFun x).2 = x.2
  rLeft : ℝ
  rRight : ℝ
  rLeft_pos : 0 < rLeft
  rRight_pos : 0 < rRight
  cLeft : ℝᵈ
  cRight : ℝᵖ
  dom : Set (ℝᵈ × ℝᵖ) := ball cLeft rLeft ×ˢ ball cRight rRight
  dom_eq : dom = ball cLeft rLeft ×ˢ ball cRight rRight := by rfl
  dist_le : ∀ ⦃x⦄, x ∈ dom → ∀ ⦃y⦄, y ∈ dom → dist x y ≤ dist (toFun x) (toFun y)
  contDiffOn : ContDiffOn ℝ 1 toFun dom
  finiteSet : Set (ℝᵈ × ℝᵖ)
  measurableSet_finiteSet : MeasurableSet finiteSet
  finiteSet_subset : finiteSet ⊆ dom
  isBigO : ∀ x₀ y₀, (x₀, y₀) ∈ finiteSet →
    (fun x ↦ f (toFun (x, y₀)) - f (toFun (x₀, y₀))) =O[𝓝 x₀] (dist · x₀ ^ r)
  ae_isLittleO : ∀ᵐ p₀ ∂volume.restrict finiteSet,
    (fun x ↦ f (toFun (x, p₀.2)) - f (toFun p₀)) =o[𝓝 p₀.1] (dist · p₀.1 ^ r)

namespace Chart

variable {m p : ℕ} {f : ℝᵐ × ℝᵖ → ℝ} {U : Set (ℝᵐ × ℝᵖ)} {r : ℝ}

attribute [coe] toFun

instance instCoeFun : CoeFun (Chart f r) fun c ↦ (Fin c.d → ℝ) × ℝᵖ → ℝᵐ × ℝᵖ where
  coe := toFun

theorem injOn (c : Chart f r) : InjOn c c.dom := fun x hx y hy h ↦
  dist_le_zero.mp <| (c.dist_le hx hy).trans_eq <| by rw [h, dist_self]

@[simps]
def mkOne (α : I) (K : Set (ℝᵐ × ℝᵖ)) (hKm : MeasurableSet K)
    (f : ℝᵐ × ℝᵖ → ℝ) (x₀ : ℝᵐ) (y₀ : ℝᵖ)
    (hmem : (x₀, y₀) ∈ K) (ε : ℝ) (hpos : 0 < ε)
    (hf : ContDiffHolder 1 α f K (ball (x₀, y₀) ε))
    (hdf : ∀ z ∈ K, fderiv ℝ f z ∘L .inl ℝ ℝᵐ ℝᵖ = 0) :
    Chart f (1 + α) where
  d := m
  toFun := id
  apply_snd _ := rfl
  rLeft := ε
  rRight := ε
  rLeft_pos := hpos
  rRight_pos := hpos
  cLeft := x₀
  cRight := y₀
  dist_le _ _ _ _ := le_rfl
  contDiffOn := contDiffOn_id
  finiteSet := K ∩ ball x₀ ε ×ˢ ball y₀ ε
  measurableSet_finiteSet := by measurability
  finiteSet_subset := inter_subset_right
  isBigO a b h := by
    simp only [Real.rpow_add_of_nonneg dist_nonneg zero_le_one α.2.1, Real.rpow_one, id]
    apply isBigO_dist_mul_of_fderiv (g := (· ^ α.1))
    · intro c hc d hd hle
      rw [mem_Ici] at hc hd
      simp (disch := positivity) only [abs_of_nonneg]
      gcongr
      exact α.2.1
    · filter_upwards [isOpen_ball.mem_nhds h.2.1] with x hx
      refine ((hf.contDiffOn.differentiableOn le_rfl).differentiableAt ?_).comp _ ?_
      · apply isOpen_ball.mem_nhds
        rw [← ball_prod_same]
        exact ⟨hx, h.2.2⟩
      · exact differentiableAt_id.prod (differentiableAt_const _)
    · have : Tendsto (·, b) (𝓝 a) (𝓝 (a, b)) :=
        (Continuous.Prod.mk_left b).continuousAt
      refine .trans ?_ <| ((hf.isBigO _ h.1).comp_tendsto this).congr_right (by simp)
      refine .of_bound' ?_
      simp only [comp_def, iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_zero_eq_comp,
        ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map]
      sorry
  ae_isLittleO := by
    sorry

theorem exists_one {α K x₀ y₀} (hf : ContDiffHolder 1 α f K U) (hKm : MeasurableSet K)
    (hU : IsOpen U) (hKU : K ⊆ U)
    (hdf : ∀ x ∈ K, fderiv ℝ f x ∘L .inl ℝ ℝᵐ ℝᵖ = 0) (h₀ : (x₀, y₀) ∈ K) :
    ∃ c : Chart f (1 + α), MapsTo c c.dom U ∧ c '' c.finiteSet ∈ 𝓝[K] (x₀, y₀) := by
  obtain ⟨ε, ε_pos, hεU⟩ : ∃ ε > 0, ball (x₀, y₀) ε ⊆ U :=
    Metric.mem_nhds_iff.mp <| hU.mem_nhds <| hKU h₀
  refine ⟨mkOne α K hKm f x₀ y₀ h₀ ε ε_pos (hf.subset_right hεU) hdf, ?_, ?_⟩
  · rwa [← ball_prod_same] at hεU
  · simp only [mkOne_toFun, image_id, mkOne_finiteSet, ball_prod_same]
    exact inter_mem_nhdsWithin _ <| ball_mem_nhds _ ε_pos

end Chart

theorem theorem_2_1 {m p : ℕ} {k : ℕ} {α : I} (hk : k ≠ 0) {f : ℝᵐ × ℝᵖ → ℝ} {A U : Set (ℝᵐ × ℝᵖ)}
    (hA : MeasurableSet A) -- TODO: not in the original paper
    (hU : IsOpen U) (hAU : A ⊆ U)
    (hf : ContDiffHolder k α f A U) (hfA : EqOn f 0 A) :
    ∃ s : Set (Chart f (k + α)), s.Countable ∧ (∀ c ∈ s, MapsTo c c.dom U) ∧
      ⋃ c ∈ s, c '' c.finiteSet = A := by
  sorry

theorem main [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
    (p k : ℕ) (hp : p < finrank ℝ F)
    (f : E → F) (K U : Set E) (hU : IsOpen U) (hKU : K ⊆ U) (α : I) (hf : ContDiffHolder k α f K U)
    (hrank : ∀ x ∈ K, finrank (LinearMap.range (fderiv ℝ f x)) ≤ p) :
    μH[p + (finrank ℝ E - p) / (k + α)] K = 0 := by
  sorry

end Moreira2001
