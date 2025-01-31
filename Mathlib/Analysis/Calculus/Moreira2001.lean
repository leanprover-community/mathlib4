/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Util.Superscript
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Moreira's version of Sard's Theorem
-/

open Set Function Asymptotics MeasureTheory Metric Filter
open scoped Topology NNReal unitInterval ContDiff
open Module (finrank)

section NormedField

variable {𝕜 E F G : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

theorem ContDiffWithinAt.contDiffOn_inter_isOpen_subset
    {f : E → F} {s t : Set E} {m n : WithTop ℕ∞} {x : E} (h : ContDiffWithinAt 𝕜 n f s x)
    (hle : m ≤ n) (htop : m = ∞ → n = ω) (ht : t ∈ 𝓝[s] x) :
    ∃ u, IsOpen u ∧ x ∈ u ∧ s ∩ u ⊆ t ∧ ContDiffOn 𝕜 m f (insert x s ∩ u) := by
  have : ∀ᶠ u in (𝓝[insert x s] x).smallSets, u ⊆ insert x t :=
    eventually_smallSets_subset.mpr <| insert_mem_nhdsWithin_insert ht
  rcases (nhdsWithin_basis_open _ _).smallSets.eventually_iff.mp
    (this.and <| h.eventually_contDiffOn hle htop) with ⟨u, ⟨hxu, huo⟩, hu⟩
  rcases hu Subset.rfl with ⟨hu_sub, hu⟩
  rw [inter_comm] at hu
  refine ⟨u, huo, hxu, fun z hz ↦ ?_, hu⟩
  rcases eq_or_ne z x with rfl | hne
  · exact mem_of_mem_nhdsWithin hz.1 ht
  · exact (hu_sub ⟨hz.2, subset_insert _ _ hz.1⟩).resolve_left hne

theorem ContDiffWithinAt.hasFTaylorSeriesUpToOn_subset_of_eventually
    {f : E → F} {s t : Set E} {m n : WithTop ℕ∞} {x : E} (h : ContDiffWithinAt 𝕜 n f s x)
    (hle : m ≤ n) (htop : m = ∞ → n = ω) (hs : ∀ᶠ x' in 𝓝[insert x s] x, UniqueDiffWithinAt 𝕜 s x')
    (ht : t ∈ 𝓝[s] x) :
    ∃ u, IsOpen u ∧ x ∈ u ∧ s ∩ u ⊆ t ∧ UniqueDiffOn 𝕜 (insert x s ∩ u) ∧
      HasFTaylorSeriesUpToOn m f (ftaylorSeriesWithin 𝕜 f s) (insert x s ∩ u) := by
  rw [nhdsWithin_insert, eventually_sup, eventually_pure] at hs
  rcases h.contDiffOn_inter_isOpen_subset hle htop (inter_mem hs.2 ht)
    with ⟨u, huo, hxu, hu_sub, hu⟩
  rw [subset_inter_iff] at hu_sub
  have Hunique : UniqueDiffOn 𝕜 (insert x s ∩ u) := by
    rintro z ⟨rfl | hzs, hzu⟩
    · exact (hs.1.mono <| subset_insert _ _).inter <| huo.mem_nhds hxu
    · refine ((hu_sub.1 ⟨hzs, hzu⟩).inter <| huo.mem_nhds hzu).mono ?_
      gcongr
      apply subset_insert
  use u, huo, hxu, hu_sub.2, Hunique
  refine (hu.ftaylorSeriesWithin Hunique).congr_series fun k hk z hz ↦ ?_
  simp only [ftaylorSeriesWithin, iteratedFDerivWithin_inter_open huo hz.2,
    iteratedFDerivWithin_insert]

theorem iteratedFDerivWithin_comp_of_eventually
    {g : F → G} {f : E → F} {s : Set E} {t : Set F} {n : ℕ} {x₀ : E}
    (hg : ContDiffWithinAt 𝕜 n g t (f x₀))
    (ht : ∀ᶠ y in 𝓝[insert (f x₀) t] f x₀, UniqueDiffWithinAt 𝕜 t y)
    (hf : ContDiffWithinAt 𝕜 n f s x₀)
    (hs : ∀ᶠ x in 𝓝[insert x₀ s] x₀, UniqueDiffWithinAt 𝕜 s x)
    (hmaps : ∀ᶠ x in 𝓝[s] x₀, f x ∈ t) :
    iteratedFDerivWithin 𝕜 n (g ∘ f) s x₀ =
      (ftaylorSeriesWithin 𝕜 g t (f x₀)).taylorComp (ftaylorSeriesWithin 𝕜 f s x₀) n := by
  rcases hg.hasFTaylorSeriesUpToOn_subset_of_eventually le_rfl (by simp) ht univ_mem
    with ⟨u, huo, hx₀u, -, -, hu⟩
  have hmem : f ⁻¹' (t ∩ u) ∈ 𝓝[s] x₀ :=
    hmaps.and <| hf.continuousWithinAt <| huo.mem_nhds hx₀u
  rcases hf.hasFTaylorSeriesUpToOn_subset_of_eventually le_rfl (by simp) hs hmem
    with ⟨v, hvo, hx₀v, hv_sub, hv_unique, hv⟩
  refine .trans ?_ ((hu.comp hv ?_).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl hv_unique
    ⟨mem_insert .., hx₀v⟩).symm
  · rw [iteratedFDerivWithin_inter_open hvo hx₀v, iteratedFDerivWithin_insert]
  · rw [insert_inter_of_mem hx₀v, insert_inter_of_mem hx₀u]
    exact .insert (mapsTo_iff_subset_preimage.mpr hv_sub) _

theorem iteratedFDerivWithin_comp {g : F → G} {f : E → F} {s : Set E} {t : Set F} {n : ℕ} {x : E}
    (hg : ContDiffWithinAt 𝕜 n g t (f x)) (ht : UniqueDiffOn 𝕜 t)
    (hf : ContDiffWithinAt 𝕜 n f s x) (hs : UniqueDiffOn 𝕜 s)
    (hmaps : MapsTo f s t) (hx : x ∈ s) :
    iteratedFDerivWithin 𝕜 n (g ∘ f) s x =
      (ftaylorSeriesWithin 𝕜 g t (f x)).taylorComp (ftaylorSeriesWithin 𝕜 f s x) n := by
  apply iteratedFDerivWithin_comp_of_eventually hg _ hf
  · rw [insert_eq_of_mem hx]
    exact eventually_mem_nhdsWithin.mono hs
  · exact eventually_mem_nhdsWithin.mono hmaps
  · rw [insert_eq_of_mem (hmaps hx)]
    exact eventually_mem_nhdsWithin.mono ht

theorem iteratedFDeriv_comp {g : F → G} {f : E → F} {n : ℕ} {x : E} (hg : ContDiffAt 𝕜 n g (f x))
    (hf : ContDiffAt 𝕜 n f x) :
    iteratedFDeriv 𝕜 n (g ∘ f) x =
      (ftaylorSeries 𝕜 g (f x)).taylorComp (ftaylorSeries 𝕜 f x) n := by
  simp only [← ftaylorSeriesWithin_univ, ← iteratedFDerivWithin_univ]
  apply iteratedFDerivWithin_comp <;> simp [contDiffWithinAt_univ, hf, hg, uniqueDiffOn_univ]

namespace OrderedFinpartition

variable {n : ℕ} (c : OrderedFinpartition n)

theorem norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le
    (f₁ f₂ : F [×c.length]→L[𝕜] G) (g₁ g₂ : ∀ i, E [×c.partSize i]→L[𝕜] F) :
    ‖c.compAlongOrderedFinpartition f₁ g₁ - c.compAlongOrderedFinpartition f₂ g₂‖ ≤
      ‖f₁‖ * c.length * max ‖g₁‖ ‖g₂‖ ^ (c.length - 1) * ‖g₁ - g₂‖ + ‖f₁ - f₂‖ * ∏ i, ‖g₂ i‖ := calc
  _ ≤ ‖c.compAlongOrderedFinpartition f₁ g₁ - c.compAlongOrderedFinpartition f₁ g₂‖ +
      ‖c.compAlongOrderedFinpartition f₁ g₂ - c.compAlongOrderedFinpartition f₂ g₂‖ :=
    norm_sub_le_norm_sub_add_norm_sub ..
  _ ≤ ‖f₁‖ * c.length * max ‖g₁‖ ‖g₂‖ ^ (c.length - 1) * ‖g₁ - g₂‖ + ‖f₁ - f₂‖ * ∏ i, ‖g₂ i‖ := by
    gcongr
    · refine ((c.compAlongOrderedFinpartitionL 𝕜 E F G f₁).norm_image_sub_le g₁ g₂).trans ?_
      simp only [Fintype.card_fin]
      gcongr
      apply norm_compAlongOrderedFinpartitionL_apply_le
    · exact c.norm_compAlongOrderedFinpartition_le (f₁ - f₂) g₂

end OrderedFinpartition

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

theorem isBigO_of_le (h : ContDiffHolder k α f K U) (hU : IsOpen U) (hKU : K ⊆ U)
    {m : ℕ} (hle : m ≤ k) {x} (hx : x ∈ K) :
    (iteratedFDeriv ℝ m f · - iteratedFDeriv ℝ m f x) =O[𝓝 x] (dist · x ^ (α : ℝ)) := by
  rcases hle.eq_or_lt with rfl | hlt
  · exact h.isBigO x hx
  · apply hKU at hx
    have := (h.1.differentiableOn_iteratedFDerivWithin (mod_cast hlt)
      hU.uniqueDiffOn).differentiableAt (hU.mem_nhds hx)
    refine (this.isBigO_sub.congr' ?_ .rfl).trans <| .of_bound' ?_
    · filter_upwards [hU.mem_nhds hx] with z hz
      rw [iteratedFDerivWithin_of_isOpen, iteratedFDerivWithin_of_isOpen] <;> assumption
    · filter_upwards [closedBall_mem_nhds _ one_pos] with y hy
      rw [Real.norm_of_nonneg (by positivity), ← dist_eq_norm]
      exact Real.self_le_rpow_of_le_one dist_nonneg hy α.2.2

theorem comp {g : F → G} {V L : Set F} (hg : ContDiffHolder k α g L V)
    (hf : ContDiffHolder k α f K U) (hUV : MapsTo f U V) :
    ContDiffHolder k α (g ∘ f) K U where
  contDiffOn := hg.contDiffOn.comp hf.contDiffOn hUV
  isBigO x hx := by
    sorry

theorem mono_alpha {α' : I} (hα': α' ≤ α) (hf : ContDiffHolder k α f K U) :
    ContDiffHolder k α' f K U where
  contDiffOn := hf.contDiffOn
  isBigO x hx := by sorry
    -- morally, same proof as monotonicity of local Holder continuity in alpha ∈ (0,1]

theorem of_contDiffOn (hf : ContDiffOn ℝ (k + 1) f U) (hU : IsOpen U) :
    ContDiffHolder k α f K U where
  contDiffOn := hf.of_le (by norm_num)
  isBigO x hx := by
    -- prose proof: iteratedFDeriv ℝ k f x_1 is C¹, in particular Hölder
    -- complications for formalising: iteratedFDeriv is not as well-behaved...
    sorry

theorem mono_k {k' : ℕ} (hk': k' ≤ k) (hf : ContDiffHolder k α f K U) :
    ContDiffHolder k' α f K U where
  contDiffOn := hf.contDiffOn.of_le (by norm_cast)
  isBigO x hx := by
    by_cases h: k' = k
    · exact h ▸ hf.isBigO x hx
    -- choose k'' between k and k', then use ContDiffHolder.ofContDiffOn
    sorry


end ContDiffHolder

-- The next section tries to formalize a wrong (too weak) version of Theorem 2.1.
-- In fact, covering is chosen before `f`.

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

-- Theorem 3.4 from the paper: assuming α ≠ 0, in particular
theorem thm34 [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F] -- added for now. TODO: necessary?
    (p k : ℕ) (hp : p < finrank ℝ F)
    (f : E → F) (K U : Set E) (hU : IsOpen U) (hKU : K ⊆ U) (α : I) (hα: α ≠ 0)
    (hf : ContDiffHolder k α f K U)
    (hrank : ∀ x ∈ K, finrank (LinearMap.range (fderiv ℝ f x)) ≤ p) :
    μH[p + (finrank ℝ E - p) / (k + α)] (f '' K) = 0 := by sorry

-- Moreira claims (Remark 3.5) that Theorem 3.3 also proves this.
theorem thm33' [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F] -- added for now. TODO: necessary?
    (hdim: finrank ℝ E < finrank ℝ F)
    (f : E → F) {s : Set E} {f' : E → E →L[ℝ] F}
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (h'f' : ∀ x ∈ s, finrank (LinearMap.range (f' x)) < (finrank ℝ E)) :
    μH[(finrank ℝ E)] (f '' s) = 0 := by
  -- mathlib has Theorem 3.3 as MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
  -- somehow reduce to that setting
  sorry

theorem main [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F] -- added this line; TODO: necessary?
    (p k : ℕ) (hp : p < finrank ℝ F)
    (f : E → F) (K U : Set E) (hU : IsOpen U) (hKU : K ⊆ U) (α : I) (hf : ContDiffHolder k α f K U)
    (hrank : ∀ x ∈ K, finrank (LinearMap.range (fderiv ℝ f x)) ≤ p) :
    μH[p + (finrank ℝ E - p) / (k + α)] (f '' K) = 0 := by
  by_cases h: α = 0; swap
  · exact thm34 p k hp f K U hU hKU α h hf hrank
  -- This is Remark 3.5 in the paper.
  replace hf := hf.contDiffOn
  by_cases k ≥ 2
  · have : ContDiffHolder (k - 1) 1 f K U := by
      apply ContDiffHolder.of_contDiffOn
      convert hf
      sorry -- goal (k - 1) + 1 = k uses Nat subtraction... but k ≥ 2, so is fine mathematically
    rw [h]
    push_cast
    rw [add_zero]
    convert thm34 p (k-1) hp f K U hU hKU (α := 1) (by norm_num) this hrank
    sorry -- same sorry as above
  · have : k = 1 := sorry
    simp [h, this]
    -- now, this is theorem 3.3, but not quite (finrank F vs finrank F)
    -- Moreira writes "the proof of Thm 3.3 shows"...
    -- presumably, the same argument works, but would need to formalise the details
    sorry /-
    refine thm33' ?_ f (f' := fderiv ℝ f) ?_ ?_
    · -- if not, we're in the easy case
      sorry
    · intro x hx
      have foo : (1 : WithTop ℕ∞) ≤ k := (by norm_cast; exact this.symm.le)
      --have aux := hf.differentiableOn foo
      have aux := ((hf x (hKU hx)).differentiableWithinAt foo).hasFDerivWithinAt
      -- not quite right, but close
      convert aux.mono hKU
      sorry
    · sorry
      /- intro x hx
      calc finrank (LinearMap.range (fderiv ℝ f x))
        _ ≤ p := by apply hrank x hx
        _ < (finrank ℝ F) := by sorry -- hp plus casting -/ -/

end Moreira2001
