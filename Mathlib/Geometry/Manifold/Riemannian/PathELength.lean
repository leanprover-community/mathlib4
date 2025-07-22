/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! # Lengths of paths in manifolds

Consider a manifold in which the tangent spaces have an enormed structure. Then one defines
`pathELength γ a b` as the length of the path `γ : ℝ → M` between `a` and `b`, i.e., the integral
of the norm of its derivative on `Icc a b`.

We give several ways to write this quantity (as an integral over `Icc`, or `Ioo`, or the subtype
`Icc`, using either `mfderiv` or `mfderivWithin`).

We show that this notion is invariant under reparameterization by a monotone map, in
`pathELength_comp_of_monotoneOn`.

We define `riemannianEDist x y` as the infimum of the length of `C^1` paths between `x`
and `y`. We prove, in `exists_lt_locally_constant_of_riemannianEDist_lt`, that it is also the
infimum on such path that are moreover locally constant near their endpoints. Such paths can be
glued while retaining the `C^1` property. We deduce that `riemannianEDist` satisfies the triangle
inequality, in `riemannianEDist_triangle`.

Note that `riemannianEDist x y` could also be named `finslerEDist x y` as we do not require that
the metric comes from an inner product space. However, as all the current applications in mathlib
are to Riemannian spaces we stick with the simpler name. This could be changed when Finsler
manifolds are studied in mathlib.
-/

open Set MeasureTheory
open scoped Manifold ENNReal ContDiff Topology

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

namespace Manifold

variable [∀ (x : M), ENorm (TangentSpace I x)] {a b c a' b' : ℝ} {γ γ' : ℝ → M}

variable (I) in
/-- The length on `Icc a b` of a path into a manifold, where the path is defined on the whole real
line.

We use the whole real line to avoid subtype hell in API, but this is equivalent to
considering functions on the manifold with boundary `Icc a b`, see
`lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc`.

We use `mfderiv` instead of `mfderivWithin` in the definition as these coincide (apart from the two
endpoints which have zero measure) and `mfderiv` is easier to manipulate. However, we give
a lemma `pathELength_eq_integral_mfderivWithin_Icc` to rewrite with the `mfderivWithin` form. -/
irreducible_def pathELength (γ : ℝ → M) (a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Icc a b, ‖mfderiv 𝓘(ℝ) I γ t 1‖ₑ

lemma pathELength_eq_lintegral_mfderiv_Icc :
    pathELength I γ a b = ∫⁻ t in Icc a b, ‖mfderiv 𝓘(ℝ) I γ t 1‖ₑ := by simp [pathELength]

lemma pathELength_eq_lintegral_mfderiv_Ioo :
    pathELength I γ a b = ∫⁻ t in Ioo a b, ‖mfderiv 𝓘(ℝ) I γ t 1‖ₑ := by
  rw [pathELength_eq_lintegral_mfderiv_Icc, restrict_Ioo_eq_restrict_Icc]

lemma pathELength_eq_lintegral_mfderivWithin_Icc :
    pathELength I γ a b = ∫⁻ t in Icc a b, ‖mfderivWithin 𝓘(ℝ) I γ (Icc a b) t 1‖ₑ := by
  -- we use that the endpoints have measure 0 to rewrite on `Ioo a b`, where `mfderiv` and
  -- `mfderivWithin` coincide.
  rw [pathELength_eq_lintegral_mfderiv_Icc, ← restrict_Ioo_eq_restrict_Icc]
  apply setLIntegral_congr_fun measurableSet_Ioo (fun t ht ↦ ?_)
  rw [mfderivWithin_of_mem_nhds]
  exact Icc_mem_nhds ht.1 ht.2

@[simp] lemma pathELength_self : pathELength I γ a a = 0 := by
  simp [pathELength]

lemma pathELength_congr_Ioo (h : EqOn γ γ' (Ioo a b)) :
    pathELength I γ a b = pathELength I γ' a b := by
  simp only [pathELength_eq_lintegral_mfderiv_Ioo]
  apply setLIntegral_congr_fun measurableSet_Ioo (fun t ht ↦ ?_)
  have A : γ t = γ' t := h ht
  congr! 2
  apply Filter.EventuallyEq.mfderiv_eq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with a ha using h ha

lemma pathELength_congr (h : EqOn γ γ' (Icc a b)) : pathELength I γ a b = pathELength I γ' a b :=
  pathELength_congr_Ioo (fun _ hx ↦ h ⟨hx.1.le, hx.2.le⟩)

@[gcongr]
lemma pathELength_mono (h : a' ≤ a) (h' : b ≤ b') :
    pathELength I γ a b ≤ pathELength I γ a' b' := by
  simpa [pathELength_eq_lintegral_mfderiv_Icc] using lintegral_mono_set (Icc_subset_Icc h h')

lemma pathELength_add (h : a ≤ b) (h' : b ≤ c) :
    pathELength I γ a b + pathELength I γ b c = pathELength I γ a c := by
  symm
  have : Icc a c = Icc a b ∪ Ioc b c := (Icc_union_Ioc_eq_Icc h h').symm
  rw [pathELength, this, lintegral_union measurableSet_Ioc]; swap
  · exact disjoint_iff_forall_ne.mpr (fun a ha b hb ↦ (ha.2.trans_lt hb.1).ne)
  simp [restrict_Ioc_eq_restrict_Icc, pathELength]

attribute [local instance] Measure.Subtype.measureSpace

/-- Given a path `γ` defined on the manifold with boundary `[a, b]`, its length (as the integral of
the norm of its manifold derivative) coincides with `pathELength` of the lift of `γ` to the real
line, between `a` and `b`. -/
lemma lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc {a b : ℝ}
    [h : Fact (a < b)] {γ : Icc a b → M} :
    ∫⁻ t, ‖mfderiv (𝓡∂ 1) I γ t 1‖ₑ = pathELength I (γ ∘ (projIcc a b h.out.le)) a b := by
  rw [pathELength_eq_lintegral_mfderivWithin_Icc]
  simp_rw [← mfderivWithin_comp_projIcc_one]
  have : MeasurePreserving (Subtype.val : Icc a b → ℝ) volume
    (volume.restrict (Icc a b)) := measurePreserving_subtype_coe measurableSet_Icc
  rw [← MeasurePreserving.lintegral_comp_emb this
    (MeasurableEmbedding.subtype_coe measurableSet_Icc)]
  congr
  ext t
  have : t = projIcc a b h.out.le (t : ℝ) := by simp
  congr

open MeasureTheory

variable [∀ (x : M), ENormSMulClass ℝ (TangentSpace I x)]

/-- The length of a path in a manifold is invariant under a monotone reparametrization. -/
lemma pathELength_comp_of_monotoneOn {f : ℝ → ℝ} (h : a ≤ b) (hf : MonotoneOn f (Icc a b))
    (h'f : DifferentiableOn ℝ f (Icc a b)) (hγ : MDifferentiableOn 𝓘(ℝ) I γ (Icc (f a) (f b))) :
    pathELength I (γ ∘ f) a b = pathELength I γ (f a) (f b) := by
  rcases h.eq_or_lt with rfl | h
  · simp
  have f_im : f '' (Icc a b) = Icc (f a) (f b) := h'f.continuousOn.image_Icc_of_monotoneOn h.le hf
  simp only [pathELength_eq_lintegral_mfderivWithin_Icc, ← f_im]
  have B (t) (ht : t ∈ Icc a b) : HasDerivWithinAt f (derivWithin f (Icc a b) t) (Icc a b) t :=
    (h'f t ht).hasDerivWithinAt
  rw [lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn measurableSet_Icc B hf]
  apply setLIntegral_congr_fun measurableSet_Icc (fun t ht ↦ ?_)
  have : (mfderivWithin 𝓘(ℝ, ℝ) I (γ ∘ f) (Icc a b) t)
      = (mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc (f a) (f b)) (f t))
          ∘L mfderivWithin 𝓘(ℝ) 𝓘(ℝ) f (Icc a b) t := by
    rw [← f_im] at hγ ⊢
    apply mfderivWithin_comp
    · apply hγ _ (mem_image_of_mem _ ht)
    · rw [mdifferentiableWithinAt_iff_differentiableWithinAt]
      exact h'f _ ht
    · exact subset_preimage_image _ _
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc h _ ht
  rw [this]
  simp only [Function.comp_apply, ContinuousLinearMap.coe_comp']
  have : mfderivWithin 𝓘(ℝ) 𝓘(ℝ) f (Icc a b) t 1
      = derivWithin f (Icc a b) t • (1 : TangentSpace 𝓘(ℝ) (f t)) := by
    simp only [mfderivWithin_eq_fderivWithin, ← fderivWithin_derivWithin, smul_eq_mul, mul_one]
    rfl
  rw [this]
  have : 0 ≤ derivWithin f (Icc a b) t := hf.derivWithin_nonneg
  simp only [map_smul, enorm_smul, ← Real.enorm_of_nonneg this, f_im]

/-- The length of a path in a manifold is invariant under an antitone reparametrization. -/
lemma pathELength_comp_of_antitoneOn {f : ℝ → ℝ} (h : a ≤ b) (hf : AntitoneOn f (Icc a b))
    (h'f : DifferentiableOn ℝ f (Icc a b)) (hγ : MDifferentiableOn 𝓘(ℝ) I γ (Icc (f b) (f a))) :
    pathELength I (γ ∘ f) a b = pathELength I γ (f b) (f a) := by
  rcases h.eq_or_lt with rfl | h
  · simp
  have f_im : f '' (Icc a b) = Icc (f b) (f a) := h'f.continuousOn.image_Icc_of_antitoneOn h.le hf
  simp only [pathELength_eq_lintegral_mfderivWithin_Icc, ← f_im]
  have B (t) (ht : t ∈ Icc a b) : HasDerivWithinAt f (derivWithin f (Icc a b) t) (Icc a b) t :=
    (h'f t ht).hasDerivWithinAt
  rw [lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn measurableSet_Icc B hf]
  apply setLIntegral_congr_fun measurableSet_Icc (fun t ht ↦ ?_)
  have : (mfderivWithin 𝓘(ℝ, ℝ) I (γ ∘ f) (Icc a b) t)
      = (mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc (f b) (f a)) (f t))
          ∘L mfderivWithin 𝓘(ℝ) 𝓘(ℝ) f (Icc a b) t := by
    rw [← f_im] at hγ ⊢
    apply mfderivWithin_comp
    · apply hγ _ (mem_image_of_mem _ ht)
    · rw [mdifferentiableWithinAt_iff_differentiableWithinAt]
      exact h'f _ ht
    · exact subset_preimage_image _ _
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc h _ ht
  rw [this]
  simp only [Function.comp_apply, ContinuousLinearMap.coe_comp']
  have : mfderivWithin 𝓘(ℝ) 𝓘(ℝ) f (Icc a b) t 1
      = derivWithin f (Icc a b) t • (1 : TangentSpace 𝓘(ℝ) (f t)) := by
    simp only [mfderivWithin_eq_fderivWithin, ← fderivWithin_derivWithin, smul_eq_mul, mul_one]
    rfl
  rw [this]
  have : 0 ≤ -derivWithin f (Icc a b) t := by simp [hf.derivWithin_nonpos]
  simp only [map_smul, enorm_smul, f_im, ← Real.enorm_of_nonneg this, enorm_neg]

section

variable {x y z : M} {r : ℝ≥0∞} {a b : ℝ}

variable (I) in
/-- The Riemannian extended distance between two points, in a manifold where the tangent spaces
have an extended norm, defined as the infimum of the lengths of `C^1` paths between the points. -/
noncomputable irreducible_def riemannianEDist (x y : M) : ℝ≥0∞ :=
  ⨅ (γ : Path x y) (_ : ContMDiff (𝓡∂ 1) I 1 γ), ∫⁻ x, ‖mfderiv (𝓡∂ 1) I γ x 1‖ₑ

/-- The Riemannian edistance is bounded above by the length of any `C^1` path from `x` to `y`.
Here, we express this using a path defined on the whole real line, considered on
some interval `[a, b]`. -/
lemma riemannianEDist_le_pathELength {γ : ℝ → M} (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ (Icc a b))
    (ha : γ a = x) (hb : γ b = y) (hab : a ≤ b) :
    riemannianEDist I x y ≤ pathELength I γ a b := by
  let η : ℝ →ᴬ[ℝ] ℝ := ContinuousAffineMap.lineMap a b
  have hη : ContMDiffOn 𝓘(ℝ) I 1 (γ ∘ η) (Icc 0 1) := by
    apply hγ.comp
    · rw [contMDiffOn_iff_contDiffOn]
      exact η.contDiff.contDiffOn
    · rw [← image_subset_iff, ContinuousAffineMap.coe_lineMap_eq, ← segment_eq_image_lineMap]
      simp [hab]
  let f : unitInterval → M := fun t ↦ (γ ∘ η) t
  have hf : ContMDiff (𝓡∂ 1) I 1 f := by
    rw [← contMDiffOn_comp_projIcc_iff]
    apply hη.congr (fun t ht ↦ ?_)
    simp only [Function.comp_apply, f, projIcc_of_mem, ht]
  let g : Path x y := by
    refine ⟨⟨f, hf.continuous⟩, ?_, ?_⟩ <;>
    simp [f, η, ContinuousAffineMap.coe_lineMap_eq, ha, hb]
  have A : riemannianEDist I x y ≤ ∫⁻ x, ‖mfderiv (𝓡∂ 1) I g x 1‖ₑ := by
    rw [riemannianEDist]; exact biInf_le _ hf
  apply A.trans_eq
  rw [lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc]
  have E : pathELength I (g ∘ projIcc 0 1 zero_le_one) 0 1 = pathELength I (γ ∘ η) 0 1 := by
    apply pathELength_congr (fun t ht ↦ ?_)
    simp only [Function.comp_apply, ht, projIcc_of_mem]
    rfl
  rw [E, pathELength_comp_of_monotoneOn zero_le_one _ η.differentiableOn]
  · simp [η, ContinuousAffineMap.coe_lineMap_eq]
  · simpa [η, ContinuousAffineMap.coe_lineMap_eq] using hγ.mdifferentiableOn le_rfl
  · apply (AffineMap.lineMap_mono hab).monotoneOn

omit [∀ (x : M), ENormSMulClass ℝ (TangentSpace I x)] in
/-- If some `r` is strictly larger than the Riemannian edistance between two points, there exists
a path between these two points of length `< r`. Here, we get such a path on `[0, 1]`.
For a more precise version giving locally constant paths around the endpoints, see
`exists_lt_locally_constant_of_riemannianEDist_lt` -/
lemma exists_lt_of_riemannianEDist_lt (hr : riemannianEDist I x y < r) :
    ∃ γ : ℝ → M, γ 0 = x ∧ γ 1 = y ∧ ContMDiffOn 𝓘(ℝ) I 1 γ (Icc 0 1) ∧
    pathELength I γ 0 1 < r := by
  simp only [riemannianEDist, iInf_lt_iff, exists_prop] at hr
  rcases hr with ⟨γ, γ_smooth, hγ⟩
  refine ⟨γ ∘ (projIcc 0 1 zero_le_one), by simp, by simp,
    contMDiffOn_comp_projIcc_iff.2 γ_smooth, ?_⟩
  rwa [← lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc]

/-- If some `r` is strictly larger than the Riemannian edistance between two points, there exists
a path between these two points of length `< r`. Here, we get such a path on an arbitrary interval
`[a, b]` with `a < b`, and moreover we ensure that the path is locally constant around `a` and `b`,
which is convenient for gluing purposes. -/
lemma exists_lt_locally_constant_of_riemannianEDist_lt
    (hr : riemannianEDist I x y < r) (hab : a < b) :
    ∃ γ : ℝ → M, γ a = x ∧ γ b = y ∧ ContMDiff 𝓘(ℝ) I 1 γ ∧
    pathELength I γ a b < r ∧ γ =ᶠ[𝓝 a] (fun _ ↦ x) ∧ γ =ᶠ[𝓝 b] (fun _ ↦ y) := by
  /- We start from a path from `x` to `y` defined on `[0, 1]` with length `< r`. Then, we
  reparameterize it using a smooth monotone map `η` from `[a, b]` to `[0, 1]` which is moreover
  locally constant around `a` and `b`.
  Such a map is easy to build with `Real.smoothTransition`.

  Note that this is a very standard construction in differential topology.
  TODO: refactor once we have more differential topology in Mathlib and this gets duplicated. -/
  rcases exists_lt_of_riemannianEDist_lt hr with ⟨γ, hγx, hγy, γ_smooth, hγ⟩
  rcases exists_between hab with ⟨a', haa', ha'b⟩
  rcases exists_between ha'b with ⟨b', ha'b', hb'b⟩
  let η (t : ℝ) : ℝ := Real.smoothTransition ((b' - a') ⁻¹ * (t - a'))
  have A (t) (ht : t < a') : η t = 0 := by
    simp only [η, Real.smoothTransition.zero_iff_nonpos]
    apply mul_nonpos_of_nonneg_of_nonpos
    · simpa using ha'b'.le
    · linarith
  have A' (t) (ht : t < a') : (γ ∘ η) t = x := by simp [A t ht, hγx]
  have B (t) (ht : b' < t) : η t = 1 := by
    simp only [η, Real.smoothTransition.eq_one_iff_one_le, inv_mul_eq_div]
    rw [one_le_div₀] <;> linarith
  have B' (t) (ht : b' < t) : (γ ∘ η) t = y := by simp [B t ht, hγy]
  refine ⟨γ ∘ η, A' _ haa', B' _ hb'b, ?_, ?_, ?_, ?_⟩
  · rw [← contMDiffOn_univ]
    apply γ_smooth.comp
    · rw [contMDiffOn_univ, contMDiff_iff_contDiff]
      fun_prop
    · intro t ht
      exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · convert hγ using 1
    rw [← A a haa', ← B b hb'b]
    apply pathELength_comp_of_monotoneOn hab.le
    · apply Monotone.monotoneOn
      apply Real.smoothTransition.monotone.comp
      intro t u htu
      dsimp only
      gcongr
      simpa only [inv_nonneg, sub_nonneg] using ha'b'.le
    · simp only [η]
      apply (ContDiff.contDiffOn _).differentiableOn le_rfl
      fun_prop
    · rw [A a haa', B b hb'b]
      apply γ_smooth.mdifferentiableOn le_rfl
  · filter_upwards [Iio_mem_nhds haa'] with t ht using A' t ht
  · filter_upwards [Ioi_mem_nhds hb'b] with t ht using B' t ht

lemma riemannianEDist_self : riemannianEDist I x x = 0 := by
  apply le_antisymm _ bot_le
  exact (riemannianEDist_le_pathELength (γ := fun (t : ℝ) ↦ x) (a := 0) (b := 0)
    contMDiffOn_const rfl rfl le_rfl).trans_eq (by simp)

lemma riemannianEDist_comm : riemannianEDist I x y = riemannianEDist I y x := by
  suffices H : ∀ x y, riemannianEDist I y x ≤ riemannianEDist I x y from le_antisymm (H y x) (H x y)
  intro x y
  apply le_of_forall_gt (fun r hr ↦ ?_)
  rcases exists_lt_locally_constant_of_riemannianEDist_lt hr zero_lt_one
    with ⟨γ, γ0, γ1, γ_smooth, hγ, -⟩
  let η : ℝ → ℝ := fun t ↦ - t
  have h_smooth : ContMDiff 𝓘(ℝ) I 1 (γ ∘ η) := by
    apply γ_smooth.comp ?_
    simp only [contMDiff_iff_contDiff]
    fun_prop
  have : riemannianEDist I y x ≤ pathELength I (γ ∘ η) (η 1) (η 0) := by
    apply riemannianEDist_le_pathELength h_smooth.contMDiffOn <;> simp [η, γ0, γ1]
  rw [← pathELength_comp_of_antitoneOn zero_le_one] at this; rotate_left
  · exact monotone_id.neg.antitoneOn _
  · exact differentiableOn_neg _
  · exact h_smooth.contMDiffOn.mdifferentiableOn le_rfl
  apply this.trans_lt
  convert hγ
  ext t
  simp [η]

lemma riemannianEDist_triangle :
    riemannianEDist I x z ≤ riemannianEDist I x y + riemannianEDist I y z := by
  apply le_of_forall_gt (fun r hr ↦ ?_)
  rcases ENNReal.exists_add_lt_of_add_lt hr with ⟨u, hu, v, hv, huv⟩
  rcases exists_lt_locally_constant_of_riemannianEDist_lt hu zero_lt_one with
    ⟨γ₁, hγ₁0, hγ₁1, hγ₁_smooth, hγ₁, -, hγ₁_const⟩
  rcases exists_lt_locally_constant_of_riemannianEDist_lt hv one_lt_two with
    ⟨γ₂, hγ₂1, hγ₂2, hγ₂_smooth, hγ₂, hγ₂_const, -⟩
  let γ := piecewise (Iic 1) γ₁ γ₂
  have : riemannianEDist I x z ≤ pathELength I γ 0 2 := by
    apply riemannianEDist_le_pathELength
    · apply ContMDiff.contMDiffOn
      exact ContMDiff.piecewise_Iic hγ₁_smooth hγ₂_smooth (hγ₁_const.trans hγ₂_const.symm)
    · simp [γ, hγ₁0]
    · simp [γ, hγ₂2]
    · exact zero_le_two
  apply this.trans_lt (lt_trans ?_ huv)
  rw [← pathELength_add zero_le_one one_le_two]
  gcongr
  · convert hγ₁ using 1
    apply pathELength_congr
    intro t ht
    simp [γ, ht.2]
  · convert hγ₂ using 1
    apply pathELength_congr_Ioo
    intro t ht
    simp [γ, ht.1]

end

end Manifold
