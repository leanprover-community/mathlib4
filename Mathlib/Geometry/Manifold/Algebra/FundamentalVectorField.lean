import Mathlib

open Set Bundle ContDiff Manifold Trivialization

noncomputable section

variable
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  {HG : Type*} [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG}
  {G : Type*} [TopologicalSpace G]
  [ChartedSpace HG G] [Group G]
  [LieGroup IG ∞ G]

lemma IsMIntegralCurve.left_translate
    (γ : ℝ → G) (v : GroupLieAlgebra IG G)
    (hγ : IsMIntegralCurve γ (mulInvariantVectorField v))
    (g : G) :
    IsMIntegralCurve (fun t ↦ g * γ t) (mulInvariantVectorField v) := by
  intro t
  have h1 : ∞ ≠ 0 := Ne.symm (not_eq_of_beq_eq_false rfl)
  have hMDiff : ∀ a b : G, MDifferentiableAt IG IG (a * ·) b :=
  fun a b => (contMDiff_mul_left (a := a) (n := ∞)).mdifferentiable h1 |>.mdifferentiableAt
  have h6 : mulInvariantVectorField v (g * γ t) =
    mfderiv IG IG (g * ·) (γ t) (mulInvariantVectorField v (γ t)) := by
    simp only [mulInvariantVectorField]
    have h3 : (fun x => (g * γ t) * x) = (fun x => g * x) ∘ (fun x => γ t * x) := by
      ext; simp [mul_assoc]
    rw [h3]
    have h4 : MDifferentiableAt IG IG (g * ·) (γ t * 1) := by rw [mul_one]; exact (hMDiff g (γ t))
    have h5 : HMul.hMul (γ t) = fun x ↦ γ t * x := rfl
    rw [mfderiv_comp (1 : G) h4 (hMDiff (γ t) 1), mul_one (γ t), h5]
    exact ContinuousLinearMap.comp_apply
      ((mfderiv% fun x ↦ g * x) (γ t)) ((mfderiv% fun x ↦ γ t * x) 1) v
  rw [h6]
  convert ((hMDiff g (γ t)).hasMFDerivAt.comp t (hγ t)) using 1
  ext
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul]
  have h2 : (((mfderiv% fun x ↦ g * x) (γ t)).comp
    (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (mulInvariantVectorField v (γ t)))) 1 =
    ((mfderiv% fun x ↦ g * x) (γ t)) (mulInvariantVectorField v (γ t)) := by
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply]
  exact h2.symm

omit [Group G] [LieGroup IG ∞ G] in
lemma IsMIntegralCurve.time_shift
    (γ : ℝ → G) (v : (x : G) → TangentSpace IG x)
    (hγ : IsMIntegralCurve γ v)
    (s : ℝ) :
    IsMIntegralCurve (fun t ↦ γ (s + t)) v := by
  intro t
  have hshift : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t ↦ s + t) t
      (ContinuousLinearMap.id ℝ ℝ) := by
    have h := (hasDerivAt_id t).const_add s
    rw [hasMFDerivAt_iff_hasFDerivAt, hasFDerivAt_iff_hasDerivAt]
    simpa using h
  exact (hγ (s + t)).comp t hshift

omit [LieGroup IG ∞ G] in
lemma IsMIntegralCurve.comp_mul'
    (γ : ℝ → G) (v : GroupLieAlgebra IG G)
    (hγ : IsMIntegralCurve γ (mulInvariantVectorField v))
    (s : ℝ) :
    IsMIntegralCurve (fun t ↦ γ (s * t)) (mulInvariantVectorField (s • v)) := by
  intro t
  have hscale : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t ↦ s * t) t
      (s • ContinuousLinearMap.id ℝ ℝ) := by
    rw [hasMFDerivAt_iff_hasFDerivAt, hasFDerivAt_iff_hasDerivAt]
    simpa using (hasDerivAt_id t).const_mul s
  have hchain := (hγ (s * t)).comp t hscale
  rw [mulInvariantVectorField_smul]
  convert hchain using 1
  ext
  simp only [Pi.smul_apply, ContinuousLinearMap.smulRight_apply,
             ContinuousLinearMap.one_apply, one_smul]
  calc s • mulInvariantVectorField v (γ (s * t))
    = ((ContinuousLinearMap.smulRight 1 (mulInvariantVectorField v (γ (s * t)))).comp
        (s • ContinuousLinearMap.id ℝ ℝ)) 1 := by
        simp only [ContinuousLinearMap.comp_smulₛₗ, Real.ringHom_apply, ContinuousLinearMap.comp_id,
                  ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.smulRight_apply,
                  ContinuousLinearMap.one_apply,
                  one_smul]

lemma IsMIntegralCurveOn.left_translate
    (γ : ℝ → G) (v : GroupLieAlgebra IG G) (s : Set ℝ)
    (hγ : IsMIntegralCurveOn γ (mulInvariantVectorField v) s)
    (g : G) :
    IsMIntegralCurveOn (fun t ↦ g * γ t) (mulInvariantVectorField v) s := by
  intro t ht
  have hMDiff : ∀ a b : G, MDifferentiableAt IG IG (a * ·) b :=
    fun a b => (contMDiff_mul_left (a := a) (n := ∞)).mdifferentiable
      (by exact Ne.symm (not_eq_of_beq_eq_false rfl)) |>.mdifferentiableAt
  have h6 : mulInvariantVectorField v (g * γ t) =
      mfderiv IG IG (g * ·) (γ t) (mulInvariantVectorField v (γ t)) := by
    simp only [mulInvariantVectorField]
    have h3 : (fun x => (g * γ t) * x) = (fun x => g * x) ∘ (fun x => γ t * x) := by
      ext; simp [mul_assoc]
    rw [h3]
    have h4 : MDifferentiableAt IG IG (g * ·) (γ t * 1) := by rw [mul_one]; exact hMDiff g (γ t)
    have h5 : HMul.hMul (γ t) = fun x ↦ γ t * x := rfl
    rw [mfderiv_comp (1 : G) h4 (hMDiff (γ t) 1), mul_one (γ t), h5]
    exact ContinuousLinearMap.comp_apply _ _ v
  rw [h6]
  convert ((hMDiff g (γ t)).hasMFDerivAt.comp_hasMFDerivWithinAt t (hγ t ht)) using 1
  ext
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul]
  have h2 : (((mfderiv% fun x ↦ g * x) (γ t)).comp
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (mulInvariantVectorField v (γ t)))) 1 =
      ((mfderiv% fun x ↦ g * x) (γ t)) (mulInvariantVectorField v (γ t)) := by
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply]
  exact h2.symm

section Whatever

variable [T2Space G]

lemma IsMIntegralCurve.mul
    (γ : ℝ → G) (v : GroupLieAlgebra IG G)
    [BoundarylessManifold IG G]
    (hγ : IsMIntegralCurve γ (mulInvariantVectorField v))
    (hγ0 : γ 0 = 1)
    (s t : ℝ) :
    γ (s + t) = γ s * γ t := by
  have hshift : IsMIntegralCurve (fun t ↦ γ (s + t)) (mulInvariantVectorField v) :=
    (hγ.time_shift) s
  have htranslate : IsMIntegralCurve (fun t ↦ γ s * γ t) (mulInvariantVectorField v) :=
    (hγ.left_translate) (γ s)
  have : minSmoothness ℝ 3 ≤ ∞ := by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact ENat.LEInfty.out
  haveI : LieGroup IG (minSmoothness ℝ 3) G := LieGroup.of_le (n := ∞) this
  have hs : 1 ≤ (minSmoothness ℝ 2) := le_trans (by norm_num) le_minSmoothness
  have h0 : γ (s + 0) = γ s * γ 0 := by rw [hγ0, add_zero, left_eq_mul]
  have heq : (fun t ↦ γ (s + t)) = (fun t ↦ γ s * γ t) :=
    isMIntegralCurve_eq_of_contMDiff (t₀ := 0)
      (fun _ ↦ BoundarylessManifold.isInteriorPoint)
      ((contMDiff_mulInvariantVectorField v).of_le hs)
      hshift
      htranslate
      h0
  exact congr_fun heq t

lemma IsMIntegralCurve.exists_global
    (v : GroupLieAlgebra IG G)
    [BoundarylessManifold IG G]
    [CompleteSpace EG] :
    ∃ γ : ℝ → G, γ 0 = 1 ∧ IsMIntegralCurve γ (mulInvariantVectorField v) := by
  let X : G → TangentBundle IG G :=
    fun x => ⟨x, mulInvariantVectorField v x⟩
  have : minSmoothness ℝ 3 ≤ ∞ := by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact ENat.LEInfty.out
  haveI : LieGroup IG (minSmoothness ℝ 3) G := LieGroup.of_le (n := ∞) this
  have hv' : CMDiff 1 X :=
    (contMDiff_mulInvariantVectorField v).of_le (le_trans (by norm_num) le_minSmoothness)
  have hv : CMDiffAt 1 X 1 := hv'.contMDiffAt
  obtain ⟨γ₀, hγ₀_start, hγ₀_local⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless (t₀ := 0) hv
  rw [isMIntegralCurveAt_iff] at hγ₀_local
  obtain ⟨s, hs, hγ₀_on⟩ := hγ₀_local
  rw [Metric.mem_nhds_iff] at hs
  obtain ⟨ε, hε, hεs⟩ := hs
  have hunif : ∀ g : G, ∃ γ : ℝ → G, γ 0 = g ∧
      IsMIntegralCurveOn γ (mulInvariantVectorField v) (Ioo (-ε) ε) := by
    intro g
    refine ⟨fun t ↦ g * γ₀ t, by simp [hγ₀_start], ?_⟩
    have : Ioo (-ε) ε = Metric.ball 0 ε := by
      simp only [Metric.ball, dist_zero_right, Real.norm_eq_abs, abs_lt]
      exact Eq.symm (Ioo_def (-ε) ε)
    rw [this]
    apply (hγ₀_on.mono hεs).left_translate
  obtain ⟨γ, hγ_start, hγ⟩ :=
    exists_isMIntegralCurve_of_isMIntegralCurveOn hv' hε hunif (1 : G)
  exact ⟨γ, hγ_start, hγ⟩

noncomputable def expLie (v : GroupLieAlgebra IG G)
    [BoundarylessManifold IG G] [CompleteSpace EG] : G :=
  (IsMIntegralCurve.exists_global v).choose 1

lemma IsMIntegralCurve.unique_global
    (v : GroupLieAlgebra IG G)
    [BoundarylessManifold IG G]
    (γ γ' : ℝ → G)
    (hγ : IsMIntegralCurve γ (mulInvariantVectorField v))
    (hγ' : IsMIntegralCurve γ' (mulInvariantVectorField v))
    (hγ0 : γ 0 = 1)
    (hγ'0 : γ' 0 = 1) :
    γ = γ' := by
  have hv' : CMDiff 1 (fun x ↦ (⟨x, mulInvariantVectorField v x⟩ : TangentBundle IG G)) := by
    have : minSmoothness ℝ 3 ≤ ∞ := by
      simp only [minSmoothness_of_isRCLikeNormedField]; exact ENat.LEInfty.out
    haveI : LieGroup IG (minSmoothness ℝ 3) G := LieGroup.of_le (n := ∞) this
    exact (contMDiff_mulInvariantVectorField v).of_le (le_trans (by norm_num) le_minSmoothness)
  exact isMIntegralCurve_eq_of_contMDiff
    (fun _ ↦ BoundarylessManifold.isInteriorPoint) hv' hγ hγ' (by rw [hγ0, hγ'0])

lemma expLie_smul
    (γ : ℝ → G) (v : GroupLieAlgebra IG G)
    [BoundarylessManifold IG G]
    [CompleteSpace EG]
    (hγ : IsMIntegralCurve γ (mulInvariantVectorField v))
    (hγ0 : γ 0 = 1)
    (t : ℝ) :
    γ t = expLie (t • v) := by
  have hγ' := (IsMIntegralCurve.exists_global (t • v)).choose_spec
  have hγ'0 : (IsMIntegralCurve.exists_global (t • v)).choose 0 = 1 := hγ'.1
  have hγ'_curve : IsMIntegralCurve (IsMIntegralCurve.exists_global (t • v)).choose
      (mulInvariantVectorField (t • v)) := hγ'.2
  have hscaled : IsMIntegralCurve (fun s ↦ γ (s * t)) (mulInvariantVectorField (t • v)) := by
    have := hγ.comp_mul t
    rwa [← mulInvariantVectorField_smul] at this
  have : minSmoothness ℝ 3 ≤ ∞ := by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact ENat.LEInfty.out
  haveI : LieGroup IG (minSmoothness ℝ 3) G := LieGroup.of_le (n := ∞) this
  have hs : 1 ≤ (minSmoothness ℝ 2) := le_trans (by norm_num) le_minSmoothness
  have heq : (fun s ↦ γ (s * t)) = (IsMIntegralCurve.exists_global (t • v)).choose :=
    isMIntegralCurve_eq_of_contMDiff (t₀ := 0)
      (fun _ ↦ BoundarylessManifold.isInteriorPoint)
      ((contMDiff_mulInvariantVectorField (t • v)).of_le hs)
      hscaled
      hγ'_curve
      (by simp [hγ0, hγ'0])
  have := congr_fun heq 1
  simp only [one_mul, expLie] at this ⊢
  exact this

lemma expLie_zero
    [BoundarylessManifold IG G] [CompleteSpace EG] :
    expLie (0 : GroupLieAlgebra IG G) = 1 := by
  have hconst : IsMIntegralCurve (fun _ ↦ (1 : G))
               (mulInvariantVectorField (0 : GroupLieAlgebra IG G)) := by
    unfold mulInvariantVectorField
    apply isMIntegralCurve_const
    simp only [map_zero]
    exact AddMonCat.zero_of
  have hγ := (IsMIntegralCurve.exists_global (0 : GroupLieAlgebra IG G)).choose_spec
  have heq : (fun _ : ℝ ↦ (1 : G)) =
             (IsMIntegralCurve.exists_global (0 : GroupLieAlgebra IG G)).choose :=
    IsMIntegralCurve.unique_global 0 _ _ hconst hγ.2 rfl hγ.1
  have := congr_fun heq 1
  simp only [expLie] at this ⊢
  exact this.symm

open MulAction
open RightActions
open MulOpposite

/-- The fundamental vector field associated to a Lie algebra element `A : GroupLieAlgebra IG G`
on a manifold with a smooth right action of the Lie group `G`.

At a point `p` in the total space, the fundamental vector field is the tangent vector
at `t = 0` of the curve `t ↦ p <• expLie(t • A)`, i.e. the infinitesimal generator of the
right action of the one-parameter subgroup generated by `A` through `p`.

This is variously denoted `A*` (Kobayashi-Nomizu), `ξ_P(A)` or `i_p(A)` (Hamilton),
`A̲` (Tu), `X_A` or `X^A` in the literature.

## References
FIXME: Check these!!!
* [Tu, L. W., *Differential Geometry: Connections, Curvature, and Characteristic Classes*,
  §27.1]
* [Hamilton, M. J. D., *Mathematical Gauge Theory*, Definition 3.3 and §21.1] -/
noncomputable def fundamentalVectorField
    [BoundarylessManifold IG G] [CompleteSpace EG]
    (A : GroupLieAlgebra IG G)
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    {HM : Type*} [TopologicalSpace HM]
    {IM : ModelWithCorners ℝ EM HM}
    {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
    [IsManifold IM ∞ M]
    [MulAction (MulOpposite G) M]
    (p : M) : TangentSpace IM p := by
  have h : p <• (expLie (0 • A) : G) = p := by
    rw [zero_smul, expLie_zero]
    simp
  exact
    h ▸
      mfderiv 𝓘(ℝ, ℝ) IM
        (fun t ↦ p <• (expLie (t • A) : G))
        (0 : ℝ)
        (1 : TangentSpace 𝓘(ℝ, ℝ) (0 : ℝ))

end Whatever
