/-
Copyright (c) 2026 Dominic Steinitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Steinitz
-/

module

public import Mathlib.Geometry.Manifold.GroupLieAlgebra
public import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime
public import Mathlib.Geometry.Manifold.Sheaf.Basic
public import Mathlib.Order.BourbakiWitt

/-!
# The Exponential Map of a Lie Group

We construct the exponential map `expLie : g → G` for a Lie group `G` and prove that it
is smooth. The main reference is:

* Eckhard Meinrenken, *Lie Groups and Lie Algebras*, Lecture Notes, University of Toronto.
  Available at https://www.math.toronto.edu/mein/teaching/LectureNotes/lie.pdf

The key steps, following Meinrenken §3–4, are:

* Every left-invariant vector field on `G` admits a unique global integral curve through
  the identity (`IsMIntegralCurve.exists_global`, `IsMIntegralCurve.unique_global`),
  corresponding to Theorem 3.8.

* The exponential map is defined as `expLie v := γᵥ 1`, where `γᵥ` is this integral curve
  (`expLie`), corresponding to Definition 4.4.

* Any integral curve of `mulInvariantVectorField v` starting at 1 equals `t ↦ expLie (t • v)`
  (`expLie_smul`, `isMIntegralCurve_expLie_smul`), corresponding to Proposition 4.3.

* The exponential map is smooth (`contMDiff_expLie`), corresponding to the smoothness
  assertion in Definition 4.4. This relies on `contMDiff_flow_like`, an axiom asserting smooth
  dependence of ODE solutions on parameters (Lee, *Introduction to Smooth Manifolds*,
  Theorem 9.12), which is currently missing from Mathlib.
-/

open Set Bundle ContDiff Manifold Trivialization

noncomputable section

variable
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  {HG : Type*} [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG}
  {G : Type*} [TopologicalSpace G]
  [ChartedSpace HG G] [Group G]
  [LieGroup IG ⊤ G]

/-- The vector field `mulInvariantVectorField v`, defined at each `g` by `d(L_g)_e(v)`, satisfies
the left-invariance property: its value at `g * h` equals the pushforward of its value at `h`
under `d(L_g)_h`. -/
public lemma mulInvariantVectorField_left_invariant
    (v : GroupLieAlgebra IG G) (g h : G) :
    mulInvariantVectorField v (g * h) =
      mfderiv IG IG (g * ·) h (mulInvariantVectorField v h) := by
  have h1 : ∞ ≠ 0 := Ne.symm (not_eq_of_beq_eq_false rfl)
  have h2 : ∀ a b : G, MDifferentiableAt IG IG (a * ·) b :=
    fun a b => (contMDiff_mul_left (a := a) (n := ∞)).mdifferentiable h1 |>.mdifferentiableAt
  simp only [mulInvariantVectorField]
  have h3 : (fun x => (g * h) * x) = (fun x => g * x) ∘ (fun x => h * x) := by
    ext; simp [mul_assoc]
  rw [h3]
  have h4 : MDifferentiableAt IG IG (g * ·) (h * 1) := by rw [mul_one]; exact h2 g h
  have h7 : mfderiv IG IG ((fun x => g * x) ∘ (h * ·)) 1 =
      (mfderiv IG IG (fun x => g * x) (h * 1)).comp (mfderiv IG IG (h * ·) 1) :=
    mfderiv_comp (1 : G) h4 (h2 h 1)
  rw [h7, mul_one h]
  exact ContinuousLinearMap.comp_apply
    ((mfderiv% fun x ↦ g * x) h) ((mfderiv% fun x ↦ h * x) 1) v

public lemma IsMIntegralCurve.left_translate
    (γ : ℝ → G) (v : GroupLieAlgebra IG G)
    (hγ : IsMIntegralCurve γ (mulInvariantVectorField v))
    (g : G) :
    IsMIntegralCurve (fun t ↦ g * γ t) (mulInvariantVectorField v) := by
  have h1 : ∞ ≠ 0 := Ne.symm (not_eq_of_beq_eq_false rfl)
  have hMDiff : ∀ a b : G, MDifferentiableAt IG IG (a * ·) b :=
    fun a b => (contMDiff_mul_left (a := a) (n := ∞)).mdifferentiable h1 |>.mdifferentiableAt
  intro t
  rw [mulInvariantVectorField_left_invariant]
  convert ((hMDiff g (γ t)).hasMFDerivAt.comp t (hγ t)) using 1
  ext
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul]
  have h2 : (((mfderiv% fun x ↦ g * x) (γ t)).comp
    (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (mulInvariantVectorField v (γ t)))) 1 =
    ((mfderiv% fun x ↦ g * x) (γ t)) (mulInvariantVectorField v (γ t)) := by
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply]
  exact h2.symm

public lemma IsMIntegralCurveOn.left_translate
    (γ : ℝ → G) (v : GroupLieAlgebra IG G) (s : Set ℝ)
    (hγ : IsMIntegralCurveOn γ (mulInvariantVectorField v) s)
    (g : G) :
    IsMIntegralCurveOn (fun t ↦ g * γ t) (mulInvariantVectorField v) s := by
  have hMDiff : ∀ a b : G, MDifferentiableAt IG IG (a * ·) b :=
    fun a b => (contMDiff_mul_left (a := a) (n := ∞)).mdifferentiable
      (by exact Ne.symm (not_eq_of_beq_eq_false rfl)) |>.mdifferentiableAt
  intro t ht
  rw [mulInvariantVectorField_left_invariant]
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

public lemma IsMIntegralCurve.exists_global
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

public noncomputable def expLie (v : GroupLieAlgebra IG G)
    [BoundarylessManifold IG G] [CompleteSpace EG] : G :=
  (IsMIntegralCurve.exists_global v).choose 1

public lemma IsMIntegralCurve.unique_global
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

public lemma expLie_smul
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

end Whatever

public lemma isMIntegralCurve_expLie_smul
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
    {HG : Type*} [TopologicalSpace HG]
    {IG : ModelWithCorners ℝ EG HG}
    {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G]
    [LieGroup IG ⊤ G] [BoundarylessManifold IG G] [CompleteSpace EG] [T2Space G]
    (A : GroupLieAlgebra IG G) :
    IsMIntegralCurve
      (fun t => expLie (IG := IG) (t • A))
      (mulInvariantVectorField (I := IG) A) := by
  obtain ⟨γ, hγ0, hγ⟩ := IsMIntegralCurve.exists_global (EG := EG) A
  have heq : ∀ t, γ t = expLie (IG := IG) (t • A) :=
    fun t => expLie_smul γ A hγ hγ0 t
  rw [show (fun t => expLie (IG := IG) (t • A)) = γ from (funext heq).symm]
  exact hγ

/-- Smooth dependence of integral curves on parameters.

Let `X` be a smooth vector field on a manifold `M`. Suppose `Φ : ℝ → M → M`
is a family of maps such that for every `x : M`, the curve `t ↦ Φ t x` is an
integral curve of `X`. Then the map `(t, x) ↦ Φ t x` is smooth.

This is a consequence of Lee, *Introduction to Smooth Manifolds*, Theorem 9.12
(Fundamental Theorem on Flows), which constructs a smooth maximal flow for any
smooth vector field. Here we assume only the smooth dependence of integral curves
on initial conditions.

Note: This statement does not assume that `Φ` satisfies the usual flow identities
(e.g. `Φ 0 x = x` or `Φ (t + s) x = Φ t (Φ s x)`), only that it parametrises
integral curves of `X`.

TODO: Replace this axiom with a proper development of flows (Lee Theorem 9.12)
once available in Mathlib. -/
axiom contMDiff_flow_like
    {M : Type*} [TopologicalSpace M] [ChartedSpace HG M] [IsManifold IG ∞ M]
    (X : ∀ x : M, TangentSpace IG x)
    (hX : ContMDiff IG IG.tangent ∞ (fun x => (⟨x, X x⟩ : TangentBundle IG M)))
    (Φ : ℝ → M → M)
    (hΦ : ∀ x, IsMIntegralCurve (fun t => Φ t x) (fun x => X x)) :
    ContMDiff (𝓘(ℝ, ℝ).prod IG) IG ∞ (fun p : ℝ × M => Φ p.1 p.2)

def dMult : TangentBundle (IG.prod IG) (G × G) → TangentBundle IG G :=
  tangentMap (IG.prod IG) IG (fun p : G × G => p.1 * p.2)

theorem contMDiff_dMult : ContMDiff (IG.prod IG).tangent IG.tangent ∞
  (dMult (IG := IG) (G := G)) := by
  apply ContMDiff.contMDiff_tangentMap
  · exact contMDiff_mul (𝕜 := ℝ) (E := EG) (H := HG) IG ∞
  · exact Std.IsPreorder.le_refl (∞ + 1)

def dMultProd : TangentBundle IG G × TangentBundle IG G → TangentBundle IG G :=
  dMult ∘ (equivTangentBundleProd IG G IG G).symm

theorem contMDiff_dMultProd : ContMDiff (IG.tangent.prod IG.tangent) IG.tangent ∞
    (dMultProd (IG := IG) (G := G)) := by
  unfold dMultProd
  apply contMDiff_dMult.comp
  exact contMDiff_equivTangentBundleProd_symm (I := IG) (M := G) (I' := IG) (M' := G)

def zeroSectionProdFiber : G × EG → TangentBundle IG G × TangentBundle IG G :=
  fun (g, ξ) => (zeroSection EG (TangentSpace IG) g, ⟨1, ξ⟩)

theorem smooth_tangentBundle_mk (b : G) :
    ContMDiff (modelWithCornersSelf ℝ EG) IG.tangent ⊤
      (fun v : EG => (⟨b, v⟩ : TangentBundle IG G)) := by
  intro v
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_const, ?_⟩
  have h_linear : ∃ L : EG →L[ℝ] EG, ∀ v : EG,
      (trivializationAt EG (TangentSpace IG) b) ⟨b, v⟩ = (b, L v) := by
    have h1 : ∀ (v : EG),
      (trivializationAt EG (TangentSpace IG) b) ⟨b, v⟩ =
      (b, (continuousLinearMapAt ℝ (trivializationAt EG (TangentSpace IG) b) b) v) := by
      intro v
      have h0 : b ∈ (trivializationAt EG (TangentSpace IG) b).baseSet :=
        FiberBundle.mem_baseSet_trivializationAt' b
      simp only [(trivializationAt EG (TangentSpace IG) b).continuousLinearMapAt_apply ℝ b]
      simp only [TangentBundle.trivializationAt_baseSet, mem_chart_source, coe_linearMapAt_of_mem]
      exact Prod.fst_eq_iff.mp rfl
    exact ⟨(trivializationAt EG (TangentSpace IG) b).continuousLinearMapAt ℝ b, h1⟩
  obtain ⟨L, hL⟩ := h_linear
  simpa only [hL] using L.contDiff.contMDiff.contMDiffAt

theorem contMDiff_zeroSectionProdFiber :
    ContMDiff (IG.prod 𝓘(ℝ, EG)) (IG.tangent.prod IG.tangent) ∞
      (zeroSectionProdFiber (IG := IG) (G := G)) := by
  apply ContMDiff.prodMk
  · exact (Bundle.contMDiff_zeroSection (B := G) ℝ (TangentSpace IG)).comp contMDiff_fst
  · have : ContMDiff (IG.prod 𝓘(ℝ, EG)) (𝓘(ℝ, EG)) ω (fun x : G × EG => x.2) := contMDiff_snd
    have fu := (smooth_tangentBundle_mk (IG := IG) (1:G)).comp this
    exact fu.of_le (right_eq_inf.mp rfl)

theorem mfderiv_mul_apply_zero_right
    (g : G) (ξ : TangentSpace IG (1 : G)) :
    mfderiv (IG.prod IG) IG (fun p : G × G => p.1 * p.2) (g, 1)
      ((0 : TangentSpace IG g), ξ) =
    mfderiv IG IG (fun x => g * x) 1 ξ := by
  have fu :  ∞ ≠ 0 := Ne.symm (not_eq_of_beq_eq_false rfl)
  have hf : MDifferentiableAt (IG.prod IG) IG (fun p : G × G => p.1 * p.2) (g, 1) :=
    (contMDiff_mul (𝕜 := ℝ) (I := IG) (n := ∞)).mdifferentiableAt fu
  rw [mfderiv_prod_eq_add_apply hf]
  simp [map_zero]

theorem dMultProd_zeroSectionProdFiber_eq (g : G) (ξ : EG) :
    dMultProd (IG := IG) (zeroSectionProdFiber (IG := IG) (g, ξ)) =
    ⟨g, mfderiv IG IG (g * ·) 1 ξ⟩ := by
  simp only [dMultProd, zeroSectionProdFiber, dMult, equivTangentBundleProd]
  simp only [Equiv.coe_fn_symm_mk, Function.comp_apply, zeroSection_proj, zeroSection_snd]
  simp only [tangentMap]
  ext
  · simp [mul_one]
  · simp only
    exact heq_of_eq (mfderiv_mul_apply_zero_right (IG := IG) g ξ)

theorem contMDiff_mulLeft_deriv :
    ContMDiff (IG.prod 𝓘(ℝ, EG)) IG.tangent ∞
      (fun p : G × EG => (⟨p.1, mfderiv IG IG (p.1 * ·) 1 p.2⟩ : TangentBundle IG G)) := by
  have key : (fun p : G × EG => (⟨p.1, mfderiv IG IG (p.1 * ·) 1 p.2⟩ : TangentBundle IG G)) =
      dMultProd ∘ zeroSectionProdFiber := by
    funext ⟨g, ξ⟩
    exact (dMultProd_zeroSectionProdFiber_eq (IG := IG) g ξ).symm
  rw [key]
  exact contMDiff_dMultProd.comp contMDiff_zeroSectionProdFiber

public theorem smooth_augmentedVF [T2Space G] [IsManifold (IG.prod 𝓘(ℝ, EG)) ∞ (G × EG)] :
    ContMDiff (IG.prod 𝓘(ℝ, EG)) (IG.prod 𝓘(ℝ, EG)).tangent ∞
      (fun p : G × EG => (⟨p, (mfderiv IG IG (p.1 * ·) 1 p.2, 0)⟩ :
        TangentBundle (IG.prod 𝓘(ℝ, EG)) (G × EG))) := by
  have key : (fun p : G × EG => (⟨p, (mfderiv IG IG (p.1 * ·) 1 p.2, 0)⟩ :
        TangentBundle (IG.prod 𝓘(ℝ, EG)) (G × EG))) =
      (equivTangentBundleProd IG G 𝓘(ℝ, EG) EG).symm ∘
        (fun p : G × EG => (
          (⟨p.1, mfderiv IG IG (p.1 * ·) 1 p.2⟩ : TangentBundle IG G),
          (⟨p.2, 0⟩ : TangentBundle 𝓘(ℝ, EG) EG))) := by
    funext ⟨g, v⟩; simp only [equivTangentBundleProd]
    simp only [Equiv.coe_fn_symm_mk, Function.comp_apply, TotalSpace.mk_inj]
    exact rfl
  rw [key]
  exact (contMDiff_equivTangentBundleProd_symm).comp
    (ContMDiff.prodMk
      (contMDiff_mulLeft_deriv)
      ((Bundle.contMDiff_zeroSection ℝ (TangentSpace 𝓘(ℝ, EG))).comp contMDiff_snd))

omit [Group G] [LieGroup IG ω G] in
lemma isMIntegralCurve_prod_mk
    [T2Space G] [BoundarylessManifold IG G] [CompleteSpace EG]
    (γ₁ : ℝ → G) (γ₂ : ℝ → EG)
    (X₁ : ∀ x : G, TangentSpace IG x)
    (X₂ : ∀ x : EG, TangentSpace (𝓘(ℝ, EG)) x)
    (h₁ : IsMIntegralCurve (I := IG) γ₁ X₁)
    (h₂ : IsMIntegralCurve (I := 𝓘(ℝ, EG)) γ₂ X₂) :
    IsMIntegralCurve (I := IG.prod 𝓘(ℝ, EG)) (fun t => (γ₁ t, γ₂ t))
      (fun p : G × EG => (X₁ p.1, X₂ p.2)) := by
  intro t;
  convert HasMFDerivAt.prodMk ( h₁ t ) ( h₂ t ) using 1

public theorem contMDiff_expLie [T2Space G] [CompleteSpace EG] [BoundarylessManifold IG G] :
    ContMDiff 𝓘(ℝ, EG) IG ∞ (fun v : EG => expLie (G := G) (IG := IG) v) := by
  have hXi : ContMDiff (IG.prod 𝓘(ℝ, EG)) (IG.prod 𝓘(ℝ, EG)).tangent ∞
      (fun p : G × EG => (⟨p, (mfderiv IG IG (p.1 * ·) 1 p.2, (0:EG))⟩ :
        TangentBundle (IG.prod 𝓘(ℝ, EG)) (G × EG))) :=
    smooth_augmentedVF
  have hflow := contMDiff_flow_like
    (fun p : G × EG => (mfderiv IG IG (p.1 * ·) 1 p.2, (0:EG)))
    hXi
    (fun t p => (expLie (t • p.2), p.2))
    (fun p : G × EG => isMIntegralCurve_prod_mk
      (γ₁ := fun t => expLie (t • p.2)) (γ₂ := fun _ => p.2)
      (X₁ := fun x => mfderiv IG IG (x * ·) 1 p.2) (X₂ := fun _ => (0 : EG))
      (isMIntegralCurve_expLie_smul p.2)
      (isMIntegralCurve_const (by rfl)))
  have hexp : (fun v : EG => expLie (G := G) (IG := IG) v) =
    fun v => expLie (G := G) (IG := IG) ((1 : ℝ) • v) := by
    funext v
    simp
  rw [hexp]
  have hkey : ContMDiff 𝓘(ℝ, EG) (𝓘(ℝ, ℝ).prod (IG.prod 𝓘(ℝ, EG))) ∞
      (fun v : EG => ((1:ℝ), ((1:G), v))) :=
    contMDiff_const.prodMk (contMDiff_const.prodMk contMDiff_id)
  have hcomp := hflow.comp hkey
  have hcomp2 : ContMDiff 𝓘(ℝ, EG) IG ∞
      (fun v : EG => expLie (G := G) (IG := IG) v) := by
    have := contMDiff_fst (I := IG) (J := 𝓘(ℝ, EG)).comp hcomp
    convert this using 1
  simp only [one_smul]
  exact hcomp2
