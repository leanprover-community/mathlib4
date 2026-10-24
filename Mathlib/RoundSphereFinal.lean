import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.Topology.UniformSpace.Uniformizable

set_option linter.style.header false
section thing_one

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H : Type*} [TopologicalSpace H]
  {G : Type*} [TopologicalSpace G]
  (I : ModelWithCorners 𝕜 E H)
  (J : ModelWithCorners 𝕜 E'' G)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  (n : WithTop ℕ∞)
  (f : M → N)

open Manifold

lemma mfderiv_injective (x : M) (hn0 : n ≠ 0) (h : IsImmersionAt I J n f x) :
    Function.Injective (mfderiv I J f x) :=
  h.injective_mfderiv hn0

lemma mfderiv_injective' (x : M) (h : IsDiffImmersionAt I J f x) :
    Function.Injective (mfderiv I J f x) :=
  h.mfderiv_injective -- TODO -- which one of these is named incorrectly?

end thing_one

noncomputable section thing_two

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open Metric Module Function Manifold

open scoped ContDiff RealInnerProductSpace

def RoundSphere (n : ℕ) [Fact (finrank ℝ E = n + 1)] : Type _ := sphere (0 : E) 1
  deriving TopologicalSpace, ChartedSpace (EuclideanSpace ℝ (Fin n)),
  IsManifold (𝓡 n) ω

variable (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]

example (x : E) (hx : dist x 0 = 1) : RoundSphere E n := ⟨x, hx⟩

namespace RoundSphere

-- note to kmb : why does "deriving" not work here?
instance : IsManifold (𝓡 n) ω (RoundSphere E n) :=
  inferInstanceAs (IsManifold (𝓡 n) ω (sphere (0 : E) 1))

def inclusion : RoundSphere E n → E := fun x ↦ x.1

end RoundSphere

end thing_two

section thing_three

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open scoped Manifold -- 𝓘(ℝ, E)

open scoped ContDiff -- ω

open Bundle

example : IsManifold (𝓘(ℝ, E)) ω E := inferInstance

noncomputable example : RiemannianBundle (fun (x : E) ↦ TangentSpace 𝓘(ℝ, E) x) := inferInstance

example : IsRiemannianManifold 𝓘(ℝ, E) E := inferInstance

end thing_three

section thing_four

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  {H : Type*} [TopologicalSpace H]
  {G : Type*} [TopologicalSpace G]
  (I : ModelWithCorners ℝ E H)
  (J : ModelWithCorners ℝ E'' G)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  (f : M → N)
  (n : WithTop ℕ∞)

open Manifold Bundle

namespace Bundle

-- `T` must *not* be assumed normed here: a `TangentSpace` carries only a topological
-- vector space structure (no `NormedAddCommGroup`/`NormedSpace` instance).
noncomputable def ContinuousBilinearForm.comap
    {k : Type*} [NontriviallyNormedField k] {T E : Type*}
    [SeminormedAddCommGroup T] [NormedSpace k T]
    [SeminormedAddCommGroup E] [NormedSpace k E]
    (b : E →L[k] E →L[k] k) (e : T →L[k] E) :
    T →L[k] T →L[k] k :=
  ((ContinuousLinearMap.compL k T E k).flip e).comp (b.comp e)

/-

Have : continuous linear map T -> E (e)
First thing we want: a *continuous* function sending a continuous linear map E -> k to a
continuous linear map T -> k

-/
@[simp] lemma ContinuousBilinearForm.comap_apply
    {k : Type*} [NontriviallyNormedField k] {T E : Type*}
    [SeminormedAddCommGroup T] [NormedSpace k T]
    [SeminormedAddCommGroup E] [NormedSpace k E]
    (b : E →L[k] E →L[k] k) (e : T →L[k] E) (x y : T) :
    ContinuousBilinearForm.comap b e x y = b (e x) (e y) := rfl

-- `T` must *not* be assumed normed here: a `TangentSpace` carries only a topological
-- vector space structure (no `NormedAddCommGroup`/`NormedSpace` instance).
noncomputable def ContinuousSesquilinearForm.comap {k : Type*} [RCLike k] {T E : Type*}
    [AddCommGroup T] [Module k T] [TopologicalSpace T] [IsTopologicalAddGroup T]
    [ContinuousConstSMul k T]
    [AddCommGroup E] [Module k E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousConstSMul k E]
    (b : E →L⋆[k] E →L[k] k) (e : T →L[k] E) :
    T →L⋆[k] T →L[k] k :=
  (ContinuousLinearMap.precomp k e).comp (b.comp e)

@[simp] lemma ContinuousSesquilinearForm.comap_apply {k : Type*} [RCLike k] {T E : Type*}
    [AddCommGroup T] [Module k T] [TopologicalSpace T] [IsTopologicalAddGroup T]
    [ContinuousConstSMul k T] [AddCommGroup E] [Module k E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousConstSMul k E]
    (b : E →L⋆[k] E →L[k] k) (e : T →L[k] E) (x y : T) :
    ContinuousSesquilinearForm.comap b e x y = b (e x) (e y) := rfl

-- The pullback of a Riemannian metric along a map whose differential splits everywhere.
-- The hypothesis `∀ x, IsDiffImmersionAt I J f x` (mfderiv has a continuous left inverse) is
-- exactly what `pos` and `isVonNBounded` need; it follows from `IsImmersion`
-- (`hf.isDiffImmersionAt`with `n ≠ 0`),
-- and, when `J`'s model space is finite-dimensional, from injectivity of `mfderiv`
-- alone (`IsDiffImmersionAt.of_injective_of_finiteDimensional`).

noncomputable def RiemannianMetric.comap (hf : ∀ x, IsDiffImmersionAt I J f x)
    (g : RiemannianMetric (TangentSpace J : (y : N) → _)) :
    RiemannianMetric (TangentSpace I : (x : M) → _) where
      inner x := ContinuousSesquilinearForm.comap (g.inner (f x)) (mfderiv% f x)

      symm x v w := g.symm (f x) (mfderiv% f x v) (mfderiv% f x w)

      pos m v hv := by
        rw [ContinuousSesquilinearForm.comap_apply]
        exact g.pos (f m) (mfderiv% f m v) fun h ↦ hv ((hf m).mfderiv_injective
          (by rw [h, map_zero]))

      continuousAt m := by
        -- `fun v ↦ (comap g).inner m v v` is defeq to `(fun w ↦ g.inner (f m) w w) ∘ mfderiv f m`
        change ContinuousAt ((fun w ↦ g.inner (f m) w w) ∘ (mfderiv% f m)) 0
        exact (g.continuousAt (f m)).comp_of_eq
          (mfderiv% f m).continuous.continuousAt (mfderiv% f m).map_zero

      isVonNBounded m := by
        obtain ⟨S, hS⟩ : (mfderiv% f m).HasLeftInverse := hf m
        apply Bornology.IsVonNBounded.subset _ ((g.isVonNBounded (f m)).image S)
        intro v hv
        exact ⟨mfderiv% f m v, hv, hS v⟩

-- every pseudo metric space has a bornology. u can make a bornology using a distance function?

@[instance_reducible]
noncomputable def RiemannianBundle.comap (hf : ∀ x, IsDiffImmersionAt I J f x)
    (g : RiemannianBundle (fun (y : N) ↦ TangentSpace J y)) :
    RiemannianBundle (fun (x : M) ↦ TangentSpace I x) where
      g := RiemannianMetric.comap I J f hf g.1


/-- Reading the pullback of a bilinear form along a linear map in coordinates amounts to pulling
back the bilinear form read in coordinates along the linear map read in coordinates. -/
theorem inCoordinates_eq_comap {𝕜 B₁ B₂ F₁ F₂ : Type*} [NontriviallyNormedField 𝕜]
    {E₁ : B₁ → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
    [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
    {E₂ : B₂ → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
    [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
    [TopologicalSpace B₁] [TopologicalSpace B₂]
    [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
    {x₀ x : B₁} {y₀ y : B₂} {b : E₂ y →L[𝕜] E₂ y →L[𝕜] 𝕜} {e : E₁ x →L[𝕜] E₂ y}
    {b' : E₁ x →L[𝕜] E₁ x →L[𝕜] 𝕜} (hb' : ∀ v w, b' v w = b (e v) (e w))
    (hx : x ∈ (trivializationAt F₁ E₁ x₀).baseSet) (hy : y ∈ (trivializationAt F₂ E₂ y₀).baseSet) :
    ContinuousLinearMap.inCoordinates F₁ E₁ (F₁ →L[𝕜] 𝕜) (fun x ↦ E₁ x →L[𝕜] 𝕜) x₀ x x₀ x b' =
      ContinuousBilinearForm.comap
        (ContinuousLinearMap.inCoordinates F₂ E₂ (F₂ →L[𝕜] 𝕜) (fun y ↦ E₂ y →L[𝕜] 𝕜) y₀ y y₀ y b)
        (ContinuousLinearMap.inCoordinates F₁ E₁ F₂ E₂ x₀ x y₀ y e) := by
  ext v w
  rw [inCoordinates_apply_eq₂ hx hx (by simp)]
  simp only [ContinuousBilinearForm.comap_apply, hb']
  rw [inCoordinates_apply_eq₂ hy hy (by simp)]
  simp [ContinuousLinearMap.inCoordinates, Trivialization.symm_linearMapAt _ hy,
    Trivialization.symmL_apply (R := 𝕜) _ hx]

/-- Continuity of the pullback of a bilinear form, in the normed setting where it is used to
express the pullback metric in local coordinates. -/
lemma _root_.ContinuousAt.bilinComap {X : Type*} [TopologicalSpace X] {x₀ : X}
    {b : X → (E'' →L[ℝ] E'' →L[ℝ] ℝ)} {e : X → (E →L[ℝ] E'')}
    (hb : ContinuousAt b x₀) (he : ContinuousAt e x₀) :
    ContinuousAt (fun x ↦ ContinuousBilinearForm.comap (b x) (e x)) x₀ :=
  ContinuousAt.clm_comp
    ((ContinuousLinearMap.compL ℝ E E'' ℝ).flip.continuous.continuousAt.comp he)
    (hb.clm_comp he)

/-- If `G` is a continuous family of bilinear forms on the tangent spaces of `N` and `f : M → N`
is `C^n` with `n ≠ 0`, then the family of bilinear forms on the tangent spaces of `M` obtained by
pulling `G` back along `mfderiv f` is continuous. -/
lemma continuous_totalSpace_mk_comap_mfderiv [IsManifold I 1 M] [IsManifold J 1 N]
    (hf : ContMDiff I J n f) (hn : n ≠ 0)
    {G : (y : N) → TangentSpace J y →L[ℝ] TangentSpace J y →L[ℝ] ℝ}
    (hG : Continuous (fun (y : N) ↦ TotalSpace.mk' (E'' →L[ℝ] E'' →L[ℝ] ℝ) y (G y)))
    {G' : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hG' : ∀ x v w, G' x v w = G (f x) (mfderiv% f x v) (mfderiv% f x w)) :
    Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (G' x)) := by
  refine continuous_iff_continuousAt.2 fun x₀ ↦ (continuousAt_hom_bundle _ _).2
    ⟨continuousAt_id, (((continuousAt_hom_bundle _ _).1
      (hG.continuousAt.comp hf.continuous.continuousAt)).2.bilinComap
      (ContMDiffAt.mfderiv_const (I := I) (I' := J) (m := 0) (x₀ := x₀) hf.contMDiffAt
        (by simpa using ENat.one_le_iff_ne_zero_withTop.mpr hn)).continuousAt).congr ?_⟩
  filter_upwards [(trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' x₀),
    hf.continuous.continuousAt ((trivializationAt E'' (TangentSpace J) (f x₀)).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' (f x₀)))] with x hx1 hx2
  exact (inCoordinates_eq_comap (hG' x) hx1 hx2).symm

/-- If the Riemannian metric on `N` varies continuously and `f : M → N` is `C^n` with `n ≠ 0`
and has a differential with a continuous left inverse at every point, then the pullback metric
`RiemannianBundle.comap` on `M` varies continuously too. -/
theorem IsContinuousRiemannianBundle.comap [IsManifold I 1 M] [IsManifold J 1 N]
    (hf : ContMDiff I J n f) (hn : n ≠ 0) (hf' : ∀ x, IsDiffImmersionAt I J f x)
    [g : RiemannianBundle (fun (y : N) ↦ TangentSpace J y)]
    [hg : IsContinuousRiemannianBundle E'' (fun (y : N) ↦ TangentSpace J y)] :
    letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := RiemannianBundle.comap I J f hf' g
    IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) := by
  let : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := RiemannianBundle.comap I J f hf' g
  obtain ⟨G, G_cont, hG⟩ := hg.exists_continuous
  refine ⟨(RiemannianMetric.comap I J f hf' g.g).inner, ?_, fun x v w ↦ rfl⟩
  exact continuous_totalSpace_mk_comap_mfderiv I J f n hf hn G_cont
    (fun x v w ↦ hG (f x) (mfderiv% f x v) (mfderiv% f x w))

end Bundle

theorem IsRiemannianManifold.comap (f : M → N) (hf : ∀ x, IsDiffImmersionAt I J f x)
    (hf0 : ContMDiff I J n f) (hn : n ≠ 0)
    [IsManifold I 1 M] [IsManifold J 1 N] [RegularSpace M]
    [PseudoEMetricSpace N] [RiemannianBundle fun (y : N) => TangentSpace J y]
    [IsContinuousRiemannianBundle E'' fun (y : N) ↦ TangentSpace J y] :
    letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
      RiemannianBundle.comap I J f hf inferInstance
    haveI : IsContinuousRiemannianBundle E fun (x : M) ↦ TangentSpace I x :=
      IsContinuousRiemannianBundle.comap I J f n hf0 hn hf
    letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
    IsRiemannianManifold I M :=
  inferInstance


end thing_four

section thing_five

open Metric

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open Metric Module Function Manifold Bundle

open scoped ContDiff RealInnerProductSpace

variable (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]

-- The round sphere `𝕊ⁿ ⊆ E` inherits the induced Riemannian metric.  We do NOT need
-- `inclusion_isImmersion`: `E` is finite-dimensional, so the differential of the inclusion splits
-- as soon as it is injective, which is `mfderiv_coe_sphere_injective`.
noncomputable instance : RiemannianBundle (fun (x : RoundSphere E n) ↦ TangentSpace (𝓡 n) x) :=
  haveI : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  RiemannianBundle.comap (𝓡 n) 𝓘(ℝ, E) (RoundSphere.inclusion E n)
    (fun x ↦ .of_injective_of_finiteDimensional (injective_mvfderiv_subtypeVal_sphere x))
    inferInstance

section

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {m : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, NormedAddCommGroup (V x)]
  [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- A smooth Riemannian bundle is in particular a continuous Riemannian bundle. This cannot be an
instance, as `IB` and `m` do not appear in the conclusion. -/
lemma IsContMDiffRiemannianBundle.isContinuousRiemannianBundle
    (h : IsContMDiffRiemannianBundle IB m F V) : IsContinuousRiemannianBundle F V := by
  obtain ⟨g, g_smooth, hg⟩ := h.exists_contMDiff
  exact ⟨g, g_smooth.continuous, hg⟩

end

/-- The canonical Riemannian metric on an inner product space varies continuously. Mathlib only
registers the smooth version (`IsContMDiffRiemannianBundle`), from which typeclass inference
cannot recover this. -/
instance instIsContinuousRiemannianBundleTangentSpaceVectorSpace :
    IsContinuousRiemannianBundle E (fun (y : E) ↦ TangentSpace 𝓘(ℝ, E) y) :=
  IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (IB := 𝓘(ℝ, E)) (m := ω)
    inferInstance

/-- The induced Riemannian metric on the round sphere varies continuously: it is the pullback of
the continuous metric on `E` along the smooth immersion `RoundSphere.inclusion`. -/
noncomputable instance : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      fun (x : RoundSphere E n) ↦ TangentSpace (𝓡 n) x :=
  haveI : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have hf : ContMDiff (𝓡 n) 𝓘(ℝ, E) ω (RoundSphere.inclusion E n) :=
    contMDiff_coe_sphere (n := n)
  have hf' : ∀ x, IsDiffImmersionAt (𝓡 n) 𝓘(ℝ, E) (RoundSphere.inclusion E n) x :=
    fun x ↦ .of_injective_of_finiteDimensional (injective_mvfderiv_subtypeVal_sphere x)
  IsContinuousRiemannianBundle.comap (𝓡 n) 𝓘(ℝ, E) (RoundSphere.inclusion E n) ω hf
    (by simp) hf'

instance : RegularSpace E := inferInstance

instance : RegularSpace (RoundSphere E n) := by
  unfold RoundSphere
  apply instRegularSpaceSubtype

/-- The associated Riemannian distance on the round sphere. -/
noncomputable instance : PseudoEMetricSpace (RoundSphere E n) :=
  PseudoEMetricSpace.ofRiemannianMetric (𝓡 n) (RoundSphere E n)

example : IsRiemannianManifold (𝓡 n) (RoundSphere E n) := inferInstance

end thing_five
