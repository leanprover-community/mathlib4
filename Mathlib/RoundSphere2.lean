import Mathlib

noncomputable section

open Metric Module Function Manifold

open scoped ContDiff RealInnerProductSpace

/-!
### The round sphere as a Riemannian manifold

This is a variant of `RoundSphere.lean` which avoids developing the `Sphere.polarChart` API.

The pullback constructions below (`ContinuousRiemannianMetric.comap` and friends) never use the
chart normal form encoded in `IsImmersion`: all they need of `f : M → N` is that it is `C^n` and
that its differential has a continuous left inverse at each point, i.e. `IsDiffImmersionAt`.
Weakening the hypothesis accordingly means the sphere's inclusion can be fed in directly using
`contMDiff_coe_sphere` and `injective_mvfderiv_subtypeVal_sphere` from mathlib, via
`IsDiffImmersionAt.of_injective_of_finiteDimensional`.

Note this is genuinely weaker than `IsImmersion`, which is defined by the local normal form in
charts: mathlib does not yet know that an injective differential between finite-dimensional
manifolds implies the normal form (that needs the inverse function theorem, and is a TODO in
`Mathlib/Geometry/Manifold/Immersion.lean`). So the `polarChart` development is still the way to
prove `IsImmersion (𝓡 n) 𝓘(ℝ, E) ω ((↑) : sphere (0 : E) 1 → E)` itself -- it is just not needed
for the Riemannian metric.
-/

section thing_two

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def RoundSphere (n : ℕ) [Fact (finrank ℝ E = n + 1)] : Type _ := sphere (0 : E) 1
  deriving TopologicalSpace, ChartedSpace (EuclideanSpace ℝ (Fin n)),
  IsManifold (𝓡 n) ω

variable (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]

example (x : E) (hx : dist x 0 = 1) : RoundSphere E n := ⟨x, hx⟩

namespace RoundSphere

instance : Neg (RoundSphere E n) where
  neg x := ⟨-x.1, by
    obtain ⟨v, hv⟩ := x
    simpa using hv⟩

instance : IsManifold (𝓡 n) ω (RoundSphere E n) :=
  inferInstanceAs (IsManifold (𝓡 n) ω (sphere (0 : E) 1))

instance : RegularSpace (RoundSphere E n) :=
  inferInstanceAs (RegularSpace (sphere (0 : E) 1))

def inclusion : RoundSphere E n → E := fun x ↦ x.1

theorem inclusion_contMDiff : ContMDiff (𝓡 n) 𝓘(ℝ, E) ω (inclusion E n) :=
  contMDiff_coe_sphere

theorem inclusion_isDiffImmersionAt (x : RoundSphere E n) :
    IsDiffImmersionAt (𝓡 n) 𝓘(ℝ, E) (inclusion E n) x :=
  have : FiniteDimensional ℝ E := FiniteDimensional.of_fact_finrank_eq_succ n
  IsDiffImmersionAt.of_injective_of_finiteDimensional
    (injective_mvfderiv_subtypeVal_sphere x)

end RoundSphere

end thing_two

section thing_three

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open Bundle

example : IsRiemannianManifold 𝓘(ℝ, E) E := inferInstance

end thing_three

section thing_four

open Bundle Bornology

namespace Bundle

/-- Pull back a continuous bilinear form along a continuous linear map.

`T` must *not* be assumed normed here: a tangent space carries only a topological vector space
structure (no `NormedAddCommGroup`/`NormedSpace` instance) unless a Riemannian structure is
already present. -/
def ContinuousBilinearForm.comap {T V : Type*}
    [AddCommGroup T] [Module ℝ T] [TopologicalSpace T] [IsTopologicalAddGroup T]
    [ContinuousConstSMul ℝ T]
    [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousConstSMul ℝ V]
    (b : V →L[ℝ] V →L[ℝ] ℝ) (e : T →L[ℝ] V) : T →L[ℝ] T →L[ℝ] ℝ :=
  (ContinuousLinearMap.precomp ℝ e).comp (b.comp e)

@[simp] lemma ContinuousBilinearForm.comap_apply {T V : Type*}
    [AddCommGroup T] [Module ℝ T] [TopologicalSpace T] [IsTopologicalAddGroup T]
    [ContinuousConstSMul ℝ T]
    [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousConstSMul ℝ V]
    (b : V →L[ℝ] V →L[ℝ] ℝ) (e : T →L[ℝ] V) (x y : T) :
    ContinuousBilinearForm.comap b e x y = b (e x) (e y) := rfl

end Bundle

section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  {H : Type*} [TopologicalSpace H]
  {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H}
  {J : ModelWithCorners ℝ E'' G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
  {f : M → N}
  {n : ℕ∞ω}

/-- Continuity of the pullback of a bilinear form, in the normed setting where it is used to
express the pullback metric in local coordinates. -/
lemma ContinuousAt.bilinComap {X : Type*} [TopologicalSpace X] {x₀ : X}
    {b : X → (E'' →L[ℝ] E'' →L[ℝ] ℝ)} {e : X → (E →L[ℝ] E'')}
    (hb : ContinuousAt b x₀) (he : ContinuousAt e x₀) :
    ContinuousAt (fun x ↦ Bundle.ContinuousBilinearForm.comap (b x) (e x)) x₀ := by
  have key : (fun x ↦ Bundle.ContinuousBilinearForm.comap (b x) (e x))
      = fun x ↦ ((ContinuousLinearMap.compL ℝ E E'' ℝ).flip (e x)).comp ((b x).comp (e x)) := by
    ext x v w
    rfl
  rw [key]
  exact ContinuousAt.clm_comp
    (((ContinuousLinearMap.compL ℝ E E'' ℝ).flip).continuous.continuousAt.comp he)
    (hb.clm_comp he)

namespace Bundle

/-- Pull back a continuous Riemannian metric along a `C^n` map whose differential has a
continuous left inverse at every point.

This is weaker than asking for an `IsImmersion`, and is all that the construction needs. -/
def ContinuousRiemannianMetric.comap (hf : ContMDiff I J n f)
    (hf' : ∀ x, IsDiffImmersionAt I J f x) (hn : n ≠ 0)
    (g : ContinuousRiemannianMetric E'' (fun (y : N) ↦ TangentSpace J y)) :
    ContinuousRiemannianMetric E (fun (x : M) ↦ TangentSpace I x) where
  inner x := ContinuousBilinearForm.comap (g.inner (f x)) (mfderiv% f x)
  symm x v w := g.symm (f x) _ _
  pos x v hv := g.pos (f x) _ fun h ↦
    hv ((hf' x).mfderiv_injective (h.trans (map_zero _).symm))
  isVonNBounded x := by
    obtain ⟨L, hL⟩ := hf' x
    refine IsVonNBounded.subset ?_ ((g.isVonNBounded (f x)).image L)
    rintro v hv
    exact ⟨(mfderiv% f x) v, hv, hL v⟩
  continuous := by
    rw [continuous_iff_continuousAt]
    intro x₀
    rw [continuousAt_hom_bundle]
    refine ⟨continuousAt_id, ?_⟩
    -- the derivative of `f`, read in tangent coordinates around `x₀` and `f x₀`
    set a : M → (E →L[ℝ] E'') :=
      inTangentCoordinates I J id f (fun x ↦ mfderiv% f x) x₀ with ha
    -- the metric on `N`, read in coordinates around `f x₀`
    set Γ : M → (E'' →L[ℝ] E'' →L[ℝ] ℝ) := fun x ↦
      ContinuousLinearMap.inCoordinates E'' (TangentSpace J) (E'' →L[ℝ] ℝ)
        (fun y ↦ TangentSpace J y →L[ℝ] ℝ) (f x₀) (f x) (f x₀) (f x) (g.inner (f x)) with hΓ
    have hfc : ContinuousAt f x₀ := (hf' x₀).continuousAt
    have hΓc : ContinuousAt Γ x₀ := by
      have h : ContinuousAt (fun x ↦ TotalSpace.mk' (E'' →L[ℝ] E'' →L[ℝ] ℝ)
          (E := fun y : N ↦ (TangentSpace J y →L[ℝ] TangentSpace J y →L[ℝ] ℝ))
          (f x) (g.inner (f x))) x₀ :=
        g.continuous.continuousAt.comp hfc
      rw [continuousAt_hom_bundle] at h
      exact h.2
    have h1n : (0 : ℕ∞ω) + 1 ≤ n := by
      simpa using ENat.one_le_iff_ne_zero_withTop.mpr hn
    have hac : ContinuousAt a x₀ :=
      (ContMDiffAt.mfderiv_const (I := I) (I' := J) (m := 0) hf.contMDiffAt
        h1n).continuousAt
    have key : (fun x ↦ ContinuousBilinearForm.comap (Γ x) (a x)) =ᶠ[nhds x₀]
        fun x ↦ ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
          (fun x ↦ TangentSpace I x →L[ℝ] ℝ) x₀ x x₀ x
          (ContinuousBilinearForm.comap (g.inner (f x)) (mfderiv% f x)) := by
      have hA : ∀ᶠ x in nhds x₀, x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
        (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
          (FiberBundle.mem_baseSet_trivializationAt' x₀)
      have hB : ∀ᶠ x in nhds x₀, f x ∈ (trivializationAt E'' (TangentSpace J) (f x₀)).baseSet :=
        hfc ((trivializationAt E'' (TangentSpace J) (f x₀)).open_baseSet.mem_nhds
          (FiberBundle.mem_baseSet_trivializationAt' (f x₀)))
      filter_upwards [hA, hB] with x hx1 hx2
      -- the derivative, read in coordinates, is the derivative conjugated by the trivialisations
      have hstep : ∀ u : E, (trivializationAt E'' (TangentSpace J) (f x₀)).symm (f x) (a x u)
          = (mfderiv% f x) ((trivializationAt E (TangentSpace I) x₀).symm x u) := by
        intro u
        rw [ha]
        simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
          ContinuousLinearMap.comp_apply, id_eq]
        rw [← Trivialization.symmL_apply (R := ℝ) _ hx2,
          Trivialization.symmL_continuousLinearMapAt _ hx2,
          Trivialization.symmL_apply (R := ℝ) _ hx1]
      ext v w
      rw [inCoordinates_apply_eq₂ hx1 hx1 (by simp)]
      simp only [ContinuousBilinearForm.comap_apply, hΓ]
      rw [inCoordinates_apply_eq₂ hx2 hx2 (by simp), hstep, hstep]
      simp
    exact (hΓc.bilinComap hac).congr key

/-- The Riemannian bundle structure on `M` obtained by pulling back a continuous Riemannian
metric on `N` along a `C^n` map `f : M → N` which is an immersion in the sense of differentials.

Because this is built from a `ContinuousRiemannianMetric`, it automatically registers an
`IsContinuousRiemannianBundle` instance as well. -/
@[instance_reducible]
def RiemannianBundle.comap (hf : ContMDiff I J n f)
    (hf' : ∀ x, IsDiffImmersionAt I J f x) (hn : n ≠ 0)
    (g : ContinuousRiemannianMetric E'' (fun (y : N) ↦ TangentSpace J y)) :
    RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
  ⟨(ContinuousRiemannianMetric.comap hf hf' hn g).toRiemannianMetric⟩

end Bundle

/-- Pulling back a Riemannian metric along a map which is an immersion in the sense of
differentials, and equipping `M` with the associated Riemannian distance, makes `M` a Riemannian
manifold.

Note that this is true by definition: `IsRiemannianManifold` asserts the compatibility of a
*pre-existing* extended distance with the metric, and here the distance is defined to be the
Riemannian one. The immersion hypothesis is used to build the metric, not the compatibility. -/
theorem IsRiemannianManifold.comap [RegularSpace M] (hf : ContMDiff I J n f)
    (hf' : ∀ x, IsDiffImmersionAt I J f x) (hn : n ≠ 0)
    (g : ContinuousRiemannianMetric E'' (fun (y : N) ↦ TangentSpace J y)) :
    letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := RiemannianBundle.comap hf hf' hn g
    letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
    IsRiemannianManifold I M :=
  inferInstance

end

end thing_four

section thing_five

open Bundle

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]

/-- The round sphere, with the metric pulled back from the ambient inner product space. -/
noncomputable instance :
    RiemannianBundle (fun (x : RoundSphere E n) ↦ TangentSpace (𝓡 n) x) :=
  RiemannianBundle.comap (RoundSphere.inclusion_contMDiff E n)
    (RoundSphere.inclusion_isDiffImmersionAt E n) (by simp)
    (riemannianMetricVectorSpace E).toContinuousRiemannianMetric

/-- The associated Riemannian distance on the round sphere. -/
noncomputable instance : PseudoEMetricSpace (RoundSphere E n) :=
  PseudoEMetricSpace.ofRiemannianMetric (𝓡 n) (RoundSphere E n)

example : IsRiemannianManifold (𝓡 n) (RoundSphere E n) := inferInstance

end thing_five

end
