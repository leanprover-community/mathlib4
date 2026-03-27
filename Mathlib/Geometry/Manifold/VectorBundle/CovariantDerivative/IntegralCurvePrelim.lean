module

public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Geometry.Manifold.IntegralCurve.Basic


/-!
# Preliminaries about integral curves of vector fiels

TODO: PR that material to Mathlib.Geometry.Manifold.IntegralCurve.Basic
except for `proj_acceleration` which uses
`Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable`.
-/

@[expose] public section

open Bundle Filter Module Topology Set

open scoped Bundle Manifold ContDiff

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*}
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] (γ : ℝ → M)
  (v : (x : M) → TangentSpace I x) (t₀ : ℝ)

variable (I) in
noncomputable
def velocity (γ : ℝ → M) (t : ℝ) : TangentBundle I M := ⟨γ t, mfderiv% γ t (1 : ℝ)⟩

@[simp]
lemma proj_velocity (γ : ℝ → M) (t : ℝ) : (velocity I γ t).proj = γ t := rfl

lemma IsMIntegralCurveAt.mdifferentiableAt (h : IsMIntegralCurveAt γ v t₀) :
    ∀ᶠ t in 𝓝 t₀, MDiffAt γ t := by
  filter_upwards [h] with t ht
  exact ht.mdifferentiableAt

set_option backward.isDefEq.respectTransparency false in
protected lemma IsMIntegralCurveAt.mfderiv (hγ : IsMIntegralCurveAt γ v t₀) :
    ∀ᶠ t in 𝓝 t₀, mfderiv% γ t (1 : ℝ) = v (γ t) := by
  filter_upwards [hγ] with t ht
  rw [ht.mfderiv]
  rw [ContinuousLinearMap.smulRight_apply]
  change 1 • v (γ t) = v (γ t)
  simp

protected lemma IsMIntegralCurveAt.velocity_eventuallyEq
    (hγ : IsMIntegralCurveAt γ v t₀) : velocity I γ =ᶠ[𝓝 t₀] T%v ∘ γ := by
  filter_upwards [hγ.mfderiv] with t ht
  simp [ht, velocity]

-- Is this really missing??
lemma IsMIntegralCurveAt_iff_mfderiv (hγ : ∀ᶠ t in 𝓝 t₀, MDiffAt γ t) :
    IsMIntegralCurveAt γ v t₀ ↔ ∀ᶠ t in 𝓝 t₀, mfderiv% γ t (1 : ℝ) = v (γ t) := by
  refine ⟨fun h ↦ h.mfderiv, fun h ↦ ?_⟩
  filter_upwards [hγ.and h] with t ⟨ht, ht'⟩
  rw [← ht']
  convert ht.hasMFDerivAt
  ext
  simp
  rfl

lemma IsMIntegralCurveAt.eventually_isMIntegralCurveAt
    {X : Π x : M, TangentSpace I x} {γ : ℝ → M} {t₀ : ℝ}
    (hγX : IsMIntegralCurveAt γ X t₀) :
    ∀ᶠ t in 𝓝 t₀, IsMIntegralCurveAt γ X t :=
  eventually_eventually_nhds.2 hγX

variable [IsManifold I 1 M]

set_option linter.flexible false in --FIXME
lemma IsMIntegralCurveAt.acceleration {X : Π x : M, TangentSpace I x}
    {γ : ℝ → M} {t₀ : ℝ} (hX : MDiffAt (T% X) (γ t₀))
    (hγX : IsMIntegralCurveAt γ X t₀) :
    velocity I.tangent (velocity I γ) t₀ = mfderiv% (T% X) (γ t₀) (X (γ t₀)) := by
  have : velocity I γ =ᶠ[𝓝 t₀] T%X ∘ γ := hγX.velocity_eventuallyEq
  have := this.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I.tangent)
  have foo := EventuallyEq.eq_of_nhds hγX.mfderiv
  simp [velocity, this, foo]
  have := hγX.mdifferentiableAt.self_of_nhds
  rw [mfderiv_comp t₀ hX this, ← foo]
  rfl

lemma IsMIntegralCurveAt.eventually_acceleration {X : Π x : M, TangentSpace I x}
    {γ : ℝ → M} {t₀ : ℝ} (hX : ∀ᶠ t in 𝓝 t₀, MDiffAt (T% X) (γ t))
    (hγX : IsMIntegralCurveAt γ X t₀) :
    ∀ᶠ t in 𝓝 t₀, velocity I.tangent (velocity I γ) t = mfderiv% (T% X) (γ t) (X (γ t)) := by
  filter_upwards [hX, hγX.eventually_isMIntegralCurveAt] with t hXt hγXt
  exact acceleration hXt hγXt

-- FIXME: bug in `mfderiv%`?
-- FIXME: missing elaborator support to find I.tangent
variable (I) in
@[simp]
lemma proj_acceleration {γ : ℝ → M} {t : ℝ} (h : MDiffAt (velocity I γ) t) :
    mfderiv I.tangent I (TotalSpace.proj : TangentBundle I M → M)
  (velocity I γ t) (velocity I.tangent (velocity I γ) t).2 = (velocity
I γ t).2 := by
  have comp_eq: (TotalSpace.proj : TangentBundle I M → M) ∘ (velocity I γ) = γ := by
    ext t
    simp
  have diff : MDifferentiableAt I.tangent I (TotalSpace.proj : TangentBundle I M → M)
      (velocity I γ t) := by
    exact mdifferentiableAt_proj (TangentSpace I)
  have := mfderiv_comp t diff h
  rw [comp_eq] at this
  exact congr($this (1 : ℝ)).symm
