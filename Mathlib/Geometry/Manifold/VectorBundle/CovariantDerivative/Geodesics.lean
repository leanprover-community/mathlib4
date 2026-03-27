/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Lift
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.IntegralCurvePrelim

/-!
# Geodesics for covariant derivatives on tangent bundles

TODO: add a more complete doc-string

-/

@[expose] public section

open Bundle Filter Module Topology Set

open scoped Bundle Manifold ContDiff

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]
  [IsManifold I 2 M]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))

lemma IsMIntegralCurveAt.proj_acceleration {X : Π x : M, TangentSpace I x}
    {γ : ℝ → M} {t₀ : ℝ} (hX : MDiffAt (T% X) (γ t₀))
    (hγX : IsMIntegralCurveAt γ X t₀) :
    cov.proj _ (velocity I.tangent (velocity I γ) t₀).2 = cov X (γ t₀) (X (γ t₀)) := by
  rw [hγX.acceleration hX, cov.proj_mderiv _ hX]
  simp

/-- The geodesic vector field of a covariant derivative on a tangent bundle, defined
by send any vector `v` to its lift at itself. -/
noncomputable
def CovariantDerivative.geodVF (v : TotalSpace E (TangentSpace I : M → Type _)) :
    TangentSpace (I.prod 𝓘(ℝ, E)) v :=  cov.lift_vec v v.2

@[simp]
lemma CovariantDerivative.geodVF_horiz (v : TotalSpace E (TangentSpace I : M → Type _)) :
    cov.geodVF v ∈ cov.horiz v := by
  simp [CovariantDerivative.geodVF]

@[simp]
lemma CovariantDerivative.proj_geodVF (v : TotalSpace E (TangentSpace I : M → Type _)) :
    cov.proj v (cov.geodVF v) = 0 := by
  simp [CovariantDerivative.geodVF]

/-- A curve `γ : ℝ → M` is a geodesic for `cov` at `t` if it is an integral
curve of the geodesic vector field of `cov` near `t`.
Remember: `IsMIntegralCurveAt` is local, not pointwise. -/
def CovariantDerivative.isGeodAt (γ : ℝ → M) (t : ℝ) :=
  IsMIntegralCurveAt (velocity I γ) cov.geodVF t

set_option backward.isDefEq.respectTransparency false in
lemma CovariantDerivative.isGeodAt_iff_horiz {γ : ℝ → M} {t₀ : ℝ}
    (hγ : ∀ᶠ (t : ℝ) in 𝓝 t₀, MDiffAt (velocity I γ) t) :
    cov.isGeodAt γ t₀ ↔
    ∀ᶠ (t : ℝ) in 𝓝 t₀, (velocity I.tangent (velocity I γ) t).2 ∈ cov.horiz _ := by
  unfold CovariantDerivative.isGeodAt CovariantDerivative.geodVF
  rw [IsMIntegralCurveAt_iff_mfderiv _ _ _ hγ]
  refine eventually_congr ?_
  filter_upwards [hγ] with t ht
  conv_lhs => rw [Eq.comm, cov.lift_vec_eq_iff (velocity I γ t).2]
  rw [← cov.mem_horiz_iff_proj, proj_velocity,
      show mfderiv% (velocity I γ) t (1 : ℝ) = (velocity I.tangent (velocity I γ) t).2 from
        rfl, -- TODO need a simp lemma here?
      ]
  -- TODO: understand why
  -- simp [proj_velocity, proj_acceleration I ht]
  -- doesn’t close the goal
  simp only [proj_velocity, and_iff_left_iff_imp]
  exact fun _ ↦ proj_acceleration I ht

lemma CovariantDerivative.isGeodAt_iff_proj {γ : ℝ → M} {t₀ : ℝ}
    (hγ : ∀ᶠ (t : ℝ) in 𝓝 t₀, MDiffAt (velocity I γ) t) :
    cov.isGeodAt γ t₀ ↔
     ∀ᶠ (t : ℝ) in 𝓝 t₀, cov.proj _ (velocity I.tangent (velocity I γ) t).2 = 0 :=
  cov.isGeodAt_iff_horiz hγ

def CovariantDerivative.isGeod (γ : ℝ → M) := ∀ t, cov.isGeodAt γ t

set_option backward.isDefEq.respectTransparency false in
lemma CovariantDerivative.orbit_geodVF {X : Π x : M, TangentSpace I x}
    {γ : ℝ → M} {t₀ : ℝ} (hX : ∀ᶠ t in 𝓝 t₀, MDiffAt (T% X) (γ t))
    (hγ : ∀ᶠ (t : ℝ) in 𝓝 t₀, MDiffAt (velocity I γ) t)
    (hγX : IsMIntegralCurveAt γ X t₀) :
    cov.isGeodAt γ t₀ ↔ ∀ᶠ t in 𝓝 t₀, cov X (γ t) (X (γ t)) = 0 := by
  rw [cov.isGeodAt_iff_proj hγ]
  refine eventually_congr ?_
  filter_upwards [hX, hγX.eventually_isMIntegralCurveAt] with t ht ht'
  rw [ht'.proj_acceleration cov ht]

