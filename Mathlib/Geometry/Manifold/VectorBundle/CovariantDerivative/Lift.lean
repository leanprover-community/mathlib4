/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
/-!
# Lifting vectors using covariant derivatives

TODO: add a more complete doc-string

-/

@[expose] public section

open Bundle Filter Module Topology Set

open scoped Bundle Manifold ContDiff

section
variable {B : Type*} (E : B → Type*) {F : Type*}

/-- Given a bundle `π : E → B`, the diagonal section of `π^*E → E`. -/
def Bundle.pullback_diag (e : TotalSpace F E) : (TotalSpace.proj *ᵖ E) e :=
  e.2
end


section
variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ F] [T2Space M] [IsManifold I ∞ M]
  {cov : ((x : M) → TangentSpace I x) → (M → F) → M → F}
  {s : Set M} (hcov : IsCovariantDerivativeOn F cov s)


noncomputable
def IsCovariantDerivativeOn.lift_vec (x : M) (f : F) :
    TangentSpace I x →L[ℝ] TangentSpace I x × F :=
  .prod (.id ℝ _) (-evalL ℝ F F f ∘L hcov.one_form x)

@[simp]
lemma IsCovariantDerivativeOn.lift_vec_apply (x : M) (f : F) (u : TangentSpace I x) :
    hcov.lift_vec x f u = (u , -hcov.one_form x u f) :=
  rfl

@[simp]
lemma IsCovariantDerivativeOn.fst_comp_lift_vec (x : M) (f : F) :
    .fst ℝ _ _ ∘L hcov.lift_vec x f = .id ℝ _ := by
  ext u
  simp

@[simp]
lemma IsCovariantDerivativeOn.projection_lift_vec (x : M) (f : F) :
    (hcov.projection x f) ∘L (hcov.lift_vec x f) = 0 := by
  ext u
  simp

end

section
variable
{E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [(x : M) → AddCommGroup (V x)] [(x : M) → Module ℝ (V x)]
  [(x : M) → TopologicalSpace (V x)] [FiberBundle F V] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ F] [T2Space M]
  [IsManifold I ∞ M] [VectorBundle ℝ F V] {cov : CovariantDerivative I F V}
  [ContMDiffVectorBundle 1 F V I]

/-- Horizontal lift of a vector tangent to the base at a point in the corresponding fiber. -/
noncomputable
def CovariantDerivative.lift_vec (v : TotalSpace F V) :
    TangentSpace I v.proj →L[ℝ] TangentSpace (I.prod 𝓘(ℝ, F)) v :=
  letI t := trivializationAt F V v.proj
  haveI d_covDerOn := t.pushCovDer_isCovariantDerivativeOn
    (cov.isCovariantDerivativeOn.mono fun _ _ ↦ mem_univ _)
  letI tlift := d_covDerOn.lift_vec v.proj (t v).2
  t.derivInv I v ∘L tlift

lemma CovariantDerivative.lift_vec_apply {v : TotalSpace F V} (u : TangentSpace I v.proj) :
    letI t := trivializationAt F V v.proj
    haveI d_covDerOn := t.pushCovDer_isCovariantDerivativeOn
      (cov.isCovariantDerivativeOn.mono fun _ _ ↦ mem_univ _)
    letI tlift := d_covDerOn.lift_vec v.proj (t v).2
    cov.lift_vec v u = t.derivInv I v (tlift u) := rfl


lemma CovariantDerivative.lift_vec_eq_iff {v : TotalSpace F V} (u : TangentSpace I v.proj)
    (w : TangentSpace (I.prod 𝓘(ℝ, F)) v) :
    cov.lift_vec v u = w  ↔
      cov.proj v w = 0 ∧
      mfderiv (I.prod 𝓘(ℝ, F)) I (TotalSpace.proj : TotalSpace F V → M) v w = u := by
  constructor
  · rintro rfl
    constructor -- TODO: write two lemmas to apply here
    · sorry
    · sorry
  · rintro ⟨h, h'⟩
    sorry

-- noncomputable
-- def CovariantDerivative.lift_vec'
--   (p : TotalSpace E ((TotalSpace.proj : (TotalSpace F V → M)) *ᵖ (TangentSpace I))) :
--     TangentSpace (I.prod 𝓘(ℝ, F)) p.1 :=
--   letI t := trivializationAt F V p.1.proj
--   haveI d_covDerOn := t.pushCovDer_isCovariantDerivativeOn
--     (cov.isCovariantDerivativeOn.mono fun _ _ ↦ mem_univ _)
--   letI tlift := d_covDerOn.lift_vec p.1.proj (t p.1).2
--   t.derivInv I p.1 (tlift p.2)
end

section integralCurve
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*}
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] (γ : ℝ → M)
  (v : (x : M) → TangentSpace I x) (t₀ : ℝ)

lemma IsMIntegralCurveAt.mdifferentiableAt (h : IsMIntegralCurveAt γ v t₀) :
    ∀ᶠ t in 𝓝 t₀, MDiffAt γ t := by
  filter_upwards [h] with t ht
  exact ht.mdifferentiableAt

-- Is this really missing??
lemma IsMIntegralCurveAt_iff_mfderiv (hγ : ∀ᶠ t in 𝓝 t₀, MDiffAt γ t) :
    IsMIntegralCurveAt γ v t₀ ↔ ∀ᶠ t in 𝓝 t₀, mfderiv% γ t (1 : ℝ) = v (γ t) := by
  refine eventually_congr ?_
  filter_upwards [hγ] with t ht
  constructor
  · intro h
    rw [h.mfderiv]
    rw [ContinuousLinearMap.smulRight_apply]
    change 1 • v (γ t) = v (γ t)
    simp
  · intro h
    convert ht.hasMFDerivAt
    ext
    simp [← h]
    rfl

variable (I) in
noncomputable
def velocity (γ : ℝ → M) (t : ℝ) : TangentBundle I M := ⟨γ t, mfderiv% γ t (1 : ℝ)⟩


variable [IsManifold I ∞ M]

lemma IsMIntegralCurveAt.acceleration {X : Π x : M, TangentSpace I x}
    {γ : ℝ → M} {t₀ : ℝ} (hX : MDiffAt (T% X) (γ t₀))
    (hγ : ∀ᶠ (t : ℝ) in 𝓝 t₀, MDiffAt (velocity I γ) t)
    (hγX : IsMIntegralCurveAt γ X t₀) :
    velocity I.tangent (velocity I γ) t₀ = mfderiv% (T% X) (γ t₀) (X (γ t₀)) := by
  sorry
end integralCurve

section geodesics

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))


noncomputable
def CovariantDerivative.geodVF (v : TotalSpace E (TangentSpace I : M → Type _)) :
    TangentSpace (I.prod 𝓘(ℝ, E)) v :=  cov.lift_vec v v.2

/-- A curve `γ : ℝ → M` is a geodesic for `cov` at `t` if it is an integral
curve of the geodesic vector field of `cov` near `t`.
Remember: `IsMIntegralCurveAt` is local, not pointwise. -/
def CovariantDerivative.isGeodAt (γ : ℝ → M) (t : ℝ) :=
  IsMIntegralCurveAt (velocity I γ) cov.geodVF t

def CovariantDerivative.isGeod (γ : ℝ → M) := ∀ t, cov.isGeodAt γ t

-- May still need to tweak the assumption (maybe `X` should be smoother for instance).
lemma CovariantDerivative.orbit_geodVF {X : Π x : M, TangentSpace I x}
    {γ : ℝ → M} {t₀ : ℝ} (hX : MDiffAt (T% X) (γ t₀))
    (hγ : ∀ᶠ (t : ℝ) in 𝓝 t₀, MDiffAt (velocity I γ) t)
    (hγX : IsMIntegralCurveAt γ X t₀) :
    cov.isGeodAt γ t₀ ↔ ∀ᶠ t in 𝓝 t₀, cov X X (γ t) = 0 := by
  have := hγX.mdifferentiableAt
  unfold CovariantDerivative.isGeodAt
  rw [IsMIntegralCurveAt_iff_mfderiv _ _ _ hγ]
  constructor
  · intro h
    filter_upwards [h] with t ht
    replace ht : velocity I.tangent (velocity I γ) t = cov.geodVF (velocity I γ t) := by
      rw [← ht]
      simp [velocity]
    have := hγX.acceleration hX hγ
    sorry
  · intro h
    rw [← eventually_eventually_nhds] at h
    filter_upwards [h] with t ht
    sorry

end geodesics
