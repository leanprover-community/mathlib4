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

@[expose] public section delaborators

-- TODO: decide whether we want this and move
-- This delaborates `TotalSpace.mk x v` to `⟨x, v⟩`
open Lean PrettyPrinter Delaborator SubExpr

@[app_delab mfderiv] meta def delab_mfderiv : Delab := do
  whenPPOption getPPNotation do
  let args := (← getExpr).getAppArgs
  if args.size < 22 then failure
  let pt : Term ← withNaryArg 21 <| delab
  let f := args[20]!
  let m := mkIdent (.mkSimple "mfderiv%")
  let T := mkIdent (.mkSimple "T%")
  try
    if let .lam _ _ b _ := f then
      if b.isAppOf ``Bundle.TotalSpace.mk' then
        let s := b.getAppArgs[4]!.getAppFn
        if s matches .fvar .. then
          let ss ← PrettyPrinter.delab s
          return ← `($m ($T $ss) $pt)
    throwError "nope"
  catch _ =>
    let x : Term ← withNaryArg 20 <| delab
    return ← `($m $x $pt)

@[app_delab Bundle.TotalSpace.mk'] meta def delabTotalSpace_mk' : Delab := do
  whenPPOption getPPNotation do
  let #[_B, _F, _E, _b, _v] := (← getExpr).getAppArgs | failure
  let bd : Term ← withNaryArg 3 <| delab
  let vd : Term ← withNaryArg 4 <| delab
  `(⟨$bd, $vd⟩)

end delaborators

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

lemma IsCovariantDerivativeOn.lift_vec_eq_iff
  {x : M} {f : F} {u : TangentSpace I x} {w : TangentSpace I x × F} :
    hcov.lift_vec x f u = w ↔ hcov.projection x f w = 0 ∧ w.1 = u := by
  constructor
  · intro rfl
    simp
  · rcases w with ⟨a, b⟩
    rintro ⟨h, rfl⟩
    simp_all
    grind

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
  have hcov := cov.isCovariantDerivativeOn_pushCovDer t
  letI tlift := hcov.lift_vec v.proj (t v).2
  t.derivInv I v ∘L tlift

lemma CovariantDerivative.lift_vec_apply {v : TotalSpace F V} (u : TangentSpace I v.proj) :
    letI t := trivializationAt F V v.proj
    haveI hcov := cov.isCovariantDerivativeOn_pushCovDer t
    letI tlift := hcov.lift_vec v.proj (t v).2
    cov.lift_vec v u = t.derivInv I v (tlift u) := rfl

/-- We can compute `lift_vec v` using any trivialization whose
base set contains `v.proj`. This is crucial to prove smoothness
of `lift_vec`. -/
lemma CovariantDerivative.lift_vec_eq {v : TotalSpace F V}
    {e : Trivialization F TotalSpace.proj} [MemTrivializationAtlas e]
    (hv : v.proj ∈ e.baseSet)
    (u : TangentSpace I v.proj) :
    haveI hcov := cov.isCovariantDerivativeOn_pushCovDer e
    cov.lift_vec v u = e.derivInv I v (hcov.lift_vec v.proj (e v).2 u) := by
  rw [cov.lift_vec_apply]
  set t := trivializationAt F V v.proj
  have hcov := cov.isCovariantDerivativeOn_pushCovDer t
  refold_let t
  sorry

@[simp]
lemma CovariantDerivative.lift_vec_horiz {v : TotalSpace F V} (u : TangentSpace I v.proj) :
    cov.lift_vec v u ∈ cov.horiz v := by
  let t := trivializationAt F V v.proj
  have hcov := cov.isCovariantDerivativeOn_pushCovDer t
  let tlift := hcov.lift_vec v.proj (t v).2
  rw [lift_vec_apply, CovariantDerivative.mem_horiz_iff_proj]
  -- TODO: cleanup
  simp only [proj, IsCovariantDerivativeOn.lift_vec_apply, ContinuousLinearMap.coe_comp',
             Trivialization.symmL_apply, Function.comp_apply]
  rw [t.deriv_derivInv_apply (FiberBundle.mem_baseSet_trivializationAt' v.proj)]
  suffices t.symm v.proj 0 = 0 by simpa
  exact (t.symmL ℝ v.proj).map_zero

@[simp]
lemma CovariantDerivative.proj_lift_vec {v : TotalSpace F V} (u : TangentSpace I v.proj) :
    cov.proj v (cov.lift_vec v u) = 0 := by
  rw [← cov.mem_horiz_iff_proj]
  exact lift_vec_horiz u

@[simp]
lemma CovariantDerivative.mfderiv_proj_lift_vec {v : TotalSpace F V} (u : TangentSpace I v.proj) :
    mfderiv (I.prod 𝓘(ℝ, F)) I TotalSpace.proj v (cov.lift_vec v u) = u := by
  unfold CovariantDerivative.lift_vec
  simp [FiberBundle.mem_baseSet_trivializationAt' v.proj]


lemma CovariantDerivative.lift_vec_eq_iff {v : TotalSpace F V} (u : TangentSpace I v.proj)
    (w : TangentSpace (I.prod 𝓘(ℝ, F)) v) :
    cov.lift_vec v u = w  ↔
      cov.proj v w = 0 ∧
      mfderiv (I.prod 𝓘(ℝ, F)) I (TotalSpace.proj : TotalSpace F V → M) v w = u := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨h, h'⟩
    let t := trivializationAt F V v.proj
    have hcov := cov.isCovariantDerivativeOn_pushCovDer t
    have mem := FiberBundle.mem_baseSet_trivializationAt F V v.proj
    apply (t.bijective_deriv mem).1
    unfold CovariantDerivative.lift_vec
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
    rw [t.deriv_derivInv_apply mem]
    rw [hcov.lift_vec_eq_iff]
    constructor
    · change t.symm v.proj ((hcov.projection v.proj (t v).2) ((t.deriv I v) w)) = 0 at h
      apply t.injective_symm mem
      refold_let t
      simp [h, t.symm_map_zero ℝ]
    · rw [← h', t.mfderiv_proj_fst_deriv mem]

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

variable [IsManifold I ∞ M]

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

end integralCurve

section geodesics

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))

-- FIXME: bug in `mfderiv%`?
-- FIXME: missing elaborator support to find I.tangent
omit [FiniteDimensional ℝ E] [T2Space M] in
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

lemma IsMIntegralCurveAt.proj_acceleration {X : Π x : M, TangentSpace I x}
    {γ : ℝ → M} {t₀ : ℝ} (hX : MDiffAt (T% X) (γ t₀))
    (hγX : IsMIntegralCurveAt γ X t₀) :
    cov.proj _ (velocity I.tangent (velocity I γ) t₀).2 = cov X X (γ t₀) := by
  rw [hγX.acceleration hX, cov.proj_mderiv _ hX hX]

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
    cov.isGeodAt γ t₀ ↔ ∀ᶠ t in 𝓝 t₀, cov X X (γ t) = 0 := by
  rw [cov.isGeodAt_iff_proj hγ]
  refine eventually_congr ?_
  filter_upwards [hX, hγX.eventually_isMIntegralCurveAt] with t ht ht'
  rw [ht'.proj_acceleration cov ht]

end geodesics
