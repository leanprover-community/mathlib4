/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Ehresmann

/-!
# Lifting vectors using covariant derivatives

TODO: add a more complete doc-string

-/

@[expose] public section

open Bundle Filter Module Topology Set

open scoped Bundle Manifold ContDiff

section
variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [FiniteDimensional 𝕜 F] [IsManifold I 1 M]
  {cov : (M → F) → (Π x : M, TangentSpace I x →L[𝕜] F)}
  {s : Set M} (hcov : IsCovariantDerivativeOn F cov s)


noncomputable
def IsCovariantDerivativeOn.lift_vec (x : M) (f : F) :
    TangentSpace I x →L[𝕜] TangentSpace I x × F :=
  .prod (.id 𝕜 _) (-hcov.one_form x f)

@[simp]
lemma IsCovariantDerivativeOn.lift_vec_apply (x : M) (f : F) (u : TangentSpace I x) :
    hcov.lift_vec x f u = (u , -hcov.one_form x f u) :=
  rfl

@[simp]
lemma IsCovariantDerivativeOn.fst_comp_lift_vec (x : M) (f : F) :
    .fst 𝕜 _ _ ∘L hcov.lift_vec x f = .id 𝕜 _ := by
  ext u
  simp

@[simp]
lemma IsCovariantDerivativeOn.projection_lift_vec (x : M) (f : F) :
    (hcov.projection x f) ∘L (hcov.lift_vec x f) = 0 := by
  ext u
  simp

lemma IsCovariantDerivativeOn.lift_vec_mem_horiz (x : M) (f : F) (u : TangentSpace I x) :
    hcov.lift_vec x f u ∈ hcov.horiz x f := by
  rw [horiz]
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
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [(x : M) → AddCommGroup (V x)] [(x : M) → Module 𝕜 (V x)]
  [(x : M) → TopologicalSpace (V x)] [FiberBundle F V]
  [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)]
  [FiniteDimensional 𝕜 F]
  [IsManifold I 1 M] [VectorBundle 𝕜 F V] {cov : CovariantDerivative I F V}
  [ContMDiffVectorBundle 1 F V I]

/-- Horizontal lift of a vector tangent to the base at a point in the corresponding fiber. -/
noncomputable
def CovariantDerivative.lift_vec (v : TotalSpace F V) :
    TangentSpace I v.proj →L[𝕜] TangentSpace (I.prod 𝓘(𝕜, F)) v :=
  letI t := trivializationAt F V v.proj
  have hcov := cov.isCovariantDerivativeOn_pushCovDer t
  letI tlift := hcov.lift_vec v.proj (t v).2
  t.derivInv I v ∘L tlift

lemma CovariantDerivative.lift_vec_apply {v : TotalSpace F V} (u : TangentSpace I v.proj) :
    letI t := trivializationAt F V v.proj
    haveI hcov := cov.isCovariantDerivativeOn_pushCovDer t
    letI tlift := hcov.lift_vec v.proj (t v).2
    cov.lift_vec v u = t.derivInv I v (tlift u) := rfl

@[simp]
lemma CovariantDerivative.lift_vec_mem_horiz {v : TotalSpace F V} (u : TangentSpace I v.proj) :
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
  exact (t.symmL 𝕜 v.proj).map_zero

@[simp]
lemma CovariantDerivative.proj_lift_vec {v : TotalSpace F V} (u : TangentSpace I v.proj) :
    cov.proj v (cov.lift_vec v u) = 0 := by
  rw [← cov.mem_horiz_iff_proj]
  exact lift_vec_mem_horiz u

@[simp]
lemma CovariantDerivative.mfderiv_proj_lift_vec {v : TotalSpace F V} (u : TangentSpace I v.proj) :
    mfderiv (I.prod 𝓘(𝕜, F)) I TotalSpace.proj v (cov.lift_vec v u) = u := by
  unfold CovariantDerivative.lift_vec
  simp [FiberBundle.mem_baseSet_trivializationAt' v.proj]

lemma CovariantDerivative.lift_vec_eq_iff {v : TotalSpace F V} (u : TangentSpace I v.proj)
    (w : TangentSpace (I.prod 𝓘(𝕜, F)) v) :
    cov.lift_vec v u = w  ↔
      cov.proj v w = 0 ∧
      mfderiv (I.prod 𝓘(𝕜, F)) I (TotalSpace.proj : TotalSpace F V → M) v w = u := by
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
      simp [h, t.symm_map_zero 𝕜]
    · rw [← h', t.mfderiv_proj_fst_deriv mem]

lemma CovariantDerivative.lift_vec_eq_iff' {v : TotalSpace F V} (u : TangentSpace I v.proj)
    (w : TangentSpace (I.prod 𝓘(𝕜, F)) v) :
    cov.lift_vec v u = w  ↔
      w ∈ cov.horiz v ∧
      mfderiv (I.prod 𝓘(𝕜, F)) I (TotalSpace.proj : TotalSpace F V → M) v w = u := by
  simp [CovariantDerivative.lift_vec_eq_iff, horiz]

/-- We can compute `lift_vec v` using any trivialization whose
base set contains `v.proj`. This is crucial to prove smoothness
of `lift_vec`. -/
lemma CovariantDerivative.lift_vec_eq [FiniteDimensional 𝕜 E] {v : TotalSpace F V}
    {e : Trivialization F TotalSpace.proj} [MemTrivializationAtlas e]
    (hv : v.proj ∈ e.baseSet)
    (u : TangentSpace I v.proj) :
    haveI hcov := cov.isCovariantDerivativeOn_pushCovDer e
    cov.lift_vec v u = e.derivInv I v (hcov.lift_vec v.proj (e v).2 u) := by
  apply (cov.lift_vec_eq_iff' _ _).mpr ⟨?_, ?_⟩
  · rw [cov.mem_horiz_iff_exists]
    have hcov := cov.isCovariantDerivativeOn_pushCovDer e
    have := hcov.lift_vec_mem_horiz v.proj (e v).2 u
    rw [hcov.mem_horiz_iff_exists] at this
    have proj_lift : (hcov.lift_vec v.proj (e v).2 u).1 = u := by simp
    rcases this with ⟨s, sdiff, sval, mfderivs, covs⟩
    -- TODO: cleanup the proof below and see how to factor stuff in
    -- `CovariantDerivative.mem_horiz_iff_exists`
    use e.funToSec s, ?_, ?_, ?_, ?_
    · exact e.mdifferentiableAt_funToSec hv sdiff
    · simp [sval, hv]
    · rw [e.mfderiv_total_funToSec sdiff hv]
      simp only [TotalSpace.proj_mk', ContinuousLinearMap.coe_comp', Function.comp_apply,
                 ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_id', id_eq]
      congr 2
      · simp [e.funToSec_proj_eq hv sval]
      · simp [e.mfderiv_proj_fst_deriv, hv]
      · simp only [hv, e.mfderiv_proj_derivInv_apply, ContinuousLinearMap.coe_neg,
                   LinearMap.neg_apply, ContinuousLinearMap.coe_coe]
        rw [proj_lift] at mfderivs ⊢
        erw [mfderivs]
        simp
    · rw [proj_lift] at covs
      simp [e.pushCovDer_funToSec cov, e.mfderiv_proj_fst_deriv hv, e.deriv_derivInv_apply hv, covs,
            e.symm_map_zero 𝕜]
  · simp [hv]

end
