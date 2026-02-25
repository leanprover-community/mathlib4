/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

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
end
