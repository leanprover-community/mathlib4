/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang, Heather Macbeth
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorField.LieBracket

/-! # Torsion of a covariant derivative

We define the torsion tensor of a covariant derivative on the tangent bundle `TM` of some
manifold `M` and derive a criterion for torsion-freeness.

## Main definitions and results

* `IsCovariantDerivativeOn.torsion`: the torsion tensor of an unbundled covariant derivative
  on `TM` on some set `s ⊆ M`
* `CovariantDerivative.torsion`: the torsion tensor of a bundled covariant derivative on `TM`
* `CovariantDerivative.IsTorsionFree`: predicate for a bundled covariant derivative `∇`
  to be torsion-free: `∇` is torsion free if and only if its torsion tensor vanishes

-/

@[expose] public section -- TODO: think if we want to expose all definitions!

open Bundle Filter Module Topology Set NormedSpace

open scoped Bundle Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {x : M}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] (n : WithTop ℕ∞) {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)] [FiberBundle F V]

namespace IsCovariantDerivativeOn

/-- The torsion of a covariant derivative on the tangent bundle `TM`, as a bare function.
Prefer to use `torsion` (which is a two-tensor) instead. -/
noncomputable def torsionAux
    (cov : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x)) :
    (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) :=
  fun X Y x ↦ cov Y x (X x) - cov X x (Y x) - VectorField.mlieBracket I X Y x

variable
  {cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x)}
  {X X' Y : Π x : M, TangentSpace I x}

variable (f X) in
lemma torsionAux_self : IsCovariantDerivativeOn.torsionAux cov X X = 0 := by
  ext
  simp [torsionAux]

variable (X Y) in
lemma torsionAux_antisymm : torsionAux cov X Y = - torsionAux cov Y X := by
  ext x
  unfold torsionAux
  rw [VectorField.mlieBracket_swap]
  dsimp
  module

variable [IsManifold I 2 M] {U : Set M}

section

variable (Y)

lemma torsionAux_add_left_apply [CompleteSpace E] (hcov : IsCovariantDerivativeOn E cov U)
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x) (hx : x ∈ U := by trivial) :
    torsionAux cov (X + X') Y x = torsionAux cov X Y x + torsionAux cov X' Y x := by
  simp [torsionAux, hcov.add hX hX', VectorField.mlieBracket_add_left hX hX']
  module

lemma torsionAux_add_right_apply [CompleteSpace E] (hcov : IsCovariantDerivativeOn E cov U)
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x) (hx : x ∈ U := by trivial) :
    torsionAux cov Y (X + X') x = torsionAux cov Y X x + torsionAux cov Y X' x := by
  rw [torsionAux_antisymm, Pi.neg_apply,
    hcov.torsionAux_add_left_apply _ hX hX', torsionAux_antisymm Y, torsionAux_antisymm Y]
  simp; abel

lemma torsionAux_smul_left_apply [CompleteSpace E] (hcov : IsCovariantDerivativeOn E cov U)
    {f : M → 𝕜} (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) (hx : x ∈ U := by trivial) :
    torsionAux cov (f • X) Y x = f x • torsionAux cov X Y x := by
  simp only [torsionAux]
  rw [hcov.leibniz hX hf, VectorField.mlieBracket_smul_left hf hX]
  simp? [smul_sub] says
    simp only [Pi.smul_apply', map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.coe_comp',
      ContinuousLinearEquiv.coe_coe, Function.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      smul_sub]
  set A := f x • (cov X x) (Y x)
  set B := f x • (cov Y x) (X x)
  set C := f x • VectorField.mlieBracket I X Y x
  set D := mfderiv% f x (Y x)
  change B - (A + (fromTangentSpace _ D) • X x) - (-(fromTangentSpace _ D) • X x + C) = B - A - C
  module

lemma torsionAux_smul_right_apply [CompleteSpace E]
    {F : ((x : M) → TangentSpace I x) → (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x}
    (hF : IsCovariantDerivativeOn E F U)
    {f : M → 𝕜} (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) (hx : x ∈ U := by trivial) :
    torsionAux F Y (f • X) x = f x • torsionAux F Y X x := by
  rw [torsionAux_antisymm, Pi.neg_apply, hF.torsionAux_smul_left_apply Y hf hX,
    torsionAux_antisymm X]
  simp

end

section

variable [CompleteSpace 𝕜] [CompleteSpace E] [FiniteDimensional 𝕜 E]

noncomputable def torsion (hcov : IsCovariantDerivativeOn E cov univ) (x : M) :
    TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] TangentSpace I x :=
  mk2TensorAt I E E (torsionAux cov)
    (fun f σ τ hf hσ hτ ↦ hcov.torsionAux_smul_left_apply τ hf hσ)
    (fun σ σ' τ hσ hσ' hτ ↦ hcov.torsionAux_add_left_apply τ hσ hσ')
    (fun f σ τ hf hσ hτ ↦  hcov.torsionAux_smul_right_apply σ hf hτ)
    (fun σ τ τ' hσ hτ hτ' ↦ hcov.torsionAux_add_right_apply σ hτ hτ')

theorem torsion_apply (hcov : IsCovariantDerivativeOn E cov univ) {x}
    {X : Π x : M, TangentSpace I x} (hX : MDiffAt (T% X) x)
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x) :
    torsion hcov x (X x) (Y x) = torsionAux cov X Y x :=
  mk2TensorAt_apply _ _ _ _ _ _ hX hY

end

end IsCovariantDerivativeOn

namespace CovariantDerivative
open VectorField

variable
  {cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x)}
  {X X' Y : Π x : M, TangentSpace I x}

variable [CompleteSpace 𝕜] [CompleteSpace E] [FiniteDimensional 𝕜 E] [IsManifold I 2 M]
variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))

/-- The torsion tensor of a covariant derivative on the tangent bundle of a manifold. -/
noncomputable def torsion := cov.isCovariantDerivativeOn.torsion

lemma torsion_apply (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    cov.torsion x (X x) (Y x) = cov Y x (X x) - cov X x (Y x) - mlieBracket I X Y x := by
  unfold torsion IsCovariantDerivativeOn.torsion
  apply mk2TensorAt_apply
  exacts [hX, hY]

lemma torsion_apply_extend (u v : TangentSpace I x) :
    cov.torsion x u v =
      cov (extend E v) x (extend E u x) - cov (extend E u) x (extend E v x)
        - mlieBracket I (extend E u) (extend E v) x := by
  unfold torsion IsCovariantDerivativeOn.torsion
  apply mk2TensorAt_apply_eq_extend

/-- A covariant derivation is called **torsion-free** iff its torsion tensor vanishes. -/
def IsTorsionFree : Prop := torsion cov = 0

lemma isTorsionFree_iff : IsTorsionFree cov ↔
    ∀ {X Y x}, MDiffAt (T% X) x → MDiffAt (T% Y) x →
      cov Y x (X x) - cov X x (Y x) = mlieBracket I X Y x := by
  unfold IsTorsionFree
  constructor
  · intro h X Y x hX hY
    replace h := congr($h x (X x) (Y x))
    rw [cov.torsion_apply hX hY] at h
    simpa [sub_eq_iff_eq_add'] using h
  · intro h
    ext x u v
    rw [torsion_apply_extend, h]
    · simp
    · apply mdifferentiableAt_extend
    · apply mdifferentiableAt_extend

end CovariantDerivative
