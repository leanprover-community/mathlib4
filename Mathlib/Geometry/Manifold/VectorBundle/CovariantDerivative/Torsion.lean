/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang, Heather Macbeth
-/
module

public import Mathlib.Topology.FiberBundle.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorField.LieBracket

/-! # Torsion of an affine connection

We define the torsion tensor of an affine connection, i.e. a covariant derivative on the tangent
bundle `TM` of some manifold `M`.

## Main definitions and results

* `IsCovariantDerivativeOn.torsion`: the torsion tensor of an unbundled covariant derivative
  on `TM` on some set `s` in `M`
* `CovariantDerivative.torsion`: the torsion tensor of a bundled covariant derivative on `TM`
* `CovariantDerivative.torsion_eq_zero_iff`: the torsion tensor of a bundled covariant derivative
  `∇` vanishes if and only if `∇_X Y - ∇_Y X = [X, Y]` for all differentiable vector fields
  `X` and `Y`.

-/

@[expose] public section

open Bundle Set NormedSpace FiberBundle
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {x : M}

/-! ## Torsion tensor of an unbundled covariant derivative on `TM` on a set `s` -/
namespace IsCovariantDerivativeOn

/-- The torsion of a covariant derivative on the tangent bundle `TM`, as a bare function.
Prefer to use `IsCovariantDerivativeOn.torsion` (which is a 2-tensor) instead. -/
noncomputable def torsionAux
    (cov : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x)) :
    (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) :=
  fun X Y x ↦ cov Y x (X x) - cov X x (Y x) - VectorField.mlieBracket I X Y x

variable [IsManifold I 2 M] [CompleteSpace E]
  {cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x)}
  {X X' Y : Π x : M, TangentSpace I x}

theorem torsionAux_tensorial₁ (hcov : IsCovariantDerivativeOn E cov) (x : M)
    (Y : Π x, TangentSpace I x) :
    TensorialAt I E (torsionAux cov · Y x) x where
  smul hf hX := by
    simp [torsionAux, hcov.leibniz hX hf, VectorField.mlieBracket_smul_left hf hX]
    module
  add hX hX' := by
    simp [torsionAux, hcov.add hX hX', VectorField.mlieBracket_add_left hX hX']
    module

theorem torsionAux_tensorial₂ (hcov : IsCovariantDerivativeOn E cov) (x : M)
    (X : Π x, TangentSpace I x) :
    TensorialAt I E (torsionAux cov X · x) x where
  smul hf hY := by
    simp [torsionAux, hcov.leibniz hY hf, VectorField.mlieBracket_smul_right hf hY]
    module
  add hY hY' := by
    simp [torsionAux, hcov.add hY hY', VectorField.mlieBracket_add_right hY hY']
    module

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]

/-- The torsion tensor of an unbundled covariant derivative on `TM`. -/
noncomputable def torsion (hcov : IsCovariantDerivativeOn E cov univ) (x : M) :
    TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] TangentSpace I x :=
  TensorialAt.mkHom₂ (torsionAux cov · · x) _
    (fun τ _ ↦ hcov.torsionAux_tensorial₁ x τ)
    (fun σ _ ↦ hcov.torsionAux_tensorial₂ x σ)

theorem torsion_apply (hcov : IsCovariantDerivativeOn E cov univ) {x}
    {X : Π x : M, TangentSpace I x} (hX : MDiffAt (T% X) x)
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x) :
    torsion hcov x (X x) (Y x) = cov Y x (X x) - cov X x (Y x) - VectorField.mlieBracket I X Y x :=
  TensorialAt.mkHom₂_apply _ _ hX hY

theorem torsion_apply_eq_extend (hcov : IsCovariantDerivativeOn E cov univ) {x}
    (X₀ Y₀ : TangentSpace I x) :
    torsion hcov x X₀ Y₀ =
      cov (extend E Y₀) x X₀ - cov (extend E X₀) x Y₀
      - VectorField.mlieBracket I (extend E X₀) (extend E Y₀) x := by
  simp [torsion, torsionAux, TensorialAt.mkHom₂_apply_eq_extend]

variable (X) in
@[simp]
lemma torsion_self (hcov : IsCovariantDerivativeOn E cov univ) (X₀ : TangentSpace I x) :
    hcov.torsion x X₀ X₀ = 0 := by
  simp [torsion_apply_eq_extend]

variable (X Y) in
lemma torsion_antisymm (hcov : IsCovariantDerivativeOn E cov univ) (X₀ Y₀ : TangentSpace I x) :
    hcov.torsion x X₀ Y₀ = - hcov.torsion x Y₀ X₀ := by
  simp only [torsion_apply_eq_extend, neg_sub]
  rw [VectorField.mlieBracket_swap]
  dsimp
  module

end IsCovariantDerivativeOn

/-! ## Torsion tensor of a bundled covariant derivative on `TM` -/
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
  apply TensorialAt.mkHom₂_apply
  exacts [hX, hY]

lemma torsion_apply_eq_extend (X₀ Y₀ : TangentSpace I x) :
    cov.torsion x X₀ Y₀ =
      cov (extend E Y₀) x (extend E X₀ x) - cov (extend E X₀) x (extend E Y₀ x)
        - mlieBracket I (extend E X₀) (extend E Y₀) x := by
  unfold torsion IsCovariantDerivativeOn.torsion
  apply TensorialAt.mkHom₂_apply_eq_extend

@[simp]
lemma torsion_self (X₀ : TangentSpace I x) : cov.torsion x X₀ X₀ = 0 :=
  cov.isCovariantDerivativeOn.torsion_self ..

lemma torsion_antisymm (X₀ Y₀ : TangentSpace I x) : cov.torsion x X₀ Y₀ = - cov.torsion x Y₀ X₀ :=
  cov.isCovariantDerivativeOn.torsion_antisymm ..

lemma torsion_eq_zero_iff : cov.torsion = 0 ↔
    ∀ {X Y x}, MDiffAt (T% X) x → MDiffAt (T% Y) x →
      cov Y x (X x) - cov X x (Y x) = mlieBracket I X Y x := by
  constructor
  · intro h X Y x hX hY
    replace h := congr($h x (X x) (Y x))
    rw [cov.torsion_apply hX hY] at h
    simpa [sub_eq_iff_eq_add'] using h
  · intro h
    ext x u v
    rw [torsion_apply_eq_extend, h]
    · simp
    · apply mdifferentiableAt_extend
    · apply mdifferentiableAt_extend

end CovariantDerivative
