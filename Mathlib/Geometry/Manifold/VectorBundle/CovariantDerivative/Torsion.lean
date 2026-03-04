/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorField.LieBracket

/-!
# Torsion of a covariant derivative

- define torsion of a covariant derivative (and its local version)
- torsion-free ness (local and global version)
- prove: torsion-freeness on `s` can be checked using a local frame on `s`

TODO: add a more complete doc-string

-/

@[expose] public section -- TODO: think if we want to expose all definitions!

open Bundle Filter Module Topology Set

open scoped Bundle Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {x : M}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (n : WithTop ℕ∞) {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)] [FiberBundle F V]

-- TODO: where is a good namespace for this?
/-- The torsion of a covariant derivative on the tangent bundle `TM` -/
noncomputable def Bundle.torsionFun
    (cov : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)) :
    (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) :=
  fun X Y x ↦ cov X x (Y x) - cov Y x (X x) - VectorField.mlieBracket I X Y x

variable
  {cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)}
  {X X' Y : Π x : M, TangentSpace I x}

variable (f X) in
lemma torsionFun_self : torsionFun cov X X = 0 := by
  ext
  simp [torsionFun]

variable (X Y) in
lemma torsionFun_antisymm : torsionFun cov X Y = - torsionFun cov Y X := by
  ext x
  unfold torsionFun
  rw [VectorField.mlieBracket_swap]
  dsimp
  module

namespace IsCovariantDerivativeOn

variable [IsManifold I ∞ M] {U : Set M}

variable (Y) in
lemma torsionFun_add_left_apply [CompleteSpace E] (hcov : IsCovariantDerivativeOn E cov U)
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x) (hx : x ∈ U := by trivial) :
    torsionFun cov (X + X') Y x = torsionFun cov X Y x + torsionFun cov X' Y x := by
  simp [torsionFun, hcov.addσ hX hX', VectorField.mlieBracket_add_left hX hX']
  module

lemma torsionFun_add_right_apply [CompleteSpace E] (hcov : IsCovariantDerivativeOn E cov U)
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x) (hx : x ∈ U := by trivial) :
    torsionFun cov Y (X + X') x = torsionFun cov Y X x + torsionFun cov Y X' x := by
  rw [torsionFun_antisymm, Pi.neg_apply,
    hcov.torsionFun_add_left_apply _ hX hX', torsionFun_antisymm Y, torsionFun_antisymm Y]
  simp; abel

variable (Y) in
lemma torsionFun_smul_left_apply [CompleteSpace E] (hcov : IsCovariantDerivativeOn E cov U)
    {f : M → ℝ} (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) (hx : x ∈ U := by trivial) :
    torsionFun cov (f • X) Y x = f x • torsionFun cov X Y x := by
  simp only [torsionFun]
  rw [hcov.leibniz hX hf, VectorField.mlieBracket_smul_left hf hX]
  simp? [bar, smul_sub] says
    simp only [bar, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_mk,
      LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, Pi.smul_apply', map_smul, neg_smul, smul_sub]
  set A := f x • (cov X x) (Y x)
  set B := f x • (cov Y x) (X x)
  set C := f x • VectorField.mlieBracket I X Y x
  sorry /-simp only [torsionFun, Pi.sub_apply, hF.smulX (X := X) (σ := Y) (f := f)]
  rw [hF.leibniz Y hX hf hx, VectorField.mlieBracket_smul_left hf hX]
  simp [bar, smul_sub]
  abel -/

lemma torsionFun_smul_right_apply [CompleteSpace E]
    {F : ((x : M) → TangentSpace I x) → (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x}
    (hF : IsCovariantDerivativeOn E F U)
    {f : M → ℝ} (hf : MDiffAt f x) (hX : MDiffAt (T% Y) x) (hx : x ∈ U := by trivial) :
    torsionFun F X (f • Y) x = f x • torsionFun F X Y x := by
  rw [torsionFun_antisymm, Pi.neg_apply, hF.torsionFun_smul_left_apply X hf hX, torsionFun_antisymm X]
  simp


section

variable [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]

noncomputable def torsion (hcov : IsCovariantDerivativeOn E cov univ) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  mk2TensorAt I E (Bundle.torsionFun cov)
    (fun {_ _ τ} ↦ hcov.torsionFun_smul_left_apply τ)
    (fun {_ _ τ} ↦ hcov.torsionFun_add_left_apply τ)
    (fun {_ _} ↦ hcov.torsionFun_smul_right_apply)
    (fun {_ _ _} ↦ hcov.torsionFun_add_right_apply)

theorem torsion_apply (hcov : IsCovariantDerivativeOn E cov univ) {x}
    {X : Π x : M, TangentSpace I x} (hX : MDiffAt (T% X) x)
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x) :
    torsion hcov x (X x) (Y x) = Bundle.torsionFun cov X Y x :=
  mk2TensorAt_apply _ _ _ _ _ hX hY

end

end IsCovariantDerivativeOn
-- /-- `∇` is torsion-free on `U` if its torsion vanishes at each `x ∈ U` -/
-- noncomputable def IsTorsionFreeOn
--     (cov : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x))
--     (U : Set M) : Prop :=
--   ∀ x ∈ U, ∀ X Y : Π x : M, TangentSpace I x, torsionFun cov X Y x = 0
--
-- namespace IsTorsionFreeOn
--
-- section changing_set
--
-- /-! Changing set
-- In this changing we change `s` in `IsTorsionFreeOn F f s`.
-- -/
--
-- lemma mono {s t : Set M} (hf : IsTorsionFreeOn cov t) (hst : s ⊆ t) : IsTorsionFreeOn cov s :=
--   fun _ hx _ _ ↦ hf _ (hst hx) ..
--
-- lemma iUnion {ι : Type*} {s : ι → Set M} (hf : ∀ i, IsTorsionFreeOn cov (s i)) :
--     IsTorsionFreeOn cov (⋃ i, s i) := by
--   rintro x ⟨si, ⟨i, hi⟩, hxsi⟩ X Y
--   exact hf i x (by simp [hi, hxsi]) X Y
--
-- end changing_set
--
-- end IsTorsionFreeOn

namespace CovariantDerivative
open VectorField

variable [IsManifold I ∞ M] [FiniteDimensional ℝ E] [T2Space M]
variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))

/-- The torsion tensor of a covariant derivative on the tangent bundle of a manifold. -/
noncomputable def torsion := cov.isCovariantDerivativeOn.torsion

lemma torsion_vector_field_apply (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    cov.torsion x (X x) (Y x) = cov X x (Y x) - cov Y x (X x) - mlieBracket I X Y x := by
  unfold torsion IsCovariantDerivativeOn.torsion
  apply mk2TensorAt_apply
  exacts [hX, hY]

lemma torsion_apply (u v : TangentSpace I x) :
    cov.torsion x u v = cov (extend I E u) x (extend I E v x)
                        - cov (extend I E v) x (extend I E u x)
                        - mlieBracket I (extend I E u) (extend I E v) x := by
  unfold torsion IsCovariantDerivativeOn.torsion
  apply mk2TensorAt_apply_eq_extend

/-- A covariant derivation is called **torsion-free** iff its torsion tensor vanishes. -/
def IsTorsionFree : Prop := torsion cov = 0

lemma isTorsionFree_iff : IsTorsionFree cov ↔
    ∀ {X Y x}, MDiffAt (T% X) x → MDiffAt (T% Y) x →
      cov X x (Y x) - cov Y x (X x) = mlieBracket I X Y x := by
  unfold IsTorsionFree
  constructor
  · intro h X Y x hX hY
    replace h := congr($h x (X x) (Y x))
    rw [cov.torsion_vector_field_apply hX hY] at h
    simpa [sub_eq_iff_eq_add'] using h
  · intro h
    ext x u v
    rw [torsion_apply, h]
    · simp
    · apply mdifferentiableAt_extend
    · apply mdifferentiableAt_extend

end CovariantDerivative
