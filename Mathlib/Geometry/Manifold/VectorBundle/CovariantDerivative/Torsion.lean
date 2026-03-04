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
noncomputable def Bundle.torsion
    (cov : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)) :
    (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) :=
  fun X Y x ↦ cov X x (Y x) - cov Y x (X x) - VectorField.mlieBracket I X Y x

variable
  {cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)}
  {X X' Y : Π x : M, TangentSpace I x}

variable (f X) in
lemma torsion_self : torsion cov X X = 0 := by
  ext
  simp [torsion]

variable (X Y) in
lemma torsion_antisymm : torsion cov X Y = - torsion cov Y X := by
  ext x
  unfold torsion
  rw [VectorField.mlieBracket_swap]
  dsimp
  module

namespace IsCovariantDerivativeOn

variable [IsManifold I ∞ M] {U : Set M}

variable (Y) in
lemma torsion_add_left_apply [CompleteSpace E] (hcov : IsCovariantDerivativeOn E cov U)
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x) (hx : x ∈ U := by trivial) :
    torsion cov (X + X') Y x = torsion cov X Y x + torsion cov X' Y x := by
  simp [torsion, hcov.addσ hX hX', VectorField.mlieBracket_add_left hX hX']
  module

lemma torsion_add_right_apply [CompleteSpace E] (hcov : IsCovariantDerivativeOn E cov U)
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x) (hx : x ∈ U := by trivial) :
    torsion cov Y (X + X') x = torsion cov Y X x + torsion cov Y X' x := by
  rw [torsion_antisymm, Pi.neg_apply,
    hcov.torsion_add_left_apply _ hX hX', torsion_antisymm Y, torsion_antisymm Y]
  simp; abel

variable (Y) in
lemma torsion_smul_left_apply [CompleteSpace E] (hcov : IsCovariantDerivativeOn E cov U)
    {f : M → ℝ} (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) (hx : x ∈ U := by trivial) :
    torsion cov (f • X) Y x = f x • torsion cov X Y x := by
  simp only [torsion]
  rw [hcov.leibniz hX hf, VectorField.mlieBracket_smul_left hf hX]
  simp? [bar, smul_sub] says
    simp only [bar, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_mk,
      LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, Pi.smul_apply', map_smul, neg_smul, smul_sub]
  set A := f x • (cov X x) (Y x)
  set B := f x • (cov Y x) (X x)
  set C := f x • VectorField.mlieBracket I X Y x
  sorry /-simp only [torsion, Pi.sub_apply, hF.smulX (X := X) (σ := Y) (f := f)]
  rw [hF.leibniz Y hX hf hx, VectorField.mlieBracket_smul_left hf hX]
  simp [bar, smul_sub]
  abel -/

lemma torsion_smul_right_apply [CompleteSpace E]
    {F : ((x : M) → TangentSpace I x) → (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x}
    (hF : IsCovariantDerivativeOn E F U)
    {f : M → ℝ} (hf : MDiffAt f x) (hX : MDiffAt (T% Y) x) (hx : x ∈ U := by trivial) :
    torsion F X (f • Y) x = f x • torsion F X Y x := by
  rw [torsion_antisymm, Pi.neg_apply, hF.torsion_smul_left_apply X hf hX, torsion_antisymm X]
  simp

end IsCovariantDerivativeOn

section

variable [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]

noncomputable def torsionTensor (hcov : IsCovariantDerivativeOn E cov univ) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  mk2TensorAt I E E (Bundle.torsion cov)
    (fun {_ _ τ} ↦ hcov.torsion_smul_left_apply τ)
    (fun {_ _ τ} ↦ hcov.torsion_add_left_apply τ)
    (hcov.torsion_smul_right_apply)
    (hcov.torsion_add_right_apply)

theorem torsionTensor_apply (hcov : IsCovariantDerivativeOn E cov univ) {x}
    {X : Π x : M, TangentSpace I x} (hX : MDiffAt (T% X) x)
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x) :
    torsionTensor hcov x (X x) (Y x) = Bundle.torsion cov X Y x := by
  rw [torsionTensor]
  refine mk2TensorAt_apply _ _ ?_ ?_ ?_ ?_ hX hY
  · exact fun {_ _ τ} ↦ hcov.torsion_smul_left_apply τ
  · exact fun {_ _ τ} ↦ hcov.torsion_add_left_apply τ
  · exact hcov.torsion_smul_right_apply
  · exact hcov.torsion_add_right_apply

end

/-- `∇` is torsion-free on `U` if its torsion vanishes at each `x ∈ U` -/
noncomputable def IsTorsionFreeOn
    (cov : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x))
    (U : Set M) : Prop :=
  ∀ x ∈ U, ∀ X Y : Π x : M, TangentSpace I x, torsion cov X Y x = 0

namespace IsTorsionFreeOn

section changing_set

/-! Changing set
In this changing we change `s` in `IsTorsionFreeOn F f s`.
-/

lemma mono {s t : Set M} (hf : IsTorsionFreeOn cov t) (hst : s ⊆ t) : IsTorsionFreeOn cov s :=
  fun _ hx _ _ ↦ hf _ (hst hx) ..

lemma iUnion {ι : Type*} {s : ι → Set M} (hf : ∀ i, IsTorsionFreeOn cov (s i)) :
    IsTorsionFreeOn cov (⋃ i, s i) := by
  rintro x ⟨si, ⟨i, hi⟩, hxsi⟩ X Y
  exact hf i x (by simp [hi, hxsi]) X Y

end changing_set

/- Congruence properties -/
section

-- unused?
lemma congr {s : Set M} (h : IsTorsionFreeOn cov s)
    (hfg : ∀ {X Y : Π x : M, TangentSpace I x}, ∀ {x}, x ∈ s → cov X x (Y x) = cov' X x (Y x)) :
    IsTorsionFreeOn cov' s := by
  intro x hx X Y
  specialize h x hx X Y
  -- now, use torsion congruence lemma, i.e. tensoriality of sorts!
  -- TODO: generalise tensoriality to the local setting!
  sorry

end

end IsTorsionFreeOn

namespace CovariantDerivative

variable [IsManifold I ∞ M]
-- The torsion tensor of a covariant derivative on the tangent bundle `TM`.
variable {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}

variable {U : Set M} (hf : IsCovariantDerivativeOn E cov U)

-- TODO: prove applied versions of these, for IsCovariantDerivativeOn --- using tensoriality, later!
variable (f) in
@[simp]
lemma torsion_zero : torsion cov 0 X = 0 := by
  ext x
  simp [torsion]


@[simp]
lemma torsion_zero' : torsion cov X 0 = 0 := by
  rw [torsion_antisymm, torsion_zero]; simp

variable (Y) in
lemma torsion_add_left [CompleteSpace E]
    (hX : MDiff (T% X)) (hX' : MDiff (T% X')) :
    torsion cov (X + X') Y = torsion cov X Y + torsion cov X' Y := by
  ext x
  exact cov.isCovariantDerivativeOn.torsion_add_left_apply _ (hX x) (hX' x)

lemma torsion_add_right [CompleteSpace E]
    (hX : MDiff (T% X)) (hX' : MDiff (T% X')) :
    torsion cov Y (X + X') = torsion cov Y X + torsion cov Y X' := by
  rw [torsion_antisymm, torsion_add_left _ hX hX', torsion_antisymm X, torsion_antisymm X']; module

variable (Y) in
lemma torsion_smul_left [CompleteSpace E] {f : M → ℝ} (hf : MDiff f) (hX : MDiff (T% X)) :
    torsion cov (f • X) Y = f • torsion cov X Y := by
  ext x
  exact cov.isCovariantDerivativeOn.torsion_smul_left_apply _ (hf x) (hX x)

variable (X) in
lemma torsion_smul_right [CompleteSpace E] {f : M → ℝ} (hf : MDiff f) (hY : MDiff (T% Y)) :
    torsion cov X (f • Y) = f • torsion cov X Y := by
  ext x
  exact cov.isCovariantDerivativeOn.torsion_smul_right_apply (hf x) (hY x)

/-- The torsion of a covariant derivative is tensorial:
the value of `torsion cov X Y` at `x₀` depends only on `X x₀` and `Y x₀`. -/
def torsion_tensorial [T2Space M] [IsManifold I ∞ M] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
    {X X' Y Y' : Π x : M, TangentSpace I x} {x₀ : M}
    (hX : MDiffAt (T% X) x₀) (hX' : MDiffAt (T% X') x₀)
    (hY : MDiffAt (T% Y) x₀) (hY' : MDiffAt (T% Y') x₀)
    (hXX' : X x₀ = X' x₀) (hYY' : Y x₀ = Y' x₀) :
    (torsion cov X Y) x₀ = (torsion cov X' Y') x₀ := by
  apply tensoriality_criterion₂ I E (TangentSpace I) E (TangentSpace I) hX hX' hY hY' hXX' hYY'
  · intro f σ τ hf hσ
    exact cov.isCovariantDerivativeOn.torsion_smul_left_apply _ hf hσ
  · intro σ σ' τ hσ hσ'
    exact cov.isCovariantDerivativeOn.torsion_add_left_apply _ hσ hσ'
  · intros f σ σ' hf hσ'
    exact cov.isCovariantDerivativeOn.torsion_smul_right_apply hf hσ'
  · intro σ τ τ' hτ hτ'
    exact cov.isCovariantDerivativeOn.torsion_add_right_apply hτ hτ'

-- TODO: relate torsion-freeness to torsion tensor
-- (That will not work for torsion-freeness on a set, though.)

-- TODO: generalise tensoriality result above to `IsCovariantDerivativeOn`,
-- so it would apply here as well

variable (cov) in
/-- A covariant derivation is called **torsion-free** iff its torsion tensor vanishes. -/
def IsTorsionFree : Prop := torsion cov = 0

@[simp]
lemma isTorsionFreeOn_univ : IsTorsionFreeOn cov univ ↔ IsTorsionFree cov := by
  simp only [IsTorsionFree, IsTorsionFreeOn]
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  ext X Y x
  simp [h x]

/-- If a covariant derivative `cov` is torsion-free on each set in an open cover,
it is torsion-free. -/
def of_isTorsionFreeOn_of_open_cover {ι : Type*} {s : ι → Set M}
    (hf : ∀ i, IsTorsionFreeOn cov (s i)) (hs : ⋃ i, s i = Set.univ) :
    IsTorsionFree cov := by
  rw [← isTorsionFreeOn_univ, ← hs]
  exact IsTorsionFreeOn.iUnion hf

lemma isTorsionFree_def : IsTorsionFree cov ↔ torsion cov = 0 := by simp [IsTorsionFree]

-- This should be obvious; am I doing something wrong?
lemma isTorsionFree_iff : IsTorsionFree cov ↔
    ∀ X Y x, cov X x (Y x) - cov Y x (X x) = VectorField.mlieBracket I X Y x := by
  unfold IsTorsionFree torsion
  simp [funext_iff, sub_eq_iff_eq_add']

end CovariantDerivative
