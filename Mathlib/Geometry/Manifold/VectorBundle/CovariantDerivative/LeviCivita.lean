/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang, Heather Macbeth
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
public import Mathlib.Geometry.Manifold.VectorBundle.OrthonormalFrame
public import Mathlib.Tactic.ClickSuggestions

/-!
# The Levi-Civita connection on a Riemannian manifold

This file defines the Levi-Civita connection on a (finite-dimensional) Riemannian manifold `(M, g)`.
A connection `∇` on the tangent bundle of a Riemannian manifold `(M, g)` is called a
*Levi-Civita connection* if it is both compatible with the metric `g` and torsion-free.
Any two such connections are equal (on differentiable vector fields), which is why one speaks of
*the* Levi-Civita connection on `TM`.
We construct a Levi-Civita connection and prove that is defines a compatible torsion-free
connection.


## Main definitions and results

* `CovariantDerivative.IsLeviCivitaConnection`: a covariant derivative `∇` on `(M, g)` is a
  Levi-Civita connection if and only if it is both torsion-free and compatible with `g`

* `CovariantDerivative.IsLeviCivitaConnection.uniqueness`: a Levi-Civita connection on `(M, g)` is
  uniquely determined on differentiable vector fields.

* `CovariantDerivative.leviCivitaConnection`: a choice of Levi-Civita connection on the tangent
  bundle `TM` of a Riemannian manifold `(M, g)`: this is unique up to the value on
  non-differentiable vector fields.
  If you know the Levi-Civita connection already, you can use `IsLeviCivitaConnection` instead.

* `CovariantDerivative.leviCivitaConnection_isLeviCivitaConnection`:
  `leviCivitaConnection` is a Levi-Civita connection (i.e., compatible and torsion-free)

## Implementation notes

* construction of LC using a tensoriality argument, and the musical isomorphism
  (avoids the use of local frames and trivialisations)

-/

open Bundle FiberBundle Function NormedSpace VectorField

open scoped Manifold ContDiff

section funpropsetup
-- In the medium term, `fun_prop` should support `MDifferentiable`, `ContMDiff` and friends fully.
-- This will require adding a custom discharger for models with corners.
-- In the mean-time, add the following attributes in this file, as they are too useful to not use.

attribute [fun_prop] MDifferentiable MDifferentiableAt
  MDifferentiable.add MDifferentiableAt.add
  mdifferentiableAt_fun_add_section MDifferentiableAt.fun_smul_section

end funpropsetup

-- Let `M` be a `C^2` manifold modeled on `(E, H)`.
variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)

-- move this
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] in
lemma injective_eval_mdifferentiableAt_vectorField
    (V : Type*) [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] (x : M) :
    Function.Injective
      (fun A : TangentSpace% x →L[ℝ] V ↦
        fun (Z : Π x, TangentSpace I x) (_ : MDiffAt (T% Z) x) ↦ A (Z x)) :=
  VectorBundle.injective_eval_mdifferentiableAt_sec ..

variable {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I 2 M]

-- From now on, `M` is endowed with a Riemannian metric.
variable
  [RiemannianBundle (fun (x : M) ↦ TangentSpace% x)]
  {X X' X'' Y Y' Y'' Z Z' : Π x : M, TangentSpace% x}

open scoped RealInnerProductSpace

-- move this, and think whether it could be more general
-- Note that Mathlib/Topology/FiberBundle/Basic.lean has a lot of similar lemma but far from enough
-- imports.
lemma VectorBundle.completeSpace (R : Type*) [NontriviallyNormedField R]
    {B : Type*} [TopologicalSpace B]
    (E : B → Type*) [(x : B) → AddCommGroup (E x)] [(x : B) → Module R (E x)]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace R F] [CompleteSpace F]
    [TopologicalSpace (TotalSpace F E)] [(x : B) → UniformSpace (E x)]
    [(x : B) → IsUniformAddGroup (E x)] [FiberBundle F E] [VectorBundle R F E] (b : B) :
    CompleteSpace (E b) := by
  let e := VectorBundle.continuousLinearEquivAt R F E b
  rwa [completeSpace_congr (e := e.toEquiv) e.isUniformEmbedding]

-- move this, also perhaps generalize to general Riemannian vector bundles,
-- and write a variant for `CMDiffAt n`
lemma injective_inner_mdifferentiableAt_vectorField [CompleteSpace E] (x : M) :
    Function.Injective
      (fun X₀ : TangentSpace% x ↦
        fun (Z : Π x, TangentSpace I x) (_ : MDiffAt (T% Z) x) ↦ (⟪X₀, Z x⟫)) := by
  have := VectorBundle.completeSpace ℝ (TangentSpace I (M := M)) E
  set Φ := InnerProductSpace.toDual ℝ (TangentSpace% x)
  exact (injective_eval_mdifferentiableAt_vectorField I ℝ x).comp Φ.injective

-- Let `cov` and `cov'` be covariant derivatives on `TM`.
variable (cov cov' : CovariantDerivative I E (TangentSpace I : M → Type _))

/-- Local notation for a covariant derivative on a vector bundle acting on a vector field and a
section. -/
local syntax:max "∇" term:arg term:arg : term
local macro_rules | `(∇ $X $σ) => `(fun (x : M) ↦ cov $σ x ($X x))
local syntax:max "∇'" term:arg term:arg : term
local macro_rules | `(∇' $X $σ) => `(fun (x : M) ↦ cov' $σ x ($X x))

-- Local notation for pointwise inner products of vector fields.
-- Note this does not cause ambiguity with the notation obtained
-- with `open scoped RealInnerProductSpace.`
local notation "⟪" X ", " Y "⟫" => fun x ↦ inner ℝ (X x) (Y x)

section prerequisites

-- TODO: generalise and move to a better place!
instance {k : ℕ∞ω} : ContMDiffMul 𝓘(ℝ, ℝ) k ℝ where
  contMDiff_mul := by
    -- This is almost [contMDiff_iff_contDiff], except that we want the other model on the domain.
    intro x
    rw [contMDiffAt_iff]
    refine ⟨by fun_prop, ?_⟩
    suffices ContDiffAt ℝ k (fun p ↦ p.1 * p.2) x by
      simp
      simpa [ModelProd, contDiffWithinAt_univ] using this
    fun_prop

variable {I}
variable {x : M}

lemma ContMDiffWithinAt.mvfderivWithin {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {k : ℕ∞ω} {f : M → V} {s : Set M}
    (hf : CMDiffAt[s] (k + 1) f x) (hX : CMDiffAt[s] (k + 1) (T% X) x) :
    CMDiffAt[s] k (fun (x : M) ↦ d[s] f x (X x)) x := by
  -- This proof is similar to ContMDiffWithinAt.mfderivWithin, but we can avoid all
  -- the coordinate change business. TODO: actually push this through.
  rw [contMDiffWithinAt_iff]
  have hf' := hf.mdifferentiableWithinAt (by simp)
  constructor
  · change ContinuousWithinAt (fun x ↦ (mfderiv[s] f x) (X x)) s x -- missing apply lemma
    simp only [mfderivWithin]
    let f' := fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ, V) x f)
      ((extChartAt I x).symm ⁻¹' s ∩ Set.range I) ((extChartAt I x) x)
    have : ContinuousWithinAt f' (extChartAt I x '' s) (extChartAt I x x) := sorry
    sorry
  · simp
    rw [contMDiffWithinAt_iff] at hf hX
    have hf' := hf.2; have hX' := hX.2
    simp at hf' hX'
    sorry

lemma ContMDiffAt.mvfderiv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {k : ℕ∞ω} {f : M → V} (hf : CMDiffAt (k + 1) f x) (hX : CMDiffAt (k + 1) (T% X) x) :
    CMDiffAt k (fun (x : M) ↦ d% f x (X x)) x := by
  simp_rw [← mvfderivWithin_univ]
  rw [← contMDiffWithinAt_univ] at hf hX ⊢
  apply ContMDiffWithinAt.mvfderivWithin hf hX

lemma ContMDiffOn.mvfderivWithin {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {k : ℕ∞ω} {f : M → V} {s : Set M} (hf : CMDiff[s] (k + 1) f) (hX : CMDiff[s] (k + 1) (T% X)) :
    CMDiff[s] k (fun (x : M) ↦ d[s] f x (X x)) :=
  fun x hx ↦ ContMDiffWithinAt.mvfderivWithin (hf x hx) (hX x hx)

lemma ContMDiff.mvfderiv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {k : ℕ∞ω} {f : M → V} (hf : CMDiff (k + 1) f) (hX : CMDiff (k + 1) (T% X)) :
    CMDiff k (fun (x : M) ↦ d% f x (X x)) :=
  fun x ↦ ContMDiffAt.mvfderiv (hf x) (hX x)

end prerequisites

/- TODO: The next four lemmas are workaround for some version of Lean 4 #9077
(Instance synthesis sees through type synonyms). They should be removed when that issue will
be fully solved. -/

section

variable {k : ℕ∞ω} [IsContMDiffRiemannianBundle I k E (fun (x : M) ↦ TangentSpace% x)]

variable {I} in
lemma _root_.ContMDiff.inner_bundle' {X Y : Π x : M, TangentSpace% x}
    (hX : CMDiff k (T% X)) (hY : CMDiff k (T% Y)) : CMDiff k ⟪X, Y⟫ :=
  ContMDiff.inner_bundle hX hY

variable {I} in
lemma _root_.ContMDiffAt.inner_bundle' {x : M} {X Y : Π x : M, TangentSpace% x}
    (hX : CMDiffAt k (T% X) x) (hY : CMDiffAt k (T% Y) x) : CMDiffAt k ⟪X, Y⟫ x :=
  ContMDiffAt.inner_bundle hX hY

end

-- From now on, we assume the Riemannian metric on `M` is `C¹`.
variable [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace% x)]

variable {I} in
@[fun_prop] lemma _root_.MDifferentiable.inner_bundle' {X Y : Π x : M, TangentSpace% x}
    (hX : MDiff (T% X)) (hY : MDiff (T% Y)) : MDiff ⟪X, Y⟫ :=
  MDifferentiable.inner_bundle hX hY

variable {I} in
@[fun_prop] lemma _root_.MDifferentiableAt.inner_bundle' {x : M} {X Y : Π x : M, TangentSpace% x}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    MDiffAt ⟪X, Y⟫ x :=
  MDifferentiableAt.inner_bundle hX hY

namespace CovariantDerivative
variable {x : M}

/-- A covariant derivative on a Riemannian bundle `TM` is called a **Levi-Civita connection**
if it is torsion-free and compatible with `g`.
Note that the bundle metric on `TM` is implicitly hidden in this definition.
-/
@[expose] public def IsLeviCivitaConnection [FiniteDimensional ℝ E] : Prop :=
  cov.IsMetricCompatible (M := M) (V := TangentSpace I) ∧ cov.torsion = 0

section uniqueness

variable {cov cov' I}

/-- Auxiliary lemma towards the uniquness of the Levi-Civita connection: expressing the term
`⟨∇ X Y, Z⟩` for all differentiable vector fields `X`, `Y` and `Z`, without reference to `∇`. -/
public lemma IsLeviCivitaConnection.apply_eq [FiniteDimensional ℝ E]
    (h : cov.IsLeviCivitaConnection)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    ⟪∇ X Y, Z⟫ x =
      (d% ⟪Y, Z⟫ x (X x) + d% ⟪Z, X⟫ x (Y x) - d% ⟪X, Y⟫ x (Z x)
      - ⟪Y, VectorField.mlieBracket I X Z⟫ x
      - ⟪Z, VectorField.mlieBracket I Y X⟫ x
      + ⟪X, VectorField.mlieBracket I Z Y⟫ x) / 2 := by
  -- use the compatibility in three ways
  have eq1a := h.1.mvfderiv_inner_eq X hY hZ
  have eq2a := h.1.mvfderiv_inner_eq Y hZ hX
  have eq3a := h.1.mvfderiv_inner_eq Z hX hY
  -- use the torsion-freeness in three ways
  have eq1b := congr(inner ℝ (Y x) ($(h.2) x (X x) (Z x)))
  have eq2b := congr(inner ℝ (Z x) ($(h.2) x (Y x) (X x)))
  have eq3b := congr(inner ℝ (X x) ($(h.2) x (Z x) (Y x)))
  -- combine
  simp (disch := fun_prop) [real_inner_comm, inner_sub_right, torsion_apply] at *
  linear_combination - (eq1a + eq1b + eq2a + eq2b - eq3a - eq3b) / 2

/-- Suppose `(M, g)` is a `C^{k+2}` manifold with a `C^{k+1}` Riemannian metric.
Then Levi-Civita connection, applied to `C^{k+1}` vector fields, yields a `C^k` vector field. -/
lemma IsLeviCivitaConnection.contMDiff_apply (k : ℕ∞) [FiniteDimensional ℝ E]
    [IsManifold I (k + 2) M]
    [IsContMDiffRiemannianBundle I (k + 1) E (fun (x : M) ↦ TangentSpace% x)]
    (h : cov.IsLeviCivitaConnection)
    {X Y Z : (x : M) → TangentSpace% x}
    (hX : CMDiff (k + 1) (T% X)) (hY : CMDiff (k + 1) (T% Y)) (hZ : CMDiff (k + 1) (T% Z)) :
    CMDiff k (fun x ↦ ⟪(cov Y x) (X x), Z x⟫) := by
  have a : IsManifold I ((k + 1) + 1) M := by
    rw [show (k : ℕ∞ω) + 1 + 1 = k + 2 by ring]; infer_instance
  have : IsManifold I (minSmoothness ℝ 2) M := by simpa
  have : IsManifold I (↑(k + 1) + 1) M := by simpa
  have : IsContMDiffRiemannianBundle I k E (fun (x : M) ↦ TangentSpace% x) :=
    IsContMDiffRiemannianBundle.of_le (n := k + 1) (by simp)
  have a (x) := h.apply_eq (hX.mdifferentiableAt (by simp))
    (hY.mdifferentiableAt (by simp)) (hZ.mdifferentiableAt (by simp) (x := x))
  simp_rw [a]
  -- Future: automate this using fun_prop!
  apply ContMDiff.div_const
  repeat apply ContMDiff.add
  all_goals
    try apply ContMDiff.neg
    try apply ContMDiff.mvfderiv
  all_goals try assumption
  · exact hY.inner_bundle' hZ
  · exact hZ.inner_bundle' hX
  · exact hX.inner_bundle' hY
  · apply ContMDiff.inner_bundle'
    · exact hY.of_le (by simp)
    · exact ContDiff.mlieBracket_vectorField (n := k + 1) hX hZ (by simp)
  · apply ContMDiff.inner_bundle'
    · exact hZ.of_le (by simp)
    · exact ContDiff.mlieBracket_vectorField (n := k + 1) hY hX (by norm_num)
  · apply ContMDiff.inner_bundle'
    · exact hX.of_le (by simp)
    · exact ContDiff.mlieBracket_vectorField (n := k + 1) hZ hY (by norm_num)

/-- The Levi-Civita connection on `(M, g)` is uniquely determined on differentiable vector fields.

Note that the differentiability hypotheses are required, since `CovariantDerivative` objects are
unconstrained in their behaviour on non-differentiable vector fields. -/
public theorem IsLeviCivitaConnection.uniqueness [FiniteDimensional ℝ E]
    (hcov : cov.IsLeviCivitaConnection) (hcov' : cov'.IsLeviCivitaConnection)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    ∇ X Y x = ∇' X Y x := by
  apply injective_inner_mdifferentiableAt_vectorField; ext Z hZ
  exact (hcov.apply_eq hX hY hZ).trans <| hcov'.apply_eq hX hY hZ |>.symm

end uniqueness

section existence

variable (X Y Z) in
/-- Auxiliary quantity for the construction of the Levi-Civita connection:
If `∇` is the Levi-Civita connection on `TM`, this formula will express `⟨∇ X Y, Z⟩`. -/
noncomputable def leviCivitaAux (x : M) : ℝ :=
  (d% ⟪Y, Z⟫ x (X x) + d% ⟪Z, X⟫ x (Y x) - d% ⟪X, Y⟫ x (Z x)
  - ⟪Y, VectorField.mlieBracket I X Z⟫ x
  - ⟪Z, VectorField.mlieBracket I Y X⟫ x
  + ⟪X, VectorField.mlieBracket I Z Y⟫ x) / 2

/-- `leviCivitaAux` is tensorial with respect to its first argument. -/
theorem leviCivitaAux_tensorial₁ [FiniteDimensional ℝ E]
    {Y : Π x : M, TangentSpace% x} (x : M) (hY : MDiffAt (T% Y) x) {Z : Π x, TangentSpace I x}
    (hZ : MDiffAt (T% Z) x) :
    TensorialAt I E (leviCivitaAux I · Y Z x) x where
  smul hf hX := by
    simp (disch := fun_prop) [leviCivitaAux, mvfderiv_fun_mul,
      mlieBracket_smul_left, mlieBracket_smul_right,
      inner_add_right, inner_smul_left, inner_smul_right, real_inner_comm]
    ring
  add hX₁ hX₂ := by
    simp (disch := fun_prop) [leviCivitaAux, mlieBracket_add_right, mlieBracket_add_left,
      mvfderiv_fun_add, inner_add_left, inner_add_right]
    ring

/-- `leviCivitaAux` is tensorial with respect to its second argument. -/
theorem leviCivitaAux_tensorial₂ [FiniteDimensional ℝ E]
    {Y : Π x : M, TangentSpace% x} (x : M) (hY : MDiffAt (T% Y) x) {X : Π x, TangentSpace I x}
    (hX : MDiffAt (T% X) x) :
    TensorialAt I E (leviCivitaAux I X Y · x) x where
  smul hf hZ := by
    simp (disch := fun_prop) [leviCivitaAux,
      mlieBracket_smul_right, mlieBracket_smul_left,
      mvfderiv_fun_mul,
      inner_smul_left, inner_smul_right, inner_add_right, real_inner_comm]
    ring
  add hZ₁ hZ₂ := by
    simp (disch := fun_prop) [leviCivitaAux,
      mlieBracket_add_right, mlieBracket_add_left,
      mvfderiv_fun_add,
      inner_add_left, inner_add_right]
    ring

/-- Almost the underlying function underlying our construction of the Levi-Civita connection:
this is the desired `(1,1)`-tensor, but without considerations to the junk value when
applied to non-differentiable vector fields. -/
noncomputable def lcAux₁ [FiniteDimensional ℝ E]
    {Y : Π x : M, TangentSpace% x} (x : M) (hY : MDiffAt (T% Y) x) :
    TangentSpace% x →L[ℝ] TangentSpace% x :=
  -- Use the musical isomorphism to produce a candidate `∇ Y` as a `(1,1)`-tensor
  -- (rather than a `2`-tensor).
  have : FiniteDimensional ℝ (TangentSpace% x) := inferInstanceAs (FiniteDimensional ℝ E)
  have : CompleteSpace (TangentSpace% x) := FiniteDimensional.complete ℝ _
  (InnerProductSpace.toDual ℝ _).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (TensorialAt.mkHom₂ _ (x := x)
      (fun _Z hZ ↦ leviCivitaAux_tensorial₁ _ _ hY hZ)
      (fun _X hX ↦ leviCivitaAux_tensorial₂ _ _ hY hX))

set_option backward.isDefEq.respectTransparency false in
theorem lcAux₁_apply [FiniteDimensional ℝ E] {x : M}
    {X : Π x : M, TangentSpace% x} (hX : MDiffAt (T% X) x)
    {Y : Π x : M, TangentSpace% x} (hY : MDiffAt (T% Y) x)
    {Z : Π x : M, TangentSpace% x} (hZ : MDiffAt (T% Z) x) :
    ⟪lcAux₁ I x hY (X x), Z x⟫ = leviCivitaAux I X Y Z x := by
  unfold lcAux₁
  simp [TensorialAt.mkHom₂_apply _ _ hX hZ]

open scoped Classical in
/-- The function underlying our construction of the Levi-Civita connection on `(M,g)` -/
noncomputable def lcAux [FiniteDimensional ℝ E]
    (Y : Π x : M, TangentSpace% x) (x : M) :
    TangentSpace% x →L[ℝ] TangentSpace% x :=
  if hY : MDiffAt (T% Y) x then lcAux₁ I x hY else 0

theorem lcAux_apply [FiniteDimensional ℝ E] {x : M}
    {X : Π x : M, TangentSpace% x} (hX : MDiffAt (T% X) x)
    {Y : Π x : M, TangentSpace% x} (hY : MDiffAt (T% Y) x)
    {Z : Π x : M, TangentSpace% x} (hZ : MDiffAt (T% Z) x) :
    ⟪lcAux I Y x (X x), Z x⟫ = leviCivitaAux I X Y Z x := by
  simpa [lcAux, dif_pos hY] using lcAux₁_apply I hX hY hZ

set_option backward.isDefEq.respectTransparency false in
lemma isCovariantDerivativeOn_lcAux [FiniteDimensional ℝ E] :
    IsCovariantDerivativeOn E (lcAux I (M := M)) where
  add {Y Y'} x hY hY' _ := by
    apply injective_eval_mdifferentiableAt_vectorField; ext X hX
    apply injective_inner_mdifferentiableAt_vectorField; ext Z hZ
    simp (disch := fun_prop) [lcAux, dif_pos, TensorialAt.mkHom₂_apply, lcAux₁,
      leviCivitaAux, mvfderiv_fun_add,
      mlieBracket_add_left, mlieBracket_add_right,
      inner_add_left, inner_add_right]
    ring
  leibniz {Y f x} hY hf _ := by
    apply injective_eval_mdifferentiableAt_vectorField; ext X hX
    apply injective_inner_mdifferentiableAt_vectorField; ext Z hZ
    simp (disch := fun_prop) [lcAux, dif_pos, lcAux₁, TensorialAt.mkHom₂_apply,
      leviCivitaAux, mvfderiv_fun_mul,
      mlieBracket_smul_left, mlieBracket_smul_right,
      inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, real_inner_comm]
    ring

variable (M) in
/-- A choice of Levi-Civita connection on the tangent bundle `TM` of a Riemannian manifold `(M, g)`:
this is unique up to the value on non-differentiable vector fields.
If you know the Levi-Civita connection already, you can use `IsLeviCivitaConnection` instead. -/
public noncomputable def leviCivitaConnection [FiniteDimensional ℝ E] :
    CovariantDerivative I E (TangentSpace I : M → Type _) where
  toFun := lcAux I
  isCovariantDerivativeOnUniv := isCovariantDerivativeOn_lcAux I

public theorem leviCivitaConnection_apply [FiniteDimensional ℝ E] {x : M}
    {X : Π x : M, TangentSpace% x} (hX : MDiffAt (T% X) x)
    {Y : Π x : M, TangentSpace% x} (hY : MDiffAt (T% Y) x)
    {Z : Π x : M, TangentSpace% x} (hZ : MDiffAt (T% Z) x) :
    ⟪leviCivitaConnection I M Y x (X x), Z x⟫ =
      (d% ⟪Y, Z⟫ x (X x) + d% ⟪Z, X⟫ x (Y x) - d% ⟪X, Y⟫ x (Z x)
      - ⟪Y, VectorField.mlieBracket I X Z⟫ x
      - ⟪Z, VectorField.mlieBracket I Y X⟫ x
      + ⟪X, VectorField.mlieBracket I Z Y⟫ x) / 2 :=
  lcAux_apply _ hX hY hZ

public theorem leviCivitaConnection_apply_right [FiniteDimensional ℝ E] {x : M}
    {X : Π x : M, TangentSpace% x} (hX : MDiffAt (T% X) x)
    {Y : Π x : M, TangentSpace% x} (hY : MDiffAt (T% Y) x)
    {Z : Π x : M, TangentSpace% x} (hZ : MDiffAt (T% Z) x) :
    ⟪X x, leviCivitaConnection I M Y x (Z x)⟫ =
      (d% ⟪Y, X⟫ x (Z x) + d% ⟪X, Z⟫ x (Y x) - d% ⟪Z, Y⟫ x (X x)
      - ⟪Y ,VectorField.mlieBracket I Z X⟫ x
      - ⟪X, VectorField.mlieBracket I Y Z⟫ x
      + ⟪Z, VectorField.mlieBracket I X Y⟫ x) / 2 := by
  rw [real_inner_comm]
  exact lcAux_apply _ hZ hY hX

public lemma leviCivitaConnection_isMetricCompatible [FiniteDimensional ℝ E] :
    (leviCivitaConnection I M).IsMetricCompatible (M := M) (V := TangentSpace I) := by
  rw [isMetricCompatible_iff]
  intro x X Y Z hX hY hZ
  -- Normalise the expressions by swapping arguments for inner product and mlieBracket,
  -- until the swappable arguments are in order X < Y < Z.
  simp (disch := fun_prop) [leviCivitaConnection_apply_right,
    fun x ↦ real_inner_comm (Z x),
    fun x ↦ real_inner_comm (Y x) (X x),
    mlieBracket_swap (V := Z),
    mlieBracket_swap (V := Y) (W := X)]
  ring

public lemma leviCivitaConnection_torsion_eq_zero [FiniteDimensional ℝ E] :
    (leviCivitaConnection I M).torsion = 0 := by
  rw [CovariantDerivative.torsion_eq_zero_iff]
  intro X Y x hX hY
  apply injective_inner_mdifferentiableAt_vectorField; ext Z hZ
  simp (disch := fun_prop) [leviCivitaConnection_apply I,
    mlieBracket_swap (V := Y) (W := X), mlieBracket_swap (V := Z) (W := X),
    mlieBracket_swap (V := Z) (W := Y),
    real_inner_comm, inner_sub_left]
  ring

/-- `leviCivitaConnection` is a Levi-Civita connection (i.e., compatible and torsion-free) -/
public lemma leviCivitaConnection_isLeviCivitaConnection [FiniteDimensional ℝ E] :
    (leviCivitaConnection I M).IsLeviCivitaConnection :=
  ⟨leviCivitaConnection_isMetricCompatible I, leviCivitaConnection_torsion_eq_zero I⟩

variable {I} in
lemma contMDiff_leviCivitaConnection_apply (k : ℕ∞) [FiniteDimensional ℝ E]
    [IsManifold I (k + 2) M]
    [IsContMDiffRiemannianBundle I (k + 1) E (fun (x : M) ↦ TangentSpace% x)]
    {X Y Z : (x : M) → TangentSpace% x}
    (hX : CMDiff (k + 1) (T% X)) (hY : CMDiff (k + 1) (T% Y)) (hZ : CMDiff (k + 1) (T% Z)) :
    CMDiff k (fun x ↦ ⟪((leviCivitaConnection I M) Y x) (X x), Z x⟫) :=
  (leviCivitaConnection_isLeviCivitaConnection I).contMDiff_apply k hX hY hZ

-- TODO: generalise all this discussion to sections of any smooth bundle!

-- Move: sections into a bundle with subsingleton fiber are smooth
section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] (n : ℕ∞ω)
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x : M, TopologicalSpace (V x)] [FiberBundle F V]
  {s : ∀ x, V x} {u : Set M} {x : M}

@[nontriviality]
lemma contMDiffWithinAt_section_of_subsingleton [Subsingleton F] :
    CMDiffAt[u] n (T% s) x := by
  rw [contMDiffWithinAt_section]
  apply contMDiffWithinAt_const |>.congr
  · intro y _
    apply Subsingleton.elim
  rfl

@[nontriviality]
lemma contMDiffAt_section_of_subsingleton [Subsingleton F] : CMDiffAt n (T% s) x := by
  rw [← contMDiffWithinAt_univ]
  apply contMDiffWithinAt_section_of_subsingleton

@[nontriviality]
lemma contMDiffOn_section_of_subsingleton [Subsingleton F] : CMDiff[u] n (T% s) :=
  fun _x _hx ↦ contMDiffWithinAt_section_of_subsingleton ..

@[nontriviality]
lemma contMDiff_section_of_subsingleton [Subsingleton F] : CMDiff n (T% s) :=
  fun _x ↦ contMDiffAt_section_of_subsingleton ..

end

-- This version is true. Does it suffice for our purposes? TODO!
open Module in
variable {I} in
lemma step2a (k : ℕ∞) {W : (x : M) → TangentSpace% x} [FiniteDimensional ℝ E]
    [IsManifold I (k + 2) M]
    [IsContMDiffRiemannianBundle I (k + 1) E (fun (x : M) ↦ TangentSpace% x)]
    [IsContMDiffRiemannianBundle I k E (fun (x : M) ↦ TangentSpace% x)] {x : M}
    (hW : ∀ {Z : (x : M) → TangentSpace% x} (hZ : CMDiffAt (k + 1) (T% Z) x),
      CMDiffAt k (fun x ↦ ⟪W x, Z x⟫) x) :
    CMDiffAt k (T% W) x := by
  nontriviality E
  -- Take an orthonormal frame.
  let b := Basis.ofVectorSpace ℝ E
  let t := trivializationAt E (TangentSpace I : M → Type _) x
  have hx : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have : Nonempty ↑(Basis.ofVectorSpaceIndex ℝ E) := b.index_nonempty
  -- The linear ordering on the indexing set of `b` is only used in this proof,
  -- so our choice does not matter.
  have : LinearOrder ↑(Basis.ofVectorSpaceIndex ℝ E) := by
    choose r wo using exists_wellFoundedLT _
    exact r
  have : LocallyFiniteOrderBot ↑(Basis.ofVectorSpaceIndex ℝ E) := by sorry
  -- Choose an orthonormal frame (s i) near x w.r.t. to this trivialisation, and the metric g
  have : IsManifold I (↑k + 1 + 1) M := by sorry -- simpa
  have : ContMDiffVectorBundle (k + 1) E (fun (x : M) ↦ TangentSpace% x) I :=
    TangentBundle.contMDiffVectorBundle
  have hs := b.orthonormalFrame_isOrthonormalFrameOn (n := k + 1) t (IB := I)
  have hs' : IsOrthonormalFrameOn I E k (b.orthonormalFrame t) t.baseSet := sorry -- easy, missing API lemma
  rw [hs'.contMDiffAt_iff_inner (t.open_baseSet.mem_nhds (mem_baseSet_trivializationAt' x))]
  intro i
  simp_rw [real_inner_comm]
  exact hW (contMDiffAt_orthonormalFrame_of_mem b t i hx)

-- TODO: can I use step2a above to prove this?
-- or is a variant true, with just C^n at x in the condition?
variable {I} in
lemma step2 (k : ℕ∞) {W : (x : M) → TangentSpace% x} [FiniteDimensional ℝ E]
    [IsManifold I (k + 2) M]
    [IsContMDiffRiemannianBundle I (k + 1) E (fun (x : M) ↦ TangentSpace% x)]
    (hW : ∀ {Z : (x : M) → TangentSpace% x} (hZ : CMDiff (k + 1) (T% Z)),
      CMDiff k (fun x ↦ ⟪W x, Z x⟫)) :
    CMDiff (k + 1) (T% W) := by
  sorry

open Module in
-- Variant of `contMDiffAt_of_inner` --- with slightly stronger requirements on differentiability,
-- but less on the regularity of the metric. This cannot be applied to the Levi-Civita connection
-- as there is a loss of derivatives there.

variable {I} in
/-- A vector field on a Riemannian manifold `(M, g)` is `C^n` at `x` if if its pairing
with any `C^n` vector field at `x` is `C^n` at `x`.
This version assumes `M` is a `C^{n+1}`-manifold with a `C^n` metric. -/
lemma contMDiffAt_of_inner (k : ℕ∞) {W : (x : M) → TangentSpace% x} [FiniteDimensional ℝ E]
    [IsManifold I k M] [IsManifold I (k + 1) M]
    [IsContMDiffRiemannianBundle I k E (fun (x : M) ↦ TangentSpace% x)] {x : M}
    (hW : ∀ {Z : (x : M) → TangentSpace% x}
      (hZ : CMDiffAt k (T% Z) x), CMDiffAt k (fun x ↦ ⟪W x, Z x⟫) x) :
    CMDiffAt k (T% W) x := by
  nontriviality E
  -- Take an orthonormal frame.
  let b := Basis.ofVectorSpace ℝ E
  let t := trivializationAt E (TangentSpace I : M → Type _) x
  have hx : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have : Nonempty ↑(Basis.ofVectorSpaceIndex ℝ E) := b.index_nonempty
  -- The linear ordering on the indexing set of `b` is only used in this proof,
  -- so our choice does not matter.
  have : LinearOrder ↑(Basis.ofVectorSpaceIndex ℝ E) := by
    choose r wo using exists_wellFoundedLT _
    exact r
  have : LocallyFiniteOrderBot ↑(Basis.ofVectorSpaceIndex ℝ E) := by sorry
  -- Choose an orthonormal frame (s i) near x w.r.t. to this trivialisation, and the metric g
  let frame := b.orthonormalFrame t
  have : ContMDiffVectorBundle k E (fun (x : M) ↦ TangentSpace% x) I :=
    TangentBundle.contMDiffVectorBundle
  have hs := b.orthonormalFrame_isOrthonormalFrameOn (n := k) t (IB := I)
  rw [hs.contMDiffAt_iff_inner (t.open_baseSet.mem_nhds (mem_baseSet_trivializationAt' x))]
  intro i
  simp_rw [real_inner_comm]
  exact hW (contMDiffAt_orthonormalFrame_of_mem b t i hx)

variable {I} in
/-- A vector field on a Riemannian manifold `(M, g)` is `C^n` at `x` if and only if its pairing
with any `C^n` vector field at `x` is `C^n` at `x`.
This version assumes `M` is a `C^{n+1}`-manifold with a `C^n` metric. -/
lemma contMDiffAt_iff_inner (k : ℕ∞) {W : (x : M) → TangentSpace% x} [FiniteDimensional ℝ E]
    [IsManifold I k M] [IsManifold I (k + 1) M]
    [IsContMDiffRiemannianBundle I k E (fun (x : M) ↦ TangentSpace% x)] {x : M} :
    CMDiffAt k (T% W) x ↔
      ∀ {Z : (x : M) → TangentSpace% x}
        (_hZ : CMDiffAt k (T% Z) x), CMDiffAt k (fun x ↦ ⟪W x, Z x⟫) x :=
  ⟨fun hW _Z hZ ↦ hW.inner_bundle' hZ, fun h ↦ contMDiffAt_of_inner k h⟩

variable {I} in
/-- A vector field on a Riemannian manifold `(M, g)` is `C^n` if if its pairing
with any `C^n` vector field is `C^n`. This version assumes `M` is a `C^{n+1}`-manifold
with a `C^n` metric. -/
lemma contMDiff_of_inner (k : ℕ∞) {W : (x : M) → TangentSpace% x} [FiniteDimensional ℝ E]
    [IsManifold I k M] [IsManifold I (k + 1) M]
    [IsContMDiffRiemannianBundle I k E (fun (x : M) ↦ TangentSpace% x)]
    (hW : ∀ {Z : (x : M) → TangentSpace% x}
      (hZ : CMDiff k (T% Z)), CMDiff k (fun x ↦ ⟪W x, Z x⟫)) :
    CMDiff k (T% W) := by
  intro x
  apply contMDiffAt_of_inner
  intro Z₀ hZ₀
  -- TODO: right now, our extension construction is not strong enough
  let Z := FiberBundle.extend E (Z₀ x)
  -- this needs a different argument, to get away with something weaker
  have scifi : CMDiff k(T% Z) := sorry
  -- this also needs an upgraded construction
  have scifi2 : Z₀ =ᶠ[nhds x] Z := sorry
  apply (hW scifi x).congr_of_eventuallyEq <| scifi2.mono (by grind)

variable {I} in
/-- A vector field on a Riemannian manifold `(M, g)` is `C^n` if and only if its pairing
with any `C^n` vector field is `C^n`.
This version assumes `M` is a `C^{n+1}`-manifold with a `C^n` metric. -/
lemma contMDiff_iff_inner (k : ℕ∞) {W : (x : M) → TangentSpace% x} [FiniteDimensional ℝ E]
    [IsManifold I k M] [IsManifold I (k + 1) M]
    [IsContMDiffRiemannianBundle I k E (fun (x : M) ↦ TangentSpace% x)] :
    CMDiff k (T% W) ↔
      ∀ {Z : (x : M) → TangentSpace% x}
        (_hZ : CMDiff k (T% Z)), CMDiff k (fun x ↦ ⟪W x, Z x⟫) :=
  ⟨fun h _Z hZ ↦ ContMDiff.inner_bundle' h hZ, fun h ↦ contMDiff_of_inner k h⟩

-- Straightforward version, but sufficient in practice??
variable {I} in
lemma contMDiff_of_contMDiffAt_inner (k : ℕ∞) {W : (x : M) → TangentSpace% x}
    [FiniteDimensional ℝ E] [IsManifold I k M] [IsManifold I (k + 1) M]
    [IsContMDiffRiemannianBundle I k E (fun (x : M) ↦ TangentSpace% x)]
    (hW : ∀ {x : M} {Z : (x : M) → TangentSpace% x}
      (_hZ : CMDiffAt k (T% Z) x), CMDiffAt k (fun x ↦ ⟪W x, Z x⟫) x) :
    CMDiff k (T% W) := by
  intro x
  apply contMDiffAt_of_inner
  intro Z₀ hZ₀
  exact hW hZ₀

/-- If `M` is endowed with a `C^k` metric, its Levi-Civita connection is a `C^k` connection. -/
instance leviCivitaConnection_foo [FiniteDimensional ℝ E] :
    ContMDiffCovariantDerivative (leviCivitaConnection I M) 1 where
  contMDiff := by
    have : IsManifold I (↑0 + 2) M := by simpa only [zero_add]
    have : IsContMDiffRiemannianBundle I (↑0 + 1) E (fun (x : M) ↦ TangentSpace% x) := by
      simpa only [zero_add]
    refine ⟨fun {σ} hσ ↦ ?_⟩
    rw [contMDiffOn_univ] at hσ ⊢
    apply ContMDiff.clm_bundle_of_apply
    intro τ hτ
    apply step2 0 (fun {Z} hZ ↦ ?_)
    exact contMDiff_leviCivitaConnection_apply 0 hτ (hσ.of_le (by simp)) hZ

section

variable {k : ℕ∞}
  [IsContMDiffRiemannianBundle I (k + 1) E (fun (x : M) ↦ TangentSpace% x)] [IsManifold I (k + 2) M]

/-- If `M` is `C^{k+2}` and endowed with a `C^{k+1}` metric,
its Levi-Civita connection is a `C^k` connection. -/
instance leviCivitaConnection_bar [FiniteDimensional ℝ E] :
    ContMDiffCovariantDerivative (leviCivitaConnection I M) (k + 1) where
  contMDiff := by
    refine ⟨fun {σ} hσ ↦ ?_⟩
    rw [contMDiffOn_univ] at hσ ⊢
    apply ContMDiff.clm_bundle_of_apply
    intro τ hτ
    apply step2 k (fun {Z} hZ ↦ ?_)
    exact contMDiff_leviCivitaConnection_apply k hτ (hσ.of_le (by simp)) hZ

end

end existence

end CovariantDerivative
