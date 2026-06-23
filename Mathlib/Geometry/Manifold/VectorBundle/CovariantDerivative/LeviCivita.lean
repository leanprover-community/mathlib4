/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang, Heather Macbeth
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

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

-- Let `M` be a `C²` manifold modeled on `(E, H)`.
variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)

variable {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I 2 M]

-- From now on, `M` is endowed with a Riemannian metric.
variable
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  {X X' X'' Y Y' Y'' Z Z' : Π x : M, TangentSpace I x}

open scoped RealInnerProductSpace

-- move this, and think whether it could be more general
-- Note that Mathlib/Topology/FiberBundle/Basic.lean has a lot of similar lemmas but far from enough
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
      (fun X₀ : TangentSpace I x ↦
        fun (Z : Π x, TangentSpace I x) (_ : MDiffAt (T% Z) x) ↦ (⟪X₀, Z x⟫)) := by
  have := VectorBundle.completeSpace ℝ (TangentSpace I (M := M)) E
  set Φ := InnerProductSpace.toDual ℝ (TangentSpace I x)
  exact (injective_eval_mdifferentiableAt_vectorField I ℝ x).comp Φ.injective

-- Let `cov` and `cov'` be covariant derivatives on `TM`.
variable (cov cov' : CovariantDerivative I E (TangentSpace I : M → Type _))

/-- Local notation for a covariant derivative on a vector bundle acting on a vector field and a
section. -/
local syntax:max "∇" term:arg term:arg : term
local macro_rules | `(∇ $X $σ) => `(fun (x : M) ↦ cov $σ x ($X x))
local syntax:max "∇'" term:arg term:arg : term
local macro_rules | `(∇' $X $σ) => `(fun (x : M) ↦ cov' $σ x ($X x))

-- From now on, we assume the Riemannian metric on `M` is `C¹`.
variable [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]

-- Local notation for pointwise inner products of vector fields.
-- Note this does not cause ambiguity with the notation obtained
-- with `open scoped RealInnerProductSpace.`
local notation "⟪" X ", " Y "⟫" => fun x ↦ inner ℝ (X x) (Y x)

/- TODO: The next two lemmas are workarounds for some version of https://github.com/leanprover/lean4/issues/9077
(Instance synthesis sees through type synonyms).
They should be removed when that issue will be fully solved. -/

variable {I} in
@[fun_prop] lemma _root_.MDifferentiable.inner_bundle' {X Y : Π x : M, TangentSpace I x}
    (hX : MDiff (T% X)) (hY : MDiff (T% Y)) : MDiff ⟪X, Y⟫ :=
  MDifferentiable.inner_bundle hX hY

variable {I} in
@[fun_prop] lemma _root_.MDifferentiableAt.inner_bundle' {x : M} {X Y : Π x : M, TangentSpace I x}
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

variable {cov cov'}

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

/-- The Levi-Civita connection on `(M, g)` is uniquely determined on differentiable vector fields.

Note that the differentiability hypotheses are required, since `CovariantDerivative` objects are
unconstrained in their behaviour on non-differentiable vector fields. -/
public theorem IsLeviCivitaConnection.uniqueness [FiniteDimensional ℝ E]
    (hcov : cov.IsLeviCivitaConnection) (hcov' : cov'.IsLeviCivitaConnection)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    ∇ X Y x = ∇' X Y x := by
  apply injective_inner_mdifferentiableAt_vectorField; ext Z hZ
  exact (hcov.apply_eq I hX hY hZ).trans <| hcov'.apply_eq I hX hY hZ |>.symm

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
    {Y : Π x : M, TangentSpace I x} (x : M) (hY : MDiffAt (T% Y) x) {Z : Π x, TangentSpace I x}
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
    {Y : Π x : M, TangentSpace I x} (x : M) (hY : MDiffAt (T% Y) x) {X : Π x, TangentSpace I x}
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
    {Y : Π x : M, TangentSpace I x} (x : M) (hY : MDiffAt (T% Y) x) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  -- Use the musical isomorphism to produce a candidate `∇ Y` as a `(1,1)`-tensor
  -- (rather than a `2`-tensor).
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  have : CompleteSpace (TangentSpace I x) := FiniteDimensional.complete ℝ _
  (InnerProductSpace.toDual ℝ _).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (TensorialAt.mkHom₂ _ (x := x)
      (fun _Z hZ ↦ leviCivitaAux_tensorial₁ _ _ hY hZ)
      (fun _X hX ↦ leviCivitaAux_tensorial₂ _ _ hY hX))

set_option backward.isDefEq.respectTransparency false in
theorem lcAux₁_apply [FiniteDimensional ℝ E] {x : M}
    {X : Π x : M, TangentSpace I x} (hX : MDiffAt (T% X) x)
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x)
    {Z : Π x : M, TangentSpace I x} (hZ : MDiffAt (T% Z) x) :
    ⟪lcAux₁ I x hY (X x), Z x⟫ = leviCivitaAux I X Y Z x := by
  unfold lcAux₁
  simp [TensorialAt.mkHom₂_apply _ _ hX hZ]

open scoped Classical in
/-- The function underlying our construction of the Levi-Civita connection on `(M,g)` -/
noncomputable def lcAux [FiniteDimensional ℝ E]
    (Y : Π x : M, TangentSpace I x) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  if hY : MDiffAt (T% Y) x then lcAux₁ I x hY else 0

theorem lcAux_apply [FiniteDimensional ℝ E] {x : M}
    {X : Π x : M, TangentSpace I x} (hX : MDiffAt (T% X) x)
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x)
    {Z : Π x : M, TangentSpace I x} (hZ : MDiffAt (T% Z) x) :
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
    {X : Π x : M, TangentSpace I x} (hX : MDiffAt (T% X) x)
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x)
    {Z : Π x : M, TangentSpace I x} (hZ : MDiffAt (T% Z) x) :
    ⟪leviCivitaConnection I M Y x (X x), Z x⟫ =
      (d% ⟪Y, Z⟫ x (X x) + d% ⟪Z, X⟫ x (Y x) - d% ⟪X, Y⟫ x (Z x)
      - ⟪Y, VectorField.mlieBracket I X Z⟫ x
      - ⟪Z, VectorField.mlieBracket I Y X⟫ x
      + ⟪X, VectorField.mlieBracket I Z Y⟫ x) / 2 :=
  lcAux_apply _ hX hY hZ

public theorem leviCivitaConnection_apply_right [FiniteDimensional ℝ E] {x : M}
    {X : Π x : M, TangentSpace I x} (hX : MDiffAt (T% X) x)
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x)
    {Z : Π x : M, TangentSpace I x} (hZ : MDiffAt (T% Z) x) :
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

end existence

end CovariantDerivative
