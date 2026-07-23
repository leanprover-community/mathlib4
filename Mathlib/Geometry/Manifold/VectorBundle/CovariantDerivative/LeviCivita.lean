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

Mathematically, there are two main approaches to this construction.
The first one notes that the uniqueness proof provides an expression (the Koszul formula) for the
Levi-Civita connection, so can be used to define a connection. This passage, however, involves an
auxiliary choice (say, of a local frame near each point), and requires proving independence of this
choice. For this reason, we use a different argument, using the so-called *musical isomorphism*.

A Riemannian metric `g` on `M` induces so-called **musical isomorphisms** between the tangent and
cotangent bundles of `M` (and, more generally, tensor fields of orders `(k+d, l)` and `(k, l+d)`
for `k, l, d : ℕ`), by associating to a tangent vector `X \in T_pM` the cotangent vector `g(X, ·)`.
Non-degeneracy of the metric `g` implies that this induces an isomorphism `T_pM → (T_pM)*` at each
point, which combines to a bundle isomorphism `TM → T*M`.
Similarly, a `(2,0)`-tensor (i.e., a map `T_pM × T_pM → ℝ` at each point) induces a `(1,1)`-tensor
(i.e., a map `T_pM → (T_pM)*` at each point).
We apply this to the `(2,0)`-tensor `(X, Z) ↦ ∇ X Y Z p`, to obtain a `(1,1)`-tensor `∇ Y`.


## Main definitions and results

* `CovariantDerivative.IsLeviCivitaConnection`: a covariant derivative `∇` on `(M, g)` is a
  Levi-Civita connection if and only if it is both torsion-free and compatible with `g`

* `CovariantDerivative.IsLeviCivitaConnection.uniqueness`: a Levi-Civita connection on `(M, g)` is
  uniquely determined on differentiable vector fields (this is known as the **Koszul formula**).

* `CovariantDerivative.leviCivitaConnection`: a choice of Levi-Civita connection on the tangent
  bundle `TM` of a Riemannian manifold `(M, g)`: this is unique up to the value on
  non-differentiable vector fields.
  If you know the Levi-Civita connection already, you can use `IsLeviCivitaConnection` instead.

* `CovariantDerivative.leviCivitaConnection_isLeviCivitaConnection`:
  `leviCivitaConnection` is a Levi-Civita connection (i.e., compatible and torsion-free)

## Implementation notes

* construction of LC using a tensoriality argument, and the musical isomorphism
  (avoids the use of local frames and trivialisations)

## Tags

Levi-Civita connection, metric, torsion-free, Koszul formula, musical isomorphism

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

-- More injectivity-like lemmas on Riemannian vector bundles.
section ext

open scoped RealInnerProductSpace

section

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)] [FiberBundle F E]

variable (IB F E) in
/-- A vector in `E x` is uniquely determined by its scalar product with sections that
are differentiable at `x` -/
public lemma injective_inner_mdifferentiableAt_section  (x : B) :
    Function.Injective
      (fun X₀ : E x ↦
        fun (Z : Π x, E x) (_ : MDiffAt (T% Z) x) ↦ (⟪X₀, Z x⟫)) := by
  intro X₀ Y₀ h
  suffices ⟪X₀, X₀ - Y₀⟫ = ⟪Y₀, X₀ - Y₀⟫ by
    rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℝ), inner_sub_left, sub_eq_zero]
    exact this
  simpa using congr($h _ (mdifferentiableAt_extend _ _ (X₀ - Y₀)))

variable (IB F E) in
/-- A vector in `E x` is uniquely determined by its scalar product with sections that
are `C^n` at `x` -/
public lemma injective_inner_contMDiffAt_section (n : ℕ∞ω) (x : B) :
    Function.Injective
      (fun X₀ : E x ↦
        fun (Z : Π x, E x) (_ : CMDiffAt n (T% Z) x) ↦ (⟪X₀, Z x⟫)) := by
  intro X₀ Y₀ h
  suffices ⟪X₀, X₀ - Y₀⟫ = ⟪Y₀, X₀ - Y₀⟫ by
    rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℝ), inner_sub_left, sub_eq_zero]
    exact this
  simpa using congr($h _ (contMDiffAt_extend _ _ (X₀ - Y₀)))

end

section -- and a specialisation to manifolds

-- Let `M` be a `C²` manifold modeled on `(E, H)`, endowed with a Riemannian metric.
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

/-- A tangent vector at `x` is uniquely determined by its scalar product with differentiable
vector fields -/
lemma injective_inner_mdifferentiableAt_vectorField (x : M) :
    Function.Injective
      (fun X₀ : TangentSpace I x ↦
        fun (Z : Π x, TangentSpace I x) (_ : MDiffAt (T% Z) x) ↦ (⟪X₀, Z x⟫)) :=
  injective_inner_mdifferentiableAt_section (E := TangentSpace I) I E x

/-- A tangent vector at `x` is uniquely determined by its scalar product with `C^n` vector fields -/
lemma injective_inner_contMDiffAt_vectorField {n : ℕ∞ω} (x : M) :
    Function.Injective
      (fun X₀ : TangentSpace I x ↦
        fun (Z : Π x, TangentSpace I x) (_ : CMDiffAt n (T% Z) x) ↦ (⟪X₀, Z x⟫)) :=
  injective_inner_contMDiffAt_section (E := TangentSpace I) I E n x

end

end ext

-- Let `M` be a `C²` manifold modeled on `(E, H)`.
variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]

-- From now on, `M` is endowed with a Riemannian metric.
variable
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  {X X' X'' Y Y' Y'' Z Z' : Π x : M, TangentSpace I x}

open scoped RealInnerProductSpace

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
-- with `open scoped RealInnerProductSpace`.
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
public structure IsLeviCivitaConnection [FiniteDimensional ℝ E] : Prop where
  isMetricCompatible : cov.IsMetricCompatible (M := M) (V := TangentSpace I)
  torsion : cov.torsion = 0

section uniqueness

variable {cov cov'}

/-- Auxiliary lemma towards the uniqueness of the Levi-Civita connection: expressing the term
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
  have eq1a := h.isMetricCompatible.mvfderiv_inner_eq X hY hZ
  have eq2a := h.isMetricCompatible.mvfderiv_inner_eq Y hZ hX
  have eq3a := h.isMetricCompatible.mvfderiv_inner_eq Z hX hY
  -- use the torsion-freeness in three ways
  have eq1b := congr(inner ℝ (Y x) ($(h.2) x (X x) (Z x)))
  have eq2b := congr(inner ℝ (Z x) ($(h.2) x (Y x) (X x)))
  have eq3b := congr(inner ℝ (X x) ($(h.2) x (Z x) (Y x)))
  -- combine
  simp (disch := fun_prop) [real_inner_comm, inner_sub_right, torsion_apply] at *
  linear_combination - (eq1a + eq1b + eq2a + eq2b - eq3a - eq3b) / 2

/-- Auxiliary lemma towards the uniqueness of the Levi-Civita connection: expressing the term
`⟨∇ X Y, Z⟩` for all differentiable vector fields `Y` and `Z`, without reference to `∇`.

Version of `IsLeviCivitaConnection.apply_eq` which does not require the vector field we are
differentiating to be differentiable. -/
public lemma IsLeviCivitaConnection.apply_eq_extend [FiniteDimensional ℝ E]
    (h : cov.IsLeviCivitaConnection) {x : M}
    (X₀ : TangentSpace I x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    inner ℝ (cov Y x X₀) (Z x) =
      (d% ⟪Y, Z⟫ x X₀ + d% ⟪Z, extend E X₀⟫ x (Y x) - d% ⟪extend E X₀, Y⟫ x (Z x)
      - ⟪Y, VectorField.mlieBracket I (extend E X₀) Z⟫ x
      - ⟪Z, VectorField.mlieBracket I Y (extend E X₀)⟫ x
      + inner ℝ X₀ (VectorField.mlieBracket I Z Y x)) / 2 := by
  nth_rw 1 [← FiberBundle.extend_apply_self E X₀]
  simp_rw [h.apply_eq _ (mdifferentiableAt_extend _ _ X₀) hY hZ]
  simp

/-- The Levi-Civita connection on `(M, g)` is uniquely determined on differentiable vector fields:
this is known as the **Koszul formula**.

Note that the differentiability hypothesis on `Y` is required, since `CovariantDerivative` objects
are unconstrained in their behaviour on non-differentiable vector fields. -/
public theorem IsLeviCivitaConnection.uniqueness [FiniteDimensional ℝ E]
    (hcov : cov.IsLeviCivitaConnection) (hcov' : cov'.IsLeviCivitaConnection)
    (hY : MDiffAt (T% Y) x) :
    cov Y x (X x) = cov' Y x (X x) := by
  apply injective_inner_mdifferentiableAt_vectorField; ext Z hZ
  exact (hcov.apply_eq_extend I (X x) hY hZ).trans <| hcov'.apply_eq_extend I (X x) hY hZ |>.symm

end uniqueness

section existence

variable (X Y Z) in
/-- Auxiliary quantity for the construction of the Levi-Civita connection:
If `∇` is the Levi-Civita connection on `TM`, this formula will express `⟨∇ X Y, Z⟩`. -/
noncomputable def leviCivitaAux₀ (x : M) : ℝ :=
  (d% ⟪Y, Z⟫ x (X x) + d% ⟪Z, X⟫ x (Y x) - d% ⟪X, Y⟫ x (Z x)
  - ⟪Y, VectorField.mlieBracket I X Z⟫ x
  - ⟪Z, VectorField.mlieBracket I Y X⟫ x
  + ⟪X, VectorField.mlieBracket I Z Y⟫ x) / 2

/-- `leviCivitaAux₀` is tensorial with respect to its first argument. -/
theorem leviCivitaAux₀_tensorial₁ [FiniteDimensional ℝ E]
    {Y : Π x : M, TangentSpace I x} (x : M) (hY : MDiffAt (T% Y) x) {Z : Π x, TangentSpace I x}
    (hZ : MDiffAt (T% Z) x) :
    TensorialAt I E (leviCivitaAux₀ I · Y Z x) x where
  smul hf hX := by
    simp (disch := fun_prop) [leviCivitaAux₀, mvfderiv_fun_mul,
      mlieBracket_smul_left, mlieBracket_smul_right,
      inner_add_right, inner_smul_left, inner_smul_right, real_inner_comm]
    ring
  add hX₁ hX₂ := by
    simp (disch := fun_prop) [leviCivitaAux₀, mlieBracket_add_right, mlieBracket_add_left,
      mvfderiv_fun_add, inner_add_left, inner_add_right]
    ring

/-- `leviCivitaAux₀` is tensorial with respect to its second argument. -/
theorem leviCivitaAux_tensorial₂ [FiniteDimensional ℝ E]
    {Y : Π x : M, TangentSpace I x} (x : M) (hY : MDiffAt (T% Y) x) {X : Π x, TangentSpace I x}
    (hX : MDiffAt (T% X) x) :
    TensorialAt I E (leviCivitaAux₀ I X Y · x) x where
  smul hf hZ := by
    simp (disch := fun_prop) [leviCivitaAux₀,
      mlieBracket_smul_right, mlieBracket_smul_left,
      mvfderiv_fun_mul,
      inner_smul_left, inner_smul_right, inner_add_right, real_inner_comm]
    ring
  add hZ₁ hZ₂ := by
    simp (disch := fun_prop) [leviCivitaAux₀,
      mlieBracket_add_right, mlieBracket_add_left,
      mvfderiv_fun_add,
      inner_add_left, inner_add_right]
    ring

/-- Almost the function underlying our construction of the Levi-Civita connection:
this is the desired `(1,1)`-tensor, but without considerations to the junk value when
applied to non-differentiable vector fields. -/
noncomputable def leviCivitaAux₁ [FiniteDimensional ℝ E]
    {Y : Π x : M, TangentSpace I x} (x : M) (hY : MDiffAt (T% Y) x) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  -- Use the musical isomorphism to produce a candidate `∇ Y` as a `(1,1)`-tensor
  -- (rather than a `2`-tensor).
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  have : CompleteSpace (TangentSpace I x) := FiniteDimensional.complete ℝ _
  (InnerProductSpace.toDual ℝ _).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (TensorialAt.mkHom₂ _ (x := x)
      (fun _Z hZ ↦ leviCivitaAux₀_tensorial₁ _ _ hY hZ)
      (fun _X hX ↦ leviCivitaAux_tensorial₂ _ _ hY hX))

theorem leviCivitaAux₁_apply_inner [FiniteDimensional ℝ E] {x : M}
    {X : Π x : M, TangentSpace I x} (hX : MDiffAt (T% X) x)
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x)
    {Z : Π x : M, TangentSpace I x} (hZ : MDiffAt (T% Z) x) :
    ⟪leviCivitaAux₁ I x hY (X x), Z x⟫ = leviCivitaAux₀ I X Y Z x := by
  unfold leviCivitaAux₁
  simp [TensorialAt.mkHom₂_apply _ _ hX hZ]

open scoped Classical in
/-- The function underlying our construction of the Levi-Civita connection on `(M,g)` -/
noncomputable def leviCivitaConnectionAux [FiniteDimensional ℝ E]
    (Y : Π x : M, TangentSpace I x) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  if hY : MDiffAt (T% Y) x then leviCivitaAux₁ I x hY else 0

theorem leviCivitaConnectionAux_apply_inner [FiniteDimensional ℝ E] {x : M}
    {X : Π x : M, TangentSpace I x} (hX : MDiffAt (T% X) x)
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x)
    {Z : Π x : M, TangentSpace I x} (hZ : MDiffAt (T% Z) x) :
    ⟪leviCivitaConnectionAux I Y x (X x), Z x⟫ = leviCivitaAux₀ I X Y Z x := by
  simpa [leviCivitaConnectionAux, dif_pos hY] using leviCivitaAux₁_apply_inner I hX hY hZ

lemma isCovariantDerivativeOn_leviCivitaConnectionAux [FiniteDimensional ℝ E] :
    IsCovariantDerivativeOn E (leviCivitaConnectionAux I (M := M)) where
  add {Y Y'} x hY hY' _ := by
    apply injective_eval_mdifferentiableAt_vectorField; ext X hX
    apply injective_inner_mdifferentiableAt_vectorField; ext Z hZ
    simp (disch := fun_prop) [leviCivitaConnectionAux, dif_pos, TensorialAt.mkHom₂_apply,
      leviCivitaAux₁, leviCivitaAux₀, mvfderiv_fun_add,
      mlieBracket_add_left, mlieBracket_add_right,
      inner_add_left, inner_add_right]
    ring
  leibniz {Y f x} hY hf _ := by
    apply injective_eval_mdifferentiableAt_vectorField; ext X hX
    apply injective_inner_mdifferentiableAt_vectorField; ext Z hZ
    simp (disch := fun_prop) [leviCivitaConnectionAux, dif_pos, leviCivitaAux₁,
      TensorialAt.mkHom₂_apply, leviCivitaAux₀, mvfderiv_fun_mul,
      mlieBracket_smul_left, mlieBracket_smul_right,
      inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, real_inner_comm]
    ring

variable (M) in
/-- A choice of Levi-Civita connection on the tangent bundle `TM` of a Riemannian manifold `(M, g)`:
this is unique up to the value on non-differentiable vector fields.
If you know the Levi-Civita connection already, you can use `IsLeviCivitaConnection` instead. -/
public noncomputable def leviCivitaConnection [FiniteDimensional ℝ E] :
    CovariantDerivative I E (TangentSpace I : M → Type _) where
  toFun := leviCivitaConnectionAux I
  isCovariantDerivativeOnUniv := isCovariantDerivativeOn_leviCivitaConnectionAux I

public theorem leviCivitaConnection_apply_inner [FiniteDimensional ℝ E] {x : M}
    {X : Π x : M, TangentSpace I x} (hX : MDiffAt (T% X) x)
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x)
    {Z : Π x : M, TangentSpace I x} (hZ : MDiffAt (T% Z) x) :
    ⟪leviCivitaConnection I M Y x (X x), Z x⟫ =
      (d% ⟪Y, Z⟫ x (X x) + d% ⟪Z, X⟫ x (Y x) - d% ⟪X, Y⟫ x (Z x)
      - ⟪Y, VectorField.mlieBracket I X Z⟫ x
      - ⟪Z, VectorField.mlieBracket I Y X⟫ x
      + ⟪X, VectorField.mlieBracket I Z Y⟫ x) / 2 :=
  leviCivitaConnectionAux_apply_inner _ hX hY hZ

public theorem leviCivitaConnection_apply_inner_right [FiniteDimensional ℝ E] {x : M}
    {X : Π x : M, TangentSpace I x} (hX : MDiffAt (T% X) x)
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x)
    {Z : Π x : M, TangentSpace I x} (hZ : MDiffAt (T% Z) x) :
    ⟪X x, leviCivitaConnection I M Y x (Z x)⟫ =
      (d% ⟪Y, X⟫ x (Z x) + d% ⟪X, Z⟫ x (Y x) - d% ⟪Z, Y⟫ x (X x)
      - ⟪Y ,VectorField.mlieBracket I Z X⟫ x
      - ⟪X, VectorField.mlieBracket I Y Z⟫ x
      + ⟪Z, VectorField.mlieBracket I X Y⟫ x) / 2 := by
  rw [real_inner_comm]
  exact leviCivitaConnectionAux_apply_inner _ hZ hY hX

public lemma isMetricCompatible_leviCivitaConnection [FiniteDimensional ℝ E] :
    (leviCivitaConnection I M).IsMetricCompatible (M := M) (V := TangentSpace I) := by
  rw [isMetricCompatible_iff]
  intro x X Y Z hX hY hZ
  -- Normalise the expressions by swapping arguments for inner product and mlieBracket,
  -- until the swappable arguments are in order X < Y < Z.
  simp (disch := fun_prop) [leviCivitaConnection_apply_inner_right,
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
  simp (disch := fun_prop) [leviCivitaConnection_apply_inner I,
    mlieBracket_swap (V := Y) (W := X), mlieBracket_swap (V := Z) (W := X),
    mlieBracket_swap (V := Z) (W := Y),
    real_inner_comm, inner_sub_left]
  ring

/-- `leviCivitaConnection` is a Levi-Civita connection (i.e., compatible and torsion-free) -/
public lemma leviCivitaConnection_isLeviCivitaConnection [FiniteDimensional ℝ E] :
    (leviCivitaConnection I M).IsLeviCivitaConnection :=
  ⟨isMetricCompatible_leviCivitaConnection I, leviCivitaConnection_torsion_eq_zero I⟩

end existence

end CovariantDerivative
