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

To be continued and polished!

This file defines the Levi-Civita connection on a (finite-dimensional) Riemannian manifold `(M, g)`.
connection `∇` on the tangent bundle of a Riemannian manifold `(M, g)` is called a
*Levi-Civita connection* if and only if it is both compatible with the metric `g` and torsion-free.
Any two such connections are equal (on differentiable vector fields), which is why one speaks of
*the* Levi-Civita connection on `TM`.
We construct a Levi-Civita connection and prove that is defines a compatible torsion-free
connection.


## Main definitions and results

* `CovariantDerivative.IsLeviCivitaConnection`: a covariant derivative `∇` on `(M, g)` is a
  Levi-Civita connection if and only if it is both torsion-free and compatible with `g`

* `CovariantDerivative.IsLeviCivitaConnection.uniqueness`: a Levi-Civita connection on `(M, g)` is
  uniquely determined on differentiable vector fields.

* `CovariantDerivative.LeviCivitaConnection`: a choice of Levi-Civita connection on the tangent
  bundle `TM` of a Riemannian manifold `(M, g)`: this is unique up to the value on
  non-differentiable vector fields.
  If you know the Levi-Civita connection already, you can use `IsLeviCivitaConnection` instead.
* `CovariantDerivative.leviCivitaConnection_isLeviCivitaConnection`:
  `LeviCivitaConnection` is a Levi-Civita connection (i.e., compatible and torsion-free)

## Implementation notes
* construction of LC using a tensoriality argument, and the musical isomorphism
  (avoids the use of local frames and trivialisations)

-/

open Bundle FiberBundle Function NormedSpace VectorField

open scoped Manifold ContDiff

-- Let `(M, g)` be a `C^k` real manifold modeled on `(E, H)`, endowed with a Riemannian metric `g`.
variable {n : WithTop ℕ∞}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I 2 M]

-- move this
lemma injective_eval_vectorField (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (x : M) :
    Function.Injective
      (fun A : TangentSpace I x →L[ℝ] V ↦
        fun (Z : Π x, TangentSpace I x) (_ : MDiffAt (T% Z) x) ↦ A (Z x)) :=
  VectorBundle.injective_eval_sec ..

variable
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  {X X' X'' Y Y' Y'' Z Z' : Π x : M, TangentSpace I x}

-- move this, also perhaps generalize to general Riemannian vector bundles
lemma injective_inner_vectorField [CompleteSpace E] (x : M) :
    Function.Injective
      (fun X₀ : TangentSpace I x ↦
        fun (Z : Π x, TangentSpace I x) (_ : MDiffAt (T% Z) x) ↦ inner ℝ X₀ (Z x)) := by
  let e := VectorBundle.continuousLinearEquivAt ℝ E (TangentSpace I) x
  have : CompleteSpace (TangentSpace I x) := by
    rw [completeSpace_congr (e := e.toEquiv) e.isUniformEmbedding]
    infer_instance
  set Φ := InnerProductSpace.toDual ℝ (TangentSpace I x)
  exact (injective_eval_vectorField I ℝ x).comp Φ.injective

namespace CovariantDerivative

-- Let `cov` be a covariant derivative on `TM`.
variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))

/-- Local notation for a connection. Caution: `∇ Y, X` corresponds to `∇ₓ Y` in textbooks -/
local notation "∇" Y "," X => fun (x:M) ↦ cov Y x (X x)

variable [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]

/-- A covariant derivative on a Riemannian bundle `TM` is called the **Levi-Civita connection**
iff it is torsion-free and compatible with `g`.
Note that the bundle metric on `TM` is implicitly hidden in this definition. See `TODO` for a
version depending on a choice of Riemannian metric on `M`.
-/
@[expose] public def IsLeviCivitaConnection [FiniteDimensional ℝ E] : Prop :=
  cov.IsCompatible ∧ cov.torsion = 0

local notation "⟪" X ", " Y "⟫" => fun x ↦ inner ℝ (X x) (Y x)

/- TODO: writing `hσ.inner_bundle hτ` or writing `by apply MDifferentiable.inner_bundle hσ hτ`
yields an error
synthesized type class instance is not definitionally equal to expression inferred by typing rules,
synthesized
  fun x ↦ instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal x
inferred
  fun b ↦ inst✝⁷
Diagnose and fix this, and then replace the below by `MDifferentiable(At).inner_bundle! -/

variable {I} in
lemma _root_.MDifferentiable.inner_bundle' {X Y : Π x : M, TangentSpace I x}
    (hX : MDiff (T% X)) (hY : MDiff (T% Y)) : MDiff ⟪X, Y⟫ :=
  MDifferentiable.inner_bundle hX hY

variable {I} in
lemma _root_.MDifferentiableAt.inner_bundle' {x : M} {X Y : Π x : M, TangentSpace I x}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    MDiffAt ⟪X, Y⟫ x :=
  MDifferentiableAt.inner_bundle hX hY

variable (X Y Z) in
/-- The first term in the definition of the candidate Levi-Civita connection:
`rhs_aux I X Y Z = X ⟨Y, Z⟩ = x ↦ d(⟨Y, Z⟩)_x (X x)`.

This definition contains mild defeq abuse, which is invisible on paper:
The function `⟨Y, Z⟩` maps `M` into `ℝ`, hence its differential at a point `x` maps `T_p M`
to an element of the tangent space of `ℝ` --- as a summand `⟨Y, [X, Z]⟩` yields an honest
real number, we apply the identification of the real numbers' tangent space with itself.
-/
noncomputable abbrev rhs_aux : M → ℝ := fun x ↦ mvfderiv% ⟪Y, Z⟫ x (X x)

section rhs_aux

variable (Y Z) in
omit [IsManifold I 2 M] in
lemma rhs_aux_swap : rhs_aux I X Y Z = rhs_aux I X Z Y := by
  ext x
  unfold rhs_aux
  simp [real_inner_comm]

omit [IsManifold I 2 M] in
variable (X X' Y Z) in
lemma rhs_aux_addX_apply {x : M} :
    rhs_aux I (X + X') Y Z x = rhs_aux I X Y Z x + rhs_aux I X' Y Z x := by
  simp [rhs_aux]

variable {x : M}

variable (X) in
@[simp]
lemma rhs_aux_addY_apply (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x) (hZ : MDiffAt (T% Z) x) :
    rhs_aux I X (Y + Y') Z x = rhs_aux I X Y Z x + rhs_aux I X Y' Z x := by
  simp [rhs_aux, inner_add_left, mvfderiv_fun_add (hY.inner_bundle' hZ) (hY'.inner_bundle' hZ)]

variable (X) in
@[simp]
lemma rhs_aux_addZ_apply (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) (hZ' : MDiffAt (T% Z') x) :
    rhs_aux I X Y (Z + Z') x = rhs_aux I X Y Z x + rhs_aux I X Y Z' x := by
  simp [rhs_aux, inner_add_right, mvfderiv_fun_add (hY.inner_bundle' hZ) (hY.inner_bundle' hZ')]

omit [IsManifold I 2 M] in
variable (X Y Z) in
lemma rhs_aux_smulX_apply (f : M → ℝ) (x) : rhs_aux I (f • X) Y Z x = f x * rhs_aux I X Y Z x := by
  simp [rhs_aux]

variable (X) in
lemma rhs_aux_smulY_apply {f : M → ℝ}
    (hf : MDiffAt f x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    letI A (x) := ((mvfderiv% f x) (X x))
    rhs_aux I X (f • Y) Z x = f x * rhs_aux I X Y Z x + A x * ⟪Y, Z⟫ x := by
  simp [rhs_aux, inner_smul_left, mvfderiv_fun_mul hf (hY.inner_bundle' hZ)]
  ring

variable (X) in
lemma rhs_aux_smulZ_apply {f : M → ℝ}
    (hf : MDiffAt f x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    letI A (x) := ((mvfderiv% f x) (X x))
    rhs_aux I X Y (f • Z) x = f x * rhs_aux I X Y Z x + A x * ⟪Y, Z⟫ x := by
  rw [rhs_aux_swap, rhs_aux_smulY_apply, rhs_aux_swap]
  · simp_rw [real_inner_comm]
  exacts [hf, hZ, hY]

end rhs_aux

variable {x : M}

variable (X Y Z) in
/-- Auxiliary quantity used in the uniqueness proof of the Levi-Civita connection:
If `∇` is a Levi-Civita connection on `TM`, then
`⟨∇ X Y, Z⟩ = leviCivitaRhs I X Y Z` for all smooth vector fields `X`, `Y` and `Z`. -/
public noncomputable def leviCivitaRhs : M → ℝ :=
  letI leviCivitaRhs' :=
    rhs_aux I X Y Z + rhs_aux I Y Z X - rhs_aux I Z X Y
    - ⟪Y ,(VectorField.mlieBracket I X Z)⟫
    - ⟪Z, (VectorField.mlieBracket I Y X)⟫
    + ⟪X, (VectorField.mlieBracket I Z Y)⟫
  (1 / 2 : ℝ) • leviCivitaRhs'

section leviCivitaRhs

@[simp]
public lemma leviCivitaRhs_addX_apply [CompleteSpace E]
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    leviCivitaRhs I (X + X') Y Z x =
      leviCivitaRhs I X Y Z x + leviCivitaRhs I X' Y Z x := by
  simp (disch := assumption) [leviCivitaRhs,
    mlieBracket_add_right, mlieBracket_add_left,
    rhs_aux_addX_apply, rhs_aux_addY_apply, rhs_aux_addZ_apply,
    inner_add_left, inner_add_right]
  ring

variable {I} in
public lemma leviCivitaRhs_smulX_apply [CompleteSpace E] {f : M → ℝ}
    (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    leviCivitaRhs I (f • X) Y Z x = f x * leviCivitaRhs I X Y Z x := by
  simp (disch := assumption) [leviCivitaRhs,
    rhs_aux_smulX_apply, rhs_aux_smulY_apply, rhs_aux_smulZ_apply,
    mlieBracket_smul_left, mlieBracket_smul_right,
    inner_add_right, inner_smul_left, inner_smul_right, real_inner_comm]
  ring

public lemma leviCivitaRhs_addY_apply [CompleteSpace E]
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hY' : MDiffAt (T% Y') x) (hZ : MDiffAt (T% Z) x) :
    leviCivitaRhs I X (Y + Y') Z x = leviCivitaRhs I X Y Z x + leviCivitaRhs I X Y' Z x := by
  simp (disch := assumption) [leviCivitaRhs,
    rhs_aux_addX_apply, rhs_aux_addY_apply, rhs_aux_addZ_apply,
    mlieBracket_add_left, mlieBracket_add_right,
    inner_add_left, inner_add_right]
  ring

public lemma leviCivitaRhs_smulY_apply [CompleteSpace E] {f : M → ℝ}
    (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    leviCivitaRhs I X (f • Y) Z x =
      f x * leviCivitaRhs I X Y Z x + mvfderiv% f x (X x) * ⟪Y, Z⟫ x := by
  simp (disch := assumption) [leviCivitaRhs,
    mlieBracket_smul_left, mlieBracket_smul_right,
    rhs_aux_smulX_apply, rhs_aux_smulY_apply, rhs_aux_smulZ_apply,
    inner_smul_left, inner_add_right, inner_smul_right, real_inner_comm]
  ring

public lemma leviCivitaRhs_addZ_apply [CompleteSpace E]
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) (hZ' : MDiffAt (T% Z') x) :
    leviCivitaRhs I X Y (Z + Z') x =
      leviCivitaRhs I X Y Z x + leviCivitaRhs I X Y Z' x := by
  simp (disch := assumption) [leviCivitaRhs,
    mlieBracket_add_right, mlieBracket_add_left,
    rhs_aux_addX_apply, rhs_aux_addY_apply, rhs_aux_addZ_apply,
    inner_add_left, inner_add_right]
  ring

public lemma leviCivitaRhs_smulZ_apply [CompleteSpace E] {f : M → ℝ}
    (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    leviCivitaRhs I X Y (f • Z) x = f x * leviCivitaRhs I X Y Z x := by
  simp (disch := assumption) [leviCivitaRhs,
    mlieBracket_smul_right, mlieBracket_smul_left,
    rhs_aux_smulX_apply, rhs_aux_smulY_apply, rhs_aux_smulZ_apply,
    inner_smul_left, inner_smul_right, inner_add_right, real_inner_comm]
  ring

end leviCivitaRhs

variable [FiniteDimensional ℝ E] in
lemma aux (h : cov.IsLeviCivitaConnection)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    rhs_aux I X Y Z x = ⟪∇ Y, X, Z⟫ x + ⟪Y, ∇ X, Z⟫ x + ⟪Y, VectorField.mlieBracket I X Z⟫ x := by
  trans ⟪∇ Y, X, Z⟫ x + ⟪Y, ∇ Z, X⟫ x
  · exact cov.isCompatible_iff.mp h.1 hX hY hZ
  · simp [← cov.torsion_eq_zero_iff.mp h.2 hX hZ, inner_sub_right]

variable {cov} in
/-- Auxiliary lemma towards the uniquness of the Levi-Civita connection: expressing the term
`⟨∇ X Y, Z⟩` for all differentiable vector fields `X`, `Y` and `Z`, without reference to `∇`. -/
public lemma IsLeviCivitaConnection.eq_leviCivitaRhs [FiniteDimensional ℝ E]
    (h : cov.IsLeviCivitaConnection)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    ⟪∇ Y, X, Z⟫ x = leviCivitaRhs I X Y Z x := by
  have eq1 := aux I cov h hX hY hZ
  have eq2 := aux I cov h hY hZ hX
  have eq3 := aux I cov h hZ hX hY
  simp [leviCivitaRhs, real_inner_comm] at *
  linear_combination - (eq1 + eq2 - eq3) / 2

section

/-- The Levi-Civita connection on `(M, g)` is uniquely determined
on differentiable vector fields.
Note that the differentiability hypotheses are required, as the Lie bracket summand in the
definition of the Levi-Civita connection is only additive for differentiable vector fields. -/
public theorem IsLeviCivitaConnection.uniqueness [FiniteDimensional ℝ E]
    {cov cov' : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (hcov : cov.IsLeviCivitaConnection) (hcov' : cov'.IsLeviCivitaConnection)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    cov Y x (X x) = cov' Y x (X x) := by
  apply injective_inner_vectorField
  ext Z hZ
  trans leviCivitaRhs I X Y Z x
  · rw [← hcov.eq_leviCivitaRhs I hX hY hZ]
  · rw [← hcov'.eq_leviCivitaRhs I hX hY hZ]

theorem leviCivitaRhs_tensorial₁ [FiniteDimensional ℝ E]
    {Y : Π x : M, TangentSpace I x} (x : M) (hY : MDiffAt (T% Y) x) {Z : Π x, TangentSpace I x}
    (hZ : MDiffAt (T% Z) x) :
    TensorialAt I E (leviCivitaRhs I · Y Z x) x where
  smul {f X} hf hX := by
    · exact leviCivitaRhs_smulX_apply hf hX hY hZ
  add hX₁ hX₂ := by
    · exact leviCivitaRhs_addX_apply I hX₁ hX₂ hY hZ

theorem leviCivitaRhs_tensorial₂ [FiniteDimensional ℝ E]
    {Y : Π x : M, TangentSpace I x} (x : M) (hY : MDiffAt (T% Y) x) {X : Π x, TangentSpace I x}
    (hX : MDiffAt (T% X) x) :
    TensorialAt I E (leviCivitaRhs I X Y · x) x where
  smul hf hZ := leviCivitaRhs_smulZ_apply I hf hX hY hZ
  add hZ₁ hZ₂ := leviCivitaRhs_addZ_apply I hX hY hZ₁ hZ₂

open scoped Classical in
/-- Auxiliary definition for the definition of the Levi-Civita connection:
this the right hand side `leviCivitaRhs`, as a `(2,0)`-tensor ?! -/
noncomputable def lcAux₀ [FiniteDimensional ℝ E]
    {Y : Π x : M, TangentSpace I x} (x : M) (hY : MDiffAt (T% Y) x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  TensorialAt.mkHom₂ _ (x := x)
    (fun _Z hZ ↦ leviCivitaRhs_tensorial₁ _ _ hY hZ)
    (fun _X hX ↦ leviCivitaRhs_tensorial₂ _ _ hY hX)

theorem lcAux₀_apply [FiniteDimensional ℝ E] {x : M}
    {X : Π x : M, TangentSpace I x} (hX : MDiffAt (T% X) x)
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x)
    {Z : Π x : M, TangentSpace I x} (hZ : MDiffAt (T% Z) x) :
    lcAux₀ I x hY (X x) (Z x) = leviCivitaRhs I X Y Z x := by
  unfold lcAux₀
  rw [TensorialAt.mkHom₂_apply _ _ hX hZ]

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
    (lcAux₀ I x hY)

set_option backward.isDefEq.respectTransparency false in
theorem lcAux₁_apply [FiniteDimensional ℝ E] {x : M}
    {X : Π x : M, TangentSpace I x} (hX : MDiffAt (T% X) x)
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x)
    {Z : Π x : M, TangentSpace I x} (hZ : MDiffAt (T% Z) x) :
    inner ℝ (lcAux₁ I x hY (X x)) (Z x) = leviCivitaRhs I X Y Z x := by
  simpa [lcAux₁] using lcAux₀_apply I hX hY hZ

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
    inner ℝ (lcAux I Y x (X x)) (Z x) = leviCivitaRhs I X Y Z x := by
  simpa [lcAux, dif_pos hY] using lcAux₁_apply I hX hY hZ

set_option backward.isDefEq.respectTransparency false in
lemma isCovariantDerivativeOn_lcAux [FiniteDimensional ℝ E] :
    IsCovariantDerivativeOn E (lcAux I (M := M)) where
  add {Y Y'} x hY hY' _ := by
    apply injective_eval_vectorField
    ext X hX
    apply injective_inner_vectorField
    ext Z hZ
    unfold lcAux
    rw [dif_pos hY, dif_pos hY', dif_pos (mdifferentiableAt_add_section hY hY')]
    simp (disch := assumption) [TensorialAt.mkHom₂_apply, lcAux₁, lcAux₀,
      leviCivitaRhs_addY_apply, inner_add_left]
  leibniz {Y f x} hY hf _ := by
    apply injective_eval_vectorField
    ext X hX
    apply injective_inner_vectorField
    ext Z hZ
    unfold lcAux
    rw [dif_pos hY, dif_pos]
    · simp (disch := assumption) [lcAux₁, lcAux₀, TensorialAt.mkHom₂_apply, inner_add_left,
        inner_smul_left, leviCivitaRhs_smulY_apply]
    exact hf.smul_section hY

end

-- TODO: make g part of the notation!
variable (M) in
/-- A choice of Levi-Civita connection on the tangent bundle `TM` of a Riemannian manifold `(M, g)`:
this is unique up to the value on non-differentiable vector fields.
If you know the Levi-Civita connection already, you can use `IsLeviCivitaConnection` instead. -/
public noncomputable def LeviCivitaConnection [FiniteDimensional ℝ E] :
    CovariantDerivative I E (TangentSpace I : M → Type _) where
  toFun := lcAux I
  isCovariantDerivativeOnUniv := isCovariantDerivativeOn_lcAux I

public theorem leviCivitaConnection_apply [FiniteDimensional ℝ E] {x : M}
    {X : Π x : M, TangentSpace I x} (hX : MDiffAt (T% X) x)
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x)
    {Z : Π x : M, TangentSpace I x} (hZ : MDiffAt (T% Z) x) :
    inner ℝ (LeviCivitaConnection I M Y x (X x)) (Z x) = leviCivitaRhs I X Y Z x :=
  lcAux_apply _ hX hY hZ

-- Why is everything so slow?
public lemma leviCivitaConnection_isCompatible [FiniteDimensional ℝ E] :
    (LeviCivitaConnection I M).IsCompatible := by
  rw [isCompatible_iff]
  intro x X Y Z hX hY hZ
  -- Normalise the expressions by swapping arguments for rhs_aux and mlieBracket,
  -- until the swappable arguments are in order X < Y < Z.
  simp (disch := assumption) [leviCivitaConnection_apply, leviCivitaRhs,
    real_inner_comm _ (Y x),
    rhs_aux_swap I Z Y, rhs_aux_swap I Z X, rhs_aux_swap I Y X,
    mlieBracket_swap (V := Z) (W := Y),
    mlieBracket_swap (V := Y) (W := X),
    mlieBracket_swap (V := Z) (W := X)]
  -- Observe that the right hand side is `rhx_aux X Y Z`;
  -- then we just need to simplify and rearrange.
  ring

public lemma leviCivitaConnection_torsion_eq_zero [FiniteDimensional ℝ E] :
    (LeviCivitaConnection I M).torsion = 0 := by
  rw [CovariantDerivative.torsion_eq_zero_iff]
  intro X Y x hX hY
  apply injective_inner_vectorField
  ext Z hZ
  simp (disch := assumption) [leviCivitaConnection_apply I, leviCivitaRhs,
    mlieBracket_swap (V := Y) (W := X), mlieBracket_swap (V := Z) (W := X),
    mlieBracket_swap (V := Z) (W := Y),
    rhs_aux_swap (Y := Z), rhs_aux_swap (X := Z),
    real_inner_comm, inner_sub_left]
  ring

/-- `LeviCivitaConnection` is a Levi-Civita connection (i.e., compatible and torsion-free) -/
public lemma leviCivitaConnection_isLeviCivitaConnection [FiniteDimensional ℝ E] :
    (LeviCivitaConnection I M).IsLeviCivitaConnection :=
  ⟨leviCivitaConnection_isCompatible I, leviCivitaConnection_torsion_eq_zero I⟩

end CovariantDerivative
