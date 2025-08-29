/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative
import Mathlib.Geometry.Manifold.VectorBundle.OrthonormalFrame
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Util.PrintSorries

/-!
# The Levi-Civita connection

This file will define the Levi-Civita connection on any Riemannian manifold.
Details to be written!

TODO: refactor this file, to make Levi-Civita take a Riemannian metric instead!


TODO: more generally, define a notion of metric connections (e.g., those whose parallel transport
is an isometry) and prove the Levi-Civita connection is a metric connection

-/

open Bundle Filter Function Module Topology

open scoped Bundle Manifold ContDiff

-- Let M be a C^k real manifold modeled on (E, H), endowed with a Riemannian metric.
variable {n : WithTop ℕ∞}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  -- don't need this assumption (yet?)
  -- [IsRiemannianManifold I M]

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-! Compatible connections: a connection on TM is compatible with the metric on M iff
`∇ X ⟨Y, Z⟩ = ⟨∇ X Y, Z⟩ + ⟨Y, ∇ X Z⟩` holds for all vector fields X, Y and Z on `M`.
The left hand side is the pushforward of the function `⟨Y, Z⟩` along the vector field `X`:
the left hand side at `X` is `df(X x)`, where `f := ⟨Y, Z⟩`. -/

variable {X X' Y Y' Z Z' : Π x : M, TangentSpace I x}

/-- The scalar product of two vector fields -/
noncomputable abbrev product (X Y : Π x : M, TangentSpace I x) : M → ℝ :=
  fun x ↦ inner ℝ (X x) (Y x)
-- Riemannian.lean shows that `product` is C^k if X and Y are

local notation "⟪" X ", " Y "⟫" => product I X Y

-- Basic API for the product of two vector fields.
section product

omit [IsManifold I ∞ M]

lemma product_apply (x) : ⟪X, Y⟫ x = inner ℝ (X x) (Y x) := rfl

variable (X Y) in
lemma product_swap : ⟪Y, X⟫ = ⟪X, Y⟫ := by
  ext x
  apply real_inner_comm

variable (X) in
@[simp]
lemma product_zero_left : ⟪0, X⟫ = 0 := by
  ext x
  simp [product]

@[simp]
lemma product_zero_right : ⟪X, 0⟫ = 0 := by rw [product_swap, product_zero_left]

variable (X X' Y) in
lemma product_add_left : ⟪X + X', Y⟫ = ⟪X, Y⟫ + ⟪X', Y⟫ := by
  ext x
  simp [product, InnerProductSpace.add_left]

variable (X X' Y) in
@[simp]
lemma product_add_left_apply (x) : ⟪X + X', Y⟫ x = ⟪X, Y⟫ x + ⟪X', Y⟫ x := by
  simp [product, InnerProductSpace.add_left]

variable (X Y Y') in
lemma product_add_right : ⟪X, Y + Y'⟫ = ⟪X, Y⟫ + ⟪X, Y'⟫ := by
  rw [product_swap, product_swap _ Y, product_swap _ Y', product_add_left]

variable (X X' Y) in
@[simp]
lemma product_add_right_apply (x) : ⟪X, Y + Y'⟫ x = ⟪X, Y⟫ x + ⟪X, Y'⟫ x := by
  rw [product_swap, product_swap _ Y, product_swap _ Y', product_add_left_apply]

variable (X Y) in
@[simp] lemma product_neg_left : ⟪-X, Y⟫ = -⟪X, Y⟫ := by ext x; simp [product]

variable (X Y) in
@[simp] lemma product_neg_right : ⟪X, -Y⟫ = -⟪X, Y⟫ := by ext x; simp [product]

variable (X X' Y) in
lemma product_sub_left : ⟪X - X', Y⟫ = ⟪X, Y⟫ - ⟪X', Y⟫ := by
  ext x
  simp [product, inner_sub_left]

variable (X Y Y') in
lemma product_sub_right : ⟪X, Y - Y'⟫ = ⟪X, Y⟫ - ⟪X, Y'⟫ := by
  ext x
  simp [product, inner_sub_right]

variable (X Y) in
lemma product_smul_left (f : M → ℝ) : product I (f • X) Y = f • product I X Y := by
  ext x
  simp [product, real_inner_smul_left]

variable (X Y) in
lemma product_smul_right (f : M → ℝ) : product I X (f • Y) = f • product I X Y := by
  ext x
  simp [product, real_inner_smul_right]

end product

set_option linter.style.commandStart false -- custom elaborators not handled well yet

/- XXX: writing `hY.inner_bundle hZ` or writing `by apply MDifferentiable.inner_bundle hY hZ`
yields an error
synthesized type class instance is not definitionally equal to expression inferred by typing rules,
synthesized
  fun x ↦ instNormedAddCommGroupOfRiemannianBundle x
inferred
  fun b ↦ inst✝⁷ -/
-- TODO: diagnose and fix this, and replace by `MDifferentiable(At).inner_bundle!

variable [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)] {I} in
lemma MDifferentiable.inner_bundle' (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) : MDiff ⟪Y, Z⟫ :=
  MDifferentiable.inner_bundle hY hZ

variable [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)] {I} in
lemma MDifferentiableAt.inner_bundle' {x} (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    MDiffAt ⟪Y, Z⟫ x :=
  MDifferentiableAt.inner_bundle hY hZ

namespace CovariantDerivative

-- Let `cov` be a covariant derivative on `TM`.
-- TODO: include in cheat sheet!
variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))

/-- Predicate saying for a connection `∇` on a Riemannian manifold `M`  to be compatible with the
ambient metric, i.e. for all smooth vector fields `X`, `Y` and `Z` on `M`, we have
`X ⟨Y, Z⟩ = ⟨∇ X Y, Z⟩ + ⟨Y, ∇ X Z⟩`. -/
def IsCompatible : Prop :=
  ∀ X Y Z : Π x : M, TangentSpace I x, -- XXX: missing differentiability hypotheses!
  ∀ x : M,
  mfderiv% ⟪Y, Z⟫ x (X x) = ⟪cov X Y, Z⟫ x + ⟪Y, cov X Z⟫ x

/-- A covariant derivative on a Riemannian bundle `TM` is called the **Levi-Civita connection**
iff it is torsion-free and compatible with `g`.
Note that the bundle metric on `TM` is implicitly hidden in this definition. See `TODO` for a
version depending on a choice of Riemannian metric on `M`.
-/
def IsLeviCivitaConnection : Prop := cov.IsCompatible ∧ cov.IsTorsionFree

variable (X Y Z) in
/-- The first term in the definition of the candidate Levi-Civita connection:
`rhs_aux I X Y Z = X ⟨Y, Z⟩ = x ↦ d(⟨Y, Z⟩)_x (X x)`.

This definition contains mild defeq abuse, which is invisible on paper:
The function `⟨Y, Z⟩` maps `M` into `ℝ`, hence its differential at a point `x` maps `T_p M`
to an element of the tangent space of `ℝ`. A summand `⟨Y, [X, Z]⟩`, however, yields an honest
real number: Lean complains that these have different types.
Fortunately, `ℝ` is defeq to its own tangent space; casting `rhs_aux` to the real numbers
allows the addition to type-check. -/
noncomputable abbrev rhs_aux : M → ℝ := fun x ↦ (mfderiv% ⟪Y, Z⟫ x (X x))

section rhs_aux

omit [IsManifold I ∞ M] in
lemma rhs_aux_swap : rhs_aux I X Y Z = rhs_aux I X Z Y := by
  ext x
  simp only [rhs_aux]
  congr
  exact product_swap I Z Y

omit [IsManifold I ∞ M] in
variable (X X' Y Z) in
lemma rhs_aux_addX : rhs_aux I (X + X') Y Z = rhs_aux I X Y Z + rhs_aux I X' Y Z := by
  ext x
  simp [rhs_aux]

variable [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)] {x}

variable (X) in
@[simp]
lemma rhs_aux_addY_apply (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x) (hZ : MDiffAt (T% Z) x) :
    rhs_aux I X (Y + Y') Z x = rhs_aux I X Y Z x + rhs_aux I X Y' Z x := by
  simp only [rhs_aux]
  rw [product_add_left, mfderiv_add (hY.inner_bundle' hZ) (hY'.inner_bundle' hZ)]
  simp; congr

variable (X) in
lemma rhs_aux_addY (hY : MDiff (T% Y)) (hY' : MDiff (T% Y')) (hZ : MDiff (T% Z)) :
    rhs_aux I X (Y + Y') Z = rhs_aux I X Y Z + rhs_aux I X Y' Z := by
  ext x
  exact rhs_aux_addY_apply I X (hY x) (hY' x) (hZ x)

variable (X) in
@[simp]
lemma rhs_aux_addZ_apply (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) (hZ' : MDiffAt (T% Z') x) :
  rhs_aux I X Y (Z + Z') x = rhs_aux I X Y Z x + rhs_aux I X Y Z' x := by
  unfold rhs_aux
  rw [product_add_right, mfderiv_add (hY.inner_bundle' hZ) (hY.inner_bundle' hZ')]; simp; congr

variable (X) in
lemma rhs_aux_addZ (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) (hZ' : MDiff (T% Z')) :
    rhs_aux I X Y (Z + Z') = rhs_aux I X Y Z + rhs_aux I X Y Z' := by
  ext x
  exact rhs_aux_addZ_apply I X (hY x) (hZ x) (hZ' x)

omit [IsManifold I ∞ M] in
variable (X Y Z) in
lemma rhs_aux_smulX (f : M → ℝ) : rhs_aux I (f • X) Y Z = f • rhs_aux I X Y Z := by
  ext x
  simp [rhs_aux]

variable (X) in
lemma rhs_aux_smulY_apply {f : M → ℝ}
    (hf : MDiffAt f x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    letI A (x) : ℝ := (mfderiv% f x) (X x)
    rhs_aux I X (f • Y) Z x = f x • rhs_aux I X Y Z x + A x • ⟪Y, Z⟫ x := by
  rw [rhs_aux, product_smul_left, mfderiv_smul (hY.inner_bundle' hZ) hf]

variable (X) in
lemma rhs_aux_smulY {f : M → ℝ} (hf : MDiff f) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) :
    letI A (x) : ℝ := (mfderiv% f x) (X x)
    rhs_aux I X (f • Y) Z = f • rhs_aux I X Y Z + A • ⟪Y, Z⟫ := by
  ext x
  simp [rhs_aux_smulY_apply I X (hf x) (hY x) (hZ x)]

variable (X) in
lemma rhs_aux_smulZ_apply {f : M → ℝ}
    (hf : MDiffAt f x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    letI A (x) : ℝ := (mfderiv% f x) (X x)
    rhs_aux I X Y (f • Z) x = f x • rhs_aux I X Y Z x + A x • ⟪Y, Z⟫ x := by
  rw [rhs_aux_swap, rhs_aux_smulY_apply, rhs_aux_swap, product_swap]
  exacts [hf, hZ, hY]

variable (X) in
lemma rhs_aux_smulZ {f : M → ℝ} (hf : MDiff f) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) :
    letI A (x) : ℝ := (mfderiv% f x) (X x)
    rhs_aux I X Y (f • Z) = f • rhs_aux I X Y Z + A • ⟪Y, Z⟫ := by
  rw [rhs_aux_swap, rhs_aux_smulY, rhs_aux_swap, product_swap]
  exacts [hf, hZ, hY]

end rhs_aux

variable {x : M}

variable (X Y Z) in
/-- Auxiliary quantity used in the uniqueness proof of the Levi-Civita connection:
If ∇ is a Levi-Civita connection on `TM`, then
`2 ⟨∇ X Y, Z⟩ = leviCivita_rhs' I X Y Z` for all vector fields `Z`. -/
noncomputable def leviCivita_rhs' : M → ℝ :=
  rhs_aux I X Y Z + rhs_aux I Y Z X - rhs_aux I Z X Y
  - ⟪Y ,(VectorField.mlieBracket I X Z)⟫
  - ⟪Z, (VectorField.mlieBracket I Y X)⟫
  + ⟪X, (VectorField.mlieBracket I Z Y)⟫

variable (X Y Z) in
/-- Auxiliary quantity used in the uniqueness proof of the Levi-Civita connection:
If `∇` is a Levi-Civita connection on `TM`, then
`⟨∇ X Y, Z⟩ = leviCivita_rhs I X Y Z` for all smooth vector fields `X`, `Y` and `Z`. -/
noncomputable def leviCivita_rhs : M → ℝ := (1 / 2 : ℝ) • leviCivita_rhs' I X Y Z

omit [IsManifold I ∞ M] in
lemma leviCivita_rhs_apply : leviCivita_rhs I X Y Z x = (1 / 2 : ℝ) • leviCivita_rhs' I X Y Z x :=
  rfl

section leviCivita_rhs

variable [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]

@[simp]
lemma leviCivita_rhs'_addX_apply [CompleteSpace E]
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    leviCivita_rhs' I (X + X') Y Z x =
      leviCivita_rhs' I X Y Z x + leviCivita_rhs' I X' Y Z x := by
  simp only [leviCivita_rhs', rhs_aux_addX, Pi.add_apply, Pi.sub_apply]
  -- We have to rewrite back and forth: the Lie bracket is only additive at x,
  -- as we are only asking for differentiability at x.
  simp_rw [product_apply, VectorField.mlieBracket_add_right (V := Y) hX hX',
    VectorField.mlieBracket_add_left (W := Z) hX hX', inner_add_right, ← product_apply,
    product_add_left_apply]
  rw [rhs_aux_addY_apply, rhs_aux_addZ_apply] <;> try assumption
  abel

lemma leviCivita_rhs'_addX [CompleteSpace E]
    (hX : MDiff (T% X)) (hX' : MDiff (T% X')) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) :
    leviCivita_rhs' I (X + X') Y Z =
      leviCivita_rhs' I X Y Z + leviCivita_rhs' I X' Y Z := by
  ext x
  simp [leviCivita_rhs'_addX_apply _ (hX x) (hX' x) (hY x) (hZ x)]

lemma leviCivita_rhs_addX_apply [CompleteSpace E]
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    leviCivita_rhs I (X + X') Y Z x = leviCivita_rhs I X Y Z x + leviCivita_rhs I X' Y Z x := by
  simp [leviCivita_rhs, leviCivita_rhs'_addX_apply I hX hX' hY hZ, left_distrib]

lemma leviCivita_rhs_addX [CompleteSpace E]
    (hX : MDiff (T% X)) (hX' : MDiff (T% X')) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) :
    leviCivita_rhs I (X + X') Y Z = leviCivita_rhs I X Y Z + leviCivita_rhs I X' Y Z := by
  ext x
  simp [leviCivita_rhs_addX_apply _ (hX x) (hX' x) (hY x) (hZ x)]

open VectorField

variable {I} in
lemma leviCivita_rhs'_smulX_apply [CompleteSpace E] {f : M → ℝ}
    (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    leviCivita_rhs' I (f • X) Y Z x = f x • leviCivita_rhs' I X Y Z x := by
  unfold leviCivita_rhs'
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [rhs_aux_smulX, rhs_aux_smulY_apply, rhs_aux_smulZ_apply] <;> try assumption
  simp only [product_apply, mlieBracket_smul_left (W := Z) hf hX,
    mlieBracket_smul_right (V := Y) hf hX, inner_add_right]
  -- Combining this line with the previous one fails.
  simp only [← product_apply, neg_smul, inner_neg_right]
  have h1 :
      letI dfZ : ℝ := (mfderiv I 𝓘(ℝ, ℝ) f x) (Z x);
      inner ℝ (Y x) ((mfderiv I 𝓘(ℝ, ℝ) f x) (Z x) • X x) = dfZ * ⟪X, Y⟫ x := by
    simp only [product]
    rw [← real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, real_inner_comm]
  have h2 :
      letI dfZ : ℝ := (mfderiv I 𝓘(ℝ, ℝ) f x) (Y x);
      inner ℝ (Z x) ((mfderiv I 𝓘(ℝ, ℝ) f x) (Y x) • X x) = dfZ * ⟪Z, X⟫ x := by
    simp only [product]
    rw [← real_inner_smul_left, real_inner_smul_right, real_inner_smul_left]
  simp only [h1, h2]
  set dfY : ℝ := (mfderiv I 𝓘(ℝ, ℝ) f x) (Y x)
  set dfZ : ℝ := (mfderiv I 𝓘(ℝ, ℝ) f x) (Z x)
  have h3 : ⟪f • X, mlieBracket I Z Y⟫ x = f x * ⟪X, mlieBracket I Z Y⟫ x := by
    rw [product_apply, Pi.smul_apply', real_inner_smul_left]
  have h4 : inner ℝ (Z x) (f x • mlieBracket I Y X x) = f x * ⟪Z, mlieBracket I Y X⟫ x := by
    rw [product_apply, real_inner_smul_right]
  rw [real_inner_smul_right (Y x), h3]--, h4]
  -- set A := ⟪Y, mlieBracket I X Z⟫ with hA
  -- set B := ⟪Z, mlieBracket I X Y⟫
  -- set C := ⟪X, mlieBracket I Z Y⟫
  -- set R := dfZ * ⟪X, Y⟫ x with hR
  -- set R' := dfY * ⟪Z, X⟫ x with hR'
  -- set E := rhs_aux I X Y Z x
  -- set F := rhs_aux I Y Z X x
  -- set G := rhs_aux I Z X Y x
  -- Push all applications of `x` inwards, then it's indeed obvious.
  simp
  ring_nf
  congr

variable {I} in
lemma leviCivita_rhs_smulX_apply [CompleteSpace E] {f : M → ℝ}
    (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    leviCivita_rhs I (f • X) Y Z x = f x • leviCivita_rhs I X Y Z x := by
  simp only [leviCivita_rhs, one_div, Pi.smul_apply, smul_eq_mul]
  simp_rw [leviCivita_rhs'_smulX_apply (I := I) hf hX hY hZ]
  rw [← mul_assoc, mul_comm (f x), smul_eq_mul]
  ring

variable {I} in
lemma leviCivita_rhs_smulX [CompleteSpace E] {f : M → ℝ}
    (hf : MDiff f) (hX : MDiff (T% X)) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) :
    leviCivita_rhs I (f • X) Y Z = f • leviCivita_rhs I X Y Z := by
  ext x
  exact leviCivita_rhs_smulX_apply (hf x) (hX x) (hY x) (hZ x)

lemma leviCivita_rhs'_addY_apply [CompleteSpace E]
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hY' : MDiffAt (T% Y') x) (hZ : MDiffAt (T% Z) x) :
    leviCivita_rhs' I X (Y + Y') Z x = leviCivita_rhs' I X Y Z x + leviCivita_rhs' I X Y' Z x := by
  simp only [leviCivita_rhs', Pi.add_apply, Pi.sub_apply, product_add_left_apply]
  rw [rhs_aux_addX, rhs_aux_addY_apply, rhs_aux_addZ_apply] <;> try assumption
  -- We have to rewrite back and forth: the Lie bracket is only additive at x,
  -- as we are only asking for differentiability at x.
  simp only [product_apply]
  simp only [Pi.add_apply, mlieBracket_add_left (W := X) hY hY',
    VectorField.mlieBracket_add_right (V := Z) hY hY', inner_add_right, ← product_apply]
  have : mlieBracket I (Y + Y') X x = mlieBracket I (Y) X x + mlieBracket I Y' X x := by
    exact mlieBracket_add_left (W := X) hY hY'
  abel

lemma leviCivita_rhs_addY_apply [CompleteSpace E]
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hY' : MDiffAt (T% Y') x) (hZ : MDiffAt (T% Z) x) :
    leviCivita_rhs I X (Y + Y') Z x = leviCivita_rhs I X Y Z x + leviCivita_rhs I X Y' Z x := by
  simp [leviCivita_rhs, leviCivita_rhs'_addY_apply I hX hY hY' hZ, left_distrib]

lemma leviCivita_rhs_addY [CompleteSpace E]
    (hX : MDiff (T% X)) (hY : MDiff (T% Y)) (hY' : MDiff (T% Y')) (hZ : MDiff (T% Z)) :
    leviCivita_rhs I X (Y + Y') Z = leviCivita_rhs I X Y Z + leviCivita_rhs I X Y' Z := by
  ext x
  simp [leviCivita_rhs_addY_apply I (hX x) (hY x) (hY' x) (hZ x)]

lemma leviCivita_rhs'_addZ_apply [CompleteSpace E]
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) (hZ' : MDiffAt (T% Z') x) :
    leviCivita_rhs' I X Y (Z + Z') x =
      leviCivita_rhs' I X Y Z x + leviCivita_rhs' I X Y Z' x := by
  simp only [leviCivita_rhs', rhs_aux_addX, Pi.add_apply, Pi.sub_apply, product_add_left_apply]
  rw [rhs_aux_addY_apply, rhs_aux_addZ_apply] <;> try assumption
  simp only [product_apply]
  simp only [VectorField.mlieBracket_add_right (V := X) hZ hZ',
    VectorField.mlieBracket_add_left (W := Y) hZ hZ', inner_add_right, ← product_apply]
  abel

lemma leviCivita_rhs'_addZ [CompleteSpace E]
    (hX : MDiff (T% X)) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) (hZ' : MDiff (T% Z')) :
    leviCivita_rhs' I X Y (Z + Z') =
      leviCivita_rhs' I X Y Z + leviCivita_rhs' I X Y Z' := by
  ext x
  exact leviCivita_rhs'_addZ_apply I (hX x) (hY x) (hZ x) (hZ' x)

lemma leviCivita_rhs_addZ_apply [CompleteSpace E]
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) (hZ' : MDiffAt (T% Z') x) :
    leviCivita_rhs I X Y (Z + Z') x = leviCivita_rhs I X Y Z x + leviCivita_rhs I X Y Z' x := by
  simp [leviCivita_rhs, leviCivita_rhs'_addZ_apply I hX hY hZ hZ', left_distrib]

lemma leviCivita_rhs_addZ [CompleteSpace E]
    (hX : MDiff (T% X)) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) (hZ' : MDiff (T% Z')) :
    leviCivita_rhs I X Y (Z + Z') = leviCivita_rhs I X Y Z + leviCivita_rhs I X Y Z' := by
  ext x
  exact leviCivita_rhs_addZ_apply I (hX x) (hY x) (hZ x) (hZ' x)

lemma leviCivita_rhs'_smulZ_apply [CompleteSpace E] {f : M → ℝ}
    (hf : MDiffAt f x) (hX : MDiffAt  (T% X) x) (hY : MDiffAt  (T% Y) x) (hZ : MDiffAt  (T% Z) x) :
    leviCivita_rhs' I X Y (f • Z) x = f x • leviCivita_rhs' I X Y Z x := by
  simp only [leviCivita_rhs']
  simp [rhs_aux_smulX]
  rw [rhs_aux_smulY_apply _ _ hf hZ hX, rhs_aux_smulZ_apply _ _ hf hY hZ]
  beta_reduce

  set A := rhs_aux I X Y Z x
  set B := rhs_aux I Y Z X x
  set C := rhs_aux I Z X Y x

  -- Apply the product rule for the lie bracket.
  have h1 : VectorField.mlieBracket I X (f • Z) x =
      f x • VectorField.mlieBracket I X Z x + mfderiv% f x (X x) • Z x := by
    rw [VectorField.mlieBracket_smul_right hf hZ, add_comm]
  have h2 : VectorField.mlieBracket I (f • Z) Y x =
      -(mfderiv% f x (Y x)) • Z x + f x • VectorField.mlieBracket I Z Y x := by
    rw [VectorField.mlieBracket_smul_left hf hZ]
  -- -- Again, we need to go into the product and back out again.
  -- simp only [product_apply]
  -- rw [h1, h2, inner_add_right, inner_smul_right_eq_smul]
  -- simp only [← product_apply]

  -- Let's try to encapsulate more.
  have h1' : ⟪Y, mlieBracket I X (f • Z)⟫ x =
      f x • ⟪Y, mlieBracket I X Z⟫ x + ⟪Y, mfderiv% f x (X x) • Z⟫ x := by
    rw [product_apply, h1, inner_add_right, inner_smul_right]
    congr
  rw [h1']
  set D := ⟪Y, mlieBracket I X Z⟫ x

  set X'' := ⟪Y, (mfderiv I 𝓘(ℝ, ℝ) f x) (X x) • Z⟫ x


  have aux : ⟪f • Z, mlieBracket I Y X⟫ x = f x • ⟪Z, mlieBracket I Y X⟫ x := by
    rw [product_smul_left]; simp

  rw [product_smul_left]
  --simp_rw [product_smul_left]

  --simp only [product_add_right_apply]
  set D := ⟪Y, mlieBracket I X Z⟫ x
  set E := ⟪Z, mlieBracket I Y X⟫ x
  set F := ⟪X, mlieBracket I Z Y⟫ x
  --rw [h1, h2]; beta_reduce
  --simp only [smul_eq_mul, product_add_right_apply]

  -- continue here!
  sorry
  -- simp_rw [product_apply]
  -- set D' := (mfderiv% f x) (X x)
  -- set D := (fun x ↦ (mfderiv% f x) (X x)) • Z

  -- --rw [product_add_right, product_add_right]
  -- -- These are all science fiction, and not fully true!
  -- rw [product_smul_left, product_smul_right, product_smul_right]
  -- set E := ⟪Z, VectorField.mlieBracket I X Y⟫
  -- set F := ⟪Y, VectorField.mlieBracket I X Z⟫
  -- set G := ⟪X, VectorField.mlieBracket I Z Y⟫
  -- -- apart from science fiction mistakes, this is "an easy computation"
  -- simp; abel_nf
  -- sorry

lemma leviCivita_rhs'_smulZ [CompleteSpace E] {f : M → ℝ}
    (hf : MDiff f) (hX : MDiff (T% X)) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) :
    leviCivita_rhs' I X Y (f • Z) = f • leviCivita_rhs' I X Y Z := by
  ext x
  exact leviCivita_rhs'_smulZ_apply I (hf x) (hX x) (hY x) (hZ x)

lemma leviCivita_rhs_smulZ [CompleteSpace E] {f : M → ℝ}
    (hf : MDiff f) (hX : MDiff (T% X)) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) :
    leviCivita_rhs I X Y (f • Z) = f • leviCivita_rhs I X Y Z := by
  simp only [leviCivita_rhs]
  rw [smul_comm, leviCivita_rhs'_smulZ I hf hX hY hZ]
/- old proof attempt was:
lemma leviCivita_rhs_smulZ [CompleteSpace E] {f : M → ℝ} (hf : MDiff f) (hZ : MDiff (T% Z)) :
    leviCivita_rhs I X Y (f • Z) = f • leviCivita_rhs I X Y Z := by
  simp only [leviCivita_rhs, leviCivita_rhs']
  simp [rhs_aux_smulX]--, rhs_aux_smulY, rhs_aux_smulZ]
  ext x
  simp only [Pi.mul_apply, Pi.add_apply]
  have h1 : VectorField.mlieBracket I X (f • Z) =
      f • VectorField.mlieBracket I X Z + (fun x ↦ mfderiv% f x (X x)) • Z := by
    ext x
    rw [VectorField.mlieBracket_smul_right (hf x) (hZ x), add_comm]
    simp
  have h2 : VectorField.mlieBracket I (f • Z) Y =
      -(fun x ↦ mfderiv% f x (Y x)) • Z + f • VectorField.mlieBracket I Z Y := by
    ext x
    rw [VectorField.mlieBracket_smul_left (hf x) (hZ x)]
    simp
  simp only [h1, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, smul_eq_mul, h2]
  set A := rhs_aux I X Y Z x
  set B := rhs_aux I Y Z X x
  set C := rhs_aux I Z X Y x
  set D := (fun x ↦ (mfderiv% f x) (X x)) • Z

  rw [product_add_right, product_add_right]
  -- These are all science fiction, and not fully true!
  rw [product_smul_left, product_smul_right, product_smul_right]
  set E := ⟪Z, VectorField.mlieBracket I X Y⟫
  set F := ⟪Y, VectorField.mlieBracket I X Z⟫
  set G := ⟪X, VectorField.mlieBracket I Z Y⟫
  -- apart from science fiction mistakes, this is "an easy computation"
  simp; abel_nf
  sorry -/

end leviCivita_rhs

variable (X Y Z) in
lemma aux (h : cov.IsLeviCivitaConnection) : rhs_aux I X Y Z =
    ⟪cov X Y, Z⟫ + ⟪Y, cov Z X⟫ + ⟪Y, VectorField.mlieBracket I X Z⟫ := by
  trans ⟪cov X Y, Z⟫ + ⟪Y, cov X Z⟫
  · ext x
    exact h.1 X Y Z x
  · simp [← isTorsionFree_iff.mp h.2 X Z, product_sub_right]

lemma isolate_aux {α : Type*} [AddCommGroup α]
    (A D E F X Y Z : α) (h : X + Y - Z = A + A + D + E - F) :
    A + A = X + Y - Z - D - E + F := by
  rw [h]; abel

variable (X Y Z) in
/-- Auxiliary lemma towards the uniquness of the Levi-Civita connection: expressing the term
⟨∇ X Y, Z⟩ for all differentiable vector fields X, Y and Z, without reference to ∇. -/
lemma isLeviCivitaConnection_uniqueness_aux (h : cov.IsLeviCivitaConnection) :
    ⟪cov X Y, Z⟫ = leviCivita_rhs I X Y Z := by
  set A := ⟪cov X Y, Z⟫
  set B := ⟪cov Z X, Y⟫
  set C := ⟪cov Y Z, X⟫
  set D := ⟪Y, VectorField.mlieBracket I X Z⟫ with D_eq
  set E := ⟪Z, VectorField.mlieBracket I Y X⟫ with E_eq
  set F := ⟪X, VectorField.mlieBracket I Z Y⟫ with F_eq
  have eq1 : rhs_aux I X Y Z = A + B + D := by
    simp only [aux I X Y Z cov h, A, B, D, product_swap _ Y (cov Z X)]
  have eq2 : rhs_aux I Y Z X = C + A + E := by
    simp only [aux I Y Z X cov h, A, C, E, product_swap _ (cov X Y) Z]
  have eq3 : rhs_aux I Z X Y = B + C + F := by
    simp only [aux I Z X Y cov h, B, C, F, product_swap _ X (cov Y Z)]
  -- Add eq1 and eq2 and subtract eq3.
  have : rhs_aux I X Y Z + rhs_aux I Y Z X - rhs_aux I Z X Y = A + A + D + E - F := by
    rw [eq1, eq2, eq3]; abel
  -- Solve for ⟪cov X Y, Z⟫ and obtain the claim.
  have almost := isolate_aux A D E F (rhs_aux I X Y Z) (rhs_aux I Y Z X) (rhs_aux I Z X Y)
    (by simp [this])
  have almoster : A + A = leviCivita_rhs' I X Y Z := by simp only [leviCivita_rhs', *]
  simp only [leviCivita_rhs, ← almoster, smul_add]
  ext; simp; ring

section

attribute [local instance] Fintype.toOrderBot Fintype.toLocallyFiniteOrder

variable [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]

variable {I} in
/-- If two vector fields `X` and `X'` on `M` satisfy the relation `⟨X, Z⟩ = ⟨X', Z⟩` for all
vector fields `Z`, then `X = X'`. XXX up to differentiability? -/
-- TODO: is this true if E is infinite-dimensional? trace the origin of the `Fintype` assumptions!
lemma congr_of_forall_product [FiniteDimensional ℝ E]
    (h : ∀ Z : Π x : M, TangentSpace I x, ⟪X, Z⟫ = ⟪X', Z⟫) : X = X' := by
  by_cases hE : Subsingleton E
  · ext x
    have : Subsingleton (TangentSpace I x) := inferInstanceAs (Subsingleton E)
    apply Subsingleton.allEq _
  ext x
  letI b := Basis.ofVectorSpace ℝ E
  letI t := trivializationAt E (TangentSpace I : M → Type _) x
  have hx : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
  have : Nonempty ↑(Basis.ofVectorSpaceIndex ℝ E) := b.index_nonempty
  have : LinearOrder ↑(Basis.ofVectorSpaceIndex ℝ E) := by
    choose r wo using exists_wellOrder _
    exact r
  haveI : LocallyFiniteOrderBot ↑(Basis.ofVectorSpaceIndex ℝ E) := inferInstance

  -- Choose an orthonormal frame (s i) near x w.r.t. to this trivialisation, and the metric g
  let real := b.orthonormalFrame t
  have hframe := b.orthonormalFrame_isOrthonormalFrameOn t (F := E) (IB := I) (n := 1)
  rw [hframe.eq_iff_repr hx]
  intro i
  have h₁ : ⟪X, real i⟫ x = (hframe.repr i) X x := by
    rw [hframe.repr_eq_inner' _ hx]
    simp [real, real_inner_comm]
  have h₂ : ⟪X', real i⟫ x = (hframe.repr i) X' x := by
    rw [hframe.repr_eq_inner' _ hx]
    simp [real, real_inner_comm]
  rw [← h₁, ← h₂, h (real i)]

/-- The Levi-Civita connection on `(M, g)` is uniquely determined,
at least on differentiable vector fields. -/
-- (probably not everywhere, as addition rules apply only for differentiable vector fields?)
theorem isLeviCivita_uniqueness [FiniteDimensional ℝ E]
    {cov cov' : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (hcov : cov.IsLeviCivitaConnection) (hcov' : cov'.IsLeviCivitaConnection) :
    -- almost, only agree on smooth functions
    cov = cov' := by
  ext X σ x
  apply congrFun
  apply congr_of_forall_product fun Z ↦ ?_
  trans leviCivita_rhs I X σ Z
  · exact cov.isLeviCivitaConnection_uniqueness_aux I X σ Z hcov
  · exact (cov'.isLeviCivitaConnection_uniqueness_aux I X σ Z hcov').symm

noncomputable def lcCandidate_aux [FiniteDimensional ℝ E]
    (e : Trivialization E (TotalSpace.proj : TangentBundle I M → M)) [MemTrivializationAtlas e] :
    ((x : M) → TangentSpace I x) → ((x : M) → TangentSpace I x) → (x : M) → TangentSpace I x :=
  open scoped Classical in
  fun X Y x ↦
  if hE : Subsingleton E then X x else
  -- Choose a trivialisation of `TM` near `x`.
  -- Since `E` is non-trivial, `b` is non-empty.
  letI b := Basis.ofVectorSpace ℝ E
  have : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
  have : Nonempty ↑(Basis.ofVectorSpaceIndex ℝ E) := b.index_nonempty
  have : LinearOrder ↑(Basis.ofVectorSpaceIndex ℝ E) := by
    choose r wo using exists_wellOrder _
    exact r
  haveI : LocallyFiniteOrderBot ↑(Basis.ofVectorSpaceIndex ℝ E) := inferInstance
  letI frame := b.orthonormalFrame e
  -- The coefficient of the desired tangent vector `∇ X Y x` w.r.t. `s i`
  -- is given by `leviCivita_rhs X Y s i`.
  ∑ i, ((leviCivita_rhs I X Y (frame i)) x) • (frame i x)

variable (M) in
-- TODO: make g part of the notation!
/-- Given two vector fields X and Y on TM, compute
the candidate definition for the Levi-Civita connection on `TM`. -/
noncomputable def lcCandidate [FiniteDimensional ℝ E] :
    (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) :=
  -- Use the preferred trivialisation at `x` to write down a candidate for the existence.
  fun X Y x ↦ lcCandidate_aux I (trivializationAt E (TangentSpace I : M → Type _) x) X Y x

variable (X Y) in
-- The above definition behaves well: for each compatible trivialisation e,
-- using e on e.baseSet yields the same result as above.
lemma bar [FiniteDimensional ℝ E] (e : Trivialization E (TotalSpace.proj: TangentBundle I M → M))
    [MemTrivializationAtlas e] {x : M} (hx : x ∈ e.baseSet) :
    lcCandidate I M X Y x = lcCandidate_aux I e X Y x := by
  by_cases hE : Subsingleton E
  · simp [lcCandidate, lcCandidate_aux, hE]
  · simp only [lcCandidate, lcCandidate_aux, hE, ↓reduceDIte]
    -- Now, start the real proof.
    sorry

-- The candidate definition is a covariant derivative on each local frame's domain.
lemma isCovariantDerivativeOn_lcCandidate_aux [FiniteDimensional ℝ E]
    (e : Trivialization E (TotalSpace.proj : TangentBundle I M → M)) [MemTrivializationAtlas e] :
    IsCovariantDerivativeOn E (lcCandidate_aux I (M := M) e) e.baseSet where
  addX X X' σ x hx := by
    by_cases hE : Subsingleton E; · simp [lcCandidate_aux, hE]
    -- these three sorries seem to be necessary!
    have hX : MDiffAt (T% X) x := sorry
    have hX' : MDiffAt (T% X') x := sorry
    have hσ : MDiffAt (T% σ) x := sorry
    simp only [lcCandidate_aux, hE, ↓reduceDIte]
    simp only [← Finset.sum_add_distrib, ← add_smul]
    congr; ext i
    rw [leviCivita_rhs_addX_apply] <;> try assumption
    let : LinearOrder ↑(Basis.ofVectorSpaceIndex ℝ E) := Classical.choose (exists_wellOrder _)
    have : LocallyFiniteOrderBot ↑(Basis.ofVectorSpaceIndex ℝ E) := sorry
    set f := ((Basis.ofVectorSpace ℝ E).orthonormalFrame e i)
    have : MDiffAt (T% f) x := -- missing API lemma!
      (contMDiffAt_orthonormalFrame_of_mem (Basis.ofVectorSpace ℝ E) e i hx)
        |>.mdifferentiableAt le_rfl
    sorry -- convert this works, except for different local orders...
  smulX X σ g x hx := by
    by_cases hE : Subsingleton E; · simp [lcCandidate_aux, hE]
    simp only [lcCandidate_aux, hE, ↓reduceDIte]
    have hX : MDiff (T% X) := sorry -- might need this (hopefully not!)
    have hg : MDiff g := sorry -- might need this (hopefully not!)
    rw [Finset.smul_sum]
    congr; ext i
    rw [leviCivita_rhs_smulX] <;> try assumption
    rotate_left
    · sorry -- missing hyp!
    · sorry -- missing hyp!
    simp [← smul_assoc]
  smul_const_σ X σ a x hx := by
    by_cases hE : Subsingleton E; · have : X x = 0 := sorry; simp [lcCandidate_aux, hE, this]
    simp only [lcCandidate_aux, hE, ↓reduceDIte]
    rw [Finset.smul_sum]; congr; ext i
    -- want leviCivita_rhs_smulY (with a constant)
    sorry
  addσ X σ σ' x hσ hσ' hx := by
    have hX : MDiffAt (T% X) x := sorry -- missing assumption!
    by_cases hE : Subsingleton E; · have : X x = 0 := sorry; simp [lcCandidate_aux, hE, this]
    simp only [lcCandidate_aux, hE, ↓reduceDIte]
    simp only [← Finset.sum_add_distrib, ← add_smul]
    congr; ext i
    rw [leviCivita_rhs_addY_apply] <;> try assumption
    let ⟨r, o⟩ := exists_wellOrder (↑(Basis.ofVectorSpaceIndex ℝ E))
    have : LocallyFiniteOrderBot ↑(Basis.ofVectorSpaceIndex ℝ E) := by sorry
    set f := ((Basis.ofVectorSpace ℝ E).orthonormalFrame e i)
    have : MDiffAt (T% f) x := -- missing API lemma!
      (contMDiffAt_orthonormalFrame_of_mem (Basis.ofVectorSpace ℝ E) e i hx)
        |>.mdifferentiableAt le_rfl
    -- mismatch between different orders; the sorry above
    convert this <;> sorry
  leibniz X σ g x hσ hg hx := by
    by_cases hE : Subsingleton E
    · have : X x = 0 := sorry
      simp [lcCandidate_aux, hE, this]
    simp only [lcCandidate_aux, hE, ↓reduceDIte]
    sorry

-- The candidate definition is a covariant derivative on each local frame's domain.
lemma isCovariantDerivativeOn_existence_candidate [FiniteDimensional ℝ E]
    (e : Trivialization E (TotalSpace.proj : TangentBundle I M → M)) [MemTrivializationAtlas e] :
    IsCovariantDerivativeOn E (lcCandidate I M) e.baseSet := by
  apply IsCovariantDerivativeOn.congr (isCovariantDerivativeOn_lcCandidate_aux I e)
  intro X σ x hx
  exact (bar I X σ e hx).symm

end

variable [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]

-- TODO: make g part of the notation!
variable (M) in
/-- A choice of Levi-Civita connection on the tangent bundle `TM` of a Riemannian manifold `(M, g)`:
this is unique up to the value on non-differentiable vector fields.
If you know the Levi-Civita connection already, you can use `IsLeviCivitaConnection` instead. -/
noncomputable def LeviCivitaConnection [FiniteDimensional ℝ E] :
    CovariantDerivative I E (TangentSpace I : M → Type _) where
  -- This is the existence part of the proof: take the formula derived above
  -- and prove it satisfies all the conditions.
  toFun := lcCandidate I M
  isCovariantDerivativeOn := by
    rw [← iUnion_source_chartAt H M]
    let t := fun x ↦ trivializationAt E (TangentSpace I : M → Type _) x
    apply IsCovariantDerivativeOn.iUnion (s := fun i ↦ (t i).baseSet) fun i ↦ ?_
    apply isCovariantDerivativeOn_existence_candidate I _

lemma baz [FiniteDimensional ℝ E] : (LeviCivitaConnection I M).IsLeviCivitaConnection := by
  refine ⟨?_, ?_⟩
  · sorry -- compatible
  · sorry -- torsion-free

end CovariantDerivative
