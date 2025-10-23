/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
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

variable {X X' X'' Y Y' Y'' Z Z' : Π x : M, TangentSpace I x}

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
@[simp]
lemma product_smul_const_left (a : ℝ) : product I (a • X) Y = a • product I X Y := by
  ext x
  simp [product, real_inner_smul_left]

variable (X Y) in
lemma product_smul_right (f : M → ℝ) : product I X (f • Y) = f • product I X Y := by
  ext x
  simp [product, real_inner_smul_right]

variable (X Y) in
@[simp]
lemma product_smul_const_right (a : ℝ) : product I X (a • Y) = a • product I X Y := by
  ext x
  simp [product, real_inner_smul_right]

end product

-- These lemmas are necessary as my Lie bracket identities (assuming minimal differentiability)
-- only hold point-wise. They abstract the expanding and unexpanding of `product`.
omit [IsManifold I ∞ M] in
lemma product_congr_left {x} (h : X x = X' x) : product I X Y x = product I X' Y x := by
  rw [product_apply, h, ← product_apply]

omit [IsManifold I ∞ M] in
lemma product_congr_left₂ {x} (h : X x = X' x + X'' x) :
    product I X Y x = product I X' Y x + product I X'' Y x := by
  rw [product_apply, h, inner_add_left, ← product_apply]
omit [IsManifold I ∞ M] in
lemma product_congr_right {x} (h : Y x = Y' x) : product I X Y x = product I X Y' x := by
  rw [product_apply, h, ← product_apply]

omit [IsManifold I ∞ M] in
lemma product_congr_right₂ {x} (h : Y x = Y' x + Y'' x) :
    product I X Y x = product I X Y' x + product I X Y'' x := by
  rw [product_apply, h, inner_add_right, ← product_apply]

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

variable (Y Z) in
omit [IsManifold I ∞ M] in
lemma rhs_aux_swap : rhs_aux I X Y Z = rhs_aux I X Z Y := by
  ext x
  simp only [rhs_aux]
  congr 2
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
lemma rhs_aux_smulX_apply (f : M → ℝ) (x) : rhs_aux I (f • X) Y Z x = f x • rhs_aux I X Y Z x := by
  simp [rhs_aux]

omit [IsManifold I ∞ M] in
variable (X Y Z) in
lemma rhs_aux_smulX (f : M → ℝ) : rhs_aux I (f • X) Y Z = f • rhs_aux I X Y Z := by
  ext x
  exact rhs_aux_smulX_apply ..

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
lemma rhs_aux_smulY_const_apply {a : ℝ} (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    rhs_aux I X (a • Y) Z x = a • rhs_aux I X Y Z x := by
  let f : M → ℝ := fun _ ↦ a
  have h1 : rhs_aux I X (a • Y) Z x = rhs_aux I X (f • Y) Z x := by simp only [f]; congr
  rw [h1, rhs_aux_smulY_apply I X mdifferentiableAt_const hY hZ]
  simp [mfderiv_const]

variable (X) in
lemma rhs_aux_smulY_const {a : ℝ} (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) :
    rhs_aux I X (a • Y) Z = a • rhs_aux I X Y Z := by
  ext x
  apply rhs_aux_smulY_const_apply I X (hY x) (hZ x)

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

variable (X) in
lemma rhs_aux_smulZ_const_apply {a : ℝ} (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    rhs_aux I X Y (a • Z) x = a • rhs_aux I X Y Z x := by
  let f : M → ℝ := fun _ ↦ a
  have h1 : rhs_aux I X Y (a • Z) x = rhs_aux I X Y (f • Z) x := by simp only [f]; congr
  rw [h1, rhs_aux_smulZ_apply I X mdifferentiableAt_const hY hZ]
  simp [mfderiv_const]

variable (X) in
lemma rhs_aux_smulZ_const {a : ℝ} (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) :
    rhs_aux I X Y (a • Z) = a • rhs_aux I X Y Z := by
  ext x
  exact rhs_aux_smulZ_const_apply I X (hY x) (hZ x)

end rhs_aux

variable {x : M}

variable (X Y Z) in
/-- Auxiliary quantity used in the uniqueness proof of the Levi-Civita connection:
If ∇ is a Levi-Civita connection on `TM`, then
`2 ⟨∇ X Y, Z⟩ = leviCivitaRhs' I X Y Z` for all vector fields `Z`. -/
noncomputable def leviCivitaRhs' : M → ℝ :=
  rhs_aux I X Y Z + rhs_aux I Y Z X - rhs_aux I Z X Y
  - ⟪Y ,(VectorField.mlieBracket I X Z)⟫
  - ⟪Z, (VectorField.mlieBracket I Y X)⟫
  + ⟪X, (VectorField.mlieBracket I Z Y)⟫

variable (X Y Z) in
/-- Auxiliary quantity used in the uniqueness proof of the Levi-Civita connection:
If `∇` is a Levi-Civita connection on `TM`, then
`⟨∇ X Y, Z⟩ = leviCivitaRhs I X Y Z` for all smooth vector fields `X`, `Y` and `Z`. -/
noncomputable def leviCivitaRhs : M → ℝ := (1 / 2 : ℝ) • leviCivitaRhs' I X Y Z

omit [IsManifold I ∞ M] in
lemma leviCivitaRhs_apply : leviCivitaRhs I X Y Z x = (1 / 2 : ℝ) • leviCivitaRhs' I X Y Z x :=
  rfl

section leviCivitaRhs

variable [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]

@[simp]
lemma leviCivitaRhs'_addX_apply [CompleteSpace E]
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    leviCivitaRhs' I (X + X') Y Z x =
      leviCivitaRhs' I X Y Z x + leviCivitaRhs' I X' Y Z x := by
  simp only [leviCivitaRhs', rhs_aux_addX, Pi.add_apply, Pi.sub_apply]
  -- We have to rewrite back and forth: the Lie bracket is only additive at x,
  -- as we are only asking for differentiability at x.
  -- Fortunately, the `product_congr_right₂` lemma abstracts this very well.
  rw [product_congr_right₂ I (VectorField.mlieBracket_add_right (V := Y) hX hX'),
    product_congr_right₂ I (VectorField.mlieBracket_add_left (W := Z) hX hX'),
    product_add_left_apply, rhs_aux_addY_apply, rhs_aux_addZ_apply] <;> try assumption
  abel

lemma leviCivitaRhs'_addX [CompleteSpace E]
    (hX : MDiff (T% X)) (hX' : MDiff (T% X')) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) :
    leviCivitaRhs' I (X + X') Y Z =
      leviCivitaRhs' I X Y Z + leviCivitaRhs' I X' Y Z := by
  ext x
  simp [leviCivitaRhs'_addX_apply _ (hX x) (hX' x) (hY x) (hZ x)]

lemma leviCivitaRhs_addX_apply [CompleteSpace E]
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    leviCivitaRhs I (X + X') Y Z x = leviCivitaRhs I X Y Z x + leviCivitaRhs I X' Y Z x := by
  simp [leviCivitaRhs, leviCivitaRhs'_addX_apply I hX hX' hY hZ, left_distrib]

lemma leviCivitaRhs_addX [CompleteSpace E]
    (hX : MDiff (T% X)) (hX' : MDiff (T% X')) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) :
    leviCivitaRhs I (X + X') Y Z = leviCivitaRhs I X Y Z + leviCivitaRhs I X' Y Z := by
  ext x
  simp [leviCivitaRhs_addX_apply _ (hX x) (hX' x) (hY x) (hZ x)]

open VectorField

variable {I} in
lemma leviCivitaRhs'_smulX_apply [CompleteSpace E] {f : M → ℝ}
    (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    leviCivitaRhs' I (f • X) Y Z x = f x • leviCivitaRhs' I X Y Z x := by
  unfold leviCivitaRhs'
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [rhs_aux_smulX, rhs_aux_smulY_apply, rhs_aux_smulZ_apply] <;> try assumption
  -- TODO: add the right congr_right lemma to avoid the product_apply, ← product_apply dance!
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
lemma leviCivitaRhs_smulX_apply [CompleteSpace E] {f : M → ℝ}
    (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    leviCivitaRhs I (f • X) Y Z x = f x • leviCivitaRhs I X Y Z x := by
  simp only [leviCivitaRhs, one_div, Pi.smul_apply, smul_eq_mul]
  simp_rw [leviCivitaRhs'_smulX_apply (I := I) hf hX hY hZ]
  rw [← mul_assoc, mul_comm (f x), smul_eq_mul]
  ring

variable {I} in
lemma leviCivitaRhs_smulX [CompleteSpace E] {f : M → ℝ}
    (hf : MDiff f) (hX : MDiff (T% X)) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) :
    leviCivitaRhs I (f • X) Y Z = f • leviCivitaRhs I X Y Z := by
  ext x
  exact leviCivitaRhs_smulX_apply (hf x) (hX x) (hY x) (hZ x)

lemma leviCivitaRhs'_addY_apply [CompleteSpace E]
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hY' : MDiffAt (T% Y') x) (hZ : MDiffAt (T% Z) x) :
    leviCivitaRhs' I X (Y + Y') Z x = leviCivitaRhs' I X Y Z x + leviCivitaRhs' I X Y' Z x := by
  simp only [leviCivitaRhs', Pi.add_apply, Pi.sub_apply, product_add_left_apply]
  rw [rhs_aux_addX, rhs_aux_addY_apply, rhs_aux_addZ_apply] <;> try assumption
  -- We have to rewrite back and forth: the Lie bracket is only additive at x,
  -- as we are only asking for differentiability at x.
  rw [product_congr_right₂ I (mlieBracket_add_left (W := X) hY hY')]
  rw [product_congr_right₂ I (VectorField.mlieBracket_add_right (V := Z) hY hY')]
  simp only [Pi.add_apply]
  abel

lemma leviCivitaRhs_addY_apply [CompleteSpace E]
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hY' : MDiffAt (T% Y') x) (hZ : MDiffAt (T% Z) x) :
    leviCivitaRhs I X (Y + Y') Z x = leviCivitaRhs I X Y Z x + leviCivitaRhs I X Y' Z x := by
  simp [leviCivitaRhs, leviCivitaRhs'_addY_apply I hX hY hY' hZ, left_distrib]

lemma leviCivitaRhs_addY [CompleteSpace E]
    (hX : MDiff (T% X)) (hY : MDiff (T% Y)) (hY' : MDiff (T% Y')) (hZ : MDiff (T% Z)) :
    leviCivitaRhs I X (Y + Y') Z = leviCivitaRhs I X Y Z + leviCivitaRhs I X Y' Z := by
  ext x
  simp [leviCivitaRhs_addY_apply I (hX x) (hY x) (hY' x) (hZ x)]

variable {I} in
lemma leviCivitaRhs'_smulY_const_apply [CompleteSpace E] {a : ℝ}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    leviCivitaRhs' I X (a • Y) Z x = a • leviCivitaRhs' I X Y Z x := by
  simp only [leviCivitaRhs']
  simp only [product_smul_const_left, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  rw [rhs_aux_smulY_const_apply I X hY hZ]
  -- TODO: clean up this proof!
  let f : M → ℝ := fun _ ↦ a
  have : rhs_aux I (a • Y) Z X x = a • rhs_aux I Y Z X x := by
    trans rhs_aux I (f • Y) Z X x
    · rfl
    rw [rhs_aux_smulX I Y (f := f) (Y := Z) (Z := X)]
    rfl
  rw [this, rhs_aux_smulZ_const_apply I _ hX hY]
  -- is there a better abstraction for "Lie bracket conv mode"?
  have : ⟪Z, mlieBracket I (a • Y) X⟫ x = a • ⟪Z, mlieBracket I Y X⟫ x := by
    simp_rw [product_apply, mlieBracket_const_smul_left (W := X) hY, inner_smul_right_eq_smul]
  rw [this]
  have aux2 : ⟪X, mlieBracket I Z (a • Y)⟫ x = a • ⟪X, mlieBracket I Z Y⟫ x := by
    simp_rw [product_apply,  mlieBracket_const_smul_right (V := Z) hY, inner_smul_right_eq_smul]
  rw [aux2]
  simp
  ring

variable {I} in
lemma leviCivitaRhs_smulY_const_apply [CompleteSpace E] {a : ℝ}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    leviCivitaRhs I X (a • Y) Z x = a • leviCivitaRhs I X Y Z x := by
  simp_rw [leviCivitaRhs, Pi.smul_apply]; rw [smul_comm]
  congr
  exact leviCivitaRhs'_smulY_const_apply hX hY hZ

variable {I} in
lemma leviCivitaRhs_smulY_const [CompleteSpace E] {a : ℝ}
    (hX : MDiff (T% X)) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) :
    leviCivitaRhs I X (a • Y) Z = a • leviCivitaRhs I X Y Z := by
  ext x
  exact leviCivitaRhs_smulY_const_apply (hX x) (hY x) (hZ x)

lemma leviCivitaRhs'_smulY_apply [CompleteSpace E] {f : M → ℝ}
    (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    leviCivitaRhs' I X (f • Y) Z x =
      f x • leviCivitaRhs' I X Y Z x + ((bar _).toFun <| mfderiv% f x (X x)) • 2 * ⟪Y, Z⟫ x := by
  simp only [leviCivitaRhs']
  simp_rw [rhs_aux_smulX I Y Z X f]
  simp only [product_smul_left, Pi.add_apply, Pi.sub_apply, smul_eq_mul, Pi.mul_apply]
  rw [rhs_aux_smulY_apply I X hf hY hZ, rhs_aux_smulZ_apply I Z hf hX hY]

  -- TODO: is there a better abstraction for this kind of "Lie bracket conv mode"?
  have h1 : ⟪Z, mlieBracket I (f • Y) X⟫ x =
      - (bar _).toFun (((mfderiv% f x) (X x))) • ⟪Z, Y⟫ x + f x • ⟪Z, mlieBracket I Y X⟫ x := by
    simp_rw [product_apply, mlieBracket_smul_left (W := X) hf hY, inner_add_right]
    congr
    · simp [bar]; rw [real_inner_smul_right]
    · rw [inner_smul_right_eq_smul]
  have h2 : ⟪X, mlieBracket I Z (f • Y)⟫ x =
      (bar _).toFun (((mfderiv% f x) (Z x))) • ⟪X, Y⟫ x + f x • ⟪X, mlieBracket I Z Y⟫ x := by
    simp_rw [product_apply, mlieBracket_smul_right (V := Z) hf hY, inner_add_right]
    congr
    · simp [bar]; rw [real_inner_smul_right]
    · rw [inner_smul_right_eq_smul]
  rw [h1, h2, product_swap I Y Z]

  set A := rhs_aux I X Y Z x
  set B := rhs_aux I Y Z X x
  set C := rhs_aux I Z X Y x
  set D := ⟪Y, mlieBracket I X Z⟫ x
  set E := ⟪Z, mlieBracket I Y X⟫ x
  set F := ⟪X, mlieBracket I Z Y⟫ x
  set G1 := ⟪Y, Z⟫ x
  set G2 := ⟪X, Y⟫ x
  set dfx := (mfderiv I 𝓘(ℝ, ℝ) f x)
  set H := (bar (f x)) (dfx (X x)) with H_eq
  set K := (bar (f x)) (dfx (Z x)) with K_eq
  change f x * A + (bar _).toFun (dfx (X x)) * G1 + f x * B
    - (f x * C + (bar _).toFun (dfx (Z x)) * G2)
    - f x * D - (-H * G1 + f x * E) + (K * G2 + f x * F) = _
  dsimp
  rw [← H_eq, ← K_eq]
  ring

lemma leviCivitaRhs_smulY_apply [CompleteSpace E] {f : M → ℝ}
    (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    leviCivitaRhs I X (f • Y) Z x =
      f x • leviCivitaRhs I X Y Z x + ((bar _).toFun <| mfderiv% f x (X x)) • ⟪Y, Z⟫ x := by
  simp only [leviCivitaRhs, Pi.smul_apply, leviCivitaRhs'_smulY_apply I hf hX hY hZ]
  rw [smul_add, smul_comm]
  congr 1
  rw [← smul_eq_mul]
  dsimp
  field_simp

lemma leviCivitaRhs'_addZ_apply [CompleteSpace E]
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) (hZ' : MDiffAt (T% Z') x) :
    leviCivitaRhs' I X Y (Z + Z') x =
      leviCivitaRhs' I X Y Z x + leviCivitaRhs' I X Y Z' x := by
  simp only [leviCivitaRhs', rhs_aux_addX, Pi.add_apply, Pi.sub_apply, product_add_left_apply]
  rw [product_congr_right₂ I (VectorField.mlieBracket_add_right (V := X) hZ hZ'),
    product_congr_right₂ I (VectorField.mlieBracket_add_left (W := Y) hZ hZ'),
    rhs_aux_addY_apply, rhs_aux_addZ_apply] <;> try assumption
  abel

lemma leviCivitaRhs'_addZ [CompleteSpace E]
    (hX : MDiff (T% X)) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) (hZ' : MDiff (T% Z')) :
    leviCivitaRhs' I X Y (Z + Z') =
      leviCivitaRhs' I X Y Z + leviCivitaRhs' I X Y Z' := by
  ext x
  exact leviCivitaRhs'_addZ_apply I (hX x) (hY x) (hZ x) (hZ' x)

lemma leviCivitaRhs_addZ_apply [CompleteSpace E]
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) (hZ' : MDiffAt (T% Z') x) :
    leviCivitaRhs I X Y (Z + Z') x = leviCivitaRhs I X Y Z x + leviCivitaRhs I X Y Z' x := by
  simp [leviCivitaRhs, leviCivitaRhs'_addZ_apply I hX hY hZ hZ', left_distrib]

lemma leviCivitaRhs_addZ [CompleteSpace E]
    (hX : MDiff (T% X)) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) (hZ' : MDiff (T% Z')) :
    leviCivitaRhs I X Y (Z + Z') = leviCivitaRhs I X Y Z + leviCivitaRhs I X Y Z' := by
  ext x
  exact leviCivitaRhs_addZ_apply I (hX x) (hY x) (hZ x) (hZ' x)

lemma leviCivitaRhs'_smulZ_apply [CompleteSpace E] {f : M → ℝ}
    (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    leviCivitaRhs' I X Y (f • Z) x = f x • leviCivitaRhs' I X Y Z x := by
  simp only [leviCivitaRhs', rhs_aux_smulX, Pi.add_apply, Pi.sub_apply]
  rw [rhs_aux_smulY_apply _ _ hf hZ hX, rhs_aux_smulZ_apply _ _ hf hY hZ]

  -- Apply the product rule for the lie bracket.
  -- Let's encapsulate the going into the product and back out again.
  have h1 : ⟪Y, mlieBracket I X (f • Z)⟫ x =
      f x • ⟪Y, mlieBracket I X Z⟫ x + ⟪Y, mfderiv% f x (X x) • Z⟫ x := by
    rw [product_apply, VectorField.mlieBracket_smul_right hf hZ, inner_add_right, add_comm,
      inner_smul_right]
    congr
  have h2 : letI dfY : ℝ :=  (mfderiv% f x) (Y x);
      ⟪X, mlieBracket I (f • Z) Y⟫ x = - dfY • ⟪X, Z⟫ x + f x • ⟪X, mlieBracket I Z Y⟫ x := by
    rw [product_apply, VectorField.mlieBracket_smul_left hf hZ, inner_add_right, inner_smul_right,
      inner_smul_right]
    congr
  rw [h1, h2, product_smul_left, product_swap I X Z]
  erw [product_smul_right]
  simp
  -- set A := rhs_aux I X Y Z x
  -- set B := rhs_aux I Y Z X x
  -- set C := rhs_aux I Z X Y x
  -- set D := ⟪Y, mlieBracket I X Z⟫ x
  -- set E := ⟪Z, mlieBracket I Y X⟫ x with E_eq
  -- set F := ⟪X, mlieBracket I Z Y⟫ x
  -- letI dfX : ℝ := (mfderiv I 𝓘(ℝ, ℝ) f x) (X x)
  -- set G := dfX * ⟪Y, Z⟫ x
  -- letI dfY : ℝ := (mfderiv I 𝓘(ℝ, ℝ) f x) (Y x)
  -- set H := dfY * ⟪X, Z⟫ x
  ring

lemma leviCivitaRhs'_smulZ [CompleteSpace E] {f : M → ℝ}
    (hf : MDiff f) (hX : MDiff (T% X)) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) :
    leviCivitaRhs' I X Y (f • Z) = f • leviCivitaRhs' I X Y Z := by
  ext x
  exact leviCivitaRhs'_smulZ_apply I (hf x) (hX x) (hY x) (hZ x)

lemma leviCivitaRhs_smulZ [CompleteSpace E] {f : M → ℝ}
    (hf : MDiff f) (hX : MDiff (T% X)) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) :
    leviCivitaRhs I X Y (f • Z) = f • leviCivitaRhs I X Y Z := by
  simp only [leviCivitaRhs]
  rw [smul_comm, leviCivitaRhs'_smulZ I hf hX hY hZ]

end leviCivitaRhs

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

variable (X Y Z) {cov} in
/-- Auxiliary lemma towards the uniquness of the Levi-Civita connection: expressing the term
⟨∇ X Y, Z⟩ for all differentiable vector fields X, Y and Z, without reference to ∇. -/
lemma IsLeviCivitaConnection.eq_leviCivitaRhs (h : cov.IsLeviCivitaConnection) :
    ⟪cov X Y, Z⟫ = leviCivitaRhs I X Y Z := by
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
  have almoster : A + A = leviCivitaRhs' I X Y Z := by simp only [leviCivitaRhs', *]
  simp only [leviCivitaRhs, ← almoster, smul_add]
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
  obtain (_hE | hE) := subsingleton_or_nontrivial E
  · ext x
    have : Subsingleton (TangentSpace I x) := inferInstanceAs (Subsingleton E)
    apply Subsingleton.allEq _
  ext x
  let b := Basis.ofVectorSpace ℝ E
  let t := trivializationAt E (TangentSpace I : M → Type _) x
  have hx : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have : Nonempty ↑(Basis.ofVectorSpaceIndex ℝ E) := b.index_nonempty
  -- The linear ordering on the indexing set of `b` is only used in this proof,
  -- so our choice does not matter.
  have : LinearOrder ↑(Basis.ofVectorSpaceIndex ℝ E) := by
    choose r wo using exists_wellOrder _
    exact r
  have : LocallyFiniteOrderBot ↑(Basis.ofVectorSpaceIndex ℝ E) := inferInstance

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
theorem IsLeviCivitaConnection.uniqueness [FiniteDimensional ℝ E]
    {cov cov' : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (hcov : cov.IsLeviCivitaConnection) (hcov' : cov'.IsLeviCivitaConnection) :
    -- almost, only agree on smooth functions
    cov = cov' := by
  ext X σ x
  apply congrFun
  apply congr_of_forall_product fun Z ↦ ?_
  trans leviCivitaRhs I X σ Z
  · exact hcov.eq_leviCivitaRhs I X σ Z
  · exact (hcov'.eq_leviCivitaRhs I X σ Z ).symm

/-- Auxiliary definition towards defining the Levi-Civita connection on `M`:
given a trivialisation `e` and a choice `o` of linear order on the standard basis of `E`,
we take the expression defined by the Koszul formula (using the orthonormal frame determined by `e`
and `o`). -/
noncomputable def lcCandidateAux [FiniteDimensional ℝ E]
    (e : Trivialization E (TotalSpace.proj : TangentBundle I M → M)) [MemTrivializationAtlas e]
    (o : LinearOrder ↑(Basis.ofVectorSpaceIndex ℝ E)) :
    ((x : M) → TangentSpace I x) → ((x : M) → TangentSpace I x) → (x : M) → TangentSpace I x :=
  open scoped Classical in
  fun X Y x ↦
  if hE : Subsingleton E then X x else
  -- Choose a trivialisation of `TM` near `x`.
  -- Since `E` is non-trivial, `b` is non-empty.
  let b := Basis.ofVectorSpace ℝ E
  have : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
  have : Nonempty ↑(Basis.ofVectorSpaceIndex ℝ E) := b.index_nonempty
  have : LocallyFiniteOrderBot ↑(Basis.ofVectorSpaceIndex ℝ E) := inferInstance
  letI frame := b.orthonormalFrame e
  -- The coefficient of the desired tangent vector `∇ X Y x` w.r.t. `s i`
  -- is given by `leviCivitaRhs X Y (s i)`.
  ∑ i, ((leviCivitaRhs I X Y (frame i)) x) • (frame i x)

variable (M) in
-- TODO: make g part of the notation!
/-- Given two vector fields X and Y on TM, compute
the candidate definition for the Levi-Civita connection on `TM`. -/
noncomputable def lcCandidate [FiniteDimensional ℝ E]
    (o : LinearOrder ↑(Basis.ofVectorSpaceIndex ℝ E)) :
    (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) :=
  -- Use the preferred trivialisation at `x` to write down a candidate for the existence.
  fun X Y x ↦ lcCandidateAux I (trivializationAt E (TangentSpace I : M → Type _) x) o X Y x

variable (X Y) in
/-- The definition `lcCandidate` behaves well: for each compatible trivialisation `e`,
the candidate definition using `e` agrees with `lcCandidate` on `e.baseSet`. -/
lemma lcCandidate_eq_lcCandidateAux [FiniteDimensional ℝ E]
    (e : Trivialization E (TotalSpace.proj : TangentBundle I M → M)) [MemTrivializationAtlas e]
    {o : LinearOrder ↑(Basis.ofVectorSpaceIndex ℝ E)} {x : M} (hx : x ∈ e.baseSet) :
    lcCandidate I M o X Y x = lcCandidateAux I e o X Y x := by
  by_cases hE : Subsingleton E
  · simp [lcCandidate, lcCandidateAux, hE]
  · simp only [lcCandidate, lcCandidateAux, hE, ↓reduceDIte]
    -- Now, start the real proof.
    sorry

lemma isCovariantDerivativeOn_lcCandidateAux_of_nonempty [FiniteDimensional ℝ E]
    (hE : ¬(Subsingleton E)) [Nontrivial E]
    (e : Trivialization E (TotalSpace.proj : TangentBundle I M → M)) [MemTrivializationAtlas e]
    {o : LinearOrder ↑(Basis.ofVectorSpaceIndex ℝ E)} :
    IsCovariantDerivativeOn E (lcCandidateAux I (M := M) e o) e.baseSet where
  addX {_X _X' _σ x} hX hX' hσ hx := by
    simp only [lcCandidateAux, hE, ↓reduceDIte]
    simp only [← Finset.sum_add_distrib, ← add_smul]
    congr; ext i
    rw [leviCivitaRhs_addX_apply] <;> try assumption
    let b := Basis.ofVectorSpace ℝ E
    have : Nonempty ↑(Basis.ofVectorSpaceIndex ℝ E) := b.index_nonempty
    exact mdifferentiableAt_orthonormalFrame_of_mem b e i hx
  smulX {_X _σ _g _x} hX hσ hg hx := by
    simp only [lcCandidateAux, hE, ↓reduceDIte]
    rw [Finset.smul_sum]
    congr; ext i
    rw [leviCivitaRhs_smulX_apply] <;> try assumption
    · simp [← smul_assoc]
    · let b := Basis.ofVectorSpace ℝ E
      have : Nonempty ↑(Basis.ofVectorSpaceIndex ℝ E) := b.index_nonempty
      exact mdifferentiableAt_orthonormalFrame_of_mem b e i hx
  smul_const_σ {X _σ x} a hX hσ hx := by
    simp only [lcCandidateAux, hE, ↓reduceDIte]
    rw [Finset.smul_sum]; congr; ext i
    rw [leviCivitaRhs_smulY_const_apply hX hσ, ← smul_assoc]
    · let b := Basis.ofVectorSpace ℝ E
      have : Nonempty ↑(Basis.ofVectorSpaceIndex ℝ E) := b.index_nonempty
      exact mdifferentiableAt_orthonormalFrame_of_mem b e i hx
  addσ {X σ σ' x} hX hσ hσ' hx := by
    simp only [lcCandidateAux, hE, ↓reduceDIte]
    simp only [← Finset.sum_add_distrib, ← add_smul]
    congr; ext i
    rw [leviCivitaRhs_addY_apply] <;> try assumption
    let b := Basis.ofVectorSpace ℝ E
    have : Nonempty ↑(Basis.ofVectorSpaceIndex ℝ E) := b.index_nonempty
    exact mdifferentiableAt_orthonormalFrame_of_mem b e i hx
  leibniz {X σ g x} hX hσ hg hx := by
    simp only [lcCandidateAux, hE, ↓reduceDIte]
    let b := Basis.ofVectorSpace ℝ E
    have : Nonempty ↑(Basis.ofVectorSpaceIndex ℝ E) := b.index_nonempty
    let Z (i : (Basis.ofVectorSpaceIndex ℝ E)) := ((Basis.ofVectorSpace ℝ E).orthonormalFrame e i)
    have hZ : IsOrthonormalFrameOn I E 1 Z e.baseSet :=
      (Basis.ofVectorSpace ℝ E).orthonormalFrame_isOrthonormalFrameOn e
    have hZ' : ∑ i, ⟪σ, Z i⟫ x • Z i x = σ x := by
      calc _
        _ = ∑ i, hZ.repr i σ x • Z i x := by
          congr; ext i
          rw [hZ.repr_eq_inner' σ hx i, product_swap]
        _ = σ x := (hZ.toIsLocalFrameOn.repr_sum_eq _ hx).symm
    trans ∑ i, leviCivitaRhs I X (g • σ) (Z i) x • (Z i) x
    · congr
    have (i : (Basis.ofVectorSpaceIndex ℝ E)) : MDiffAt (T% (Z i)) x :=
      mdifferentiableAt_orthonormalFrame_of_mem _ _ i hx
    have aux (i) := leviCivitaRhs_smulY_apply I hg hX hσ (this i)
    simp_rw [aux]
    trans ∑ i, (g x • leviCivitaRhs I X σ (Z i) x • Z i x)
        + ∑ i, ((bar (g x)) ((mfderiv I 𝓘(ℝ, ℝ) g x) (X x)) • ⟪σ, Z i⟫ x) • Z i x
    · simp only [← Finset.sum_add_distrib, add_smul, smul_assoc]
      dsimp
    have : ∑ i, g x • leviCivitaRhs I X σ (Z i) x • Z i x = (g • lcCandidateAux I e o X σ) x := by
      simp only [lcCandidateAux, hE, ↓reduceDIte, Pi.smul_apply', Finset.smul_sum]
      congr
    rw [this]
    simp_rw [← hZ', smul_assoc, Finset.smul_sum]
    dsimp

/-- The candidate definition `lcCandidateAux` is a covariant derivative
on each local trivialisation's domain. -/
lemma isCovariantDerivativeOn_lcCandidateAux [FiniteDimensional ℝ E]
    (e : Trivialization E (TotalSpace.proj : TangentBundle I M → M)) [MemTrivializationAtlas e]
    {o : LinearOrder ↑(Basis.ofVectorSpaceIndex ℝ E)} :
    IsCovariantDerivativeOn E (lcCandidateAux I (M := M) e o) e.baseSet := by
  by_cases hE : Subsingleton E
  · exact (IsCovariantDerivativeOn.of_subsingleton E _).mono (Set.subset_univ _)
  · have : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    exact isCovariantDerivativeOn_lcCandidateAux_of_nonempty I hE e

-- The candidate definition is a covariant derivative on each local frame's domain.
lemma isCovariantDerivativeOn_lcCandidate [FiniteDimensional ℝ E]
    (e : Trivialization E (TotalSpace.proj : TangentBundle I M → M)) [MemTrivializationAtlas e]
    {o : LinearOrder ↑(Basis.ofVectorSpaceIndex ℝ E)} :
    IsCovariantDerivativeOn E (lcCandidate I M o) e.baseSet := by
  apply IsCovariantDerivativeOn.congr (isCovariantDerivativeOn_lcCandidateAux I e (o := o))
  intro X σ x hx
  exact (lcCandidate_eq_lcCandidateAux I X σ e hx).symm

end

variable [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]

variable (M) in
/-- A choice of Levi-Civita connection on the tangent bundle `TM` of a Riemannian manifold `(M, g)`:
this is unique up to the value on non-differentiable vector fields.
If you know the Levi-Civita connection already, you can use `IsLeviCivitaConnection` instead. -/
private noncomputable def LeviCivitaConnection_aux [FiniteDimensional ℝ E]
    (o : LinearOrder ↑(Basis.ofVectorSpaceIndex ℝ E)) :
    CovariantDerivative I E (TangentSpace I : M → Type _) where
  -- This is the existence part of the proof: take the formula derived above
  -- and prove it satisfies all the conditions.
  toFun := lcCandidate I M o
  isCovariantDerivativeOn := by
    rw [← iUnion_source_chartAt H M]
    let t := fun x ↦ trivializationAt E (TangentSpace I : M → Type _) x
    apply IsCovariantDerivativeOn.iUnion (s := fun i ↦ (t i).baseSet) fun i ↦ ?_
    exact isCovariantDerivativeOn_lcCandidate I _

-- TODO: make g part of the notation!
variable (M) in
/-- A choice of Levi-Civita connection on the tangent bundle `TM` of a Riemannian manifold `(M, g)`:
this is unique up to the value on non-differentiable vector fields.
If you know the Levi-Civita connection already, you can use `IsLeviCivitaConnection` instead. -/
noncomputable def LeviCivitaConnection [FiniteDimensional ℝ E] :
    CovariantDerivative I E (TangentSpace I : M → Type _) :=
  LeviCivitaConnection_aux I M (Classical.choose (exists_wellOrder _))

-- TODO: move this section to `Torsion.lean`
section

--omit [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
--omit [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

/-- The **Christoffel symbol** of a covariant derivative on a set `U ⊆ M`
with respect to a local frame `(s_i)` on `U`: for each triple `(i, j, k)` of indices,
this is a function `Γᵢⱼᵏ : M → ℝ`, whose value outside of `U` is meaningless. -/
noncomputable def ChristoffelSymbol
    (f : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x))
    {U : Set M} {ι : Type*} {s : ι → (x : M) → TangentSpace I x}
    (hs : IsLocalFrameOn I E n s U) (i j k : ι) : M → ℝ :=
  hs.repr k (f (s i) (s j))

-- special case of `foobar` below; needed?
lemma ChristoffelSymbol.sum_eq
    (f : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x))
    {U : Set M} {ι : Type*} [Fintype ι] {s : ι → (x : M) → TangentSpace I x}
    (hs : IsLocalFrameOn I E n s U) (i j : ι) (hx : x ∈ U) :
    f (s i) (s j) x = ∑ k, (ChristoffelSymbol I f hs i j k x) • (s k) x := by
  simp only [ChristoffelSymbol]
  exact hs.repr_sum_eq _ hx

variable {U : Set M}
  {f g : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x)}
  {ι : Type*} {s : ι → (x : M) → TangentSpace I x}

-- Note that this result is false if `{s i}` is merely a local frame.
lemma eq_product_apply [Fintype ι]
    (hf : IsCovariantDerivativeOn E f U)
    (hs : IsOrthonormalFrameOn I E n s U)
    (i j k : ι) (hx : x ∈ U) :
    ChristoffelSymbol I f hs.toIsLocalFrameOn i j k x = ⟪f (s i) (s j), (s k)⟫ x := by
  -- Choose a linear order on ι: which one really does not matter for our result.
  have : LinearOrder ι := by
    choose r wo using exists_wellOrder _
    exact r
  have : LocallyFiniteOrderBot ι := by sorry
  rw [ChristoffelSymbol, hs.repr_eq_inner' (f (s i) (s j)) hx k, real_inner_comm]

-- Lemma 4.3 in Lee, Chapter 5: first term still missing
lemma foobar [Fintype ι] [FiniteDimensional ℝ E] (hf : IsCovariantDerivativeOn E f U)
    (hs : IsLocalFrameOn I E 1 s U) {x : M} (hx : x ∈ U) :
    f X Y x = ∑ k,
      letI S₁ := ∑ i, ∑ j, (hs.repr i X) * (hs.repr j Y) * (ChristoffelSymbol I f hs i j k)
      letI S₂ : M → ℝ := sorry -- first summand in Leibniz' rule!
      S₁ x • s k x := by
  have hY := hs.repr_sum_eq Y hx
  -- should this be a separate lemma also?
  have : ∀ x ∈ U, Y x = ∑ i, (hs.repr i) Y x • s i x := by
    intro x hx
    apply hs.repr_sum_eq Y hx
  have : f X Y x = f X (fun x ↦ ∑ i, (hs.repr i) Y x • s i x) x := by
    -- apply `congr_σ_of_eventuallyEq` from Basic.lean (after restoring it)
    -- want U to be a neighbourhood of x to make this work
    sorry
  rw [this]
  -- straightforward computation: use linearity and Leibniz rule
  sorry

/- TODO: prove some basic properties, such as
- the Christoffel symbols are linear in cov
- if (s_i) is a smooth local frame on U, then cov is smooth on U iff each Christoffel symbol is (?)
- prove a `spec` equality
- deduce: two covariant derivatives are equal iff their Christoffel symbols are equal
-/

lemma _root_.IsCovariantDerivativeOn.congr_of_christoffelSymbol_eq [Fintype ι]
    (hf : IsCovariantDerivativeOn E f U) (hg : IsCovariantDerivativeOn E g U)
    (hs : IsLocalFrameOn I E n s U)
    (hfg : ∀ i j k, ∀ x ∈ U, ChristoffelSymbol I f hs i j k x = ChristoffelSymbol I g hs i j k x) :
    ∀ X Y : Π x : M, TangentSpace I x, ∀ x ∈ U, f X Y x = g X Y x := by
  have (i j : ι) : ∀ x ∈ U, f (s i) (s j) x = g (s i) (s j) x := by
    intro x hx
    rw [hs.eq_iff_repr hx]
    exact fun k ↦ hfg i j k x hx
  intro X Y x hx
  -- use linearity (=formula for f in terms of Christoffel symbols) now, another separate lemma!
  sorry

/-- Two covariant derivatives on `U` are equal on `U` if and only if all of their
covariant derivatives w.r.t. some local frame on `U` are equal on `U`. -/
lemma _root_.IsCovariantDerivativeOn.congr_iff_christoffelSymbol_eq [Fintype ι]
    (hf : IsCovariantDerivativeOn E f U) (hg : IsCovariantDerivativeOn E g U)
    (hs : IsLocalFrameOn I E n s U) :
    (∀ X Y : Π x : M, TangentSpace I x, ∀ x ∈ U, f X Y x = g X Y x) ↔
    ∀ i j k, ∀ x ∈ U, ChristoffelSymbol I f hs i j k x = ChristoffelSymbol I g hs i j k x :=
  ⟨fun hfg _i _j _k _x hx ↦ hs.repr_congr (hfg _ _ _ hx ) ..,
    fun h X Y x hx ↦ hf.congr_of_christoffelSymbol_eq I hg hs h X Y x hx⟩

-- TODO: global version for convenience, with an alias for the interesting direction!

variable (hs : IsLocalFrameOn I E n s U)

lemma christoffelSymbol_zero (U : Set M) {ι : Type*} {s : ι → (x : M) → TangentSpace I x}
    (hs : IsLocalFrameOn I E n s U) (i j k : ι) : ChristoffelSymbol I 0 hs i j k = 0 := by
  simp [ChristoffelSymbol]

@[simp]
lemma christoffelSymbol_zero_apply (U : Set M) {ι : Type*} {s : ι → (x : M) → TangentSpace I x}
    (hs : IsLocalFrameOn I E n s U) (i j k : ι) (x) : ChristoffelSymbol I 0 hs i j k x = 0 := by
  simp [christoffelSymbol_zero]

end

-- Lemma 4.3 in Lee, Chapter 5: first term still missing
variable {U : Set M} {ι : Type*} [Fintype ι] {s : ι → (x : M) → TangentSpace I x}
  {f : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x)}

-- errors: omit [IsContMDiffRiemannianBundle I 1 E fun x ↦ TangentSpace I x] in
/-- Let `{s i}` be a local frame on `U` such that `[s i, s j] = 0` on `U` for all `i, j`.
A covariant derivative on `U` is torsion-free on `U` iff for each `x ∈ U`,
the Christoffel symbols `Γᵢⱼᵏ` w.r.t. `{s i}` are symmetric. -/
lemma isTorsionFreeOn_iff_christoffelSymbols [CompleteSpace E] {ι : Type*} [Fintype ι]
    (hf : IsCovariantDerivativeOn E f U)
    {s : ι → (x : M) → TangentSpace I x} (hs : IsLocalFrameOn I E n s U)
    (hs'' : ∀ i j, ∀ x : U, VectorField.mlieBracket I (s i) (s j) x = 0) :
    IsTorsionFreeOn f U ↔
      ∀ i j k, ∀ x ∈ U, ChristoffelSymbol I f hs i j k x = ChristoffelSymbol I f hs j i k x := by
  rw [hf.isTorsionFreeOn_iff_localFrame (n := n) hs]
  have (i j : ι) {x} (hx : x ∈ U) :
      torsion f (s i) (s j) x = f (s i) (s j) x - f (s j) (s i) x := by
    simp [torsion, hs'' i j ⟨x, hx⟩]
  peel with i j
  refine ⟨?_, ?_⟩
  · intro h k x hx
    simp only [ChristoffelSymbol]
    apply hs.repr_congr
    specialize h x hx
    rw [this i j hx, sub_eq_zero] at h
    exact h
  · intro h x hx
    rw [this i j hx, sub_eq_zero, hs.eq_iff_repr hx]
    exact fun k ↦ h k x hx

-- Exercise 4.2(b) in Lee, Chapter 4
/-- A covariant derivative on `U` is torsion-free on `U` iff for each `x ∈ U` and
any local coordinate frame, the Christoffel symbols `Γᵢⱼᵏ` are symmetric.

TODO: figure out the right quantifiers here!
right now, I just have one fixed coordinate frame... will this do??
-/
lemma isTorsionFree_iff_christoffelSymbols' [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    (hf : IsCovariantDerivativeOn E f U) :
    IsTorsionFreeOn f U ↔
      ∀ x ∈ U,
      -- Let `{s_i}` be the coordinate frame at `x`: this statement is false for arbitrary frames.
      -- TODO: does the following do what I want??
      letI cs := ChristoffelSymbol I f
          ((Basis.ofVectorSpace ℝ E).localFrame_isLocalFrameOn_baseSet I 1 (trivializationAt E _ x))
      ∀ i j k, cs i j k x = cs j i k x := by
  letI t := (trivializationAt E (fun (x : M) ↦ TangentSpace I x))
  have hs (x) :=
    ((Basis.ofVectorSpace ℝ E).localFrame_isLocalFrameOn_baseSet I 1 (t x))

  -- TODO: check that the Lie bracket of any two coordinate vector fields is zero!
  rw [isTorsionFreeOn_iff_christoffelSymbols (ι := (↑(Basis.ofVectorSpaceIndex ℝ E))) I hf]
  -- issues with quantifier order in the statement... prove both directions separately, at each x?
  repeat sorry

theorem LeviCivitaConnection.christoffelSymbol_symm [FiniteDimensional ℝ E] (x : M) :
    letI t := trivializationAt E (TangentSpace I) x;
    letI hs := (Basis.ofVectorSpace ℝ E).localFrame_isLocalFrameOn_baseSet I 1 t
    ∀ x', x' ∈ t.baseSet → ∀ (i j k : ↑(Basis.ofVectorSpaceIndex ℝ E)),
      ChristoffelSymbol I (LeviCivitaConnection I M) hs i j k x' =
        ChristoffelSymbol I (LeviCivitaConnection I M) hs j i k x' := by
  by_cases hE : Subsingleton E
  · have (y : M) (X : TangentSpace I y) : X = 0 := by
      have : Subsingleton (TangentSpace I y) := inferInstanceAs (Subsingleton E)
      apply Subsingleton.eq_zero X
    have (X : Π y : M, TangentSpace I y) : X = 0 := sorry
    intro x'' hx'' i j k
    simp only [LeviCivitaConnection, LeviCivitaConnection_aux]
    unfold lcCandidate
    simp only [lcCandidateAux, hE, ↓reduceDIte]

    letI t := trivializationAt E (TangentSpace I) x;
    letI hs := (Basis.ofVectorSpace ℝ E).localFrame_isLocalFrameOn_baseSet I 1 t
    have : ChristoffelSymbol I 0 hs i j k = 0 := christoffelSymbol_zero I t.baseSet hs i j k
    -- now, use a congruence result and the first `have`
    sorry
  -- Note that hs is not necessarily an orthonormal frame, so we cannot simply rewrite
  -- the Christoffel symbols as Γᵢⱼᵏ = ⟪∇ᵍ X Y, Z⟫`: however, the result we wants to prove boils
  -- down to proving the same.
  intro x' hx' i j
  set t := trivializationAt E (TangentSpace I) x
  set b := (Basis.ofVectorSpace ℝ E)
  set s := b.localFrame t
  set ι := ↑(Basis.ofVectorSpaceIndex ℝ E)
  -- Same computation as above; extract as lemma!
  let O : (x : M) → TangentSpace I x := fun x ↦ 0
  have need : ∀ i j, VectorField.mlieBracket I (s i) (s j) x' = O x' := sorry
  have aux : ∀ k, ⟪LeviCivitaConnection I M (s i) (s j), (s k)⟫ x'
      = ⟪LeviCivitaConnection I M (s j) (s i), (s k)⟫ x' := by
    intro k
    simp only [LeviCivitaConnection, LeviCivitaConnection_aux]
    unfold lcCandidate
    rw [product_apply, product_apply]
    simp only [lcCandidateAux, hE, ↓reduceDIte]
    -- Choose a linear order on ι: which one really does not matter for our result.
    have : LinearOrder ι := by
      choose r wo using exists_wellOrder _
      exact r
    have : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    have : Nonempty ι := b.index_nonempty
    -- The linear ordering on the indexing set of `b` is only used in this proof,
    -- so our choice does not matter.
    have : LinearOrder ι := by
      choose r wo using exists_wellOrder _
      exact r
    have : Fintype ι := sorry
    -- why does this fail? are there two different orders in play?
    have : LocallyFiniteOrderBot ι := sorry
    have : ∑ k', inner ℝ
      (leviCivitaRhs I (s i) (s j)
          (b.orthonormalFrame (trivializationAt E (TangentSpace I) x') k') x' •
          b.orthonormalFrame (trivializationAt E (TangentSpace I) x') k' x')
      (s k x') =
       ∑ k', inner ℝ
        (leviCivitaRhs I (s j) (s i)
          (b.orthonormalFrame (trivializationAt E (TangentSpace I) x') k') x' •
          b.orthonormalFrame (trivializationAt E (TangentSpace I) x') k' x')
        (s k x') := by
      congr with k'
      simp only [leviCivitaRhs]
      set sij := b.orthonormalFrame (trivializationAt E (TangentSpace I) x') k' x'
      rw [inner_smul_left, inner_smul_left]
      congr
      simp [leviCivitaRhs']
      set S := b.orthonormalFrame (trivializationAt E (TangentSpace I) x') k'
      have need' : ∀ i, VectorField.mlieBracket I (s i) S x' = O x' := by
        -- expand the definition of Gram-Schmidt and use need and linearity
        sorry
      have need'' : ∀ i, VectorField.mlieBracket I S (s i) x' = O x' := by
        sorry -- swap and use need', or so
      rw [product_congr_right I (need i j), product_congr_right I (need j i),
        product_congr_right I (need' i), product_congr_right I (need'' i),
        product_congr_right I (need' j), product_congr_right I (need'' j),
        rhs_aux_swap I (s i) (s j), rhs_aux_swap I (s j) S, rhs_aux_swap I S (s i)]
      simp [O]
      abel
    -- now, just rewrite `inner` to take out a sum: same lemma twice
    convert this
    sorry
    sorry

  -- deduce the goal from `aux`
  sorry

lemma baz [FiniteDimensional ℝ E] : (LeviCivitaConnection I M).IsLeviCivitaConnection := by
  -- If `E` is trivial, the Levi-Civita connection is always zero and all proofs are trivial.
  by_cases hE : Subsingleton E
  · have (y : M) (X : TangentSpace I y) : X = 0 := by
      have : Subsingleton (TangentSpace I y) := inferInstanceAs (Subsingleton E)
      apply Subsingleton.eq_zero X
    refine ⟨?_, ?_⟩
    · intro X Y Z x
      simp only [LeviCivitaConnection, LeviCivitaConnection_aux]
      unfold lcCandidate
      simp [this]
    · simp only [isTorsionFree_def, LeviCivitaConnection, LeviCivitaConnection_aux]
      unfold lcCandidate torsion
      ext; simp [this]
  refine ⟨?_, ?_⟩
  · intro X Y Z x
    unfold LeviCivitaConnection LeviCivitaConnection_aux lcCandidate
    simp only [lcCandidateAux, hE, ↓reduceDIte]
    --simp [product_apply]
    sorry -- compatible
  · let s : M → Set M := fun x ↦ (trivializationAt E (fun (x : M) ↦ TangentSpace I x) x).baseSet
    apply (LeviCivitaConnection I M).of_isTorsionFreeOn_of_open_cover (s := s) ?_ (by aesop)
    intro x
    simp only [s]
    set t := fun x ↦ trivializationAt E (TangentSpace I : M → Type _) x with t_eq
    have : IsCovariantDerivativeOn E (LeviCivitaConnection I M) (t x).baseSet :=
      isCovariantDerivativeOn_lcCandidate _ (t x)
    rw [isTorsionFree_iff_christoffelSymbols' _ this]
    intro x' hx' i j k
    -- Now, compute christoffel symbols and be happy.
    have := LeviCivitaConnection.christoffelSymbol_symm I x  x' hx' i j k
    sorry -- almost there, except x vs x' convert this

end CovariantDerivative
