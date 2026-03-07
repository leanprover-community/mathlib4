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

open Bundle Function NormedSpace
open scoped Manifold ContDiff

@[expose] public section -- TODO: think if we want to expose all definitions!

-- TODO: revisit and fix this once the dust has settled
set_option backward.isDefEq.respectTransparency false

-- Let `(M, g)` be a `C^k` real manifold modeled on `(E, H)`, endowed with a Riemannian metric `g`.
variable {n : WithTop ℕ∞}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  {X X' X'' Y Y' Y'' Z Z' : Π x : M, TangentSpace I x}

namespace CovariantDerivative

-- Let `cov` be a covariant derivative on `TM`.
-- TODO: include in cheat sheet!
variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))

/-- Local notation for a connection. Caution: `∇ Y, X` corresponds to `∇ₓ Y` in textbooks -/
local notation "∇" Y "," X => fun (x:M) ↦ cov Y x (X x)

variable [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]

/-- A covariant derivative on a Riemannian bundle `TM` is called the **Levi-Civita connection**
iff it is torsion-free and compatible with `g`.
Note that the bundle metric on `TM` is implicitly hidden in this definition. See `TODO` for a
version depending on a choice of Riemannian metric on `M`.
-/
def IsLeviCivitaConnection [FiniteDimensional ℝ E] : Prop := cov.IsCompatible ∧ cov.torsion = 0

local notation "⟪" X ", " Y "⟫" => product X Y

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
omit [IsManifold I 2 M] in
lemma rhs_aux_swap : rhs_aux I X Y Z = rhs_aux I X Z Y := by
  ext x
  simp only [rhs_aux]
  congr 2
  exact product_swap Z Y

omit [IsManifold I 2 M] in
variable (X X' Y Z) in
lemma rhs_aux_addX : rhs_aux I (X + X') Y Z = rhs_aux I X Y Z + rhs_aux I X' Y Z := by
  ext x
  simp [rhs_aux]

variable {x : M}

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

omit [IsManifold I 2 M] in
variable (X Y Z) in
lemma rhs_aux_smulX_apply (f : M → ℝ) (x) : rhs_aux I (f • X) Y Z x = f x • rhs_aux I X Y Z x := by
  simp [rhs_aux]

omit [IsManifold I 2 M] in
variable (X Y Z) in
lemma rhs_aux_smulX (f : M → ℝ) : rhs_aux I (f • X) Y Z = f • rhs_aux I X Y Z := by
  ext x
  exact rhs_aux_smulX_apply ..

variable (X) in
lemma rhs_aux_smulY_apply {f : M → ℝ}
    (hf : MDiffAt f x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    letI A (x) := fromTangentSpace _ ((mfderiv% f x) (X x))
    rhs_aux I X (f • Y) Z x = f x • rhs_aux I X Y Z x + A x • ⟪Y, Z⟫ x := by
  rw [rhs_aux, product_smul_left, mfderiv_smul hf (hY.inner_bundle' hZ)]
  rfl

variable (X) in
lemma rhs_aux_smulY {f : M → ℝ} (hf : MDiff f) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) :
    letI A (x) := fromTangentSpace _ ((mfderiv% f x) (X x))
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
    letI A (x) := fromTangentSpace _ ((mfderiv% f x) (X x))
    rhs_aux I X Y (f • Z) x = f x • rhs_aux I X Y Z x + A x • ⟪Y, Z⟫ x := by
  rw [rhs_aux_swap, rhs_aux_smulY_apply, rhs_aux_swap, product_swap]
  exacts [hf, hZ, hY]

variable (X) in
lemma rhs_aux_smulZ {f : M → ℝ} (hf : MDiff f) (hY : MDiff (T% Y)) (hZ : MDiff (T% Z)) :
    letI A (x) := fromTangentSpace _ ((mfderiv% f x) (X x))
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

omit [IsManifold I 2 M] in
lemma leviCivitaRhs_apply : leviCivitaRhs I X Y Z x = (1 / 2 : ℝ) • leviCivitaRhs' I X Y Z x :=
  rfl

section leviCivitaRhs

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
  rw [product_congr_right₂ (VectorField.mlieBracket_add_right (V := Y) hX hX'),
    product_congr_right₂ (VectorField.mlieBracket_add_left (W := Z) hX hX'),
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

open VectorField NormedSpace

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
      inner ℝ (Y x) ((fromTangentSpace _ (mfderiv% f x (Z x))) • X x) =
        fromTangentSpace (f x) (mfderiv% f x (Z x)) * ⟪X, Y⟫ x := by
    simp only [product]
    rw [← real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, real_inner_comm]
  have h2 :
      inner ℝ (Z x) (fromTangentSpace (f x) ((mfderiv% f x (Y x))) • X x) =
        (fromTangentSpace (f x) (mfderiv% f x (Y x))) * ⟪Z, X⟫ x := by
    simp only [product]
    rw [← real_inner_smul_left, real_inner_smul_right, real_inner_smul_left]
  rw [h1, h2]
  --set dfY := fromTangentSpace (f x) ((mfderiv% f x (Y x)))--(mfderiv% f x) (Y x)
  --set dfZ : ℝ := (mfderiv% f x) (Z x)
  have h3 : ⟪f • X, mlieBracket I Z Y⟫ x = f x * ⟪X, mlieBracket I Z Y⟫ x := by
    rw [product_apply, Pi.smul_apply', real_inner_smul_left]
  have h4 : inner ℝ (Z x) (f x • mlieBracket I Y X x) = f x * ⟪Z, mlieBracket I Y X⟫ x := by
    rw [product_apply, real_inner_smul_right]
  rw [real_inner_smul_right (Y x), h3, h4]
  -- Push all applications of `x` inwards, then it's indeed obvious.
  simp
  -- set A := ⟪Y, mlieBracket I X Z⟫ with hA
  -- set B := ⟪Z, mlieBracket I X Y⟫
  -- set C := ⟪X, mlieBracket I Z Y⟫
  -- set R := dfZ * ⟪X, Y⟫ x with hR
  -- set R' := dfY * ⟪Z, X⟫ x with hR'
  -- set E := rhs_aux I X Y Z x
  -- set F := rhs_aux I Y Z X x
  -- set G := rhs_aux I Z X Y x
  ring_nf

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
  rw [product_congr_right₂ (mlieBracket_add_left (W := X) hY hY')]
  rw [product_congr_right₂ (VectorField.mlieBracket_add_right (V := Z) hY hY')]
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
      f x • leviCivitaRhs' I X Y Z x +
        ((fromTangentSpace _).toFun <| mfderiv% f x (X x)) • 2 * ⟪Y, Z⟫ x := by
  simp only [leviCivitaRhs']
  simp_rw [rhs_aux_smulX I Y Z X f]
  simp only [product_smul_left, Pi.add_apply, Pi.sub_apply, smul_eq_mul, Pi.mul_apply]
  rw [rhs_aux_smulY_apply I X hf hY hZ, rhs_aux_smulZ_apply I Z hf hX hY]
  -- TODO: is there a better abstraction for this kind of "Lie bracket conv mode"?
  have h1 : ⟪Z, mlieBracket I (f • Y) X⟫ x =
      - (fromTangentSpace _).toFun (((mfderiv% f x) (X x))) • ⟪Z, Y⟫ x
      + f x • ⟪Z, mlieBracket I Y X⟫ x := by
    simp_rw [product_apply, mlieBracket_smul_left (W := X) hf hY, inner_add_right]
    congr
    · simp only [neg_smul, inner_neg_right, fromTangentSpace, AddHom.toFun_eq_coe, AddHom.coe_mk,
        smul_eq_mul, neg_mul, neg_inj]
      rw [real_inner_smul_right]
      rfl
    · rw [inner_smul_right_eq_smul]
  have h2 : ⟪X, mlieBracket I Z (f • Y)⟫ x =
      (fromTangentSpace _).toFun (((mfderiv% f x) (Z x))) • ⟪X, Y⟫ x
        + f x • ⟪X, mlieBracket I Z Y⟫ x := by
    simp_rw [product_apply, mlieBracket_smul_right (V := Z) hf hY, inner_add_right]
    congr
    · simp only [fromTangentSpace, AddHom.toFun_eq_coe, AddHom.coe_mk, smul_eq_mul]
      rw [real_inner_smul_right]
      rfl
    · rw [inner_smul_right_eq_smul]
  rw [h1, h2, product_swap Y Z]
  set A := rhs_aux I X Y Z x
  set B := rhs_aux I Y Z X x
  set C := rhs_aux I Z X Y x
  set D := ⟪Y, mlieBracket I X Z⟫ x
  set E := ⟪Z, mlieBracket I Y X⟫ x
  set F := ⟪X, mlieBracket I Z Y⟫ x
  set G1 := ⟪Y, Z⟫ x
  set G2 := ⟪X, Y⟫ x
  set dfx := (mfderiv I 𝓘(ℝ, ℝ) f x)
  set H := (fromTangentSpace (f x)) (dfx (X x)) with H_eq
  set K := (fromTangentSpace (f x)) (dfx (Z x)) with K_eq
  change f x * A + (fromTangentSpace _).toFun (dfx (X x)) * G1 + f x * B
    - (f x * C + (fromTangentSpace _).toFun (dfx (Z x)) * G2)
    - f x * D - (-H * G1 + f x * E) + (K * G2 + f x * F) = _
  dsimp
  rw [← H_eq, ← K_eq]
  ring

lemma leviCivitaRhs_smulY_apply [CompleteSpace E] {f : M → ℝ}
    (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    leviCivitaRhs I X (f • Y) Z x =
      f x • leviCivitaRhs I X Y Z x
        + ((fromTangentSpace _).toFun <| mfderiv% f x (X x)) • ⟪Y, Z⟫ x := by
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
  rw [product_congr_right₂ (VectorField.mlieBracket_add_right (V := X) hZ hZ'),
    product_congr_right₂ (VectorField.mlieBracket_add_left (W := Y) hZ hZ'),
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
      f x • ⟪Y, mlieBracket I X Z⟫ x + ⟪Y, fromTangentSpace _ (mfderiv% f x (X x)) • Z⟫ x := by
    rw [product_apply, VectorField.mlieBracket_smul_right hf hZ, inner_add_right, add_comm,
      inner_smul_right]
    congr
  have h2 : letI dfY := fromTangentSpace _ ((mfderiv% f x) (Y x));
      ⟪X, mlieBracket I (f • Z) Y⟫ x = - dfY • ⟪X, Z⟫ x + f x • ⟪X, mlieBracket I Z Y⟫ x := by
    rw [product_apply, VectorField.mlieBracket_smul_left hf hZ, inner_add_right, inner_smul_right,
      inner_smul_right]
    congr
  rw [h1, h2, product_smul_left, product_swap X Z]
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

lemma leviCivitaRhs_smulZ_apply [CompleteSpace E] {f : M → ℝ}
    (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    leviCivitaRhs I X Y (f • Z) x = f x * leviCivitaRhs I X Y Z x := by
  simp [leviCivitaRhs, leviCivitaRhs'_smulZ_apply I hf hX hY hZ]
  ring

end leviCivitaRhs

variable [FiniteDimensional ℝ E] in
lemma aux (h : cov.IsLeviCivitaConnection) {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) : rhs_aux I X Y Z x =
    ⟪∇ Y, X, Z⟫ x + ⟪Y, ∇ X, Z⟫ x + ⟪Y, VectorField.mlieBracket I X Z⟫ x := by
  trans ⟪∇ Y, X, Z⟫ x + ⟪Y, ∇ Z, X⟫ x
  · exact cov.isCompatible_iff.mp h.1 hX hY hZ
  · simp [← cov.torsion_eq_zero_iff.mp h.2 hX hZ, product, inner_sub_right]

variable {cov} in
/-- Auxiliary lemma towards the uniquness of the Levi-Civita connection: expressing the term
⟨∇ X Y, Z⟩ for all differentiable vector fields X, Y and Z, without reference to ∇. -/
lemma IsLeviCivitaConnection.eq_leviCivitaRhs [FiniteDimensional ℝ E]
    (h : cov.IsLeviCivitaConnection)
    {x : M} (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    ⟪∇ Y, X, Z⟫ x = leviCivitaRhs I X Y Z x := by
  unfold leviCivitaRhs leviCivitaRhs'
  have eq1 := aux I cov h hX hY hZ
  have eq2 := aux I cov h hY hZ hX
  have eq3 := aux I cov h hZ hX hY
  simp [real_inner_comm, smul_eq_mul] at *
  linear_combination - (eq1 + eq2 - eq3) / 2

section

omit [IsManifold I 2 M] [IsContMDiffRiemannianBundle I 1 E (TangentSpace I (M := M))] in
variable {I} in
lemma congr_of_forall_product_apply [FiniteDimensional ℝ E] {Y Y' : TangentSpace I x}
    (h : ∀ Z : TangentSpace I x, inner ℝ Y Z = inner ℝ Y' Z) : Y = Y' := by
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  have : CompleteSpace (TangentSpace I x) := FiniteDimensional.complete ℝ _
  set Φ := InnerProductSpace.toDual ℝ (TangentSpace I x)
  apply Φ.injective
  ext Z₀
  simpa [Φ, product] using h Z₀

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I (M := M))] in
variable {I} in
/-- If two vector fields `X` and `X'` on `M` satisfy the relation `⟨X, Z⟩ = ⟨X', Z⟩` for all
vector fields `Z`, then `X = X'`. XXX up to differentiability? -/
-- TODO: is this true if E is infinite-dimensional? trace the origin of the `Fintype` assumptions!
lemma congr_of_forall_product [FiniteDimensional ℝ E]
    (h : ∀ Z : Π x : M, TangentSpace I x, ⟪X, Z⟫ = ⟪X', Z⟫) : X = X' := by
  ext1 x
  apply congr_of_forall_product_apply
  intro Z₀
  simpa [product] using congr($(h (_root_.extend E Z₀)) x)

/-- The Levi-Civita connection on `(M, g)` is uniquely determined,
at least on differentiable vector fields. -/
-- (probably not everywhere, as addition rules apply only for differentiable vector fields?)
theorem IsLeviCivitaConnection.uniqueness [FiniteDimensional ℝ E]
    {cov cov' : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (hcov : cov.IsLeviCivitaConnection) (hcov' : cov'.IsLeviCivitaConnection)
    {X Y : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    cov Y x (X x) = cov' Y x (X x) := by
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  have : CompleteSpace (TangentSpace I x) := FiniteDimensional.complete ℝ _
  set Φ := InnerProductSpace.toDual ℝ (TangentSpace I x)
  apply Φ.injective
  ext Z₀
  let Z := _root_.extend E Z₀
  have hZ := mdifferentiableAt_extend I E Z₀
  suffices inner ℝ (cov Y x (X x)) (Z x) = inner ℝ (cov' Y x (X x)) (Z x) by simpa [Φ, Z]
  trans leviCivitaRhs I X Y Z x
  · rw [← hcov.eq_leviCivitaRhs I hX hY hZ]
  · rw [← hcov'.eq_leviCivitaRhs I hX hY hZ]

open Classical in
noncomputable def lcAux₀' (Y : Π x : M, TangentSpace I x) (x : M)
    (X Z : Π x : M, TangentSpace I x) :=
  if MDiffAt (T% X) x then if MDiffAt (T% Z) x then
    leviCivitaRhs I X Y Z
  else 0 else 0

theorem leviCivitaRhs_tensorial₁ [FiniteDimensional ℝ E]
    {Y : Π x : M, TangentSpace I x} (x : M) (hY : MDiffAt (T% Y) x) (Z : Π x, TangentSpace I x) :
    TensorialAt I E (lcAux₀' I Y x · Z x) x where
  smul hf hX := by
    dsimp [lcAux₀']
    rw [if_pos hX, if_pos]
    · split_ifs with hZ
      · exact leviCivitaRhs_smulX_apply hf hX hY hZ
      · simp
    · exact hf.smul_section hX
  add hX₁ hX₂ := by
    dsimp [lcAux₀']
    rw [if_pos hX₁, if_pos hX₂, if_pos]
    · split_ifs with hZ
      · exact leviCivitaRhs_addX_apply I hX₁ hX₂ hY hZ
      · simp
    · exact mdifferentiableAt_add_section hX₁ hX₂

theorem leviCivitaRhs_tensorial₂ [FiniteDimensional ℝ E]
    {Y : Π x : M, TangentSpace I x} (x : M) (hY : MDiffAt (T% Y) x) (X : Π x, TangentSpace I x)
    (hX : MDiffAt (T% X) x) :
    TensorialAt I E (lcAux₀' I Y x X · x) x where
  smul hf hZ := by
    dsimp [lcAux₀']
    rw [if_pos hX, if_pos hZ, if_pos, if_pos hX]
    · exact leviCivitaRhs_smulZ_apply I hf hX hY hZ
    · exact hf.smul_section hZ
  add hZ₁ hZ₂ := by
    dsimp [lcAux₀']
    rw [if_pos hZ₁, if_pos hZ₂, if_pos hX, if_pos, if_pos hX, if_pos hX]
    · exact leviCivitaRhs_addZ_apply I hX hY hZ₁ hZ₂
    · exact mdifferentiableAt_add_section hZ₁ hZ₂

open Classical in
noncomputable def lcAux₀ [FiniteDimensional ℝ E]
    {Y : Π x : M, TangentSpace I x} (x : M) (hY : MDiffAt (T% Y) x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  TensorialAt.mkHom₂ _ (x := x)
    (fun Z _ ↦ leviCivitaRhs_tensorial₁ _ _ hY Z)
    (fun X hX ↦ leviCivitaRhs_tensorial₂ _ _ hY X hX)

theorem lcAux₀_apply [FiniteDimensional ℝ E] {x : M}
    {X : Π x : M, TangentSpace I x} (hX : MDiffAt (T% X) x)
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x)
    {Z : Π x : M, TangentSpace I x} (hZ : MDiffAt (T% Z) x) :
    lcAux₀ I x hY (X x) (Z x) = leviCivitaRhs I X Y Z x := by
  unfold lcAux₀
  rw [TensorialAt.mkHom₂_apply _ _ hX hZ, lcAux₀', if_pos hX, if_pos hZ]

noncomputable def lcAux₁ [FiniteDimensional ℝ E]
    {Y : Π x : M, TangentSpace I x} (x : M) (hY : MDiffAt (T% Y) x) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  -- use the musical isomorphism to produce a candidate ∇ Y as a (1,1)-tensor
  -- (rather than a 2-tensor)
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  have : CompleteSpace (TangentSpace I x) := FiniteDimensional.complete ℝ _
  (InnerProductSpace.toDual ℝ _).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (lcAux₀ I x hY)

theorem lcAux₁_apply [FiniteDimensional ℝ E] {x : M}
    {X : Π x : M, TangentSpace I x} (hX : MDiffAt (T% X) x)
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x)
    {Z : Π x : M, TangentSpace I x} (hZ : MDiffAt (T% Z) x) :
    inner ℝ (lcAux₁ I x hY (X x)) (Z x) = leviCivitaRhs I X Y Z x := by
  simpa [lcAux₁] using lcAux₀_apply I hX hY hZ

open Classical in
noncomputable def lcAux [FiniteDimensional ℝ E]
    (Y : Π x : M, TangentSpace I x) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  if hY : MDiffAt (T% Y) x then lcAux₁ I x hY else 0

theorem lcAux_apply [FiniteDimensional ℝ E] {x : M}
    {X : Π x : M, TangentSpace I x} (hX : MDiffAt (T% X) x)
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x)
    {Z : Π x : M, TangentSpace I x} (hZ : MDiffAt (T% Z) x) :
    inner ℝ (lcAux I Y x (X x)) (Z x) = leviCivitaRhs I X Y Z x := by
  unfold lcAux
  rw [dif_pos hY]
  simpa [lcAux] using lcAux₁_apply I hX hY hZ

lemma isCovariantDerivativeOn_lcAux [FiniteDimensional ℝ E] :
    IsCovariantDerivativeOn E (lcAux I (M := M)) where
  add {Y Y'} x hY hY' _ := by
    unfold lcAux
    rw [dif_pos hY, dif_pos hY', dif_pos (mdifferentiableAt_add_section hY hY')]
    unfold lcAux₁
    dsimp
    rw [← ContinuousLinearMap.comp_add]
    congr! 1
    simp only [lcAux₀]
    ext X₀ Y₀
    simp only [TensorialAt.mkHom₂_apply_eq_extend, ContinuousLinearMap.add_apply, lcAux₀']
    rw [if_pos, if_pos, if_pos, if_pos, if_pos, if_pos]
    · exact leviCivitaRhs_addY_apply _ (FiberBundle.mdifferentiableAt_extend ..)
        hY hY' (FiberBundle.mdifferentiableAt_extend ..)
    · exact FiberBundle.mdifferentiableAt_extend ..
    · exact FiberBundle.mdifferentiableAt_extend ..
    · exact FiberBundle.mdifferentiableAt_extend ..
    · exact FiberBundle.mdifferentiableAt_extend ..
    · exact FiberBundle.mdifferentiableAt_extend ..
    · exact FiberBundle.mdifferentiableAt_extend ..
  leibniz {Y f x} hY hf _ := by
    unfold lcAux
    dsimp
    rw [dif_pos hY, dif_pos]
    · unfold lcAux₁
      dsimp
      rw [← ContinuousLinearMap.comp_smul]
      have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
      have : CompleteSpace (TangentSpace I x) := FiniteDimensional.complete ℝ _
      set Φ := InnerProductSpace.toDual ℝ (TangentSpace I x)
      ext X₀
      apply Φ.injective
      simp only [ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe,
        LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv, comp_apply,
        LinearIsometryEquiv.apply_symm_apply, ContinuousLinearMap.comp_smulₛₗ, RingHom.id_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
        ContinuousLinearMap.toSpanSingleton_apply, map_add, map_smul]
      ext Z₀
      simp only [lcAux₀, lcAux₀', TensorialAt.mkHom₂_apply_eq_extend,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
      rw [if_pos, if_pos, if_pos, if_pos]
      · convert leviCivitaRhs_smulY_apply I (Z := FiberBundle.extend E Z₀) (x := x)
          hf (FiberBundle.mdifferentiableAt_extend I E X₀) hY
          (FiberBundle.mdifferentiableAt_extend I E Z₀)
        · simp
        · simp [Φ, product]
      · exact FiberBundle.mdifferentiableAt_extend ..
      · exact FiberBundle.mdifferentiableAt_extend ..
      · exact FiberBundle.mdifferentiableAt_extend ..
      · exact FiberBundle.mdifferentiableAt_extend ..
    exact MDifferentiableAt.smul_section hf hY

end

-- TODO: make g part of the notation!
variable (M) in
/-- A choice of Levi-Civita connection on the tangent bundle `TM` of a Riemannian manifold `(M, g)`:
this is unique up to the value on non-differentiable vector fields.
If you know the Levi-Civita connection already, you can use `IsLeviCivitaConnection` instead. -/
noncomputable def LeviCivitaConnection [FiniteDimensional ℝ E] :
    CovariantDerivative I E (TangentSpace I : M → Type _) where
  toFun := lcAux I
  isCovariantDerivativeOnUniv := isCovariantDerivativeOn_lcAux I

theorem leviCivitaConnection_apply [FiniteDimensional ℝ E] {x : M}
    {X : Π x : M, TangentSpace I x} (hX : MDiffAt (T% X) x)
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x)
    {Z : Π x : M, TangentSpace I x} (hZ : MDiffAt (T% Z) x) :
    inner ℝ (LeviCivitaConnection I M Y x (X x)) (Z x) = leviCivitaRhs I X Y Z x :=
  lcAux_apply _ hX hY hZ

-- Side computation for `leviCivitaConnection_isCompatible`.
omit [IsManifold I 2 M] in
lemma leviCivitaConnection_isCompatible_aux
    {x : M} {X Y Z : (x : M) → TangentSpace I x} :
    leviCivitaRhs I X Y Z x + leviCivitaRhs I X Z Y x =
    fromTangentSpace _ ((mfderiv% fun x ↦ inner ℝ (Y x) (Z x)) x (X x)) := by
  simp only [leviCivitaRhs, Pi.smul_apply, ← smul_add,  leviCivitaRhs']
  -- Normalise the expressions by swapping arguments for rhs_aux and mlieBracket,
  -- until the swappable arguments are in order X < Y < Z.
  rw [rhs_aux_swap I Z Y, rhs_aux_swap I Z X, rhs_aux_swap I Y X,
    VectorField.mlieBracket_swap (V := Z) (W := Y),
    VectorField.mlieBracket_swap (V := Y) (W := X),
    VectorField.mlieBracket_swap (V := Z) (W := X)]
  -- Observe that the right hand side is rhx_aux X Y Z; then we just need to simplify and rearrange.
  trans 1 / 2 * (rhs_aux I X Y Z x + rhs_aux I X Y Z x)
  · simp
    abel
  · rw [← two_mul, ← mul_assoc, one_div, inv_mul_cancel₀ (by simp), one_mul]
    rfl

-- Why is everything so slow?
lemma leviCivitaConnection_isCompatible [FiniteDimensional ℝ E] :
    (LeviCivitaConnection I M).IsCompatible := by
  rw [isCompatible_iff]
  intro x X Y Z hX hY hZ
  symm
  unfold product
  dsimp
  rw [leviCivitaConnection_apply I hX hY hZ]
  have : inner ℝ (Y x) (((LeviCivitaConnection I M) Z x) (X x)) =
      inner ℝ (((LeviCivitaConnection I M) Z x) (X x)) (Y x) := by
    rw [real_inner_comm]
  -- TODO: why does the following line not work, but `rw [this]` does?
  --rw [real_inner_comm]
  rw [this]
  have : inner ℝ (((LeviCivitaConnection I M) Z x) (X x)) (Y x) = leviCivitaRhs I X Z Y x := by
    rw [leviCivitaConnection_apply I hX hZ hY]
  rw [leviCivitaConnection_apply I hX hZ hY, leviCivitaConnection_isCompatible_aux]

lemma leviCivitaConnection_torsion_eq_zero [FiniteDimensional ℝ E] :
    (LeviCivitaConnection I M).torsion = 0 := by
  have a := (LeviCivitaConnection I M).isCovariantDerivativeOnUniv
  rw [CovariantDerivative.torsion_eq_zero_iff]
  intro X Y x hX hY
  apply congr_of_forall_product_apply
  intro Z
  trans (inner ℝ (((LeviCivitaConnection I M) Y x) (X x)) Z) -
    (inner ℝ (((LeviCivitaConnection I M) X x) (Y x)) Z)
  · apply inner_sub_left
  have hZ' : _root_.extend E Z x = Z := extend_apply_self Z
  rw [← hZ']
  rw [leviCivitaConnection_apply I hY hX (mdifferentiableAt_extend ..)]
  rw [leviCivitaConnection_apply I hX hY (mdifferentiableAt_extend ..)]
  simp only [leviCivitaRhs_apply]
  -- XXX: should there be leviCivitaRhs'_apply?
  simp only [leviCivitaRhs', Pi.add_apply, Pi.sub_apply, product_apply]
  simp only [VectorField.mlieBracket_swap (V := Y) (W := X)]
  simp only [Pi.neg_apply, inner_neg_right, sub_neg_eq_add]
  set C := inner ℝ Z (VectorField.mlieBracket I X Y x)
  set Z' := _root_.extend E Z
  simp only [VectorField.mlieBracket_swap (V := Z') (W := X)]
  simp only [VectorField.mlieBracket_swap (V := Z') (W := Y)]
  simp only [Pi.neg_apply, inner_neg_right]
  rw [rhs_aux_swap (Y := Z'), rhs_aux_swap (Y := Z'), rhs_aux_swap (X := Z')]
  rw [real_inner_comm (Z' x) (VectorField.mlieBracket I X Y x)]
  -- set A := inner ℝ (Z' x) (VectorField.mlieBracket I X Y x)
  -- set B := inner ℝ (Y x) (VectorField.mlieBracket I X Z' x)
  -- set C := inner ℝ (X x) (VectorField.mlieBracket I Y Z' x)
  -- set D := rhs_aux I X Y Z' x
  -- set E := rhs_aux I Y X Z' x
  -- set F := rhs_aux I Z' X Y x
  match_scalars <;> simp
  norm_num

/-- `LeviCivitaConnection` is a Levi-Civita connection (i.e., compatible and torsion-free) -/
lemma leviCivitaConnection_isLeviCivitaConnection [FiniteDimensional ℝ E] :
    (LeviCivitaConnection I M).IsLeviCivitaConnection :=
  ⟨leviCivitaConnection_isCompatible I, leviCivitaConnection_torsion_eq_zero I⟩

end CovariantDerivative
