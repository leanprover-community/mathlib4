/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis
-/
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic

/-!
# Inner product spaces

This file defines inner product spaces.  We do not formally define Hilbert spaces, but they can be
obtained using the set of assumptions
`[NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]`.

An inner product space is a vector space endowed with an inner product. It generalizes the notion of
dot product in `ℝ^n` and provides the means of defining the length of a vector and the angle between
two vectors. In particular vectors `x` and `y` are orthogonal if their inner product equals zero.
We define both the real and complex cases at the same time using the `RCLike` typeclass.

Rather than defining the norm on an inner product space to be `√(re ⟪x, x⟫)`, we assume that a norm
is given, and add a hypothesis stating that `‖x‖ ^ 2 = re (inner x x)`. This makes it possible to
handle spaces where the norm is equal, but not defeq, to the square root of the
inner product. Defining a norm starting from an inner product is handled via the
`InnerProductSpace.Core` structure.

This file is intended to contain the minimal amount of machinery needed to define inner product
spaces, and to construct a normed space from an inner product space. Many more general lemmas can
be found in `Analysis.InnerProductSpace.Basic`. For the specific construction of an inner product
structure on `n → 𝕜` for `𝕜 = ℝ` or `ℂ`, see `EuclideanSpace` in
`Analysis.InnerProductSpace.PiL2`.

## Main results

- We define the class `InnerProductSpace 𝕜 E` extending `NormedSpace 𝕜 E` with a number of basic
  properties, most notably the Cauchy-Schwarz inequality. Here `𝕜` is understood to be either `ℝ`
  or `ℂ`, through the `RCLike` typeclass.

## Notation

We globally denote the real and complex inner products by `⟪·, ·⟫_ℝ` and `⟪·, ·⟫_ℂ` respectively.
We also provide two notation namespaces: `RealInnerProductSpace`, `ComplexInnerProductSpace`,
which respectively introduce the plain notation `⟪·, ·⟫` for the real and complex inner product.

## Implementation notes

We choose the convention that inner products are conjugate linear in the first argument and linear
in the second.

## Tags

inner product space, Hilbert space, norm

## References
* [Clément & Martin, *The Lax-Milgram Theorem. A detailed proof to be formalized in Coq*]
* [Clément & Martin, *A Coq formal proof of the Lax–Milgram theorem*]

The Coq code is available at the following address: <http://www.lri.fr/~sboldo/elfic/index.html>
-/


noncomputable section

open RCLike Real Filter Topology ComplexConjugate Finsupp

open LinearMap (BilinForm)

variable {𝕜 E F : Type*} [RCLike 𝕜]

/-- Syntactic typeclass for types endowed with an inner product -/
class Inner (𝕜 E : Type*) where
  /-- The inner product function. -/
  inner : E → E → 𝕜

export Inner (inner)

/-- The inner product with values in `𝕜`. -/
scoped[InnerProductSpace] notation3:max "⟪" x ", " y "⟫_" 𝕜:max => @inner 𝕜 _ _ x y

section Notations

/-- The inner product with values in `ℝ`. -/
scoped[RealInnerProductSpace] notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- The inner product with values in `ℂ`. -/
scoped[ComplexInnerProductSpace] notation "⟪" x ", " y "⟫" => @inner ℂ _ _ x y

end Notations

/-- A (pre) inner product space is a vector space with an additional operation called inner product.
The (semi)norm could be derived from the inner product, instead we require the existence of a
seminorm and the fact that `‖x‖^2 = re ⟪x, x⟫` to be able to put instances on `𝕂` or product spaces.

Note that `NormedSpace` does not assume that `‖x‖=0` implies `x=0` (it is rather a seminorm).

To construct a seminorm from an inner product, see `PreInnerProductSpace.ofCore`.
-/
class InnerProductSpace (𝕜 : Type*) (E : Type*) [RCLike 𝕜] [SeminormedAddCommGroup E] extends
  NormedSpace 𝕜 E, Inner 𝕜 E where
  /-- The inner product induces the norm. -/
  norm_sq_eq_inner : ∀ x : E, ‖x‖ ^ 2 = re (inner x x)
  /-- The inner product is *hermitian*, taking the `conj` swaps the arguments. -/
  conj_symm : ∀ x y, conj (inner y x) = inner x y
  /-- The inner product is additive in the first coordinate. -/
  add_left : ∀ x y z, inner (x + y) z = inner x z + inner y z
  /-- The inner product is conjugate linear in the first coordinate. -/
  smul_left : ∀ x y r, inner (r • x) y = conj r * inner x y

/-!
### Constructing a normed space structure from an inner product

In the definition of an inner product space, we require the existence of a norm, which is equal
(but maybe not defeq) to the square root of the scalar product. This makes it possible to put
an inner product space structure on spaces with a preexisting norm (for instance `ℝ`), with good
properties. However, sometimes, one would like to define the norm starting only from a well-behaved
scalar product. This is what we implement in this paragraph, starting from a structure
`InnerProductSpace.Core` stating that we have a nice scalar product.

Our goal here is not to develop a whole theory with all the supporting API, as this will be done
below for `InnerProductSpace`. Instead, we implement the bare minimum to go as directly as
possible to the construction of the norm and the proof of the triangular inequality.

Warning: Do not use this `Core` structure if the space you are interested in already has a norm
instance defined on it, otherwise this will create a second non-defeq norm instance!
-/

/-- A structure requiring that a scalar product is positive semidefinite and symmetric. -/
structure PreInnerProductSpace.Core (𝕜 : Type*) (F : Type*) [RCLike 𝕜] [AddCommGroup F]
  [Module 𝕜 F] extends Inner 𝕜 F where
  /-- The inner product is *hermitian*, taking the `conj` swaps the arguments. -/
  conj_symm : ∀ x y, conj (inner y x) = inner x y
  /-- The inner product is positive (semi)definite. -/
  nonneg_re : ∀ x, 0 ≤ re (inner x x)
  /-- The inner product is additive in the first coordinate. -/
  add_left : ∀ x y z, inner (x + y) z = inner x z + inner y z
  /-- The inner product is conjugate linear in the first coordinate. -/
  smul_left : ∀ x y r, inner (r • x) y = conj r * inner x y

attribute [class] PreInnerProductSpace.Core

/-- A structure requiring that a scalar product is positive definite. Some theorems that
require this assumptions are put under section `InnerProductSpace.Core`. -/
-- @[nolint HasNonemptyInstance] porting note: I don't think we have this linter anymore
structure InnerProductSpace.Core (𝕜 : Type*) (F : Type*) [RCLike 𝕜] [AddCommGroup F]
  [Module 𝕜 F] extends PreInnerProductSpace.Core 𝕜 F where
  /-- The inner product is positive definite. -/
  definite : ∀ x, inner x x = 0 → x = 0

/- We set `InnerProductSpace.Core` to be a class as we will use it as such in the construction
of the normed space structure that it produces. However, all the instances we will use will be
local to this proof. -/
attribute [class] InnerProductSpace.Core

instance (𝕜 : Type*) (F : Type*) [RCLike 𝕜] [AddCommGroup F]
  [Module 𝕜 F] [cd : InnerProductSpace.Core 𝕜 F] : PreInnerProductSpace.Core 𝕜 F where
  inner := cd.inner
  conj_symm := cd.conj_symm
  nonneg_re := cd.nonneg_re
  add_left := cd.add_left
  smul_left := cd.smul_left

/-- Define `PreInnerProductSpace.Core` from `PreInnerProductSpace`. Defined to reuse lemmas about
`PreInnerProductSpace.Core` for `PreInnerProductSpace`s. Note that the `Seminorm` instance provided
by `PreInnerProductSpace.Core.norm` is propositionally but not definitionally equal to the original
norm. -/
def PreInnerProductSpace.toCore [SeminormedAddCommGroup E] [c : InnerProductSpace 𝕜 E] :
    PreInnerProductSpace.Core 𝕜 E :=
  { c with
    nonneg_re := fun x => by
      rw [← InnerProductSpace.norm_sq_eq_inner]
      apply sq_nonneg }

/-- Define `InnerProductSpace.Core` from `InnerProductSpace`. Defined to reuse lemmas about
`InnerProductSpace.Core` for `InnerProductSpace`s. Note that the `Norm` instance provided by
`InnerProductSpace.Core.norm` is propositionally but not definitionally equal to the original
norm. -/
def InnerProductSpace.toCore [NormedAddCommGroup E] [c : InnerProductSpace 𝕜 E] :
    InnerProductSpace.Core 𝕜 E :=
  { c with
    nonneg_re := fun x => by
      rw [← InnerProductSpace.norm_sq_eq_inner]
      apply sq_nonneg
    definite := fun x hx =>
      norm_eq_zero.1 <| pow_eq_zero (n := 2) <| by
        rw [InnerProductSpace.norm_sq_eq_inner (𝕜 := 𝕜) x, hx, map_zero] }

namespace InnerProductSpace.Core

section PreInnerProductSpace.Core

variable [AddCommGroup F] [Module 𝕜 F] [c : PreInnerProductSpace.Core 𝕜 F]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 F _ x y

local notation "normSqK" => @RCLike.normSq 𝕜 _

local notation "reK" => @RCLike.re 𝕜 _

local notation "ext_iff" => @RCLike.ext_iff 𝕜 _

local postfix:90 "†" => starRingEnd _

/-- Inner product defined by the `PreInnerProductSpace.Core` structure. We can't reuse
`PreInnerProductSpace.Core.toInner` because it takes `PreInnerProductSpace.Core` as an explicit
argument. -/
def toPreInner' : Inner 𝕜 F :=
  c.toInner

attribute [local instance] toPreInner'

/-- The norm squared function for `PreInnerProductSpace.Core` structure. -/
def normSq (x : F) :=
  reK ⟪x, x⟫

local notation "normSqF" => @normSq 𝕜 F _ _ _ _

theorem inner_conj_symm (x y : F) : ⟪y, x⟫† = ⟪x, y⟫ :=
  c.conj_symm x y

theorem inner_self_nonneg {x : F} : 0 ≤ re ⟪x, x⟫ :=
  c.nonneg_re _

theorem inner_self_im (x : F) : im ⟪x, x⟫ = 0 := by
  rw [← @ofReal_inj 𝕜, im_eq_conj_sub]
  simp [inner_conj_symm]

theorem inner_add_left (x y z : F) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ :=
  c.add_left _ _ _

theorem inner_add_right (x y z : F) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ := by
  rw [← inner_conj_symm, inner_add_left, RingHom.map_add]; simp only [inner_conj_symm]

theorem ofReal_normSq_eq_inner_self (x : F) : (normSqF x : 𝕜) = ⟪x, x⟫ := by
  rw [ext_iff]
  exact ⟨by simp only [ofReal_re]; rfl, by simp only [inner_self_im, ofReal_im]⟩

theorem inner_re_symm (x y : F) : re ⟪x, y⟫ = re ⟪y, x⟫ := by rw [← inner_conj_symm, conj_re]

theorem inner_im_symm (x y : F) : im ⟪x, y⟫ = -im ⟪y, x⟫ := by rw [← inner_conj_symm, conj_im]

theorem inner_smul_left (x y : F) {r : 𝕜} : ⟪r • x, y⟫ = r† * ⟪x, y⟫ :=
  c.smul_left _ _ _

theorem inner_smul_right (x y : F) {r : 𝕜} : ⟪x, r • y⟫ = r * ⟪x, y⟫ := by
  rw [← inner_conj_symm, inner_smul_left]
  simp only [conj_conj, inner_conj_symm, RingHom.map_mul]

theorem inner_zero_left (x : F) : ⟪0, x⟫ = 0 := by
  rw [← zero_smul 𝕜 (0 : F), inner_smul_left]
  simp only [zero_mul, RingHom.map_zero]

theorem inner_zero_right (x : F) : ⟪x, 0⟫ = 0 := by
  rw [← inner_conj_symm, inner_zero_left]; simp only [RingHom.map_zero]

theorem inner_self_of_eq_zero {x : F} : x = 0 → ⟪x, x⟫ = 0 := by
  rintro rfl
  exact inner_zero_left _

theorem normSq_eq_zero_of_eq_zero {x : F} : x = 0 → normSqF x = 0 := by
  rintro rfl
  simp [normSq, inner_self_of_eq_zero]

theorem ne_zero_of_inner_self_ne_zero {x : F} : ⟪x, x⟫ ≠ 0 → x ≠ 0 :=
  mt inner_self_of_eq_zero
theorem inner_self_ofReal_re (x : F) : (re ⟪x, x⟫ : 𝕜) = ⟪x, x⟫ := by
  norm_num [ext_iff, inner_self_im]

theorem norm_inner_symm (x y : F) : ‖⟪x, y⟫‖ = ‖⟪y, x⟫‖ := by rw [← inner_conj_symm, norm_conj]

theorem inner_neg_left (x y : F) : ⟪-x, y⟫ = -⟪x, y⟫ := by
  rw [← neg_one_smul 𝕜 x, inner_smul_left]
  simp

theorem inner_neg_right (x y : F) : ⟪x, -y⟫ = -⟪x, y⟫ := by
  rw [← inner_conj_symm, inner_neg_left]; simp only [RingHom.map_neg, inner_conj_symm]

theorem inner_sub_left (x y z : F) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ := by
  simp [sub_eq_add_neg, inner_add_left, inner_neg_left]

theorem inner_sub_right (x y z : F) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ := by
  simp [sub_eq_add_neg, inner_add_right, inner_neg_right]

theorem inner_mul_symm_re_eq_norm (x y : F) : re (⟪x, y⟫ * ⟪y, x⟫) = ‖⟪x, y⟫ * ⟪y, x⟫‖ := by
  rw [← inner_conj_symm, mul_comm]
  exact re_eq_norm_of_mul_conj (inner y x)

/-- Expand `inner (x + y) (x + y)` -/
theorem inner_add_add_self (x y : F) : ⟪x + y, x + y⟫ = ⟪x, x⟫ + ⟪x, y⟫ + ⟪y, x⟫ + ⟪y, y⟫ := by
  simp only [inner_add_left, inner_add_right]; ring

-- Expand `inner (x - y) (x - y)`
theorem inner_sub_sub_self (x y : F) : ⟪x - y, x - y⟫ = ⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫ := by
  simp only [inner_sub_left, inner_sub_right]; ring

theorem inner_smul_ofReal_left (x y : F) {t : ℝ} : ⟪(t : 𝕜) • x, y⟫ = ⟪x, y⟫ * t := by
  rw [inner_smul_left, conj_ofReal, mul_comm]

theorem inner_smul_ofReal_right (x y : F) {t : ℝ} : ⟪x, (t : 𝕜) • y⟫ = ⟪x, y⟫ * t := by
  rw [inner_smul_right, mul_comm]

theorem re_inner_smul_ofReal_smul_self (x : F) {t : ℝ} :
    re ⟪(t : 𝕜) • x, (t : 𝕜) • x⟫ = normSqF x * t * t := by
  apply ofReal_injective (K := 𝕜)
  simp [inner_self_ofReal_re, inner_smul_ofReal_left, inner_smul_ofReal_right, normSq]

/-- An auxiliary equality useful to prove the **Cauchy–Schwarz inequality**. Here we use the
standard argument involving the discriminant of quadratic form. -/
lemma cauchy_schwarz_aux' (x y : F) (t : ℝ) : 0 ≤ normSqF x * t * t + 2 * re ⟪x, y⟫ * t
    + normSqF y := by
  calc 0 ≤ re ⟪(ofReal t : 𝕜) • x + y, (ofReal t : 𝕜) • x + y⟫ := inner_self_nonneg
  _ = re (⟪(ofReal t : 𝕜) • x, (ofReal t : 𝕜) • x⟫ + ⟪(ofReal t : 𝕜) • x, y⟫
      + ⟪y, (ofReal t : 𝕜) • x⟫ + ⟪y, y⟫) := by rw [inner_add_add_self ((ofReal t : 𝕜) • x) y]
  _ = re ⟪(ofReal t : 𝕜) • x, (ofReal t : 𝕜) • x⟫
      + re ⟪(ofReal t : 𝕜) • x, y⟫ + re ⟪y, (ofReal t : 𝕜) • x⟫ + re ⟪y, y⟫ := by
      simp only [map_add]
  _ = normSq x * t * t + re (⟪x, y⟫ * t) + re (⟪y, x⟫ * t) + re ⟪y, y⟫ := by rw
    [re_inner_smul_ofReal_smul_self, inner_smul_ofReal_left, inner_smul_ofReal_right]
  _ = normSq x * t * t + re ⟪x, y⟫ * t + re ⟪y, x⟫ * t + re ⟪y, y⟫ := by rw [mul_comm ⟪x,y⟫ _,
    RCLike.re_ofReal_mul, mul_comm t _, mul_comm ⟪y,x⟫ _, RCLike.re_ofReal_mul, mul_comm t _]
  _ = normSq x * t * t + re ⟪x, y⟫ * t + re ⟪y, x⟫ * t + normSq y := by rw [← normSq]
  _ = normSq x * t * t + re ⟪x, y⟫ * t + re ⟪x, y⟫ * t + normSq y := by rw [inner_re_symm]
  _ = normSq x * t * t + 2 * re ⟪x, y⟫ * t + normSq y := by ring

/-- Another auxiliary equality related with the **Cauchy–Schwarz inequality**: the square of the
seminorm of `⟪x, y⟫ • x - ⟪x, x⟫ • y` is equal to `‖x‖ ^ 2 * (‖x‖ ^ 2 * ‖y‖ ^ 2 - ‖⟪x, y⟫‖ ^ 2)`.
We use `InnerProductSpace.ofCore.normSq x` etc (defeq to `is_R_or_C.re ⟪x, x⟫`) instead of `‖x‖ ^ 2`
etc to avoid extra rewrites when applying it to an `InnerProductSpace`. -/
theorem cauchy_schwarz_aux (x y : F) : normSqF (⟪x, y⟫ • x - ⟪x, x⟫ • y)
    = normSqF x * (normSqF x * normSqF y - ‖⟪x, y⟫‖ ^ 2) := by
  rw [← @ofReal_inj 𝕜, ofReal_normSq_eq_inner_self]
  simp only [inner_sub_sub_self, inner_smul_left, inner_smul_right, conj_ofReal, mul_sub, ←
    ofReal_normSq_eq_inner_self x, ← ofReal_normSq_eq_inner_self y]
  rw [← mul_assoc, mul_conj, RCLike.conj_mul, mul_left_comm, ← inner_conj_symm y, mul_conj]
  push_cast
  ring

/-- **Cauchy–Schwarz inequality**.
We need this for the `PreInnerProductSpace.Core` structure to prove the triangle inequality below
when showing the core is a normed group and to take the quotient.

(This is not intended for general use; see `Analysis.InnerProductSpace.Basic` for a variety of
versions of Cauchy-Schwartz for an inner product space, rather than a `PreInnerProductSpace.Core`).
-/
theorem inner_mul_inner_self_le (x y : F) : ‖⟪x, y⟫‖ * ‖⟪y, x⟫‖ ≤ re ⟪x, x⟫ * re ⟪y, y⟫ := by
  suffices discrim (normSqF x) (2 * ‖⟪x, y⟫_𝕜‖) (normSqF y) ≤ 0 by
    rw [norm_inner_symm y x]
    rw [discrim, normSq, normSq, sq] at this
    linarith
  refine discrim_le_zero fun t ↦ ?_
  by_cases hzero : ⟪x, y⟫ = 0
  · simp only [mul_assoc, ← sq, hzero, norm_zero, mul_zero, zero_mul, add_zero, ge_iff_le]
    obtain ⟨hx, hy⟩ : (0 ≤ normSqF x ∧ 0 ≤ normSqF y) := ⟨inner_self_nonneg, inner_self_nonneg⟩
    positivity
  · have hzero' : ‖⟪x, y⟫‖ ≠ 0 := norm_ne_zero_iff.2 hzero
    convert cauchy_schwarz_aux' (𝕜 := 𝕜) (⟪x, y⟫ • x) y (t / ‖⟪x, y⟫‖) using 3
    · field_simp
      rw [← sq, normSq, normSq, inner_smul_right, inner_smul_left, ← mul_assoc _ _ ⟪x, x⟫,
        mul_conj]
      nth_rw 2 [sq]
      rw [← ofReal_mul, re_ofReal_mul]
      ring
    · field_simp
      rw [inner_smul_left, mul_comm _ ⟪x, y⟫_𝕜, mul_conj, ← ofReal_pow, ofReal_re]
      ring

/-- (Semi)norm constructed from an `PreInnerProductSpace.Core` structure, defined to be the square
root of the scalar product. -/
def toNorm : Norm F where norm x := √(re ⟪x, x⟫)

attribute [local instance] toNorm

theorem norm_eq_sqrt_inner (x : F) : ‖x‖ = √(re ⟪x, x⟫) := rfl

theorem inner_self_eq_norm_mul_norm (x : F) : re ⟪x, x⟫ = ‖x‖ * ‖x‖ := by
  rw [norm_eq_sqrt_inner, ← sqrt_mul inner_self_nonneg (re ⟪x, x⟫), sqrt_mul_self inner_self_nonneg]

theorem sqrt_normSq_eq_norm (x : F) : √(normSqF x) = ‖x‖ := rfl

/-- Cauchy–Schwarz inequality with norm -/
theorem norm_inner_le_norm (x y : F) : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ :=
  nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) <|
    calc
      ‖⟪x, y⟫‖ * ‖⟪x, y⟫‖ = ‖⟪x, y⟫‖ * ‖⟪y, x⟫‖ := by rw [norm_inner_symm]
      _ ≤ re ⟪x, x⟫ * re ⟪y, y⟫ := inner_mul_inner_self_le x y
      _ = ‖x‖ * ‖y‖ * (‖x‖ * ‖y‖) := by simp only [inner_self_eq_norm_mul_norm]; ring

/-- Seminormed group structure constructed from an `PreInnerProductSpace.Core` structure -/
def toSeminormedAddCommGroup : SeminormedAddCommGroup F :=
  AddGroupSeminorm.toSeminormedAddCommGroup
    { toFun := fun x => √(re ⟪x, x⟫)
      map_zero' := by simp only [sqrt_zero, inner_zero_right, map_zero]
      neg' := fun x => by simp only [inner_neg_left, neg_neg, inner_neg_right]
      add_le' := fun x y => by
        have h₁ : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ := norm_inner_le_norm _ _
        have h₂ : re ⟪x, y⟫ ≤ ‖⟪x, y⟫‖ := re_le_norm _
        have h₃ : re ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ := h₂.trans h₁
        have h₄ : re ⟪y, x⟫ ≤ ‖x‖ * ‖y‖ := by rwa [← inner_conj_symm, conj_re]
        have : ‖x + y‖ * ‖x + y‖ ≤ (‖x‖ + ‖y‖) * (‖x‖ + ‖y‖) := by
          simp only [← inner_self_eq_norm_mul_norm, inner_add_add_self, mul_add, mul_comm, map_add]
          linarith
        exact nonneg_le_nonneg_of_sq_le_sq (add_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) this }

attribute [local instance] toSeminormedAddCommGroup

/-- Normed space (which is actually a seminorm) structure constructed from an
`PreInnerProductSpace.Core` structure -/
def toSeminormedSpace : NormedSpace 𝕜 F where
  norm_smul_le r x := by
    rw [norm_eq_sqrt_inner, inner_smul_left, inner_smul_right, ← mul_assoc]
    rw [RCLike.conj_mul, ← ofReal_pow, re_ofReal_mul, sqrt_mul, ← ofReal_normSq_eq_inner_self,
      ofReal_re]
    · simp [sqrt_normSq_eq_norm, RCLike.sqrt_normSq_eq_norm]
    · positivity

end PreInnerProductSpace.Core

section InnerProductSpace.Core

variable [AddCommGroup F] [Module 𝕜 F] [cd : InnerProductSpace.Core 𝕜 F]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 F _ x y

local notation "normSqK" => @RCLike.normSq 𝕜 _

local notation "ext_iff" => @RCLike.ext_iff 𝕜 _

/-- Inner product defined by the `InnerProductSpace.Core` structure. We can't reuse
`InnerProductSpace.Core.toInner` because it takes `InnerProductSpace.Core` as an explicit
argument. -/
def toInner' : Inner 𝕜 F :=
  cd.toInner

attribute [local instance] toInner'

local notation "normSqF" => @normSq 𝕜 F _ _ _ _

theorem inner_self_eq_zero {x : F} : ⟪x, x⟫ = 0 ↔ x = 0 :=
  ⟨cd.definite _, inner_self_of_eq_zero⟩

theorem normSq_eq_zero {x : F} : normSqF x = 0 ↔ x = 0 :=
  Iff.trans
    (by simp only [normSq, ext_iff, map_zero, inner_self_im, eq_self_iff_true, and_true])
    (@inner_self_eq_zero 𝕜 _ _ _ _ _ x)

theorem inner_self_ne_zero {x : F} : ⟪x, x⟫ ≠ 0 ↔ x ≠ 0 :=
  inner_self_eq_zero.not

attribute [local instance] toNorm

/-- Normed group structure constructed from an `InnerProductSpace.Core` structure -/
def toNormedAddCommGroup : NormedAddCommGroup F :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := fun x => √(re ⟪x, x⟫)
      map_zero' := by simp only [sqrt_zero, inner_zero_right, map_zero]
      neg' := fun x => by simp only [inner_neg_left, neg_neg, inner_neg_right]
      add_le' := fun x y => by
        have h₁ : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ := norm_inner_le_norm _ _
        have h₂ : re ⟪x, y⟫ ≤ ‖⟪x, y⟫‖ := re_le_norm _
        have h₃ : re ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ := h₂.trans h₁
        have h₄ : re ⟪y, x⟫ ≤ ‖x‖ * ‖y‖ := by rwa [← inner_conj_symm, conj_re]
        have : ‖x + y‖ * ‖x + y‖ ≤ (‖x‖ + ‖y‖) * (‖x‖ + ‖y‖) := by
          simp only [← inner_self_eq_norm_mul_norm, inner_add_add_self, mul_add, mul_comm, map_add]
          linarith
        exact nonneg_le_nonneg_of_sq_le_sq (add_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) this
      eq_zero_of_map_eq_zero' := fun _ hx =>
        normSq_eq_zero.1 <| (sqrt_eq_zero inner_self_nonneg).1 hx }

attribute [local instance] toNormedAddCommGroup

/-- Normed space structure constructed from an `InnerProductSpace.Core` structure -/
def toNormedSpace : NormedSpace 𝕜 F where
  norm_smul_le r x := by
    rw [norm_eq_sqrt_inner, inner_smul_left, inner_smul_right, ← mul_assoc]
    rw [RCLike.conj_mul, ← ofReal_pow, re_ofReal_mul, sqrt_mul, ← ofReal_normSq_eq_inner_self,
      ofReal_re]
    · simp [sqrt_normSq_eq_norm, RCLike.sqrt_normSq_eq_norm]
    · positivity

end InnerProductSpace.Core

end InnerProductSpace.Core

section

attribute [local instance] InnerProductSpace.Core.toNormedAddCommGroup

/-- Given an `InnerProductSpace.Core` structure on a space, one can use it to turn
the space into an inner product space. The `NormedAddCommGroup` structure is expected
to already be defined with `InnerProductSpace.ofCore.toNormedAddCommGroup`. -/
def InnerProductSpace.ofCore [AddCommGroup F] [Module 𝕜 F] (cd : InnerProductSpace.Core 𝕜 F) :
    InnerProductSpace 𝕜 F :=
  letI : NormedSpace 𝕜 F := @InnerProductSpace.Core.toNormedSpace 𝕜 F _ _ _ cd
  { cd with
    norm_sq_eq_inner := fun x => by
      have h₁ : ‖x‖ ^ 2 = √(re (cd.inner x x)) ^ 2 := rfl
      have h₂ : 0 ≤ re (cd.inner x x) := InnerProductSpace.Core.inner_self_nonneg
      simp [h₁, sq_sqrt, h₂] }

end

end
