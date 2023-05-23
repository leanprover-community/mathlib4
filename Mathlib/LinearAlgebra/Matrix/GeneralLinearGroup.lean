/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck

! This file was ported from Lean 3 source module linear_algebra.matrix.general_linear_group
! leanprover-community/mathlib commit 2705404e701abc6b3127da906f40bae062a169c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.GeneralLinearGroup
import Mathbin.LinearAlgebra.Matrix.NonsingularInverse
import Mathbin.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# The General Linear group $GL(n, R)$

This file defines the elements of the General Linear group `general_linear_group n R`,
consisting of all invertible `n` by `n` `R`-matrices.

## Main definitions

* `matrix.general_linear_group` is the type of matrices over R which are units in the matrix ring.
* `matrix.GL_pos` gives the subgroup of matrices with
  positive determinant (over a linear ordered ring).

## Tags

matrix group, group, matrix inverse
-/


namespace Matrix

universe u v

open Matrix

open LinearMap

-- disable this instance so we do not accidentally use it in lemmas.
attribute [-instance] special_linear_group.has_coe_to_fun

/-- `GL n R` is the group of `n` by `n` `R`-matrices with unit determinant.
Defined as a subtype of matrices-/
abbrev GeneralLinearGroup (n : Type u) (R : Type v) [DecidableEq n] [Fintype n] [CommRing R] :
    Type _ :=
  (Matrix n n R)ˣ
#align matrix.general_linear_group Matrix.GeneralLinearGroup

-- mathport name: exprGL
notation "GL" => GeneralLinearGroup

namespace GeneralLinearGroup

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

/-- The determinant of a unit matrix is itself a unit. -/
@[simps]
def det : GL n R →* Rˣ
    where
  toFun A :=
    { val := (↑A : Matrix n n R).det
      inv := (↑A⁻¹ : Matrix n n R).det
      val_inv := by rw [← det_mul, ← mul_eq_mul, A.mul_inv, det_one]
      inv_val := by rw [← det_mul, ← mul_eq_mul, A.inv_mul, det_one] }
  map_one' := Units.ext det_one
  map_mul' A B := Units.ext <| det_mul _ _
#align matrix.general_linear_group.det Matrix.GeneralLinearGroup.det

/-- The `GL n R` and `general_linear_group R n` groups are multiplicatively equivalent-/
def toLin : GL n R ≃* LinearMap.GeneralLinearGroup R (n → R) :=
  Units.mapEquiv toLinAlgEquiv'.toMulEquiv
#align matrix.general_linear_group.to_lin Matrix.GeneralLinearGroup.toLin

/-- Given a matrix with invertible determinant we get an element of `GL n R`-/
def mk' (A : Matrix n n R) (h : Invertible (Matrix.det A)) : GL n R :=
  unitOfDetInvertible A
#align matrix.general_linear_group.mk' Matrix.GeneralLinearGroup.mk'

/-- Given a matrix with unit determinant we get an element of `GL n R`-/
noncomputable def mk'' (A : Matrix n n R) (h : IsUnit (Matrix.det A)) : GL n R :=
  nonsingInvUnit A h
#align matrix.general_linear_group.mk'' Matrix.GeneralLinearGroup.mk''

/-- Given a matrix with non-zero determinant over a field, we get an element of `GL n K`-/
def mkOfDetNeZero {K : Type _} [Field K] (A : Matrix n n K) (h : Matrix.det A ≠ 0) : GL n K :=
  mk' A (invertibleOfNonzero h)
#align matrix.general_linear_group.mk_of_det_ne_zero Matrix.GeneralLinearGroup.mkOfDetNeZero

theorem ext_iff (A B : GL n R) : A = B ↔ ∀ i j, (A : Matrix n n R) i j = (B : Matrix n n R) i j :=
  Units.ext_iff.trans Matrix.ext_iff.symm
#align matrix.general_linear_group.ext_iff Matrix.GeneralLinearGroup.ext_iff

/-- Not marked `@[ext]` as the `ext` tactic already solves this. -/
theorem ext ⦃A B : GL n R⦄ (h : ∀ i j, (A : Matrix n n R) i j = (B : Matrix n n R) i j) : A = B :=
  Units.ext <| Matrix.ext h
#align matrix.general_linear_group.ext Matrix.GeneralLinearGroup.ext

section CoeLemmas

variable (A B : GL n R)

@[simp]
theorem coe_mul : ↑(A * B) = (↑A : Matrix n n R) ⬝ (↑B : Matrix n n R) :=
  rfl
#align matrix.general_linear_group.coe_mul Matrix.GeneralLinearGroup.coe_mul

@[simp]
theorem coe_one : ↑(1 : GL n R) = (1 : Matrix n n R) :=
  rfl
#align matrix.general_linear_group.coe_one Matrix.GeneralLinearGroup.coe_one

theorem coe_inv : ↑A⁻¹ = (↑A : Matrix n n R)⁻¹ :=
  letI := A.invertible
  inv_of_eq_nonsing_inv (↑A : Matrix n n R)
#align matrix.general_linear_group.coe_inv Matrix.GeneralLinearGroup.coe_inv

/-- An element of the matrix general linear group on `(n) [fintype n]` can be considered as an
element of the endomorphism general linear group on `n → R`. -/
def toLinear : GeneralLinearGroup n R ≃* LinearMap.GeneralLinearGroup R (n → R) :=
  Units.mapEquiv Matrix.toLinAlgEquiv'.toRingEquiv.toMulEquiv
#align matrix.general_linear_group.to_linear Matrix.GeneralLinearGroup.toLinear

-- Note that without the `@` and `‹_›`, lean infers `λ a b, _inst a b` instead of `_inst` as the
-- decidability argument, which prevents `simp` from obtaining the instance by unification.
-- These `λ a b, _inst a b` terms also appear in the type of `A`, but simp doesn't get confused by
-- them so for now we do not care.
@[simp]
theorem coe_toLinear : (@toLinear n ‹_› ‹_› _ _ A : (n → R) →ₗ[R] n → R) = Matrix.mulVecLin A :=
  rfl
#align matrix.general_linear_group.coe_to_linear Matrix.GeneralLinearGroup.coe_toLinear

@[simp]
theorem toLinear_apply (v : n → R) : (@toLinear n ‹_› ‹_› _ _ A) v = Matrix.mulVecLin (↑A) v :=
  rfl
#align matrix.general_linear_group.to_linear_apply Matrix.GeneralLinearGroup.toLinear_apply

end CoeLemmas

end GeneralLinearGroup

namespace SpecialLinearGroup

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

instance hasCoeToGeneralLinearGroup : Coe (SpecialLinearGroup n R) (GL n R) :=
  ⟨fun A => ⟨↑A, ↑A⁻¹, congr_arg coe (mul_right_inv A), congr_arg coe (mul_left_inv A)⟩⟩
#align matrix.special_linear_group.has_coe_to_general_linear_group Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup

@[simp]
theorem coe_to_GL_det (g : SpecialLinearGroup n R) : (g : GL n R).det = 1 :=
  Units.ext g.Prop
#align matrix.special_linear_group.coe_to_GL_det Matrix.SpecialLinearGroup.coe_to_GL_det

end SpecialLinearGroup

section

variable {n : Type u} {R : Type v} [DecidableEq n] [Fintype n] [LinearOrderedCommRing R]

section

variable (n R)

/-- This is the subgroup of `nxn` matrices with entries over a
linear ordered ring and positive determinant. -/
def gLPos : Subgroup (GL n R) :=
  (Units.posSubgroup R).comap GeneralLinearGroup.det
#align matrix.GL_pos Matrix.gLPos

end

@[simp]
theorem mem_gLPos (A : GL n R) : A ∈ gLPos n R ↔ 0 < (A.det : R) :=
  Iff.rfl
#align matrix.mem_GL_pos Matrix.mem_gLPos

theorem gLPos.det_ne_zero (A : gLPos n R) : (A : Matrix n n R).det ≠ 0 :=
  ne_of_gt A.Prop
#align matrix.GL_pos.det_ne_zero Matrix.gLPos.det_ne_zero

end

section Neg

variable {n : Type u} {R : Type v} [DecidableEq n] [Fintype n] [LinearOrderedCommRing R]
  [Fact (Even (Fintype.card n))]

/-- Formal operation of negation on general linear group on even cardinality `n` given by negating
each element. -/
instance : Neg (gLPos n R) :=
  ⟨fun g =>
    ⟨-g,
      by
      rw [mem_GL_pos, general_linear_group.coe_det_apply, Units.val_neg, det_neg,
        (Fact.out <| Even <| Fintype.card n).neg_one_pow, one_mul]
      exact g.prop⟩⟩

@[simp]
theorem gLPos.coe_neg_GL (g : gLPos n R) : ↑(-g) = -(g : GL n R) :=
  rfl
#align matrix.GL_pos.coe_neg_GL Matrix.gLPos.coe_neg_GL

@[simp]
theorem gLPos.coe_neg (g : gLPos n R) : ↑(-g) = -(g : Matrix n n R) :=
  rfl
#align matrix.GL_pos.coe_neg Matrix.gLPos.coe_neg

@[simp]
theorem gLPos.coe_neg_apply (g : gLPos n R) (i j : n) :
    (↑(-g) : Matrix n n R) i j = -(↑g : Matrix n n R) i j :=
  rfl
#align matrix.GL_pos.coe_neg_apply Matrix.gLPos.coe_neg_apply

instance : HasDistribNeg (gLPos n R) :=
  Subtype.coe_injective.HasDistribNeg _ gLPos.coe_neg_GL (gLPos n R).val_mul

end Neg

namespace SpecialLinearGroup

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [LinearOrderedCommRing R]

/-- `special_linear_group n R` embeds into `GL_pos n R` -/
def toGLPos : SpecialLinearGroup n R →* gLPos n R
    where
  toFun A := ⟨(A : GL n R), show 0 < (↑A : Matrix n n R).det from A.Prop.symm ▸ zero_lt_one⟩
  map_one' := Subtype.ext <| Units.ext <| rfl
  map_mul' A₁ A₂ := Subtype.ext <| Units.ext <| rfl
#align matrix.special_linear_group.to_GL_pos Matrix.SpecialLinearGroup.toGLPos

instance : Coe (SpecialLinearGroup n R) (gLPos n R) :=
  ⟨toGLPos⟩

theorem coe_eq_toGLPos : (coe : SpecialLinearGroup n R → gLPos n R) = toGLPos :=
  rfl
#align matrix.special_linear_group.coe_eq_to_GL_pos Matrix.SpecialLinearGroup.coe_eq_toGLPos

theorem toGLPos_injective : Function.Injective (toGLPos : SpecialLinearGroup n R → gLPos n R) :=
  (show Function.Injective ((coe : gLPos n R → Matrix n n R) ∘ toGLPos) from
      Subtype.coe_injective).of_comp
#align matrix.special_linear_group.to_GL_pos_injective Matrix.SpecialLinearGroup.toGLPos_injective

/-- Coercing a `special_linear_group` via `GL_pos` and `GL` is the same as coercing striaght to a
matrix. -/
@[simp]
theorem coe_gLPos_coe_GL_coe_matrix (g : SpecialLinearGroup n R) :
    (↑(↑(↑g : gLPos n R) : GL n R) : Matrix n n R) = ↑g :=
  rfl
#align matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix Matrix.SpecialLinearGroup.coe_gLPos_coe_GL_coe_matrix

@[simp]
theorem coe_to_gLPos_to_GL_det (g : SpecialLinearGroup n R) : ((g : gLPos n R) : GL n R).det = 1 :=
  Units.ext g.Prop
#align matrix.special_linear_group.coe_to_GL_pos_to_GL_det Matrix.SpecialLinearGroup.coe_to_gLPos_to_GL_det

variable [Fact (Even (Fintype.card n))]

@[norm_cast]
theorem coe_gLPos_neg (g : SpecialLinearGroup n R) : ↑(-g) = -(↑g : gLPos n R) :=
  Subtype.ext <| Units.ext rfl
#align matrix.special_linear_group.coe_GL_pos_neg Matrix.SpecialLinearGroup.coe_gLPos_neg

end SpecialLinearGroup

section Examples

/-- The matrix [a, -b; b, a] (inspired by multiplication by a complex number); it is an element of
$GL_2(R)$ if `a ^ 2 + b ^ 2` is nonzero. -/
@[simps (config := { fullyApplied := false }) coe]
def planeConformalMatrix {R} [Field R] (a b : R) (hab : a ^ 2 + b ^ 2 ≠ 0) :
    Matrix.GeneralLinearGroup (Fin 2) R :=
  GeneralLinearGroup.mkOfDetNeZero !![a, -b; b, a] (by simpa [det_fin_two, sq] using hab)
#align matrix.plane_conformal_matrix Matrix.planeConformalMatrix

/- TODO: Add Iwasawa matrices `n_x=!![1,x; 0,1]`, `a_t=!![exp(t/2),0;0,exp(-t/2)]` and
  `k_θ=!![cos θ, sin θ; -sin θ, cos θ]`
-/
end Examples

namespace GeneralLinearGroup

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

-- this section should be last to ensure we do not use it in lemmas
section CoeFnInstance

/-- This instance is here for convenience, but is not the simp-normal form. -/
instance : CoeFun (GL n R) fun _ => n → n → R where coe A := A.val

@[simp]
theorem coeFn_eq_coe (A : GL n R) : ⇑A = (↑A : Matrix n n R) :=
  rfl
#align matrix.general_linear_group.coe_fn_eq_coe Matrix.GeneralLinearGroup.coeFn_eq_coe

end CoeFnInstance

end GeneralLinearGroup

end Matrix

