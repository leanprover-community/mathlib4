/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

! This file was ported from Lean 3 source module linear_algebra.matrix.special_linear_group
! leanprover-community/mathlib commit f06058e64b7e8397234455038f3f8aec83aaba5a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.GeneralLinearGroup
import Mathbin.LinearAlgebra.Matrix.Adjugate
import Mathbin.LinearAlgebra.Matrix.ToLin

/-!
# The Special Linear group $SL(n, R)$

This file defines the elements of the Special Linear group `special_linear_group n R`, consisting
of all square `R`-matrices with determinant `1` on the fintype `n` by `n`.  In addition, we define
the group structure on `special_linear_group n R` and the embedding into the general linear group
`general_linear_group R (n → R)`.

## Main definitions

 * `matrix.special_linear_group` is the type of matrices with determinant 1
 * `matrix.special_linear_group.group` gives the group structure (under multiplication)
 * `matrix.special_linear_group.to_GL` is the embedding `SLₙ(R) → GLₙ(R)`

## Notation

For `m : ℕ`, we introduce the notation `SL(m,R)` for the special linear group on the fintype
`n = fin m`, in the locale `matrix_groups`.

## Implementation notes
The inverse operation in the `special_linear_group` is defined to be the adjugate
matrix, so that `special_linear_group n R` has a group structure for all `comm_ring R`.

We define the elements of `special_linear_group` to be matrices, since we need to
compute their determinant. This is in contrast with `general_linear_group R M`,
which consists of invertible `R`-linear maps on `M`.

We provide `matrix.special_linear_group.has_coe_to_fun` for convenience, but do not state any
lemmas about it, and use `matrix.special_linear_group.coe_fn_eq_coe` to eliminate it `⇑` in favor
of a regular `↑` coercion.

## References

 * https://en.wikipedia.org/wiki/Special_linear_group

## Tags

matrix group, group, matrix inverse
-/


namespace Matrix

universe u v

open Matrix

open LinearMap

section

variable (n : Type u) [DecidableEq n] [Fintype n] (R : Type v) [CommRing R]

/-- `special_linear_group n R` is the group of `n` by `n` `R`-matrices with determinant equal to 1.
-/
def SpecialLinearGroup :=
  { A : Matrix n n R // A.det = 1 }
#align matrix.special_linear_group Matrix.SpecialLinearGroup

end

-- mathport name: special_linear_group.fin
scoped[MatrixGroups] notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

namespace SpecialLinearGroup

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

instance hasCoeToMatrix : Coe (SpecialLinearGroup n R) (Matrix n n R) :=
  ⟨fun A => A.val⟩
#align matrix.special_linear_group.has_coe_to_matrix Matrix.SpecialLinearGroup.hasCoeToMatrix

-- mathport name: «expr↑ₘ »
/- In this file, Lean often has a hard time working out the values of `n` and `R` for an expression
like `det ↑A`. Rather than writing `(A : matrix n n R)` everywhere in this file which is annoyingly
verbose, or `A.val` which is not the simp-normal form for subtypes, we create a local notation
`↑ₘA`. This notation references the local `n` and `R` variables, so is not valid as a global
notation. -/
local prefix:1024 "↑ₘ" => @coe _ (Matrix n n R) _

theorem ext_iff (A B : SpecialLinearGroup n R) : A = B ↔ ∀ i j, ↑ₘA i j = ↑ₘB i j :=
  Subtype.ext_iff.trans Matrix.ext_iff.symm
#align matrix.special_linear_group.ext_iff Matrix.SpecialLinearGroup.ext_iff

@[ext]
theorem ext (A B : SpecialLinearGroup n R) : (∀ i j, ↑ₘA i j = ↑ₘB i j) → A = B :=
  (SpecialLinearGroup.ext_iff A B).mpr
#align matrix.special_linear_group.ext Matrix.SpecialLinearGroup.ext

instance hasInv : Inv (SpecialLinearGroup n R) :=
  ⟨fun A => ⟨adjugate A, by rw [det_adjugate, A.prop, one_pow]⟩⟩
#align matrix.special_linear_group.has_inv Matrix.SpecialLinearGroup.hasInv

instance hasMul : Mul (SpecialLinearGroup n R) :=
  ⟨fun A B => ⟨A.1 ⬝ B.1, by erw [det_mul, A.2, B.2, one_mul]⟩⟩
#align matrix.special_linear_group.has_mul Matrix.SpecialLinearGroup.hasMul

instance hasOne : One (SpecialLinearGroup n R) :=
  ⟨⟨1, det_one⟩⟩
#align matrix.special_linear_group.has_one Matrix.SpecialLinearGroup.hasOne

instance : Pow (SpecialLinearGroup n R) ℕ
    where pow x n := ⟨x ^ n, (det_pow _ _).trans <| x.Prop.symm ▸ one_pow _⟩

instance : Inhabited (SpecialLinearGroup n R) :=
  ⟨1⟩

section CoeLemmas

variable (A B : SpecialLinearGroup n R)

@[simp]
theorem coe_mk (A : Matrix n n R) (h : det A = 1) : ↑(⟨A, h⟩ : SpecialLinearGroup n R) = A :=
  rfl
#align matrix.special_linear_group.coe_mk Matrix.SpecialLinearGroup.coe_mk

@[simp]
theorem coe_inv : ↑ₘA⁻¹ = adjugate A :=
  rfl
#align matrix.special_linear_group.coe_inv Matrix.SpecialLinearGroup.coe_inv

@[simp]
theorem coe_mul : ↑ₘ(A * B) = ↑ₘA ⬝ ↑ₘB :=
  rfl
#align matrix.special_linear_group.coe_mul Matrix.SpecialLinearGroup.coe_mul

@[simp]
theorem coe_one : ↑ₘ(1 : SpecialLinearGroup n R) = (1 : Matrix n n R) :=
  rfl
#align matrix.special_linear_group.coe_one Matrix.SpecialLinearGroup.coe_one

@[simp]
theorem det_coe : det ↑ₘA = 1 :=
  A.2
#align matrix.special_linear_group.det_coe Matrix.SpecialLinearGroup.det_coe

@[simp]
theorem coe_pow (m : ℕ) : ↑ₘ(A ^ m) = ↑ₘA ^ m :=
  rfl
#align matrix.special_linear_group.coe_pow Matrix.SpecialLinearGroup.coe_pow

theorem det_ne_zero [Nontrivial R] (g : SpecialLinearGroup n R) : det ↑ₘg ≠ 0 :=
  by
  rw [g.det_coe]
  norm_num
#align matrix.special_linear_group.det_ne_zero Matrix.SpecialLinearGroup.det_ne_zero

theorem row_ne_zero [Nontrivial R] (g : SpecialLinearGroup n R) (i : n) : ↑ₘg i ≠ 0 := fun h =>
  g.det_ne_zero <| det_eq_zero_of_row_eq_zero i <| by simp [h]
#align matrix.special_linear_group.row_ne_zero Matrix.SpecialLinearGroup.row_ne_zero

end CoeLemmas

instance : Monoid (SpecialLinearGroup n R) :=
  Function.Injective.monoid coe Subtype.coe_injective coe_one coe_mul coe_pow

instance : Group (SpecialLinearGroup n R) :=
  { SpecialLinearGroup.monoid, SpecialLinearGroup.hasInv with
    mul_left_inv := fun A => by
      ext1
      simp [adjugate_mul] }

/-- A version of `matrix.to_lin' A` that produces linear equivalences. -/
def toLin' : SpecialLinearGroup n R →* (n → R) ≃ₗ[R] n → R
    where
  toFun A :=
    LinearEquiv.ofLinear (Matrix.toLin' ↑ₘA) (Matrix.toLin' ↑ₘA⁻¹)
      (by rw [← to_lin'_mul, ← coe_mul, mul_right_inv, coe_one, to_lin'_one])
      (by rw [← to_lin'_mul, ← coe_mul, mul_left_inv, coe_one, to_lin'_one])
  map_one' := LinearEquiv.toLinearMap_injective Matrix.toLin'_one
  map_mul' A B := LinearEquiv.toLinearMap_injective <| Matrix.toLin'_mul A B
#align matrix.special_linear_group.to_lin' Matrix.SpecialLinearGroup.toLin'

theorem toLin'_apply (A : SpecialLinearGroup n R) (v : n → R) :
    SpecialLinearGroup.toLin' A v = Matrix.toLin' (↑ₘA) v :=
  rfl
#align matrix.special_linear_group.to_lin'_apply Matrix.SpecialLinearGroup.toLin'_apply

theorem toLin'_to_linearMap (A : SpecialLinearGroup n R) :
    ↑(SpecialLinearGroup.toLin' A) = Matrix.toLin' ↑ₘA :=
  rfl
#align matrix.special_linear_group.to_lin'_to_linear_map Matrix.SpecialLinearGroup.toLin'_to_linearMap

theorem toLin'_symm_apply (A : SpecialLinearGroup n R) (v : n → R) :
    A.toLin'.symm v = Matrix.toLin' (↑ₘA⁻¹) v :=
  rfl
#align matrix.special_linear_group.to_lin'_symm_apply Matrix.SpecialLinearGroup.toLin'_symm_apply

theorem toLin'_symm_to_linearMap (A : SpecialLinearGroup n R) :
    ↑A.toLin'.symm = Matrix.toLin' ↑ₘA⁻¹ :=
  rfl
#align matrix.special_linear_group.to_lin'_symm_to_linear_map Matrix.SpecialLinearGroup.toLin'_symm_to_linearMap

theorem toLin'_injective :
    Function.Injective ⇑(toLin' : SpecialLinearGroup n R →* (n → R) ≃ₗ[R] n → R) := fun A B h =>
  Subtype.coe_injective <| Matrix.toLin'.Injective <| LinearEquiv.toLinearMap_injective.eq_iff.mpr h
#align matrix.special_linear_group.to_lin'_injective Matrix.SpecialLinearGroup.toLin'_injective

/-- `to_GL` is the map from the special linear group to the general linear group -/
def toGL : SpecialLinearGroup n R →* GeneralLinearGroup R (n → R) :=
  (GeneralLinearGroup.generalLinearEquiv _ _).symm.toMonoidHom.comp toLin'
#align matrix.special_linear_group.to_GL Matrix.SpecialLinearGroup.toGL

theorem coe_toGL (A : SpecialLinearGroup n R) : ↑A.toGL = A.toLin'.toLinearMap :=
  rfl
#align matrix.special_linear_group.coe_to_GL Matrix.SpecialLinearGroup.coe_toGL

variable {S : Type _} [CommRing S]

/-- A ring homomorphism from `R` to `S` induces a group homomorphism from
`special_linear_group n R` to `special_linear_group n S`. -/
@[simps]
def map (f : R →+* S) : SpecialLinearGroup n R →* SpecialLinearGroup n S
    where
  toFun g :=
    ⟨f.mapMatrix ↑g, by
      rw [← f.map_det]
      simp [g.2]⟩
  map_one' := Subtype.ext <| f.mapMatrix.map_one
  map_mul' x y := Subtype.ext <| f.mapMatrix.map_mul x y
#align matrix.special_linear_group.map Matrix.SpecialLinearGroup.map

section cast

/-- Coercion of SL `n` `ℤ` to SL `n` `R` for a commutative ring `R`. -/
instance : Coe (SpecialLinearGroup n ℤ) (SpecialLinearGroup n R) :=
  ⟨fun x => map (Int.castRingHom R) x⟩

@[simp]
theorem coe_matrix_coe (g : SpecialLinearGroup n ℤ) :
    ↑(g : SpecialLinearGroup n R) = (↑g : Matrix n n ℤ).map (Int.castRingHom R) :=
  map_apply_coe (Int.castRingHom R) g
#align matrix.special_linear_group.coe_matrix_coe Matrix.SpecialLinearGroup.coe_matrix_coe

end cast

section Neg

variable [Fact (Even (Fintype.card n))]

/-- Formal operation of negation on special linear group on even cardinality `n` given by negating
each element. -/
instance : Neg (SpecialLinearGroup n R) :=
  ⟨fun g =>
    ⟨-g, by
      simpa [(Fact.out <| Even <| Fintype.card n).neg_one_pow, g.det_coe] using
        det_smul (↑ₘg) (-1)⟩⟩

@[simp]
theorem coe_neg (g : SpecialLinearGroup n R) : ↑(-g) = -(g : Matrix n n R) :=
  rfl
#align matrix.special_linear_group.coe_neg Matrix.SpecialLinearGroup.coe_neg

instance : HasDistribNeg (SpecialLinearGroup n R) :=
  Function.Injective.hasDistribNeg _ Subtype.coe_injective coe_neg coe_mul

@[simp]
theorem coe_int_neg (g : SpecialLinearGroup n ℤ) : ↑(-g) = (-↑g : SpecialLinearGroup n R) :=
  Subtype.ext <| (@RingHom.mapMatrix n _ _ _ _ _ _ (Int.castRingHom R)).map_neg ↑g
#align matrix.special_linear_group.coe_int_neg Matrix.SpecialLinearGroup.coe_int_neg

end Neg

section SpecialCases

theorem SL2_inv_expl_det (A : SL(2, R)) : det ![![A.1 1 1, -A.1 0 1], ![-A.1 1 0, A.1 0 0]] = 1 :=
  by
  rw [Matrix.det_fin_two, mul_comm]
  simp only [Subtype.val_eq_coe, cons_val_zero, cons_val_one, head_cons, mul_neg, neg_mul, neg_neg]
  have := A.2
  rw [Matrix.det_fin_two] at this
  convert this
#align matrix.special_linear_group.SL2_inv_expl_det Matrix.SpecialLinearGroup.SL2_inv_expl_det

theorem SL2_inv_expl (A : SL(2, R)) :
    A⁻¹ = ⟨![![A.1 1 1, -A.1 0 1], ![-A.1 1 0, A.1 0 0]], SL2_inv_expl_det A⟩ :=
  by
  ext
  have := Matrix.adjugate_fin_two A.1
  simp only [Subtype.val_eq_coe] at this
  rw [coe_inv, this]
  rfl
#align matrix.special_linear_group.SL2_inv_expl Matrix.SpecialLinearGroup.SL2_inv_expl

theorem fin_two_induction (P : SL(2, R) → Prop)
    (h : ∀ (a b c d : R) (hdet : a * d - b * c = 1), P ⟨!![a, b; c, d], by rwa [det_fin_two_of]⟩)
    (g : SL(2, R)) : P g := by
  obtain ⟨m, hm⟩ := g
  convert h (m 0 0) (m 0 1) (m 1 0) (m 1 1) (by rwa [det_fin_two] at hm)
  ext (i j); fin_cases i <;> fin_cases j <;> rfl
#align matrix.special_linear_group.fin_two_induction Matrix.SpecialLinearGroup.fin_two_induction

theorem fin_two_exists_eq_mk_of_apply_zero_one_eq_zero {R : Type _} [Field R] (g : SL(2, R))
    (hg : (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0) :
    ∃ (a b : R)(h : a ≠ 0), g = (⟨!![a, b; 0, a⁻¹], by simp [h]⟩ : SL(2, R)) :=
  by
  induction' g using Matrix.SpecialLinearGroup.fin_two_induction with a b c d h_det
  replace hg : c = 0 := by simpa using hg
  have had : a * d = 1 := by rwa [hg, MulZeroClass.mul_zero, sub_zero] at h_det
  refine' ⟨a, b, left_ne_zero_of_mul_eq_one had, _⟩
  simp_rw [eq_inv_of_mul_eq_one_right had, hg]
#align matrix.special_linear_group.fin_two_exists_eq_mk_of_apply_zero_one_eq_zero Matrix.SpecialLinearGroup.fin_two_exists_eq_mk_of_apply_zero_one_eq_zero

end SpecialCases

-- this section should be last to ensure we do not use it in lemmas
section CoeFnInstance

/-- This instance is here for convenience, but is not the simp-normal form. -/
instance : CoeFun (SpecialLinearGroup n R) fun _ => n → n → R where coe A := A.val

@[simp]
theorem coeFn_eq_coe (s : SpecialLinearGroup n R) : ⇑s = ↑ₘs :=
  rfl
#align matrix.special_linear_group.coe_fn_eq_coe Matrix.SpecialLinearGroup.coeFn_eq_coe

end CoeFnInstance

end SpecialLinearGroup

end Matrix

namespace ModularGroup

open MatrixGroups

open Matrix Matrix.SpecialLinearGroup

-- mathport name: «expr↑ₘ »
local prefix:1024 "↑ₘ" => @coe _ (Matrix (Fin 2) (Fin 2) ℤ) _

/-- The matrix `S = [[0, -1], [1, 0]]` as an element of `SL(2, ℤ)`.

This element acts naturally on the Euclidean plane as a rotation about the origin by `π / 2`.

This element also acts naturally on the hyperbolic plane as rotation about `i` by `π`. It
represents the Mobiüs transformation `z ↦ -1/z` and is an involutive elliptic isometry. -/
def s : SL(2, ℤ) :=
  ⟨!![0, -1; 1, 0], by norm_num [Matrix.det_fin_two_of] ⟩
#align modular_group.S ModularGroup.s

/-- The matrix `T = [[1, 1], [0, 1]]` as an element of `SL(2, ℤ)` -/
def t : SL(2, ℤ) :=
  ⟨!![1, 1; 0, 1], by norm_num [Matrix.det_fin_two_of] ⟩
#align modular_group.T ModularGroup.t

theorem coe_s : ↑ₘs = !![0, -1; 1, 0] :=
  rfl
#align modular_group.coe_S ModularGroup.coe_s

theorem coe_t : ↑ₘt = !![1, 1; 0, 1] :=
  rfl
#align modular_group.coe_T ModularGroup.coe_t

theorem coe_t_inv : ↑ₘt⁻¹ = !![1, -1; 0, 1] := by simp [coe_inv, coe_T, adjugate_fin_two]
#align modular_group.coe_T_inv ModularGroup.coe_t_inv

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, ",", expr _, ";", expr _, ",", expr _, "]"] [])]] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, ",", expr _, ";", expr _, ",", expr _, "]"] [])]] -/
theorem coe_t_zpow (n : ℤ) : ↑ₘ(t ^ n) = !![1, n; 0, 1] :=
  by
  induction' n using Int.induction_on with n h n h
  · rw [zpow_zero, coe_one, Matrix.one_fin_two]
  · simp_rw [zpow_add, zpow_one, coe_mul, h, coe_T, Matrix.mul_fin_two]
    trace
      "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \",\", expr _, \";\", expr _, \",\", expr _, \"]\"] [])]]"
    rw [mul_one, mul_one, add_comm]
  · simp_rw [zpow_sub, zpow_one, coe_mul, h, coe_T_inv, Matrix.mul_fin_two]
    trace
        "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr «expr!![ »(matrix.notation [expr _, \",\", expr _, \";\", expr _, \",\", expr _, \"]\"] [])]]" <;>
      ring
#align modular_group.coe_T_zpow ModularGroup.coe_t_zpow

@[simp]
theorem t_pow_mul_apply_one (n : ℤ) (g : SL(2, ℤ)) : ↑ₘ(t ^ n * g) 1 = ↑ₘg 1 := by
  simp [coe_T_zpow, Matrix.mul, Matrix.dotProduct, Fin.sum_univ_succ]
#align modular_group.T_pow_mul_apply_one ModularGroup.t_pow_mul_apply_one

@[simp]
theorem t_mul_apply_one (g : SL(2, ℤ)) : ↑ₘ(t * g) 1 = ↑ₘg 1 := by
  simpa using T_pow_mul_apply_one 1 g
#align modular_group.T_mul_apply_one ModularGroup.t_mul_apply_one

@[simp]
theorem t_inv_mul_apply_one (g : SL(2, ℤ)) : ↑ₘ(t⁻¹ * g) 1 = ↑ₘg 1 := by
  simpa using T_pow_mul_apply_one (-1) g
#align modular_group.T_inv_mul_apply_one ModularGroup.t_inv_mul_apply_one

end ModularGroup

