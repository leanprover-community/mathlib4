/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Wen Yang
-/
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# The Special Linear group $SL(n, R)$

This file defines the elements of the Special Linear group `SpecialLinearGroup n R`, consisting
of all square `R`-matrices with determinant `1` on the fintype `n` by `n`.  In addition, we define
the group structure on `SpecialLinearGroup n R` and the embedding into the general linear group
`GeneralLinearGroup R (n → R)`.

## Main definitions

* `Matrix.SpecialLinearGroup` is the type of matrices with determinant 1
* `Matrix.SpecialLinearGroup.group` gives the group structure (under multiplication)
* `Matrix.SpecialLinearGroup.toGL` is the embedding `SLₙ(R) → GLₙ(R)`

## Notation

For `m : ℕ`, we introduce the notation `SL(m,R)` for the special linear group on the fintype
`n = Fin m`, in the locale `MatrixGroups`.

## Implementation notes
The inverse operation in the `SpecialLinearGroup` is defined to be the adjugate
matrix, so that `SpecialLinearGroup n R` has a group structure for all `CommRing R`.

We define the elements of `SpecialLinearGroup` to be matrices, since we need to
compute their determinant. This is in contrast with `GeneralLinearGroup R M`,
which consists of invertible `R`-linear maps on `M`.

We provide `Matrix.SpecialLinearGroup.hasCoeToFun` for convenience, but do not state any
lemmas about it, and use `Matrix.SpecialLinearGroup.coeFn_eq_coe` to eliminate it `⇑` in favor
of a regular `↑` coercion.

## References

* https://en.wikipedia.org/wiki/Special_linear_group

## Tags

matrix group, group, matrix inverse
-/


namespace Matrix

universe u v

open LinearMap

section

variable (n : Type u) [DecidableEq n] [Fintype n] (R : Type v) [CommRing R]

/-- `SpecialLinearGroup n R` is the group of `n` by `n` `R`-matrices with determinant equal to 1.
-/
def SpecialLinearGroup :=
  { A : Matrix n n R // A.det = 1 }

end

@[inherit_doc]
scoped[MatrixGroups] notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

namespace SpecialLinearGroup

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

instance hasCoeToMatrix : Coe (SpecialLinearGroup n R) (Matrix n n R) :=
  ⟨fun A => A.val⟩

/-- In this file, Lean often has a hard time working out the values of `n` and `R` for an expression
like `det ↑A`. Rather than writing `(A : Matrix n n R)` everywhere in this file which is annoyingly
verbose, or `A.val` which is not the simp-normal form for subtypes, we create a local notation
`↑ₘA`. This notation references the local `n` and `R` variables, so is not valid as a global
notation. -/
local notation:1024 "↑ₘ" A:1024 => ((A : SpecialLinearGroup n R) : Matrix n n R)

section CoeFnInstance

/-- This instance is here for convenience, but is literally the same as the coercion from
`hasCoeToMatrix`. -/
instance instCoeFun : CoeFun (SpecialLinearGroup n R) fun _ => n → n → R where coe A := ↑ₘA

end CoeFnInstance

theorem ext_iff (A B : SpecialLinearGroup n R) : A = B ↔ ∀ i j, A i j = B i j :=
  Subtype.ext_iff.trans Matrix.ext_iff.symm

@[ext]
theorem ext (A B : SpecialLinearGroup n R) : (∀ i j, A i j = B i j) → A = B :=
  (SpecialLinearGroup.ext_iff A B).mpr

instance subsingleton_of_subsingleton [Subsingleton n] : Subsingleton (SpecialLinearGroup n R) := by
  refine ⟨fun ⟨A, hA⟩ ⟨B, hB⟩ ↦ ?_⟩
  ext i j
  rcases isEmpty_or_nonempty n with hn | hn; · exfalso; exact IsEmpty.false i
  rw [det_eq_elem_of_subsingleton _ i] at hA hB
  simp only [Subsingleton.elim j i, hA, hB]

instance hasInv : Inv (SpecialLinearGroup n R) :=
  ⟨fun A => ⟨adjugate A, by rw [det_adjugate, A.prop, one_pow]⟩⟩

instance hasMul : Mul (SpecialLinearGroup n R) :=
  ⟨fun A B => ⟨A * B, by rw [det_mul, A.prop, B.prop, one_mul]⟩⟩

instance hasOne : One (SpecialLinearGroup n R) :=
  ⟨⟨1, det_one⟩⟩

instance : Pow (SpecialLinearGroup n R) ℕ where
  pow x n := ⟨x ^ n, (det_pow _ _).trans <| x.prop.symm ▸ one_pow _⟩

instance : Inhabited (SpecialLinearGroup n R) :=
  ⟨1⟩

instance [Fintype R] [DecidableEq R] : Fintype (SpecialLinearGroup n R) := Subtype.fintype _
instance [Finite R] : Finite (SpecialLinearGroup n R) := Subtype.finite

/-- The transpose of a matrix in `SL(n, R)` -/
def transpose (A : SpecialLinearGroup n R) : SpecialLinearGroup n R :=
  ⟨A.1.transpose, A.1.det_transpose ▸ A.2⟩

@[inherit_doc]
scoped postfix:1024 "ᵀ" => SpecialLinearGroup.transpose

section CoeLemmas

variable (A B : SpecialLinearGroup n R)

theorem coe_mk (A : Matrix n n R) (h : det A = 1) : ↑(⟨A, h⟩ : SpecialLinearGroup n R) = A :=
  rfl

@[simp]
theorem coe_inv : ↑ₘ(A⁻¹) = adjugate A :=
  rfl

@[simp]
theorem coe_mul : ↑ₘ(A * B) = ↑ₘA * ↑ₘB :=
  rfl

@[simp]
theorem coe_one : (1 : SpecialLinearGroup n R) = (1 : Matrix n n R) :=
  rfl

@[simp]
theorem det_coe : det ↑ₘA = 1 :=
  A.2

@[simp]
theorem coe_pow (m : ℕ) : ↑ₘ(A ^ m) = ↑ₘA ^ m :=
  rfl

@[simp]
lemma coe_transpose (A : SpecialLinearGroup n R) : ↑ₘAᵀ = (↑ₘA)ᵀ :=
  rfl

theorem det_ne_zero [Nontrivial R] (g : SpecialLinearGroup n R) : det ↑ₘg ≠ 0 := by
  rw [g.det_coe]
  norm_num

theorem row_ne_zero [Nontrivial R] (g : SpecialLinearGroup n R) (i : n) : g i ≠ 0 := fun h =>
  g.det_ne_zero <| det_eq_zero_of_row_eq_zero i <| by simp [h]

end CoeLemmas

instance monoid : Monoid (SpecialLinearGroup n R) :=
  Function.Injective.monoid _ Subtype.coe_injective coe_one coe_mul coe_pow

instance : Group (SpecialLinearGroup n R) :=
  { SpecialLinearGroup.monoid, SpecialLinearGroup.hasInv with
    inv_mul_cancel := fun A => by
      ext1
      simp [adjugate_mul] }

/-- A version of `Matrix.toLin' A` that produces linear equivalences. -/
def toLin' : SpecialLinearGroup n R →* (n → R) ≃ₗ[R] n → R where
  toFun A :=
    LinearEquiv.ofLinear (Matrix.toLin' ↑ₘA) (Matrix.toLin' ↑ₘA⁻¹)
      (by rw [← toLin'_mul, ← coe_mul, mul_inv_cancel, coe_one, toLin'_one])
      (by rw [← toLin'_mul, ← coe_mul, inv_mul_cancel, coe_one, toLin'_one])
  map_one' := LinearEquiv.toLinearMap_injective Matrix.toLin'_one
  map_mul' A B := LinearEquiv.toLinearMap_injective <| Matrix.toLin'_mul ↑ₘA ↑ₘB

theorem toLin'_apply (A : SpecialLinearGroup n R) (v : n → R) :
    SpecialLinearGroup.toLin' A v = Matrix.toLin' (↑ₘA) v :=
  rfl

theorem toLin'_to_linearMap (A : SpecialLinearGroup n R) :
    ↑(SpecialLinearGroup.toLin' A) = Matrix.toLin' ↑ₘA :=
  rfl

theorem toLin'_symm_apply (A : SpecialLinearGroup n R) (v : n → R) :
    A.toLin'.symm v = Matrix.toLin' (↑ₘA⁻¹) v :=
  rfl

theorem toLin'_symm_to_linearMap (A : SpecialLinearGroup n R) :
    ↑A.toLin'.symm = Matrix.toLin' ↑ₘA⁻¹ :=
  rfl

theorem toLin'_injective :
    Function.Injective ↑(toLin' : SpecialLinearGroup n R →* (n → R) ≃ₗ[R] n → R) := fun _ _ h =>
  Subtype.coe_injective <| Matrix.toLin'.injective <| LinearEquiv.toLinearMap_injective.eq_iff.mpr h

variable {S : Type*} [CommRing S]

/-- A ring homomorphism from `R` to `S` induces a group homomorphism from
`SpecialLinearGroup n R` to `SpecialLinearGroup n S`. -/
@[simps]
def map (f : R →+* S) : SpecialLinearGroup n R →* SpecialLinearGroup n S where
  toFun g :=
    ⟨f.mapMatrix ↑ₘg, by
      rw [← f.map_det]
      simp [g.prop]⟩
  map_one' := Subtype.ext <| f.mapMatrix.map_one
  map_mul' x y := Subtype.ext <| f.mapMatrix.map_mul ↑ₘx ↑ₘy

section center

open Subgroup

@[simp]
theorem center_eq_bot_of_subsingleton [Subsingleton n] :
    center (SpecialLinearGroup n R) = ⊥ :=
  eq_bot_iff.mpr fun x _ ↦ by rw [mem_bot, Subsingleton.elim x 1]

theorem scalar_eq_self_of_mem_center
    {A : SpecialLinearGroup n R} (hA : A ∈ center (SpecialLinearGroup n R)) (i : n) :
    scalar n (A i i) = A := by
  obtain ⟨r : R, hr : scalar n r = A⟩ := mem_range_scalar_of_commute_transvectionStruct fun t ↦
    Subtype.ext_iff.mp <| Subgroup.mem_center_iff.mp hA ⟨t.toMatrix, by simp⟩
  simp [← congr_fun₂ hr i i, ← hr]

theorem scalar_eq_coe_self_center
    (A : center (SpecialLinearGroup n R)) (i : n) :
    scalar n ((A : Matrix n n R) i i) = A :=
  scalar_eq_self_of_mem_center A.property i

/-- The center of a special linear group of degree `n` is the subgroup of scalar matrices, for which
the scalars are the `n`-th roots of unity. -/
theorem mem_center_iff {A : SpecialLinearGroup n R} :
    A ∈ center (SpecialLinearGroup n R) ↔ ∃ (r : R), r ^ (Fintype.card n) = 1 ∧ scalar n r = A := by
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i⟩⟩; · exact ⟨by aesop, by simp [Subsingleton.elim A 1]⟩
  refine ⟨fun h ↦ ⟨A i i, ?_, ?_⟩, fun ⟨r, _, hr⟩ ↦ Subgroup.mem_center_iff.mpr fun B ↦ ?_⟩
  · have : det ((scalar n) (A i i)) = 1 := (scalar_eq_self_of_mem_center h i).symm ▸ A.property
    simpa using this
  · exact scalar_eq_self_of_mem_center h i
  · suffices ↑ₘ(B * A) = ↑ₘ(A * B) from Subtype.val_injective this
    simpa only [coe_mul, ← hr] using (scalar_commute (n := n) r (Commute.all r) B).symm

/-- An equivalence of groups, from the center of the special linear group to the roots of unity. -/
@[simps]
def center_equiv_rootsOfUnity' (i : n) :
    center (SpecialLinearGroup n R) ≃* rootsOfUnity (Fintype.card n) R where
  toFun A :=
    haveI : Nonempty n := ⟨i⟩
    rootsOfUnity.mkOfPowEq (↑ₘA i i) <| by
      obtain ⟨r, hr, hr'⟩ := mem_center_iff.mp A.property
      replace hr' : A.val i i = r := by simp only [← hr', scalar_apply, diagonal_apply_eq]
      simp only [hr', hr]
  invFun a := ⟨⟨a • (1 : Matrix n n R), by aesop⟩,
    Subgroup.mem_center_iff.mpr fun B ↦ Subtype.val_injective <| by simp [coe_mul]⟩
  left_inv A := by
    refine SetCoe.ext <| SetCoe.ext ?_
    obtain ⟨r, _, hr⟩ := mem_center_iff.mp A.property
    simpa [← hr, Submonoid.smul_def, Units.smul_def] using smul_one_eq_diagonal r
  right_inv a := by
    obtain ⟨⟨a, _⟩, ha⟩ := a
    exact SetCoe.ext <| Units.ext <| by simp
  map_mul' A B := by
    dsimp
    ext
    simp only [rootsOfUnity.val_mkOfPowEq_coe, Subgroup.coe_mul, Units.val_mul]
    rw [← scalar_eq_coe_self_center A i, ← scalar_eq_coe_self_center B i]
    simp

open scoped Classical in
/-- An equivalence of groups, from the center of the special linear group to the roots of unity.

See also `center_equiv_rootsOfUnity'`. -/
noncomputable def center_equiv_rootsOfUnity :
    center (SpecialLinearGroup n R) ≃* rootsOfUnity (max (Fintype.card n) 1) R :=
  (isEmpty_or_nonempty n).by_cases
  (fun hn ↦ by
    rw [center_eq_bot_of_subsingleton, Fintype.card_eq_zero, max_eq_right_of_lt zero_lt_one,
      rootsOfUnity_one]
    exact MulEquiv.ofUnique)
  (fun _ ↦
    (max_eq_left (NeZero.one_le : 1 ≤ Fintype.card n)).symm ▸
      center_equiv_rootsOfUnity' (Classical.arbitrary n))

end center

section cast

/-- Coercion of SL `n` `ℤ` to SL `n` `R` for a commutative ring `R`. -/
instance : Coe (SpecialLinearGroup n ℤ) (SpecialLinearGroup n R) :=
  ⟨fun x => map (Int.castRingHom R) x⟩

@[simp]
theorem coe_matrix_coe (g : SpecialLinearGroup n ℤ) :
    ↑(g : SpecialLinearGroup n R) = (↑g : Matrix n n ℤ).map (Int.castRingHom R) :=
  map_apply_coe (Int.castRingHom R) g

lemma map_intCast_injective [CharZero R] :
    Function.Injective ((↑) : SpecialLinearGroup n ℤ → SpecialLinearGroup n R) := fun g h ↦ by
  simp_rw [ext_iff, map_apply_coe, RingHom.mapMatrix_apply, Int.coe_castRingHom,
    Matrix.map_apply, Int.cast_inj]
  tauto

@[simp]
lemma map_intCast_inj [CharZero R] {x y : SpecialLinearGroup n ℤ} :
    (x : SpecialLinearGroup n R) = y ↔ x = y :=
  map_intCast_injective.eq_iff

end cast

section Neg

variable [Fact (Even (Fintype.card n))]

/-- Formal operation of negation on special linear group on even cardinality `n` given by negating
each element. -/
instance instNeg : Neg (SpecialLinearGroup n R) :=
  ⟨fun g => ⟨-g, by
    simpa [(@Fact.out <| Even <| Fintype.card n).neg_one_pow, g.det_coe] using det_smul (↑ₘg) (-1)⟩⟩

@[simp]
theorem coe_neg (g : SpecialLinearGroup n R) : ↑(-g) = -(g : Matrix n n R) :=
  rfl

instance : HasDistribNeg (SpecialLinearGroup n R) :=
  Function.Injective.hasDistribNeg _ Subtype.coe_injective coe_neg coe_mul

@[simp]
theorem coe_int_neg (g : SpecialLinearGroup n ℤ) : ↑(-g) = (-↑g : SpecialLinearGroup n R) :=
  Subtype.ext <| (@RingHom.mapMatrix n _ _ _ _ _ _ (Int.castRingHom R)).map_neg ↑g

end Neg

section SpecialCases

open scoped MatrixGroups

theorem SL2_inv_expl_det (A : SL(2, R)) :
    det ![![A.1 1 1, -A.1 0 1], ![-A.1 1 0, A.1 0 0]] = 1 := by
  simpa [-det_coe, Matrix.det_fin_two, mul_comm] using A.2

theorem SL2_inv_expl (A : SL(2, R)) :
    A⁻¹ = ⟨![![A.1 1 1, -A.1 0 1], ![-A.1 1 0, A.1 0 0]], SL2_inv_expl_det A⟩ := by
  ext
  have := Matrix.adjugate_fin_two A.1
  rw [coe_inv, this]
  simp

theorem fin_two_induction (P : SL(2, R) → Prop)
    (h : ∀ (a b c d : R) (hdet : a * d - b * c = 1), P ⟨!![a, b; c, d], by rwa [det_fin_two_of]⟩)
    (g : SL(2, R)) : P g := by
  obtain ⟨m, hm⟩ := g
  convert h (m 0 0) (m 0 1) (m 1 0) (m 1 1) (by rwa [det_fin_two] at hm)
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem fin_two_exists_eq_mk_of_apply_zero_one_eq_zero {R : Type*} [Field R] (g : SL(2, R))
    (hg : g 1 0 = 0) :
    ∃ (a b : R) (h : a ≠ 0), g = (⟨!![a, b; 0, a⁻¹], by simp [h]⟩ : SL(2, R)) := by
  induction g using Matrix.SpecialLinearGroup.fin_two_induction with | h a b c d h_det =>
  replace hg : c = 0 := by simpa using hg
  have had : a * d = 1 := by rwa [hg, mul_zero, sub_zero] at h_det
  refine ⟨a, b, left_ne_zero_of_mul_eq_one had, ?_⟩
  simp_rw [eq_inv_of_mul_eq_one_right had, hg]

lemma isCoprime_row (A : SL(2, R)) (i : Fin 2) : IsCoprime (A i 0) (A i 1) := by
  refine match i with
  | 0 => ⟨A 1 1, -(A 1 0), ?_⟩
  | 1 => ⟨-(A 0 1), A 0 0, ?_⟩ <;>
  · simp_rw [det_coe A ▸ det_fin_two A.1]
    ring

lemma isCoprime_col (A : SL(2, R)) (j : Fin 2) : IsCoprime (A 0 j) (A 1 j) := by
  refine match j with
  | 0 => ⟨A 1 1, -(A 0 1), ?_⟩
  | 1 => ⟨-(A 1 0), A 0 0, ?_⟩ <;>
  · simp_rw [det_coe A ▸ det_fin_two A.1]
    ring

end SpecialCases

end SpecialLinearGroup

end Matrix

namespace IsCoprime

open Matrix MatrixGroups SpecialLinearGroup

variable {R : Type*} [CommRing R]

/-- Given any pair of coprime elements of `R`, there exists a matrix in `SL(2, R)` having those
entries as its left or right column. -/
lemma exists_SL2_col {a b : R} (hab : IsCoprime a b) (j : Fin 2) :
    ∃ g : SL(2, R), g 0 j = a ∧ g 1 j = b := by
  obtain ⟨u, v, h⟩ := hab
  refine match j with
  | 0 => ⟨⟨!![a, -v; b, u], ?_⟩, rfl, rfl⟩
  | 1 => ⟨⟨!![v, a; -u, b], ?_⟩, rfl, rfl⟩ <;>
  · rw [Matrix.det_fin_two_of, ← h]
    ring

/-- Given any pair of coprime elements of `R`, there exists a matrix in `SL(2, R)` having those
entries as its top or bottom row. -/
lemma exists_SL2_row {a b : R} (hab : IsCoprime a b) (i : Fin 2) :
    ∃ g : SL(2, R), g i 0 = a ∧ g i 1 = b := by
  obtain ⟨u, v, h⟩ := hab
  refine match i with
  | 0 => ⟨⟨!![a, b; -v, u], ?_⟩, rfl, rfl⟩
  | 1 => ⟨⟨!![v, -u; a, b], ?_⟩, rfl, rfl⟩ <;>
  · rw [Matrix.det_fin_two_of, ← h]
    ring

/-- A vector with coprime entries, right-multiplied by a matrix in `SL(2, R)`, has
coprime entries. -/
lemma vecMulSL {v : Fin 2 → R} (hab : IsCoprime (v 0) (v 1)) (A : SL(2, R)) :
    IsCoprime ((v ᵥ* A.1) 0) ((v ᵥ* A.1) 1) := by
  obtain ⟨g, hg⟩ := hab.exists_SL2_row 0
  have : v = g 0 := funext fun t ↦ by { fin_cases t <;> tauto }
  simpa only [this] using isCoprime_row (g * A) 0

/-- A vector with coprime entries, left-multiplied by a matrix in `SL(2, R)`, has
coprime entries. -/
lemma mulVecSL {v : Fin 2 → R} (hab : IsCoprime (v 0) (v 1)) (A : SL(2, R)) :
    IsCoprime ((A.1 *ᵥ v) 0) ((A.1 *ᵥ v) 1) := by
  simpa only [← vecMul_transpose] using hab.vecMulSL A.transpose

end IsCoprime

namespace ModularGroup

open MatrixGroups

open Matrix Matrix.SpecialLinearGroup

/-- The matrix `S = [[0, -1], [1, 0]]` as an element of `SL(2, ℤ)`.

This element acts naturally on the Euclidean plane as a rotation about the origin by `π / 2`.

This element also acts naturally on the hyperbolic plane as rotation about `i` by `π`. It
represents the Mobiüs transformation `z ↦ -1/z` and is an involutive elliptic isometry. -/
def S : SL(2, ℤ) :=
  ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two_of]⟩

/-- The matrix `T = [[1, 1], [0, 1]]` as an element of `SL(2, ℤ)`. -/
def T : SL(2, ℤ) :=
  ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩

theorem coe_S : ↑S = !![0, -1; 1, 0] :=
  rfl

theorem coe_T : ↑T = (!![1, 1; 0, 1] : Matrix _ _ ℤ) :=
  rfl

theorem coe_T_inv : ↑(T⁻¹) = !![1, -1; 0, 1] := by simp [coe_inv, coe_T, adjugate_fin_two]

theorem coe_T_zpow (n : ℤ) : (T ^ n).1 = !![1, n; 0, 1] := by
  induction n with
  | zero => rw [zpow_zero, coe_one, Matrix.one_fin_two]
  | succ n h =>
    simp_rw [zpow_add, zpow_one, coe_mul, h, coe_T, Matrix.mul_fin_two]
    congrm !![_, ?_; _, _]
    rw [mul_one, mul_one, add_comm]
  | pred n h =>
    simp_rw [zpow_sub, zpow_one, coe_mul, h, coe_T_inv, Matrix.mul_fin_two]
    congrm !![?_, ?_; _, _] <;> ring

@[simp]
theorem T_pow_mul_apply_one (n : ℤ) (g : SL(2, ℤ)) : (T ^ n * g) 1 = g 1 := by
  ext j
  simp [coe_T_zpow, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

@[simp]
theorem T_mul_apply_one (g : SL(2, ℤ)) : (T * g) 1 = g 1 := by
  simpa using T_pow_mul_apply_one 1 g

@[simp]
theorem T_inv_mul_apply_one (g : SL(2, ℤ)) : (T⁻¹ * g) 1 = g 1 := by
  simpa using T_pow_mul_apply_one (-1) g

lemma S_mul_S_eq : (S : Matrix (Fin 2) (Fin 2) ℤ) * S = -1 := by
  simp only [S, Int.reduceNeg, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd,
    vecMul_cons, head_cons, zero_smul, tail_cons, neg_smul, one_smul, neg_cons, neg_zero, neg_empty,
    empty_vecMul, add_zero, zero_add, empty_mul, Equiv.symm_apply_apply]
  exact Eq.symm (eta_fin_two (-1))

lemma T_S_rel : S • S • S • T • S • T • S = T⁻¹ := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end ModularGroup
