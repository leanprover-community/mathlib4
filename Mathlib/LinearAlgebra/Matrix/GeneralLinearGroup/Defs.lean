/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.GeneralLinearGroup
import Mathlib.Algebra.Ring.Subring.Units

/-!
# The General Linear group $GL(n, R)$

This file defines the elements of the General Linear group `Matrix.GeneralLinearGroup n R`,
consisting of all invertible `n` by `n` `R`-matrices.

## Main definitions

* `Matrix.GeneralLinearGroup` is the type of matrices over R which are units in the matrix ring.
* `Matrix.GLPos` gives the subgroup of matrices with
  positive determinant (over a linear ordered ring).

## Tags

matrix group, group, matrix inverse
-/


namespace Matrix

universe u v

open Matrix

open LinearMap

/-- `GL n R` is the group of `n` by `n` `R`-matrices with unit determinant.
Defined as a subtype of matrices -/
abbrev GeneralLinearGroup (n : Type u) (R : Type v) [DecidableEq n] [Fintype n] [Semiring R] :
    Type _ :=
  (Matrix n n R)ˣ

@[inherit_doc] notation "GL" => GeneralLinearGroup

namespace GeneralLinearGroup

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v}

section CoeFnInstance

instance instCoeFun [Semiring R] : CoeFun (GL n R) fun _ => n → n → R where
  coe A := (A : Matrix n n R)

end CoeFnInstance

variable [CommRing R]

/-- The determinant of a unit matrix is itself a unit. -/
@[simps]
def det : GL n R →* Rˣ where
  toFun A :=
    { val := (↑A : Matrix n n R).det
      inv := (↑A⁻¹ : Matrix n n R).det
      val_inv := by rw [← det_mul, A.mul_inv, det_one]
      inv_val := by rw [← det_mul, A.inv_mul, det_one] }
  map_one' := Units.ext det_one
  map_mul' _ _ := Units.ext <| det_mul _ _

lemma det_ne_zero [Nontrivial R] (g : GL n R) : g.val.det ≠ 0 :=
  g.det.ne_zero

/-- The groups `GL n R` (notation for `Matrix.GeneralLinearGroup n R`) and
`LinearMap.GeneralLinearGroup R (n → R)` are multiplicatively equivalent -/
def toLin : GL n R ≃* LinearMap.GeneralLinearGroup R (n → R) :=
  Units.mapEquiv toLinAlgEquiv'.toMulEquiv

/-- Given a matrix with invertible determinant, we get an element of `GL n R`. -/
@[simps! val]
def mk' (A : Matrix n n R) (_ : Invertible (Matrix.det A)) : GL n R :=
  unitOfDetInvertible A

/-- Given a matrix with unit determinant, we get an element of `GL n R`. -/
@[simps! val]
noncomputable def mk'' (A : Matrix n n R) (h : IsUnit (Matrix.det A)) : GL n R :=
  nonsingInvUnit A h

/-- Given a matrix with non-zero determinant over a field, we get an element of `GL n K`. -/
@[simps! val]
def mkOfDetNeZero {K : Type*} [Field K] (A : Matrix n n K) (h : Matrix.det A ≠ 0) : GL n K :=
  mk' A (invertibleOfNonzero h)

theorem ext_iff (A B : GL n R) : A = B ↔ ∀ i j, (A : Matrix n n R) i j = (B : Matrix n n R) i j :=
  Units.ext_iff.trans Matrix.ext_iff.symm

/-- Not marked `@[ext]` as the `ext` tactic already solves this. -/
theorem ext ⦃A B : GL n R⦄ (h : ∀ i j, (A : Matrix n n R) i j = (B : Matrix n n R) i j) : A = B :=
  Units.ext <| Matrix.ext h

section CoeLemmas

variable (A B : GL n R)

@[simp]
theorem coe_mul : ↑(A * B) = (↑A : Matrix n n R) * (↑B : Matrix n n R) :=
  rfl

@[simp]
theorem coe_one : ↑(1 : GL n R) = (1 : Matrix n n R) :=
  rfl

theorem coe_inv : ↑A⁻¹ = (↑A : Matrix n n R)⁻¹ :=
  letI := A.invertible
  invOf_eq_nonsing_inv (↑A : Matrix n n R)

@[simp]
theorem coe_toLin : (toLin A : (n → R) →ₗ[R] n → R) = Matrix.mulVecLin A :=
  rfl

@[simp]
theorem toLin_apply (v : n → R) : (toLin A : _ → n → R) v = Matrix.mulVecLin A v :=
  rfl

end CoeLemmas

variable {S T : Type*} [CommRing S] [CommRing T]

/-- A ring homomorphism ``f : R →+* S`` induces a homomorphism ``GLₙ(f) : GLₙ(R) →* GLₙ(S)``. -/
@[simps! apply_val]
def map (f : R →+* S) : GL n R →* GL n S := Units.map <| (RingHom.mapMatrix f).toMonoidHom

@[simp]
theorem map_id : map (RingHom.id R) = MonoidHom.id (GL n R) :=
  rfl

@[simp]
protected lemma map_apply (f : R →+* S) (i j : n) (g : GL n R) : map f g i j = f (g i j) := by
  rfl

@[simp]
theorem map_comp (f : T →+* R) (g : R →+* S) :
    map (g.comp f) = (map g).comp (map (n := n) f) :=
  rfl

@[simp]
theorem map_comp_apply (f : T →+* R) (g : R →+* S) (x : GL n T) :
    (map g).comp (map f) x = map g (map f x) :=
  rfl

variable (f : R →+* S)

@[simp]
protected lemma map_one : map f (1 : GL n R) = 1 := by
  simp only [map_one]

protected lemma map_mul (g h : GL n R) : map f (g * h) = map f g * map f h := by
  simp only [map_mul]

protected lemma map_inv (g : GL n R) : map f g⁻¹ = (map f g)⁻¹ := by
  simp only [map_inv]

protected lemma map_det (g : GL n R) : Matrix.GeneralLinearGroup.det (map f g) =
    Units.map f (Matrix.GeneralLinearGroup.det g) := by
  ext
  simp only [map,
    Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map, MonoidHom.coe_coe]
  exact Eq.symm (RingHom.map_det f g.1)

lemma map_mul_map_inv (g : GL n R) : map f g * map f g⁻¹ = 1 := by
  simp only [map_inv, mul_inv_cancel]

lemma map_inv_mul_map (g : GL n R) : map f g⁻¹ * map f g = 1 := by
  simp only [map_inv, inv_mul_cancel]

@[simp]
lemma coe_map_mul_map_inv (g : GL n R) : g.val.map f * g.val⁻¹.map f = 1 := by
  rw [← Matrix.map_mul]
  simp only [isUnits_det_units, mul_nonsing_inv, map_zero, map_one, Matrix.map_one]

@[simp]
lemma coe_map_inv_mul_map (g : GL n R) : g.val⁻¹.map f * g.val.map f = 1 := by
  rw [← Matrix.map_mul]
  simp only [isUnits_det_units, nonsing_inv_mul, map_zero, map_one, Matrix.map_one]

end GeneralLinearGroup

namespace SpecialLinearGroup

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]
  {S : Type*} [CommRing S] [Algebra R S]

/-- `toGL` is the map from the special linear group to the general linear group. -/
def toGL : Matrix.SpecialLinearGroup n R →* Matrix.GeneralLinearGroup n R where
  toFun A := ⟨↑A, ↑A⁻¹, congr_arg (·.1) (mul_inv_cancel A), congr_arg (·.1) (inv_mul_cancel A)⟩
  map_one' := Units.ext rfl
  map_mul' _ _ := Units.ext rfl

instance hasCoeToGeneralLinearGroup : Coe (SpecialLinearGroup n R) (GL n R) :=
  ⟨toGL⟩

lemma toGL_injective :
    Function.Injective (toGL : SpecialLinearGroup n R → GL n R) := fun g g' ↦ by
  simpa [toGL] using fun h _ ↦ Subtype.ext h

@[simp]
lemma toGL_inj (g g' : SpecialLinearGroup n R) :
    (g : GeneralLinearGroup n R) = g' ↔ g = g' :=
  toGL_injective.eq_iff

@[simp]
theorem coeToGL_det (g : SpecialLinearGroup n R) :
    Matrix.GeneralLinearGroup.det (g : GL n R) = 1 :=
  Units.ext g.prop

@[simp]
lemma coe_GL_coe_matrix (g : SpecialLinearGroup n R) : ((toGL g) : Matrix n n R) = g := rfl

variable (S) in
/-- `mapGL` is the map from the special linear group over `R` to the general linear group over
`S`, where `S` is an `R`-algebra. -/
def mapGL : Matrix.SpecialLinearGroup n R →* Matrix.GeneralLinearGroup n S :=
  toGL.comp (map (algebraMap R S))

@[simp]
lemma mapGL_inj [FaithfulSMul R S] (g g' : SpecialLinearGroup n R) :
    mapGL S g = mapGL S g' ↔ g = g' := by
  refine ⟨fun h ↦ ?_, by tauto⟩
  apply SpecialLinearGroup.ext
  simpa [mapGL, toGL_inj, ext_iff, (FaithfulSMul.algebraMap_injective R S).eq_iff] using h

lemma mapGL_injective [FaithfulSMul R S] :
    Function.Injective (mapGL (R := R) (n := n) S) :=
  fun a b ↦ by simp

@[simp]
lemma mapGL_coe_matrix (g : SpecialLinearGroup n R) :
    ((mapGL S g) : Matrix n n S) = g.map (algebraMap R S) :=
  rfl

@[simp]
lemma map_mapGL {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (g : SpecialLinearGroup n R) :
    (mapGL S g).map (algebraMap S T) = mapGL T g := by
  ext
  simp [IsScalarTower.algebraMap_apply R S T]

@[simp]
lemma det_mapGL (g : SpecialLinearGroup n R) : (mapGL S g).det = 1 := by
  simp [mapGL]

end SpecialLinearGroup

section

variable {n : Type u} {R : Type v} [DecidableEq n] [Fintype n]
  [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

section

variable (n R)

/-- This is the subgroup of `nxn` matrices with entries over a
linear ordered ring and positive determinant. -/
def GLPos : Subgroup (GL n R) :=
  (Units.posSubgroup R).comap GeneralLinearGroup.det

@[inherit_doc] scoped[MatrixGroups] notation "GL(" n ", " R ")" "⁺" => GLPos (Fin n) R

end

@[simp]
theorem mem_glpos (A : GL n R) : A ∈ GLPos n R ↔ 0 < (Matrix.GeneralLinearGroup.det A : R) :=
  Iff.rfl

theorem GLPos.det_ne_zero (A : GLPos n R) : ((A : GL n R) : Matrix n n R).det ≠ 0 :=
  ne_of_gt A.prop

end

section Neg

variable {n : Type u} {R : Type v} [DecidableEq n] [Fintype n]
  [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  [Fact (Even (Fintype.card n))]

/-- Formal operation of negation on general linear group on even cardinality `n` given by negating
each element. -/
instance : Neg (GLPos n R) :=
  ⟨fun g =>
    ⟨-g, by
      rw [mem_glpos, GeneralLinearGroup.val_det_apply, Units.val_neg, det_neg,
        (Fact.out (p := Even <| Fintype.card n)).neg_one_pow, one_mul]
      exact g.prop⟩⟩

@[simp]
theorem GLPos.coe_neg_GL (g : GLPos n R) : ↑(-g) = -(g : GL n R) :=
  rfl

@[simp]
theorem GLPos.coe_neg (g : GLPos n R) : (↑(-g) : GL n R) = -((g : GL n R) : Matrix n n R) :=
  rfl

@[simp]
theorem GLPos.coe_neg_apply (g : GLPos n R) (i j : n) :
    ((↑(-g) : GL n R) : Matrix n n R) i j = -((g : GL n R) : Matrix n n R) i j :=
  rfl

instance : HasDistribNeg (GLPos n R) :=
  Subtype.coe_injective.hasDistribNeg _ GLPos.coe_neg_GL (GLPos n R).coe_mul

end Neg

namespace SpecialLinearGroup

variable {n : Type u} [DecidableEq n] [Fintype n]
  {R : Type v} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- `Matrix.SpecialLinearGroup n R` embeds into `GL_pos n R` -/
def toGLPos : SpecialLinearGroup n R →* GLPos n R where
  toFun A := ⟨(A : GL n R), show 0 < (↑A : Matrix n n R).det from A.prop.symm ▸ zero_lt_one⟩
  map_one' := Subtype.ext <| Units.ext <| rfl
  map_mul' _ _ := Subtype.ext <| Units.ext <| rfl

instance : Coe (SpecialLinearGroup n R) (GLPos n R) :=
  ⟨toGLPos⟩

theorem toGLPos_injective : Function.Injective (toGLPos : SpecialLinearGroup n R → GLPos n R) :=
  -- Porting note: had to rewrite this to hint the correct types to Lean
  -- (It can't find the coercion GLPos n R → Matrix n n R)
  Function.Injective.of_comp
    (f := fun (A : GLPos n R) ↦ ((A : GL n R) : Matrix n n R))
    Subtype.coe_injective

/-- Coercing a `Matrix.SpecialLinearGroup` via `GL_pos` and `GL` is the same as coercing straight to
a matrix. -/
@[simp]
theorem coe_GLPos_coe_GL_coe_matrix (g : SpecialLinearGroup n R) :
    (↑(↑(↑g : GLPos n R) : GL n R) : Matrix n n R) = ↑g :=
  rfl

@[simp]
theorem coe_to_GLPos_to_GL_det (g : SpecialLinearGroup n R) :
    Matrix.GeneralLinearGroup.det ((g : GLPos n R) : GL n R) = 1 :=
  Units.ext g.prop

variable [Fact (Even (Fintype.card n))]

@[norm_cast]
theorem coe_GLPos_neg (g : SpecialLinearGroup n R) : ↑(-g) = -(↑g : GLPos n R) :=
  Subtype.ext <| Units.ext rfl

end SpecialLinearGroup

end Matrix
