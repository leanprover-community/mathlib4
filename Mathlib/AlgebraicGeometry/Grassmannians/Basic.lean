import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.AlgebraicGeometry.OpenImmersion

open AlgebraicGeometry Scheme FiniteDimensional CategoryTheory Matrix

noncomputable section

universe u v w

instance basic_open_isOpenImmersion' {R : Type*} [CommRing R] (f : R) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))) :=
  @basic_open_isOpenImmersion (CommRingCat.of R) _

variable (K V : Type u) [Field K] [AddCommGroup V] [Module K V]
  [Module.Finite K V] [Module.Free K V]
variable (r : ℕ) (hr : r < finrank K V)
variable {A : Type*} [CommRing A] [Algebra K A]

variable (R : Type*) [CommRing R] (f : R)

example : IsUnit (algebraMap R (Localization.Away f) f) := by
   refine isUnit_iff_exists_inv.mpr ?_
   existsi IsLocalization.Away.invSelf f
   simp only [IsLocalization.Away.mul_invSelf]

namespace Grassmannian

def chart :=
  Spec (CommRingCat.of (MvPolynomial ((Fin (finrank K V - r)) × Fin r) K))

def matrix (i j : Basis (Fin (finrank K V)) K V) :
    (((Fin (finrank K V - r)) × Fin r) → A) →
    Matrix (Fin (finrank K V)) (Fin r) A := by
  intro φ
  set φ' : Matrix (Fin (finrank K V)) (Fin r) A := Matrix.of
    (fun x y ↦
      if x < r then if x.1 = y.1 then 1 else 0
      else φ (⟨x.1 - r, by have := x.2; omega⟩, y))
  exact (Basis.toMatrix i j).map (algebraMap K A) * φ'

def matrix_F (i j : Basis (Fin (finrank K V)) K V) :
    (((Fin (finrank K V - r)) × Fin r) → A) →
    Matrix (Fin r) (Fin r) A :=
  fun φ  ↦ Matrix.submatrix (matrix K V r hr i j φ) (Fin.castLE hr.le) id

def matrix_G (i j : Basis (Fin (finrank K V)) K V) :
    (((Fin (finrank K V - r)) × Fin r) → A) →
    Matrix (Fin (finrank K V - r)) (Fin r) A :=
  fun φ  ↦ Matrix.submatrix (matrix K V r hr i j φ) (Fin.castLE (by simp)) id


lemma matrix_F_eq_id_of_diagonal (i : Basis (Fin (finrank K V)) K V)
    (M : ((Fin (finrank K V - r)) × Fin r) → A) :
    matrix_F K V r hr i i M = 1 := by
  ext a b
  simp only [matrix_F, matrix, Basis.toMatrix_self, map_zero, _root_.map_one, Matrix.map_one,
    Matrix.one_mul, submatrix_apply, id_eq, of_apply, Fin.coe_castLE, Fin.is_lt, ↓reduceIte]
  by_cases h : a = b
  · simp only [h, ↓reduceIte, one_apply_eq]
  · simp only [ne_eq, h, not_false_eq_true, one_apply_ne, ite_eq_right_iff]
    rw [← Fin.ext_iff]
    simp only [h, false_implies]

lemma matrix_G_eq_of_diagonal (i : Basis (Fin (finrank K V)) K V)
    (M : ((Fin (finrank K V - r)) × Fin r) → A) :
    matrix_G K V r hr i i M = Matrix.of (fun p q ↦ M (p,q)) := by sorry

def element (i j : Basis (Fin (finrank K V)) K V) :
    (MvPolynomial ((Fin (finrank K V - r)) × Fin r) K) := by
  exact (matrix_F (hr := hr) i j MvPolynomial.X
    (A := MvPolynomial ((Fin (finrank K V - r)) × Fin r) K)).det

abbrev matrix_F' (i j : Basis (Fin (finrank K V)) K V) :=
  (algebraMap (MvPolynomial (Fin (finrank K V - r) × Fin r) K)
    (Localization.Away (element K V r hr i j))).mapMatrix
    (matrix_F K V r hr i j (MvPolynomial.X (R := K) (σ := Fin (finrank K V - r) × Fin r)))

abbrev matrix_G' (i j : Basis (Fin (finrank K V)) K V) :=
  (matrix_G K V r hr i j (MvPolynomial.X (R := K) (σ := Fin (finrank K V - r) × Fin r))).map
  (algebraMap (MvPolynomial (Fin (finrank K V - r) × Fin r) K)
  (Localization.Away (element K V r hr i j)))

lemma matrix_F'_eq_id_of_diagonal (i : Basis (Fin (finrank K V)) K V) :
    matrix_F' K V r hr i i = 1 := sorry

lemma matrix_G'_eq_X_of_diagonal (i : Basis (Fin (finrank K V)) K V) :
    matrix_G' K V r hr i i = Matrix.of (fun p q ↦
    (algebraMap (MvPolynomial (Fin (finrank K V - r) × Fin r) K)
    (Localization.Away (element K V r hr i i)) (MvPolynomial.X (p,q)))) := by sorry

lemma isUnit_F' (i j : Basis (Fin (finrank K V)) K V) :
    IsUnit (matrix_F' K V r hr i j) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    rw [← RingHom.map_det]
    simp only [element]
    refine isUnit_iff_exists_inv.mpr ?_
    existsi IsLocalization.Away.invSelf (matrix_F K V r hr i j
      (MvPolynomial.X (R := K))).det
    simp only [IsLocalization.Away.mul_invSelf]

lemma element_eq_one_of_diagonal (i : Basis (Fin (finrank K V)) K V) :
    element K V r hr i i = 1 := by
  simp only [element]
  rw [matrix_F_eq_id_of_diagonal]
  simp only [det_one]

abbrev open_immersion (i j : Basis (Fin (finrank K V)) K V) :=
  Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial ((Fin (finrank K V - r)) × Fin r) K)
    (Localization.Away (Grassmannian.element K V r hr i j))))

def glueData : GlueData where
  J := Basis (Fin (finrank K V)) K V
  U _ := chart K V r
  V ij := Spec (CommRingCat.of (Localization.Away (element K V r hr ij.1 ij.2)))
  f i j := open_immersion K V r hr i j
  f_mono _ _ := inferInstance
  f_hasPullback := inferInstance
  f_id i := by
    simp only [open_immersion]
    suffices h : IsIso ((CommRingCat.ofHom (algebraMap (MvPolynomial
      (Fin (finrank K V - r) × Fin r) K) (Localization.Away (element K V r hr i i))))) by
      exact inferInstance
    rw [element_eq_one_of_diagonal]
    exact localization_unit_isIso (CommRingCat.of
      (MvPolynomial ((Fin (finrank K V - r)) × Fin r) K))
  t i j := by
    simp only
    apply Spec.map
    apply CommRingCat.ofHom
    apply Localization.awayLift (r := element K V r hr j i)
    swap
    · apply MvPolynomial.eval₂Hom (algebraMap K (Localization.Away (element K V r hr i j)))
      exact fun pq ↦ ((matrix_G' K V r hr i j) * (matrix_F' K V r hr i j)⁻¹) pq.1 pq.2
    · simp only [RingHom.mapMatrix_apply, MvPolynomial.coe_eval₂Hom]
      sorry
  t_id i := by
    simp only [RingHom.mapMatrix_apply, id_eq]
    rw [← Spec.map_id]
    apply congrArg
    change _ = CommRingCat.ofHom (RingHom.id _)
    apply congrArg
    simp_rw [matrix_F_eq_id_of_diagonal]
    rw [matrix_G'_eq_X_of_diagonal]
    simp only [map_zero, _root_.map_one, Matrix.map_one, inv_one, Matrix.mul_one, of_apply,
      Prod.mk.eta]
    have heq : MvPolynomial.eval₂Hom (algebraMap K (Localization.Away (element K V r hr i i)))
      (fun pq ↦ (algebraMap (MvPolynomial (Fin (finrank K V - r) × Fin r) K) (Localization.Away
      (element K V r hr i i))) (MvPolynomial.X pq)) = algebraMap _ _ := sorry
    simp_rw [heq]
    ext a
    simp only [RingHom.id_apply]
    change IsLocalization.awayLift _ _ = _
    erw [IsLocalization.Away.AwayMap.lift_eq]
  t' := sorry
  t_fac := sorry
  cocycle := sorry
  f_open _ _ := inferInstance

end Grassmannian
