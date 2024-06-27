import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.AlgebraicGeometry.OpenImmersion

open AlgebraicGeometry Scheme FiniteDimensional CategoryTheory Matrix

noncomputable section

universe u v w

section

variable {m n o α β : Type*} [Fintype m] [Fintype n] [Fintype o]
  [NonAssocSemiring α] [NonAssocSemiring β] (M : Matrix m n α) (N : Matrix n o α) (f : α →+* β)

theorem RingHom.map_matrix_mul' :
    (M * N).map f = (M.map f.toFun) * (N.map f.toFun) := by
  ext i j
  simp only [map_apply, map_matrix_mul, toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
    MonoidHom.toOneHom_coe, MonoidHom.coe_coe]

end

section

variable (R : Type*) [CommRing R] (f : R)

lemma Localization.Away.map_unit : IsUnit (algebraMap R (Localization.Away f) f) := by
   refine isUnit_iff_exists_inv.mpr ?_
   existsi IsLocalization.Away.invSelf f
   simp only [IsLocalization.Away.mul_invSelf]

lemma IsLocalization.Away.invSelf_unit :
    IsUnit (IsLocalization.Away.invSelf (S := Localization.Away f) f) := by
   refine isUnit_iff_exists_inv.mpr ?_
   existsi algebraMap R (Localization.Away f) f
   rw [mul_comm]; simp only [mul_invSelf]

end

instance basic_open_isOpenImmersion' {R : Type*} [CommRing R] (f : R) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))) :=
  @basic_open_isOpenImmersion (CommRingCat.of R) _

variable (K V : Type u) [Field K] [AddCommGroup V] [Module K V]
  [Module.Finite K V] [Module.Free K V]
variable (r : ℕ) (hr : r < finrank K V)
variable {A : Type*} [CommRing A] [Algebra K A]

namespace Grassmannian

abbrev functions_chart := MvPolynomial ((Fin (finrank K V - r)) × Fin r) K

abbrev chart :=
  Spec (CommRingCat.of (MvPolynomial ((Fin (finrank K V - r)) × Fin r) K))

variable {r}

abbrev matrix_coord : Matrix (Fin (finrank K V)) (Fin r) (functions_chart K V r) :=
  Matrix.of
    (fun x y ↦
      if x < r then if x.1 = y.1 then 1 else 0
      else MvPolynomial.X (⟨x.1 - r, by have := x.2; omega⟩, y))

variable {K V}

abbrev B (i j : Basis (Fin (finrank K V)) K V) := i.toMatrix j

example (i j k : Basis (Fin (finrank K V)) K V) : B i j * B j k = B i k :=
  Basis.toMatrix_mul_toMatrix i j k

example (i j : Basis (Fin (finrank K V)) K V) : B i j * B j i = 1 :=
  Basis.toMatrix_mul_toMatrix_flip _ _

abbrev matrix_generic (i j : Basis (Fin (finrank K V)) K V) :
    (((Fin (finrank K V - r)) × Fin r) → A) →
    Matrix (Fin (finrank K V)) (Fin r) A := by
  intro φ
  set φ' : Matrix (Fin (finrank K V)) (Fin r) A := Matrix.of
    (fun x y ↦
      if x < r then if x.1 = y.1 then 1 else 0
      else φ (⟨x.1 - r, by have := x.2; omega⟩, y))
  exact (B j i).map (algebraMap K A) * φ'

abbrev matrix_F_generic (i j : Basis (Fin (finrank K V)) K V) :
    (((Fin (finrank K V - r)) × Fin r) → A) →
    Matrix (Fin r) (Fin r) A :=
  fun φ  ↦ Matrix.submatrix (matrix_generic hr i j φ) (Fin.castLE hr.le) id

abbrev matrix_G_generic (i j : Basis (Fin (finrank K V)) K V) :
    (((Fin (finrank K V - r)) × Fin r) → A) →
    Matrix (Fin (finrank K V - r)) (Fin r) A :=
  fun φ  ↦ Matrix.submatrix (matrix_generic hr i j φ)
    (fun i ↦ ⟨i.1 + r, by have := i.2; omega⟩) id

abbrev matrix (i j : Basis (Fin (finrank K V)) K V) :=
  (B j i).map (algebraMap K _) * matrix_coord K V hr

abbrev matrix_F (i j : Basis (Fin (finrank K V)) K V) :
    Matrix (Fin r) (Fin r) (functions_chart K V r) :=
  Matrix.submatrix ((B j i).map (algebraMap K _) * matrix_coord K V hr) (Fin.castLE hr.le) id

abbrev matrix_G (i j : Basis (Fin (finrank K V)) K V) :
    Matrix (Fin (finrank K V - r)) (Fin r) (functions_chart K V r) :=
  Matrix.submatrix ((B j i).map (algebraMap K _) * matrix_coord K V hr)
    (fun i ↦ ⟨i.1 + r, by have := i.2; omega⟩) id


/-
abbrev matrix_F (i j : Basis (Fin (finrank K V)) K V) :=
  matrix_F_generic hr i j (MvPolynomial.X (R := K) (σ := Fin (finrank K V - r) × Fin r))

abbrev matrix_G (i j : Basis (Fin (finrank K V)) K V) :=
  matrix_G_generic hr i j (MvPolynomial.X (R := K) (σ := Fin (finrank K V - r) × Fin r))
-/

/-
lemma matrix_F_generic_eq_id_of_diagonal (i : Basis (Fin (finrank K V)) K V)
    (M : ((Fin (finrank K V - r)) × Fin r) → A) :
    matrix_F_generic hr i i M = 1 := by
  ext a b
  simp only [matrix, matrix_F_generic, Basis.toMatrix_self, map_zero, _root_.map_one, Matrix.map_one,
    Matrix.one_mul, submatrix_apply, id_eq, of_apply, Fin.coe_castLE, Fin.is_lt, ↓reduceIte]
  by_cases h : a = b
  · simp only [h, ↓reduceIte, one_apply_eq]
  · simp only [ne_eq, h, not_false_eq_true, one_apply_ne, ite_eq_right_iff]
    rw [← Fin.ext_iff]
    simp only [h, false_implies]

lemma matrix_G_generic_eq_of_diagonal (i : Basis (Fin (finrank K V)) K V)
    (M : ((Fin (finrank K V - r)) × Fin r) → A) :
    matrix_G_generic hr i i M = Matrix.of (fun p q ↦ M (p,q)) := by
  ext _ _
  simp only [matrix_G_generic, matrix, Basis.toMatrix_self, map_zero, _root_.map_one, Matrix.map_one,
    Matrix.one_mul, submatrix_apply, id_eq, of_apply, add_lt_iff_neg_right, not_lt_zero',
    ↓reduceIte, add_tsub_cancel_right, Fin.eta]
-/

lemma matrix_F_eq_id_of_diagonal (i : Basis (Fin (finrank K V)) K V) :
    matrix_F hr i i = 1 := by
  apply Matrix.ext; intro a b
  simp only [matrix_F, Basis.toMatrix_self, MvPolynomial.algebraMap_eq, map_zero, _root_.map_one,
    Matrix.map_one, matrix_coord, Matrix.one_mul, submatrix_apply, id_eq, of_apply, Fin.coe_castLE,
    Fin.is_lt, ↓reduceIte]
  by_cases h : a = b
  · simp only [h, ↓reduceIte, one_apply_eq]
  · simp only [ne_eq, h, not_false_eq_true, one_apply_ne, ite_eq_right_iff]
    rw [← Fin.ext_iff]
    simp only [h, false_implies]

lemma matrix_G_eq_of_diagonal (i : Basis (Fin (finrank K V)) K V) :
    matrix_G hr i i = Matrix.of (fun p q ↦ MvPolynomial.X (p,q)) := by
  apply Matrix.ext; intro _ _
  simp only [matrix_G, matrix_coord, Basis.toMatrix_self, map_zero, _root_.map_one, Matrix.map_one,
    Matrix.one_mul, submatrix_apply, id_eq, of_apply, add_lt_iff_neg_right, not_lt_zero',
    ↓reduceIte, add_tsub_cancel_right, Fin.eta]

def equation (i j : Basis (Fin (finrank K V)) K V) :
    (MvPolynomial ((Fin (finrank K V - r)) × Fin r) K) := (matrix_F hr i j).det

abbrev matrix_F' (i j : Basis (Fin (finrank K V)) K V) :=
  (algebraMap (MvPolynomial (Fin (finrank K V - r) × Fin r) K)
    (Localization.Away (equation hr i j))).mapMatrix (matrix_F hr i j)

abbrev matrix_G' (i j : Basis (Fin (finrank K V)) K V) :=
  (matrix_G hr i j).map
  (algebraMap (MvPolynomial (Fin (finrank K V - r) × Fin r) K)
  (Localization.Away (equation hr i j)))

lemma matrix_F'_eq_id_of_diagonal (i : Basis (Fin (finrank K V)) K V) :
    matrix_F' hr i i = 1 := by
  simp only [matrix_F', matrix_F_eq_id_of_diagonal, _root_.map_one]

lemma matrix_G'_eq_X_of_diagonal (i : Basis (Fin (finrank K V)) K V) :
    matrix_G' hr i i = Matrix.of (fun p q ↦
    (algebraMap (MvPolynomial (Fin (finrank K V - r) × Fin r) K)
    (Localization.Away (equation hr i i)) (MvPolynomial.X (p,q)))) := by
  simp only [matrix_G', matrix_G_eq_of_diagonal]
  ext _ _
  simp only [map_apply, of_apply]

local instance isUnit_F' (i j : Basis (Fin (finrank K V)) K V) :
    IsUnit (matrix_F' hr i j) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    rw [← RingHom.map_det]
    simp only [equation]
    refine isUnit_iff_exists_inv.mpr ?_
    existsi IsLocalization.Away.invSelf (matrix_F_generic hr i j
      (MvPolynomial.X (R := K))).det
    simp only [IsLocalization.Away.mul_invSelf]

lemma equation_eq_one_of_diagonal (i : Basis (Fin (finrank K V)) K V) :
    equation hr i i = 1 := by
  simp only [equation]
  rw [matrix_F_eq_id_of_diagonal]
  simp only [det_one]

abbrev open_immersion (i j : Basis (Fin (finrank K V)) K V) :=
  Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial ((Fin (finrank K V - r)) × Fin r) K)
    (Localization.Away (equation hr i j))))

abbrev transition_aux (i j : Basis (Fin (finrank K V)) K V) :
    functions_chart K V r →ₐ[K] Localization.Away (equation hr i j) :=
  {MvPolynomial.eval₂Hom (algebraMap K (Localization.Away (equation hr i j)))
  (fun pq ↦ ((matrix_G' hr i j) * (matrix_F' hr i j)⁻¹) pq.1 pq.2) with
    commutes' := by
      intro a
      simp only [RingHom.toMonoidHom_eq_coe, MvPolynomial.algebraMap_eq, OneHom.toFun_eq_coe,
        MonoidHom.toOneHom_coe, MonoidHom.coe_coe, MvPolynomial.eval₂Hom_C]}

lemma transition_aux_matrix_coord (i j : Basis (Fin (finrank K V)) K V) :
    Matrix.map (matrix_coord K V hr) (transition_aux hr i j) =
    (matrix hr i j).map (algebraMap (MvPolynomial (Fin (finrank K V - r) × Fin r) K)
    (Localization.Away (equation hr i j))) * (matrix_F' hr i j)⁻¹ := by
  sorry

lemma transition_aux_matrix (i j k l : Basis (Fin (finrank K V)) K V) :
    Matrix.map (matrix hr k l) (transition_aux hr i j) =
    (B l k).map (algebraMap K (Localization.Away (equation hr i j))) *
    (B j i).map (algebraMap K (Localization.Away (equation hr i j))) *
    (matrix_coord K V hr).map (algebraMap (MvPolynomial (Fin (finrank K V - r) × Fin r) K)
    (Localization.Away (equation hr i j))) * (matrix_F' hr i j)⁻¹ := by
  simp only [matrix]
  erw [RingHom.map_matrix_mul']; rw [Matrix.map_map]
  have : (transition_aux hr i j).toRingHom.toFun ∘ (algebraMap K (functions_chart K V r)) =
      algebraMap K _ := by
    ext _
    simp only [RingHom.mapMatrix_apply, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
      MonoidHom.toOneHom_coe, MonoidHom.coe_coe, MvPolynomial.coe_eval₂Hom,
      MvPolynomial.algebraMap_eq, Function.comp_apply, MvPolynomial.eval₂_C]
  rw [this]
  conv_lhs => congr; rfl; erw [transition_aux_matrix_coord]
  simp only [matrix]
  conv_rhs => rw [Matrix.mul_assoc, Matrix.mul_assoc]
  congr 1
  conv_rhs => rw [← Matrix.mul_assoc]
  congr 1
  conv_lhs => rw [RingHom.map_matrix_mul']
  rfl

lemma transition_aux_F (i j : Basis (Fin (finrank K V)) K V) :
    Matrix.map (matrix_F hr j i) (transition_aux hr i j) = (matrix_F' hr i j)⁻¹ := by
  simp only [matrix_F]
  rw [← Matrix.submatrix_map, transition_aux_matrix]
  rw [Matrix.submatrix_mul _ _ (e₁ := (Fin.castLE hr.le)) (e₂ := id (α := Fin r)) _
    Function.bijective_id, Matrix.submatrix_id_id]
  slice_lhs 1 2 => rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_mul,
                     Basis.toMatrix_mul_toMatrix_flip i j, RingHom.map_one]
  rw [Matrix.one_mul]
  conv_rhs => rw [← one_mul (matrix_F' hr i j)⁻¹]
  congr 1
  apply Matrix.ext; intro a b
  simp only [submatrix_apply, id_eq, map_apply, of_apply, Fin.coe_castLE, Fin.is_lt, ↓reduceIte,
    RingHom.map_ite_one_zero]
  by_cases h : a = b
  · simp only [h, ↓reduceIte, one_apply_eq]
  · simp only [ne_eq, h, not_false_eq_true, one_apply_ne, ite_eq_right_iff]
    rw [← Fin.ext_iff]
    simp only [h, false_implies]

lemma transition_aux_equation (i j : Basis (Fin (finrank K V)) K V) :
    transition_aux hr i j (equation hr j i) = IsLocalization.Away.invSelf (equation hr i j) := by
  simp only [equation]
  conv_lhs => erw [RingHom.map_det (transition_aux hr i j).toRingHom (matrix_F hr j i)]
              rw [RingHom.mapMatrix_apply]; erw [transition_aux_F]; rw [det_nonsing_inv, matrix_F']
              rw [← RingHom.map_det]
  rw [← one_mul (Ring.inverse _)]
  symm
  simp only [equation]
  rw [Ring.eq_mul_inverse_iff_mul_eq, mul_comm, IsLocalization.Away.mul_invSelf]
  exact Localization.Away.map_unit _ _

abbrev transition (i j : Basis (Fin (finrank K V)) K V) :
    Localization.Away (equation hr j i) →+* Localization.Away (equation hr i j) := by
  apply Localization.awayLift (r := equation hr j i) (transition_aux hr i j)
  erw [transition_aux_equation]
  exact IsLocalization.Away.invSelf_unit _ (equation hr i j)

variable (K V r)

def glueData : GlueData where
  J := Basis (Fin (finrank K V)) K V
  U _ := chart K V r
  V ij := Spec (CommRingCat.of (Localization.Away (equation hr ij.1 ij.2)))
  f i j := open_immersion hr i j
  f_mono _ _ := inferInstance
  f_hasPullback := inferInstance
  f_id i := by
    simp only [open_immersion]
    suffices h : IsIso ((CommRingCat.ofHom (algebraMap (MvPolynomial
      (Fin (finrank K V - r) × Fin r) K) (Localization.Away (equation hr i i))))) by
      exact inferInstance
    rw [equation_eq_one_of_diagonal]
    exact localization_unit_isIso (CommRingCat.of
      (MvPolynomial ((Fin (finrank K V - r)) × Fin r) K))
  t i j := by
    simp only
    apply Spec.map
    apply CommRingCat.ofHom
    exact transition hr i j
  t_id i := by
    simp only [transition, AlgHom.coe_ringHom_mk, RingHom.mapMatrix_apply, id_eq]
    rw [← Spec.map_id]
    apply congrArg
    change _ = CommRingCat.ofHom (RingHom.id _)
    apply congrArg
    simp_rw [matrix_F_eq_id_of_diagonal]
    simp_rw [matrix_G'_eq_X_of_diagonal]
    simp only [map_zero, _root_.map_one, Matrix.map_one, inv_one, Matrix.mul_one, of_apply,
      Prod.mk.eta]
    have heq : MvPolynomial.eval₂Hom (algebraMap K (Localization.Away (equation hr i i)))
        (fun pq ↦ (algebraMap (MvPolynomial (Fin (finrank K V - r) × Fin r) K) (Localization.Away
        (equation hr i i))) (MvPolynomial.X pq)) = algebraMap _ _ := by
      ext a
      · simp only [RingHom.coe_comp, MvPolynomial.coe_eval₂Hom, Function.comp_apply,
        MvPolynomial.eval₂_C]
        rw [← MvPolynomial.algebraMap_eq]
        rw [← IsScalarTower.algebraMap_apply]
      · simp only [MvPolynomial.eval₂Hom_X']
    simp_rw [heq]
    ext _
    simp only [RingHom.id_apply]
    erw [IsLocalization.lift_id]
  t' := sorry
  t_fac := sorry
  cocycle := sorry
  f_open _ _ := inferInstance

end Grassmannian
