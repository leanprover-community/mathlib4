import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Localization.LocalizationLocalization

open AlgebraicGeometry Scheme FiniteDimensional CategoryTheory Matrix

noncomputable section

universe u v w

section

open Function

variable {X Y : Scheme}

lemma SchemeIsoToBijective (f : X ≅ Y) : Bijective f.hom.val.base := by
  rw [bijective_iff_has_inverse]
  existsi f.inv.val.base
  constructor
  · intro x
    rw [← Function.comp_apply (f := f.inv.val.base)]
    change (f.hom ≫ _).val.base x = x
    rw [Iso.hom_inv_id]
    simp only [id_val_base, TopCat.coe_id, id_eq]
  · intro x
    rw [← Function.comp_apply (f := f.hom.val.base)]
    change (f.inv ≫ _).val.base x = x
    rw [Iso.inv_hom_id]
    simp only [id_val_base, TopCat.coe_id, id_eq]

end

section

open CommRingCat TensorProduct CategoryTheory.Limits

variable (R S T U : Type u) [CommRing R] [CommRing S] [CommRing T] [CommRing U]
  [Algebra R S] [Algebra R T] [Algebra R U] [Algebra S U] [IsScalarTower R S U] [Algebra T U]
  [IsScalarTower R T U]
  (f g : R)

noncomputable
nonrec abbrev Spec.algebraMap : Spec (.of S) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R S))

lemma basicOpen_range [IsLocalization.Away f S] :
    Set.range (Spec.map (CommRingCat.ofHom (algebraMap R S))).val.base =
    Scheme.basicOpen (X := Spec (.of R)) (U := ⊤) ((Scheme.ΓSpecIso (.of R)).inv f) := by
  simp only [basicOpen_eq_of_affine', coe_of]
  rw [Spec.map_base]
  change Set.range ⇑(PrimeSpectrum.comap (algebraMap R S)) = _
  rw [PrimeSpectrum.localization_away_comap_range (S := S) (r := f)]
  rw [← Function.comp_apply (f := (ΓSpecIso (CommRingCat.of R)).hom)]
  change _ = ↑(PrimeSpectrum.basicOpen (((ΓSpecIso (CommRingCat.of R)).inv ≫
    (ΓSpecIso (CommRingCat.of R)).hom) f))
  rw [Iso.inv_hom_id]
  simp only [PrimeSpectrum.basicOpen_eq_zeroLocus_compl, coe_id_of, RingHom.id_apply]


noncomputable
def pullbackSpecIso (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    (pullback (Spec.algebraMap R S) (Spec.algebraMap R T)) ≅ Spec (.of <| S ⊗[R] T) := by
  refine (PreservesPullback.iso (Scheme.Spec) _ _).symm ≪≫ Scheme.Spec.mapIso ?_
  refine (pushoutIsoUnopPullback _ _).op ≪≫ (Iso.op ?_)
  letI H := CommRingCat.pushoutCoconeIsColimit (CommRingCat.ofHom (algebraMap R S))
    (CommRingCat.ofHom (algebraMap R T))
  refine RingEquiv.toCommRingCatIso ?_ ≪≫ (colimit.isoColimitCocone ⟨_, H⟩).symm
  dsimp
  refine AlgEquiv.toRingEquiv (R := R) ?_
  apply (config := { allowSynthFailures := true }) @Algebra.TensorProduct.congr
  · convert IsScalarTower.of_algebraMap_eq ?_
    refine fun _ ↦ rfl
  · apply (config := { allowSynthFailures := true, newGoals := .all }) AlgEquiv.mk
    exacts [Equiv.refl _, fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ ↦ rfl]
  · apply (config := { allowSynthFailures := true, newGoals := .all }) AlgEquiv.mk
    exacts [Equiv.refl _, fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ ↦ rfl]

noncomputable def pullbackLocalizationIso [IsLocalization.Away f S] [IsLocalization.Away g T]
    [IsLocalization.Away (f * g) U] : pullback (Spec.algebraMap R S)
    (Spec.algebraMap R T) ≅ Spec (.of U) := sorry

lemma pullbackSpecIso_inv_fst
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    (pullbackSpecIso R S T).inv ≫ pullback.fst =
      Spec.algebraMap _ _ := by
  simp only [pullbackSpecIso, Scheme.Spec_obj, Scheme.Spec_map, Quiver.Hom.unop_op',
    CommRingCat.coe_of, AlgEquiv.toRingEquiv_eq_coe, id_eq, CommRingCat.pushoutCocone_pt,
    Functor.mapIso_trans, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, Iso.symm_inv,
    RingEquiv.toCommRingCatIso_inv, RingEquiv.toRingHom_eq_coe, op_comp, unop_comp,
    Quiver.Hom.unop_op, Spec.map_comp, Category.assoc, PreservesPullback.iso_hom]
  erw [pullbackComparison_comp_fst]
  simp only [Scheme.Spec_map, ← Spec.map_comp, Category.assoc]
  congr 1
  rw [← Category.assoc, ← (Iso.inv _).unop_op, ← unop_comp]
  erw [pushoutIsoUnopPullback_inv_fst]
  simp only [Quiver.Hom.unop_op, colimit.isoColimitCocone_ι_hom_assoc, span_right,
    CommRingCat.pushoutCocone_pt, CommRingCat.coe_of, PushoutCocone.ι_app_right,
    CommRingCat.pushoutCocone_inr, AlgHom.toRingHom_eq_coe]
  ext; rfl

lemma pullbackLocalizationIso_inv_fst [IsLocalization.Away f S] [IsLocalization.Away g T]
    [IsLocalization.Away (f * g) U] : (pullbackLocalizationIso R S T U f g).inv ≫ pullback.fst =
    Spec.algebraMap _ _ := sorry

lemma pullbackSpecIso_inv_snd
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    (pullbackSpecIso R S T).inv ≫ pullback.snd =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom)) := by
  simp only [pullbackSpecIso, Scheme.Spec_obj, Scheme.Spec_map, Quiver.Hom.unop_op',
    CommRingCat.coe_of, AlgEquiv.toRingEquiv_eq_coe, id_eq, CommRingCat.pushoutCocone_pt,
    Functor.mapIso_trans, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, Iso.symm_inv,
    RingEquiv.toCommRingCatIso_inv, RingEquiv.toRingHom_eq_coe, op_comp, unop_comp,
    Quiver.Hom.unop_op, Spec.map_comp, Category.assoc, PreservesPullback.iso_hom,
    AlgHom.toRingHom_eq_coe]
  erw [pullbackComparison_comp_snd]
  simp only [Scheme.Spec_map, ← Spec.map_comp, Category.assoc]
  congr 1
  rw [← Category.assoc, ← (Iso.inv _).unop_op, ← unop_comp]
  erw [pushoutIsoUnopPullback_inv_snd]
  simp only [Quiver.Hom.unop_op, colimit.isoColimitCocone_ι_hom_assoc, span_right,
    CommRingCat.pushoutCocone_pt, CommRingCat.coe_of, PushoutCocone.ι_app_right,
    CommRingCat.pushoutCocone_inr, AlgHom.toRingHom_eq_coe]
  ext; rfl

lemma pullbackLocalizationIso_inv_snd [IsLocalization.Away f S] [IsLocalization.Away g T]
    [IsLocalization.Away (f * g) U] : (pullbackLocalizationIso R S T U f g).inv ≫ pullback.snd =
    Spec.algebraMap _ _ := sorry

noncomputable def localizationAlgebraOfMulRight [IsLocalization.Away f S]
    [IsLocalization.Away (f * g) U] : Algebra S U :=
  RingHom.toAlgebra (IsLocalization.Away.awayToAwayRight f g)

lemma localization_isScalarTower_of_mul_right [IsLocalization.Away f S]
    [IsLocalization.Away (f * g) U] :
    @IsScalarTower R S U _ (localizationAlgebraOfMulRight R S U f g).toSMul _ := by
  letI := localizationAlgebraOfMulRight R S U f g
  apply IsScalarTower.of_algebraMap_eq'
  exact (IsLocalization.lift_comp _).symm

lemma isLocalizationAway_of_mul_right [IsLocalization.Away f S]
    [IsLocalization.Away (f * g) U] :
    @IsLocalization.Away S _ (algebraMap R S g) U _ (localizationAlgebraOfMulRight R S U f g):= by
  letI := localizationAlgebraOfMulRight R S U f g
  sorry

noncomputable def localizationAlgebraOfMulLeft [IsLocalization.Away g T]
    [IsLocalization.Away (f * g) U] : Algebra T U := by
  have : IsLocalization.Away (g * f) U := by
    rw [mul_comm]
    exact inferInstance
  exact RingHom.toAlgebra (IsLocalization.Away.awayToAwayRight g f)

lemma localization_isScalarTower_of_mul_left [IsLocalization.Away g T]
    [IsLocalization.Away (f * g) U] :
    @IsScalarTower R T U _ (localizationAlgebraOfMulLeft R T U f g).toSMul _ := by
  letI := localizationAlgebraOfMulLeft R T U f g
  apply IsScalarTower.of_algebraMap_eq'
  exact (IsLocalization.lift_comp _).symm

lemma isLocalizationAway_of_mul_left [IsLocalization.Away g T] [Algebra T U] [IsScalarTower R T U]
    [IsLocalization.Away (f * g) U] :
    IsLocalization.Away (algebraMap R T f) U := by
  sorry

end

section

variable {m n o α β : Type*} [Fintype n]
  [NonAssocSemiring α] [NonAssocSemiring β] (M : Matrix m n α) (N : Matrix n o α) (f : α →+* β)

theorem RingHom.map_matrix_mul' :
    (M * N).map f = (M.map f.toFun) * (N.map f.toFun) := by
  ext i j
  simp only [map_apply, map_matrix_mul, toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
    MonoidHom.toOneHom_coe, MonoidHom.coe_coe]

end

namespace Matrix

variable {m n m₁ m₂ α : Type*} (e₁ : m₁ → m) (e₂ : m₂ → m)
  (M : Matrix m n α) (N : Matrix m n α)

lemma eq_of_submatrix_eq (h₁ : M.submatrix e₁ id = N.submatrix e₁ id)
    (h₂ : M.submatrix e₂ id = N.submatrix e₂ id) (hsurj : ∀ (x : m),
  (∃ (y : m₁), e₁ y = x) ∨ (∃ (y : m₂), e₂ y = x)) :
    M = N := by
  apply Matrix.ext; intro p q
  cases (hsurj p) with
  | inl h =>
    obtain ⟨p', h⟩ := h
    rw [← h]
    conv_lhs => congr; rfl; change id q
    rw [← Matrix.submatrix_apply M e₁ id]
    conv_rhs => congr; rfl; change id q
    rw [← Matrix.submatrix_apply N e₁ id]
    rw [h₁]
  | inr h =>
    obtain ⟨p', h⟩ := h
    rw [← h]
    conv_lhs => congr; rfl; change id q
    rw [← Matrix.submatrix_apply M e₂ id]
    conv_rhs => congr; rfl; change id q
    rw [← Matrix.submatrix_apply N e₂ id]
    rw [h₂]

end Matrix

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

variable (K V : Type u) [CommRing K] [AddCommGroup V] [Module K V]
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

lemma matrix_coord_submatrix₁ : (matrix_coord K V hr).submatrix (Fin.castLE hr.le) id = 1 := by
  apply Matrix.ext; intro p q
  simp only [submatrix_apply, id_eq, of_apply, Fin.coe_castLE, Fin.is_lt, ↓reduceIte]
  by_cases h : p = q
  · simp only [h, ↓reduceIte, one_apply_eq]
  · simp only [ne_eq, h, not_false_eq_true, one_apply_ne, ite_eq_right_iff, one_ne_zero, imp_false]
    rw [← Fin.ext_iff]; intro h'; exfalso; exact h h'

lemma matrix_coord_submatrix₂ : (matrix_coord K V hr).submatrix
    (fun i ↦ ⟨i.1 + r, by have := i.2; omega⟩ : Fin (finrank K V - r) → Fin (finrank K V)) id
    = Matrix.of (fun p q ↦ MvPolynomial.X (p,q)) := by
  apply Matrix.ext; intro p q
  simp only [submatrix_apply, id_eq, of_apply, add_lt_iff_neg_right, not_lt_zero', ↓reduceIte,
    add_tsub_cancel_right, Fin.eta]

variable {K V}

abbrev B (i j : Basis (Fin (finrank K V)) K V) := i.toMatrix j

example (i j k : Basis (Fin (finrank K V)) K V) : B i j * B j k = B i k :=
  Basis.toMatrix_mul_toMatrix i j k

example (i j : Basis (Fin (finrank K V)) K V) : B i j * B j i = 1 :=
  Basis.toMatrix_mul_toMatrix_flip _ _

abbrev matrix (i j : Basis (Fin (finrank K V)) K V) :=
  (B j i).map (algebraMap K _) * matrix_coord K V hr

abbrev matrix_F (i j : Basis (Fin (finrank K V)) K V) :
    Matrix (Fin r) (Fin r) (functions_chart K V r) :=
  Matrix.submatrix ((B j i).map (algebraMap K _) * matrix_coord K V hr) (Fin.castLE hr.le) id

abbrev matrix_G (i j : Basis (Fin (finrank K V)) K V) :
    Matrix (Fin (finrank K V - r)) (Fin r) (functions_chart K V r) :=
  Matrix.submatrix ((B j i).map (algebraMap K _) * matrix_coord K V hr)
    (fun i ↦ ⟨i.1 + r, by have := i.2; omega⟩) id

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
    existsi IsLocalization.Away.invSelf (matrix_F hr i j).det
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
  refine Matrix.eq_of_submatrix_eq (Fin.castLE hr.le)
    (fun i ↦ ⟨i.1 + r, by have := i.2; omega⟩ : Fin (finrank K V - r) → Fin (finrank K V))
    _ _ ?_ ?_ ?_
  · rw [Matrix.submatrix_mul _ _ (Fin.castLE hr.le) id id Function.bijective_id,
      Matrix.submatrix_id_id, Matrix.submatrix_map, matrix_coord_submatrix₁]
    rw [Matrix.submatrix_map]
    conv_rhs => congr; change matrix_F' hr i j
    have := IsUnit.invertible (isUnit_F' hr i j)
    rw [Matrix.mul_inv_of_invertible]
    simp only [AlgHom.coe_mk, RingHom.mapMatrix_apply, MvPolynomial.coe_eval₂Hom,
      MvPolynomial.eval₂_zero, MvPolynomial.eval₂_one, Matrix.map_one]
  · rw [Matrix.submatrix_mul _ _ _ id id Function.bijective_id,
      Matrix.submatrix_id_id, Matrix.submatrix_map, matrix_coord_submatrix₂]
    rw [Matrix.submatrix_map]
    conv_rhs => congr; change matrix_G' hr i j
    apply Matrix.ext; intro _ _
    simp only [AlgHom.coe_mk, RingHom.mapMatrix_apply, MvPolynomial.coe_eval₂Hom, map_apply,
      of_apply, MvPolynomial.eval₂_X]
  · intro i
    by_cases h : i.1 < r
    · left
      existsi ⟨i.1, h⟩
      simp only [Fin.castLE_mk, Fin.eta]
    · right
      existsi ⟨i - r, by have := i.2; omega⟩
      simp only; rw [Fin.ext_iff]
      rw [lt_iff_not_le, not_not] at h
      simp only [h, Nat.sub_add_cancel]

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

lemma transition_aux_F (i j k : Basis (Fin (finrank K V)) K V) :
    Matrix.map (matrix_F hr j k) (transition_aux hr i j) =
    (matrix_F hr i k).map (algebraMap (MvPolynomial (Fin (finrank K V - r) × Fin r) K)
    (Localization.Away (equation hr i j))) * (matrix_F' hr i j)⁻¹ := by
  simp only [matrix_F]
  rw [← Matrix.submatrix_map, transition_aux_matrix]
  erw [← RingHom.map_matrix_mul']; rw [Basis.toMatrix_mul_toMatrix k j i]
  rw [Matrix.submatrix_mul _ _ (e₁ := (Fin.castLE hr.le)) (e₂ := id (α := Fin r)) _
    Function.bijective_id, Matrix.submatrix_id_id]
  congr 1
  rw [← Matrix.submatrix_map]
  conv_rhs => rw [RingHom.map_matrix_mul']
  rfl
lemma transition_aux_F_flip (i j : Basis (Fin (finrank K V)) K V) :
    Matrix.map (matrix_F hr j i) (transition_aux hr i j) = (matrix_F' hr i j)⁻¹ := by
  rw [transition_aux_F, matrix_F_eq_id_of_diagonal]
  simp only [map_zero, _root_.map_one, Matrix.map_one, RingHom.mapMatrix_apply, one_mul]

lemma transition_aux_equation (i j : Basis (Fin (finrank K V)) K V) :
    transition_aux hr i j (equation hr j i) = IsLocalization.Away.invSelf (equation hr i j) := by
  simp only [equation]
  conv_lhs => erw [RingHom.map_det (transition_aux hr i j).toRingHom (matrix_F hr j i)]
              rw [RingHom.mapMatrix_apply]; erw [transition_aux_F_flip]
              rw [det_nonsing_inv, matrix_F', ← RingHom.map_det]
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

abbrev transition_Spec (i j : Basis (Fin (finrank K V)) K V) :=
  Spec.map (CommRingCat.ofHom (transition hr i j))

abbrev transition'₁ (i j k : Basis (Fin (finrank K V)) K V) :
    Limits.pullback (open_immersion hr i j) (open_immersion hr i k) ⟶
    Spec (CommRingCat.of (Localization.Away (equation hr j k))) := by
  refine (pullbackSpecIso (MvPolynomial (Fin (finrank K V - r) × Fin r) K)
    (Localization.Away (equation hr i j)) (Localization.Away (equation hr i k))).hom ≫
    Spec.map (CommRingCat.ofHom (IsLocalization.Away.lift (equation hr j k) ?_
    (g := Algebra.TensorProduct.includeLeftRingHom.comp (transition_aux hr i j))))
  sorry

lemma transition'₁_immersion (i j k : Basis (Fin (finrank K V)) K V) :
    transition'₁ hr i j k ≫ open_immersion hr j k =
    (Limits.pullback.fst ≫ transition_Spec hr i j) ≫ open_immersion hr j i := by
  rw [transition'₁]
  rw [← cancel_epi (f := (pullbackSpecIso (MvPolynomial (Fin (finrank K V - r) × Fin r) K)
    (Localization.Away (equation hr i j)) (Localization.Away (equation hr i k))).inv)]
  rw [← Category.assoc, ← Category.assoc, Iso.inv_hom_id, Category.id_comp, ← Category.assoc]
  rw [← Category.assoc, pullbackSpecIso_inv_fst]
  conv_rhs => rw [Spec.algebraMap, open_immersion, ← Spec.map_comp, ← Spec.map_comp]
  conv_lhs => rw [open_immersion, ← Spec.map_comp]
  apply congrArg Spec.map
  rw [← CommRingCat.ringHom_comp_eq_comp, ← Category.assoc, ← CommRingCat.ringHom_comp_eq_comp]
  conv_rhs => change CommRingCat.ofHom ((transition hr i j).comp (algebraMap _ _)) ≫
    CommRingCat.ofHom (algebraMap _ _)
              rw [← CommRingCat.ringHom_comp_eq_comp]
  rw [transition]
  rw [IsLocalization.Away.AwayMap.lift_comp, IsLocalization.Away.AwayMap.lift_comp]
  rfl

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
  t i j := transition_Spec hr i j
  t_id i := by
    simp only [transition_Spec, transition, AlgHom.coe_ringHom_mk, RingHom.mapMatrix_apply, id_eq]
    rw [← Spec.map_id]
    apply congrArg
    change _ = CommRingCat.ofHom (RingHom.id _)
    apply congrArg
    apply IsLocalization.ringHom_ext (R := MvPolynomial (Fin (finrank K V - r) × Fin r) K)
      (M := Submonoid.powers (equation hr i i))
    ext x
    · simp only [AlgHom.coe_ringHom_mk, RingHom.mapMatrix_apply,
      IsLocalization.Away.AwayMap.lift_comp, RingHom.coe_comp, MvPolynomial.coe_eval₂Hom,
      Function.comp_apply, MvPolynomial.eval₂_C, RingHomCompTriple.comp_eq]
      rw [← MvPolynomial.algebraMap_eq]
      rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin (finrank K V - r) × Fin r) K)]
    · simp only [AlgHom.coe_ringHom_mk, RingHom.mapMatrix_apply,
      IsLocalization.Away.AwayMap.lift_comp, MvPolynomial.eval₂Hom_X', RingHomCompTriple.comp_eq]
      simp_rw [matrix_F_eq_id_of_diagonal]
      simp_rw [matrix_G'_eq_X_of_diagonal]
      simp only [map_zero, _root_.map_one, Matrix.map_one, inv_one, Matrix.mul_one, of_apply,
        Prod.mk.eta]
  t' i j k := by
    refine Limits.pullback.lift (transition'₁ hr i j k)
      (Limits.pullback.fst ≫ transition_Spec hr i j) ?_
    exact transition'₁_immersion _ _ _ _
  t_fac i j k := by simp
  cocycle i j k := by
    simp only
  f_open _ _ := inferInstance


end Grassmannian
