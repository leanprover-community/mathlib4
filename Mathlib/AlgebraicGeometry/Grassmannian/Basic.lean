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

def AlgebraicGeometry.Scheme.GlueData.glueMorphisms (GD : Scheme.GlueData)
    {Y : Scheme} (f : (i : GD.J) → GD.U i ⟶ Y) (hf : ∀ (i j : GD.J),
    GD.f i j ≫ (f i) = GD.t i j ≫ GD.f j i ≫ (f j)) :
    GD.glued ⟶ Y := by
  refine Limits.Multicoequalizer.desc _ Y f ?_
  simp only [GlueData.diagram_l, GlueData.diagram_left, GlueData.diagram_right, Prod.forall,
    GlueData.diagram_fstFrom, GlueData.diagram_fst, GlueData.diagram_sndFrom, GlueData.diagram_snd,
    Category.assoc]
  exact hf

@[simp, reassoc]
theorem AlgebraicGeometry.Scheme.GlueData.ι_glueMorphisms (GD : Scheme.GlueData) {Y : Scheme}
    (f : (i : GD.J) → GD.U i ⟶ Y) (hf : ∀ (i j : GD.J), GD.f i j ≫ (f i) =
    GD.t i j ≫ GD.f j i ≫ (f j)) (i : GD.J) : GD.ι i ≫ GD.glueMorphisms f hf = f i := by
  erw [Limits.Multicoequalizer.π_desc]

theorem AlgebraicGeometry.Scheme.GlueData.hom_ext (GD : Scheme.GlueData) {Y : Scheme}
    (f₁ f₂ : GD.glued ⟶ Y) (h : ∀ (i : GD.J), GD.ι i ≫ f₁ = GD.ι i ≫ f₂) : f₁ = f₂ :=
  GD.openCover.hom_ext f₁ f₂ h

end

section

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

lemma Algebra.TensorProduct.algebraMap : algebraMap R (TensorProduct R A B) =
    Algebra.TensorProduct.includeLeftRingHom.comp (algebraMap R A) := by
  ext _
  simp only [algebraMap_apply, RingHom.coe_comp, Function.comp_apply, includeLeftRingHom_apply]

/-
lemma Algebra.TensorProduct.algebraMap' : algebraMap R (TensorProduct R A B) =
    Algebra.TensorProduct.includeRight.toRingHom.comp (algebraMap R B) := sorry
-/

end

section

open Function

variable {X Y : Scheme}

lemma SchemeIsoToBijective (f : X ≅ Y) : Bijective f.hom.val.base := by
  change Bijective ((Scheme.forgetToTop ⋙ forget TopCat).mapIso f).toEquiv
  exact Equiv.bijective _

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

/-
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
-/

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

/-
noncomputable def pullbackLocalizationIso [IsLocalization.Away f S] [IsLocalization.Away g T]
    [IsLocalization.Away (f * g) U] : pullback (Spec.algebraMap R S)
    (Spec.algebraMap R T) ≅ Spec (.of U) := sorry
-/

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

/-
lemma pullbackLocalizationIso_inv_fst [IsLocalization.Away f S] [IsLocalization.Away g T]
    [IsLocalization.Away (f * g) U] : (pullbackLocalizationIso R S T U f g).inv ≫ pullback.fst =
    Spec.algebraMap _ _ := sorry
-/

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

/-
lemma pullbackLocalizationIso_inv_snd [IsLocalization.Away f S] [IsLocalization.Away g T]
    [IsLocalization.Away (f * g) U] : (pullbackLocalizationIso R S T U f g).inv ≫ pullback.snd =
    Spec.algebraMap _ _ := sorry
-/

/-
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
-/

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

section
variable {m α β : Type*} [Fintype m] [DecidableEq m]
  [Ring α] [Ring β] (M : Matrix m m α) (f : α →+* β)

theorem RingHom.map_inv (x : α) (hx : IsUnit x) :
    f (Ring.inverse x) = Ring.inverse (f x) := by
  change f (Ring.inverse (IsUnit.unit hx).1) = _
  rw [Ring.inverse_unit]; erw [← Units.coe_map_inv]; rw [← Ring.inverse_unit, Units.coe_map]
  rfl

/-
theorem RingHom.mapMatrix_inv : f.mapMatrix M⁻¹ = (f.mapMatrix M)⁻¹ := sorry

theorem RingHom.map_matrix_inv : M⁻¹.map f = (M.map f)⁻¹ := sorry
-/

end

section

lemma AlgHom.map_inv {R : Type*} {α : Type*} {β : Type*} [CommRing R] [Ring α] [Ring β]
    [Algebra R α] [Algebra R β] (f : α →ₐ[R] β) (x : α) (hx : IsUnit x) :
    f (Ring.inverse x) = Ring.inverse (f x) := by
  erw [RingHom.map_inv _ _ hx]; rfl

/-
lemma AlgHom.mapMatrix_inv {m : Type*} {R : Type*} {α : Type*} {β : Type*} [Fintype m]
    [DecidableEq m] [CommRing R] [CommRing α] [CommRing β] [Algebra R α] [Algebra R β]
    (f : α →ₐ[R] β) (M : Matrix m m α) : f.mapMatrix M⁻¹ = (f.mapMatrix M)⁻¹ := sorry
-/

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

abbrev matrix_X : Matrix (Fin (finrank K V - r)) (Fin r) (functions_chart K V r) :=
  Matrix.of (fun p q ↦ MvPolynomial.X (p,q))

lemma matrix_coord_submatrix₁ : (matrix_coord K V hr).submatrix (Fin.castLE hr.le) id = 1 := by
  apply Matrix.ext; intro p q
  simp only [submatrix_apply, id_eq, of_apply, Fin.coe_castLE, Fin.is_lt, ↓reduceIte]
  by_cases h : p = q
  · simp only [h, ↓reduceIte, one_apply_eq]
  · simp only [ne_eq, h, not_false_eq_true, one_apply_ne, ite_eq_right_iff, one_ne_zero, imp_false]
    rw [← Fin.ext_iff]; intro h'; exfalso; exact h h'

lemma matrix_coord_submatrix₂ : (matrix_coord K V hr).submatrix
    (fun i ↦ ⟨i.1 + r, by have := i.2; omega⟩ : Fin (finrank K V - r) → Fin (finrank K V)) id
    = matrix_X K V := by
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

abbrev matrix_X' (i j : Basis (Fin (finrank K V)) K V) :=
  (matrix_X K V).map
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

lemma transition_aux_matrix_X (i j : Basis (Fin (finrank K V)) K V) :
     Matrix.map (matrix_X K V) (transition_aux hr i j) =
    (matrix_G' hr i j) * (matrix_F' hr i j)⁻¹ := by
  conv_rhs => congr; change matrix_G' hr i j
  apply Matrix.ext; intro _ _
  simp only [AlgHom.coe_mk, RingHom.mapMatrix_apply, MvPolynomial.coe_eval₂Hom, map_apply,
      of_apply, MvPolynomial.eval₂_X]

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
    exact transition_aux_matrix_X _ _ _
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

lemma transition_aux_G (i j k : Basis (Fin (finrank K V)) K V) :
    Matrix.map (matrix_G hr j k) (transition_aux hr i j) =
    (matrix_G hr i k).map (algebraMap (MvPolynomial (Fin (finrank K V - r) × Fin r) K)
    (Localization.Away (equation hr i j))) * (matrix_F' hr i j)⁻¹ := by
  simp only [matrix_G]
  rw [← Matrix.submatrix_map, transition_aux_matrix]
  erw [← RingHom.map_matrix_mul']; rw [Basis.toMatrix_mul_toMatrix k j i]
  conv_lhs => rw [Matrix.submatrix_mul _ (matrix_F' hr i j)⁻¹ _ (e₂ := id (α := Fin r))
    (e₃ := id (α := Fin r)) Function.bijective_id, Matrix.submatrix_id_id]
  congr 1
  rw [← Matrix.submatrix_map]
  conv_rhs => rw [RingHom.map_matrix_mul']
  rfl

lemma transition_aux_equation (i j k : Basis (Fin (finrank K V)) K V) :
    transition_aux hr i j (equation hr j k) =
    algebraMap _ (Localization.Away (equation hr i j)) (equation hr i k) *
    IsLocalization.Away.invSelf (equation hr i j) := by
  simp only [equation]
  conv_lhs => erw [RingHom.map_det (transition_aux hr i j).toRingHom (matrix_F hr j k)]
              rw [RingHom.mapMatrix_apply]; erw [transition_aux_F]
              rw [Matrix.det_mul, det_nonsing_inv, matrix_F', ← RingHom.map_det,
                ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  congr 1
  rw [← one_mul (Ring.inverse _)]
  symm
  simp only [equation]
  rw [Ring.eq_mul_inverse_iff_mul_eq, mul_comm, IsLocalization.Away.mul_invSelf]
  exact Localization.Away.map_unit _ _

lemma transition_aux_F_flip (i j : Basis (Fin (finrank K V)) K V) :
    Matrix.map (matrix_F hr j i) (transition_aux hr i j) = (matrix_F' hr i j)⁻¹ := by
  rw [transition_aux_F, matrix_F_eq_id_of_diagonal]
  simp only [map_zero, _root_.map_one, Matrix.map_one, RingHom.mapMatrix_apply, one_mul]

lemma transition_aux_G_flip (i j : Basis (Fin (finrank K V)) K V) :
    Matrix.map (matrix_G hr j i) (transition_aux hr i j) =
    (matrix_X' hr i j) * (matrix_F' hr i j)⁻¹ := by
  rw [transition_aux_G, matrix_G_eq_of_diagonal]

lemma transition_aux_equation_flip (i j : Basis (Fin (finrank K V)) K V) :
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


lemma transition_aux_equation_isUnit (i j : Basis (Fin (finrank K V)) K V) :
    IsUnit ((transition_aux hr i j) (equation hr j i)) := by
  erw [transition_aux_equation_flip]
  exact IsLocalization.Away.invSelf_unit _ (equation hr i j)

abbrev transitionRingHom (i j : Basis (Fin (finrank K V)) K V) :
    Localization.Away (equation hr j i) →+* Localization.Away (equation hr i j) := by
  apply Localization.awayLift (r := equation hr j i) (transition_aux hr i j)
  exact transition_aux_equation_isUnit _ _ _

abbrev transition (i j : Basis (Fin (finrank K V)) K V) :
    Localization.Away (equation hr j i) →ₐ[K] Localization.Away (equation hr i j) :=
  {
   transitionRingHom hr i j with
   commutes' := by
     intro x
     dsimp
     rw [transitionRingHom]
     rw [IsScalarTower.algebraMap_apply _ (functions_chart K V r) _]
     rw [IsLocalization.Away.AwayMap.lift_eq]
     simp only [AlgHom.coe_ringHom_mk, RingHom.mapMatrix_apply, MvPolynomial.algebraMap_eq,
       MvPolynomial.eval₂Hom_C]
  }

lemma transition_F'_flip (i j : Basis (Fin (finrank K V)) K V) :
    Matrix.map (matrix_F' hr j i) (transition hr i j) = (matrix_F' hr i j)⁻¹ := by
  rw [transition, matrix_F', RingHom.mapMatrix_apply, Matrix.map_map]
  rw [← AlgHom.coe_toRingHom]
  rw [← RingHom.coe_comp]; erw [IsLocalization.Away.AwayMap.lift_comp]
  erw [transition_aux_F_flip]; erw [transition_aux_equation_flip]
  apply IsLocalization.Away.invSelf_unit

lemma transition_F'_inv_flip (i j : Basis (Fin (finrank K V)) K V) :
    Matrix.map (matrix_F' hr j i)⁻¹ (transition hr i j) = matrix_F' hr i j := by
  rw [← AlgHom.coe_toRingHom]
  rw [← RingHom.mapMatrix_apply, Matrix.nonsing_inv_eq_ring_inverse]
  erw [RingHom.map_inv (f := (transition hr i j).toRingHom.mapMatrix)
    (α := Matrix (Fin r) (Fin r) (Localization.Away (equation hr j i)))
    (β := Matrix (Fin r) (Fin r) (Localization.Away (equation hr i j)))]
  rw [RingHom.mapMatrix_apply]
  erw [transition_F'_flip]
  rw [← Matrix.nonsing_inv_eq_ring_inverse (matrix_F' hr i j)⁻¹, Matrix.nonsing_inv_nonsing_inv]
  rw [← Matrix.isUnit_iff_isUnit_det]; all_goals (exact isUnit_F' _ _ _)

lemma transition_G'_flip (i j : Basis (Fin (finrank K V)) K V) :
    Matrix.map (matrix_G' hr j i) (transition hr i j) =
    (matrix_X' hr i j) * (matrix_F' hr i j)⁻¹ := by
  rw [transition, matrix_G', Matrix.map_map]
  rw [← AlgHom.coe_toRingHom, ← RingHom.coe_comp]; erw [IsLocalization.Away.AwayMap.lift_comp]
  erw [transition_aux_G_flip]
  exact transition_aux_equation_isUnit _ _ _

lemma transition_transition (i j : Basis (Fin (finrank K V)) K V) :
    (transition hr i j).comp (transition hr j i) = AlgHom.id _ _ := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (R := MvPolynomial (Fin (finrank K V - r) × Fin r) K)
    (M := Submonoid.powers (equation hr i j))
  simp only [AlgHom.id_toRingHom, RingHomCompTriple.comp_eq]
  rw [AlgHom.comp_toRingHom, RingHom.comp_assoc]
  conv_lhs => congr; rfl; rw [transition]; erw [IsLocalization.Away.AwayMap.lift_comp]; rfl;
              exact transition_aux_equation_isUnit _ _ _
  ext x
  · rw [← MvPolynomial.algebraMap_eq]
    rw [← AlgHom.comp_toRingHom]
    erw [AlgHom.comp_algebraMap]
    simp only [transition, AlgHom.coe_ringHom_mk, RingHom.mapMatrix_apply,
    MvPolynomial.comp_eval₂Hom, RingHom.coe_comp, MvPolynomial.coe_eval₂Hom, Function.comp_apply,
    MvPolynomial.eval₂_C]
    rw [← IsScalarTower.algebraMap_apply]
  · simp only [AlgHom.coe_ringHom_mk, RingHom.mapMatrix_apply, MvPolynomial.comp_eval₂Hom,
    MvPolynomial.eval₂Hom_X']
    change ((matrix_G' hr j i) * (matrix_F' hr j i)⁻¹).map (transition hr i j) x.1 x.2 = _
    erw [Matrix.map_mul, transition_F'_inv_flip, transition_G'_flip]
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul, Matrix.mul_one]
    simp only [map_apply, of_apply, Prod.mk.eta]
    rw [← Matrix.isUnit_iff_isUnit_det]; exact isUnit_F' hr i j

abbrev transition_Spec (i j : Basis (Fin (finrank K V)) K V) :=
  Spec.map (CommRingCat.ofHom (transition hr i j).toRingHom)

lemma transition_transition_Spec (i j : Basis (Fin (finrank K V)) K V) :
    transition_Spec hr i j ≫ transition_Spec hr j i = 𝟙 _ := by
  simp only [transition_Spec]
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((transition hr i j).comp (transition hr j i)).toRingHom) = _
  rw [transition_transition]
  change Spec.map (𝟙 _) = _
  rw [Spec.map_id]

def transition'₁RingHom (i j k : Basis (Fin (finrank K V)) K V) :
    Localization.Away (equation hr j k) →+* (TensorProduct (MvPolynomial
    (Fin (finrank K V - r) × Fin r) K) (Localization.Away (equation hr i j))
    (Localization.Away (equation hr i k))) := by
  refine IsLocalization.Away.lift (equation hr j k) ?_
    (g := Algebra.TensorProduct.includeLeftRingHom.comp (transition_aux hr i j))
  rw [RingHom.comp_apply]; erw [transition_aux_equation, RingHom.map_mul, IsUnit.mul_iff]
  constructor
  · rw [← RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap,
      RingHom.comp_apply]
    exact IsUnit.map Algebra.TensorProduct.includeRight (Localization.Away.map_unit _ _)
  · exact IsUnit.map Algebra.TensorProduct.includeLeftRingHom
      (IsLocalization.Away.invSelf_unit _ _)

def transition'₁ (i j k : Basis (Fin (finrank K V)) K V) :
    Localization.Away (equation hr j k) →ₐ[K] (TensorProduct (MvPolynomial
    (Fin (finrank K V - r) × Fin r) K) (Localization.Away (equation hr i j))
    (Localization.Away (equation hr i k))) := by
  exact
  {
    transition'₁RingHom hr i j k with
    commutes' := by
      intro x
      simp only [transition'₁RingHom, AlgHom.coe_ringHom_mk, RingHom.mapMatrix_apply,
        MvPolynomial.comp_eval₂Hom, Algebra.TensorProduct.includeLeftRingHom_apply,
        RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe,
        Algebra.TensorProduct.algebraMap_apply]
      rw [IsScalarTower.algebraMap_apply (R := K) (S := functions_chart K V r)]
      rw [IsLocalization.Away.AwayMap.lift_eq]
      simp only [MvPolynomial.algebraMap_eq, MvPolynomial.eval₂Hom_C, RingHom.coe_comp,
        Function.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply]
  }

def transition'₁_Spec (i j k : Basis (Fin (finrank K V)) K V) :
    Limits.pullback (open_immersion hr i j) (open_immersion hr i k) ⟶
    Spec (CommRingCat.of (Localization.Away (equation hr j k))) :=
  (pullbackSpecIso (MvPolynomial (Fin (finrank K V - r) × Fin r) K)
    (Localization.Away (equation hr i j)) (Localization.Away (equation hr i k))).hom ≫
    Spec.map (CommRingCat.ofHom (transition'₁ hr i j k))

abbrev matrix_F''ij (i j k : Basis (Fin (finrank K V)) K V) :=
  (algebraMap (MvPolynomial (Fin (finrank K V - r) × Fin r) K)
  (TensorProduct (MvPolynomial (Fin (finrank K V - r) × Fin r) K) (Localization.Away
  (equation hr i j)) (Localization.Away (equation hr i k)))).mapMatrix (matrix_F hr i j)

abbrev matrix_G''ij (i j k : Basis (Fin (finrank K V)) K V) :=
  (matrix_G hr i j).map
  (algebraMap (MvPolynomial (Fin (finrank K V - r) × Fin r) K)
  (TensorProduct (MvPolynomial (Fin (finrank K V - r) × Fin r) K) (Localization.Away
  (equation hr i j)) (Localization.Away (equation hr i k))))

abbrev matrix_F''ik (i j k : Basis (Fin (finrank K V)) K V) :=
  (algebraMap (MvPolynomial (Fin (finrank K V - r) × Fin r) K)
  (TensorProduct (MvPolynomial (Fin (finrank K V - r) × Fin r) K) (Localization.Away
  (equation hr i j)) (Localization.Away (equation hr i k)))).mapMatrix (matrix_F hr i k)

lemma matrix_F''ij_inv_eq (i j k : Basis (Fin (finrank K V)) K V) :
    (matrix_F''ij hr i j k)⁻¹ =
    RingHom.mapMatrix Algebra.TensorProduct.includeLeftRingHom (matrix_F' hr i j)⁻¹ := by
  conv_rhs => rw [Matrix.nonsing_inv_eq_ring_inverse]
              change AlgHom.mapMatrix (R := functions_chart K V r)
                Algebra.TensorProduct.includeLeft (Ring.inverse (matrix_F' hr i j))
              rw [AlgHom.map_inv (f := Algebra.TensorProduct.includeLeft.mapMatrix)
              (α := Matrix (Fin r) (Fin r) (Localization.Away (equation hr i j)))
              (β := Matrix (Fin r) (Fin r) (TensorProduct (MvPolynomial
              (Fin (finrank K V - r) × Fin r) K) (Localization.Away (equation hr i j))
              (Localization.Away (equation hr i k)))) _ (isUnit_F' hr i j)]
  rw [Matrix.nonsing_inv_eq_ring_inverse, matrix_F']
  conv_rhs => rw [AlgHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_map]
              erw [← RingHom.coe_comp, ← Algebra.TensorProduct.algebraMap]
              rw [← RingHom.mapMatrix_apply]

lemma matrix_F''ik_inv_eq (i j k : Basis (Fin (finrank K V)) K V) :
    (matrix_F''ik hr i j k)⁻¹ =
    AlgHom.mapMatrix Algebra.TensorProduct.includeRight (matrix_F' hr i k)⁻¹ := by
  conv_rhs => rw [Matrix.nonsing_inv_eq_ring_inverse]
              rw [AlgHom.map_inv (f := Algebra.TensorProduct.includeRight.mapMatrix)
              (α := Matrix (Fin r) (Fin r) (Localization.Away (equation hr i k)))
              (R := MvPolynomial (Fin (finrank K V - r) × Fin r) K)
              (β := Matrix (Fin r) (Fin r) (TensorProduct (MvPolynomial
              (Fin (finrank K V - r) × Fin r) K) (Localization.Away (equation hr i j))
              (Localization.Away (equation hr i k)))) _ (isUnit_F' hr i k)]
  rw [Matrix.nonsing_inv_eq_ring_inverse, matrix_F']
  have heq : Algebra.TensorProduct.includeRight ∘ (algebraMap (MvPolynomial
    (Fin (finrank K V - r) × Fin r) K) (Localization.Away (equation hr i k))) =
    algebraMap _ (TensorProduct (MvPolynomial
    (Fin (finrank K V - r) × Fin r) K) (Localization.Away (equation hr i j))
    (Localization.Away (equation hr i k))) := by
    ext _
    simp only [Function.comp_apply, AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
  rw [AlgHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_map, heq]
  rw [matrix_F''ik, RingHom.mapMatrix_apply]

abbrev matrix_G''ik (i j k : Basis (Fin (finrank K V)) K V) :=
  (matrix_G hr i k).map
  (algebraMap (MvPolynomial (Fin (finrank K V - r) × Fin r) K)
  (TensorProduct (MvPolynomial (Fin (finrank K V - r) × Fin r) K) (Localization.Away
  (equation hr i j)) (Localization.Away (equation hr i k))))

lemma matrix_F''ij_isUnit (i j k : Basis (Fin (finrank K V)) K V) :
    IsUnit (matrix_F''ij hr i j k) := by
  rw [matrix_F''ij, Algebra.TensorProduct.algebraMap, ← RingHom.mapMatrix_comp, RingHom.comp_apply]
  apply IsUnit.map
  exact isUnit_F' hr i j

/-
lemma matrix_F''ik_isUnit (i j k : Basis (Fin (finrank K V)) K V) :
    IsUnit (matrix_F''ik hr i j k) := sorry
-/

lemma transition'₁_algebraMap (i j k : Basis (Fin (finrank K V)) K V) :
    (transition'₁RingHom hr i j k).comp (algebraMap (functions_chart K V r) _) =
    Algebra.TensorProduct.includeLeftRingHom.comp (transition_aux hr i j) := by
  rw [transition'₁RingHom, IsLocalization.Away.AwayMap.lift_comp]

lemma transition'₁_F' (i j k : Basis (Fin (finrank K V)) K V) :
    (matrix_F' hr j k).map (transition'₁ hr i j k) =
    (matrix_F''ik hr i j k) * (matrix_F''ij hr i j k)⁻¹ := by
  rw [matrix_F', transition'₁]; erw [← RingHom.mapMatrix_apply]
  conv_lhs => change (transition'₁RingHom hr i j k).mapMatrix
                ((algebraMap (functions_chart K V r) _).mapMatrix (matrix_F hr j k))
              rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_map]
              rw [← RingHom.coe_comp]
              rw [transition'₁_algebraMap, RingHom.coe_comp, ← Matrix.map_map]
              erw [transition_aux_F]
              rw [RingHom.map_matrix_mul']
              congr; rw [Matrix.map_map]; erw [← RingHom.coe_comp]
              rw [← Algebra.TensorProduct.algebraMap]; rfl
              erw [← RingHom.mapMatrix_apply]; rw [← matrix_F''ij_inv_eq]
  rfl

lemma transition'₁_F'_inv (i j k : Basis (Fin (finrank K V)) K V) :
    (matrix_F' hr j k)⁻¹.map (transition'₁ hr i j k) =
    (matrix_F''ij hr i j k) * (matrix_F''ik hr i j k)⁻¹ := by
  rw [← AlgHom.mapMatrix_apply, Matrix.nonsing_inv_eq_ring_inverse]
  rw [AlgHom.map_inv (f := (transition'₁ hr i j k).mapMatrix)
    (α := Matrix (Fin r) (Fin r) (Localization.Away (equation hr j k)))
    (β := Matrix (Fin r) (Fin r) (TensorProduct (MvPolynomial (Fin (finrank K V - r) × Fin r) K)
    (Localization.Away (equation hr i j)) (Localization.Away (equation hr i k))))
    (hx := isUnit_F' hr j k)]
  rw [AlgHom.mapMatrix_apply, transition'₁_F', ← Matrix.nonsing_inv_eq_ring_inverse
  ((matrix_F''ik hr i j k * (matrix_F''ij hr i j k)⁻¹))]
  rw [Matrix.mul_inv_rev (matrix_F''ik hr i j k)]
  rw [Matrix.nonsing_inv_nonsing_inv]
  rw [← Matrix.isUnit_iff_isUnit_det]
  exact matrix_F''ij_isUnit hr i j k

lemma transition'₁_G' (i j k : Basis (Fin (finrank K V)) K V) :
    (matrix_G' hr j k).map (transition'₁ hr i j k) =
    (matrix_G''ik hr i j k) * (matrix_F''ij hr i j k)⁻¹ := by
  rw [matrix_G', transition'₁, Matrix.map_map]; erw [← RingHom.coe_comp]
  conv_lhs => change (matrix_G hr j k).map ((transition'₁RingHom hr i j k).comp (algebraMap
                (functions_chart K V r) _))
              rw [transition'₁_algebraMap, RingHom.coe_comp, ← Matrix.map_map]
              erw [transition_aux_G]
              rw [RingHom.map_matrix_mul']
              congr; rw [Matrix.map_map]; erw [← RingHom.coe_comp]
              rw [← Algebra.TensorProduct.algebraMap]; rfl
              erw [← RingHom.mapMatrix_apply]; rw [← matrix_F''ij_inv_eq]


lemma immersion_transition'₁_Spec (i j k : Basis (Fin (finrank K V)) K V) :
    transition'₁_Spec hr i j k ≫ open_immersion hr j k =
    (Limits.pullback.fst ≫ transition_Spec hr i j) ≫ open_immersion hr j i := by
  rw [transition'₁_Spec, transition'₁]
  conv_lhs => congr; congr; rfl; change Spec.map (CommRingCat.ofHom (transition'₁RingHom hr i j k))
  rw [transition'₁RingHom]
  rw [← cancel_epi (f := (pullbackSpecIso (MvPolynomial (Fin (finrank K V - r) × Fin r) K)
    (Localization.Away (equation hr i j)) (Localization.Away (equation hr i k))).inv)]
  rw [← Category.assoc, ← Category.assoc, Iso.inv_hom_id, Category.id_comp, ← Category.assoc]
  rw [← Category.assoc, pullbackSpecIso_inv_fst]
  conv_rhs => rw [Spec.algebraMap, open_immersion, ← Spec.map_comp, ← Spec.map_comp]
  conv_lhs => rw [open_immersion, ← Spec.map_comp]
  apply congrArg Spec.map
  rw [← CommRingCat.ringHom_comp_eq_comp, ← Category.assoc, ← CommRingCat.ringHom_comp_eq_comp]
  conv_rhs => change CommRingCat.ofHom ((transition hr i j).toRingHom.comp (algebraMap _ _)) ≫
    CommRingCat.ofHom (algebraMap _ _)
              rw [← CommRingCat.ringHom_comp_eq_comp]
  rw [transition]
  rw [IsLocalization.Away.AwayMap.lift_comp, IsLocalization.Away.AwayMap.lift_comp]
  rfl

lemma transition'₁_transition (i j k : Basis (Fin (finrank K V)) K V) :
    transition'₁_Spec hr i j k ≫ transition_Spec hr j k ≫ open_immersion hr k j =
    Limits.pullback.snd ≫ transition_Spec hr i k ≫ open_immersion hr k i := by
  rw [transition'₁_Spec]
  rw [← cancel_epi (f := (pullbackSpecIso (MvPolynomial (Fin (finrank K V - r) × Fin r) K)
    (Localization.Away (equation hr i j)) (Localization.Away (equation hr i k))).inv)]
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  conv_rhs => rw [← Category.assoc, pullbackSpecIso_inv_snd, transition_Spec, open_immersion]
              rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ringHom_comp_eq_comp]
              change Spec.map (CommRingCat.ofHom ((transition hr i k).toRingHom.comp
                (algebraMap _ _)) ≫ CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom)
              rw [← CommRingCat.ringHom_comp_eq_comp]
  conv_lhs => rw [open_immersion, ← Spec.map_comp, ← Spec.map_comp, ← Category.assoc,
                ← CommRingCat.ringHom_comp_eq_comp]
              erw [← CommRingCat.ringHom_comp_eq_comp]
  apply congrArg Spec.map
  conv_lhs => congr; rfl; change (transition hr j k).toRingHom.comp (algebraMap _ _)
              rw [transition, IsLocalization.Away.AwayMap.lift_comp]
  rw [IsLocalization.Away.AwayMap.lift_comp]
  rw [← AlgHom.comp_toRingHom]
  conv_rhs => change (Algebra.TensorProduct.includeRight.restrictScalars (R := K)).toRingHom.comp
                (transition_aux hr i k).toRingHom
              erw [← AlgHom.comp_toRingHom (R := K)
                (φ₁ := Algebra.TensorProduct.includeRight.restrictScalars (R := K))
                (φ₂ := transition_aux hr i k)]
  rw [← AlgHom.toRingHom_eq_coe, ← AlgHom.toRingHom_eq_coe]
  apply congrArg (fun (s : functions_chart K V r →ₐ[K]
    TensorProduct (MvPolynomial (Fin (finrank K V - r) × Fin r) K)
    (Localization.Away (equation hr i j)) (Localization.Away (equation hr i k))) ↦ s.toRingHom)
  refine MvPolynomial.algHom_ext (fun pq ↦ ?_)
  suffices h : (matrix_X K V).map ((transition'₁ hr i j k).comp (transition_aux hr j k)) =
      (matrix_X K V).map ((Algebra.TensorProduct.includeRight.restrictScalars (R := K)).comp
      (transition_aux hr i k)) by
    have heq : matrix_X K V pq.1 pq.2 = MvPolynomial.X pq := rfl
    conv_lhs => rw [← heq, ← Matrix.map_apply (f := (transition'₁ hr i j k).comp
                  (transition_aux hr j k)), h]
    simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', AlgHom.coe_mk, RingHom.mapMatrix_apply,
      MvPolynomial.coe_eval₂Hom, map_apply, of_apply, Prod.mk.eta, Function.comp_apply,
      MvPolynomial.eval₂_X, Algebra.TensorProduct.includeRight_apply]
  rw [AlgHom.coe_comp, ← Matrix.map_map, transition_aux_matrix_X]; erw [RingHom.map_matrix_mul']
  erw [transition'₁_G', transition'₁_F'_inv]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (matrix_F''ij hr i j k)⁻¹]
  rw [Matrix.nonsing_inv_mul _
    (by rw [← Matrix.isUnit_iff_isUnit_det]; exact matrix_F''ij_isUnit hr i j k), Matrix.one_mul]
  rw [AlgHom.coe_comp, ← Matrix.map_map, transition_aux_matrix_X]; erw [RingHom.map_matrix_mul']
  have heq : ((AlgHom.restrictScalars K Algebra.TensorProduct.includeRight).toRingHom).toFun ∘
    (algebraMap (MvPolynomial (Fin (finrank K V - r) × Fin r) K) (Localization.Away
    (equation hr i k))) = algebraMap _ (TensorProduct (MvPolynomial
    (Fin (finrank K V - r) × Fin r) K) (Localization.Away (equation hr i j))
    (Localization.Away (equation hr i k))) := by
    ext x
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_restrictScalars, RingHom.toMonoidHom_eq_coe,
      OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_coe,
      Function.comp_apply, AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
  conv_rhs => congr; rw [matrix_G', Matrix.map_map, heq]; change matrix_G''ik hr i j k
  conv_rhs => congr; rfl; erw [← RingHom.mapMatrix_apply]
              change Algebra.TensorProduct.includeRight.toRingHom.mapMatrix (matrix_F' hr i k)⁻¹
              erw [← matrix_F''ik_inv_eq]

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
    refine Limits.pullback.lift (transition'₁_Spec hr i j k)
      (Limits.pullback.fst ≫ transition_Spec hr i j) ?_
    exact immersion_transition'₁_Spec _ _ _ _
  t_fac i j k := by rw [Limits.pullback.lift_snd]
  cocycle i j k := by
    simp only
    rw [← cancel_mono Limits.pullback.snd]
    conv_lhs => rw [Category.assoc, Category.assoc]
                congr; rfl; congr; rfl
                rw [Limits.pullback.lift_snd]
    slice_lhs 2 3 => rw [Limits.pullback.lift_fst]
    rw [← cancel_mono (f := open_immersion hr i k), Category.assoc, Category.assoc]
    rw [transition'₁_transition, Category.id_comp, ← Category.assoc, Limits.pullback.lift_snd]
    slice_lhs 2 3 => rw [transition_transition_Spec]
    rw [Category.id_comp, Limits.pullback.condition]
  f_open _ _ := inferInstance


end Grassmannian

def Grassmannian := (Grassmannian.glueData K V r hr).glued

namespace Grassmannian

def structMorphism : Grassmannian K V r hr ⟶ Spec (CommRingCat.of K) := by
  refine Scheme.GlueData.glueMorphisms (Grassmannian.glueData K V r hr)
    (fun _ ↦ Spec.map (CommRingCat.ofHom (algebraMap _ _))) ?_
  intro i j
  simp only [glueData, open_immersion, transition_Spec]
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  conv_lhs =>  change (algebraMap _ (Localization.Away (equation hr i j))).comp
                 (algebraMap K (functions_chart K V r))
               rw [← IsScalarTower.algebraMap_eq K]
  conv_rhs => congr; change (algebraMap _ (Localization.Away (equation hr j i))).comp
                 (algebraMap K (functions_chart K V r))
              rw [← IsScalarTower.algebraMap_eq K]
  conv_rhs => change (transitionRingHom hr i j).comp (algebraMap K _)
  simp only [CommRingCat.coe_of, transitionRingHom, AlgHom.coe_ringHom_mk, RingHom.mapMatrix_apply]
  conv_rhs => rw [IsScalarTower.algebraMap_eq K (functions_chart K V r), ← RingHom.comp_assoc,
                IsLocalization.Away.AwayMap.lift_comp, AlgHom.comp_algebraMap]
  
end Grassmannian
