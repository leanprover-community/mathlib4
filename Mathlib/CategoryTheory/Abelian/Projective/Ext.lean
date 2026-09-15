/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import Mathlib.CategoryTheory.Abelian.Projective.Extend

/-!
# Computing `Ext` using a projective resolution

Given a projective resolution `R` of an object `X` in an abelian category `C`,
we provide an API in order to construct elements in `Ext X Y n` in terms
of the complex `R.complex` and to make computations in the `Ext`-group.

-/

@[expose] public section

universe w v u

open CategoryTheory Limits CochainComplex HomComplex Abelian Localization

namespace CategoryTheory.ProjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {X Y : C} (R : ProjectiveResolution X) {n : ℕ}

instance : R.cochainComplex.IsKProjective := isKProjective_of_projective _ 0

/-- If `R` is a projective resolution of `X`, then `Ext X Y n` identifies
to the type of cohomology classes of degree `n` from `R.cochainComplex`
to `(singleFunctor C 0).obj Y`. -/
noncomputable def extEquivCohomologyClass :
    Ext X Y n ≃ CohomologyClass R.cochainComplex ((singleFunctor C 0).obj Y) n :=
  (SmallShiftedHom.precompEquiv.{w} R.π'
    ((by rw [HomologicalComplex.mem_quasiIso_iff]; infer_instance))).trans
      CochainComplex.HomComplex.CohomologyClass.equivOfIsKProjective.{w}.symm

lemma extEquivCohomologyClass_symm_mk_hom [HasDerivedCategory C]
    (x : Cocycle R.cochainComplex ((singleFunctor C 0).obj Y) n) :
    (R.extEquivCohomologyClass.symm (.mk x)).hom =
    (ShiftedHom.mk₀ _ rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫
      inv (DerivedCategory.Q.map R.π'))).comp
        ((ShiftedHom.map (Cocycle.equivHomShift.symm x) DerivedCategory.Q).comp
          (.mk₀ _ rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).inv.app Y))
            (zero_add _)) (add_zero _) := by
  change SmallShiftedHom.equiv _ _ (.comp _ (CohomologyClass.mk x).toSmallShiftedHom _) = _
  simp only [SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_mk₀Inv, isoOfHom, asIso_inv,
    CohomologyClass.equiv_toSmallShiftedHom_mk,
    DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    Iso.refl_inv]
  congr
  exact (ShiftedHom.comp_mk₀_id ..).symm

@[simp]
lemma extEquivCohomologyClass_symm_add
    (x y : CohomologyClass R.cochainComplex ((singleFunctor C 0).obj Y) n) :
    R.extEquivCohomologyClass.symm (x + y) =
      R.extEquivCohomologyClass.symm x + R.extEquivCohomologyClass.symm y := by
  have := HasDerivedCategory.standard C
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨y, rfl⟩ := y.mk_surjective
  ext
  simp [← CohomologyClass.mk_add, extEquivCohomologyClass_symm_mk_hom, ShiftedHom.map]

/-- If `R` is a projective resolution of `X`, then `Ext X Y n` identifies
to the type of cohomology classes of degree `n` from `R.cochainComplex`
to `(singleFunctor C 0).obj Y`. -/
@[simps!]
noncomputable def extAddEquivCohomologyClass :
    Ext X Y n ≃+ CohomologyClass R.cochainComplex ((singleFunctor C 0).obj Y) n :=
  AddEquiv.symm
    { toEquiv := R.extEquivCohomologyClass.symm
      map_add' := by simp }

@[simp]
lemma extEquivCohomologyClass_symm_sub
    (x y : CohomologyClass R.cochainComplex ((singleFunctor C 0).obj Y) n) :
    R.extEquivCohomologyClass.symm (x - y) =
      R.extEquivCohomologyClass.symm x - R.extEquivCohomologyClass.symm y :=
  R.extAddEquivCohomologyClass.symm.map_sub _ _

@[simp]
lemma extEquivCohomologyClass_symm_neg
    (x : CohomologyClass R.cochainComplex ((singleFunctor C 0).obj Y) n) :
    R.extEquivCohomologyClass.symm (-x) =
      -R.extEquivCohomologyClass.symm x :=
  R.extAddEquivCohomologyClass.symm.map_neg _

@[simp]
lemma extEquivCohomologyClass_symm_zero :
    (R.extEquivCohomologyClass (Y := Y) (n := n)).symm 0 = 0 :=
  R.extAddEquivCohomologyClass.symm.map_zero

@[simp]
lemma extEquivCohomologyClass_add (x y : Ext X Y n) :
    R.extEquivCohomologyClass (x + y) =
      R.extEquivCohomologyClass x + R.extEquivCohomologyClass y :=
  R.extAddEquivCohomologyClass.map_add _ _

@[simp]
lemma extEquivCohomologyClass_sub (x y : Ext X Y n) :
    R.extEquivCohomologyClass (x - y) =
      R.extEquivCohomologyClass x - R.extEquivCohomologyClass y :=
  R.extAddEquivCohomologyClass.map_sub _ _

@[simp]
lemma extEquivCohomologyClass_neg (x : Ext X Y n) :
    R.extEquivCohomologyClass (-x) =
      -R.extEquivCohomologyClass x :=
  R.extAddEquivCohomologyClass.map_neg _

variable (X n) in
@[simp]
lemma extEquivCohomologyClass_zero :
    R.extEquivCohomologyClass (0 : Ext X Y n) = 0 :=
  R.extAddEquivCohomologyClass.map_zero

/-- Given a projective resolution `R` of an object `X` of an abelian category,
this is a constructor for elements in `Ext X Y n` which takes as an input
a "cocycle" `f : R.cocomplex.X n ⟶ Y`. -/
noncomputable def extMk {n : ℕ} (f : R.complex.X n ⟶ Y) (m : ℕ) (hm : n + 1 = m)
    (hf : R.complex.d m n ≫ f = 0) :
    Ext X Y n :=
  R.extEquivCohomologyClass.symm
    (.mk (Cocycle.toSingleMk ((R.cochainComplexXIso (-n) n rfl).hom ≫ f) (by simp)
      (-m) (by lia) (by simpa [cochainComplex_d _ _ _ m n rfl rfl])))

@[simp]
lemma extEquivCohomologyClass_extMk {n : ℕ} (f : R.complex.X n ⟶ Y) (m : ℕ) (hm : n + 1 = m)
    (hf : R.complex.d m n ≫ f = 0) :
    R.extEquivCohomologyClass (R.extMk f m hm hf) =
      (.mk (Cocycle.toSingleMk ((R.cochainComplexXIso (-n) n rfl).hom ≫ f) (by simp)
        (-m) (by lia) (by simpa [cochainComplex_d _ _ _ m n rfl rfl]))) := by
  simp [extMk]

lemma add_extMk {n : ℕ} (f g : R.complex.X n ⟶ Y) (m : ℕ) (hm : n + 1 = m)
    (hf : R.complex.d m n ≫ f = 0) (hg : R.complex.d m n ≫ g = 0) :
    R.extMk f m hm hf + R.extMk g m hm hg =
      R.extMk (f + g) m hm (by simp [hf, hg]) := by
  simp only [extMk, Preadditive.comp_add]
  rw [Cocycle.toSingleMk_add _ _ _ _ _
    (by simpa [cochainComplex_d _ _ _ m n rfl rfl])
    (by simpa [cochainComplex_d _ _ _ m n rfl rfl])]
  simp

lemma sub_extMk {n : ℕ} (f g : R.complex.X n ⟶ Y) (m : ℕ) (hm : n + 1 = m)
    (hf : R.complex.d m n ≫ f = 0) (hg : R.complex.d m n ≫ g = 0) :
    R.extMk f m hm hf - R.extMk g m hm hg =
      R.extMk (f - g) m hm (by simp [hf, hg]) := by
  simp only [extMk, Preadditive.comp_sub]
  rw [Cocycle.toSingleMk_sub _ _ _ _ _
    (by simpa [cochainComplex_d _ _ _ m n rfl rfl])
    (by simpa [cochainComplex_d _ _ _ m n rfl rfl])]
  simp

lemma neg_extMk {n : ℕ} (f : R.complex.X n ⟶ Y) (m : ℕ) (hm : n + 1 = m)
    (hf : R.complex.d m n ≫ f = 0) :
    -R.extMk f m hm hf =
      R.extMk (-f) m hm (by simp [hf]) := by
  simp only [extMk, Preadditive.comp_neg]
  rw [Cocycle.toSingleMk_neg _ _ _ _
    (by simpa [cochainComplex_d _ _ _ m n rfl rfl])]
  simp

@[simp]
lemma extMk_zero {n : ℕ} (m : ℕ) (hm : n + 1 = m) :
    R.extMk (0 : R.complex.X n ⟶ Y) m hm (by simp) = 0 := by
  simp [extMk]

lemma extMk_hom
    [HasDerivedCategory C] {n : ℕ} (f : R.complex.X n ⟶ Y) (m : ℕ) (hm : n + 1 = m)
    (hf : R.complex.d m n ≫ f = 0) :
    (R.extMk f m hm hf).hom =
    (ShiftedHom.mk₀ _ rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫
      inv (DerivedCategory.Q.map R.π'))).comp
        ((ShiftedHom.map (Cocycle.equivHomShift.symm
          (Cocycle.toSingleMk ((R.cochainComplexXIso (-n) n rfl).hom ≫ f) (by simp) (-m)
            (by lia) (by simpa [cochainComplex_d _ _ _ _ _ rfl rfl]))) _).comp
              (.mk₀ _ rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).inv.app Y))
                (zero_add _)) (add_zero _) :=
  extEquivCohomologyClass_symm_mk_hom _ _

lemma extMk_eq_zero_iff (f : R.complex.X n ⟶ Y) (m : ℕ) (hm : n + 1 = m)
    (hf : R.complex.d m n ≫ f = 0)
    (p : ℕ) (hp : p + 1 = n) :
    R.extMk f m hm hf = 0 ↔
      ∃ (g : R.complex.X p ⟶ Y), R.complex.d n p ≫ g = f := by
  simp only [← R.extEquivCohomologyClass.apply_eq_iff_eq,
    extEquivCohomologyClass_extMk, extEquivCohomologyClass_zero,
    CohomologyClass.mk_eq_zero_iff]
  rw [Cocycle.toSingleMk_mem_coboundaries_iff _ _ _ _ _ (-p) (by lia),
    R.cochainComplex_d _ _ _ _ rfl rfl]
  refine ⟨fun ⟨g, hg⟩ ↦ ⟨(R.cochainComplexXIso (-p) p rfl).inv ≫ g, ?_⟩,
    fun ⟨g, hg⟩ ↦ ⟨(R.cochainComplexXIso (-p) p rfl).hom ≫ g, by simpa⟩⟩
  rw [← cancel_epi (R.cochainComplexXIso (-n) n rfl).hom]
  simpa [Category.assoc] using hg

lemma extMk_surjective (α : Ext X Y n) (m : ℕ) (hm : n + 1 = m) :
    ∃ (f : R.complex.X n ⟶ Y) (hf : R.complex.d m n ≫ f = 0),
      R.extMk f m hm hf = α := by
  obtain ⟨x, rfl⟩ := R.extEquivCohomologyClass.symm.surjective α
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨f, hf, rfl⟩ := Cocycle.toSingleMk_surjective x (-n) (by simp) (-m) (by lia)
  refine ⟨(R.cochainComplexXIso (-n) n rfl).inv ≫ f, ?_, by simp [extMk]⟩
  rw [← cancel_epi (R.cochainComplexXIso (-m) m rfl).hom]
  simpa [R.cochainComplex_d _ _ _ _ rfl rfl] using hf

lemma extMk_comp_mk₀ {n : ℕ} (f : R.complex.X n ⟶ Y) (m : ℕ) (hm : n + 1 = m)
    (hf : R.complex.d m n ≫ f = 0) {Y' : C} (g : Y ⟶ Y') :
    (R.extMk f m hm hf).comp (Ext.mk₀ g) (add_zero _) =
      R.extMk (f ≫ g) m hm (by simp [reassoc_of% hf]) := by
  have := HasDerivedCategory.standard C
  ext
  simp only [extMk, Ext.comp_hom, Int.cast_ofNat_Int, Ext.mk₀_hom,
    extEquivCohomologyClass_symm_mk_hom]
  simp only [← Category.assoc]
  rw [Cocycle.toSingleMk_postcomp _ _ _ _
      (by simpa [cochainComplex_d _ _ _ m n rfl rfl]) g,
    Cocycle.equivHomShift_symm_postcomp,
    ← ShiftedHom.comp_mk₀ _ 0 rfl,
    ShiftedHom.map_comp, ShiftedHom.map_mk₀,
    ShiftedHom.comp_assoc _ _ _ (add_zero _) (zero_add _) (by simp),
    ShiftedHom.comp_assoc _ _ _ (zero_add _) (zero_add _) (by simp),
    ShiftedHom.comp_assoc _ _ _ (zero_add _) (zero_add _) (by simp),
    ShiftedHom.mk₀_comp_mk₀, ShiftedHom.mk₀_comp_mk₀, ← NatTrans.naturality]
  dsimp

variable {R} in
lemma mk₀_comp_extMk {n : ℕ} (f : R.complex.X n ⟶ Y) (m : ℕ) (hm : n + 1 = m)
    (hf : R.complex.d m n ≫ f = 0)
    {X' : C} {R' : ProjectiveResolution X'} {g : X' ⟶ X} (φ : Hom R' R g) :
    (Ext.mk₀ g).comp (R.extMk f m hm hf) (zero_add _) =
      R'.extMk (φ.hom.f n ≫ f) m hm (by simp [← φ.hom.comm_assoc, hf]) := by
  have := HasDerivedCategory.standard C
  ext
  have : (R'.cochainComplexXIso (-n) n (by lia)).hom ≫ φ.hom.f n =
      φ.hom'.f (-n) ≫ (R.cochainComplexXIso (-n) n (by lia)).hom := by
    simp [φ.hom'_f _ _ rfl]
  simp only [Ext.comp_hom, extMk_hom, Ext.mk₀_hom, reassoc_of% this]
  rw [Cocycle.toSingleMk_precomp _ _ _ (by lia)
    (by simpa [R.cochainComplex_d _ _ _ _ rfl rfl]),
    Cocycle.equivHomShift_symm_precomp,
    ← ShiftedHom.mk₀_comp 0 rfl, ShiftedHom.map_comp,
    ← ShiftedHom.comp_assoc _ _ _ (zero_add _) _ (by simp),
    ← ShiftedHom.comp_assoc _ _ _ (add_zero _) _ (by simp),
    ← ShiftedHom.comp_assoc _ _ _ (add_zero _) _ (by simp),
    ← ShiftedHom.comp_assoc _ _ _ (zero_add _) _ (by simp),
    ShiftedHom.map_mk₀, ShiftedHom.mk₀_comp_mk₀, ShiftedHom.mk₀_comp_mk₀]
  congr 3
  simp [← Functor.map_comp_assoc, ← Functor.map_comp]

-- The `(-1) ^ m` can be explained by the fact that in the complex of morphisms
-- `HomComplex R.cochainComplex ((singleFunctor C 0).obj S.X₂)`
-- there is a sign `(-1) ^ m` in the differential `d n m`:
-- the computation here is consistent with the snake lemma applied to the short exact
-- sequence of cochain complexes of morphisms from `R.cochainComplex`
-- to the single complexes `S.X₁`, `S.X₂` and `S.X₃`, see [conrad2000], p. 13
open CochainComplex.HomComplex in
lemma extMk_comp_extClass'
    {S : ShortComplex C} (hS : S.ShortExact) (f₃ : R.complex.X n ⟶ S.X₃)
    (m : ℕ) (hm : n + 1 = m)
    (f₂ : R.complex.X n ⟶ S.X₂) (hf₂ : f₂ ≫ S.g = f₃)
    (f₁ : R.complex.X m ⟶ S.X₁) (hf₁ : Int.negOnePow m • f₁ ≫ S.f = R.complex.d m n ≫ f₂)
    (m' : ℕ) (hm' : m + 1 = m') :
    (R.extMk f₃ m hm (by simp [← hf₂, ← reassoc_of% hf₁])).comp hS.extClass hm =
    R.extMk f₁ m' hm' (by
      have := hS.mono_f
      rw [← smul_left_cancel_iff (Int.negOnePow m), smul_smul,
        Int.units_mul_self, one_smul] at hf₁
      simp [← cancel_mono S.f, hf₁]) := by
  have := HasDerivedCategory.standard C
  rw [← smul_left_cancel_iff (Int.negOnePow m), smul_smul,
    Int.units_mul_self, one_smul] at hf₁
  ext
  simp only [Ext.comp_hom, extMk_hom, DerivedCategory.singleFunctorIsoCompQ_hom_app,
    Category.id_comp, DerivedCategory.singleFunctorIsoCompQ_inv_app,
    ShortComplex.ShortExact.extClass_hom, ← DerivedCategory.Q_obj_single_obj,
    ShiftedHom.comp_mk₀_id]
  rw [ShiftedHom.comp_assoc (a₂₃ := (m : ℤ)) _ _ _ (by lia) (by lia) (by lia)]
  congr 1
  have := CochainComplex.mappingCocone.quasiIso_liftShortComplex
    (hS.map_of_exact (HomologicalComplex.single C (.up ℤ) 0))
  refine (ShiftedHom.postcompIsoEquiv
    (asIso (DerivedCategory.Q.map (CochainComplex.mappingCocone.liftShortComplex
    ((S.map (HomologicalComplex.single C _ 0))))))).injective ?_
  dsimp
  rw [ShiftedHom.comp_assoc _ _ _  (by lia) (zero_add 1) (by lia),
    ShiftedHom.comp_mk₀, ShortComplex.ShortExact.singleδ_liftShortComplex,
    ← ShiftedHom.map, ← ShiftedHom.map_comp, ← ShiftedHom.map_mk₀, ← ShiftedHom.map_comp,
    Cocycle.equivHomShift_symm_shiftedHomComp, Cocycle.equivHomShift_symm_shiftedHomComp,
    ← CohomologyClass.toShiftedHom_mk, ← CohomologyClass.toShiftedHom_mk]
  congr 1
  symm
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ n (by lia)]
  refine ⟨((Cochain.toSingleEquiv (neg_add_cancel _)).symm
    ((R.cochainComplexXIso (-n) n (by lia)).hom ≫ f₂)).comp (mappingCocone.inl _) (by lia), ?_⟩
  dsimp
  simp only [Cocycle.comp_coe, Cocycle.toSingleMk_coe]
  ext p q hpq
  by_cases! hq : q = 0 ∨ q = 1
  · obtain rfl | rfl := hq
    · simp [mappingCocone.ext_to_iff _ _ _ (zero_add (-1)),
        δ_v n m (by lia) _ p 0 hpq (-1) (p + 1) (by lia) (by lia),
        Cochain.toSingleEquiv_symm_apply,
        Cochain.toSingleMk_v_eq_zero _ _ _ _ _ (show p ≠ -n by lia),
        Cochain.comp_v (n₁ := n) (n₂ := 1) (n₁₂ := m) _ _ (by lia) p (-1) 0 (by lia) (by lia),
        Cocycle.equivHomShift_apply, R.cochainComplex_d p (p + 1) m n,
        Cochain.rightUnshift_v _ _ (zero_add 0) _ _ (zero_add 0) _ (zero_add 0),
        ShiftedHom.mk₀, shiftFunctorZero'_eq_shiftFunctorZero, shiftFunctorZero_inv_app_f,
        dsimp% mappingCocone.liftShortComplex_f_fst_f
          (S.map (HomologicalComplex.single C (ComplexShape.up ℤ) 0)) 0,
        dsimp% mappingCocone.liftShortComplex_f_snd_v
          (S.map (HomologicalComplex.single C (ComplexShape.up ℤ) 0)) 0 (-1) (by lia),
        Cochain.toSingleMk_v' _ (neg_add_cancel (n : ℤ)) (p + 1) 0 (by lia) (by lia),
        Cochain.toSingleMk_v' _ (neg_add_cancel (m : ℤ)) p 0 (by lia) (by lia),
        HomologicalComplex.single_map_f_self, HomologicalComplex.singleObjXSelf,
        reassoc_of% hf₁]
    · simp [mappingCocone.ext_to_iff _ _ _ (add_neg_cancel 1),
        δ_v n m (by lia) _ p 1 hpq 0 (p + 1) (by lia) (by lia),
        Cochain.toSingleEquiv_symm_apply,
        Cochain.toSingleMk_v_eq_zero _ _ _ _ _ (show p ≠ -m by lia),
        Cochain.comp_v (n₁ := n) (n₂ := 1) (n₁₂ := m) _ _ (by lia) p 0 1 (by lia) (by lia),
        Cocycle.equivHomShift_apply,
        Cochain.toSingleMk_v_eq_zero _ _ _ _ _ (show p + 1 ≠ -n by lia),
        Cochain.rightUnshift_v _ _ (zero_add 1) 0 1 (by lia) _ (zero_add 0),
        mappingCocone.inl_v_d_assoc _ _ _ (zero_add 1),
        dsimp% mappingCocone.triangleδ_f_fst_f _ 0,
        dsimp% mappingCocone.triangleδ_f_snd_v _ 0, ← hf₂,
        HomologicalComplex.single_map_f_self,
        Cochain.toSingleMk_v' _ (neg_add_cancel (n : ℤ)) p 0 (by lia) (by lia),
        HomologicalComplex.singleObjXSelf]
  · apply IsZero.eq_of_tgt
    rw [mappingCocone.isZero_X_iff _ q (q - 1) (by lia)]
    constructor
    all_goals exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia)

end CategoryTheory.ProjectiveResolution
