/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

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

## TODO
* Functoriality in `X`: this would involve a morphism `X ⟶ X'`, projective
resolutions `R` and `R'` of `X` and `X'`, a lift of `X ⟶ X'` as a morphism
of cochain complexes `R.complex ⟶ R'.complex`; in this context,
we should be able to compute the precomposition of an element
`R.extMk f m hm hf : Ext X' Y n` by `X ⟶ X'`.

-/

@[expose] public section

universe w v u

open CategoryTheory CochainComplex HomComplex Abelian Localization

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
    CohomologyClass.equiv_toSmallShiftedHom_mk, Functor.comp_obj,
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

end CategoryTheory.ProjectiveResolution
