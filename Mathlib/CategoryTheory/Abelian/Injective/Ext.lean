/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.Injective.Extend

/-!
# Computing `Ext` using an injective resolution

Given an injective resolution `R` of an object `Y` in an abelian category `C`,
we provide an API in order to construct elements in `Ext X Y n` in terms
of the complex `R.cocomplex` and to make computations in the `Ext`-group.

-/

@[expose] public section

universe w v u

open CategoryTheory CochainComplex HomComplex Abelian Localization

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {X Y : C} (R : InjectiveResolution Y) {n : ℕ}

instance : R.cochainComplex.IsKInjective := isKInjective_of_injective _ 0

/-- If `R` is an injective resolution of `Y`, then `Ext X Y n` identifies
to the type of cohomology classes of degree `n` from `(singleFunctor C 0).obj X`
to `R.cochainComplex`. -/
noncomputable def extEquivCohomologyClass :
    Ext X Y n ≃ CohomologyClass ((singleFunctor C 0).obj X) R.cochainComplex n :=
  (SmallShiftedHom.postcompEquiv.{w} R.ι'
      (by rw [HomologicalComplex.mem_quasiIso_iff]; infer_instance)).trans
    CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective.{w}.symm

lemma extEquivCohomologyClass_symm_mk_hom [HasDerivedCategory C]
    (x : Cocycle ((singleFunctor C 0).obj X) R.cochainComplex n) :
    (R.extEquivCohomologyClass.symm (.mk x)).hom =
      (ShiftedHom.mk₀ _ rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X)).comp
        ((ShiftedHom.map (Cocycle.equivHomShift.symm x) DerivedCategory.Q).comp
        (.mk₀ _ rfl (inv (DerivedCategory.Q.map R.ι') ≫
          (DerivedCategory.singleFunctorIsoCompQ C 0).inv.app Y)) (zero_add _)) (add_zero _) := by
  change SmallShiftedHom.equiv _ _ ((CohomologyClass.mk x).toSmallShiftedHom.comp _ _) = _
  simp only [SmallShiftedHom.equiv_comp, CohomologyClass.equiv_toSmallShiftedHom_mk,
    SmallShiftedHom.equiv_mk₀Inv, isoOfHom, asIso_inv, Functor.comp_obj,
    DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, NatTrans.id_app, Iso.refl_inv,
    ShiftedHom.mk₀_id_comp]
  congr
  cat_disch

@[simp]
lemma extEquivCohomologyClass_symm_add
    (x y : CohomologyClass ((singleFunctor C 0).obj X) R.cochainComplex n) :
    R.extEquivCohomologyClass.symm (x + y) =
      R.extEquivCohomologyClass.symm x + R.extEquivCohomologyClass.symm y := by
  have := HasDerivedCategory.standard C
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨y, rfl⟩ := y.mk_surjective
  ext
  simp [← CohomologyClass.mk_add, extEquivCohomologyClass_symm_mk_hom, ShiftedHom.map]

/-- If `R` is an injective resolution of `Y`, then `Ext X Y n` identifies
to the group of cohomology classes of degree `n` from `(singleFunctor C 0).obj X`
to `R.cochainComplex`. -/
@[simps!]
noncomputable def extAddEquivCohomologyClass :
    Ext X Y n ≃+ CohomologyClass ((singleFunctor C 0).obj X) R.cochainComplex n :=
  AddEquiv.symm
    { toEquiv := (R.extEquivCohomologyClass (X := X) (Y := Y) (n := n)).symm
      map_add' := by simp }

@[simp]
lemma extEquivCohomologyClass_symm_sub
    (x y : CohomologyClass ((singleFunctor C 0).obj X) R.cochainComplex n) :
    R.extEquivCohomologyClass.symm (x - y) =
      R.extEquivCohomologyClass.symm x - R.extEquivCohomologyClass.symm y :=
  R.extAddEquivCohomologyClass.symm.map_sub _ _

@[simp]
lemma extEquivCohomologyClass_symm_neg
    (x : CohomologyClass ((singleFunctor C 0).obj X) R.cochainComplex n) :
    R.extEquivCohomologyClass.symm (-x) =
      -R.extEquivCohomologyClass.symm x :=
  R.extAddEquivCohomologyClass.symm.map_neg _

@[simp]
lemma extEquivCohomologyClass_symm_zero :
    (R.extEquivCohomologyClass (X := X) (n := n)).symm 0 = 0 :=
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

/-- Given an injective resolution `R` of an object `Y` of an abelian category,
this is a constructor for elements in `Ext X Y n` which takes as an input
a "cocycle" `f : X ⟶ R.cocomplex.X n`. -/
noncomputable def extMk {n : ℕ} (f : X ⟶ R.cocomplex.X n) (m : ℕ) (hm : n + 1 = m)
    (hf : f ≫ R.cocomplex.d n m = 0) :
    Ext X Y n :=
  R.extEquivCohomologyClass.symm
    (.mk (Cocycle.fromSingleMk (f ≫ (R.cochainComplexXIso n n rfl).inv) (zero_add _)
      m (by lia) (by simp [cochainComplex_d _ _ _ n m rfl rfl, reassoc_of% hf])))

@[simp]
lemma extEquivCohomologyClass_extMk {n : ℕ} (f : X ⟶ R.cocomplex.X n) (m : ℕ) (hm : n + 1 = m)
    (hf : f ≫ R.cocomplex.d n m = 0) :
    R.extEquivCohomologyClass (R.extMk f m hm hf) =
      (.mk (Cocycle.fromSingleMk (f ≫ (R.cochainComplexXIso n n rfl).inv) (zero_add _)
        m (by lia) (by simp [cochainComplex_d _ _ _ n m rfl rfl, reassoc_of% hf]))) := by
  simp [extMk]

lemma add_extMk {n : ℕ} (f g : X ⟶ R.cocomplex.X n) (m : ℕ) (hm : n + 1 = m)
    (hf : f ≫ R.cocomplex.d n m = 0) (hg : g ≫ R.cocomplex.d n m = 0) :
    R.extMk f m hm hf + R.extMk g m hm hg =
      R.extMk (f + g) m hm (by simp [hf, hg]) := by
  simp only [extMk, Preadditive.add_comp]
  rw [Cocycle.fromSingleMk_add _ _ _ _ _
    (by simp [cochainComplex_d _ _ _ n m rfl rfl, reassoc_of% hf])
    (by simp [cochainComplex_d _ _ _ n m rfl rfl, reassoc_of% hg])]
  simp

lemma sub_extMk {n : ℕ} (f g : X ⟶ R.cocomplex.X n) (m : ℕ) (hm : n + 1 = m)
    (hf : f ≫ R.cocomplex.d n m = 0) (hg : g ≫ R.cocomplex.d n m = 0) :
    R.extMk f m hm hf - R.extMk g m hm hg =
      R.extMk (f - g) m hm (by simp [hf, hg]) := by
  dsimp [extMk]
  simp only [Preadditive.sub_comp]
  rw [Cocycle.fromSingleMk_sub _ _ _ _ _
    (by simp [cochainComplex_d _ _ _ n m rfl rfl, reassoc_of% hf])
    (by simp [cochainComplex_d _ _ _ n m rfl rfl, reassoc_of% hg])]
  simp

lemma neg_extMk {n : ℕ} (f : X ⟶ R.cocomplex.X n) (m : ℕ) (hm : n + 1 = m)
    (hf : f ≫ R.cocomplex.d n m = 0) :
    -R.extMk f m hm hf = R.extMk (-f) m hm (by simp [hf]) := by
  dsimp [extMk]
  simp only [Preadditive.neg_comp]
  rw [Cocycle.fromSingleMk_neg _ _ _ _
    (by simp [cochainComplex_d _ _ _ n m rfl rfl, reassoc_of% hf])]
  simp

@[simp]
lemma extMk_zero {n : ℕ} (m : ℕ) (hm : n + 1 = m) :
    R.extMk (0 : X ⟶ R.cocomplex.X n) m hm (by simp) = 0 := by
  simp [extMk]

lemma extMk_hom
    [HasDerivedCategory C] {n : ℕ} (f : X ⟶ R.cocomplex.X n) (m : ℕ) (hm : n + 1 = m)
    (hf : f ≫ R.cocomplex.d n m = 0) :
    (R.extMk f m hm hf).hom =
    (ShiftedHom.mk₀ _ rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X)).comp
      ((ShiftedHom.map (Cocycle.equivHomShift.symm
        (Cocycle.fromSingleMk (f ≫ (R.cochainComplexXIso n n rfl).inv) (zero_add _) m
          (by lia) (by simp [cochainComplex_d _ _ _ n m rfl rfl, reassoc_of% hf]))) _).comp
            (.mk₀ _ rfl (inv (DerivedCategory.Q.map R.ι') ≫
              (DerivedCategory.singleFunctorIsoCompQ C 0).inv.app Y))
                (zero_add _)) (add_zero _) :=
  extEquivCohomologyClass_symm_mk_hom _ _

lemma extMk_eq_zero_iff (f : X ⟶ R.cocomplex.X n) (m : ℕ) (hm : n + 1 = m)
    (hf : f ≫ R.cocomplex.d n m = 0)
    (p : ℕ) (hp : p + 1 = n) :
    R.extMk f m hm hf = 0 ↔
      ∃ (g : X ⟶ R.cocomplex.X p), g ≫ R.cocomplex.d p n = f := by
  simp only [← R.extEquivCohomologyClass.apply_eq_iff_eq,
    extEquivCohomologyClass_extMk, extEquivCohomologyClass_zero,
    CohomologyClass.mk_eq_zero_iff]
  rw [Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ p (by lia),
    R.cochainComplex_d _ _ _ _ rfl rfl]
  exact ⟨fun ⟨g, hg⟩ ↦ ⟨g ≫ (R.cochainComplexXIso p p rfl).hom,
      by simp only [← cancel_mono (R.cochainComplexXIso n n rfl).inv, Category.assoc, hg]⟩,
    fun ⟨g, hg⟩ ↦ ⟨g ≫ (R.cochainComplexXIso p p rfl).inv, by simp [← hg]⟩⟩

lemma extMk_surjective (α : Ext X Y n) (m : ℕ) (hm : n + 1 = m) :
    ∃ (f : X ⟶ R.cocomplex.X n) (hf : f ≫ R.cocomplex.d n m = 0),
      R.extMk f m hm hf = α := by
  obtain ⟨x, rfl⟩ := R.extEquivCohomologyClass.symm.surjective α
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨f, hf, rfl⟩ := Cocycle.fromSingleMk_surjective x n (by simp) m (by lia)
  exact ⟨f ≫ (R.cochainComplexXIso n n rfl).hom,
    by simpa [R.cochainComplex_d _ _ _ _ rfl rfl,
      ← cancel_mono (R.cochainComplexXIso m m rfl).inv] using hf, by simp [extMk]⟩

lemma mk₀_comp_extMk {n : ℕ} (f : X ⟶ R.cocomplex.X n) (m : ℕ) (hm : n + 1 = m)
    (hf : f ≫ R.cocomplex.d n m = 0) {X' : C} (g : X' ⟶ X) :
    (Ext.mk₀ g).comp (R.extMk f m hm hf) (zero_add _) =
      R.extMk (g ≫ f) m hm (by simp [hf]) := by
  have := HasDerivedCategory.standard C
  ext
  simp only [extMk, Ext.comp_hom, Int.cast_ofNat_Int, Ext.mk₀_hom,
    extEquivCohomologyClass_symm_mk_hom, Category.assoc]
  rw [Cocycle.fromSingleMk_precomp g _ (zero_add _) _ (by lia) (by
      simp [cochainComplex_d _ _ _ n m rfl rfl, reassoc_of% hf]),
    Cocycle.equivHomShift_symm_precomp, ← ShiftedHom.mk₀_comp 0 rfl,
    ShiftedHom.map_comp,
    ShiftedHom.comp_assoc _ _ _ (add_zero _) (zero_add _) (by simp),
    ← ShiftedHom.comp_assoc _ _ _ (add_zero _) (add_zero (n : ℤ)) (by simp)]
  simp

variable {R} in
lemma extMk_comp_mk₀ {n : ℕ} (f : X ⟶ R.cocomplex.X n) (m : ℕ) (hm : n + 1 = m)
    (hf : f ≫ R.cocomplex.d n m = 0)
    {Y' : C} {R' : InjectiveResolution Y'} {g : Y ⟶ Y'} (φ : Hom R R' g) :
    (R.extMk f m hm hf).comp (Ext.mk₀ g) (add_zero _) =
      R'.extMk (f ≫ φ.hom.f n) m hm (by simp [reassoc_of% hf]) := by
  have := HasDerivedCategory.standard C
  ext
  have : (f ≫ φ.hom.f n) ≫ (R'.cochainComplexXIso n n (by lia)).inv =
      (f ≫ (R.cochainComplexXIso n n (by lia)).inv) ≫ φ.hom'.f n := by
    simp [φ.hom'_f n n rfl]
  simp only [Ext.comp_hom, extMk_hom, Ext.mk₀_hom, this]
  rw [Cocycle.fromSingleMk_postcomp _ (zero_add _) _ (by lia)
      (by simp [R.cochainComplex_d _ _ _ _ rfl rfl, reassoc_of% hf]),
    Cocycle.equivHomShift_symm_postcomp,
    ← ShiftedHom.comp_mk₀ _ 0 rfl, ShiftedHom.map_comp,
    ShiftedHom.comp_assoc _ _ _ _ (zero_add _) (by simp),
    ShiftedHom.comp_assoc _ _ _ _ (zero_add _) (by simp),
    ShiftedHom.comp_assoc _ _ _ _ (zero_add _) (by simp),
    ShiftedHom.map_mk₀, ShiftedHom.mk₀_comp_mk₀, ShiftedHom.mk₀_comp_mk₀]
  congr 3
  rw [Category.assoc, ← NatTrans.naturality, ← Category.assoc, ← Category.assoc]
  congr 1
  simpa only [IsIso.eq_comp_inv, Category.assoc, IsIso.inv_comp_eq,
    Functor.map_comp] using DerivedCategory.Q.congr_map φ.ι'_comp_hom'.symm

end CategoryTheory.InjectiveResolution
