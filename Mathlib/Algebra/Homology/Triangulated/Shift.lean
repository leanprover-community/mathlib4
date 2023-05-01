import Mathlib.Algebra.Homology.Triangulated.HomComplex
import Mathlib.CategoryTheory.Shift.Induced

open CategoryTheory Category Limits

variable (C D : Type _) [Category C] [Preadditive C] [Category D] [Preadditive D]

namespace CochainComplex

open HomologicalComplex

attribute [local simp] Preadditive.comp_zsmul Preadditive.zsmul_comp
attribute [local simp] XIsoOfEq_hom_naturality

@[simps]
def shiftFunctor (n : ℤ) : CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj K :=
    { X := fun i => K.X (i + n)
      d := fun i j => CochainComplex.HomComplex.ε n • K.d _ _
      d_comp_d' := by
        intros
        simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp, d_comp_d, smul_zero]
      shape := fun i j hij => by
        dsimp
        rw [K.shape, smul_zero]
        intro hij'
        apply hij
        dsimp at hij' ⊢
        linarith }
  map φ :=
    { f := fun i => φ.f _
      comm' := by
        intros
        dsimp
        simp only [Preadditive.comp_zsmul, Hom.comm, Preadditive.zsmul_comp] }
  map_id := by intros ; rfl
  map_comp := by intros ; rfl

variable {C}

@[simp]
def shiftFunctorObjXIso (K : CochainComplex C ℤ) (n i m : ℤ) (hm : m = i + n) :
    ((shiftFunctor C n).obj K).X i ≅ K.X m := K.XIsoOfEq hm.symm

variable (C)

@[simp]
def shiftFunctorCongr {n n' : ℤ} (h : n = n') :
    shiftFunctor C n ≅ shiftFunctor C n' :=
  NatIso.ofComponents (fun K => Hom.isoOfComponents (fun i => K.XIsoOfEq (by subst h ; rfl))
    (fun _ _ _ => by simp [h])) (by aesop_cat)

@[simps!]
def shiftFunctorZero' (n : ℤ) (h : n = 0) :
    shiftFunctor C n ≅ 𝟭 _ :=
  NatIso.ofComponents (fun K => Hom.isoOfComponents
    (fun i => K.shiftFunctorObjXIso _ _ _ (by linarith))
    (fun _ _ _ => by simp [h])) (by aesop_cat)

@[simps!]
def shiftFunctorAdd' (n₁ n₂ n₁₂ : ℤ) (h : n₁ + n₂ = n₁₂ ) :
    shiftFunctor C n₁₂ ≅ shiftFunctor C n₁ ⋙ shiftFunctor C n₂ :=
  NatIso.ofComponents (fun K => Hom.isoOfComponents
    (fun i => K.shiftFunctorObjXIso _ _ _ (by linarith))
    (fun _ _ _ => by
      subst h
      dsimp
      simp only [add_comm n₁ n₂, HomComplex.ε_add, Preadditive.comp_zsmul,
        XIsoOfEq_hom_comp_d, smul_smul, Preadditive.zsmul_comp, d_comp_XIsoOfEq_hom]))
    (by aesop_cat)

attribute [local simp] XIsoOfEq

instance : HasShift (CochainComplex C ℤ) ℤ := hasShiftMk _ _
  { F := shiftFunctor C
    zero := shiftFunctorZero' C _ rfl
    add := fun n₁ n₂ => shiftFunctorAdd' C n₁ n₂ _ rfl }

variable {C}

@[simp]
lemma shiftFunctor_map_f' {K L : CochainComplex C ℤ} (φ : K ⟶ L) (n p : ℤ) :
    ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) n).map φ).f p = φ.f (p+n) := rfl

@[simp]
lemma shiftFunctor_obj_d' (K : CochainComplex C ℤ) (n i j : ℤ) :
    ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) n).obj K).d i j =
      HomComplex.ε n • K.d _ _ := rfl

lemma shiftFunctorAdd_inv_app_f (K : CochainComplex C ℤ) (a b n : ℤ) :
  ((shiftFunctorAdd (CochainComplex C ℤ) a b).inv.app K).f n =
    (K.XIsoOfEq (by dsimp ; rw [add_comm a, add_assoc])).hom := rfl

lemma shiftFunctorAdd_hom_app_f (K : CochainComplex C ℤ) (a b n : ℤ) :
  ((shiftFunctorAdd (CochainComplex C ℤ) a b).hom.app K).f n =
    (K.XIsoOfEq (by dsimp ; rw [add_comm a, add_assoc])).hom := by
  have : IsIso (((shiftFunctorAdd (CochainComplex C ℤ) a b).inv.app K).f n) := by
    rw [shiftFunctorAdd_inv_app_f]
    infer_instance
  rw [← cancel_mono (((shiftFunctorAdd (CochainComplex C ℤ) a b).inv.app K).f n),
    ← comp_f, Iso.hom_inv_id_app, id_f, shiftFunctorAdd_inv_app_f]
  simp only [XIsoOfEq, eqToIso.hom, eqToHom_trans, eqToHom_refl]

lemma shiftFunctorAdd'_inv_app_f' (K : CochainComplex C ℤ) (a b ab : ℤ) (h : a + b = ab) (n : ℤ) :
  ((CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) a b ab h).inv.app K).f n =
    (K.XIsoOfEq (by dsimp ; rw [← h, add_assoc, add_comm a])).hom := by
  subst h
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd, shiftFunctorAdd_inv_app_f]

lemma shiftFunctorAdd'_hom_app_f' (K : CochainComplex C ℤ) (a b ab : ℤ) (h : a + b = ab) (n : ℤ) :
  ((CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) a b ab h).hom.app K).f n =
    (K.XIsoOfEq (by dsimp ; rw [← h, add_assoc, add_comm a])).hom := by
  subst h
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd, shiftFunctorAdd_hom_app_f]

lemma shiftFunctorZero_inv_app_f (K : CochainComplex C ℤ) (n : ℤ) :
  ((CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ).inv.app K).f n =
    (K.XIsoOfEq (by dsimp ; rw [add_zero])).hom := rfl

lemma shiftFunctorZero_hom_app_f (K : CochainComplex C ℤ) (n : ℤ) :
  ((CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app K).f n =
    (K.XIsoOfEq (by dsimp ; rw [add_zero])).hom := by
  have : IsIso (((shiftFunctorZero (CochainComplex C ℤ) ℤ).inv.app K).f n) := by
    rw [shiftFunctorZero_inv_app_f]
    infer_instance
  rw [← cancel_mono (((shiftFunctorZero (CochainComplex C ℤ) ℤ).inv.app K).f n), ← comp_f,
    Iso.hom_inv_id_app, id_f, shiftFunctorZero_inv_app_f]
  simp only [XIsoOfEq, eqToIso.hom, eqToHom_trans, eqToHom_refl]

variable (C)

lemma shiftFunctorAdd'_eq (a b c : ℤ) (h : a + b = c) :
    CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) a b c h =
      shiftFunctorAdd' C a b c h := by
  ext
  simp only [shiftFunctorAdd'_hom_app_f', XIsoOfEq, eqToIso.hom, shiftFunctorAdd'_hom_app_f]

lemma shiftFunctorAdd_eq (a b : ℤ) :
    CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) a b = shiftFunctorAdd' C a b _ rfl := by
  rw [← CategoryTheory.shiftFunctorAdd'_eq_shiftFunctorAdd, shiftFunctorAdd'_eq]

lemma shiftFunctorZero_eq :
    CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ = shiftFunctorZero' C 0 rfl := by
  ext
  rw [shiftFunctorZero_hom_app_f, shiftFunctorZero'_hom_app_f]

end CochainComplex

namespace CategoryTheory

namespace Functor

variable {C D}
variable (F : C ⥤ D) [Preadditive D] [F.Additive]

attribute [local simp] Functor.map_zsmul HomologicalComplex.XIsoOfEq --eqToHom_map
--  CochainComplex.shiftFunctorZero_hom_app_f
--  CochainComplex.shiftFunctorZero_inv_app_f

def mapCochainComplexShiftIso (n : ℤ) :
    shiftFunctor _ n ⋙ F.mapHomologicalComplex (ComplexShape.up ℤ) ≅
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ shiftFunctor _ n :=
  NatIso.ofComponents (fun K => HomologicalComplex.Hom.isoOfComponents (fun i => Iso.refl _)
    (by aesop_cat)) (fun _ => by ext ; dsimp ; rw [id_comp, comp_id])

@[simp]
lemma mapCochainComplexShiftIso_hom_app_f (K : CochainComplex C ℤ) (i : ℤ) :
    ((F.mapCochainComplexShiftIso n).hom.app K).f i = 𝟙 _ := rfl

@[simp]
lemma mapCochainComplexShiftIso_inv_app_f (K : CochainComplex C ℤ) (i : ℤ) :
    ((F.mapCochainComplexShiftIso n).inv.app K).f i = 𝟙 _ := rfl

instance hasCommShiftMapCochainComplex :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).HasCommShift ℤ :=
  ⟨{  iso := F.mapCochainComplexShiftIso
      zero := by
        ext
        rw [CommShift.iso_zero_hom_app]
        dsimp
        simp only [mapCochainComplexShiftIso_hom_app_f, CochainComplex.shiftFunctorZero_inv_app_f,
           CochainComplex.shiftFunctorZero_hom_app_f, HomologicalComplex.XIsoOfEq, eqToIso,
           eqToHom_map, eqToHom_trans, eqToHom_refl]
      add := fun a b => by
        ext
        rw [CommShift.iso_add_hom_app]
        dsimp
        erw [id_comp, id_comp]
        simp only [CochainComplex.shiftFunctorAdd_hom_app_f,
          CochainComplex.shiftFunctorAdd_inv_app_f, HomologicalComplex.XIsoOfEq, eqToIso,
          eqToHom_map, eqToHom_trans, eqToHom_refl] }⟩

lemma mapHomologicalComplex_commShiftIso_eq (n : ℤ) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n =
      F.mapCochainComplexShiftIso n := rfl

@[simp]
lemma mapHomologicalComplex_commShiftIso_hom_app_f (K : CochainComplex C ℤ) (n : ℤ) :
    (((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).hom.app K).f n = 𝟙 _ := rfl

@[simp]
lemma mapHomologicalComplex_commShiftIso_inv_app_f (K : CochainComplex C ℤ) (n : ℤ) :
    (((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).inv.app K).f n = 𝟙 _ := rfl

end Functor

end CategoryTheory
