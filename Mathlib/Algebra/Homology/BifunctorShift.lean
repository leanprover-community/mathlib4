/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.TotalComplexShift
public import Mathlib.CategoryTheory.Shift.CommShiftTwo

/-!
# Behavior of the action of a bifunctor on cochain complexes with respect to shifts

In this file, given cochain complexes `K₁ : CochainComplex C₁ ℤ`, `K₂ : CochainComplex C₂ ℤ` and
a functor `F : C₁ ⥤ C₂ ⥤ D`, we define an isomorphism of cochain complexes in `D`:
- `CochainComplex.mapBifunctorShift₁Iso K₁ K₂ F x` of type
  `mapBifunctor (K₁⟦x⟧) K₂ F ≅ (mapBifunctor K₁ K₂ F)⟦x⟧` for `x : ℤ`.
- `CochainComplex.mapBifunctorShift₂Iso K₁ K₂ F y` of type
  `mapBifunctor K₁ (K₂⟦y⟧) F ≅ (mapBifunctor K₁ K₂ F)⟦y⟧` for `y : ℤ`.

In the lemma `CochainComplex.mapBifunctorShift₁Iso_trans_mapBifunctorShift₂Iso`, we obtain
that the two ways to deduce an isomorphism
`mapBifunctor (K₁⟦x⟧) (K₂⟦y⟧) F ≅ (mapBifunctor K₁ K₂ F)⟦x + y⟧` differ by the sign
`(x * y).negOnePow`.

These definitions and properties can be summarised by saying that the bifunctor
`F.map₂CochainComplex : CochainComplex C₁ ℤ ⥤ CochainComplex C₂ ℤ ⥤ CochainComplex D ℤ`
commutes with shifts by `ℤ`.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

open CategoryTheory Category Limits HomologicalComplex

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]

namespace CochainComplex

section

variable [HasZeroMorphisms C₁] [HasZeroMorphisms C₂]
  (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ) [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
  [∀ (X₁ : C₁), (F.obj X₁).PreservesZeroMorphisms]

/-- The condition that `((F.mapBifunctorHomologicalComplex _ _).obj K₁).obj K₂` has
a total cochain complex. -/
abbrev HasMapBifunctor := HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)

/-- Given `K₁ : CochainComplex C₁ ℤ`, `K₂ : CochainComplex C₂ ℤ`,
a bifunctor `F : C₁ ⥤ C₂ ⥤ D`, this `mapBifunctor K₁ K₂ F : CochainComplex D ℤ`
is the total complex of the bicomplex obtained by applying `F` to `K₁` and `K₂`. -/
noncomputable abbrev mapBifunctor [HasMapBifunctor K₁ K₂ F] : CochainComplex D ℤ :=
  HomologicalComplex.mapBifunctor K₁ K₂ F (ComplexShape.up ℤ)

/-- The inclusion of a summand `(F.obj (K₁.X n₁)).obj (K₂.X n₂) ⟶ (mapBifunctor K₁ K₂ F).X n`
of the total cochain complex when `n₁ + n₂ = n`. -/
noncomputable abbrev ιMapBifunctor [HasMapBifunctor K₁ K₂ F] (n₁ n₂ n : ℤ) (h : n₁ + n₂ = n) :
    (F.obj (K₁.X n₁)).obj (K₂.X n₂) ⟶ (mapBifunctor K₁ K₂ F).X n :=
  HomologicalComplex.ιMapBifunctor K₁ K₂ F _ _ _ _ h

end

section

variable [Preadditive C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (K₁ L₁ : CochainComplex C₁ ℤ) (f₁ : K₁ ⟶ L₁) (K₂ : CochainComplex C₂ ℤ)
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ (X₁ : C₁), (F.obj X₁).PreservesZeroMorphisms] (x : ℤ)
  [HasMapBifunctor K₁ K₂ F]

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `mapBifunctorShift₁Iso`. -/
@[simps! hom_f_f inv_f_f]
def mapBifunctorHomologicalComplexShift₁Iso :
    ((F.mapBifunctorHomologicalComplex _ _).obj (K₁⟦x⟧)).obj K₂ ≅
    (HomologicalComplex₂.shiftFunctor₁ D x).obj
      (((F.mapBifunctorHomologicalComplex _ _).obj K₁).obj K₂) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intros
    ext
    dsimp
    simp only [Linear.comp_units_smul, id_comp, Functor.map_units_smul,
      NatTrans.app_units_zsmul, comp_id])

instance : HasMapBifunctor (K₁⟦x⟧) K₂ F :=
  HomologicalComplex₂.hasTotal_of_iso (mapBifunctorHomologicalComplexShift₁Iso K₁ K₂ F x).symm _

/-- The canonical isomorphism `mapBifunctor (K₁⟦x⟧) K₂ F ≅ (mapBifunctor K₁ K₂ F)⟦x⟧`.
This isomorphism does not involve signs. -/
noncomputable def mapBifunctorShift₁Iso :
    mapBifunctor (K₁⟦x⟧) K₂ F ≅ (mapBifunctor K₁ K₂ F)⟦x⟧ :=
  HomologicalComplex₂.total.mapIso (mapBifunctorHomologicalComplexShift₁Iso K₁ K₂ F x) _ ≪≫
    (((F.mapBifunctorHomologicalComplex _ _).obj K₁).obj K₂).totalShift₁Iso x

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma ι_mapBifunctorShift₁Iso_hom_f (n₁ n₂ n : ℤ) (h : n₁ + n₂ = n)
    (m₁ m : ℤ) (hm₁ : m₁ = n₁ + x) (hm : m = n + x) :
    ιMapBifunctor _ K₂ F n₁ n₂ n h ≫ (mapBifunctorShift₁Iso K₁ K₂ F x).hom.f n =
      (F.map (shiftFunctorObjXIso K₁ x n₁ m₁ hm₁).hom).app _ ≫
        ιMapBifunctor K₁ K₂ F m₁ n₂ m (by lia) ≫
          (shiftFunctorObjXIso (mapBifunctor K₁ K₂ F) x n m hm).inv := by
  dsimp [mapBifunctorShift₁Iso]
  simp only [HomologicalComplex₂.ιTotal_map_assoc,
    HomologicalComplex₂.ι_totalShift₁Iso_hom_f _ _ _ _ _ _ _ hm₁ _ hm]
  simp [HomologicalComplex₂.ιTotal, HomologicalComplex₂.shiftFunctor₁XXIso,
    HomologicalComplex.XIsoOfEq, eqToHom_map]

set_option backward.isDefEq.respectTransparency false in
variable {K₁ L₁} in
@[reassoc (attr := simp)]
lemma mapBifunctorShift₁Iso_hom_naturality₁ [HasMapBifunctor L₁ K₂ F] :
    mapBifunctorMap (f₁⟦x⟧') (𝟙 K₂) F (.up ℤ) ≫ (mapBifunctorShift₁Iso L₁ K₂ F x).hom =
      (mapBifunctorShift₁Iso K₁ K₂ F x).hom ≫ mapBifunctorMap f₁ (𝟙 K₂) F (.up ℤ)⟦x⟧' := by
  ext n p q h
  simp [ι_mapBifunctorShift₁Iso_hom_f _ _ _ _ _ _ _ _ (p + x) (n + x) rfl rfl,
    ι_mapBifunctorShift₁Iso_hom_f_assoc _ _ _ _ _ _ _ _ (p + x) (n + x) rfl rfl]

end

section

variable [HasZeroMorphisms C₁] [Preadditive C₂] [Preadditive D]
  (K₁ : CochainComplex C₁ ℤ) (K₂ L₂ : CochainComplex C₂ ℤ) (f₂ : K₂ ⟶ L₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ (X₁ : C₁), (F.obj X₁).Additive] (y : ℤ)
  [HasMapBifunctor K₁ K₂ F]

/-- Auxiliary definition for `mapBifunctorShift₂Iso`. -/
@[simps! hom_f_f inv_f_f]
def mapBifunctorHomologicalComplexShift₂Iso :
    ((F.mapBifunctorHomologicalComplex _ _).obj K₁).obj (K₂⟦y⟧) ≅
    (HomologicalComplex₂.shiftFunctor₂ D y).obj
      (((F.mapBifunctorHomologicalComplex _ _).obj K₁).obj K₂) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i₁ => HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)) (by
      intros
      ext
      dsimp
      simp only [id_comp, comp_id])

instance : HasMapBifunctor K₁ (K₂⟦y⟧) F :=
  HomologicalComplex₂.hasTotal_of_iso (mapBifunctorHomologicalComplexShift₂Iso K₁ K₂ F y).symm _

/-- The canonical isomorphism `mapBifunctor K₁ (K₂⟦y⟧) F ≅ (mapBifunctor K₁ K₂ F)⟦y⟧`.
This isomorphism involves signs: on the summand `(F.obj (K₁.X p)).obj (K₂.X q)`, it is given
by the multiplication by `(p * y).negOnePow`. -/
noncomputable def mapBifunctorShift₂Iso :
    mapBifunctor K₁ (K₂⟦y⟧) F ≅ (mapBifunctor K₁ K₂ F)⟦y⟧ :=
  HomologicalComplex₂.total.mapIso
    (mapBifunctorHomologicalComplexShift₂Iso K₁ K₂ F y) (ComplexShape.up ℤ) ≪≫
    (((F.mapBifunctorHomologicalComplex _ _).obj K₁).obj K₂).totalShift₂Iso y

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma ι_mapBifunctorShift₂Iso_hom_f (n₁ n₂ n : ℤ) (h : n₁ + n₂ = n)
    (m₂ m : ℤ) (hm₂ : m₂ = n₂ + y) (hm : m = n + y) :
    ιMapBifunctor K₁ _ F n₁ n₂ n h ≫ (mapBifunctorShift₂Iso K₁ K₂ F y).hom.f n =
      (n₁ * y).negOnePow • (F.obj _).map (shiftFunctorObjXIso K₂ y n₂ m₂ hm₂).hom ≫
        ιMapBifunctor K₁ K₂ F n₁ m₂ m (by lia) ≫
        (shiftFunctorObjXIso (mapBifunctor K₁ K₂ F) y n m hm).inv := by
  dsimp [mapBifunctorShift₂Iso]
  simp only [HomologicalComplex₂.ιTotal_map_assoc,
    HomologicalComplex₂.ι_totalShift₂Iso_hom_f _ _ _ _ _ _ _ hm₂ _ hm]
  simp [HomologicalComplex₂.ιTotal, HomologicalComplex₂.shiftFunctor₂XXIso,
    HomologicalComplex.XIsoOfEq, eqToHom_map]

set_option backward.isDefEq.respectTransparency false in
variable {K₂ L₂} in
@[reassoc (attr := simp)]
lemma mapBifunctorShift₂Iso_hom_naturality₂ [HasMapBifunctor K₁ L₂ F] :
    mapBifunctorMap (𝟙 K₁) (f₂⟦y⟧') F (.up ℤ) ≫ (mapBifunctorShift₂Iso K₁ L₂ F y).hom =
      (mapBifunctorShift₂Iso K₁ K₂ F y).hom ≫ mapBifunctorMap (𝟙 K₁) f₂ F (.up ℤ)⟦y⟧' := by
  ext n p q h
  simp [ι_mapBifunctorShift₂Iso_hom_f _ _ _ _ _ _ _ _ (q + y) (n + y) rfl rfl,
    ι_mapBifunctorShift₂Iso_hom_f_assoc _ _ _ _ _ _ _ _ (q + y) (n + y) rfl rfl]

end

section

variable [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ)
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ (X₁ : C₁), (F.obj X₁).Additive] (x y : ℤ)
  [HasMapBifunctor K₁ K₂ F]

set_option backward.isDefEq.respectTransparency false in
lemma mapBifunctorShift₁Iso_trans_mapBifunctorShift₂Iso :
    mapBifunctorShift₁Iso K₁ (K₂⟦y⟧) F x ≪≫
      (CategoryTheory.shiftFunctor _ x).mapIso (mapBifunctorShift₂Iso K₁ K₂ F y) =
      (x * y).negOnePow • (mapBifunctorShift₂Iso (K₁⟦x⟧) K₂ F y ≪≫
        (CategoryTheory.shiftFunctor _ y).mapIso (mapBifunctorShift₁Iso K₁ K₂ F x) ≪≫
          (shiftFunctorComm (CochainComplex D ℤ) x y).app _) := by
  ext1
  dsimp [mapBifunctorShift₁Iso, mapBifunctorShift₂Iso]
  rw [Functor.map_comp, Functor.map_comp, assoc, assoc, assoc,
    ← HomologicalComplex₂.totalShift₁Iso_hom_naturality_assoc,
    HomologicalComplex₂.totalShift₁Iso_hom_totalShift₂Iso_hom,
    ← HomologicalComplex₂.totalShift₂Iso_hom_naturality_assoc,
    Linear.comp_units_smul, Linear.comp_units_smul,
    smul_left_cancel_iff,
    ← HomologicalComplex₂.total.map_comp_assoc,
    ← HomologicalComplex₂.total.map_comp_assoc,
    ← HomologicalComplex₂.total.map_comp_assoc]
  congr 2
  ext a b
  dsimp [HomologicalComplex₂.shiftFunctor₁₂CommIso]
  simp only [id_comp]

end

end CochainComplex

namespace CategoryTheory.Functor

variable [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ (X₁ : C₁), (F.obj X₁).Additive]
  [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ),
    CochainComplex.HasMapBifunctor K₁ K₂ F]

set_option backward.isDefEq.respectTransparency false in
noncomputable instance (K₁ : CochainComplex C₁ ℤ) :
    (F.map₂CochainComplex.obj K₁).CommShift ℤ where
  commShiftIso n :=
    NatIso.ofComponents (fun K₂ ↦ CochainComplex.mapBifunctorShift₂Iso K₁ K₂ F n)
  commShiftIso_zero := by
    ext K₂ n
    dsimp
    ext p q h
    simp [CochainComplex.ι_mapBifunctorShift₂Iso_hom_f _ _ F 0 p q n h q n (by lia) (by lia),
      CochainComplex.shiftFunctorZero_eq]
  commShiftIso_add a b := by
    ext K₂ n
    dsimp
    ext p q h
    dsimp at h
    simp [CochainComplex.ι_mapBifunctorShift₂Iso_hom_f _ _ F (a + b) p q n h
        (q + a + b) (n + a + b) (by lia) (by lia),
      CochainComplex.ι_mapBifunctorShift₂Iso_hom_f_assoc _ _ F b p q n h _ _ rfl rfl,
      CochainComplex.ι_mapBifunctorShift₂Iso_hom_f_assoc _ _ F a p (q + b) (n + b)
        (by lia) (q + a + b) (n + a + b) (by lia) (by lia), smul_smul,
        ← Int.negOnePow_add, CochainComplex.shiftFunctorAdd_eq,
        add_comm (p * b), mul_add, XIsoOfEq]

lemma commShiftIso_map₂CochainComplex_hom_app (K₁ : CochainComplex C₁ ℤ)
    (K₂ : CochainComplex C₂ ℤ) (n : ℤ) :
    ((F.map₂CochainComplex.obj K₁).commShiftIso n).hom.app K₂ =
      (CochainComplex.mapBifunctorShift₂Iso K₁ K₂ F n).hom := rfl

lemma commShiftIso_map₂CochainComplex_inv_app (K₁ : CochainComplex C₁ ℤ)
    (K₂ : CochainComplex C₂ ℤ) (n : ℤ) :
    ((F.map₂CochainComplex.obj K₁).commShiftIso n).inv.app K₂ =
      (CochainComplex.mapBifunctorShift₂Iso K₁ K₂ F n).inv := rfl

set_option backward.isDefEq.respectTransparency false in
instance {K₁ L₁ : CochainComplex C₁ ℤ} (f : K₁ ⟶ L₁) :
    NatTrans.CommShift (F.map₂CochainComplex.map f) ℤ where
  shift_comm n := by
    ext K₂ d
    dsimp
    ext p q h
    simp [commShiftIso_map₂CochainComplex_hom_app,
      CochainComplex.ι_mapBifunctorShift₂Iso_hom_f _ _ _ _ _ _ _ _ (q + n) (d + n) rfl rfl,
      CochainComplex.ι_mapBifunctorShift₂Iso_hom_f_assoc _ _ _ _ _ _ _ _ (q + n) (d + n) rfl rfl]

set_option backward.isDefEq.respectTransparency false in
noncomputable instance (K₂ : CochainComplex C₂ ℤ) :
    (F.map₂CochainComplex.flip.obj K₂).CommShift ℤ where
  commShiftIso n :=
    NatIso.ofComponents (fun K₁ ↦ CochainComplex.mapBifunctorShift₁Iso K₁ K₂ F n)
  commShiftIso_zero := by
    ext K₂ n
    dsimp
    ext p q h
    simp [CochainComplex.ι_mapBifunctorShift₁Iso_hom_f _ _ F 0 p q n h p n
      (by lia) (by lia), CochainComplex.shiftFunctorZero_eq]
  commShiftIso_add a b := by
    ext K₂ n
    dsimp
    ext p q h
    dsimp at h
    simp [CochainComplex.ι_mapBifunctorShift₁Iso_hom_f _ _ F (a + b) p q n h
        (p + a + b) (n + a + b) (by lia) (by lia),
      CochainComplex.ι_mapBifunctorShift₁Iso_hom_f_assoc _ _ F b p q n h _ _ rfl rfl,
      CochainComplex.ι_mapBifunctorShift₁Iso_hom_f_assoc _ _ F a (p + b) q (n + b)
        (by lia) (p + a + b) (n + a + b) (by lia) (by lia),
      CochainComplex.shiftFunctorAdd_eq, XIsoOfEq, eqToHom_map]

lemma commShiftIso_map₂CochainComplex_flip_hom_app (K₁ : CochainComplex C₁ ℤ)
    (K₂ : CochainComplex C₂ ℤ) (n : ℤ) :
    ((F.map₂CochainComplex.flip.obj K₂).commShiftIso n).hom.app K₁ =
      (CochainComplex.mapBifunctorShift₁Iso K₁ K₂ F n).hom := rfl

lemma commShiftIso_map₂CochainComplex_flip_inv_app (K₁ : CochainComplex C₁ ℤ)
    (K₂ : CochainComplex C₂ ℤ) (n : ℤ) :
    ((F.map₂CochainComplex.flip.obj K₂).commShiftIso n).inv.app K₁ =
      (CochainComplex.mapBifunctorShift₁Iso K₁ K₂ F n).inv := rfl

set_option backward.isDefEq.respectTransparency false in
instance {K₂ L₂ : CochainComplex C₂ ℤ} (g : K₂ ⟶ L₂) :
    NatTrans.CommShift (F.map₂CochainComplex.flip.map g) ℤ where
  shift_comm n := by
    ext K₁ d
    dsimp
    ext p q h
    simp [commShiftIso_map₂CochainComplex_flip_hom_app,
      CochainComplex.ι_mapBifunctorShift₁Iso_hom_f _ _ _ _ _ _ _ _ (p + n) (d + n) rfl rfl,
      CochainComplex.ι_mapBifunctorShift₁Iso_hom_f_assoc _ _ _ _ _ _ _ _ (p + n) (d + n) rfl rfl]

set_option backward.isDefEq.respectTransparency false in
noncomputable instance :
    F.map₂CochainComplex.CommShift₂Int where
  comm K₁ K₂ p q := by
    have := congr_arg Iso.hom
      (CochainComplex.mapBifunctorShift₁Iso_trans_mapBifunctorShift₂Iso K₁ K₂ F p q)
    dsimp at this
    simp [commShiftIso_map₂CochainComplex_hom_app,
      commShiftIso_map₂CochainComplex_flip_hom_app,
      reassoc_of% this, smul_smul]

end CategoryTheory.Functor
