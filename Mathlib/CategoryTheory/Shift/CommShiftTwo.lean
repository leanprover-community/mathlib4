/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Shift.CommShiftProd
import Mathlib.CategoryTheory.Shift.Prod
import Mathlib.CategoryTheory.Shift.Twist
import Mathlib.CategoryTheory.Shift.Pullback
import Mathlib.Algebra.Ring.Int.Parity

/-!
# Commutation to shifts of functors in two variables

-/

@[simps]
def AddMonoidHom.sum (M : Type*) [AddCommMonoid M] : M × M →+ M where
  toFun m := m.1 + m.2
  map_zero' := by simp
  map_add' := by
    rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
    dsimp
    rw [add_assoc, ← add_assoc y₁, add_comm y₁, add_assoc, add_assoc]

namespace CategoryTheory

variable {C C₁ C₂ D : Type*}
  [Category C] [Category C₁] [Category C₂] [Category D]

section

variable (D) (M : Type*)
  [AddCommMonoid M] [HasShift C₁ M] [HasShift C₂ M] [HasShift D M]

structure CommShift₂Setup extends TwistShiftData (PullbackShift D (.sum M)) (M × M) where
  z_zero₁ (m₁ m₂ : M) : z (0, m₁) (0, m₂) = 1 := by aesop
  z_zero₂ (m₁ m₂ : M) : z (m₁, 0) (m₂, 0) = 1 := by aesop
  ε (m n : M) : (CatCenter D)ˣ
  hε (m n : M) : ε m n = (z (0, n) (m, 0))⁻¹ * z (m, 0) (0, n) := by aesop

end

namespace Functor

class CommShift₂ (G : C₁ ⥤ C₂ ⥤ D) {M : Type*}
    [AddCommMonoid M] [HasShift C₁ M] [HasShift C₂ M] [HasShift D M] (h : CommShift₂Setup D M) where
  commShiftObj (X₁ : C₁) : (G.obj X₁).CommShift M := by infer_instance
  commShift_map {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁) : NatTrans.CommShift (G.map f) M := by infer_instance
  commShiftFlipObj (X₂ : C₂) : (G.flip.obj X₂).CommShift M := by infer_instance
  commShift_flip_map {X₂ Y₂ : C₂} (g : X₂ ⟶ Y₂) : NatTrans.CommShift (G.flip.map g) M := by
    infer_instance
  comm (G h) (X₁ : C₁) (X₂ : C₂) (m n : M) :
      ((G.obj (X₁⟦m⟧)).commShiftIso n).hom.app X₂ ≫
          (((G.flip.obj X₂).commShiftIso m).hom.app X₁)⟦n⟧' =
        ((G.flip.obj (X₂⟦n⟧)).commShiftIso m).hom.app X₁ ≫
          (((G.obj X₁).commShiftIso n).hom.app X₂)⟦m⟧' ≫
          (shiftComm ((G.obj X₁).obj X₂) m n).inv ≫ (h.ε m n).val.app _

namespace CommShift₂

attribute [instance] commShiftObj commShiftFlipObj
  commShift_map commShift_flip_map

end CommShift₂

end Functor

variable {M : Type*} [AddCommMonoid M] [HasShift C₁ M] [HasShift C₂ M] [HasShift D M]
variable (h : CommShift₂Setup D M)

namespace CommShift₂Setup

protected def Category (h : CommShift₂Setup D M) := TwistShift h.toTwistShiftData

instance : Category h.Category := inferInstanceAs (Category (TwistShift h.toTwistShiftData))

noncomputable instance : HasShift h.Category (M × M) :=
  inferInstanceAs (HasShift (TwistShift h.toTwistShiftData) (M × M))

-- variable (G : C₁ × C₂ ⥤ h.Category) [G.CommShift (M × M)]
-- should be essentially equivalent to
-- variable (F : C₁ ⥤ C₂ ⥤ D) [F.CommShift₂ h]

noncomputable def shiftIso (m n p : M) (hp : m + n = p) :
    shiftFunctor h.Category (m, n) ≅ shiftFunctor D p :=
  pullbackShiftIso _ _ _ _ hp.symm

@[reassoc]
lemma shiftFunctor_map (m n p : M) (hp : m + n = p) {X Y : D} (f : X ⟶ Y) :
    (shiftFunctor h.Category (m, n)).map f =
    (h.shiftIso m n p hp).hom.app X ≫ (shiftFunctor D p).map f ≫
      (h.shiftIso m n p hp).inv.app Y := by
  simp

lemma shiftFunctorZero_inv_app (X : h.Category) :
    (shiftFunctorZero _ (M × M)).inv.app X =
      (shiftFunctorZero D M).inv.app X ≫ (h.shiftIso 0 0 0 (add_zero 0)).inv.app X :=
  pullbackShiftFunctorZero_inv_app ..

lemma shiftFunctorAdd'_inv_app (m₁ m₂ m₃ : M) (hm : m₁ + m₂ = m₃)
    (n₁ n₂ n₃ : M) (hn : n₁ + n₂ = n₃)
    (p₁ p₂ p₃ : M) (hp₁ : m₁ + n₁ = p₁) (hp₂ : m₂ + n₂ = p₂) (hp₃ : m₃ + n₃ = p₃)
    (X : h.Category) :
    (shiftFunctorAdd' h.Category (m₁, n₁) (m₂, n₂) (m₃, n₃) (by aesop)).inv.app X =
      (h.shiftIso m₂ n₂ p₂ hp₂).hom.app _ ≫
        (shiftFunctor D p₂).map ((h.shiftIso m₁ n₁ p₁ hp₁).hom.app X) ≫
        (shiftFunctorAdd' D p₁ p₂ p₃ (by rw [← hp₃, ← hp₂, ← hp₁, ← hm, ← hn]; abel)).inv.app X ≫
        (h.shiftIso m₃ n₃ p₃ hp₃).inv.app X ≫
          (((h.z (m₁, n₁) (m₂, n₂))⁻¹).1).app _
          := by
  refine (TwistShift.shiftFunctorAdd'_inv_app ..).trans ?_
  dsimp [shiftIso]
  rw [pullbackShiftFunctorAdd'_inv_app _ _ _ _ _ _ p₁ p₂ p₃
    (by aesop) (by aesop) (by aesop)]
  aesop

section

variable (F : C₁ ⥤ C₂ ⥤ D) [F.CommShift₂ h]

protected abbrev uncurry : C₁ × C₂ ⥤ h.Category := uncurry.obj F

namespace commShiftUncurry

noncomputable def iso₁ (m₁ : M) :
    shiftFunctor (C₁ × C₂) (m₁, (0 : M)) ⋙ h.uncurry F ≅
      h.uncurry F ⋙ shiftFunctor h.Category (m₁, (0 : M)) :=
  fullyFaithfulCurry.preimageIso (NatIso.ofComponents
    (fun X₁ ↦ NatIso.ofComponents (fun X₂ ↦
      (F.obj (X₁⟦m₁⟧)).mapIso ((shiftFunctorZero C₂ M).app X₂) ≪≫
        ((F.flip.obj X₂).commShiftIso m₁).app X₁ ≪≫
        (h.shiftIso m₁ 0 m₁ (add_zero m₁)).symm.app _)
      (fun {X₂ Y₂} f ↦ by
        have := NatTrans.shift_app_comm (F.flip.map f) m₁ X₁
        dsimp at this ⊢
        simp only [Functor.map_id, NatTrans.id_app, Category.id_comp,
          Category.assoc, ← NatTrans.naturality, reassoc_of% this]
        simp [-Functor.map_comp, ← Functor.map_comp_assoc]))
    (fun {X₁ Y₁} f ↦ by
      ext X₂
      have := (F.flip.obj X₂).commShiftIso_hom_naturality f m₁
      dsimp at this ⊢
      simp only [Functor.map_id, Category.comp_id, Category.assoc,
        ← NatTrans.naturality, ← NatTrans.naturality_assoc, ← reassoc_of% this]))

@[reassoc]
lemma iso₁_hom_app (X₁ : C₁) (X₂ : C₂) (m₁ : M) :
    (iso₁ h F m₁).hom.app (X₁, X₂) =
    (F.obj ((shiftFunctor C₁ m₁).obj X₁)).map ((shiftFunctorZero C₂ M).hom.app X₂) ≫
    ((F.flip.obj X₂).commShiftIso m₁).hom.app X₁ ≫
      (h.shiftIso m₁ 0 m₁ (add_zero m₁)).inv.app ((F.obj X₁).obj X₂) := by
  simp [iso₁, fullyFaithfulCurry, Equivalence.fullyFaithfulInverse]

lemma iso₁_zero : iso₁ h F 0 = Functor.CommShift.isoZero _ _ := by
  ext ⟨X₁, X₂⟩
  simp [iso₁_hom_app, shiftFunctorZero_inv_app, Functor.commShiftIso_zero]

lemma iso₁_add (m m' : M) :
    iso₁ h F (m + m') =
      Functor.CommShift.isoAdd' (by aesop) (iso₁ h F m) (iso₁ h F m') := by
  ext ⟨X₁, X₂⟩
  have := NatTrans.shift_app_comm (F.flip.map ((shiftFunctorZero C₂ M).hom.app X₂)) m' (X₁⟦m⟧)
  dsimp at this
  simp only [shiftFunctor_prod, Functor.comp_obj, Functor.prod_obj, uncurry_obj_obj, iso₁_hom_app,
    Functor.id_obj, Functor.flip_obj_obj, Functor.CommShift.isoAdd'_hom_app, shiftFunctorAdd'_prod,
    NatIso.prod_hom, uncurry_obj_map, NatTrans.prod_app_fst, NatTrans.prod_app_snd,
    Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
    h.shiftFunctor_map_assoc _ _ _ (add_zero m'), Category.assoc, Iso.inv_hom_id_app_assoc,
    h.shiftFunctorAdd'_inv_app _ _ _ rfl _ _ _ (add_zero 0) _ _ (m + m')
    (add_zero m) (add_zero m') (by simp), Iso.inv_hom_id_app_assoc, h.z_zero₂,
    inv_one, Units.val_one, End.one_def, NatTrans.id_app,
    Functor.commShiftIso_add' _ rfl, Functor.CommShift.isoAdd'_hom_app]
  simp only [Functor.flip_obj_obj, Functor.flip_obj_map, Functor.id_obj,
    Category.assoc, Category.comp_id, NatTrans.naturality_assoc, Functor.map_comp_assoc,
    shiftFunctorAdd'_add_zero_hom_app]
  nth_rw 1 [← Functor.map_comp_assoc]
  nth_rw 3 [← Functor.map_comp_assoc]
  simp [← reassoc_of% this]

noncomputable def iso₂ (m₂ : M) :
    shiftFunctor (C₁ × C₂) ((0 : M), m₂) ⋙ h.uncurry F ≅
      h.uncurry F ⋙ shiftFunctor h.Category ((0 : M), m₂) :=
  fullyFaithfulCurry.preimageIso (NatIso.ofComponents
    (fun X₁ ↦ NatIso.ofComponents (fun X₂ ↦
      (F.mapIso ((shiftFunctorZero C₁ M).app X₁)).app (X₂⟦m₂⟧) ≪≫
        ((F.obj X₁).commShiftIso m₂).app X₂ ≪≫
        (h.shiftIso 0 m₂ m₂ (zero_add m₂)).symm.app ((F.obj X₁).obj X₂))
      (fun {X₂ Y₂} f ↦ by simp))
    (fun {X₁ Y₁} f ↦ by
      ext X₂
      have := congr_app (F.congr_map ((shiftFunctorZero C₁ M).hom.naturality f)) (X₂⟦m₂⟧)
      simp only [Functor.map_comp] at this
      dsimp at this ⊢
      simp only [Functor.map_id, Category.comp_id, Category.assoc, ← NatTrans.naturality]
      rw [NatTrans.shift_app_comm_assoc (F.map f) m₂ X₂, reassoc_of% this]))

@[reassoc]
lemma iso₂_hom_app (X₁ : C₁) (X₂ : C₂) (m₂ : M) :
    (iso₂ h F m₂).hom.app (X₁, X₂) =
      (F.map ((shiftFunctorZero C₁ M).hom.app X₁)).app (X₂⟦m₂⟧) ≫
        ((F.obj X₁).commShiftIso m₂).hom.app X₂ ≫
        (h.shiftIso 0 m₂ m₂ (zero_add m₂)).inv.app ((F.obj X₁).obj X₂) := by
  simp [iso₂, fullyFaithfulCurry, Equivalence.fullyFaithfulInverse]

lemma iso₂_zero : iso₂ h F 0 = Functor.CommShift.isoZero _ _ := by
  ext ⟨X₁, X₂⟩
  simp [iso₂_hom_app, shiftFunctorZero_inv_app, Functor.commShiftIso_zero]

lemma iso₂_add (m m' : M) :
    iso₂ h F (m + m') =
      Functor.CommShift.isoAdd' (by aesop) (iso₂ h F m) (iso₂ h F m') := by
  ext ⟨X₁, X₂⟩
  have this := NatTrans.shift_app_comm (F.map ((shiftFunctorZero C₁ M).hom.app X₁)) m' (X₂⟦m⟧)
  dsimp at this
  simp only [shiftFunctor_prod, Functor.comp_obj, Functor.prod_obj, uncurry_obj_obj,
    iso₂_hom_app, Functor.id_obj, Functor.CommShift.isoAdd'_hom_app, shiftFunctorAdd'_prod,
    NatIso.prod_hom, uncurry_obj_map, NatTrans.prod_app_fst, NatTrans.prod_app_snd,
    Functor.map_comp, Category.assoc, NatTrans.naturality_assoc]
  rw [h.shiftFunctor_map_assoc _ _ _ (zero_add m'), Iso.inv_hom_id_app_assoc,
    NatTrans.naturality_assoc, ← Functor.map_comp_assoc,
    h.shiftFunctorAdd'_inv_app _ _ _ (add_zero 0) _ _ _ rfl _ _ _
    (zero_add m) (zero_add m') (zero_add (m + m')), h.z_zero₁,
    inv_one, Units.val_one, End.one_def, NatTrans.id_app,
    Functor.commShiftIso_add' _ rfl, Functor.CommShift.isoAdd'_hom_app,
    shiftFunctorAdd'_add_zero_hom_app, ← NatTrans.comp_app_assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app, NatTrans.naturality_assoc, NatTrans.naturality_assoc]
  nth_rw 2 [← Functor.map_comp_assoc]
  simp [reassoc_of% this]

lemma isoAdd'_iso₁_iso₂ (m₁ m₂ : M) :
    Functor.CommShift.isoAdd' (show _ = (m₁, m₂) by aesop)
        (iso₁ h F m₁) (iso₂ h F m₂) =
      Functor.CommShift.isoAdd' (by aesop) (iso₂ h F m₂) (iso₁ h F m₁) := by
  ext ⟨X₁, X₂⟩
  simp [shiftFunctorAdd'_add_zero_hom_app, shiftFunctorAdd'_zero_add_hom_app,
    iso₁_hom_app, iso₂_hom_app]
  have h₁ := Functor.CommShift₂.comm F h X₁ X₂ m₁ m₂
  have h₂ := NatTrans.naturality_1 ((F.flip.obj (X₂⟦m₂⟧)).commShiftIso m₁).hom
    ((shiftFunctorZero C₁ M).app X₁)
  dsimp at h₁ h₂
  conv_lhs =>
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
      Category.assoc, Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
      shiftFunctor_map_assoc _ _ _ _ (zero_add _), Iso.inv_hom_id_app_assoc,
      shiftFunctorAdd'_inv_app _ _ _ _ (add_zero m₁) _ _ _ (zero_add m₂) _ _ _
        (add_zero m₁) (zero_add m₂) rfl, Iso.inv_hom_id_app_assoc,
      ← NatTrans.comp_app_assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    simp only [NatTrans.id_app, Functor.id_obj, Functor.map_id, Category.id_comp]
    rw [Functor.map_comp_assoc, reassoc_of% h₁, ← Functor.map_comp_assoc,
      Iso.inv_hom_id_app, Functor.map_id, Category.id_comp,
      ← CatCenter.naturality_assoc, ← CatCenter.naturality_assoc,
      ← CatCenter.mul_app, h.hε, Units.val_mul, mul_assoc, Units.mul_inv, mul_one,
      shiftFunctorComm_eq _ _ _ _ rfl, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
      Category.assoc, Iso.hom_inv_id_app_assoc, ← reassoc_of% h₂]
  conv_rhs =>
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
      shiftFunctorAdd'_inv_app _ _ _ _ (zero_add m₁) _ _ _ (add_zero m₂) _ _ _
        (zero_add m₂) (add_zero m₁) rfl, NatTrans.naturality_assoc,
      ← (shiftFunctor D m₁).map_comp_assoc, Iso.inv_hom_id_app]
    simp only [Functor.id_obj, Functor.map_id, Category.id_comp,
      NatTrans.naturality, NatTrans.naturality_assoc, Iso.inv_hom_id_app_assoc]

end commShiftUncurry

open commShiftUncurry in
noncomputable instance commShiftUncurry : (h.uncurry F).CommShift (M × M) :=
  Functor.CommShift.mkProd (iso₁ h F) (iso₂ h F) (iso₁_zero h F) (iso₂_zero h F)
    (iso₁_add h F) (iso₂_add h F) (isoAdd'_iso₁_iso₂ h F)

end

section

variable (G : C₁ × C₂ ⥤ h.Category) [G.CommShift (M × M)]

protected abbrev curry : C₁ ⥤ C₂ ⥤ D := curry.obj G

namespace commShift₂Curry

noncomputable def iso₁ (m : M) :
    curry.obj (Functor.prod (𝟭 _) (shiftFunctor C₂ m) ⋙ G) ≅
    curry.obj (G ⋙ shiftFunctor D m) :=
  curry.mapIso (isoWhiskerRight (NatIso.prod (shiftFunctorZero C₁ M).symm (Iso.refl _)) _ ≪≫
    G.commShiftIso ((0 : M), m) ≪≫
    isoWhiskerLeft G (h.shiftIso 0 m m (zero_add m)))

@[reassoc]
lemma iso₁_hom_app_app (X₁ : C₁) (X₂ : C₂) (m : M) :
    ((iso₁ h G m).hom.app X₁).app X₂ =
      G.map (Prod.mkHom ((shiftFunctorZero C₁ M).inv.app X₁) (𝟙 _)) ≫
        (G.commShiftIso ((0 : M), m)).hom.app (X₁, X₂) ≫
          (h.shiftIso 0 m m (zero_add m)).hom.app _ := by
  simp [iso₁, NatTrans.prod]

noncomputable instance (X₁ : C₁) :
    ((h.curry G).obj X₁).CommShift M where
  iso m := (iso₁ h G m).app X₁
  zero := by
    ext X₂
    simp only [curry_obj_obj_obj, Functor.comp_obj, Functor.prod_obj, Functor.id_obj, Iso.app_hom,
      iso₁_hom_app_app, shiftFunctor_prod, Functor.CommShift.isoZero_hom_app, curry_obj_obj_map]
    change _ ≫ (G.commShiftIso (0 : M × M)).hom.app (X₁, X₂) ≫ _ = _
    rw [G.commShiftIso_zero, Functor.CommShift.isoZero_hom_app,
      Category.assoc, shiftFunctorZero_inv_app, Category.assoc, Iso.inv_hom_id_app,
      Category.comp_id, ← G.map_comp_assoc]
    congr 2
    aesop
  add m n := by
    ext X₂
    dsimp
    simp only [iso₁_hom_app_app, Functor.CommShift.isoAdd_hom_app,
      G.commShiftIso_add' (show ((0 : M), m) + (0, n) = (0, m + n) by aesop),
      shiftFunctorAdd'_inv_app _ _ _ _ (add_zero 0) _ _ _ rfl _ _ _ (zero_add m)
      (zero_add n) (zero_add (m + n)), Functor.id_obj, Functor.comp_obj, shiftFunctor_prod,
      Functor.CommShift.isoAdd'_hom_app, Functor.prod_obj, shiftFunctorAdd'_prod, NatIso.prod_hom,
      h.z_zero₁, inv_one, Units.val_one, End.one_def, NatTrans.id_app, Category.comp_id,
      NatTrans.naturality_assoc, Category.assoc, Iso.inv_hom_id_app, curry_obj_obj_obj, ←
      shiftFunctorAdd'_eq_shiftFunctorAdd, curry_obj_obj_map, Iso.app_hom,
      Functor.map_comp]
    rw [← NatTrans.naturality_1_assoc (G.commShiftIso ((0 : M), n)).hom
      (Iso.prod ((shiftFunctorZero C₁ M).symm.app X₁) (Iso.refl (X₂⟦m⟧)))]
    dsimp
    simp only [← G.map_comp_assoc, NatTrans.naturality_assoc]
    congr 2
    ext
    · simp [shiftFunctorAdd'_zero_add_hom_app, ← Functor.map_comp]
    · simp

end commShift₂Curry

open commShift₂Curry in
lemma commShift_curry_obj_hom_app (X₁ : C₁) (X₂ : C₂) (m : M) :
    (((h.curry G).obj X₁).commShiftIso m).hom.app X₂ = ((iso₁ h G m).app X₁).hom.app X₂ := rfl

namespace commShift₂Curry

attribute [local simp] commShift_curry_obj_hom_app

instance {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁) :
    NatTrans.CommShift ((h.curry G).map f) M where
  shift_comm m := by
    ext X₂
    have h₁ := (G.commShiftIso ((0 : M), m)).hom.naturality (Prod.mkHom f (𝟙 X₂))
    have h₂ := (h.shiftIso 0 m m (zero_add m)).hom.naturality (G.map (Prod.mkHom f (𝟙 X₂)))
    dsimp at h₁ h₂ ⊢
    simp only [iso₁_hom_app_app, Functor.id_obj, Functor.comp_obj, shiftFunctor_prod,
      Category.assoc]
    rw [← h₂, ← reassoc_of% h₁, ← G.map_comp_assoc, ← G.map_comp_assoc]
    congr 2
    ext
    · simp [← NatTrans.naturality]
    · simp

noncomputable def iso₂ (m : M) :
    curry.obj (Functor.prod (shiftFunctor C₁ m) (𝟭 _)  ⋙ G) ≅
    curry.obj (G ⋙ shiftFunctor D m) :=
  curry.mapIso (isoWhiskerRight (NatIso.prod  (Iso.refl _) (shiftFunctorZero C₂ M).symm) _ ≪≫
    G.commShiftIso (m, (0 : M)) ≪≫
    isoWhiskerLeft G (h.shiftIso m 0 m (add_zero m)))

@[reassoc]
lemma iso₂_hom_app_app (X₁ : C₁) (X₂ : C₂) (m : M) :
    ((iso₂ h G m).hom.app X₁).app X₂ =
      G.map (Prod.mkHom (𝟙 _) ((shiftFunctorZero C₂ M).inv.app X₂)) ≫
        (G.commShiftIso (m, (0 : M))).hom.app (X₁, X₂) ≫
          (h.shiftIso m 0 m (add_zero m)).hom.app _ := by
  simp [iso₂, NatTrans.prod]

noncomputable instance (X₂ : C₂) : ((h.curry G).flip.obj X₂).CommShift M where
  iso m := ((flipFunctor _ _ _).mapIso (iso₂ h G m)).app X₂
  zero := by
    ext X₁
    simp only [flipFunctor_obj, Functor.flip_obj_obj, curry_obj_obj_obj, Functor.comp_obj,
      Functor.prod_obj, Functor.id_obj, Iso.app_hom, Functor.mapIso_hom, flipFunctor_map_app_app,
      iso₂_hom_app_app, shiftFunctor_prod, Functor.CommShift.isoZero_hom_app, Functor.flip_obj_map,
      curry_obj_map_app]
    change _ ≫ (G.commShiftIso (0 : M × M)).hom.app (X₁, X₂) ≫ _ = _
    rw [G.commShiftIso_zero, Functor.CommShift.isoZero_hom_app,
      Category.assoc, shiftFunctorZero_inv_app, Category.assoc, Iso.inv_hom_id_app,
      Category.comp_id, ← G.map_comp_assoc]
    congr 2
    aesop
  add m n := by
    ext X₁
    simp [iso₂_hom_app_app,
      G.commShiftIso_add' (show (m, (0 : M)) + (n, 0) = (m + n, 0) by aesop),
      shiftFunctorAdd'_inv_app _ _ _ _ rfl _ _ _ (zero_add 0) _ _ _
      (add_zero m) (add_zero n) (add_zero (m + n)),
      ← shiftFunctorAdd'_eq_shiftFunctorAdd, h.z_zero₂]
    rw [← NatTrans.naturality_1_assoc (G.commShiftIso (n, (0 : M))).hom
      (Iso.prod (Iso.refl (X₁⟦m⟧)) ((shiftFunctorZero C₂ M).symm.app X₂))]
    dsimp
    simp only [← G.map_comp_assoc, NatTrans.naturality_assoc]
    congr 2
    ext
    · simp
    · simp [shiftFunctorAdd'_zero_add_hom_app, ← Functor.map_comp]

end commShift₂Curry

open commShift₂Curry in
lemma commShift_curry_flip_obj_hom_app (X₁ : C₁) (X₂ : C₂) (m : M) :
    (((h.curry G).flip.obj X₂).commShiftIso m).hom.app X₁ =
      ((iso₂ h G m).hom.app X₁).app X₂ := rfl

namespace commShift₂Curry

attribute [local simp] commShift_curry_flip_obj_hom_app

instance {X₂ Y₂ : C₂} (f : X₂ ⟶ Y₂) :
    NatTrans.CommShift ((h.curry G).flip.map f) M where
  shift_comm m := by
    ext X₁
    dsimp
    have h₁ := (G.commShiftIso (m, (0 : M))).hom.naturality (Prod.mkHom (𝟙 X₁) f)
    have h₂ := (h.shiftIso m 0 m (add_zero m)).hom.naturality (G.map (Prod.mkHom (𝟙 X₁) f))
    simp only [iso₂_hom_app_app, Functor.id_obj, Functor.comp_obj, shiftFunctor_prod,
      Category.assoc]
    rw [← h₂, ← reassoc_of% h₁, ← G.map_comp_assoc, ← G.map_comp_assoc]
    congr 2
    ext
    · simp
    · simp [← NatTrans.naturality]

end commShift₂Curry

open commShift₂Curry in
noncomputable instance commShift₂Curry : (h.curry G).CommShift₂ h where
  comm X₁ X₂ m n := by
    simp only [Functor.comp_obj, curry_obj_obj_obj, Functor.flip_obj_obj,
      commShift_curry_obj_hom_app, Iso.app_hom, iso₁_hom_app_app, Functor.id_obj,
      shiftFunctor_prod, commShift_curry_flip_obj_hom_app, iso₂_hom_app_app,
      Functor.map_comp, Category.assoc, Iso.app_inv]
    trans (G.commShiftIso (m, n)).hom.app (X₁, X₂) ≫
      (h.shiftIso m n _ rfl).hom.app _ ≫ (shiftFunctorAdd' D m n (m + n) rfl).hom.app _ ≫
        (h.z (m, 0) (0, n)).1.app _
    · simp only [G.commShiftIso_add' (show (m, 0) + (0, n) = (m, n) by aesop),
        shiftFunctorAdd'_inv_app _ _ _ _ (add_zero m) _ _ _ (zero_add n) _ _ _ (add_zero m)
          (zero_add n) rfl,
        Functor.comp_obj, shiftFunctor_prod, Functor.CommShift.isoAdd'_hom_app,
        Functor.prod_obj, shiftFunctorAdd'_prod, NatIso.prod_hom,
        Functor.id_obj, NatTrans.naturality_assoc, Category.assoc]
      have := NatTrans.naturality_1 (G.commShiftIso ((0 : M), n)).hom
        (Iso.prod (Iso.refl (X₁⟦m⟧)) ((shiftFunctorZero C₂ M).symm.app X₂) )
      dsimp at this
      rw [← reassoc_of% this, ← G.map_comp_assoc,
        ← CatCenter.naturality_assoc, ← CatCenter.naturality, Category.assoc,
        ← CatCenter.mul_app, Units.mul_inv, End.one_def, NatTrans.id_app,
        Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app_assoc,
        NatTrans.naturality_assoc]
      dsimp
      rw [Category.comp_id]
      congr 2
      · ext
        · simp [shiftFunctorAdd'_add_zero_hom_app]
        · simp [shiftFunctorAdd'_zero_add_hom_app, ← Functor.map_comp]
    · rw [G.commShiftIso_add' (show (0, n) + (m, 0) = (m, n) by aesop)]
      simp [shiftFunctorAdd'_inv_app _ _ _ _ (zero_add m) _ _ _ (add_zero n) _ _ _
        (zero_add n) (add_zero m) rfl, shiftFunctorComm_eq _ _ _ _ rfl]
      have := NatTrans.naturality_1 (G.commShiftIso (m, (0 : M))).hom
        (Iso.prod ((shiftFunctorZero C₁ M).symm.app X₁) (Iso.refl (X₂⟦n⟧)))
      dsimp at this
      rw [← reassoc_of% this, ← G.map_comp_assoc,
        ← CatCenter.naturality_assoc, ← CatCenter.naturality_assoc, ← CatCenter.mul_app,
        ← Units.val_mul, ← h.hε, Iso.inv_hom_id_app_assoc,
        NatTrans.naturality_assoc]
      congr 2
      · ext
        · simp [shiftFunctorAdd'_zero_add_hom_app, ← Functor.map_comp]
        · simp [shiftFunctorAdd'_add_zero_hom_app]

end

noncomputable def int
    {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
    [∀ (n : ℤ), (shiftFunctor D n).Additive] :
    CommShift₂Setup D ℤ where
  z m n := (-1) ^ (m.1 * n.2)
  assoc := by
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
    rw [← zpow_add, ← zpow_add]
    congr 1
    dsimp
    rw [add_mul, mul_add]
    abel
  shift_z_app := by
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩ X
    dsimp
    generalize hn : a * d = n
    obtain ⟨n, rfl⟩ | ⟨n, rfl⟩ := Int.even_or_odd n
    · simp [zpow_add, ← mul_zpow]
    · rw [zpow_add, two_mul, zpow_add, ← mul_zpow, mul_neg, mul_one, neg_neg, one_zpow,
        one_mul, zpow_one, Units.val_neg, Units.val_one, End.one_def, NatTrans.app_neg,
        NatTrans.app_neg]
      simp
  ε p q := (-1) ^ (p * q)

end CommShift₂Setup

end CategoryTheory
