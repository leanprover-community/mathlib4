/-
<<<<<<< HEAD
Copyright (c) 2024 Joël Riou. All rights reserved.
=======
Copyright (c) 2026 Joël Riou. All rights reserved.
>>>>>>> origin
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.Order.WithBotTop

/-!
# Truncations for a t-structure

Let `t` be a t-structure on a triangulated category `C`.
In this file, we extend the definition of the truncation functors
`truncLT` and `truncGE` for indices in `ℤ` to `EInt`,
as `t.eTruncLT : EInt ⥤ C ⥤ C` and `t.eTruncGE : EInt ⥤ C ⥤ C`.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits Pretriangulated ZeroObject Preadditive

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Triangulated

namespace TStructure

variable (t : TStructure C)

/-- The functor `EInt ⥤ C ⥤ C` which sends `⊥` to the zero functor,
`n : ℤ` to `t.truncLT n` and `⊤` to `𝟭 C`. -/
noncomputable def eTruncLT : EInt ⥤ C ⥤ C where
<<<<<<< HEAD
  obj n := by
    induction n using WithBotTop.rec with
    | bot => exact 0
    | coe a => exact t.truncLT a
    | top => exact 𝟭 C
=======
  obj := WithBotTop.rec 0 t.truncLT (𝟭 C)
>>>>>>> origin
  map {x y} f := by
    induction x using WithBotTop.rec with
    | bot =>
      induction y using WithBotTop.rec with
      | bot => exact 𝟙 _
      | coe b => exact 0
      | top => exact 0
    | coe a =>
      induction y using WithBotTop.rec with
      | bot => exact 0
      | coe b => exact t.natTransTruncLTOfLE a b (by simpa using leOfHom f)
      | top => exact t.truncLTι a
    | top =>
      induction y using WithBotTop.rec with
      | bot => exact 0
      | coe b => exact 0
      | top => exact 𝟙 _
  map_id n := by induction n using WithBotTop.rec <;> simp
  map_comp {x y z} f g := by
    have f' := leOfHom f
    have g' := leOfHom g
    induction x using WithBotTop.rec <;> induction y using WithBotTop.rec <;>
      induction z using WithBotTop.rec <;> cat_disch

@[simp]
lemma eTruncLT_obj_top : t.eTruncLT.obj ⊤ = 𝟭 _ := rfl

@[simp]
lemma eTruncLT_obj_bot : t.eTruncLT.obj ⊥ = 0 := rfl

@[simp]
lemma eTruncLT_obj_coe (n : ℤ) : t.eTruncLT.obj n = t.truncLT n := rfl

@[simp]
lemma eTruncLT_map_eq_truncLTι (n : ℤ) :
    t.eTruncLT.map (homOfLE (show (n : EInt) ≤ ⊤ by simp)) = t.truncLTι n := rfl

instance (i : EInt) : (t.eTruncLT.obj i).Additive := by
<<<<<<< HEAD
  induction i using WithBotTop.rec <;> constructor <;> cat_disch
=======
  induction i using WithBotTop.rec
  all_goals dsimp; infer_instance
>>>>>>> origin

/-- The functor `EInt ⥤ C ⥤ C` which sends `⊥` to `𝟭 C`,
`n : ℤ` to `t.truncGE n` and `⊤` to the zero functor. -/
noncomputable def eTruncGE : EInt ⥤ C ⥤ C where
<<<<<<< HEAD
  obj n := by
    induction n using WithBotTop.rec with
    | bot => exact 𝟭 C
    | coe a => exact t.truncGE a
    | top => exact 0
=======
  obj := WithBotTop.rec (𝟭 C) t.truncGE 0
>>>>>>> origin
  map {x y} f := by
    induction x using WithBotTop.rec with
    | bot =>
      induction y using WithBotTop.rec with
      | bot => exact 𝟙 _
      | coe b => exact t.truncGEπ b
      | top => exact 0
    | coe a =>
      induction y using WithBotTop.rec with
      | bot => exact 0
      | coe b => exact t.natTransTruncGEOfLE a b (by simpa using leOfHom f)
      | top => exact 0
    | top =>
      induction y using WithBotTop.rec with
      | bot => exact 0
      | coe b => exact 0
      | top => exact 𝟙 _
  map_id n := by induction n using WithBotTop.rec <;> simp
  map_comp {x y z} f g := by
    have f' := leOfHom f
    have g' := leOfHom g
    induction x using WithBotTop.rec <;> induction y using WithBotTop.rec <;>
      induction z using WithBotTop.rec <;> cat_disch

@[simp]
lemma eTruncGE_obj_bot :
    t.eTruncGE.obj ⊥ = 𝟭 _ := rfl

@[simp]
lemma eTruncGE_obj_top :
    t.eTruncGE.obj ⊤ = 0 := rfl

@[simp]
lemma eTruncGE_obj_coe (n : ℤ) : t.eTruncGE.obj n = t.truncGE n := rfl

instance (i : EInt) : (t.eTruncGE.obj i).Additive := by
<<<<<<< HEAD
  induction i using WithBotTop.rec <;> constructor <;> cat_disch

/-- The connecting homomorphism from `t.eTruncGE` to the
shift by `1` of `t.eTruncLT`. -/
noncomputable def eTruncGEδLT :
    t.eTruncGE ⟶ t.eTruncLT ⋙ ((Functor.whiskeringRight C C C).obj (shiftFunctor C (1 : ℤ))) where
  app a := by
    induction a using WithBotTop.rec with
    | bot => exact 0
    | coe a => exact t.truncGEδLT a
    | top => exact 0
=======
  induction i using WithBotTop.rec
  all_goals dsimp; infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The connecting homomorphism from `t.eTruncGE` to the
shift by `1` of `t.eTruncLT`. -/
noncomputable def eTruncGEδLT :
    t.eTruncGE ⟶ t.eTruncLT ⋙ ((Functor.whiskeringRight ..).obj (shiftFunctor C (1 : ℤ))) where
  app := WithBotTop.rec 0 t.truncGEδLT 0
>>>>>>> origin
  naturality {a b} hab := by
    replace hab := leOfHom hab
    induction a using WithBotTop.rec; rotate_right
    · apply (isZero_zero _).eq_of_src
    all_goals
      induction b using WithBotTop.rec <;> simp at hab <;>
        dsimp [eTruncGE, eTruncLT] <;>
        simp [t.truncGEδLT_comp_whiskerRight_natTransTruncLTOfLE]

@[simp]
lemma eTruncGEδLT_coe (n : ℤ) :
    t.eTruncGEδLT.app n = t.truncGEδLT n := rfl

/-- The natural transformation `t.eTruncLT.obj i ⟶ 𝟭 C` for all `i : EInt`. -/
noncomputable abbrev eTruncLTι (i : EInt) : t.eTruncLT.obj i ⟶ 𝟭 _ :=
  t.eTruncLT.map (homOfLE (le_top))

@[simp] lemma eTruncLT_ι_bot : t.eTruncLTι ⊥ = 0 := rfl
@[simp] lemma eTruncLT_ι_coe (n : ℤ) : t.eTruncLTι n = t.truncLTι n := rfl
@[simp] lemma eTruncLT_ι_top : t.eTruncLTι ⊤ = 𝟙 _ := rfl

@[reassoc]
lemma eTruncLTι_naturality (i : EInt) {X Y : C} (f : X ⟶ Y) :
    (t.eTruncLT.obj i).map f ≫ (t.eTruncLTι i).app Y = (t.eTruncLTι i).app X ≫ f :=
  (t.eTruncLTι i).naturality f

instance : IsIso (t.eTruncLTι ⊤) := by
  dsimp [eTruncLTι]
  infer_instance

<<<<<<< HEAD
=======
set_option backward.isDefEq.respectTransparency false in
>>>>>>> origin
@[reassoc (attr := simp)]
lemma eTruncLT_map_app_eTruncLTι_app {i j : EInt} (f : i ⟶ j) (X : C) :
    (t.eTruncLT.map f).app X ≫ (t.eTruncLTι j).app X = (t.eTruncLTι i).app X := by
  simp only [← NatTrans.comp_app, ← Functor.map_comp]
  rfl

<<<<<<< HEAD
=======
set_option backward.isDefEq.respectTransparency false in
>>>>>>> origin
@[reassoc]
lemma eTruncLT_obj_map_eTruncLTι_app (i : EInt) (X : C) :
    (t.eTruncLT.obj i).map ((t.eTruncLTι i).app X) =
    (t.eTruncLTι i).app ((t.eTruncLT.obj i).obj X) := by
<<<<<<< HEAD
  induction i using WithBotTop.rec with
  | bot => simp
  | coe n => simp [truncLT_map_truncLTι_app]
  | top => simp
=======
  induction i using WithBotTop.rec with simp [truncLT_map_truncLTι_app]
>>>>>>> origin

/-- The natural transformation `𝟭 C ⟶ t.eTruncGE.obj i` for all `i : EInt`. -/
noncomputable abbrev eTruncGEπ (i : EInt) : 𝟭 C ⟶ t.eTruncGE.obj i :=
  t.eTruncGE.map (homOfLE (bot_le))

@[simp] lemma eTruncGEπ_bot : t.eTruncGEπ ⊥ = 𝟙 _ := rfl
@[simp] lemma eTruncGEπ_coe (n : ℤ) : t.eTruncGEπ n = t.truncGEπ n := rfl
@[simp] lemma eTruncGEπ_top : t.eTruncGEπ ⊤ = 0 := rfl

@[reassoc (attr := simp)]
lemma eTruncGEπ_naturality (i : EInt) {X Y : C} (f : X ⟶ Y) :
    (t.eTruncGEπ i).app X ≫ (t.eTruncGE.obj i).map f = f ≫ (t.eTruncGEπ i).app Y :=
  ((t.eTruncGEπ i).naturality f).symm

instance : IsIso (t.eTruncGEπ ⊥) := by
  dsimp [eTruncGEπ]
  infer_instance

<<<<<<< HEAD
=======
set_option backward.isDefEq.respectTransparency false in
>>>>>>> origin
@[reassoc (attr := simp)]
lemma eTruncGEπ_app_eTruncGE_map_app {i j : EInt} (f : i ⟶ j) (X : C) :
    (t.eTruncGEπ i).app X ≫ (t.eTruncGE.map f).app X = (t.eTruncGEπ j).app X := by
  simp only [← NatTrans.comp_app, ← Functor.map_comp]
  rfl

<<<<<<< HEAD
=======
set_option backward.isDefEq.respectTransparency false in
>>>>>>> origin
@[reassoc]
lemma eTruncGE_obj_map_eTruncGEπ_app (i : EInt) (X : C) :
    (t.eTruncGE.obj i).map ((t.eTruncGEπ i).app X) =
    (t.eTruncGEπ i).app ((t.eTruncGE.obj i).obj X) := by
<<<<<<< HEAD
  induction i using WithBotTop.rec with
  | bot => simp
  | coe n => simp [truncGE_map_truncGEπ_app]
  | top => simp

=======
  induction i using WithBotTop.rec with simp [truncGE_map_truncGEπ_app]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma eTruncLT_obj_map_eTruncLTι_app_eTruncLT_map_app
    {i j : EInt} (f : i ⟶ j) (X : C) :
    (t.eTruncLT.obj i).map ((t.eTruncLTι j).app X) ≫ (t.eTruncLT.map f).app X =
      (t.eTruncLTι i).app ((t.eTruncLT.obj j).obj X) := by
  dsimp [eTruncLTι]
  rw [show homOfLE le_top = f ≫ homOfLE le_top by rfl]
  induction j using WithBotTop.rec with simp [truncLT_map_truncLTι_app]

set_option backward.isDefEq.respectTransparency false in
>>>>>>> origin
/-- The (distinguished) triangles given by the natural transformations
`t.eTruncLT.obj i ⟶ 𝟭 C ⟶ t.eTruncGE.obj i ⟶ ...` for all `i : EInt`. -/
@[simps!]
noncomputable def eTriangleLTGE : EInt ⥤ C ⥤ Triangle C where
  obj i := Triangle.functorMk (t.eTruncLTι i) (t.eTruncGEπ i) (t.eTruncGEδLT.app i)
  map f := Triangle.functorHomMk _ _ (t.eTruncLT.map f) (𝟙 _) (t.eTruncGE.map f)

lemma eTriangleLTGE_distinguished (i : EInt) (X : C) :
    (t.eTriangleLTGE.obj i).obj X ∈ distTriang _ := by
  induction i using WithBotTop.rec with
  | bot =>
    rw [Triangle.distinguished_iff_of_isZero₁ _ (Functor.zero_obj X)]
    dsimp
    infer_instance
  | coe n => exact t.triangleLTGE_distinguished n X
  | top =>
    rw [Triangle.distinguished_iff_of_isZero₃ _ (Functor.zero_obj X)]
    dsimp
    infer_instance

instance (X : C) (n : ℤ) [t.IsLE X n] (i : EInt) :
    t.IsLE ((t.eTruncLT.obj i).obj X) n := by
  induction i using WithBotTop.rec with
  | bot => exact isLE_of_isZero _ (by simp) _
  | coe _ => dsimp; infer_instance
  | top => dsimp; infer_instance

instance (X : C) (n : ℤ) [t.IsGE X n] (i : EInt) :
    t.IsGE ((t.eTruncGE.obj i).obj X) n := by
  induction i using WithBotTop.rec with
  | bot => dsimp; infer_instance
  | coe _ => dsimp; infer_instance
  | top => exact isGE_of_isZero _ (by simp) _

lemma isGE_eTruncGE_obj_obj (n : ℤ) (i : EInt) (h : n ≤ i) (X : C) :
    t.IsGE ((t.eTruncGE.obj i).obj X) n := by
  induction i using WithBotTop.rec with
  | bot => simp at h
  | coe i =>
    dsimp
    exact t.isGE_of_ge  _ _ _ (by simpa using h)
  | top => exact t.isGE_of_isZero (Functor.zero_obj _) _

lemma isLE_eTruncLT_obj_obj (n : ℤ) (i : EInt) (h : i ≤ (n + 1 :)) (X : C) :
    t.IsLE (((t.eTruncLT.obj i)).obj X) n := by
  induction i using WithBotTop.rec with
  | bot => exact t.isLE_of_isZero (by simp) _
  | coe i =>
    simp only [WithBotTop.coe_le_coe] at h
    dsimp
    exact t.isLE_of_le _ (i - 1) n (by lia)
  | top => simp at h

lemma isZero_eTruncLT_obj_obj (X : C) (n : ℤ) [t.IsGE X n] (j : EInt) (hj : j ≤ n) :
    IsZero ((t.eTruncLT.obj j).obj X) := by
  induction j using WithBotTop.rec with
  | bot => simp
  | coe j =>
    have := t.isGE_of_ge X j n (by simpa using hj)
    exact t.isZero_truncLT_obj_of_isGE _ _
  | top => simp at hj

lemma isZero_eTruncGE_obj_obj (X : C) (n : ℤ) [t.IsLE X n] (j : EInt) (hj : n < j) :
    IsZero ((t.eTruncGE.obj j).obj X) := by
  induction j using WithBotTop.rec with
  | bot => simp at hj
  | coe j =>
    simp only [WithBotTop.coe_lt_coe] at hj
    have := t.isLE_of_le X n (j - 1) (by lia)
    exact t.isZero_truncGE_obj_of_isLE (j - 1) j (by lia) _
  | top => simp

section

variable [IsTriangulated C]

lemma isIso_eTruncGE_obj_map_truncGEπ_app (a b : EInt) (h : a ≤ b) (X : C) :
    IsIso ((t.eTruncGE.obj b).map ((t.eTruncGEπ a).app X)) := by
  induction b using WithBotTop.rec with
  | bot =>
    obtain rfl : a = ⊥ := by simpa using h
    infer_instance
  | coe b =>
    induction a using WithBotTop.rec with
<<<<<<< HEAD
    | bot => dsimp; infer_instance
=======
    | bot => infer_instance
>>>>>>> origin
    | coe a => exact t.isIso_truncGE_map_truncGEπ_app b a (by simpa using h) X
    | top => simp at h
  | top => exact ⟨0, IsZero.eq_of_src (by simp) _ _, IsZero.eq_of_src (by simp) _ _⟩

lemma isIso_eTruncLT_obj_map_truncLTπ_app (a b : EInt) (h : a ≤ b) (X : C) :
    IsIso ((t.eTruncLT.obj a).map ((t.eTruncLTι b).app X)) := by
  induction a using WithBotTop.rec with
  | bot => exact ⟨0, IsZero.eq_of_src (by simp) _ _, IsZero.eq_of_src (by simp) _ _⟩
  | coe a =>
    induction b using WithBotTop.rec with
    | bot => simp at h
    | coe b =>
      exact t.isIso_truncLT_map_truncLTι_app a b (by simpa using h) X
    | top => dsimp; infer_instance
  | top =>
    obtain rfl : b = ⊤ := by simpa using h
    infer_instance

instance (a : EInt) (X : C) : IsIso ((t.eTruncLT.obj a).map ((t.eTruncLTι a).app X)) :=
  isIso_eTruncLT_obj_map_truncLTπ_app t a a (by rfl) X

<<<<<<< HEAD
=======
set_option backward.isDefEq.respectTransparency false in
>>>>>>> origin
instance (a : EInt) (X : C) : IsIso ((t.eTruncLTι a).app ((t.eTruncLT.obj a).obj X)) := by
  rw [← eTruncLT_obj_map_eTruncLTι_app]
  infer_instance

instance (X : C) (n : ℤ) [t.IsGE X n] (i : EInt) :
    t.IsGE ((t.eTruncLT.obj i).obj X) n := by
  induction i using WithBotTop.rec with
  | bot => exact isGE_of_isZero _ (by simp) _
  | coe _ => dsimp; infer_instance
  | top => dsimp; infer_instance

instance (X : C) (n : ℤ) [t.IsLE X n] (i : EInt) :
    t.IsLE ((t.eTruncGE.obj i).obj X) n := by
  induction i using WithBotTop.rec with
  | bot => dsimp; infer_instance
  | coe _ => dsimp; infer_instance
  | top => exact isLE_of_isZero _ (by simp) _

/-- The natural transformation `t.eTruncGE.obj b ⟶ t.eTruncGE.obj a ⋙ t.eTruncGE.obj b`
for all `a` and `b` in `EInt`. -/
@[simps!]
noncomputable def eTruncGEToGEGE (a b : EInt) :
    t.eTruncGE.obj b ⟶ t.eTruncGE.obj a ⋙ t.eTruncGE.obj b :=
  (Functor.leftUnitor _).inv ≫ Functor.whiskerRight (t.eTruncGEπ a) _

lemma isIso_eTruncGEIsoGEGE (a b : EInt) (hab : a ≤ b) :
    IsIso (t.eTruncGEToGEGE a b) := by
  rw [NatTrans.isIso_iff_isIso_app]
<<<<<<< HEAD
  intro X
=======
  intro
>>>>>>> origin
  simp only [Functor.comp_obj, eTruncGEToGEGE_app]
  exact t.isIso_eTruncGE_obj_map_truncGEπ_app _ _ hab _

section

variable (a b : EInt) (hab : a ≤ b)

/-- The natural isomorphism `t.eTruncGE.obj b ≅ t.eTruncGE.obj a ⋙ t.eTruncGE.obj b`
when `a` and `b` in `EInt` satisfy `a ≤ b`. -/
@[simps! hom]
noncomputable def eTruncGEIsoGEGE :
    t.eTruncGE.obj b ≅ t.eTruncGE.obj a ⋙ t.eTruncGE.obj b :=
  haveI := t.isIso_eTruncGEIsoGEGE a b hab
  asIso (t.eTruncGEToGEGE a b)

@[reassoc (attr := simp)]
lemma eTruncGEIsoGEGE_hom_inv_id_app (X : C) :
    (t.eTruncGE.obj b).map ((t.eTruncGEπ a).app X) ≫ (t.eTruncGEIsoGEGE a b hab).inv.app X =
      𝟙 _ := by
  simpa using (t.eTruncGEIsoGEGE a b hab).hom_inv_id_app X

@[reassoc (attr := simp)]
lemma eTruncGEIsoGEGE_inv_hom_id_app (X : C) :
    (t.eTruncGEIsoGEGE a b hab).inv.app X ≫ (t.eTruncGE.obj b).map ((t.eTruncGEπ a).app X) =
      𝟙 _ := by
  simpa using (t.eTruncGEIsoGEGE a b hab).inv_hom_id_app X

end

/-- The natural transformation `t.eTruncLT.obj a ⋙ t.eTruncLT.obj b ⟶ t.eTruncLT.obj b`
for all `a` and `b` in `EInt`. -/
@[simps!]
noncomputable def eTruncLTLTToLT (a b : EInt) :
    t.eTruncLT.obj a ⋙ t.eTruncLT.obj b ⟶ t.eTruncLT.obj b :=
  Functor.whiskerRight (t.eTruncLTι a) _ ≫ (Functor.leftUnitor _).hom

lemma isIso_eTruncLTLTIsoLT (a b : EInt) (hab : b ≤ a) :
    IsIso (t.eTruncLTLTToLT a b) := by
  rw [NatTrans.isIso_iff_isIso_app]
<<<<<<< HEAD
  intro X
=======
  intro
>>>>>>> origin
  simp only [Functor.comp_obj, eTruncLTLTToLT_app]
  exact t.isIso_eTruncLT_obj_map_truncLTπ_app _ _ hab _

section

variable (a b : EInt) (hab : b ≤ a)

/-- The natural isomorphism `t.eTruncLT.obj a ⋙ t.eTruncLT.obj b ⟶ t.eTruncLT.obj b`
when `a` and `b` in `EInt` satisfy `b ≤ a`. -/
@[simps! hom]
noncomputable def eTruncLTLTIsoLT :
    t.eTruncLT.obj a ⋙ t.eTruncLT.obj b ≅ t.eTruncLT.obj b :=
  haveI := t.isIso_eTruncLTLTIsoLT a b hab
  asIso (t.eTruncLTLTToLT a b)

@[reassoc]
lemma eTruncLTLTIsoLT_hom_inv_id_app (X : C) :
    (t.eTruncLT.obj b).map ((t.eTruncLTι a).app X) ≫
      (t.eTruncLTLTIsoLT a b hab).inv.app X = 𝟙 _ := by
  simpa using (t.eTruncLTLTIsoLT a b hab).hom_inv_id_app X

@[reassoc (attr := simp)]
lemma eTruncLTLTIsoLT_inv_hom_id_app (X : C) :
    (t.eTruncLTLTIsoLT a b hab).inv.app X ≫
    (t.eTruncLT.obj b).map ((t.eTruncLTι a).app X) = 𝟙 _ := by
  simpa using (t.eTruncLTLTIsoLT a b hab).inv_hom_id_app X

<<<<<<< HEAD
=======
set_option backward.isDefEq.respectTransparency false in
>>>>>>> origin
@[reassoc (attr := simp)]
lemma eTruncLTLTIsoLT_inv_hom_id_app_eTruncLT_obj (X : C) :
    (t.eTruncLTLTIsoLT a b hab).inv.app ((t.eTruncLT.obj a).obj X) ≫
      (t.eTruncLT.obj b).map ((t.eTruncLT.obj a).map ((t.eTruncLTι a).app X)) = 𝟙 _ := by
  simp [eTruncLT_obj_map_eTruncLTι_app]

end


section

variable (a b : EInt)

/-- The natural transformation from
`t.eTruncLT.obj b ⋙ t.eTruncGE.obj a ⋙ t.eTruncLT.obj b` to
`t.eTruncGE.obj a ⋙ t.eTruncLT.obj b`. (This is an isomorphism.) -/
@[simps!]
noncomputable def eTruncLTGELTSelfToLTGE :
    t.eTruncLT.obj b ⋙ t.eTruncGE.obj a ⋙ t.eTruncLT.obj b ⟶
      t.eTruncGE.obj a ⋙ t.eTruncLT.obj b :=
  Functor.whiskerRight (t.eTruncLTι b) _ ≫ (Functor.leftUnitor _).hom

/-- The natural transformation from
`t.eTruncLT.obj b ⋙ t.eTruncGE.obj a ⋙ t.eTruncLT.obj b` to
`t.eTruncLT.obj b ⋙ t.eTruncGE.obj a`. (This is an isomorphism.) -/
@[simps!]
noncomputable def eTruncLTGELTSelfToGELT :
    t.eTruncLT.obj b ⋙ t.eTruncGE.obj a ⋙ t.eTruncLT.obj b ⟶
      t.eTruncLT.obj b ⋙ t.eTruncGE.obj a :=
  (Functor.associator _ _ _).inv ≫ Functor.whiskerLeft _ (t.eTruncLTι b) ≫
    (Functor.rightUnitor _).hom

<<<<<<< HEAD
=======
set_option backward.isDefEq.respectTransparency false in
>>>>>>> origin
instance : IsIso (t.eTruncLTGELTSelfToLTGE a b) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  induction b using WithBotTop.rec with
  | bot => simp [isIsoZero_iff_source_target_isZero]
  | coe b =>
    induction a using WithBotTop.rec with
    | bot => simpa using inferInstanceAs (IsIso ((t.truncLT b).map ((t.truncLTι b).app X)))
    | coe a =>
      simp only [eTruncLT_obj_coe, eTruncGE_obj_coe, Functor.comp_obj, eTruncLTGELTSelfToLTGE_app,
        eTruncLT_map_eq_truncLTι]
      infer_instance
    | top =>
      simp only [eTruncLT_obj_coe, eTruncGE_obj_top, Functor.comp_obj, eTruncLTGELTSelfToLTGE_app,
        eTruncLT_map_eq_truncLTι, zero_map, Functor.map_zero, isIsoZero_iff_source_target_isZero]
      constructor
      all_goals exact Functor.map_isZero _ (Functor.zero_obj _)
  | top => simpa using inferInstanceAs (IsIso (𝟙 _))

variable (b : EInt) (X : C)

<<<<<<< HEAD
=======
set_option backward.isDefEq.respectTransparency false in
>>>>>>> origin
instance : IsIso (t.eTruncLTGELTSelfToGELT a b) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  induction a using WithBotTop.rec with
  | bot => simpa using inferInstanceAs (IsIso ((t.eTruncLTι b).app ((t.eTruncLT.obj b).obj X)))
  | coe a =>
    induction b using WithBotTop.rec with
    | bot => simpa [isIsoZero_iff_source_target_isZero] using
        (t.eTruncGE.obj a).map_isZero (Functor.zero_obj _)
    | coe b =>
      simp only [eTruncLT_obj_coe, eTruncGE_obj_coe, Functor.comp_obj, eTruncLTGELTSelfToGELT_app,
        eTruncLT_map_eq_truncLTι]
      infer_instance
    | top => simpa using inferInstanceAs (IsIso (𝟙 _))
  | top =>
    exact ⟨0, ((t.eTruncLT.obj b).map_isZero (by simp)).eq_of_src _ _,
      IsZero.eq_of_src (by simp) _ _⟩

end

/-- The commutation natural isomorphism
`t.eTruncGE.obj a ⋙ t.eTruncLT.obj b ≅ t.eTruncLT.obj b ⋙ t.eTruncGE.obj a`
for all `a` and `b` in `EInt`. -/
<<<<<<< HEAD
noncomputable def eTruncLTGEIsoLEGT (a b : EInt) :
=======
noncomputable def eTruncLTGEIsoGELT (a b : EInt) :
>>>>>>> origin
    t.eTruncGE.obj a ⋙ t.eTruncLT.obj b ≅ t.eTruncLT.obj b ⋙ t.eTruncGE.obj a :=
  (asIso (t.eTruncLTGELTSelfToLTGE a b)).symm ≪≫ asIso (t.eTruncLTGELTSelfToGELT a b)

@[reassoc (attr := simp)]
<<<<<<< HEAD
lemma eTruncLTGEIsoLEGT_hom_naturality (a b : EInt) {X Y : C} (f : X ⟶ Y) :
    (t.eTruncLT.obj b).map ((t.eTruncGE.obj a).map f) ≫ (t.eTruncLTGEIsoLEGT a b).hom.app Y =
      (t.eTruncLTGEIsoLEGT a b).hom.app X ≫ (t.eTruncGE.obj a).map ((t.eTruncLT.obj b).map f) :=
  (t.eTruncLTGEIsoLEGT a b).hom.naturality f

@[reassoc]
lemma eTruncLTGEIsoLEGT_hom_app_fac (a b : EInt) (X : C) :
    (t.eTruncLT.obj b).map ((t.eTruncGE.obj a).map ((t.eTruncLTι b).app X)) ≫
      (t.eTruncLTGEIsoLEGT a b).hom.app X =
    (t.eTruncLTι b).app ((t.eTruncGE.obj a).obj ((t.eTruncLT.obj b).obj X)):= by
  simp [eTruncLTGEIsoLEGT]

@[reassoc (attr := simp)]
lemma eTruncLTGEIsoLEGT_hom_app_fac' (a b : EInt) (X : C) :
    (t.eTruncLTGEIsoLEGT a b).hom.app X ≫ (t.eTruncGE.obj a).map ((t.eTruncLTι b).app X) =
      (t.eTruncLTι b).app ((t.eTruncGE.obj a).obj X) := by
  simp [eTruncLTGEIsoLEGT]

open ComposableArrows in
@[reassoc]
lemma eTruncLTGEIsoLEGT_naturality_app (a b : EInt) (hab : a ≤ b)
    (a' b' : EInt) (hab' : a' ≤ b') (φ : mk₁ (homOfLE hab) ⟶ mk₁ (homOfLE hab')) (X : C) :
      (t.eTruncLT.map (φ.app 1)).app ((t.eTruncGE.obj a).obj X) ≫
        (t.eTruncLT.obj b').map ((t.eTruncGE.map (φ.app 0)).app X) ≫
        (t.eTruncLTGEIsoLEGT a' b').hom.app X =
    (t.eTruncLTGEIsoLEGT a b).hom.app X ≫ (t.eTruncGE.map (φ.app 0)).app _ ≫
      (t.eTruncGE.obj a').map ((t.eTruncLT.map (φ.app 1)).app X) := by
  rw [← cancel_epi ((t.eTruncLTGELTSelfToLTGE a b).app X)]
  dsimp
  rw [eTruncLTGELTSelfToLTGE_app, eTruncLTGEIsoLEGT_hom_app_fac_assoc,
    NatTrans.naturality_assoc, ← Functor.map_comp_assoc, NatTrans.naturality,
    Functor.map_comp_assoc, ← t.eTruncLT_map_app_eTruncLTι_app (φ.app 1) X,
    Functor.map_comp, Functor.map_comp, Category.assoc,
    t.eTruncLTGEIsoLEGT_hom_app_fac]
  simp
=======
lemma eTruncLTGEIsoGELT_hom_naturality (a b : EInt) {X Y : C} (f : X ⟶ Y) :
    (t.eTruncLT.obj b).map ((t.eTruncGE.obj a).map f) ≫ (t.eTruncLTGEIsoGELT a b).hom.app Y =
      (t.eTruncLTGEIsoGELT a b).hom.app X ≫ (t.eTruncGE.obj a).map ((t.eTruncLT.obj b).map f) :=
  (t.eTruncLTGEIsoGELT a b).hom.naturality f

@[reassoc]
lemma eTruncLTGEIsoGELT_hom_app_fac (a b : EInt) (X : C) :
    (t.eTruncLT.obj b).map ((t.eTruncGE.obj a).map ((t.eTruncLTι b).app X)) ≫
      (t.eTruncLTGEIsoGELT a b).hom.app X =
    (t.eTruncLTι b).app ((t.eTruncGE.obj a).obj ((t.eTruncLT.obj b).obj X)):= by
  simp [eTruncLTGEIsoGELT]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma eTruncLTGEIsoGELT_hom_app_fac' (a b : EInt) (X : C) :
    (t.eTruncLTGEIsoGELT a b).hom.app X ≫ (t.eTruncGE.obj a).map ((t.eTruncLTι b).app X) =
      (t.eTruncLTι b).app ((t.eTruncGE.obj a).obj X) := by
  simp [eTruncLTGEIsoGELT]

set_option backward.isDefEq.respectTransparency false in
open ComposableArrows in
@[reassoc]
lemma eTruncLTGEIsoGELT_naturality_app (a b : EInt) (hab : a ≤ b)
    (a' b' : EInt) (hab' : a' ≤ b') (φ : mk₁ (homOfLE hab) ⟶ mk₁ (homOfLE hab')) (X : C) :
      (t.eTruncLT.map (φ.app 1)).app ((t.eTruncGE.obj a).obj X) ≫
        (t.eTruncLT.obj b').map ((t.eTruncGE.map (φ.app 0)).app X) ≫
        (t.eTruncLTGEIsoGELT a' b').hom.app X =
    (t.eTruncLTGEIsoGELT a b).hom.app X ≫ (t.eTruncGE.map (φ.app 0)).app _ ≫
      (t.eTruncGE.obj a').map ((t.eTruncLT.map (φ.app 1)).app X) := by
  dsimp
  rw [← cancel_epi ((t.eTruncLTGELTSelfToLTGE a b).app X), eTruncLTGELTSelfToLTGE_app,
    eTruncLTGEIsoGELT_hom_app_fac_assoc, NatTrans.naturality_assoc, ← Functor.map_comp_assoc,
    NatTrans.naturality, Functor.map_comp_assoc, ← t.eTruncLT_map_app_eTruncLTι_app (φ.app 1) X]
  simp [↓Functor.map_comp, t.eTruncLTGEIsoGELT_hom_app_fac]
>>>>>>> origin

end

end TStructure

end Triangulated

end CategoryTheory
