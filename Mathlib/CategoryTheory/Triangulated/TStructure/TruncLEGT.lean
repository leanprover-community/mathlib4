/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# Truncations for a t-structure

Let `t` be a t-structure on a (pre)triangulated category `C`.
In this file, for any `n : ℤ`, we introduce the truncation functors
`t.truncLE n : C ⥤ C` and `t.truncGT n : C ⥤ C`, as variants of the functors
`t.truncLT n : C ⥤ C` and `t.truncGE n : C ⥤ C` introduced in the file
`Mathlib/CategoryTheory/Triangulated/TStucture/TruncLTGE.lean`.

-/

@[expose] public section

namespace CategoryTheory

open Limits Pretriangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Triangulated

namespace TStructure

variable (t : TStructure C)

/-- Given a t-structure `t` on a pretriangulated category `C` and `n : ℤ`, this
is the `≤ n`-truncation functor. See also the natural transformation `truncLEι`. -/
noncomputable def truncLE (n : ℤ) : C ⥤ C := t.truncLT (n + 1)

instance (n : ℤ) : (t.truncLE n).Additive := by
  dsimp only [truncLE]
  infer_instance

lemma isLE_truncLE_obj (X : C) (a b : ℤ) (hn : a ≤ b := by lia) :
    t.IsLE ((t.truncLE a).obj X) b :=
  t.isLE_truncLT_obj ..

instance (n : ℤ) (X : C) : t.IsLE ((t.truncLE n).obj X) n :=
  t.isLE_truncLE_obj ..

/-- Given a t-structure `t` on a pretriangulated category `C` and `n : ℤ`, this
is the `> n`-truncation functor. See also the natural transformation `truncGTπ`. -/
noncomputable def truncGT (n : ℤ) : C ⥤ C := t.truncGE (n + 1)

instance (n : ℤ) : (t.truncGT n).Additive := by
  dsimp only [truncGT]
  infer_instance

lemma isGE_truncGT_obj (X : C) (a b : ℤ) (hn : b ≤ a + 1 := by lia) :
    t.IsGE ((t.truncGT a).obj X) b :=
  t.isGE_truncGE_obj ..

instance (n : ℤ) (X : C) : t.IsGE ((t.truncGT n).obj X) (n + 1) :=
  t.isGE_truncGT_obj ..

instance (n : ℤ) (X : C) : t.IsGE ((t.truncGT (n - 1)).obj X) n :=
  t.isGE_truncGT_obj ..

/-- The isomorphism `t.truncLE a ≅ t.truncLT b` when `a + 1 = b`. -/
noncomputable def truncLEIsoTruncLT (a b : ℤ) (h : a + 1 = b) :
    t.truncLE a ≅ t.truncLT b :=
  eqToIso (by rw [← h]; rfl)

/-- The isomorphism `t.truncGT a ≅ t.truncGE b` when `a + 1 = b`. -/
noncomputable def truncGTIsoTruncGE (a b : ℤ) (h : a + 1 = b) :
    t.truncGT a ≅ t.truncGE b :=
  eqToIso (by rw [← h]; rfl)

/-- The natural transformation `t.truncLE n ⟶ 𝟭 C` when `t` is a t-structure
on a category `C` and `n : ℤ`. -/
noncomputable def truncLEι (n : ℤ) : t.truncLE n ⟶ 𝟭 C := t.truncLTι (n + 1)

@[reassoc (attr := simp)]
lemma truncLEIsoTruncLT_hom_ι (a b : ℤ) (h : a + 1 = b) :
    (t.truncLEIsoTruncLT a b h).hom ≫ t.truncLTι b = t.truncLEι a := by
  subst h
  dsimp [truncLEIsoTruncLT, truncLEι]
  rw [Category.id_comp]

@[reassoc (attr := simp)]
lemma truncLEIsoTruncLT_hom_ι_app (a b : ℤ) (h : a + 1 = b) (X : C) :
    (t.truncLEIsoTruncLT a b h).hom.app X ≫ (t.truncLTι b).app X = (t.truncLEι a).app X :=
  congr_app (t.truncLEIsoTruncLT_hom_ι a b h) X

@[reassoc (attr := simp)]
lemma truncLEIsoTruncLT_inv_ι (a b : ℤ) (h : a + 1 = b) :
    (t.truncLEIsoTruncLT a b h).inv ≫ t.truncLEι a = t.truncLTι b := by
  subst h
  dsimp [truncLEIsoTruncLT, truncLEι, truncLE]
  rw [Category.id_comp]

@[reassoc (attr := simp)]
lemma truncLEIsoTruncLT_inv_ι_app (a b : ℤ) (h : a + 1 = b) (X : C) :
    (t.truncLEIsoTruncLT a b h).inv.app X ≫ (t.truncLEι a).app X = (t.truncLTι b).app X :=
  congr_app (t.truncLEIsoTruncLT_inv_ι a b h) X

/-- The natural transformation `t.truncLE a ⟶ t.truncLE b` when `a ≤ b`. -/
noncomputable def natTransTruncLEOfLE (a b : ℤ) (h : a ≤ b) :
    t.truncLE a ⟶ t.truncLE b :=
  t.natTransTruncLTOfLE (a+1) (b+1) (by lia)

@[reassoc (attr := simp)]
lemma natTransTruncLEOfLE_ι_app (n₀ n₁ : ℤ) (h : n₀ ≤ n₁) (X : C) :
    (t.natTransTruncLEOfLE n₀ n₁ h).app X ≫ (t.truncLEι n₁).app X =
      (t.truncLEι n₀).app X :=
  t.natTransTruncLTOfLE_ι_app _ _ _ _

@[reassoc (attr := simp)]
lemma natTransTruncLEOfLE_ι (a b : ℤ) (h : a ≤ b) :
    t.natTransTruncLEOfLE a b h ≫ t.truncLEι b = t.truncLEι a := by cat_disch

@[simp]
lemma natTransTruncLEOfLE_refl (a : ℤ) :
    t.natTransTruncLEOfLE a a (by rfl) = 𝟙 _ :=
  t.natTransTruncLTOfLE_refl _

@[simp]
lemma natTransTruncLEOfLE_trans (a b c : ℤ) (hab : a ≤ b) (hbc : b ≤ c) :
    t.natTransTruncLEOfLE a b hab ≫ t.natTransTruncLEOfLE b c hbc =
      t.natTransTruncLEOfLE a c (hab.trans hbc) :=
  t.natTransTruncLTOfLE_trans _ _ _ _ _

lemma natTransTruncLEOfLE_refl_app (a : ℤ) (X : C) :
    (t.natTransTruncLEOfLE a a (by rfl)).app X = 𝟙 _ :=
  congr_app (t.natTransTruncLEOfLE_refl a) X

@[reassoc (attr := simp)]
lemma natTransTruncLEOfLE_trans_app (a b c : ℤ) (hab : a ≤ b) (hbc : b ≤ c) (X : C) :
    (t.natTransTruncLEOfLE a b hab).app X ≫ (t.natTransTruncLEOfLE b c hbc).app X =
      (t.natTransTruncLEOfLE a c (hab.trans hbc)).app X :=
  congr_app (t.natTransTruncLEOfLE_trans a b c hab hbc) X

/-- The natural transformation `𝟭 C ⟶ t.truncGT n` when `t` is a t-structure
on a category `C` and `n : ℤ`. -/
noncomputable def truncGTπ (n : ℤ) : 𝟭 C ⟶ t.truncGT n := t.truncGEπ (n + 1)

@[reassoc (attr := simp)]
lemma π_truncGTIsoTruncGE_hom (a b : ℤ) (h : a + 1 = b) :
    t.truncGTπ a ≫ (t.truncGTIsoTruncGE a b h).hom = t.truncGEπ b := by
  subst h
  dsimp [truncGTIsoTruncGE, truncGTπ]
  rw [Category.comp_id]

@[reassoc (attr := simp)]
lemma π_truncGTIsoTruncGE_hom_ι_app (a b : ℤ) (h : a + 1 = b) (X : C) :
    (t.truncGTπ a).app X ≫ (t.truncGTIsoTruncGE a b h).hom.app X = (t.truncGEπ b).app X :=
  congr_app (t.π_truncGTIsoTruncGE_hom a b h) X

@[reassoc (attr := simp)]
lemma π_truncGTIsoTruncGE_inv (a b : ℤ) (h : a + 1 = b) :
    t.truncGEπ b ≫ (t.truncGTIsoTruncGE a b h).inv = t.truncGTπ a := by
  subst h
  dsimp [truncGTIsoTruncGE, truncGTπ, truncGT]
  rw [Category.comp_id]

@[reassoc (attr := simp)]
lemma π_truncGTIsoTruncGE_inv_ι_app (a b : ℤ) (h : a + 1 = b) (X : C) :
    (t.truncGEπ b).app X ≫ (t.truncGTIsoTruncGE a b h).inv.app X = (t.truncGTπ a).app X :=
  congr_app (t.π_truncGTIsoTruncGE_inv a b h) X

/-- The connecting homomorphism `(t.truncGE b).obj X ⟶ ((t.truncLE a).obj X)⟦1⟧`
when `a + 1 = b`, as a natural transformation. -/
noncomputable def truncGEδLE (a b : ℤ) (h : a + 1 = b) :
    t.truncGE b ⟶ t.truncLE a ⋙ shiftFunctor C (1 : ℤ) :=
  t.truncGEδLT b ≫ Functor.whiskerRight (t.truncLEIsoTruncLT a b h).inv (shiftFunctor C (1 : ℤ))

/-- The distinguished triangle `(t.truncLE a).obj A ⟶ A ⟶ (t.truncGE b).obj A ⟶ ...`
as a functor `C ⥤ Triangle C` when `t` is a `t`-structure on a pretriangulated
category `C` and `a + 1 = b`. -/
@[simps!]
noncomputable def triangleLEGE (a b : ℤ) (h : a + 1 = b) : C ⥤ Triangle C :=
  Triangle.functorMk (t.truncLEι a) (t.truncGEπ b) (t.truncGEδLE a b h)

/-- The natural isomorphism of triangles `t.triangleLEGE a b h ≅ t.triangleLTGE b`
when `a + 1 = b`. -/
noncomputable def triangleLEGEIsoTriangleLTGE (a b : ℤ) (h : a + 1 = b) :
    t.triangleLEGE a b h ≅ t.triangleLTGE b := by
  refine Triangle.functorIsoMk _ _ (t.truncLEIsoTruncLT a b h) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · cat_disch
  · cat_disch
  · ext
    dsimp [truncGEδLE]
    simp only [Category.assoc, Category.id_comp, ← Functor.map_comp,
      Iso.inv_hom_id_app, Functor.map_id, Category.comp_id]

lemma triangleLEGE_distinguished (a b : ℤ) (h : a + 1 = b) (X : C) :
    (t.triangleLEGE a b h).obj X ∈ distTriang C :=
  isomorphic_distinguished _ (t.triangleLTGE_distinguished b X) _
    ((t.triangleLEGEIsoTriangleLTGE a b h).app X)

/-- The connecting homomorphism `(t.truncGT n).obj X ⟶ ((t.truncLE n).obj X)⟦1⟧`
for `n : ℤ`, as a natural transformation. -/
noncomputable def truncGTδLE (n : ℤ) :
    t.truncGT n ⟶ t.truncLE n ⋙ shiftFunctor C (1 : ℤ) :=
  (t.truncGTIsoTruncGE n (n+1) rfl).hom ≫ t.truncGEδLE n (n + 1) (by lia)

/-- The distinguished triangle `(t.truncLE n).obj A ⟶ A ⟶ (t.truncGT n).obj A ⟶ ...`
as a functor `C ⥤ Triangle C` when `t` is a t-structure on a pretriangulated
category `C` and `n : ℤ`. -/
@[simps!]
noncomputable def triangleLEGT (n : ℤ) : C ⥤ Triangle C :=
  Triangle.functorMk (t.truncLEι n) (t.truncGTπ n) (t.truncGTδLE n)

/-- The natural isomorphism `t.triangleLEGT a ≅ t.triangleLEGE a b h`
when `a + 1 = b`. -/
noncomputable def triangleLEGTIsoTriangleLEGE (a b : ℤ) (h : a + 1 = b) :
    t.triangleLEGT a ≅ t.triangleLEGE a b h :=
  Triangle.functorIsoMk _ _ (Iso.refl _) (Iso.refl _) (t.truncGTIsoTruncGE a b h)
    (by cat_disch) (by cat_disch) (by
      ext
      dsimp [truncGTδLE]
      subst h
      simp only [Functor.map_id, Category.comp_id])

lemma triangleLEGT_distinguished (n : ℤ) (X : C) :
    (t.triangleLEGT n).obj X ∈ distTriang C :=
  isomorphic_distinguished _ (t.triangleLEGE_distinguished n (n+1) rfl X) _
    ((t.triangleLEGTIsoTriangleLEGE n (n+1) rfl).app X)

lemma isLE_iff_isIso_truncLEι_app (n : ℤ) (X : C) :
    t.IsLE X n ↔ IsIso ((t.truncLEι n).app X) :=
  t.isLE_iff_isIso_truncLTι_app n (n + 1) rfl X

lemma isGE_iff_isIso_truncGTπ_app (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) (X : C) :
    t.IsGE X n₁ ↔ IsIso ((t.truncGTπ n₀).app X) := by
  rw [t.isGE_iff_isIso_truncGEπ_app n₁ X]
  exact (MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (Arrow.isoMk (Iso.refl _) ((t.truncGTIsoTruncGE _ _ hn₁).symm.app X))

instance (X : C) (n : ℤ) [t.IsLE X n] : IsIso ((t.truncLEι n).app X) := by
  rw [← isLE_iff_isIso_truncLEι_app ]
  infer_instance

lemma isLE_iff_isZero_truncGT_obj (n : ℤ) (X : C) :
    t.IsLE X n ↔ IsZero ((t.truncGT n).obj X) := by
  rw [t.isLE_iff_isIso_truncLEι_app n X]
  exact (Triangle.isZero₃_iff_isIso₁ _ (t.triangleLEGT_distinguished n X)).symm

lemma isGE_iff_isZero_truncLE_obj (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) :
    t.IsGE X n₁ ↔ IsZero ((t.truncLE n₀).obj X) := by
  rw [t.isGE_iff_isIso_truncGEπ_app n₁ X]
  exact (Triangle.isZero₁_iff_isIso₂ _ (t.triangleLEGE_distinguished n₀ n₁ h X)).symm

lemma isZero_truncLE_obj_of_isGE (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) [t.IsGE X n₁] :
    IsZero ((t.truncLE n₀).obj X) := by
  rw [← t.isGE_iff_isZero_truncLE_obj _ _ h X]
  infer_instance

lemma to_truncLE_obj_ext {n : ℤ} {Y : C} {X : C}
    {f₁ f₂ : Y ⟶ (t.truncLE n).obj X} (h : f₁ ≫ (t.truncLEι n).app X = f₂ ≫ (t.truncLEι n).app X)
    [t.IsLE Y n] :
    f₁ = f₂ := by
  have : t.IsLE Y (n + 1 - 1) := by simpa
  rw [← cancel_mono ((t.truncLEIsoTruncLT n (n + 1) rfl).hom.app _)]
  exact t.to_truncLT_obj_ext (by simpa)

section

variable {X Y : C} (f : X ⟶ Y) (n : ℤ) [t.IsLE X n]

lemma liftTruncLE_aux :
    ∃ (f' : X ⟶ (t.truncLE n).obj Y), f = f' ≫ (t.truncLEι n).app Y :=
  Triangle.coyoneda_exact₂ _ (t.triangleLEGT_distinguished n Y) f
    (t.zero_of_isLE_of_isGE  _ n (n + 1) (by lia) inferInstance (by dsimp; infer_instance))

/-- Constructor for morphisms to `(t.truncLE n).obj Y`. -/
noncomputable def liftTruncLE :
    X ⟶ (t.truncLE n).obj Y := (t.liftTruncLE_aux f n).choose

@[reassoc (attr := simp)]
lemma liftTruncLE_ι :
    t.liftTruncLE f n ≫ (t.truncLEι n).app Y = f :=
  (t.liftTruncLE_aux f n).choose_spec.symm

end

section

variable {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) [t.IsGE Y n₁]

include h in
lemma descTruncGT_aux :
  ∃ (f' : (t.truncGT n₀).obj X ⟶ Y), f = (t.truncGTπ n₀).app X ≫ f' :=
  Triangle.yoneda_exact₂ _ (t.triangleLEGT_distinguished n₀ X) f
    (t.zero_of_isLE_of_isGE _ n₀ n₁ (by lia) (by dsimp; infer_instance) inferInstance)

/-- Constructor for morphisms from `(t.truncGT n₀).obj Y`. -/
noncomputable def descTruncGT :
    (t.truncGT n₀).obj X ⟶ Y :=
  (t.descTruncGT_aux f n₀ n₁ h).choose

@[reassoc (attr := simp)]
lemma π_descTruncGT :
    (t.truncGTπ n₀).app X ≫ t.descTruncGT f n₀ n₁ h = f :=
  (t.descTruncGT_aux f n₀ n₁ h).choose_spec.symm

end

lemma isIso_truncLE_map_iff {X Y : C} (f : X ⟶ Y) (a b : ℤ) (h : a + 1 = b) :
    IsIso ((t.truncLE a).map f) ↔
      ∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ ((t.truncLE a).obj X)⟦1⟧)
        (_ : Triangle.mk ((t.truncLEι a).app X ≫ f) g h ∈ distTriang _), t.IsGE Z b := by
  subst h
  apply isIso_truncLT_map_iff

lemma isIso_truncGT_map_iff {Y Z : C} (g : Y ⟶ Z) (n : ℤ) :
    IsIso ((t.truncGT n).map g) ↔
      ∃ (X : C) (f : X ⟶ Y) (h : ((t.truncGT n).obj Z) ⟶ X⟦(1 : ℤ)⟧)
        (_ : Triangle.mk f (g ≫ (t.truncGTπ n).app Z) h ∈ distTriang _), t.IsLE X n :=
  t.isIso_truncGE_map_iff g n (n + 1) rfl

instance (X : C) (a b : ℤ) [t.IsLE X b] : t.IsLE ((t.truncLE a).obj X) b := by
  dsimp [truncLE]
  infer_instance

instance (X : C) (a b : ℤ) [t.IsGE X a] : t.IsGE ((t.truncGT b).obj X) a := by
  dsimp [truncGT]
  infer_instance

/-- The composition `t.truncGE a ⋙ t.truncGE b`. -/
noncomputable abbrev truncLEGE (a b : ℤ) : C ⥤ C := t.truncGE a ⋙ t.truncLE b

/-- The composition `t.truncLE b ⋙ t.truncGE a`. -/
noncomputable abbrev truncGELE (a b : ℤ) : C ⥤ C := t.truncLE b ⋙ t.truncGE a

instance (X : C) (a b : ℤ) : t.IsGE ((t.truncGELE a b).obj X) a := by
  dsimp; infer_instance

/-- The natural isomorphism `t.truncGELE a b ≅ t.truncGELT a b'` when `b + 1 = b'`. -/
noncomputable def truncGELEIsoTruncGELT (a b b' : ℤ) (hb' : b + 1 = b') :
    t.truncGELE a b ≅ t.truncGELT a b' :=
  Functor.isoWhiskerRight (t.truncLEIsoTruncLT b b' hb') _

section

variable [IsTriangulated C]

lemma isIso₁_truncLE_map_of_isGE (T : Triangle C) (hT : T ∈ distTriang C)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (h₃ : t.IsGE T.obj₃ n₁) :
    IsIso ((t.truncLE n₀).map T.mor₁) := by
  subst h
  exact t.isIso₁_truncLT_map_of_isGE _ hT _ h₃

lemma isIso₂_truncGT_map_of_isLE (T : Triangle C) (hT : T ∈ distTriang C)
    (n₀ : ℤ) (h₁ : t.IsLE T.obj₁ n₀) :
    IsIso ((t.truncGT n₀).map T.mor₂) :=
  t.isIso₂_truncGE_map_of_isLE _ hT _ _ rfl h₁

instance (X : C) (a b : ℤ) [t.IsGE X a] :
    t.IsGE ((t.truncLE b).obj X) a := by
  dsimp [truncLE]; infer_instance

instance (X : C) (a b : ℤ) [t.IsLE X b] :
    t.IsLE ((t.truncGT a).obj X) b := by
  dsimp [truncGT]; infer_instance

instance (X : C) (a b : ℤ) [t.IsGE X a] :
    t.IsGE ((t.truncLE b).obj X) a := by
  dsimp [truncLE]; infer_instance

instance (X : C) (a b : ℤ) :
    t.IsLE ((t.truncGELE a b).obj X) b := by
  dsimp; infer_instance

lemma isIso_truncLE_map_truncLEι_app (a b : ℤ) (h : a ≤ b) (X : C) :
    IsIso ((t.truncLE a).map ((t.truncLEι b).app X)) :=
  t.isIso_truncLT_map_truncLTι_app _ _ (by lia) _

lemma isIso_truncGT_map_truncGTπ_app (a b : ℤ) (h : b ≤ a) (X : C) :
    IsIso ((t.truncGT a).map ((t.truncGTπ b).app X)) :=
  isIso_truncGE_map_truncGEπ_app _ _ _ (by lia) _

instance (X : C) (n : ℤ) : IsIso ((t.truncLE n).map ((t.truncLEι n).app X)) :=
  t.isIso_truncLE_map_truncLEι_app _ _ (by lia) _

/-- The natural isomorphism `t.truncGELE a b ≅ t.truncLEGE a b`. -/
noncomputable def truncGELEIsoLEGE (a b : ℤ) : t.truncGELE a b ≅ t.truncLEGE a b :=
  t.truncGELTIsoLTGE a (b + 1)

end

end TStructure

end Triangulated

end CategoryTheory
