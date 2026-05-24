/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.Basic
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Truncations for a t-structure

Let `t` be a t-structure on a (pre)triangulated category `C`.
In this file, for any `n : ℤ`, we construct truncation functors `t.truncLT n : C ⥤ C`,
`t.truncGE n : C ⥤ C` and natural transformations `t.truncLTι n : t.truncLT n ⟶ 𝟭 C`,
`t.truncGEπ n : 𝟭 C ⟶ t.truncGE n` and
`t.truncGEδLT n : t.truncGE n ⟶ t.truncLT n ⋙ shiftFunctor C (1 : ℤ)` which are
part of a distinguished triangle
`(t.truncLT n).obj X ⟶ X ⟶ (t.truncGE n).obj X ⟶ ((t.truncLT n).obj X)⟦1⟧` for any `X : C`,
with `(t.truncLT n).obj X < n` and `(t.truncGE n).obj X ≥ n`.

We obtain various properties of these truncation functors.
Variants `truncGT` and `truncLE` are introduced in the file
`Mathlib/CategoryTheory/Triangulated/TStucture/TruncLEGT.lean`.
Extensions to indices in `EInt` instead of `ℤ` are introduced in the file
`Mathlib/CategoryTheory/Triangulated/TStucture/ETrunc.lean`.
The spectral object attached to an object `X : C` is constructed in the file
`Mathlib/CategoryTheory/Triangulated/TStucture/SpectralObject.lean`.

-/

universe v u

namespace CategoryTheory

open Limits Pretriangulated ZeroObject

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Triangulated

namespace TStructure

variable (t : TStructure C)

set_option backward.isDefEq.respectTransparency false in
/-- Two morphisms `T ⟶ T'` between distinguished triangles must coincide when
they coincide on the middle object, and there are integers `a ≤ b` such that
for a t-structure, we have `T.obj₁ ≤ a` and `T'.obj₃ ≥ b`. -/
public lemma triangle_map_ext {T T' : Triangle C} {f₁ f₂ : T ⟶ T'}
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C) (a b : ℤ)
    (h₀ : t.IsLE T.obj₁ a) (h₁ : t.IsGE T'.obj₃ b)
    (H : f₁.hom₂ = f₂.hom₂ := by cat_disch)
    (hab : a ≤ b := by lia) : f₁ = f₂ := by
  suffices ∀ (f : T ⟶ T'), f.hom₂ = 0 → f = 0 by rw [← sub_eq_zero]; cat_disch
  intro f hf
  ext
  · obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _ hT')
      f.hom₁ (by simp [← f.comm₁, hf])
    simp [hg, t.zero_of_isLE_of_isGE g a (b + 1) (by lia)
      h₀ (t.isGE_shift _ b (-1) (b + 1))]
  · simp [hf]
  · obtain ⟨g, hg⟩ := T.yoneda_exact₃ hT f.hom₃ (by cat_disch)
    simp [hg, t.zero_of_isLE_of_isGE g (a - 1) b (by lia)
      (t.isLE_shift _ a 1 (a - 1)) inferInstance]

/-- If `a < b`, then a morphism `T.obj₂ ⟶ T'.obj₂` extends to a morphism `T ⟶ T'`
of distinguished triangles when for a t-structure `T.obj₁ ≤ a` and `T'.obj₃ ≥ b`. -/
public lemma triangle_map_exists {T T' : Triangle C}
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C)
    (φ : T.obj₂ ⟶ T'.obj₂) (a b : ℤ)
    (h₀ : t.IsLE T.obj₁ a) (h₁' : t.IsGE T'.obj₃ b) (h : a < b := by lia) :
    ∃ (f : T ⟶ T'), f.hom₂ = φ := by
  obtain ⟨a, comm₁⟩ := T'.coyoneda_exact₂ hT' (T.mor₁ ≫ φ) (t.zero _ a b)
  obtain ⟨c, comm₂, comm₃⟩ := complete_distinguished_triangle_morphism _ _ hT hT' a φ comm₁
  exact ⟨{ hom₁ := a, hom₂ := φ, hom₃ := c }, rfl⟩

/-- If `a < b`, then an isomorphism `T.obj₂ ≅ T'.obj₂` extends to an isomorphism `T ≅ T'`
of distinguished triangles when for a t-structure, both `T.obj₁` and `T'.obj₁` are `≤ a` and
both `T.obj₃` and `T'.obj₃` are `≥ b`. -/
public lemma triangle_iso_exists {T T' : Triangle C}
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C) (e : T.obj₂ ≅ T'.obj₂)
    (a b : ℤ) (h₀ : t.IsLE T.obj₁ a) (h₁ : t.IsGE T.obj₃ b)
    (h₀' : t.IsLE T'.obj₁ a) (h₁' : t.IsGE T'.obj₃ b) (h : a < b := by lia) :
    ∃ (e' : T ≅ T'), e'.hom.hom₂ = e.hom := by
  obtain ⟨hom, hhom⟩ := triangle_map_exists t hT hT' e.hom _ _ h₀ h₁'
  obtain ⟨inv, _⟩ := triangle_map_exists t hT' hT e.inv _ _ h₀' h₁
  exact
    ⟨{hom := hom
      inv := inv
      hom_inv_id := triangle_map_ext t hT hT a b h₀ h₁
      inv_hom_id := triangle_map_ext t hT' hT' a b h₀' h₁' }, hhom⟩

namespace TruncAux
/-! The private definitions in the namespace `TStructure.TruncAux` are part of the
implementation of the truncation functors `truncLT`, `truncGE` and the
distinguished triangles they fit in. -/

variable (n : ℤ) (X : C)

/-- Given a t-structure `t` on `C`, `X : C` and `n : ℤ`, this is a distinguished
triangle `obj₁ ⟶ X ⟶ obj₃ ⟶ obj₁⟦1⟧` where `obj₁` is `< n` and `obj₃` is `≥ n`.
(This should not be used directly: use `truncLT` and `truncGE` instead.) -/
@[simps! obj₂]
noncomputable def triangle : Triangle C :=
  Triangle.mk
    (t.exists_triangle X (n - 1) n
      (by lia)).choose_spec.choose_spec.choose_spec.choose_spec.choose
    (t.exists_triangle X (n - 1) n
      (by lia)).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
    (t.exists_triangle X (n - 1) n
      (by lia)).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose

lemma triangle_distinguished :
    triangle t n X ∈ distTriang C :=
  (t.exists_triangle X (n - 1) n
    (by lia)).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec

instance triangle_obj₁_isLE (n : ℤ) :
    t.IsLE (triangle t n X).obj₁ (n - 1) :=
  ⟨(t.exists_triangle X (n - 1) n (by lia)).choose_spec.choose_spec.choose⟩

instance triangle_obj₃_isGE :
    t.IsGE (triangle t n X).obj₃ n :=
  ⟨(t.exists_triangle X (n - 1) n (by lia)).choose_spec.choose_spec.choose_spec.choose⟩

variable {X} {Y : C} (φ : X ⟶ Y)

/-- Version of `TStructure.triangle_map_ext` that is specialized for the auxiliary
definition `TruncAux.triangle`. -/
@[ext]
lemma triangle_map_ext' (f₁ f₂ : triangle t n X ⟶ triangle t n Y)
    (H : f₁.hom₂ = f₂.hom₂ := by cat_disch) : f₁ = f₂ :=
  triangle_map_ext t (triangle_distinguished t n X) (triangle_distinguished t n Y) (n - 1) n
    inferInstance inferInstance H (by lia)

/-- Auxiliary definition for `triangleFunctor`. -/
@[simps hom₂]
noncomputable def triangleMap : triangle t n X ⟶ triangle t n Y :=
  have H := triangle_map_exists t (triangle_distinguished t n X)
    (triangle_distinguished t n Y) φ (n - 1) n inferInstance inferInstance (by lia)
  { hom₁ := H.choose.hom₁
    hom₂ := φ
    hom₃ := H.choose.hom₃
    comm₁ := by rw [← H.choose.comm₁, H.choose_spec]
    comm₂ := by rw [H.choose.comm₂, H.choose_spec]
    comm₃ := H.choose.comm₃ }

/-- Given a t-structure `t` on `C` and `n : ℤ`, this is the
functorial (distinguished) triangle `obj₁ ⟶ X ⟶ obj₃ ⟶ obj₁⟦1⟧` for any `X : C`,
where `obj₁` is `< n` and `obj₃` is `≥ n`.
(This should not be used directly: use `triangleLTGE` instead.) -/
@[simps]
noncomputable def triangleFunctor : C ⥤ Triangle C where
  obj := triangle t n
  map φ := triangleMap t n φ

variable (A)

lemma triangleFunctor_obj_distinguished :
    (triangleFunctor t n).obj A ∈ distTriang C :=
  triangle_distinguished t n A

instance isLE_triangleFunctor_obj_obj₁ :
    t.IsLE ((triangleFunctor t n).obj A).obj₁ (n - 1) := by
  dsimp [triangleFunctor]
  infer_instance

instance isGE_triangleFunctor_obj_obj₃ :
    t.IsGE ((triangleFunctor t n).obj A).obj₃ n := by
  dsimp [triangleFunctor]
  infer_instance

noncomputable def triangleMapOfLE (a b : ℤ) (h : a ≤ b) : triangle t a A ⟶ triangle t b A :=
  have H := triangle_map_exists t (triangle_distinguished t a A)
    (triangle_distinguished t b A) (𝟙 _) (a - 1) b inferInstance inferInstance
  { hom₁ := H.choose.hom₁
    hom₂ := 𝟙 _
    hom₃ := H.choose.hom₃
    comm₁ := by rw [← H.choose.comm₁, H.choose_spec]
    comm₂ := by rw [H.choose.comm₂, H.choose_spec]
    comm₃ := H.choose.comm₃ }

noncomputable def triangleFunctorNatTransOfLE (a b : ℤ) (h : a ≤ b) :
    triangleFunctor t a ⟶ triangleFunctor t b where
  app X := triangleMapOfLE t X a b h
  naturality _ _ _ :=
    triangle_map_ext t (triangleFunctor_obj_distinguished _ _ _)
      (triangleFunctor_obj_distinguished _ _ _) (a - 1) b inferInstance inferInstance
        (by simp [triangleMapOfLE])

@[simp]
lemma triangleFunctorNatTransOfLE_app_hom₂ (a b : ℤ) (h : a ≤ b) (X : C) :
    ((triangleFunctorNatTransOfLE t a b h).app X).hom₂ = 𝟙 X := rfl

lemma triangleFunctorNatTransOfLE_trans (a b c : ℤ) (hab : a ≤ b) (hbc : b ≤ c) :
    triangleFunctorNatTransOfLE t a b hab ≫ triangleFunctorNatTransOfLE t b c hbc =
      triangleFunctorNatTransOfLE t a c (hab.trans hbc) := by
  apply NatTrans.ext
  ext1 X
  exact triangle_map_ext t (triangleFunctor_obj_distinguished _ _ _)
    (triangleFunctor_obj_distinguished _ _ _) (a - 1) c inferInstance inferInstance (by simp)

lemma triangleFunctorNatTransOfLE_refl (a : ℤ) :
    triangleFunctorNatTransOfLE t a a (by rfl) = 𝟙 _ := by
  apply NatTrans.ext
  ext1 X
  exact triangle_map_ext t (triangleFunctor_obj_distinguished _ _ _)
    (triangleFunctor_obj_distinguished _ _ _) (a - 1) a inferInstance inferInstance (by simp)

instance : (triangleFunctor t n).Additive where

end TruncAux

public section

/-- Given a t-structure `t` on a pretriangulated category `C` and `n : ℤ`, this
is the `< n`-truncation functor. See also the natural transformation `truncLTι`. -/
noncomputable def truncLT (n : ℤ) : C ⥤ C :=
  TruncAux.triangleFunctor t n ⋙ Triangle.π₁

set_option backward.isDefEq.respectTransparency false in
instance (n : ℤ) : (t.truncLT n).Additive where
  map_add {_ _ _ _} := by
    dsimp only [truncLT, Functor.comp_map]
    rw [Functor.map_add]
    dsimp

/-- The natural transformation `t.truncLT n ⟶ 𝟭 C` when `t` is a t-structure
on a category `C` and `n : ℤ`. -/
noncomputable def truncLTι (n : ℤ) : t.truncLT n ⟶ 𝟭 _ :=
  Functor.whiskerLeft (TruncAux.triangleFunctor t n) Triangle.π₁Toπ₂

/-- Given a t-structure `t` on a pretriangulated category `C` and `n : ℤ`, this
is the `≥ n`-truncation functor. See also the natural transformation `truncGEπ`. -/
noncomputable def truncGE (n : ℤ) : C ⥤ C :=
  TruncAux.triangleFunctor t n ⋙ Triangle.π₃

set_option backward.isDefEq.respectTransparency false in
instance (n : ℤ) : (t.truncGE n).Additive where
  map_add {_ _ _ _} := by
    dsimp only [truncGE, Functor.comp_map]
    rw [Functor.map_add]
    dsimp

/-- The natural transformation `𝟭 C ⟶ t.truncGE n` when `t` is a t-structure
on a category `C` and `n : ℤ`. -/
noncomputable def truncGEπ (n : ℤ) : 𝟭 _ ⟶ t.truncGE n :=
  Functor.whiskerLeft (TruncAux.triangleFunctor t n) Triangle.π₂Toπ₃

@[reassoc (attr := simp)]
lemma truncGEπ_naturality (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    (t.truncGEπ n).app X ≫ (t.truncGE n).map f = f ≫ (t.truncGEπ n).app Y :=
  ((t.truncGEπ n).naturality f).symm

lemma isLE_truncLT_obj (X : C) (a b : ℤ) (hn : a ≤ b + 1 := by lia) :
    t.IsLE ((t.truncLT a).obj X) b := by
  have : t.IsLE ((t.truncLT a).obj X) (a - 1) := by dsimp [truncLT]; infer_instance
  exact t.isLE_of_le _ (a - 1) _ (by lia)

instance (X : C) (n : ℤ) : t.IsLE ((t.truncLT n).obj X) (n - 1) :=
  t.isLE_truncLT_obj ..

instance (X : C) (n : ℤ) : t.IsLE ((t.truncLT (n + 1)).obj X) n :=
  t.isLE_truncLT_obj ..

lemma isGE_truncGE_obj (X : C) (a b : ℤ) (hn : b ≤ a := by lia) :
    t.IsGE ((t.truncGE a).obj X) b := by
  have : t.IsGE ((t.truncGE a).obj X) a := by dsimp [truncGE]; infer_instance
  exact t.isGE_of_ge _ _ a (by lia)

instance (X : C) (n : ℤ) : t.IsGE ((t.truncGE n).obj X) n :=
  t.isGE_truncGE_obj ..

/-- The connecting morphism `t.truncGE n ⟶ t.truncLT n ⋙ shiftFunctor C (1 : ℤ)`
when `t` is a t-structure on a pretriangulated category and `n : ℤ`. -/
noncomputable def truncGEδLT (n : ℤ) :
    t.truncGE n ⟶ t.truncLT n ⋙ shiftFunctor C (1 : ℤ) :=
  Functor.whiskerLeft (TruncAux.triangleFunctor t n) Triangle.π₃Toπ₁

/-- The distinguished triangle `(t.truncLT n).obj A ⟶ A ⟶ (t.truncGE n).obj A ⟶ ...`
as a functor `C ⥤ Triangle C` when `t` is a `t`-structure on a pretriangulated
category `C` and `n : ℤ`. -/
@[expose, simps!]
noncomputable def triangleLTGE (n : ℤ) : C ⥤ Triangle C :=
  Triangle.functorMk (t.truncLTι n) (t.truncGEπ n) (t.truncGEδLT n)

lemma triangleLTGE_distinguished (n : ℤ) (X : C) :
    (t.triangleLTGE n).obj X ∈ distTriang C :=
  TruncAux.triangleFunctor_obj_distinguished t n X

instance (X : C) (n : ℤ) : t.IsLE ((t.triangleLTGE n).obj X).obj₁ (n - 1) := by
  dsimp
  infer_instance

instance (X : C) (n : ℤ) : t.IsGE ((t.triangleLTGE n).obj X).obj₃ n := by
  dsimp
  infer_instance

@[reassoc (attr := simp)]
lemma truncLTι_comp_truncGEπ_app (n : ℤ) (X : C) :
    (t.truncLTι n).app X ≫ (t.truncGEπ n).app X = 0 :=
  comp_distTriang_mor_zero₁₂ _ (t.triangleLTGE_distinguished n X)

@[reassoc (attr := simp)]
lemma truncGEπ_comp_truncGEδLT_app (n : ℤ) (X : C) :
    (t.truncGEπ n).app X ≫ (t.truncGEδLT n).app X = 0 :=
  comp_distTriang_mor_zero₂₃ _ (t.triangleLTGE_distinguished n X)

@[reassoc (attr := simp)]
lemma truncGEδLT_comp_truncLTι_app (n : ℤ) (X : C) :
    (t.truncGEδLT n).app X ≫ ((t.truncLTι n).app X)⟦(1 : ℤ)⟧' = 0 :=
  comp_distTriang_mor_zero₃₁ _ (t.triangleLTGE_distinguished n X)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma truncLTι_comp_truncGEπ (n : ℤ) :
    t.truncLTι n ≫ t.truncGEπ n = 0 := by
  cat_disch

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma truncGEπ_comp_truncGEδLT (n : ℤ) :
    t.truncGEπ n ≫ t.truncGEδLT n = 0 := by cat_disch

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma truncGEδLT_comp_truncLTι (n : ℤ) :
    t.truncGEδLT n ≫ Functor.whiskerRight (t.truncLTι n) (shiftFunctor C (1 : ℤ)) = 0 := by
  cat_disch

/-- The natural transformation `t.truncLT a ⟶ t.truncLT b` when `a ≤ b`. -/
noncomputable def natTransTruncLTOfLE (a b : ℤ) (h : a ≤ b) :
    t.truncLT a ⟶ t.truncLT b :=
  Functor.whiskerRight (TruncAux.triangleFunctorNatTransOfLE t a b h) Triangle.π₁

/-- The natural transformation `t.truncGE a ⟶ t.truncGE b` when `a ≤ b`. -/
noncomputable def natTransTruncGEOfLE (a b : ℤ) (h : a ≤ b) :
    t.truncGE a ⟶ t.truncGE b :=
  Functor.whiskerRight (TruncAux.triangleFunctorNatTransOfLE t a b h) Triangle.π₃

@[reassoc (attr := simp)]
lemma natTransTruncLTOfLE_ι_app (a b : ℤ) (h : a ≤ b) (X : C) :
    (t.natTransTruncLTOfLE a b h).app X ≫ (t.truncLTι b).app X = (t.truncLTι a).app X := by
  simpa using ((TruncAux.triangleFunctorNatTransOfLE t a b h).app X).comm₁.symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma natTransTruncLTOfLE_ι (a b : ℤ) (h : a ≤ b) :
    t.natTransTruncLTOfLE a b h ≫ t.truncLTι b = t.truncLTι a := by
  cat_disch

@[reassoc (attr := simp)]
lemma π_natTransTruncGEOfLE_app (a b : ℤ) (h : a ≤ b) (X : C) :
    (t.truncGEπ a).app X ≫ (t.natTransTruncGEOfLE a b h).app X = (t.truncGEπ b).app X := by
  simpa only [TruncAux.triangleFunctor_obj, TruncAux.triangle_obj₂,
    TruncAux.triangleFunctorNatTransOfLE_app_hom₂, Category.id_comp] using
    ((TruncAux.triangleFunctorNatTransOfLE t a b h).app X).comm₂

@[reassoc]
lemma truncGEδLT_comp_natTransTruncLTOfLE_app (a b : ℤ) (h : a ≤ b) (X : C) :
  (t.truncGEδLT a).app X ≫ ((natTransTruncLTOfLE t a b h).app X)⟦(1 : ℤ)⟧' =
    (t.natTransTruncGEOfLE a b h).app X ≫ (t.truncGEδLT b).app X :=
  ((TruncAux.triangleFunctorNatTransOfLE t a b h).app X).comm₃

@[reassoc]
lemma truncGEδLT_comp_whiskerRight_natTransTruncLTOfLE (a b : ℤ) (h : a ≤ b) :
  t.truncGEδLT a ≫ Functor.whiskerRight (natTransTruncLTOfLE t a b h) (shiftFunctor C (1 : ℤ)) =
    t.natTransTruncGEOfLE a b h ≫ t.truncGEδLT b := by
  ext X
  exact t.truncGEδLT_comp_natTransTruncLTOfLE_app a b h X

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma π_natTransTruncGEOfLE (a b : ℤ) (h : a ≤ b) :
    t.truncGEπ a ≫ t.natTransTruncGEOfLE a b h = t.truncGEπ b := by
  cat_disch

/-- The natural transformation `t.triangleLTGE a ⟶ t.triangleLTGE b`
when `a ≤ b`. -/
noncomputable def natTransTriangleLTGEOfLE (a b : ℤ) (h : a ≤ b) :
    t.triangleLTGE a ⟶ t.triangleLTGE b :=
  Triangle.functorHomMk' (t.natTransTruncLTOfLE a b h) (𝟙 _)
    ((t.natTransTruncGEOfLE a b h)) (by simp) (by simp)
    (t.truncGEδLT_comp_whiskerRight_natTransTruncLTOfLE a b h)

@[simp]
lemma natTransTriangleLTGEOfLE_refl (a : ℤ) :
    t.natTransTriangleLTGEOfLE a a (by rfl) = 𝟙 _ :=
  TruncAux.triangleFunctorNatTransOfLE_refl t a

lemma natTransTriangleLTGEOfLE_trans (a b c : ℤ) (hab : a ≤ b) (hbc : b ≤ c) :
    t.natTransTriangleLTGEOfLE a b hab ≫ t.natTransTriangleLTGEOfLE b c hbc =
      t.natTransTriangleLTGEOfLE a c (hab.trans hbc) :=
  TruncAux.triangleFunctorNatTransOfLE_trans t a b c hab hbc

@[simp]
lemma natTransTruncLTOfLE_refl (a : ℤ) :
    t.natTransTruncLTOfLE a a (by rfl) = 𝟙 _ :=
  congr_arg (fun x ↦ Functor.whiskerRight x (Triangle.π₁)) (t.natTransTriangleLTGEOfLE_refl a)

@[simp]
lemma natTransTruncLTOfLE_trans (a b c : ℤ) (hab : a ≤ b) (hbc : b ≤ c) :
    t.natTransTruncLTOfLE a b hab ≫ t.natTransTruncLTOfLE b c hbc =
      t.natTransTruncLTOfLE a c (hab.trans hbc) :=
  congr_arg (fun x ↦ Functor.whiskerRight x Triangle.π₁)
    (t.natTransTriangleLTGEOfLE_trans a b c hab hbc)

@[simp]
lemma natTransTruncGEOfLE_refl (a : ℤ) :
    t.natTransTruncGEOfLE a a (by rfl) = 𝟙 _ :=
  congr_arg (fun x ↦ Functor.whiskerRight x (Triangle.π₃)) (t.natTransTriangleLTGEOfLE_refl a)

@[simp]
lemma natTransTruncGEOfLE_trans (a b c : ℤ) (hab : a ≤ b) (hbc : b ≤ c) :
    t.natTransTruncGEOfLE a b hab ≫ t.natTransTruncGEOfLE b c hbc =
      t.natTransTruncGEOfLE a c (hab.trans hbc) :=
  congr_arg (fun x ↦ Functor.whiskerRight x Triangle.π₃)
    (t.natTransTriangleLTGEOfLE_trans a b c hab hbc)

lemma natTransTruncLTOfLE_refl_app (a : ℤ) (X : C) :
    (t.natTransTruncLTOfLE a a (by rfl)).app X = 𝟙 _ :=
  congr_app (t.natTransTruncLTOfLE_refl a) X

lemma natTransTruncLTOfLE_trans_app (a b c : ℤ) (hab : a ≤ b) (hbc : b ≤ c) (X : C) :
    (t.natTransTruncLTOfLE a b hab).app X ≫ (t.natTransTruncLTOfLE b c hbc).app X =
      (t.natTransTruncLTOfLE a c (hab.trans hbc)).app X :=
  congr_app (t.natTransTruncLTOfLE_trans a b c hab hbc) X

lemma natTransTruncGEOfLE_refl_app (a : ℤ) (X : C) :
    (t.natTransTruncGEOfLE a a (by rfl)).app X = 𝟙 _ :=
  congr_app (t.natTransTruncGEOfLE_refl a) X

lemma natTransTruncGEOfLE_trans_app (a b c : ℤ) (hab : a ≤ b) (hbc : b ≤ c) (X : C) :
    (t.natTransTruncGEOfLE a b hab).app X ≫ (t.natTransTruncGEOfLE b c hbc).app X =
      (t.natTransTruncGEOfLE a c (hab.trans hbc)).app X :=
  congr_app (t.natTransTruncGEOfLE_trans a b c hab hbc) X

lemma isLE_of_isZero {X : C} (hX : IsZero X) (n : ℤ) : t.IsLE X n :=
  t.isLE_of_iso (((t.truncLT (n + 1)).map_isZero hX).isoZero ≪≫ hX.isoZero.symm) n

lemma isGE_of_isZero {X : C} (hX : IsZero X) (n : ℤ) : t.IsGE X n :=
  t.isGE_of_iso (((t.truncGE n).map_isZero hX).isoZero ≪≫ hX.isoZero.symm) n

instance (n : ℤ) : t.IsLE (0 : C) n := t.isLE_of_isZero (isZero_zero C) n

instance (n : ℤ) : t.IsGE (0 : C) n := t.isGE_of_isZero (isZero_zero C) n

set_option backward.isDefEq.respectTransparency false in
lemma isLE_iff_isIso_truncLTι_app (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) :
    t.IsLE X n₀ ↔ IsIso (((t.truncLTι n₁)).app X) := by
  subst h
  refine ⟨fun _ ↦ ?_,
    fun _ ↦ t.isLE_of_iso (asIso (((t.truncLTι (n₀ + 1))).app X)) n₀⟩
  obtain ⟨e, he⟩ := t.triangle_iso_exists
    (contractible_distinguished X) (t.triangleLTGE_distinguished (n₀ + 1) X)
    (Iso.refl X) n₀ (n₀ + 1)
    (by dsimp; infer_instance) (by dsimp; infer_instance)
    (by dsimp; infer_instance) (by dsimp; infer_instance)
  have he' : e.inv.hom₂ = 𝟙 X := by
    rw [← cancel_mono e.hom.hom₂, ← comp_hom₂, e.inv_hom_id, he]
    simp
  have : (t.truncLTι (n₀ + 1)).app X = e.inv.hom₁ := by
    simpa [he'] using e.inv.comm₁
  rw [this]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
lemma isGE_iff_isIso_truncGEπ_app (n : ℤ) (X : C) :
    t.IsGE X n ↔ IsIso ((t.truncGEπ n).app X) := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := t.triangle_iso_exists
      (inv_rot_of_distTriang _ (contractible_distinguished X))
      (t.triangleLTGE_distinguished n X) (Iso.refl X) (n - 1) n
      (t.isLE_of_iso (shiftFunctor C (-1 : ℤ)).mapZeroObject.symm _)
      (by dsimp; infer_instance) (by dsimp; infer_instance) (by dsimp; infer_instance)
    dsimp at he
    have : (truncGEπ t n).app X = e.hom.hom₃ := by
      have := e.hom.comm₂
      dsimp at this
      rw [← cancel_epi e.hom.hom₂, ← this, he]
    rw [this]
    infer_instance
  · intro
    exact t.isGE_of_iso (asIso ((truncGEπ t n).app X)).symm n

instance (X : C) (n : ℤ) [t.IsGE X n] : IsIso ((t.truncGEπ n).app X) := by
  rw [← isGE_iff_isIso_truncGEπ_app]
  infer_instance

lemma isGE_iff_isZero_truncLT_obj (n : ℤ) (X : C) :
    t.IsGE X n ↔ IsZero ((t.truncLT n).obj X) := by
  rw [t.isGE_iff_isIso_truncGEπ_app n X]
  exact (Triangle.isZero₁_iff_isIso₂ _ (t.triangleLTGE_distinguished n X)).symm

lemma isLE_iff_isZero_truncGE_obj (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) :
    t.IsLE X n₀ ↔ IsZero ((t.truncGE n₁).obj X) := by
  rw [t.isLE_iff_isIso_truncLTι_app n₀ n₁ h X]
  exact (Triangle.isZero₃_iff_isIso₁ _ (t.triangleLTGE_distinguished n₁ X)).symm

lemma isZero_truncLT_obj_of_isGE (n : ℤ) (X : C) [t.IsGE X n] :
    IsZero ((t.truncLT n).obj X) := by
  rw [← isGE_iff_isZero_truncLT_obj]
  infer_instance

lemma isZero_truncGE_obj_of_isLE (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) [t.IsLE X n₀] :
    IsZero ((t.truncGE n₁).obj X) := by
  rw [← t.isLE_iff_isZero_truncGE_obj _ _ h X]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
lemma from_truncGE_obj_ext {n : ℤ} {X : C} {Y : C}
    {f₁ f₂ : (t.truncGE n).obj X ⟶ Y} (h : (t.truncGEπ n).app X ≫ f₁ = (t.truncGEπ n).app X ≫ f₂)
    [t.IsGE Y n] :
    f₁ = f₂ := by
  suffices ∀ (f : (t.truncGE n).obj X ⟶ Y), (t.truncGEπ n).app X ≫ f = 0 → f = 0 by
    rw [← sub_eq_zero, this (f₁ - f₂) (by cat_disch)]
  intro f hf
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _
    (t.triangleLTGE_distinguished n X) f hf
  have hg' := t.zero_of_isLE_of_isGE g (n-2) n (by lia)
    (by exact t.isLE_shift _ (n-1) 1 (n-2) (by lia)) inferInstance
  rw [hg, hg', comp_zero]

set_option backward.isDefEq.respectTransparency false in
lemma to_truncLT_obj_ext {n : ℤ} {Y : C} {X : C}
    {f₁ f₂ : Y ⟶ (t.truncLT n).obj X}
    (h : f₁ ≫ (t.truncLTι n).app X = f₂ ≫ (t.truncLTι n).app X)
    [t.IsLE Y (n - 1)] :
    f₁ = f₂ := by
  suffices ∀ (f : Y ⟶ (t.truncLT n).obj X) (_ : f ≫ (t.truncLTι n).app X = 0), f = 0 by
    rw [← sub_eq_zero, this (f₁ - f₂) (by cat_disch)]
  intro f hf
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _
    (t.triangleLTGE_distinguished n X)) f hf
  have hg' := t.zero_of_isLE_of_isGE g (n - 1) (n + 1) (by lia) inferInstance
    (by dsimp; apply (t.isGE_shift _ n (-1) (n + 1) (by lia)))
  rw [hg, hg', zero_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma truncLT_map_truncLTι_app (n : ℤ) (X : C) :
    (t.truncLT n).map ((t.truncLTι n).app X) = (t.truncLTι n).app ((t.truncLT n).obj X) :=
  t.to_truncLT_obj_ext (by simp)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma truncGE_map_truncGEπ_app (n : ℤ) (X : C) :
    (t.truncGE n).map ((t.truncGEπ n).app X) = (t.truncGEπ n).app ((t.truncGE n).obj X) :=
  t.from_truncGE_obj_ext (by simp)

section

variable {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) [t.IsLE X n₀]

include h in
lemma liftTruncLT_aux :
    ∃ (f' : X ⟶ (t.truncLT n₁).obj Y), f = f' ≫ (t.truncLTι n₁).app Y :=
  Triangle.coyoneda_exact₂ _ (t.triangleLTGE_distinguished n₁ Y) f
    (t.zero_of_isLE_of_isGE _ n₀ n₁ (by lia) inferInstance (by dsimp; infer_instance))

/-- Constructor for morphisms to `(t.truncLT n₁).obj Y`. -/
noncomputable def liftTruncLT {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) [t.IsLE X n₀] :
    X ⟶ (t.truncLT n₁).obj Y :=
  (t.liftTruncLT_aux f n₀ n₁ h).choose

@[reassoc (attr := simp)]
lemma liftTruncLT_ι {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) [t.IsLE X n₀] :
    t.liftTruncLT f n₀ n₁ h ≫ (t.truncLTι n₁).app Y = f :=
  (t.liftTruncLT_aux f n₀ n₁ h).choose_spec.symm

end

section

variable {X Y : C} (f : X ⟶ Y) (n : ℤ) [t.IsGE Y n]

lemma descTruncGE_aux :
  ∃ (f' : (t.truncGE n).obj X ⟶ Y), f = (t.truncGEπ n).app X ≫ f' :=
  Triangle.yoneda_exact₂ _ (t.triangleLTGE_distinguished n X) f
    (t.zero_of_isLE_of_isGE _ (n-1) n (by lia) (by dsimp; infer_instance) inferInstance)

/-- Constructor for morphisms from `(t.truncGE n).obj X`. -/
noncomputable def descTruncGE :
    (t.truncGE n).obj X ⟶ Y :=
  (t.descTruncGE_aux f n).choose

@[reassoc (attr := simp)]
lemma π_descTruncGE {X Y : C} (f : X ⟶ Y) (n : ℤ) [t.IsGE Y n] :
    (t.truncGEπ n).app X ≫ t.descTruncGE f n = f :=
  (t.descTruncGE_aux f n).choose_spec.symm

end

lemma isLE_iff_orthogonal (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) :
    t.IsLE X n₀ ↔ ∀ (Y : C) (f : X ⟶ Y) (_ : t.IsGE Y n₁), f = 0 := by
  refine ⟨fun _ Y f _ ↦ t.zero f n₀ n₁ (by lia), fun hX ↦ ?_⟩
  rw [t.isLE_iff_isZero_truncGE_obj n₀ n₁ h, IsZero.iff_id_eq_zero]
  exact t.from_truncGE_obj_ext (by simpa using hX _ _ inferInstance)

lemma isGE_iff_orthogonal (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) :
    t.IsGE X n₁ ↔ ∀ (Y : C) (f : Y ⟶ X) (_ : t.IsLE Y n₀), f = 0 := by
  refine ⟨fun _ Y f _ ↦ t.zero f n₀ n₁ (by lia), fun hX ↦ ?_⟩
  rw [t.isGE_iff_isZero_truncLT_obj n₁ X, IsZero.iff_id_eq_zero]
  exact t.to_truncLT_obj_ext (by simpa using hX _ _ (by rw [← h]; infer_instance))

lemma isLE₂ (T : Triangle C) (hT : T ∈ distTriang C) (n : ℤ) (h₁ : t.IsLE T.obj₁ n)
    (h₃ : t.IsLE T.obj₃ n) : t.IsLE T.obj₂ n := by
  rw [t.isLE_iff_orthogonal n (n + 1) rfl]
  intro Y f hY
  obtain ⟨f', hf'⟩ := Triangle.yoneda_exact₂ _ hT f
    (t.zero _ n (n + 1) (by lia))
  rw [hf', t.zero f' n (n + 1) (by lia), comp_zero]

lemma isGE₂ (T : Triangle C) (hT : T ∈ distTriang C) (n : ℤ) (h₁ : t.IsGE T.obj₁ n)
    (h₃ : t.IsGE T.obj₃ n) : t.IsGE T.obj₂ n := by
  rw [t.isGE_iff_orthogonal (n-1) n (by lia)]
  intro Y f hY
  obtain ⟨f', hf'⟩ := Triangle.coyoneda_exact₂ _ hT f (t.zero _ (n-1) n (by lia))
  rw [hf', t.zero f' (n-1) n (by lia), zero_comp]

instance : t.minus.IsTriangulated where
  exists_zero := ⟨0, isZero_zero C, 0, inferInstance⟩
  toIsTriangulatedClosed₂ := .mk' (fun T hT ↦ by
    rintro ⟨i₁, hi₁⟩ ⟨i₃, hi₃⟩
    exact ⟨max i₁ i₃, t.isLE₂ T hT _ (t.isLE_of_le _ _ _ (le_max_left i₁ i₃))
      (t.isLE_of_le _ _ _ (le_max_right i₁ i₃))⟩)

instance : t.plus.IsTriangulated where
  exists_zero := ⟨0, isZero_zero C, 0, inferInstance⟩
  toIsTriangulatedClosed₂ := .mk' (fun T hT ↦ by
    rintro ⟨i₁, hi₁⟩ ⟨i₃, hi₃⟩
    exact ⟨min i₁ i₃, t.isGE₂ T hT _ (t.isGE_of_ge _ _ _ (min_le_left i₁ i₃))
      (t.isGE_of_ge _ _ _ (min_le_right i₁ i₃))⟩)

instance : t.bounded.IsTriangulated := by
  dsimp [bounded]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
lemma isIso_truncLT_map_iff {X Y : C} (f : X ⟶ Y) (n : ℤ) :
    IsIso ((t.truncLT n).map f) ↔
      ∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ ((t.truncLT n).obj X)⟦1⟧)
        (_ : Triangle.mk ((t.truncLTι n).app X ≫ f) g h ∈ distTriang _), t.IsGE Z n := by
  refine ⟨fun hf ↦ ?_, fun ⟨Z, g, h, mem, _⟩ ↦ ?_⟩
  · refine ⟨(t.truncGE n).obj Y, (t.truncGEπ n).app Y,
      (t.truncGEδLT n).app Y ≫ (inv ((t.truncLT n).map f))⟦1⟧',
      isomorphic_distinguished _ (t.triangleLTGE_distinguished n Y) _ ?_, inferInstance⟩
    exact Triangle.isoMk _ _ (asIso ((t.truncLT n).map f)) (Iso.refl _) (Iso.refl _)
  · obtain ⟨e, he⟩ := t.triangle_iso_exists
      mem (t.triangleLTGE_distinguished n Y) (Iso.refl _) (n - 1) n
      (by dsimp; infer_instance) (by dsimp; infer_instance)
      (by dsimp; infer_instance) (by dsimp; infer_instance)
    suffices ((t.truncLT n).map f) = e.hom.hom₁ by rw [this]; infer_instance
    exact t.to_truncLT_obj_ext (Eq.trans (by cat_disch) e.hom.comm₁)

set_option backward.isDefEq.respectTransparency false in
lemma isIso_truncGE_map_iff {Y Z : C} (g : Y ⟶ Z) (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁) :
    IsIso ((t.truncGE n₁).map g) ↔
      ∃ (X : C) (f : X ⟶ Y) (h : ((t.truncGE n₁).obj Z) ⟶ X⟦(1 : ℤ)⟧)
        (_ : Triangle.mk f (g ≫ (t.truncGEπ n₁).app Z) h ∈ distTriang _), t.IsLE X n₀ := by
  refine ⟨fun hf ↦ ?_, fun ⟨X, f, h, mem, _⟩ ↦ ?_⟩
  · refine ⟨_, (t.truncLTι n₁).app Y, inv ((t.truncGE n₁).map g) ≫ (t.truncGEδLT n₁).app Y,
      isomorphic_distinguished _ (t.triangleLTGE_distinguished n₁ Y) _ ?_,
      by subst hn; infer_instance⟩
    exact Iso.symm (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
      (asIso ((t.truncGE n₁).map g)) (by simp) (by simp) (by simp))
  · obtain ⟨e, he⟩ :=
      t.triangle_iso_exists (t.triangleLTGE_distinguished n₁ Y) mem (Iso.refl _) n₀ n₁
        (by dsimp; rw [← hn]; infer_instance) (by dsimp; infer_instance)
        (by dsimp; infer_instance) (by dsimp; infer_instance)
    suffices ((t.truncGE n₁).map g) = e.hom.hom₃ by rw [this]; infer_instance
    exact t.from_truncGE_obj_ext (Eq.trans (by cat_disch) e.hom.comm₂.symm)

instance (X : C) (a b : ℤ) [t.IsLE X b] : t.IsLE ((t.truncLT a).obj X) b := by
  by_cases h : a ≤ b + 1
  · exact t.isLE_truncLT_obj ..
  · have := (t.isLE_iff_isIso_truncLTι_app (a - 1) a (by lia) X).1 (t.isLE_of_le _ b _ (by lia))
    exact t.isLE_of_iso (show X ≅ _ from (asIso ((t.truncLTι a).app X)).symm) _

set_option backward.isDefEq.respectTransparency false in
instance (X : C) (a b : ℤ) [t.IsGE X a] : t.IsGE ((t.truncGE b).obj X) a := by
  by_cases h : a ≤ b
  · exact t.isGE_truncGE_obj ..
  · have : t.IsGE X b := t.isGE_of_ge X b a (by lia)
    exact t.isGE_of_iso (show X ≅ _ from asIso ((t.truncGEπ b).app X)) _

/-- The composition `t.truncLT b ⋙ t.truncGE a`. -/
noncomputable abbrev truncGELT (a b : ℤ) : C ⥤ C := t.truncLT b ⋙ t.truncGE a

/-- The composition `t.truncGE b ⋙ t.truncLT a`. -/
noncomputable abbrev truncLTGE (a b : ℤ) : C ⥤ C := t.truncGE a ⋙ t.truncLT b

instance (X : C) (a b : ℤ) : t.IsGE ((t.truncGELT a b).obj X) a := by
  dsimp; infer_instance

instance (X : C) (a b : ℤ) : t.IsLE ((t.truncLTGE a b).obj X) (b - 1) := by
  dsimp; infer_instance

section

variable [IsTriangulated C]

lemma isIso₁_truncLT_map_of_isGE (T : Triangle C) (hT : T ∈ distTriang C)
    (n : ℤ) (h₃ : t.IsGE T.obj₃ n) :
    IsIso ((t.truncLT n).map T.mor₁) := by
  rw [isIso_truncLT_map_iff]
  obtain ⟨Z, g, k, mem⟩ := distinguished_cocone_triangle ((t.truncLTι n).app T.obj₁ ≫ T.mor₁)
  refine ⟨_, _, _, mem, ?_⟩
  let H := someOctahedron rfl (t.triangleLTGE_distinguished n T.obj₁) hT mem
  exact t.isGE₂ _ H.mem n (by dsimp; infer_instance) (by dsimp; infer_instance)

lemma isIso₂_truncGE_map_of_isLE (T : Triangle C) (hT : T ∈ distTriang C)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (h₁ : t.IsLE T.obj₁ n₀) :
    IsIso ((t.truncGE n₁).map T.mor₂) := by
  rw [isIso_truncGE_map_iff _ _ _ _ h]
  obtain ⟨X, f, k, mem⟩ := distinguished_cocone_triangle₁ (T.mor₂ ≫ (t.truncGEπ n₁).app T.obj₃)
  refine ⟨_, _, _, mem, ?_⟩
  subst h
  have H := someOctahedron rfl (rot_of_distTriang _ hT)
    (rot_of_distTriang _ (t.triangleLTGE_distinguished (n₀ + 1) T.obj₃))
    (rot_of_distTriang _ mem)
  have : t.IsLE (X⟦(1 : ℤ)⟧) (n₀ - 1) :=
    t.isLE₂ _ H.mem (n₀ - 1) (t.isLE_shift T.obj₁ n₀ 1 (n₀ - 1) (by lia))
      (t.isLE_shift ((t.truncLT (n₀ + 1)).obj T.obj₃) n₀ 1 (n₀-1) (by lia))
  exact t.isLE_of_shift X n₀ 1 (n₀ - 1) (by lia)

set_option backward.isDefEq.respectTransparency false in
instance (X : C) (a b : ℤ) [t.IsGE X a] :
    t.IsGE ((t.truncLT b).obj X) a := by
  rw [t.isGE_iff_isZero_truncLT_obj]
  have := t.isIso₁_truncLT_map_of_isGE _ ((t.triangleLTGE_distinguished b X)) a
    (by dsimp; infer_instance)
  dsimp at this
  refine IsZero.of_iso ?_ (asIso ((t.truncLT a).map ((t.truncLTι b).app X)))
  rwa [← isGE_iff_isZero_truncLT_obj]

set_option backward.isDefEq.respectTransparency false in
instance (X : C) (a b : ℤ) [t.IsLE X b] : t.IsLE ((t.truncGE a).obj X) b := by
  rw [t.isLE_iff_isZero_truncGE_obj b (b + 1) rfl]
  have := t.isIso₂_truncGE_map_of_isLE _ (t.triangleLTGE_distinguished a X) b _ rfl
    (by dsimp; infer_instance)
  dsimp at this
  refine IsZero.of_iso ?_ (asIso ((t.truncGE (b + 1)).map ((t.truncGEπ a).app X))).symm
  rwa [← isLE_iff_isZero_truncGE_obj _ _ _ rfl]

instance (X : C) (a b : ℤ) :
    t.IsLE ((t.truncGELT a b).obj X) (b - 1) := by
  dsimp; infer_instance

instance (X : C) (a b : ℤ) :
    t.IsGE ((t.truncLTGE a b).obj X) a := by
  dsimp; infer_instance

lemma isIso_truncGE_map_truncGEπ_app (a b : ℤ) (h : b ≤ a) (X : C) :
    IsIso ((t.truncGE a).map ((t.truncGEπ b).app X)) :=
  t.isIso₂_truncGE_map_of_isLE _ (t.triangleLTGE_distinguished b X)
    (a - 1) a (by lia) (t.isLE_truncLT_obj _ _ _ (by simpa))

lemma isIso_truncLT_map_truncLTι_app (a b : ℤ) (h : a ≤ b) (X : C) :
    IsIso ((t.truncLT a).map ((t.truncLTι b).app X)) :=
  t.isIso₁_truncLT_map_of_isGE _ (t.triangleLTGE_distinguished b X) a
    (t.isGE_of_ge ((t.truncGE b).obj X) a b (by lia))

instance (X : C) (n : ℤ) : IsIso ((t.truncLT n).map ((t.truncLTι n).app X)) :=
  isIso_truncLT_map_truncLTι_app t _ _ (by rfl) X

instance (X : C) (n : ℤ) : IsIso ((t.truncGE n).map ((t.truncGEπ n).app X)) :=
  t.isIso_truncGE_map_truncGEπ_app _ _ (by rfl) _

instance (a b : ℤ) (X : C) :
    IsIso ((t.truncLTι b).app ((t.truncGE a).obj ((t.truncLT b).obj X))) := by
  rw [← t.isLE_iff_isIso_truncLTι_app (b - 1) b (by lia)]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The natural transformation `t.truncGELT a b ⟶ t.truncLTGE a b`
(which is an isomorphism, see `truncGELTIsoLTGE`.) -/
noncomputable def truncGELTToLTGE (a b : ℤ) :
    t.truncGELT a b ⟶ t.truncLTGE a b where
  app X := t.liftTruncLT (t.descTruncGE
    ((t.truncLTι b).app X ≫ (t.truncGEπ a).app X) a) (b - 1) b (by lia)
  naturality _ _ _ :=
    t.to_truncLT_obj_ext (by dsimp; exact t.from_truncGE_obj_ext (by simp))

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma truncGELTToLTGE_app_pentagon (a b : ℤ) (X : C) :
    (t.truncGEπ a).app _ ≫ (t.truncGELTToLTGE a b).app X ≫ (t.truncLTι b).app _ =
      (t.truncLTι b).app X ≫ (t.truncGEπ a).app X := by
  simp [truncGELTToLTGE]

set_option backward.isDefEq.respectTransparency false in
lemma truncGELTToLTGE_app_pentagon_uniqueness {a b : ℤ} {X : C}
    (φ : (t.truncGELT a b).obj X ⟶ (t.truncLTGE a b).obj X)
    (hφ : (t.truncGEπ a).app _ ≫ φ ≫ (t.truncLTι b).app _ =
      (t.truncLTι b).app X ≫ (t.truncGEπ a).app X) :
    (t.truncGELTToLTGE a b).app X = φ :=
  t.to_truncLT_obj_ext (by dsimp; exact t.from_truncGE_obj_ext (by cat_disch))

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma truncLT_map_truncGE_map_truncLTι_app_fac (a b : ℤ) (X : C) :
    (t.truncLTι b).app ((t.truncGE a).obj ((t.truncLT b).obj X)) ≫
        (t.truncGELTToLTGE a b).app X =
    (t.truncLT b).map ((t.truncGE a).map ((t.truncLTι b).app X)) := by
  rw [← cancel_epi (inv ((t.truncLTι b).app ((t.truncGE a).obj ((t.truncLT b).obj X)))),
    IsIso.inv_hom_id_assoc]
  exact t.truncGELTToLTGE_app_pentagon_uniqueness _ (by simp)

/-- The connecting homomorphism
`(t.truncGELT a b).obj X ⟶ ((t.truncLT a).obj X)⟦1⟧`,
as a natural transformation. -/
@[expose, simps!]
noncomputable def truncGELTδLT (a b : ℤ) :
    t.truncGELT a b ⟶ t.truncLT a ⋙ shiftFunctor C (1 : ℤ) :=
  Functor.whiskerLeft (t.truncLT b) (t.truncGEδLT a) ≫
    Functor.whiskerRight (t.truncLTι b) (t.truncLT a ⋙ shiftFunctor C (1 : ℤ))

/-- The functorial (distinguished) triangle
`(t.truncLT a).obj X ⟶ (t.truncLT b).obj X ⟶ (t.truncGELT a b).obj X ⟶ ...`
when `a ≤ b`. -/
@[expose, simps!]
noncomputable def triangleLTLTGELT (a b : ℤ) (h : a ≤ b) : C ⥤ Triangle C :=
  Triangle.functorMk (t.natTransTruncLTOfLE a b h)
    (Functor.whiskerLeft (t.truncLT b) (t.truncGEπ a)) (t.truncGELTδLT a b)

set_option backward.isDefEq.respectTransparency false in
lemma triangleLTLTGELT_distinguished (a b : ℤ) (h : a ≤ b) (X : C) :
    (t.triangleLTLTGELT a b h).obj X ∈ distTriang C := by
  have := t.isIso_truncLT_map_truncLTι_app a b h X
  refine isomorphic_distinguished _ (t.triangleLTGE_distinguished a ((t.truncLT b).obj X)) _ ?_
  refine Triangle.isoMk _ _ ((asIso ((t.truncLT a).map ((t.truncLTι b).app X))).symm)
    (Iso.refl _) (Iso.refl _) ?_ (by simp) (by simp)
  dsimp
  simp only [Category.comp_id, IsIso.eq_inv_comp]
  exact t.to_truncLT_obj_ext (by simp)

set_option backward.isDefEq.respectTransparency false in
instance (a b : ℤ) : IsIso (t.truncGELTToLTGE a b) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  by_cases h : a ≤ b
  · let u₁₂ := (t.natTransTruncLTOfLE a b h).app X
    let u₂₃ : (t.truncLT b).obj X ⟶ X := (t.truncLTι b).app X
    let u₁₃ : _ ⟶ X := (t.truncLTι a).app X
    have eq : u₁₂ ≫ u₂₃ = u₁₃ := by simp [u₁₂, u₂₃, u₁₃]
    have H := someOctahedron eq (t.triangleLTLTGELT_distinguished a b h X)
      (t.triangleLTGE_distinguished b X) (t.triangleLTGE_distinguished a X)
    let m₁ : (t.truncGELT a b).obj X ⟶ _ := H.m₁
    have : IsIso ((t.truncLT b).map H.m₁) :=
      t.isIso₁_truncLT_map_of_isGE _ H.mem b (by dsimp; infer_instance)
    have eq' : t.liftTruncLT m₁ (b - 1) b (by lia) = (t.truncGELTToLTGE a b).app X :=
      t.to_truncLT_obj_ext
        (by dsimp; exact t.from_truncGE_obj_ext (by simpa using H.comm₁))
    rw [← eq']
    have fac : (t.truncLTι b).app ((t.truncGE a).obj ((t.truncLT b).obj X)) ≫
        t.liftTruncLT m₁ (b - 1) b (by lia) = (t.truncLT b).map m₁ :=
      t.to_truncLT_obj_ext (by simp [truncGELT])
    exact IsIso.of_isIso_fac_left fac
  · simp at h
    refine ⟨0, ?_, ?_⟩
    all_goals exact IsZero.eq_of_src (t.isZero _ (b-1) a (by lia)) _ _

set_option backward.isDefEq.respectTransparency false in
instance (a b : ℤ) (X : C) :
    IsIso ((t.truncLT b).map ((t.truncGE a).map ((t.truncLTι b).app X))) := by
  rw [← t.truncLT_map_truncGE_map_truncLTι_app_fac a b X]
  infer_instance

/-- The natural transformation `t.truncGELT a b ≅ t.truncLTGE a b`. -/
noncomputable def truncGELTIsoLTGE (a b : ℤ) : t.truncGELT a b ≅ t.truncLTGE a b :=
  asIso (t.truncGELTToLTGE a b)

end

end

end TStructure

end Triangulated

end CategoryTheory
