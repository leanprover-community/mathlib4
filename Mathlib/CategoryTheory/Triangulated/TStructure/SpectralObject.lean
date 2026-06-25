/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.SpectralObject
public import Mathlib.CategoryTheory.Triangulated.TStructure.ETrunc

/-!
# Spectral objects attached to t-structures

Let `C` be a triangulated category equipped with a t-structure `t`.
We define a functor `t.ω₁ : ComposableArrows EInt 1 ⥤ C ⥤ C` which sends
a map `a ⟶ b` in `EInt` (i.e. `a ≤ b`) to the functor
`t.eTruncLT.obj b ⋙ t.eTruncGE.obj a`. (Roughly speaking, we "keep" the
`t`-homology only in degree `n` such that `a ≤ n < b`.)
When we have two composable morphisms `f : a ⟶ b` and `g : b ⟶ c` in `EInt`,
we define a connecting homomorphism
`ω₁δ : t.ω₁.obj (mk₁ g) ⟶ t.ω₁.obj (mk₁ f) ⋙ shiftFunctor C (1 : ℤ)`, and
this gives distinguished triangles that are functorial both in `X : C`
and `a ⟶ b ⟶ c` in `ComposableArrows EInt 2`.

In other words, for each `X : C`, we define a spectral
object `t.spectralObject X : SpectralObject C EInt` in the
triangulated category `C`, and this extends to a functor
`t.spectralObjectFunctor : C ⥤ SpectralObject C EInt`.

-/

@[expose] public section

namespace CategoryTheory

open Limits Pretriangulated ZeroObject Preadditive ComposableArrows

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Triangulated

namespace TStructure

variable (t : TStructure C)

set_option backward.defeqAttrib.useBackward true in
/-- Given a t-structure `t` on a triangulated category `C`, this is the functor
`ComposableArrows EInt 1 ⥤ C ⥤ C` which sends an arrows `a ⟶ b` in `EInt`
to the functor `t.eTruncLT.obj b ⋙ t.eTruncGE.obj a`. -/
@[simps]
noncomputable def ω₁ : ComposableArrows EInt 1 ⥤ C ⥤ C where
  obj D := t.eTruncLT.obj (D.obj 1) ⋙ t.eTruncGE.obj (D.obj 0)
  map φ := t.eTruncLT.map (φ.app 1) ◫ t.eTruncGE.map (φ.app 0)

variable [IsTriangulated C]

section

variable (a b c : EInt) (hab : a ≤ b) (hbc : b ≤ c)

open Functor in
/-- The connecting homomorphism (as a natural transformation) for the spectral
objects attached to the objects of a triangulated equipped with a t-structure. -/
@[simps!]
noncomputable def ω₁δ :
    t.ω₁.obj (mk₁ (homOfLE hbc)) ⟶ t.ω₁.obj (mk₁ (homOfLE hab)) ⋙ shiftFunctor C (1 : ℤ) :=
  whiskerLeft _ (t.eTruncGEToGEGE a b) ≫ (associator _ _ _).inv ≫
    (t.ω₁.obj (mk₁ (homOfLE (hab.trans hbc)))).whiskerLeft (t.eTruncGEδLT.app b) ≫
      (associator _ _ _).inv ≫
        whiskerRight ((associator _ _ _).hom ≫ whiskerLeft _ (t.eTruncLTGEIsoGELT a b).hom ≫
          (associator _ _ _).inv ≫ whiskerRight (t.eTruncLTLTToLT c b) _) _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma ω₁δ_naturality (a' b' c' : EInt) (hab' : a' ≤ b') (hbc' : b' ≤ c')
    (φ : mk₂ (homOfLE hab) (homOfLE hbc) ⟶ mk₂ (homOfLE hab') (homOfLE hbc')) :
    t.ω₁.map (homMk₁ (φ.app 1) (φ.app 2)) ≫ t.ω₁δ a' b' c' hab' hbc' =
      t.ω₁δ a b c hab hbc ≫ Functor.whiskerRight (t.ω₁.map (homMk₁ (φ.app 0) (φ.app 1))) _ := by
  ext
  dsimp
  simp only [ω₁δ_app, ← Functor.map_comp, NatTrans.naturality_assoc, Functor.comp_map,
    Category.assoc, ← Functor.map_comp_assoc, NatTrans.naturality_app_assoc,
    Functor.whiskeringRight_obj_map, Functor.whiskerRight_app, NatTrans.naturality]
  congr 2
  simp only [Functor.map_comp, Category.assoc]
  have h₁ := t.eTruncLTGEIsoGELT_naturality_app a b hab a' b' hab' (homMk₁ (φ.app 0) (φ.app 1))
  rw [← reassoc_of% dsimp% h₁, ← eTruncLTGEIsoGELT_hom_naturality,
    ← eTruncLTGEIsoGELT_hom_naturality, ← t.eTruncLT_map_app_eTruncLTι_app (φ.app 2)]
  simp only [↓NatTrans.naturality_assoc, ↓← Functor.map_comp_assoc]
  simp

/-- The functorial (distinguished) triangles that are part of the spectral
object attached to objects in a triangulated category equipped with a t-structure. -/
@[simps!]
noncomputable def triangleω₁δ : C ⥤ Triangle C :=
  Triangle.functorMk (t.ω₁.map (twoδ₂Toδ₁' a b c hab hbc))
    (t.ω₁.map (twoδ₁Toδ₀' a b c hab hbc)) (t.ω₁δ a b c hab hbc)

set_option backward.defeqAttrib.useBackward true in
/-- The triangle `(t.triangleω₁δ a b c hab hbc).obj X` is isomorphic to
the (distinguished) triangle obtained by applying the functor `t.eTriangleLTGE.obj b`
to the object `(t.eTruncGE.obj a).obj ((t.eTruncLT.obj c).obj X)`. -/
noncomputable def triangleω₁δObjIso (X : C) :
    (t.triangleω₁δ a b c hab hbc).obj X ≅
      (t.eTriangleLTGE.obj b).obj ((t.ω₁.obj (mk₁ (homOfLE (hab.trans hbc)))).obj X) := by
  refine Triangle.isoMk _ _ ((t.eTruncGE.obj a).mapIso ((t.eTruncLTLTIsoLT c b hbc).symm.app X) ≪≫
    (t.eTruncLTGEIsoGELT a b).symm.app _) (Iso.refl _) ((t.eTruncGEIsoGEGE a b hab).app _) ?_ ?_ ?_
  · dsimp
    simp only [triangleω₁δ_obj_mor₁, homOfLE_leOfHom, Category.comp_id, Category.assoc]
    rw [← cancel_epi ((t.eTruncGE.obj a).map ((t.eTruncLTLTIsoLT c b hbc).hom.app X)),
      ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id, Category.id_comp,
      ← cancel_epi ((t.eTruncLTGEIsoGELT a b).hom.app ((t.eTruncLT.obj c).obj X)),
      Iso.hom_inv_id_app_assoc, eTruncLTLTIsoLT_hom, eTruncLTLTToLT_app,
      ← Functor.map_comp, eTruncLT_obj_map_eTruncLTι_app_eTruncLT_map_app]
    simp
  · dsimp
    simp only [triangleω₁δ_obj_mor₂, eTruncGEToGEGE_app, Category.id_comp,
      ← t.eTruncGEπ_app_eTruncGE_map_app (homOfLE hab), ← NatTrans.naturality,
      eTruncGE_obj_map_eTruncGEπ_app]
  · simp [← Functor.map_comp_assoc, ← Functor.map_comp]

lemma triangleω₁δ_distinguished (X : C) : (t.triangleω₁δ a b c hab hbc).obj X ∈ distTriang _ :=
  isomorphic_distinguished _ (t.eTriangleLTGE_distinguished b _) _
    (t.triangleω₁δObjIso a b c hab hbc X)

end

/-- The spectral object attached to an object `X : C` in a category
equipped with a t-structure. It consists of all truncations of `X`. -/
@[simps ω₁]
noncomputable def spectralObject (X : C) : SpectralObject C EInt where
  ω₁ := t.ω₁ ⋙ (evaluation _ _).obj X
  δ'.app D := (t.ω₁δ (D.obj 0) (D.obj 1) (D.obj 2)
    (leOfHom (D.map' 0 1)) (leOfHom (D.map' 1 2))).app X
  δ'.naturality {D D'} φ := by
    obtain ⟨a, b, c, f, g, rfl⟩ := mk₂_surjective D
    obtain ⟨a', b', c', f', g', rfl⟩ := mk₂_surjective D'
    exact NatTrans.congr_app (t.ω₁δ_naturality a b c (leOfHom f) (leOfHom g)
      a' b' c' (leOfHom f') (leOfHom g') φ) X
  distinguished' D := by
    obtain ⟨a, b, c, f, g, rfl⟩ := mk₂_surjective D
    exact t.triangleω₁δ_distinguished a b c (leOfHom f) (leOfHom g) X

@[simp]
lemma spectralObject_δ (X : C) {a b c : EInt} (f : a ⟶ b) (g : b ⟶ c) :
    (t.spectralObject X).δ f g = (t.ω₁δ a b c (leOfHom f) (leOfHom g)).app X := rfl

/-- The spectral object attached to an object `X : C` in a category
equipped with a t-structure, as a functor `C ⥤ SpectralObject C EInt`. -/
@[simps]
noncomputable def spectralObjectFunctor : C ⥤ SpectralObject C EInt where
  obj := t.spectralObject
  map φ :=
    { hom := Functor.whiskerLeft _ ((evaluation _ _).map φ)
      comm f g := ((t.ω₁δ _ _ _ (leOfHom f) (leOfHom g)).naturality φ).symm }

end TStructure

end Triangulated

end CategoryTheory
