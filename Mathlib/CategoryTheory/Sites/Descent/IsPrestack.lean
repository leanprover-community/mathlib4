/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Cat
public import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.Strict.Pseudofunctor
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Prestacks: descent of morphisms

Let `C` be a category and `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`.
Given `S : C`, and objects `M` and `N` in `F.obj (.mk (op S))`,
we define a presheaf of types `F.presheafHom M N` on the category `Over S`:
its sections on an object `T : Over S` corresponding to a morphism `p : X ⟶ S`
are the type of morphisms `p^* M ⟶ p^* N`. We shall say that
`F` satisfies the descent of morphisms for a Grothendieck topology `J`
if these presheaves are all sheaves (typeclass `F.IsPrestack J`).

## Terminological note

In this file, we use the language of pseudofunctors to formalize prestacks.
Similar notions could also be phrased in terms of fibered categories.
In the mathematical literature, various uses of the words "prestacks" and
"stacks" exists. Our definitions are consistent with Giraud's definition II 1.2.1
in *Cohomologie non abélienne*: a prestack is defined by the descent of morphisms
condition with respect to a Grothendieck topology, and a stack by the effectiveness
of the descent. However, contrary to Laumon and Moret-Bailly in *Champs algébriques* 3.1,
we do not require that target categories are groupoids.

## References
* [Jean Giraud, *Cohomologie non abélienne*][giraud1971]
* [Gérard Laumon and Laurent Moret-Bailly, *Champs algébriques*][laumon-morel-bailly-2000]

-/

@[expose] public section

universe v' v u' u

namespace CategoryTheory

open Opposite Bicategory

namespace Pseudofunctor

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}

namespace LocallyDiscreteOpToCat

/-- Given a pseudofunctor `F` from  `LocallyDiscrete Cᵒᵖ` to `Cat`, objects `M₁` and `M₂`
of `F` over `X₁` and `X₂`, morphisms `f₁ : Y ⟶ X₁` and `f₂ : Y ⟶ X₂`, this is a version
of the pullback map `(f₁^* M₁ ⟶ f₂^* M₂) → (g^* (f₁^* M₁) ⟶ g^* (f₂^* M₂))` by a
morphism `g : Y' ⟶ Y`, where we actually replace `g^* (f₁^* M₁)` by `gf₁^* M₁`
where `gf₁ : Y' ⟶ X₁` is a morphism such that `g ≫ f₁ = gf₁` (and similarly for `M₂`). -/
def pullHom ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch)
    (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    (F.map gf₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map gf₂.op.toLoc).toFunctor.obj M₂ :=
  (F.mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc (by aesop)).hom.toNatTrans.app _ ≫
    (F.map g.op.toLoc).toFunctor.map φ ≫
      (F.mapComp' f₂.op.toLoc g.op.toLoc gf₂.op.toLoc (by aesop)).inv.toNatTrans.app _

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma map_eq_pullHom
    ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    (F.map g.op.toLoc).toFunctor.map φ =
    (F.mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc (by aesop)).inv.toNatTrans.app _ ≫
    pullHom φ g gf₁ gf₂ hgf₁ hgf₂ ≫
    (F.mapComp' f₂.op.toLoc g.op.toLoc gf₂.op.toLoc (by aesop)).hom.toNatTrans.app _ := by
  simp [Cat.Hom.comp_toFunctor, pullHom, ← reassoc_of% Cat.Hom₂.comp_app, ← Cat.Hom₂.comp_app]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma pullHom_id ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) :
      pullHom φ (𝟙 _) f₁ f₂ = φ := by
  simp [pullHom, mapComp'_comp_id_hom_app, mapComp'_comp_id_inv_app,
    ← reassoc_of% Cat.Hom₂.comp_app, Iso.inv_hom_id]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma pullHom_pullHom
    ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) ⦃Y'' : C⦄ (g' : Y'' ⟶ Y') (g'f₁ : Y'' ⟶ X₁)
    (g'f₂ : Y'' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch)
    (hg'f₁ : g' ≫ gf₁ = g'f₁ := by cat_disch) (hg'f₂ : g' ≫ gf₂ = g'f₂ := by cat_disch) :
    pullHom (pullHom φ g gf₁ gf₂ hgf₁ hgf₂) g' g'f₁ g'f₂ hg'f₁ hg'f₂ =
      pullHom φ (g' ≫ g) g'f₁ g'f₂ := by
  dsimp [pullHom]
  rw [Functor.map_comp_assoc, Functor.map_comp_assoc,
    F.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app _ _ _ _ _ _ _ rfl (by aesop),
    F.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_app_assoc _ _ _ _ _ _ _ rfl (by aesop),
    mapComp'_inv_naturality_assoc,
      ← reassoc_of% Cat.Hom₂.comp_app, Iso.hom_inv_id, Cat.Hom₂.id_app, Category.id_comp]

end LocallyDiscreteOpToCat

open LocallyDiscreteOpToCat

section

variable (F) {S : C} (M N : F.obj (.mk (op S)))

/-- If `F` is a pseudofunctor from `Cᵒᵖ` to `Cat`, and `M` and `N` are objects in
`F.obj (.mk (op S))`, this is the presheaf of morphisms from `M` to `N`: it sends
an object `T : Over S` corresponding to a morphism `p : X ⟶ S` to the type
of morphisms $p^* M ⟶ p^* N$. -/
@[simps]
def presheafHom : (Over S)ᵒᵖ ⥤ Type v' where
  obj T := (F.map (.toLoc T.unop.hom.op)).toFunctor.obj M ⟶
    (F.map (.toLoc T.unop.hom.op)).toFunctor.obj N
  map {T₁ T₂} p := TypeCat.ofHom (fun f ↦ pullHom f p.unop.left T₂.unop.hom T₂.unop.hom)

/-- The bijection `(M ⟶ N) ≃ (F.presheafHom M N).obj (op (Over.mk (𝟙 S)))`. -/
@[simps! -isSimp]
def presheafHomObjHomEquiv {M N : (F.obj (.mk (op S)))} :
    (M ⟶ N) ≃ (F.presheafHom M N).obj (op (Over.mk (𝟙 S))) :=
  Iso.homCongr ((Cat.Hom.toNatIso (F.mapId (.mk (op S)))).symm.app M)
    ((Cat.Hom.toNatIso (F.mapId (.mk (op S)))).symm.app N)

set_option backward.isDefEq.respectTransparency false in
/-- Compatibility isomorphism of `Pseudofunctor.presheafHom` with "restrictions". -/
def overMapCompPresheafHomIso {S' : C} (q : S' ⟶ S) :
    (Over.map q).op ⋙ F.presheafHom M N ≅
      F.presheafHom ((F.map (.toLoc q.op)).toFunctor.obj M)
        ((F.map (.toLoc q.op)).toFunctor.obj N) :=
  NatIso.ofComponents (fun T ↦ Equiv.toIso (by
    letI e := Cat.Hom.toNatIso (F.mapComp' (.toLoc q.op) (.toLoc T.unop.hom.op)
      (.toLoc ((Over.map q).obj T.unop).hom.op))
    exact (Iso.homFromEquiv (e.app M)).trans (Iso.homToEquiv (e.app N)))) (by
      rintro ⟨T₁⟩ ⟨T₂⟩ ⟨f⟩
      ext g
      dsimp [pullHom]
      simp only [Category.assoc, Functor.map_comp]
      rw [F.mapComp'₀₁₃_inv_comp_mapComp'₀₂₃_hom_app_assoc _ _ _ _ _ _ rfl _ rfl,
        F.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app _ _ _ _ _ _ _ _ (by
          simp only [← Quiver.Hom.comp_toLoc, ← op_comp, Over.w_assoc])])

end

variable (F)

/-- The property that a pseudofunctor `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`
satisfies the descent property for morphisms, i.e. is a prestack.
(See the terminological note in the introduction of the file `Sites.Descent.IsPrestack`.) -/
@[stacks 026F "(2)"]
class IsPrestack (J : GrothendieckTopology C) : Prop where
  isSheaf (J) {S : C} (M N : F.obj (.mk (op S))) :
    Presheaf.IsSheaf (J.over S) (F.presheafHom M N)

/-- If `F` is a prestack from `Cᵒᵖ` to `Cat` relatively to a Grothendieck topology `J`,
and `M` and `N` are two objects in `F.obj (.mk (op S))`, this is the sheaf of
morphisms from `M` to `N`: it sends an object `T : Over S` corresponding to
a morphism `p : X ⟶ S` to the type of morphisms $p^* M ⟶ p^* N$. -/
@[simps]
def sheafHom (J : GrothendieckTopology C) [F.IsPrestack J]
    {S : C} (M N : F.obj (.mk (op S))) :
    Sheaf (J.over S) (Type v') where
  obj := F.presheafHom M N
  property := IsPrestack.isSheaf _ _ _

end Pseudofunctor

end CategoryTheory
