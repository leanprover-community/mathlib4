/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Bicategory.Functor.Cat
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Over

/-!
# Descent of morphisms

Let `C` be a category and `F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat`.
Given `S : C`, and objects `M` and `N` in `F.obj (.mk (op S))`,
we define a presheaf of types `F.presheafHom M N` on the category `Over S`:
its sections on a object `T : Over S` corresponding to a morphism `p : X ⟶ S`
are the type of morphisms `p^* M ⟶ p^* N`. We shall say that
`F` satisfies the descent of morphisms for a Grothendieck topology `J`
if these presheaves are all sheaves (typeclass `F.HasDescentForMorphisms J`).

## TODO

* Relate this notion to the property that for any covering family `f i : X i ⟶ S`
for `J`, the functor `F.obj S` to the category of objects in `F.obj (X i)` for all `i`
equipped with a descent datum is fully faithful.
* Define a typeclass `HasEffectiveDescent` extending `HasDescentOfMorphisms`
by saying that the functors mentionned above are essentially surjective.

-/

universe v' v u' u

namespace CategoryTheory

open Opposite Bicategory

namespace Pseudofunctor

variable {C : Type u} [Category.{v} C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}

namespace LocallyDiscreteOpToCat

def pullHom ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : (F.map f₁.op.toLoc).obj M₁ ⟶ (F.map f₂.op.toLoc).obj M₂) ⦃Y' : C⦄ (g : Y' ⟶ Y)
    (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁ := by aesop_cat)
    (hgf₂ : g ≫ f₂ = gf₂ := by aesop_cat) :
    (F.map gf₁.op.toLoc).obj M₁ ⟶ (F.map gf₂.op.toLoc).obj M₂ :=
  (F.mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc (by aesop)).hom.app _ ≫
    (F.map g.op.toLoc).map φ ≫
      (F.mapComp' f₂.op.toLoc g.op.toLoc gf₂.op.toLoc (by aesop)).inv.app _

@[reassoc]
lemma map_eq_pullHom
    ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : (F.map f₁.op.toLoc).obj M₁ ⟶ (F.map f₂.op.toLoc).obj M₂) ⦃Y' : C⦄ (g : Y' ⟶ Y)
    (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁)
    (hgf₂ : g ≫ f₂ = gf₂) :
    (F.map g.op.toLoc).map φ =
    (F.mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc (by aesop)).inv.app _ ≫
    pullHom φ g gf₁ gf₂ hgf₁ hgf₂ ≫
    (F.mapComp' f₂.op.toLoc g.op.toLoc gf₂.op.toLoc (by aesop)).hom.app _ := by
  simp [pullHom]

@[simp]
lemma pullHom_id ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : (F.map f₁.op.toLoc).obj M₁ ⟶ (F.map f₂.op.toLoc).obj M₂) :
      pullHom φ (𝟙 _) f₁ f₂ = φ := by
  simp [pullHom, mapComp'_comp_id_hom_app, mapComp'_comp_id_inv_app]

@[simp]
lemma pullHom_pullHom
    ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : (F.map f₁.op.toLoc).obj M₁ ⟶ (F.map f₂.op.toLoc).obj M₂) ⦃Y' : C⦄ (g : Y' ⟶ Y)
    (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) ⦃Y'' : C⦄
    (g' : Y'' ⟶ Y') (g'f₁ : Y'' ⟶ X₁) (g'f₂ : Y'' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁ := by aesop_cat)
    (hgf₂ : g ≫ f₂ = gf₂ := by aesop_cat)
    (hg'f₁ : g' ≫ gf₁ = g'f₁ := by aesop_cat)
    (hg'f₂ : g' ≫ gf₂ = g'f₂ := by aesop_cat) :
    pullHom (pullHom φ g gf₁ gf₂ hgf₁ hgf₂) g' g'f₁ g'f₂ hg'f₁ hg'f₂ =
      pullHom φ (g' ≫ g) g'f₁ g'f₂ := by
  dsimp [pullHom]
  rw [Functor.map_comp_assoc, Functor.map_comp_assoc,
    F.map_map_mapComp'_inv_app_comp_mapComp'_inv_app _ _ _ _ _ _ _ rfl (by aesop),
    F.mapComp'_hom_app_comp_map_map_mapComp'_hom_app_assoc _ _ _ _ _ _ _ rfl (by aesop),
    mapComp'_inv_naturality_assoc, Iso.hom_inv_id_app_assoc]

end LocallyDiscreteOpToCat

open LocallyDiscreteOpToCat

variable (F) {S : C} (M N : F.obj (.mk (op S)))
/-- If `F` is a pseudofunctor from `Cᵒᵖ` to `Cat`, and `M` and `N` are objects in
`F.obj (.mk (op S))`, this is the presheaf of morphisms from `M` to `N`: it sends
an object `T : Over S` corresponding to a morphism `p : X ⟶ S` to the type
of morphisms $$p^* M ⟶ p^* N$$. -/
@[simps]
def presheafHom : (Over S)ᵒᵖ ⥤ Type v' where
  obj T := (F.map (.toLoc T.unop.hom.op)).obj M ⟶ (F.map (.toLoc T.unop.hom.op)).obj N
  map {T₁ T₂} p f := pullHom f p.unop.left T₂.unop.hom T₂.unop.hom

/-- Compatiblity isomorphism of `Pseudofunctor.presheafHom` with the "restrictions". -/
def overMapCompPresheafHomIso {S' : C} (q : S' ⟶ S) :
    (Over.map q).op ⋙ F.presheafHom M N ≅
      F.presheafHom ((F.map (.toLoc q.op)).obj M) ((F.map (.toLoc q.op)).obj N) :=
  NatIso.ofComponents (fun T ↦ Equiv.toIso (by
    letI e := F.mapComp' (.toLoc q.op) (.toLoc T.unop.hom.op)
      (.toLoc ((Over.map q).obj T.unop).hom.op)
    exact (Iso.homFromEquiv (e.app M)).trans (Iso.homToEquiv (e.app N)))) (by
      rintro ⟨T₁⟩ ⟨T₂⟩ ⟨f⟩
      ext g
      dsimp [pullHom]
      simp only [Category.assoc, Functor.map_comp]
      rw [F.mapComp'_inv_app_comp_mapComp'_hom_app_assoc _ _ _ _ _ _ rfl _ rfl,
        F.mapComp'_inv_app_comp_mapComp'_hom_app' _ _ _ _ _ _ _ _ rfl])

/-- The property that a pseudofunctor `F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat`
satisfies the descent property for morphisms. -/
class IsPrestack (J : GrothendieckTopology C) : Prop where
  isSheaf {S : C} (M N : F.obj (.mk (op S))) :
    Presheaf.IsSheaf (J.over S) (F.presheafHom M N)

variable (J : GrothendieckTopology C) [F.IsPrestack J]

/-- If `F` is a pseudofunctor from `Cᵒᵖ` to `Cat` which satisfies the descent
of morphisms for a Grothendieck topology `J`, and `M` and `N` are to objects in
`F.obj (.mk (op S))`, this is the esheaf of morphisms from `M` to `N`: it sends
an object `T : Over S` corresponding to a morphism `p : X ⟶ S` to the type
of morphisms $$p^* M ⟶ p^* N$$. -/
@[simps]
def sheafHom : Sheaf (J.over S) (Type v') where
  val := F.presheafHom M N
  cond := IsPrestack.isSheaf _ _

end Pseudofunctor

end CategoryTheory
