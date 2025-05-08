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

variable {C : Type u} [Category.{v} C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
  {S : C} (M N : F.obj (.mk (op S)))

/-- If `F` is a pseudofunctor from `Cᵒᵖ` to `Cat`, and `M` and `N` are objects in
`F.obj (.mk (op S))`, this is the presheaf of morphisms from `M` to `N`: it sends
an object `T : Over S` corresponding to a morphism `p : X ⟶ S` to the type
of morphisms $$p^* M ⟶ p^* N$$. -/
@[simps -isSimp obj map]
def presheafHom : (Over S)ᵒᵖ ⥤ Type v' where
  obj T := (F.map (.toLoc T.unop.hom.op)).obj M ⟶ (F.map (.toLoc T.unop.hom.op)).obj N
  map {T₁ T₂} p f := by
    letI e := F.mapComp' (.toLoc T₁.unop.hom.op) (.toLoc p.unop.left.op)
      (.toLoc T₂.unop.hom.op) (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, Over.w p.unop])
    exact e.hom.app M ≫ (F.map (.toLoc p.unop.left.op)).map f ≫ e.inv.app N
  map_id T := by
    ext
    simp [mapComp'_comp_id_hom_app, mapComp'_comp_id_inv_app]
  map_comp {T₁ T₂ T₃} p q := by
    ext f
    dsimp
    rw [Functor.map_comp_assoc, Functor.map_comp_assoc,
      F.map_map_mapComp'_inv_app_comp_mapComp'_inv_app _ _ _ _ _ _
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, Over.w p.unop]) rfl
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, Over.w q.unop]),
      F.mapComp'_hom_app_comp_map_map_mapComp'_hom_app_assoc _ _ _ _ _ _
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, Over.w p.unop]) rfl
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, Over.w q.unop]),
      ← mapComp'_hom_naturality_assoc, Iso.hom_inv_id_app_assoc]

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
      dsimp
      erw [Iso.homToEquiv_apply, Iso.homToEquiv_apply,
        Iso.homFromEquiv_apply, Iso.homFromEquiv_apply]
      dsimp [presheafHom_obj, presheafHom_map]
      simp only [Functor.map_comp, Category.assoc]
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
