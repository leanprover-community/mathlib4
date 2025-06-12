/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Closed.FunctorCategory.Basic
import Mathlib.CategoryTheory.Localization.Monoidal
import Mathlib.CategoryTheory.Sites.Localization
import Mathlib.CategoryTheory.Sites.SheafHom

/-!
# Monoidal category structure on categories of sheaves

If `A` is a closed braided category with suitable limits,
and `J` is a Grothendieck topology with `HasWeakSheafify J A`,
then `Sheaf J A` can be equipped with a monoidal category
structure. This is not made an instance as in some cases
it may conflict with monoidal structure deduced from
chosen finite products.

## TODO

* show that the monoidal category structure on sheaves is closed,
  and that the internal hom can be defined in such a way that the
  underlying presheaf is the internal hom in the category of presheaves.
  Note that a `MonoidalClosed` instance on sheaves can already be obtained
  abstractly using the material in `CategoryTheory.Monoidal.Braided.Reflection`.

-/

universe v v' u u'

namespace CategoryTheory

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {A : Type u} [Category.{v} A] [MonoidalCategory A]

open Opposite Limits MonoidalCategory MonoidalClosed Enriched.FunctorCategory

namespace Presheaf

variable [MonoidalClosed A]

/-- Relation between `functorEnrichedHom` and `presheafHom`. -/
noncomputable def functorEnrichedHomCoyonedaObjEquiv (M : A) (F G : Cᵒᵖ ⥤ A)
    [HasFunctorEnrichedHom A F G] (X : C) :
    (functorEnrichedHom A F G ⋙ coyoneda.obj (op M)).obj (op X) ≃
    (presheafHom (F ⊗ (Functor.const _).obj M) G).obj (op X) where
  toFun f :=
    { app j := MonoidalClosed.uncurry (f ≫ enrichedHomπ A _ _ (Under.mk j.unop.hom.op))
      naturality j j' φ := by
        dsimp
        rw [tensorHom_id, ← uncurry_natural_right, ← uncurry_pre_app, Category.assoc,
          Category.assoc, ← enrichedOrdinaryCategorySelf_eHomWhiskerRight,
          ← enrichedOrdinaryCategorySelf_eHomWhiskerLeft]
        congr 2
        exact (enrichedHom_condition A (Under.forget (op X) ⋙ F) (Under.forget (op X) ⋙ G)
          (i := Under.mk j.unop.hom.op) (j := Under.mk j'.unop.hom.op)
            (Under.homMk φ.unop.left.op (Quiver.Hom.unop_inj (by simp)))).symm }
  invFun g :=
    end_.lift (fun j ↦ MonoidalClosed.curry (g.app (op (Over.mk j.hom.unop)))) (fun j j' φ ↦ by
      dsimp
      rw [enrichedOrdinaryCategorySelf_eHomWhiskerRight,
        enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
        curry_pre_app, ← curry_natural_right]
      congr 1
      let α : Over.mk j'.hom.unop ⟶ Over.mk j.hom.unop := Over.homMk φ.right.unop
        (Quiver.Hom.op_inj (by simp))
      simpa using (g.naturality α.op).symm )
  left_inv f := by
    dsimp
    ext j
    dsimp
    simp only [curry_uncurry, end_.lift_π]
    rfl
  right_inv g := by
    dsimp
    ext j
    dsimp
    simp only [uncurry_curry, end_.lift_π]
    rfl

lemma functorEnrichedHomCoyonedaObjEquiv_naturality
    {M : A} {F G : Cᵒᵖ ⥤ A} {X Y : C} (f : X ⟶ Y)
    [HasFunctorEnrichedHom A F G]
    (y : (functorEnrichedHom A F G ⋙ coyoneda.obj (op M)).obj (op Y)) :
    functorEnrichedHomCoyonedaObjEquiv M F G X
      (y ≫ precompEnrichedHom' _ (Under.map f.op) (Iso.refl _) (Iso.refl _)) =
    (presheafHom (F ⊗ (Functor.const Cᵒᵖ).obj M) G).map f.op
      (functorEnrichedHomCoyonedaObjEquiv M F G Y y) := by
  dsimp
  ext ⟨j⟩
  simp [functorEnrichedHomCoyonedaObjEquiv, presheafHom]
  rfl

lemma isSheaf_functorEnrichedHom (F G : Cᵒᵖ ⥤ A) (hG : Presheaf.IsSheaf J G)
    [HasFunctorEnrichedHom A F G] :
    Presheaf.IsSheaf J (functorEnrichedHom A F G) := fun M ↦ by
  rw [Presieve.isSheaf_iff_of_nat_equiv
    (functorEnrichedHomCoyonedaObjEquiv M F G)
    (fun _ _ _ _ ↦ functorEnrichedHomCoyonedaObjEquiv_naturality _ _)]
  rw [← isSheaf_iff_isSheaf_of_type]
  exact Presheaf.IsSheaf.hom (F ⊗ (Functor.const _).obj M) G hG

end Presheaf

namespace GrothendieckTopology

variable [MonoidalClosed A]
  [∀ (F₁ F₂ : Cᵒᵖ ⥤ A), HasFunctorEnrichedHom A F₁ F₂]
  [∀ (F₁ F₂ : Cᵒᵖ ⥤ A), HasEnrichedHom A F₁ F₂]

namespace W

open MonoidalClosed.FunctorCategory

lemma whiskerLeft {G₁ G₂ : Cᵒᵖ ⥤ A} {g : G₁ ⟶ G₂} (hg : J.W g) (F : Cᵒᵖ ⥤ A) :
    J.W (F ◁ g) := fun H h ↦ by
  have := hg _ (Presheaf.isSheaf_functorEnrichedHom F H h)
  rw [← Function.Bijective.of_comp_iff' (f := MonoidalClosed.curry)
    ((ihom.adjunction _).homEquiv _ _).bijective]
  rw [← Function.Bijective.of_comp_iff (g := MonoidalClosed.curry) _
    ((ihom.adjunction _).homEquiv _ _).bijective] at this
  convert this using 1
  ext α : 1
  dsimp
  rw [curry_natural_left]

lemma whiskerRight [BraidedCategory A]
    {F₁ F₂ : Cᵒᵖ ⥤ A} {f : F₁ ⟶ F₂} (hf : J.W f) (G : Cᵒᵖ ⥤ A) :
    J.W (f ▷ G) :=
  (J.W.arrow_mk_iso_iff (Arrow.isoMk (β_ F₁ G) (β_ F₂ G))).2 (hf.whiskerLeft G)

instance monoidal [BraidedCategory A] : (J.W (A := A)).IsMonoidal where
  whiskerLeft F _ _ _ hg := hg.whiskerLeft F
  whiskerRight _ hf G := hf.whiskerRight G

end W

end GrothendieckTopology

namespace Sheaf

variable (J A)

/-- The monoidal category structure on `Sheaf J A` that is obtained
by localization of the monoidal category structure on the category
of presheaves. -/
noncomputable def monoidalCategory [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A] :
    MonoidalCategory (Sheaf J A) :=
  inferInstanceAs (MonoidalCategory
    (LocalizedMonoidal (L := presheafToSheaf J A) (W := J.W) (Iso.refl _)))

noncomputable instance [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A] :
    letI := monoidalCategory J A
    (presheafToSheaf J A).Monoidal :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (L := presheafToSheaf J A) (W := J.W) (Iso.refl _)).Monoidal

noncomputable example
    [HasWeakSheafify J A] [MonoidalClosed A] [BraidedCategory A]
    [∀ (F₁ F₂ : Cᵒᵖ ⥤ A), HasFunctorEnrichedHom A F₁ F₂]
    [∀ (F₁ F₂ : Cᵒᵖ ⥤ A), HasEnrichedHom A F₁ F₂] :
    MonoidalCategory (Sheaf J A) :=
  monoidalCategory J A

end Sheaf

end CategoryTheory
