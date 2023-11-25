/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Sites.Over

/-! Internal hom of sheaves

In this file, given two sheaves `F` and `G` in `Sheaf J A`
(with `J : GrothendieckTopology C`), we shall define a sheaf of types
`Sheaf.internalHom F G` which sends `X : C` to the type of morphisms
between the restrictions of `F` and `G` to the categories `Over X`.

We first define `Presheaf.internalHom F G` when `F` and `G` are
presheaves `Cᵒᵖ ⥤ A` and show that it is a sheaf when `G` is a sheaf.

-/

universe v v' u u'

namespace CategoryTheory

open Category Opposite Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Type u'} [Category.{v'} A]

namespace Presheaf

variable (F G : Cᵒᵖ ⥤ A)

/-- Given two presheaves `F` and `G` on a category `C` with values in a category `A`,
this `internalHom F G` is the presheaf of types which sends an object `X : C`
to the type of morphisms between the "restrictions" of `F` and `G` to the category `Over X`. -/
@[simps! obj]
def internalHom : Cᵒᵖ ⥤ Type _ where
  obj X := (Over.forget X.unop).op ⋙ F ⟶ (Over.forget X.unop).op ⋙ G
  map f := whiskerLeft (Over.map f.unop).op
  map_id := by
    rintro ⟨X⟩
    dsimp
    ext φ ⟨Y⟩
    simpa [Over.mapId] using φ.naturality ((Over.mapId X).hom.app Y).op
  map_comp := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ ⟨f : Y ⟶ X⟩ ⟨g : Z ⟶ Y⟩
    dsimp
    ext φ ⟨W⟩
    simpa [Over.mapComp] using φ.naturality ((Over.mapComp g f).hom.app W).op

variable {F G}

/-- Equational lemma for the presheaf structure on `Presheaf.internalHom`.
It is advisable to use this lemma rather than `dsimp [internalHom]` which may result
in the need to prove equalities of objects in an `Over` category. -/
lemma internalHom_map_app {X Y Z : C} (f : Z ⟶ Y) (g : Y ⟶ X) (h : Z ⟶ X) (w : f ≫ g = h)
    (α : (internalHom F G).obj (op X)) :
    ((internalHom F G).map g.op α).app (op (Over.mk f)) =
      α.app (op (Over.mk h)) := by
  subst w
  rfl

@[simp]
lemma internalHom_map_app_op_mk_id {X Y : C} (g : Y ⟶ X)
    (α : (internalHom F G).obj (op X)) :
    ((internalHom F G).map g.op α).app (op (Over.mk (𝟙 Y))) =
      α.app (op (Over.mk g)) :=
  internalHom_map_app (𝟙 Y) g g (by simp) α

variable (F G)

/-- The sections of the presheaf `internalHom F G` identify to morphisms `F ⟶ G`. -/
def internalHomSectionsEquiv : (internalHom F G).sections ≃ (F ⟶ G) where
  toFun s :=
    { app := fun X => (s.1 X).app ⟨Over.mk (𝟙 _)⟩
      naturality := by
        rintro ⟨X₁⟩ ⟨X₂⟩ ⟨f : X₂ ⟶ X₁⟩
        dsimp
        refine' Eq.trans _ ((s.1 ⟨X₁⟩).naturality
          (Over.homMk f : Over.mk f ⟶ Over.mk (𝟙 X₁)).op)
        erw [← s.2 f.op, internalHom_map_app_op_mk_id]
        rfl }
  invFun f := ⟨fun X => whiskerLeft _ f, fun _ => rfl⟩
  left_inv s := by
    dsimp
    ext ⟨X⟩ ⟨Y : Over X⟩
    have H := s.2 Y.hom.op
    dsimp at H ⊢
    rw [← H]
    apply internalHom_map_app_op_mk_id
  right_inv f := rfl

variable {F G}

lemma InternalHom.isAmalgamation_iff {X : C} (S : Sieve X)
    (x : Presieve.FamilyOfElements (internalHom F G) S.arrows)
    (hx : x.Compatible) (y : (internalHom F G).obj (op X)) :
    x.IsAmalgamation y ↔ ∀ (Y : C) (g : Y ⟶ X) (hg : S g),
      y.app (op (Over.mk g)) = (x g hg).app (op (Over.mk (𝟙 Y))) := by
  constructor
  · intro h Y g hg
    rw [← h g hg, internalHom_map_app_op_mk_id]
  · intro h Y g hg
    dsimp
    ext ⟨W : Over Y⟩
    refine (h W.left (W.hom ≫ g) (S.downward_closed hg _)).trans ?_
    have H := hx (𝟙 _) W.hom (S.downward_closed hg W.hom) hg (by simp)
    dsimp at H
    simp only [Functor.map_id, FunctorToTypes.map_id_apply] at H
    rw [H, internalHom_map_app_op_mk_id]
    rfl

variable (F G)

lemma internalHom_isSheafFor {X : C} (S : Sieve X)
    (hG : ∀ ⦃Y : C⦄ (f : Y ⟶ X), IsLimit (G.mapCone (S.pullback f).arrows.cocone.op)) :
    Presieve.IsSheafFor (internalHom F G) S.arrows := by
  intro x hx
  apply exists_unique_of_exists_of_unique
  · have Φ : ∀ {Y : C} (g : Y ⟶ X), ∃ (φ : F.obj (op Y) ⟶ G.obj (op Y)),
      ∀ {Z : C} (p : Z ⟶ Y) (hp : S (p ≫ g)), φ ≫ G.map p.op =
        F.map p.op ≫ (x (p ≫ g) hp).app ⟨Over.mk (𝟙 Z)⟩ := fun {Y} g => by
        let c : Cone ((Presieve.diagram (Sieve.pullback g S).arrows).op ⋙ G) :=
          { pt := F.obj (op Y)
            π :=
              { app := fun ⟨Z, hZ⟩ => F.map Z.hom.op ≫ (x _ hZ).app (op (Over.mk (𝟙 _)))
                naturality := by
                  rintro ⟨Z₁, hZ₁⟩ ⟨Z₂, hZ₂⟩ ⟨f : Z₂ ⟶ Z₁⟩
                  dsimp
                  rw [id_comp, assoc]
                  have H := hx f.left (𝟙 _) hZ₁ hZ₂ (by simp)
                  simp only [internalHom_obj, unop_op, Functor.id_obj, op_id,
                    FunctorToTypes.map_id_apply] at H
                  let φ : Over.mk f.left ⟶ Over.mk (𝟙 Z₁.left) := Over.homMk f.left
                  have H' := (x (Z₁.hom ≫ g) hZ₁).naturality φ.op
                  dsimp at H H' ⊢
                  erw [← H, ← H', internalHom_map_app_op_mk_id, ← F.map_comp_assoc,
                    ← op_comp, Over.w f] } }
        use (hG g).lift c
        intro Z p hp
        exact ((hG g).fac c ⟨Over.mk p, hp⟩)
    let app : ∀ {Y : C} (_ : Y ⟶ X), F.obj (op Y) ⟶ G.obj (op Y) := fun g => (Φ g).choose
    have happ : ∀ {Y : C} (g : Y ⟶ X) {Z : C} (p : Z ⟶ Y) (hp : S (p ≫ g)),
      app g ≫ G.map p.op = F.map p.op ≫ (x (p ≫ g) hp).app ⟨Over.mk (𝟙 Z)⟩ :=
        fun g => (Φ g).choose_spec
    refine ⟨
      { app := fun Y => app Y.unop.hom
        naturality := by
          rintro ⟨Y₁ : Over X⟩ ⟨Y₂ : Over X⟩ ⟨φ : Y₂ ⟶ Y₁⟩
          apply (hG Y₂.hom).hom_ext
          rintro ⟨Z : Over Y₂.left, hZ⟩
          change (F.map φ.left.op ≫ app Y₂.hom) ≫ G.map Z.hom.op =
            (app Y₁.hom ≫ G.map φ.left.op) ≫ G.map Z.hom.op
          rw [assoc, assoc, happ Y₂.hom Z.hom hZ, ← G.map_comp, ← op_comp,
            happ Y₁.hom (Z.hom ≫ φ.left) (by simpa using hZ), ← F.map_comp_assoc, op_comp]
          congr 3
          simp }, ?_⟩
    rw [InternalHom.isAmalgamation_iff _ _ hx]
    intro Y g hg
    dsimp
    have H := happ g (𝟙 _) (by simpa using hg)
    rw [op_id, G.map_id, comp_id, F.map_id, id_comp] at H
    exact H.trans (by congr; simp)
  · intro y₁ y₂ hy₁ hy₂
    rw [InternalHom.isAmalgamation_iff _ _ hx] at hy₁ hy₂
    apply NatTrans.ext
    ext ⟨Y : Over X⟩
    apply (hG Y.hom).hom_ext
    rintro ⟨Z : Over Y.left, hZ⟩
    dsimp
    let φ : Over.mk (Z.hom ≫ Y.hom) ⟶ Y := Over.homMk Z.hom
    refine' (y₁.naturality φ.op).symm.trans (Eq.trans _ (y₂.naturality φ.op))
    rw [(hy₁ _ _ hZ), ← ((hy₂ _ _ hZ))]

lemma internalHom_isSheaf (hG : IsSheaf J G) :
    IsSheaf J (internalHom F G) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro X S hS
  exact internalHom_isSheafFor F G S
    (fun _ _ => ((isSheaf_iff_isLimit J G).1 hG _ (J.pullback_stable _ hS)).some)

end Presheaf

end CategoryTheory
