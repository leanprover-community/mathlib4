/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.Over

/-! Internal hom of sheaves

In this file, given two sheaves `F` and `G` on a site `(C, J)` with values
in a category `A`, we define a sheaf of types
`sheafHom F G` which sends `X : C` to the type of morphisms
between the restrictions of `F` and `G` to the categories `Over X`.

We first define `presheafHom F G` when `F` and `G` are
presheaves `Cᵒᵖ ⥤ A` and show that it is a sheaf when `G` is a sheaf.

TODO:
- turn both `presheafHom` and `sheafHom` into bifunctors
- for a sheaf of types `F`, the `sheafHom` functor from `F` is right-adjoint to
  the product functor with `F`, i.e. for all `X` and `Y`, there is a
  natural bijection `(X ⨯ F ⟶ Y) ≃ (X ⟶ sheafHom F Y)`.
- use these results in order to show that the category of sheaves of types is Cartesian closed

-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory

open Category Opposite Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Type u'} [Category.{v'} A]

variable (F G : Cᵒᵖ ⥤ A)

/-- Given two presheaves `F` and `G` on a category `C` with values in a category `A`,
this `presheafHom F G` is the presheaf of types which sends an object `X : C`
to the type of morphisms between the "restrictions" of `F` and `G` to the category `Over X`. -/
@[simps! obj]
def presheafHom : Cᵒᵖ ⥤ Type _ where
  obj X := (Over.forget X.unop).op ⋙ F ⟶ (Over.forget X.unop).op ⋙ G
  map f := TypeCat.ofHom (Functor.whiskerLeft (Over.map f.unop).op)
  map_id := by
    rintro ⟨X⟩
    ext φ ⟨Y⟩
    simpa [Over.mapId] using φ.naturality ((Over.mapId X).hom.app Y).op
  map_comp := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ ⟨f : Y ⟶ X⟩ ⟨g : Z ⟶ Y⟩
    ext φ ⟨W⟩
    simpa [Over.mapComp] using φ.naturality ((Over.mapComp g f).hom.app W).op

variable {F G}

/-- Equational lemma for the presheaf structure on `presheafHom`.
It is advisable to use this lemma rather than `dsimp [presheafHom]` which may result
in the need to prove equalities of objects in an `Over` category. -/
lemma presheafHom_map_app {X Y Z : C} (f : Z ⟶ Y) (g : Y ⟶ X) (h : Z ⟶ X) (w : f ≫ g = h)
    (α : (presheafHom F G).obj (op X)) :
    ((presheafHom F G).map g.op α).app (op (Over.mk f)) =
      α.app (op (Over.mk h)) := by
  subst w
  rfl

@[simp]
lemma presheafHom_map_app_op_mk_id {X Y : C} (g : Y ⟶ X)
    (α : (presheafHom F G).obj (op X)) :
    dsimp% ((presheafHom F G).map g.op α).app (op (Over.mk (𝟙 Y))) =
      α.app (op (Over.mk g)) :=
  presheafHom_map_app (𝟙 Y) g g (by simp) α

variable (F G)

/-- The sections of the presheaf `presheafHom F G` identify to morphisms `F ⟶ G`. -/
def presheafHomSectionsEquiv : (presheafHom F G).sections ≃ (F ⟶ G) where
  toFun s :=
    { app := fun X => (s.1 X).app ⟨Over.mk (𝟙 _)⟩
      naturality := by
        rintro ⟨X₁⟩ ⟨X₂⟩ ⟨f : X₂ ⟶ X₁⟩
        dsimp
        refine Eq.trans ?_ ((s.1 ⟨X₁⟩).naturality
          (Over.homMk f : Over.mk f ⟶ Over.mk (𝟙 X₁)).op)
        rw [← s.2 f.op]
        dsimp
        rw [presheafHom_map_app_op_mk_id]
        rfl }
  invFun f := ⟨fun _ => Functor.whiskerLeft _ f, fun _ => rfl⟩
  left_inv s := by
    dsimp
    ext ⟨X⟩ ⟨Y : Over X⟩
    have H := s.2 Y.hom.op
    dsimp at H ⊢
    rw [← H]
    apply presheafHom_map_app_op_mk_id

variable {F G}

lemma PresheafHom.isAmalgamation_iff {X : C} (S : Sieve X)
    (x : Presieve.FamilyOfElements (presheafHom F G) S.arrows)
    (hx : x.Compatible) (y : (presheafHom F G).obj (op X)) :
    x.IsAmalgamation y ↔ ∀ (Y : C) (g : Y ⟶ X) (hg : S g),
      y.app (op (Over.mk g)) = (x g hg).app (op (Over.mk (𝟙 Y))) := by
  constructor
  · intro h Y g hg
    rw [← h g hg]
    dsimp
    rw [presheafHom_map_app_op_mk_id]
  · intro h Y g hg
    dsimp
    ext ⟨W : Over Y⟩
    refine (h W.left (W.hom ≫ g) (S.downward_closed hg _)).trans ?_
    have H := hx (𝟙 _) W.hom (S.downward_closed hg W.hom) hg (by simp)
    simp only [op_id, Functor.map_id, id_apply] at H
    rw [H, presheafHom_map_app _ _ W.hom (by simp)]
    rfl

section

variable {X : C} {S : Sieve X}
    (hG : ∀ ⦃Y : C⦄ (f : Y ⟶ X), IsLimit (G.mapCone (S.pullback f).arrows.cocone.op))

namespace PresheafHom.IsSheafFor

variable (x : Presieve.FamilyOfElements (presheafHom F G) S.arrows) {Y : C}

include hG in
lemma exists_app (hx : x.Compatible) (g : Y ⟶ X) :
    ∃ (φ : F.obj (op Y) ⟶ G.obj (op Y)),
      ∀ {Z : C} (p : Z ⟶ Y) (hp : S (p ≫ g)), φ ≫ G.map p.op =
        F.map p.op ≫ (x (p ≫ g) hp).app ⟨Over.mk (𝟙 Z)⟩ := by
  let c : Cone ((Presieve.diagram (Sieve.pullback g S).arrows).op ⋙ G) :=
    { pt := F.obj (op Y)
      π :=
        { app := fun ⟨Z, hZ⟩ => F.map Z.hom.op ≫ (x _ hZ).app (op (Over.mk (𝟙 _)))
          naturality := by
            rintro ⟨Z₁, hZ₁⟩ ⟨Z₂, hZ₂⟩ ⟨⟨f : Z₂ ⟶ Z₁⟩⟩
            dsimp
            rw [id_comp, assoc]
            have H := hx f.left (𝟙 _) hZ₁ hZ₂ (by simp)
            simp only [op_id, Functor.map_id, id_apply] at H
            let φ : Over.mk f.left ⟶ Over.mk (𝟙 Z₁.left) := Over.homMk f.left
            have H' := (x (Z₁.hom ≫ g) hZ₁).naturality φ.op
            dsimp at H H' ⊢
            erw [← H, ← H', presheafHom_map_app_op_mk_id, ← F.map_comp_assoc,
              ← op_comp, Over.w f] } }
  use (hG g).lift c
  intro Z p hp
  exact ((hG g).fac c ⟨Over.mk p, hp⟩)

/-- Auxiliary definition for `presheafHom_isSheafFor`. -/
noncomputable def app (hx : x.Compatible) (g : Y ⟶ X) : F.obj (op Y) ⟶ G.obj (op Y) :=
  (exists_app hG x hx g).choose

lemma app_cond (hx : x.Compatible) (g : Y ⟶ X) {Z : C} (p : Z ⟶ Y) (hp : S (p ≫ g)) :
    app hG x hx g ≫ G.map p.op = F.map p.op ≫ (x (p ≫ g) hp).app ⟨Over.mk (𝟙 Z)⟩ :=
  (exists_app hG x hx g).choose_spec p hp

end PresheafHom.IsSheafFor

variable (F G S)

set_option backward.isDefEq.respectTransparency false in
include hG in
open PresheafHom.IsSheafFor in
lemma presheafHom_isSheafFor :
    Presieve.IsSheafFor (presheafHom F G) S.arrows := by
  intro x hx
  apply existsUnique_of_exists_of_unique
  · refine ⟨
      { app := fun Y => app hG x hx Y.unop.hom
        naturality := by
          rintro ⟨Y₁ : Over X⟩ ⟨Y₂ : Over X⟩ ⟨φ : Y₂ ⟶ Y₁⟩
          apply (hG Y₂.hom).hom_ext
          rintro ⟨Z : Over Y₂.left, hZ⟩
          dsimp
          rw [assoc, assoc, app_cond hG x hx Y₂.hom Z.hom hZ, ← G.map_comp, ← op_comp]
          rw [app_cond hG x hx Y₁.hom (Z.hom ≫ φ.left) (by simpa using hZ),
            ← F.map_comp_assoc, op_comp]
          congr 3
          simp }, ?_⟩
    rw [PresheafHom.isAmalgamation_iff _ _ hx]
    intro Y g hg
    dsimp
    have H := app_cond hG x hx g (𝟙 _) (by simpa using hg)
    rw [op_id, G.map_id, comp_id, F.map_id, id_comp] at H
    exact H.trans (by congr; simp)
  · intro y₁ y₂ hy₁ hy₂
    rw [PresheafHom.isAmalgamation_iff _ _ hx] at hy₁ hy₂
    apply NatTrans.ext
    ext ⟨Y : Over X⟩
    apply (hG Y.hom).hom_ext
    rintro ⟨Z : Over Y.left, hZ⟩
    dsimp
    let φ : Over.mk (Z.hom ≫ Y.hom) ⟶ Y := Over.homMk Z.hom
    refine (y₁.naturality φ.op).symm.trans (Eq.trans ?_ (y₂.naturality φ.op))
    rw [(hy₁ _ _ hZ), ← ((hy₂ _ _ hZ))]

end

variable (F G)

lemma Presheaf.IsSheaf.hom (hG : Presheaf.IsSheaf J G) :
    Presheaf.IsSheaf J (presheafHom F G) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro X S hS
  exact presheafHom_isSheafFor F G S
    (fun _ _ => ((Presheaf.isSheaf_iff_isLimit J G).1 hG _ (J.pullback_stable _ hS)).some)


/-- The underlying presheaf of `sheafHom F G`. It is isomorphic to `presheafHom F.1 G.1`
(see `sheafHom'Iso`), but has better definitional properties. -/
def sheafHom' (F G : Sheaf J A) : Cᵒᵖ ⥤ Type _ where
  obj X := ((J.overPullback A X.unop).obj F ⟶ (J.overPullback A X.unop).obj G)
  map f := TypeCat.ofHom ((J.overMapPullback A f.unop).map)
  map_id X := by
    ext φ : 4
    exact ConcreteCategory.congr_hom ((presheafHom F.1 G.1).map_id X) φ.1
  map_comp f g := by
    ext φ : 4
    exact ConcreteCategory.congr_hom ((presheafHom F.1 G.1).map_comp f g) φ.1

/-- The canonical isomorphism `sheafHom' F G ≅ presheafHom F.1 G.1`. -/
def sheafHom'Iso (F G : Sheaf J A) :
    sheafHom' F G ≅ presheafHom F.1 G.1 :=
  NatIso.ofComponents
    (fun _ => Sheaf.homEquiv.toIso) (fun _ => rfl)

/-- Given two sheaves `F` and `G` on a site `(C, J)` with values in a category `A`,
this `sheafHom F G` is the sheaf of types which sends an object `X : C`
to the type of morphisms between the "restrictions" of `F` and `G` to the category `Over X`. -/
def sheafHom (F G : Sheaf J A) : Sheaf J (Type _) where
  obj := sheafHom' F G
  property := (Presheaf.isSheaf_of_iso_iff (sheafHom'Iso F G)).2 (G.2.hom F.1)

/-- The sections of the sheaf `sheafHom F G` identify to morphisms `F ⟶ G`. -/
def sheafHomSectionsEquiv (F G : Sheaf J A) :
    (sheafHom F G).1.sections ≃ (F ⟶ G) :=
  ((Functor.sectionsFunctor Cᵒᵖ).mapIso (sheafHom'Iso F G)).toEquiv.trans
    ((presheafHomSectionsEquiv F.1 G.1).trans Sheaf.homEquiv.symm)

@[simp]
lemma sheafHomSectionsEquiv_symm_apply_coe_apply {F G : Sheaf J A} (φ : F ⟶ G) (X : Cᵒᵖ) :
    ((sheafHomSectionsEquiv F G).symm φ).1 X = (J.overPullback A X.unop).map φ := rfl

end CategoryTheory
