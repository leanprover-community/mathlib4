/-
Copyright (c) 2025 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
import Mathlib.CategoryTheory.Sites.Sieves

/-!
# Descent data

Let `C` be a category. Given a pseudofunctor `S` from  `C` into the 2-category `Cat` and a
presieve `P` on an object `a : C`, a descent datum on `P` consists of
* an object `X f` of `S b` for each morphism `f : b ⟶ a` in `P`, and
* an isomorphism `φ g : S g (X f) ≅ X (g ≫ f)` for each `f : b ⟶ a` and `g : c ⟶ b`,
satisfying compatibility conditions for the identities and compositions.

The set of descent data on `P` forms a category `DescentData S P`.

-/

universe v u v₁ u₁

open CategoryTheory Opposite Bicategory Limits LocallyDiscrete

variable {C : Type u} [Category.{v} C]

namespace CategoryTheory

namespace Pseudofunctor

/-- The category `S X` associated with an object `X : C` by the pseudofunctor `S`. -/
abbrev mkCat (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}) (X : C) : Cat :=
  S.obj (.mk (.op X))

/-- The functor `S X ⟶ S Y` associated with a morphism `f : Y ⟶ X` in `C` by
the pseudofunctor `S`. -/
abbrev mkFunctor (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}) {X Y : C} (f : Y ⟶ X) :
    S.mkCat X ⟶ S.mkCat Y :=
  S.map (mkHom f.op)

/-- The natural isomorphism `S (𝟙 X) ≅ 𝟙 (S X)`. -/
abbrev mapIdCat (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}) (X : C) :
    S.mkFunctor (𝟙 X) ≅ 𝟙 (S.mkCat X) :=
  S.mapId ⟨op X⟩

/-- The natural isomorphism `S (g ≫ f) ≅ S f ≫ S g`. -/
abbrev mapCompCat (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}) {X Y Z : C}
    (f : Y ⟶ X) (g : Z ⟶ Y) :
    (S.mkFunctor (g ≫ f)) ≅ S.mkFunctor f ≫ S.mkFunctor g :=
  S.mapComp (mkHom f.op) (mkHom g.op)

/-- An auxiliary structure for descent data: it contains only data, with no conditions. -/
structure PreDescentData (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁})
    {a : C} (P : Presieve a) where
  /-- A family of objects in the category `S b` for each morphism `f : b ⟶ a` in
  the presieve `P`. -/
  obj : ∀ {b : C} (f : b ⟶ a) (_ : P f := by cat_disch), S.mkCat b
  /-- A family of isomorphisms `S g (obj f) ≅ obj (g ≫ f)` in `S c` for each composable pair
  `c -g→ b -f→ a` with `P f` and `P (g ≫ f)`. -/
  iso : ∀ {b c : C} {f : b ⟶ a} (g : c ⟶ b)
    (hf : P f := by cat_disch) (hg : P (g ≫ f) := by cat_disch),
    (S.mkFunctor g).obj (obj f) ≅ obj (g ≫ f)

/--
Given a pseudofunctor `S` and a presieve `P` on an object `a` in the category `C`, the descent datum
for `S` consists of:
- `obj`: A family of objects in the category `S b` for each morphism `f : b ⟶ a` in
  the presieve `P`.
- `iso`: A family of isomorphisms `S g (obj f) ≅ obj (g ≫ f)` in `S c` for each composable pair
  `c -g→ b -f→ a` with `P f` and `P (g ≫ f)`.
- `iso_id`: The condition that the isomorphism associated with the identity morphism is compatible
  with the isomorphism `S (𝟙 b) ≅ 𝟙 (S b)`.
- `iso_comp`: The condition that the isomorphism associated with the composition `h ≫ g` is
  compatible with the isomorphism `S (h ≫ g) ≅ S h ≫ S g`.
-/
structure DescentData (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁})
    {a : C} (P : Presieve a) extends PreDescentData S P where
  iso_id {b} (f : b ⟶ a) (hf : P f := by cat_disch) :
    iso (𝟙 b) = (S.mapIdCat b).app (obj f) ≪≫ eqToIso (by simp)
  iso_comp {b c d} (f : b ⟶ a) (g : c ⟶ b) (h : d ⟶ c)
      (hf : P f := by cat_disch) (hg : P (g ≫ f) := by cat_disch)
      (hh : P (h ≫ g ≫ f) := by cat_disch) :
    iso (h ≫ g) =
      (S.mapCompCat g h).app (obj f) ≪≫
        (S.map (mkHom h.op)).mapIso (iso g) ≪≫ iso h ≪≫ eqToIso (by simp)

namespace DescentData

variable {S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}} {a : C} {P : Presieve a}

/-- The homomorphism between two descent data. -/
@[ext]
structure Hom (𝒟₁ 𝒟₂ : DescentData S P) where
  /-- For each morphism `f : b ⟶ a` in `P`, a morphism `𝒟₁.obj f ⟶ 𝒟₂.obj f`. -/
  hom {b : C} (f : b ⟶ a) (_ : P f := by cat_disch) : 𝒟₁.obj f ⟶ 𝒟₂.obj f
  comm {b c : C} (f : b ⟶ a) (g : c ⟶ b)
    (hf : P f := by cat_disch) (hg : P (g ≫ f) := by cat_disch) :
    (S.mkFunctor g).map (hom f) ≫ (𝒟₂.iso g).hom = (𝒟₁.iso g).hom ≫ hom (g ≫ f) := by cat_disch

attribute [reassoc] Hom.comm

/-- The identity morphisms on a descent datum. -/
@[simps]
def Hom.id (𝒟 : DescentData S P) : Hom 𝒟 𝒟 where
  hom f _ := 𝟙 (𝒟.obj f)

/-- The composition of morphisms between descent data. -/
@[simps]
def Hom.comp {𝒟₁ 𝒟₂ 𝒟₃ : DescentData S P} (η₁ : Hom 𝒟₁ 𝒟₂) (η₂ : Hom 𝒟₂ 𝒟₃) : Hom 𝒟₁ 𝒟₃ where
  hom f _ := η₁.hom f ≫ η₂.hom f
  comm f g hf hg := by
    simp only [Functor.map_comp, Category.assoc]
    rw [η₂.comm f g, η₁.comm_assoc f g]

instance : Category (DescentData S P) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

/-- Given a presieve on `a : C`, we have a descent datum for each object `x : S a`,
called the canonical descent datum. The object for `f : b ⟶ a` is given by `(S f) x`,
and the isomorphism for `c -g⟶ b -f⟶ a` is given by `S g ((S f) x) ≅ (S (g ≫ f)) x`
which is the `mapComp` isomorphism of the pseudofunctor `S`. -/
@[simps]
def canonical (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}) (x : S.mkCat a) :
    DescentData S P where
  obj f _ := (S.mkFunctor f).obj x
  iso g _ _ := (S.mapCompCat _ g).symm.app x
  iso_id f _ := by
    ext
    dsimp only [Cat.comp_obj, Iso.app_hom, Iso.symm_hom, Cat.id_obj, Iso.trans_hom, eqToIso.hom]
    rw [← eqToHom_app (by simp), ← Cat.whiskerLeft_app, ← NatTrans.comp_app]
    congr 1
    dsimp only [mapCompCat, mkFunctor]
    rw [S.mapComp_eq_right _ (show mkHom (𝟙 _).op = 𝟙 _ from rfl)]
    dsimp only [op_id, op_comp, eqToIso_refl, Iso.trans_inv, Iso.refl_inv]
    rw [S.mapComp_id_right_inv]
    simp only [Category.assoc]
    rw [Cat.rightUnitor_eqToIso, LocallyDiscrete.rightUnitor_inv, S.map₂_eqToHom]
    simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id, eqToHom_naturality_assoc,
      Category.id_comp]
    /- We need to give an argument. `rw [Category.id_comp]` alone does not work. -/
    rw [Category.id_comp (X := S.map (mkHom f.op) ≫ S.map (𝟙 _))]
    rw [Category.comp_id (Y := S.map (mkHom f.op ≫ mkHom (𝟙 _)))]
  iso_comp f g h _ _ _ := by
    ext
    dsimp only [Iso.app_hom, Iso.symm_hom, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom]
    /- We manually write this to avoid a defeq abuse about the associator. Actually, I want to get
    the RHS by `rw` or `simp`. Related discussion:
    https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Functor.20identity.20.60.F0.9D.9F.AD.20_.20.E2.8B.99.20F.20.3D.20F.60.20is.20definitional.20equality/with/527059148 -/
    have : (S.mapCompCat g h).hom.app ((S.mkFunctor f).obj x) ≫
          (S.map (mkHom h.op)).map ((S.mapCompCat f g).inv.app x) =
          (S.mkFunctor f ◁ (S.mapCompCat g h).hom ≫ (α_ _ _ _).inv ≫
          (S.mapCompCat f g).inv ▷ S.map (mkHom h.op)).app x := by
      dsimp only [Cat.comp_obj, Cat.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app]
      rw [Cat.associator_eqToIso]
      simp only [eqToIso_refl, Iso.refl_inv, Cat.id_app, Cat.comp_obj, Category.id_comp]
    rw [reassoc_of% this, ← eqToHom_app (by simp)]
    simp only [← NatTrans.comp_app]
    congr 1
    dsimp only [mapCompCat, mkFunctor]
    rw [S.mapComp_eq_right _ (show (mkHom (h ≫ g).op) = mkHom g.op ≫ mkHom h.op from rfl)]
    rw [S.mapComp_eq_left (show (mkHom (g ≫ f).op) = mkHom f.op ≫ mkHom g.op from rfl)]
    dsimp only [op_comp, eqToIso_refl, Iso.trans_inv, Iso.refl_inv]
    simp only [Category.assoc]
    rw [Category.id_comp (X := S.map (mkHom f.op) ≫ S.map (mkHom g.op ≫ mkHom h.op))]
    rw [Category.id_comp (X := S.map (mkHom f.op ≫ mkHom g.op) ≫ S.map (mkHom h.op))]
    rw [Category.id_comp (X := S.map (mkHom (f.op ≫ g.op) ≫ mkHom h.op))]
    rw [Category.comp_id (Y := S.map (mkHom f.op ≫ mkHom (g.op ≫ h.op)))]
    rw [S.mapComp_comp_right_inv]
    rw [LocallyDiscrete.associator_hom]
    rw [S.map₂_eqToHom]

end DescentData

end Pseudofunctor

end CategoryTheory
