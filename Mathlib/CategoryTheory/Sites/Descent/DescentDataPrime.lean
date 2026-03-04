/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.ChosenPullback

/-!
# Descent data when we have pullbacks

In this file, given a pseudofunctor `F` from `LocallyDiscrete Cᵒᵖ` to `Cat`,
a family of maps `f i : X i ⟶ S` in the category `C`, chosen pullbacks `sq`
and threefold wide pullbacks `sq₃` for these morphisms, we define a
category `F.DescentData' sq sq₃` of objects over the `X i`
equipped with a descent data relative to the morphisms `f i : X i ⟶ S`, where
the data and compatibilities are expressed using the chosen pullbacks.

## TODO
* show that this category is equivalent to `F.DescentData f`.

-/

@[expose] public section

universe t v' v u' u

namespace CategoryTheory

open Opposite Limits

namespace Pseudofunctor

open LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
  {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
  (sq : ∀ i j, ChosenPullback (f i) (f j))
  (sq₃ : ∀ (i₁ i₂ i₃ : ι), ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃))

namespace DescentData'

variable {F sq}

section

variable {obj obj' : ∀ (i : ι), F.obj (.mk (op (X i)))}
  (hom : ∀ (i j : ι), (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ⟶
    (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj' j))

/-- Variant of `Pseudofunctor.LocallyDiscreteOpToCat.pullHom` when we have
chosen pullbacks. -/
noncomputable def pullHom' ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q := by cat_disch) (hf₂ : f₂ ≫ f i₂ = q := by cat_disch) :
    (F.map f₁.op.toLoc).toFunctor.obj (obj i₁) ⟶ (F.map f₂.op.toLoc).toFunctor.obj (obj' i₂) :=
  pullHom (hom i₁ i₂) ((sq i₁ i₂).isPullback.lift f₁ f₂ (by cat_disch)) f₁ f₂

@[reassoc]
lemma pullHom'_eq_pullHom ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (p : Y ⟶ (sq i₁ i₂).pullback)
    (hf₁ : f₁ ≫ f i₁ = q := by cat_disch) (hf₂ : f₂ ≫ f i₂ = q := by cat_disch)
    (hp₁ : p ≫ (sq i₁ i₂).p₁ = f₁ := by cat_disch)
    (hp₂ : p ≫ (sq i₁ i₂).p₂ = f₂ := by cat_disch) :
  pullHom' hom q f₁ f₂ hf₁ hf₂ =
    pullHom (hom i₁ i₂) p f₁ f₂ := by
  obtain rfl : p = (sq i₁ i₂).isPullback.lift f₁ f₂ (by rw [hf₁, hf₂]) := by
    apply (sq i₁ i₂).isPullback.hom_ext <;> cat_disch
  rfl

@[reassoc]
lemma pullHom'₁₂_eq_pullHom_of_chosenPullback₃ (i₁ i₂ i₃ : ι) :
    pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ =
      pullHom (hom i₁ i₂) (sq₃ i₁ i₂ i₃).p₁₂ _ _ :=
  pullHom'_eq_pullHom _ _ _ ..

@[reassoc]
lemma pullHom'₁₃_eq_pullHom_of_chosenPullback₃ (i₁ i₂ i₃ : ι) :
    pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃ =
      pullHom (hom i₁ i₃) (sq₃ i₁ i₂ i₃).p₁₃ _ _ :=
  pullHom'_eq_pullHom _ _ _ ..

@[reassoc]
lemma pullHom'₂₃_eq_pullHom_of_chosenPullback₃ (i₁ i₂ i₃ : ι) :
    pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ =
      pullHom (hom i₂ i₃) (sq₃ i₁ i₂ i₃).p₂₃ _ _ :=
  pullHom'_eq_pullHom _ _ _ ..

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma pullHom_pullHom' ⦃Y Y' : C⦄ (g : Y' ⟶ Y) (q : Y ⟶ S) (q' : Y' ⟶ S)
    ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (gf₁ : Y' ⟶ X i₁) (gf₂ : Y' ⟶ X i₂)
    (hq : g ≫ q = q' := by cat_disch)
    (hf₁ : f₁ ≫ f i₁ = q := by cat_disch) (hf₂ : f₂ ≫ f i₂ = q := by cat_disch)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    pullHom (pullHom' hom q f₁ f₂ hf₁ hf₂) g gf₁ gf₂ =
      pullHom' hom q' gf₁ gf₂ := by
  let p := (sq i₁ i₂).isPullback.lift f₁ f₂ (by cat_disch)
  rw [pullHom'_eq_pullHom _ _ _ _ p, pullHom'_eq_pullHom _ _ _ _ (g ≫ p)]
  dsimp [pullHom]
  simp only [Functor.map_comp, Category.assoc]
  rw [F.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_app_assoc
    _ _ _ _ _ _ (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, IsPullback.lift_fst])
    rfl (by cat_disch),
    F.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app _ _ _ _ _ _
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, IsPullback.lift_snd]) rfl (by cat_disch)]
  simp

end

section

variable {obj : ∀ (i : ι), F.obj (.mk (op (X i)))}
  (hom : ∀ (i j : ι), (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ⟶
    (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j))

@[simp]
lemma pullHom'_p₁_p₂ (i₁ i₂ : ι) :
    pullHom' hom (sq i₁ i₂).p (sq i₁ i₂).p₁ (sq i₁ i₂).p₂ (by simp) (by simp) = hom i₁ i₂ := by
  simp [pullHom'_eq_pullHom hom (sq i₁ i₂).p (sq i₁ i₂).p₁ (sq i₁ i₂).p₂ (𝟙 _)]

set_option backward.isDefEq.respectTransparency false in
lemma pullHom'_self' (hom_self : ∀ i, pullHom' hom (f i) (𝟙 (X i)) (𝟙 (X i)) = 𝟙 _)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i : ι⦄ (g : Y ⟶ X i) (hg : g ≫ f i = q := by cat_disch) :
    pullHom' hom q g g hg hg = 𝟙 _ := by
  simp [← pullHom_pullHom' hom g (f i) q (𝟙 (X i)) (𝟙 (X i)) g g hg, hom_self, pullHom]

set_option backward.isDefEq.respectTransparency false in
variable {sq₃} in
@[reassoc]
lemma comp_pullHom'' (hom_comp : ∀ (i₁ i₂ i₃ : ι),
    pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ ≫
    pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ =
    pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ i₃ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (f₃ : Y ⟶ X i₃) (hf₁ : f₁ ≫ f i₁ = q)
    (hf₂ : f₂ ≫ f i₂ = q) (hf₃ : f₃ ≫ f i₃ = q) :
    pullHom' hom q f₁ f₂ ≫ pullHom' hom q f₂ f₃ = pullHom' hom q f₁ f₃ := by
  obtain ⟨φ, _, _, _⟩ := (sq₃ i₁ i₂ i₃).exists_lift f₁ f₂ f₃ q hf₁ hf₂ hf₃
  rw [← pullHom_pullHom'_assoc hom φ (sq₃ i₁ i₂ i₃).p _ (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ _ _,
    ← pullHom_pullHom' hom φ (sq₃ i₁ i₂ i₃).p _ (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ _ _,
    ← pullHom_pullHom' hom φ (sq₃ i₁ i₂ i₃).p _ (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃ _ _]
  dsimp [pullHom]
  simp [← Functor.map_comp_assoc, hom_comp]

end

end DescentData'

open DescentData' in
/-- Given a pseudofunctor `F` from `LocallyDiscrete Cᵒᵖ` to `Cat`, a family of
morphisms `f i : X i ⟶ S`, chosen pullbacks `sq i j` of `f i` and `f j` for all `i` and `j`,
and chosen threefold wide pullbacks `sq₃`, this structure contains a description
of objects over the `X i` equipped with a descent data relative to the morphisms `f i`,
where the (iso)morphisms are compatibilities are considered over the chosen pullbacks. -/
structure DescentData' where
  /-- The objects over `X i` for all `i` -/
  obj (i : ι) : F.obj (.mk (op (X i)))
  /-- The compatibility morphisms after pulling back to the chosen pullbacks. It follows
  from the conditions `pullHom'_hom_self` and `pullHom'_hom_comp` that these morphisms
  are isomorphisms. -/
  hom : ∀ (i j : ι), (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ⟶
    (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j)
  pullHom'_hom_self : ∀ i, pullHom' hom (f i) (𝟙 (X i)) (𝟙 (X i)) = 𝟙 _
  pullHom'_hom_comp (i₁ i₂ i₃ : ι) :
    pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ ≫
    pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ =
    pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃

namespace DescentData'

attribute [reassoc] pullHom'_hom_comp

variable {F sq sq₃}

@[simp]
lemma pullHom'_self (D : F.DescentData' sq sq₃)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i : ι⦄ (g : Y ⟶ X i) (hg : g ≫ f i = q := by cat_disch) :
    pullHom' D.hom q g g hg hg = 𝟙 _ :=
  pullHom'_self' _ D.pullHom'_hom_self _ _

@[reassoc (attr := simp)]
lemma comp_pullHom' (D : F.DescentData' sq sq₃)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ i₃ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (f₃ : Y ⟶ X i₃) (hf₁ : f₁ ≫ f i₁ = q := by cat_disch)
    (hf₂ : f₂ ≫ f i₂ = q := by cat_disch) (hf₃ : f₃ ≫ f i₃ = q := by cat_disch) :
    pullHom' D.hom q f₁ f₂ hf₁ hf₂ ≫ pullHom' D.hom q f₂ f₃ hf₂ hf₃ =
      pullHom' D.hom q f₁ f₃ hf₁ hf₃ :=
  comp_pullHom'' _ D.pullHom'_hom_comp _ _ _ _ hf₁ hf₂ hf₃

instance (D : F.DescentData' sq sq₃)
    {Y : C} (q : Y ⟶ S) (i₁ i₂ : ι) (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q)
    (hf₂ : f₂ ≫ f i₂ = q) :
    IsIso (pullHom' D.hom q f₁ f₂ hf₁ hf₂) :=
  ⟨pullHom' D.hom q f₂ f₁ hf₂ hf₁, by simp, by simp⟩

lemma pullHom'_eq_hom (D : F.DescentData' sq sq₃) (i₁ i₂ : ι) :
    pullHom' D.hom _ _ _ (by simp) = D.hom i₁ i₂ := by
  simp

instance (D : F.DescentData' sq sq₃) (i₁ i₂ : ι) :
    IsIso (D.hom i₁ i₂) := by
  simpa using inferInstanceAs% (IsIso (pullHom' D.hom (sq i₁ i₂).p (sq i₁ i₂).p₁ (sq i₁ i₂).p₂))

/-- The type of morphisms in the category `F.DescentData' sq sq₃`. -/
@[ext]
structure Hom (D₁ D₂ : F.DescentData' sq sq₃) where
  /-- The morphisms between the `obj` fields of descent data. -/
  hom (i : ι) : D₁.obj i ⟶ D₂.obj i
  comm (i₁ i₂ : ι) :
    (F.map (sq i₁ i₂).p₁.op.toLoc).toFunctor.map (hom i₁) ≫ D₂.hom i₁ i₂ =
    D₁.hom i₁ i₂ ≫ (F.map (sq i₁ i₂).p₂.op.toLoc).toFunctor.map (hom i₂) := by cat_disch

attribute [reassoc (attr := simp)] Hom.comm

instance : Quiver (F.DescentData' sq sq₃) where
  Hom := Hom

@[simps id_hom comp_hom]
instance : Category (F.DescentData' sq sq₃) where
  id _ := { hom _ := 𝟙 _ }
  comp f g := { hom i := f.hom i ≫ g.hom i }

attribute [reassoc] comp_hom

@[ext]
lemma hom_ext {D₁ D₂ : F.DescentData' sq sq₃} {f g : D₁ ⟶ D₂}
    (h : ∀ i, f.hom i = g.hom i) : f = g :=
  Hom.ext (funext h)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma comm {D₁ D₂ : F.DescentData' sq sq₃} (φ : D₁ ⟶ D₂)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q := by cat_disch) (hf₂ : f₂ ≫ f i₂ = q := by cat_disch) :
    (F.map f₁.op.toLoc).toFunctor.map (φ.hom i₁) ≫ pullHom' D₂.hom q f₁ f₂ hf₁ hf₂ =
      pullHom' D₁.hom q f₁ f₂ hf₁ hf₂ ≫ (F.map f₂.op.toLoc).toFunctor.map (φ.hom i₂) := by
  obtain ⟨p, _, _⟩ := (sq i₁ i₂).isPullback.exists_lift f₁ f₂ (by cat_disch)
  rw [← pullHom_pullHom' D₂.hom p (sq i₁ i₂).p q (sq i₁ i₂).p₁ (sq i₁ i₂).p₂ f₁ f₂,
    ← pullHom_pullHom' D₁.hom p (sq i₁ i₂).p q (sq i₁ i₂).p₁ (sq i₁ i₂).p₂ f₁ f₂,
    pullHom'_p₁_p₂, pullHom'_p₁_p₂]
  dsimp only [pullHom]
  rw [NatTrans.naturality_assoc]
  dsimp
  rw [← Functor.map_comp_assoc, φ.comm, Functor.map_comp_assoc, mapComp'_inv_naturality]
  simp only [Category.assoc]

/-- Constructor for isomorphisms in the category `F.DescentData' sq sq₃`. -/
@[simps]
def isoMk {D₁ D₂ : F.DescentData' sq sq₃} (e : ∀ (i : ι), D₁.obj i ≅ D₂.obj i)
    (comm : ∀ (i₁ i₂ : ι), (F.map (sq i₁ i₂).p₁.op.toLoc).toFunctor.map (e i₁).hom ≫ D₂.hom i₁ i₂ =
      D₁.hom i₁ i₂ ≫ (F.map (sq i₁ i₂).p₂.op.toLoc).toFunctor.map (e i₂).hom := by cat_disch) :
    D₁ ≅ D₂ where
  hom.hom i := (e i).hom
  hom.comm := comm
  inv.hom i := (e i).inv
  inv.comm i₁ i₂ := by
    rw [← cancel_mono ((F.map _).toFunctor.map (e i₂).hom), Category.assoc,
      Category.assoc, Iso.map_inv_hom_id, Category.comp_id,
      ← cancel_epi ((F.map _).toFunctor.map (e i₁).hom),
      Iso.map_hom_inv_id_assoc, comm i₁ i₂]

end DescentData'

end Pseudofunctor

end CategoryTheory
