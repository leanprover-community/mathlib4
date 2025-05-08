/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Sites.Descent.DescentData

/-!
# Descent data ...

-/

namespace CategoryTheory

open Opposite Limits

namespace Pseudofunctor

variable {C : Type*} [Category C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat)
  {ι : Type*} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
  (sq : ∀ i j, ChosenPullback (f i) (f j))
  (sq₃ : ∀ (i₁ i₂ i₃ : ι), ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃))

namespace DescentData'

variable {F sq}

section

variable {obj obj' : ∀ (i : ι), F.obj (.mk (op (X i)))}
  (hom : ∀ (i j : ι), (F.map (sq i j).p₁.op.toLoc).obj (obj i) ⟶
    (F.map (sq i j).p₂.op.toLoc).obj (obj' j))

noncomputable def pullHom ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q := by aesop_cat) (hf₂ : f₂ ≫ f i₂ = q := by aesop_cat) :
    (F.map f₁.op.toLoc).obj (obj i₁) ⟶ (F.map f₂.op.toLoc).obj (obj' i₂) :=
  DescentData.pull (hom i₁ i₂) ((sq i₁ i₂).isPullback.lift f₁ f₂ (by aesop)) f₁ f₂

@[reassoc]
lemma pullHom_eq_pull ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) (p : Y ⟶ (sq i₁ i₂).pullback)
    (hp₁ : p ≫ (sq i₁ i₂).p₁ = f₁) (hp₂ : p ≫ (sq i₁ i₂).p₂ = f₂) :
  pullHom hom q f₁ f₂ hf₁ hf₂ =
    DescentData.pull (hom i₁ i₂) p f₁ f₂ := by
  obtain rfl : p = (sq i₁ i₂).isPullback.lift f₁ f₂ (by rw [hf₁, hf₂]) := by
    apply (sq i₁ i₂).isPullback.hom_ext <;> aesop
  rfl

@[reassoc]
  lemma pull_pullHom ⦃Y Y' : C⦄ (g : Y' ⟶ Y) (q : Y ⟶ S) (q' : Y' ⟶ S) (hq : g ≫ q = q')
    ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q)
    (gf₁ : Y' ⟶ X i₁) (gf₂ : Y' ⟶ X i₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    DescentData.pull (pullHom hom q f₁ f₂ hf₁ hf₂) g gf₁ gf₂ =
      pullHom hom q' gf₁ gf₂ := by
  let p := (sq i₁ i₂).isPullback.lift f₁ f₂ (by aesop)
  dsimp
  rw [pullHom_eq_pull _ _ _ _ _ _ p (by aesop) (by aesop),
    pullHom_eq_pull _ _ _ _ _ _ (g ≫ p) (by aesop) (by aesop)]
  dsimp [DescentData.pull]
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.mapComp'_hom_app_comp_mapComp'_hom_app_map_obj_assoc
    _ _ _ _ _ _ (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, IsPullback.lift_fst]) rfl
    (by rw [← Quiver.Hom.comp_toLoc, ← Quiver.Hom.comp_toLoc, ← op_comp, ← op_comp,
        Category.assoc, IsPullback.lift_fst, hgf₁])]
  rw [F.map_map_mapComp'_inv_app_comp_mapComp'_inv_app
    _ _ _ _ _ _ (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, IsPullback.lift_snd]) rfl
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hgf₂]),
    mapComp'_inv_naturality_assoc, Iso.hom_inv_id_app_assoc]

end

section

variable {obj : ∀ (i : ι), F.obj (.mk (op (X i)))}
  (hom : ∀ (i j : ι), (F.map (sq i j).p₁.op.toLoc).obj (obj i) ⟶
    (F.map (sq i j).p₂.op.toLoc).obj (obj j))

@[simp]
lemma pullHom_p₁_p₂ (i : ι) :
    pullHom hom (sq i i).p (sq i i).p₁ (sq i i).p₂ (by simp) (by simp) = hom i i := by
  rw [pullHom_eq_pull hom (sq i i).p (sq i i).p₁ (sq i i).p₂ (by simp) (by simp)
    (𝟙 _) (by simp)  (by simp)]
  simp [DescentData.pull, mapComp'_comp_id_hom_app, mapComp'_comp_id_inv_app]

lemma pullHom_self' (hom_self : ∀ i, pullHom hom (f i) (𝟙 (X i)) (𝟙 (X i)) = 𝟙 _)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i : ι⦄ (g : Y ⟶ X i) (hg : g ≫ f i = q) :
    pullHom hom q g g hg hg = 𝟙 _ := by
  simp [← pull_pullHom hom g (f i) q hg (𝟙 (X i)) (𝟙 (X i)) (by simp) (by simp) g g
    (by simp) (by simp), hom_self, DescentData.pull]

variable {sq₃} in
@[reassoc]
lemma comp_pullHom' (hom_comp : ∀ (i₁ i₂ i₃ : ι),
    pullHom hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ ≫
    pullHom hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ =
    pullHom hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ i₃ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (f₃ : Y ⟶ X i₃) (hf₁ : f₁ ≫ f i₁ = q)
    (hf₂ : f₂ ≫ f i₂ = q) (hf₃ : f₃ ≫ f i₃ = q) :
    pullHom hom q f₁ f₂ ≫ pullHom hom q f₂ f₃ = pullHom hom q f₁ f₃ := by
  obtain ⟨φ, _, _, _⟩ := (sq₃ i₁ i₂ i₃).exists_lift f₁ f₂ f₃ q hf₁ hf₂ hf₃
  rw [← pull_pullHom_assoc hom φ (sq₃ i₁ i₂ i₃).p _ _ (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂,
    DescentData.pull, Category.assoc, Category.assoc,
    ← pull_pullHom hom φ (sq₃ i₁ i₂ i₃).p _ _ (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃,
    ← pull_pullHom hom φ (sq₃ i₁ i₂ i₃).p _ _ (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃,
    DescentData.pull, DescentData.pull,
    Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, hom_comp]
  all_goals aesop

end

end DescentData'

open DescentData' in

structure DescentData' where
  obj (i : ι) : F.obj (.mk (op (X i)))
  hom : ∀ (i j : ι), (F.map (sq i j).p₁.op.toLoc).obj (obj i) ⟶
    (F.map (sq i j).p₂.op.toLoc).obj (obj j)
  hom_self : ∀ i, pullHom hom (f i) (𝟙 (X i)) (𝟙 (X i)) = 𝟙 _
  hom_comp (i₁ i₂ i₃ : ι) :
    pullHom hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ ≫
    pullHom hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ =
    pullHom hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃

namespace DescentData'

variable {F sq sq₃}

@[simp]
lemma pullHom_self (D : F.DescentData' sq sq₃)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i : ι⦄ (g : Y ⟶ X i) (hg : g ≫ f i = q) :
    pullHom D.hom q g g hg hg = 𝟙 _ :=
  pullHom_self' _ D.hom_self _ _ _

@[reassoc (attr := simp)]
lemma comp_pullHom (D : F.DescentData' sq sq₃)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ i₃ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (f₃ : Y ⟶ X i₃) (hf₁ : f₁ ≫ f i₁ = q)
    (hf₂ : f₂ ≫ f i₂ = q) (hf₃ : f₃ ≫ f i₃ = q) :
    pullHom D.hom q f₁ f₂ hf₁ hf₂ ≫ pullHom D.hom q f₂ f₃ hf₂ hf₃ =
      pullHom D.hom q f₁ f₃ hf₁ hf₃ :=
  comp_pullHom' _ D.hom_comp _ _ _ _ hf₁ hf₂ hf₃

@[ext]
structure Hom (D₁ D₂ : F.DescentData' sq sq₃) where
  hom (i : ι) : D₁.obj i ⟶ D₂.obj i
  comm (i₁ i₂ : ι) :
    (F.map (sq i₁ i₂).p₁.op.toLoc).map (hom i₁) ≫
      pullHom D₂.hom (sq i₁ i₂).p (sq i₁ i₂).p₁ (sq i₁ i₂).p₂ =
    pullHom D₁.hom (sq i₁ i₂).p (sq i₁ i₂).p₁ (sq i₁ i₂).p₂ ≫
      (F.map (sq i₁ i₂).p₂.op.toLoc).map (hom i₂) := by aesop_cat

attribute [reassoc (attr := simp)] Hom.comm

@[simps]
def Hom.id (D : F.DescentData' sq sq₃) : Hom D D where
  hom _ := 𝟙 _

@[simps]
def Hom.comp {D₁ D₂ D₃ : F.DescentData' sq sq₃} (f : Hom D₁ D₂) (g : Hom D₂ D₃) : Hom D₁ D₃ where
  hom i := f.hom i ≫ g.hom i

instance : Category (F.DescentData' sq sq₃) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

@[ext]
lemma hom_ext {D₁ D₂ : F.DescentData' sq sq₃} {f g : D₁ ⟶ D₂}
    (h : ∀ i, f.hom i = g.hom i) : f = g :=
  Hom.ext (funext h)

@[reassoc, simp]
lemma comp_hom {D₁ D₂ D₃ : F.DescentData' sq sq₃} (f : D₁ ⟶ D₂) (g : D₂ ⟶ D₃) (i : ι) :
    (f ≫ g).hom i = f.hom i ≫ g.hom i :=
  rfl

@[simp]
lemma id_hom (D : F.DescentData' sq sq₃) (i : ι) :
    Hom.hom (𝟙 D) i = 𝟙 _ :=
  rfl

@[reassoc]
lemma comm {D₁ D₂ : F.DescentData' sq sq₃} (φ : D₁ ⟶ D₂)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    (F.map f₁.op.toLoc).map (φ.hom i₁) ≫ pullHom D₂.hom q f₁ f₂ hf₁ hf₂ =
      pullHom D₁.hom q f₁ f₂ hf₁ hf₂ ≫ (F.map f₂.op.toLoc).map (φ.hom i₂) := by
  obtain ⟨p, _, _⟩  := (sq i₁ i₂).isPullback.exists_lift f₁ f₂ (by aesop)
  rw [← pull_pullHom D₂.hom p (sq i₁ i₂).p q (by aesop) (sq i₁ i₂).p₁ (sq i₁ i₂).p₂
    (by simp) (by simp) f₁ f₂ (by aesop) (by aesop),
    ← pull_pullHom D₁.hom p (sq i₁ i₂).p q (by aesop) (sq i₁ i₂).p₁ (sq i₁ i₂).p₂
      (by simp) (by simp) f₁ f₂ (by aesop) (by aesop)]
  dsimp only [DescentData.pull]
  rw [NatTrans.naturality_assoc]
  dsimp
  rw [← Functor.map_comp_assoc, φ.comm i₁ i₂, Functor.map_comp_assoc,
    mapComp'_inv_naturality]
  simp only [Category.assoc]

@[simps]
def isoMk {D₁ D₂ : F.DescentData' sq sq₃} (e : ∀ (i : ι), D₁.obj i ≅ D₂.obj i)
    (comm : ∀ (i₁ i₂ : ι), (F.map (sq i₁ i₂).p₁.op.toLoc).map (e i₁).hom ≫
      pullHom D₂.hom (sq i₁ i₂).p (sq i₁ i₂).p₁ (sq i₁ i₂).p₂ =
    pullHom D₁.hom (sq i₁ i₂).p (sq i₁ i₂).p₁ (sq i₁ i₂).p₂ ≫
      (F.map (sq i₁ i₂).p₂.op.toLoc).map (e i₂).hom := by aesop_cat) : D₁ ≅ D₂ where
  hom :=
    { hom i := (e i).hom
      comm := comm }
  inv :=
    { hom i := (e i).inv
      comm i₁ i₂ := by
        rw [← cancel_mono ((F.map _).map (e i₂).hom), Category.assoc,
          Category.assoc, Iso.map_inv_hom_id, Category.comp_id,
          ← cancel_epi ((F.map _).map (e i₁).hom),
          Iso.map_hom_inv_id_assoc, comm i₁ i₂] }

@[simps]
noncomputable def descentData (D : F.DescentData' sq sq₃) : F.DescentData f where
  obj := D.obj
  hom _ _ _ _ _ _ hf₁ hf₂ := pullHom D.hom _ _ _ hf₁ hf₂
  pull_hom _ _ _ _ _ hq _ _ _ _ _ _ _ _ hgf₁ hgf₂ :=
    pull_pullHom _ _ _ _ hq _ _ _ _ _ _ hgf₁ hgf₂

@[simps]
def ofDescentData (D : F.DescentData f) : F.DescentData' sq sq₃ where
  obj := D.obj
  hom i₁ i₂ := D.hom (sq i₁ i₂).p (sq i₁ i₂).p₁ (sq i₁ i₂).p₂
  hom_self i := by
    obtain ⟨p, h₁, h₂⟩ := (sq i i).isPullback.exists_lift (𝟙 _) (𝟙 _) (by simp)
    have : p ≫ (sq i i).p = f i := by rw [← (sq i i).hp₁, reassoc_of% h₁]
    rw [pullHom_eq_pull _ _ _ _ _ _ p, D.pull_hom _ _ (f i), D.hom_self (f i) (𝟙 _)]
    all_goals aesop
  hom_comp i₁ i₂ i₃ := by
    rw [pullHom_eq_pull _ _ _ _ _ _ (sq₃ i₁ i₂ i₃).p₁₂,
      pullHom_eq_pull _ _ _ _ _ _ (sq₃ i₁ i₂ i₃).p₂₃,
      pullHom_eq_pull _ _ _ _ _ _ (sq₃ i₁ i₂ i₃).p₁₃,
      D.pull_hom _ _ (sq₃ i₁ i₂ i₃).p, D.pull_hom _ _ (sq₃ i₁ i₂ i₃).p,
      D.pull_hom _ _ (sq₃ i₁ i₂ i₃).p,
      D.hom_comp]
    all_goals aesop

@[simps]
noncomputable def toDescentDataFunctor : F.DescentData' sq sq₃ ⥤ F.DescentData f where
  obj D := D.descentData
  map φ :=
    { hom := φ.hom
      comm := comm φ }

@[simps]
noncomputable def fromDescentDataFunctor : F.DescentData f ⥤ F.DescentData' sq sq₃ where
  obj D := .ofDescentData D
  map {D₁ D₂} φ :=
    { hom := φ.hom
      comm i₁ i₂ := by
        rw [pullHom_eq_pull _ _ _ _ _ _ (𝟙 _) (by simp) (by simp),
          pullHom_eq_pull _ _ _ _ _ _ (𝟙 _) (by simp) (by simp)]
        simp }

end DescentData'

end Pseudofunctor

end CategoryTheory
