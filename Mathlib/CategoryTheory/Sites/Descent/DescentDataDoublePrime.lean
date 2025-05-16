/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
import Mathlib.CategoryTheory.Sites.Descent.DescentDataAsCoalgebra
import Mathlib.CategoryTheory.Bicategory.Adjunction.Adj

/-!
# Descent data ...

-/

namespace CategoryTheory

open Opposite Limits Bicategory

namespace Pseudofunctor

open LocallyDiscreteOpToCat

variable {C : Type*} [Category C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) (Adj Cat))
  {ι : Type*} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
  (sq : ∀ i j, ChosenPullback (f i) (f j))
  (sq₃ : ∀ (i₁ i₂ i₃ : ι), ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃))

namespace DescentData''

variable {F sq}
section

variable {obj : ∀ (i : ι), (F.obj (.mk (op (X i)))).obj}
  (hom : ∀ (i₁ i₂ : ι), obj i₁ ⟶ (F.map (sq i₁ i₂).p₁.op.toLoc).g.obj
    ((F.map (sq i₁ i₂).p₂.op.toLoc).f.obj (obj i₂)))

def homComp (i₁ i₂ i₃ : ι) : obj i₁ ⟶ (F.map (sq₃ i₁ i₂ i₃).p₁.op.toLoc).g.obj
      ((F.map (sq₃ i₁ i₂ i₃).p₃.op.toLoc).f.obj (obj i₃)) :=
  hom i₁ i₂ ≫ (F.map (sq i₁ i₂).p₁.op.toLoc).g.map
      ((F.map (sq i₁ i₂).p₂.op.toLoc).f.map (hom i₂ i₃)) ≫
        (F.map (sq i₁ i₂).p₁.op.toLoc).g.map
          ((F.baseChange (sq₃ i₁ i₂ i₃).isPullback₂.toCommSq.flip.op.toLoc).app _) ≫
    (Adj.gIso (F.mapComp' (sq i₁ i₂).p₁.op.toLoc (sq₃ i₁ i₂ i₃).p₁₂.op.toLoc
          (sq₃ i₁ i₂ i₃).p₁.op.toLoc (by aesoptoloc))).inv.app _ ≫
    (F.map (sq₃ i₁ i₂ i₃).p₁.op.toLoc).g.map
      ((Adj.fIso (F.mapComp' (sq i₂ i₃).p₂.op.toLoc (sq₃ i₁ i₂ i₃).p₂₃.op.toLoc
          (sq₃ i₁ i₂ i₃).p₃.op.toLoc (by aesoptoloc))).inv.app _)

end

section

variable {X₁₂ X₁ X₂ : C}
  {obj₁ : (F.obj (.mk (op X₁))).obj} {obj₂ : (F.obj (.mk (op X₂))).obj}
  {p₁ : X₁₂ ⟶ X₁} {p₂ : X₁₂ ⟶ X₂}
  (hom : obj₁ ⟶ (F.map p₁.op.toLoc).g.obj ((F.map p₂.op.toLoc).f.obj obj₂))

def pullHom'' ⦃Y₁₂ : C⦄ (p₁₂ : Y₁₂ ⟶ X₁₂) (q₁ : Y₁₂ ⟶ X₁) (q₂ : Y₁₂ ⟶ X₂)
    (hq₁ : p₁₂ ≫ p₁ = q₁ := by aesop_cat) (hq₂ : p₁₂ ≫ p₂ = q₂ := by aesop_cat) :
    obj₁ ⟶ (F.map q₁.op.toLoc).g.obj ((F.map q₂.op.toLoc).f.obj obj₂) :=
  hom ≫ (F.map p₁.op.toLoc).g.map ((F.map p₁₂.op.toLoc).adj.unit.app _) ≫
    (Adj.gIso (F.mapComp' p₁.op.toLoc p₁₂.op.toLoc q₁.op.toLoc (by aesoptoloc))).inv.app _ ≫
      (F.map q₁.op.toLoc).g.map
    ((Adj.fIso (F.mapComp' p₂.op.toLoc p₁₂.op.toLoc q₂.op.toLoc (by aesoptoloc))).inv.app _)

end

end DescentData''

open DescentData'' in
structure DescentData'' where
  obj (i : ι) : (F.obj (.mk (op (X i)))).obj
  hom (i₁ i₂ : ι) : obj i₁ ⟶
    (F.map (sq i₁ i₂).p₁.op.toLoc).g.obj
      ((F.map (sq i₁ i₂).p₂.op.toLoc).f.obj (obj i₂))
  hom_self (i : ι) (δ : (sq i i).Diagonal) :
    pullHom'' (hom i i) δ.f (𝟙 _) (𝟙 _) = (F.map (𝟙 (.mk (op (X i))))).adj.unit.app _
  hom_comp (i₁ i₂ i₃ : ι) :
    homComp sq₃ hom i₁ i₂ i₃ = pullHom'' (hom i₁ i₃) (sq₃ i₁ i₂ i₃).p₁₃ _ _

end Pseudofunctor

end CategoryTheory
