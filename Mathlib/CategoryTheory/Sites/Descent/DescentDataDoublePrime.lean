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

lemma homEquiv_symm_pullHom' ⦃X₁ X₂ : C⦄
    ⦃obj₁ : (F.obj (.mk (op X₁))).obj⦄ ⦃obj₂ : (F.obj (.mk (op X₂))).obj⦄
    ⦃X₁₂ : C⦄ ⦃p₁ : X₁₂ ⟶ X₁⦄ ⦃p₂ : X₁₂ ⟶ X₂⦄
    (hom : obj₁ ⟶ (F.map p₁.op.toLoc).g.obj ((F.map p₂.op.toLoc).f.obj obj₂))
    ⦃Y₁₂ : C⦄ (g : Y₁₂ ⟶ X₁₂) (gp₁ : Y₁₂ ⟶ X₁) (gp₂ : Y₁₂ ⟶ X₂)
    (hgp₁ : g ≫ p₁ = gp₁) (hgp₂ : g ≫ p₂ = gp₂) :
    ((F.map gp₁.op.toLoc).adj.toCategory.homEquiv _ _ ).symm (pullHom'' hom g gp₁ gp₂ hgp₁ hgp₂) =
      pullHom (F := F.comp Adj.forget₁)
        ((((F.map p₁.op.toLoc).adj.toCategory).homEquiv _ _ ).symm hom) g gp₁ gp₂ hgp₁ hgp₂ := by
  sorry

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

namespace DescentData''

variable {F} {sq} {obj : ∀ (i : ι), (F.obj (.mk (op (X i)))).obj}
  (hom : ∀ i₁ i₂, obj i₁ ⟶ (F.map (sq i₁ i₂).p₁.op.toLoc).g.obj
    ((F.map (sq i₁ i₂).p₂.op.toLoc).f.obj (obj i₂)))

section

def dataEquivDescentData' :
    (∀ i₁ i₂, obj i₁ ⟶ (F.map (sq i₁ i₂).p₁.op.toLoc).g.obj
      ((F.map (sq i₁ i₂).p₂.op.toLoc).f.obj (obj i₂))) ≃
    (∀ i₁ i₂, (F.map (sq i₁ i₂).p₁.op.toLoc).f.obj (obj i₁) ⟶
      (F.map (sq i₁ i₂).p₂.op.toLoc).f.obj (obj i₂)) :=
  Equiv.piCongrRight (fun i₁ ↦ Equiv.piCongrRight (fun i₂ ↦
    (((F.map (sq i₁ i₂).p₁.op.toLoc).adj.toCategory).homEquiv _ _).symm))


lemma hom_self_iff_dataEquivDescentData' :
    (∀ (i : ι) (δ : (sq i i).Diagonal),
      pullHom'' (hom i i) δ.f (𝟙 _) (𝟙 _) = (F.map (𝟙 (.mk (op (X i))))).adj.unit.app _) ↔
    ∀ (i : ι), DescentData'.pullHom' (F := F.comp Adj.forget₁)
        (dataEquivDescentData' hom) (f i) (𝟙 (X i)) (𝟙 (X i)) = 𝟙 _ := by
  refine forall_congr' (fun i ↦ ?_)
  have δ : (sq i i).Diagonal := Classical.arbitrary _
  trans ((F.map (𝟙 (.mk (op (X i))))).adj.toCategory.homEquiv _ _).symm
    (pullHom'' (hom i i) δ.f (𝟙 (X i)) (𝟙 (X i))) = 𝟙 _
  · dsimp
    rw [← Adjunction.toCategory_unit, ← Adjunction.homEquiv_id,
      Equiv.apply_eq_iff_eq_symm_apply]
    constructor
    · intro h
      rw [h, Equiv.symm_symm]
    · intro h δ'
      obtain rfl := Subsingleton.elim δ δ'
      exact h
  · convert Iff.rfl using 2
    have := homEquiv_symm_pullHom' (hom _ _) δ.f (𝟙 _) (𝟙 _) (by simp) (by simp)
    dsimp at this ⊢
    rw [this]
    apply DescentData'.pullHom'_eq_pullHom <;> simp

lemma hom_comp_iff_dataEquivDescentData' :
    (∀ i₁ i₂ i₃, homComp sq₃ hom i₁ i₂ i₃ = pullHom'' (hom i₁ i₃) (sq₃ i₁ i₂ i₃).p₁₃ _ _) ↔
      ∀ (i₁ i₂ i₃ : ι),
        DescentData'.pullHom' (F := F.comp Adj.forget₁)
          (dataEquivDescentData' hom) (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ ≫
        DescentData'.pullHom'
          (dataEquivDescentData' hom) (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ =
        DescentData'.pullHom'
          (dataEquivDescentData' hom) (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃ := by
  refine forall_congr' (fun i₁ ↦ forall_congr' (fun i₂ ↦ forall_congr' (fun i₃ ↦ ?_)))
  sorry

end

section

variable [∀ i₁ i₂, IsIso (F.baseChange (sq i₁ i₂).isPullback.toCommSq.flip.op.toLoc)]
-- should require the same for `(sq₃ i₁ i₂ i₃).isPullback₂`.

noncomputable def dataEquivCoalgebra
  [∀ i₁ i₂, IsIso (F.baseChange (sq i₁ i₂).isPullback.toCommSq.flip.op.toLoc)] :
    (∀ i₁ i₂, obj i₁ ⟶ (F.map (sq i₁ i₂).p₁.op.toLoc).g.obj
      ((F.map (sq i₁ i₂).p₂.op.toLoc).f.obj (obj i₂))) ≃
    (∀ i₁ i₂, obj i₁ ⟶ (F.map (f i₁).op.toLoc).f.obj ((F.map (f i₂).op.toLoc).g.obj (obj i₂))) :=
  Equiv.piCongrRight (fun i₁ ↦ Equiv.piCongrRight (fun i₂ ↦
    Iso.homCongr (Iso.refl _)
      ((asIso (F.baseChange (sq i₁ i₂).isPullback.toCommSq.flip.op.toLoc)).symm.app _)))

lemma hom_self_iff_dataEquivCoalgebra :
    (∀ (i : ι) (δ : (sq i i).Diagonal),
      pullHom'' (hom i i) δ.f (𝟙 _) (𝟙 _) = (F.map (𝟙 (.mk (op (X i))))).adj.unit.app _) ↔
    ∀ i, dataEquivCoalgebra hom i i ≫ (F.map (f i).op.toLoc).adj.counit.app _ = 𝟙 _ := by
  refine forall_congr' (fun i ↦ ?_)
  sorry

lemma hom_comp_iff_dataEquivCoalgebra :
    (∀ i₁ i₂ i₃, homComp sq₃ hom i₁ i₂ i₃ = pullHom'' (hom i₁ i₃) (sq₃ i₁ i₂ i₃).p₁₃ _ _) ↔
    ∀ (i₁ i₂ i₃ : ι),
      dataEquivCoalgebra hom i₁ i₂ ≫ (F.map (f i₁).op.toLoc).f.map
        ((F.map (f i₂).op.toLoc).g.map (dataEquivCoalgebra hom i₂ i₃)) =
      dataEquivCoalgebra hom i₁ i₃ ≫
        (F.map (f i₁).op.toLoc).f.map ((F.map (f i₂).op.toLoc).adj.unit.app _) := by
  refine forall_congr' (fun i₁ ↦ forall_congr' (fun i₂ ↦ forall_congr' (fun i₃ ↦ ?_)))
  sorry


end

end DescentData''

end Pseudofunctor

end CategoryTheory
