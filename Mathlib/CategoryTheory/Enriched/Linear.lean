import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

namespace CategoryTheory

universe w v v' u u'

open TensorProduct MonoidalCategory

variable {R : Type u} [CommRing R]

variable {C : Type u} [Category.{u} C] [Preadditive C] [Linear R C]

@[simp]
lemma aux1 {X Y Z : Type u} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z] (f : X →ₗ[R] Y):
    ModuleCat.ofHom f ▷ ModuleCat.of R Z =
    ModuleCat.ofHom (LinearMap.rTensor Z f) :=
  rfl

@[simp]
lemma aux1' {X Y Z : Type u} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z] (f : X →ₗ[R] Y):
    ModuleCat.of R Z ◁ ModuleCat.ofHom f =
    ModuleCat.ofHom (LinearMap.lTensor Z f) :=
  rfl

@[simp]
lemma aux2 {X : Type u} [AddCommGroup X] [Module R X] :
    ModuleCat.Hom.hom (λ_ (ModuleCat.of R X)).inv = (TensorProduct.lid R X).symm.toLinearMap :=
  rfl

@[simp]
lemma aux2' {X : Type u} [AddCommGroup X] [Module R X] :
    ModuleCat.Hom.hom (ρ_ (ModuleCat.of R X)).inv = (TensorProduct.rid R X).symm.toLinearMap :=
  rfl

@[simp]
lemma aux2'' {X Y Z : Type u} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [AddCommGroup Z] [Module R Z] :
    ModuleCat.Hom.hom (α_ (ModuleCat.of R X) (ModuleCat.of R Y) (ModuleCat.of R Z)).inv =
      (TensorProduct.assoc R X Y Z).symm.toLinearMap :=
  rfl

lemma aux8 {W X Y Z : C} (f₁ f₂ : ((W ⟶ X) ⊗[R] (X ⟶ Y)) ⊗[R] (Y ⟶ Z)) :
    (TensorProduct.assoc R _ _ _).toLinearMap (f₁ + f₂) =
    (TensorProduct.assoc R _ _ _).toLinearMap f₁ + (TensorProduct.assoc R _ _ _).toLinearMap f₂ :=
  (TensorProduct.assoc R (W ⟶ X) (X ⟶ Y) (Y ⟶ Z)).map_add  f₁ f₂

lemma aux4'' {W X Y Z : C} (f : ((W ⟶ X) ⊗[R] (X ⟶ Y)) ⊗[R] (Y ⟶ Z)) :
    lift (Linear.comp W Y Z) ((LinearMap.rTensor (Y ⟶ Z) (lift (Linear.comp W X Y))) f) =
      lift (R := R) (Linear.comp W X Z)
        (LinearMap.lTensor (R := R) (N := (X ⟶ Y) ⊗[R] (Y ⟶ Z)) (P := X ⟶ Z) (W ⟶ X)
          (lift (Linear.comp X Y Z)) ((TensorProduct.assoc R _ _ _).toLinearMap f)) :=
  TensorProduct.induction_on f rfl
    (fun fg h => TensorProduct.induction_on fg
      (by simp)
      (by simp)
      (fun fg₂ fg₃ h₂ h₃ => by
        simp
        rw [add_tmul]
        erw [aux8]
        simp
        erw [← h₂, ← h₃, ← Preadditive.add_comp]))
    (fun f₂ f₃ h₂ h₃ => by
      rw [aux8]
      simp [h₂, h₃])

lemma aux5 {X : C} : (LinearMap.ringLmapEquivSelf R R (X ⟶ X)).symm (𝟙 X) =
    LinearMap.toSpanSingleton R (X ⟶ X) (𝟙 X) := rfl

lemma aux5' {X Z : C} (f : X ⟶ Z) :
    (LinearMap.ringLmapEquivSelf R R (X ⟶ Z)).symm f =
    LinearMap.toSpanSingleton R  (X ⟶ Z) f := rfl

lemma aux7 {W X Y Z: ModuleCat R} (f : W ⟶ X) (g : Y ⟶ Z) :
    ModuleCat.Hom.hom (R := R) (f ⊗ g) = map (ModuleCat.Hom.hom f) (ModuleCat.Hom.hom g) :=
  rfl

noncomputable instance : EnrichedOrdinaryCategory (ModuleCat R) C where
  Hom X Y := .of R (X ⟶ Y)
  id X := ModuleCat.ofHom <| LinearMap.toSpanSingleton R (X ⟶ X) (𝟙 X)
  comp X Y Z := ModuleCat.ofHom <| lift (Linear.comp X Y Z)
  id_comp X Y := by
    ext f
    simp only [aux1, ModuleCat.hom_comp, ModuleCat.hom_ofHom, aux2, LinearMap.coe_comp,
      Function.comp_apply, ModuleCat.hom_id, LinearMap.id_coe, id_eq] at f ⊢
    erw [lid_symm_apply, LinearMap.rTensor_tmul _ (LinearMap.toSpanSingleton R _ (𝟙 X)) f 1,
      lift.tmul]
    simp
  comp_id X Y := by
    ext f
    simp only [aux1', ModuleCat.hom_comp, ModuleCat.hom_ofHom, aux2', LinearMap.coe_comp,
      Function.comp_apply, ModuleCat.hom_id, LinearMap.id_coe, id_eq] at f ⊢
    erw [rid_symm_apply, LinearMap.lTensor_tmul _ (LinearMap.toSpanSingleton R _ (𝟙 Y)) f 1,
      lift.tmul]
    simp
  assoc W X Y Z := by
    ext f
    change _ ⊗[R] _ ⊗[R] _ at f
    simp at f ⊢
    erw [aux4'']
    congr
    exact (TensorProduct.assoc R (W ⟶ X) (X ⟶ Y) (Y ⟶ Z)).right_inv f
  homEquiv {X Y} := (ModuleCat.homEquiv.trans
      (LinearMap.ringLmapEquivSelf R R (X ⟶ Y)).toEquiv).symm
  homEquiv_id X := rfl
  homEquiv_comp {X Y Z} f g := by
    dsimp [eComp]
    erw [aux5', aux5', aux5']
    rw [aux6]
    simp [ModuleCat.homEquiv]
    ext
    simp
    erw [aux2]
    simp [TensorProduct.lid]
    change _ =
      (lift (Linear.comp X Y Z))
        ((ModuleCat.Hom.hom
          (ModuleCat.ofHom (LinearMap.toSpanSingleton R (X ⟶ Y) f) ⊗
            ModuleCat.ofHom (LinearMap.toSpanSingleton R (Y ⟶ Z) g)))
          (1 ⊗ₜ 1))
    simp [aux7]
    erw [map_tmul (R := R) (LinearMap.toSpanSingleton R (X ⟶ Y) f)
      (LinearMap.toSpanSingleton R (Y ⟶ Z) g) 1 1]
    simp

end CategoryTheory
