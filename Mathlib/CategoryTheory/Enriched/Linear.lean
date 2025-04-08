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

@[simp]
lemma aux4 {X Y : C} (f : X ⟶ Y) :
    (LinearMap.toSpanSingleton R (X ⟶ X) (𝟙 X)).rTensor (X ⟶ Y)
      ((TensorProduct.lid R (X ⟶ Y)).symm.toLinearMap f) = 𝟙 X ⊗ₜ f := by
  simp

@[simp]
lemma aux4' {X Y : C} (f : X ⟶ Y) :
    (LinearMap.toSpanSingleton R (Y ⟶ Y) (𝟙 Y)).lTensor (X ⟶ Y)
      ((TensorProduct.rid R (X ⟶ Y)).symm.toLinearMap f) = f ⊗ₜ 𝟙 Y := by
  simp

lemma aux4'' {W X Y Z : C} (f : ((W ⟶ X) ⊗[R] (X ⟶ Y)) ⊗[R] (Y ⟶ Z)) :
    lift (Linear.comp W Y Z) ((LinearMap.rTensor (Y ⟶ Z) (lift (Linear.comp W X Y))) f) =
      lift (R := R) (Linear.comp W X Z)
        (LinearMap.lTensor (R := R) (N := (X ⟶ Y) ⊗[R] (Y ⟶ Z)) (P := X ⟶ Z) (W ⟶ X)
          (lift (Linear.comp X Y Z)) ((TensorProduct.assoc R _ _ _).toLinearMap f)) := sorry

#check TensorProduct.rid
#check TensorProduct.assoc
#check LinearMap.rTensor_tensor

noncomputable instance : EnrichedOrdinaryCategory (ModuleCat R) C where
  Hom X Y := .of R (X ⟶ Y)
  id X := ModuleCat.ofHom <| LinearMap.toSpanSingleton R (X ⟶ X) (𝟙 X)
  comp X Y Z := ModuleCat.ofHom <| lift (Linear.comp X Y Z)
  id_comp X Y := by
    ext f
    simp at f ⊢
    erw [aux4 (R := R) f]
    erw [lift.tmul]
    simp
  comp_id X Y := by
    ext f
    simp at f ⊢
    erw [aux4' (R := R) f]
    erw [lift.tmul]
    simp
  assoc W X Y Z := by
    ext f
    simp at f ⊢
    change _ ⊗[R] _ ⊗[R] _ at f
    simp at f ⊢
    erw [aux4'']
    congr
    exact (TensorProduct.assoc R (W ⟶ X) (X ⟶ Y) (Y ⟶ Z)).right_inv f
  homEquiv {X Y} := sorry

#check ModuleCat.tensorUnit

end CategoryTheory
