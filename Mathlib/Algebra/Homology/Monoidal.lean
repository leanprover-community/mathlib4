import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.GradedObject.Monoidal
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomologicalBicomplex
import Mathlib.Algebra.GroupPower.NegOnePow

open CategoryTheory Category Limits MonoidalCategory Preadditive
  MonoidalPreadditive

instance (C D : Type*) [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] : PreservesFiniteCoproducts F := sorry

namespace ComplexShape

variable {I : Type*} [AddMonoid I] (c : ComplexShape I)

structure TensorSigns where
  ε : I → ℤ
  rel_add (p q r : I) (hpq : c.Rel p q) : c.Rel (p + r) (q + r)
  add_rel (p q r : I) (hpq : c.Rel p q) : c.Rel (r + p) (r + q)
  ε_succ (p q : I) (hpq : c.Rel p q) : ε q = - ε p

variable {c}

def TensorSigns.totalComplexShape (s : TensorSigns c) : TotalComplexShape c c c where
  π := fun ⟨p, q⟩ => p + q
  ε₁ := fun _ => 1
  ε₂ := fun ⟨p, _⟩ => s.ε p
  rel₁ p p' h q := s.rel_add _ _ _ h
  rel₂ p q q' h := s.add_rel _ _ _ h
  eq p p' _ _ h _ := by
    dsimp
    rw [one_mul, mul_one, s.ε_succ _ _ h, add_left_neg]

def tensorSignsDownℕ  : TensorSigns (ComplexShape.down ℕ) where
  ε p := (-1) ^ p
  rel_add p q r (hpq : q + 1 = p) := by
    simp only [down_Rel]
    linarith
  add_rel p q r (hpq : q + 1 = p) := by
    simp only [down_Rel]
    linarith
  ε_succ := by
    rintro _ q rfl
    dsimp
    rw [pow_add, pow_one, mul_neg, mul_one, neg_neg]

def tensorSignsUpℤ   : TensorSigns (ComplexShape.up ℤ) where
  ε := Int.negOnePow
  rel_add p q r (hpq : p + 1 = q) := by
    simp only [up_Rel]
    linarith
  add_rel p q r (hpq : p + 1 = q) := by
    simp only [up_Rel]
    linarith
  ε_succ := by
    rintro p _ rfl
    rw [Int.negOnePow_succ]

end ComplexShape

namespace HomologicalComplex

variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  {I : Type*} [AddCommMonoid I] {c : ComplexShape I} [DecidableEq I]

noncomputable def _root_.CategoryTheory.GradedObject.Monoidal.ιTensorObjOrZero (X₁ X₂ : GradedObject I C)
    [GradedObject.HasTensor X₁ X₂]
    (i₁ i₂ j : I) : X₁ i₁ ⊗ X₂ i₂ ⟶ GradedObject.Monoidal.tensorObj X₁ X₂ j :=
  if h : i₁ + i₂ = j
    then
      GradedObject.Monoidal.ιTensorObj X₁ X₂ i₁ i₂ j h
    else 0

noncomputable def _root_.CategoryTheory.GradedObject.Monoidal.ιTensorObjOrZero_eq (X₁ X₂ : GradedObject I C)
    [GradedObject.HasTensor X₁ X₂]
    (i₁ i₂ j : I) (h : i₁ + i₂ = j) :
    GradedObject.Monoidal.ιTensorObjOrZero X₁ X₂ i₁ i₂ j =
      GradedObject.Monoidal.ιTensorObj X₁ X₂ i₁ i₂ j h :=
  dif_pos h

noncomputable def _root_.CategoryTheory.GradedObject.Monoidal.ιTensorObjOrZero_eq_zero (X₁ X₂ : GradedObject I C)
    [GradedObject.HasTensor X₁ X₂]
    (i₁ i₂ j : I) (h : i₁ + i₂ ≠ j) :
    GradedObject.Monoidal.ιTensorObjOrZero X₁ X₂ i₁ i₂ j = 0 :=
  dif_neg h

abbrev HasTensor (K L : HomologicalComplex C c) :=
  GradedObject.HasTensor K.toGradedObject L.toGradedObject

namespace Monoidal

variable {s}

variable (s : c.TensorSigns) [(curryObj (MonoidalCategory.tensor C)).PreservesZeroMorphisms]
  [∀ (X : C), ((curryObj (tensor C)).obj X).PreservesZeroMorphisms ]

attribute [local simp] add_comp comp_add zsmul_comp comp_zsmul

instance (K L : HomologicalComplex C c) [h : HasTensor K L] :
  (((Functor.mapHomologicalComplex₂ (curryObj (tensor C)) c c).obj K).obj L).toGradedObject.HasMap
      s.totalComplexShape.π := h

noncomputable def tensorObj (K L : HomologicalComplex C c) [HasTensor K L] :
    HomologicalComplex C c :=
  (((Functor.mapHomologicalComplex₂ (curryObj (MonoidalCategory.tensor C)) c c).obj K).obj L).total s.totalComplexShape

noncomputable def tensorHom {K₁ L₁ K₂ L₂ : HomologicalComplex C c}
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) [HasTensor K₁ K₂] [HasTensor L₁ L₂] :
    tensorObj s K₁ K₂ ⟶ tensorObj s L₁ L₂ :=
  HomologicalComplex₂.totalMap
    (((Functor.mapHomologicalComplex₂ (curryObj (MonoidalCategory.tensor C)) c c).map f₁).app K₂ ≫
      ((Functor.mapHomologicalComplex₂ (curryObj (MonoidalCategory.tensor C)) c c).obj L₁).map f₂) _

lemma tensorHom_f {K₁ L₁ K₂ L₂ : HomologicalComplex C c}
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) [HasTensor K₁ K₂] [HasTensor L₁ L₂] :
  (tensorHom s f₁ f₂).f = GradedObject.Monoidal.tensorHom f₁.f f₂.f := rfl

lemma tensor_id (K L : HomologicalComplex C c) [HasTensor K L] :
    tensorHom s (𝟙 K) (𝟙 L) = 𝟙 (tensorObj s K L) := by
  apply toGradedObjectFunctor_map_injective
  apply GradedObject.Monoidal.tensor_id

lemma tensor_comp {K₁ K₂ K₃ L₁ L₂ L₃ : HomologicalComplex C c}
    (f₁ : K₁ ⟶ K₂) (f₂ : K₂ ⟶ K₃)
    (g₁ : L₁ ⟶ L₂) (g₂ : L₂ ⟶ L₃) [HasTensor K₁ L₁] [HasTensor K₂ L₂] [HasTensor K₃ L₃] :
    tensorHom s (f₁ ≫ f₂) (g₁ ≫ g₂) = tensorHom s f₁ g₁ ≫ tensorHom s f₂ g₂ := by
  apply toGradedObjectFunctor_map_injective
  apply GradedObject.Monoidal.tensor_comp

section

variable (K₁ K₂ K₃ : HomologicalComplex C c)
  [HasTensor K₁ K₂] [HasTensor (tensorObj s K₁ K₂) K₃]
  [HasTensor K₂ K₃] [HasTensor K₁ (tensorObj s K₂ K₃)]
  [GradedObject.HasGoodTensor₁₂Tensor K₁.X K₂.X K₃.X]
  [GradedObject.HasGoodTensorTensor₂₃ K₁.X K₂.X K₃.X]

/-noncomputable def associator :
    tensorObj s (tensorObj s K₁ K₂) K₃ ≅ tensorObj s K₁ (tensorObj s K₂ K₃) :=
  have : GradedObject.HasTensor (GradedObject.Monoidal.tensorObj K₁.X K₂.X) K₃.X :=
    (inferInstance : HasTensor (tensorObj s K₁ K₂) K₃)
  have : GradedObject.HasTensor K₁.X (GradedObject.Monoidal.tensorObj K₂.X K₃.X) :=
    (inferInstance : HasTensor K₁ (tensorObj s K₂ K₃))
  Hom.isoOfComponents (fun i => (GradedObject.eval i).mapIso
    (GradedObject.Monoidal.associator K₁.toGradedObject K₂.toGradedObject K₃.toGradedObject)) (by
      intro i j hij
      dsimp
      sorry)-/

end

end Monoidal

section

variable
  [∀ (X₁ X₂ : GradedObject I C), GradedObject.HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasInitial C]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C)
    ((curryObj (MonoidalCategory.tensor C)).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C)
    ((curryObj (MonoidalCategory.tensor C)).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]

instance (X : C) : ((curryObj (MonoidalCategory.tensor C)).obj X).Additive := by
  change (tensorLeft X).Additive
  infer_instance

instance (X : C) : ((curryObj (MonoidalCategory.tensor C)).flip.obj X).Additive := by
  change (tensorRight X).Additive
  infer_instance

noncomputable example : MonoidalCategory (GradedObject I C) := inferInstance

end

end HomologicalComplex
