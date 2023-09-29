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

variable {I : Type*} [AddCommMonoid I] (c : ComplexShape I)

structure TensorSigns where
  ε : I → ℤ
  rel_add (p q r : I) (hpq : c.Rel p q) : c.Rel (p + r) (q + r)
  ε_succ (p q : I) (hpq : c.Rel p q) : ε q = - ε p

variable {c}

lemma TensorSigns.add_rel (s : TensorSigns c) (p q r : I) (hpq : c.Rel p q) :
    c.Rel (r + p) (r + q) := by
  rw [add_comm r, add_comm r]
  exact s.rel_add _ _ _ hpq

def tensorSignsDownℕ  : TensorSigns (ComplexShape.down ℕ) where
  ε p := (-1) ^ p
  rel_add p q r (hpq : q + 1 = p) := by
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
  ε_succ := by
    rintro p _ rfl
    rw [Int.negOnePow_succ]

end ComplexShape

namespace HomologicalComplex

variable (C : Type*) [Category C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  {I : Type*} [AddCommMonoid I] (c : ComplexShape I) [DecidableEq I]

variable {C}

@[simps]
def ofGradedObject (X : GradedObject I C) (c : ComplexShape I)
    (d : ∀ (i j : I), X i ⟶ X j) (shape : ∀ (i j : I), ¬ c.Rel i j → d i j = 0)
    (d_comp_d' : ∀ (i j k : I), c.Rel i j → c.Rel j k → d i j ≫ d j k = 0) :
    HomologicalComplex C c where
  X := X
  d := d
  shape := shape
  d_comp_d' := d_comp_d'

variable {c}

abbrev toGradedObject (K : HomologicalComplex C c) : GradedObject I C := K.X

variable (C c)

@[simps]
def toGradedObjectFunctor : HomologicalComplex C c ⥤ GradedObject I C where
  obj K := K.toGradedObject
  map f := f.f

instance : Faithful (toGradedObjectFunctor C c) where
  map_injective {K L} f g h := by
    ext n
    exact congr_fun h n

variable {C c}

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

variable (s : c.TensorSigns)

attribute [local simp] add_comp comp_add zsmul_comp comp_zsmul


-- this is ok, but these verifications should be part of a more general construction
-- HomologicalComplex C₁ c ⥤ HomologicalComplex C₂ c' ⥤ HomologicalComplex C₃ c''
-- for a bifunctor C₁ ⥤ C₂ ⥤ C₃`, some map `ι × ι' → ι''`, + conditions, + bunch of signs
-- see Algebra.Homology.HomologicalBicomplex

noncomputable def tensorObj (K L : HomologicalComplex C c) [HasTensor K L] :
    HomologicalComplex C c :=
  ofGradedObject (GradedObject.Monoidal.tensorObj K.toGradedObject L.toGradedObject) c
    (fun n m => GradedObject.Monoidal.descTensor
      (fun p q hpq =>
        (K.d p (c.next p) ⊗ 𝟙 (L.X q)) ≫ GradedObject.Monoidal.ιTensorObjOrZero _ _ _ _ _ +
          (s.ε p : ℤ) • ((𝟙 (K.X p)) ⊗ L.d q (c.next q)) ≫ GradedObject.Monoidal.ιTensorObjOrZero _ _ _ _ _))
    (fun n m hnm => by
      ext p q hpq
      dsimp
      simp only [GradedObject.Monoidal.ι_descTensor, comp_zero]
      conv_rhs => rw [← add_zero 0]
      congr 1
      · by_cases c.Rel p (c.next p)
        · rw [GradedObject.Monoidal.ιTensorObjOrZero_eq_zero, comp_zero]
          intro h'
          apply hnm
          rw [← h', ← hpq]
          exact s.rel_add p (c.next p) q h
        · rw [K.shape _ _ h, zero_tensor, zero_comp]
      · by_cases c.Rel q (c.next q)
        · rw [GradedObject.Monoidal.ιTensorObjOrZero_eq_zero, comp_zero, smul_zero]
          intro h'
          apply hnm
          rw [← h', ← hpq, add_comm p, add_comm p]
          exact s.rel_add q (c.next q) p h
        . rw [L.shape _ _ h, tensor_zero, zero_comp, smul_zero])
    (fun i j k _ _ => by
      ext p q hpq
      dsimp
      simp only [GradedObject.Monoidal.ι_descTensor_assoc, Preadditive.add_comp, assoc, comp_zero]
      by_cases hj : c.next p + q = j
      · rw [GradedObject.Monoidal.ιTensorObjOrZero_eq _ _ _ _ _ hj]
        by_cases hj' : p + c.next q = j
        · simp only [GradedObject.Monoidal.ιTensorObjOrZero_eq _ _ _ _ _ hj',
            GradedObject.Monoidal.ι_descTensor, comp_add, comp_zsmul, tensor_id_comp_id_tensor_assoc,
            zsmul_comp, assoc,
            id_tensor_comp_tensor_id_assoc, ← tensor_comp_assoc, d_comp_d,
            tensor_zero, zero_tensor, zero_comp, smul_zero, zero_add, add_zero,
            comp_id, id_comp, ← add_smul]
          by_cases h : c.Rel p (c.next p)
          · rw [s.ε_succ _ _ h, add_left_neg, zero_smul]
          · rw [K.shape _ _ h, zero_tensor, zero_comp, smul_zero]
        · rw [GradedObject.Monoidal.ιTensorObjOrZero_eq_zero _ _ _ _ _ hj',
            comp_zero, smul_zero, zero_comp, add_zero, GradedObject.Monoidal.ι_descTensor,
            comp_add, comp_zsmul, tensor_id_comp_id_tensor_assoc,
            ← tensor_comp_assoc, d_comp_d, zero_tensor, zero_comp, zero_add]
          by_cases hp : c.Rel p (c.next p)
          · by_cases hq : c.Rel q (c.next q)
            · exfalso
              apply hj'
              rw [← hj, ← c.next_eq' (s.rel_add _ _ q hp),
                ← c.next_eq' (s.add_rel _ _ p hq)]
            · rw [L.shape _ _ hq, tensor_zero, zero_comp, smul_zero]
          . rw [K.shape _ _ hp, zero_tensor, zero_comp, smul_zero]
      · simp only [GradedObject.Monoidal.ιTensorObjOrZero_eq_zero _ _ _ _ _ hj, zero_comp,
          comp_zero, zero_add, zsmul_comp, assoc]
        by_cases hj' : p + c.next q = j
        · rw [GradedObject.Monoidal.ιTensorObjOrZero_eq _ _ _ _ _ hj',
            GradedObject.Monoidal.ι_descTensor, comp_add,
            id_tensor_comp_tensor_id_assoc, comp_zsmul,
            ← tensor_comp_assoc, d_comp_d, tensor_zero, zero_comp,
            smul_zero, add_zero]
          by_cases hp : c.Rel p (c.next p)
          · by_cases hq : c.Rel q (c.next q)
            · exfalso
              apply hj
              rw [← hj', ← c.next_eq' (s.rel_add _ _ q hp), ← c.next_eq' (s.add_rel _ _ p hq)]
            · rw [L.shape _ _ hq, tensor_zero, zero_comp, smul_zero]
          · rw [K.shape _ _ hp, zero_tensor, zero_comp, smul_zero]
        · rw [GradedObject.Monoidal.ιTensorObjOrZero_eq_zero _ _ _ _ _ hj',
            zero_comp, comp_zero, smul_zero])

@[simps]
noncomputable def tensorHom {K₁ L₁ K₂ L₂ : HomologicalComplex C c}
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) [HasTensor K₁ K₂] [HasTensor L₁ L₂] :
    tensorObj s K₁ K₂ ⟶ tensorObj s L₁ L₂ where
  f := GradedObject.Monoidal.tensorHom f₁.f f₂.f
  comm' i j _ := by
    apply GradedObject.Monoidal.tensorObj_ext
    intro p q hpq
    dsimp [tensorObj]
    simp only [GradedObject.Monoidal.ι_tensorHom_assoc, GradedObject.Monoidal.ι_descTensor,
      comp_add, comp_zsmul, GradedObject.Monoidal.ι_descTensor_assoc, add_comp,
      assoc, zsmul_comp]
    congr 1
    · by_cases hj : c.next p + q = j
      · simp only [GradedObject.Monoidal.ιTensorObjOrZero_eq _ _ _ _ _ hj,
          GradedObject.Monoidal.ι_tensorHom,
          ← tensor_comp_assoc, id_comp, comp_id, Hom.comm]
      · simp only [GradedObject.Monoidal.ιTensorObjOrZero_eq_zero _ _ _ _ _ hj,
          comp_zero, zero_comp]
    · by_cases hj : p + c.next q = j
      · simp only [GradedObject.Monoidal.ιTensorObjOrZero_eq _ _ _ _ _ hj,
          GradedObject.Monoidal.ι_tensorHom,
          ← tensor_comp_assoc, id_comp, comp_id, Hom.comm]
      · simp only [GradedObject.Monoidal.ιTensorObjOrZero_eq_zero _ _ _ _ _ hj,
          zero_comp, comp_zero]

lemma tensor_id (K L : HomologicalComplex C c) [HasTensor K L] :
    tensorHom s (𝟙 K) (𝟙 L) = 𝟙 (tensorObj s K L) := by
  apply (toGradedObjectFunctor C c).map_injective
  apply GradedObject.Monoidal.tensor_id

lemma tensor_comp {K₁ K₂ K₃ L₁ L₂ L₃ : HomologicalComplex C c}
    (f₁ : K₁ ⟶ K₂) (f₂ : K₂ ⟶ K₃)
    (g₁ : L₁ ⟶ L₂) (g₂ : L₂ ⟶ L₃) [HasTensor K₁ L₁] [HasTensor K₂ L₂] [HasTensor K₃ L₃] :
    tensorHom s (f₁ ≫ f₂) (g₁ ≫ g₂) = tensorHom s f₁ g₁ ≫ tensorHom s f₂ g₂ := by
  apply (toGradedObjectFunctor C c).map_injective
  apply GradedObject.Monoidal.tensor_comp

section

variable (K₁ K₂ K₃ : HomologicalComplex C c)
  [HasTensor K₁ K₂] [HasTensor (tensorObj s K₁ K₂) K₃]
  [HasTensor K₂ K₃] [HasTensor K₁ (tensorObj s K₂ K₃)]
  [GradedObject.HasGoodTensor₁₂Tensor K₁.X K₂.X K₃.X]
  [GradedObject.HasGoodTensorTensor₂₃ K₁.X K₂.X K₃.X]


/-def associator :
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
