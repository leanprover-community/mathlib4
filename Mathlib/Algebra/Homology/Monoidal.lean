import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.GradedObject.Monoidal
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomologicalBicomplex
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.GroupPower.NegOnePow

open CategoryTheory Category Limits MonoidalCategory Preadditive
  MonoidalPreadditive

instance (C D : Type*) [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] : PreservesFiniteCoproducts F := sorry

namespace CategoryTheory

namespace MonoidalPreadditive

variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]

variable {X₁ X₂ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)

lemma tensor_zsmul (n : ℤ) : tensorHom f₁ (n • f₂) = n • tensorHom f₁ f₂ := sorry
lemma zsmul_tensor (n : ℤ) : tensorHom (n • f₁) f₂ = n • tensorHom f₁ f₂ := sorry

end MonoidalPreadditive

end CategoryTheory

namespace ComplexShape

variable {I : Type*} [AddMonoid I] (c : ComplexShape I)

structure TensorSigns where
  ε : I → ℤ
  rel_add (p q r : I) (hpq : c.Rel p q) : c.Rel (p + r) (q + r)
  add_rel (p q r : I) (hpq : c.Rel p q) : c.Rel (r + p) (r + q)
  ε_succ (p q : I) (hpq : c.Rel p q) : ε q = - ε p
  ε_add (p q : I) : ε (p + q) = ε p * ε q -- needed for the associator
  ε_zero : ε 0 = 1 -- should be necessary for one of the unitor

attribute [simp] TensorSigns.ε_zero

variable {c}

lemma TensorSigns.next_add (s : TensorSigns c) (p q : I) (hp : c.Rel p (c.next p)) :
    c.next (p + q) = c.next p + q :=
  c.next_eq' (s.rel_add _ _ q hp)

lemma TensorSigns.next_add' (s : TensorSigns c) (p q : I) (hq : c.Rel q (c.next q)) :
    c.next (p + q) = p + c.next q :=
  c.next_eq' (s.add_rel _ _ p hq)

@[simps]
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
  ε_add p q := by
    dsimp
    rw [pow_add]
  ε_zero := by simp

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
  ε_add := Int.negOnePow_add
  ε_zero := Int.negOnePow_zero

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

variable (K₁ K₂ : HomologicalComplex C c) [HasTensor K₁ K₂]

noncomputable def ιTensorObj (i₁ i₂ i₁₂ : I) (h : i₁ + i₂ = i₁₂) :
  K₁.X i₁ ⊗ K₂.X i₂ ⟶ (tensorObj s K₁ K₂).X i₁₂ :=
    GradedObject.Monoidal.ιTensorObj K₁.toGradedObject K₂.toGradedObject i₁ i₂ i₁₂ h

noncomputable def ιTensorObjOrZero (i₁ i₂ i₁₂ : I) :
  K₁.X i₁ ⊗ K₂.X i₂ ⟶ (tensorObj s K₁ K₂).X i₁₂ :=
  if h : i₁ + i₂ = i₁₂
    then
      ιTensorObj s K₁ K₂ i₁ i₂ i₁₂ h
    else 0

lemma ιTensorObjOrZero_eq (i₁ i₂ i₁₂ : I) (h : i₁ + i₂ = i₁₂) :
    ιTensorObjOrZero s K₁ K₂ i₁ i₂ i₁₂ = ιTensorObj s K₁ K₂ i₁ i₂ i₁₂ h := dif_pos h

lemma ιTensorObjOrZero_eq_zero (i₁ i₂ i₁₂ : I) (h : i₁ + i₂ ≠ i₁₂) :
    ιTensorObjOrZero s K₁ K₂ i₁ i₂ i₁₂ = 0 := dif_neg h

variable {K₁ K₂}

noncomputable def descTensor {A : C} {j : I}
    (f : ∀ (i₁ i₂ : I) (_ : i₁ + i₂ = j), K₁.X i₁ ⊗ K₂.X i₂ ⟶ A) :
    (tensorObj s K₁ K₂).X j ⟶ A :=
  @GradedObject.Monoidal.descTensor I _ _ _ _ K₁.toGradedObject K₂.toGradedObject _ A j f

@[reassoc (attr := simp)]
lemma ι_descTensor {A : C} (j : I) (f : ∀ (i₁ i₂ : I) (_ : i₁ + i₂ = j), K₁.X i₁ ⊗ K₂.X i₂ ⟶ A)
    (i₁ i₂ : I) (hi : i₁ + i₂ = j) :
    ιTensorObj s K₁ K₂ i₁ i₂ j hi ≫ descTensor s f = f i₁ i₂ hi := by
  apply GradedObject.Monoidal.ι_descTensor

@[ext]
lemma tensorObj_ext {K₁ K₂ : HomologicalComplex C c} {A : C} {j : I}
    [HasTensor K₁ K₂] (f g : (tensorObj s K₁ K₂).X j ⟶ A)
    (h : ∀ (i₁ i₂ : I) (hi : i₁ + i₂ = j),
      ιTensorObj s K₁ K₂ i₁ i₂ j hi ≫ f = ιTensorObj s K₁ K₂ i₁ i₂ j hi ≫ g)  : f = g :=
  GradedObject.Monoidal.tensorObj_ext _ _ h

@[reassoc]
lemma ιTensorObj_d (n m : I) (i₁ i₂ : I) (h : i₁ + i₂ = n) :
  ιTensorObj s K₁ K₂ i₁ i₂ n h ≫ (tensorObj s K₁ K₂).d n m =
    (K₁.d i₁ (c.next i₁) ⊗ 𝟙 (K₂.X i₂)) ≫ ιTensorObjOrZero _ _ _ _ _ _ +
    s.ε i₁ • (𝟙 (K₁.X i₁) ⊗ K₂.d i₂ (c.next i₂)) ≫ ιTensorObjOrZero _ _ _ _ _ _ := by
  dsimp [tensorObj, HomologicalComplex₂.total]
  erw [GradedObject.ι_descMapObj]
  rw [one_smul]
  rfl

@[reassoc]
lemma ιTensorObj_d' (n m : I) (i₁ i₂ : I) (h : i₁ + i₂ = n) (i₁' i₂' : I) (h₁ : i₁' = c.next i₁) (h₂ : i₂' = c.next i₂) :
  ιTensorObj s K₁ K₂ i₁ i₂ n h ≫ (tensorObj s K₁ K₂).d n m =
    (K₁.d i₁ i₁' ⊗ 𝟙 (K₂.X i₂)) ≫ ιTensorObjOrZero _ _ _ _ _ _ +
    s.ε i₁ • (𝟙 (K₁.X i₁) ⊗ K₂.d i₂ i₂') ≫ ιTensorObjOrZero _ _ _ _ _ _ := by
  subst h₁ h₂
  apply ιTensorObj_d

end

section

variable (K₁ K₂ K₃ : HomologicalComplex C c) [HasTensor K₂ K₃] [H : HasTensor K₁ (tensorObj s K₂ K₃)]

noncomputable def ιTensorObj₃ (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    K₁.X i₁ ⊗ K₂.X i₂ ⊗ K₃.X i₃ ⟶ (tensorObj s K₁ (tensorObj s K₂ K₃)).X j :=
  have : GradedObject.HasTensor K₁.toGradedObject (GradedObject.Monoidal.tensorObj K₂.toGradedObject K₃.toGradedObject) := H
  GradedObject.Monoidal.ιTensorObj₃ K₁.toGradedObject K₂.toGradedObject K₃.toGradedObject i₁ i₂ i₃ j h

@[reassoc]
lemma ιTensorObj₃_eq (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) (i₂₃ : I) (h' : i₂ + i₃ = i₂₃) :
    ιTensorObj₃ s K₁ K₂ K₃ i₁ i₂ i₃ j h =
      (𝟙 _ ⊗ ιTensorObj s K₂ K₃ i₂ i₃ i₂₃ h') ≫
        ιTensorObj s K₁ (tensorObj s K₂ K₃) i₁ i₂₃ j (by rw [← h', ← add_assoc, h]) :=
  have : GradedObject.HasTensor K₁.toGradedObject (GradedObject.Monoidal.tensorObj K₂.toGradedObject K₃.toGradedObject) := H
  GradedObject.Monoidal.ιTensorObj₃_eq _ _ _ _ _ _ _ h _ _

variable {K₁ K₂ K₃ s}

@[ext]
lemma tensorObj₃_ext {j : I} {A : C} (f g : (tensorObj s K₁ (tensorObj s K₂ K₃)).X j ⟶ A)
    [H₂₃ : GradedObject.HasGoodTensorTensor₂₃ K₁.X K₂.X K₃.X]
    (h : ∀ (i₁ i₂ i₃ : I) (hi : i₁ + i₂ + i₃ = j),
      ιTensorObj₃ s K₁ K₂ K₃ i₁ i₂ i₃ j hi ≫ f = ιTensorObj₃ s K₁ K₂ K₃ i₁ i₂ i₃ j hi ≫ g) : f = g := by
  have : GradedObject.HasTensor K₁.X (GradedObject.Monoidal.tensorObj K₂.X K₃.X) := H
  exact GradedObject.Monoidal.tensorObj₃_ext _ _ h

end

section

variable (K₁ K₂ K₃ : HomologicalComplex C c) [HasTensor K₁ K₂] [H : HasTensor (tensorObj s K₁ K₂) K₃]

noncomputable def ιTensorObj₃' (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    (K₁.X i₁ ⊗ K₂.X i₂) ⊗ K₃.X i₃ ⟶ (tensorObj s (tensorObj s K₁ K₂) K₃).X j :=
  have : GradedObject.HasTensor (GradedObject.Monoidal.tensorObj K₁.toGradedObject K₂.toGradedObject) K₃.toGradedObject := H
  GradedObject.Monoidal.ιTensorObj₃' K₁.toGradedObject K₂.toGradedObject K₃.toGradedObject i₁ i₂ i₃ j h

@[reassoc]
lemma ιTensorObj₃'_eq (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) (i₁₂ : I) (h' : i₁ + i₂ = i₁₂) :
    ιTensorObj₃' s K₁ K₂ K₃ i₁ i₂ i₃ j h =
      (ιTensorObj s K₁ K₂ i₁ i₂ i₁₂ h' ⊗ 𝟙 _) ≫
        ιTensorObj s (tensorObj s K₁ K₂) K₃ i₁₂ i₃ j (by rw [←h', h]) :=
  have : GradedObject.HasTensor (GradedObject.Monoidal.tensorObj K₁.toGradedObject K₂.toGradedObject) K₃.toGradedObject := H
  GradedObject.Monoidal.ιTensorObj₃'_eq _ _ _ _ _ _ _ h _ _

variable {K₁ K₂ K₃ s}

@[ext]
lemma tensorObj₃'_ext {j : I} {A : C} (f g : (tensorObj s (tensorObj s K₁ K₂) K₃).X j ⟶ A)
    [GradedObject.HasGoodTensor₁₂Tensor K₁.X K₂.X K₃.X]
    (h : ∀ (i₁ i₂ i₃ : I) (hi : i₁ + i₂ + i₃ = j),
      ιTensorObj₃' s K₁ K₂ K₃ i₁ i₂ i₃ j hi ≫ f = ιTensorObj₃' s K₁ K₂ K₃ i₁ i₂ i₃ j hi ≫ g) : f = g := by
  have : GradedObject.HasTensor (GradedObject.Monoidal.tensorObj K₁.X K₂.X) K₃.X := H
  exact GradedObject.Monoidal.tensorObj₃'_ext _ _ h

end


section

variable (K₁ K₂ K₃ : HomologicalComplex C c)
  [HasTensor K₁ K₂] [HasTensor (tensorObj s K₁ K₂) K₃]
  [HasTensor K₂ K₃] [HasTensor K₁ (tensorObj s K₂ K₃)]
  [GradedObject.HasGoodTensor₁₂Tensor K₁.X K₂.X K₃.X]
  [GradedObject.HasGoodTensorTensor₂₃ K₁.X K₂.X K₃.X]

noncomputable def associator :
    tensorObj s (tensorObj s K₁ K₂) K₃ ≅ tensorObj s K₁ (tensorObj s K₂ K₃) :=
  have : GradedObject.HasTensor (GradedObject.Monoidal.tensorObj K₁.X K₂.X) K₃.X :=
    (inferInstance : HasTensor (tensorObj s K₁ K₂) K₃)
  have : GradedObject.HasTensor K₁.X (GradedObject.Monoidal.tensorObj K₂.X K₃.X) :=
    (inferInstance : HasTensor K₁ (tensorObj s K₂ K₃))
  Hom.isoOfComponents (fun i => (GradedObject.eval i).mapIso
    (GradedObject.Monoidal.associator K₁.toGradedObject K₂.toGradedObject K₃.toGradedObject)) (by
      intro n m _
      apply GradedObject.Monoidal.tensorObj₃'_ext
      intro i₁ i₂ i₃ h
      dsimp
      rw [GradedObject.Monoidal.ιTensorObj₃'_associator_hom_assoc]
      change _ ≫ ιTensorObj₃ s K₁ K₂ K₃ i₁ i₂ i₃ n h ≫ _ =
        ιTensorObj₃' s K₁ K₂ K₃ i₁ i₂ i₃ n h ≫ _
      rw [ιTensorObj₃_eq s K₁ K₂ K₃ i₁ i₂ i₃ n h _ rfl, assoc,
        ιTensorObj₃'_eq s K₁ K₂ K₃ i₁ i₂ i₃ n h _ rfl, assoc,
        ιTensorObj_d, comp_add, comp_add, comp_zsmul, comp_zsmul,
        ← tensor_comp_assoc, id_comp, comp_id, ← tensor_comp_assoc, id_comp, ιTensorObj_d,
        tensor_add, add_comp, comp_add, smul_add, id_tensor_comp, assoc, tensor_zsmul,
        zsmul_comp, comp_zsmul, smul_smul,
        ιTensorObj_d_assoc, add_comp, assoc, comp_add]
      conv_rhs => rw [← tensor_comp_assoc, id_comp, ιTensorObj_d, add_tensor, add_comp,
        zsmul_comp, comp_zsmul, assoc, zsmul_tensor, zsmul_comp]
      rw [add_assoc]
      congr 1
      · by_cases h₁ : c.Rel i₁ (c.next i₁)
        · by_cases h₂ : c.next (i₁ + i₂) + i₃ = m
          · have h₃ : c.Rel (i₁ + i₂) (c.next (i₁ + i₂)) := by
              rw [s.next_add _ _ h₁]
              exact s.rel_add _ _ _ h₁
            have h₄ : c.next i₁ + (i₂ + i₃) = m := by
              rw [← s.next_add _ _ h₁, ← add_assoc, s.next_add _ _ h₃, h₂]
            have h₅ : c.next i₁ + i₂ + i₃ = m := by rw [← h₄, add_assoc]
            rw [ιTensorObjOrZero_eq _ _ _ _ _ _ h₂, ιTensorObjOrZero_eq _ _ _ _ _ _ h₄,
              ιTensorObjOrZero_eq _ _ _ _ _ _ (s.next_add _ _ h₁).symm, comp_tensor_id, assoc,
              ← ιTensorObj₃'_eq_assoc _ _ _ _ _ _ _ _ h₅]
            erw [GradedObject.Monoidal.ιTensorObj₃'_associator_hom]
            rw [← tensor_id_comp_id_tensor, assoc, ← ιTensorObj₃_eq  _ _ _ _ _ _ _ _ h₅,
              ← MonoidalCategory.tensor_id, ← associator_naturality_assoc]
            rfl
          · rw [ιTensorObjOrZero_eq_zero _ _ _ _ _ _ h₂, zero_comp, comp_zero]
            rw [ιTensorObjOrZero_eq_zero, comp_zero, comp_zero]
            intro h₃
            apply h₂
            rw [c.next_eq' (s.rel_add _ _ i₂ h₁), ← h₃, add_assoc]
        · dsimp
          rw [K₁.shape _ _ h₁, zero_tensor, zero_tensor, zero_comp, comp_zero, zero_comp,
            zero_tensor, zero_comp]
      · congr 2
        · by_cases h₁ : c.Rel i₂ (c.next i₂)
          · rw [ιTensorObjOrZero_eq _ _ _ _ _ _ (s.next_add i₂ i₃ h₁).symm]
            by_cases h₂ : i₁ + c.next (i₂ + i₃) = m
            · have h₃ : i₁ + c.next i₂ + i₃ = m := by rw [add_assoc, ← s.next_add _ _ h₁, h₂]
              have h₄ : c.next (i₁ + i₂) + i₃ = m := by rw [← h₃, s.next_add' _ _ h₁]
              rw [ιTensorObjOrZero_eq _ _ _ _ _ _ h₂,
                ιTensorObjOrZero_eq _ _ _ _ _ _ (s.next_add' i₁ i₂ h₁).symm,
                ιTensorObjOrZero_eq _ _ _ _ _ _ h₄, comp_tensor_id, assoc]
              rw [← ιTensorObj₃'_eq_assoc _ _ _ _ _ _ _ _ h₃]
              erw [GradedObject.Monoidal.ιTensorObj₃'_associator_hom]
              rw [← associator_naturality_assoc, ← ιTensorObj₃_eq _ _ _ _ _ _ _ _ h₃]
              rfl
            · rw [ιTensorObjOrZero_eq_zero _ _ _ _ _ _ h₂, comp_zero, comp_zero, comp_zero]
              have : c.next (i₁ + i₂) + i₃ ≠ m := by
                rw [s.next_add' i₁ i₂ h₁, add_assoc, ← s.next_add i₂ i₃ h₁]
                exact h₂
              rw [ιTensorObjOrZero_eq_zero _ _ _ _ _ _ this, zero_comp, comp_zero]
          · rw [K₂.shape _ _ h₁, tensor_zero, zero_tensor, tensor_zero, zero_comp, comp_zero,
              zero_comp, zero_tensor, zero_comp]
        · rw [s.ε_add]
        · by_cases h₁ : c.Rel i₃ (c.next i₃)
          · rw [ιTensorObjOrZero_eq _ _ _ _ _ _ (s.next_add' i₂ i₃ h₁).symm]
            by_cases h₂ : i₁ + c.next (i₂ + i₃) = m
            · have h₃ : i₁ + i₂ + c.next i₃ = m := by rw [add_assoc, ← s.next_add' _ _ h₁, h₂]
              rw [ιTensorObjOrZero_eq _ _ _ _ _ _ h₂,
                ιTensorObjOrZero_eq _ _ _ _ _ _ h₃,
                tensor_id_comp_id_tensor_assoc]
              conv_rhs => rw [← id_tensor_comp_tensor_id, assoc,
                ← ιTensorObj₃'_eq_assoc _ _ _ _ _ _ _ _ h₃]
              erw [GradedObject.Monoidal.ιTensorObj₃'_associator_hom]
              rw [id_tensor_comp, assoc, ← ιTensorObj₃_eq _ _ _ _ _ _ _ _ h₃]
              rw [← associator_naturality_assoc, MonoidalCategory.tensor_id]
              rfl
            · rw [ιTensorObjOrZero_eq_zero _ _ _ _ _ _ h₂, comp_zero, comp_zero,
                ιTensorObjOrZero_eq_zero, zero_comp, comp_zero, comp_zero]
              intro h₃
              apply h₂
              rw [s.next_add' _ _ h₁, ← h₃, add_assoc]
          · rw [K₃.shape _ _ h₁, tensor_zero, tensor_zero,
              zero_comp, zero_comp, tensor_zero, zero_comp, comp_zero,
              comp_zero])

end

section

variable [HasZeroObject C]
variable [∀ (X₁ : C), PreservesColimit (Functor.empty C) ((curryObj (tensor C)).obj X₁)]
variable [∀ (X₂ : C), PreservesColimit (Functor.empty C) ((Functor.flip (curryObj (tensor C))).obj X₂)]

-- we could consider using the `single` functor instead, but the compatibilities
-- would be slightly more difficult to get
noncomputable def tensorUnit :
    HomologicalComplex C c :=
  HomologicalComplex.ofGradedObject GradedObject.Monoidal.tensorUnit c
    (fun _ _ => 0) (fun _ _ _ => rfl) (by aesop_cat)

@[simp]
lemma tensorUnit_d (n m : I) : (tensorUnit : HomologicalComplex C c).d n m = 0 := rfl

variable (K : HomologicalComplex C c)

instance : HasTensor tensorUnit K := by
  change GradedObject.HasTensor GradedObject.Monoidal.tensorUnit _
  infer_instance

noncomputable def leftUnitor : tensorObj s tensorUnit K ≅ K :=
  Iso.symm
    (Hom.isoOfComponents
      (fun n => (GradedObject.eval n).mapIso
        (GradedObject.Monoidal.leftUnitor K.toGradedObject).symm) (fun n m hnm => by
      dsimp
      by_cases hnm : c.Rel n m
      . obtain rfl := c.next_eq' hnm
        rw [GradedObject.Monoidal.leftUnitor_inv_apply, assoc, assoc]
        change _ ≫ _ ≫ ιTensorObj s tensorUnit K 0 n n (zero_add n) ≫ _ = _
        rw [ιTensorObj_d, tensorUnit_d, zero_tensor, zero_comp, zero_add,
          s.ε_zero, comp_zsmul, one_smul, ιTensorObjOrZero_eq _ _ _ _ _ _ (zero_add _),
          GradedObject.Monoidal.leftUnitor_inv_apply,
          leftUnitor_inv_naturality_assoc,
          id_tensor_comp_tensor_id_assoc]
        erw [tensor_id_comp_id_tensor_assoc]
        rfl
      · rw [HomologicalComplex.shape _ _ _ hnm, K.shape _ _ hnm, comp_zero, zero_comp]))

instance : HasTensor K tensorUnit := by
  change GradedObject.HasTensor _ GradedObject.Monoidal.tensorUnit
  infer_instance

noncomputable def rightUnitor : tensorObj s K tensorUnit ≅ K :=
  Iso.symm
    (Hom.isoOfComponents
      (fun n => (GradedObject.eval n).mapIso
        (GradedObject.Monoidal.rightUnitor K.toGradedObject).symm) (fun n m hnm => by
      dsimp
      by_cases hnm : c.Rel n m
      . obtain rfl := c.next_eq' hnm
        rw [GradedObject.Monoidal.rightUnitor_inv_apply, assoc, assoc]
        change _ ≫ _ ≫ ιTensorObj s K tensorUnit n 0 n (add_zero n) ≫ _ = _
        rw [ιTensorObj_d, tensorUnit_d, tensor_zero, zero_comp, smul_zero, add_zero,
          ιTensorObjOrZero_eq _ _ _ _ _ _ (add_zero _),
          GradedObject.Monoidal.rightUnitor_inv_apply,
          rightUnitor_inv_naturality_assoc, tensor_id_comp_id_tensor_assoc]
        erw [id_tensor_comp_tensor_id_assoc]
        rfl
      · rw [HomologicalComplex.shape _ _ _ hnm, K.shape _ _ hnm, comp_zero, zero_comp]))

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
