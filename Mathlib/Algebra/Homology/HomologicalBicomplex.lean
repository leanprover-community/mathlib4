import Mathlib.CategoryTheory.GradedObject.Bifunctor
import Mathlib.Algebra.Homology.Flip
import Mathlib.Algebra.GroupPower.NegOnePow
import Mathlib.Tactic.Linarith

open CategoryTheory Category Limits Preadditive

variable {C D C₁ C₂ C₃ : Type*} [Category C] [Category D]
  [Category C₁] [Category C₂] [Category C₃]
  (F G : C₁ ⥤ C₂ ⥤ C₃) (τ : F ⟶ G) (e : F ≅ G)
  {I₁ I₂ I₃ : Type*} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)

namespace HomologicalComplex

variable [HasZeroMorphisms C] {I : Type*} {c : ComplexShape I}

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

lemma toGradedObjectFunctor_map_injective {K L : HomologicalComplex C c} (f g : K ⟶ L)
    (h : f.f = g.f) :
    f = g :=
  (toGradedObjectFunctor C c).map_injective h

end HomologicalComplex

namespace CategoryTheory.GradedObject

variable [HasZeroMorphisms C] {I J : Type*} (X : GradedObject I C) (p : I → J) [X.HasMap p]
  (i : I) (j : J) [DecidableEq J]

noncomputable def ιMapObjOrZero : X i ⟶ X.mapObj p j :=
  if h : p i = j
    then X.ιMapObj p i j h
    else 0

lemma ιMapObjOrZero_eq (h : p i = j) : X.ιMapObjOrZero p i j = X.ιMapObj p i j h := dif_pos h

lemma ιMapObjOrZero_eq_zero (h : p i ≠ j) : X.ιMapObjOrZero p i j = 0 := dif_neg h

end CategoryTheory.GradedObject

@[simps]
def HomologicalComplex.ofGradedObject [HasZeroMorphisms C] {I : Type*} (X : GradedObject I C) (c : ComplexShape I)
    (d : ∀ (i j : I), X i ⟶ X j) (shape : ∀ (i j : I), ¬ c.Rel i j → d i j = 0)
    (d_comp_d' : ∀ (i j k : I), c.Rel i j → c.Rel j k → d i j ≫ d j k = 0) :
    HomologicalComplex C c where
  X := X
  d := d
  shape := shape
  d_comp_d' := d_comp_d'

-- let `c₁` correspond to the horizontal differential
-- let `c₂` correspond to the vertical differential
-- `(K.X p).X q` is in position (p, q)

variable (C)

abbrev HomologicalComplex₂ [HasZeroMorphisms C] := HomologicalComplex (HomologicalComplex C c₂) c₁

variable {C}

@[simps]
def HomologicalComplex₂.ofGradedObject [HasZeroMorphisms C] (X : GradedObject (I₁ × I₂) C)
    (d₁ : ∀ (i₁ i₁' : I₁) (i₂ : I₂), X ⟨i₁, i₂⟩ ⟶ X ⟨i₁', i₂⟩)
    (d₂ : ∀ (i₁ : I₁) (i₂ i₂' : I₂), X ⟨i₁, i₂⟩ ⟶ X ⟨i₁, i₂'⟩)
    (shape₁ : ∀ (i₁ i₁' : I₁) (_ : ¬c₁.Rel i₁ i₁') (i₂ : I₂), d₁ i₁ i₁' i₂ = 0)
    (shape₂ : ∀ (i₁ : I₁) (i₂ i₂' : I₂) (_ : ¬c₂.Rel i₂ i₂'), d₂ i₁ i₂ i₂' = 0)
    (d_comp_d₁ : ∀ (i₁ i₁' i₁'' : I₁) (i₂ : I₂), d₁ i₁ i₁' i₂ ≫ d₁ i₁' i₁'' i₂ = 0)
    (d_comp_d₂ : ∀ (i₁ : I₁) (i₂ i₂' i₂'' : I₂), d₂ i₁ i₂ i₂' ≫ d₂ i₁ i₂' i₂'' = 0)
    (comm : ∀ (i₁ i₁' : I₁) (i₂ i₂' : I₂), d₁ i₁ i₁' i₂ ≫ d₂ i₁' i₂ i₂' = d₂ i₁ i₂ i₂' ≫ d₁ i₁ i₁' i₂') :
    HomologicalComplex₂ C c₁ c₂ where
  X i₁ :=
    { X := fun i₂ => X ⟨i₁, i₂⟩
      d := fun i₂ i₂' => d₂ i₁ i₂ i₂'
      shape := shape₂ i₁
      d_comp_d' := by intros; apply d_comp_d₂ }
  d i₁ i₁' :=
    { f := fun i₂ => d₁ i₁ i₁' i₂
      comm' := by intros; apply comm }
  shape i₁ i₁' h := by
    ext i₂
    exact shape₁ i₁ i₁' h i₂
  d_comp_d' i₁ i₁' i₁'' _ _ := by ext i₂; apply d_comp_d₁

namespace CategoryTheory

namespace Functor

variable [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [HasZeroMorphisms C₃]

variable {c₁ c₂}

@[simps!]
def mapHomologicalComplex₂ObjObj [F.PreservesZeroMorphisms] [∀ (X : C₁), (F.obj X).PreservesZeroMorphisms]
    (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂) : HomologicalComplex₂ C₃ c₁ c₂ :=
  HomologicalComplex₂.ofGradedObject c₁ c₂ (((GradedObject.mapBifunctor F I₁ I₂).obj K₁.X).obj K₂.X)
    (fun i₁ i₁' i₂ => (F.map (K₁.d i₁ i₁')).app (K₂.X i₂))
    (fun i₁ i₂ i₂' => (F.obj (K₁.X i₁)).map (K₂.d i₂ i₂'))
    (fun i₁ i₁' h₁ i₂ => by
      dsimp
      rw [K₁.shape _ _ h₁, Functor.map_zero, zero_app])
    (fun i₁ i₂ i₂' h₂ => by
      dsimp
      rw [K₂.shape _ _ h₂, Functor.map_zero])
    (fun i₁ i₁' i₁' i₂ => by
      dsimp
      rw [← NatTrans.comp_app, ← F.map_comp, K₁.d_comp_d, Functor.map_zero, zero_app])
    (fun i₁ i₂ i₂' i₂'' => by
      dsimp
      rw [← Functor.map_comp, K₂.d_comp_d, Functor.map_zero])
    (fun i₁ i₁' i₂ i₂' => by
      dsimp
      rw [NatTrans.naturality])

variable (c₂)

@[simps]
def mapHomologicalComplex₂Obj [F.PreservesZeroMorphisms] [∀ (X : C₁), (F.obj X).PreservesZeroMorphisms] (K₁ : HomologicalComplex C₁ c₁) :
    HomologicalComplex C₂ c₂ ⥤ HomologicalComplex₂ C₃ c₁ c₂ where
  obj K₂ := mapHomologicalComplex₂ObjObj F K₁ K₂
  map {K₂ L₂} φ :=
    { f := fun i₁ =>
        { f := fun i₂ => ((GradedObject.mapBifunctor F I₁ I₂).obj K₁.X).map φ.f ⟨i₁, i₂⟩
          comm' := fun i₂ i₂' _ => by
            dsimp
            rw [← Functor.map_comp, ← Functor.map_comp, φ.comm] }
      comm' := fun i₁ i₁' _ => by
        ext
        dsimp
        rw [NatTrans.naturality] }
  map_id K₂ := by
    ext i₁ i₂
    dsimp
    rw [Functor.map_id]
  map_comp φ φ' := by
    ext i₁ i₂
    dsimp
    rw [Functor.map_comp]

variable (c₁)

set_option maxHeartbeats 400000 in
@[simps]
def mapHomologicalComplex₂ [F.PreservesZeroMorphisms] [∀ (X : C₁), (F.obj X).PreservesZeroMorphisms] : HomologicalComplex C₁ c₁ ⥤ HomologicalComplex C₂ c₂ ⥤
    HomologicalComplex₂ C₃ c₁ c₂ where
  obj K₁ := mapHomologicalComplex₂Obj F c₂ K₁
  map {K₁ L₁} φ :=
    { app := fun K₂ =>
        { f := fun i₁ =>
          { f := fun i₂ => ((GradedObject.mapBifunctor F I₁ I₂).map φ.f).app K₂.X ⟨i₁, i₂⟩
            comm' := fun i₂ i₂' _ => by
              dsimp
              rw [NatTrans.naturality] }
          comm' := fun i₁ i₁' _ => by
            ext i₂
            dsimp
            rw [← NatTrans.comp_app, ← NatTrans.comp_app,
              ← Functor.map_comp, ← Functor.map_comp, φ.comm] } }

end Functor

end CategoryTheory

section

variable (c₃ : ComplexShape I₃)

class TotalComplexShape  where
  π : I₁ × I₂ → I₃
  ε₁ : I₁ × I₂ → ℤ
  ε₂ : I₁ × I₂ → ℤ
  rel₁ ⦃i₁ i₁' : I₁⦄ (h : c₁.Rel i₁ i₁') (i₂ : I₂) : c₃.Rel (π ⟨i₁, i₂⟩) (π ⟨i₁', i₂⟩)
  rel₂ (i₁ : I₁) ⦃i₂ i₂' : I₂⦄ (h : c₂.Rel i₂ i₂') : c₃.Rel (π ⟨i₁, i₂⟩) (π ⟨i₁, i₂'⟩)
  eq ⦃i₁ i₁' : I₁⦄ ⦃i₂ i₂' : I₂⦄ (h₁ : c₁.Rel i₁ i₁') (h₂ : c₂.Rel i₂ i₂') :
    ε₁ ⟨i₁, i₂⟩ * ε₂ ⟨i₁', i₂⟩ + ε₂ ⟨i₁, i₂⟩ * ε₁ ⟨i₁, i₂'⟩ = 0

variable [TotalComplexShape c₁ c₂ c₃]

namespace ComplexShape

abbrev π (i : I₁ × I₂) : I₃ := TotalComplexShape.π c₁ c₂ c₃ i
abbrev ε₁ (i : I₁ × I₂) : ℤ := TotalComplexShape.ε₁ c₁ c₂ c₃ i
abbrev ε₂ (i : I₁ × I₂) : ℤ := TotalComplexShape.ε₂ c₁ c₂ c₃ i

variable {c₁}

lemma rel_π₁ {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) : c₃.Rel (π c₁ c₂ c₃ ⟨i₁, i₂⟩) (π c₁ c₂ c₃ ⟨i₁', i₂⟩) :=
  TotalComplexShape.rel₁ h i₂

variable (c₁) {c₂}

lemma rel_π₂ (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') : c₃.Rel (π c₁ c₂ c₃ ⟨i₁, i₂⟩) (π c₁ c₂ c₃ ⟨i₁, i₂'⟩) :=
  TotalComplexShape.rel₂ i₁ h

variable {c₁}

lemma totalComplexShape_compatibility
    {i₁ i₁' : I₁} {i₂ i₂' : I₂} (h₁ : c₁.Rel i₁ i₁') (h₂ : c₂.Rel i₂ i₂') :
    ε₁ c₁ c₂ c₃ ⟨i₁, i₂⟩ * ε₂ c₁ c₂ c₃ ⟨i₁', i₂⟩ + ε₂ c₁ c₂ c₃ ⟨i₁, i₂⟩ * ε₁ c₁ c₂ c₃ ⟨i₁, i₂'⟩ = 0 :=
  TotalComplexShape.eq h₁ h₂

end ComplexShape

end

namespace HomologicalComplex₂

variable {c₁ c₂}

@[pp_dot, simps!]
def flip [HasZeroMorphisms C] (K : HomologicalComplex₂ C c₁ c₂) :
  HomologicalComplex₂ C c₂ c₁ := HomologicalComplex.flipObj K

@[pp_dot]
def toGradedObject [HasZeroMorphisms C] (K : HomologicalComplex₂ C c₁ c₂) :
  GradedObject (I₁ × I₂) C := fun ⟨i₁, i₂⟩ => (K.X i₁).X i₂

variable (c₁ c₂ C)

def flipFunctor [HasZeroMorphisms C]:
    HomologicalComplex₂ C c₁ c₂ ⥤ HomologicalComplex₂ C c₂ c₁ := HomologicalComplex.flip C c₂ c₁

@[reducible]
def toGradedObjectFunctor [HasZeroMorphisms C] :
    HomologicalComplex₂ C c₁ c₂ ⥤ GradedObject (I₁ × I₂) C where
  obj := toGradedObject
  map φ := fun ⟨i₁, i₂⟩ => (φ.f i₁).f i₂

variable {c₁ c₂ C}
variable [Preadditive C] (K L M : HomologicalComplex₂ C c₁ c₂) (φ : K ⟶ L) (ψ : L ⟶ M) (e : K ≅ L)
  (c₃ : ComplexShape I₃) [DecidableEq I₃]

variable [TotalComplexShape c₁ c₂ c₃] [K.toGradedObject.HasMap (ComplexShape.π c₁ c₂ c₃)]
  [L.toGradedObject.HasMap (ComplexShape.π c₁ c₂ c₃)] [M.toGradedObject.HasMap (ComplexShape.π c₁ c₂ c₃)]

attribute [reassoc] HomologicalComplex.comp_f

@[pp_dot]
noncomputable def total : HomologicalComplex C c₃ :=
  HomologicalComplex.ofGradedObject (K.toGradedObject.mapObj (ComplexShape.π c₁ c₂ c₃)) c₃
    (fun i₃ i₃' => GradedObject.descMapObj _ (ComplexShape.π c₁ c₂ c₃)
      (fun ⟨i₁, i₂⟩ _ => ComplexShape.ε₁ c₁ c₂ c₃ ⟨i₁, i₂⟩ • ((K.d i₁ (c₁.next i₁)).f i₂ ≫ K.toGradedObject.ιMapObjOrZero (ComplexShape.π c₁ c₂ c₃) ⟨_, i₂⟩ i₃') +
        ComplexShape.ε₂ c₁ c₂ c₃ ⟨i₁, i₂⟩ • ((K.X i₁).d i₂ (c₂.next i₂) ≫ K.toGradedObject.ιMapObjOrZero (ComplexShape.π c₁ c₂ c₃) ⟨i₁, _⟩ i₃')))
    (fun i₃ i₃' h₃ => by
      ext ⟨i₁, i₂⟩ h₀
      dsimp
      simp only [Prod.mk.eta, GradedObject.ι_descMapObj, comp_zero]
      conv_rhs => rw [← add_zero 0]
      congr 1
      · by_cases h₁ : (ComplexShape.π c₁ c₂ c₃) ⟨c₁.next i₁, i₂⟩ = i₃'
        · rw [K.shape, HomologicalComplex.zero_f, zero_comp, smul_zero]
          intro h₂
          apply h₃
          rw [← h₀, ← h₁]
          apply ComplexShape.rel_π₁
          exact h₂
        · rw [GradedObject.ιMapObjOrZero_eq_zero _ _ _ _ h₁, comp_zero, smul_zero]
      · by_cases h₁ : (ComplexShape.π c₁ c₂ c₃) ⟨i₁, c₂.next i₂⟩ = i₃'
        · rw [(K.X i₁).shape, zero_comp, smul_zero]
          intro h₂
          apply h₃
          rw [← h₀, ← h₁]
          apply ComplexShape.rel_π₂
          exact h₂
        · rw [GradedObject.ιMapObjOrZero_eq_zero _ _ _ _ h₁, comp_zero, smul_zero])
    (fun i₃ i₃' i₃'' _ _ => by
      ext ⟨i₁, i₂⟩ h₀
      dsimp
      rw [GradedObject.ι_descMapObj_assoc, add_comp, comp_zero, zsmul_comp,
        zsmul_comp, assoc, assoc]
      dsimp
      by_cases h₁ : (ComplexShape.π c₁ c₂ c₃) (c₁.next i₁, i₂) = i₃'
      · rw [GradedObject.ιMapObjOrZero_eq _ _ _ _ h₁, GradedObject.ι_descMapObj,
          comp_add]
        simp only [comp_zsmul, ← HomologicalComplex.comp_f_assoc, HomologicalComplex.d_comp_d,
          HomologicalComplex.zero_f, zero_comp, zsmul_zero, zero_add]
        by_cases h₂ : (ComplexShape.π c₁ c₂ c₃) (i₁, c₂.next i₂) = i₃'
        · dsimp
          rw [GradedObject.ιMapObjOrZero_eq _ _ _ _ h₂, GradedObject.ι_descMapObj,
            comp_add, comp_zsmul, comp_zsmul, HomologicalComplex.d_comp_d_assoc, zero_comp,
            smul_zero, add_zero, smul_smul, smul_smul,
            HomologicalComplex.Hom.comm_assoc, ← add_smul]
          dsimp
          by_cases h₃ : c₂.Rel i₂ (c₂.next i₂)
          · by_cases h₄ : c₁.Rel i₁ (c₁.next i₁)
            · rw [ComplexShape.totalComplexShape_compatibility c₃ h₄ h₃, zero_smul]
            · rw [K.shape _ _ h₄, HomologicalComplex.zero_f, zero_comp, comp_zero, smul_zero]
          · rw [(K.X i₁).shape _ _ h₃, zero_comp, smul_zero]
        · rw [GradedObject.ιMapObjOrZero_eq_zero _ _ _ _ h₂, zero_comp, comp_zero,
            smul_zero, add_zero]
          by_cases h₃ : c₂.Rel i₂ (c₂.next i₂)
          · by_cases h₄ : c₁.Rel i₁ (c₁.next i₁)
            · exfalso
              apply h₂
              simpa only [c₃.next_eq' (ComplexShape.rel_π₁ c₂ c₃ h₄ i₂), ← c₃.next_eq' (ComplexShape.rel_π₂ c₁ c₃ i₁ h₃)]
                using h₁
            · rw [HomologicalComplex.shape _ _ _ h₄, HomologicalComplex.zero_f, zero_comp,
                smul_zero, smul_zero]
          · rw [HomologicalComplex.shape _ _ _ h₃, zero_comp, comp_zero, smul_zero, smul_zero]
      · rw [GradedObject.ιMapObjOrZero_eq_zero _ _ _ _ h₁, zero_comp, comp_zero, smul_zero,
          zero_add]
        by_cases h₂ : (ComplexShape.π c₁ c₂ c₃) (i₁, c₂.next i₂) = i₃'
        · rw [GradedObject.ιMapObjOrZero_eq _ _ _ _ h₂, GradedObject.ι_descMapObj,
            comp_add, comp_zsmul, comp_zsmul, HomologicalComplex.d_comp_d_assoc, zero_comp,
            smul_zero, add_zero]
          dsimp
          by_cases h₃ : c₂.Rel i₂ (c₂.next i₂)
          · by_cases h₄ : c₁.Rel i₁ (c₁.next i₁)
            · exfalso
              apply h₁
              simpa only [c₃.next_eq' (ComplexShape.rel_π₁ c₂ c₃ h₄ i₂), ← c₃.next_eq' (ComplexShape.rel_π₂ c₁ c₃ i₁ h₃)]
                using h₂
            · rw [HomologicalComplex.shape _ _ _ h₄, HomologicalComplex.zero_f,
                zero_comp, comp_zero, smul_zero, smul_zero]
          · rw [HomologicalComplex.shape _ _ _ h₃, zero_comp, smul_zero, smul_zero]
        · rw [GradedObject.ιMapObjOrZero_eq_zero _ _ _ _ h₂, zero_comp, comp_zero, smul_zero])

noncomputable def ιTotal (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (h : (ComplexShape.π c₁ c₂ c₃) ⟨i₁, i₂⟩ = i₃) :
    (K.X i₁).X i₂ ⟶ (K.total c₃).X i₃ :=
  K.toGradedObject.ιMapObj (ComplexShape.π c₁ c₂ c₃) ⟨i₁, i₂⟩ i₃ h

noncomputable def descTotal {A : C} {i₃ : I₃} (f : ∀ (i₁ : I₁) (i₂ : I₂) (_ : (ComplexShape.π c₁ c₂ c₃) ⟨i₁, i₂⟩ = i₃), (K.X i₁).X i₂ ⟶ A) :
    (K.total c₃).X i₃ ⟶ A :=
  K.toGradedObject.descMapObj (ComplexShape.π c₁ c₂ c₃) (fun ⟨i₁, i₂⟩ h => f i₁ i₂ h)

@[reassoc (attr := simp)]
lemma ι_descTotal {A : C} (i₃ : I₃) (f : ∀ (i₁ : I₁) (i₂ : I₂) (_ : (ComplexShape.π c₁ c₂ c₃) ⟨i₁, i₂⟩ = i₃), (K.X i₁).X i₂ ⟶ A)
    (i₁ : I₁) (i₂ : I₂) (h : (ComplexShape.π c₁ c₂ c₃) ⟨i₁, i₂⟩ = i₃) :
      K.ιTotal c₃ i₁ i₂ i₃ h ≫ K.descTotal c₃ f = f i₁ i₂ h := by
  apply K.toGradedObject.ι_descMapObj

variable {K c₃}

@[ext]
lemma descTotal_ext {A : C} {i₃ : I₃} (f g : (K.total c₃).X i₃ ⟶ A)
    (h : ∀ (i₁ : I₁) (i₂ : I₂) (h : (ComplexShape.π c₁ c₂ c₃) ⟨i₁, i₂⟩ = i₃), K.ιTotal c₃ i₁ i₂ i₃ h ≫ f = K.ιTotal c₃ i₁ i₂ i₃ h ≫ g) : f = g :=
  GradedObject.mapObj_ext _ _ _ _ (fun ⟨i₁, i₂⟩ hi => h i₁ i₂ hi)

variable (K c₃)

noncomputable def ιTotalOrZero (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) :
    (K.X i₁).X i₂ ⟶ (K.total c₃).X i₃ :=
  if h : (ComplexShape.π c₁ c₂ c₃) ⟨i₁, i₂⟩ = i₃
    then K.toGradedObject.ιMapObj (ComplexShape.π c₁ c₂ c₃) ⟨i₁, i₂⟩ i₃ h
    else 0

lemma ιTotalOrZero_eq (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (h : (ComplexShape.π c₁ c₂ c₃) ⟨i₁, i₂⟩ = i₃):
  K.ιTotalOrZero c₃ i₁ i₂ i₃ = K.ιTotal c₃ i₁ i₂ i₃ h := dif_pos h

lemma ιTotalOrZero_eq_zero (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (h : (ComplexShape.π c₁ c₂ c₃) ⟨i₁, i₂⟩ ≠ i₃):
  K.ιTotalOrZero c₃ i₁ i₂ i₃ = 0 := dif_neg h

@[reassoc]
lemma ιTotal_d (i₁ : I₁) (i₂ : I₂) (i₃ i₃' : I₃) (h : (ComplexShape.π c₁ c₂ c₃) ⟨i₁, i₂⟩ = i₃) :
    K.ιTotal c₃ i₁ i₂ i₃ h ≫ (K.total c₃).d i₃ i₃' =
      ComplexShape.ε₁ c₁ c₂ c₃ ⟨i₁, i₂⟩ • ((K.d i₁ (c₁.next i₁)).f i₂) ≫ K.ιTotalOrZero c₃ _ _ _ +
        ComplexShape.ε₂ c₁ c₂ c₃ ⟨i₁, i₂⟩ • ((K.X i₁).d i₂ (c₂.next i₂) ≫ K.ιTotalOrZero c₃ _ _ _) := by
  dsimp [total, ιTotal]
  apply GradedObject.ι_descMapObj

variable {K L}

@[simps]
noncomputable def totalMap : K.total c₃ ⟶ L.total c₃ where
  f := GradedObject.mapMap ((toGradedObjectFunctor C c₁ c₂).map φ) (ComplexShape.π c₁ c₂ c₃)
  comm' i₃ i₃' _ := by
    apply GradedObject.mapObj_ext
    rintro ⟨i₁, i₂⟩ h
    dsimp [total]
    simp only [GradedObject.ι_mapMap_assoc, GradedObject.ι_descMapObj, comp_add, comp_zsmul,
      GradedObject.ι_descMapObj_assoc, add_comp, zsmul_comp, assoc]
    congr 2
    · by_cases (ComplexShape.π c₁ c₂ c₃) (c₁.next i₁, i₂) = i₃'
      · simp only [GradedObject.ιMapObjOrZero_eq _ _ _ _ h, GradedObject.ι_mapMap,
          ← HomologicalComplex.comp_f_assoc, φ.comm]
      · simp only [GradedObject.ιMapObjOrZero_eq_zero _ _ _ _ h, comp_zero, zero_comp]
    · by_cases (ComplexShape.π c₁ c₂ c₃) (i₁, c₂.next i₂) = i₃'
      · simp only [GradedObject.ιMapObjOrZero_eq _ _ _ _ h, GradedObject.ι_mapMap,
          HomologicalComplex.Hom.comm_from_assoc]
      · simp only [GradedObject.ιMapObjOrZero_eq_zero _ _ _ _ h, comp_zero, zero_comp]

variable (K)

@[simp]
lemma totalMap_id : totalMap (𝟙 K) c₃ = 𝟙 _ := by
  apply (HomologicalComplex.toGradedObjectFunctor _ _).map_injective
  apply GradedObject.mapMap_id

variable {K M}

@[simp, reassoc]
lemma totalMap_comp : totalMap (φ ≫ ψ) c₃ = totalMap φ c₃ ≫ totalMap ψ c₃ := by
  apply (HomologicalComplex.toGradedObjectFunctor _ _).map_injective
  exact GradedObject.mapMap_comp ((HomologicalComplex₂.toGradedObjectFunctor C c₁ c₂).map φ)
    ((HomologicalComplex₂.toGradedObjectFunctor C c₁ c₂).map ψ) (ComplexShape.π c₁ c₂ c₃)

@[simps]
noncomputable def totalMapIso : K.total c₃ ≅ L.total c₃ where
  hom := totalMap e.hom c₃
  inv := totalMap e.inv c₃
  hom_inv_id := by rw [← totalMap_comp, e.hom_inv_id, totalMap_id]
  inv_hom_id := by rw [← totalMap_comp, e.inv_hom_id, totalMap_id]

end HomologicalComplex₂

namespace TotalComplexShape

variable {c₁ c₂} (c₃ : ComplexShape I₃)

variable [TotalComplexShape c₁ c₂ c₃] [DecidableEq I₃]

@[simps]
noncomputable def totalFunctor (C : Type*) [Category C] [Preadditive C]
    [∀ (K : HomologicalComplex₂ C c₁ c₂), K.toGradedObject.HasMap (ComplexShape.π c₁ c₂ c₃)] :
    HomologicalComplex₂ C c₁ c₂ ⥤ HomologicalComplex C c₃ where
  obj K := K.total c₃
  map φ := HomologicalComplex₂.totalMap φ c₃

end TotalComplexShape

namespace CategoryTheory

namespace Functor

variable [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [HasZeroMorphisms C₃]
  [F.PreservesZeroMorphisms] [∀ (X : C₁), (F.obj X).PreservesZeroMorphisms]
  [F.flip.PreservesZeroMorphisms] [∀ (X : C₂), (F.flip.obj X).PreservesZeroMorphisms]

variable {c₁ c₂}

@[simps!]
def mapHomologicalComplex₂FlipObjObjIso (K₁ : HomologicalComplex C₁ c₁)
  (K₂ : HomologicalComplex C₂ c₂) :
    ((mapHomologicalComplex₂ F c₁ c₂).obj K₁).obj K₂ ≅
      (((mapHomologicalComplex₂ F.flip c₂ c₁).obj K₂).obj K₁).flip :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i₂ => HomologicalComplex.Hom.isoOfComponents (fun i₁ => Iso.refl _ )
      (by aesop_cat)) (by aesop_cat)

variable (c₁ c₂)

@[simps!]
def mapHomologicalComplex₂FlipIso :
    mapHomologicalComplex₂ F c₁ c₂ ≅
      (mapHomologicalComplex₂ F.flip c₂ c₁).flip ⋙
      (whiskeringRight _ _ _).obj (HomologicalComplex₂.flipFunctor C₃ c₂ c₁) :=
  NatIso.ofComponents
    (fun K₁ => NatIso.ofComponents
      (fun K₂ => mapHomologicalComplex₂FlipObjObjIso F K₁ K₂)
        (by aesop_cat)) (by aesop_cat)

end Functor

variable {F G}

namespace NatTrans

variable [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [HasZeroMorphisms C₃]
  [F.PreservesZeroMorphisms] [∀ (X : C₁), (F.obj X).PreservesZeroMorphisms]
  [G.PreservesZeroMorphisms] [∀ (X : C₁), (G.obj X).PreservesZeroMorphisms]

@[simps]
def mapHomologicalComplex₂ : F.mapHomologicalComplex₂ c₁ c₂ ⟶ G.mapHomologicalComplex₂ c₁ c₂ where
  app K₁ :=
    { app := fun K₂ =>
        { f := fun i₁ =>
            { f := fun i₂ => (τ.app _).app _ }
          comm' := fun i₁ i₁' _ => by
            ext i₂
            dsimp
            simp only [← NatTrans.comp_app, NatTrans.naturality] } }
  naturality K₁ L₁ f := by
    ext K₂ i₁ i₂
    dsimp
    simp only [← NatTrans.comp_app, NatTrans.naturality]


end NatTrans

namespace NatIso

variable [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [HasZeroMorphisms C₃]
  [F.PreservesZeroMorphisms] [∀ (X : C₁), (F.obj X).PreservesZeroMorphisms]
  [G.PreservesZeroMorphisms] [∀ (X : C₁), (G.obj X).PreservesZeroMorphisms]

@[simps]
def mapHomologicalComplex₂ :
    F.mapHomologicalComplex₂ c₁ c₂ ≅ G.mapHomologicalComplex₂ c₁ c₂ where
  hom := NatTrans.mapHomologicalComplex₂ e.hom c₁ c₂
  inv := NatTrans.mapHomologicalComplex₂ e.inv c₁ c₂
  hom_inv_id := by
    ext K₁ K₂ i₁ i₂
    dsimp
    rw [← NatTrans.comp_app, e.hom_inv_id_app, NatTrans.id_app]
  inv_hom_id := by
    ext K₁ K₂ i₁ i₂
    dsimp
    rw [← NatTrans.comp_app, e.inv_hom_id_app, NatTrans.id_app]

end NatIso

end CategoryTheory

variable (c₃ : ComplexShape I₃) [TotalComplexShape c₁ c₂ c₃] [TotalComplexShape c₂ c₁ c₃]

class TotalComplexShapeSymmetry where --(τ : TotalComplexShape c₁ c₂ c₃) (τ' : TotalComplexShape c₂ c₁ c₃) where
  symm (i₁ : I₁) (i₂ : I₂) : ComplexShape.π c₂ c₁ c₃ ⟨i₂, i₁⟩ = ComplexShape.π c₁ c₂ c₃ ⟨i₁, i₂⟩
  σ (i₁ : I₁) (i₂ : I₂) : ℤ
  σ_mul_self (i₁ : I₁) (i₂ : I₂) : σ i₁ i₂ * σ i₁ i₂ = 1
  compatibility₁ ⦃i₁ i₁' : I₁⦄ (h₁ : c₁.Rel i₁ i₁') (i₂ : I₂) :
    σ i₁ i₂ * ComplexShape.ε₂ c₂ c₁ c₃ ⟨i₂, i₁⟩ = ComplexShape.ε₁ c₁ c₂ c₃ ⟨i₁, i₂⟩ * σ i₁' i₂
  compatibility₂ (i₁ : I₁) ⦃i₂ i₂' : I₂⦄ (h₂ : c₂.Rel i₂ i₂') :
    σ i₁ i₂ * ComplexShape.ε₁ c₂ c₁ c₃ ⟨i₂, i₁⟩ = ComplexShape.ε₂ c₁ c₂ c₃ ⟨i₁, i₂⟩ * σ i₁ i₂'

variable [TotalComplexShapeSymmetry c₁ c₂ c₃]

namespace ComplexShape

abbrev σ (i₁ : I₁) (i₂ : I₂) : ℤ := TotalComplexShapeSymmetry.σ c₁ c₂ c₃ i₁ i₂

lemma π_symm (i₁ : I₁) (i₂ : I₂) :
    ComplexShape.π c₂ c₁ c₃ ⟨i₂, i₁⟩ = ComplexShape.π c₁ c₂ c₃ ⟨i₁, i₂⟩ := by
  apply TotalComplexShapeSymmetry.symm

@[simp]
lemma σ_mul_self (i₁ : I₁) (i₂ : I₂) : σ c₁ c₂ c₃ i₁ i₂ * σ c₁ c₂ c₃ i₁ i₂ = 1 := by
  apply TotalComplexShapeSymmetry.σ_mul_self

variable {c₁}

lemma σ_compatibility₁ {i₁ i₁' : I₁} (h₁ : c₁.Rel i₁ i₁') (i₂ : I₂) :
    σ c₁ c₂ c₃ i₁ i₂ * ComplexShape.ε₂ c₂ c₁ c₃ ⟨i₂, i₁⟩ = ComplexShape.ε₁ c₁ c₂ c₃ ⟨i₁, i₂⟩ * σ c₁ c₂ c₃ i₁' i₂ :=
  TotalComplexShapeSymmetry.compatibility₁ h₁ i₂

variable (c₁) {c₂}

lemma σ_compatibility₂ (i₁ : I₁) {i₂ i₂' : I₂} (h₂ : c₂.Rel i₂ i₂') :
    σ c₁ c₂ c₃ i₁ i₂ * ComplexShape.ε₁ c₂ c₁ c₃ ⟨i₂, i₁⟩ = ComplexShape.ε₂ c₁ c₂ c₃ ⟨i₁, i₂⟩ * σ c₁ c₂ c₃ i₁ i₂' :=
  TotalComplexShapeSymmetry.compatibility₂ i₁ h₂

end ComplexShape

--attribute [simp] TotalComplexShapeSymmetry.σ_mul

namespace HomologicalComplex₂

variable {c₁ c₂}
variable [Preadditive C] [DecidableEq I₃]
  (K : HomologicalComplex₂ C c₁ c₂)
  [K.toGradedObject.HasMap (ComplexShape.π c₁ c₂ c₃)]
  [K.flip.toGradedObject.HasMap (ComplexShape.π c₂ c₁ c₃)]

attribute [local simp] zsmul_comp smul_smul ιTotal_d_assoc

noncomputable def totalSymmIso : K.total c₃ ≅ K.flip.total c₃ :=
  HomologicalComplex.Hom.isoOfComponents (fun i₃ =>
    { hom := K.descTotal c₃
          (fun i₁ i₂ h => ComplexShape.σ c₁ c₂ c₃ i₁ i₂ • K.flip.ιTotal c₃ i₂ i₁ i₃ (by rw [ComplexShape.π_symm, h]))
      inv := K.flip.descTotal c₃
        (fun i₂ i₁ h => ComplexShape.σ c₁ c₂ c₃ i₁ i₂ • K.ιTotal c₃ i₁ i₂ i₃ (by rw [← ComplexShape.π_symm, h])) }) (by
    intro i₃ i₃' _
    ext i₁ i₂ h'
    dsimp
    simp only [ι_descTotal_assoc, zsmul_comp, ιTotal_d, flip_X_X, flip_d_f, flip_X_d, smul_add, smul_smul,
      ιTotal_d_assoc, add_comp, assoc]
    rw [add_comm]
    congr 1
    · by_cases h₁ : c₁.Rel i₁ (c₁.next i₁)
      · by_cases h₂ : (ComplexShape.π c₁ c₂ c₃) ⟨c₁.next i₁, i₂⟩ = i₃'
        · have h₃ : (ComplexShape.π c₂ c₁ c₃) ⟨i₂, c₁.next i₁⟩ = i₃' := by rw [ComplexShape.π_symm, h₂]
          rw [K.ιTotalOrZero_eq c₃ _ _ _ h₂, K.flip.ιTotalOrZero_eq c₃ _ _ _ h₃,
            ι_descTotal, comp_zsmul, smul_smul, ComplexShape.σ_compatibility₁ c₂ c₃ h₁ i₂]
        · rw [K.ιTotalOrZero_eq_zero c₃ _ _ _ h₂, zero_comp, comp_zero, smul_zero,
            K.flip.ιTotalOrZero_eq_zero, comp_zero, smul_zero]
          rw [ComplexShape.π_symm]
          exact h₂
      · rw [K.shape _ _ h₁, HomologicalComplex.zero_f, zero_comp, zero_comp, smul_zero, smul_zero]
    · by_cases h₁ : c₂.Rel i₂ (c₂.next i₂)
      · by_cases h₂ : (ComplexShape.π c₁ c₂ c₃) ⟨i₁, c₂.next i₂⟩ = i₃'
        · have h₃ : (ComplexShape.π c₂ c₁ c₃) ⟨c₂.next i₂, i₁⟩ = i₃' := by rw [ComplexShape.π_symm, h₂]
          rw [K.ιTotalOrZero_eq c₃ _ _ _ h₂, K.flip.ιTotalOrZero_eq c₃ _ _ _ h₃,
            ι_descTotal, comp_zsmul, smul_smul, ComplexShape.σ_compatibility₂ c₁ c₃ i₁ h₁]
        · rw [K.ιTotalOrZero_eq_zero c₃ _ _ _ h₂, zero_comp, comp_zero, smul_zero,
            K.flip.ιTotalOrZero_eq_zero, comp_zero, smul_zero]
          rw [ComplexShape.π_symm]
          exact h₂
      · rw [(K.X i₁).shape _ _ h₁, zero_comp, zero_comp, smul_zero, smul_zero])

end HomologicalComplex₂
