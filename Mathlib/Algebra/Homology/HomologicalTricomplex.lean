/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.TotalComplex

#align_import algebra.homology.flip from "leanprover-community/mathlib"@"ff511590476ef357b6132a45816adc120d5d7b1d"

/-!
# Tricomplexes

Given a category `C` with zero morphisms and three complex shapes
`c₁ : ComplexShape I₁`, `c₂ : ComplexShape I₂`, `c₃ : ComplexShape I₃`, we define
the type of tricomplexes `HomologicalComplex₃ C c₁ c₂ c₃` as an
abbreviation for `HomologicalComplex (HomologicalComplex₂ C c₂ c₃) c₁`.

-/

open CategoryTheory Category Limits

variable {C : Type*} [Category C] {I₁ I₂ I₃ I₁₂ I₂₃ J : Type*}
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c₃ : ComplexShape I₃}

variable (C c₁ c₂ c₃) in
/-- Given a category `C` and three complex shapes `c₁`, `c₂` and `c₃` on
types `I₁`, `I₂` and `I₃`, the associated type of tricomplexes `HomologicalComplex₂ C c₁ c₂ c₃`
is `K : HomologicalComplex (HomologicalComplex₂ C c₂ c₃) c₁`. -/
abbrev HomologicalComplex₃ [HasZeroMorphisms C] :=
  HomologicalComplex (HomologicalComplex₂ C c₂ c₃) c₁

variable [Preadditive C]

namespace HomologicalComplex₃

variable (K : HomologicalComplex₃ C c₁ c₂ c₃)

@[reassoc (attr := simp)]
lemma d_f_f_comp_d_f_f (i₁ i₁' i₁'' : I₁) (i₂ : I₂) (i₃ : I₃) :
    ((K.d i₁ i₁').f i₂).f i₃ ≫ ((K.d i₁' i₁'').f i₂).f i₃ = 0 := by
  rw [← HomologicalComplex.comp_f, HomologicalComplex₂.d_f_comp_d_f, HomologicalComplex.zero_f]

section

variable (c₂₃ : ComplexShape I₂₃) [DecidableEq I₂₃] [TotalComplexShape c₂ c₃ c₂₃]

abbrev HasInt₂₃ := ∀ (i₁ : I₁), (K.X i₁).HasTotal c₂₃

@[simps]
noncomputable def int₂₃ [K.HasInt₂₃ c₂₃] : HomologicalComplex₂ C c₁ c₂₃ where
  X i₁ := (K.X i₁).total c₂₃
  d i₁ i₁' := HomologicalComplex₂.total.map (K.d i₁ i₁') _
  shape i₁ i₁' h := by
    dsimp
    rw [K.shape _ _ h, HomologicalComplex₂.total.map_zero]
  d_comp_d' i₁ i₁' i₁'' _ _ := by
    dsimp
    rw [← HomologicalComplex₂.total.map_comp, K.d_comp_d,
      HomologicalComplex₂.total.map_zero]

end

section

@[simps!]
def X' (i₃ : I₃) : HomologicalComplex₂ C c₁ c₂ where
  X i₁ :=
    { X := fun i₂ => ((K.X i₁).X i₂).X i₃
      d := fun i₂ i₂' => ((K.X i₁).d i₂ i₂').f i₃ }
  d i₁ i₁' :=
    { f := fun i₂ => ((K.d i₁ i₁').f i₂).f i₃ }

@[simps]
def d' (i₃ i₃' : I₃) : K.X' i₃ ⟶ K.X' i₃' where
  f i₁ :=
    { f := fun i₂ => ((K.X i₁).X i₂).d i₃ i₃' }

lemma shape_d' (i₃ i₃' : I₃) (h : ¬ c₃.Rel i₃ i₃') :
    K.d' i₃ i₃' = 0 := by
  ext i₁ i₂
  dsimp
  rw [HomologicalComplex.shape _ _ _ h]

@[reassoc (attr := simp)]
lemma d'_comp_d' (i₃ i₃' i₃'' : I₃) : K.d' i₃ i₃' ≫ K.d' i₃' i₃'' = 0 := by aesop_cat

variable (c₁₂ : ComplexShape I₁₂) [DecidableEq I₁₂] [TotalComplexShape c₁ c₂ c₁₂]

abbrev HasInt₁₂ := ∀ (i₃ : I₃), (K.X' i₃).HasTotal c₁₂

@[simps]
noncomputable def int₁₂' [K.HasInt₁₂ c₁₂] : HomologicalComplex₂ C c₃ c₁₂ where
  X i₃ := (K.X' i₃).total c₁₂
  d i₃ i₃' := HomologicalComplex₂.total.map (K.d' i₃ i₃') _
  shape i₃ i₃' h := by
    dsimp
    rw [K.shape_d' _ _ h, HomologicalComplex₂.total.map_zero]
  d_comp_d' i₁ i₂ i₃ _ _ := by
    dsimp
    rw [← HomologicalComplex₂.total.map_comp, K.d'_comp_d',
      HomologicalComplex₂.total.map_zero]

@[simps!]
noncomputable def int₁₂ [K.HasInt₁₂ c₁₂] : HomologicalComplex₂ C c₁₂ c₃ := (K.int₁₂' c₁₂).flip

end

section

variable (c₁₂ : ComplexShape I₁₂) (c₂₃ : ComplexShape I₂₃) (c : ComplexShape J)
  [DecidableEq I₁₂] [DecidableEq I₂₃] [DecidableEq J]
  [TotalComplexShape c₁ c₂ c₁₂] [TotalComplexShape c₂ c₃ c₂₃]
  [TotalComplexShape c₁₂ c₃ c] [TotalComplexShape c₁ c₂₃ c]

section

variable [K.HasInt₁₂ c₁₂]

abbrev HasTotal₁₂ := (K.int₁₂ c₁₂).HasTotal c

variable [K.HasTotal₁₂ c₁₂ c]

noncomputable def total₁₂ : HomologicalComplex C c := (K.int₁₂ c₁₂).total c

section

variable (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)

noncomputable def ιTotal₁₂
    (h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) = j) :
    ((K.X i₁).X i₂).X i₃ ⟶ (K.total₁₂ c₁₂ c).X j :=
  (K.X' i₃).ιTotal c₁₂ i₁ i₂ _ rfl ≫
    (K.int₁₂ c₁₂).ιTotal c (ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩) i₃ j h

@[reassoc]
lemma ιTotal₁₂_eq
    (h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) = j)
    (i₁₂ : I₁₂) (h' : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂) :
    K.ιTotal₁₂ c₁₂ c i₁ i₂ i₃ j h = (K.X' i₃).ιTotal c₁₂ i₁ i₂ i₁₂ h' ≫
    (K.int₁₂ c₁₂).ιTotal c i₁₂ i₃ j (by rw [← h', h]) := by
  subst h'
  rfl

noncomputable def ιTotal₁₂OrZero :
    ((K.X i₁).X i₂).X i₃ ⟶ (K.total₁₂ c₁₂ c).X j :=
  if h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) = j then
    K.ιTotal₁₂ c₁₂ c i₁ i₂ i₃ j h
  else 0

lemma ιTotal₁₂OrZero_eq (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
    (h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) = j) :
    K.ιTotal₁₂OrZero c₁₂ c i₁ i₂ i₃ j = K.ιTotal₁₂ c₁₂ c i₁ i₂ i₃ j h := dif_pos h

lemma ιTotal₁₂OrZero_eq_zero (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
    (h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) ≠ j) :
    K.ιTotal₁₂OrZero c₁₂ c i₁ i₂ i₃ j = 0 := dif_neg h

end

section

variable (i₁ i₁' : I₁) (h₁ : c₁.Rel i₁ i₁')
  (i₂ i₂' : I₂) (h₂ : c₂.Rel i₂ i₂')
  (i₃ i₃' : I₃) (h₃ : c₃.Rel i₃ i₃') (j : J)

noncomputable def d₁ : ((K.X i₁).X i₂).X i₃ ⟶ (K.total₁₂ c₁₂ c).X j :=
  (ComplexShape.ε₁ c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) *
    ComplexShape.ε₁ c₁ c₂ c₁₂ (i₁, i₂)) •
      ((K.d i₁ (c₁.next i₁)).f i₂).f i₃ ≫ K.ιTotal₁₂OrZero c₁₂ c _ _ _ _

noncomputable def d₂ : ((K.X i₁).X i₂).X i₃ ⟶ (K.total₁₂ c₁₂ c).X j :=
  (ComplexShape.ε₁ c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) *
    ComplexShape.ε₂ c₁ c₂ c₁₂ (i₁, i₂)) •
  ((K.X i₁).d i₂ (c₂.next i₂)).f i₃ ≫ K.ιTotal₁₂OrZero c₁₂ c _ _ _ _

noncomputable def d₃ : ((K.X i₁).X i₂).X i₃ ⟶ (K.total₁₂ c₁₂ c).X j :=
  ComplexShape.ε₂ c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩, i₃) •
    ((K.X i₁).X i₂).d i₃ (c₃.next i₃) ≫ K.ιTotal₁₂OrZero c₁₂ c _ _ _ _

lemma d₁_eq_zero (h : ¬ c₁.Rel i₁ (c₁.next i₁)) : K.d₁ c₁₂ c i₁ i₂ i₃ j = 0 := by
  dsimp [d₁]
  rw [HomologicalComplex.shape _ _ _ h, HomologicalComplex.zero_f,
    HomologicalComplex.zero_f, zero_comp, smul_zero]

lemma d₂_eq_zero (h : ¬ c₂.Rel i₂ (c₂.next i₂)) : K.d₂ c₁₂ c i₁ i₂ i₃ j = 0 := by
  dsimp [d₂]
  rw [HomologicalComplex.shape _ _ _ h, HomologicalComplex.zero_f, zero_comp, smul_zero]

lemma d₃_eq_zero (h : ¬ c₃.Rel i₃ (c₃.next i₃)) : K.d₃ c₁₂ c i₁ i₂ i₃ j = 0 := by
  dsimp [d₃]
  rw [HomologicalComplex.shape _ _ _ h, zero_comp, smul_zero]

section

variable {i₁ i₁'}

lemma d₁_eq' :
    K.d₁ c₁₂ c i₁ i₂ i₃ j = (ComplexShape.ε₁ c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) *
      ComplexShape.ε₁ c₁ c₂ c₁₂ (i₁, i₂)) •
        ((K.d i₁ i₁').f i₂).f i₃ ≫ K.ιTotal₁₂OrZero c₁₂ c _ _ _ _ := by
  obtain rfl := c₁.next_eq' h₁
  rfl

lemma d₁_eq_zero'
    (h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁', i₂), i₃) ≠ j) :
    K.d₁ c₁₂ c i₁ i₂ i₃ j = 0 := by
  rw [K.d₁_eq' c₁₂ c h₁, ιTotal₁₂OrZero_eq_zero _ _ _ _ _ _ _ h, comp_zero, smul_zero]

lemma d₁_eq
    (h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁', i₂), i₃) = j) :
    K.d₁ c₁₂ c i₁ i₂ i₃ j = (ComplexShape.ε₁ c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) *
      ComplexShape.ε₁ c₁ c₂ c₁₂ (i₁, i₂)) •
        ((K.d i₁ i₁').f i₂).f i₃ ≫ ιTotal₁₂ K c₁₂ c i₁' i₂ i₃ j h := by
  rw [K.d₁_eq' c₁₂ c h₁, ιTotal₁₂OrZero_eq _ _ _ _ _ _ _ h]

end

section

variable {i₂ i₂'}

lemma d₂_eq' : K.d₂ c₁₂ c i₁ i₂ i₃ j =
    (ComplexShape.ε₁ c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) *
    ComplexShape.ε₂ c₁ c₂ c₁₂ (i₁, i₂)) • ((K.X i₁).d i₂ i₂').f i₃ ≫
      K.ιTotal₁₂OrZero c₁₂ c _ _ _ _ := by
  obtain rfl := c₂.next_eq' h₂
  rfl

lemma d₂_eq_zero'
    (h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂'), i₃) ≠ j) :
    K.d₂ c₁₂ c i₁ i₂ i₃ j = 0 := by
  rw [K.d₂_eq' c₁₂ c i₁ h₂, ιTotal₁₂OrZero_eq_zero _ _ _ _ _ _ _ h, comp_zero, smul_zero]

lemma d₂_eq
    (h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂'), i₃) = j) :
    K.d₂ c₁₂ c i₁ i₂ i₃ j =
      (ComplexShape.ε₁ c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) *
        ComplexShape.ε₂ c₁ c₂ c₁₂ (i₁, i₂)) • ((K.X i₁).d i₂ i₂').f i₃ ≫
          ιTotal₁₂ K c₁₂ c i₁ i₂' i₃ j h := by
  rw [K.d₂_eq' c₁₂ c i₁ h₂, ιTotal₁₂OrZero_eq _ _ _ _ _ _ _ h]

end

section

variable {i₃ i₃'}

lemma d₃_eq' : K.d₃ c₁₂ c i₁ i₂ i₃ j =
    ComplexShape.ε₂ c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩, i₃) •
      ((K.X i₁).X i₂).d i₃ i₃' ≫ K.ιTotal₁₂OrZero c₁₂ c _ _ _ _ := by
  obtain rfl := c₃.next_eq' h₃
  rfl

lemma d₃_eq_zero'
    (h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃') ≠ j) :
    K.d₃ c₁₂ c i₁ i₂ i₃ j = 0 := by
  rw [K.d₃_eq' c₁₂ c i₁ i₂ h₃, ιTotal₁₂OrZero_eq_zero _ _ _ _ _ _ _ h, comp_zero, smul_zero]

lemma d₃_eq
    (h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃') = j) :
    K.d₃ c₁₂ c i₁ i₂ i₃ j = ComplexShape.ε₂ c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩, i₃) •
      ((K.X i₁).X i₂).d i₃ i₃' ≫ ιTotal₁₂ K c₁₂ c i₁ i₂ i₃' j h := by
  rw [K.d₃_eq' c₁₂ c i₁ i₂ h₃, ιTotal₁₂OrZero_eq _ _ _ _ _ _ _ h]

end

end

section

variable {c₁₂ c}
variable {A : C} {j : J} (f : ∀ (i₁ : I₁) (i₂ : I₂) (i₃ : I₃)
    (_ : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) = j),
      ((K.X i₁).X i₂).X i₃ ⟶ A)

noncomputable def total₁₂Desc : (K.total₁₂ c₁₂ c).X j ⟶ A :=
  (K.int₁₂ c₁₂).totalDesc (fun i₁₂ i₃ h => (K.X' i₃).totalDesc
    (fun i₁ i₂ h' => f i₁ i₂ i₃ (by rw [h', h])))

@[reassoc (attr := simp)]
lemma ι_total₁₂Desc (i₁ : I₁) (i₂ : I₂) (i₃ : I₃)
    (h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) = j) :
    K.ιTotal₁₂ c₁₂ c i₁ i₂ i₃ j h ≫ total₁₂Desc K f = f i₁ i₂ i₃ h := by
  simp [ιTotal₁₂, total₁₂Desc]

end

variable {K c₁₂ c} in
@[ext]
lemma total₁₂.hom_ext {A : C} {j : J} {f g : (K.total₁₂ c₁₂ c).X j ⟶ A}
    (hfg : ∀ (i₁ : I₁) (i₂ : I₂) (i₃ : I₃)
      (h' : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) = j),
        K.ιTotal₁₂ c₁₂ c i₁ i₂ i₃ j h' ≫ f = K.ιTotal₁₂ c₁₂ c i₁ i₂ i₃ j h' ≫ g) :
    f = g :=
  HomologicalComplex₂.total.hom_ext (fun i₁₂ i₃ h =>
    HomologicalComplex₂.total.hom_ext (fun i₁ i₂ h' => by
      simpa only [← ιTotal₁₂_eq_assoc _ c₁₂ c i₁ i₂ i₃ j
        (by rw [h', h]) i₁₂ h'] using hfg i₁ i₂ i₃ (by rw [h', h])))

noncomputable def D₁ (j j' : J) : (K.total₁₂ c₁₂ c).X j ⟶ (K.total₁₂ c₁₂ c).X j' :=
  K.total₁₂Desc (fun _ _ _ _ => K.d₁ _ _ _ _ _ _)

noncomputable def D₂ (j j' : J) : (K.total₁₂ c₁₂ c).X j ⟶ (K.total₁₂ c₁₂ c).X j' :=
  K.total₁₂Desc (fun _ _ _ _ => K.d₂ _ _ _ _ _ _)

noncomputable def D₃ (j j' : J) : (K.total₁₂ c₁₂ c).X j ⟶ (K.total₁₂ c₁₂ c).X j' :=
  K.total₁₂Desc (fun _ _ _ _ => K.d₃ _ _ _ _ _ _)

@[reassoc (attr := simp)]
lemma ι_D₁ (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j j' : J)
    (h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) = j) :
    K.ιTotal₁₂ c₁₂ c i₁ i₂ i₃ j h ≫ K.D₁ c₁₂ c j j' = K.d₁ _ _ _ _ _ _ := by
  simp [D₁]

@[reassoc (attr := simp)]
lemma ι_D₂ (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j j' : J)
    (h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) = j) :
    K.ιTotal₁₂ c₁₂ c i₁ i₂ i₃ j h ≫ K.D₂ c₁₂ c j j' = K.d₂ _ _ _ _ _ _ := by
  simp [D₂]

@[reassoc (attr := simp)]
lemma ι_D₃ (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j j' : J)
    (h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) = j) :
    K.ιTotal₁₂ c₁₂ c i₁ i₂ i₃ j h ≫ K.D₃ c₁₂ c j j' = K.d₃ _ _ _ _ _ _ := by
  simp [D₃]

lemma D₁_shape (j j' : J) (h : ¬ c.Rel j j') : K.D₁ c₁₂ c j j' = 0 := by
  ext i₁ i₂ i₃ h'
  rw [ι_D₁, comp_zero]
  by_cases h₁ : c₁.Rel i₁ (c₁.next i₁)
  · rw [K.d₁_eq_zero' _ _ h₁]
    intro h₂
    apply h
    rw [← h', ← h₂]
    exact ComplexShape.rel_π₁ c₃ c (ComplexShape.rel_π₁ c₂ c₁₂ h₁ i₂) i₃
  · rw [K.d₁_eq_zero _ _ _ _ _ _ h₁]

lemma D₂_shape (j j' : J) (h : ¬ c.Rel j j') : K.D₂ c₁₂ c j j' = 0 := by
  ext i₁ i₂ i₃ h'
  rw [ι_D₂, comp_zero]
  by_cases h₁ : c₂.Rel i₂ (c₂.next i₂)
  · rw [K.d₂_eq_zero' _ _ _ h₁]
    intro h₂
    apply h
    rw [← h', ← h₂]
    exact ComplexShape.rel_π₁ c₃ c (ComplexShape.rel_π₂ c₁ c₁₂ i₁ h₁) i₃
  · rw [K.d₂_eq_zero _ _ _ _ _ _ h₁]

lemma D₃_shape (j j' : J) (h : ¬ c.Rel j j') : K.D₃ c₁₂ c j j' = 0 := by
  ext i₁ i₂ i₃ h'
  rw [ι_D₃, comp_zero]
  by_cases h₁ : c₃.Rel i₃ (c₃.next i₃)
  · rw [K.d₃_eq_zero' _ _ _ _ h₁]
    intro h₂
    apply h
    rw [← h', ← h₂]
    exact ComplexShape.rel_π₂ c₁₂ c _ h₁
  · rw [K.d₃_eq_zero _ _ _ _ _ _ h₁]

lemma int₁₂_D₁ (j j' : J) :
    (int₁₂ K c₁₂).D₁ c j j' = K.D₁ c₁₂ c j j' + K.D₂ c₁₂ c j j' := by
  by_cases h₀ : c.Rel j j'
  · apply total₁₂.hom_ext
    intro i₁ i₂ i₃ h
    rw [Preadditive.comp_add, ι_D₁, ι_D₂, K.ιTotal₁₂_eq c₁₂ c i₁ i₂ i₃ j h _ rfl, assoc,
      HomologicalComplex₂.ι_D₁]
    let i₁₂ := ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩
    by_cases h₁ : c₁₂.Rel i₁₂ (c₁₂.next i₁₂)
    · rw [(K.int₁₂ c₁₂).d₁_eq c h₁ i₃ j']; swap
      · rw [← c.next_eq' h₀, ← h, ComplexShape.next_π₁ c₃ c h₁]
      dsimp
      simp only [Preadditive.add_comp, smul_add, Preadditive.comp_add, Linear.comp_units_smul,
        HomologicalComplex₂.ι_D₁_assoc, HomologicalComplex₂.ι_D₂_assoc]
      congr 1
      · by_cases h₂ : c₁.Rel i₁ (c₁.next i₁)
        · rw [(K.X' i₃).d₁_eq _ h₂ _ _ (ComplexShape.next_π₁ c₂ c₁₂ h₂ i₂).symm,
            Linear.units_smul_comp, assoc, smul_smul, K.d₁_eq c₁₂ c h₂ i₂ i₃ j']; swap
          · rw [← c.next_eq' h₀, ← h, ComplexShape.next_π₁ c₃ c h₁,
              ComplexShape.next_π₁ c₂ c₁₂ h₂ i₂]
          congr 2
          symm
          apply K.ιTotal₁₂_eq
        · rw [(K.X' i₃).d₁_eq_zero _ _ _ _ h₂, zero_comp, smul_zero,
            K.d₁_eq_zero _ _ _ _ _ _ h₂]
      · by_cases h₂ : c₂.Rel i₂ (c₂.next i₂)
        · rw [(K.X' i₃).d₂_eq _ _ h₂ _ (ComplexShape.next_π₂ c₁ c₁₂ i₁ h₂).symm,
            Linear.units_smul_comp, assoc, smul_smul, K.d₂_eq c₁₂ c i₁ h₂ i₃ j']; swap
          · rw [← c.next_eq' h₀, ← h, ← ComplexShape.next_π₂ c₁ c₁₂ i₁ h₂,
              ComplexShape.next_π₁ c₃ c h₁ i₃]
          congr 2
          symm
          apply K.ιTotal₁₂_eq
        · rw [(K.X' i₃).d₂_eq_zero _ _ _ _ h₂, zero_comp, smul_zero,
            K.d₂_eq_zero _ _ _ _ _ _ h₂]
    · rw [(K.int₁₂ c₁₂).d₁_eq_zero _ _ _ _ h₁, K.d₁_eq_zero, K.d₂_eq_zero, zero_add, comp_zero]
      · intro h₂
        have H := ComplexShape.rel_π₂ c₁ c₁₂ i₁ h₂
        rw [c₁₂.next_eq' H] at h₁
        exact h₁ H
      · intro h₂
        have H := ComplexShape.rel_π₁ c₂ c₁₂ h₂ i₂
        rw [c₁₂.next_eq' H] at h₁
        exact h₁ H
  · rw [(K.int₁₂ c₁₂).D₁_shape _ _ _ h₀, K.D₁_shape _ _ _ _ h₀, K.D₂_shape _ _ _ _ h₀, zero_add]

lemma int₁₂_D₂ (j j' : J) : (int₁₂ K c₁₂).D₂ c j j' = K.D₃ c₁₂ c j j' :=
  total₁₂.hom_ext (fun i₁ i₂ i₃ h => by
    rw [ι_D₃, K.ιTotal₁₂_eq_assoc c₁₂ c i₁ i₂ i₃ j h _ rfl, HomologicalComplex₂.ι_D₂]
    by_cases h₁ : c₃.Rel i₃ (c₃.next i₃)
    · by_cases h₂ : ComplexShape.π c₁₂ c₃ c
        (ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩, ComplexShape.next c₃ i₃) = j'
      · rw [(K.int₁₂ c₁₂).d₂_eq c _ h₁ j' h₂, Linear.comp_units_smul, int₁₂_X_d,
          HomologicalComplex₂.ιTotal_map_assoc, K.d₃_eq c₁₂ c i₁ i₂ h₁ j' (by rw [← h₂])]
        rfl
      · rw [(K.int₁₂ c₁₂).d₂_eq_zero' c _ h₁ j' h₂, comp_zero,
          K.d₃_eq_zero' c₁₂ c i₁ i₂ h₁ j' (fun h₃ => h₂ (by rw [← h₃]))]
    · rw [(K.int₁₂ c₁₂).d₂_eq_zero c _ i₃ j' h₁, comp_zero, K.d₃_eq_zero c₁₂ c i₁ i₂ i₃ j' h₁])

@[simp]
lemma total₁₂_d (j j' : J) :
    (K.total₁₂ c₁₂ c).d j j' = K.D₁ c₁₂ c j j' + K.D₂ c₁₂ c j j' + K.D₃ c₁₂ c j j' := by
  dsimp [total₁₂]
  rw [int₁₂_D₁, int₁₂_D₂]

end

section

variable [K.HasInt₂₃ c₂₃]

abbrev HasTotal₂₃ := (K.int₂₃ c₂₃).HasTotal c

variable [K.HasTotal₂₃ c₂₃ c]

noncomputable def total₂₃ : HomologicalComplex C c :=
  (K.int₂₃ c₂₃).total c

section

variable (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)

noncomputable def ιTotal₂₃
    (h : ComplexShape.π c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) = j) :
    ((K.X i₁).X i₂).X i₃ ⟶ (K.total₂₃ c₂₃ c).X j :=
  (K.X i₁).ιTotal c₂₃ i₂ i₃ _ rfl ≫
    (K.int₂₃ c₂₃).ιTotal c i₁ (ComplexShape.π c₂ c₃ c₂₃ ⟨i₂, i₃⟩) j h

@[reassoc]
lemma ιTotal₂₃_eq
    (h : ComplexShape.π c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) = j)
    (i₂₃ : I₂₃) (h' : ComplexShape.π c₂ c₃ c₂₃ ⟨i₂, i₃⟩ = i₂₃) :
    K.ιTotal₂₃ c₂₃ c i₁ i₂ i₃ j h = (K.X i₁).ιTotal c₂₃ i₂ i₃ i₂₃ h' ≫
    (K.int₂₃ c₂₃).ιTotal c i₁ i₂₃ j (by rw [← h', h]) := by
  subst h'
  rfl

noncomputable def ιTotal₂₃OrZero :
    ((K.X i₁).X i₂).X i₃ ⟶ (K.total₂₃ c₂₃ c).X j :=
  if h : ComplexShape.π c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) = j then
    K.ιTotal₂₃ c₂₃ c i₁ i₂ i₃ j h
  else 0

lemma ιTotal₂₃OrZero_eq
    (h : ComplexShape.π c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) = j) :
    K.ιTotal₂₃OrZero c₂₃ c i₁ i₂ i₃ j = K.ιTotal₂₃ c₂₃ c i₁ i₂ i₃ j h := dif_pos h

lemma ιTotal₂₃OrZero_eq_zero (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
    (h : ComplexShape.π c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) ≠ j) :
    K.ιTotal₂₃OrZero c₂₃ c i₁ i₂ i₃ j = 0 := dif_neg h

end

section

variable (i₁ i₁' : I₁) (h₁ : c₁.Rel i₁ i₁')
  (i₂ i₂' : I₂) (h₂ : c₂.Rel i₂ i₂')
  (i₃ i₃' : I₃) (h₃ : c₃.Rel i₃ i₃') (j : J)

noncomputable def d₁' : ((K.X i₁).X i₂).X i₃ ⟶ (K.total₂₃ c₂₃ c).X j :=
    ComplexShape.ε₁ c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) •
      ((K.d i₁ (c₁.next i₁)).f i₂).f i₃ ≫ K.ιTotal₂₃OrZero c₂₃ c _ _ _ _

noncomputable def d₂' : ((K.X i₁).X i₂).X i₃ ⟶ (K.total₂₃ c₂₃ c).X j :=
    (ComplexShape.ε₂ c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) *
      ComplexShape.ε₁ c₂ c₃ c₂₃ (i₂, i₃)) •
  ((K.X i₁).d i₂ (c₂.next i₂)).f i₃ ≫ K.ιTotal₂₃OrZero c₂₃ c _ _ _ _

noncomputable def d₃' : ((K.X i₁).X i₂).X i₃ ⟶ (K.total₂₃ c₂₃ c).X j :=
    (ComplexShape.ε₂ c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) *
      ComplexShape.ε₂ c₂ c₃ c₂₃ (i₂, i₃)) •
        ((K.X i₁).X i₂).d i₃ (c₃.next i₃) ≫ K.ιTotal₂₃OrZero c₂₃ c _ _ _ _

lemma d₁'_eq_zero (h : ¬ c₁.Rel i₁ (c₁.next i₁)) : K.d₁' c₂₃ c i₁ i₂ i₃ j = 0 := by
  dsimp [d₁']
  rw [HomologicalComplex.shape _ _ _ h, HomologicalComplex.zero_f,
    HomologicalComplex.zero_f, zero_comp, smul_zero]

lemma d₂'_eq_zero (h : ¬ c₂.Rel i₂ (c₂.next i₂)) : K.d₂' c₂₃ c i₁ i₂ i₃ j = 0 := by
  dsimp [d₂']
  rw [HomologicalComplex.shape _ _ _ h, HomologicalComplex.zero_f, zero_comp, smul_zero]

lemma d₃'_eq_zero (h : ¬ c₃.Rel i₃ (c₃.next i₃)) : K.d₃' c₂₃ c i₁ i₂ i₃ j = 0 := by
  dsimp [d₃']
  rw [HomologicalComplex.shape _ _ _ h, zero_comp, smul_zero]

section

variable {i₁ i₁'}

lemma d₁'_eq' :
    K.d₁' c₂₃ c i₁ i₂ i₃ j = ComplexShape.ε₁ c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) •
        ((K.d i₁ i₁').f i₂).f i₃ ≫ K.ιTotal₂₃OrZero c₂₃ c _ _ _ _ := by
  obtain rfl := c₁.next_eq' h₁
  rfl

lemma d₁'_eq_zero'
    (h : ComplexShape.π c₁ c₂₃ c (i₁', ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) ≠ j) :
    K.d₁' c₂₃ c i₁ i₂ i₃ j = 0 := by
  rw [K.d₁'_eq' c₂₃ c h₁, ιTotal₂₃OrZero_eq_zero _ _ _ _ _ _ _ h, comp_zero, smul_zero]

lemma d₁'_eq
    (h : ComplexShape.π c₁ c₂₃ c (i₁', ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) = j) :
    K.d₁' c₂₃ c i₁ i₂ i₃ j = ComplexShape.ε₁ c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) •
        ((K.d i₁ i₁').f i₂).f i₃ ≫ ιTotal₂₃ K c₂₃ c i₁' i₂ i₃ j h := by
  rw [K.d₁'_eq' c₂₃ c h₁, ιTotal₂₃OrZero_eq _ _ _ _ _ _ _ h]

end

section

variable {i₂ i₂'}

lemma d₂'_eq' :
    K.d₂' c₂₃ c i₁ i₂ i₃ j = (ComplexShape.ε₂ c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) *
      ComplexShape.ε₁ c₂ c₃ c₂₃ (i₂, i₃)) • ((K.X i₁).d i₂ i₂').f i₃ ≫
      K.ιTotal₂₃OrZero c₂₃ c _ _ _ _ := by
  obtain rfl := c₂.next_eq' h₂
  rfl

lemma d₂'_eq_zero'
    (h : ComplexShape.π c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂', i₃)) ≠ j) :
    K.d₂' c₂₃ c i₁ i₂ i₃ j = 0 := by
  rw [K.d₂'_eq' c₂₃ c i₁ h₂, ιTotal₂₃OrZero_eq_zero _ _ _ _ _ _ _ h, comp_zero, smul_zero]

lemma d₂'_eq
    (h : ComplexShape.π c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂', i₃)) = j) :
    K.d₂' c₂₃ c i₁ i₂ i₃ j = (ComplexShape.ε₂ c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) *
      ComplexShape.ε₁ c₂ c₃ c₂₃ (i₂, i₃)) • ((K.X i₁).d i₂ i₂').f i₃ ≫
        ιTotal₂₃ K c₂₃ c i₁ i₂' i₃ j h := by
  rw [K.d₂'_eq' c₂₃ c i₁ h₂, ιTotal₂₃OrZero_eq _ _ _ _ _ _ _ h]

end

section

variable {i₃ i₃'}

lemma d₃'_eq' :
    K.d₃' c₂₃ c i₁ i₂ i₃ j = (ComplexShape.ε₂ c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) *
      ComplexShape.ε₂ c₂ c₃ c₂₃ (i₂, i₃)) •
      ((K.X i₁).X i₂).d i₃ i₃' ≫ K.ιTotal₂₃OrZero c₂₃ c _ _ _ _ := by
  obtain rfl := c₃.next_eq' h₃
  rfl

lemma d₃'_eq_zero'
    (h : ComplexShape.π c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃')) ≠ j) :
    K.d₃' c₂₃ c i₁ i₂ i₃ j = 0 := by
  rw [K.d₃'_eq' c₂₃ c i₁ i₂ h₃, ιTotal₂₃OrZero_eq_zero _ _ _ _ _ _ _ h, comp_zero, smul_zero]

lemma d₃'_eq
    (h : ComplexShape.π c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃')) = j) :
    K.d₃' c₂₃ c i₁ i₂ i₃ j = (ComplexShape.ε₂ c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) *
      ComplexShape.ε₂ c₂ c₃ c₂₃ (i₂, i₃)) •
      ((K.X i₁).X i₂).d i₃ i₃' ≫ ιTotal₂₃ K c₂₃ c i₁ i₂ i₃' j h := by
  rw [K.d₃'_eq' c₂₃ c i₁ i₂ h₃, ιTotal₂₃OrZero_eq _ _ _ _ _ _ _ h]

end

end

section

variable {c₂₃ c}
variable {A : C} {j : J} (f : ∀ (i₁ : I₁) (i₂ : I₂) (i₃ : I₃)
    (_ : ComplexShape.π c₁ c₂₃ c ⟨i₁, ComplexShape.π c₂ c₃ c₂₃ ⟨i₂, i₃⟩⟩ = j),
      ((K.X i₁).X i₂).X i₃ ⟶ A)

noncomputable def total₂₃Desc : (K.total₂₃ c₂₃ c).X j ⟶ A :=
  (K.int₂₃ c₂₃).totalDesc (fun i₁ i₂₃ h => (K.X i₁).totalDesc
    (fun i₂ i₃ h' => f i₁ i₂ i₃ (by rw [h', h])))

@[reassoc (attr := simp)]
lemma ι_total₂₃Desc (i₁ : I₁) (i₂ : I₂) (i₃ : I₃)
    (h : ComplexShape.π c₁ c₂₃ c ⟨i₁, ComplexShape.π c₂ c₃ c₂₃ ⟨i₂, i₃⟩⟩ = j) :
    K.ιTotal₂₃ c₂₃ c i₁ i₂ i₃ j h ≫ total₂₃Desc K f = f i₁ i₂ i₃ h := by
  simp [ιTotal₂₃, total₂₃Desc]

end

variable {K c₂₃ c} in
@[ext]
lemma total₂₃.hom_ext {A : C} {j : J} {f g : (K.total₂₃ c₂₃ c).X j ⟶ A}
    (hfg : ∀ (i₁ : I₁) (i₂ : I₂) (i₃ : I₃)
      (h' : ComplexShape.π c₁ c₂₃ c ⟨i₁, ComplexShape.π c₂ c₃ c₂₃ ⟨i₂, i₃⟩⟩ = j),
        K.ιTotal₂₃ c₂₃ c i₁ i₂ i₃ j h' ≫ f = K.ιTotal₂₃ c₂₃ c i₁ i₂ i₃ j h' ≫ g) :
    f = g :=
  HomologicalComplex₂.total.hom_ext (fun i₁ i₂₃ h =>
    HomologicalComplex₂.total.hom_ext (fun i₂ i₃ h' => by
      simpa only [← ιTotal₂₃_eq_assoc _ c₂₃ c i₁ i₂ i₃ j
        (by rw [h', h]) i₂₃ h'] using hfg i₁ i₂ i₃ (by rw [h', h])))

noncomputable def D₁' (j j' : J) : (K.total₂₃ c₂₃ c).X j ⟶ (K.total₂₃ c₂₃ c).X j' :=
  K.total₂₃Desc (fun _ _ _ _ => K.d₁' _ _ _ _ _ _)

noncomputable def D₂' (j j' : J) : (K.total₂₃ c₂₃ c).X j ⟶ (K.total₂₃ c₂₃ c).X j' :=
  K.total₂₃Desc (fun _ _ _ _ => K.d₂' _ _ _ _ _ _)

noncomputable def D₃' (j j' : J) : (K.total₂₃ c₂₃ c).X j ⟶ (K.total₂₃ c₂₃ c).X j' :=
  K.total₂₃Desc (fun _ _ _ _ => K.d₃' _ _ _ _ _ _)

@[reassoc (attr := simp)]
lemma ι_D₁' (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j j' : J)
    (h : ComplexShape.π c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) = j) :
    K.ιTotal₂₃ c₂₃ c i₁ i₂ i₃ j h ≫ K.D₁' c₂₃ c j j' = K.d₁' _ _ _ _ _ _ := by
  simp [D₁']

@[reassoc (attr := simp)]
lemma ι_D₂' (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j j' : J)
    (h : ComplexShape.π c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) = j) :
    K.ιTotal₂₃ c₂₃ c i₁ i₂ i₃ j h ≫ K.D₂' c₂₃ c j j' = K.d₂' _ _ _ _ _ _ := by
  simp [D₂']

@[reassoc (attr := simp)]
lemma ι_D₃' (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j j' : J)
    (h : ComplexShape.π c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) = j) :
    K.ιTotal₂₃ c₂₃ c i₁ i₂ i₃ j h ≫ K.D₃' c₂₃ c j j' = K.d₃' _ _ _ _ _ _ := by
  simp [D₃']

lemma D₁'_shape (j j' : J) (h : ¬ c.Rel j j') : K.D₁' c₂₃ c j j' = 0 := by
  ext i₁ i₂ i₃ h'
  rw [ι_D₁', comp_zero]
  by_cases h₁ : c₁.Rel i₁ (c₁.next i₁)
  · rw [K.d₁'_eq_zero' _ _ h₁]
    intro h₂
    apply h
    rw [← h', ← h₂]
    exact ComplexShape.rel_π₁ c₂₃ c h₁ _
  · rw [K.d₁'_eq_zero _ _ _ _ _ _ h₁]

lemma D₂'_shape (j j' : J) (h : ¬ c.Rel j j') : K.D₂' c₂₃ c j j' = 0 := by
  ext i₁ i₂ i₃ h'
  rw [ι_D₂', comp_zero]
  by_cases h₁ : c₂.Rel i₂ (c₂.next i₂)
  · rw [K.d₂'_eq_zero' _ _ _ h₁]
    intro h₂
    apply h
    rw [← h', ← h₂]
    exact ComplexShape.rel_π₂ c₁ c i₁ (ComplexShape.rel_π₁ c₃ c₂₃ h₁ i₃)
  · rw [K.d₂'_eq_zero _ _ _ _ _ _ h₁]

lemma D₃'_shape (j j' : J) (h : ¬ c.Rel j j') : K.D₃' c₂₃ c j j' = 0 := by
  ext i₁ i₂ i₃ h'
  rw [ι_D₃', comp_zero]
  by_cases h₁ : c₃.Rel i₃ (c₃.next i₃)
  · rw [K.d₃'_eq_zero' _ _ _ _ h₁]
    intro h₂
    apply h
    rw [← h', ← h₂]
    exact ComplexShape.rel_π₂ c₁ c i₁ (ComplexShape.rel_π₂ c₂ c₂₃ i₂ h₁)
  · rw [K.d₃'_eq_zero _ _ _ _ _ _ h₁]

lemma int₂₃_D₁ (j j' : J) :
    (int₂₃ K c₂₃).D₁ c j j' = K.D₁' c₂₃ c j j' :=
  total₂₃.hom_ext (fun i₁ i₂ i₃ h => by
    rw [ι_D₁', K.ιTotal₂₃_eq c₂₃ c i₁ i₂ i₃ j h _ rfl, assoc, HomologicalComplex₂.ι_D₁]
    by_cases h₁ : c₁.Rel i₁ (c₁.next i₁)
    · by_cases h₂ : ComplexShape.π c₁ c₂₃ c (ComplexShape.next c₁ i₁,
        ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) = j'
      · rw [(K.int₂₃ c₂₃).d₁_eq c h₁ _ _ h₂, Linear.comp_units_smul,
          int₂₃_d, HomologicalComplex₂.ιTotal_map_assoc]
        congr 2
        symm
        apply ιTotal₂₃OrZero_eq
      · rw [(K.int₂₃ c₂₃).d₁_eq_zero' c h₁ _ _ h₂, comp_zero, K.d₁'_eq_zero' c₂₃ c h₁ _ _ _ h₂]
    · rw [K.d₁'_eq_zero c₂₃ c i₁ i₂ i₃ j' h₁, (K.int₂₃ c₂₃).d₁_eq_zero _ _ _ _ h₁, comp_zero])

lemma int₂₃_D₂ (j j' : J) : (int₂₃ K c₂₃).D₂ c j j' = K.D₂' c₂₃ c j j' + K.D₃' c₂₃ c j j' := by
  by_cases h₀ : c.Rel j j'
  · apply total₂₃.hom_ext
    intro i₁ i₂ i₃ h
    rw [Preadditive.comp_add, ι_D₂', ι_D₃', K.ιTotal₂₃_eq c₂₃ c i₁ i₂ i₃ j h _ rfl, assoc,
      HomologicalComplex₂.ι_D₂]
    let i₂₃ := ComplexShape.π c₂ c₃ c₂₃ ⟨i₂, i₃⟩
    by_cases h₁ : c₂₃.Rel i₂₃ (c₂₃.next i₂₃)
    · rw [(K.int₂₃ c₂₃).d₂_eq c i₁ h₁ j']; swap
      · rw [← c.next_eq' h₀, ← h, ComplexShape.next_π₂ c₁ c i₁ h₁]
      dsimp
      simp only [Preadditive.add_comp, smul_add, Preadditive.comp_add, Linear.comp_units_smul,
        HomologicalComplex₂.ι_D₁_assoc, HomologicalComplex₂.ι_D₂_assoc]
      congr 1
      · by_cases h₂ : c₂.Rel i₂ (c₂.next i₂)
        · rw [(K.X i₁).d₁_eq _ h₂ _ _ (ComplexShape.next_π₁ c₃ c₂₃ h₂ i₃).symm,
            Linear.units_smul_comp, assoc, smul_smul, K.d₂'_eq c₂₃ c i₁ h₂ i₃ j']; swap
          · rw [← c.next_eq' h₀, ← h, ComplexShape.next_π₂ c₁ c i₁ h₁,
              ComplexShape.next_π₁ c₃ c₂₃ h₂]
          congr 2
          symm
          apply K.ιTotal₂₃_eq
        · rw [(K.X i₁).d₁_eq_zero _ _ _ _ h₂, zero_comp, smul_zero, K.d₂'_eq_zero _ _ _ _ _ _ h₂]
      · by_cases h₂ : c₃.Rel i₃ (c₃.next i₃)
        · rw [(K.X i₁).d₂_eq _ _ h₂ _ (ComplexShape.next_π₂ c₂ c₂₃ i₂ h₂).symm,
            Linear.units_smul_comp, assoc, smul_smul, K.d₃'_eq c₂₃ c i₁ i₂ h₂ j']; swap
          · rw [← c.next_eq' h₀, ← h, ComplexShape.next_π₂ c₁ c i₁ h₁,
              ComplexShape.next_π₂ c₂ c₂₃ i₂ h₂]
          congr 2
          symm
          apply K.ιTotal₂₃_eq
        · rw [(K.X i₁).d₂_eq_zero _ _ _ _ h₂, zero_comp, smul_zero, K.d₃'_eq_zero _ _ _ _ _ _ h₂]
    · rw [(K.int₂₃ c₂₃).d₂_eq_zero _ _ _ _ h₁, K.d₂'_eq_zero, K.d₃'_eq_zero, zero_add, comp_zero]
      · intro h₂
        have H := ComplexShape.rel_π₂ c₂ c₂₃ i₂ h₂
        rw [c₂₃.next_eq' H] at h₁
        exact h₁ H
      · intro h₂
        have H := ComplexShape.rel_π₁ c₃ c₂₃ h₂ i₃
        rw [c₂₃.next_eq' H] at h₁
        exact h₁ H
  · rw [(K.int₂₃ c₂₃).D₂_shape _ _ _ h₀, K.D₂'_shape _ _ _ _ h₀, K.D₃'_shape _ _ _ _ h₀, zero_add]

@[simp]
lemma total₂₃_d (j j' : J) :
    (K.total₂₃ c₂₃ c).d j j' = K.D₁' c₂₃ c j j' + K.D₂' c₂₃ c j j' + K.D₃' c₂₃ c j j' := by
  dsimp [total₂₃]
  rw [int₂₃_D₁, int₂₃_D₂, add_assoc]

end

variable [K.HasInt₁₂ c₁₂] [K.HasInt₂₃ c₂₃] [K.HasTotal₁₂ c₁₂ c] [K.HasTotal₂₃ c₂₃ c]
  [ComplexShape.Associator c₁ c₂ c₃ c₁₂ c₂₃ c]

noncomputable def totalAssociatorX (j : J) : (K.total₁₂ c₁₂ c).X j ≅ (K.total₂₃ c₂₃ c).X j where
  hom := K.total₁₂Desc (fun i₁ i₂ i₃ h => K.ιTotal₂₃ c₂₃ c i₁ i₂ i₃ j
    (by rw [← h, ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c]))
  inv := K.total₂₃Desc (fun i₁ i₂ i₃ h => K.ιTotal₁₂ c₁₂ c i₁ i₂ i₃ j
    (by rw [← h, ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c]))

section

variable (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)

@[reassoc (attr := simp)]
lemma ιTotal₁₂OrZero_totalAssociatorX_hom :
    K.ιTotal₁₂OrZero c₁₂ c i₁ i₂ i₃ j ≫ (K.totalAssociatorX c₁₂ c₂₃ c j).hom =
      K.ιTotal₂₃OrZero c₂₃ c i₁ i₂ i₃ j := by
  by_cases h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) = j
  · dsimp [totalAssociatorX]
    rw [K.ιTotal₁₂OrZero_eq c₁₂ c i₁ i₂ i₃ j h, ι_total₁₂Desc,
      K.ιTotal₂₃OrZero_eq c₂₃ c i₁ i₂ i₃ j]
  · rw [K.ιTotal₁₂OrZero_eq_zero c₁₂ c i₁ i₂ i₃ j h, zero_comp,
      K.ιTotal₂₃OrZero_eq_zero c₂₃ c i₁ i₂ i₃ j]
    intro h'
    refine' h _
    rw [ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c, h']

@[reassoc (attr := simp)]
lemma totalAssociatorX_hom_d₁' :
    K.d₁ c₁₂ c i₁ i₂ i₃ j ≫ (K.totalAssociatorX c₁₂ c₂₃ c j).hom = K.d₁' c₂₃ c i₁ i₂ i₃ j := by
  dsimp [d₁, d₁']
  rw [Linear.units_smul_comp, assoc, ιTotal₁₂OrZero_totalAssociatorX_hom,
    ComplexShape.associator_ε₁_eq_mul c₁ c₂ c₃ c₁₂ c₂₃ c i₁ i₂ i₃]

@[reassoc (attr := simp)]
lemma totalAssociatorX_hom_d₂' :
    K.d₂ c₁₂ c i₁ i₂ i₃ j ≫ (K.totalAssociatorX c₁₂ c₂₃ c j).hom = K.d₂' c₂₃ c i₁ i₂ i₃ j := by
  dsimp [d₂, d₂']
  rw [Linear.units_smul_comp, assoc, ιTotal₁₂OrZero_totalAssociatorX_hom,
    ComplexShape.associator_ε₂_ε₁ c₁ c₂ c₃ c₁₂ c₂₃ c i₁ i₂ i₃]

@[reassoc (attr := simp)]
lemma totalAssociatorX_hom_d₃' :
    K.d₃ c₁₂ c i₁ i₂ i₃ j ≫ (K.totalAssociatorX c₁₂ c₂₃ c j).hom = K.d₃' c₂₃ c i₁ i₂ i₃ j := by
  dsimp [d₃, d₃']
  rw [Linear.units_smul_comp, assoc, ιTotal₁₂OrZero_totalAssociatorX_hom,
    ComplexShape.associator_ε₂_eq_mul c₁ c₂ c₃ c₁₂ c₂₃ c i₁ i₂ i₃]

end

@[reassoc]
lemma D₁_totalAssociatorX_hom (j j' : J) :
    K.D₁ c₁₂ c j j' ≫ (K.totalAssociatorX c₁₂ c₂₃ c j').hom =
      (K.totalAssociatorX c₁₂ c₂₃ c j).hom ≫ K.D₁' c₂₃ c j j' := by
  ext i₁ i₂ i₃ h
  dsimp [totalAssociatorX]
  simp only [ι_D₁_assoc, ι_total₁₂Desc_assoc, ι_D₁']
  apply totalAssociatorX_hom_d₁'

@[reassoc]
lemma D₂_totalAssociatorX_hom (j j' : J) :
    K.D₂ c₁₂ c j j' ≫ (K.totalAssociatorX c₁₂ c₂₃ c j').hom =
      (K.totalAssociatorX c₁₂ c₂₃ c j).hom ≫ K.D₂' c₂₃ c j j' := by
  ext i₁ i₂ i₃ h
  dsimp [totalAssociatorX]
  simp only [ι_D₂_assoc, ι_total₁₂Desc_assoc, ι_D₂']
  apply totalAssociatorX_hom_d₂'

@[reassoc]
lemma D₃_totalAssociatorX_hom (j j' : J) :
    K.D₃ c₁₂ c j j' ≫ (K.totalAssociatorX c₁₂ c₂₃ c j').hom =
      (K.totalAssociatorX c₁₂ c₂₃ c j).hom ≫ K.D₃' c₂₃ c j j' := by
  ext i₁ i₂ i₃ h
  dsimp [totalAssociatorX]
  simp only [ι_D₃_assoc, ι_total₁₂Desc_assoc, ι_D₃']
  apply totalAssociatorX_hom_d₃'

@[reassoc]
lemma totalAssociatorX_hom_d (j j' : J) :
    (K.totalAssociatorX c₁₂ c₂₃ c j).hom ≫ (K.total₂₃ c₂₃ c).d j j' =
      (K.total₁₂ c₁₂ c).d j j' ≫ (K.totalAssociatorX c₁₂ c₂₃ c j').hom := by
  simp only [total₂₃_d, Preadditive.comp_add, total₁₂_d, Preadditive.add_comp,
    D₁_totalAssociatorX_hom, D₂_totalAssociatorX_hom, D₃_totalAssociatorX_hom]

noncomputable def totalAssociator : K.total₁₂ c₁₂ c ≅ K.total₂₃ c₂₃ c :=
  HomologicalComplex.Hom.isoOfComponents (K.totalAssociatorX c₁₂ c₂₃ c)
    (fun j j' _ => K.totalAssociatorX_hom_d c₁₂ c₂₃ c j j')

end

end HomologicalComplex₃
