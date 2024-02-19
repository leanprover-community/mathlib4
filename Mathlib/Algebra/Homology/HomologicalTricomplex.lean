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

open CategoryTheory Limits

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

@[simps!]
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

@[simps!]
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

noncomputable def ιTotal₁₂ (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
    (h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) = j) :
    ((K.X i₁).X i₂).X i₃ ⟶ (K.total₁₂ c₁₂ c).X j :=
  (K.X' i₃).ιTotal c₁₂ i₁ i₂ _ rfl ≫
    (K.int₁₂ c₁₂).ιTotal c (ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩) i₃ j h

@[reassoc]
lemma ιTotal₁₂_eq (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
    (h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) = j)
    (i₁₂ : I₁₂) (h' : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂) :
    K.ιTotal₁₂ c₁₂ c i₁ i₂ i₃ j h = (K.X' i₃).ιTotal c₁₂ i₁ i₂ i₁₂ h' ≫
    (K.int₁₂ c₁₂).ιTotal c i₁₂ i₃ j (by rw [← h', h]) := by
  subst h'
  rfl

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

end

section

variable [K.HasInt₂₃ c₂₃]

abbrev HasTotal₂₃ := (K.int₂₃ c₂₃).HasTotal c

variable [K.HasTotal₂₃ c₂₃ c]

noncomputable def total₂₃ : HomologicalComplex C c :=
  (K.int₂₃ c₂₃).total c

noncomputable def ιTotal₂₃ (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
    (h : ComplexShape.π c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) = j) :
    ((K.X i₁).X i₂).X i₃ ⟶ (K.total₂₃ c₂₃ c).X j :=
  (K.X i₁).ιTotal c₂₃ i₂ i₃ _ rfl ≫
    (K.int₂₃ c₂₃).ιTotal c i₁ (ComplexShape.π c₂ c₃ c₂₃ ⟨i₂, i₃⟩) j h

@[reassoc]
lemma ιTotal₂₃_eq (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
    (h : ComplexShape.π c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) = j)
    (i₂₃ : I₂₃) (h' : ComplexShape.π c₂ c₃ c₂₃ ⟨i₂, i₃⟩ = i₂₃) :
    K.ιTotal₂₃ c₂₃ c i₁ i₂ i₃ j h = (K.X i₁).ιTotal c₂₃ i₂ i₃ i₂₃ h' ≫
    (K.int₂₃ c₂₃).ιTotal c i₁ i₂₃ j (by rw [← h', h]) := by
  subst h'
  rfl

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

end

variable [K.HasInt₁₂ c₁₂] [K.HasInt₂₃ c₂₃] [K.HasTotal₁₂ c₁₂ c] [K.HasTotal₂₃ c₂₃ c]
  [ComplexShape.Associator c₁ c₂ c₃ c₁₂ c₂₃ c]

@[simps!]
noncomputable def totalAssociatorX (j : J) : (K.total₁₂ c₁₂ c).X j ≅ (K.total₂₃ c₂₃ c).X j where
  hom := K.total₁₂Desc (fun i₁ i₂ i₃ h => K.ιTotal₂₃ c₂₃ c i₁ i₂ i₃ j
    (by rw [← h, ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c]))
  inv := K.total₂₃Desc (fun i₁ i₂ i₃ h => K.ιTotal₁₂ c₁₂ c i₁ i₂ i₃ j
    (by rw [← h, ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c]))

/-@[reassoc]
lemma totalAssociatorX_hom_d (j j' : J) :
    (K.totalAssociatorX c₁₂ c₂₃ c j).hom ≫ (K.total₂₃ c₂₃ c).d j j' =
      (K.total₁₂ c₁₂ c).d j j' ≫ (K.totalAssociatorX c₁₂ c₂₃ c j').hom := by
  by_cases h₁ : c.Rel j j'
  · ext i₁ i₂ i₃ h₂
    dsimp
    sorry
  · simp only [HomologicalComplex.shape _ _ _ h₁, zero_comp, comp_zero]

noncomputable def totalAssociator : K.total₁₂ c₁₂ c ≅ K.total₂₃ c₂₃ c :=
  HomologicalComplex.Hom.isoOfComponents (K.totalAssociatorX c₁₂ c₂₃ c)
    (fun j j' _ => K.totalAssociatorX_hom_d c₁₂ c₂₃ c j j')-/

end

end HomologicalComplex₃
