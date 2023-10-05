/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.ShortComplex.Homology
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Homology of preadditive categories

In this file, it is shown that if `C` is a preadditive category, then
`ShortComplex C` is a preadditive category.

TODO: Introduce the notion of homotopy of morphisms of short complexes.

-/

namespace CategoryTheory

open Category Limits Preadditive

variable {C : Type*} [Category C] [Preadditive C]

namespace ShortComplex

variable {S₁ S₂ S₃ : ShortComplex C}

attribute [local simp] Hom.comm₁₂ Hom.comm₂₃

instance : Add (S₁ ⟶ S₂) where
  add φ φ' :=
    { τ₁ := φ.τ₁ + φ'.τ₁
      τ₂ := φ.τ₂ + φ'.τ₂
      τ₃ := φ.τ₃ + φ'.τ₃ }

instance : Sub (S₁ ⟶ S₂) where
  sub φ φ' :=
    { τ₁ := φ.τ₁ - φ'.τ₁
      τ₂ := φ.τ₂ - φ'.τ₂
      τ₃ := φ.τ₃ - φ'.τ₃ }

instance : Neg (S₁ ⟶ S₂) where
  neg φ :=
    { τ₁ := -φ.τ₁
      τ₂ := -φ.τ₂
      τ₃ := -φ.τ₃ }

instance : AddCommGroup (S₁ ⟶ S₂) where
  add_assoc := fun a b c => by ext <;> apply add_assoc
  add_zero := fun a => by ext <;> apply add_zero
  zero_add := fun a => by ext <;> apply zero_add
  add_left_neg := fun a => by ext <;> apply add_left_neg
  add_comm := fun a b => by ext <;> apply add_comm
  sub_eq_add_neg := fun a b => by ext <;> apply sub_eq_add_neg

@[simp] lemma add_τ₁ (φ φ' : S₁ ⟶ S₂) : (φ + φ').τ₁ = φ.τ₁ + φ'.τ₁ := rfl
@[simp] lemma add_τ₂ (φ φ' : S₁ ⟶ S₂) : (φ + φ').τ₂ = φ.τ₂ + φ'.τ₂ := rfl
@[simp] lemma add_τ₃ (φ φ' : S₁ ⟶ S₂) : (φ + φ').τ₃ = φ.τ₃ + φ'.τ₃ := rfl
@[simp] lemma sub_τ₁ (φ φ' : S₁ ⟶ S₂) : (φ - φ').τ₁ = φ.τ₁ - φ'.τ₁ := rfl
@[simp] lemma sub_τ₂ (φ φ' : S₁ ⟶ S₂) : (φ - φ').τ₂ = φ.τ₂ - φ'.τ₂ := rfl
@[simp] lemma sub_τ₃ (φ φ' : S₁ ⟶ S₂) : (φ - φ').τ₃ = φ.τ₃ - φ'.τ₃ := rfl
@[simp] lemma neg_τ₁ (φ : S₁ ⟶ S₂) : (-φ).τ₁ = -φ.τ₁ := rfl
@[simp] lemma neg_τ₂ (φ : S₁ ⟶ S₂) : (-φ).τ₂ = -φ.τ₂ := rfl
@[simp] lemma neg_τ₃ (φ : S₁ ⟶ S₂) : (-φ).τ₃ = -φ.τ₃ := rfl

instance : Preadditive (ShortComplex C) where

section LeftHomology

variable {φ φ' : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}

namespace LeftHomologyMapData

variable (γ : LeftHomologyMapData φ h₁ h₂) (γ' : LeftHomologyMapData φ' h₁ h₂)

/-- Given a left homology map data for morphism `φ`, this is induced left homology
map data for `-φ`. -/
@[simps]
def neg : LeftHomologyMapData (-φ) h₁ h₂ where
  φK := -γ.φK
  φH := -γ.φH

/-- Given left homology map data for morphisms `φ` and `φ'`, this is induced left homology
map data for `φ + φ'`. -/
@[simps]
def add : LeftHomologyMapData (φ + φ') h₁ h₂ where
  φK := γ.φK + γ'.φK
  φH := γ.φH + γ'.φH

end LeftHomologyMapData

variable (h₁ h₂)

@[simp]
lemma leftHomologyMap'_neg :
    leftHomologyMap' (-φ) h₁ h₂ = -leftHomologyMap' φ h₁ h₂ := by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  simp only [γ.leftHomologyMap'_eq, γ.neg.leftHomologyMap'_eq, LeftHomologyMapData.neg_φH]

@[simp]
lemma cyclesMap'_neg :
    cyclesMap' (-φ) h₁ h₂ = -cyclesMap' φ h₁ h₂ := by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  simp only [γ.cyclesMap'_eq, γ.neg.cyclesMap'_eq, LeftHomologyMapData.neg_φK]

@[simp]
lemma leftHomologyMap'_add :
    leftHomologyMap' (φ + φ') h₁ h₂ = leftHomologyMap' φ h₁ h₂ +
      leftHomologyMap' φ' h₁ h₂ := by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  have γ' : LeftHomologyMapData φ' h₁ h₂ := default
  simp only [γ.leftHomologyMap'_eq, γ'.leftHomologyMap'_eq,
    (γ.add γ').leftHomologyMap'_eq, LeftHomologyMapData.add_φH]

@[simp]
lemma cyclesMap'_add :
    cyclesMap' (φ + φ') h₁ h₂ = cyclesMap' φ h₁ h₂ +
      cyclesMap' φ' h₁ h₂ := by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  have γ' : LeftHomologyMapData φ' h₁ h₂ := default
  simp only [γ.cyclesMap'_eq, γ'.cyclesMap'_eq,
    (γ.add γ').cyclesMap'_eq, LeftHomologyMapData.add_φK]

@[simp]
lemma leftHomologyMap'_sub :
    leftHomologyMap' (φ - φ') h₁ h₂ = leftHomologyMap' φ h₁ h₂ -
      leftHomologyMap' φ' h₁ h₂ := by
  simp only [sub_eq_add_neg, leftHomologyMap'_add, leftHomologyMap'_neg]

@[simp]
lemma cyclesMap'_sub :
    cyclesMap' (φ - φ') h₁ h₂ = cyclesMap' φ h₁ h₂ -
      cyclesMap' φ' h₁ h₂ := by
  simp only [sub_eq_add_neg, cyclesMap'_add, cyclesMap'_neg]

variable (φ φ')

section

variable [S₁.HasLeftHomology] [S₂.HasLeftHomology]

@[simp]
lemma leftHomologyMap_neg : leftHomologyMap (-φ)  = -leftHomologyMap φ :=
  leftHomologyMap'_neg _ _

@[simp]
lemma cyclesMap_neg : cyclesMap (-φ) = -cyclesMap φ :=
  cyclesMap'_neg _ _

@[simp]
lemma leftHomologyMap_add : leftHomologyMap (φ + φ')  = leftHomologyMap φ + leftHomologyMap φ' :=
  leftHomologyMap'_add _ _

@[simp]
lemma cyclesMap_add : cyclesMap (φ + φ') = cyclesMap φ + cyclesMap φ' :=
  cyclesMap'_add _ _

@[simp]
lemma leftHomologyMap_sub : leftHomologyMap (φ - φ') = leftHomologyMap φ - leftHomologyMap φ' :=
  leftHomologyMap'_sub  _ _

@[simp]
lemma cyclesMap_sub : cyclesMap (φ - φ') = cyclesMap φ - cyclesMap φ' :=
  cyclesMap'_sub _ _

end

instance leftHomologyFunctor_additive [HasKernels C] [HasCokernels C] :
  (leftHomologyFunctor C).Additive where

instance cyclesFunctor_additive [HasKernels C] [HasCokernels C] :
  (cyclesFunctor C).Additive where

end LeftHomology

end ShortComplex

end CategoryTheory
