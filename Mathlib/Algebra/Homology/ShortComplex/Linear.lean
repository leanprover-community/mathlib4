/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.ShortComplex.Preadditive
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Homology of linear categories

In this file, it is shown that if `C` is a `R`-linear category, then
`ShortComplex C` is a `R`-linear category. Various homological notions
are also shown to be linear.

-/

namespace CategoryTheory

open Category Limits

variable {R C : Type*} [Semiring R] [Category C] [Preadditive C] [Linear R C]

namespace ShortComplex

variable {S₁ S₂ : ShortComplex C}

attribute [local simp] Hom.comm₁₂ Hom.comm₂₃ mul_smul add_smul

instance : SMul R (S₁ ⟶ S₂) where
  smul a φ :=
    { τ₁ := a • φ.τ₁
      τ₂ := a • φ.τ₂
      τ₃ := a • φ.τ₃ }

@[simp] lemma smul_τ₁ (a : R) (φ : S₁ ⟶ S₂) : (a • φ).τ₁ = a • φ.τ₁ := rfl
@[simp] lemma smul_τ₂ (a : R) (φ : S₁ ⟶ S₂) : (a • φ).τ₂ = a • φ.τ₂ := rfl
@[simp] lemma smul_τ₃ (a : R) (φ : S₁ ⟶ S₂) : (a • φ).τ₃ = a • φ.τ₃ := rfl

instance : Module R (S₁ ⟶ S₂) where
  zero_smul := by cat_disch
  one_smul := by cat_disch
  smul_zero := by cat_disch
  smul_add := by cat_disch
  add_smul := by cat_disch
  mul_smul := by cat_disch

instance : Linear R (ShortComplex C) where

section LeftHomology

variable {φ φ' : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}

namespace LeftHomologyMapData

variable (γ : LeftHomologyMapData φ h₁ h₂)

/-- Given a left homology map data for morphism `φ`, this is the induced left homology
map data for `a • φ`. -/
@[simps]
def smul (a : R) : LeftHomologyMapData (a • φ) h₁ h₂ where
  φK := a • γ.φK
  φH := a • γ.φH

end LeftHomologyMapData

variable (h₁ h₂ φ)
variable (a : R)

@[simp]
lemma leftHomologyMap'_smul :
    leftHomologyMap' (a • φ) h₁ h₂ = a • leftHomologyMap' φ h₁ h₂ := by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  simp only [(γ.smul a).leftHomologyMap'_eq, LeftHomologyMapData.smul_φH, γ.leftHomologyMap'_eq]

@[simp]
lemma cyclesMap'_smul :
    cyclesMap' (a • φ) h₁ h₂ = a • cyclesMap' φ h₁ h₂ := by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  simp only [(γ.smul a).cyclesMap'_eq, LeftHomologyMapData.smul_φK, γ.cyclesMap'_eq]

section

variable [S₁.HasLeftHomology] [S₂.HasLeftHomology]

@[simp]
lemma leftHomologyMap_smul : leftHomologyMap (a • φ) = a • leftHomologyMap φ :=
  leftHomologyMap'_smul _ _ _ _

@[simp]
lemma cyclesMap_smul : cyclesMap (a • φ) = a • cyclesMap φ :=
  cyclesMap'_smul _ _ _ _

end

instance leftHomologyFunctor_linear [HasKernels C] [HasCokernels C] :
    Functor.Linear R (leftHomologyFunctor C) where

instance cyclesFunctor_linear [HasKernels C] [HasCokernels C] :
    Functor.Linear R (cyclesFunctor C) where

end LeftHomology

section RightHomology

variable {φ φ' : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData} {h₂ : S₂.RightHomologyData}

namespace RightHomologyMapData

variable (γ : RightHomologyMapData φ h₁ h₂)

/-- Given a right homology map data for morphism `φ`, this is the induced right homology
map data for `a • φ`. -/
@[simps]
def smul (a : R) : RightHomologyMapData (a • φ) h₁ h₂ where
  φQ := a • γ.φQ
  φH := a • γ.φH

end RightHomologyMapData

variable (h₁ h₂ φ)
variable (a : R)

@[simp]
lemma rightHomologyMap'_smul :
    rightHomologyMap' (a • φ) h₁ h₂ = a • rightHomologyMap' φ h₁ h₂ := by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  simp only [(γ.smul a).rightHomologyMap'_eq, RightHomologyMapData.smul_φH, γ.rightHomologyMap'_eq]

@[simp]
lemma opcyclesMap'_smul :
    opcyclesMap' (a • φ) h₁ h₂ = a • opcyclesMap' φ h₁ h₂ := by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  simp only [(γ.smul a).opcyclesMap'_eq, RightHomologyMapData.smul_φQ, γ.opcyclesMap'_eq]

section

variable [S₁.HasRightHomology] [S₂.HasRightHomology]

@[simp]
lemma rightHomologyMap_smul : rightHomologyMap (a • φ) = a • rightHomologyMap φ :=
  rightHomologyMap'_smul _ _ _ _

@[simp]
lemma opcyclesMap_smul : opcyclesMap (a • φ) = a • opcyclesMap φ :=
  opcyclesMap'_smul _ _ _ _

end

instance rightHomologyFunctor_linear [HasKernels C] [HasCokernels C] :
    Functor.Linear R (rightHomologyFunctor C) where

instance opcyclesFunctor_linear [HasKernels C] [HasCokernels C] :
    Functor.Linear R (opcyclesFunctor C) where

end RightHomology

section Homology

variable {φ φ' : S₁ ⟶ S₂} {h₁ : S₁.HomologyData} {h₂ : S₂.HomologyData}

namespace HomologyMapData

variable (γ : HomologyMapData φ h₁ h₂) (γ' : HomologyMapData φ' h₁ h₂)

/-- Given a homology map data for a morphism `φ`, this is the induced homology
map data for `a • φ`. -/
@[simps]
def smul (a : R) : HomologyMapData (a • φ) h₁ h₂ where
  left := γ.left.smul a
  right := γ.right.smul a

end HomologyMapData

variable (h₁ h₂)
variable (a : R)

@[simp]
lemma homologyMap'_smul :
    homologyMap' (a • φ) h₁ h₂ = a • homologyMap' φ h₁ h₂ :=
  leftHomologyMap'_smul _ _ _ _

variable (φ φ')

@[simp]
lemma homologyMap_smul [S₁.HasHomology] [S₂.HasHomology] :
    homologyMap (a • φ) = a • homologyMap φ :=
  homologyMap'_smul _ _ _

instance homologyFunctor_linear [CategoryWithHomology C] :
    Functor.Linear R (homologyFunctor C) where

end Homology

/-- Homotopy between morphisms of short complexes is compatible with the scalar multiplication. -/
@[simps]
def Homotopy.smul {φ₁ φ₂ : S₁ ⟶ S₂} (h : Homotopy φ₁ φ₂) (a : R) :
    Homotopy (a • φ₁) (a • φ₂) where
  h₀ := a • h.h₀
  h₁ := a • h.h₁
  h₂ := a • h.h₂
  h₃ := a • h.h₃
  comm₁ := by
    dsimp
    rw [h.comm₁]
    simp only [smul_add, Linear.comp_smul]
  comm₂ := by
    dsimp
    rw [h.comm₂]
    simp only [smul_add, Linear.comp_smul, Linear.smul_comp]
  comm₃ := by
    dsimp
    rw [h.comm₃]
    simp only [smul_add, Linear.smul_comp]

end ShortComplex

end CategoryTheory
