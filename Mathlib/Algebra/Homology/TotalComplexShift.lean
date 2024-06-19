/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import Mathlib.Algebra.Homology.TotalComplex

/-!
# Behaviour of the total complex with respect to shifts

There are two ways to shift objects in `HomologicalComplex₂ C (up ℤ) (up ℤ)`:
* by shifting the first indices (and changing signs of horizontal differentials),
which corresponds to the shift by `ℤ` on `CochainComplex (CochainComplex C ℤ) ℤ`.
* by shifting the second indices (and changing signs of vertical differentials).

These two sorts of shift functors shall be abbreviated as
`HomologicalComplex₂.shiftFunctor₁ C x` and
`HomologicalComplex₂.shiftFunctor₂ C y`.

In this file, for any `K : HomologicalComplex₂ C (up ℤ) (up ℤ)`, we define an isomorphism
`K.totalShift₁Iso x : ((shiftFunctor₁ C x).obj K).total (up ℤ) ≅ (K.total (up ℤ))⟦x⟧`
for any `x : ℤ` (which does not involve signs) and an isomorphism
`K.totalShift₂Iso y : ((shiftFunctor₂ C y).obj K).total (up ℤ) ≅ (K.total (up ℤ))⟦y⟧`
for any `y : ℤ` (which is given by the multiplication by `(p * y).negOnePow` on the
summand in bidegree `(p, q)` of `K`).

## TODO

- show that the two sorts of shift functors on bicomplexes "commute", but that signs
appear when we compare the compositions of the two compatibilities with the total complex functor.
- deduce compatiblities with shifts on both variables of the action of a
bifunctor on cochain complexes

-/

open CategoryTheory Category ComplexShape Limits

namespace HomologicalComplex₂

variable (C : Type*) [Category C] [Preadditive C]

/-- The shift on bicomplexes obtained by shifting the first indices (and changing the
sign of differentials). -/
abbrev shiftFunctor₁ (x : ℤ) :
    HomologicalComplex₂ C (up ℤ) (up ℤ) ⥤ HomologicalComplex₂ C (up ℤ) (up ℤ) :=
  shiftFunctor _ x

/-- The shift on bicomplexes obtained by shifting the second indices (and changing the
sign of differentials). -/
abbrev shiftFunctor₂ (y : ℤ) :
    HomologicalComplex₂ C (up ℤ) (up ℤ) ⥤ HomologicalComplex₂ C (up ℤ) (up ℤ) :=
  (shiftFunctor _ y).mapHomologicalComplex _

variable {C}
variable (K : HomologicalComplex₂ C (up ℤ) (up ℤ))

section

variable (x : ℤ) [K.HasTotal (up ℤ)] [((shiftFunctor₁ C x).obj K).HasTotal (up ℤ)]

/-- Auxiliary definition for `totalShift₁Iso`. -/
noncomputable def totalShift₁XIso (n n' : ℤ) (h : n + x = n') :
    (((shiftFunctor₁ C x).obj K).total (up ℤ)).X n ≅ (K.total (up ℤ)).X n' where
  hom := totalDesc _ (fun p q hpq => K.ιTotal (up ℤ) (p + x) q n' (by dsimp at hpq ⊢; omega))
  inv := totalDesc _ (fun p q hpq =>
    (K.XXIsoOfEq (Int.sub_add_cancel p x) rfl).inv ≫
      ((shiftFunctor₁ C x).obj K).ιTotal (up ℤ) (p - x) q n
        (by dsimp at hpq ⊢; omega))
  hom_inv_id := by
    ext p q h
    dsimp
    simp only [ι_totalDesc_assoc, CochainComplex.shiftFunctor_obj_X', ι_totalDesc, comp_id]
    exact ((shiftFunctor₁ C x).obj K).XXIsoOfEq_inv_ιTotal _ (by omega) rfl _ _

@[reassoc]
lemma D₁_totalShift₁XIso_hom (n₀ n₁ n₀' n₁' : ℤ) (h₀ : n₀ + x = n₀') (h₁ : n₁ + x = n₁') :
    ((shiftFunctor₁ C x).obj K).D₁ (up ℤ) n₀ n₁ ≫ (K.totalShift₁XIso x n₁ n₁' h₁).hom =
      x.negOnePow • ((K.totalShift₁XIso x n₀ n₀' h₀).hom ≫ K.D₁ (up ℤ) n₀' n₁') := by
  by_cases h : (up ℤ).Rel n₀ n₁
  · apply total.hom_ext
    intro p q hpq
    dsimp at h hpq
    dsimp [totalShift₁XIso]
    rw [ι_D₁_assoc, Linear.comp_units_smul, ι_totalDesc_assoc, ι_D₁,
      ((shiftFunctor₁ C x).obj K).d₁_eq _ rfl _ _ (by dsimp; omega),
      K.d₁_eq _ (show p + x + 1 = p + 1 + x by omega) _ _ (by dsimp; omega)]
    dsimp
    rw [one_smul, assoc, ι_totalDesc, one_smul, Linear.units_smul_comp]
  · rw [D₁_shape _ _ _ _ h, zero_comp, D₁_shape, comp_zero, smul_zero]
    intro h'
    apply h
    dsimp at h' ⊢
    omega

@[reassoc]
lemma D₂_totalShift₁XIso_hom (n₀ n₁ n₀' n₁' : ℤ) (h₀ : n₀ + x = n₀') (h₁ : n₁ + x = n₁') :
    ((shiftFunctor₁ C x).obj K).D₂ (up ℤ) n₀ n₁ ≫ (K.totalShift₁XIso x n₁ n₁' h₁).hom =
      x.negOnePow • ((K.totalShift₁XIso x n₀ n₀' h₀).hom ≫ K.D₂ (up ℤ) n₀' n₁') := by
  by_cases h : (up ℤ).Rel n₀ n₁
  · apply total.hom_ext
    intro p q hpq
    dsimp at h hpq
    dsimp [totalShift₁XIso]
    rw [ι_D₂_assoc, Linear.comp_units_smul, ι_totalDesc_assoc, ι_D₂,
      ((shiftFunctor₁ C x).obj K).d₂_eq _ _ rfl _ (by dsimp; omega),
      K.d₂_eq _ _ rfl _ (by dsimp; omega), smul_smul,
      Linear.units_smul_comp, assoc, ι_totalDesc]
    dsimp
    congr 1
    rw [add_comm p, Int.negOnePow_add, ← mul_assoc, Int.units_mul_self, one_mul]
  · rw [D₂_shape _ _ _ _ h, zero_comp, D₂_shape, comp_zero, smul_zero]
    intro h'
    apply h
    dsimp at h' ⊢
    omega

/-- The isomorphism `((shiftFunctor₁ C x).obj K).total (up ℤ) ≅ (K.total (up ℤ))⟦x⟧`
expressing the compatibility of the total complex with the shift on the first indices.
This isomorphism does not involve signs. -/
noncomputable def totalShift₁Iso :
    ((shiftFunctor₁ C x).obj K).total (up ℤ) ≅ (K.total (up ℤ))⟦x⟧ :=
  HomologicalComplex.Hom.isoOfComponents (fun n => K.totalShift₁XIso x n (n + x) rfl)
    (fun n n' _ => by
      dsimp
      simp only [Preadditive.add_comp, Preadditive.comp_add, smul_add,
        Linear.comp_units_smul, K.D₁_totalShift₁XIso_hom x n n' _ _ rfl rfl,
        K.D₂_totalShift₁XIso_hom x n n' _ _ rfl rfl])

end

section

variable (y : ℤ) [K.HasTotal (up ℤ)] [((shiftFunctor₂ C y).obj K).HasTotal (up ℤ)]

attribute [local simp] smul_smul

/-- Auxiliary definition for `totalShift₂Iso`. -/
noncomputable def totalShift₂XIso (n n' : ℤ) (h : n + y = n') :
    (((shiftFunctor₂ C y).obj K).total (up ℤ)).X n ≅ (K.total (up ℤ)).X n' where
  hom := totalDesc _ (fun p q hpq => (p * y).negOnePow • K.ιTotal (up ℤ) p (q + y) n'
    (by dsimp at hpq ⊢; omega))
  inv := totalDesc _ (fun p q hpq => (p * y).negOnePow •
    (K.XXIsoOfEq rfl (Int.sub_add_cancel q y)).inv ≫
      ((shiftFunctor₂ C y).obj K).ιTotal (up ℤ) p (q - y) n (by dsimp at hpq ⊢; omega))
  hom_inv_id := by
    ext p q h
    dsimp
    simp only [ι_totalDesc_assoc, Linear.units_smul_comp, ι_totalDesc, smul_smul,
      Int.units_mul_self, one_smul, comp_id]
    exact ((shiftFunctor₂ C y).obj K).XXIsoOfEq_inv_ιTotal _ rfl (by omega) _ _

@[reassoc]
lemma D₁_totalShift₂XIso_hom (n₀ n₁ n₀' n₁' : ℤ) (h₀ : n₀ + y = n₀') (h₁ : n₁ + y = n₁') :
    ((shiftFunctor₂ C y).obj K).D₁ (up ℤ) n₀ n₁ ≫ (K.totalShift₂XIso y n₁ n₁' h₁).hom =
      y.negOnePow • ((K.totalShift₂XIso y n₀ n₀' h₀).hom ≫ K.D₁ (up ℤ) n₀' n₁') := by
  by_cases h : (up ℤ).Rel n₀ n₁
  · apply total.hom_ext
    intro p q hpq
    dsimp at h hpq
    dsimp [totalShift₂XIso]
    rw [ι_D₁_assoc, Linear.comp_units_smul, ι_totalDesc_assoc, Linear.units_smul_comp,
      ι_D₁, smul_smul, ((shiftFunctor₂ C y).obj K).d₁_eq _ rfl _ _ (by dsimp; omega),
      K.d₁_eq _ rfl _ _ (by dsimp; omega)]
    dsimp
    rw [one_smul, one_smul, assoc, ι_totalDesc, Linear.comp_units_smul, ← Int.negOnePow_add]
    congr 2
    linarith
  · rw [D₁_shape _ _ _ _ h, zero_comp, D₁_shape, comp_zero, smul_zero]
    intro h'
    apply h
    dsimp at h' ⊢
    omega

@[reassoc]
lemma D₂_totalShift₂XIso_hom (n₀ n₁ n₀' n₁' : ℤ) (h₀ : n₀ + y = n₀') (h₁ : n₁ + y = n₁') :
    ((shiftFunctor₂ C y).obj K).D₂ (up ℤ) n₀ n₁ ≫ (K.totalShift₂XIso y n₁ n₁' h₁).hom =
      y.negOnePow • ((K.totalShift₂XIso y n₀ n₀' h₀).hom ≫ K.D₂ (up ℤ) n₀' n₁') := by
  by_cases h : (up ℤ).Rel n₀ n₁
  · apply total.hom_ext
    intro p q hpq
    dsimp at h hpq
    dsimp [totalShift₂XIso]
    rw [ι_D₂_assoc, Linear.comp_units_smul, ι_totalDesc_assoc, Linear.units_smul_comp,
      smul_smul, ι_D₂, ((shiftFunctor₂ C y).obj K).d₂_eq _ _ rfl _ (by dsimp; omega),
      K.d₂_eq _ _ (show q + y + 1 = q + 1 + y by omega) _ (by dsimp; omega),
      Linear.units_smul_comp, assoc, smul_smul, ι_totalDesc]
    dsimp
    rw [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul, smul_smul,
      ← Int.negOnePow_add, ← Int.negOnePow_add, ← Int.negOnePow_add,
      ← Int.negOnePow_add]
    congr 2
    omega
  · rw [D₂_shape _ _ _ _ h, zero_comp, D₂_shape, comp_zero, smul_zero]
    intro h'
    apply h
    dsimp at h' ⊢
    omega

/-- The isomorphism `((shiftFunctor₂ C y).obj K).total (up ℤ) ≅ (K.total (up ℤ))⟦y⟧`
expressing the compatibility of the total complex with the shift on the second indices.
This isomorphism involves signs: in the summand in degree `(p, q)` of `K`, it is given by the
multiplication by `(p * y).negOnePow`. -/
noncomputable def totalShift₂Iso :
    ((shiftFunctor₂ C y).obj K).total (up ℤ) ≅ (K.total (up ℤ))⟦y⟧ :=
  HomologicalComplex.Hom.isoOfComponents (fun n => K.totalShift₂XIso y n (n + y) rfl)
    (fun n n' _ => by
      dsimp
      simp only [Preadditive.add_comp, Preadditive.comp_add, smul_add,
        Linear.comp_units_smul, K.D₁_totalShift₂XIso_hom y n n' _ _ rfl rfl,
        K.D₂_totalShift₂XIso_hom y n n' _ _ rfl rfl])

end

end HomologicalComplex₂
