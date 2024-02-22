import Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import Mathlib.Algebra.Homology.TotalComplex
/-!
# Behaviour of the total complex with respect to shifts

There are two ways to shift objects in `HomologicalComplex₂ C (up ℤ) (up ℤ)`:
* by shifting the first indices (and changing signs of horizontal differentials),
with corresponds to the shift by `ℤ` on `CochainComplex (CochainComplex C ℤ) ℤ`.
* by shifting the second indices (and changing signs of vertical differentials).

These two sorts of shift functors shall be abbreviated as
`HomologicalComplex₂.shiftFunctor₁ C x` and
`HomologicalComplex₂.shiftFunctor₂ C y`.

In this file, for any `K : HomologicalComplex₂ C (up ℤ) (up ℤ)`,
we define an isomorphism
`K.totalShift₁Iso : ((shiftFunctor₁ C x).obj K).total (up ℤ) ≅ (K.total (up ℤ))⟦x⟧`
for any `x : ℤ` (which does not involve signs).

## TODO

- define `K.totalShift₂Iso : ((shiftFunctor₂ C y).obj K).total (up ℤ) ≅ (K.total (up ℤ))⟦y⟧`.
- show that the two sorts of shift functors on bicomplexes "commute", but that signs
appear when we compare the compositions of the two compatibilities with the total complex functor.
- deduce compatiblities with shifts on both variables of the action of a
bifunctor on cochain complexes

-/

open CategoryTheory Category ComplexShape Limits

namespace HomologicalComplex₂

variable (C : Type*) [Category C] [Preadditive C]

abbrev shiftFunctor₁ (x : ℤ) :
    HomologicalComplex₂ C (up ℤ) (up ℤ) ⥤ HomologicalComplex₂ C (up ℤ) (up ℤ) :=
  shiftFunctor _ x

abbrev shiftFunctor₂ (y : ℤ) :
    HomologicalComplex₂ C (up ℤ) (up ℤ) ⥤ HomologicalComplex₂ C (up ℤ) (up ℤ) :=
  (shiftFunctor _ y).mapHomologicalComplex _

variable {C}
variable (K : HomologicalComplex₂ C (up ℤ) (up ℤ))

section

variable (x : ℤ)  [K.HasTotal (up ℤ)] [((shiftFunctor₁ C x).obj K).HasTotal (up ℤ)]

noncomputable def totalShift₁XIso (n n' : ℤ) (h : n + x = n') :
    (((shiftFunctor₁ C x).obj K).total (up ℤ)).X n ≅ (K.total (up ℤ)).X n' where
  hom := totalDesc _ (fun p q hpq => K.ιTotal (up ℤ) (p + x) q n'
    (by rw [← h, ← hpq]; dsimp; linarith))
  inv := totalDesc _ (fun p q hpq =>
    (K.XXIsoOfEq (show p - x + x = p by exact Int.sub_add_cancel p x) rfl).inv ≫
      ((shiftFunctor₁ C x).obj K).ιTotal (up ℤ) (p - x) q n
        (by dsimp at hpq ⊢; omega))
  hom_inv_id := by
    ext p q h
    dsimp
    simp only [ι_totalDesc_assoc, CochainComplex.shiftFunctor_obj_X', ι_totalDesc, comp_id]
    exact ((shiftFunctor₁ C x).toPrefunctor.obj K).XXIsoOfEq_inv_ιTotal _ (by omega) rfl _ _

lemma D₁_totalShift₁XIso_hom (n₀ n₁ n₀' n₁' : ℤ) (h₀ : n₀ + x = n₀') (h₁ : n₁ + x = n₁') :
    ((shiftFunctor₁ C x).obj K).D₁ (up ℤ) n₀ n₁ ≫ (K.totalShift₁XIso x n₁ n₁' h₁).hom =
      x.negOnePow • ((K.totalShift₁XIso x n₀ n₀' h₀).hom ≫ K.D₁ (up ℤ) n₀' n₁') := by
  by_cases h : (up ℤ).Rel n₀ n₁
  · ext ⟨p, q⟩ hpq
    dsimp at h hpq
    dsimp [totalShift₁XIso]
    rw [ι_D₁_assoc, Linear.comp_units_smul, ι_totalDesc_assoc, ι_D₁,
      ((shiftFunctor₁ C x).obj K).d₁_eq _ rfl _ _ (by dsimp; omega),
      K.d₁_eq _ (show p + x + 1 = p + 1 + x by omega) _ _ (by dsimp; omega)]
    dsimp
    rw [one_smul, assoc, ι_totalDesc, one_smul]
    erw [Linear.smul_comp]
    rfl
  · rw [D₁_shape _ _ _ _ h, zero_comp, D₁_shape, comp_zero, smul_zero]
    intro h'
    apply h
    dsimp at h' ⊢
    omega

lemma D₂_totalShift₁XIso_hom (n₀ n₁ n₀' n₁' : ℤ) (h₀ : n₀ + x = n₀') (h₁ : n₁ + x = n₁') :
    ((shiftFunctor₁ C x).obj K).D₂ (up ℤ) n₀ n₁ ≫ (K.totalShift₁XIso x n₁ n₁' h₁).hom =
      x.negOnePow • ((K.totalShift₁XIso x n₀ n₀' h₀).hom ≫ K.D₂ (up ℤ) n₀' n₁') := by
  by_cases h : (up ℤ).Rel n₀ n₁
  · ext ⟨p, q⟩ hpq
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

noncomputable def totalShift₁Iso :
    ((shiftFunctor₁ C x).obj K).total (up ℤ) ≅ (K.total (up ℤ))⟦x⟧ :=
  HomologicalComplex.Hom.isoOfComponents (fun n => K.totalShift₁XIso x n (n + x) rfl)
    (fun n n' _ => by
      dsimp
      simp only [Preadditive.add_comp, Preadditive.comp_add, smul_add,
        Linear.comp_units_smul, K.D₁_totalShift₁XIso_hom x n n' _ _ rfl rfl,
        K.D₂_totalShift₁XIso_hom x n n' _ _ rfl rfl])

end

end HomologicalComplex₂
