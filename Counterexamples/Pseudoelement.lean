/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.CategoryTheory.Abelian.Pseudoelements
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# Pseudoelements and pullbacks
Borceux claims in Proposition 1.9.5 that the pseudoelement constructed in
`CategoryTheory.Abelian.Pseudoelement.pseudo_pullback` is unique. We show here that this claim is
false. This means in particular that we cannot have an extensionality principle for pullbacks in
terms of pseudoelements.

## Implementation details
The construction, suggested in https://mathoverflow.net/a/419951/7845, is the following.
We work in the category of `ModuleCat ℤ` and we consider the special case of `ℚ ⊞ ℚ` (that is the
pullback over the terminal object). We consider the pseudoelements associated to `x : ℚ ⟶ ℚ ⊞ ℚ`
given by `t ↦ (t, 2 * t)` and `y : ℚ ⟶ ℚ ⊞ ℚ` given by `t ↦ (t, t)`.

## Main results
* `Counterexample.exist_ne_and_fst_eq_fst_and_snd_eq_snd` : there are two
  pseudoelements `x y : ℚ ⊞ ℚ` such that `x ≠ y`, `biprod.fst x = biprod.fst y` and
  `biprod.snd x = biprod.snd y`.

## References
* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
-/


open CategoryTheory.Abelian CategoryTheory CategoryTheory.Limits ModuleCat LinearMap

namespace Counterexample

noncomputable section

open CategoryTheory.Abelian.Pseudoelement

/-- `x` is given by `t ↦ (t, 2 * t)`. -/
def x : Over (of ℤ ℚ ⊞ of ℤ ℚ) :=
  Over.mk (biprod.lift (𝟙 _) (2 • 𝟙 _))

/-- `y` is given by `t ↦ (t, t)`. -/
def y : Over (of ℤ ℚ ⊞ of ℤ ℚ) :=
  Over.mk (biprod.lift (𝟙 _) (𝟙 _))

/-- `biprod.fst ≫ x` is pseudoequal to `biprod.fst y`. -/
theorem fst_x_pseudo_eq_fst_y : PseudoEqual _ (app biprod.fst x) (app biprod.fst y) := by
  refine ⟨of ℤ ℚ, 𝟙 _, 𝟙 _, inferInstance, ?_, ?_⟩
  · exact (ModuleCat.epi_iff_surjective _).2 fun a => ⟨(a : ℚ), rfl⟩
  · dsimp [x, y]
    simp

/-- `biprod.snd ≫ x` is pseudoequal to `biprod.snd y`. -/
theorem snd_x_pseudo_eq_snd_y : PseudoEqual _ (app biprod.snd x) (app biprod.snd y) := by
  refine ⟨of ℤ ℚ, 𝟙 _, 2 • 𝟙 _, inferInstance, ?_, ?_⟩
  · refine (ModuleCat.epi_iff_surjective _).2 fun a => ⟨(show ℚ from a) / 2, ?_⟩
    simpa only [two_smul] using add_halves (show ℚ from a)
  · dsimp [x, y]
    refine ConcreteCategory.hom_ext _ _ fun a => ?_
    simp_rw [biprod.lift_snd]; rfl

-- Porting note: locally disable instance to avoid inferred/synthesized clash
attribute [-instance] AddCommGroup.toIntModule in
/-- `x` is not pseudoequal to `y`. -/
theorem x_not_pseudo_eq : ¬PseudoEqual _ x y := by
  intro h
  replace h := ModuleCat.eq_range_of_pseudoequal h
  dsimp [x, y] at h
  let φ := biprod.lift (𝟙 (of ℤ ℚ)) (2 • 𝟙 (of ℤ ℚ))
  have mem_range := mem_range_self φ.hom (1 : ℚ)
  rw [h] at mem_range
  obtain ⟨a, ha⟩ := mem_range
  rw [← ModuleCat.id_apply _ (φ (1 : ℚ)), ← biprod.total, ← LinearMap.comp_apply,
    ← ModuleCat.hom_comp, Preadditive.comp_add] at ha
  let π₁ := (biprod.fst : of ℤ ℚ ⊞ of ℤ ℚ ⟶ _)
  have ha₁ := congr_arg π₁ ha
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply] at ha₁
  simp only [π₁, φ, biprod.lift_fst, biprod.lift_fst_assoc, Category.id_comp,
    biprod.lift_snd_assoc, Linear.smul_comp, Preadditive.add_comp, BinaryBicone.inl_fst,
    BinaryBicone.inr_fst, smul_zero, add_zero] at ha₁
  let π₂ := (biprod.snd : of ℤ ℚ ⊞ of ℤ ℚ ⟶ _)
  have ha₂ := congr_arg π₂ ha
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply] at ha₂
  simp_all [π₂, φ]

attribute [local instance] Pseudoelement.setoid

open scoped Pseudoelement

/-- `biprod.fst ⟦x⟧ = biprod.fst ⟦y⟧`. -/
theorem fst_mk'_x_eq_fst_mk'_y :
    pseudoApply biprod.fst ⟦x⟧ = pseudoApply biprod.fst ⟦y⟧ :=
  Quotient.eq.2 fst_x_pseudo_eq_fst_y

/-- `biprod.snd ⟦x⟧ = biprod.snd ⟦y⟧`. -/
theorem snd_mk'_x_eq_snd_mk'_y :
    pseudoApply biprod.snd ⟦x⟧ = pseudoApply biprod.snd ⟦y⟧ :=
  Quotient.eq.2 snd_x_pseudo_eq_snd_y

-- Porting note: needs explicit type ascription `: Quotient <| Pseudoelement.setoid _`
-- for some reason the setoid instance isn't picked up automatically,
-- despite the local instance ~20 lines up
/-- `⟦x⟧ ≠ ⟦y⟧`. -/
theorem mk'_x_ne_mk'_y : (⟦x⟧ : Quotient <| Pseudoelement.setoid _) ≠ ⟦y⟧ :=
  fun h => x_not_pseudo_eq <| Quotient.eq'.1 h

/-- There are two pseudoelements `x y : ℚ ⊞ ℚ` such that `x ≠ y`, `biprod.fst x = biprod.fst y` and
`biprod.snd x = biprod.snd y`. -/
theorem exist_ne_and_fst_eq_fst_and_snd_eq_snd :
    ∃ x y, -- Porting note: removed type ascription `: of ℤ ℚ ⊞ of ℤ ℚ`, it gave an error about
           -- `Type` not having zero morphisms. jmc: I don't understand where the error came from
      x ≠ y ∧
        pseudoApply (biprod.fst : of ℤ ℚ ⊞ of ℤ ℚ ⟶ _) x = pseudoApply biprod.fst y ∧
          pseudoApply biprod.snd x = pseudoApply biprod.snd y :=
  ⟨⟦x⟧, ⟦y⟧, mk'_x_ne_mk'_y, fst_mk'_x_eq_fst_mk'_y, snd_mk'_x_eq_snd_mk'_y⟩

end

end Counterexample
