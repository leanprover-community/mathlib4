/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca

! This file was ported from Lean 3 source module pseudoelement
! leanprover-community/mathlib commit 328375597f2c0dd00522d9c2e5a33b6a6128feeb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Abelian.Pseudoelements
import Mathbin.Algebra.Category.Module.Biproducts

/-!
# Pseudoelements and pullbacks
Borceux claims in Proposition 1.9.5 that the pseudoelement constructed in
`category_theory.abelian.pseudoelement.pseudo_pullback` is unique. We show here that this claim is
false. This means in particular that we cannot have an extensionality principle for pullbacks in
terms of pseudoelements.

## Implementation details
The construction, suggested in https://mathoverflow.net/a/419951/7845, is the following.
We work in the category of `Module ℤ` and we consider the special case of `ℚ ⊞ ℚ` (that is the
pullback over the terminal object). We consider the pseudoelements associated to `x : ℚ ⟶ ℚ ⊞ ℚ`
given by `t ↦ (t, 2 * t)` and `y : ℚ ⟶ ℚ ⊞ ℚ` given by `t ↦ (t, t)`.

## Main results
* `category_theory.abelian.pseudoelement.exist_ne_and_fst_eq_fst_and_snd_eq_snd` : there are two
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
  Over.mk (biprod.lift (ofHom id) (ofHom (2 * id)))
#align counterexample.x Counterexample.x

/-- `y` is given by `t ↦ (t, t)`. -/
def y : Over (of ℤ ℚ ⊞ of ℤ ℚ) :=
  Over.mk (biprod.lift (ofHom id) (ofHom id))
#align counterexample.y Counterexample.y

/-- `biprod.fst ≫ x` is pseudoequal to `biprod.fst y`. -/
theorem fst_x_pseudo_eq_fst_y : PseudoEqual _ (app biprod.fst x) (app biprod.fst y) :=
  by
  refine' ⟨of ℤ ℚ, of_hom id, of_hom id, category_struct.id.epi (of ℤ ℚ), _, _⟩
  · exact (ModuleCat.epi_iff_surjective _).2 fun a => ⟨(a : ℚ), by simp⟩
  · dsimp [x, y]
    simp
#align counterexample.fst_x_pseudo_eq_fst_y Counterexample.fst_x_pseudo_eq_fst_y

/-- `biprod.snd ≫ x` is pseudoequal to `biprod.snd y`. -/
theorem snd_x_pseudo_eq_snd_y : PseudoEqual _ (app biprod.snd x) (app biprod.snd y) :=
  by
  refine' ⟨of ℤ ℚ, of_hom id, 2 • of_hom id, category_struct.id.epi (of ℤ ℚ), _, _⟩
  · refine' (ModuleCat.epi_iff_surjective _).2 fun a => ⟨(a / 2 : ℚ), _⟩
    simp only [two_smul, add_apply, of_hom_apply, id_coe, id.def]
    exact add_halves' (show ℚ from a)
  · dsimp [x, y]
    exact concrete_category.hom_ext _ _ fun a => by simpa
#align counterexample.snd_x_pseudo_eq_snd_y Counterexample.snd_x_pseudo_eq_snd_y

/-- `x` is not pseudoequal to `y`. -/
theorem x_not_pseudo_eq : ¬PseudoEqual _ x y :=
  by
  intro h
  replace h := Module.eq_range_of_pseudoequal h
  dsimp [x, y] at h 
  let φ := biprod.lift (of_hom (id : ℚ →ₗ[ℤ] ℚ)) (of_hom (2 * id))
  have mem_range := mem_range_self φ (1 : ℚ)
  rw [h] at mem_range 
  obtain ⟨a, ha⟩ := mem_range
  rw [← ModuleCat.id_apply (φ (1 : ℚ)), ← biprod.total, ← LinearMap.comp_apply, ← comp_def,
    preadditive.comp_add] at ha 
  let π₁ := (biprod.fst : of ℤ ℚ ⊞ of ℤ ℚ ⟶ _)
  have ha₁ := congr_arg π₁ ha
  simp only [← LinearMap.comp_apply, ← comp_def] at ha₁ 
  simp only [biprod.lift_fst, of_hom_apply, id_coe, id.def, preadditive.add_comp, category.assoc,
    biprod.inl_fst, category.comp_id, biprod.inr_fst, limits.comp_zero, add_zero] at ha₁ 
  let π₂ := (biprod.snd : of ℤ ℚ ⊞ of ℤ ℚ ⟶ _)
  have ha₂ := congr_arg π₂ ha
  simp only [← LinearMap.comp_apply, ← comp_def] at ha₂ 
  have : (2 : ℚ →ₗ[ℤ] ℚ) 1 = 1 + 1 := rfl
  simp only [ha₁, this, biprod.lift_snd, of_hom_apply, id_coe, id.def, preadditive.add_comp,
    category.assoc, biprod.inl_snd, limits.comp_zero, biprod.inr_snd, category.comp_id, zero_add,
    mul_apply, self_eq_add_left] at ha₂ 
  exact one_ne_zero' ℚ ha₂
#align counterexample.x_not_pseudo_eq Counterexample.x_not_pseudo_eq

attribute [local instance] pseudoelement.setoid

open scoped Pseudoelement

/-- `biprod.fst ⟦x⟧ = biprod.fst ⟦y⟧`. -/
theorem fst_mk'_x_eq_fst_mk'_y :
    (biprod.fst : of ℤ ℚ ⊞ of ℤ ℚ ⟶ _) ⟦x⟧ = (biprod.fst : of ℤ ℚ ⊞ of ℤ ℚ ⟶ _) ⟦y⟧ := by
  simpa only [abelian.pseudoelement.pseudo_apply_mk, Quotient.eq'] using fst_x_pseudo_eq_fst_y
#align counterexample.fst_mk_x_eq_fst_mk_y Counterexample.fst_mk'_x_eq_fst_mk'_y

/-- `biprod.snd ⟦x⟧ = biprod.snd ⟦y⟧`. -/
theorem snd_mk'_x_eq_snd_mk'_y :
    (biprod.snd : of ℤ ℚ ⊞ of ℤ ℚ ⟶ _) ⟦x⟧ = (biprod.snd : of ℤ ℚ ⊞ of ℤ ℚ ⟶ _) ⟦y⟧ := by
  simpa only [abelian.pseudoelement.pseudo_apply_mk, Quotient.eq'] using snd_x_pseudo_eq_snd_y
#align counterexample.snd_mk_x_eq_snd_mk_y Counterexample.snd_mk'_x_eq_snd_mk'_y

/-- `⟦x⟧ ≠ ⟦y⟧`. -/
theorem mk'_x_ne_mk'_y : ⟦x⟧ ≠ ⟦y⟧ := fun h => x_not_pseudo_eq <| Quotient.eq'.1 h
#align counterexample.mk_x_ne_mk_y Counterexample.mk'_x_ne_mk'_y

/-- There are two pseudoelements `x y : ℚ ⊞ ℚ` such that `x ≠ y`, `biprod.fst x = biprod.fst y` and
 `biprod.snd x = biprod.snd y`. -/
theorem exist_ne_and_fst_eq_fst_and_snd_eq_snd :
    ∃ x y : of ℤ ℚ ⊞ of ℤ ℚ,
      x ≠ y ∧
        (biprod.fst : of ℤ ℚ ⊞ of ℤ ℚ ⟶ _) x = (biprod.fst : of ℤ ℚ ⊞ of ℤ ℚ ⟶ _) y ∧
          (biprod.snd : of ℤ ℚ ⊞ of ℤ ℚ ⟶ _) x = (biprod.snd : of ℤ ℚ ⊞ of ℤ ℚ ⟶ _) y :=
  ⟨⟦x⟧, ⟦y⟧, mk'_x_ne_mk'_y, fst_mk'_x_eq_fst_mk'_y, snd_mk'_x_eq_snd_mk'_y⟩
#align counterexample.exist_ne_and_fst_eq_fst_and_snd_eq_snd Counterexample.exist_ne_and_fst_eq_fst_and_snd_eq_snd

end Counterexample

