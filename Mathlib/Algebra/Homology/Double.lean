/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Homology.Single
import Mathlib.CategoryTheory.Yoneda

/-!
# A homological complex lying in two degrees

Given `c : ComplexShape ι`, distinct indices `i₀` and `i₁` such that `hi₀₁ : c.Rel i₀ i₁`,
we construct a homological complex `double f hi₀₁` for any morphism `f : X₀ ⟶ X₁`.
It consists of the objects `X₀` and `X₁` in degrees `i₀` and `i₁`, respectively,
with the differential `X₀ ⟶ X₁` given by `f`, and zero everywhere else.

-/

open CategoryTheory Category Limits ZeroObject Opposite

namespace HomologicalComplex

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]

variable {X₀ X₁ : C} (f : X₀ ⟶ X₁) {ι : Type*} {c : ComplexShape ι}
  {i₀ i₁ : ι} (hi₀₁ : c.Rel i₀ i₁)

open Classical
/-- Given a complex shape `c`, two indices `i₀` and `i₁` such that `c.Rel i₀ i₁`,
and `f : X₀ ⟶ X₁`, this is the homological complex which, if `i₀ ≠ i₁`, only
consists of the map `f` in degrees `i₀` and `i₁`, and zero everywhere else. -/
noncomputable def double : HomologicalComplex C c where
  X k := if k = i₀ then X₀ else if k = i₁ then X₁ else 0
  d k k' :=
    if hk : k = i₀ ∧ k' = i₁ ∧ i₀ ≠ i₁ then
      eqToHom (if_pos hk.1) ≫ f ≫ eqToHom (by
        dsimp [X]
        rw [if_neg, if_pos hk.2.1]
        rintro rfl
        exact hk.2.2 hk.2.1)
    else 0
  d_comp_d' := by
    rintro i j k hij hjk
    dsimp
    by_cases hi : i = i₀
    · subst hi
      by_cases hj : j = i₁
      · subst hj
        nth_rw 2 [dif_neg]
        · rw [comp_zero]
        · rintro ⟨rfl, _, h⟩
          exact h rfl
      · rw [dif_neg, zero_comp]
        rintro ⟨_, h, _⟩
        exact hj h
    · rw [dif_neg, zero_comp]
      rintro ⟨h, _, _⟩
      exact hi h
  shape i j hij := dif_neg (by
    rintro ⟨rfl, rfl, _⟩
    exact hij hi₀₁)

lemma isZero_double_X (k : ι) (h₀ : k ≠ i₀) (h₁ : k ≠ i₁) :
    IsZero ((double f hi₀₁).X k) := by
  dsimp [double]
  rw [if_neg h₀, if_neg h₁]
  exact Limits.isZero_zero C

/-- The isomorphism `(double f hi₀₁).X i₀ ≅ X₀`. -/
noncomputable def doubleXIso₀ : (double f hi₀₁).X i₀ ≅ X₀ :=
  eqToIso (dif_pos rfl)

/-- The isomorphism `(double f hi₀₁).X i₁ ≅ X₁`. -/
noncomputable def doubleXIso₁ (h : i₀ ≠ i₁) : (double f hi₀₁).X i₁ ≅ X₁ :=
  eqToIso (by
    dsimp [double]
    rw [if_neg h.symm, if_pos rfl])

lemma double_d (h : i₀ ≠ i₁) :
    (double f hi₀₁).d i₀ i₁ =
      (doubleXIso₀ f hi₀₁).hom ≫ f ≫ (doubleXIso₁ f hi₀₁ h).inv :=
  dif_pos ⟨rfl, rfl, h⟩

lemma double_d_eq_zero₀ (a b : ι) (ha : a ≠ i₀) :
    (double f hi₀₁).d a b = 0 :=
  dif_neg (by rintro ⟨h, _, _⟩; exact ha h)

lemma double_d_eq_zero₁ (a b : ι) (hb : b ≠ i₁) :
    (double f hi₀₁).d a b = 0 :=
  dif_neg (by rintro ⟨_, h, _⟩; exact hb h)

variable {f hi₀₁} in
@[ext]
lemma from_double_hom_ext {K : HomologicalComplex C c} {φ φ' : double f hi₀₁ ⟶ K}
    (h₀ : φ.f i₀ = φ'.f i₀) (h₁ : φ.f i₁ = φ'.f i₁) : φ = φ' := by
  ext k
  by_cases h : k = i₀ ∨ k = i₁
  · obtain rfl | rfl := h <;> assumption
  · simp only [not_or] at h
    apply (isZero_double_X f hi₀₁ k h.1 h.2).eq_of_src

variable {f hi₀₁} in
@[ext]
lemma to_double_hom_ext {K : HomologicalComplex C c} {φ φ' : K ⟶ double f hi₀₁}
    (h₀ : φ.f i₀ = φ'.f i₀) (h₁ : φ.f i₁ = φ'.f i₁) : φ = φ' := by
  ext k
  by_cases h : k = i₀ ∨ k = i₁
  · obtain rfl | rfl := h <;> assumption
  · simp only [not_or] at h
    apply (isZero_double_X f hi₀₁ k h.1 h.2).eq_of_tgt

section

variable {f} (h : i₀ ≠ i₁) {K : HomologicalComplex C c} (φ₀ : X₀ ⟶ K.X i₀) (φ₁ : X₁ ⟶ K.X i₁)
  (comm : φ₀ ≫ K.d i₀ i₁ = f ≫ φ₁)
  (hφ : ∀ (k : ι), c.Rel i₁ k → φ₁ ≫ K.d i₁ k = 0)

open Classical in
/-- Constructor for morphisms from a homological complex `double f hi₀₁`.  -/
noncomputable def mkHomFromDouble : double f hi₀₁ ⟶ K where
  f k :=
    if hk₀ : k = i₀ then
      eqToHom (by rw [hk₀]) ≫ (doubleXIso₀ f hi₀₁).hom ≫ φ₀ ≫ eqToHom (by rw [hk₀])
    else if hk₁ : k = i₁ then
      eqToHom (by rw [hk₁]) ≫ (doubleXIso₁ f hi₀₁ h).hom ≫ φ₁ ≫ eqToHom (by rw [hk₁])
    else 0
  comm' k₀ k₁ hk := by
    dsimp
    by_cases h₀ : k₀ = i₀
    · subst h₀
      rw [dif_pos rfl]
      obtain rfl := c.next_eq hk hi₀₁
      simp [dif_neg h.symm, dif_pos rfl, double_d f hi₀₁ h, comm]
    · rw [dif_neg h₀]
      by_cases h₁ : k₀ = i₁
      · subst h₁
        dsimp
        rw [if_pos rfl, comp_id, id_comp, assoc, hφ k₁ hk, comp_zero,
          double_d_eq_zero₀ _ _ _ _ h.symm, zero_comp]
      · apply (isZero_double_X f hi₀₁ k₀ h₀ h₁).eq_of_src

@[simp, reassoc]
lemma mkHomFromDouble_f₀ :
    (mkHomFromDouble hi₀₁ h φ₀ φ₁ comm hφ).f i₀ =
      (doubleXIso₀ f hi₀₁).hom ≫ φ₀ := by
  dsimp [mkHomFromDouble]
  rw [if_pos rfl, id_comp, comp_id]

@[simp, reassoc]
lemma mkHomFromDouble_f₁ :
    (mkHomFromDouble hi₀₁ h φ₀ φ₁ comm hφ).f i₁ =
      (doubleXIso₁ f hi₀₁ h).hom ≫ φ₁ := by
  dsimp [mkHomFromDouble]
  rw [dif_neg h.symm, if_pos rfl, id_comp, comp_id]

end

end HomologicalComplex
