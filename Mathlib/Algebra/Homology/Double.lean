/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HasNoLoop
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

section

variable {X₀ X₁ : C} (f : X₀ ⟶ X₁) {ι : Type*} {c : ComplexShape ι}
  {i₀ i₁ : ι} (hi₀₁ : c.Rel i₀ i₁)

open Classical in
/-- Given a complex shape `c`, two indices `i₀` and `i₁` such that `c.Rel i₀ i₁`,
and `f : X₀ ⟶ X₁`, this is the homological complex which, if `i₀ ≠ i₁`, only
consists of the map `f` in degrees `i₀` and `i₁`, and zero everywhere else. -/
noncomputable def double : HomologicalComplex C c where
  X k := if k = i₀ then X₀ else if k = i₁ then X₁ else 0
  d k k' :=
    if hk : k = i₀ ∧ k' = i₁ ∧ i₀ ≠ i₁ then
      eqToHom (if_pos hk.1) ≫ f ≫ eqToHom (by
        rw [if_neg, if_pos hk.2.1]
        aesop)
    else 0
  d_comp_d' := by
    rintro i j k hij hjk
    dsimp
    by_cases hi : i = i₀
    · subst hi
      by_cases hj : j = i₁
      · subst hj
        nth_rw 2 [dif_neg (by tauto)]
        rw [comp_zero]
      · rw [dif_neg (by tauto), zero_comp]
    · rw [dif_neg (by tauto), zero_comp]
  shape i j hij := dif_neg (by aesop)

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
  dif_neg (by tauto)

lemma double_d_eq_zero₁ (a b : ι) (hb : b ≠ i₁) :
    (double f hi₀₁).d a b = 0 :=
  dif_neg (by tauto)

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
/-- Constructor for morphisms from a homological complex `double f hi₀₁`. -/
noncomputable def mkHomFromDouble : double f hi₀₁ ⟶ K where
  f k :=
    if hk₀ : k = i₀ then
      eqToHom (by rw [hk₀]) ≫ (doubleXIso₀ f hi₀₁).hom ≫ φ₀ ≫ eqToHom (by rw [hk₀])
    else if hk₁ : k = i₁ then
      eqToHom (by rw [hk₁]) ≫ (doubleXIso₁ f hi₀₁ h).hom ≫ φ₁ ≫ eqToHom (by rw [hk₁])
    else 0
  comm' k₀ k₁ hk := by
    by_cases h₀ : k₀ = i₀
    · subst h₀
      rw [dif_pos rfl]
      obtain rfl := c.next_eq hk hi₀₁
      simp [dif_neg h.symm, double_d f hi₀₁ h, comm]
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

/-- Let `c : ComplexShape ι`, and `i₀` and `i₁` be distinct indices such
that `hi₀₁ : c.Rel i₀ i₁`, then for any `X : C`, the functor which sends
`K : HomologicalComplex C c` to `X ⟶ K.X i` is corepresentable by `double (𝟙 X) hi₀₁`. -/
@[simps -isSimp]
noncomputable def evalCompCoyonedaCorepresentableByDoubleId (h : i₀ ≠ i₁) (X : C) :
    (eval C c i₀ ⋙ coyoneda.obj (op X)).CorepresentableBy (double (𝟙 X) hi₀₁) where
  homEquiv {K} :=
    { toFun g := (doubleXIso₀ _ hi₀₁).inv ≫ g.f i₀
      invFun φ₀ := mkHomFromDouble _ h φ₀ (φ₀ ≫ K.d i₀ i₁) (by simp) (by simp)
      left_inv g := by
        ext
        · simp
        · simp [double_d _ _ h]
      right_inv _ := by simp }
  homEquiv_comp _ _ := by simp

end

variable {ι : Type*} (c : ComplexShape ι)

/-- If `i` has no successor for the complex shape `c`,
then for any `X : C`, the functor which sends `K : HomologicalComplex C c`
to `X ⟶ K.X i` is corepresentable by `(single C c i).obj X`. -/
@[simps -isSimp]
noncomputable def evalCompCoyonedaCorepresentableBySingle (i : ι) [DecidableEq ι]
    (hi : ∀ (j : ι), ¬ c.Rel i j) (X : C) :
    (eval C c i ⋙ coyoneda.obj (op X)).CorepresentableBy ((single C c i).obj X) where
  homEquiv {K} :=
    { toFun g := (singleObjXSelf c i X).inv ≫ g.f i
      invFun f := mkHomFromSingle f (fun j hj ↦ (hi j hj).elim)
      left_inv g := by cat_disch
      right_inv f := by simp }
  homEquiv_comp := by simp

variable [c.HasNoLoop]

open Classical in
/-- Given a complex shape `c : ComplexShape ι` (with no loop), `X : C` and `j : ι`,
this is a quite explicit choice of corepresentative of the functor which sends
`K : HomologicalComplex C c` to `X ⟶ K.X j`. -/
noncomputable def evalCompCoyonedaCorepresentative (X : C) (j : ι) :
    HomologicalComplex C c :=
  if hj : ∃ (k : ι), c.Rel j k then
    double (𝟙 X) hj.choose_spec
  else (single C c j).obj X

/-- If a complex shape `c : ComplexShape ι` has no loop,
then for any `X : C` and `j : ι`, the functor which sends `K : HomologicalComplex C c`
to `X ⟶ K.X j` is corepresentable. -/
noncomputable def evalCompCoyonedaCorepresentable (X : C) (j : ι) :
    (eval C c j ⋙ coyoneda.obj (op X)).CorepresentableBy
      (evalCompCoyonedaCorepresentative c X j) := by
  dsimp [evalCompCoyonedaCorepresentative]
  classical
  split_ifs with h
  · exact evalCompCoyonedaCorepresentableByDoubleId _
      (fun hj ↦ c.not_rel_of_eq hj h.choose_spec) _
  · apply evalCompCoyonedaCorepresentableBySingle
    obtain _ | _ := c.exists_distinct_prev_or j <;> tauto

instance (X : C) (j : ι) : (eval C c j ⋙ coyoneda.obj (op X)).IsCorepresentable where
  has_corepresentation := ⟨_, ⟨evalCompCoyonedaCorepresentable c X j⟩⟩

end HomologicalComplex
