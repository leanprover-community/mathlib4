/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Endofunctor.Pointed.Algebra
public import Mathlib.CategoryTheory.Presentable.LocallyPresentable
public import Mathlib.CategoryTheory.Presentable.PreservesCardinalPresentable

import Mathlib.CategoryTheory.Endofunctor.Accessible
import Mathlib.CategoryTheory.Endofunctor.Pointed.Limits
import Mathlib.CategoryTheory.Endofunctor.Limits
import Mathlib.CategoryTheory.Equifier.Accessible
import Mathlib.CategoryTheory.Inserter.Accessible
import Mathlib.CategoryTheory.Presentable.Adjunction
import Mathlib.CategoryTheory.Presentable.SharplyLT.Lemmas

/-! # Accessibility of categories of (co)algebra

In this file, we show that categories of (co)algebras are accessible in good situations, as well
as the corresponding categories of (co)pointed (co)algebras.

In the unpointed case, this is obtained by identifying `Algebra F` with `Inserter F (𝟭 C)` and
using the theorem that categories of inserters are accessible in good situations
(see the file `Mathlib.CategoryTheory.Inserter.Accessible` what "good situations" refers to
exactly).

In the pointed case, this is obtained by realizing the object property `σ` as an equifier of a
well-chosen pair of endofunctors.
-/

universe w

namespace CategoryTheory.Endofunctor

variable {C : Type*} [Category* C] (F : C ⥤ C)

namespace Algebra.Pointed

/-- Construct a natural transformation from a pointing of an endofunctor -/
def φ₀ (σ : 𝟭 C ⟶ F) : forget F ⟶ forget F where
  app x := σ.app x.a ≫ x.str
  naturality x y f := by simp [reassoc_of% σ.naturality f.f]

lemma pointed_eq_equifier (σ : 𝟭 C ⟶ F) : pointed σ = equifier (φ₀ F σ) (𝟙 (forget F)) := rfl

public section

variable (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalAccessibleCategory C κ] [F.IsCardinalAccessible κ] [F.PreservesCardinalPresentable κ]
    (Λ : Type*) [Nonempty Λ] [LinearOrder Λ] [SuccOrder Λ] [WellFoundedLT Λ] [NoMaxOrder Λ]
    (hΛ : HasCardinalLT Λ κ) [Limits.HasColimitsOfShape Λ C] [Limits.PreservesColimitsOfShape Λ F]
include Λ hΛ

variable {F} (σ : 𝟭 C ⟶ F)

/-- Let `F : C ⥤ C` be an endofunctor of a category and assume that
- `F` is κ-accessible
- `F` preserves κ-presentable objects
- There exists an infinite well-order Λ of cardinality < κ such that `C` admits Λ-indexed colimits
  and `F` preserves them.

Then, the class of pointed algebras such that the underlying object of `C` is κ-presentable is a
κ-filtered generator for the category of pointed `F`-algebras for all pointing
`σ : 𝟭 C ⟶ F`. -/
theorem isCardinalFilteredGenerator :
    ((isCardinalPresentable (Algebra F) κ).inverseImage
      (Pointed.ι σ)).IsCardinalFilteredGenerator κ := by
  let e₁ := ObjectProperty.fullSubcategoryCongr (pointed_eq_equifier F σ)
  have : IsCardinalAccessibleCategory (Algebra F) κ :=
    Algebra.isCardinalAccessibleCategory F κ Λ hΛ
  have : (forget F).PreservesCardinalPresentable κ :=
    Algebra.preservesCardinalPresentable_forget F κ Λ hΛ
  convert e₁.toAdjunction'.isCardinalFilteredGenerator <|
    Equifier.isCardinalFilteredGenerator_inverseImage_isCardinalPresentable κ _ _ Λ hΛ
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp only [ObjectProperty.prop_inverseImage_iff, ObjectProperty.ι_obj,
      ObjectProperty.prop_map_iff] at h ⊢
    use e₁.functor.obj x
    exact ⟨h, ⟨.refl _⟩⟩
  · simp only [ObjectProperty.prop_map_iff, ObjectProperty.prop_inverseImage_iff,
    ObjectProperty.ι_obj] at h ⊢
    obtain ⟨X, q, ⟨e⟩⟩ := h
    let e' := (ι _).mapIso e
    simp only [ι, ObjectProperty.fullSubcategoryCongr_inverse, ObjectProperty.ι_obj,
      ObjectProperty.ιOfLE_obj_obj, e₁] at e'
    exact ObjectProperty.IsClosedUnderIsomorphisms.of_iso e' q

/-- Let `F : C ⥤ C` be an endofunctor of a category and assume that
- `F` is κ-accessible
- `F` preserves κ-presentable objects
- There exists an infinite well-order Λ of cardinality < κ such that `C` admits Λ-indexed colimits
  and `F` preserves them.

Then, the category of pointed `F`-algebras is accessible for all pointing `σ : 𝟭 C ⟶ F`. -/
theorem isCardinalAccessibleCategory :
    IsCardinalAccessibleCategory (Pointed σ) κ :=
  have : IsCardinalAccessibleCategory (Algebra F) κ :=
    Algebra.isCardinalAccessibleCategory F κ Λ hΛ
  have : (forget F).PreservesCardinalPresentable κ :=
    Algebra.preservesCardinalPresentable_forget F κ Λ hΛ
  have : IsCardinalAccessibleCategory (Equifier (φ₀ F σ) (𝟙 (forget F))) κ :=
    Equifier.isCardinalAccessibleCategory κ _ _ Λ hΛ
  (ObjectProperty.fullSubcategoryCongr
    (pointed_eq_equifier F σ)).symm.isCardinalAccessibleCategory κ

omit Λ hΛ in
instance isCardinalAccessible_ι : (Pointed.ι σ).IsCardinalAccessible κ := by
  constructor
  intro J _ _
  have : Limits.HasColimitsOfShape J C :=
    hasColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ J
  have : Limits.PreservesColimitsOfShape J F :=
    Functor.preservesColimitsOfShape_of_isCardinalAccessible _ κ _
  infer_instance

theorem isCardinalPresentable_eq :
    isCardinalPresentable (Pointed σ) κ =
      (isCardinalPresentable C κ).inverseImage (ι σ ⋙ forget F) := by
  have := isCardinalFilteredGenerator κ Λ hΛ σ
  rw [this.isPresentable_eq_retractClosure,
    ObjectProperty.inverseImage_comp,
    ObjectProperty.retractClosure_eq_self,
    Algebra.isCardinalPresentable_eq _ κ Λ hΛ]

theorem preservesCardinalPresentable_ι :
    (ι σ).PreservesCardinalPresentable κ := by
  constructor
  rw [isCardinalPresentable_eq κ Λ hΛ,
    Algebra.isCardinalPresentable_eq _ κ Λ hΛ,
    ObjectProperty.inverseImage_comp]

end

/-- Let `F` be an accessible endofunctor of an accessible category.
The category of `F`-coalgebras is accessible. -/
public instance [IsAccessibleCategory.{w} C] [F.IsAccessible.{w}] (σ : 𝟭 C ⟶ F) :
    IsAccessibleCategory.{w} (Pointed σ) :=
  (ObjectProperty.fullSubcategoryCongr
    (pointed_eq_equifier F σ)).symm.isAccessibleCategory

public instance [IsAccessibleCategory.{w} C] [F.IsAccessible.{w}] (σ : 𝟭 C ⟶ F) :
    (ι σ).IsAccessible.{w} := by
  obtain ⟨κ₀, _, _⟩ := IsAccessibleCategory.exists_cardinal C
  obtain ⟨κ, _, _⟩ := Functor.IsAccessible.exists_cardinal F
  obtain ⟨κ₁, _, h₁, h₂⟩ := Cardinal.SharplyLT.exists_of_pair κ₀ κ
  refine ⟨κ₁, inferInstance, ⟨fun J _ _ ↦ ?_⟩⟩
  have : IsCardinalAccessibleCategory C κ₁ := h₁.isCardinalAccessibleCategory C
  have : Limits.HasColimitsOfShape J C :=
    hasColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ₁ J
  have : F.IsCardinalAccessible κ₁ := Functor.isCardinalAccessible_of_le _ h₂.le
  have : Limits.PreservesColimitsOfShape J F :=
    Functor.IsCardinalAccessible.preservesColimitOfShape κ₁ J
  infer_instance

end Algebra.Pointed

namespace Coalgebra.Copointed

/-- Construct a natural transformation from a copointing of an endofunctor -/
def φ₀ (σ : F ⟶ 𝟭 C) : forget F ⟶ forget F where
  app x := x.str ≫ σ.app x.V
  naturality x y f := by simp [← dsimp% σ.naturality f.f, -NatTrans.naturality]

lemma copointed_eq_equifier (σ : F ⟶ 𝟭 C) : copointed σ = equifier (φ₀ F σ) (𝟙 (forget F)) := rfl

public section

variable (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalAccessibleCategory C κ] [F.IsCardinalAccessible κ]
    (Λ : Type*) [Nonempty Λ] [LinearOrder Λ] [SuccOrder Λ] [WellFoundedLT Λ] [NoMaxOrder Λ]
    (hΛ : HasCardinalLT Λ κ) [Limits.HasColimitsOfShape Λ C] [Limits.PreservesColimitsOfShape Λ F]

include Λ hΛ

variable {F} (σ : F ⟶ 𝟭 C)

/-- Let `F : C ⥤ C` be an endofunctor of a category and assume that
- `F` is κ-accessible
- There exists an infinite well-order Λ of cardinality < κ such that `C` admits Λ-indexed colimits
  and `F` preserves them.

Then, the class of copointed coalgebras such that the underlying object of `C` is κ-presentable is a
κ-filtered generator for the category of copointed `F`-coalgebras for all copointing
`σ : F ⟶ 𝟭 C`. -/
theorem isCardinalFilteredGenerator :
    ((isCardinalPresentable (Coalgebra F) κ).inverseImage
      (Copointed.ι σ)).IsCardinalFilteredGenerator κ := by
  let e₁ := ObjectProperty.fullSubcategoryCongr (copointed_eq_equifier F σ)
  have : IsCardinalAccessibleCategory (Coalgebra F) κ :=
    Coalgebra.isCardinalAccessibleCategory F κ Λ hΛ
  have : (forget F).PreservesCardinalPresentable κ :=
    Coalgebra.preservesCardinalPresentable_forget F κ Λ hΛ
  convert e₁.toAdjunction'.isCardinalFilteredGenerator <|
    Equifier.isCardinalFilteredGenerator_inverseImage_isCardinalPresentable κ _ _ Λ hΛ
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp only [ObjectProperty.prop_inverseImage_iff, ObjectProperty.ι_obj,
      ObjectProperty.prop_map_iff] at h ⊢
    use e₁.functor.obj x
    exact ⟨h, ⟨.refl _⟩⟩
  · simp only [ObjectProperty.prop_map_iff, ObjectProperty.prop_inverseImage_iff,
    ObjectProperty.ι_obj] at h ⊢
    obtain ⟨X, q, ⟨e⟩⟩ := h
    let e' := (ι _).mapIso e
    simp only [ι, ObjectProperty.fullSubcategoryCongr_inverse, ObjectProperty.ι_obj,
      ObjectProperty.ιOfLE_obj_obj, e₁] at e'
    exact ObjectProperty.IsClosedUnderIsomorphisms.of_iso e' q

/-- Let `F : C ⥤ C` be an endofunctor of a category and assume that
- `F` is κ-accessible
- There exists an infinite well-order Λ of cardinality < κ such that `C` admits Λ-indexed colimits
  and `F` preserves them.

Then, the category of pointed `F`-algebras is accessible for all pointing `σ : 𝟭 C ⟶ F`. -/
theorem isCardinalAccessibleCategory :
    IsCardinalAccessibleCategory (Copointed σ) κ :=
  have : IsCardinalAccessibleCategory (Coalgebra F) κ :=
    Coalgebra.isCardinalAccessibleCategory F κ Λ hΛ
  have : (forget F).PreservesCardinalPresentable κ :=
    Coalgebra.preservesCardinalPresentable_forget F κ Λ hΛ
  have : IsCardinalAccessibleCategory (Equifier (φ₀ F σ) (𝟙 (forget F))) κ :=
    Equifier.isCardinalAccessibleCategory κ _ _ Λ hΛ
  (ObjectProperty.fullSubcategoryCongr
    (copointed_eq_equifier F σ)).symm.isCardinalAccessibleCategory κ

omit Λ hΛ in
instance isCardinalAccessible_ι : (ι σ).IsCardinalAccessible κ := by
  constructor
  intro J _ _
  have : Limits.HasColimitsOfShape J C :=
    hasColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ J
  have : Limits.PreservesColimitsOfShape J F :=
    Functor.preservesColimitsOfShape_of_isCardinalAccessible _ κ _
  infer_instance

theorem isCardinalPresentable_eq :
    isCardinalPresentable (Copointed σ) κ =
      (isCardinalPresentable C κ).inverseImage (ι σ ⋙ forget F) := by
  have := isCardinalFilteredGenerator κ Λ hΛ σ
  rw [this.isPresentable_eq_retractClosure,
    ObjectProperty.inverseImage_comp,
    ObjectProperty.retractClosure_eq_self,
    Coalgebra.isCardinalPresentable_eq _ κ Λ hΛ]

theorem preservesCardinalPresentable_ι :
    (ι σ).PreservesCardinalPresentable κ := by
  constructor
  rw [isCardinalPresentable_eq κ Λ hΛ,
    Coalgebra.isCardinalPresentable_eq _ κ Λ hΛ,
    ObjectProperty.inverseImage_comp]

end

/-- Let `F` be an accessible endofunctor of an accessible category.
The category of `F`-coalgebras is accessible. -/
public instance [IsAccessibleCategory.{w} C] [F.IsAccessible.{w}] (σ : F ⟶ 𝟭 C) :
    IsAccessibleCategory.{w} (Copointed σ) :=
  (ObjectProperty.fullSubcategoryCongr
    (copointed_eq_equifier F σ)).symm.isAccessibleCategory

public instance [IsAccessibleCategory.{w} C] [F.IsAccessible.{w}] (σ : F ⟶ 𝟭 C) :
    (ι σ).IsAccessible.{w} := by
  obtain ⟨κ₀, _, _⟩ := IsAccessibleCategory.exists_cardinal C
  obtain ⟨κ, _, _⟩ := Functor.IsAccessible.exists_cardinal F
  obtain ⟨κ₁, _, h₁, h₂⟩ := Cardinal.SharplyLT.exists_of_pair κ₀ κ
  refine ⟨κ₁, inferInstance, ⟨fun J _ _ ↦ ?_⟩⟩
  have : IsCardinalAccessibleCategory C κ₁ := h₁.isCardinalAccessibleCategory C
  have : Limits.HasColimitsOfShape J C :=
    hasColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ₁ J
  have : F.IsCardinalAccessible κ₁ := Functor.isCardinalAccessible_of_le _ h₂.le
  have : Limits.PreservesColimitsOfShape J F :=
    Functor.IsCardinalAccessible.preservesColimitOfShape κ₁ J
  infer_instance

end Coalgebra.Copointed

end CategoryTheory.Endofunctor

