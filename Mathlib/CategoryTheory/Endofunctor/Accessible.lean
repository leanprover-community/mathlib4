/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Inserter.Accessible
public import Mathlib.CategoryTheory.Equifier.Accessible
public import Mathlib.CategoryTheory.Endofunctor.PointedAlgebra
public import Mathlib.CategoryTheory.Endofunctor.Limits

import Mathlib.CategoryTheory.Presentable.Adjunction

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

namespace Algebra

/-- Construct a natural transformation from a pointing of an endofunctor -/
def φ₀ (σ : 𝟭 C ⟶ F) : forget F ⟶ forget F where
  app x := σ.app x.a ≫ x.str
  naturality x y f := by simp [reassoc_of% σ.naturality f.f]

lemma pointed_eq_equifier (σ : 𝟭 C ⟶ F) : pointed σ = equifier (φ₀ F σ) (𝟙 (forget F)) := rfl

section

variable (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalAccessibleCategory C κ] [F.IsCardinalAccessible κ] [F.PreservesCardinalPresentable κ]
    (Λ : Type*) [Nonempty Λ] [LinearOrder Λ] [SuccOrder Λ] [WellFoundedLT Λ] [NoMaxOrder Λ]
    (hΛ : HasCardinalLT Λ κ) [Limits.HasColimitsOfShape Λ C] [Limits.PreservesColimitsOfShape Λ F]

include Λ hΛ
/-- Let `F : C ⥤ C` be an endofunctor of a category and assume that
- `F` is κ-accessible
- `F` preserves κ-presentable objects
- There exists an infinite well-order Λ of cardinality < κ such that `C` admits Λ-indexed colimits
  and `F` preserves them.

Then, the class of algebras such that the underlying object of `C` is κ-presentable is a cardinal
filtered generator for the category of `F`-algebras.

This is a special case of `CategoryTheory.Inserter.isCardinalAccessibleCategory` where one of the
functor is the identity functor. -/
public theorem isCardinalFilteredGenerator :
    ((isCardinalPresentable C κ).inverseImage (forget F)).IsCardinalFilteredGenerator κ := by
  convert (equivInserter F).toAdjunction'.isCardinalFilteredGenerator <|
    Inserter.isCardinalFilteredGenerator_inverseImage_isCardinalPresentable F (𝟭 C) κ Λ hΛ
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp only [ObjectProperty.prop_map_iff, ObjectProperty.prop_inverseImage_iff,
      Inserter.proj_obj] at h ⊢
    use (equivInserter F).functor.obj x
    exact ⟨h, ⟨.refl _⟩⟩
  · simp only [ObjectProperty.prop_map_iff, ObjectProperty.prop_inverseImage_iff,
      Inserter.proj_obj, forget_obj] at h ⊢
    obtain ⟨X, q, ⟨e⟩⟩ := h
    let e' := (forget F).mapIso e
    simp only [equivInserter, forget_obj] at e'
    exact ObjectProperty.IsClosedUnderIsomorphisms.of_iso e' q

/-- Let `F : C ⥤ C` be an endofunctor of a category and assume that
- `F` is κ-accessible
- `F` preserves κ-presentable objects
- There exists an infinite well-order Λ of cardinality < κ such that `C` admits Λ-indexed colimits
  and `F` preserves them.

Then, the category of `F`-algebras is accessible.

This is a special case of `CategoryTheory.Inserter.isCardinalAccessibleCategory` where one of the
functor is the identity functor. -/
public theorem isCardinalAccessibleCategory :
    IsCardinalAccessibleCategory (Algebra F) κ :=
  have : IsCardinalAccessibleCategory (Inserter F (𝟭 C)) κ :=
    Inserter.isCardinalAccessibleCategory F (𝟭 C) κ Λ hΛ
  (equivInserter F).symm.isCardinalAccessibleCategory κ

public theorem isCardinalPresentable_eq :
    isCardinalPresentable (Algebra F) κ = (isCardinalPresentable C κ).inverseImage (forget F) := by
  have := isCardinalFilteredGenerator F κ Λ hΛ
  rw [this.isPresentable_eq_retractClosure]
  apply ObjectProperty.retractClosure_eq_self

omit Λ hΛ in
public instance isCardinalAccessible_forget : (forget F).IsCardinalAccessible κ := by
  constructor
  intro J _ _
  have : Limits.HasColimitsOfShape J C :=
    hasColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ J
  have : Limits.PreservesColimitsOfShape J F :=
    Functor.preservesColimitsOfShape_of_isCardinalAccessible _ κ _
  infer_instance

public theorem preservesCardinalPresentable_forget :
    (forget F).PreservesCardinalPresentable κ := by
  constructor
  rw [isCardinalPresentable_eq _ κ Λ hΛ]

end

/-- Let `F` be an accessible endofunctor of an accessible category.
The category of `F`-algebras is accessible. -/
public instance [IsAccessibleCategory.{w} C] [F.IsAccessible.{w}] :
    IsAccessibleCategory.{w} (Algebra F) :=
  (equivInserter F).symm.isAccessibleCategory.{w}

namespace Pointed

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
cardinal filtered generator for the category of pointed `F`-algebras for all pointing
`σ : 𝟭 C ⟶ F`. -/
public theorem isCardinalFilteredGenerator :
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
public theorem isCardinalAccessibleCategory :
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
set_option trace.Meta.synthInstance true in
public instance isCardinalAccessible_ι : (Pointed.ι σ).IsCardinalAccessible κ := by
  sorry
  constructor
  intro J _ _
  have : Limits.HasColimitsOfShape J C :=
    hasColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ J
  have : Limits.PreservesColimitsOfShape J F :=
    Functor.preservesColimitsOfShape_of_isCardinalAccessible _ κ _
  infer_instance

public theorem isCardinalPresentable_eq :
    isCardinalPresentable (Pointed σ) κ = 
      (isCardinalPresentable C κ).inverseImage (ι σ ⋙ forget F) := by
  have := isCardinalFilteredGenerator κ Λ hΛ σ
  rw [this.isPresentable_eq_retractClosure,
    ObjectProperty.inverseImage_comp]
  apply ObjectProperty.retractClosure_eq_self

public theorem preservesCardinalPresentable_forget :
    (ι σ).PreservesCardinalPresentable κ := by
  constructor
  rw [isCardinalPresentable_eq _ κ Λ hΛ]

end Pointed

end Algebra

namespace Coalgebra

variable (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalAccessibleCategory C κ] [F.IsCardinalAccessible κ]
    (Λ : Type*) [Nonempty Λ] [LinearOrder Λ] [SuccOrder Λ] [WellFoundedLT Λ] [NoMaxOrder Λ]
    (hΛ : HasCardinalLT Λ κ) [Limits.HasColimitsOfShape Λ C] [Limits.PreservesColimitsOfShape Λ F]

include Λ hΛ

/-- Let `F : C ⥤ C` be an endofunctor of a category and assume that
- `F` is κ-accessible
- There exists an infinite well-order Λ of cardinality < κ such that `C` admits Λ-indexed colimits
  and `F` preserves them.

Then, the class of coalgebras such that the underlying object of `C` is κ-presentable is a cardinal
filtered generator for the category of `F`-coalgebras.

This is a special case of `CategoryTheory.Inserter.isCardinalAccessibleCategory` where one of the
functor is the identity functor. -/
public theorem isCardinalFilteredGenerator :
    ((isCardinalPresentable C κ).inverseImage (forget F)).IsCardinalFilteredGenerator κ := by
  convert (equivInserter F).toAdjunction'.isCardinalFilteredGenerator <|
    Inserter.isCardinalFilteredGenerator_inverseImage_isCardinalPresentable (𝟭 C) F κ Λ hΛ
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp only [ObjectProperty.prop_map_iff, ObjectProperty.prop_inverseImage_iff,
      Inserter.proj_obj] at h ⊢
    use (equivInserter F).functor.obj x
    exact ⟨h, ⟨.refl _⟩⟩
  · simp only [ObjectProperty.prop_map_iff, ObjectProperty.prop_inverseImage_iff,
      Inserter.proj_obj, forget_obj] at h ⊢
    obtain ⟨X, q, ⟨e⟩⟩ := h
    let e' := (forget F).mapIso e
    simp only [equivInserter, forget_obj] at e'
    exact ObjectProperty.IsClosedUnderIsomorphisms.of_iso e' q

/-- Let `F : C ⥤ C` be an endofunctor of a category and assume that
- `F` is κ-accessible
- There exists an infinite well-order Λ of cardinality < κ such that `C` admits Λ-indexed colimits
  and `F` preserves them.

Then, the class of coalgebras such that the underlying object of `C` is κ-presentable is a cardinal
filtered generator for the category of `F`-coalgebras.

This is a special case of `CategoryTheory.Inserter.isCardinalAccessibleCategory` where one of the
functor is the identity functor. -/
public theorem isCardinalAccessibleCategory :
    IsCardinalAccessibleCategory (Coalgebra F) κ :=
  have : IsCardinalAccessibleCategory (Inserter (𝟭 C) F) κ :=
    Inserter.isCardinalAccessibleCategory (𝟭 C) F κ Λ hΛ
  (equivInserter F).symm.isCardinalAccessibleCategory κ

public theorem isCardinalPresentable_eq :
    isCardinalPresentable (Coalgebra F) κ =
      (isCardinalPresentable C κ).inverseImage (forget F) := by
  have := isCardinalFilteredGenerator F κ Λ hΛ
  rw [this.isPresentable_eq_retractClosure]
  apply ObjectProperty.retractClosure_eq_self

section pointed

end pointed

end Coalgebra

end CategoryTheory.Endofunctor
