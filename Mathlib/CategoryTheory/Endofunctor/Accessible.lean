/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Inserter.Accessible
public import Mathlib.CategoryTheory.Equifier.Accessible
public import Mathlib.CategoryTheory.Endofunctor.Pointed.Algebra
public import Mathlib.CategoryTheory.Endofunctor.Limits

import Mathlib.CategoryTheory.Presentable.Adjunction

/-! # Accessibility of categories of (co)algebras of an endofunctor

In this file, we show that categories of (co)algebras are accessible in good situations
(see the file `Mathlib.CategoryTheory.Inserter.Accessible` what "good situations"
refers to exactly).

This is obtained by identifying `Algebra F` with `Inserter F (𝟭 C)` and
using the theorem that categories of inserters are accessible in good situations.
-/

universe w

namespace CategoryTheory.Endofunctor

variable {C : Type*} [Category* C] (F : C ⥤ C)

namespace Algebra

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

end Coalgebra

end CategoryTheory.Endofunctor
