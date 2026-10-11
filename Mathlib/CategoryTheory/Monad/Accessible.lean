/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Monad.Limits
public import Mathlib.CategoryTheory.Presentable.LocallyPresentable
public import Mathlib.CategoryTheory.Presentable.PreservesCardinalPresentable

import Mathlib.CategoryTheory.Endofunctor.Accessible
import Mathlib.CategoryTheory.Endofunctor.Limits
import Mathlib.CategoryTheory.Endofunctor.Pointed.Accessible
import Mathlib.CategoryTheory.Endofunctor.Pointed.Limits
import Mathlib.CategoryTheory.Equifier.Accessible
import Mathlib.CategoryTheory.Presentable.Adjunction
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Presentable.SharplyLT.Lemmas

/-!
# Accessibility of Eilenberg-Moore (co)algebras for a (co)monad

This file proves the following results:

Let `T` be a κ-accessible monad on a `κ`-accessible category C, such that `T`
preserves κ-presentable objects. Assume that `C` has Λ-indexed colimits for an infinite well-order
`Λ` of cardinality `< κ` and that `T` preserves these colimits.
Then the category `Algebra T` of Eilenberg-Moore algebras for `T` is κ-accessible,
its κ-presentable objects are exactly the algebras such that the underlying object of `C` is
κ-presentable, and the forgetful functor from `T`-algebras to `C` is κ-accessible.

This implies that if `T` is an accessible monad on an accessible category, the category
of `T`-algebras is accessible and the forgetful functor from `T`-algebra to `C` is accessible.

The result is also dualized to coalgebras for a comonad. For coalgebras, it is no longer
necessary to assume that the comonad preserves κ-presentable objects.
-/

namespace CategoryTheory

open Category

universe w

variable {C : Type*} [Category* C]

namespace Monad.Algebra

variable (T : Monad C)

section

/-- The "forgetful" functor from η-pointed algebras for the endofunctor underlying a
monad T -/
abbrev U := Endofunctor.Algebra.Pointed.ι T.η ⋙ Endofunctor.Algebra.forget (T : C ⥤ C)

/-- The LHS of the associativity identity as a natural transformation on the category
of η-pointed algebras. -/
abbrev φₗ : U T ⋙ (T : C ⥤ C) ⋙ (T : C ⥤ C) ⟶ U T where
  app X := T.μ.app X.obj.a ≫ X.obj.str
  naturality {X Y} f := by
    dsimp
    simp only [Category.assoc, ← f.hom.h, reassoc_of% T.μ.naturality]

/-- The RHS of the associativity identity as a natural transformation. -/
abbrev φᵣ : U T ⋙ (T : C ⥤ C) ⋙ (T : C ⥤ C) ⟶ U T where
  app X := (T : C ⥤ C).map X.obj.str ≫ X.obj.str
  naturality {X Y} f := by
    dsimp
    simp only [Category.assoc, ← f.hom.h, ← T.map_comp_assoc]

/-- The category of `T`-algebra for a monad `T` can be realized as an equifier
of the category of pointed algebras for the endofunctor underlying `T`, with the pointing given
by the unit `η`. -/
def equivEquifier : Algebra T ≌ Equifier (φₗ T) (φᵣ T) where
  functor.obj X := ⟨⟨{ a := X.A, str := X.a }, X.unit⟩, X.assoc⟩
  functor.map {x y} f := ⟨⟨{ f := f.f }⟩⟩
  inverse.obj X := { A := X.obj.obj.a, a := X.obj.obj.str, unit := X.obj.prop, assoc := X.prop }
  inverse.map {x y} f := { f := f.hom.hom.f }
  unitIso := NatIso.ofComponents (fun _ ↦ .refl _)
  counitIso := NatIso.ofComponents (fun _ ↦ .refl _)
  -- cat_disch is unusually slow here
  functor_unitIso_comp X := by
    ext
    dsimp
    simp

end

public section

variable (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalAccessibleCategory C κ] [T.IsCardinalAccessible κ] [T.PreservesCardinalPresentable κ]
    (Λ : Type*) [Nonempty Λ] [LinearOrder Λ] [SuccOrder Λ] [WellFoundedLT Λ] [NoMaxOrder Λ]
    (hΛ : HasCardinalLT Λ κ) [Limits.HasColimitsOfShape Λ C]
    [Limits.PreservesColimitsOfShape Λ (T : C ⥤ C)]

include Λ hΛ

/-- Let `T : C ⥤ C` be a monad on a category `C` and assume that
- `C` is κ-accessible
- `T` is κ-accessible
- `T` preserves κ-presentable objects
- There exists an infinite well-order Λ of cardinality < κ such that `C` admits Λ-indexed colimits
  and `T` preserves them.

Then, the class T-algebras such that the underlying object of `C` is κ-presentable is a
cardinal filtered generator for the category of `T`-algebras. -/
theorem isCardinalFilteredGenerator :
    ((isCardinalPresentable C κ).inverseImage (forget T)).IsCardinalFilteredGenerator κ := by
  have : IsCardinalAccessibleCategory (Endofunctor.Algebra.Pointed T.η) κ :=
    Endofunctor.Algebra.Pointed.isCardinalAccessibleCategory κ Λ hΛ T.η
  have : (Endofunctor.Algebra.forget T.toFunctor).IsCardinalAccessible κ :=
    Endofunctor.Algebra.isCardinalAccessible_forget T.toFunctor κ
  have : (Endofunctor.Algebra.forget T.toFunctor).PreservesCardinalPresentable κ :=
    Endofunctor.Algebra.preservesCardinalPresentable_forget T.toFunctor κ Λ hΛ
  have : (Endofunctor.Algebra.Pointed.ι T.η).PreservesCardinalPresentable κ :=
    Endofunctor.Algebra.Pointed.preservesCardinalPresentable_ι κ Λ hΛ T.η
  have := Equifier.isCardinalFilteredGenerator_inverseImage_isCardinalPresentable κ
    (φₗ T) (φᵣ T) Λ hΛ
  convert (equivEquifier T).toAdjunction'.isCardinalFilteredGenerator this
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp only [ObjectProperty.prop_inverseImage_iff, forget_obj] at h ⊢
    use (equivEquifier T).functor.obj x
    rw [Endofunctor.Algebra.Pointed.isCardinalPresentable_eq (hΛ := hΛ)]
    exact ⟨h, ⟨.refl _⟩⟩
  · simp only [ObjectProperty.prop_map_iff, ObjectProperty.prop_inverseImage_iff,
    ObjectProperty.ι_obj] at h ⊢
    obtain ⟨X, q, ⟨e⟩⟩ := h
    let e' := (forget T).mapIso e
    rw [Endofunctor.Algebra.Pointed.isCardinalPresentable_eq (hΛ := hΛ)] at q
    simp only [forget_obj] at e'
    exact ObjectProperty.IsClosedUnderIsomorphisms.of_iso e' q

/-- Let `T : C ⥤ C` be a monad on a category `C` and assume that
- `C` is κ-accessible
- `T` is κ-accessible
- `T` preserves κ-presentable objects
- There exists an infinite well-order Λ of cardinality < κ such that `C` admits Λ-indexed colimits
  and `T` preserves them.

Then, the category of `T`-algebras is κ-accessible. -/
theorem isCardinalAccessibleCategory :
    IsCardinalAccessibleCategory (Algebra T) κ :=
  have : IsCardinalAccessibleCategory (Endofunctor.Algebra.Pointed T.η) κ :=
    Endofunctor.Algebra.Pointed.isCardinalAccessibleCategory κ Λ hΛ T.η
  have : (Endofunctor.Algebra.forget T.toFunctor).PreservesCardinalPresentable κ :=
    Endofunctor.Algebra.preservesCardinalPresentable_forget T.toFunctor κ Λ hΛ
  have : (Endofunctor.Algebra.Pointed.ι T.η).PreservesCardinalPresentable κ :=
    Endofunctor.Algebra.Pointed.preservesCardinalPresentable_ι κ Λ hΛ T.η
  have : IsCardinalAccessibleCategory (Equifier (φₗ T) (φᵣ T)) κ :=
    Equifier.isCardinalAccessibleCategory κ (φₗ T) (φᵣ T) Λ hΛ
  (equivEquifier T).symm.isCardinalAccessibleCategory κ

omit Λ hΛ in
instance isCardinalAccessible_ι : (forget T).IsCardinalAccessible κ := by
  constructor
  intro J _ _
  have : Limits.HasColimitsOfShape J C :=
    hasColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ J
  have : Limits.PreservesColimitsOfShape J T.toFunctor :=
    Functor.preservesColimitsOfShape_of_isCardinalAccessible _ κ _
  infer_instance

theorem isCardinalPresentable_eq :
    isCardinalPresentable (Algebra T) κ =
      (isCardinalPresentable C κ).inverseImage (forget T) := by
  have := isCardinalFilteredGenerator T κ Λ hΛ
  rw [this.isPresentable_eq_retractClosure,
    ObjectProperty.retractClosure_eq_self]

theorem preservesCardinalPresentable_ι :
    (forget T).PreservesCardinalPresentable κ := by
  constructor
  rw [isCardinalPresentable_eq T κ Λ hΛ]

end

/-- Let `F` be an accessible monad on an accessible category.
The category of `F`-algebras is accessible. -/
public instance [IsAccessibleCategory.{w} C] [T.IsAccessible.{w}] :
    IsAccessibleCategory.{w} (Algebra T) :=
  (equivEquifier T).symm.isAccessibleCategory

public instance [IsAccessibleCategory.{w} C] [T.IsAccessible.{w}] :
    (forget T).IsAccessible.{w} := by
  obtain ⟨κ₀, _, _⟩ := IsAccessibleCategory.exists_cardinal C
  obtain ⟨κ, _, _⟩ := Functor.IsAccessible.exists_cardinal T.toFunctor
  obtain ⟨κ₁, _, h₁, h₂⟩ := Cardinal.SharplyLT.exists_of_pair κ₀ κ
  refine ⟨κ₁, inferInstance, ⟨fun J _ _ ↦ ?_⟩⟩
  have : IsCardinalAccessibleCategory C κ₁ := h₁.isCardinalAccessibleCategory C
  have : Limits.HasColimitsOfShape J C :=
    hasColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ₁ J
  have : T.toFunctor.IsCardinalAccessible κ₁ := Functor.isCardinalAccessible_of_le _ h₂.le
  have : Limits.PreservesColimitsOfShape J T.toFunctor :=
    Functor.IsCardinalAccessible.preservesColimitOfShape κ₁ J
  infer_instance

end Monad.Algebra

namespace Comonad.Coalgebra

variable (T : Comonad C)

/-- The "forgetful" functor from η-pointed algebras for the endofunctor underlying a
monad T -/
abbrev U := Endofunctor.Coalgebra.Copointed.ι T.ε ⋙ Endofunctor.Coalgebra.forget (T : C ⥤ C)

/-- The LHS of the coassociativity identity as a natural transformation on the
category of ε-copointed coalgebras. -/
abbrev φₗ : U T ⟶ U T ⋙ (T : C ⥤ C) ⋙ (T : C ⥤ C) where
  app X := X.obj.str ≫ T.δ.app X.obj.V
  naturality {X Y} f := by
    dsimp
    simp only [Category.assoc, ← reassoc_of% f.hom.h, ← dsimp% T.δ.naturality]

/-- The RHS of the coassociativity identity as a natural transformation. -/
abbrev φᵣ : U T ⟶ U T ⋙ (T : C ⥤ C) ⋙ (T : C ⥤ C) where
  app X := X.obj.str ≫ T.toFunctor.map X.obj.str
  naturality {X Y} f := by
    dsimp
    simp only [Category.assoc, ← reassoc_of% f.hom.h, ← T.map_comp]
    simp

/-- The category of `T`-coalgebras for a comonad `T` can be realized as an equifier
of the category of ε-copointed coalgebras for the endofunctor underlying `T`. -/
def equivEquifier : Coalgebra T ≌ Equifier (φₗ T) (φᵣ T) where
  functor.obj X := ⟨⟨{ V := X.A, str := X.a }, X.counit⟩, X.coassoc⟩
  functor.map {x y} f := ⟨⟨{ f := f.f }⟩⟩
  inverse.obj X := { A := X.obj.obj.V, a := X.obj.obj.str, counit := X.obj.prop, coassoc := X.prop }
  inverse.map {x y} f := { f := f.hom.hom.f }
  unitIso := NatIso.ofComponents (fun _ ↦ .refl _)
  counitIso := NatIso.ofComponents (fun _ ↦ .refl _)
  -- cat_disch is unusually slow here
  functor_unitIso_comp X := by
    ext
    dsimp
    simp

public section

variable (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalAccessibleCategory C κ] [T.IsCardinalAccessible κ]
    (Λ : Type*) [Nonempty Λ] [LinearOrder Λ] [SuccOrder Λ] [WellFoundedLT Λ] [NoMaxOrder Λ]
    (hΛ : HasCardinalLT Λ κ) [Limits.HasColimitsOfShape Λ C]
    [Limits.PreservesColimitsOfShape Λ (T : C ⥤ C)]

include Λ hΛ

/-- Let `T : C ⥤ C` be a comonad on a category `C` and assume that
- `C` is κ-accessible
- `T` is κ-accessible
- There exists an infinite well-order Λ of cardinality < κ such that `C` admits Λ-indexed colimits
  and `T` preserves them.

Then, the class of T-coalgebras such that the underlying object of `C` is κ-presentable is a
κ-filtered generator for the category of `T`-algebras. -/
theorem isCardinalFilteredGenerator :
    ((isCardinalPresentable C κ).inverseImage (forget T)).IsCardinalFilteredGenerator κ := by
  have : IsCardinalAccessibleCategory (Endofunctor.Coalgebra.Copointed T.ε) κ :=
    Endofunctor.Coalgebra.Copointed.isCardinalAccessibleCategory κ Λ hΛ T.ε
  have : (Endofunctor.Coalgebra.forget T.toFunctor).IsCardinalAccessible κ :=
    Endofunctor.Coalgebra.isCardinalAccessible_forget T.toFunctor κ
  have : (Endofunctor.Coalgebra.forget T.toFunctor).PreservesCardinalPresentable κ :=
    Endofunctor.Coalgebra.preservesCardinalPresentable_forget T.toFunctor κ Λ hΛ
  have : (Endofunctor.Coalgebra.Copointed.ι T.ε).PreservesCardinalPresentable κ :=
    Endofunctor.Coalgebra.Copointed.preservesCardinalPresentable_ι κ Λ hΛ T.ε
  have := Equifier.isCardinalFilteredGenerator_inverseImage_isCardinalPresentable κ
    (φₗ T) (φᵣ T) Λ hΛ
  convert (equivEquifier T).toAdjunction'.isCardinalFilteredGenerator this
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp only [ObjectProperty.prop_inverseImage_iff, forget_obj] at h ⊢
    use (equivEquifier T).functor.obj x
    rw [Endofunctor.Coalgebra.Copointed.isCardinalPresentable_eq (hΛ := hΛ)]
    exact ⟨h, ⟨.refl _⟩⟩
  · simp only [ObjectProperty.prop_map_iff, ObjectProperty.prop_inverseImage_iff,
    ObjectProperty.ι_obj] at h ⊢
    obtain ⟨X, q, ⟨e⟩⟩ := h
    let e' := (forget T).mapIso e
    rw [Endofunctor.Coalgebra.Copointed.isCardinalPresentable_eq (hΛ := hΛ)] at q
    simp only [forget_obj] at e'
    exact ObjectProperty.IsClosedUnderIsomorphisms.of_iso e' q

/-- Let `T : C ⥤ C` be a monad on a category `C` and assume that
- `C` is κ-accessible
- `T` is κ-accessible
- `T` preserves κ-presentable objects
- There exists an infinite well-order Λ of cardinality < κ such that `C` admits Λ-indexed colimits
  and `T` preserves them.

Then, the category of `T`-algebras is κ-accessible. -/
theorem isCardinalAccessibleCategory :
    IsCardinalAccessibleCategory (Coalgebra T) κ :=
  have : IsCardinalAccessibleCategory (Endofunctor.Coalgebra.Copointed T.ε) κ :=
    Endofunctor.Coalgebra.Copointed.isCardinalAccessibleCategory κ Λ hΛ T.ε
  have : (Endofunctor.Coalgebra.forget T.toFunctor).PreservesCardinalPresentable κ :=
    Endofunctor.Coalgebra.preservesCardinalPresentable_forget T.toFunctor κ Λ hΛ
  have : (Endofunctor.Coalgebra.Copointed.ι T.ε).PreservesCardinalPresentable κ :=
    Endofunctor.Coalgebra.Copointed.preservesCardinalPresentable_ι κ Λ hΛ T.ε
  have : IsCardinalAccessibleCategory (Equifier (φₗ T) (φᵣ T)) κ :=
    Equifier.isCardinalAccessibleCategory κ (φₗ T) (φᵣ T) Λ hΛ
  (equivEquifier T).symm.isCardinalAccessibleCategory κ

omit Λ hΛ in
instance isCardinalAccessible_ι : (forget T).IsCardinalAccessible κ := by
  constructor
  intro J _ _
  have : Limits.HasColimitsOfShape J C :=
    hasColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ J
  have : Limits.PreservesColimitsOfShape J T.toFunctor :=
    Functor.preservesColimitsOfShape_of_isCardinalAccessible _ κ _
  infer_instance

theorem isCardinalPresentable_eq :
    isCardinalPresentable (Coalgebra T) κ =
      (isCardinalPresentable C κ).inverseImage (forget T) := by
  have := isCardinalFilteredGenerator T κ Λ hΛ
  rw [this.isPresentable_eq_retractClosure,
    ObjectProperty.retractClosure_eq_self]

theorem preservesCardinalPresentable_ι :
    (forget T).PreservesCardinalPresentable κ := by
  constructor
  rw [isCardinalPresentable_eq T κ Λ hΛ]

end

/-- Let `F` be an accessible monad on an accessible category.
The category of `F`-algebras is accessible. -/
public instance [IsAccessibleCategory.{w} C] [T.IsAccessible.{w}] :
    IsAccessibleCategory.{w} (Coalgebra T) :=
  (equivEquifier T).symm.isAccessibleCategory

public instance [IsAccessibleCategory.{w} C] [T.IsAccessible.{w}] :
    (forget T).IsAccessible.{w} := by
  obtain ⟨κ₀, _, _⟩ := IsAccessibleCategory.exists_cardinal C
  obtain ⟨κ, _, _⟩ := Functor.IsAccessible.exists_cardinal T.toFunctor
  obtain ⟨κ₁, _, h₁, h₂⟩ := Cardinal.SharplyLT.exists_of_pair κ₀ κ
  refine ⟨κ₁, inferInstance, ⟨fun J _ _ ↦ ?_⟩⟩
  have : IsCardinalAccessibleCategory C κ₁ := h₁.isCardinalAccessibleCategory C
  have : Limits.HasColimitsOfShape J C :=
    hasColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ₁ J
  have : T.toFunctor.IsCardinalAccessible κ₁ := Functor.isCardinalAccessible_of_le _ h₂.le
  have : Limits.PreservesColimitsOfShape J T.toFunctor :=
    Functor.IsCardinalAccessible.preservesColimitOfShape κ₁ J
  infer_instance

end Comonad.Coalgebra

end CategoryTheory
