/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Endofunctor.Pointed.Algebra
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Colimits of pointed (co)algebras

Let `F : C ⥤ C` be an endofunctor and `σ : 𝟭 C ⟶ F`. We show that the full subcategory `Pointed σ`
is closed under all limits and colimits that `forget F : Algebra F ⥤ C` preserves.

-/

@[expose] public section

namespace CategoryTheory.Endofunctor

variable {C J : Type*} [Category* C] [Category* J] (F : C ⥤ C)

open Limits

namespace Algebra.Pointed

variable (σ : 𝟭 C ⟶ F)

instance {J : Type*} [Category* J]
    [Limits.PreservesColimitsOfShape J (forget F)] :
    (pointed σ).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le c := by
    rintro ⟨p, h⟩
    apply (p.map (forget F)).isColimit.hom_ext
    intro j
    dsimp [pointed] at h ⊢
    simp [Limits.ColimitPresentation.map,
      reassoc_of% dsimp% σ.naturality (p.ι.app j).f, reassoc_of% h]

instance {J : Type*} [Category* J]
    [PreservesLimitsOfShape J (forget F)] :
    (pointed σ).IsClosedUnderLimitsOfShape J where
  limitsOfShape_le c := by
    rintro ⟨p, h⟩
    apply (p.map (forget F)).isLimit.hom_ext
    intro j
    dsimp [Limits.LimitPresentation.map, pointed] at h ⊢
    simp only [Functor.constComp_inv_app, forget_obj, Functor.const_obj_obj, Category.id_comp,
      Category.assoc]
    grind [dsimp% (p.π.app j).h, dsimp% σ.naturality (p.π.app j).f]

end Algebra.Pointed

namespace Coalgebra.Copointed

variable (σ : F ⟶ 𝟭 C)

instance {J : Type*} [Category* J]
    [Limits.PreservesColimitsOfShape J (forget F)] :
    (copointed σ).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le c := by
    rintro ⟨p, h⟩
    apply (p.map (forget F)).isColimit.hom_ext
    intro j
    dsimp [copointed] at h ⊢
    simp [Limits.ColimitPresentation.map, ← reassoc_of% dsimp% (p.ι.app j).h,
      dsimp% σ.naturality (p.ι.app j).f,
      reassoc_of% h]

instance {J : Type*} [Category* J]
    [PreservesLimitsOfShape J (forget F)] :
    (copointed σ).IsClosedUnderLimitsOfShape J where
  limitsOfShape_le c := by
    rintro ⟨p, h⟩
    apply (p.map (forget F)).isLimit.hom_ext
    intro j
    dsimp [Limits.LimitPresentation.map, copointed] at h ⊢
    simp only [Functor.constComp_inv_app, forget_obj, Functor.const_obj_obj,
      Category.id_comp, Category.assoc]
    grind [dsimp% (p.π.app j).h, dsimp% σ.naturality (p.π.app j).f]

end Coalgebra.Copointed

end CategoryTheory.Endofunctor

