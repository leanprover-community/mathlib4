/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
public import Mathlib.Topology.Sheaves.Limits
public import Mathlib.Topology.Sheaves.Skyscraper

/-!
# Sheaves over Abelian categories
We provide instances for categories of sheaves over Abelian categories.

## Main Results

* `TopCat.Sheaf.exact_iff_stalkFunctor_map_exact`: A complex of sheaves over a concrete abelian
category is exact if and only if it is exact on stalks.

-/

@[expose] public section

universe u v v₁ v₂

open TopologicalSpace CategoryTheory Limits

namespace TopCat

variable {X : TopCat.{u}}

section

variable {C : Type v₁} [Category.{v₂} C] [HasSheafify (Opens.grothendieckTopology X) C] [Abelian C]

noncomputable instance : Abelian (Presheaf C X) := inferInstanceAs (Abelian (_ ⥤ _))

namespace Sheaf

instance : Abelian (Sheaf C X) := inferInstanceAs (Abelian (CategoryTheory.Sheaf _ _))

instance : (Sheaf.forget C X).Additive where

instance [Category.{u} C] [Abelian C] [IsGrothendieckAbelian.{u} C]
    [HasSheafify (Opens.grothendieckTopology X) C] : IsGrothendieckAbelian.{u} (Sheaf C X) :=
  inferInstanceAs (IsGrothendieckAbelian (CategoryTheory.Sheaf _ _))

end Sheaf

end

/-- The stalk functor is additive -/
instance (p₀ : X) {C : Type v} [Category.{u} C] [Abelian C] [HasColimits C] :
    (Presheaf.stalkFunctor C p₀).Additive := by
  apply @Functor.instAdditiveComp _ _ _ _ _ _ ((Functor.whiskeringLeft _ _ _).obj _) ⟨by cat_disch⟩

namespace Sheaf

open Presheaf

variable {X : TopCat.{u}} (p₀ : X) {C : Type v} [Category.{u} C] [HasColimits C] [HasLimits C]
  {FC : C → C → Type*} {CC : C → Type u} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory C FC] [PreservesFilteredColimits (CategoryTheory.forget C)]
  [PreservesLimits (CategoryTheory.forget C)] [Abelian C]
  [HasSheafify (Opens.grothendieckTopology X) C]

/-- Taking stalks of sheaves is exact. -/
instance : (forget C X ⋙ stalkFunctor C p₀).PreservesHomology := by
  simp only [(forget C X ⋙ stalkFunctor C p₀).exact_tfae.out 2 0]
  intro S h
  have := ((forget C X ⋙ stalkFunctor C p₀).preservesFiniteColimits_tfae.out 3 0).mp
    (inferInstanceAs (PreservesFiniteColimits _))
  refine ShortComplex.ShortExact.mk' (this S h).left ?_ (this S h).right
  have := h.2
  exact Functor.map_mono (forget C X ⋙ stalkFunctor C p₀) _

instance : Limits.PreservesFiniteLimits (forget C X ⋙ stalkFunctor C p₀) :=
  (forget C X ⋙ stalkFunctor C p₀).preservesFiniteLimits_of_preservesHomology

open ZeroObject

/-- A sheaf is zero if and only if its stalks are all zero. -/
lemma isZero_iff_stalkFunctor_obj_isZero (F : Sheaf C X)
    [PreservesLimits (CategoryTheory.forget C)] :
    IsZero F ↔ ∀ x : X, IsZero ((forget C X ⋙ stalkFunctor C x).obj F) := by
  refine ⟨fun h _ => Functor.map_isZero _ h, ?_⟩
  intro h
  let f : F ⟶ 0 := (isZero_zero (Sheaf C X)).from_ F
  have : IsIso f := by
    rw[Presheaf.isIso_iff_stalkFunctor_map_iso]
    exact fun x => isIso_of_source_target_iso_zero _ (h x).isoZero
      ((forget C X ⋙ stalkFunctor C x).map_isZero (isZero_zero _)).isoZero
  exact (isZero_zero _).of_iso (asIso f)

/-- Exactness can be checked on stalks for complexes of sheaves. -/
theorem exact_iff_stalkFunctor_map_exact [PreservesLimits (CategoryTheory.forget C)]
    (S : ShortComplex (Sheaf C X)) :
    S.Exact ↔ ∀ x : X, (S.map (forget C X ⋙ stalkFunctor C x)).Exact := by
  constructor
  · intro h x
    have := (forget C X ⋙ stalkFunctor C x).exact_tfae.out 2 1
    exact this.mp inferInstance S h
  intro h
  simp_rw [ShortComplex.exact_iff_isZero_homology] at h
  rw[ShortComplex.exact_iff_isZero_homology, isZero_iff_stalkFunctor_obj_isZero S.homology]
  exact fun x => (h x).of_iso
    (ShortComplex.mapHomologyIso S (forget C X ⋙ stalkFunctor C x)).symm

end Sheaf

end TopCat
