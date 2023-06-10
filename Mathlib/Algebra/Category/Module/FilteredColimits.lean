/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer

! This file was ported from Lean 3 source module algebra.category.Module.filtered_colimits
! leanprover-community/mathlib commit 806bbb0132ba63b93d5edbe4789ea226f8329979
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.Group.FilteredColimits
import Mathbin.Algebra.Category.Module.Basic

/-!
# The forgetful functor from `R`-modules preserves filtered colimits.

Forgetful functors from algebraic categories usually don't preserve colimits. However, they tend
to preserve _filtered_ colimits.

In this file, we start with a ring `R`, a small filtered category `J` and a functor
`F : J ⥤ Module R`. We show that the colimit of `F ⋙ forget₂ (Module R) AddCommGroup`
(in `AddCommGroup`) carries the structure of an `R`-module, thereby showing that the forgetful
functor `forget₂ (Module R) AddCommGroup` preserves filtered colimits. In particular, this implies
that `forget (Module R)` preserves filtered colimits.

-/


universe u v

noncomputable section

open scoped Classical

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.IsFiltered renaming max → max'

-- avoid name collision with `_root_.max`.
open AddMonCat.FilteredColimits (colimit_zero_eq colimit_add_mk_eq)

namespace ModuleCat.FilteredColimits

section

-- We use parameters here, mainly so we can have the abbreviations `M` and `M.mk` below, without
-- passing around `F` all the time.
parameter {R : Type u} [Ring R] {J : Type v} [SmallCategory J] [IsFiltered J]

parameter (F : J ⥤ ModuleCat.{max v u} R)

/-- The colimit of `F ⋙ forget₂ (Module R) AddCommGroup` in the category `AddCommGroup`.
In the following, we will show that this has the structure of an `R`-module.
-/
abbrev m : AddCommGroupCat :=
  AddCommGroupCat.FilteredColimits.colimit (F ⋙ forget₂ (ModuleCat R) AddCommGroupCat.{max v u})
#align Module.filtered_colimits.M ModuleCat.FilteredColimits.m

/-- The canonical projection into the colimit, as a quotient type. -/
abbrev m.mk : (Σ j, F.obj j) → M :=
  Quot.mk (Types.Quot.Rel (F ⋙ forget (ModuleCat R)))
#align Module.filtered_colimits.M.mk ModuleCat.FilteredColimits.m.mk

theorem m.mk_eq (x y : Σ j, F.obj j)
    (h : ∃ (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k), F.map f x.2 = F.map g y.2) : M.mk x = M.mk y :=
  Quot.EqvGen_sound (Types.FilteredColimit.eqvGen_quot_rel_of_rel (F ⋙ forget (ModuleCat R)) x y h)
#align Module.filtered_colimits.M.mk_eq ModuleCat.FilteredColimits.m.mk_eq

/-- The "unlifted" version of scalar multiplication in the colimit. -/
def colimitSmulAux (r : R) (x : Σ j, F.obj j) : M :=
  M.mk ⟨x.1, r • x.2⟩
#align Module.filtered_colimits.colimit_smul_aux ModuleCat.FilteredColimits.colimitSmulAux

theorem colimitSmulAux_eq_of_rel (r : R) (x y : Σ j, F.obj j)
    (h : Types.FilteredColimit.Rel (F ⋙ forget (ModuleCat R)) x y) :
    colimit_smul_aux r x = colimit_smul_aux r y :=
  by
  apply M.mk_eq
  obtain ⟨k, f, g, hfg⟩ := h
  use k, f, g
  simp only [CategoryTheory.Functor.comp_map, forget_map_eq_coe] at hfg 
  rw [LinearMap.map_smul, LinearMap.map_smul, hfg]
#align Module.filtered_colimits.colimit_smul_aux_eq_of_rel ModuleCat.FilteredColimits.colimitSmulAux_eq_of_rel

/-- Scalar multiplication in the colimit. See also `colimit_smul_aux`. -/
instance colimitHasSmul : SMul R M
    where smul r x := by
    refine' Quot.lift (colimit_smul_aux F r) _ x
    intro x y h
    apply colimit_smul_aux_eq_of_rel
    apply types.filtered_colimit.rel_of_quot_rel
    exact h
#align Module.filtered_colimits.colimit_has_smul ModuleCat.FilteredColimits.colimitHasSmul

@[simp]
theorem colimit_smul_mk_eq (r : R) (x : Σ j, F.obj j) : r • M.mk x = M.mk ⟨x.1, r • x.2⟩ :=
  rfl
#align Module.filtered_colimits.colimit_smul_mk_eq ModuleCat.FilteredColimits.colimit_smul_mk_eq

instance colimitModule : Module R M
    where
  one_smul x := by
    apply Quot.inductionOn x; clear x; intro x; cases' x with j x
    erw [colimit_smul_mk_eq F 1 ⟨j, x⟩, one_smul]
    rfl
  mul_smul r s x := by
    apply Quot.inductionOn x; clear x; intro x; cases' x with j x
    erw [colimit_smul_mk_eq F (r * s) ⟨j, x⟩, colimit_smul_mk_eq F s ⟨j, x⟩,
      colimit_smul_mk_eq F r ⟨j, _⟩, mul_smul]
  smul_add r x y := by
    apply Quot.induction_on₂ x y; clear x y; intro x y; cases' x with i x; cases' y with j y
    erw [colimit_add_mk_eq _ ⟨i, x⟩ ⟨j, y⟩ (max' i j) (left_to_max i j) (right_to_max i j),
      colimit_smul_mk_eq, smul_add, colimit_smul_mk_eq, colimit_smul_mk_eq,
      colimit_add_mk_eq _ ⟨i, _⟩ ⟨j, _⟩ (max' i j) (left_to_max i j) (right_to_max i j),
      LinearMap.map_smul, LinearMap.map_smul]
    rfl
  smul_zero r :=
    by
    erw [colimit_zero_eq _ (is_filtered.nonempty.some : J), colimit_smul_mk_eq, smul_zero]
    rfl
  zero_smul x := by
    apply Quot.inductionOn x; clear x; intro x; cases' x with j x
    erw [colimit_smul_mk_eq, zero_smul, colimit_zero_eq _ j]
    rfl
  add_smul r s x := by
    apply Quot.inductionOn x; clear x; intro x; cases' x with j x
    erw [colimit_smul_mk_eq, add_smul, colimit_smul_mk_eq, colimit_smul_mk_eq,
      colimit_add_mk_eq _ ⟨j, _⟩ ⟨j, _⟩ j (𝟙 j) (𝟙 j), CategoryTheory.Functor.map_id, id_apply,
      id_apply]
    rfl
#align Module.filtered_colimits.colimit_module ModuleCat.FilteredColimits.colimitModule

/-- The bundled `R`-module giving the filtered colimit of a diagram. -/
def colimit : ModuleCat R :=
  ModuleCat.of R M
#align Module.filtered_colimits.colimit ModuleCat.FilteredColimits.colimit

/-- The linear map from a given `R`-module in the diagram to the colimit module. -/
def coconeMorphism (j : J) : F.obj j ⟶ colimit :=
  {
    (AddCommGroupCat.FilteredColimits.colimitCocone
            (F ⋙ forget₂ (ModuleCat R) AddCommGroupCat.{max v u})).ι.app
      j with
    map_smul' := fun r x => by erw [colimit_smul_mk_eq F r ⟨j, x⟩]; rfl }
#align Module.filtered_colimits.cocone_morphism ModuleCat.FilteredColimits.coconeMorphism

/-- The cocone over the proposed colimit module. -/
def colimitCocone : cocone F where
  pt := colimit
  ι :=
    { app := cocone_morphism
      naturality' := fun j j' f =>
        LinearMap.coe_injective ((Types.colimitCocone (F ⋙ forget (ModuleCat R))).ι.naturality f) }
#align Module.filtered_colimits.colimit_cocone ModuleCat.FilteredColimits.colimitCocone

/-- Given a cocone `t` of `F`, the induced monoid linear map from the colimit to the cocone point.
We already know that this is a morphism between additive groups. The only thing left to see is that
it is a linear map, i.e. preserves scalar multiplication.
-/
def colimitDesc (t : cocone F) : colimit ⟶ t.pt :=
  {
    (AddCommGroupCat.FilteredColimits.colimitCoconeIsColimit
          (F ⋙ forget₂ (ModuleCat R) AddCommGroupCat.{max v u})).desc
      ((forget₂ (ModuleCat R) AddCommGroupCat.{max v u}).mapCocone t) with
    map_smul' := fun r x => by
      apply Quot.inductionOn x; clear x; intro x; cases' x with j x
      erw [colimit_smul_mk_eq]
      exact LinearMap.map_smul (t.ι.app j) r x }
#align Module.filtered_colimits.colimit_desc ModuleCat.FilteredColimits.colimitDesc

/-- The proposed colimit cocone is a colimit in `Module R`. -/
def colimitCoconeIsColimit : IsColimit colimit_cocone
    where
  desc := colimit_desc
  fac t j :=
    LinearMap.coe_injective <|
      (Types.colimitCoconeIsColimit (F ⋙ forget (ModuleCat R))).fac
        ((forget (ModuleCat R)).mapCocone t) j
  uniq t m h :=
    LinearMap.coe_injective <|
      (Types.colimitCoconeIsColimit (F ⋙ forget (ModuleCat R))).uniq
        ((forget (ModuleCat R)).mapCocone t) m fun j => funext fun x => LinearMap.congr_fun (h j) x
#align Module.filtered_colimits.colimit_cocone_is_colimit ModuleCat.FilteredColimits.colimitCoconeIsColimit

instance forget₂AddCommGroupPreservesFilteredColimits :
    PreservesFilteredColimits (forget₂ (ModuleCat R) AddCommGroupCat.{u})
    where PreservesFilteredColimits J _ _ :=
    {
      PreservesColimit := fun F =>
        preserves_colimit_of_preserves_colimit_cocone (colimit_cocone_is_colimit F)
          (AddCommGroupCat.FilteredColimits.colimitCoconeIsColimit
            (F ⋙ forget₂ (ModuleCat.{u} R) AddCommGroupCat.{u})) }
#align Module.filtered_colimits.forget₂_AddCommGroup_preserves_filtered_colimits ModuleCat.FilteredColimits.forget₂AddCommGroupPreservesFilteredColimits

instance forgetPreservesFilteredColimits : PreservesFilteredColimits (forget (ModuleCat.{u} R)) :=
  Limits.compPreservesFilteredColimits (forget₂ (ModuleCat R) AddCommGroupCat)
    (forget AddCommGroupCat)
#align Module.filtered_colimits.forget_preserves_filtered_colimits ModuleCat.FilteredColimits.forgetPreservesFilteredColimits

end

end ModuleCat.FilteredColimits

