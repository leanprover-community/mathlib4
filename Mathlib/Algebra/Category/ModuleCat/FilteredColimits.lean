/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Basic

#align_import algebra.category.Module.filtered_colimits from "leanprover-community/mathlib"@"806bbb0132ba63b93d5edbe4789ea226f8329979"

/-!
# The forgetful functor from `R`-modules preserves filtered colimits.

Forgetful functors from algebraic categories usually don't preserve colimits. However, they tend
to preserve _filtered_ colimits.

In this file, we start with a ring `R`, a small filtered category `J` and a functor
`F : J ⥤ ModuleCat R`. We show that the colimit of `F ⋙ forget₂ (ModuleCat R) AddCommGrp`
(in `AddCommGrp`) carries the structure of an `R`-module, thereby showing that the forgetful
functor `forget₂ (ModuleCat R) AddCommGrp` preserves filtered colimits. In particular, this
implies that `forget (ModuleCat R)` preserves filtered colimits.

-/


universe v u

noncomputable section

open scoped Classical

open CategoryTheory CategoryTheory.Limits

open CategoryTheory.IsFiltered renaming max → max' -- avoid name collision with `_root_.max`.

open AddMonCat.FilteredColimits (colimit_zero_eq colimit_add_mk_eq)

namespace ModuleCat.FilteredColimits

section

variable {R : Type u} [Ring R] {J : Type v} [SmallCategory J] [IsFiltered J]
variable (F : J ⥤ ModuleCatMax.{v, u, u} R)

/-- The colimit of `F ⋙ forget₂ (ModuleCat R) AddCommGrp` in the category `AddCommGrp`.
In the following, we will show that this has the structure of an `R`-module.
-/
abbrev M : AddCommGrp :=
  AddCommGrp.FilteredColimits.colimit.{v, u}
    (F ⋙ forget₂ (ModuleCat R) AddCommGrp.{max v u})
set_option linter.uppercaseLean3 false in
#align Module.filtered_colimits.M ModuleCat.FilteredColimits.M

/-- The canonical projection into the colimit, as a quotient type. -/
abbrev M.mk : (Σ j, F.obj j) → M F :=
  Quot.mk (Types.Quot.Rel (F ⋙ forget (ModuleCat R)))
set_option linter.uppercaseLean3 false in
#align Module.filtered_colimits.M.mk ModuleCat.FilteredColimits.M.mk

theorem M.mk_eq (x y : Σ j, F.obj j)
    (h : ∃ (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k), F.map f x.2 = F.map g y.2) : M.mk F x = M.mk F y :=
  Quot.EqvGen_sound (Types.FilteredColimit.eqvGen_quot_rel_of_rel (F ⋙ forget (ModuleCat R)) x y h)
set_option linter.uppercaseLean3 false in
#align Module.filtered_colimits.M.mk_eq ModuleCat.FilteredColimits.M.mk_eq

/-- The "unlifted" version of scalar multiplication in the colimit. -/
def colimitSMulAux (r : R) (x : Σ j, F.obj j) : M F :=
  M.mk F ⟨x.1, r • x.2⟩
set_option linter.uppercaseLean3 false in
#align Module.filtered_colimits.colimit_smul_aux ModuleCat.FilteredColimits.colimitSMulAux

theorem colimitSMulAux_eq_of_rel (r : R) (x y : Σ j, F.obj j)
    (h : Types.FilteredColimit.Rel (F ⋙ forget (ModuleCat R)) x y) :
    colimitSMulAux F r x = colimitSMulAux F r y := by
  apply M.mk_eq
  obtain ⟨k, f, g, hfg⟩ := h
  use k, f, g
  simp only [Functor.comp_obj, Functor.comp_map, forget_map] at hfg
  simp [hfg]
set_option linter.uppercaseLean3 false in
#align Module.filtered_colimits.colimit_smul_aux_eq_of_rel ModuleCat.FilteredColimits.colimitSMulAux_eq_of_rel

/-- Scalar multiplication in the colimit. See also `colimitSMulAux`. -/
instance colimitHasSMul : SMul R (M F) where
  smul r x := by
    refine Quot.lift (colimitSMulAux F r) ?_ x
    intro x y h
    apply colimitSMulAux_eq_of_rel
    apply Types.FilteredColimit.rel_of_quot_rel
    exact h
set_option linter.uppercaseLean3 false in
#align Module.filtered_colimits.colimit_has_smul ModuleCat.FilteredColimits.colimitHasSMul

@[simp]
theorem colimit_smul_mk_eq (r : R) (x : Σ j, F.obj j) : r • M.mk F x = M.mk F ⟨x.1, r • x.2⟩ :=
  rfl
set_option linter.uppercaseLean3 false in
#align Module.filtered_colimits.colimit_smul_mk_eq ModuleCat.FilteredColimits.colimit_smul_mk_eq

private theorem colimitModule.one_smul (x : (M F)) : (1 : R) • x = x := by
  refine Quot.inductionOn x ?_; clear x; intro x; cases' x with j x
  erw [colimit_smul_mk_eq F 1 ⟨j, x⟩]
  simp
  rfl

-- Porting note (#11083): writing directly the `Module` instance makes things very slow.
instance colimitMulAction : MulAction R (M F) where
  one_smul x := by
    refine Quot.inductionOn x ?_; clear x; intro x; cases' x with j x
    erw [colimit_smul_mk_eq F 1 ⟨j, x⟩, one_smul]
    rfl
  mul_smul r s x := by
    refine Quot.inductionOn x ?_; clear x; intro x; cases' x with j x
    erw [colimit_smul_mk_eq F (r * s) ⟨j, x⟩, colimit_smul_mk_eq F s ⟨j, x⟩,
      colimit_smul_mk_eq F r ⟨j, _⟩, mul_smul]

instance colimitSMulWithZero : SMulWithZero R (M F) :=
{ colimitMulAction F with
  smul_zero := fun r => by
    erw [colimit_zero_eq _ (IsFiltered.nonempty.some : J), colimit_smul_mk_eq, smul_zero]
    rfl
  zero_smul := fun x => by
    refine Quot.inductionOn x ?_; clear x; intro x; cases' x with j x
    erw [colimit_smul_mk_eq, zero_smul, colimit_zero_eq _ j]
    rfl }

private theorem colimitModule.add_smul (r s : R) (x : (M F)) : (r + s) • x = r • x + s • x := by
  refine Quot.inductionOn x ?_; clear x; intro x; cases' x with j x
  erw [colimit_smul_mk_eq, _root_.add_smul, colimit_smul_mk_eq, colimit_smul_mk_eq,
      colimit_add_mk_eq _ ⟨j, _⟩ ⟨j, _⟩ j (𝟙 j) (𝟙 j)]
  simp only [Functor.comp_obj, forget₂_obj, Functor.comp_map, CategoryTheory.Functor.map_id,
    forget₂_map]
  rfl

instance colimitModule : Module R (M F) :=
{ colimitMulAction F,
  colimitSMulWithZero F with
  smul_add := fun r x y => by
    refine Quot.induction_on₂ x y ?_; clear x y; intro x y; cases' x with i x; cases' y with j y
    erw [colimit_add_mk_eq _ ⟨i, _⟩ ⟨j, _⟩ (max' i j) (IsFiltered.leftToMax i j)
      (IsFiltered.rightToMax i j), colimit_smul_mk_eq, smul_add, colimit_smul_mk_eq,
      colimit_smul_mk_eq, colimit_add_mk_eq _ ⟨i, _⟩ ⟨j, _⟩ (max' i j) (IsFiltered.leftToMax i j)
      (IsFiltered.rightToMax i j), LinearMap.map_smul, LinearMap.map_smul]
    rfl
  add_smul := colimitModule.add_smul F }

set_option linter.uppercaseLean3 false in
#align Module.filtered_colimits.colimit_module ModuleCat.FilteredColimits.colimitModule

/-- The bundled `R`-module giving the filtered colimit of a diagram. -/
def colimit : ModuleCatMax.{v, u, u} R :=
  ModuleCat.of R (M F)
set_option linter.uppercaseLean3 false in
#align Module.filtered_colimits.colimit ModuleCat.FilteredColimits.colimit

/-- The linear map from a given `R`-module in the diagram to the colimit module. -/
def coconeMorphism (j : J) : F.obj j ⟶ colimit F :=
  { (AddCommGrp.FilteredColimits.colimitCocone
      (F ⋙ forget₂ (ModuleCat R) AddCommGrp.{max v u})).ι.app j with
    map_smul' := fun r x => by erw [colimit_smul_mk_eq F r ⟨j, x⟩]; rfl }
set_option linter.uppercaseLean3 false in
#align Module.filtered_colimits.cocone_morphism ModuleCat.FilteredColimits.coconeMorphism

/-- The cocone over the proposed colimit module. -/
def colimitCocone : Cocone F where
  pt := colimit F
  ι :=
    { app := coconeMorphism F
      naturality := fun _ _' f =>
        LinearMap.coe_injective
          ((Types.TypeMax.colimitCocone (F ⋙ forget (ModuleCat R))).ι.naturality f) }
set_option linter.uppercaseLean3 false in
#align Module.filtered_colimits.colimit_cocone ModuleCat.FilteredColimits.colimitCocone

/-- Given a cocone `t` of `F`, the induced monoid linear map from the colimit to the cocone point.
We already know that this is a morphism between additive groups. The only thing left to see is that
it is a linear map, i.e. preserves scalar multiplication.
-/
def colimitDesc (t : Cocone F) : colimit F ⟶ t.pt :=
  { (AddCommGrp.FilteredColimits.colimitCoconeIsColimit
          (F ⋙ forget₂ (ModuleCatMax.{v, u} R) AddCommGrp.{max v u})).desc
      ((forget₂ (ModuleCat R) AddCommGrp.{max v u}).mapCocone t) with
    map_smul' := fun r x => by
      refine Quot.inductionOn x ?_; clear x; intro x; cases' x with j x
      erw [colimit_smul_mk_eq]
      exact LinearMap.map_smul (t.ι.app j) r x }
set_option linter.uppercaseLean3 false in
#align Module.filtered_colimits.colimit_desc ModuleCat.FilteredColimits.colimitDesc

/-- The proposed colimit cocone is a colimit in `ModuleCat R`. -/
def colimitCoconeIsColimit : IsColimit (colimitCocone F) where
  desc := colimitDesc F
  fac t j :=
    LinearMap.coe_injective <|
      (Types.TypeMax.colimitCoconeIsColimit.{v, u} (F ⋙ forget (ModuleCat R))).fac
        ((forget (ModuleCat R)).mapCocone t) j
  uniq t _ h :=
    LinearMap.coe_injective <|
      (Types.TypeMax.colimitCoconeIsColimit (F ⋙ forget (ModuleCat R))).uniq
        ((forget (ModuleCat R)).mapCocone t) _ fun j => funext fun x => LinearMap.congr_fun (h j) x
set_option linter.uppercaseLean3 false in
#align Module.filtered_colimits.colimit_cocone_is_colimit ModuleCat.FilteredColimits.colimitCoconeIsColimit

instance forget₂AddCommGroupPreservesFilteredColimits :
    PreservesFilteredColimits (forget₂ (ModuleCat.{u} R) AddCommGrp.{u}) where
  preserves_filtered_colimits J _ _ :=
  { -- Porting note: without the curly braces for `F`
    -- here we get a confusing error message about universes.
    preservesColimit := fun {F : J ⥤ ModuleCat.{u} R} =>
      preservesColimitOfPreservesColimitCocone (colimitCoconeIsColimit F)
        (AddCommGrp.FilteredColimits.colimitCoconeIsColimit
          (F ⋙ forget₂ (ModuleCat.{u} R) AddCommGrp.{u})) }
set_option linter.uppercaseLean3 false in
#align Module.filtered_colimits.forget₂_AddCommGroup_preserves_filtered_colimits ModuleCat.FilteredColimits.forget₂AddCommGroupPreservesFilteredColimits

instance forgetPreservesFilteredColimits : PreservesFilteredColimits (forget (ModuleCat.{u} R)) :=
  Limits.compPreservesFilteredColimits (forget₂ (ModuleCat R) AddCommGrp)
    (forget AddCommGrp)
set_option linter.uppercaseLean3 false in
#align Module.filtered_colimits.forget_preserves_filtered_colimits ModuleCat.FilteredColimits.forgetPreservesFilteredColimits

end

end ModuleCat.FilteredColimits
