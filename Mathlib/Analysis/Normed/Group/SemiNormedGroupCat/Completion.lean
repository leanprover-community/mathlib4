/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Johan Commelin
-/
import Mathlib.Analysis.Normed.Group.SemiNormedGroupCat
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Analysis.Normed.Group.HomCompletion

#align_import analysis.normed.group.SemiNormedGroup.completion from "leanprover-community/mathlib"@"17ef379e997badd73e5eabb4d38f11919ab3c4b3"

/-!
# Completions of normed groups

This file contains an API for completions of seminormed groups (basic facts about
objects and morphisms).

## Main definitions

- `SemiNormedGroupCat.Completion : SemiNormedGroupCat ⥤ SemiNormedGroupCat` : the completion of a
  seminormed group (defined as a functor on `SemiNormedGroupCat` to itself).
- `SemiNormedGroupCat.Completion.lift (f : V ⟶ W) : (Completion.obj V ⟶ W)` : a normed group hom
  from `V` to complete `W` extends ("lifts") to a seminormed group hom from the completion of
  `V` to `W`.

## Projects

1. Construct the category of complete seminormed groups, say `CompleteSemiNormedGroupCat`
  and promote the `Completion` functor below to a functor landing in this category.
2. Prove that the functor `Completion : SemiNormedGroupCat ⥤ CompleteSemiNormedGroupCat`
  is left adjoint to the forgetful functor.

-/

noncomputable section

universe u

open UniformSpace MulOpposite CategoryTheory NormedAddGroupHom

set_option linter.uppercaseLean3 false

namespace SemiNormedGroupCat

/-- The completion of a seminormed group, as an endofunctor on `SemiNormedGroupCat`. -/
@[simps]
def completion : SemiNormedGroupCat.{u} ⥤ SemiNormedGroupCat.{u} where
  obj V := SemiNormedGroupCat.of (Completion V)
  map f := f.completion
  map_id _ := completion_id
  map_comp f g := (completion_comp f g).symm
#align SemiNormedGroup.Completion SemiNormedGroupCat.completion

instance completion_completeSpace {V : SemiNormedGroupCat} : CompleteSpace (completion.obj V) :=
  Completion.completeSpace _
#align SemiNormedGroup.Completion_complete_space SemiNormedGroupCat.completion_completeSpace

/-- The canonical morphism from a seminormed group `V` to its completion. -/
@[simps]
def completion.incl {V : SemiNormedGroupCat} : V ⟶ completion.obj V where
  toFun v := (v : Completion V)
  map_add' := Completion.coe_add
  bound' := ⟨1, fun v => by simp⟩
#align SemiNormedGroup.Completion.incl SemiNormedGroupCat.completion.incl

-- These lemmas have always been bad (#7657), but leanprover/lean4#2644 made `simp` start noticing
attribute [nolint simpNF] SemiNormedGroupCat.completion.incl_apply

theorem completion.norm_incl_eq {V : SemiNormedGroupCat} {v : V} : ‖completion.incl v‖ = ‖v‖ :=
  UniformSpace.Completion.norm_coe _
#align SemiNormedGroup.Completion.norm_incl_eq SemiNormedGroupCat.completion.norm_incl_eq

theorem completion.map_normNoninc {V W : SemiNormedGroupCat} {f : V ⟶ W} (hf : f.NormNoninc) :
    (completion.map f).NormNoninc :=
  NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.2 <|
    (NormedAddGroupHom.norm_completion f).le.trans <|
      NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.1 hf
#align SemiNormedGroup.Completion.map_norm_noninc SemiNormedGroupCat.completion.map_normNoninc

variable (V W : SemiNormedGroupCat)

/-- Given a normed group hom `V ⟶ W`, this defines the associated morphism
from the completion of `V` to the completion of `W`.
The difference from the definition obtained from the functoriality of completion is in that the
map sending a morphism `f` to the associated morphism of completions is itself additive. -/
def completion.mapHom (V W : SemiNormedGroupCat.{u}) :
    -- Porting note: cannot see instances through concrete cats
    have (V W : SemiNormedGroupCat.{u}) : AddGroup (V ⟶ W) :=
      inferInstanceAs <| AddGroup <| NormedAddGroupHom V W
    (V ⟶ W) →+ (completion.obj V ⟶ completion.obj W) :=
  @AddMonoidHom.mk' _ _ (_) (_) completion.map fun f g => f.completion_add g
#align SemiNormedGroup.Completion.map_hom SemiNormedGroupCat.completion.mapHom

-- @[simp] -- Porting note: removed simp since LHS simplifies and is not used
theorem completion.map_zero (V W : SemiNormedGroupCat) : completion.map (0 : V ⟶ W) = 0 :=
  -- Porting note: cannot see instances through concrete cats
  @AddMonoidHom.map_zero _ _ (_) (_) (completion.mapHom V W)
#align SemiNormedGroup.Completion.map_zero SemiNormedGroupCat.completion.map_zero

instance : Preadditive SemiNormedGroupCat.{u} where
  homGroup P Q := inferInstanceAs <| AddCommGroup <| NormedAddGroupHom P Q
  add_comp _ Q _ f f' g := by
    ext x
    -- Porting note: failing simps probably due to instance synthesis issues with concrete
    -- cats; see the gymnastics below for what used to be
    -- simp only [add_apply, comp_apply. map_add]
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    rw [NormedAddGroupHom.add_apply]; erw [CategoryTheory.comp_apply, CategoryTheory.comp_apply,
      CategoryTheory.comp_apply, @NormedAddGroupHom.add_apply _ _ (_) (_)]
    convert map_add g (f x) (f' x)
  comp_add _ _ _ _ _ _ := by
    ext
    -- Porting note: failing simps probably due to instance synthesis issues with concrete
    -- cats; see the gymnastics below for what used to be
    -- simp only [add_apply, comp_apply. map_add]
    rw [NormedAddGroupHom.add_apply]
    -- This used to be a single `rw`, but we need `erw` after leanprover/lean4#2644
    erw [CategoryTheory.comp_apply, CategoryTheory.comp_apply,
      CategoryTheory.comp_apply, @NormedAddGroupHom.add_apply _ _ (_) (_)]
    rfl

instance : Functor.Additive completion where
  map_add := NormedAddGroupHom.completion_add _ _

/-- Given a normed group hom `f : V → W` with `W` complete, this provides a lift of `f` to
the completion of `V`. The lemmas `lift_unique` and `lift_comp_incl` provide the api for the
universal property of the completion. -/
def completion.lift {V W : SemiNormedGroupCat} [CompleteSpace W] [T0Space W] (f : V ⟶ W) :
    completion.obj V ⟶ W where
  toFun := f.extension
  map_add' := f.extension.toAddMonoidHom.map_add'
  bound' := f.extension.bound'
#align SemiNormedGroup.Completion.lift SemiNormedGroupCat.completion.lift

theorem completion.lift_comp_incl {V W : SemiNormedGroupCat} [CompleteSpace W] [T0Space W]
    (f : V ⟶ W) : completion.incl ≫ completion.lift f = f :=
  ext <| NormedAddGroupHom.extension_coe _
#align SemiNormedGroup.Completion.lift_comp_incl SemiNormedGroupCat.completion.lift_comp_incl

theorem completion.lift_unique {V W : SemiNormedGroupCat} [CompleteSpace W] [T0Space W]
    (f : V ⟶ W) (g : completion.obj V ⟶ W) : completion.incl ≫ g = f → g = completion.lift f :=
  fun h => (NormedAddGroupHom.extension_unique _ fun v => ((ext_iff.1 h) v).symm).symm
#align SemiNormedGroup.Completion.lift_unique SemiNormedGroupCat.completion.lift_unique

end SemiNormedGroupCat
