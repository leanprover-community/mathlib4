/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Johan Commelin
-/
import Mathlib.Analysis.Normed.Group.SemiNormedGrp
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Analysis.Normed.Group.HomCompletion

/-!
# Completions of normed groups

This file contains an API for completions of seminormed groups (basic facts about
objects and morphisms).

## Main definitions

- `SemiNormedGrp.Completion : SemiNormedGrp ⥤ SemiNormedGrp` : the completion of a
  seminormed group (defined as a functor on `SemiNormedGrp` to itself).
- `SemiNormedGrp.Completion.lift (f : V ⟶ W) : (Completion.obj V ⟶ W)` : a normed group hom
  from `V` to complete `W` extends ("lifts") to a seminormed group hom from the completion of
  `V` to `W`.

## Projects

1. Construct the category of complete seminormed groups, say `CompleteSemiNormedGrp`
  and promote the `Completion` functor below to a functor landing in this category.
2. Prove that the functor `Completion : SemiNormedGrp ⥤ CompleteSemiNormedGrp`
  is left adjoint to the forgetful functor.

-/

noncomputable section

universe u

open UniformSpace MulOpposite CategoryTheory NormedAddGroupHom


namespace SemiNormedGrp

/-- The completion of a seminormed group, as an endofunctor on `SemiNormedGrp`. -/
@[simps]
def completion : SemiNormedGrp.{u} ⥤ SemiNormedGrp.{u} where
  obj V := SemiNormedGrp.of (Completion V)
  map f := f.completion
  map_id _ := completion_id
  map_comp f g := (completion_comp f g).symm

instance completion_completeSpace {V : SemiNormedGrp} : CompleteSpace (completion.obj V) :=
  Completion.completeSpace _

/-- The canonical morphism from a seminormed group `V` to its completion. -/
@[simps]
def completion.incl {V : SemiNormedGrp} : V ⟶ completion.obj V where
  toFun v := (v : Completion V)
  map_add' := Completion.coe_add
  bound' := ⟨1, fun v => by simp⟩

-- These lemmas have always been bad (https://github.com/leanprover-community/mathlib4/issues/7657), but https://github.com/leanprover/lean4/pull/2644 made `simp` start noticing
attribute [nolint simpNF] SemiNormedGrp.completion.incl_apply

theorem completion.norm_incl_eq {V : SemiNormedGrp} {v : V} : ‖completion.incl v‖ = ‖v‖ :=
  UniformSpace.Completion.norm_coe _

theorem completion.map_normNoninc {V W : SemiNormedGrp} {f : V ⟶ W} (hf : f.NormNoninc) :
    (completion.map f).NormNoninc :=
  NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.2 <|
    (NormedAddGroupHom.norm_completion f).le.trans <|
      NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.1 hf

variable (V W : SemiNormedGrp)

/-- Given a normed group hom `V ⟶ W`, this defines the associated morphism
from the completion of `V` to the completion of `W`.
The difference from the definition obtained from the functoriality of completion is in that the
map sending a morphism `f` to the associated morphism of completions is itself additive. -/
def completion.mapHom (V W : SemiNormedGrp.{u}) :
    -- Porting note: cannot see instances through concrete cats
    have (V W : SemiNormedGrp.{u}) : AddGroup (V ⟶ W) :=
      inferInstanceAs <| AddGroup <| NormedAddGroupHom V W
    (V ⟶ W) →+ (completion.obj V ⟶ completion.obj W) :=
  @AddMonoidHom.mk' _ _ (_) (_) completion.map fun f g => f.completion_add g

-- @[simp] -- Porting note: removed simp since LHS simplifies and is not used
theorem completion.map_zero (V W : SemiNormedGrp) : completion.map (0 : V ⟶ W) = 0 :=
  -- Porting note: cannot see instances through concrete cats
  @AddMonoidHom.map_zero _ _ (_) (_) (completion.mapHom V W)

instance : Preadditive SemiNormedGrp.{u} where
  homGroup P Q := inferInstanceAs <| AddCommGroup <| NormedAddGroupHom P Q
  add_comp _ Q _ f f' g := by
    ext x
    -- Porting note: failing simps probably due to instance synthesis issues with concrete
    -- cats; see the gymnastics below for what used to be
    -- simp only [add_apply, comp_apply. map_add]
    rw [NormedAddGroupHom.add_apply, CategoryTheory.comp_apply, CategoryTheory.comp_apply,
      CategoryTheory.comp_apply, @NormedAddGroupHom.add_apply _ _ (_) (_)]
    convert map_add g (f x) (f' x)
  comp_add _ _ _ _ _ _ := by
    ext
    -- Porting note: failing simps probably due to instance synthesis issues with concrete
    -- cats; see the gymnastics below for what used to be
    rw [NormedAddGroupHom.add_apply, CategoryTheory.comp_apply, CategoryTheory.comp_apply,
      CategoryTheory.comp_apply, @NormedAddGroupHom.add_apply _ _ (_) (_)]

instance : Functor.Additive completion where
  map_add := NormedAddGroupHom.completion_add _ _

/-- Given a normed group hom `f : V → W` with `W` complete, this provides a lift of `f` to
the completion of `V`. The lemmas `lift_unique` and `lift_comp_incl` provide the api for the
universal property of the completion. -/
def completion.lift {V W : SemiNormedGrp} [CompleteSpace W] [T0Space W] (f : V ⟶ W) :
    completion.obj V ⟶ W where
  toFun := f.extension
  map_add' := f.extension.toAddMonoidHom.map_add'
  bound' := f.extension.bound'

theorem completion.lift_comp_incl {V W : SemiNormedGrp} [CompleteSpace W] [T0Space W]
    (f : V ⟶ W) : completion.incl ≫ completion.lift f = f :=
  ext <| NormedAddGroupHom.extension_coe _

theorem completion.lift_unique {V W : SemiNormedGrp} [CompleteSpace W] [T0Space W]
    (f : V ⟶ W) (g : completion.obj V ⟶ W) : completion.incl ≫ g = f → g = completion.lift f :=
  fun h => (NormedAddGroupHom.extension_unique _ fun v =>
    ((NormedAddGroupHom.ext_iff.1 h) v).symm).symm

end SemiNormedGrp
