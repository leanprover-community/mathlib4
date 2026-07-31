/-
Copyright (c) 2024 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Filtered.OfColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Limits.Preserves.Grothendieck
public import Mathlib.CategoryTheory.Limits.Final

meta import Lean.PostprocessTraces

/-!
# Inferring Filteredness from Filteredness of Costructured Arrow Categories

## References

* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Proposition 3.1.8

-/


open Lean.PostprocessTraces

public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits CategoryTheory.Functor

section Small

variable {A : Type u₁} [SmallCategory A] {B : Type u₁} [SmallCategory B]
variable {T : Type u₁} [SmallCategory T]

private meta partial def elideBelow (p : TracePattern) : TracePostprocessor :=
  fun trees => trees.mapM go
where
  go (t : TraceTree) : Lean.CoreM TraceTree := do
    match t with
    | .leaf msg => return .leaf msg
    | .node data msg children wrap =>
      if ← p t then
        return .node data m!"{msg} (truncated)" #[] wrap
      else
        return .node data msg (← children.mapM go) wrap

/-! # Issue -/

-- `simp only [Cat.of_α]` rewrites the shape carrier of `colim` to `CostructuredArrow L (R.obj b)`
-- but leaves that `colim`'s `Category` instance typed at the old spelling
-- `↑(Cat.of (CostructuredArrow …))`. Synthesizing the lemma's `HasColimitsOfShape` argument (via
-- `Types.hasColimitsOfShape`) must reproduce this carrier-vs-instance mismatch through an
-- instance-typed mvar, which denies the assignment (trace below): the direct `.instances` check
-- can't cross the `CostructuredArrow =?= ↑(Cat.of …)` boundary, and under `markOrSynth` the
-- re-synthesis fallback finds `instCategoryCostructuredArrow_1`, which is not defeq to the unified
-- instance either.
set_option linter.style.longLine false in
/--
error: failed to synthesize instance of type class
  HasColimitsOfShape (CostructuredArrow L (R.obj b)) (Type u₁)
---
trace: [Meta.synthInstance] ❌️ HasColimitsOfShape (CostructuredArrow L (R.obj b)) (Type u₁)
  [Meta.synthInstance.apply] ❌️ apply @Types.hasColimitsOfShape to HasColimitsOfShape (CostructuredArrow L (R.obj b))
        (Type u₁)
    [Meta.synthInstance.tryResolve] ❌️ HasColimitsOfShape (CostructuredArrow L (R.obj b))
          (Type u₁) ≟ HasColimitsOfShape ?m.79 (Type ?u.120)
      [Meta.isDefEq] ❌️ [instances] HasColimitsOfShape (CostructuredArrow L (R.obj b))
            (Type u₁) =?= HasColimitsOfShape ?m.79 (Type ?u.120)
        [Meta.isDefEq] ❌️ [instances] (Cat.of (CostructuredArrow L (R.obj b))).str =?= ?m.80
          [Meta.isDefEq.assign.checkTypes] ❌️ (?m.80 : Category.{?u.121, u₁}
                (CostructuredArrow L
                  (R.obj
                    b))) := ((Cat.of
                  (CostructuredArrow L (R.obj b))).str : Category.{u₁, u₁} ↑(Cat.of (CostructuredArrow L (R.obj b))))
            [Meta.isDefEq] ❌️ [instances] Category.{?u.121, u₁}
                  (CostructuredArrow L (R.obj b)) =?= Category.{u₁, u₁} ↑(Cat.of (CostructuredArrow L (R.obj b)))
              [Meta.isDefEq] ❌️ [instances] CostructuredArrow L (R.obj b) =?= ↑(Cat.of (CostructuredArrow L (R.obj b)))
                [Meta.isDefEq] ❌️ [instances] CostructuredArrow L
                      (R.obj b) =?= (Cat.of (CostructuredArrow L (R.obj b))).1
                  [Meta.isDefEq.onFailure] ❌️ CostructuredArrow L
                        (R.obj b) =?= (Cat.of (CostructuredArrow L (R.obj b))).1
              [Meta.isDefEq.onFailure] ❌️ Category.{?u.121, u₁}
                    (CostructuredArrow L (R.obj b)) =?= Category.{u₁, u₁} ↑(Cat.of (CostructuredArrow L (R.obj b)))
            [Meta.synthInstance] ✅️ Category.{u₁, u₁} (CostructuredArrow L (R.obj b)) (truncated)
            [Meta.isDefEq] ❌️ [instances] (Cat.of
                    (CostructuredArrow L (R.obj b))).str =?= instCategoryCostructuredArrow_1 L (R.obj b) (truncated)
          [Meta.isDefEq.assign.checkTypes] ❌️ (?m.80 : Category.{?u.121, u₁}
                (CostructuredArrow L
                  (R.obj
                    b))) := ((Cat.of
                  (CostructuredArrow L (R.obj b))).2 : Category.{u₁, u₁} (Cat.of (CostructuredArrow L (R.obj b))).1)
            [Meta.isDefEq] ❌️ [instances] Category.{?u.121, u₁}
                  (CostructuredArrow L (R.obj b)) =?= Category.{u₁, u₁} (Cat.of (CostructuredArrow L (R.obj b))).1
              [Meta.isDefEq] ❌️ [instances] CostructuredArrow L (R.obj b) =?= (Cat.of (CostructuredArrow L (R.obj b))).1
                [Meta.isDefEq.onFailure] ❌️ CostructuredArrow L (R.obj b) =?= (Cat.of (CostructuredArrow L (R.obj b))).1
              [Meta.isDefEq.onFailure] ❌️ Category.{?u.121, u₁}
                    (CostructuredArrow L (R.obj b)) =?= Category.{u₁, u₁} (Cat.of (CostructuredArrow L (R.obj b))).1
            [Meta.synthInstance] ✅️ Category.{u₁, u₁} (CostructuredArrow L (R.obj b)) (truncated)
            [Meta.isDefEq] ❌️ [instances] (Cat.of
                    (CostructuredArrow L (R.obj b))).2 =?= instCategoryCostructuredArrow_1 L (R.obj b) (truncated)
-/
#guard_msgs in
postprocess_traces
  filterSubtrees (fun x => (ofClass `Meta.synthInstance.apply x) <&&>
    containsString "Types.hasColimitsOfShape" x)
  >=> filterSubtrees (fun x => (ofClass `Meta.isDefEq.assign.checkTypes x) <&&> failed x)
  >=> elideBelow (fun x => (ofClass `Meta.synthInstance x) <&&> succeeded x)
  >=> elideBelow (fun x => (ofClass `Meta.isDefEq x) <&&>
    containsString "instCategoryCostructuredArrow_1" x)
in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
example (L : A ⥤ T) (R : B ⥤ T)
    [IsFiltered B] [Final R] [∀ b, IsFiltered (CostructuredArrow L (R.obj b))] : IsFiltered A := by
  refine isFiltered_of_nonempty_limit_colimit_to_colimit_limit fun J {_ _} F => ⟨?_⟩
  haveI : ∀ b, PreservesLimitsOfShape J
      (colim (J := (R ⋙ CostructuredArrow.functor L).obj b) (C := Type u₁)) := fun b => by
    simp only [comp_obj, CostructuredArrow.functor_obj, Cat.of_α]
    set_option trace.Meta.synthInstance true in
    set_option trace.Meta.isDefEq true in
    set_option trace.Meta.isDefEq.printTransparency true in
    set_option trace.Meta.isDefEq.assign.checkTypes true in
    exact filtered_colim_preservesFiniteLimits
  sorry

/-! # Fix -/

theorem Cat.of_str {C} [inst : Category C] : (Cat.of C).str = inst := rfl

-- Adding `Cat.of_str` to the `simp only` set rewrites the desynced `colim` `Category` instance back
-- to `CostructuredArrow`'s own `instCategoryCostructuredArrow_1`, realigning carrier and instance
-- so that `HasColimitsOfShape` synthesis needs no cross-boundary assignment.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma isFiltered_of_isFiltered_costructuredArrow_small (L : A ⥤ T) (R : B ⥤ T)
    [IsFiltered B] [Final R] [∀ b, IsFiltered (CostructuredArrow L (R.obj b))] : IsFiltered A := by
  refine isFiltered_of_nonempty_limit_colimit_to_colimit_limit fun J {_ _} F => ⟨?_⟩
  let R' := Grothendieck.pre (CostructuredArrow.functor L) R
  haveI : ∀ b, PreservesLimitsOfShape J
      (colim (J := (R ⋙ CostructuredArrow.functor L).obj b) (C := Type u₁)) := fun b => by
    simp only [comp_obj, CostructuredArrow.functor_obj, Cat.of_α, Cat.of_str] -- Added: `Cat.of_str`
    exact filtered_colim_preservesFiniteLimits
  refine lim.map ((colimitIsoColimitGrothendieck L F.flip).hom ≫
    (inv (colimit.pre (CostructuredArrow.grothendieckProj L ⋙ F.flip) R'))) ≫
    (colimitLimitIso (R' ⋙ CostructuredArrow.grothendieckProj L ⋙ F.flip).flip).inv ≫
    colim.map ?_ ≫
    colimit.pre _ R' ≫
    (colimitIsoColimitGrothendieck L (limit F)).inv
  exact (limitCompWhiskeringLeftIsoCompLimit F (R' ⋙ CostructuredArrow.grothendieckProj L)).hom

end Small

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
variable {T : Type u₃} [Category.{v₃} T]

/-- Given functors `L : A ⥤ T` and `R : B ⥤ T` with a common codomain we can conclude that `A`
is filtered given that `R` is final, `B` is filtered and each costructured arrow category
`CostructuredArrow L (R.obj b)` is filtered. -/
theorem isFiltered_of_isFiltered_costructuredArrow (L : A ⥤ T) (R : B ⥤ T)
    [IsFiltered B] [Final R] [∀ b, IsFiltered (CostructuredArrow L (R.obj b))] : IsFiltered A := by
  let sA : A ≌ AsSmall.{max u₁ u₂ u₃ v₁ v₂ v₃} A := AsSmall.equiv
  let sB : B ≌ AsSmall.{max u₁ u₂ u₃ v₁ v₂ v₃} B := AsSmall.equiv
  let sT : T ≌ AsSmall.{max u₁ u₂ u₃ v₁ v₂ v₃} T := AsSmall.equiv
  let sC : ∀ b, CostructuredArrow (sA.inverse ⋙ L ⋙ sT.functor)
      ((sB.inverse ⋙ R ⋙ sT.functor).obj ⟨b⟩) ≌ CostructuredArrow L (R.obj b) := fun b =>
    (CostructuredArrow.pre sA.inverse (L ⋙ sT.functor) _).asEquivalence.trans
      (CostructuredArrow.post L sT.functor _).asEquivalence.symm
  have : ∀ b, IsFiltered (CostructuredArrow _ ((sB.inverse ⋙ R ⋙ sT.functor).obj b)) :=
    fun b => IsFiltered.of_equivalence (sC b.1).symm
  have := isFiltered_of_isFiltered_costructuredArrow_small
    (sA.inverse ⋙ L ⋙ sT.functor) (sB.inverse ⋙ R ⋙ sT.functor)
  exact IsFiltered.of_equivalence sA.symm

end CategoryTheory
