/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.FinCategory.AsType
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.Data.Fintype.Option

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback  -- shake: keep (`example`)

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Categories with finite limits.

A typeclass for categories with all finite (co)limits.
-/

public section


universe w' w v' u' v u

noncomputable section

open CategoryTheory

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]

-- We can't just made this an `abbrev`
-- because of https://github.com/leanprover-community/lean/issues/429
/-- A category has all finite limits if every functor `J ⥤ C` with a `FinCategory J`
instance and `J : Type` has a limit.

This is often called 'finitely complete'.
-/
class HasFiniteLimits : Prop where
  /-- `C` has all limits over any type `J` whose objects and morphisms lie in the same universe
  and which has `FinType` objects and morphisms -/
  out (J : Type) [𝒥 : SmallCategory J] [@FinCategory J 𝒥] : @HasLimitsOfShape J 𝒥 C _

/-- A category has all finite colimits if every functor `J ⥤ C` with a `FinCategory J`
instance and `J : Type` has a colimit.

This is often called 'finitely cocomplete'.
-/
@[to_dual]
class HasFiniteColimits : Prop where
  /-- `C` has all colimits over any type `J` whose objects and morphisms lie in the same universe
  and which has `Fintype` objects and morphisms -/
  out (J : Type) [𝒥 : SmallCategory J] [@FinCategory J 𝒥] : @HasColimitsOfShape J 𝒥 C _

-- See note [instance argument order]
@[to_dual]
instance (priority := 100) hasLimitsOfShape_of_hasFiniteLimits [HasFiniteLimits C] (J : Type w)
    [SmallCategory J] [FinCategory J] : HasLimitsOfShape J C := by
  apply @hasLimitsOfShape_of_equivalence _ _ _ _ _ _ (FinCategory.equivAsType J) ?_
  apply HasFiniteLimits.out

@[to_dual]
lemma hasFiniteLimits_of_hasLimitsOfSize [HasLimitsOfSize.{v', u'} C] :
    HasFiniteLimits C where
  out := fun J hJ hJ' =>
    haveI := hasLimitsOfSizeShrink.{0, 0} C
    let F := @FinCategory.equivAsType J (@FinCategory.fintypeObj J hJ hJ') hJ hJ'
    @hasLimitsOfShape_of_equivalence (@FinCategory.AsType J (@FinCategory.fintypeObj J hJ hJ'))
    (@FinCategory.categoryAsType J (@FinCategory.fintypeObj J hJ hJ') hJ hJ') _ _ J hJ F _

/-- If `C` has all limits, it has finite limits. -/
@[to_dual]
instance (priority := 100) hasFiniteLimits_of_hasLimits [HasLimits C] : HasFiniteLimits C :=
  hasFiniteLimits_of_hasLimitsOfSize C

@[to_dual]
instance (priority := 90) hasFiniteLimits_of_hasLimitsOfSize₀ [HasLimitsOfSize.{0, 0} C] :
    HasFiniteLimits C :=
  hasFiniteLimits_of_hasLimitsOfSize C

instance (J : Type) [hJ : SmallCategory J] : Category (ULiftHom (ULift J)) :=
  (@ULiftHom.category (ULift J) (@uliftCategory J hJ))

/-- We can always derive `HasFiniteLimits C` by providing limits at an
arbitrary universe. -/
@[to_dual
/-- We can always derive `HasFiniteColimits C` by providing colimits at an
arbitrary universe. -/]
theorem hasFiniteLimits_of_hasFiniteLimits_of_size
    (h : ∀ (J : Type w) {𝒥 : SmallCategory J} (_ : @FinCategory J 𝒥), HasLimitsOfShape J C) :
    HasFiniteLimits C where
  out := fun J hJ hhJ => by
    have := h (ULiftHom.{w} (ULift.{w} J)) <| @CategoryTheory.finCategoryUlift J hJ hhJ
    have l : @Equivalence J (ULiftHom (ULift J)) hJ
                          (@ULiftHom.category (ULift J) (@uliftCategory J hJ)) :=
      @ULiftHomULiftCategory.equiv J hJ
    apply @hasLimitsOfShape_of_equivalence (ULiftHom (ULift J))
      (@ULiftHom.category (ULift J) (@uliftCategory J hJ)) C _ J hJ l.symm _

section

open WalkingParallelPair WalkingParallelPairHom

instance fintypeWalkingParallelPair : Fintype WalkingParallelPair where
  elems := [WalkingParallelPair.zero, WalkingParallelPair.one].toFinset
  complete x := by cases x <;> simp

instance instFintypeWalkingParallelPairHom (j j' : WalkingParallelPair) :
    Fintype (WalkingParallelPairHom j j') where
  elems :=
    WalkingParallelPair.recOn j
      (WalkingParallelPair.recOn j' [WalkingParallelPairHom.id zero].toFinset
        [left, right].toFinset)
      (WalkingParallelPair.recOn j' ∅ [WalkingParallelPairHom.id one].toFinset)
  complete := by rintro (_ | _ | (_ | _)) <;> simp
end

instance : FinCategory WalkingParallelPair where
  fintypeObj := fintypeWalkingParallelPair
  fintypeHom := instFintypeWalkingParallelPairHom

/-- Equalizers are finite limits, so if `C` has all finite limits, it also has all equalizers -/
example [HasFiniteLimits C] : HasEqualizers C := by infer_instance

/-- Coequalizers are finite colimits, of if `C` has all finite colimits, it also has all
coequalizers -/
example [HasFiniteColimits C] : HasCoequalizers C := by infer_instance

variable {J : Type v}

-- Porting note: we would like to write something like:
-- attribute [local aesop safe cases] WidePullbackShape WidePushoutShape
-- But aesop can't add a `cases` attribute to type synonyms.

namespace WidePullbackShape

@[to_dual]
instance fintypeObj [Fintype J] : Fintype (WidePullbackShape J) :=
  inferInstanceAs <| Fintype (Option _)

@[to_dual (reorder := j j')]
instance fintypeHom (j j' : WidePullbackShape J) : Fintype (j ⟶ j') where
  elems := by
    obtain - | j' := j'
    · obtain - | j := j
      · exact {Hom.id none}
      · exact {Hom.term j}
    · by_cases h : some j' = j
      · rw [h]
        exact {Hom.id j}
      · exact ∅
  complete := by
    rintro (_ | _)
    · cases j <;> simp
    · simp

end WidePullbackShape

@[to_dual]
instance finCategoryWidePullback [Fintype J] : FinCategory (WidePullbackShape J) where
  fintypeHom := WidePullbackShape.fintypeHom

-- We can't just made this an `abbrev`
-- because of https://github.com/leanprover-community/lean/issues/429
/-- A category `HasFiniteWidePullbacks` if it has all limits of shape `WidePullbackShape J` for
finite `J`, i.e. if it has a wide pullback for every finite collection of morphisms with the same
codomain. -/
class HasFiniteWidePullbacks : Prop where
  /-- `C` has all wide pullbacks for any Finite `J` -/
  out (J : Type) [Finite J] : HasLimitsOfShape (WidePullbackShape J) C

/-- A category `HasFiniteWidePushouts` if it has all colimits of shape `WidePushoutShape J` for
finite `J`, i.e. if it has a wide pushout for every finite collection of morphisms with the same
domain. -/
@[to_dual]
class HasFiniteWidePushouts : Prop where
  /-- `C` has all wide pushouts for any Finite `J` -/
  out (J : Type) [Finite J] : HasColimitsOfShape (WidePushoutShape J) C

@[to_dual]
instance hasLimitsOfShape_widePullbackShape (J : Type) [Finite J] [HasFiniteWidePullbacks C] :
    HasLimitsOfShape (WidePullbackShape J) C := by
  have := @HasFiniteWidePullbacks.out C _ _ J
  infer_instance

/-- Finite wide pullbacks are finite limits, so if `C` has all finite limits,
it also has finite wide pullbacks
-/
@[to_dual
/-- Finite wide pushouts are finite colimits, so if `C` has all finite colimits,
it also has finite wide pushouts
-/]
instance (priority := 900) hasFiniteWidePullbacks_of_hasFiniteLimits [HasFiniteLimits C] :
    HasFiniteWidePullbacks C :=
  ⟨fun J _ => by cases nonempty_fintype J; exact HasFiniteLimits.out _⟩

@[deprecated (since := "2026-11-17")]
alias hasFiniteWidePushouts_of_has_finite_limits := hasFiniteWidePushouts_of_hasFiniteColimits

instance fintypeWalkingPair : Fintype WalkingPair where
  elems := {WalkingPair.left, WalkingPair.right}
  complete x := by cases x <;> simp

/-- Pullbacks are finite limits, so if `C` has all finite limits, it also has all pullbacks -/
example [HasFiniteWidePullbacks C] : HasPullbacks C := by infer_instance

/-- Pushouts are finite colimits, so if `C` has all finite colimits, it also has all pushouts -/
example [HasFiniteWidePushouts C] : HasPushouts C := by infer_instance

end CategoryTheory.Limits
