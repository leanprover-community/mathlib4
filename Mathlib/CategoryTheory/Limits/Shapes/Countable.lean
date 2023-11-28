/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Countable
import Mathlib.Data.Countable.Defs

open CategoryTheory Opposite

variable (C : Type*) [Category C] (J : Type*) [Countable J]

namespace CategoryTheory.Limits

/--
A category has all countable limits if every functor `J ⥤ C` with a `CountableCategory J`
instance and `J : Type` has a limit.
-/
class HasCountableLimits : Prop where
  /-- `C` has all limits over any type `J` whose objects and morphisms lie in the same universe
  and which has countably many objects and morphisms-/
  out (J : Type) [𝒥 : SmallCategory J] [@CountableCategory J 𝒥] : @HasLimitsOfShape J 𝒥 C _

instance (priority := 100) hasFiniteLimits_of_hasCountableLimits [HasCountableLimits C] :
    HasFiniteLimits C where
  out J := HasCountableLimits.out J

instance (priority := 100) hasCountableLimits_of_hasLimits [HasLimits C] :
    HasCountableLimits C where
  out := inferInstance

/--
A category has all countable colimits if every functor `J ⥤ C` with a `CountableCategory J`
instance and `J : Type` has a colimit.
-/
class HasCountableColimits : Prop where
  /-- `C` has all limits over any type `J` whose objects and morphisms lie in the same universe
  and which has countably many objects and morphisms-/
  out (J : Type) [𝒥 : SmallCategory J] [@CountableCategory J 𝒥] : @HasColimitsOfShape J 𝒥 C _

instance (priority := 100) hasFiniteColimits_of_hasCountableColimits [HasCountableColimits C] :
    HasFiniteColimits C where
  out J := HasCountableColimits.out J

instance (priority := 100) hasCountableColimits_of_hasColimits [HasColimits C] :
    HasCountableColimits C where
  out := inferInstance

section Preorder

attribute [local instance] IsCofiltered.nonempty

variable {C} [Preorder J] [IsCofiltered J]

/-- The object part of the initial functor `ℕᵒᵖ ⥤ J` -/
noncomputable def sequentialFunctor_obj : ℕ → J := fun
  | .zero => (exists_surjective_nat _).choose 0
  | .succ n => (IsCofilteredOrEmpty.cone_objs ((exists_surjective_nat _).choose n)
      (sequentialFunctor_obj n)).choose

theorem sequentialFunctor_map  : Antitone (sequentialFunctor_obj J) :=
  antitone_nat_of_succ_le fun n ↦
    leOfHom (IsCofilteredOrEmpty.cone_objs ((exists_surjective_nat _).choose n)
      (sequentialFunctor_obj J n)).choose_spec.choose_spec.choose

/--
The initial functor `ℕᵒᵖ ⥤ J`, which allows us to turn cofiltered limits over countable preorders
into sequential limits.
-/
noncomputable def sequentialFunctor : ℕᵒᵖ ⥤ J where
  obj n := sequentialFunctor_obj J (unop n)
  map h := homOfLE (sequentialFunctor_map J (leOfHom h.unop))

theorem sequentialFunctor_initial_aux (j : J) : ∃ (n : ℕ), sequentialFunctor_obj J n ≤ j := by
  obtain ⟨m, h⟩ := (exists_surjective_nat _).choose_spec j
  refine ⟨m + 1, ?_⟩
  simpa [h] using leOfHom (IsCofilteredOrEmpty.cone_objs ((exists_surjective_nat _).choose m)
    (sequentialFunctor_obj J m)).choose_spec.choose

instance sequentialFunctor_initial : (sequentialFunctor J).Initial  where
  out d := by
    obtain ⟨n, (g : (sequentialFunctor J).obj ⟨n⟩ ≤ d)⟩ := sequentialFunctor_initial_aux J d
    have : Nonempty (CostructuredArrow (sequentialFunctor J) d) :=
      ⟨CostructuredArrow.mk (homOfLE g)⟩
    apply isConnected_of_zigzag
    refine fun i j ↦ ⟨[j], ?_⟩
    simp only [List.chain_cons, Zag, List.Chain.nil, and_true, ne_eq, not_false_eq_true,
      List.getLast_cons, not_true_eq_false, List.getLast_singleton']
    wlog h : (unop i.left) ≤ (unop j.left)
    · exact or_comm.1 (this (C := C) J d n g inferInstance j i (le_of_lt (not_le.mp h)))
    · right
      exact ⟨CostructuredArrow.homMk (homOfLE h).op rfl⟩

/--
This is proved in https://stacks.math.columbia.edu/tag/0032
-/
proof_wanted preorder_of_cofiltered (J : Type*) [Category J] [IsCofiltered J] :
    ∃ (I : Type*) (_ : Preorder I) (_ : IsCofiltered I) (F : I ⥤ J), F.Initial

/--
The proof of `preorder_of_cofiltered` should give a countable `I` in the case that `J` is a
countable category.
-/
proof_wanted preorder_of_cofiltered_countable
    (J : Type*) [SmallCategory J] [IsCofiltered J] [CountableCategory J] :
    ∃ (I : Type) (_ : Preorder I) (_ : Countable I) (_ : IsCofiltered I) (F : I ⥤ J), F.Initial

/--
Put together `sequentialFunctor_initial` and `preorder_of_cofiltered_countable`.
-/
proof_wanted hasCofilteredCountableLimits_of_hasSequentialLimits [HasLimitsOfShape ℕᵒᵖ C] :
    ∀ (J : Type) [SmallCategory J] [IsCofiltered J] [CountableCategory J], HasLimitsOfShape J C

/--
This is the countable version of `CategoryTheory.Limits.has_limits_of_finite_and_cofiltered`, given
all of the above.
-/
proof_wanted hasCountableLimits_of_hasFiniteLimits_and_hasSequentialLimits [HasFiniteLimits C]
  [HasLimitsOfShape ℕᵒᵖ C] : HasCountableLimits C

/--
For this we need to dualize this whole section.
-/
proof_wanted hasCountableColimits_of_hasFiniteColimits_and_hasSequentialColimits
  [HasFiniteColimits C] [HasLimitsOfShape ℕ C] : HasCountableColimits C

end Preorder

end CategoryTheory.Limits
