/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Countable
import Mathlib.Data.Countable.Defs
/-!
# Countable limits and colimits

A typeclass for categories with all countable (co)limits.

We also prove that all cofiltered limits over countable preorders are isomorphic to sequential
limits, see `sequentialFunctor_initial`.

## Projects

* There is a series of `proof_wanted` at the bottom of this file, implying that all cofiltered
  limits over countable categories are isomorphic to sequential limits.

* Prove the dual result for filtered colimits.

-/

open CategoryTheory Opposite CountableCategory

variable (C : Type*) [Category C] (J : Type*) [Countable J]

namespace CategoryTheory.Limits

/--
A category has all countable limits if every functor `J ⥤ C` with a `CountableCategory J`
instance and `J : Type` has a limit.
-/
class HasCountableLimits : Prop where
  /-- `C` has all limits over any type `J` whose objects and morphisms lie in the same universe
  and which has countably many objects and morphisms -/
  out (J : Type) [SmallCategory J] [CountableCategory J] : HasLimitsOfShape J C

instance (priority := 100) hasFiniteLimits_of_hasCountableLimits [HasCountableLimits C] :
    HasFiniteLimits C where
  out J := HasCountableLimits.out J

instance (priority := 100) hasCountableLimits_of_hasLimits [HasLimits C] :
    HasCountableLimits C where
  out := inferInstance

universe v in
instance [HasCountableLimits C] [Category.{v} J] [CountableCategory J] : HasLimitsOfShape J C :=
  have : HasLimitsOfShape (HomAsType J) C := HasCountableLimits.out (HomAsType J)
  hasLimitsOfShape_of_equivalence (homAsTypeEquiv J)

/-- A category has countable products if it has all products indexed by countable types. -/
class HasCountableProducts where
  out (J : Type) [Countable J] : HasProductsOfShape J C

instance [HasCountableProducts C] (J : Type*) [Countable J] : HasProductsOfShape J C :=
  have : Countable (Shrink.{0} J) := Countable.of_equiv _ (equivShrink.{0} J)
  have : HasLimitsOfShape (Discrete (Shrink.{0} J)) C := HasCountableProducts.out _
  hasLimitsOfShape_of_equivalence (Discrete.equivalence (equivShrink.{0} J)).symm

instance (priority := 100) hasCountableProducts_of_hasProducts [HasProducts C] :
    HasCountableProducts C where
  out _ :=
    have : HasProducts.{0} C := has_smallest_products_of_hasProducts
    inferInstance

instance (priority := 100) hasCountableProducts_of_hasCountableLimits [HasCountableLimits C] :
    HasCountableProducts C where
  out _ := inferInstance

instance (priority := 100) hasFiniteProducts_of_hasCountableProducts [HasCountableProducts C] :
    HasFiniteProducts C where
  out _ := inferInstance

/--
A category has all countable colimits if every functor `J ⥤ C` with a `CountableCategory J`
instance and `J : Type` has a colimit.
-/
class HasCountableColimits : Prop where
  /-- `C` has all limits over any type `J` whose objects and morphisms lie in the same universe
  and which has countably many objects and morphisms -/
  out (J : Type) [SmallCategory J] [CountableCategory J] : HasColimitsOfShape J C

instance (priority := 100) hasFiniteColimits_of_hasCountableColimits [HasCountableColimits C] :
    HasFiniteColimits C where
  out J := HasCountableColimits.out J

instance (priority := 100) hasCountableColimits_of_hasColimits [HasColimits C] :
    HasCountableColimits C where
  out := inferInstance

-- See note [instance argument order]
universe v in
instance [HasCountableColimits C] (J : Type*) [Category.{v} J] [CountableCategory J] :
    HasColimitsOfShape J C :=
  have : HasColimitsOfShape (HomAsType J) C := HasCountableColimits.out (HomAsType J)
  hasColimitsOfShape_of_equivalence (homAsTypeEquiv J)

/-- A category has countable coproducts if it has all coproducts indexed by countable types. -/
class HasCountableCoproducts where
  out (J : Type) [Countable J] : HasCoproductsOfShape J C

instance (priority := 100) hasCountableCoproducts_of_hasCoproducts [HasCoproducts C] :
    HasCountableCoproducts C where
  out _ :=
    have : HasCoproducts.{0} C := has_smallest_coproducts_of_hasCoproducts
    inferInstance

-- See note [instance argument order]
instance [HasCountableCoproducts C] (J : Type*) [Countable J] : HasCoproductsOfShape J C :=
  have : Countable (Shrink.{0} J) := Countable.of_equiv _ (equivShrink.{0} J)
  have : HasColimitsOfShape (Discrete (Shrink.{0} J)) C := HasCountableCoproducts.out _
  hasColimitsOfShape_of_equivalence (Discrete.equivalence (equivShrink.{0} J)).symm

instance (priority := 100) hasCountableCoproducts_of_hasCountableColimits [HasCountableColimits C] :
    HasCountableCoproducts C where
  out _ := inferInstance

instance (priority := 100) hasFiniteCoproducts_of_hasCountableCoproducts
    [HasCountableCoproducts C] : HasFiniteCoproducts C where
  out _ := inferInstance

section Preorder

namespace IsFiltered

attribute [local instance] IsFiltered.nonempty

variable {C} [Preorder J] [IsFiltered J]

/-- The object part of the initial functor `ℕᵒᵖ ⥤ J` -/
noncomputable def sequentialFunctor_obj : ℕ → J := fun
  | .zero => (exists_surjective_nat _).choose 0
  | .succ n => (IsFilteredOrEmpty.cocone_objs ((exists_surjective_nat _).choose n)
      (sequentialFunctor_obj n)).choose

theorem sequentialFunctor_map : Monotone (sequentialFunctor_obj J) :=
  monotone_nat_of_le_succ fun n ↦
    leOfHom (IsFilteredOrEmpty.cocone_objs ((exists_surjective_nat _).choose n)
      (sequentialFunctor_obj J n)).choose_spec.choose_spec.choose

/--
The initial functor `ℕᵒᵖ ⥤ J`, which allows us to turn cofiltered limits over countable preorders
into sequential limits.
-/
noncomputable def sequentialFunctor : ℕ ⥤ J where
  obj n := sequentialFunctor_obj J n
  map h := homOfLE (sequentialFunctor_map J (leOfHom h))

theorem sequentialFunctor_final_aux (j : J) : ∃ (n : ℕ), j ≤ sequentialFunctor_obj J n := by
  obtain ⟨m, h⟩ := (exists_surjective_nat _).choose_spec j
  refine ⟨m + 1, ?_⟩
  simpa only [h] using leOfHom (IsFilteredOrEmpty.cocone_objs ((exists_surjective_nat _).choose m)
    (sequentialFunctor_obj J m)).choose_spec.choose

instance sequentialFunctor_final : (sequentialFunctor J).Final where
  out d := by
    obtain ⟨n, (g : d ≤ (sequentialFunctor J).obj n)⟩ := sequentialFunctor_final_aux J d
    have : Nonempty (StructuredArrow d (sequentialFunctor J)) :=
      ⟨StructuredArrow.mk (homOfLE g)⟩
    apply isConnected_of_zigzag
    refine fun i j ↦ ⟨[j], ?_⟩
    simp only [List.isChain_cons_cons, Zag, List.isChain_singleton, and_true, ne_eq,
      not_false_eq_true, List.getLast_cons, List.getLast_singleton', reduceCtorEq]
    clear! C
    wlog h : j.right ≤ i.right
    · exact or_comm.1 (this J d n g inferInstance j i (le_of_lt (not_le.mp h)))
    · right
      exact ⟨StructuredArrow.homMk (homOfLE h) rfl⟩

end IsFiltered

namespace IsCofiltered

attribute [local instance] IsCofiltered.nonempty

variable {C} [Preorder J] [IsCofiltered J]

/-- The object part of the initial functor `ℕᵒᵖ ⥤ J` -/
noncomputable def sequentialFunctor_obj : ℕ → J := fun
  | .zero => (exists_surjective_nat _).choose 0
  | .succ n => (IsCofilteredOrEmpty.cone_objs ((exists_surjective_nat _).choose n)
      (sequentialFunctor_obj n)).choose

theorem sequentialFunctor_map : Antitone (sequentialFunctor_obj J) :=
  antitone_nat_of_succ_le fun n ↦
    leOfHom (IsCofilteredOrEmpty.cone_objs ((exists_surjective_nat _).choose n)
      (sequentialFunctor_obj J n)).choose_spec.choose_spec.choose

/--
The initial functor `ℕᵒᵖ ⥤ J`, which allows us to turn cofiltered limits over countable preorders
into sequential limits.

TODO: redefine this as `(IsFiltered.sequentialFunctor Jᵒᵖ).leftOp`. This would need API for initial/
final functors of the form `leftOp`/`rightOp`.
-/
noncomputable def sequentialFunctor : ℕᵒᵖ ⥤ J where
  obj n := sequentialFunctor_obj J (unop n)
  map h := homOfLE (sequentialFunctor_map J (leOfHom h.unop))

theorem sequentialFunctor_initial_aux (j : J) : ∃ (n : ℕ), sequentialFunctor_obj J n ≤ j := by
  obtain ⟨m, h⟩ := (exists_surjective_nat _).choose_spec j
  refine ⟨m + 1, ?_⟩
  simpa only [h] using leOfHom (IsCofilteredOrEmpty.cone_objs ((exists_surjective_nat _).choose m)
    (sequentialFunctor_obj J m)).choose_spec.choose

instance sequentialFunctor_initial : (sequentialFunctor J).Initial where
  out d := by
    obtain ⟨n, (g : (sequentialFunctor J).obj ⟨n⟩ ≤ d)⟩ := sequentialFunctor_initial_aux J d
    have : Nonempty (CostructuredArrow (sequentialFunctor J) d) :=
      ⟨CostructuredArrow.mk (homOfLE g)⟩
    apply isConnected_of_zigzag
    refine fun i j ↦ ⟨[j], ?_⟩
    simp only [List.isChain_cons_cons, Zag, List.isChain_singleton, and_true, ne_eq,
      not_false_eq_true, List.getLast_cons, List.getLast_singleton', reduceCtorEq]
    clear! C
    wlog h : (unop i.left) ≤ (unop j.left)
    · exact or_comm.1 (this J d n g inferInstance j i (le_of_lt (not_le.mp h)))
    · right
      exact ⟨CostructuredArrow.homMk (homOfLE h).op rfl⟩

@[stacks 0032]
proof_wanted preorder_of_cofiltered (J : Type*) [Category J] [IsCofiltered J] :
    ∃ (I : Type*) (_ : Preorder I) (_ : IsCofiltered I) (F : I ⥤ J), F.Initial

/--
The proof of `preorder_of_cofiltered` should give a countable `I` in the case that `J` is a
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

end IsCofiltered

end Preorder

end CategoryTheory.Limits
