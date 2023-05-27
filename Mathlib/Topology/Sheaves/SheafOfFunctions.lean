/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison

! This file was ported from Lean 3 source module topology.sheaves.sheaf_of_functions
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Sheaves.PresheafOfFunctions
import Mathbin.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Sheaf conditions for presheaves of (continuous) functions.

We show that
* `Top.presheaf.to_Type_is_sheaf`: not-necessarily-continuous functions into a type form a sheaf
* `Top.presheaf.to_Types_is_sheaf`: in fact, these may be dependent functions into a type family

For
* `Top.sheaf_to_Top`: continuous functions into a topological space form a sheaf
please see `topology/sheaves/local_predicate.lean`, where we set up a general framework
for constructing sub(pre)sheaves of the sheaf of dependent functions.

## Future work
Obviously there's more to do:
* sections of a fiber bundle
* various classes of smooth and structure preserving functions
* functions into spaces with algebraic structure, which the sections inherit
-/


open CategoryTheory

open CategoryTheory.Limits

open TopologicalSpace

open TopologicalSpace.Opens

universe u

noncomputable section

variable (X : TopCat.{u})

open TopCat

namespace TopCat.Presheaf

/-- We show that the presheaf of functions to a type `T`
(no continuity assumptions, just plain functions)
form a sheaf.

In fact, the proof is identical when we do this for dependent functions to a type family `T`,
so we do the more general case.
-/
theorem to_Types_isSheaf (T : X → Type u) : (presheafToTypes X T).IsSheaf :=
  isSheaf_of_isSheafUniqueGluing_types _ fun ι U sf hsf =>
    -- We use the sheaf condition in terms of unique gluing
  -- U is a family of open sets, indexed by `ι` and `sf` is a compatible family of sections.
  -- In the informal comments below, I'll just write `U` to represent the union.
  by
    -- Our first goal is to define a function "lifted" to all of `U`.
    -- We do this one point at a time. Using the axiom of choice, we can pick for each
    -- `x : supr U` an index `i : ι` such that `x` lies in `U i`
    choose index index_spec using fun x : iSup U => opens.mem_supr.mp x.2
    -- Using this data, we can glue our functions together to a single section
    let s : ∀ x : iSup U, T x := fun x => sf (index x) ⟨x.1, index_spec x⟩
    refine' ⟨s, _, _⟩
    · intro i
      ext x
      -- Now we need to verify that this lifted function restricts correctly to each set `U i`.
      -- Of course, the difficulty is that at any given point `x ∈ U i`,
      -- we may have used the axiom of choice to pick a different `j` with `x ∈ U j`
      -- when defining the function.
      -- Thus we'll need to use the fact that the restrictions are compatible.
      convert congr_fun (hsf (index ⟨x, _⟩) i) ⟨x, ⟨index_spec ⟨x.1, _⟩, x.2⟩⟩
      ext
      rfl
    · -- Now we just need to check that the lift we picked was the only possible one.
      -- So we suppose we had some other gluing `t` of our sections
      intro t ht
      -- and observe that we need to check that it agrees with our choice
      -- for each `f : s .X` and each `x ∈ supr U`.
      ext x
      convert congr_fun (ht (index x)) ⟨x.1, index_spec x⟩
      ext
      rfl
#align Top.presheaf.to_Types_is_sheaf TopCat.Presheaf.to_Types_isSheaf

-- We verify that the non-dependent version is an immediate consequence:
/-- The presheaf of not-necessarily-continuous functions to
a target type `T` satsifies the sheaf condition.
-/
theorem to_Type_isSheaf (T : Type u) : (presheafToType X T).IsSheaf :=
  to_Types_isSheaf X fun _ => T
#align Top.presheaf.to_Type_is_sheaf TopCat.Presheaf.to_Type_isSheaf

end TopCat.Presheaf

namespace TopCat

/-- The sheaf of not-necessarily-continuous functions on `X` with values in type family
`T : X → Type u`.
-/
def sheafToTypes (T : X → Type u) : Sheaf (Type u) X :=
  ⟨presheafToTypes X T, Presheaf.to_Types_isSheaf _ _⟩
#align Top.sheaf_to_Types TopCat.sheafToTypes

/-- The sheaf of not-necessarily-continuous functions on `X` with values in a type `T`.
-/
def sheafToType (T : Type u) : Sheaf (Type u) X :=
  ⟨presheafToType X T, Presheaf.to_Type_isSheaf _ _⟩
#align Top.sheaf_to_Type TopCat.sheafToType

end TopCat

