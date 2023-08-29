/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/
import Mathlib.Topology.Sheaves.PresheafOfFunctions
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

#align_import topology.sheaves.sheaf_of_functions from "leanprover-community/mathlib"@"5dc6092d09e5e489106865241986f7f2ad28d4c8"

/-!
# Sheaf conditions for presheaves of (continuous) functions.

We show that
* `Top.Presheaf.toType_isSheaf`: not-necessarily-continuous functions into a type form a sheaf
* `Top.Presheaf.toTypes_isSheaf`: in fact, these may be dependent functions into a type family

For
* `Top.sheafToTop`: continuous functions into a topological space form a sheaf
please see `Topology/Sheaves/LocalPredicate.lean`, where we set up a general framework
for constructing sub(pre)sheaves of the sheaf of dependent functions.

## Future work
Obviously there's more to do:
* sections of a fiber bundle
* various classes of smooth and structure preserving functions
* functions into spaces with algebraic structure, which the sections inherit
-/


open CategoryTheory Limits TopologicalSpace Opens

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
theorem toTypes_isSheaf (T : X → Type u) : (presheafToTypes X T).IsSheaf :=
  isSheaf_of_isSheafUniqueGluing_types.{u} _ fun ι U sf hsf => by
  -- We use the sheaf condition in terms of unique gluing
  -- U is a family of open sets, indexed by `ι` and `sf` is a compatible family of sections.
  -- In the informal comments below, I'll just write `U` to represent the union.
    -- Our first goal is to define a function "lifted" to all of `U`.
    -- We do this one point at a time. Using the axiom of choice, we can pick for each
    -- `x : ↑(iSup U)` an index `i : ι` such that `x` lies in `U i`
    choose index index_spec using fun x : ↑(iSup U) => Opens.mem_iSup.mp x.2
    -- ⊢ ∃! s, IsGluing (presheafToTypes X T) U sf s
    -- Using this data, we can glue our functions together to a single section
    let s : ∀ x : ↑(iSup U), T x := fun x => sf (index x) ⟨x.1, index_spec x⟩
    -- ⊢ ∃! s, IsGluing (presheafToTypes X T) U sf s
    refine' ⟨s, _, _⟩
    -- ⊢ (fun s => IsGluing (presheafToTypes X T) U sf s) s
    · intro i
      -- ⊢ ↑((presheafToTypes X T).map (leSupr U i).op) s = sf i
      funext x
      -- ⊢ ↑((presheafToTypes X T).map (leSupr U i).op) s x = sf i x
      -- Now we need to verify that this lifted function restricts correctly to each set `U i`.
      -- Of course, the difficulty is that at any given point `x ∈ U i`,
      -- we may have used the axiom of choice to pick a different `j` with `x ∈ U j`
      -- when defining the function.
      -- Thus we'll need to use the fact that the restrictions are compatible.
      exact congr_fun (hsf (index ⟨x, _⟩) i) ⟨x, ⟨index_spec ⟨x.1, _⟩, x.2⟩⟩
      -- 🎉 no goals
    · -- Now we just need to check that the lift we picked was the only possible one.
      -- So we suppose we had some other gluing `t` of our sections
      intro t ht
      -- ⊢ t = s
      -- and observe that we need to check that it agrees with our choice
      -- for each `x ∈ ↑(iSup U)`.
      funext x
      -- ⊢ t x = s x
      exact congr_fun (ht (index x)) ⟨x.1, index_spec x⟩
      -- 🎉 no goals
set_option linter.uppercaseLean3 false
#align Top.presheaf.to_Types_is_sheaf TopCat.Presheaf.toTypes_isSheaf

-- We verify that the non-dependent version is an immediate consequence:
/-- The presheaf of not-necessarily-continuous functions to
a target type `T` satsifies the sheaf condition.
-/
theorem toType_isSheaf (T : Type u) : (presheafToType X T).IsSheaf :=
  toTypes_isSheaf X fun _ => T
#align Top.presheaf.to_Type_is_sheaf TopCat.Presheaf.toType_isSheaf

end TopCat.Presheaf

namespace TopCat

/-- The sheaf of not-necessarily-continuous functions on `X` with values in type family
`T : X → Type u`.
-/
def sheafToTypes (T : X → Type u) : Sheaf (Type u) X :=
  ⟨presheafToTypes X T, Presheaf.toTypes_isSheaf _ _⟩
set_option linter.uppercaseLean3 false
#align Top.sheaf_to_Types TopCat.sheafToTypes

/-- The sheaf of not-necessarily-continuous functions on `X` with values in a type `T`.
-/
def sheafToType (T : Type u) : Sheaf (Type u) X :=
  ⟨presheafToType X T, Presheaf.toType_isSheaf _ _⟩
set_option linter.uppercaseLean3 false
#align Top.sheafToType TopCat.sheafToType

end TopCat
