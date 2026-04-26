/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Split
public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
public import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# The splitting of a simplicial set

Let `X` be a simplicial set. The fact that any simplex `x : X _⦋n⦌` can be
written in a unique way as `X.map f.op y` for an epimorphism `f : ⦋n⦌ ⟶ ⦋m⦌`
and a nondegenerate simplex `y : X _⦋m⦌` is translated in this file
as the data of a splitting of `X`.

-/

@[expose] public section

universe u

open CategoryTheory TypeCat Limits Simplicial

namespace SSet

variable (X : SSet.{u})

/-- The canonical splitting of a simplicial set that is given
by the nondegenerate simplices. -/
@[simps]
noncomputable def splitting : X.Splitting where
  N n := X.nonDegenerate n
  ι n := ↾Subtype.val
  isColimit' := fun ⟨⟨n⟩⟩ ↦ Nonempty.some (by
    rw [← Limits.Cofan.isColimit_cofanTypes_iff]
    refine CofanTypes.isColimit_mk _ (fun x ↦ ?_) (fun ⟨⟨⟨m⟩⟩, f, _⟩ x y h ↦ ?_)
      (fun ⟨⟨⟨m⟩⟩, f, _⟩ ⟨⟨⟨p⟩⟩, g, _⟩ x y h ↦ ?_)
    · obtain ⟨m, f, _, y, rfl⟩ := X.exists_nonDegenerate x
      exact ⟨.mk f, y, rfl⟩
    · exact unique_nonDegenerate_simplex _ _ _ _ rfl _ _ h
    · obtain rfl : m = p := unique_nonDegenerate_dim _ _ _ _ rfl _ _ h
      obtain rfl : x = y := unique_nonDegenerate_simplex _ _ _ _ rfl _ _ h
      obtain rfl : f = g := unique_nonDegenerate_map _ _ _ _ rfl _ _ h
      dsimp)

end SSet
