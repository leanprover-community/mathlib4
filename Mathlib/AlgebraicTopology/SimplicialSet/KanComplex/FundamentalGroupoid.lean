/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex.MulStruct
public import Mathlib.AlgebraicTopology.Quasicategory.TwoTruncatedQuasicategory


/-!
# The fundamental groupoid of a Kan complex


-/

@[expose] public section

universe u

open HomotopicalAlgebra CategoryTheory Simplicial

namespace SSet

namespace KanComplex

/-- The fundamental groupoid of a Kan complex. -/
@[nolint unusedArguments]
def FundamentalGroupoid (X : SSet.{u}) [KanComplex X] :=
  Truncated.HomotopyCategory₂ ((SSet.truncation 2).obj X)

variable {X : SSet.{u}} [KanComplex X]

noncomputable instance : Category (FundamentalGroupoid X) :=
  inferInstanceAs (Category (Truncated.HomotopyCategory₂ ((SSet.truncation 2).obj X)))

namespace FundamentalGroupoid

/-- The objects of the fundamental groupoid of a Kan complex identify to `0`-simplices. -/
@[implicit_reducible, simps]
def objEquiv : FundamentalGroupoid X ≃ X _⦋0⦌ where
  toFun x := x.pt
  invFun x := { pt := x }

/-- Constructor for objects of the fundamental groupoid of a Kan complex. -/
abbrev objMk (x : X _⦋0⦌) : FundamentalGroupoid X := objEquiv.symm x

/-- Constructor for morphisms of the fundamental groupoid of a Kan complex. -/
@[no_expose]
def homMk {x y : X _⦋0⦌} (e : Edge x y) : objMk x ⟶ objMk y :=
  Truncated.HomotopyCategory₂.homMk e

@[simp]
lemma homMk_id (x : X _⦋0⦌) : homMk (.id x) = 𝟙 _ := by
  rfl

lemma homMk_surjective {x y : X _⦋0⦌} :
    Function.Surjective (fun (e : Edge x y) ↦ homMk e) :=
  Truncated.HomotopyCategory₂.homMk_surjective

@[reassoc]
lemma homMk_fac_of_compStruct {x y z : X _⦋0⦌} {e₁ : Edge x y} {e₂ : Edge y z} {e₃ : Edge x z}
    (h : Edge.CompStruct e₁ e₂ e₃) :
    homMk e₁ ≫ homMk e₂ = homMk e₃ :=
  Truncated.Edge.CompStruct.nonempty_iff.1 ⟨h⟩

instance : IsGroupoid (FundamentalGroupoid X) := sorry

end FundamentalGroupoid

end KanComplex

namespace Edge

variable {X : SSet.{u}} [KanComplex X] {x y z : X _⦋0⦌}

open KanComplex.FundamentalGroupoid

lemma CompStruct.nonempty_iff {e₁ : Edge x y} {e₂ : Edge y z} {e₃ : Edge x z} :
    Nonempty (CompStruct e₁ e₂ e₃) ↔ homMk e₁ ≫ homMk e₂ = homMk e₃ :=
  Truncated.Edge.CompStruct.nonempty_iff

/-- A choice of inverse of an edge in a Kan complex. -/
@[no_expose]
protected noncomputable def inv (e : Edge x y) : Edge y x :=
  (homMk_surjective (CategoryTheory.inv (homMk e))).choose

@[simp]
lemma homMk_inv (e : Edge x y) : homMk e.inv = inv (homMk e) :=
  (homMk_surjective (CategoryTheory.inv (homMk e))).choose_spec

/-- `Edge.inv` is a right inverse. -/
@[no_expose]
noncomputable def CompStruct.homInvId (e : Edge x y) : CompStruct e e.inv (id x) :=
  Nonempty.some (by simp [nonempty_iff])

/-- `Edge.inv` is a left inverse. -/
@[no_expose]
noncomputable def CompStruct.invHomId (e : Edge x y) : CompStruct e.inv e (id y) :=
  Nonempty.some (by simp [nonempty_iff])

end Edge

end SSet
