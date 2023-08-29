/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.PUnit
import Mathlib.CategoryTheory.StructuredArrow

#align_import category_theory.adjunction.comma from "leanprover-community/mathlib"@"8a318021995877a44630c898d0b2bc376fceef3b"

/-!
# Properties of comma categories relating to adjunctions

This file shows that for a functor `G : D ⥤ C` the data of an initial object in each
`StructuredArrow` category on `G` is equivalent to a left adjoint to `G`, as well as the dual.

Specifically, `adjunctionOfStructuredArrowInitials` gives the left adjoint assuming the
appropriate initial objects exist, and `mkInitialOfLeftAdjoint` constructs the initial objects
provided a left adjoint.

The duals are also shown.
-/


universe v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory

open Limits

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (G : D ⥤ C)

section OfInitials

variable [∀ A, HasInitial (StructuredArrow A G)]

/-- Implementation: If each structured arrow category on `G` has an initial object, an equivalence
which is helpful for constructing a left adjoint to `G`.
-/
@[simps]
def leftAdjointOfStructuredArrowInitialsAux (A : C) (B : D) :
    ((⊥_ StructuredArrow A G).right ⟶ B) ≃ (A ⟶ G.obj B)
    where
  toFun g := (⊥_ StructuredArrow A G).hom ≫ G.map g
  invFun f := CommaMorphism.right (initial.to (StructuredArrow.mk f))
  left_inv g := by
    let B' : StructuredArrow A G := StructuredArrow.mk ((⊥_ StructuredArrow A G).hom ≫ G.map g)
    -- ⊢ (fun f => (initial.to (StructuredArrow.mk f)).right) ((fun g => (⊥_ Structur …
    let g' : ⊥_ StructuredArrow A G ⟶ B' := StructuredArrow.homMk g rfl
    -- ⊢ (fun f => (initial.to (StructuredArrow.mk f)).right) ((fun g => (⊥_ Structur …
    have : initial.to _ = g' := by aesop_cat
    -- ⊢ (fun f => (initial.to (StructuredArrow.mk f)).right) ((fun g => (⊥_ Structur …
    change CommaMorphism.right (initial.to B') = _
    -- ⊢ (initial.to B').right = g
    rw [this]
    -- ⊢ g'.right = g
    rfl
    -- 🎉 no goals
  right_inv f := by
    let B' : StructuredArrow A G := StructuredArrow.mk f
    -- ⊢ (fun g => (⊥_ StructuredArrow A G).hom ≫ G.map g) ((fun f => (initial.to (St …
    apply (CommaMorphism.w (initial.to B')).symm.trans (Category.id_comp _)
    -- 🎉 no goals
#align category_theory.left_adjoint_of_structured_arrow_initials_aux CategoryTheory.leftAdjointOfStructuredArrowInitialsAux

/--
If each structured arrow category on `G` has an initial object, construct a left adjoint to `G`. It
is shown that it is a left adjoint in `adjunctionOfStructuredArrowInitials`.
-/
def leftAdjointOfStructuredArrowInitials : C ⥤ D :=
  Adjunction.leftAdjointOfEquiv (leftAdjointOfStructuredArrowInitialsAux G) fun _ _ => by simp
                                                                                          -- 🎉 no goals
#align category_theory.left_adjoint_of_structured_arrow_initials CategoryTheory.leftAdjointOfStructuredArrowInitials

/--
If each structured arrow category on `G` has an initial object, we have a constructed left adjoint
to `G`.
-/
def adjunctionOfStructuredArrowInitials : leftAdjointOfStructuredArrowInitials G ⊣ G :=
  Adjunction.adjunctionOfEquivLeft _ _
#align category_theory.adjunction_of_structured_arrow_initials CategoryTheory.adjunctionOfStructuredArrowInitials

/-- If each structured arrow category on `G` has an initial object, `G` is a right adjoint. -/
def isRightAdjointOfStructuredArrowInitials : IsRightAdjoint G
    where
  left := _
  adj := adjunctionOfStructuredArrowInitials G
#align category_theory.is_right_adjoint_of_structured_arrow_initials CategoryTheory.isRightAdjointOfStructuredArrowInitials

end OfInitials

section OfTerminals

variable [∀ A, HasTerminal (CostructuredArrow G A)]

/-- Implementation: If each costructured arrow category on `G` has a terminal object, an equivalence
which is helpful for constructing a right adjoint to `G`.
-/
@[simps]
def rightAdjointOfCostructuredArrowTerminalsAux (B : D) (A : C) :
    (G.obj B ⟶ A) ≃ (B ⟶ (⊤_ CostructuredArrow G A).left)
    where
  toFun g := CommaMorphism.left (terminal.from (CostructuredArrow.mk g))
  invFun g := G.map g ≫ (⊤_ CostructuredArrow G A).hom
  left_inv := by aesop_cat
                 -- 🎉 no goals
  right_inv g := by
    let B' : CostructuredArrow G A :=
      CostructuredArrow.mk (G.map g ≫ (⊤_ CostructuredArrow G A).hom)
    let g' : B' ⟶ ⊤_ CostructuredArrow G A := CostructuredArrow.homMk g rfl
    -- ⊢ (fun g => (terminal.from (CostructuredArrow.mk g)).left) ((fun g => G.map g  …
    have : terminal.from _ = g' := by aesop_cat
    -- ⊢ (fun g => (terminal.from (CostructuredArrow.mk g)).left) ((fun g => G.map g  …
    change CommaMorphism.left (terminal.from B') = _
    -- ⊢ (terminal.from B').left = g
    rw [this]
    -- ⊢ g'.left = g
    rfl
    -- 🎉 no goals
#align category_theory.right_adjoint_of_costructured_arrow_terminals_aux CategoryTheory.rightAdjointOfCostructuredArrowTerminalsAux

/--
If each costructured arrow category on `G` has a terminal object, construct a right adjoint to `G`.
It is shown that it is a right adjoint in `adjunctionOfStructuredArrowInitials`.
-/
def rightAdjointOfCostructuredArrowTerminals : C ⥤ D :=
  Adjunction.rightAdjointOfEquiv (rightAdjointOfCostructuredArrowTerminalsAux G)
      fun B₁ B₂ A f g => by
    rw [← Equiv.eq_symm_apply]
    -- ⊢ G.map f ≫ g = ↑(rightAdjointOfCostructuredArrowTerminalsAux G B₁ A).symm (f  …
    simp
    -- 🎉 no goals
#align category_theory.right_adjoint_of_costructured_arrow_terminals CategoryTheory.rightAdjointOfCostructuredArrowTerminals

/-- If each costructured arrow category on `G` has a terminal object, we have a constructed right
adjoint to `G`.
-/
def adjunctionOfCostructuredArrowTerminals : G ⊣ rightAdjointOfCostructuredArrowTerminals G :=
  Adjunction.adjunctionOfEquivRight _ _
#align category_theory.adjunction_of_costructured_arrow_terminals CategoryTheory.adjunctionOfCostructuredArrowTerminals

/-- If each costructured arrow category on `G` has a terminal object, `G` is a left adjoint. -/
def isLeftAdjointOfCostructuredArrowTerminals : IsLeftAdjoint G
    where
  right := rightAdjointOfCostructuredArrowTerminals G
  adj := Adjunction.adjunctionOfEquivRight _ _
#align category_theory.is_left_adjoint_of_costructured_arrow_terminals CategoryTheory.isLeftAdjointOfCostructuredArrowTerminals

end OfTerminals

section

variable {F : C ⥤ D}

/-- Given a left adjoint to `G`, we can construct an initial object in each structured arrow
category on `G`. -/
def mkInitialOfLeftAdjoint (h : F ⊣ G) (A : C) :
    IsInitial (StructuredArrow.mk (h.unit.app A) : StructuredArrow A G)
    where
  desc B := StructuredArrow.homMk ((h.homEquiv _ _).symm B.pt.hom)
  uniq s m _ := by
    apply StructuredArrow.ext
    -- ⊢ m.right = ((fun B => StructuredArrow.homMk (↑(Adjunction.homEquiv h ((Functo …
    dsimp
    -- ⊢ m.right = ↑(Adjunction.homEquiv h A s.pt.right).symm s.pt.hom
    rw [Equiv.eq_symm_apply, Adjunction.homEquiv_unit]
    -- ⊢ NatTrans.app h.unit A ≫ G.map m.right = s.pt.hom
    apply StructuredArrow.w m
    -- 🎉 no goals
#align category_theory.mk_initial_of_left_adjoint CategoryTheory.mkInitialOfLeftAdjoint

/-- Given a right adjoint to `F`, we can construct a terminal object in each costructured arrow
category on `F`. -/
def mkTerminalOfRightAdjoint (h : F ⊣ G) (A : D) :
    IsTerminal (CostructuredArrow.mk (h.counit.app A) : CostructuredArrow F A)
    where
  lift B := CostructuredArrow.homMk (h.homEquiv _ _ B.pt.hom)
  uniq s m _ := by
    apply CostructuredArrow.ext
    -- ⊢ m.left = ((fun B => CostructuredArrow.homMk (↑(Adjunction.homEquiv h B.pt.le …
    dsimp
    -- ⊢ m.left = ↑(Adjunction.homEquiv h s.pt.left A) s.pt.hom
    rw [h.eq_homEquiv_apply, Adjunction.homEquiv_counit]
    -- ⊢ F.map m.left ≫ NatTrans.app h.counit A = s.pt.hom
    exact CostructuredArrow.w m
    -- 🎉 no goals
#align category_theory.mk_terminal_of_right_adjoint CategoryTheory.mkTerminalOfRightAdjoint

end

theorem nonempty_isRightAdjoint_iff_hasInitial_structuredArrow {G : D ⥤ C} :
    Nonempty (IsRightAdjoint G) ↔ ∀ A, HasInitial (StructuredArrow A G) :=
  ⟨fun ⟨h⟩ A => (mkInitialOfLeftAdjoint _ h.adj A).hasInitial, fun _ =>
    ⟨isRightAdjointOfStructuredArrowInitials _⟩⟩
#align category_theory.nonempty_is_right_adjoint_iff_has_initial_structured_arrow CategoryTheory.nonempty_isRightAdjoint_iff_hasInitial_structuredArrow

theorem nonempty_isLeftAdjoint_iff_hasTerminal_costructuredArrow {F : C ⥤ D} :
    Nonempty (IsLeftAdjoint F) ↔ ∀ A, HasTerminal (CostructuredArrow F A) :=
  ⟨fun ⟨h⟩ A => (mkTerminalOfRightAdjoint _ h.adj A).hasTerminal, fun _ =>
    ⟨isLeftAdjointOfCostructuredArrowTerminals _⟩⟩
#align category_theory.nonempty_is_left_adjoint_iff_has_terminal_costructured_arrow CategoryTheory.nonempty_isLeftAdjoint_iff_hasTerminal_costructuredArrow

end CategoryTheory
