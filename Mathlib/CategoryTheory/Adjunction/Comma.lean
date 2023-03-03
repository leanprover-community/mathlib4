/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.adjunction.comma
! leanprover-community/mathlib commit 8a318021995877a44630c898d0b2bc376fceef3b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Adjunction.Basic
import Mathbin.CategoryTheory.Punit
import Mathbin.CategoryTheory.StructuredArrow

/-!
# Properties of comma categories relating to adjunctions

This file shows that for a functor `G : D ⥤ C` the data of an initial object in each
`structured_arrow` category on `G` is equivalent to a left adjoint to `G`, as well as the dual.

Specifically, `adjunction_of_structured_arrow_initials` gives the left adjoint assuming the
appropriate initial objects exist, and `mk_initial_of_left_adjoint` constructs the initial objects
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
  toFun g := (⊥_ StructuredArrow A G).Hom ≫ G.map g
  invFun f := CommaMorphism.right (initial.to (StructuredArrow.mk f))
  left_inv g :=
    by
    let B' : structured_arrow A G := structured_arrow.mk ((⊥_ structured_arrow A G).Hom ≫ G.map g)
    let g' : ⊥_ structured_arrow A G ⟶ B' := structured_arrow.hom_mk g rfl
    have : initial.to _ = g' := by
      apply colimit.hom_ext
      rintro ⟨⟨⟩⟩
    change comma_morphism.right (initial.to B') = _
    rw [this]
    rfl
  right_inv f := by
    let B' : structured_arrow A G := structured_arrow.mk f
    apply (comma_morphism.w (initial.to B')).symm.trans (category.id_comp _)
#align category_theory.left_adjoint_of_structured_arrow_initials_aux CategoryTheory.leftAdjointOfStructuredArrowInitialsAux

/--
If each structured arrow category on `G` has an initial object, construct a left adjoint to `G`. It
is shown that it is a left adjoint in `adjunction_of_structured_arrow_initials`.
-/
def leftAdjointOfStructuredArrowInitials : C ⥤ D :=
  Adjunction.leftAdjointOfEquiv (leftAdjointOfStructuredArrowInitialsAux G) fun _ _ => by simp
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
  invFun g := G.map g ≫ (⊤_ CostructuredArrow G A).Hom
  left_inv := by tidy
  right_inv g :=
    by
    let B' : costructured_arrow G A :=
      costructured_arrow.mk (G.map g ≫ (⊤_ costructured_arrow G A).Hom)
    let g' : B' ⟶ ⊤_ costructured_arrow G A := costructured_arrow.hom_mk g rfl
    have : terminal.from _ = g' := by
      apply limit.hom_ext
      rintro ⟨⟨⟩⟩
    change comma_morphism.left (terminal.from B') = _
    rw [this]
    rfl
#align category_theory.right_adjoint_of_costructured_arrow_terminals_aux CategoryTheory.rightAdjointOfCostructuredArrowTerminalsAux

/--
If each costructured arrow category on `G` has a terminal object, construct a right adjoint to `G`.
It is shown that it is a right adjoint in `adjunction_of_structured_arrow_initials`.
-/
def rightAdjointOfCostructuredArrowTerminals : C ⥤ D :=
  Adjunction.rightAdjointOfEquiv (rightAdjointOfCostructuredArrowTerminalsAux G) fun B₁ B₂ A f g =>
    by
    rw [← Equiv.eq_symm_apply]
    simp
#align category_theory.right_adjoint_of_costructured_arrow_terminals CategoryTheory.rightAdjointOfCostructuredArrowTerminals

/-- If each costructured arrow category on `G` has a terminal object, we have a constructed right
adjoint to `G`.
-/
def adjunctionOfCostructuredArrowTerminals : G ⊣ rightAdjointOfCostructuredArrowTerminals G :=
  Adjunction.adjunctionOfEquivRight _ _
#align category_theory.adjunction_of_costructured_arrow_terminals CategoryTheory.adjunctionOfCostructuredArrowTerminals

/-- If each costructured arrow category on `G` has an terminal object, `G` is a left adjoint. -/
def isLeftAdjointOfCostructuredArrowTerminals : IsLeftAdjoint G
    where
  right := rightAdjointOfCostructuredArrowTerminals G
  adj := Adjunction.adjunctionOfEquivRight _ _
#align category_theory.is_left_adjoint_of_costructured_arrow_terminals CategoryTheory.isLeftAdjointOfCostructuredArrowTerminals

end OfTerminals

section

variable {F : C ⥤ D}

attribute [local tidy] tactic.discrete_cases

/-- Given a left adjoint to `G`, we can construct an initial object in each structured arrow
category on `G`. -/
def mkInitialOfLeftAdjoint (h : F ⊣ G) (A : C) :
    IsInitial (StructuredArrow.mk (h.Unit.app A) : StructuredArrow A G)
    where
  desc B := StructuredArrow.homMk ((h.homEquiv _ _).symm B.pt.Hom) (by tidy)
  uniq s m w := by
    ext
    dsimp
    rw [Equiv.eq_symm_apply, adjunction.hom_equiv_unit]
    apply structured_arrow.w m
#align category_theory.mk_initial_of_left_adjoint CategoryTheory.mkInitialOfLeftAdjoint

/-- Given a right adjoint to `F`, we can construct a terminal object in each costructured arrow
category on `F`. -/
def mkTerminalOfRightAdjoint (h : F ⊣ G) (A : D) :
    IsTerminal (CostructuredArrow.mk (h.counit.app A) : CostructuredArrow F A)
    where
  lift B := CostructuredArrow.homMk (h.homEquiv _ _ B.pt.Hom) (by tidy)
  uniq s m w := by
    ext
    dsimp
    rw [h.eq_hom_equiv_apply, adjunction.hom_equiv_counit]
    exact costructured_arrow.w m
#align category_theory.mk_terminal_of_right_adjoint CategoryTheory.mkTerminalOfRightAdjoint

end

theorem nonempty_isRightAdjoint_iff_hasInitial_structuredArrow {G : D ⥤ C} :
    Nonempty (IsRightAdjoint G) ↔ ∀ A, HasInitial (StructuredArrow A G) :=
  ⟨fun ⟨h⟩ A => (mk_initial_of_left_adjoint _ h.adj A).HasInitial, fun h =>
    ⟨is_right_adjoint_of_structured_arrow_initials _⟩⟩
#align category_theory.nonempty_is_right_adjoint_iff_has_initial_structured_arrow CategoryTheory.nonempty_isRightAdjoint_iff_hasInitial_structuredArrow

theorem nonempty_isLeftAdjoint_iff_hasTerminal_costructuredArrow {F : C ⥤ D} :
    Nonempty (IsLeftAdjoint F) ↔ ∀ A, HasTerminal (CostructuredArrow F A) :=
  ⟨fun ⟨h⟩ A => (mk_terminal_of_right_adjoint _ h.adj A).HasTerminal, fun h =>
    ⟨is_left_adjoint_of_costructured_arrow_terminals _⟩⟩
#align category_theory.nonempty_is_left_adjoint_iff_has_terminal_costructured_arrow CategoryTheory.nonempty_isLeftAdjoint_iff_hasTerminal_costructuredArrow

end CategoryTheory

