/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Subobject.MonoOver

#align_import category_theory.subterminal from "leanprover-community/mathlib"@"bb103f356534a9a7d3596a672097e375290a4c3a"


/-!
# Subterminal objects

Subterminal objects are the objects which can be thought of as subobjects of the terminal object.
In fact, the definition can be constructed to not require a terminal object, by defining `A` to be
subterminal iff for any `Z`, there is at most one morphism `Z ⟶ A`.
An alternate definition is that the diagonal morphism `A ⟶ A ⨯ A` is an isomorphism.
In this file we define subterminal objects and show the equivalence of these three definitions.

We also construct the subcategory of subterminal objects.

## TODO

* Define exponential ideals, and show this subcategory is an exponential ideal.
* Use the above to show that in a locally cartesian closed category, every subobject lattice
  is cartesian closed (equivalently, a Heyting algebra).

-/


universe v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory

open Limits Category

variable {C : Type u₁} [Category.{v₁} C] {A : C}

/-- An object `A` is subterminal iff for any `Z`, there is at most one morphism `Z ⟶ A`. -/
def IsSubterminal (A : C) : Prop :=
  ∀ ⦃Z : C⦄ (f g : Z ⟶ A), f = g
#align category_theory.is_subterminal CategoryTheory.IsSubterminal

theorem IsSubterminal.def : IsSubterminal A ↔ ∀ ⦃Z : C⦄ (f g : Z ⟶ A), f = g :=
  Iff.rfl
#align category_theory.is_subterminal.def CategoryTheory.IsSubterminal.def

/-- If `A` is subterminal, the unique morphism from it to a terminal object is a monomorphism.
The converse of `isSubterminal_of_mono_isTerminal_from`.
-/
theorem IsSubterminal.mono_isTerminal_from (hA : IsSubterminal A) {T : C} (hT : IsTerminal T) :
    Mono (hT.from A) :=
  { right_cancellation := fun _ _ _ => hA _ _ }
#align category_theory.is_subterminal.mono_is_terminal_from CategoryTheory.IsSubterminal.mono_isTerminal_from

/-- If `A` is subterminal, the unique morphism from it to the terminal object is a monomorphism.
The converse of `isSubterminal_of_mono_terminal_from`.
-/
theorem IsSubterminal.mono_terminal_from [HasTerminal C] (hA : IsSubterminal A) :
    Mono (terminal.from A) :=
  hA.mono_isTerminal_from terminalIsTerminal
#align category_theory.is_subterminal.mono_terminal_from CategoryTheory.IsSubterminal.mono_terminal_from

/-- If the unique morphism from `A` to a terminal object is a monomorphism, `A` is subterminal.
The converse of `IsSubterminal.mono_isTerminal_from`.
-/
theorem isSubterminal_of_mono_isTerminal_from {T : C} (hT : IsTerminal T) [Mono (hT.from A)] :
    IsSubterminal A := fun Z f g => by
  rw [← cancel_mono (hT.from A)]
  apply hT.hom_ext
#align category_theory.is_subterminal_of_mono_is_terminal_from CategoryTheory.isSubterminal_of_mono_isTerminal_from

/-- If the unique morphism from `A` to the terminal object is a monomorphism, `A` is subterminal.
The converse of `IsSubterminal.mono_terminal_from`.
-/
theorem isSubterminal_of_mono_terminal_from [HasTerminal C] [Mono (terminal.from A)] :
    IsSubterminal A := fun Z f g => by
  rw [← cancel_mono (terminal.from A)]
  apply Subsingleton.elim
#align category_theory.is_subterminal_of_mono_terminal_from CategoryTheory.isSubterminal_of_mono_terminal_from

theorem isSubterminal_of_isTerminal {T : C} (hT : IsTerminal T) : IsSubterminal T := fun _ _ _ =>
  hT.hom_ext _ _
#align category_theory.is_subterminal_of_is_terminal CategoryTheory.isSubterminal_of_isTerminal

theorem isSubterminal_of_terminal [HasTerminal C] : IsSubterminal (⊤_ C) := fun _ _ _ =>
  Subsingleton.elim _ _
#align category_theory.is_subterminal_of_terminal CategoryTheory.isSubterminal_of_terminal

/-- If `A` is subterminal, its diagonal morphism is an isomorphism.
The converse of `isSubterminal_of_isIso_diag`.
-/
theorem IsSubterminal.isIso_diag (hA : IsSubterminal A) [HasBinaryProduct A A] : IsIso (diag A) :=
  ⟨⟨Limits.prod.fst,
      ⟨by simp, by
        rw [IsSubterminal.def] at hA
        aesop_cat⟩⟩⟩
#align category_theory.is_subterminal.is_iso_diag CategoryTheory.IsSubterminal.isIso_diag

/-- If the diagonal morphism of `A` is an isomorphism, then it is subterminal.
The converse of `isSubterminal.isIso_diag`.
-/
theorem isSubterminal_of_isIso_diag [HasBinaryProduct A A] [IsIso (diag A)] : IsSubterminal A :=
  fun Z f g => by
  have : (Limits.prod.fst : A ⨯ A ⟶ _) = Limits.prod.snd := by simp [← cancel_epi (diag A)]
  rw [← prod.lift_fst f g, this, prod.lift_snd]
#align category_theory.is_subterminal_of_is_iso_diag CategoryTheory.isSubterminal_of_isIso_diag

/-- If `A` is subterminal, it is isomorphic to `A ⨯ A`. -/
@[simps!]
def IsSubterminal.isoDiag (hA : IsSubterminal A) [HasBinaryProduct A A] : A ⨯ A ≅ A := by
  letI := IsSubterminal.isIso_diag hA
  apply (asIso (diag A)).symm
#align category_theory.is_subterminal.iso_diag CategoryTheory.IsSubterminal.isoDiag

variable (C)

/-- The (full sub)category of subterminal objects.
TODO: If `C` is the category of sheaves on a topological space `X`, this category is equivalent
to the lattice of open subsets of `X`. More generally, if `C` is a topos, this is the lattice of
"external truth values".
-/
def Subterminals (C : Type u₁) [Category.{v₁} C] :=
  FullSubcategory fun A : C => IsSubterminal A
#align category_theory.subterminals CategoryTheory.Subterminals

instance (C : Type u₁) [Category.{v₁} C] :
  Category (Subterminals C) := FullSubcategory.category _

instance [HasTerminal C] : Inhabited (Subterminals C) :=
  ⟨⟨⊤_ C, isSubterminal_of_terminal⟩⟩

/-- The inclusion of the subterminal objects into the original category. -/
@[simps!]
def subterminalInclusion : Subterminals C ⥤ C :=
  fullSubcategoryInclusion _
#align category_theory.subterminal_inclusion CategoryTheory.subterminalInclusion

instance (C : Type u₁) [Category.{v₁} C] : (subterminalInclusion C).Full :=
  FullSubcategory.full _

instance (C : Type u₁) [Category.{v₁} C] : (subterminalInclusion C).Faithful :=
  FullSubcategory.faithful _

instance subterminals_thin (X Y : Subterminals C) : Subsingleton (X ⟶ Y) :=
  ⟨fun f g => Y.2 f g⟩
#align category_theory.subterminals_thin CategoryTheory.subterminals_thin

/--
The category of subterminal objects is equivalent to the category of monomorphisms to the terminal
object (which is in turn equivalent to the subobjects of the terminal object).
-/
@[simps]
def subterminalsEquivMonoOverTerminal [HasTerminal C] : Subterminals C ≌ MonoOver (⊤_ C) where
  functor :=
    { obj := fun X => ⟨Over.mk (terminal.from X.1), X.2.mono_terminal_from⟩
      map := fun f => MonoOver.homMk f (by ext1 ⟨⟨⟩⟩)
      map_id := fun X => rfl
      map_comp := fun f g => rfl }
  inverse :=
    { obj := fun X =>
        ⟨X.obj.left, fun Z f g => by
          rw [← cancel_mono X.arrow]
          apply Subsingleton.elim⟩
      map := fun f => f.1
      map_id := fun X => rfl
      map_comp := fun f g => rfl }
  -- Porting note: the original definition was triggering a timeout, using `NatIso.ofComponents`
  -- in the definition of the natural isomorphisms makes the situation slightly better
  unitIso := NatIso.ofComponents (fun X => Iso.refl X) (fun _ => by apply Subsingleton.elim)
  counitIso := NatIso.ofComponents (fun X => MonoOver.isoMk (Iso.refl _))
    (fun _ => by apply Subsingleton.elim)
  functor_unitIso_comp := fun _ => by apply Subsingleton.elim
  -- With `aesop` filling the auto-params this was taking 20s or so
#align category_theory.subterminals_equiv_mono_over_terminal CategoryTheory.subterminalsEquivMonoOverTerminal

@[simp]
theorem subterminals_to_monoOver_terminal_comp_forget [HasTerminal C] :
    (subterminalsEquivMonoOverTerminal C).functor ⋙ MonoOver.forget _ ⋙ Over.forget _ =
      subterminalInclusion C :=
  rfl
#align category_theory.subterminals_to_mono_over_terminal_comp_forget CategoryTheory.subterminals_to_monoOver_terminal_comp_forget

@[simp]
theorem monoOver_terminal_to_subterminals_comp [HasTerminal C] :
    (subterminalsEquivMonoOverTerminal C).inverse ⋙ subterminalInclusion C =
      MonoOver.forget _ ⋙ Over.forget _ :=
  rfl
#align category_theory.mono_over_terminal_to_subterminals_comp CategoryTheory.monoOver_terminal_to_subterminals_comp

end CategoryTheory
