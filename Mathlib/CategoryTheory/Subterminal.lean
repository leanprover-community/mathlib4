/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Sina Hazratpour
-/
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Subobject.MonoOver

/-!
# Subterminal objects

Subterminal objects are the objects which can be thought of as subobjects of the terminal object.
In fact, the definition can be constructed to not require a terminal object, by defining `A` to be
subterminal iff for any `Z`, there is at most one morphism `Z ⟶ A`.
An alternate definition is that the diagonal morphism `A ⟶ A ⨯ A` is an isomorphism.
In this file we define subterminal objects and show the equivalence of these three definitions.

We also construct the subcategory of subterminal objects.

Dually, a preinitial object is an object with at most one morphism to each given object.
In the presence of an initial object, the unique morphism `⊥ ⟶ P` to the preinitial object is an
epimorphism. Moreover, every preinitial object is an epimorph of the initial object.
In a category with binary coproducts, `P` is preinitial if and only if the codiagonal morphism
`P ⨿ P ⟶ P` is an isomorphism.

## TODO

* Define exponential ideals, and show this subcategory is an exponential ideal.
* Use the above to show that in a locally cartesian closed category, every subobject lattice
  is cartesian closed (equivalently, a Heyting algebra).

* The category of preinitial objects is equivalent to the category of epimorphisms from the
initial object (which is in turn equivalent to the quotient of the initial object by the relation
of being isomorphic).

-/


universe v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory

open Limits Category

variable {C : Type u₁} [Category.{v₁} C] {A : C}

/-- An object `A` is subterminal iff for any `Z`, there is at most one morphism `Z ⟶ A`. -/
def IsSubterminal (A : C) : Prop :=
  ∀ ⦃Z : C⦄ (f g : Z ⟶ A), f = g

theorem IsSubterminal.def : IsSubterminal A ↔ ∀ ⦃Z : C⦄ (f g : Z ⟶ A), f = g :=
  Iff.rfl

/-- If `A` is subterminal, the unique morphism from it to a terminal object is a monomorphism.
The converse of `isSubterminal_of_mono_isTerminal_from`.
-/
theorem IsSubterminal.mono_isTerminal_from (hA : IsSubterminal A) {T : C} (hT : IsTerminal T) :
    Mono (hT.from A) :=
  { right_cancellation := fun _ _ _ => hA _ _ }

/-- If `A` is subterminal, the unique morphism from it to the terminal object is a monomorphism.
The converse of `isSubterminal_of_mono_terminal_from`.
-/
theorem IsSubterminal.mono_terminal_from [HasTerminal C] (hA : IsSubterminal A) :
    Mono (terminal.from A) :=
  hA.mono_isTerminal_from terminalIsTerminal

/-- If the unique morphism from `A` to a terminal object is a monomorphism, `A` is subterminal.
The converse of `IsSubterminal.mono_isTerminal_from`.
-/
theorem isSubterminal_of_mono_isTerminal_from {T : C} (hT : IsTerminal T) [Mono (hT.from A)] :
    IsSubterminal A := fun Z f g => by
  rw [← cancel_mono (hT.from A)]
  apply hT.hom_ext

/-- If the unique morphism from `A` to the terminal object is a monomorphism, `A` is subterminal.
The converse of `IsSubterminal.mono_terminal_from`.
-/
theorem isSubterminal_of_mono_terminal_from [HasTerminal C] [Mono (terminal.from A)] :
    IsSubterminal A := fun Z f g => by
  rw [← cancel_mono (terminal.from A)]
  subsingleton

theorem isSubterminal_of_isTerminal {T : C} (hT : IsTerminal T) : IsSubterminal T := fun _ _ _ =>
  hT.hom_ext _ _

theorem isSubterminal_of_terminal [HasTerminal C] : IsSubterminal (⊤_ C) := fun _ _ _ => by
  subsingleton

/-- `A` is subterminal iff the first and second projections from `A ⨯ A` to `A` are equal. -/
@[simp]
theorem IsSubterminal.prod_proj_eq_iff [HasBinaryProduct A A] :
    IsSubterminal A ↔ (prod.fst : A ⨯ A ⟶ A) = Limits.prod.snd := by
  constructor
  · intro hA
    apply hA
  · intro heq Z f g
    have : prod.lift f g ≫ prod.fst = prod.lift f g ≫ prod.snd := by rw [heq]
    simpa using this

/-- If `A` is subterminal, its diagonal morphism is an isomorphism.
The converse of `isSubterminal_of_isIso_diag`.
-/
theorem IsSubterminal.isIso_diag (hA : IsSubterminal A) [HasBinaryProduct A A] : IsIso (diag A) :=
  ⟨⟨Limits.prod.fst,
      ⟨by simp, by
        rw [IsSubterminal.def] at hA
        aesop_cat⟩⟩⟩

/-- If `A` is subterminal, it is isomorphic to `A ⨯ A`. -/
@[simps!]
def IsSubterminal.isoDiag (hA : IsSubterminal A) [HasBinaryProduct A A] : A ⨯ A ≅ A := by
  letI := IsSubterminal.isIso_diag hA
  apply (asIso (diag A)).symm

/-- If the diagonal morphism of `A` is an isomorphism, `A` is subterminal. -/
theorem isSubterminal_of_isIso_diag [HasBinaryProduct A A] [IsIso (diag A)] : IsSubterminal A :=
  fun Z f g => by
  have : (prod.fst : A ⨯ A ⟶ A) = prod.snd := by simp [← cancel_epi (diag A)]
  apply IsSubterminal.prod_proj_eq_iff.mpr this

/-- `A` is subterminal iff the first projection from `A ⨯ A` to `A` is an isomorphism. -/
theorem IsSubterminal.isIso_fst_iff {A : C} [HasBinaryProduct A A] :
    IsSubterminal A ↔ IsIso (prod.fst : A ⨯ A ⟶ A) := by
  constructor
  · intro h
    refine ⟨prod.lift (𝟙 A) (𝟙 A), by aesop, by aesop⟩
  · intro h Z f g
    have : IsIso (diag A) := by
      have := IsIso.inv_eq_of_inv_hom_id (f:= prod.fst) (g:= diag A) (by simp)
      rw [← this]
      infer_instance
    apply isSubterminal_of_isIso_diag

variable (C)

/-- The (full sub)category of subterminal objects.
TODO: If `C` is the category of sheaves on a topological space `X`, this category is equivalent
to the lattice of open subsets of `X`. More generally, if `C` is a topos, this is the lattice of
"external truth values".
-/
def Subterminals (C : Type u₁) [Category.{v₁} C] :=
  FullSubcategory fun A : C => IsSubterminal A

instance (C : Type u₁) [Category.{v₁} C] :
  Category (Subterminals C) := FullSubcategory.category _

instance [HasTerminal C] : Inhabited (Subterminals C) :=
  ⟨⟨⊤_ C, isSubterminal_of_terminal⟩⟩

/-- The inclusion of the subterminal objects into the original category. -/
@[simps!]
def subterminalInclusion : Subterminals C ⥤ C :=
  fullSubcategoryInclusion _

instance (C : Type u₁) [Category.{v₁} C] : (subterminalInclusion C).Full :=
  FullSubcategory.full _

instance (C : Type u₁) [Category.{v₁} C] : (subterminalInclusion C).Faithful :=
  FullSubcategory.faithful _

instance subterminals_thin (X Y : Subterminals C) : Subsingleton (X ⟶ Y) :=
  ⟨fun f g => Y.2 f g⟩

/--
The category of subterminal objects is equivalent to the category of monomorphisms to the terminal
object (which is in turn equivalent to the subobjects of the terminal object).
-/
@[simps]
def subterminalsEquivMonoOverTerminal [HasTerminal C] : Subterminals C ≌ MonoOver (⊤_ C) where
  functor :=
    { obj := fun X => ⟨Over.mk (terminal.from X.1), X.2.mono_terminal_from⟩
      map := fun f => MonoOver.homMk f (by ext1 ⟨⟨⟩⟩)
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }
  inverse :=
    { obj := fun X =>
        ⟨X.obj.left, fun Z f g => by
          rw [← cancel_mono X.arrow]
          subsingleton⟩
      map := fun f => f.1
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }
  -- Porting note: the original definition was triggering a timeout, using `NatIso.ofComponents`
  -- in the definition of the natural isomorphisms makes the situation slightly better
  unitIso := NatIso.ofComponents (fun X => Iso.refl X) (by subsingleton)
  counitIso := NatIso.ofComponents (fun X => MonoOver.isoMk (Iso.refl _)) (by subsingleton)
  functor_unitIso_comp := by subsingleton
  -- With `aesop` filling the auto-params this was taking 20s or so

@[simp]
theorem subterminals_to_monoOver_terminal_comp_forget [HasTerminal C] :
    (subterminalsEquivMonoOverTerminal C).functor ⋙ MonoOver.forget _ ⋙ Over.forget _ =
      subterminalInclusion C :=
  rfl

@[simp]
theorem monoOver_terminal_to_subterminals_comp [HasTerminal C] :
    (subterminalsEquivMonoOverTerminal C).inverse ⋙ subterminalInclusion C =
      MonoOver.forget _ ⋙ Over.forget _ :=
  rfl

variable {C}

/-- A preinitial object is an object with at most one morphism to each given object. -/
def IsPreinitial (P : C) : Prop :=
  ∀ ⦃Z : C⦄ (f g : P ⟶ Z), f = g

variable {P : C}

theorem IsPreinitial.def : IsPreinitial P ↔ ∀ ⦃Z : C⦄ (f g : P ⟶ Z), f = g :=
  Iff.rfl

/-- If `P` is preinitial, the unique morphism to it from an initial object is an epimorphism.
The converse of `isPreinitial_of_epi_initial_to`. -/
theorem IsPreinitial.epi_initial_to (hP : IsPreinitial P) {I : C} (hI : IsInitial I) :
    Epi (hI.to P) :=
  { left_cancellation := fun _ _ _ => hP _ _ }

/-- If `P` is preinitial, the unique morphism to it from the initial object is an epimorphism.
The converse of `isPreinitial_of_epi_initial_to`. -/
theorem IsPreinitial.epi_initial_to' [HasInitial C] (hP : IsPreinitial P) :
    Epi (initial.to P) :=
  hP.epi_initial_to initialIsInitial

/-- If the unique morphism to `P` from an initial object is an epimorphism, `P` is preinitial.
The converse of `IsPreinitial.epi_initial_to`. -/
theorem isPreinitial_of_epi_initial_to {I : C} (hI : IsInitial I) [Epi (hI.to P)] :
    IsPreinitial P := fun Z f g => by
  rw [← cancel_epi (hI.to P)]
  apply hI.hom_ext

/-- If the unique morphism to `P` from the initial object is an epimorphism, `P` is preinitial.
The converse of `IsPreinitial.epi_initial_to'. -/
theorem isPreinitial_of_epi_initial_to' [HasInitial C] [Epi (initial.to P)] :
    IsPreinitial P := fun Z f g => by
  rw [← cancel_epi (initial.to P)]
  subsingleton

theorem isPreinitial_of_isInitial {I : C} (hI : IsInitial I) : IsPreinitial I := fun _ _ _ =>
  hI.hom_ext _ _

theorem isPreinitial_of_initial [HasInitial C] : IsPreinitial (⊥_ C) := fun _ _ _ => by
  subsingleton

/-- `P` is preinitial if and only if the left and right coprojections from `P` to `P ⨿ P`
are equal. -/
@[simp]
theorem IsPreinitial.inl_eq_inr_iff [HasBinaryCoproduct P P] :
    IsPreinitial P ↔ (coprod.inl : P ⟶ P ⨿ P) = coprod.inr := by
  constructor
  · intro hP
    apply hP
  · intro heq Z f g
    have : coprod.inl ≫ coprod.desc f g = coprod.inr ≫ coprod.desc f g := by rw [heq]
    simpa using this

/-- If `P` is preinitial, its codiagonal morphism is an isomorphism.
The converse of `isPreinitial_of_isIso_codiag`. -/
theorem IsPreinitial.isIso_codiag (hP : IsPreinitial P) [HasBinaryCoproduct P P] :
    IsIso (codiag P) :=
  ⟨⟨coprod.inl,
      ⟨by aesop, by
        simp only [coprod.inl_desc]⟩⟩⟩

/-- If `P` is preinitial, it is isomorphic to `P ⨿ P`. -/
@[simps!]
def IsPreinitial.isoCodiag (hP : IsPreinitial P) [HasBinaryCoproduct P P] : P ⨿ P ≅ P := by
  letI := IsPreinitial.isIso_codiag hP
  apply (asIso (codiag P))

/-- If the codiagonal morphism of `P` is an isomorphism, then it is preinitial.
The converse of `isPreinitial.isIso_codiag`. -/
theorem isPreinitial_of_isIso_codiag [HasBinaryCoproduct P P] [IsIso (codiag P)] :
    IsPreinitial P :=
  fun Z f g => by
  have : (coprod.inl : P ⟶ P ⨿ P) = coprod.inr := by simp [← cancel_mono (codiag P)]
  apply IsPreinitial.inl_eq_inr_iff.mpr this

/-- `P` is preinitial if and only if the (left) coproduct coprojection `P ⟶ P ⨿ P`
is an isomorphism. -/
theorem IsPreinitial.isIso_inl_iff {P : C}
    [HasBinaryCoproduct P P] :
    IsPreinitial P ↔ IsIso (coprod.inl : P ⟶ P ⨿ P) := by
  constructor
  · intro h
    refine ⟨coprod.desc (𝟙 P) (𝟙 P), by simp only [coprod.inl_desc] , by aesop⟩
  · intro h Z f g
    have : IsIso (codiag P) := by
      have := IsIso.inv_eq_of_hom_inv_id (f:= coprod.inl) (g:= codiag P) (coprod.inl_desc _ _)
      rw [← this]
      infer_instance
    apply isPreinitial_of_isIso_codiag

variable (C)

/-- The (full sub)category of preinitial objects. -/
def Preinitials (C : Type u₁) [Category.{v₁} C] :=
  FullSubcategory fun P : C => IsPreinitial P

instance (C : Type u₁) [Category.{v₁} C] :
  Category (Preinitials C) := FullSubcategory.category _

instance [HasInitial C] : Inhabited (Preinitials C) :=
  ⟨⟨⊥_ C, isPreinitial_of_initial⟩⟩

/-- The inclusion of the preinitial objects into the original category. -/
@[simps!]
def preinitialInclusion : Preinitials C ⥤ C :=
  fullSubcategoryInclusion _

instance (C : Type u₁) [Category.{v₁} C] : (preinitialInclusion C).Full :=
  FullSubcategory.full _

instance (C : Type u₁) [Category.{v₁} C] : (preinitialInclusion C).Faithful :=
  FullSubcategory.faithful _

instance preinitials_thin (X Y : Preinitials C) : Subsingleton (X ⟶ Y) :=
  ⟨fun f g => X.2 f g⟩

end CategoryTheory
