/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison

! This file was ported from Lean 3 source module category_theory.preadditive.projective
! leanprover-community/mathlib commit f8d8465c3c392a93b9ed226956e26dee00975946
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Homology.Exact
import Mathbin.CategoryTheory.Limits.Shapes.Biproducts
import Mathbin.CategoryTheory.Adjunction.Limits
import Mathbin.CategoryTheory.Limits.Preserves.Finite

/-!
# Projective objects and categories with enough projectives

An object `P` is called projective if every morphism out of `P` factors through every epimorphism.

A category `C` has enough projectives if every object admits an epimorphism from some
projective object.

`projective.over X` picks an arbitrary such projective object,
and `projective.π X : projective.over X ⟶ X` is the corresponding epimorphism.

Given a morphism `f : X ⟶ Y`, `projective.left f` is a projective object over `kernel f`,
and `projective.d f : projective.left f ⟶ X` is the morphism `π (kernel f) ≫ kernel.ι f`.
-/


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

open Opposite

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/--
An object `P` is called projective if every morphism out of `P` factors through every epimorphism.
-/
class Projective (P : C) : Prop where
  Factors : ∀ {E X : C} (f : P ⟶ X) (e : E ⟶ X) [Epi e], ∃ f', f' ≫ e = f
#align category_theory.projective CategoryTheory.Projective

section

/-- A projective presentation of an object `X` consists of an epimorphism `f : P ⟶ X`
from some projective object `P`.
-/
@[nolint has_nonempty_instance]
structure ProjectivePresentation (X : C) where
  p : C
  Projective : Projective P := by infer_instance
  f : P ⟶ X
  Epi : Epi f := by infer_instance
#align category_theory.projective_presentation CategoryTheory.ProjectivePresentation

attribute [instance] projective_presentation.projective projective_presentation.epi

variable (C)

/-- A category "has enough projectives" if for every object `X` there is a projective object `P` and
    an epimorphism `P ↠ X`. -/
class EnoughProjectives : Prop where
  presentation : ∀ X : C, Nonempty (ProjectivePresentation X)
#align category_theory.enough_projectives CategoryTheory.EnoughProjectives

end

namespace Projective

/--
An arbitrarily chosen factorisation of a morphism out of a projective object through an epimorphism.
-/
def factorThru {P X E : C} [Projective P] (f : P ⟶ X) (e : E ⟶ X) [Epi e] : P ⟶ E :=
  (Projective.factors f e).some
#align category_theory.projective.factor_thru CategoryTheory.Projective.factorThru

@[simp]
theorem factorThru_comp {P X E : C} [Projective P] (f : P ⟶ X) (e : E ⟶ X) [Epi e] :
    factorThru f e ≫ e = f :=
  (Projective.factors f e).choose_spec
#align category_theory.projective.factor_thru_comp CategoryTheory.Projective.factorThru_comp

section

open ZeroObject

instance zero_projective [HasZeroObject C] [HasZeroMorphisms C] : Projective (0 : C)
    where Factors E X f e epi := by
    use 0
    ext
#align category_theory.projective.zero_projective CategoryTheory.Projective.zero_projective

end

theorem of_iso {P Q : C} (i : P ≅ Q) (hP : Projective P) : Projective Q :=
  by
  fconstructor
  intro E X f e e_epi
  obtain ⟨f', hf'⟩ := projective.factors (i.hom ≫ f) e
  exact ⟨i.inv ≫ f', by simp [hf']⟩
#align category_theory.projective.of_iso CategoryTheory.Projective.of_iso

theorem iso_iff {P Q : C} (i : P ≅ Q) : Projective P ↔ Projective Q :=
  ⟨of_iso i, of_iso i.symm⟩
#align category_theory.projective.iso_iff CategoryTheory.Projective.iso_iff

/-- The axiom of choice says that every type is a projective object in `Type`. -/
instance (X : Type u) : Projective X
    where Factors E X' f e epi :=
    ⟨fun x => ((epi_iff_surjective _).mp epi (f x)).some,
      by
      ext x
      exact ((epi_iff_surjective _).mp epi (f x)).choose_spec⟩

instance Type.enoughProjectives : EnoughProjectives (Type u)
    where presentation X :=
    ⟨{  p := X
        f := 𝟙 X }⟩
#align category_theory.projective.Type.enough_projectives CategoryTheory.Projective.Type.enoughProjectives

instance {P Q : C} [HasBinaryCoproduct P Q] [Projective P] [Projective Q] : Projective (P ⨿ Q)
    where Factors E X' f e epi :=
    ⟨coprod.desc (factor_thru (coprod.inl ≫ f) e) (factor_thru (coprod.inr ≫ f) e), by tidy⟩

section

attribute [local tidy] tactic.discrete_cases

instance {β : Type v} (g : β → C) [HasCoproduct g] [∀ b, Projective (g b)] : Projective (∐ g)
    where Factors E X' f e epi := ⟨sigma.desc fun b => factor_thru (sigma.ι g b ≫ f) e, by tidy⟩

end

instance {P Q : C} [HasZeroMorphisms C] [HasBinaryBiproduct P Q] [Projective P] [Projective Q] :
    Projective (P ⊞ Q)
    where Factors E X' f e epi :=
    ⟨biprod.desc (factor_thru (biprod.inl ≫ f) e) (factor_thru (biprod.inr ≫ f) e), by tidy⟩

instance {β : Type v} (g : β → C) [HasZeroMorphisms C] [HasBiproduct g] [∀ b, Projective (g b)] :
    Projective (⨁ g)
    where Factors E X' f e epi :=
    ⟨biproduct.desc fun b => factor_thru (biproduct.ι g b ≫ f) e, by tidy⟩

theorem projective_iff_preservesEpimorphisms_coyoneda_obj (P : C) :
    Projective P ↔ (coyoneda.obj (op P)).PreservesEpimorphisms :=
  ⟨fun hP =>
    ⟨fun X Y f hf =>
      (epi_iff_surjective _).2 fun g =>
        have : Projective (unop (op P)) := hP
        ⟨factor_thru g f, factor_thru_comp _ _⟩⟩,
    fun h =>
    ⟨fun E X f e he =>
      (epi_iff_surjective _).1 (inferInstance : epi ((coyoneda.obj (op P)).map e)) f⟩⟩
#align category_theory.projective.projective_iff_preserves_epimorphisms_coyoneda_obj CategoryTheory.Projective.projective_iff_preservesEpimorphisms_coyoneda_obj

section EnoughProjectives

variable [EnoughProjectives C]

/-- `projective.over X` provides an arbitrarily chosen projective object equipped with
an epimorphism `projective.π : projective.over X ⟶ X`.
-/
def over (X : C) : C :=
  (EnoughProjectives.presentation X).some.p
#align category_theory.projective.over CategoryTheory.Projective.over

instance projective_over (X : C) : Projective (over X) :=
  (EnoughProjectives.presentation X).some.Projective
#align category_theory.projective.projective_over CategoryTheory.Projective.projective_over

/-- The epimorphism `projective.π : projective.over X ⟶ X`
from the arbitrarily chosen projective object over `X`.
-/
def π (X : C) : over X ⟶ X :=
  (EnoughProjectives.presentation X).some.f
#align category_theory.projective.π CategoryTheory.Projective.π

instance π_epi (X : C) : Epi (π X) :=
  (EnoughProjectives.presentation X).some.Epi
#align category_theory.projective.π_epi CategoryTheory.Projective.π_epi

section

variable [HasZeroMorphisms C] {X Y : C} (f : X ⟶ Y) [HasKernel f]

/-- When `C` has enough projectives, the object `projective.syzygies f` is
an arbitrarily chosen projective object over `kernel f`.
-/
def syzygies : C :=
  over (kernel f)deriving Projective
#align category_theory.projective.syzygies CategoryTheory.Projective.syzygies

/-- When `C` has enough projectives,
`projective.d f : projective.syzygies f ⟶ X` is the composition
`π (kernel f) ≫ kernel.ι f`.

(When `C` is abelian, we have `exact (projective.d f) f`.)
-/
abbrev d : syzygies f ⟶ X :=
  π (kernel f) ≫ kernel.ι f
#align category_theory.projective.d CategoryTheory.Projective.d

end

end EnoughProjectives

end Projective

namespace Adjunction

variable {D : Type _} [Category D] {F : C ⥤ D} {G : D ⥤ C}

theorem map_projective (adj : F ⊣ G) [G.PreservesEpimorphisms] (P : C) (hP : Projective P) :
    Projective (F.obj P) :=
  ⟨fun X Y f g => by
    intro
    rcases hP.factors (adj.unit.app P ≫ G.map f) (G.map g) with ⟨⟩
    use F.map w ≫ adj.counit.app X
    rw [category.assoc, ← adjunction.counit_naturality, ← category.assoc, ← F.map_comp, h]
    simp⟩
#align category_theory.adjunction.map_projective CategoryTheory.Adjunction.map_projective

theorem projective_of_map_projective (adj : F ⊣ G) [Full F] [Faithful F] (P : C)
    (hP : Projective (F.obj P)) : Projective P :=
  ⟨fun X Y f g => by
    intro
    haveI := adj.left_adjoint_preserves_colimits
    rcases(@hP).1 (F.map f) (F.map g) with ⟨⟩
    use adj.unit.app _ ≫ G.map w ≫ (inv <| adj.unit.app _)
    refine' faithful.map_injective F _
    simpa⟩
#align category_theory.adjunction.projective_of_map_projective CategoryTheory.Adjunction.projective_of_map_projective

/-- Given an adjunction `F ⊣ G` such that `G` preserves epis, `F` maps a projective presentation of
`X` to a projective presentation of `F(X)`. -/
def mapProjectivePresentation (adj : F ⊣ G) [G.PreservesEpimorphisms] (X : C)
    (Y : ProjectivePresentation X) : ProjectivePresentation (F.obj X)
    where
  p := F.obj Y.p
  Projective := adj.map_projective _ Y.Projective
  f := F.map Y.f
  Epi := by haveI := adj.left_adjoint_preserves_colimits <;> infer_instance
#align category_theory.adjunction.map_projective_presentation CategoryTheory.Adjunction.mapProjectivePresentation

end Adjunction

namespace Equivalence

variable {D : Type _} [Category D] (F : C ≌ D)

/-- Given an equivalence of categories `F`, a projective presentation of `F(X)` induces a
projective presentation of `X.` -/
def projectivePresentationOfMapProjectivePresentation (X : C)
    (Y : ProjectivePresentation (F.Functor.obj X)) : ProjectivePresentation X
    where
  p := F.inverse.obj Y.p
  Projective := Adjunction.map_projective F.symm.toAdjunction Y.p Y.Projective
  f := F.inverse.map Y.f ≫ F.unitInv.app _
  Epi := epi_comp _ _
#align category_theory.equivalence.projective_presentation_of_map_projective_presentation CategoryTheory.Equivalence.projectivePresentationOfMapProjectivePresentation

theorem enoughProjectives_iff (F : C ≌ D) : EnoughProjectives C ↔ EnoughProjectives D :=
  by
  constructor
  all_goals intro H; constructor; intro X; constructor
  ·
    exact
      F.symm.projective_presentation_of_map_projective_presentation _
        (Nonempty.some (H.presentation (F.inverse.obj X)))
  ·
    exact
      F.projective_presentation_of_map_projective_presentation X
        (Nonempty.some (H.presentation (F.functor.obj X)))
#align category_theory.equivalence.enough_projectives_iff CategoryTheory.Equivalence.enoughProjectives_iff

end Equivalence

open Projective

section

variable [HasZeroMorphisms C] [HasEqualizers C] [HasImages C]

/-- Given a projective object `P` mapping via `h` into
the middle object `R` of a pair of exact morphisms `f : Q ⟶ R` and `g : R ⟶ S`,
such that `h ≫ g = 0`, there is a lift of `h` to `Q`.
-/
def Exact.lift {P Q R S : C} [Projective P] (h : P ⟶ R) (f : Q ⟶ R) (g : R ⟶ S) (hfg : Exact f g)
    (w : h ≫ g = 0) : P ⟶ Q :=
  factorThru (factorThru (factorThruKernelSubobject g h w) (imageToKernel f g hfg.w))
    (factorThruImageSubobject f)
#align category_theory.exact.lift CategoryTheory.Exact.lift

@[simp]
theorem Exact.lift_comp {P Q R S : C} [Projective P] (h : P ⟶ R) (f : Q ⟶ R) (g : R ⟶ S)
    (hfg : Exact f g) (w : h ≫ g = 0) : Exact.lift h f g hfg w ≫ f = h :=
  by
  simp [exact.lift]
  conv_lhs =>
    congr
    skip
    rw [← image_subobject_arrow_comp f]
  rw [← category.assoc, factor_thru_comp, ← imageToKernel_arrow, ← category.assoc,
    CategoryTheory.Projective.factorThru_comp, factor_thru_kernel_subobject_comp_arrow]
#align category_theory.exact.lift_comp CategoryTheory.Exact.lift_comp

end

end CategoryTheory

