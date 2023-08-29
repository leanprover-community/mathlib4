/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison
-/
import Mathlib.Algebra.Homology.Exact
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Finite

#align_import category_theory.preadditive.projective from "leanprover-community/mathlib"@"3974a774a707e2e06046a14c0eaef4654584fada"

/-!
# Projective objects and categories with enough projectives

An object `P` is called *projective* if every morphism out of `P` factors through every epimorphism.

A category `C` *has enough projectives* if every object admits an epimorphism from some
projective object.

`CategoryTheory.Projective.over X` picks an arbitrary such projective object, and
`CategoryTheory.Projective.π X : CategoryTheory.Projective.over X ⟶ X` is the corresponding
epimorphism.

Given a morphism `f : X ⟶ Y`, `CategoryTheory.Projective.left f` is a projective object over
`CategoryTheory.Limits.kernel f`, and `projective.d f : projective.left f ⟶ X` is the morphism
`π (kernel f) ≫ kernel.ι f`.

-/


noncomputable section

open CategoryTheory Limits Opposite

universe v u v' u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/--
An object `P` is called *projective* if every morphism out of `P` factors through every epimorphism.
-/
class Projective (P : C) : Prop where
  factors : ∀ {E X : C} (f : P ⟶ X) (e : E ⟶ X) [Epi e], ∃ f', f' ≫ e = f
#align category_theory.projective CategoryTheory.Projective

section

/-- A projective presentation of an object `X` consists of an epimorphism `f : P ⟶ X`
from some projective object `P`.
-/
-- Porting note: was @[nolint has_nonempty_instance]
structure ProjectivePresentation (X : C) where
  p : C
  [projective : Projective p]
  f : p ⟶ X
  [epi : Epi f]
#align category_theory.projective_presentation CategoryTheory.ProjectivePresentation

attribute [instance] ProjectivePresentation.projective ProjectivePresentation.epi

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
  (Projective.factors f e).choose
#align category_theory.projective.factor_thru CategoryTheory.Projective.factorThru

@[simp]
theorem factorThru_comp {P X E : C} [Projective P] (f : P ⟶ X) (e : E ⟶ X) [Epi e] :
    factorThru f e ≫ e = f :=
  (Projective.factors f e).choose_spec
#align category_theory.projective.factor_thru_comp CategoryTheory.Projective.factorThru_comp

section

open ZeroObject

instance zero_projective [HasZeroObject C] [HasZeroMorphisms C] : Projective (0 : C) where
  factors f e _ := ⟨0, by ext⟩
                          -- 🎉 no goals
#align category_theory.projective.zero_projective CategoryTheory.Projective.zero_projective

end

theorem of_iso {P Q : C} (i : P ≅ Q) (hP : Projective P) : Projective Q where
  factors f e e_epi :=
    let ⟨f', hf'⟩ := Projective.factors (i.hom ≫ f) e
    ⟨i.inv ≫ f', by simp [hf']⟩
                    -- 🎉 no goals
#align category_theory.projective.of_iso CategoryTheory.Projective.of_iso

theorem iso_iff {P Q : C} (i : P ≅ Q) : Projective P ↔ Projective Q :=
  ⟨of_iso i, of_iso i.symm⟩
#align category_theory.projective.iso_iff CategoryTheory.Projective.iso_iff

/-- The axiom of choice says that every type is a projective object in `Type`. -/
instance (X : Type u) : Projective X where
  factors f e _ :=
    have he : Function.Surjective e := surjective_of_epi e
    ⟨fun x => (he (f x)).choose, funext fun x ↦ (he (f x)).choose_spec⟩

instance Type.enoughProjectives : EnoughProjectives (Type u) where
  presentation X := ⟨⟨X, 𝟙 X⟩⟩
#align category_theory.projective.Type.enough_projectives CategoryTheory.Projective.Type.enoughProjectives

instance {P Q : C} [HasBinaryCoproduct P Q] [Projective P] [Projective Q] : Projective (P ⨿ Q) where
  factors f e epi := ⟨coprod.desc (factorThru (coprod.inl ≫ f) e) (factorThru (coprod.inr ≫ f) e),
    by aesop_cat⟩
       -- 🎉 no goals

instance {β : Type v} (g : β → C) [HasCoproduct g] [∀ b, Projective (g b)] : Projective (∐ g) where
  factors f e epi := ⟨Sigma.desc fun b => factorThru (Sigma.ι g b ≫ f) e, by aesop_cat⟩
                                                                             -- 🎉 no goals

instance {P Q : C} [HasZeroMorphisms C] [HasBinaryBiproduct P Q] [Projective P] [Projective Q] :
    Projective (P ⊞ Q) where
  factors f e epi := ⟨biprod.desc (factorThru (biprod.inl ≫ f) e) (factorThru (biprod.inr ≫ f) e),
    by aesop_cat⟩
       -- 🎉 no goals

instance {β : Type v} (g : β → C) [HasZeroMorphisms C] [HasBiproduct g] [∀ b, Projective (g b)] :
    Projective (⨁ g) where
  factors f e epi := ⟨biproduct.desc fun b => factorThru (biproduct.ι g b ≫ f) e, by aesop_cat⟩
                                                                                     -- 🎉 no goals

theorem projective_iff_preservesEpimorphisms_coyoneda_obj (P : C) :
    Projective P ↔ (coyoneda.obj (op P)).PreservesEpimorphisms :=
  ⟨fun hP =>
    ⟨fun f _ =>
      (epi_iff_surjective _).2 fun g =>
        have : Projective (unop (op P)) := hP
        ⟨factorThru g f, factorThru_comp _ _⟩⟩,
    fun _ =>
    ⟨fun f e _ =>
      (epi_iff_surjective _).1 (inferInstance : Epi ((coyoneda.obj (op P)).map e)) f⟩⟩
#align category_theory.projective.projective_iff_preserves_epimorphisms_coyoneda_obj CategoryTheory.Projective.projective_iff_preservesEpimorphisms_coyoneda_obj

section EnoughProjectives

variable [EnoughProjectives C]

/-- `Projective.over X` provides an arbitrarily chosen projective object equipped with
an epimorphism `Projective.π : Projective.over X ⟶ X`.
-/
def over (X : C) : C :=
  (EnoughProjectives.presentation X).some.p
#align category_theory.projective.over CategoryTheory.Projective.over

instance projective_over (X : C) : Projective (over X) :=
  (EnoughProjectives.presentation X).some.projective
#align category_theory.projective.projective_over CategoryTheory.Projective.projective_over

/-- The epimorphism `projective.π : projective.over X ⟶ X`
from the arbitrarily chosen projective object over `X`.
-/
def π (X : C) : over X ⟶ X :=
  (EnoughProjectives.presentation X).some.f
#align category_theory.projective.π CategoryTheory.Projective.π

instance π_epi (X : C) : Epi (π X) :=
  (EnoughProjectives.presentation X).some.epi
#align category_theory.projective.π_epi CategoryTheory.Projective.π_epi

section

variable [HasZeroMorphisms C] {X Y : C} (f : X ⟶ Y) [HasKernel f]

/-- When `C` has enough projectives, the object `projective.syzygies f` is
an arbitrarily chosen projective object over `kernel f`.
-/
def syzygies : C := over (kernel f)
#align category_theory.projective.syzygies CategoryTheory.Projective.syzygies

instance : Projective (syzygies f) := inferInstanceAs (Projective (over _))

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

variable {D : Type u'} [Category.{v'} D] {F : C ⥤ D} {G : D ⥤ C}

theorem map_projective (adj : F ⊣ G) [G.PreservesEpimorphisms] (P : C) (hP : Projective P) :
    Projective (F.obj P) where
  factors f g _ := by
    rcases hP.factors (adj.unit.app P ≫ G.map f) (G.map g) with ⟨f', hf'⟩
    -- ⊢ ∃ f', f' ≫ g = f
    use F.map f' ≫ adj.counit.app _
    -- ⊢ (F.map f' ≫ NatTrans.app adj.counit E✝) ≫ g = f
    rw [Category.assoc, ← Adjunction.counit_naturality, ← Category.assoc, ← F.map_comp, hf']
    -- ⊢ F.map (NatTrans.app adj.unit P ≫ G.map f) ≫ NatTrans.app adj.counit X✝ = f
    simp
    -- 🎉 no goals
#align category_theory.adjunction.map_projective CategoryTheory.Adjunction.map_projective

theorem projective_of_map_projective (adj : F ⊣ G) [Full F] [Faithful F] (P : C)
    (hP : Projective (F.obj P)) : Projective P where
  factors f g _ := by
    haveI := Adjunction.leftAdjointPreservesColimits.{0, 0} adj
    -- ⊢ ∃ f', f' ≫ g = f
    rcases (@hP).1 (F.map f) (F.map g) with ⟨f', hf'⟩
    -- ⊢ ∃ f', f' ≫ g = f
    use adj.unit.app _ ≫ G.map f' ≫ (inv <| adj.unit.app _)
    -- ⊢ (NatTrans.app adj.unit P ≫ G.map f' ≫ inv (NatTrans.app adj.unit E✝)) ≫ g = f
    refine' Faithful.map_injective (F := F) _
    -- ⊢ F.map ((NatTrans.app adj.unit P ≫ G.map f' ≫ inv (NatTrans.app adj.unit E✝)) …
    simpa
    -- 🎉 no goals
#align category_theory.adjunction.projective_of_map_projective CategoryTheory.Adjunction.projective_of_map_projective

/-- Given an adjunction `F ⊣ G` such that `G` preserves epis, `F` maps a projective presentation of
`X` to a projective presentation of `F(X)`. -/
def mapProjectivePresentation (adj : F ⊣ G) [G.PreservesEpimorphisms] (X : C)
    (Y : ProjectivePresentation X) : ProjectivePresentation (F.obj X) where
  p := F.obj Y.p
  projective := adj.map_projective _ Y.projective
  f := F.map Y.f
  epi := have := Adjunction.leftAdjointPreservesColimits.{0, 0} adj; inferInstance
#align category_theory.adjunction.map_projective_presentation CategoryTheory.Adjunction.mapProjectivePresentation

end Adjunction

namespace Equivalence

variable {D : Type u'} [Category.{v'} D] (F : C ≌ D)

/-- Given an equivalence of categories `F`, a projective presentation of `F(X)` induces a
projective presentation of `X.` -/
def projectivePresentationOfMapProjectivePresentation (X : C)
    (Y : ProjectivePresentation (F.functor.obj X)) : ProjectivePresentation X where
  p := F.inverse.obj Y.p
  projective := Adjunction.map_projective F.symm.toAdjunction Y.p Y.projective
  f := F.inverse.map Y.f ≫ F.unitInv.app _
  epi := epi_comp _ _
#align category_theory.equivalence.projective_presentation_of_map_projective_presentation CategoryTheory.Equivalence.projectivePresentationOfMapProjectivePresentation

theorem enoughProjectives_iff (F : C ≌ D) : EnoughProjectives C ↔ EnoughProjectives D := by
  constructor
  -- ⊢ EnoughProjectives C → EnoughProjectives D
  all_goals intro H; constructor; intro X; constructor
  -- ⊢ ProjectivePresentation X
  · exact F.symm.projectivePresentationOfMapProjectivePresentation _
      (Nonempty.some (H.presentation (F.inverse.obj X)))
  · exact F.projectivePresentationOfMapProjectivePresentation X
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
  -- See the porting note on `Exact.epi`.
  haveI := hfg.epi
  factorThru (factorThru (factorThruKernelSubobject g h w) (imageToKernel f g hfg.w))
    (factorThruImageSubobject f)
#align category_theory.exact.lift CategoryTheory.Exact.lift

@[simp]
theorem Exact.lift_comp {P Q R S : C} [Projective P] (h : P ⟶ R) (f : Q ⟶ R) (g : R ⟶ S)
    (hfg : Exact f g) (w : h ≫ g = 0) : Exact.lift h f g hfg w ≫ f = h := by
  simp only [Exact.lift]
  -- ⊢ factorThru (factorThru (factorThruKernelSubobject g h w) (imageToKernel f g  …
  conv_lhs =>
    congr
    rfl
    rw [← imageSubobject_arrow_comp f]
  -- See the porting note on `Exact.epi`.
  haveI := hfg.epi
  -- ⊢ factorThru (factorThru (factorThruKernelSubobject g h w) (imageToKernel f g  …
  rw [← Category.assoc, factorThru_comp, ← imageToKernel_arrow f g, ← Category.assoc,
    CategoryTheory.Projective.factorThru_comp, factorThruKernelSubobject_comp_arrow]
#align category_theory.exact.lift_comp CategoryTheory.Exact.lift_comp

end

end CategoryTheory
