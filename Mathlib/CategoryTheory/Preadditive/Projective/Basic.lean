/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-!
# Projective objects and categories with enough projectives

An object `P` is called *projective* if every morphism out of `P` factors through every epimorphism.

A category `C` *has enough projectives* if every object admits an epimorphism from some
projective object.

`CategoryTheory.Projective.over X` picks an arbitrary such projective object, and
`CategoryTheory.Projective.π X : CategoryTheory.Projective.over X ⟶ X` is the corresponding
epimorphism.

Given a morphism `f : X ⟶ Y`, `CategoryTheory.Projective.left f` is a projective object over
`CategoryTheory.Limits.kernel f`, and `Projective.d f : Projective.left f ⟶ X` is the morphism
`π (kernel f) ≫ kernel.ι f`.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


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

variable (C) in
/-- The `ObjectProperty C` corresponding to the notion of projective objects in `C`. -/
abbrev isProjective : ObjectProperty C := Projective

lemma Limits.IsZero.projective {X : C} (h : IsZero X) : Projective X where
  factors _ _ _ := ⟨h.to_ _, h.eq_of_src _ _⟩

section

/-- A projective presentation of an object `X` consists of an epimorphism `f : P ⟶ X`
from some projective object `P`.
-/
structure ProjectivePresentation (X : C) where
  /-- The projective object `p` of this presentation -/
  p : C
  [projective : Projective p]
  /-- The epimorphism from `p` of this presentation -/
  f : p ⟶ X
  [epi : Epi f]

attribute [instance] ProjectivePresentation.projective ProjectivePresentation.epi

variable (C)

/-- A category "has enough projectives" if for every object `X` there is a projective object `P` and
an epimorphism `P ↠ X`. -/
class EnoughProjectives : Prop where
  presentation : ∀ X : C, Nonempty (ProjectivePresentation X)

attribute [instance low] EnoughProjectives.presentation

end

namespace Projective

/--
An arbitrarily chosen factorisation of a morphism out of a projective object through an epimorphism.
-/
def factorThru {P X E : C} [Projective P] (f : P ⟶ X) (e : E ⟶ X) [Epi e] : P ⟶ E :=
  (Projective.factors f e).choose

@[reassoc (attr := simp)]
theorem factorThru_comp {P X E : C} [Projective P] (f : P ⟶ X) (e : E ⟶ X) [Epi e] :
    factorThru f e ≫ e = f :=
  (Projective.factors f e).choose_spec

section

open ZeroObject

instance zero_projective [HasZeroObject C] : Projective (0 : C) :=
  (isZero_zero C).projective

end

theorem of_iso {P Q : C} (i : P ≅ Q) (_ : Projective P) : Projective Q where
  factors f e _ :=
    let ⟨f', hf'⟩ := Projective.factors (i.hom ≫ f) e
    ⟨i.inv ≫ f', by simp [hf']⟩

theorem iso_iff {P Q : C} (i : P ≅ Q) : Projective P ↔ Projective Q :=
  ⟨of_iso i, of_iso i.symm⟩

/-- The axiom of choice says that every type is a projective object in `Type`. -/
instance (X : Type u) : Projective X where
  factors f e _ :=
    have he : Function.Surjective e := surjective_of_epi e
    ⟨TypeCat.ofHom (fun x => (he (f x)).choose), by ext x; exact (he (f x)).choose_spec⟩

instance Type.enoughProjectives : EnoughProjectives (Type u) where
  presentation X := ⟨⟨X, 𝟙 X⟩⟩

set_option backward.isDefEq.respectTransparency false in
instance {P Q : C} [HasBinaryCoproduct P Q] [Projective P] [Projective Q] : Projective (P ⨿ Q) where
  factors f e epi := ⟨coprod.desc (factorThru (coprod.inl ≫ f) e) (factorThru (coprod.inr ≫ f) e),
    by cat_disch⟩

set_option backward.isDefEq.respectTransparency false in
instance {β : Type v} (g : β → C) [HasCoproduct g] [∀ b, Projective (g b)] : Projective (∐ g) where
  factors f e epi := ⟨Sigma.desc fun b => factorThru (Sigma.ι g b ≫ f) e, by cat_disch⟩

instance {P Q : C} [HasZeroMorphisms C] [HasBinaryBiproduct P Q] [Projective P] [Projective Q] :
    Projective (P ⊞ Q) where
  factors f e epi := ⟨biprod.desc (factorThru (biprod.inl ≫ f) e) (factorThru (biprod.inr ≫ f) e),
    by cat_disch⟩

instance {β : Type v} (g : β → C) [HasZeroMorphisms C] [HasBiproduct g] [∀ b, Projective (g b)] :
    Projective (⨁ g) where
  factors f e epi := ⟨biproduct.desc fun b => factorThru (biproduct.ι g b ≫ f) e, by cat_disch⟩

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

section EnoughProjectives

variable [EnoughProjectives C]

/-- `Projective.over X` provides an arbitrarily chosen projective object equipped with
an epimorphism `Projective.π : Projective.over X ⟶ X`.
-/
def over (X : C) : C :=
  (EnoughProjectives.presentation X).some.p

instance projective_over (X : C) : Projective (over X) :=
  (EnoughProjectives.presentation X).some.projective

/-- The epimorphism `projective.π : projective.over X ⟶ X`
from the arbitrarily chosen projective object over `X`.
-/
def π (X : C) : over X ⟶ X :=
  (EnoughProjectives.presentation X).some.f

instance π_epi (X : C) : Epi (π X) :=
  (EnoughProjectives.presentation X).some.epi

section

variable [HasZeroMorphisms C] {X Y : C} (f : X ⟶ Y) [HasKernel f]

/-- When `C` has enough projectives, the object `Projective.syzygies f` is
an arbitrarily chosen projective object over `kernel f`.
-/
def syzygies : C := over (kernel f)

instance : Projective (syzygies f) := inferInstanceAs (Projective (over _))

/-- When `C` has enough projectives,
`Projective.d f : Projective.syzygies f ⟶ X` is the composition
`π (kernel f) ≫ kernel.ι f`.

(When `C` is abelian, we have `exact (projective.d f) f`.)
-/
abbrev d : syzygies f ⟶ X :=
  π (kernel f) ≫ kernel.ι f

end

end EnoughProjectives

end Projective

namespace Adjunction

variable {D : Type u'} [Category.{v'} D] {F : C ⥤ D} {G : D ⥤ C}

set_option backward.isDefEq.respectTransparency false in
theorem map_projective (adj : F ⊣ G) [G.PreservesEpimorphisms] (P : C) (hP : Projective P) :
    Projective (F.obj P) where
  factors f g _ := by
    rcases hP.factors (adj.unit.app P ≫ G.map f) (G.map g) with ⟨f', hf'⟩
    use F.map f' ≫ adj.counit.app _
    rw [Category.assoc, ← Adjunction.counit_naturality, ← Category.assoc, ← F.map_comp, hf']
    simp

set_option backward.isDefEq.respectTransparency false in
theorem projective_of_map_projective (adj : F ⊣ G) [F.Full] [F.Faithful] (P : C)
    (hP : Projective (F.obj P)) : Projective P where
  factors f g _ := by
    haveI := Adjunction.leftAdjoint_preservesColimits.{0, 0} adj
    rcases (@hP).1 (F.map f) (F.map g) with ⟨f', hf'⟩
    use adj.unit.app _ ≫ G.map f' ≫ (inv <| adj.unit.app _)
    exact F.map_injective (by simpa)

/-- Given an adjunction `F ⊣ G` such that `G` preserves epis, `F` maps a projective presentation of
`X` to a projective presentation of `F(X)`. -/
def mapProjectivePresentation (adj : F ⊣ G) [G.PreservesEpimorphisms] (X : C)
    (Y : ProjectivePresentation X) : ProjectivePresentation (F.obj X) where
  p := F.obj Y.p
  projective := adj.map_projective _ Y.projective
  f := F.map Y.f
  epi := have := Adjunction.leftAdjoint_preservesColimits.{0, 0} adj; inferInstance

end Adjunction

namespace Functor

variable {D : Type*} [Category* D] (F : C ⥤ D)

theorem projective_of_map_projective [F.Full] [F.Faithful]
    [F.PreservesEpimorphisms] {P : C} (hP : Projective (F.obj P)) : Projective P where
  factors g f _ := by
    obtain ⟨h, fac⟩ := hP.factors (F.map g) (F.map f)
    exact ⟨F.preimage h, F.map_injective (by simp [fac])⟩

end Functor

namespace Equivalence

variable {D : Type u'} [Category.{v'} D] (F : C ≌ D)

theorem map_projective_iff (P : C) : Projective (F.functor.obj P) ↔ Projective P :=
  ⟨F.toAdjunction.projective_of_map_projective P, F.toAdjunction.map_projective P⟩

set_option backward.isDefEq.respectTransparency false in
/-- Given an equivalence of categories `F`, a projective presentation of `F(X)` induces a
projective presentation of `X.` -/
def projectivePresentationOfMapProjectivePresentation (X : C)
    (Y : ProjectivePresentation (F.functor.obj X)) : ProjectivePresentation X where
  p := F.inverse.obj Y.p
  projective := Adjunction.map_projective F.symm.toAdjunction Y.p Y.projective
  f := F.inverse.map Y.f ≫ F.unitInv.app _
  epi := epi_comp _ _

theorem enoughProjectives_iff (F : C ≌ D) : EnoughProjectives C ↔ EnoughProjectives D := by
  constructor
  all_goals intro H; constructor; intro X; constructor
  · exact F.symm.projectivePresentationOfMapProjectivePresentation _
      (Nonempty.some (H.presentation (F.inverse.obj X)))
  · exact F.projectivePresentationOfMapProjectivePresentation X
      (Nonempty.some (H.presentation (F.functor.obj X)))

end Equivalence

lemma Retract.projective {X Y : C} (h : Retract X Y) [p : Projective Y] : Projective X := by
  refine Projective.mk (fun {A B} f e _ ↦ ?_)
  rcases p.factors (h.r ≫ f) e with ⟨g, hg⟩
  use h.i ≫ g
  simp [hg]

end CategoryTheory
