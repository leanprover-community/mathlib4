/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Kevin Buzzard

! This file was ported from Lean 3 source module category_theory.preadditive.injective
! leanprover-community/mathlib commit 3974a774a707e2e06046a14c0eaef4654584fada
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Preadditive.Projective

/-!
# Injective objects and categories with enough injectives

An object `J` is injective iff every morphism into `J` can be obtained by extending a monomorphism.
-/


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

open Opposite

universe v v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

/--
An object `J` is injective iff every morphism into `J` can be obtained by extending a monomorphism.
-/
class Injective (J : C) : Prop where
  Factors : ∀ {X Y : C} (g : X ⟶ J) (f : X ⟶ Y) [Mono f], ∃ h : Y ⟶ J, f ≫ h = g
#align category_theory.injective CategoryTheory.Injective

section

/-- An injective presentation of an object `X` consists of a monomorphism `f : X ⟶ J`
to some injective object `J`.
-/
@[nolint has_nonempty_instance]
structure InjectivePresentation (X : C) where
  j : C
  Injective : Injective J := by infer_instance
  f : X ⟶ J
  Mono : Mono f := by infer_instance
#align category_theory.injective_presentation CategoryTheory.InjectivePresentation

attribute [instance] injective_presentation.injective injective_presentation.mono

variable (C)

/-- A category "has enough injectives" if every object has an injective presentation,
i.e. if for every object `X` there is an injective object `J` and a monomorphism `X ↪ J`. -/
class EnoughInjectives : Prop where
  presentation : ∀ X : C, Nonempty (InjectivePresentation X)
#align category_theory.enough_injectives CategoryTheory.EnoughInjectives

end

namespace Injective

/--
Let `J` be injective and `g` a morphism into `J`, then `g` can be factored through any monomorphism.
-/
def factorThru {J X Y : C} [Injective J] (g : X ⟶ J) (f : X ⟶ Y) [Mono f] : Y ⟶ J :=
  (Injective.factors g f).some
#align category_theory.injective.factor_thru CategoryTheory.Injective.factorThru

@[simp]
theorem comp_factorThru {J X Y : C} [Injective J] (g : X ⟶ J) (f : X ⟶ Y) [Mono f] :
    f ≫ factorThru g f = g :=
  (Injective.factors g f).choose_spec
#align category_theory.injective.comp_factor_thru CategoryTheory.Injective.comp_factorThru

section

open ZeroObject

instance zero_injective [HasZeroObject C] [HasZeroMorphisms C] : Injective (0 : C)
    where Factors X Y g f mono := ⟨0, by ext⟩
#align category_theory.injective.zero_injective CategoryTheory.Injective.zero_injective

end

theorem of_iso {P Q : C} (i : P ≅ Q) (hP : Injective P) : Injective Q :=
  {
    Factors := fun X Y g f mono =>
      by
      obtain ⟨h, h_eq⟩ := @injective.factors C _ P _ _ _ (g ≫ i.inv) f mono
      refine' ⟨h ≫ i.hom, _⟩
      rw [← category.assoc, h_eq, category.assoc, iso.inv_hom_id, category.comp_id] }
#align category_theory.injective.of_iso CategoryTheory.Injective.of_iso

theorem iso_iff {P Q : C} (i : P ≅ Q) : Injective P ↔ Injective Q :=
  ⟨of_iso i, of_iso i.symm⟩
#align category_theory.injective.iso_iff CategoryTheory.Injective.iso_iff

/-- The axiom of choice says that every nonempty type is an injective object in `Type`. -/
instance (X : Type u₁) [Nonempty X] : Injective X
    where Factors Y Z g f mono :=
    ⟨fun z => by
      classical exact
          if h : z ∈ Set.range f then g (Classical.choose h) else Nonempty.some inferInstance,
      by
      ext y
      change dite _ _ _ = _
      split_ifs
      · rw [mono_iff_injective] at mono
        rw [mono (Classical.choose_spec h)]
      · exact False.elim (h ⟨y, rfl⟩)⟩

instance Type.enoughInjectives : EnoughInjectives (Type u₁)
    where presentation X :=
    Nonempty.intro
      { j := WithBot X
        Injective := inferInstance
        f := Option.some
        Mono := by
          rw [mono_iff_injective]
          exact Option.some_injective X }
#align category_theory.injective.Type.enough_injectives CategoryTheory.Injective.Type.enoughInjectives

instance {P Q : C} [HasBinaryProduct P Q] [Injective P] [Injective Q] : Injective (P ⨯ Q)
    where Factors X Y g f mono := by
    skip
    use limits.prod.lift (factor_thru (g ≫ limits.prod.fst) f) (factor_thru (g ≫ limits.prod.snd) f)
    simp only [prod.comp_lift, comp_factor_thru]
    ext
    · simp only [prod.lift_fst]
    · simp only [prod.lift_snd]

instance {β : Type v} (c : β → C) [HasProduct c] [∀ b, Injective (c b)] : Injective (∏ c)
    where Factors X Y g f mono := by
    skip
    refine' ⟨pi.lift fun b => factor_thru (g ≫ pi.π c _) f, _⟩
    ext ⟨j⟩
    simp only [category.assoc, limit.lift_π, fan.mk_π_app, comp_factor_thru]

instance {P Q : C} [HasZeroMorphisms C] [HasBinaryBiproduct P Q] [Injective P] [Injective Q] :
    Injective (P ⊞ Q)
    where Factors X Y g f mono := by
    skip
    refine' ⟨biprod.lift (factor_thru (g ≫ biprod.fst) f) (factor_thru (g ≫ biprod.snd) f), _⟩
    ext
    · simp only [category.assoc, biprod.lift_fst, comp_factor_thru]
    · simp only [category.assoc, biprod.lift_snd, comp_factor_thru]

instance {β : Type v} (c : β → C) [HasZeroMorphisms C] [HasBiproduct c] [∀ b, Injective (c b)] :
    Injective (⨁ c)
    where Factors X Y g f mono := by
    skip
    refine' ⟨biproduct.lift fun b => factor_thru (g ≫ biproduct.π _ _) f, _⟩
    ext
    simp only [category.assoc, biproduct.lift_π, comp_factor_thru]

instance {P : Cᵒᵖ} [Projective P] : Injective (unop P)
    where Factors X Y g f mono :=
    ⟨(@projective.factor_thru Cᵒᵖ _ P _ _ _ g.op f.op _).unop, Quiver.Hom.op_inj (by simp)⟩

instance {J : Cᵒᵖ} [Injective J] : Projective (unop J)
    where Factors E X f e he :=
    ⟨(@factor_thru Cᵒᵖ _ J _ _ _ f.op e.op _).unop, Quiver.Hom.op_inj (by simp)⟩

instance {J : C} [Injective J] : Projective (op J)
    where Factors E X f e epi :=
    ⟨(@factor_thru C _ J _ _ _ f.unop e.unop _).op, Quiver.Hom.unop_inj (by simp)⟩

instance {P : C} [Projective P] : Injective (op P)
    where Factors X Y g f mono :=
    ⟨(@projective.factor_thru C _ P _ _ _ g.unop f.unop _).op, Quiver.Hom.unop_inj (by simp)⟩

theorem injective_iff_projective_op {J : C} : Injective J ↔ Projective (op J) :=
  ⟨fun h => inferInstance, fun h => show Injective (unop (op J)) from inferInstance⟩
#align category_theory.injective.injective_iff_projective_op CategoryTheory.Injective.injective_iff_projective_op

theorem projective_iff_injective_op {P : C} : Projective P ↔ Injective (op P) :=
  ⟨fun h => inferInstance, fun h => show Projective (unop (op P)) from inferInstance⟩
#align category_theory.injective.projective_iff_injective_op CategoryTheory.Injective.projective_iff_injective_op

theorem injective_iff_preservesEpimorphisms_yoneda_obj (J : C) :
    Injective J ↔ (yoneda.obj J).PreservesEpimorphisms :=
  by
  rw [injective_iff_projective_op, projective.projective_iff_preserves_epimorphisms_coyoneda_obj]
  exact functor.preserves_epimorphisms.iso_iff (coyoneda.obj_op_op _)
#align category_theory.injective.injective_iff_preserves_epimorphisms_yoneda_obj CategoryTheory.Injective.injective_iff_preservesEpimorphisms_yoneda_obj

section Adjunction

open CategoryTheory.Functor

variable {D : Type u₂} [Category.{v₂} D]

variable {L : C ⥤ D} {R : D ⥤ C} [PreservesMonomorphisms L]

theorem injective_of_adjoint (adj : L ⊣ R) (J : D) [Injective J] : Injective <| R.obj J :=
  ⟨fun A A' g f im =>
    ⟨adj.hom_equiv _ _ (factor_thru ((adj.hom_equiv A J).symm g) (L.map f)),
      (adj.hom_equiv _ _).symm.Injective (by simp)⟩⟩
#align category_theory.injective.injective_of_adjoint CategoryTheory.Injective.injective_of_adjoint

end Adjunction

section EnoughInjectives

variable [EnoughInjectives C]

/-- `injective.under X` provides an arbitrarily chosen injective object equipped with
an monomorphism `injective.ι : X ⟶ injective.under X`.
-/
def under (X : C) : C :=
  (EnoughInjectives.presentation X).some.j
#align category_theory.injective.under CategoryTheory.Injective.under

instance injective_under (X : C) : Injective (under X) :=
  (EnoughInjectives.presentation X).some.Injective
#align category_theory.injective.injective_under CategoryTheory.Injective.injective_under

/-- The monomorphism `injective.ι : X ⟶ injective.under X`
from the arbitrarily chosen injective object under `X`.
-/
def ι (X : C) : X ⟶ under X :=
  (EnoughInjectives.presentation X).some.f
#align category_theory.injective.ι CategoryTheory.Injective.ι

instance ι_mono (X : C) : Mono (ι X) :=
  (EnoughInjectives.presentation X).some.Mono
#align category_theory.injective.ι_mono CategoryTheory.Injective.ι_mono

section

variable [HasZeroMorphisms C] {X Y : C} (f : X ⟶ Y) [HasCokernel f]

/-- When `C` has enough injectives, the object `injective.syzygies f` is
an arbitrarily chosen injective object under `cokernel f`.
-/
def syzygies : C :=
  under (cokernel f)deriving Injective
#align category_theory.injective.syzygies CategoryTheory.Injective.syzygies

/-- When `C` has enough injective,
`injective.d f : Y ⟶ syzygies f` is the composition
`cokernel.π f ≫ ι (cokernel f)`.

(When `C` is abelian, we have `exact f (injective.d f)`.)
-/
abbrev d : Y ⟶ syzygies f :=
  cokernel.π f ≫ ι (cokernel f)
#align category_theory.injective.d CategoryTheory.Injective.d

end

end EnoughInjectives

instance [EnoughInjectives C] : EnoughProjectives Cᵒᵖ :=
  ⟨fun X => ⟨⟨_, inferInstance, (Injective.ι (unop X)).op, inferInstance⟩⟩⟩

instance [EnoughProjectives C] : EnoughInjectives Cᵒᵖ :=
  ⟨fun X => ⟨⟨_, inferInstance, (Projective.π (unop X)).op, inferInstance⟩⟩⟩

theorem enoughProjectives_of_enoughInjectives_op [EnoughInjectives Cᵒᵖ] : EnoughProjectives C :=
  ⟨fun X => ⟨⟨_, inferInstance, (Injective.ι (op X)).unop, inferInstance⟩⟩⟩
#align category_theory.injective.enough_projectives_of_enough_injectives_op CategoryTheory.Injective.enoughProjectives_of_enoughInjectives_op

theorem enoughInjectives_of_enoughProjectives_op [EnoughProjectives Cᵒᵖ] : EnoughInjectives C :=
  ⟨fun X => ⟨⟨_, inferInstance, (Projective.π (op X)).unop, inferInstance⟩⟩⟩
#align category_theory.injective.enough_injectives_of_enough_projectives_op CategoryTheory.Injective.enoughInjectives_of_enoughProjectives_op

open Injective

section

variable [HasZeroMorphisms C] [HasImages Cᵒᵖ] [HasEqualizers Cᵒᵖ]

/-- Given a pair of exact morphism `f : Q ⟶ R` and `g : R ⟶ S` and a map `h : R ⟶ J` to an injective
object `J` such that `f ≫ h = 0`, then `g` descents to a map `S ⟶ J`. See below:

```
Q --- f --> R --- g --> S
            |
            | h
            v
            J
```
-/
def Exact.desc {J Q R S : C} [Injective J] (h : R ⟶ J) (f : Q ⟶ R) (g : R ⟶ S)
    (hgf : Exact g.op f.op) (w : f ≫ h = 0) : S ⟶ J :=
  (Exact.lift h.op g.op f.op hgf (congr_arg Quiver.Hom.op w)).unop
#align category_theory.injective.exact.desc CategoryTheory.Injective.Exact.desc

@[simp]
theorem Exact.comp_desc {J Q R S : C} [Injective J] (h : R ⟶ J) (f : Q ⟶ R) (g : R ⟶ S)
    (hgf : Exact g.op f.op) (w : f ≫ h = 0) : g ≫ Exact.desc h f g hgf w = h := by
  convert congr_arg Quiver.Hom.unop (exact.lift_comp h.op g.op f.op hgf (congr_arg Quiver.Hom.op w))
#align category_theory.injective.exact.comp_desc CategoryTheory.Injective.Exact.comp_desc

end

end Injective

namespace Adjunction

variable {D : Type _} [Category D] {F : C ⥤ D} {G : D ⥤ C}

theorem map_injective (adj : F ⊣ G) [F.PreservesMonomorphisms] (I : D) (hI : Injective I) :
    Injective (G.obj I) :=
  ⟨fun X Y f g => by
    intro
    rcases hI.factors (F.map f ≫ adj.counit.app _) (F.map g) with ⟨⟩
    use adj.unit.app Y ≫ G.map w
    rw [← unit_naturality_assoc, ← G.map_comp, h]
    simp⟩
#align category_theory.adjunction.map_injective CategoryTheory.Adjunction.map_injective

theorem injective_of_map_injective (adj : F ⊣ G) [Full G] [Faithful G] (I : D)
    (hI : Injective (G.obj I)) : Injective I :=
  ⟨fun X Y f g => by
    intro
    haveI : PreservesLimitsOfSize.{0, 0} G := adj.right_adjoint_preserves_limits
    rcases hI.factors (G.map f) (G.map g) with ⟨⟩
    use inv (adj.counit.app _) ≫ F.map w ≫ adj.counit.app _
    refine' faithful.map_injective G _
    simpa⟩
#align category_theory.adjunction.injective_of_map_injective CategoryTheory.Adjunction.injective_of_map_injective

/-- Given an adjunction `F ⊣ G` such that `F` preserves monos, `G` maps an injective presentation
of `X` to an injective presentation of `G(X)`. -/
def mapInjectivePresentation (adj : F ⊣ G) [F.PreservesMonomorphisms] (X : D)
    (I : InjectivePresentation X) : InjectivePresentation (G.obj X)
    where
  j := G.obj I.j
  Injective := adj.map_injective _ I.Injective
  f := G.map I.f
  Mono := by
    haveI : PreservesLimitsOfSize.{0, 0} G := adj.right_adjoint_preserves_limits <;> infer_instance
#align category_theory.adjunction.map_injective_presentation CategoryTheory.Adjunction.mapInjectivePresentation

end Adjunction

namespace Equivalence

variable {D : Type _} [Category D] (F : C ≌ D)

/-- Given an equivalence of categories `F`, an injective presentation of `F(X)` induces an
injective presentation of `X.` -/
def injectivePresentationOfMapInjectivePresentation (X : C)
    (I : InjectivePresentation (F.Functor.obj X)) : InjectivePresentation X
    where
  j := F.inverse.obj I.j
  Injective := Adjunction.map_injective F.toAdjunction I.j I.Injective
  f := F.Unit.app _ ≫ F.inverse.map I.f
  Mono := mono_comp _ _
#align category_theory.equivalence.injective_presentation_of_map_injective_presentation CategoryTheory.Equivalence.injectivePresentationOfMapInjectivePresentation

theorem enoughInjectives_iff (F : C ≌ D) : EnoughInjectives C ↔ EnoughInjectives D :=
  by
  constructor
  all_goals intro H; constructor; intro X; constructor
  ·
    exact
      F.symm.injective_presentation_of_map_injective_presentation _
        (Nonempty.some (H.presentation (F.inverse.obj X)))
  ·
    exact
      F.injective_presentation_of_map_injective_presentation X
        (Nonempty.some (H.presentation (F.functor.obj X)))
#align category_theory.equivalence.enough_injectives_iff CategoryTheory.Equivalence.enoughInjectives_iff

end Equivalence

end CategoryTheory

