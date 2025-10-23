/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Kevin Buzzard
-/
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Injective objects and categories with enough injectives

An object `J` is injective iff every morphism into `J` can be obtained by extending a monomorphism.
-/


noncomputable section

open CategoryTheory Limits Opposite

universe v v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

/--
An object `J` is injective iff every morphism into `J` can be obtained by extending a monomorphism.
-/
class Injective (J : C) : Prop where
  factors : ∀ {X Y : C} (g : X ⟶ J) (f : X ⟶ Y) [Mono f], ∃ h : Y ⟶ J, f ≫ h = g

attribute [inherit_doc Injective] Injective.factors

lemma Limits.IsZero.injective {X : C} (h : IsZero X) : Injective X where
  factors _ _ _ := ⟨h.from_ _, h.eq_of_tgt _ _⟩

section

/-- An injective presentation of an object `X` consists of a monomorphism `f : X ⟶ J`
to some injective object `J`.
-/
structure InjectivePresentation (X : C) where
  J : C
  injective : Injective J := by infer_instance
  f : X ⟶ J
  mono : Mono f := by infer_instance

open InjectivePresentation in
attribute [inherit_doc InjectivePresentation] J injective f mono

attribute [instance] InjectivePresentation.injective InjectivePresentation.mono

variable (C)

/-- A category "has enough injectives" if every object has an injective presentation,
i.e. if for every object `X` there is an injective object `J` and a monomorphism `X ↪ J`. -/
class EnoughInjectives : Prop where
  presentation : ∀ X : C, Nonempty (InjectivePresentation X)

attribute [inherit_doc EnoughInjectives] EnoughInjectives.presentation

end

namespace Injective

/--
Let `J` be injective and `g` a morphism into `J`, then `g` can be factored through any monomorphism.
-/
def factorThru {J X Y : C} [Injective J] (g : X ⟶ J) (f : X ⟶ Y) [Mono f] : Y ⟶ J :=
  (Injective.factors g f).choose

@[reassoc (attr := simp)]
theorem comp_factorThru {J X Y : C} [Injective J] (g : X ⟶ J) (f : X ⟶ Y) [Mono f] :
    f ≫ factorThru g f = g :=
  (Injective.factors g f).choose_spec

section

open ZeroObject

instance zero_injective [HasZeroObject C] : Injective (0 : C) :=
  (isZero_zero C).injective

end

theorem of_iso {P Q : C} (i : P ≅ Q) (hP : Injective P) : Injective Q :=
  {
    factors := fun g f mono => by
      obtain ⟨h, h_eq⟩ := @Injective.factors C _ P _ _ _ (g ≫ i.inv) f mono
      refine ⟨h ≫ i.hom, ?_⟩
      rw [← Category.assoc, h_eq, Category.assoc, Iso.inv_hom_id, Category.comp_id] }

theorem iso_iff {P Q : C} (i : P ≅ Q) : Injective P ↔ Injective Q :=
  ⟨of_iso i, of_iso i.symm⟩

/-- The axiom of choice says that every nonempty type is an injective object in `Type`. -/
instance (X : Type u₁) [Nonempty X] : Injective X where
  factors g f mono :=
    ⟨fun z => by
      classical
      exact
          if h : z ∈ Set.range f then g (Classical.choose h) else Nonempty.some inferInstance, by
      ext y
      classical
      change dite (f y ∈ Set.range f) (fun h => g (Classical.choose h)) _ = _
      split_ifs <;> rename_i h
      · rw [mono_iff_injective] at mono
        rw [mono (Classical.choose_spec h)]
      · exact False.elim (h ⟨y, rfl⟩)⟩

instance Type.enoughInjectives : EnoughInjectives (Type u₁) where
  presentation X :=
    Nonempty.intro
      { J := WithBot X
        injective := inferInstance
        f := WithBot.some
        mono := by
          rw [mono_iff_injective]
          exact WithBot.coe_injective }

instance {P Q : C} [HasBinaryProduct P Q] [Injective P] [Injective Q] : Injective (P ⨯ Q) where
  factors g f mono := by
    use Limits.prod.lift (factorThru (g ≫ Limits.prod.fst) f) (factorThru (g ≫ Limits.prod.snd) f)
    simp only [prod.comp_lift, comp_factorThru]
    ext
    · simp only [prod.lift_fst]
    · simp only [prod.lift_snd]

instance {β : Type v} (c : β → C) [HasProduct c] [∀ b, Injective (c b)] : Injective (∏ᶜ c) where
  factors g f mono := by
    refine ⟨Pi.lift fun b => factorThru (g ≫ Pi.π c _) f, ?_⟩
    ext b
    simp only [Category.assoc, limit.lift_π, Fan.mk_π_app, comp_factorThru]

instance {P Q : C} [HasZeroMorphisms C] [HasBinaryBiproduct P Q] [Injective P] [Injective Q] :
    Injective (P ⊞ Q) where
  factors g f mono := by
    refine ⟨biprod.lift (factorThru (g ≫ biprod.fst) f) (factorThru (g ≫ biprod.snd) f), ?_⟩
    ext
    · simp only [Category.assoc, biprod.lift_fst, comp_factorThru]
    · simp only [Category.assoc, biprod.lift_snd, comp_factorThru]

instance {β : Type v} (c : β → C) [HasZeroMorphisms C] [HasBiproduct c] [∀ b, Injective (c b)] :
    Injective (⨁ c) where
  factors g f mono := by
    refine ⟨biproduct.lift fun b => factorThru (g ≫ biproduct.π _ _) f, ?_⟩
    ext
    simp only [Category.assoc, biproduct.lift_π, comp_factorThru]

instance {P : Cᵒᵖ} [Projective P] : Injective no_index (unop P) where
  factors g f mono :=
    ⟨(@Projective.factorThru Cᵒᵖ _ P _ _ _ g.op f.op _).unop, Quiver.Hom.op_inj (by simp)⟩

instance {J : Cᵒᵖ} [Injective J] : Projective no_index (unop J) where
  factors f e he :=
    ⟨(@factorThru Cᵒᵖ _ J _ _ _ f.op e.op _).unop, Quiver.Hom.op_inj (by simp)⟩

instance {J : C} [Injective J] : Projective (op J) where
  factors f e epi :=
    ⟨(@factorThru C _ J _ _ _ f.unop e.unop _).op, Quiver.Hom.unop_inj (by simp)⟩

instance {P : C} [Projective P] : Injective (op P) where
  factors g f mono :=
    ⟨(@Projective.factorThru C _ P _ _ _ g.unop f.unop _).op, Quiver.Hom.unop_inj (by simp)⟩

theorem injective_iff_projective_op {J : C} : Injective J ↔ Projective (op J) :=
  ⟨fun _ => inferInstance, fun _ => show Injective (unop (op J)) from inferInstance⟩

theorem projective_iff_injective_op {P : C} : Projective P ↔ Injective (op P) :=
  ⟨fun _ => inferInstance, fun _ => show Projective (unop (op P)) from inferInstance⟩

theorem injective_iff_preservesEpimorphisms_yoneda_obj (J : C) :
    Injective J ↔ (yoneda.obj J).PreservesEpimorphisms := by
  rw [injective_iff_projective_op, Projective.projective_iff_preservesEpimorphisms_coyoneda_obj]
  exact Functor.preservesEpimorphisms.iso_iff (Coyoneda.objOpOp _)

section Adjunction

open CategoryTheory.Functor

variable {D : Type u₂} [Category.{v₂} D]
variable {L : C ⥤ D} {R : D ⥤ C} [PreservesMonomorphisms L]

theorem injective_of_adjoint (adj : L ⊣ R) (J : D) [Injective J] : Injective <| R.obj J :=
  ⟨fun {A} {_} g f im =>
    ⟨adj.homEquiv _ _ (factorThru ((adj.homEquiv A J).symm g) (L.map f)),
      (adj.homEquiv _ _).symm.injective
        (by simp [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit])⟩⟩

end Adjunction

section EnoughInjectives

variable [EnoughInjectives C]

/-- `Injective.under X` provides an arbitrarily chosen injective object equipped with
a monomorphism `Injective.ι : X ⟶ Injective.under X`.
-/
def under (X : C) : C :=
  (EnoughInjectives.presentation X).some.J

instance injective_under (X : C) : Injective (under X) :=
  (EnoughInjectives.presentation X).some.injective

/-- The monomorphism `Injective.ι : X ⟶ Injective.under X`
from the arbitrarily chosen injective object under `X`.
-/
def ι (X : C) : X ⟶ under X :=
  (EnoughInjectives.presentation X).some.f

instance ι_mono (X : C) : Mono (ι X) :=
  (EnoughInjectives.presentation X).some.mono

section

variable [HasZeroMorphisms C] {X Y : C} (f : X ⟶ Y) [HasCokernel f]

/-- When `C` has enough injectives, the object `Injective.syzygies f` is
an arbitrarily chosen injective object under `cokernel f`.
-/
def syzygies : C :=
  under (cokernel f)
deriving Injective

/-- When `C` has enough injective,
`Injective.d f : Y ⟶ syzygies f` is the composition
`cokernel.π f ≫ ι (cokernel f)`.

(When `C` is abelian, we have `exact f (injective.d f)`.)
-/
abbrev d : Y ⟶ syzygies f :=
  cokernel.π f ≫ ι (cokernel f)

end

end EnoughInjectives

instance [EnoughInjectives C] : EnoughProjectives Cᵒᵖ :=
  ⟨fun X => ⟨{ p := _, f := (Injective.ι (unop X)).op}⟩⟩

instance [EnoughProjectives C] : EnoughInjectives Cᵒᵖ :=
  ⟨fun X => ⟨⟨_, inferInstance, (Projective.π (unop X)).op, inferInstance⟩⟩⟩

theorem enoughProjectives_of_enoughInjectives_op [EnoughInjectives Cᵒᵖ] : EnoughProjectives C :=
  ⟨fun X => ⟨{ p := _, f := (Injective.ι (op X)).unop} ⟩⟩

theorem enoughInjectives_of_enoughProjectives_op [EnoughProjectives Cᵒᵖ] : EnoughInjectives C :=
  ⟨fun X => ⟨⟨_, inferInstance, (Projective.π (op X)).unop, inferInstance⟩⟩⟩

end Injective

namespace Adjunction

variable {D : Type*} [Category D] {F : C ⥤ D} {G : D ⥤ C}

theorem map_injective (adj : F ⊣ G) [F.PreservesMonomorphisms] (I : D) (hI : Injective I) :
    Injective (G.obj I) :=
  ⟨fun {X} {Y} f g => by
    intro
    rcases hI.factors (F.map f ≫ adj.counit.app _) (F.map g) with ⟨w,h⟩
    use adj.unit.app Y ≫ G.map w
    rw [← unit_naturality_assoc, ← G.map_comp, h]
    simp⟩

theorem injective_of_map_injective (adj : F ⊣ G) [G.Full] [G.Faithful] (I : D)
    (hI : Injective (G.obj I)) : Injective I :=
  ⟨fun {X} {Y} f g => by
    intro
    haveI : PreservesLimitsOfSize.{0, 0} G := adj.rightAdjoint_preservesLimits
    rcases hI.factors (G.map f) (G.map g) with ⟨w,h⟩
    use inv (adj.counit.app _) ≫ F.map w ≫ adj.counit.app _
    exact G.map_injective (by simpa)⟩

/-- Given an adjunction `F ⊣ G` such that `F` preserves monos, `G` maps an injective presentation
of `X` to an injective presentation of `G(X)`. -/
def mapInjectivePresentation (adj : F ⊣ G) [F.PreservesMonomorphisms] (X : D)
    (I : InjectivePresentation X) : InjectivePresentation (G.obj X) where
  J := G.obj I.J
  injective := adj.map_injective _ I.injective
  f := G.map I.f
  mono := by
    haveI : PreservesLimitsOfSize.{0, 0} G := adj.rightAdjoint_preservesLimits; infer_instance

/-- Given an adjunction `F ⊣ G` such that `F` preserves monomorphisms and is faithful,
  then any injective presentation of `F(X)` can be pulled back to an injective presentation of `X`.
  This is similar to `mapInjectivePresentation`. -/
def injectivePresentationOfMap (adj : F ⊣ G)
    [F.PreservesMonomorphisms] [F.ReflectsMonomorphisms] (X : C)
    (I : InjectivePresentation <| F.obj X) :
    InjectivePresentation X where
  J := G.obj I.J
  injective := Injective.injective_of_adjoint adj _
  f := adj.homEquiv _ _ I.f

end Adjunction

namespace Functor

variable {D : Type*} [Category D] (F : C ⥤ D)

theorem injective_of_map_injective [F.Full] [F.Faithful]
    [F.PreservesMonomorphisms] {I : C} (hI : Injective (F.obj I)) : Injective I where
  factors g f _ := by
    obtain ⟨h, fac⟩ := hI.factors (F.map g) (F.map f)
    exact ⟨F.preimage h, F.map_injective (by simp [fac])⟩

end Functor

/--
[Lemma 3.8](https://ncatlab.org/nlab/show/injective+object#preservation_of_injective_objects)
-/
lemma EnoughInjectives.of_adjunction {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [L.PreservesMonomorphisms] [L.ReflectsMonomorphisms]
    [EnoughInjectives D] : EnoughInjectives C where
  presentation _ :=
    ⟨adj.injectivePresentationOfMap _ (EnoughInjectives.presentation _).some⟩

/-- An equivalence of categories transfers enough injectives. -/
lemma EnoughInjectives.of_equivalence {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    (e : C ⥤ D) [e.IsEquivalence] [EnoughInjectives D] : EnoughInjectives C :=
  EnoughInjectives.of_adjunction (adj := e.asEquivalence.toAdjunction)

namespace Equivalence

variable {D : Type*} [Category D] (F : C ≌ D)

theorem map_injective_iff (P : C) : Injective (F.functor.obj P) ↔ Injective P :=
  ⟨F.symm.toAdjunction.injective_of_map_injective P, F.symm.toAdjunction.map_injective P⟩

/-- Given an equivalence of categories `F`, an injective presentation of `F(X)` induces an
injective presentation of `X.` -/
def injectivePresentationOfMapInjectivePresentation (X : C)
    (I : InjectivePresentation (F.functor.obj X)) : InjectivePresentation X :=
  F.toAdjunction.injectivePresentationOfMap _ I

theorem enoughInjectives_iff (F : C ≌ D) : EnoughInjectives C ↔ EnoughInjectives D :=
  ⟨fun h => h.of_adjunction F.symm.toAdjunction, fun h => h.of_adjunction F.toAdjunction⟩

end Equivalence

end CategoryTheory
