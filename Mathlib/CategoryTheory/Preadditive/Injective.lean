/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Kevin Buzzard
-/
import Mathlib.CategoryTheory.Preadditive.Projective

#align_import category_theory.preadditive.injective from "leanprover-community/mathlib"@"3974a774a707e2e06046a14c0eaef4654584fada"

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
  factors : ∀ {X Y : C} (g : X ⟶ J) (f : X ⟶ Y) [Mono f], ∃ h : Y ⟶ J, f ≫ h = g
#align category_theory.injective CategoryTheory.Injective

attribute [inherit_doc Injective] Injective.factors

section

/-- An injective presentation of an object `X` consists of a monomorphism `f : X ⟶ J`
to some injective object `J`.
-/
structure InjectivePresentation (X : C) where
  J : C
  injective : Injective J := by infer_instance
  f : X ⟶ J
  mono : Mono f := by infer_instance
#align category_theory.injective_presentation CategoryTheory.InjectivePresentation

open InjectivePresentation in
attribute [inherit_doc InjectivePresentation] J injective f mono

attribute [instance] InjectivePresentation.injective InjectivePresentation.mono

variable (C)

/-- A category "has enough injectives" if every object has an injective presentation,
i.e. if for every object `X` there is an injective object `J` and a monomorphism `X ↪ J`. -/
class EnoughInjectives : Prop where
  presentation : ∀ X : C, Nonempty (InjectivePresentation X)
#align category_theory.enough_injectives CategoryTheory.EnoughInjectives

attribute [inherit_doc EnoughInjectives] EnoughInjectives.presentation

end

namespace Injective

/--
Let `J` be injective and `g` a morphism into `J`, then `g` can be factored through any monomorphism.
-/
def factorThru {J X Y : C} [Injective J] (g : X ⟶ J) (f : X ⟶ Y) [Mono f] : Y ⟶ J :=
  (Injective.factors g f).choose
#align category_theory.injective.factor_thru CategoryTheory.Injective.factorThru

@[simp]
theorem comp_factorThru {J X Y : C} [Injective J] (g : X ⟶ J) (f : X ⟶ Y) [Mono f] :
    f ≫ factorThru g f = g :=
  (Injective.factors g f).choose_spec
#align category_theory.injective.comp_factor_thru CategoryTheory.Injective.comp_factorThru

section

open ZeroObject

instance zero_injective [HasZeroObject C] [HasZeroMorphisms C] : Injective (0 : C) where
  factors g f := ⟨0, by ext⟩
                        -- 🎉 no goals
#align category_theory.injective.zero_injective CategoryTheory.Injective.zero_injective

end

theorem of_iso {P Q : C} (i : P ≅ Q) (hP : Injective P) : Injective Q :=
  {
    factors := fun g f mono => by
      obtain ⟨h, h_eq⟩ := @Injective.factors C _ P _ _ _ (g ≫ i.inv) f mono
      -- ⊢ ∃ h, f ≫ h = g
      refine' ⟨h ≫ i.hom, _⟩
      -- ⊢ f ≫ h ≫ i.hom = g
      rw [← Category.assoc, h_eq, Category.assoc, Iso.inv_hom_id, Category.comp_id] }
      -- 🎉 no goals
#align category_theory.injective.of_iso CategoryTheory.Injective.of_iso

theorem iso_iff {P Q : C} (i : P ≅ Q) : Injective P ↔ Injective Q :=
  ⟨of_iso i, of_iso i.symm⟩
#align category_theory.injective.iso_iff CategoryTheory.Injective.iso_iff

/-- The axiom of choice says that every nonempty type is an injective object in `Type`. -/
instance (X : Type u₁) [Nonempty X] : Injective X where
  factors g f mono :=
    ⟨fun z => by
      classical
      exact
          if h : z ∈ Set.range f then g (Classical.choose h) else Nonempty.some inferInstance, by
      ext y
      -- ⊢ (f ≫ fun z => if h : z ∈ Set.range f then g (Classical.choose h) else Nonemp …
      classical
      change dite (f y ∈ Set.range f) (fun h => g (Classical.choose h)) _ = _
      split_ifs <;> rename_i h
      · rw [mono_iff_injective] at mono
        erw [mono (Classical.choose_spec h)]
      · exact False.elim (h ⟨y, rfl⟩)⟩

instance Type.enoughInjectives : EnoughInjectives (Type u₁) where
  presentation X :=
    Nonempty.intro
      { J := WithBot X
        injective := inferInstance
        f := Option.some
        mono := by
          rw [mono_iff_injective]
          -- ⊢ Function.Injective some
          exact Option.some_injective X }
          -- 🎉 no goals
#align category_theory.injective.Type.enough_injectives CategoryTheory.Injective.Type.enoughInjectives

instance {P Q : C} [HasBinaryProduct P Q] [Injective P] [Injective Q] : Injective (P ⨯ Q) where
  factors g f mono := by
    skip
    -- ⊢ ∃ h, f ≫ h = g
    use Limits.prod.lift (factorThru (g ≫ Limits.prod.fst) f) (factorThru (g ≫ Limits.prod.snd) f)
    -- ⊢ f ≫ prod.lift (factorThru (g ≫ prod.fst) f) (factorThru (g ≫ prod.snd) f) = g
    simp only [prod.comp_lift, comp_factorThru]
    -- ⊢ prod.lift (g ≫ prod.fst) (g ≫ prod.snd) = g
    ext
    -- ⊢ prod.lift (g ≫ prod.fst) (g ≫ prod.snd) ≫ prod.fst = g ≫ prod.fst
    · simp only [prod.lift_fst]
      -- 🎉 no goals
    · simp only [prod.lift_snd]
      -- 🎉 no goals

instance {β : Type v} (c : β → C) [HasProduct c] [∀ b, Injective (c b)] : Injective (∏ c) where
  factors g f mono := by
    skip
    -- ⊢ ∃ h, f ≫ h = g
    refine' ⟨Pi.lift fun b => factorThru (g ≫ Pi.π c _) f, _⟩
    -- ⊢ (f ≫ Pi.lift fun b => factorThru (g ≫ Pi.π c b) f) = g
    ext b
    -- ⊢ (f ≫ Pi.lift fun b => factorThru (g ≫ Pi.π c b) f) ≫ Pi.π c b = g ≫ Pi.π c b
    simp only [Category.assoc, limit.lift_π, Fan.mk_π_app, comp_factorThru]
    -- 🎉 no goals

instance {P Q : C} [HasZeroMorphisms C] [HasBinaryBiproduct P Q] [Injective P] [Injective Q] :
    Injective (P ⊞ Q) where
  factors g f mono := by
    skip
    -- ⊢ ∃ h, f ≫ h = g
    refine' ⟨biprod.lift (factorThru (g ≫ biprod.fst) f) (factorThru (g ≫ biprod.snd) f), _⟩
    -- ⊢ f ≫ biprod.lift (factorThru (g ≫ biprod.fst) f) (factorThru (g ≫ biprod.snd) …
    ext
    -- ⊢ (f ≫ biprod.lift (factorThru (g ≫ biprod.fst) f) (factorThru (g ≫ biprod.snd …
    · simp only [Category.assoc, biprod.lift_fst, comp_factorThru]
      -- 🎉 no goals
    · simp only [Category.assoc, biprod.lift_snd, comp_factorThru]
      -- 🎉 no goals

instance {β : Type v} (c : β → C) [HasZeroMorphisms C] [HasBiproduct c] [∀ b, Injective (c b)] :
    Injective (⨁ c) where
  factors g f mono := by
    skip
    -- ⊢ ∃ h, f ≫ h = g
    refine' ⟨biproduct.lift fun b => factorThru (g ≫ biproduct.π _ _) f, _⟩
    -- ⊢ (f ≫ biproduct.lift fun b => factorThru (g ≫ biproduct.π c b) f) = g
    ext
    -- ⊢ (f ≫ biproduct.lift fun b => factorThru (g ≫ biproduct.π c b) f) ≫ biproduct …
    simp only [Category.assoc, biproduct.lift_π, comp_factorThru]
    -- 🎉 no goals

instance {P : Cᵒᵖ} [Projective P] : Injective (unop P) where
  factors g f mono :=
    ⟨(@Projective.factorThru Cᵒᵖ _ P _ _ _ g.op f.op _).unop, Quiver.Hom.op_inj (by simp)⟩
                                                                                    -- 🎉 no goals

instance {J : Cᵒᵖ} [Injective J] : Projective (unop J) where
  factors f e he :=
    ⟨(@factorThru Cᵒᵖ _ J _ _ _ f.op e.op _).unop, Quiver.Hom.op_inj (by simp)⟩
                                                                         -- 🎉 no goals

instance {J : C} [Injective J] : Projective (op J) where
  factors f e epi :=
    ⟨(@factorThru C _ J _ _ _ f.unop e.unop _).op, Quiver.Hom.unop_inj (by simp)⟩
                                                                           -- 🎉 no goals

instance {P : C} [Projective P] : Injective (op P) where
  factors g f mono :=
    ⟨(@Projective.factorThru C _ P _ _ _ g.unop f.unop _).op, Quiver.Hom.unop_inj (by simp)⟩
                                                                                      -- 🎉 no goals

theorem injective_iff_projective_op {J : C} : Injective J ↔ Projective (op J) :=
  ⟨fun _ => inferInstance, fun _ => show Injective (unop (op J)) from inferInstance⟩
#align category_theory.injective.injective_iff_projective_op CategoryTheory.Injective.injective_iff_projective_op

theorem projective_iff_injective_op {P : C} : Projective P ↔ Injective (op P) :=
  ⟨fun _ => inferInstance, fun _ => show Projective (unop (op P)) from inferInstance⟩
#align category_theory.injective.projective_iff_injective_op CategoryTheory.Injective.projective_iff_injective_op

theorem injective_iff_preservesEpimorphisms_yoneda_obj (J : C) :
    Injective J ↔ (yoneda.obj J).PreservesEpimorphisms := by
  rw [injective_iff_projective_op, Projective.projective_iff_preservesEpimorphisms_coyoneda_obj]
  -- ⊢ Functor.PreservesEpimorphisms (coyoneda.obj (op (op J))) ↔ Functor.Preserves …
  exact Functor.preservesEpimorphisms.iso_iff (Coyoneda.objOpOp _)
  -- 🎉 no goals
#align category_theory.injective.injective_iff_preserves_epimorphisms_yoneda_obj CategoryTheory.Injective.injective_iff_preservesEpimorphisms_yoneda_obj

section Adjunction

open CategoryTheory.Functor

variable {D : Type u₂} [Category.{v₂} D]

variable {L : C ⥤ D} {R : D ⥤ C} [PreservesMonomorphisms L]

theorem injective_of_adjoint (adj : L ⊣ R) (J : D) [Injective J] : Injective <| R.obj J :=
  ⟨fun {A} {_} g f im =>
    ⟨adj.homEquiv _ _ (factorThru ((adj.homEquiv A J).symm g) (L.map f)),
      (adj.homEquiv _ _).symm.injective (by simp)⟩⟩
                                            -- 🎉 no goals
#align category_theory.injective.injective_of_adjoint CategoryTheory.Injective.injective_of_adjoint

end Adjunction

section EnoughInjectives

variable [EnoughInjectives C]

/-- `Injective.under X` provides an arbitrarily chosen injective object equipped with
a monomorphism `Injective.ι : X ⟶ Injective.under X`.
-/
def under (X : C) : C :=
  (EnoughInjectives.presentation X).some.J
#align category_theory.injective.under CategoryTheory.Injective.under

instance injective_under (X : C) : Injective (under X) :=
  (EnoughInjectives.presentation X).some.injective
#align category_theory.injective.injective_under CategoryTheory.Injective.injective_under

/-- The monomorphism `Injective.ι : X ⟶ Injective.under X`
from the arbitrarily chosen injective object under `X`.
-/
def ι (X : C) : X ⟶ under X :=
  (EnoughInjectives.presentation X).some.f
#align category_theory.injective.ι CategoryTheory.Injective.ι

instance ι_mono (X : C) : Mono (ι X) :=
  (EnoughInjectives.presentation X).some.mono
#align category_theory.injective.ι_mono CategoryTheory.Injective.ι_mono

section

variable [HasZeroMorphisms C] {X Y : C} (f : X ⟶ Y) [HasCokernel f]

/-- When `C` has enough injectives, the object `Injective.syzygies f` is
an arbitrarily chosen injective object under `cokernel f`.
-/
def syzygies : C :=
  under (cokernel f) -- Porting note: no deriving Injective
#align category_theory.injective.syzygies CategoryTheory.Injective.syzygies

instance : Injective <| syzygies f := injective_under (cokernel f)

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
  ⟨fun X => ⟨{ p := _, f := (Injective.ι (unop X)).op}⟩⟩

instance [EnoughProjectives C] : EnoughInjectives Cᵒᵖ :=
  ⟨fun X => ⟨⟨_, inferInstance, (Projective.π (unop X)).op, inferInstance⟩⟩⟩

theorem enoughProjectives_of_enoughInjectives_op [EnoughInjectives Cᵒᵖ] : EnoughProjectives C :=
  ⟨fun X => ⟨{ p := _, f := (Injective.ι (op X)).unop} ⟩⟩
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
  convert congr_arg Quiver.Hom.unop (Exact.lift_comp h.op g.op f.op hgf (congrArg Quiver.Hom.op w))
  -- 🎉 no goals
#align category_theory.injective.exact.comp_desc CategoryTheory.Injective.Exact.comp_desc

end

end Injective

namespace Adjunction

variable {D : Type*} [Category D] {F : C ⥤ D} {G : D ⥤ C}

theorem map_injective (adj : F ⊣ G) [F.PreservesMonomorphisms] (I : D) (hI : Injective I) :
    Injective (G.obj I) :=
  ⟨fun {X} {Y} f g => by
    intro
    -- ⊢ ∃ h, g ≫ h = f
    rcases hI.factors (F.map f ≫ adj.counit.app _) (F.map g) with ⟨w,h⟩
    -- ⊢ ∃ h, g ≫ h = f
    use adj.unit.app Y ≫ G.map w
    -- ⊢ g ≫ NatTrans.app adj.unit Y ≫ G.map w = f
    rw [← unit_naturality_assoc, ← G.map_comp, h]
    -- ⊢ NatTrans.app adj.unit X ≫ G.map (F.map f ≫ NatTrans.app adj.counit I) = f
    simp⟩
    -- 🎉 no goals
#align category_theory.adjunction.map_injective CategoryTheory.Adjunction.map_injective

theorem injective_of_map_injective (adj : F ⊣ G) [Full G] [Faithful G] (I : D)
    (hI : Injective (G.obj I)) : Injective I :=
  ⟨fun {X} {Y} f g => by
    intro
    -- ⊢ ∃ h, g ≫ h = f
    haveI : PreservesLimitsOfSize.{0, 0} G := adj.rightAdjointPreservesLimits
    -- ⊢ ∃ h, g ≫ h = f
    rcases hI.factors (G.map f) (G.map g) with ⟨w,h⟩
    -- ⊢ ∃ h, g ≫ h = f
    use inv (adj.counit.app _) ≫ F.map w ≫ adj.counit.app _
    -- ⊢ g ≫ inv (NatTrans.app adj.counit Y) ≫ F.map w ≫ NatTrans.app adj.counit I = f
    refine' Faithful.map_injective (F := G) _
    -- ⊢ G.map (g ≫ inv (NatTrans.app adj.counit Y) ≫ F.map w ≫ NatTrans.app adj.coun …
    simpa⟩
    -- 🎉 no goals
#align category_theory.adjunction.injective_of_map_injective CategoryTheory.Adjunction.injective_of_map_injective

/-- Given an adjunction `F ⊣ G` such that `F` preserves monos, `G` maps an injective presentation
of `X` to an injective presentation of `G(X)`. -/
def mapInjectivePresentation (adj : F ⊣ G) [F.PreservesMonomorphisms] (X : D)
    (I : InjectivePresentation X) : InjectivePresentation (G.obj X) where
  J := G.obj I.J
  injective := adj.map_injective _ I.injective
  f := G.map I.f
  mono := by
    haveI : PreservesLimitsOfSize.{0, 0} G := adj.rightAdjointPreservesLimits; infer_instance
    -- ⊢ Mono (G.map I.f)
                                                                               -- 🎉 no goals
#align category_theory.adjunction.map_injective_presentation CategoryTheory.Adjunction.mapInjectivePresentation

end Adjunction

namespace Equivalence

variable {D : Type*} [Category D] (F : C ≌ D)

/-- Given an equivalence of categories `F`, an injective presentation of `F(X)` induces an
injective presentation of `X.` -/
def injectivePresentationOfMapInjectivePresentation (X : C)
    (I : InjectivePresentation (F.functor.obj X)) : InjectivePresentation X where
  J := F.inverse.obj I.J
  injective := Adjunction.map_injective F.toAdjunction I.J I.injective
  f := F.unit.app _ ≫ F.inverse.map I.f
  mono := mono_comp _ _
#align category_theory.equivalence.injective_presentation_of_map_injective_presentation CategoryTheory.Equivalence.injectivePresentationOfMapInjectivePresentation

theorem enoughInjectives_iff (F : C ≌ D) : EnoughInjectives C ↔ EnoughInjectives D := by
  constructor
  -- ⊢ EnoughInjectives C → EnoughInjectives D
  all_goals intro H; constructor; intro X; constructor
  -- ⊢ InjectivePresentation X
  · exact
      F.symm.injectivePresentationOfMapInjectivePresentation _
        (Nonempty.some (H.presentation (F.inverse.obj X)))
  · exact
      F.injectivePresentationOfMapInjectivePresentation X
        (Nonempty.some (H.presentation (F.functor.obj X)))
#align category_theory.equivalence.enough_injectives_iff CategoryTheory.Equivalence.enoughInjectives_iff

end Equivalence

end CategoryTheory
