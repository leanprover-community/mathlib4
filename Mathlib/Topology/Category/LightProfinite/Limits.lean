/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Topology.Category.LightProfinite.IsLight
import Mathlib.Topology.Category.Profinite.Limits
/-!

# Explicit limits and colimits

This file collects some constructions of explicit limits and colimits in `LightProfinite`,
which may be useful due to their definitional properties.

## Main definitions

* `LightProfinite.pullback`: Explicit pullback, defined in the "usual" way as a subset of the
  product.

* `LightProfinite.finiteCoproduct`: Explicit finite coproducts, defined as a disjoint union.

-/

universe u w

/-
Previously, this had accidentally been made a global instance,
and we now turn it on locally when convenient.
-/
attribute [local instance] CategoryTheory.ConcreteCategory.instFunLike

open CategoryTheory Profinite TopologicalSpace Limits

namespace LightProfinite

section Pullback

instance {X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B) [X.IsLight] [Y.IsLight] :
    (Profinite.pullback f g).IsLight := by
  let i : Profinite.pullback f g ⟶ Profinite.of (X × Y) := ⟨fun x ↦ x.val, continuous_induced_dom⟩
  have : Mono i := by
    rw [Profinite.mono_iff_injective]
    exact Subtype.val_injective
  exact isLight_of_mono i

variable {X Y B : LightProfinite.{u}} (f : X ⟶ B) (g : Y ⟶ B)

/--
The "explicit" pullback of two morphisms `f, g` in `LightProfinite`, whose underlying profinite set
is the set of pairs `(x, y)` such that `f x = g y`, with the topology induced by the product.
-/
noncomputable def pullback : LightProfinite.{u} :=
  ofIsLight (Profinite.pullback (lightToProfinite.map f) (lightToProfinite.map g))

/-- The projection from the pullback to the first component. -/
def pullback.fst : pullback f g ⟶ X where
  toFun := fun ⟨⟨x, _⟩, _⟩ ↦ x
  continuous_toFun := Continuous.comp continuous_fst continuous_subtype_val

/-- The projection from the pullback to the second component. -/
def pullback.snd : pullback f g ⟶ Y where
  toFun := fun ⟨⟨_, y⟩, _⟩ ↦ y
  continuous_toFun := Continuous.comp continuous_snd continuous_subtype_val

@[reassoc]
lemma pullback.condition : pullback.fst f g ≫ f = pullback.snd f g ≫ g := by
  ext ⟨_, h⟩
  exact h

/--
Construct a morphism to the explicit pullback given morphisms to the factors
which are compatible with the maps to the base.
This is essentially the universal property of the pullback.
-/
def pullback.lift {Z : LightProfinite.{u}} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g) :
    Z ⟶ pullback f g where
  toFun := fun z ↦ ⟨⟨a z, b z⟩, by apply_fun (· z) at w; exact w⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    rw [continuous_prod_mk]
    exact ⟨a.continuous, b.continuous⟩

@[reassoc (attr := simp)]
lemma pullback.lift_fst {Z : LightProfinite.{u}} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g) :
    pullback.lift f g a b w ≫ pullback.fst f g = a := rfl

@[reassoc (attr := simp)]
lemma pullback.lift_snd {Z : LightProfinite.{u}} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g) :
    pullback.lift f g a b w ≫ pullback.snd f g = b := rfl

lemma pullback.hom_ext {Z : LightProfinite.{u}} (a b : Z ⟶ pullback f g)
    (hfst : a ≫ pullback.fst f g = b ≫ pullback.fst f g)
    (hsnd : a ≫ pullback.snd f g = b ≫ pullback.snd f g) : a = b := by
  ext z
  apply_fun (· z) at hfst hsnd
  apply Subtype.ext
  apply Prod.ext
  · exact hfst
  · exact hsnd

/-- The pullback cone whose cone point is the explicit pullback. -/
@[simps! pt π]
noncomputable def pullback.cone : Limits.PullbackCone f g :=
  Limits.PullbackCone.mk (pullback.fst f g) (pullback.snd f g) (pullback.condition f g)

/-- The explicit pullback cone is a limit cone. -/
@[simps! lift]
def pullback.isLimit : Limits.IsLimit (pullback.cone f g) :=
  Limits.PullbackCone.isLimitAux _
    (fun s ↦ pullback.lift f g s.fst s.snd s.condition)
    (fun _ ↦ pullback.lift_fst _ _ _ _ _)
    (fun _ ↦ pullback.lift_snd _ _ _ _ _)
    (fun _ _ hm ↦ pullback.hom_ext _ _ _ _ (hm .left) (hm .right))

end Pullback

section FiniteCoproduct

instance {α : Type w} [Finite α] (X : α → Profinite.{max u w}) [∀ a, (X a).IsLight] :
    (Profinite.finiteCoproduct X).IsLight where
  countable_clopens := by
    refine @Function.Surjective.countable ((a : α) → Clopens (X a)) _ inferInstance
      (fun f ↦ ⟨⋃ (a : α), Sigma.mk a '' (f a).1, ?_⟩) ?_
    · apply isClopen_iUnion_of_finite
      intro i
      exact ⟨isClosedMap_sigmaMk _ (f i).2.1, isOpenMap_sigmaMk _ (f i).2.2⟩
    · intro ⟨s, ⟨hsc, hso⟩⟩
      rw [isOpen_sigma_iff] at hso
      rw [isClosed_sigma_iff] at hsc
      refine ⟨fun i ↦ ⟨_, ⟨hsc i, hso i⟩⟩, ?_⟩
      simp only [Subtype.mk.injEq]
      ext ⟨i, xi⟩
      refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
      · simp only [Clopens.coe_mk, Set.mem_iUnion] at hx
        obtain ⟨_, _, hj, hxj⟩ := hx
        simpa [hxj] using hj
      · simp only [Clopens.coe_mk, Set.mem_iUnion]
        refine ⟨i, xi, (by simpa using hx), rfl⟩

variable {α : Type w} [Finite α] (X : α → LightProfinite.{max u w})

/--
The "explicit" coproduct of a finite family of objects in `LightProfinite`, whose underlying
profinite set is the disjoint union with its usual topology.
-/
noncomputable
def finiteCoproduct : LightProfinite :=
  ofIsLight (Profinite.finiteCoproduct.{u, w} fun a ↦ (X a).toProfinite)

/-- The inclusion of one of the factors into the explicit finite coproduct. -/
def finiteCoproduct.ι (a : α) : X a ⟶ finiteCoproduct X where
  toFun := (⟨a, ·⟩)
  continuous_toFun := continuous_sigmaMk (σ := fun a ↦ (X a).toProfinite)

/--
To construct a morphism from the explicit finite coproduct, it suffices to
specify a morphism from each of its factors. This is the universal property of the coproduct.
-/
def finiteCoproduct.desc {B : LightProfinite.{max u w}} (e : (a : α) → (X a ⟶ B)) :
    finiteCoproduct X ⟶ B where
  toFun := fun ⟨a, x⟩ ↦ e a x
  continuous_toFun := by
    apply continuous_sigma
    intro a
    exact (e a).continuous

@[reassoc (attr := simp)]
lemma finiteCoproduct.ι_desc {B : LightProfinite.{max u w}} (e : (a : α) → (X a ⟶ B)) (a : α) :
    finiteCoproduct.ι X a ≫ finiteCoproduct.desc X e = e a := rfl

lemma finiteCoproduct.hom_ext {B : LightProfinite.{max u w}} (f g : finiteCoproduct X ⟶ B)
    (h : ∀ a : α, finiteCoproduct.ι X a ≫ f = finiteCoproduct.ι X a ≫ g) : f = g := by
  ext ⟨a, x⟩
  specialize h a
  apply_fun (· x) at h
  exact h

/-- The coproduct cocone associated to the explicit finite coproduct. -/
noncomputable abbrev finiteCoproduct.cofan : Limits.Cofan X :=
  Cofan.mk (finiteCoproduct X) (finiteCoproduct.ι X)

/-- The explicit finite coproduct cocone is a colimit cocone. -/
def finiteCoproduct.isColimit : Limits.IsColimit (finiteCoproduct.cofan X) :=
  mkCofanColimit _
    (fun s ↦ desc _ fun a ↦ s.inj a)
    (fun s a ↦ ι_desc _ _ _)
    fun s m hm ↦ finiteCoproduct.hom_ext _ _ _ fun a ↦
      (by ext t; exact congrFun (congrArg DFunLike.coe (hm a)) t)

end FiniteCoproduct

section HasPreserves

instance (n : ℕ) (F : Discrete (Fin n) ⥤ LightProfinite) :
    HasColimit (Discrete.functor (F.obj ∘ Discrete.mk) : Discrete (Fin n) ⥤ LightProfinite) where
  exists_colimit := ⟨⟨finiteCoproduct.cofan _, finiteCoproduct.isColimit _⟩⟩

instance : HasFiniteCoproducts LightProfinite where
  out _ := { has_colimit := fun _ ↦ hasColimitOfIso Discrete.natIsoFunctor }

instance {X Y B : LightProfinite} (f : X ⟶ B) (g : Y ⟶ B) : HasLimit (cospan f g) where
  exists_limit := ⟨⟨pullback.cone f g, pullback.isLimit f g⟩⟩

instance : HasPullbacks LightProfinite where
  has_limit F := hasLimitOfIso (diagramIsoCospan F).symm

noncomputable
instance : PreservesFiniteCoproducts lightToProfinite := by
  refine ⟨fun J hJ ↦ ⟨fun {F} ↦ ?_⟩⟩
  suffices PreservesColimit (Discrete.functor (F.obj ∘ Discrete.mk)) lightToProfinite by
    exact preservesColimitOfIsoDiagram _ Discrete.natIsoFunctor.symm
  apply preservesColimitOfPreservesColimitCocone (finiteCoproduct.isColimit _)
  exact Profinite.finiteCoproduct.isColimit _

noncomputable
instance : PreservesLimitsOfShape WalkingCospan lightToProfinite := by
  suffices ∀ {X Y B} (f : X ⟶ B) (g : Y ⟶ B), PreservesLimit (cospan f g) lightToProfinite from
    ⟨fun {F} ↦ preservesLimitOfIsoDiagram _ (diagramIsoCospan F).symm⟩
  intro _ _ _ f g
  apply preservesLimitOfPreservesLimitCone (pullback.isLimit f g)
  exact (isLimitMapConePullbackConeEquiv lightToProfinite (pullback.condition f g)).symm
    (Profinite.pullback.isLimit _ _)

instance (X : LightProfinite) : Unique (X ⟶ (FintypeCat.of PUnit.{u+1}).toLightProfinite) :=
  ⟨⟨⟨fun _ ↦ PUnit.unit, continuous_const⟩⟩, fun _ ↦ rfl⟩

/-- A one-element space is terminal in `LightProfinite` -/
def isTerminalPUnit : IsTerminal ((FintypeCat.of PUnit.{u+1}).toLightProfinite) :=
  Limits.IsTerminal.ofUnique _

instance : HasTerminal LightProfinite.{u} :=
  Limits.hasTerminal_of_unique (FintypeCat.of PUnit.{u+1}).toLightProfinite

/-- The isomorphism from an arbitrary terminal object of `LightProfinite` to a one-element space. -/
noncomputable def terminalIsoPUnit :
    ⊤_ LightProfinite.{u} ≅ (FintypeCat.of PUnit.{u+1}).toLightProfinite :=
  terminalIsTerminal.uniqueUpToIso LightProfinite.isTerminalPUnit

noncomputable instance : PreservesFiniteCoproducts LightProfinite.toTopCat.{u} where
  preserves _ _ := (inferInstance :
    PreservesColimitsOfShape _ (LightProfinite.lightToProfinite.{u} ⋙ Profinite.toTopCat.{u}))

noncomputable instance : PreservesLimitsOfShape WalkingCospan LightProfinite.toTopCat.{u} :=
  (inferInstance : PreservesLimitsOfShape WalkingCospan
    (LightProfinite.lightToProfinite.{u} ⋙ Profinite.toTopCat.{u}))

end HasPreserves

end LightProfinite
