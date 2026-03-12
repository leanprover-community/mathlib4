/-
Copyright (c) 2026 Benoît Guillemet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benoît Guillemet, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!

# Equivalence relations

We define internal equivalence relations (sometimes called congruences) in any category `C`, as a
structure on pairs of parallel morphisms `p₁, p₂ : R ⟶ X` .
We also define effective and universally effective equivalence relations.

We prove that equivalence relations on types provide internal equivalence relation structures in the
category of types.
In general, kernel pairs in any category are internal equivalence relations.

## References

* <https://ncatlab.org/nlab/show/congruence>

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {D : Type*} [Category D]
variable {R X : C} {p₁ p₂ : R ⟶ X}

/-- A typeclass for pairs of morphisms that are jointly monic. -/
class JointlyMono₂ {R X₁ X₂ : C} (p₁ : R ⟶ X₁) (p₂ : R ⟶ X₂) where
  right_cancellation : ∀ ⦃Y : C⦄ (f g : Y ⟶ R), f ≫ p₁ = g ≫ p₁ → f ≫ p₂ = g ≫ p₂ → f = g

/-- A reflexive relation is a jointly monic pair of parallel morphisms `p₁, p₂ : R ⟶ X`, together
with a section `r : X ⟶ R` of both `p₁` and `p₂`. -/
structure ReflexiveRelation {R X : C} (p₁ p₂ : R ⟶ X) extends JointlyMono₂ p₁ p₂ where
  /-- `r` is the morphism witnessing reflexivity -/
  r : X ⟶ R
  reflexivity₁ : r ≫ p₁ = 𝟙 _ := by cat_disch
  reflexivity₂ : r ≫ p₂ = 𝟙 _ := by cat_disch

attribute [reassoc (attr := simp)] ReflexiveRelation.reflexivity₁ ReflexiveRelation.reflexivity₂

/-- A symmetric relation is a jointly monic pair of parallel morphisms `p₁, p₂ : R ⟶ X` together
with a morphism `s : R ⟶ R` which interchanges `p₁` and `p₂`. -/
structure SymmetricRelation {R X : C} (p₁ p₂ : R ⟶ X) extends JointlyMono₂ p₁ p₂ where
  /-- `s` is the morphism witnessing symmetry -/
  s : R ⟶ R
  symmetry₁ : s ≫ p₁ = p₂ := by cat_disch
  symmetry₂ : s ≫ p₂ = p₁ := by cat_disch

attribute [reassoc (attr := simp)] SymmetricRelation.symmetry₁ SymmetricRelation.symmetry₂

/-- A transitive relation is a jointly monic pair of parallel morphisms `p₁, p₂ : R ⟶ X`, together
with a limiting pullback cone `c` for `p₁` and `p₂` and a map `c.pt ⟶ R` which factors the two
projections `c.pt ⟶ X` through `R`. -/
structure TransitiveRelation {R X : C} (p₁ p₂ : R ⟶ X) extends JointlyMono₂ p₁ p₂ where
  /-- `c` is a pullback cone for `p₁` and `p₂` -/
  c : PullbackCone p₂ p₁
  /-- `c` is limiting -/
  isLimit : IsLimit c
  /-- `t` is the morphism witnessing transitivity -/
  t : c.pt ⟶ R
  transitivity₁ : t ≫ p₁ = c.fst ≫ p₁ := by cat_disch
  transitivity₂ : t ≫ p₂ = c.snd ≫ p₂ := by cat_disch

attribute [reassoc (attr := simp)] TransitiveRelation.transitivity₁ TransitiveRelation.transitivity₂

/-- An equivalence relation is a reflexive, symmetric and transitive relation. -/
structure EquivalenceRelation {R X : C} (p₁ p₂ : R ⟶ X) extends ReflexiveRelation p₁ p₂,
    SymmetricRelation p₁ p₂, TransitiveRelation p₁ p₂

/-- The typeclass associated with the structure `EquivalenceRelation`. -/
class IsEquivalenceRelation {R X : C} (p₁ p₂ : R ⟶ X) : Prop where
  nonempty_equivalenceRelation : Nonempty (EquivalenceRelation p₁ p₂)

lemma EquivalenceRelation.isEquivalenceRelation (h : EquivalenceRelation p₁ p₂) :
    IsEquivalenceRelation p₁ p₂ where
  nonempty_equivalenceRelation := ⟨h⟩

/-- A kernel pair gives rise to an equivalence relation. -/
noncomputable def IsKernelPair.equivalenceRelation {X Y : C} (f : X ⟶ Y) {R : C} (p₁ p₂ : R ⟶ X)
    [HasPullback p₂ p₁] (h : IsKernelPair f p₁ p₂) :
    EquivalenceRelation p₁ p₂ where
  right_cancellation A a b h₁ h₂ := h.hom_ext h₁ h₂
  r := h.lift (𝟙 _) (𝟙 _) (by simp)
  s := h.lift p₂ p₁ h.w.symm
  c := PullbackCone.mk (pullback.fst p₂ p₁) _ pullback.condition
  isLimit := pullbackIsPullback _ _
  t := h.lift (pullback.fst _ _ ≫ p₁) (pullback.snd _ _ ≫ p₂)
    (by simp [h.w, pullback.condition_assoc])

/-- Equivalences relations on types are internal equivalence relations in the category of types. -/
def Types.equivalenceRelation {X : Type*} {r : X → X → Prop} (hr : _root_.Equivalence r) :
    EquivalenceRelation (R := Subtype r.uncurry) (_root_.Prod.fst ∘ Subtype.val)
      (_root_.Prod.snd ∘ Subtype.val) where
  r x := ⟨⟨x, x⟩, hr.refl x⟩
  s p := ⟨(p.1.2, p.1.1), hr.symm p.2⟩
  c := Types.pullbackCone _ _
  isLimit := (Types.pullbackLimitCone _ _).isLimit
  t p := ⟨(p.1.1.1.1, p.1.2.1.2), hr.trans p.1.1.2 (by
    have := p.1.2.2
    dsimp [Function.uncurry] at this
    convert this using 1
    exact p.2)⟩
  right_cancellation Y f g h₁ h₂ := by
    ext y
    · exact congr($h₁ y)
    · exact congr($h₂ y)

/-- Given a functor `F : C ⥤ D`, if `F.map p₁` and `F.map p₂` form a jointly monic pair of
morphisms, then `F` preserves reflexive relations. -/
def ReflexiveRelation.map (e : ReflexiveRelation p₁ p₂) (F : C ⥤ D)
    [JointlyMono₂ (F.map p₁) (F.map p₂)] :
    ReflexiveRelation (F.map p₁) (F.map p₂) where
  r := F.map e.r
  reflexivity₁ := by simp [← F.map_comp]
  reflexivity₂ := by simp [← F.map_comp]

/-- Given a functor `F : C ⥤ D`, if `F.map p₁` and `F.map p₂` form a jointly monic pair of
morphisms, then `F` preserves symmetric relations. -/
def SymmetricRelation.map (e : SymmetricRelation p₁ p₂) (F : C ⥤ D)
    [JointlyMono₂ (F.map p₁) (F.map p₂)] :
    SymmetricRelation (F.map p₁) (F.map p₂) where
  s := F.map e.s
  symmetry₁ := by simp [← F.map_comp]
  symmetry₂ := by simp [← F.map_comp]

/-- Given a functor `F : C ⥤ D`, if `F.map p₁` and `F.map p₂` form a jointly monic pair of
morphisms, and if `F` preserves pullbacks, then `F` preserves reflexive relations. -/
noncomputable def TransitiveRelation.map (e : TransitiveRelation p₁ p₂) (F : C ⥤ D)
    [JointlyMono₂ (F.map p₁) (F.map p₂)] [PreservesLimitsOfShape WalkingCospan F] :
    TransitiveRelation (F.map p₁) (F.map p₂) where
  t := F.map e.t
  c := e.c.map F
  isLimit := isLimitPullbackConeMapOfIsLimit F e.c.condition (.ofIsoLimit e.isLimit e.c.eta)
  transitivity₁ := by
    dsimp
    rw [← F.map_comp, ← F.map_comp, transitivity₁]
  transitivity₂ := by
    dsimp
    rw [← F.map_comp, ← F.map_comp, transitivity₂]

section Effective

/-- An effective equivalence relation is an equivalence relation `p₁, p₂ : R ⟶ A` together with a
morphism `π : A ⟶ B` such that the resulting square is both a pullback square and a pushout
square. -/
structure EffectiveEquivalenceRelation {R A : C} (p₁ p₂ : R ⟶ A) extends EquivalenceRelation p₁ p₂
    where
  /-- `B` is the "quotient" of the relation -/
  B : C
  /-- `π` is the "quotient map" of the relation -/
  π : A ⟶ B
  isKernelPair : IsKernelPair π p₁ p₂
  isPushout : IsPushout p₁ p₂ π π

/-- The typeclass associated with the structure `EffectiveEquivalenceRelation`. -/
class IsEffectiveEquivalenceRelation {R A : C} (p₁ p₂ : R ⟶ A) : Prop where
  nonempty_effectiveEquivalenceRelation : Nonempty (EffectiveEquivalenceRelation p₁ p₂)

/-- Given an effective equivalence relation structure `e` on `p₁, p₂ : R ⟶ A`, the morphism
`e.π : A ⟶ e.B` makes `e.B` a coequalizer of `p₁` and `p₂`. -/
noncomputable def EffectiveEquivalenceRelation.isCoequalizer {R A : C} (p₁ p₂ : R ⟶ A)
    (e : EffectiveEquivalenceRelation p₁ p₂) :
    IsColimit (Cofork.ofπ e.π e.isPushout.w) :=
  e.isPushout.isLimitFork

instance {R A : C} (p₁ p₂ : R ⟶ A) (e : EffectiveEquivalenceRelation p₁ p₂) :
    IsRegularEpi e.π :=
  ⟨⟨Cofork.IsColimit.regularEpi e.isCoequalizer⟩⟩

/-- A universally effective equivalence relation is an effective equivalence relation
`p₁, p₂ : R ⟶ A` such that the corresponding morphism `π : A ⟶ B` is a universal effective
epimorphism. -/
structure UniversallyEffectiveEquivalenceRelation {R A : C} (p₁ p₂ : R ⟶ A)
    extends EffectiveEquivalenceRelation p₁ p₂ where
  universally_effectiveEpi_π : MorphismProperty.universally (fun _ _ f => EffectiveEpi f)
    (toEffectiveEquivalenceRelation.π)

/-- The typeclass associated with the structure `UniversallyEffectiveEquivalenceRelation`. -/
class IsUniversallyEffectiveEquivalenceRelation {R A : C} (p₁ p₂ : R ⟶ A) : Prop where
  nonempty_universallyEffectiveEquivalenceRelation :
    Nonempty (UniversallyEffectiveEquivalenceRelation p₁ p₂)

variable (C) in
/-- A category `C` is a universally effective equivalence relation category if all equivalence
relations in `C` are universally effective equivalence relations. -/
class IsUniversallyEffectiveEquivalenceRelationCategory where
  isUniversallyEffectiveEquivalenceRelation {R A : C} (p₁ p₂ : R ⟶ A)
    [IsEquivalenceRelation p₁ p₂] : IsUniversallyEffectiveEquivalenceRelation p₁ p₂

end Effective

end CategoryTheory
