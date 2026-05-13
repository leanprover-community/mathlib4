/-
Copyright (c) 2026 Benoît Guillemet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benoît Guillemet, Christian Merten
-/
module

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

universe w

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] {D : Type*} [Category* D]
variable {R X : C} {p₁ p₂ : R ⟶ X}

/-- A typeclass for pairs of morphisms that are jointly monic. -/
class JointlyMono₂ {R X₁ X₂ : C} (p₁ : R ⟶ X₁) (p₂ : R ⟶ X₂) : Prop where
  right_cancellation : ∀ ⦃Y : C⦄ (f g : Y ⟶ R), f ≫ p₁ = g ≫ p₁ → f ≫ p₂ = g ≫ p₂ → f = g

/-- A reflexive relation is a jointly monic pair of parallel morphisms `p₁, p₂ : R ⟶ X`, together
with a section `r : X ⟶ R` of both `p₁` and `p₂`. -/
structure ReflexiveRelation {R X : C} (p₁ p₂ : R ⟶ X) extends JointlyMono₂ p₁ p₂ where
  /-- `r` is the morphism witnessing reflexivity -/
  r : X ⟶ R
  reflexivity₁ : r ≫ p₁ = 𝟙 _ := by cat_disch
  reflexivity₂ : r ≫ p₂ = 𝟙 _ := by cat_disch

attribute [reassoc (attr := simp), elementwise (attr := simp)]
  ReflexiveRelation.reflexivity₁ ReflexiveRelation.reflexivity₂

/-- A symmetric relation is a jointly monic pair of parallel morphisms `p₁, p₂ : R ⟶ X` together
with a morphism `s : R ⟶ R` which interchanges `p₁` and `p₂`. -/
structure SymmetricRelation {R X : C} (p₁ p₂ : R ⟶ X) extends JointlyMono₂ p₁ p₂ where
  /-- `s` is the morphism witnessing symmetry -/
  s : R ⟶ R
  symmetry₁ : s ≫ p₁ = p₂ := by cat_disch
  symmetry₂ : s ≫ p₂ = p₁ := by cat_disch

attribute [reassoc (attr := simp), elementwise (attr := simp)]
  SymmetricRelation.symmetry₁ SymmetricRelation.symmetry₂

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

initialize_simps_projections TransitiveRelation (-isLimit)

attribute [reassoc (attr := simp), elementwise (attr := simp)]
  TransitiveRelation.transitivity₁ TransitiveRelation.transitivity₂

/-- An equivalence relation is a reflexive, symmetric and transitive relation. -/
structure EquivalenceRelation {R X : C} (p₁ p₂ : R ⟶ X) extends ReflexiveRelation p₁ p₂,
  SymmetricRelation p₁ p₂, TransitiveRelation p₁ p₂

/-- Reinterpret an equivalence relation as a reflexive relation. -/
add_decl_doc EquivalenceRelation.toReflexiveRelation

/-- Reinterpret an equivalence relation as a symmetric relation. -/
add_decl_doc EquivalenceRelation.toSymmetricRelation

/-- Reinterpret an equivalence relation as a transitive relation. -/
add_decl_doc EquivalenceRelation.toTransitiveRelation

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
  transitivity₁ := by simp [← Functor.map_comp]
  transitivity₂ := by simp [← Functor.map_comp]

end CategoryTheory

namespace TypeCat

open CategoryTheory Limits

variable {X : Type w} (φ : X → X → Prop)

abbrev ROfRel := Subtype φ.uncurry
abbrev p₁OfRel : ROfRel φ ⟶ X := ↾(Prod.fst ∘ Subtype.val)
abbrev p₂OfRel : ROfRel φ ⟶ X := ↾(Prod.snd ∘ Subtype.val)

lemma jointlyMono₂ :
    JointlyMono₂ (p₁OfRel φ) (p₂OfRel φ) where
  right_cancellation Y f g h₁ h₂ := by
    ext y
    · exact congr($h₁ y)
    · exact congr($h₂ y)

/-- Standard reflexive relations on types are internal reflexive relations in the category of
types. -/
def ReflexiveRelation.ofRefl {X : Type w} {φ : X → X → Prop} (hφ : Std.Refl φ) :
    ReflexiveRelation (p₁OfRel φ) (p₂OfRel φ) where
  __ := jointlyMono₂ φ
  r := (↾(fun x => ⟨⟨x, x⟩, hφ.refl x⟩))

/-- Standard symmetric relations on types are internal symmetric relations in the category of
types. -/
def SymmetricRelation.ofSymmetric {X : Type w} {φ : X → X → Prop} (hφ : Symmetric φ) :
    SymmetricRelation (p₁OfRel φ) (p₂OfRel φ) where
  __ := jointlyMono₂ φ
  s := ↾(fun ⟨⟨x₁, x₂⟩, h⟩ => ⟨⟨x₂, x₁⟩, hφ h⟩)

/-- Standard transitive relations on types are internal transitive relations in the category of
types. -/
def TransitiveRelation.ofIsTrans {X : Type w} {φ : X → X → Prop} (hφ : IsTrans _ φ) :
    TransitiveRelation (p₁OfRel φ) (p₂OfRel φ) where
  __ := jointlyMono₂ φ
  c := Types.pullbackCone _ _
  isLimit := (Types.pullbackLimitCone _ _).isLimit
  t := ↾(fun ⟨⟨⟨⟨x₁, _⟩, h⟩, ⟨⟨_, x₂'⟩, h'⟩⟩, h₁₂⟩ => by
    dsimp at h₁₂
    rw [← h₁₂] at h'
    refine ⟨⟨x₁, x₂'⟩, hφ.trans _ _ _ h h'⟩)

/-- Standard equivalence relations on types are internal equivalence relations in the category of
types. -/
def EquivalenceRelation.ofEquivalence {X : Type w} {φ : X → X → Prop} (hφ : Equivalence φ) :
    EquivalenceRelation (p₁OfRel φ) (p₂OfRel φ) where
  __ := ReflexiveRelation.ofRefl hφ.stdRefl
  __ := SymmetricRelation.ofSymmetric hφ.symmetric
  __ := TransitiveRelation.ofIsTrans hφ.isTrans

variable {R : Type w} (p₁ p₂ : R ⟶ X)

abbrev Rel.ofPair := fun x₁ x₂ => ∃ r : R, p₁ r = x₁ ∧ p₂ r = x₂

variable {p₁ p₂}

/-- An internal reflexive relation in the category of types gives rise to a standard reflexive
relation. -/
lemma of_reflexiveRelation (e : ReflexiveRelation p₁ p₂) :
    Std.Refl (Rel.ofPair p₁ p₂) where
  refl x := ⟨e.r x, congr($e.reflexivity₁ x), by simp⟩

/-- An internal symmetric relation in the category of types gives rise to a standard symmetric
relation. -/
lemma of_symmetricRelation (e : SymmetricRelation p₁ p₂) :
    Symmetric (Rel.ofPair p₁ p₂) := by
  refine fun x₁ x₂ ⟨r, hr₁, hr₂⟩ => ⟨e.s r, ?_, ?_⟩
  all_goals simpa

/-- An internal transitive relation in the category of types gives rise to a standard transitive
relation. -/
lemma of_transitiveRelation (e : TransitiveRelation p₁ p₂) :
    IsTrans _ (Rel.ofPair p₁ p₂) where
  trans x₁ x₂ x₃ := by
    refine fun ⟨r, ⟨hr₁, hr₂⟩⟩ ⟨r', ⟨hr₁', hr₂'⟩⟩ =>
      ⟨e.t ((PullbackCone.IsLimit.equivPullbackObj e.isLimit).symm ⟨(r, r'), hr₂.trans hr₁'.symm⟩),
        ⟨?_, ?_⟩⟩
    all_goals simpa

/-- An internal equivalence relation in the category of types gives rise to a standard equivalence
relation. -/
lemma of_equivalenceRelation (e : EquivalenceRelation p₁ p₂) :
    Equivalence (Rel.ofPair p₁ p₂) where
  refl := (of_reflexiveRelation e.toReflexiveRelation).refl
  symm h := of_symmetricRelation e.toSymmetricRelation h
  trans := (of_transitiveRelation e.toTransitiveRelation).trans _ _ _

end TypeCat

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C]
variable {R A : C} (p₁ p₂ : R ⟶ A)

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

instance (e : EffectiveEquivalenceRelation p₁ p₂) :
    IsRegularEpi e.π where
  regularEpi := ⟨Cofork.IsColimit.regularEpi e.isCoequalizer⟩

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
/-- A category `C` is a universally exact category if all equivalence relations in `C` are
universally effective equivalence relations. -/
class IsUniversallyEffectiveEquivalenceRelationCategory where
  isUniversallyEffectiveEquivalenceRelation {R A : C} (p₁ p₂ : R ⟶ A)
    [IsEquivalenceRelation p₁ p₂] : IsUniversallyEffectiveEquivalenceRelation p₁ p₂

end Effective

end CategoryTheory
