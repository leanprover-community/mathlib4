/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kim Morrison
-/
import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
import Mathlib.CategoryTheory.Limits.Constructions.Equalizers
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Creates.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma

/-!
# Constructing limits from products and equalizers.

If a category has all products, and all equalizers, then it has all limits.
Similarly, if it has all finite products, and all equalizers, then it has all finite limits.

If a functor preserves all products and equalizers, then it preserves all limits.
Similarly, if it preserves all finite products and equalizers, then it preserves all finite limits.

## TODO

Provide the dual results.
Show the analogous results for functors which reflect or create (co)limits.
-/


open CategoryTheory

open Opposite

namespace CategoryTheory.Limits

universe w v v₂ u u₂

variable {C : Type u} [Category.{v} C]
variable {J : Type w} [SmallCategory J]

-- We hide the "implementation details" inside a namespace
namespace HasLimitOfHasProductsOfHasEqualizers

variable {F : J ⥤ C} {c₁ : Fan F.obj} {c₂ : Fan fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.2}
  (s t : c₁.pt ⟶ c₂.pt)

/--
(Implementation) Given the appropriate product and equalizer cones, build the cone for `F` which is
limiting if the given cones are also.
-/
@[simps]
def buildLimit
    (hs : ∀ f : Σ p : J × J, p.1 ⟶ p.2, s ≫ c₂.π.app ⟨f⟩ = c₁.π.app ⟨f.1.1⟩ ≫ F.map f.2)
    (ht : ∀ f : Σ p : J × J, p.1 ⟶ p.2, t ≫ c₂.π.app ⟨f⟩ = c₁.π.app ⟨f.1.2⟩)
    (i : Fork s t) : Cone F where
  pt := i.pt
  π :=
    { app := fun _ => i.ι ≫ c₁.π.app ⟨_⟩
      naturality := fun j₁ j₂ f => by
        dsimp
        rw [Category.id_comp, Category.assoc, ← hs ⟨⟨_, _⟩, f⟩, i.condition_assoc, ht] }

variable
  (hs : ∀ f : Σ p : J × J, p.1 ⟶ p.2, s ≫ c₂.π.app ⟨f⟩ = c₁.π.app ⟨f.1.1⟩ ≫ F.map f.2)
  (ht : ∀ f : Σ p : J × J, p.1 ⟶ p.2, t ≫ c₂.π.app ⟨f⟩ = c₁.π.app ⟨f.1.2⟩)
  {i : Fork s t}

/--
(Implementation) Show the cone constructed in `buildLimit` is limiting, provided the cones used in
its construction are.
-/
def buildIsLimit (t₁ : IsLimit c₁) (t₂ : IsLimit c₂) (hi : IsLimit i) :
    IsLimit (buildLimit s t hs ht i) where
  lift q := by
    refine hi.lift (Fork.ofι ?_ ?_)
    · refine t₁.lift (Fan.mk _ fun j => ?_)
      apply q.π.app j
    · apply t₂.hom_ext
      intro ⟨j⟩
      simp [hs, ht]
  uniq q m w := hi.hom_ext (i.equalizer_ext (t₁.hom_ext fun j => by simpa using w j.1))
  fac s j := by simp

end HasLimitOfHasProductsOfHasEqualizers

open HasLimitOfHasProductsOfHasEqualizers

/-- Given the existence of the appropriate (possibly finite) products and equalizers,
we can construct a limit cone for `F`.
(This assumes the existence of all equalizers, which is technically stronger than needed.)
-/
noncomputable def limitConeOfEqualizerAndProduct (F : J ⥤ C) [HasLimit (Discrete.functor F.obj)]
    [HasLimit (Discrete.functor fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.2)] [HasEqualizers C] :
    LimitCone F where
  cone := _
  isLimit :=
    buildIsLimit (Pi.lift fun f => limit.π (Discrete.functor F.obj) ⟨_⟩ ≫ F.map f.2)
      (Pi.lift fun f => limit.π (Discrete.functor F.obj) ⟨f.1.2⟩) (by simp) (by simp)
      (limit.isLimit _) (limit.isLimit _) (limit.isLimit _)

/--
Given the existence of the appropriate (possibly finite) products and equalizers, we know a limit of
`F` exists.
(This assumes the existence of all equalizers, which is technically stronger than needed.)
-/
theorem hasLimit_of_equalizer_and_product (F : J ⥤ C) [HasLimit (Discrete.functor F.obj)]
    [HasLimit (Discrete.functor fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.2)] [HasEqualizers C] :
    HasLimit F :=
  HasLimit.mk (limitConeOfEqualizerAndProduct F)

/-- A limit can be realised as a subobject of a product. -/
noncomputable def limitSubobjectProduct [HasLimitsOfSize.{w, w} C] (F : J ⥤ C) :
    limit F ⟶ ∏ᶜ fun j => F.obj j :=
  have := hasFiniteLimits_of_hasLimitsOfSize C
  (limit.isoLimitCone (limitConeOfEqualizerAndProduct F)).hom ≫ equalizer.ι _ _

instance limitSubobjectProduct_mono [HasLimitsOfSize.{w, w} C] (F : J ⥤ C) :
    Mono (limitSubobjectProduct F) :=
  mono_comp _ _

@[reassoc (attr := simp)]
lemma limitSubobjectProduct_π {J : Type w} [Category.{w} J] {C : Type u} [Category.{v} C]
    [HasLimitsOfSize.{w, w} C] (F : J ⥤ C) (j : J) :
    limitSubobjectProduct F ≫ Pi.π F.obj j = limit.π F j := by
  simp only [limitSubobjectProduct, limit.cone_x, Category.assoc]
  rw [← Iso.eq_inv_comp]
  simp [limitConeOfEqualizerAndProduct]

/-- `limitSubobjectProduct` is indeed the canonical map from the limit to the product. -/
@[simp]
lemma limitSubobjectProduct_eq_lift {J : Type w} [Category.{w} J] {C : Type u} [Category.{v} C]
    [HasLimitsOfSize.{w, w} C] (F : J ⥤ C) :
    limitSubobjectProduct F = Pi.lift (limit.π F) := by
  apply limit.hom_ext
  intro ⟨j⟩
  simp

/-- Any category with products and equalizers has all limits. -/
@[stacks 002N]
theorem has_limits_of_hasEqualizers_and_products [HasProducts.{w} C] [HasEqualizers C] :
    HasLimitsOfSize.{w, w} C :=
  { has_limits_of_shape :=
    fun _ _ => { has_limit := fun F => hasLimit_of_equalizer_and_product F } }

/-- Any category with finite products and equalizers has all finite limits. -/
@[stacks 002O]
theorem hasFiniteLimits_of_hasEqualizers_and_finite_products [HasFiniteProducts C]
    [HasEqualizers C] : HasFiniteLimits C where
  out _ := { has_limit := fun F => hasLimit_of_equalizer_and_product F }

variable {D : Type u₂} [Category.{v₂} D]

section

variable [HasLimitsOfShape (Discrete J) C] [HasLimitsOfShape (Discrete (Σ p : J × J, p.1 ⟶ p.2)) C]
  [HasEqualizers C]

variable (G : C ⥤ D) [PreservesLimitsOfShape WalkingParallelPair G]
  -- [PreservesFiniteProducts G]
  [PreservesLimitsOfShape (Discrete.{w} J) G]
  [PreservesLimitsOfShape (Discrete.{w} (Σ p : J × J, p.1 ⟶ p.2)) G]

/-- If a functor preserves equalizers and the appropriate products, it preserves limits. -/
lemma preservesLimit_of_preservesEqualizers_and_product :
    PreservesLimitsOfShape J G where
  preservesLimit {K} := by
    let P := ∏ᶜ K.obj
    let Q := ∏ᶜ fun f : Σ p : J × J, p.fst ⟶ p.snd => K.obj f.1.2
    let s : P ⟶ Q := Pi.lift fun f => limit.π (Discrete.functor K.obj) ⟨_⟩ ≫ K.map f.2
    let t : P ⟶ Q := Pi.lift fun f => limit.π (Discrete.functor K.obj) ⟨f.1.2⟩
    let I := equalizer s t
    let i : I ⟶ P := equalizer.ι s t
    apply preservesLimit_of_preserves_limit_cone
        (buildIsLimit s t (by simp [P, s]) (by simp [P, t]) (limit.isLimit _)
          (limit.isLimit _) (limit.isLimit _))
    apply IsLimit.ofIsoLimit (buildIsLimit _ _ _ _ _ _ _) _
    · exact Fan.mk _ fun j => G.map (Pi.π _ j)
    · exact Fan.mk (G.obj Q) fun f => G.map (Pi.π _ f)
    · apply G.map s
    · apply G.map t
    · intro f
      dsimp [P, Q, s, Fan.mk]
      simp only [← G.map_comp, limit.lift_π]
      congr
    · intro f
      dsimp [P, Q, t, Fan.mk]
      simp only [← G.map_comp, limit.lift_π]
      apply congrArg G.map
      dsimp
    · apply Fork.ofι (G.map i)
      rw [← G.map_comp, ← G.map_comp]
      apply congrArg G.map
      exact equalizer.condition s t
    · apply isLimitOfHasProductOfPreservesLimit
    · apply isLimitOfHasProductOfPreservesLimit
    · apply isLimitForkMapOfIsLimit
      apply equalizerIsEqualizer
    · refine Cones.ext (Iso.refl _) ?_
      intro j; dsimp [P, Q, I, i]; simp

end

/-- If G preserves equalizers and finite products, it preserves finite limits. -/
lemma preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts [HasEqualizers C]
    [HasFiniteProducts C] (G : C ⥤ D) [PreservesLimitsOfShape WalkingParallelPair G]
    [PreservesFiniteProducts G] : PreservesFiniteLimits G where
  preservesFiniteLimits := by
    intros
    apply preservesLimit_of_preservesEqualizers_and_product


/-- If G preserves equalizers and products, it preserves all limits. -/
lemma preservesLimits_of_preservesEqualizers_and_products [HasEqualizers C]
    [HasProducts.{w} C] (G : C ⥤ D) [PreservesLimitsOfShape WalkingParallelPair G]
    [∀ J, PreservesLimitsOfShape (Discrete.{w} J) G] : PreservesLimitsOfSize.{w, w} G where
  preservesLimitsOfShape := preservesLimit_of_preservesEqualizers_and_product G

section

variable [HasLimitsOfShape (Discrete J) D] [HasLimitsOfShape (Discrete (Σ p : J × J, p.1 ⟶ p.2)) D]
  [HasEqualizers D]

variable (G : C ⥤ D) [G.ReflectsIsomorphisms] [CreatesLimitsOfShape WalkingParallelPair G]
  [CreatesLimitsOfShape (Discrete.{w} J) G]
  [CreatesLimitsOfShape (Discrete.{w} (Σ p : J × J, p.1 ⟶ p.2)) G]

attribute [local instance] preservesLimit_of_preservesEqualizers_and_product in
/-- If a functor creates equalizers and the appropriate products, it creates limits.

We additionally require the rather strong condition that the functor reflects isomorphisms. It is
unclear whether the statement remains true without this condition. There are various definitions of
"creating limits" in the literature, and whether or not the condition can be dropped seems to depend
on the specific definition that is used. -/
noncomputable def createsLimitsOfShapeOfCreatesEqualizersAndProducts :
    CreatesLimitsOfShape J G where
  CreatesLimit {K} :=
    have : HasLimitsOfShape (Discrete J) C :=
      hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape G
    have : HasLimitsOfShape (Discrete (Σ p : J × J, p.1 ⟶ p.2)) C :=
      hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape G
    have : HasEqualizers C :=
      hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape G
    have : HasLimit K := hasLimit_of_equalizer_and_product K
    createsLimitOfReflectsIsomorphismsOfPreserves

end

/-- If a functor creates equalizers and finite products, it creates finite limits.

We additionally require the rather strong condition that the functor reflects isomorphisms. It is
unclear whether the statement remains true without this condition. There are various definitions of
"creating limits" in the literature, and whether or not the condition can be dropped seems to depend
on the specific definition that is used. -/
noncomputable def createsFiniteLimitsOfCreatesEqualizersAndFiniteProducts [HasEqualizers D]
    [HasFiniteProducts D] (G : C ⥤ D) [G.ReflectsIsomorphisms]
    [CreatesLimitsOfShape WalkingParallelPair G]
    [CreatesFiniteProducts G] : CreatesFiniteLimits G where
  createsFiniteLimits _ _ _ := createsLimitsOfShapeOfCreatesEqualizersAndProducts G

/-- If a functor creates equalizers and products, it creates limits.

We additionally require the rather strong condition that the functor reflects isomorphisms. It is
unclear whether the statement remains true without this condition. There are various definitions of
"creating limits" in the literature, and whether or not the condition can be dropped seems to depend
on the specific definition that is used. -/
noncomputable def createsLimitsOfSizeOfCreatesEqualizersAndProducts [HasEqualizers D]
    [HasProducts.{w} D] (G : C ⥤ D) [G.ReflectsIsomorphisms]
    [CreatesLimitsOfShape WalkingParallelPair G] [∀ J, CreatesLimitsOfShape (Discrete.{w} J) G] :
    CreatesLimitsOfSize.{w, w} G where
  CreatesLimitsOfShape := createsLimitsOfShapeOfCreatesEqualizersAndProducts G

theorem hasFiniteLimits_of_hasTerminal_and_pullbacks [HasTerminal C] [HasPullbacks C] :
    HasFiniteLimits C :=
  @hasFiniteLimits_of_hasEqualizers_and_finite_products C _
    (@hasFiniteProducts_of_has_binary_and_terminal C _
      (hasBinaryProducts_of_hasTerminal_and_pullbacks C) inferInstance)
    (@hasEqualizers_of_hasPullbacks_and_binary_products C _
      (hasBinaryProducts_of_hasTerminal_and_pullbacks C) inferInstance)

/-- If G preserves terminal objects and pullbacks, it preserves all finite limits. -/
lemma preservesFiniteLimits_of_preservesTerminal_and_pullbacks [HasTerminal C]
    [HasPullbacks C] (G : C ⥤ D) [PreservesLimitsOfShape (Discrete.{0} PEmpty) G]
    [PreservesLimitsOfShape WalkingCospan G] : PreservesFiniteLimits G := by
  have : HasFiniteLimits C := hasFiniteLimits_of_hasTerminal_and_pullbacks
  have : PreservesLimitsOfShape (Discrete WalkingPair) G :=
    preservesBinaryProducts_of_preservesTerminal_and_pullbacks G
  have : PreservesLimitsOfShape WalkingParallelPair G :=
    preservesEqualizers_of_preservesPullbacks_and_binaryProducts G
  have : PreservesFiniteProducts G := .of_preserves_binary_and_terminal _
  exact preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts G

attribute [local instance] preservesFiniteLimits_of_preservesTerminal_and_pullbacks in
/-- If a functor creates terminal objects and pullbacks, it creates finite limits.

We additionally require the rather strong condition that the functor reflects isomorphisms. It is
unclear whether the statement remains true without this condition. There are various definitions of
"creating limits" in the literature, and whether or not the condition can be dropped seems to depend
on the specific definition that is used. -/
noncomputable def createsFiniteLimitsOfCreatesTerminalAndPullbacks [HasTerminal D]
    [HasPullbacks D] (G : C ⥤ D) [G.ReflectsIsomorphisms]
    [CreatesLimitsOfShape (Discrete.{0} PEmpty) G] [CreatesLimitsOfShape WalkingCospan G] :
    CreatesFiniteLimits G where
  createsFiniteLimits _ _ _ :=
    { CreatesLimit :=
        have : HasTerminal C := hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape G
        have : HasPullbacks C := hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape G
        have : HasFiniteLimits C := hasFiniteLimits_of_hasTerminal_and_pullbacks
        createsLimitOfReflectsIsomorphismsOfPreserves }

/-!
We now dualize the above constructions, resorting to copy-paste.
-/


-- We hide the "implementation details" inside a namespace
namespace HasColimitOfHasCoproductsOfHasCoequalizers

variable {F : J ⥤ C} {c₁ : Cofan fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.1} {c₂ : Cofan F.obj}
  (s t : c₁.pt ⟶ c₂.pt)

/-- (Implementation) Given the appropriate coproduct and coequalizer cocones,
build the cocone for `F` which is colimiting if the given cocones are also.
-/
@[simps]
def buildColimit
    (hs : ∀ f : Σ p : J × J, p.1 ⟶ p.2, c₁.ι.app ⟨f⟩ ≫ s = F.map f.2 ≫ c₂.ι.app ⟨f.1.2⟩)
    (ht : ∀ f : Σ p : J × J, p.1 ⟶ p.2, c₁.ι.app ⟨f⟩ ≫ t = c₂.ι.app ⟨f.1.1⟩)
    (i : Cofork s t) : Cocone F where
  pt := i.pt
  ι :=
    { app := fun _ => c₂.ι.app ⟨_⟩ ≫ i.π
      naturality := fun j₁ j₂ f => by
        dsimp
        have reassoced (f : (p : J × J) × (p.fst ⟶ p.snd)) {W : C} {h : _ ⟶ W} :
          c₁.ι.app ⟨f⟩ ≫ s ≫ h = F.map f.snd ≫ c₂.ι.app ⟨f.fst.snd⟩ ≫ h := by
            simp only [← Category.assoc, eq_whisker (hs f)]
        rw [Category.comp_id, ← reassoced ⟨⟨_, _⟩, f⟩, i.condition, ← Category.assoc, ht] }

variable
  (hs : ∀ f : Σ p : J × J, p.1 ⟶ p.2, c₁.ι.app ⟨f⟩ ≫ s = F.map f.2 ≫ c₂.ι.app ⟨f.1.2⟩)
  (ht : ∀ f : Σ p : J × J, p.1 ⟶ p.2, c₁.ι.app ⟨f⟩ ≫ t = c₂.ι.app ⟨f.1.1⟩)
  {i : Cofork s t}

/-- (Implementation) Show the cocone constructed in `buildColimit` is colimiting,
provided the cocones used in its construction are.
-/
def buildIsColimit (t₁ : IsColimit c₁) (t₂ : IsColimit c₂) (hi : IsColimit i) :
    IsColimit (buildColimit s t hs ht i) where
  desc q := by
    refine hi.desc (Cofork.ofπ ?_ ?_)
    · refine t₂.desc (Cofan.mk _ fun j => ?_)
      apply q.ι.app j
    · apply t₁.hom_ext
      intro ⟨j⟩
      have reassoced_s (f : (p : J × J) × (p.fst ⟶ p.snd)) {W : C} (h : _ ⟶ W) :
        c₁.ι.app ⟨f⟩ ≫ s ≫ h = F.map f.snd ≫ c₂.ι.app ⟨f.fst.snd⟩ ≫ h := by
          simp only [← Category.assoc]
          apply eq_whisker (hs f)
      have reassoced_t (f : (p : J × J) × (p.fst ⟶ p.snd)) {W : C} (h : _ ⟶ W) :
        c₁.ι.app ⟨f⟩ ≫ t ≫ h = c₂.ι.app ⟨f.fst.fst⟩ ≫ h := by
          simp only [← Category.assoc]
          apply eq_whisker (ht f)
      simp [reassoced_s, reassoced_t]
  uniq q m w := hi.hom_ext (i.coequalizer_ext (t₂.hom_ext fun j => by simpa using w j.1))
  fac s j := by simp

end HasColimitOfHasCoproductsOfHasCoequalizers

open HasColimitOfHasCoproductsOfHasCoequalizers

/-- Given the existence of the appropriate (possibly finite) coproducts and coequalizers,
we can construct a colimit cocone for `F`.
(This assumes the existence of all coequalizers, which is technically stronger than needed.)
-/
noncomputable def colimitCoconeOfCoequalizerAndCoproduct (F : J ⥤ C)
    [HasColimit (Discrete.functor F.obj)]
    [HasColimit (Discrete.functor fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.1)]
    [HasCoequalizers C] : ColimitCocone F where
  cocone := _
  isColimit :=
    buildIsColimit (Sigma.desc fun f => F.map f.2 ≫ colimit.ι (Discrete.functor F.obj) ⟨f.1.2⟩)
      (Sigma.desc fun f => colimit.ι (Discrete.functor F.obj) ⟨f.1.1⟩) (by simp) (by simp)
      (colimit.isColimit _) (colimit.isColimit _) (colimit.isColimit _)

/-- Given the existence of the appropriate (possibly finite) coproducts and coequalizers,
we know a colimit of `F` exists.
(This assumes the existence of all coequalizers, which is technically stronger than needed.)
-/
theorem hasColimit_of_coequalizer_and_coproduct (F : J ⥤ C) [HasColimit (Discrete.functor F.obj)]
    [HasColimit (Discrete.functor fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.1)]
    [HasCoequalizers C] : HasColimit F :=
  HasColimit.mk (colimitCoconeOfCoequalizerAndCoproduct F)

/-- A colimit can be realised as a quotient of a coproduct. -/
noncomputable def colimitQuotientCoproduct [HasColimitsOfSize.{w, w} C] (F : J ⥤ C) :
    ∐ (fun j => F.obj j) ⟶ colimit F :=
  have := hasFiniteColimits_of_hasColimitsOfSize C
  coequalizer.π _ _ ≫ (colimit.isoColimitCocone (colimitCoconeOfCoequalizerAndCoproduct F)).inv

instance colimitQuotientCoproduct_epi [HasColimitsOfSize.{w, w} C] (F : J ⥤ C) :
    Epi (colimitQuotientCoproduct F) :=
  epi_comp _ _

@[reassoc (attr := simp)]
lemma colimitQuotientCoproduct_ι {J : Type w} [Category.{w} J] {C : Type u} [Category.{v} C]
    [HasColimitsOfSize.{w, w} C] (F : J ⥤ C) (j : J) :
    Sigma.ι F.obj j ≫ colimitQuotientCoproduct F = colimit.ι F j := by
  simp only [colimitQuotientCoproduct, colimit.cocone_x, ← Category.assoc]
  rw [Iso.comp_inv_eq]
  simp [colimitCoconeOfCoequalizerAndCoproduct]

/-- `colimitQuotientCoproduct` is indeed the canonical map from the coproduct to the colimit. -/
@[simp]
lemma colimitQuotientCoproduct_eq_desc {J : Type w} [Category.{w} J] {C : Type u} [Category.{v} C]
    [HasColimitsOfSize.{w, w} C] (F : J ⥤ C) :
    colimitQuotientCoproduct F = Sigma.desc (colimit.ι F) := by
  apply colimit.hom_ext
  intro ⟨j⟩
  simp

/-- Any category with coproducts and coequalizers has all colimits. -/
@[stacks 002P]
theorem has_colimits_of_hasCoequalizers_and_coproducts [HasCoproducts.{w} C] [HasCoequalizers C] :
    HasColimitsOfSize.{w, w} C where
  has_colimits_of_shape := fun _ _ =>
      { has_colimit := fun F => hasColimit_of_coequalizer_and_coproduct F }

/-- Any category with finite coproducts and coequalizers has all finite colimits. -/
@[stacks 002Q]
theorem hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts [HasFiniteCoproducts C]
    [HasCoequalizers C] : HasFiniteColimits C where
  out _ := { has_colimit := fun F => hasColimit_of_coequalizer_and_coproduct F }

section

variable [HasColimitsOfShape (Discrete.{w} J) C]
  [HasColimitsOfShape (Discrete.{w} (Σ p : J × J, p.1 ⟶ p.2)) C] [HasCoequalizers C]

variable (G : C ⥤ D) [PreservesColimitsOfShape WalkingParallelPair G]
  [PreservesColimitsOfShape (Discrete.{w} J) G]
  [PreservesColimitsOfShape (Discrete.{w} (Σ p : J × J, p.1 ⟶ p.2)) G]

/-- If a functor preserves coequalizers and the appropriate coproducts, it preserves colimits. -/
lemma preservesColimit_of_preservesCoequalizers_and_coproduct :
    PreservesColimitsOfShape J G where
  preservesColimit {K} := by
    let P := ∐ K.obj
    let Q := ∐ fun f : Σ p : J × J, p.fst ⟶ p.snd => K.obj f.1.1
    let s : Q ⟶ P := Sigma.desc fun f => K.map f.2 ≫ colimit.ι (Discrete.functor K.obj) ⟨_⟩
    let t : Q ⟶ P := Sigma.desc fun f => colimit.ι (Discrete.functor K.obj) ⟨f.1.1⟩
    let I := coequalizer s t
    let i : P ⟶ I := coequalizer.π s t
    apply preservesColimit_of_preserves_colimit_cocone
        (buildIsColimit s t (by simp [P, s]) (by simp [P, t]) (colimit.isColimit _)
          (colimit.isColimit _) (colimit.isColimit _))
    apply IsColimit.ofIsoColimit (buildIsColimit _ _ _ _ _ _ _) _
    · refine Cofan.mk (G.obj Q) fun j => G.map ?_
      apply Sigma.ι _ j
    -- fun j => G.map (Sigma.ι _ j)
    · exact Cofan.mk _ fun f => G.map (Sigma.ι _ f)
    · apply G.map s
    · apply G.map t
    · intro f
      dsimp [P, Q, s, Cofan.mk]
      simp only [← G.map_comp, colimit.ι_desc]
      congr
    · intro f
      dsimp [P, Q, t, Cofan.mk]
      simp only [← G.map_comp, colimit.ι_desc]
      dsimp
    · refine Cofork.ofπ (G.map i) ?_
      rw [← G.map_comp, ← G.map_comp]
      apply congrArg G.map
      apply coequalizer.condition
    · apply isColimitOfHasCoproductOfPreservesColimit
    · apply isColimitOfHasCoproductOfPreservesColimit
    · apply isColimitCoforkMapOfIsColimit
      apply coequalizerIsCoequalizer
    refine Cocones.ext (Iso.refl _) ?_
    intro j
    dsimp [P, Q, I, i]
    simp

end

/-- If G preserves coequalizers and finite coproducts, it preserves finite colimits. -/
lemma preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts
    [HasCoequalizers C] [HasFiniteCoproducts C] (G : C ⥤ D)
    [PreservesColimitsOfShape WalkingParallelPair G]
    [PreservesFiniteCoproducts G] : PreservesFiniteColimits G where
  preservesFiniteColimits := by
    intro J sJ fJ
    apply preservesColimit_of_preservesCoequalizers_and_coproduct

/-- If G preserves coequalizers and coproducts, it preserves all colimits. -/
lemma preservesColimits_of_preservesCoequalizers_and_coproducts [HasCoequalizers C]
    [HasCoproducts.{w} C] (G : C ⥤ D) [PreservesColimitsOfShape WalkingParallelPair G]
    [∀ J, PreservesColimitsOfShape (Discrete.{w} J) G] : PreservesColimitsOfSize.{w, w} G where
  preservesColimitsOfShape := preservesColimit_of_preservesCoequalizers_and_coproduct G

section

variable [HasColimitsOfShape (Discrete J) D]
  [HasColimitsOfShape (Discrete (Σ p : J × J, p.1 ⟶ p.2)) D] [HasCoequalizers D]

variable (G : C ⥤ D) [G.ReflectsIsomorphisms] [CreatesColimitsOfShape WalkingParallelPair G]
  [CreatesColimitsOfShape (Discrete.{w} J) G]
  [CreatesColimitsOfShape (Discrete.{w} (Σ p : J × J, p.1 ⟶ p.2)) G]

attribute [local instance] preservesColimit_of_preservesCoequalizers_and_coproduct in
/-- If a functor creates coequalizers and the appropriate coproducts, it creates colimits.

We additionally require the rather strong condition that the functor reflects isomorphisms. It is
unclear whether the statement remains true without this condition. There are various definitions of
"creating colimits" in the literature, and whether or not the condition can be dropped seems to
depend on the specific definition that is used. -/
noncomputable def createsColimitsOfShapeOfCreatesCoequalizersAndCoproducts :
    CreatesColimitsOfShape J G where
  CreatesColimit {K} :=
    have : HasColimitsOfShape (Discrete J) C :=
      hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape G
    have : HasColimitsOfShape (Discrete (Σ p : J × J, p.1 ⟶ p.2)) C :=
      hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape G
    have : HasCoequalizers C :=
      hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape G
    have : HasColimit K := hasColimit_of_coequalizer_and_coproduct K
    createsColimitOfReflectsIsomorphismsOfPreserves

end

/-- If a functor creates coequalizers and finite coproducts, it creates finite colimits.

We additionally require the rather strong condition that the functor reflects isomorphisms. It is
unclear whether the statement remains true without this condition. There are various definitions of
"creating colimits" in the literature, and whether or not the condition can be dropped seems to
depend on the specific definition that is used. -/
noncomputable def createsFiniteColimitsOfCreatesCoequalizersAndFiniteCoproducts [HasCoequalizers D]
    [HasFiniteCoproducts D] (G : C ⥤ D) [G.ReflectsIsomorphisms]
    [CreatesColimitsOfShape WalkingParallelPair G]
    [CreatesFiniteCoproducts G] : CreatesFiniteColimits G where
  createsFiniteColimits _ _ _ := createsColimitsOfShapeOfCreatesCoequalizersAndCoproducts G

/-- If a functor creates coequalizers and coproducts, it creates colimits.

We additionally require the rather strong condition that the functor reflects isomorphisms. It is
unclear whether the statement remains true without this condition. There are various definitions of
"creating colimits" in the literature, and whether or not the condition can be dropped seems to
depend on the specific definition that is used. -/
noncomputable def createsColimitsOfSizeOfCreatesCoequalizersAndCoproducts [HasCoequalizers D]
    [HasCoproducts.{w} D] (G : C ⥤ D) [G.ReflectsIsomorphisms]
    [CreatesColimitsOfShape WalkingParallelPair G]
    [∀ J, CreatesColimitsOfShape (Discrete.{w} J) G] : CreatesColimitsOfSize.{w, w} G where
  CreatesColimitsOfShape := createsColimitsOfShapeOfCreatesCoequalizersAndCoproducts G

theorem hasFiniteColimits_of_hasInitial_and_pushouts [HasInitial C] [HasPushouts C] :
    HasFiniteColimits C :=
  @hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts C _
    (@hasFiniteCoproducts_of_has_binary_and_initial C _
      (hasBinaryCoproducts_of_hasInitial_and_pushouts C) inferInstance)
    (@hasCoequalizers_of_hasPushouts_and_binary_coproducts C _
      (hasBinaryCoproducts_of_hasInitial_and_pushouts C) inferInstance)

/-- If G preserves initial objects and pushouts, it preserves all finite colimits. -/
lemma preservesFiniteColimits_of_preservesInitial_and_pushouts [HasInitial C]
    [HasPushouts C] (G : C ⥤ D) [PreservesColimitsOfShape (Discrete.{0} PEmpty) G]
    [PreservesColimitsOfShape WalkingSpan G] : PreservesFiniteColimits G := by
  haveI : HasFiniteColimits C := hasFiniteColimits_of_hasInitial_and_pushouts
  haveI : PreservesColimitsOfShape (Discrete WalkingPair) G :=
    preservesBinaryCoproducts_of_preservesInitial_and_pushouts G
  haveI : PreservesColimitsOfShape (WalkingParallelPair) G :=
      (preservesCoequalizers_of_preservesPushouts_and_binaryCoproducts G)
  refine
    @preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts _ _ _ _ _ _ G _ ?_
  refine ⟨fun _ ↦ ?_⟩
  apply preservesFiniteCoproductsOfPreservesBinaryAndInitial G

attribute [local instance] preservesFiniteColimits_of_preservesInitial_and_pushouts in
/-- If a functor creates initial objects and pushouts, it creates finite colimits.

We additionally require the rather strong condition that the functor reflects isomorphisms. It is
unclear whether the statement remains true without this condition. There are various definitions of
"creating colimits" in the literature, and whether or not the condition can be dropped seems to
depend on the specific definition that is used. -/
noncomputable def createsFiniteColimitsOfCreatesInitialAndPushouts [HasInitial D]
    [HasPushouts D] (G : C ⥤ D) [G.ReflectsIsomorphisms]
    [CreatesColimitsOfShape (Discrete.{0} PEmpty) G] [CreatesColimitsOfShape WalkingSpan G] :
    CreatesFiniteColimits G where
  createsFiniteColimits _ _ _ :=
    { CreatesColimit :=
        have : HasInitial C := hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape G
        have : HasPushouts C := hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape G
        have : HasFiniteColimits C := hasFiniteColimits_of_hasInitial_and_pushouts
        createsColimitOfReflectsIsomorphismsOfPreserves }

end CategoryTheory.Limits
