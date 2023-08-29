/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Scott Morrison
-/
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.Constructions.Equalizers
import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts

#align_import category_theory.limits.constructions.limits_of_products_and_equalizers from "leanprover-community/mathlib"@"c3019c79074b0619edb4b27553a91b2e82242395"

/-!
# Constructing limits from products and equalizers.

If a category has all products, and all equalizers, then it has all limits.
Similarly, if it has all finite products, and all equalizers, then it has all finite limits.

If a functor preserves all products and equalizers, then it preserves all limits.
Similarly, if it preserves all finite products and equalizers, then it preserves all finite limits.

# TODO

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

variable {F : J ⥤ C} {c₁ : Fan F.obj} {c₂ : Fan fun f : Σp : J × J, p.1 ⟶ p.2 => F.obj f.1.2}
  (s t : c₁.pt ⟶ c₂.pt)
  (hs : ∀ f : Σp : J × J, p.1 ⟶ p.2, s ≫ c₂.π.app ⟨f⟩ = c₁.π.app ⟨f.1.1⟩ ≫ F.map f.2)
  (ht : ∀ f : Σp : J × J, p.1 ⟶ p.2, t ≫ c₂.π.app ⟨f⟩ = c₁.π.app ⟨f.1.2⟩) (i : Fork s t)

/--
(Implementation) Given the appropriate product and equalizer cones, build the cone for `F` which is
limiting if the given cones are also.
-/
@[simps]
def buildLimit : Cone F where
  pt := i.pt
  π :=
    { app := fun j => i.ι ≫ c₁.π.app ⟨_⟩
      naturality := fun j₁ j₂ f => by
        dsimp
        -- ⊢ 𝟙 i.pt ≫ Fork.ι i ≫ NatTrans.app c₁.π { as := j₂ } = (Fork.ι i ≫ NatTrans.ap …
        rw [Category.id_comp, Category.assoc, ← hs ⟨⟨_, _⟩, f⟩, i.condition_assoc, ht] }
        -- 🎉 no goals
#align category_theory.limits.has_limit_of_has_products_of_has_equalizers.build_limit CategoryTheory.Limits.HasLimitOfHasProductsOfHasEqualizers.buildLimit

variable {i}

/--
(Implementation) Show the cone constructed in `buildLimit` is limiting, provided the cones used in
its construction are.
-/
def buildIsLimit (t₁ : IsLimit c₁) (t₂ : IsLimit c₂) (hi : IsLimit i) :
    IsLimit (buildLimit s t hs ht i) where
  lift q := by
    refine' hi.lift (Fork.ofι _ _)
    -- ⊢ q.1 ⟶ c₁.pt
    · refine' t₁.lift (Fan.mk _ fun j => _)
      -- ⊢ q.1 ⟶ F.obj j
      apply q.π.app j
      -- 🎉 no goals
    · apply t₂.hom_ext
      -- ⊢ ∀ (j : Discrete ((p : J × J) × (p.fst ⟶ p.snd))), (IsLimit.lift t₁ (Fan.mk q …
      intro ⟨j⟩
      -- ⊢ (IsLimit.lift t₁ (Fan.mk q.1 fun j => NatTrans.app q.π j) ≫ s) ≫ NatTrans.ap …
      simp [hs, ht]
      -- 🎉 no goals
  uniq q m w :=
    hi.hom_ext
      (i.equalizer_ext
        (t₁.hom_ext fun j => by
          cases' j with j
          -- ⊢ (m ≫ Fork.ι i) ≫ NatTrans.app c₁.π { as := j } = ((fun q => IsLimit.lift hi  …
          simpa using w j))
                -- 🎉 no goals
          -- 🎉 no goals
  fac s j := by simp
#align category_theory.limits.has_limit_of_has_products_of_has_equalizers.build_is_limit CategoryTheory.Limits.HasLimitOfHasProductsOfHasEqualizers.buildIsLimit

end HasLimitOfHasProductsOfHasEqualizers

open HasLimitOfHasProductsOfHasEqualizers

/-- Given the existence of the appropriate (possibly finite) products and equalizers,
we can construct a limit cone for `F`.
(This assumes the existence of all equalizers, which is technically stronger than needed.)
-/
noncomputable def limitConeOfEqualizerAndProduct (F : J ⥤ C) [HasLimit (Discrete.functor F.obj)]
    [HasLimit (Discrete.functor fun f : Σp : J × J, p.1 ⟶ p.2 => F.obj f.1.2)] [HasEqualizers C] :
    LimitCone F where
  cone := _
  isLimit :=
    buildIsLimit (Pi.lift fun f => limit.π (Discrete.functor F.obj) ⟨_⟩ ≫ F.map f.2)
      (Pi.lift fun f => limit.π (Discrete.functor F.obj) ⟨f.1.2⟩) (by simp) (by simp)
                                                                      -- 🎉 no goals
                                                                                -- 🎉 no goals
      (limit.isLimit _) (limit.isLimit _) (limit.isLimit _)
#align category_theory.limits.limit_cone_of_equalizer_and_product CategoryTheory.Limits.limitConeOfEqualizerAndProduct

/--
Given the existence of the appropriate (possibly finite) products and equalizers, we know a limit of
`F` exists.
(This assumes the existence of all equalizers, which is technically stronger than needed.)
-/
theorem hasLimit_of_equalizer_and_product (F : J ⥤ C) [HasLimit (Discrete.functor F.obj)]
    [HasLimit (Discrete.functor fun f : Σp : J × J, p.1 ⟶ p.2 => F.obj f.1.2)] [HasEqualizers C] :
    HasLimit F :=
  HasLimit.mk (limitConeOfEqualizerAndProduct F)
#align category_theory.limits.has_limit_of_equalizer_and_product CategoryTheory.Limits.hasLimit_of_equalizer_and_product

/-- A limit can be realised as a subobject of a product. -/
noncomputable def limitSubobjectProduct [HasLimitsOfSize.{w, w} C] (F : J ⥤ C) :
    limit F ⟶ ∏ fun j => F.obj j :=
  (limit.isoLimitCone (limitConeOfEqualizerAndProduct F)).hom ≫ equalizer.ι _ _
#align category_theory.limits.limit_subobject_product CategoryTheory.Limits.limitSubobjectProduct

instance limitSubobjectProduct_mono [HasLimitsOfSize.{w, w} C] (F : J ⥤ C) :
    Mono (limitSubobjectProduct F) :=
  mono_comp _ _
#align category_theory.limits.limit_subobject_product_mono CategoryTheory.Limits.limitSubobjectProduct_mono

/-- Any category with products and equalizers has all limits.

See <https://stacks.math.columbia.edu/tag/002N>.
-/
theorem has_limits_of_hasEqualizers_and_products [HasProducts.{w} C] [HasEqualizers C] :
    HasLimitsOfSize.{w, w} C :=
  { has_limits_of_shape :=
    fun _ _ => { has_limit := fun F => hasLimit_of_equalizer_and_product F } }
#align category_theory.limits.has_limits_of_has_equalizers_and_products CategoryTheory.Limits.has_limits_of_hasEqualizers_and_products

/-- Any category with finite products and equalizers has all finite limits.

See <https://stacks.math.columbia.edu/tag/002O>.
-/
theorem hasFiniteLimits_of_hasEqualizers_and_finite_products [HasFiniteProducts C]
    [HasEqualizers C] : HasFiniteLimits C where
  out _ := { has_limit := fun F => hasLimit_of_equalizer_and_product F }
#align category_theory.limits.has_finite_limits_of_has_equalizers_and_finite_products CategoryTheory.Limits.hasFiniteLimits_of_hasEqualizers_and_finite_products

variable {D : Type u₂} [Category.{v₂} D]

/- Porting note: Removed this and made whatever necessary noncomputable -/
-- noncomputable section

section

variable [HasLimitsOfShape (Discrete J) C] [HasLimitsOfShape (Discrete (Σp : J × J, p.1 ⟶ p.2)) C]
  [HasEqualizers C]

variable (G : C ⥤ D) [PreservesLimitsOfShape WalkingParallelPair G]
  -- [PreservesFiniteProducts G]
  [PreservesLimitsOfShape (Discrete.{w} J) G]
  [PreservesLimitsOfShape (Discrete.{w} (Σp : J × J, p.1 ⟶ p.2)) G]

/-- If a functor preserves equalizers and the appropriate products, it preserves limits. -/
noncomputable def preservesLimitOfPreservesEqualizersAndProduct : PreservesLimitsOfShape J G where
  preservesLimit {K} := by
    let P := ∏ K.obj
    -- ⊢ PreservesLimit K G
    let Q := ∏ fun f : Σp : J × J, p.fst ⟶ p.snd => K.obj f.1.2
    -- ⊢ PreservesLimit K G
    let s : P ⟶ Q := Pi.lift fun f => limit.π (Discrete.functor K.obj) ⟨_⟩ ≫ K.map f.2
    -- ⊢ PreservesLimit K G
    let t : P ⟶ Q := Pi.lift fun f => limit.π (Discrete.functor K.obj) ⟨f.1.2⟩
    -- ⊢ PreservesLimit K G
    let I := equalizer s t
    -- ⊢ PreservesLimit K G
    let i : I ⟶ P := equalizer.ι s t
    -- ⊢ PreservesLimit K G
    apply
      preservesLimitOfPreservesLimitCone
        (buildIsLimit s t (by simp) (by simp) (limit.isLimit _) (limit.isLimit _)
          (limit.isLimit _))
    refine' IsLimit.ofIsoLimit (buildIsLimit _ _ _ _ _ _ _) _
    · exact Fan.mk _ fun j => G.map (Pi.π _ j)
      -- 🎉 no goals
    · exact Fan.mk (G.obj Q) fun f => G.map (Pi.π _ f)
      -- 🎉 no goals
    · apply G.map s
      -- 🎉 no goals
    · apply G.map t
      -- 🎉 no goals
    · intro f
      -- ⊢ G.map s ≫ NatTrans.app (Fan.mk (G.obj Q) fun f => G.map (Pi.π (fun f => K.ob …
      dsimp [Fan.mk]
      -- ⊢ G.map (Pi.lift fun f => limit.π (Discrete.functor K.obj) { as := f.fst.1 } ≫ …
      simp only [← G.map_comp, limit.lift_π]
      -- ⊢ G.map (NatTrans.app (Fan.mk (∏ K.obj) fun f => limit.π (Discrete.functor K.o …
      congr
      -- 🎉 no goals
    · intro f
      -- ⊢ G.map t ≫ NatTrans.app (Fan.mk (G.obj Q) fun f => G.map (Pi.π (fun f => K.ob …
      dsimp [Fan.mk]
      -- ⊢ G.map (Pi.lift fun f => limit.π (Discrete.functor K.obj) { as := f.fst.snd } …
      simp only [← G.map_comp, limit.lift_π]
      -- ⊢ G.map (NatTrans.app (Fan.mk (∏ K.obj) fun f => limit.π (Discrete.functor K.o …
      apply congrArg G.map
      -- ⊢ NatTrans.app (Fan.mk (∏ K.obj) fun f => limit.π (Discrete.functor K.obj) { a …
      dsimp
      -- 🎉 no goals
    · apply Fork.ofι (G.map i)
      -- ⊢ G.map i ≫ G.map s = G.map i ≫ G.map t
      rw [← G.map_comp, ← G.map_comp]
      -- ⊢ G.map (i ≫ s) = G.map (i ≫ t)
      apply congrArg G.map
      -- ⊢ i ≫ s = i ≫ t
      exact equalizer.condition s t
      -- 🎉 no goals
    · apply isLimitOfHasProductOfPreservesLimit
      -- 🎉 no goals
    · apply isLimitOfHasProductOfPreservesLimit
      -- 🎉 no goals
    · apply isLimitForkMapOfIsLimit
      -- ⊢ IsLimit (Fork.ofι i ?refine'_10.w)
      apply equalizerIsEqualizer
      -- 🎉 no goals
    · refine Cones.ext (Iso.refl _) ?_
      -- ⊢ ∀ (j : J), NatTrans.app (buildLimit (G.map s) (G.map t) (_ : ∀ (f : (p : J × …
      intro j; dsimp; simp
      -- ⊢ NatTrans.app (buildLimit (G.map s) (G.map t) (_ : ∀ (f : (p : J × J) × (p.fs …
               -- ⊢ G.map (equalizer.ι (Pi.lift fun f => limit.π (Discrete.functor K.obj) { as : …
                      -- 🎉 no goals
-- See note [dsimp, simp].
#align category_theory.limits.preserves_limit_of_preserves_equalizers_and_product CategoryTheory.Limits.preservesLimitOfPreservesEqualizersAndProduct

end

/- Porting note: the original parameter [∀ (J) [Fintype J], PreservesColimitsOfShape
(Discrete.{0} J) G] triggered the error "invalid parametric local instance, parameter
with type Fintype J does not have forward dependencies, type class resolution cannot
use this kind of local instance because it will not be able to infer a value for this
parameter." Factored out this as new class in `CategoryTheory.Limits.Preserves.Finite` -/
/-- If G preserves equalizers and finite products, it preserves finite limits. -/
noncomputable def preservesFiniteLimitsOfPreservesEqualizersAndFiniteProducts [HasEqualizers C]
    [HasFiniteProducts C] (G : C ⥤ D) [PreservesLimitsOfShape WalkingParallelPair G]
    [PreservesFiniteProducts G] : PreservesFiniteLimits G where
  preservesFiniteLimits := by
    intro J sJ fJ
    -- ⊢ PreservesLimitsOfShape J G
    haveI : Fintype J := inferInstance
    -- ⊢ PreservesLimitsOfShape J G
    haveI : Fintype ((p : J × J) × (p.fst ⟶ p.snd)) := inferInstance
    -- ⊢ PreservesLimitsOfShape J G
    apply @preservesLimitOfPreservesEqualizersAndProduct _ _ _ sJ _ _ ?_ ?_ _ G _ ?_ ?_
    · apply hasLimitsOfShape_discrete _ _
      -- 🎉 no goals
    · apply hasLimitsOfShape_discrete _
      -- 🎉 no goals
    · apply PreservesFiniteProducts.preserves _
      -- 🎉 no goals
    · apply PreservesFiniteProducts.preserves _
      -- 🎉 no goals
#align category_theory.limits.preserves_finite_limits_of_preserves_equalizers_and_finite_products CategoryTheory.Limits.preservesFiniteLimitsOfPreservesEqualizersAndFiniteProducts

/-- If G preserves equalizers and products, it preserves all limits. -/
noncomputable def preservesLimitsOfPreservesEqualizersAndProducts [HasEqualizers C]
    [HasProducts.{w} C] (G : C ⥤ D) [PreservesLimitsOfShape WalkingParallelPair G]
    [∀ J, PreservesLimitsOfShape (Discrete.{w} J) G] : PreservesLimitsOfSize.{w, w} G where
  preservesLimitsOfShape := preservesLimitOfPreservesEqualizersAndProduct G
#align category_theory.limits.preserves_limits_of_preserves_equalizers_and_products CategoryTheory.Limits.preservesLimitsOfPreservesEqualizersAndProducts

theorem hasFiniteLimits_of_hasTerminal_and_pullbacks [HasTerminal C] [HasPullbacks C] :
    HasFiniteLimits C :=
  @hasFiniteLimits_of_hasEqualizers_and_finite_products C _
    (@hasFiniteProducts_of_has_binary_and_terminal C _
      (hasBinaryProducts_of_hasTerminal_and_pullbacks C) inferInstance)
    (@hasEqualizers_of_hasPullbacks_and_binary_products C _
      (hasBinaryProducts_of_hasTerminal_and_pullbacks C) inferInstance)
#align category_theory.limits.has_finite_limits_of_has_terminal_and_pullbacks CategoryTheory.Limits.hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- If G preserves terminal objects and pullbacks, it preserves all finite limits. -/
noncomputable def preservesFiniteLimitsOfPreservesTerminalAndPullbacks [HasTerminal C]
    [HasPullbacks C] (G : C ⥤ D) [PreservesLimitsOfShape (Discrete.{0} PEmpty) G]
    [PreservesLimitsOfShape WalkingCospan G] : PreservesFiniteLimits G := by
  haveI : HasFiniteLimits C := hasFiniteLimits_of_hasTerminal_and_pullbacks
  -- ⊢ PreservesFiniteLimits G
  haveI : PreservesLimitsOfShape (Discrete WalkingPair) G :=
    preservesBinaryProductsOfPreservesTerminalAndPullbacks G
  haveI : PreservesLimitsOfShape WalkingParallelPair G :=
      preservesEqualizersOfPreservesPullbacksAndBinaryProducts G
  apply
    @preservesFiniteLimitsOfPreservesEqualizersAndFiniteProducts _ _ _ _ _ _ G _ ?_
  apply PreservesFiniteProducts.mk
  -- ⊢ (J : Type) → [inst : Fintype J] → PreservesLimitsOfShape (Discrete J) G
  apply preservesFiniteProductsOfPreservesBinaryAndTerminal G
  -- 🎉 no goals
#align category_theory.limits.preserves_finite_limits_of_preserves_terminal_and_pullbacks CategoryTheory.Limits.preservesFiniteLimitsOfPreservesTerminalAndPullbacks

/-!
We now dualize the above constructions, resorting to copy-paste.
-/


-- We hide the "implementation details" inside a namespace
namespace HasColimitOfHasCoproductsOfHasCoequalizers

variable {F : J ⥤ C} {c₁ : Cofan fun f : Σp : J × J, p.1 ⟶ p.2 => F.obj f.1.1} {c₂ : Cofan F.obj}
  (s t : c₁.pt ⟶ c₂.pt)
  (hs : ∀ f : Σp : J × J, p.1 ⟶ p.2, c₁.ι.app ⟨f⟩ ≫ s = F.map f.2 ≫ c₂.ι.app ⟨f.1.2⟩)
  (ht : ∀ f : Σp : J × J, p.1 ⟶ p.2, c₁.ι.app ⟨f⟩ ≫ t = c₂.ι.app ⟨f.1.1⟩) (i : Cofork s t)

/-- (Implementation) Given the appropriate coproduct and coequalizer cocones,
build the cocone for `F` which is colimiting if the given cocones are also.
-/
@[simps]
def buildColimit : Cocone F where
  pt := i.pt
  ι :=
    { app := fun j => c₂.ι.app ⟨_⟩ ≫ i.π
      naturality := fun j₁ j₂ f => by
        dsimp
        -- ⊢ F.map f ≫ NatTrans.app c₂.ι { as := j₂ } ≫ Cofork.π i = (NatTrans.app c₂.ι { …
        have reassoced (f : (p : J × J) × (p.fst ⟶ p.snd)) {W : C} {h : _ ⟶ W} :
          c₁.ι.app ⟨f⟩ ≫ s ≫ h = F.map f.snd ≫ c₂.ι.app ⟨f.fst.snd⟩ ≫ h := by
            simp only [← Category.assoc, eq_whisker (hs f)]
        rw [Category.comp_id, ← reassoced ⟨⟨_, _⟩, f⟩, i.condition, ← Category.assoc, ht] }
        -- 🎉 no goals
#align category_theory.limits.has_colimit_of_has_coproducts_of_has_coequalizers.build_colimit CategoryTheory.Limits.HasColimitOfHasCoproductsOfHasCoequalizers.buildColimit

variable {i}

/-- (Implementation) Show the cocone constructed in `buildColimit` is colimiting,
provided the cocones used in its construction are.
-/
def buildIsColimit (t₁ : IsColimit c₁) (t₂ : IsColimit c₂) (hi : IsColimit i) :
    IsColimit (buildColimit s t hs ht i) where
  desc q := by
    refine' hi.desc (Cofork.ofπ _ _)
    -- ⊢ c₂.pt ⟶ q.1
    · refine' t₂.desc (Cofan.mk _ fun j => _)
      -- ⊢ F.obj j ⟶ q.1
      apply q.ι.app j
      -- 🎉 no goals
    · apply t₁.hom_ext
      -- ⊢ ∀ (j : Discrete ((p : J × J) × (p.fst ⟶ p.snd))), NatTrans.app c₁.ι j ≫ s ≫  …
      intro j
      -- ⊢ NatTrans.app c₁.ι j ≫ s ≫ IsColimit.desc t₂ (Cofan.mk q.1 fun j => NatTrans. …
      cases' j with j
      -- ⊢ NatTrans.app c₁.ι { as := j } ≫ s ≫ IsColimit.desc t₂ (Cofan.mk q.1 fun j => …
      have reassoced_s (f : (p : J × J) × (p.fst ⟶ p.snd)) {W : C} (h : _ ⟶ W) :
        c₁.ι.app ⟨f⟩ ≫ s ≫ h = F.map f.snd ≫ c₂.ι.app ⟨f.fst.snd⟩ ≫ h := by
          simp only [← Category.assoc]
          apply eq_whisker (hs f)
      have reassoced_t (f : (p : J × J) × (p.fst ⟶ p.snd)) {W : C} (h : _ ⟶ W) :
        c₁.ι.app ⟨f⟩ ≫ t ≫ h = c₂.ι.app ⟨f.fst.fst⟩ ≫ h := by
          simp only [← Category.assoc]
          apply eq_whisker (ht f)
      simp [reassoced_s, reassoced_t]
      -- 🎉 no goals
  uniq q m w :=
    hi.hom_ext
      (i.coequalizer_ext
        (t₂.hom_ext fun j => by
          cases' j with j
          -- ⊢ NatTrans.app c₂.ι { as := j } ≫ Cofork.π i ≫ m = NatTrans.app c₂.ι { as := j …
          simpa using w j))
                -- 🎉 no goals
          -- 🎉 no goals
  fac s j := by simp
#align category_theory.limits.has_colimit_of_has_coproducts_of_has_coequalizers.build_is_colimit CategoryTheory.Limits.HasColimitOfHasCoproductsOfHasCoequalizers.buildIsColimit

end HasColimitOfHasCoproductsOfHasCoequalizers

open HasColimitOfHasCoproductsOfHasCoequalizers

/-- Given the existence of the appropriate (possibly finite) coproducts and coequalizers,
we can construct a colimit cocone for `F`.
(This assumes the existence of all coequalizers, which is technically stronger than needed.)
-/
noncomputable def colimitCoconeOfCoequalizerAndCoproduct (F : J ⥤ C)
    [HasColimit (Discrete.functor F.obj)]
    [HasColimit (Discrete.functor fun f : Σp : J × J, p.1 ⟶ p.2 => F.obj f.1.1)]
    [HasCoequalizers C] : ColimitCocone F where
  cocone := _
  isColimit :=
    buildIsColimit (Sigma.desc fun f => F.map f.2 ≫ colimit.ι (Discrete.functor F.obj) ⟨f.1.2⟩)
      (Sigma.desc fun f => colimit.ι (Discrete.functor F.obj) ⟨f.1.1⟩) (by simp) (by simp)
                                                                           -- 🎉 no goals
                                                                                     -- 🎉 no goals
      (colimit.isColimit _) (colimit.isColimit _) (colimit.isColimit _)
#align category_theory.limits.colimit_cocone_of_coequalizer_and_coproduct CategoryTheory.Limits.colimitCoconeOfCoequalizerAndCoproduct

/-- Given the existence of the appropriate (possibly finite) coproducts and coequalizers,
we know a colimit of `F` exists.
(This assumes the existence of all coequalizers, which is technically stronger than needed.)
-/
theorem hasColimit_of_coequalizer_and_coproduct (F : J ⥤ C) [HasColimit (Discrete.functor F.obj)]
    [HasColimit (Discrete.functor fun f : Σp : J × J, p.1 ⟶ p.2 => F.obj f.1.1)]
    [HasCoequalizers C] : HasColimit F :=
  HasColimit.mk (colimitCoconeOfCoequalizerAndCoproduct F)
#align category_theory.limits.has_colimit_of_coequalizer_and_coproduct CategoryTheory.Limits.hasColimit_of_coequalizer_and_coproduct

/-- A colimit can be realised as a quotient of a coproduct. -/
noncomputable def colimitQuotientCoproduct [HasColimitsOfSize.{w, w} C] (F : J ⥤ C) :
    ∐ (fun j => F.obj j) ⟶ colimit F :=
  coequalizer.π _ _ ≫ (colimit.isoColimitCocone (colimitCoconeOfCoequalizerAndCoproduct F)).inv
#align category_theory.limits.colimit_quotient_coproduct CategoryTheory.Limits.colimitQuotientCoproduct

instance colimitQuotientCoproduct_epi [HasColimitsOfSize.{w, w} C] (F : J ⥤ C) :
    Epi (colimitQuotientCoproduct F) :=
  epi_comp _ _
#align category_theory.limits.colimit_quotient_coproduct_epi CategoryTheory.Limits.colimitQuotientCoproduct_epi

/-- Any category with coproducts and coequalizers has all colimits.

See <https://stacks.math.columbia.edu/tag/002P>.
-/
theorem has_colimits_of_hasCoequalizers_and_coproducts [HasCoproducts.{w} C] [HasCoequalizers C] :
    HasColimitsOfSize.{w, w} C where
  has_colimits_of_shape := fun _ _ =>
      { has_colimit := fun F => hasColimit_of_coequalizer_and_coproduct F }
#align category_theory.limits.has_colimits_of_has_coequalizers_and_coproducts CategoryTheory.Limits.has_colimits_of_hasCoequalizers_and_coproducts

/-- Any category with finite coproducts and coequalizers has all finite colimits.

See <https://stacks.math.columbia.edu/tag/002Q>.
-/
theorem hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts [HasFiniteCoproducts C]
    [HasCoequalizers C] : HasFiniteColimits C where
  out _ := { has_colimit := fun F => hasColimit_of_coequalizer_and_coproduct F }
#align category_theory.limits.has_finite_colimits_of_has_coequalizers_and_finite_coproducts CategoryTheory.Limits.hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts

-- Porting note: removed and added individually
-- noncomputable section
section

variable [HasColimitsOfShape (Discrete.{w} J) C]
  [HasColimitsOfShape (Discrete.{w} (Σp : J × J, p.1 ⟶ p.2)) C] [HasCoequalizers C]

variable (G : C ⥤ D) [PreservesColimitsOfShape WalkingParallelPair G]
  [PreservesColimitsOfShape (Discrete.{w} J) G]
  [PreservesColimitsOfShape (Discrete.{w} (Σp : J × J, p.1 ⟶ p.2)) G]

/-- If a functor preserves coequalizers and the appropriate coproducts, it preserves colimits. -/
noncomputable def preservesColimitOfPreservesCoequalizersAndCoproduct :
    PreservesColimitsOfShape J G where
  preservesColimit {K} := by
    let P := ∐ K.obj
    -- ⊢ PreservesColimit K G
    let Q := ∐ fun f : Σp : J × J, p.fst ⟶ p.snd => K.obj f.1.1
    -- ⊢ PreservesColimit K G
    let s : Q ⟶ P := Sigma.desc fun f => K.map f.2 ≫ colimit.ι (Discrete.functor K.obj) ⟨_⟩
    -- ⊢ PreservesColimit K G
    let t : Q ⟶ P := Sigma.desc fun f => colimit.ι (Discrete.functor K.obj) ⟨f.1.1⟩
    -- ⊢ PreservesColimit K G
    let I := coequalizer s t
    -- ⊢ PreservesColimit K G
    let i : P ⟶ I := coequalizer.π s t
    -- ⊢ PreservesColimit K G
    apply
      preservesColimitOfPreservesColimitCocone
        (buildIsColimit s t (by simp) (by simp) (colimit.isColimit _) (colimit.isColimit _)
          (colimit.isColimit _))
    refine' IsColimit.ofIsoColimit (buildIsColimit _ _ _ _ _ _ _) _
    · refine Cofan.mk (G.obj Q) fun j => G.map ?_
      -- ⊢ K.obj j.fst.fst ⟶ Q
      apply Sigma.ι _ j
      -- 🎉 no goals
    -- fun j => G.map (Sigma.ι _ j)
    · exact Cofan.mk _ fun f => G.map (Sigma.ι _ f)
      -- 🎉 no goals
    · apply G.map s
      -- 🎉 no goals
    · apply G.map t
      -- 🎉 no goals
    · intro f
      -- ⊢ NatTrans.app (Cofan.mk (G.obj Q) fun j => G.map (Sigma.ι (fun j => K.obj j.f …
      dsimp [Cofan.mk]
      -- ⊢ G.map (Sigma.ι (fun j => K.obj j.fst.fst) f) ≫ G.map (Sigma.desc fun f => K. …
      simp only [← G.map_comp, colimit.ι_desc]
      -- ⊢ G.map (NatTrans.app (Cofan.mk (∐ K.obj) fun f => K.map f.snd ≫ colimit.ι (Di …
      congr
      -- 🎉 no goals
    · intro f
      -- ⊢ NatTrans.app (Cofan.mk (G.obj Q) fun j => G.map (Sigma.ι (fun j => K.obj j.f …
      dsimp [Cofan.mk]
      -- ⊢ G.map (Sigma.ι (fun j => K.obj j.fst.fst) f) ≫ G.map (Sigma.desc fun f => co …
      simp only [← G.map_comp, colimit.ι_desc]
      -- ⊢ G.map (NatTrans.app (Cofan.mk (∐ K.obj) fun f => colimit.ι (Discrete.functor …
      dsimp
      -- 🎉 no goals
    · refine Cofork.ofπ (G.map i) ?_
      -- ⊢ G.map s ≫ G.map i = G.map t ≫ G.map i
      rw [← G.map_comp, ← G.map_comp]
      -- ⊢ G.map (s ≫ i) = G.map (t ≫ i)
      apply congrArg G.map
      -- ⊢ s ≫ i = t ≫ i
      apply coequalizer.condition
      -- 🎉 no goals
    · apply isColimitOfHasCoproductOfPreservesColimit
      -- 🎉 no goals
    · apply isColimitOfHasCoproductOfPreservesColimit
      -- 🎉 no goals
    · apply isColimitCoforkMapOfIsColimit
      -- ⊢ IsColimit (Cofork.ofπ i ?refine'_10.w)
      apply coequalizerIsCoequalizer
      -- 🎉 no goals
    refine' Cocones.ext (Iso.refl _) _
    -- ⊢ ∀ (j : J), NatTrans.app (buildColimit (G.map s) (G.map t) (_ : ∀ (f : (p : J …
    intro j
    -- ⊢ NatTrans.app (buildColimit (G.map s) (G.map t) (_ : ∀ (f : (p : J × J) × (p. …
    dsimp
    -- ⊢ (G.map (Sigma.ι K.obj j) ≫ G.map (coequalizer.π (Sigma.desc fun f => K.map f …
    simp
    -- 🎉 no goals
-- See note [dsimp, simp].
#align category_theory.limits.preserves_colimit_of_preserves_coequalizers_and_coproduct CategoryTheory.Limits.preservesColimitOfPreservesCoequalizersAndCoproduct

end

/- Porting note: the original parameter [∀ (J) [Fintype J], PreservesColimitsOfShape
(Discrete.{0} J) G] triggered the error "invalid parametric local instance, parameter
with type Fintype J does not have forward dependencies, type class resolution cannot use
this kind of local instance because it will not be able to infer a value for this parameter."
Factored out this as new class in `CategoryTheory.Limits.Preserves.Finite` -/
/-- If G preserves coequalizers and finite coproducts, it preserves finite colimits. -/
noncomputable def preservesFiniteColimitsOfPreservesCoequalizersAndFiniteCoproducts
    [HasCoequalizers C] [HasFiniteCoproducts C] (G : C ⥤ D)
    [PreservesColimitsOfShape WalkingParallelPair G]
    [PreservesFiniteCoproducts G] : PreservesFiniteColimits G where
  preservesFiniteColimits := by
    intro J sJ fJ
    -- ⊢ PreservesColimitsOfShape J G
    haveI : Fintype J := inferInstance
    -- ⊢ PreservesColimitsOfShape J G
    haveI : Fintype ((p : J × J) × (p.fst ⟶ p.snd)) := inferInstance
    -- ⊢ PreservesColimitsOfShape J G
    apply @preservesColimitOfPreservesCoequalizersAndCoproduct _ _ _ sJ _ _ ?_ ?_ _ G _ ?_ ?_
    · apply hasColimitsOfShape_discrete _ _
      -- 🎉 no goals
    · apply hasColimitsOfShape_discrete _
      -- 🎉 no goals
    · apply PreservesFiniteCoproducts.preserves _
      -- 🎉 no goals
    · apply PreservesFiniteCoproducts.preserves _
      -- 🎉 no goals
#align category_theory.limits.preserves_finite_colimits_of_preserves_coequalizers_and_finite_coproducts CategoryTheory.Limits.preservesFiniteColimitsOfPreservesCoequalizersAndFiniteCoproducts

/-- If G preserves coequalizers and coproducts, it preserves all colimits. -/
noncomputable def preservesColimitsOfPreservesCoequalizersAndCoproducts [HasCoequalizers C]
    [HasCoproducts.{w} C] (G : C ⥤ D) [PreservesColimitsOfShape WalkingParallelPair G]
    [∀ J, PreservesColimitsOfShape (Discrete.{w} J) G] : PreservesColimitsOfSize.{w} G where
  preservesColimitsOfShape := preservesColimitOfPreservesCoequalizersAndCoproduct G
#align category_theory.limits.preserves_colimits_of_preserves_coequalizers_and_coproducts CategoryTheory.Limits.preservesColimitsOfPreservesCoequalizersAndCoproducts

theorem hasFiniteColimits_of_hasInitial_and_pushouts [HasInitial C] [HasPushouts C] :
    HasFiniteColimits C :=
  @hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts C _
    (@hasFiniteCoproducts_of_has_binary_and_initial C _
      (hasBinaryCoproducts_of_hasInitial_and_pushouts C) inferInstance)
    (@hasCoequalizers_of_hasPushouts_and_binary_coproducts C _
      (hasBinaryCoproducts_of_hasInitial_and_pushouts C) inferInstance)
#align category_theory.limits.has_finite_colimits_of_has_initial_and_pushouts CategoryTheory.Limits.hasFiniteColimits_of_hasInitial_and_pushouts

/-- If G preserves initial objects and pushouts, it preserves all finite colimits. -/
noncomputable def preservesFiniteColimitsOfPreservesInitialAndPushouts [HasInitial C]
    [HasPushouts C] (G : C ⥤ D) [PreservesColimitsOfShape (Discrete.{0} PEmpty) G]
    [PreservesColimitsOfShape WalkingSpan G] : PreservesFiniteColimits G := by
  haveI : HasFiniteColimits C := hasFiniteColimits_of_hasInitial_and_pushouts
  -- ⊢ PreservesFiniteColimits G
  haveI : PreservesColimitsOfShape (Discrete WalkingPair) G :=
    preservesBinaryCoproductsOfPreservesInitialAndPushouts G
  haveI : PreservesColimitsOfShape (WalkingParallelPair) G :=
      (preservesCoequalizersOfPreservesPushoutsAndBinaryCoproducts G)
  refine
    @preservesFiniteColimitsOfPreservesCoequalizersAndFiniteCoproducts _ _ _ _ _ _ G _ ?_
  apply PreservesFiniteCoproducts.mk
  -- ⊢ (J : Type) → [inst : Fintype J] → PreservesColimitsOfShape (Discrete J) G
  apply preservesFiniteCoproductsOfPreservesBinaryAndInitial G
  -- 🎉 no goals
#align category_theory.limits.preserves_finite_colimits_of_preserves_initial_and_pushouts CategoryTheory.Limits.preservesFiniteColimitsOfPreservesInitialAndPushouts

end CategoryTheory.Limits
