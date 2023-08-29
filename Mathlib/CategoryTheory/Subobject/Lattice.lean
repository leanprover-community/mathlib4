/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Scott Morrison
-/
import Mathlib.CategoryTheory.Subobject.FactorThru
import Mathlib.CategoryTheory.Subobject.WellPowered

#align_import category_theory.subobject.lattice from "leanprover-community/mathlib"@"024a4231815538ac739f52d08dd20a55da0d6b23"

/-!
# The lattice of subobjects

We provide the `SemilatticeInf` with `OrderTop (subobject X)` instance when `[HasPullback C]`,
and the `SemilatticeSup (Subobject X)` instance when `[HasImages C] [HasBinaryCoproducts C]`.
-/


universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {X Y Z : C}

variable {D : Type u₂} [Category.{v₂} D]

namespace CategoryTheory

namespace MonoOver

section Top

instance {X : C} : Top (MonoOver X) where top := mk' (𝟙 _)

instance {X : C} : Inhabited (MonoOver X) :=
  ⟨⊤⟩

/-- The morphism to the top object in `MonoOver X`. -/
def leTop (f : MonoOver X) : f ⟶ ⊤ :=
  homMk f.arrow (comp_id _)
#align category_theory.mono_over.le_top CategoryTheory.MonoOver.leTop

@[simp]
theorem top_left (X : C) : ((⊤ : MonoOver X) : C) = X :=
  rfl
#align category_theory.mono_over.top_left CategoryTheory.MonoOver.top_left

@[simp]
theorem top_arrow (X : C) : (⊤ : MonoOver X).arrow = 𝟙 X :=
  rfl
#align category_theory.mono_over.top_arrow CategoryTheory.MonoOver.top_arrow

/-- `map f` sends `⊤ : MonoOver X` to `⟨X, f⟩ : MonoOver Y`. -/
def mapTop (f : X ⟶ Y) [Mono f] : (map f).obj ⊤ ≅ mk' f :=
  iso_of_both_ways (homMk (𝟙 _) rfl) (homMk (𝟙 _) (by simp [id_comp f]))
                                                      -- 🎉 no goals
#align category_theory.mono_over.map_top CategoryTheory.MonoOver.mapTop

section

variable [HasPullbacks C]

/-- The pullback of the top object in `MonoOver Y`
is (isomorphic to) the top object in `MonoOver X`. -/
def pullbackTop (f : X ⟶ Y) : (pullback f).obj ⊤ ≅ ⊤ :=
  iso_of_both_ways (leTop _)
    (homMk (pullback.lift f (𝟙 _) (by aesop_cat)) (pullback.lift_snd _ _ _))
                                      -- 🎉 no goals
#align category_theory.mono_over.pullback_top CategoryTheory.MonoOver.pullbackTop

/-- There is a morphism from `⊤ : MonoOver A` to the pullback of a monomorphism along itself;
as the category is thin this is an isomorphism. -/
def topLEPullbackSelf {A B : C} (f : A ⟶ B) [Mono f] :
    (⊤ : MonoOver A) ⟶ (pullback f).obj (mk' f) :=
  homMk _ (pullback.lift_snd _ _ rfl)
#align category_theory.mono_over.top_le_pullback_self CategoryTheory.MonoOver.topLEPullbackSelf

/-- The pullback of a monomorphism along itself is isomorphic to the top object. -/
def pullbackSelf {A B : C} (f : A ⟶ B) [Mono f] : (pullback f).obj (mk' f) ≅ ⊤ :=
  iso_of_both_ways (leTop _) (topLEPullbackSelf _)
#align category_theory.mono_over.pullback_self CategoryTheory.MonoOver.pullbackSelf

end

end Top

section Bot

variable [HasInitial C] [InitialMonoClass C]

instance {X : C} : Bot (MonoOver X) where bot := mk' (initial.to X)

@[simp]
theorem bot_left (X : C) : ((⊥ : MonoOver X) : C) = ⊥_ C :=
  rfl
#align category_theory.mono_over.bot_left CategoryTheory.MonoOver.bot_left

@[simp]
theorem bot_arrow {X : C} : (⊥ : MonoOver X).arrow = initial.to X :=
  rfl
#align category_theory.mono_over.bot_arrow CategoryTheory.MonoOver.bot_arrow

/-- The (unique) morphism from `⊥ : MonoOver X` to any other `f : MonoOver X`. -/
def botLE {X : C} (f : MonoOver X) : ⊥ ⟶ f :=
  homMk (initial.to _)
#align category_theory.mono_over.bot_le CategoryTheory.MonoOver.botLE

/-- `map f` sends `⊥ : MonoOver X` to `⊥ : MonoOver Y`. -/
def mapBot (f : X ⟶ Y) [Mono f] : (map f).obj ⊥ ≅ ⊥ :=
  iso_of_both_ways (homMk (initial.to _)) (homMk (𝟙 _))
#align category_theory.mono_over.map_bot CategoryTheory.MonoOver.mapBot

end Bot

section ZeroOrderBot

variable [HasZeroObject C]

open ZeroObject

/-- The object underlying `⊥ : Subobject B` is (up to isomorphism) the zero object. -/
def botCoeIsoZero {B : C} : ((⊥ : MonoOver B) : C) ≅ 0 :=
  initialIsInitial.uniqueUpToIso HasZeroObject.zeroIsInitial
#align category_theory.mono_over.bot_coe_iso_zero CategoryTheory.MonoOver.botCoeIsoZero

-- porting note: removed @[simp] as the LHS simplifies
theorem bot_arrow_eq_zero [HasZeroMorphisms C] {B : C} : (⊥ : MonoOver B).arrow = 0 :=
  zero_of_source_iso_zero _ botCoeIsoZero
#align category_theory.mono_over.bot_arrow_eq_zero CategoryTheory.MonoOver.bot_arrow_eq_zero

end ZeroOrderBot

section Inf

variable [HasPullbacks C]

/-- When `[HasPullbacks C]`, `MonoOver A` has "intersections", functorial in both arguments.

As `MonoOver A` is only a preorder, this doesn't satisfy the axioms of `SemilatticeInf`,
but we reuse all the names from `SemilatticeInf` because they will be used to construct
`SemilatticeInf (subobject A)` shortly.
-/
@[simps]
def inf {A : C} : MonoOver A ⥤ MonoOver A ⥤ MonoOver A where
  obj f := pullback f.arrow ⋙ map f.arrow
  map k :=
    { app := fun g => by
        apply homMk _ _
        -- ⊢ (((fun f => pullback (arrow f) ⋙ map (arrow f)) X✝).obj g).obj.left ⟶ (((fun …
        apply pullback.lift pullback.fst (pullback.snd ≫ k.left) _
        -- ⊢ pullback.fst ≫ ((forget A).obj g).hom = (pullback.snd ≫ k.left) ≫ arrow Y✝
        rw [pullback.condition, assoc, w k]
        -- ⊢ pullback.lift pullback.fst (pullback.snd ≫ k.left) (_ : pullback.fst ≫ ((for …
        dsimp
        -- ⊢ pullback.lift pullback.fst (pullback.snd ≫ k.left) (_ : pullback.fst ≫ arrow …
        rw [pullback.lift_snd_assoc, assoc, w k] }
        -- 🎉 no goals
#align category_theory.mono_over.inf CategoryTheory.MonoOver.inf

/-- A morphism from the "infimum" of two objects in `MonoOver A` to the first object. -/
def infLELeft {A : C} (f g : MonoOver A) : (inf.obj f).obj g ⟶ f :=
  homMk _ rfl
#align category_theory.mono_over.inf_le_left CategoryTheory.MonoOver.infLELeft

/-- A morphism from the "infimum" of two objects in `MonoOver A` to the second object. -/
def infLERight {A : C} (f g : MonoOver A) : (inf.obj f).obj g ⟶ g :=
  homMk _ pullback.condition
#align category_theory.mono_over.inf_le_right CategoryTheory.MonoOver.infLERight

/-- A morphism version of the `le_inf` axiom. -/
def leInf {A : C} (f g h : MonoOver A) : (h ⟶ f) → (h ⟶ g) → (h ⟶ (inf.obj f).obj g) := by
  intro k₁ k₂
  -- ⊢ h ⟶ (inf.obj f).obj g
  refine' homMk (pullback.lift k₂.left k₁.left _) _
  -- ⊢ k₂.left ≫ ((forget A).obj g).hom = k₁.left ≫ arrow f
  rw [w k₁, w k₂]
  -- ⊢ pullback.lift k₂.left k₁.left (_ : k₂.left ≫ ((forget A).obj g).hom = k₁.lef …
  erw [pullback.lift_snd_assoc, w k₁]
  -- 🎉 no goals
#align category_theory.mono_over.le_inf CategoryTheory.MonoOver.leInf

end Inf

section Sup

variable [HasImages C] [HasBinaryCoproducts C]

/-- When `[HasImages C] [HasBinaryCoproducts C]`, `MonoOver A` has a `sup` construction,
which is functorial in both arguments,
and which on `Subobject A` will induce a `SemilatticeSup`. -/
def sup {A : C} : MonoOver A ⥤ MonoOver A ⥤ MonoOver A :=
  curryObj ((forget A).prod (forget A) ⋙ uncurry.obj Over.coprod ⋙ image)
#align category_theory.mono_over.sup CategoryTheory.MonoOver.sup

/-- A morphism version of `le_sup_left`. -/
def leSupLeft {A : C} (f g : MonoOver A) : f ⟶ (sup.obj f).obj g := by
  refine' homMk (coprod.inl ≫ factorThruImage _) _
  -- ⊢ (coprod.inl ≫ factorThruImage ((uncurry.obj Over.coprod).obj ((Functor.prod  …
  erw [Category.assoc, image.fac, coprod.inl_desc]
  -- ⊢ ((Functor.prod (forget A) (forget A)).obj (f, g)).fst.hom = arrow f
  rfl
  -- 🎉 no goals
#align category_theory.mono_over.le_sup_left CategoryTheory.MonoOver.leSupLeft

/-- A morphism version of `le_sup_right`. -/
def leSupRight {A : C} (f g : MonoOver A) : g ⟶ (sup.obj f).obj g := by
  refine' homMk (coprod.inr ≫ factorThruImage _) _
  -- ⊢ (coprod.inr ≫ factorThruImage ((uncurry.obj Over.coprod).obj ((Functor.prod  …
  erw [Category.assoc, image.fac, coprod.inr_desc]
  -- ⊢ ((Functor.prod (forget A) (forget A)).obj (f, g)).snd.hom = arrow g
  rfl
  -- 🎉 no goals
#align category_theory.mono_over.le_sup_right CategoryTheory.MonoOver.leSupRight

/-- A morphism version of `sup_le`. -/
def supLe {A : C} (f g h : MonoOver A) : (f ⟶ h) → (g ⟶ h) → ((sup.obj f).obj g ⟶ h) := by
  intro k₁ k₂
  -- ⊢ (sup.obj f).obj g ⟶ h
  refine' homMk _ _
  -- ⊢ ((sup.obj f).obj g).obj.left ⟶ h.obj.left
  apply image.lift ⟨_, h.arrow, coprod.desc k₁.left k₂.left, _⟩
  -- ⊢ coprod.desc k₁.left k₂.left ≫ arrow h = ((uncurry.obj Over.coprod).obj ((Fun …
  · ext
    -- ⊢ coprod.inl ≫ coprod.desc k₁.left k₂.left ≫ arrow h = coprod.inl ≫ ((uncurry. …
    · simp [w k₁]
      -- 🎉 no goals
    · simp [w k₂]
      -- 🎉 no goals
  · apply image.lift_fac
    -- 🎉 no goals
#align category_theory.mono_over.sup_le CategoryTheory.MonoOver.supLe

end Sup

end MonoOver

namespace Subobject

section OrderTop

instance orderTop {X : C} : OrderTop (Subobject X) where
  top := Quotient.mk'' ⊤
  le_top := by
    refine' Quotient.ind' fun f => _
    -- ⊢ Quotient.mk'' f ≤ ⊤
    exact ⟨MonoOver.leTop f⟩
    -- 🎉 no goals
#align category_theory.subobject.order_top CategoryTheory.Subobject.orderTop

instance {X : C} : Inhabited (Subobject X) :=
  ⟨⊤⟩

theorem top_eq_id (B : C) : (⊤ : Subobject B) = Subobject.mk (𝟙 B) :=
  rfl
#align category_theory.subobject.top_eq_id CategoryTheory.Subobject.top_eq_id

theorem underlyingIso_top_hom {B : C} : (underlyingIso (𝟙 B)).hom = (⊤ : Subobject B).arrow := by
  convert underlyingIso_hom_comp_eq_mk (𝟙 B)
  -- ⊢ (underlyingIso (𝟙 B)).hom = (underlyingIso (𝟙 B)).hom ≫ 𝟙 B
  simp only [comp_id]
  -- 🎉 no goals
#align category_theory.subobject.underlying_iso_top_hom CategoryTheory.Subobject.underlyingIso_top_hom

instance top_arrow_isIso {B : C} : IsIso (⊤ : Subobject B).arrow := by
  rw [← underlyingIso_top_hom]
  -- ⊢ IsIso (underlyingIso (𝟙 B)).hom
  infer_instance
  -- 🎉 no goals
#align category_theory.subobject.top_arrow_is_iso CategoryTheory.Subobject.top_arrow_isIso

@[reassoc (attr := simp)]
theorem underlyingIso_inv_top_arrow {B : C} :
    (underlyingIso _).inv ≫ (⊤ : Subobject B).arrow = 𝟙 B :=
  underlyingIso_arrow _
#align category_theory.subobject.underlying_iso_inv_top_arrow CategoryTheory.Subobject.underlyingIso_inv_top_arrow

@[simp]
theorem map_top (f : X ⟶ Y) [Mono f] : (map f).obj ⊤ = Subobject.mk f :=
  Quotient.sound' ⟨MonoOver.mapTop f⟩
#align category_theory.subobject.map_top CategoryTheory.Subobject.map_top

theorem top_factors {A B : C} (f : A ⟶ B) : (⊤ : Subobject B).Factors f :=
  ⟨f, comp_id _⟩
#align category_theory.subobject.top_factors CategoryTheory.Subobject.top_factors

theorem isIso_iff_mk_eq_top {X Y : C} (f : X ⟶ Y) [Mono f] : IsIso f ↔ mk f = ⊤ :=
  ⟨fun _ => mk_eq_mk_of_comm _ _ (asIso f) (Category.comp_id _), fun h => by
    rw [← ofMkLEMk_comp h.le, Category.comp_id]
    -- ⊢ IsIso (ofMkLEMk f (𝟙 Y) (_ : mk f ≤ ⊤))
    exact IsIso.of_iso (isoOfMkEqMk _ _ h)⟩
    -- 🎉 no goals
#align category_theory.subobject.is_iso_iff_mk_eq_top CategoryTheory.Subobject.isIso_iff_mk_eq_top

theorem isIso_arrow_iff_eq_top {Y : C} (P : Subobject Y) : IsIso P.arrow ↔ P = ⊤ := by
  rw [isIso_iff_mk_eq_top, mk_arrow]
  -- 🎉 no goals
#align category_theory.subobject.is_iso_arrow_iff_eq_top CategoryTheory.Subobject.isIso_arrow_iff_eq_top

instance isIso_top_arrow {Y : C} : IsIso (⊤ : Subobject Y).arrow := by rw [isIso_arrow_iff_eq_top]
                                                                       -- 🎉 no goals
#align category_theory.subobject.is_iso_top_arrow CategoryTheory.Subobject.isIso_top_arrow

theorem mk_eq_top_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : mk f = ⊤ :=
  (isIso_iff_mk_eq_top f).mp inferInstance
#align category_theory.subobject.mk_eq_top_of_is_iso CategoryTheory.Subobject.mk_eq_top_of_isIso

theorem eq_top_of_isIso_arrow {Y : C} (P : Subobject Y) [IsIso P.arrow] : P = ⊤ :=
  (isIso_arrow_iff_eq_top P).mp inferInstance
#align category_theory.subobject.eq_top_of_is_iso_arrow CategoryTheory.Subobject.eq_top_of_isIso_arrow

section

variable [HasPullbacks C]

theorem pullback_top (f : X ⟶ Y) : (pullback f).obj ⊤ = ⊤ :=
  Quotient.sound' ⟨MonoOver.pullbackTop f⟩
#align category_theory.subobject.pullback_top CategoryTheory.Subobject.pullback_top

theorem pullback_self {A B : C} (f : A ⟶ B) [Mono f] : (pullback f).obj (mk f) = ⊤ :=
  Quotient.sound' ⟨MonoOver.pullbackSelf f⟩
#align category_theory.subobject.pullback_self CategoryTheory.Subobject.pullback_self

end

end OrderTop

section OrderBot

variable [HasInitial C] [InitialMonoClass C]

instance orderBot {X : C} : OrderBot (Subobject X) where
  bot := Quotient.mk'' ⊥
  bot_le := by
    refine' Quotient.ind' fun f => _
    -- ⊢ ⊥ ≤ Quotient.mk'' f
    exact ⟨MonoOver.botLE f⟩
    -- 🎉 no goals
#align category_theory.subobject.order_bot CategoryTheory.Subobject.orderBot

theorem bot_eq_initial_to {B : C} : (⊥ : Subobject B) = Subobject.mk (initial.to B) :=
  rfl
#align category_theory.subobject.bot_eq_initial_to CategoryTheory.Subobject.bot_eq_initial_to

/-- The object underlying `⊥ : Subobject B` is (up to isomorphism) the initial object. -/
def botCoeIsoInitial {B : C} : ((⊥ : Subobject B) : C) ≅ ⊥_ C :=
  underlyingIso _
#align category_theory.subobject.bot_coe_iso_initial CategoryTheory.Subobject.botCoeIsoInitial

theorem map_bot (f : X ⟶ Y) [Mono f] : (map f).obj ⊥ = ⊥ :=
  Quotient.sound' ⟨MonoOver.mapBot f⟩
#align category_theory.subobject.map_bot CategoryTheory.Subobject.map_bot

end OrderBot

section ZeroOrderBot

variable [HasZeroObject C]

open ZeroObject

/-- The object underlying `⊥ : Subobject B` is (up to isomorphism) the zero object. -/
def botCoeIsoZero {B : C} : ((⊥ : Subobject B) : C) ≅ 0 :=
  botCoeIsoInitial ≪≫ initialIsInitial.uniqueUpToIso HasZeroObject.zeroIsInitial
#align category_theory.subobject.bot_coe_iso_zero CategoryTheory.Subobject.botCoeIsoZero

variable [HasZeroMorphisms C]

theorem bot_eq_zero {B : C} : (⊥ : Subobject B) = Subobject.mk (0 : 0 ⟶ B) :=
  mk_eq_mk_of_comm _ _ (initialIsInitial.uniqueUpToIso HasZeroObject.zeroIsInitial) (by simp)
                                                                                        -- 🎉 no goals
#align category_theory.subobject.bot_eq_zero CategoryTheory.Subobject.bot_eq_zero

@[simp]
theorem bot_arrow {B : C} : (⊥ : Subobject B).arrow = 0 :=
  zero_of_source_iso_zero _ botCoeIsoZero
#align category_theory.subobject.bot_arrow CategoryTheory.Subobject.bot_arrow

theorem bot_factors_iff_zero {A B : C} (f : A ⟶ B) : (⊥ : Subobject B).Factors f ↔ f = 0 :=
  ⟨by
    rintro ⟨h, rfl⟩
    -- ⊢ h ≫ MonoOver.arrow ⊥ = 0
    simp only [MonoOver.bot_arrow_eq_zero, Functor.id_obj, Functor.const_obj_obj,
      MonoOver.bot_left, comp_zero],
   by
    rintro rfl
    -- ⊢ Factors ⊥ 0
    exact ⟨0, by simp⟩⟩
    -- 🎉 no goals
#align category_theory.subobject.bot_factors_iff_zero CategoryTheory.Subobject.bot_factors_iff_zero

theorem mk_eq_bot_iff_zero {f : X ⟶ Y} [Mono f] : Subobject.mk f = ⊥ ↔ f = 0 :=
  ⟨fun h => by simpa [h, bot_factors_iff_zero] using mk_factors_self f, fun h =>
               -- 🎉 no goals
    mk_eq_mk_of_comm _ _ ((isoZeroOfMonoEqZero h).trans HasZeroObject.zeroIsoInitial) (by simp [h])⟩
                                                                                          -- 🎉 no goals
#align category_theory.subobject.mk_eq_bot_iff_zero CategoryTheory.Subobject.mk_eq_bot_iff_zero

end ZeroOrderBot

section Functor

variable (C)

/-- Sending `X : C` to `Subobject X` is a contravariant functor `Cᵒᵖ ⥤ Type`. -/
@[simps]
def functor [HasPullbacks C] : Cᵒᵖ ⥤ Type max u₁ v₁ where
  obj X := Subobject X.unop
  map f := (pullback f.unop).obj
  map_id _ := funext pullback_id
  map_comp _ _ := funext (pullback_comp _ _)
#align category_theory.subobject.functor CategoryTheory.Subobject.functor

end Functor

section SemilatticeInfTop

variable [HasPullbacks C]

/-- The functorial infimum on `MonoOver A` descends to an infimum on `Subobject A`. -/
def inf {A : C} : Subobject A ⥤ Subobject A ⥤ Subobject A :=
  ThinSkeleton.map₂ MonoOver.inf
#align category_theory.subobject.inf CategoryTheory.Subobject.inf

theorem inf_le_left {A : C} (f g : Subobject A) : (inf.obj f).obj g ≤ f :=
  Quotient.inductionOn₂' f g fun _ _ => ⟨MonoOver.infLELeft _ _⟩
#align category_theory.subobject.inf_le_left CategoryTheory.Subobject.inf_le_left

theorem inf_le_right {A : C} (f g : Subobject A) : (inf.obj f).obj g ≤ g :=
  Quotient.inductionOn₂' f g fun _ _ => ⟨MonoOver.infLERight _ _⟩
#align category_theory.subobject.inf_le_right CategoryTheory.Subobject.inf_le_right

theorem le_inf {A : C} (h f g : Subobject A) : h ≤ f → h ≤ g → h ≤ (inf.obj f).obj g :=
  Quotient.inductionOn₃' h f g
    (by
      rintro f g h ⟨k⟩ ⟨l⟩
      -- ⊢ Quotient.mk'' f ≤ (inf.obj (Quotient.mk'' g)).obj (Quotient.mk'' h)
      exact ⟨MonoOver.leInf _ _ _ k l⟩)
      -- 🎉 no goals
#align category_theory.subobject.le_inf CategoryTheory.Subobject.le_inf

instance semilatticeInf {B : C} : SemilatticeInf (Subobject B) where
  inf := fun m n => (inf.obj m).obj n
  inf_le_left := inf_le_left
  inf_le_right := inf_le_right
  le_inf := le_inf

theorem factors_left_of_inf_factors {A B : C} {X Y : Subobject B} {f : A ⟶ B}
    (h : (X ⊓ Y).Factors f) : X.Factors f :=
  factors_of_le _ (inf_le_left _ _) h
#align category_theory.subobject.factors_left_of_inf_factors CategoryTheory.Subobject.factors_left_of_inf_factors

theorem factors_right_of_inf_factors {A B : C} {X Y : Subobject B} {f : A ⟶ B}
    (h : (X ⊓ Y).Factors f) : Y.Factors f :=
  factors_of_le _ (inf_le_right _ _) h
#align category_theory.subobject.factors_right_of_inf_factors CategoryTheory.Subobject.factors_right_of_inf_factors

@[simp]
theorem inf_factors {A B : C} {X Y : Subobject B} (f : A ⟶ B) :
    (X ⊓ Y).Factors f ↔ X.Factors f ∧ Y.Factors f :=
  ⟨fun h => ⟨factors_left_of_inf_factors h, factors_right_of_inf_factors h⟩, by
    revert X Y
    -- ⊢ ∀ {X Y : Subobject B}, Factors X f ∧ Factors Y f → Factors (X ⊓ Y) f
    apply Quotient.ind₂'
    -- ⊢ ∀ (a₁ a₂ : MonoOver B), Factors (Quotient.mk'' a₁) f ∧ Factors (Quotient.mk' …
    rintro X Y ⟨⟨g₁, rfl⟩, ⟨g₂, hg₂⟩⟩
    -- ⊢ Factors (Quotient.mk'' X ⊓ Quotient.mk'' Y) (g₁ ≫ MonoOver.arrow X)
    exact ⟨_, pullback.lift_snd_assoc _ _ hg₂ _⟩⟩
    -- 🎉 no goals
#align category_theory.subobject.inf_factors CategoryTheory.Subobject.inf_factors

theorem inf_arrow_factors_left {B : C} (X Y : Subobject B) : X.Factors (X ⊓ Y).arrow :=
  (factors_iff _ _).mpr ⟨ofLE (X ⊓ Y) X (inf_le_left X Y), by simp⟩
                                                              -- 🎉 no goals
#align category_theory.subobject.inf_arrow_factors_left CategoryTheory.Subobject.inf_arrow_factors_left

theorem inf_arrow_factors_right {B : C} (X Y : Subobject B) : Y.Factors (X ⊓ Y).arrow :=
  (factors_iff _ _).mpr ⟨ofLE (X ⊓ Y) Y (inf_le_right X Y), by simp⟩
                                                               -- 🎉 no goals
#align category_theory.subobject.inf_arrow_factors_right CategoryTheory.Subobject.inf_arrow_factors_right

@[simp]
theorem finset_inf_factors {I : Type*} {A B : C} {s : Finset I} {P : I → Subobject B} (f : A ⟶ B) :
    (s.inf P).Factors f ↔ ∀ i ∈ s, (P i).Factors f := by
  classical
  induction' s using Finset.induction_on with _ _ _ ih
  · simp [top_factors]
  · simp [ih]
#align category_theory.subobject.finset_inf_factors CategoryTheory.Subobject.finset_inf_factors

-- `i` is explicit here because often we'd like to defer a proof of `m`
theorem finset_inf_arrow_factors {I : Type*} {B : C} (s : Finset I) (P : I → Subobject B) (i : I)
    (m : i ∈ s) : (P i).Factors (s.inf P).arrow := by
  classical
  revert i m
  induction' s using Finset.induction_on with _ _ _ ih
  · rintro _ ⟨⟩
  · intro _ m
    rw [Finset.inf_insert]
    simp only [Finset.mem_insert] at m
    rcases m with (rfl | m)
    · rw [← factorThru_arrow _ _ (inf_arrow_factors_left _ _)]
      exact factors_comp_arrow _
    · rw [← factorThru_arrow _ _ (inf_arrow_factors_right _ _)]
      apply factors_of_factors_right
      exact ih _ m
#align category_theory.subobject.finset_inf_arrow_factors CategoryTheory.Subobject.finset_inf_arrow_factors

theorem inf_eq_map_pullback' {A : C} (f₁ : MonoOver A) (f₂ : Subobject A) :
    (Subobject.inf.obj (Quotient.mk'' f₁)).obj f₂ =
      (Subobject.map f₁.arrow).obj ((Subobject.pullback f₁.arrow).obj f₂) := by
  induction' f₂ using Quotient.inductionOn' with f₂
  -- ⊢ (inf.obj (Quotient.mk'' f₁)).obj (Quotient.mk'' f₂) = (map (MonoOver.arrow f …
  rfl
  -- 🎉 no goals
#align category_theory.subobject.inf_eq_map_pullback' CategoryTheory.Subobject.inf_eq_map_pullback'

theorem inf_eq_map_pullback {A : C} (f₁ : MonoOver A) (f₂ : Subobject A) :
    (Quotient.mk'' f₁ ⊓ f₂ : Subobject A) = (map f₁.arrow).obj ((pullback f₁.arrow).obj f₂) :=
  inf_eq_map_pullback' f₁ f₂
#align category_theory.subobject.inf_eq_map_pullback CategoryTheory.Subobject.inf_eq_map_pullback

theorem prod_eq_inf {A : C} {f₁ f₂ : Subobject A} [HasBinaryProduct f₁ f₂] :
    (f₁ ⨯ f₂) = f₁ ⊓ f₂ := by
  apply le_antisymm
  -- ⊢ (f₁ ⨯ f₂) ≤ f₁ ⊓ f₂
  · refine' le_inf _ _ _ (Limits.prod.fst.le) (Limits.prod.snd.le)
    -- 🎉 no goals
  · apply leOfHom
    -- ⊢ f₁ ⊓ f₂ ⟶ f₁ ⨯ f₂
    exact prod.lift (inf_le_left _ _).hom (inf_le_right _ _).hom
    -- 🎉 no goals
#align category_theory.subobject.prod_eq_inf CategoryTheory.Subobject.prod_eq_inf

theorem inf_def {B : C} (m m' : Subobject B) : m ⊓ m' = (inf.obj m).obj m' :=
  rfl
#align category_theory.subobject.inf_def CategoryTheory.Subobject.inf_def

/-- `⊓` commutes with pullback. -/
theorem inf_pullback {X Y : C} (g : X ⟶ Y) (f₁ f₂) :
    (pullback g).obj (f₁ ⊓ f₂) = (pullback g).obj f₁ ⊓ (pullback g).obj f₂ := by
  revert f₁
  -- ⊢ ∀ (f₁ : Subobject Y), (pullback g).obj (f₁ ⊓ f₂) = (pullback g).obj f₁ ⊓ (pu …
  apply Quotient.ind'
  -- ⊢ ∀ (a : MonoOver Y), (pullback g).obj (Quotient.mk'' a ⊓ f₂) = (pullback g).o …
  intro f₁
  -- ⊢ (pullback g).obj (Quotient.mk'' f₁ ⊓ f₂) = (pullback g).obj (Quotient.mk'' f …
  erw [inf_def, inf_def, inf_eq_map_pullback', inf_eq_map_pullback', ← pullback_comp, ←
    map_pullback pullback.condition (pullbackIsPullback f₁.arrow g), ← pullback_comp,
    pullback.condition]
  rfl
  -- 🎉 no goals
#align category_theory.subobject.inf_pullback CategoryTheory.Subobject.inf_pullback

/-- `⊓` commutes with map. -/
theorem inf_map {X Y : C} (g : Y ⟶ X) [Mono g] (f₁ f₂) :
    (map g).obj (f₁ ⊓ f₂) = (map g).obj f₁ ⊓ (map g).obj f₂ := by
  revert f₁
  -- ⊢ ∀ (f₁ : Subobject Y), (map g).obj (f₁ ⊓ f₂) = (map g).obj f₁ ⊓ (map g).obj f₂
  apply Quotient.ind'
  -- ⊢ ∀ (a : MonoOver Y), (map g).obj (Quotient.mk'' a ⊓ f₂) = (map g).obj (Quotie …
  intro f₁
  -- ⊢ (map g).obj (Quotient.mk'' f₁ ⊓ f₂) = (map g).obj (Quotient.mk'' f₁) ⊓ (map  …
  erw [inf_def, inf_def, inf_eq_map_pullback', inf_eq_map_pullback', ← map_comp]
  -- ⊢ (map (MonoOver.arrow f₁ ≫ g)).obj ((pullback (MonoOver.arrow f₁)).obj f₂) =  …
  dsimp
  -- ⊢ (map (MonoOver.arrow f₁ ≫ g)).obj ((pullback (MonoOver.arrow f₁)).obj f₂) =  …
  rw [pullback_comp, pullback_map_self]
  -- 🎉 no goals
#align category_theory.subobject.inf_map CategoryTheory.Subobject.inf_map

end SemilatticeInfTop

section SemilatticeSup

variable [HasImages C] [HasBinaryCoproducts C]

/-- The functorial supremum on `MonoOver A` descends to a supremum on `Subobject A`. -/
def sup {A : C} : Subobject A ⥤ Subobject A ⥤ Subobject A :=
  ThinSkeleton.map₂ MonoOver.sup
#align category_theory.subobject.sup CategoryTheory.Subobject.sup

instance semilatticeSup {B : C} : SemilatticeSup (Subobject B) where
  sup := fun m n => (sup.obj m).obj n
  le_sup_left := fun m n => Quotient.inductionOn₂' m n fun _ _ => ⟨MonoOver.leSupLeft _ _⟩
  le_sup_right := fun m n => Quotient.inductionOn₂' m n fun _ _ => ⟨MonoOver.leSupRight _ _⟩
  sup_le := fun m n k =>
    Quotient.inductionOn₃' m n k fun _ _ _ ⟨i⟩ ⟨j⟩ => ⟨MonoOver.supLe _ _ _ i j⟩

theorem sup_factors_of_factors_left {A B : C} {X Y : Subobject B} {f : A ⟶ B} (P : X.Factors f) :
    (X ⊔ Y).Factors f :=
  factors_of_le f le_sup_left P
#align category_theory.subobject.sup_factors_of_factors_left CategoryTheory.Subobject.sup_factors_of_factors_left

theorem sup_factors_of_factors_right {A B : C} {X Y : Subobject B} {f : A ⟶ B} (P : Y.Factors f) :
    (X ⊔ Y).Factors f :=
  factors_of_le f le_sup_right P
#align category_theory.subobject.sup_factors_of_factors_right CategoryTheory.Subobject.sup_factors_of_factors_right

variable [HasInitial C] [InitialMonoClass C]

theorem finset_sup_factors {I : Type*} {A B : C} {s : Finset I} {P : I → Subobject B} {f : A ⟶ B}
    (h : ∃ i ∈ s, (P i).Factors f) : (s.sup P).Factors f := by
  classical
  revert h
  induction' s using Finset.induction_on with _ _ _ ih
  · rintro ⟨_, ⟨⟨⟩, _⟩⟩
  · rintro ⟨j, ⟨m, h⟩⟩
    simp only [Finset.sup_insert]
    simp at m
    rcases m with (rfl | m)
    · exact sup_factors_of_factors_left h
    · exact sup_factors_of_factors_right (ih ⟨j, ⟨m, h⟩⟩)
#align category_theory.subobject.finset_sup_factors CategoryTheory.Subobject.finset_sup_factors

end SemilatticeSup

section Lattice

instance boundedOrder [HasInitial C] [InitialMonoClass C] {B : C} : BoundedOrder (Subobject B) :=
  { Subobject.orderTop, Subobject.orderBot with }

variable [HasPullbacks C] [HasImages C] [HasBinaryCoproducts C]

instance {B : C} : Lattice (Subobject B) :=
  { Subobject.semilatticeInf, Subobject.semilatticeSup with }

end Lattice

section Inf

variable [WellPowered C]

/-- The "wide cospan" diagram, with a small indexing type, constructed from a set of subobjects.
(This is just the diagram of all the subobjects pasted together, but using `WellPowered C`
to make the diagram small.)
-/
def wideCospan {A : C} (s : Set (Subobject A)) : WidePullbackShape (equivShrink _ '' s) ⥤ C :=
  WidePullbackShape.wideCospan A
    (fun j : equivShrink _ '' s => ((equivShrink (Subobject A)).symm j : C)) fun j =>
    ((equivShrink (Subobject A)).symm j).arrow
#align category_theory.subobject.wide_cospan CategoryTheory.Subobject.wideCospan

@[simp]
theorem wideCospan_map_term {A : C} (s : Set (Subobject A)) (j) :
    (wideCospan s).map (WidePullbackShape.Hom.term j) =
      ((equivShrink (Subobject A)).symm j).arrow :=
  rfl
#align category_theory.subobject.wide_cospan_map_term CategoryTheory.Subobject.wideCospan_map_term

/-- Auxiliary construction of a cone for `le_inf`. -/
def leInfCone {A : C} (s : Set (Subobject A)) (f : Subobject A) (k : ∀ g ∈ s, f ≤ g) :
    Cone (wideCospan s) :=
  WidePullbackShape.mkCone f.arrow
    (fun j =>
      underlying.map
        (homOfLE
          (k _
            (by
              rcases j with ⟨-, ⟨g, ⟨m, rfl⟩⟩⟩
              -- ⊢ ↑(equivShrink (Subobject A)).symm ↑{ val := ↑(equivShrink (Subobject A)) g,  …
              simpa using m))))
              -- 🎉 no goals
    (by aesop_cat)
        -- 🎉 no goals
#align category_theory.subobject.le_Inf_cone CategoryTheory.Subobject.leInfCone

@[simp]
theorem leInfCone_π_app_none {A : C} (s : Set (Subobject A)) (f : Subobject A)
    (k : ∀ g ∈ s, f ≤ g) : (leInfCone s f k).π.app none = f.arrow :=
  rfl
#align category_theory.subobject.le_Inf_cone_π_app_none CategoryTheory.Subobject.leInfCone_π_app_none

variable [HasWidePullbacks.{v₁} C]

/-- The limit of `wideCospan s`. (This will be the supremum of the set of subobjects.)
-/
def widePullback {A : C} (s : Set (Subobject A)) : C :=
  Limits.limit (wideCospan s)
#align category_theory.subobject.wide_pullback CategoryTheory.Subobject.widePullback

/-- The inclusion map from `widePullback s` to `A`
-/
def widePullbackι {A : C} (s : Set (Subobject A)) : widePullback s ⟶ A :=
  Limits.limit.π (wideCospan s) none
#align category_theory.subobject.wide_pullback_ι CategoryTheory.Subobject.widePullbackι

instance widePullbackι_mono {A : C} (s : Set (Subobject A)) : Mono (widePullbackι s) :=
  ⟨fun u v h =>
    limit.hom_ext fun j => by
      cases j
      -- ⊢ u ≫ limit.π (wideCospan s) none = v ≫ limit.π (wideCospan s) none
      · exact h
        -- 🎉 no goals
      · apply (cancel_mono ((equivShrink (Subobject A)).symm _).arrow).1
        -- ⊢ (u ≫ limit.π (wideCospan s) (some val✝)) ≫ arrow (↑(equivShrink (Subobject A …
        rw [assoc, assoc]
        -- ⊢ u ≫ limit.π (wideCospan s) (some val✝) ≫ arrow (↑(equivShrink (Subobject A)) …
        erw [limit.w (wideCospan s) (WidePullbackShape.Hom.term _)]
        -- ⊢ u ≫ limit.π (wideCospan s) none = v ≫ limit.π (wideCospan s) none
        exact h⟩
        -- 🎉 no goals
#align category_theory.subobject.wide_pullback_ι_mono CategoryTheory.Subobject.widePullbackι_mono

/-- When `[WellPowered C]` and `[HasWidePullbacks C]`, `Subobject A` has arbitrary infimums.
-/
def sInf {A : C} (s : Set (Subobject A)) : Subobject A :=
  Subobject.mk (widePullbackι s)
#align category_theory.subobject.Inf CategoryTheory.Subobject.sInf

theorem sInf_le {A : C} (s : Set (Subobject A)) (f) (hf : f ∈ s) : sInf s ≤ f := by
  fapply le_of_comm
  -- ⊢ underlying.obj (sInf s) ⟶ underlying.obj f
  · exact (underlyingIso _).hom ≫
      Limits.limit.π (wideCospan s)
        (some ⟨equivShrink (Subobject A) f,
          Set.mem_image_of_mem (equivShrink (Subobject A)) hf⟩) ≫
      eqToHom (congr_arg (fun X : Subobject A => (X : C)) (Equiv.symm_apply_apply _ _))
  · dsimp [sInf]
    -- ⊢ ((underlyingIso (widePullbackι s)).hom ≫ limit.π (wideCospan s) (some { val  …
    simp only [Category.comp_id, Category.assoc, ← underlyingIso_hom_comp_eq_mk,
      Subobject.arrow_congr, congrArg_mpr_hom_left, Iso.cancel_iso_hom_left]
    convert limit.w (wideCospan s) (WidePullbackShape.Hom.term _)
    -- ⊢ eqToHom (_ : underlying.obj (↑(equivShrink (Subobject A)).symm (↑(equivShrin …
    aesop_cat
    -- 🎉 no goals
#align category_theory.subobject.Inf_le CategoryTheory.Subobject.sInf_le

theorem le_sInf {A : C} (s : Set (Subobject A)) (f : Subobject A) (k : ∀ g ∈ s, f ≤ g) :
    f ≤ sInf s := by
  fapply le_of_comm
  -- ⊢ underlying.obj f ⟶ underlying.obj (sInf s)
  · exact Limits.limit.lift _ (leInfCone s f k) ≫ (underlyingIso _).inv
    -- 🎉 no goals
  · dsimp [sInf]
    -- ⊢ (limit.lift (wideCospan s) (leInfCone s f k) ≫ (underlyingIso (widePullbackι …
    rw [assoc, underlyingIso_arrow, widePullbackι, limit.lift_π, leInfCone_π_app_none]
    -- 🎉 no goals
#align category_theory.subobject.le_Inf CategoryTheory.Subobject.le_inf

instance completeSemilatticeInf {B : C} : CompleteSemilatticeInf (Subobject B) where
  sInf := sInf
  sInf_le := sInf_le
  le_sInf := le_sInf

end Inf

section Sup

variable [WellPowered C] [HasCoproducts.{v₁} C]

/-- The universal morphism out of the coproduct of a set of subobjects,
after using `[WellPowered C]` to reindex by a small type.
-/
def smallCoproductDesc {A : C} (s : Set (Subobject A)) :=
  Limits.Sigma.desc fun j : equivShrink _ '' s => ((equivShrink (Subobject A)).symm j).arrow
#align category_theory.subobject.small_coproduct_desc CategoryTheory.Subobject.smallCoproductDesc

variable [HasImages C]

/-- When `[WellPowered C] [HasImages C] [HasCoproducts C]`,
`Subobject A` has arbitrary supremums. -/
def sSup {A : C} (s : Set (Subobject A)) : Subobject A :=
  Subobject.mk (image.ι (smallCoproductDesc s))
#align category_theory.subobject.Sup CategoryTheory.Subobject.sup

theorem le_sSup {A : C} (s : Set (Subobject A)) (f) (hf : f ∈ s) : f ≤ sSup s := by
  fapply le_of_comm
  -- ⊢ underlying.obj f ⟶ underlying.obj (sSup s)
  · refine' eqToHom _ ≫ Sigma.ι _ ⟨equivShrink (Subobject A) f, by simpa [Set.mem_image] using hf⟩
      ≫ factorThruImage _ ≫ (underlyingIso _).inv
    exact (congr_arg (fun X : Subobject A => (X : C)) (Equiv.symm_apply_apply _ _).symm)
    -- 🎉 no goals
  · simp [sSup, smallCoproductDesc]
    -- 🎉 no goals
#align category_theory.subobject.le_Sup CategoryTheory.Subobject.le_sSup

theorem symm_apply_mem_iff_mem_image {α β : Type*} (e : α ≃ β) (s : Set α) (x : β) :
    e.symm x ∈ s ↔ x ∈ e '' s :=
  ⟨fun h => ⟨e.symm x, h, by simp⟩, by
                             -- 🎉 no goals
    rintro ⟨a, m, rfl⟩
    -- ⊢ ↑e.symm (↑e a) ∈ s
    simpa using m⟩
    -- 🎉 no goals
#align category_theory.subobject.symm_apply_mem_iff_mem_image CategoryTheory.Subobject.symm_apply_mem_iff_mem_image

theorem sSup_le {A : C} (s : Set (Subobject A)) (f : Subobject A) (k : ∀ g ∈ s, g ≤ f) :
    sSup s ≤ f := by
  fapply le_of_comm
  -- ⊢ underlying.obj (sSup s) ⟶ underlying.obj f
  · refine'(underlyingIso _).hom ≫ image.lift ⟨_, f.arrow, _, _⟩
    -- ⊢ (∐ fun j => underlying.obj (↑(equivShrink (Subobject A)).symm ↑j)) ⟶ underly …
    · refine' Sigma.desc _
      -- ⊢ (b : ↑(↑(equivShrink (Subobject A)) '' s)) → underlying.obj (↑(equivShrink ( …
      rintro ⟨g, m⟩
      -- ⊢ underlying.obj (↑(equivShrink (Subobject A)).symm ↑{ val := g, property := m …
      refine' underlying.map (homOfLE (k _ _))
      -- ⊢ ↑(equivShrink (Subobject A)).symm ↑{ val := g, property := m } ∈ s
      simpa using m
      -- 🎉 no goals
    · ext
      -- ⊢ Sigma.ι (fun j => underlying.obj (↑(equivShrink (Subobject A)).symm ↑j)) b✝  …
      dsimp [smallCoproductDesc]
      -- ⊢ Sigma.ι (fun j => underlying.obj (↑(equivShrink (Subobject A)).symm ↑j)) b✝  …
      simp
      -- 🎉 no goals
  · dsimp [sSup]
    -- ⊢ ((underlyingIso (image.ι (smallCoproductDesc s))).hom ≫ image.lift (MonoFact …
    rw [assoc, image.lift_fac, underlyingIso_hom_comp_eq_mk]
    -- 🎉 no goals
#align category_theory.subobject.Sup_le CategoryTheory.Subobject.sSup_le

instance completeSemilatticeSup {B : C} : CompleteSemilatticeSup (Subobject B) where
  sSup := sSup
  le_sSup := le_sSup
  sSup_le := sSup_le

end Sup

section CompleteLattice

variable [WellPowered C] [HasWidePullbacks.{v₁} C] [HasImages C] [HasCoproducts.{v₁} C]
  [InitialMonoClass C]

attribute [local instance] has_smallest_coproducts_of_hasCoproducts

instance {B : C} : CompleteLattice (Subobject B) :=
  { Subobject.semilatticeInf, Subobject.semilatticeSup, Subobject.boundedOrder,
    Subobject.completeSemilatticeInf, Subobject.completeSemilatticeSup with }

end CompleteLattice

section ZeroObject

variable [HasZeroMorphisms C] [HasZeroObject C]

open ZeroObject

/-- A nonzero object has nontrivial subobject lattice. -/
theorem nontrivial_of_not_isZero {X : C} (h : ¬IsZero X) : Nontrivial (Subobject X) :=
  ⟨⟨mk (0 : 0 ⟶ X), mk (𝟙 X), fun w => h (IsZero.of_iso (isZero_zero C) (isoOfMkEqMk _ _ w).symm)⟩⟩
#align category_theory.subobject.nontrivial_of_not_is_zero CategoryTheory.Subobject.nontrivial_of_not_isZero

end ZeroObject

section SubobjectSubobject

/-- The subobject lattice of a subobject `Y` is order isomorphic to the interval `Set.Iic Y`. -/
def subobjectOrderIso {X : C} (Y : Subobject X) : Subobject (Y : C) ≃o Set.Iic Y where
  toFun Z :=
    ⟨Subobject.mk (Z.arrow ≫ Y.arrow),
      Set.mem_Iic.mpr (le_of_comm ((underlyingIso _).hom ≫ Z.arrow) (by simp))⟩
                                                                        -- 🎉 no goals
  invFun Z := Subobject.mk (ofLE _ _ Z.2)
  left_inv Z := mk_eq_of_comm _ (underlyingIso _) (by aesop_cat)
                                                      -- 🎉 no goals
  right_inv Z := Subtype.ext (mk_eq_of_comm _ (underlyingIso _) (by
          dsimp
          -- ⊢ (underlyingIso (ofLE (↑Z) Y (_ : ↑Z ∈ Set.Iic Y))).hom ≫ arrow ↑Z = arrow (m …
          simp [← Iso.eq_inv_comp]))
          -- 🎉 no goals
  map_rel_iff' {W Z} := by
    dsimp
    -- ⊢ { val := mk (arrow W ≫ arrow Y), property := (_ : mk (arrow W ≫ arrow Y) ∈ S …
    constructor
    -- ⊢ { val := mk (arrow W ≫ arrow Y), property := (_ : mk (arrow W ≫ arrow Y) ∈ S …
    · intro h
      -- ⊢ W ≤ Z
      exact le_of_comm (((underlyingIso _).inv ≫ ofLE _ _ (Subtype.mk_le_mk.mp h) ≫
        (underlyingIso _).hom)) (by aesop_cat)
    · intro h
      -- ⊢ { val := mk (arrow W ≫ arrow Y), property := (_ : mk (arrow W ≫ arrow Y) ∈ S …
      exact Subtype.mk_le_mk.mpr (le_of_comm
        ((underlyingIso _).hom ≫ ofLE _ _ h ≫ (underlyingIso _).inv) (by simp))
#align category_theory.subobject.subobject_order_iso CategoryTheory.Subobject.subobjectOrderIso

end SubobjectSubobject

end Subobject

end CategoryTheory
