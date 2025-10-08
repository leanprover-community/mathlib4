/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kim Morrison
-/
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Subobject.FactorThru
import Mathlib.CategoryTheory.Subobject.WellPowered
import Mathlib.Data.Finset.Lattice.Fold

/-!
# The lattice of subobjects

We provide the `SemilatticeInf` with `OrderTop (Subobject X)` instance when `[HasPullback C]`,
and the `SemilatticeSup (Subobject X)` instance when `[HasImages C] [HasBinaryCoproducts C]`.
-/


universe w v₁ v₂ u₁ u₂

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

@[simp]
theorem top_left (X : C) : ((⊤ : MonoOver X) : C) = X :=
  rfl

@[simp]
theorem top_arrow (X : C) : (⊤ : MonoOver X).arrow = 𝟙 X :=
  rfl

/-- `map f` sends `⊤ : MonoOver X` to `⟨X, f⟩ : MonoOver Y`. -/
def mapTop (f : X ⟶ Y) [Mono f] : (map f).obj ⊤ ≅ mk' f :=
  iso_of_both_ways (homMk (𝟙 _) rfl) (homMk (𝟙 _) (by simp [id_comp f]))

section

variable [HasPullbacks C]

/-- The pullback of the top object in `MonoOver Y`
is (isomorphic to) the top object in `MonoOver X`. -/
def pullbackTop (f : X ⟶ Y) : (pullback f).obj ⊤ ≅ ⊤ :=
  iso_of_both_ways (leTop _)
    (homMk (pullback.lift f (𝟙 _) (by simp)) (pullback.lift_snd _ _ _))

/-- There is a morphism from `⊤ : MonoOver A` to the pullback of a monomorphism along itself;
as the category is thin this is an isomorphism. -/
def topLEPullbackSelf {A B : C} (f : A ⟶ B) [Mono f] :
    (⊤ : MonoOver A) ⟶ (pullback f).obj (mk' f) :=
  homMk _ (pullback.lift_snd _ _ rfl)

/-- The pullback of a monomorphism along itself is isomorphic to the top object. -/
def pullbackSelf {A B : C} (f : A ⟶ B) [Mono f] : (pullback f).obj (mk' f) ≅ ⊤ :=
  iso_of_both_ways (leTop _) (topLEPullbackSelf _)

end

end Top

section Bot

variable [HasInitial C] [InitialMonoClass C]

instance {X : C} : Bot (MonoOver X) where bot := mk' (initial.to X)

@[simp]
theorem bot_left (X : C) : ((⊥ : MonoOver X) : C) = ⊥_ C :=
  rfl

@[simp]
theorem bot_arrow {X : C} : (⊥ : MonoOver X).arrow = initial.to X :=
  rfl

/-- The (unique) morphism from `⊥ : MonoOver X` to any other `f : MonoOver X`. -/
def botLE {X : C} (f : MonoOver X) : ⊥ ⟶ f :=
  homMk (initial.to _)

/-- `map f` sends `⊥ : MonoOver X` to `⊥ : MonoOver Y`. -/
def mapBot (f : X ⟶ Y) [Mono f] : (map f).obj ⊥ ≅ ⊥ :=
  iso_of_both_ways (homMk (initial.to _)) (homMk (𝟙 _))

end Bot

section ZeroOrderBot

variable [HasZeroObject C]

open ZeroObject

/-- The object underlying `⊥ : Subobject B` is (up to isomorphism) the zero object. -/
def botCoeIsoZero {B : C} : ((⊥ : MonoOver B) : C) ≅ 0 :=
  initialIsInitial.uniqueUpToIso HasZeroObject.zeroIsInitial

theorem bot_arrow_eq_zero [HasZeroMorphisms C] {B : C} : (⊥ : MonoOver B).arrow = 0 :=
  zero_of_source_iso_zero _ botCoeIsoZero

/-- `simp`-normal form of `bot_arrow_eq_zero`. -/
@[simp]
theorem initialTo_b_eq_zero [HasZeroMorphisms C] {B : C} : initial.to B = 0 := by
  rw [← bot_arrow, bot_arrow_eq_zero]

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
        · apply pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ k.left) _
          rw [pullback.condition, assoc, w k]
        dsimp
        rw [pullback.lift_snd_assoc, assoc, w k] }

/-- A morphism from the "infimum" of two objects in `MonoOver A` to the first object. -/
def infLELeft {A : C} (f g : MonoOver A) : (inf.obj f).obj g ⟶ f :=
  homMk _ rfl

/-- A morphism from the "infimum" of two objects in `MonoOver A` to the second object. -/
def infLERight {A : C} (f g : MonoOver A) : (inf.obj f).obj g ⟶ g :=
  homMk _ pullback.condition

/-- A morphism version of the `le_inf` axiom. -/
def leInf {A : C} (f g h : MonoOver A) : (h ⟶ f) → (h ⟶ g) → (h ⟶ (inf.obj f).obj g) := by
  intro k₁ k₂
  refine homMk (pullback.lift k₂.left k₁.left ?_) ?_
  · rw [w k₁, w k₂]
  · erw [pullback.lift_snd_assoc, w k₁]

end Inf

section Sup

variable [HasImages C] [HasBinaryCoproducts C]

/-- When `[HasImages C] [HasBinaryCoproducts C]`, `MonoOver A` has a `sup` construction,
which is functorial in both arguments,
and which on `Subobject A` will induce a `SemilatticeSup`. -/
def sup {A : C} : MonoOver A ⥤ MonoOver A ⥤ MonoOver A :=
  Functor.curryObj ((forget A).prod (forget A) ⋙ Functor.uncurry.obj Over.coprod ⋙ image)

/-- A morphism version of `le_sup_left`. -/
def leSupLeft {A : C} (f g : MonoOver A) : f ⟶ (sup.obj f).obj g := by
  refine homMk (coprod.inl ≫ factorThruImage _) ?_
  erw [Category.assoc, image.fac, coprod.inl_desc]
  rfl

/-- A morphism version of `le_sup_right`. -/
def leSupRight {A : C} (f g : MonoOver A) : g ⟶ (sup.obj f).obj g := by
  refine homMk (coprod.inr ≫ factorThruImage _) ?_
  erw [Category.assoc, image.fac, coprod.inr_desc]
  rfl

/-- A morphism version of `sup_le`. -/
def supLe {A : C} (f g h : MonoOver A) : (f ⟶ h) → (g ⟶ h) → ((sup.obj f).obj g ⟶ h) := by
  intro k₁ k₂
  refine homMk ?_ ?_
  · apply image.lift ⟨_, h.arrow, coprod.desc k₁.left k₂.left, _⟩
    ext
    · simp [w k₁]
    · simp [w k₂]
  · apply image.lift_fac

end Sup

end MonoOver

namespace Subobject

section OrderTop

instance orderTop {X : C} : OrderTop (Subobject X) where
  top := Quotient.mk'' ⊤
  le_top := by
    refine Quotient.ind' fun f => ?_
    exact ⟨MonoOver.leTop f⟩

instance {X : C} : Inhabited (Subobject X) :=
  ⟨⊤⟩

theorem top_eq_id (B : C) : (⊤ : Subobject B) = Subobject.mk (𝟙 B) :=
  rfl

theorem underlyingIso_top_hom {B : C} : (underlyingIso (𝟙 B)).hom = (⊤ : Subobject B).arrow := by
  convert underlyingIso_hom_comp_eq_mk (𝟙 B)
  simp only [comp_id]

instance top_arrow_isIso {B : C} : IsIso (⊤ : Subobject B).arrow := by
  rw [← underlyingIso_top_hom]
  infer_instance

@[reassoc (attr := simp)]
theorem underlyingIso_inv_top_arrow {B : C} :
    (underlyingIso _).inv ≫ (⊤ : Subobject B).arrow = 𝟙 B :=
  underlyingIso_arrow _

@[simp]
theorem map_top (f : X ⟶ Y) [Mono f] : (map f).obj ⊤ = Subobject.mk f :=
  Quotient.sound' ⟨MonoOver.mapTop f⟩

theorem top_factors {A B : C} (f : A ⟶ B) : (⊤ : Subobject B).Factors f :=
  ⟨f, comp_id _⟩

theorem isIso_iff_mk_eq_top {X Y : C} (f : X ⟶ Y) [Mono f] : IsIso f ↔ mk f = ⊤ :=
  ⟨fun _ => mk_eq_mk_of_comm _ _ (asIso f) (Category.comp_id _), fun h => by
    rw [← ofMkLEMk_comp h.le, Category.comp_id]
    exact (isoOfMkEqMk _ _ h).isIso_hom⟩

theorem isIso_arrow_iff_eq_top {Y : C} (P : Subobject Y) : IsIso P.arrow ↔ P = ⊤ := by
  rw [isIso_iff_mk_eq_top, mk_arrow]

instance isIso_top_arrow {Y : C} : IsIso (⊤ : Subobject Y).arrow := by rw [isIso_arrow_iff_eq_top]

theorem mk_eq_top_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : mk f = ⊤ :=
  (isIso_iff_mk_eq_top f).mp inferInstance

theorem eq_top_of_isIso_arrow {Y : C} (P : Subobject Y) [IsIso P.arrow] : P = ⊤ :=
  (isIso_arrow_iff_eq_top P).mp inferInstance

lemma epi_iff_mk_eq_top [Balanced C] (f : X ⟶ Y) [Mono f] :
    Epi f ↔ Subobject.mk f = ⊤ := by
  rw [← isIso_iff_mk_eq_top]
  exact ⟨fun _ ↦ isIso_of_mono_of_epi f, fun _ ↦ inferInstance⟩

section

variable [HasPullbacks C]

theorem pullback_top (f : X ⟶ Y) : (pullback f).obj ⊤ = ⊤ :=
  Quotient.sound' ⟨MonoOver.pullbackTop f⟩

theorem pullback_self {A B : C} (f : A ⟶ B) [Mono f] : (pullback f).obj (mk f) = ⊤ :=
  Quotient.sound' ⟨MonoOver.pullbackSelf f⟩

end

end OrderTop

section OrderBot

variable [HasInitial C] [InitialMonoClass C]

instance orderBot {X : C} : OrderBot (Subobject X) where
  bot := Quotient.mk'' ⊥
  bot_le := by
    refine Quotient.ind' fun f => ?_
    exact ⟨MonoOver.botLE f⟩

theorem bot_eq_initial_to {B : C} : (⊥ : Subobject B) = Subobject.mk (initial.to B) :=
  rfl

/-- The object underlying `⊥ : Subobject B` is (up to isomorphism) the initial object. -/
def botCoeIsoInitial {B : C} : ((⊥ : Subobject B) : C) ≅ ⊥_ C :=
  underlyingIso _

theorem map_bot (f : X ⟶ Y) [Mono f] : (map f).obj ⊥ = ⊥ :=
  Quotient.sound' ⟨MonoOver.mapBot f⟩

end OrderBot

section ZeroOrderBot

variable [HasZeroObject C]

open ZeroObject

/-- The object underlying `⊥ : Subobject B` is (up to isomorphism) the zero object. -/
def botCoeIsoZero {B : C} : ((⊥ : Subobject B) : C) ≅ 0 :=
  botCoeIsoInitial ≪≫ initialIsInitial.uniqueUpToIso HasZeroObject.zeroIsInitial

variable [HasZeroMorphisms C]

theorem bot_eq_zero {B : C} : (⊥ : Subobject B) = Subobject.mk (0 : 0 ⟶ B) :=
  mk_eq_mk_of_comm _ _ (initialIsInitial.uniqueUpToIso HasZeroObject.zeroIsInitial)
    (by simp)

@[simp]
theorem bot_arrow {B : C} : (⊥ : Subobject B).arrow = 0 :=
  zero_of_source_iso_zero _ botCoeIsoZero

theorem bot_factors_iff_zero {A B : C} (f : A ⟶ B) : (⊥ : Subobject B).Factors f ↔ f = 0 :=
  ⟨by
    rintro ⟨h, rfl⟩
    simp only [MonoOver.bot_arrow_eq_zero, MonoOver.bot_left, comp_zero],
   by
    rintro rfl
    exact ⟨0, by simp⟩⟩

theorem mk_eq_bot_iff_zero {f : X ⟶ Y} [Mono f] : Subobject.mk f = ⊥ ↔ f = 0 :=
  ⟨fun h => by simpa [h, bot_factors_iff_zero] using mk_factors_self f, fun h =>
    mk_eq_mk_of_comm _ _ ((isoZeroOfMonoEqZero h).trans HasZeroObject.zeroIsoInitial) (by simp [h])⟩

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

end Functor

section SemilatticeInfTop

variable [HasPullbacks C]

/-- The functorial infimum on `MonoOver A` descends to an infimum on `Subobject A`. -/
def inf {A : C} : Subobject A ⥤ Subobject A ⥤ Subobject A :=
  ThinSkeleton.map₂ MonoOver.inf

theorem inf_le_left {A : C} (f g : Subobject A) : (inf.obj f).obj g ≤ f :=
  Quotient.inductionOn₂' f g fun _ _ => ⟨MonoOver.infLELeft _ _⟩

theorem inf_le_right {A : C} (f g : Subobject A) : (inf.obj f).obj g ≤ g :=
  Quotient.inductionOn₂' f g fun _ _ => ⟨MonoOver.infLERight _ _⟩

theorem le_inf {A : C} (h f g : Subobject A) : h ≤ f → h ≤ g → h ≤ (inf.obj f).obj g :=
  Quotient.inductionOn₃' h f g
    (by
      rintro f g h ⟨k⟩ ⟨l⟩
      exact ⟨MonoOver.leInf _ _ _ k l⟩)

instance semilatticeInf {B : C} : SemilatticeInf (Subobject B) where
  inf := fun m n => (inf.obj m).obj n
  inf_le_left := inf_le_left
  inf_le_right := inf_le_right
  le_inf := le_inf

theorem factors_left_of_inf_factors {A B : C} {X Y : Subobject B} {f : A ⟶ B}
    (h : (X ⊓ Y).Factors f) : X.Factors f :=
  factors_of_le _ (inf_le_left _ _) h

theorem factors_right_of_inf_factors {A B : C} {X Y : Subobject B} {f : A ⟶ B}
    (h : (X ⊓ Y).Factors f) : Y.Factors f :=
  factors_of_le _ (inf_le_right _ _) h

@[simp]
theorem inf_factors {A B : C} {X Y : Subobject B} (f : A ⟶ B) :
    (X ⊓ Y).Factors f ↔ X.Factors f ∧ Y.Factors f :=
  ⟨fun h => ⟨factors_left_of_inf_factors h, factors_right_of_inf_factors h⟩, by
    revert X Y
    apply Quotient.ind₂'
    rintro X Y ⟨⟨g₁, rfl⟩, ⟨g₂, hg₂⟩⟩
    exact ⟨_, pullback.lift_snd_assoc _ _ hg₂ _⟩⟩

theorem inf_arrow_factors_left {B : C} (X Y : Subobject B) : X.Factors (X ⊓ Y).arrow :=
  (factors_iff _ _).mpr ⟨ofLE (X ⊓ Y) X (inf_le_left X Y), by simp⟩

theorem inf_arrow_factors_right {B : C} (X Y : Subobject B) : Y.Factors (X ⊓ Y).arrow :=
  (factors_iff _ _).mpr ⟨ofLE (X ⊓ Y) Y (inf_le_right X Y), by simp⟩

@[simp]
theorem finset_inf_factors {I : Type*} {A B : C} {s : Finset I} {P : I → Subobject B} (f : A ⟶ B) :
    (s.inf P).Factors f ↔ ∀ i ∈ s, (P i).Factors f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [top_factors]
  | insert _ _ _ ih => simp [ih]

-- `i` is explicit here because often we'd like to defer a proof of `m`
theorem finset_inf_arrow_factors {I : Type*} {B : C} (s : Finset I) (P : I → Subobject B) (i : I)
    (m : i ∈ s) : (P i).Factors (s.inf P).arrow := by
  classical
  revert i m
  induction s using Finset.induction_on with
  | empty => rintro _ ⟨⟩
  | insert _ _ _ ih =>
    intro _ m
    rw [Finset.inf_insert]
    simp only [Finset.mem_insert] at m
    rcases m with (rfl | m)
    · rw [← factorThru_arrow _ _ (inf_arrow_factors_left _ _)]
      exact factors_comp_arrow _
    · rw [← factorThru_arrow _ _ (inf_arrow_factors_right _ _)]
      apply factors_of_factors_right
      exact ih _ m

theorem inf_eq_map_pullback' {A : C} (f₁ : MonoOver A) (f₂ : Subobject A) :
    (Subobject.inf.obj (Quotient.mk'' f₁)).obj f₂ =
      (Subobject.map f₁.arrow).obj ((Subobject.pullback f₁.arrow).obj f₂) := by
  induction f₂ using Quotient.inductionOn'
  rfl

theorem inf_eq_map_pullback {A : C} (f₁ : MonoOver A) (f₂ : Subobject A) :
    (Quotient.mk'' f₁ ⊓ f₂ : Subobject A) = (map f₁.arrow).obj ((pullback f₁.arrow).obj f₂) :=
  inf_eq_map_pullback' f₁ f₂

theorem prod_eq_inf {A : C} {f₁ f₂ : Subobject A} [HasBinaryProduct f₁ f₂] :
    (f₁ ⨯ f₂) = f₁ ⊓ f₂ := by
  apply le_antisymm
  · refine le_inf _ _ _ (Limits.prod.fst.le) (Limits.prod.snd.le)
  · apply leOfHom
    exact prod.lift (inf_le_left _ _).hom (inf_le_right _ _).hom

theorem inf_def {B : C} (m m' : Subobject B) : m ⊓ m' = (inf.obj m).obj m' :=
  rfl

/-- `⊓` commutes with pullback. -/
theorem inf_pullback {X Y : C} (g : X ⟶ Y) (f₁ f₂) :
    (pullback g).obj (f₁ ⊓ f₂) = (pullback g).obj f₁ ⊓ (pullback g).obj f₂ := by
  revert f₁
  apply Quotient.ind'
  intro f₁
  erw [inf_def, inf_def, inf_eq_map_pullback', inf_eq_map_pullback', ← pullback_comp, ←
    map_pullback pullback.condition (pullbackIsPullback f₁.arrow g), ← pullback_comp,
    pullback.condition]
  rfl

/-- `⊓` commutes with map. -/
theorem inf_map {X Y : C} (g : Y ⟶ X) [Mono g] (f₁ f₂) :
    (map g).obj (f₁ ⊓ f₂) = (map g).obj f₁ ⊓ (map g).obj f₂ := by
  revert f₁
  apply Quotient.ind'
  intro f₁
  erw [inf_def, inf_def, inf_eq_map_pullback', inf_eq_map_pullback', ← map_comp]
  dsimp
  rw [pullback_comp, pullback_map_self]

end SemilatticeInfTop

section SemilatticeSup

variable [HasImages C] [HasBinaryCoproducts C]

/-- The functorial supremum on `MonoOver A` descends to a supremum on `Subobject A`. -/
def sup {A : C} : Subobject A ⥤ Subobject A ⥤ Subobject A :=
  ThinSkeleton.map₂ MonoOver.sup

instance semilatticeSup {B : C} : SemilatticeSup (Subobject B) where
  sup := fun m n => (sup.obj m).obj n
  le_sup_left := fun m n => Quotient.inductionOn₂' m n fun _ _ => ⟨MonoOver.leSupLeft _ _⟩
  le_sup_right := fun m n => Quotient.inductionOn₂' m n fun _ _ => ⟨MonoOver.leSupRight _ _⟩
  sup_le := fun m n k =>
    Quotient.inductionOn₃' m n k fun _ _ _ ⟨i⟩ ⟨j⟩ => ⟨MonoOver.supLe _ _ _ i j⟩

theorem sup_factors_of_factors_left {A B : C} {X Y : Subobject B} {f : A ⟶ B} (P : X.Factors f) :
    (X ⊔ Y).Factors f :=
  factors_of_le f le_sup_left P

theorem sup_factors_of_factors_right {A B : C} {X Y : Subobject B} {f : A ⟶ B} (P : Y.Factors f) :
    (X ⊔ Y).Factors f :=
  factors_of_le f le_sup_right P

variable [HasInitial C] [InitialMonoClass C]

theorem finset_sup_factors {I : Type*} {A B : C} {s : Finset I} {P : I → Subobject B} {f : A ⟶ B}
    (h : ∃ i ∈ s, (P i).Factors f) : (s.sup P).Factors f := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty => rintro ⟨_, ⟨⟨⟩, _⟩⟩
  | insert _ _ _ ih =>
    rintro ⟨j, ⟨m, h⟩⟩
    simp only [Finset.sup_insert]
    simp only [Finset.mem_insert] at m
    rcases m with (rfl | m)
    · exact sup_factors_of_factors_left h
    · exact sup_factors_of_factors_right (ih ⟨j, ⟨m, h⟩⟩)

end SemilatticeSup

section Lattice

instance boundedOrder [HasInitial C] [InitialMonoClass C] {B : C} : BoundedOrder (Subobject B) :=
  { Subobject.orderTop, Subobject.orderBot with }

variable [HasPullbacks C] [HasImages C] [HasBinaryCoproducts C]

instance {B : C} : Lattice (Subobject B) :=
  { Subobject.semilatticeInf, Subobject.semilatticeSup with }

end Lattice

section Inf

variable [LocallySmall.{w} C] [WellPowered.{w} C]

/-- The "wide cospan" diagram, with a small indexing type, constructed from a set of subobjects.
(This is just the diagram of all the subobjects pasted together, but using `WellPowered C`
to make the diagram small.)
-/
def wideCospan {A : C} (s : Set (Subobject A)) : WidePullbackShape (equivShrink _ '' s) ⥤ C :=
  WidePullbackShape.wideCospan A
    (fun j : equivShrink _ '' s => ((equivShrink (Subobject A)).symm j : C)) fun j =>
    ((equivShrink (Subobject A)).symm j).arrow

@[simp]
theorem wideCospan_map_term {A : C} (s : Set (Subobject A)) (j) :
    (wideCospan s).map (WidePullbackShape.Hom.term j) =
      ((equivShrink (Subobject A)).symm j).arrow :=
  rfl

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
              simpa using m))))
    (by simp)

@[simp]
theorem leInfCone_π_app_none {A : C} (s : Set (Subobject A)) (f : Subobject A)
    (k : ∀ g ∈ s, f ≤ g) : (leInfCone s f k).π.app none = f.arrow :=
  rfl

variable [HasWidePullbacks.{w} C]

/-- The limit of `wideCospan s`. (This will be the supremum of the set of subobjects.)
-/
def widePullback {A : C} (s : Set (Subobject A)) : C :=
  Limits.limit (wideCospan s)

/-- The inclusion map from `widePullback s` to `A`
-/
def widePullbackι {A : C} (s : Set (Subobject A)) : widePullback s ⟶ A :=
  Limits.limit.π (wideCospan s) none

instance widePullbackι_mono {A : C} (s : Set (Subobject A)) : Mono (widePullbackι s) :=
  ⟨fun u v h =>
    limit.hom_ext fun j => by
      cases j
      · exact h
      · apply (cancel_mono ((equivShrink (Subobject A)).symm _).arrow).1
        rw [assoc, assoc]
        erw [limit.w (wideCospan s) (WidePullbackShape.Hom.term _)]
        exact h⟩

/-- When `[WellPowered C]` and `[HasWidePullbacks C]`, `Subobject A` has arbitrary infimums.
-/
def sInf {A : C} (s : Set (Subobject A)) : Subobject A :=
  Subobject.mk (widePullbackι s)

theorem sInf_le {A : C} (s : Set (Subobject A)) (f) (hf : f ∈ s) : sInf s ≤ f := by
  fapply le_of_comm
  · exact (underlyingIso _).hom ≫
      Limits.limit.π (wideCospan s)
        (some ⟨equivShrink (Subobject A) f,
          Set.mem_image_of_mem (equivShrink (Subobject A)) hf⟩) ≫
      eqToHom (congr_arg (fun X : Subobject A => (X : C)) (Equiv.symm_apply_apply _ _))
  · dsimp [sInf]
    simp only [Category.assoc, ← underlyingIso_hom_comp_eq_mk,
      Iso.cancel_iso_hom_left]
    convert limit.w (wideCospan s) (WidePullbackShape.Hom.term _)
    simp

theorem le_sInf {A : C} (s : Set (Subobject A)) (f : Subobject A) (k : ∀ g ∈ s, f ≤ g) :
    f ≤ sInf s := by
  fapply le_of_comm
  · exact Limits.limit.lift _ (leInfCone s f k) ≫ (underlyingIso _).inv
  · dsimp [sInf]
    rw [assoc, underlyingIso_arrow, widePullbackι, limit.lift_π, leInfCone_π_app_none]

instance completeSemilatticeInf {B : C} : CompleteSemilatticeInf (Subobject B) where
  sInf := sInf
  sInf_le := sInf_le
  le_sInf := le_sInf

end Inf

section Sup

variable [LocallySmall.{w} C] [WellPowered.{w} C] [HasCoproducts.{w} C]

/-- The universal morphism out of the coproduct of a set of subobjects,
after using `[WellPowered C]` to reindex by a small type.
-/
def smallCoproductDesc {A : C} (s : Set (Subobject A)) :=
  Limits.Sigma.desc fun j : equivShrink _ '' s => ((equivShrink (Subobject A)).symm j).arrow

variable [HasImages C]

/-- When `[WellPowered C] [HasImages C] [HasCoproducts C]`,
`Subobject A` has arbitrary supremums. -/
def sSup {A : C} (s : Set (Subobject A)) : Subobject A :=
  Subobject.mk (image.ι (smallCoproductDesc s))

theorem le_sSup {A : C} (s : Set (Subobject A)) (f) (hf : f ∈ s) : f ≤ sSup s := by
  fapply le_of_comm
  · refine eqToHom ?_ ≫ Sigma.ι _ ⟨equivShrink (Subobject A) f, by simpa [Set.mem_image] using hf⟩
      ≫ factorThruImage _ ≫ (underlyingIso _).inv
    exact (congr_arg (fun X : Subobject A => (X : C)) (Equiv.symm_apply_apply _ _).symm)
  · simp [sSup, smallCoproductDesc]

theorem symm_apply_mem_iff_mem_image {α β : Type*} (e : α ≃ β) (s : Set α) (x : β) :
    e.symm x ∈ s ↔ x ∈ e '' s :=
  ⟨fun h => ⟨e.symm x, h, by simp⟩, by
    rintro ⟨a, m, rfl⟩
    simpa using m⟩

theorem sSup_le {A : C} (s : Set (Subobject A)) (f : Subobject A) (k : ∀ g ∈ s, g ≤ f) :
    sSup s ≤ f := by
  fapply le_of_comm
  · refine(underlyingIso _).hom ≫ image.lift ⟨_, f.arrow, ?_, ?_⟩
    · refine Sigma.desc ?_
      rintro ⟨g, m⟩
      refine underlying.map (homOfLE (k _ ?_))
      simpa using m
    · ext
      dsimp [smallCoproductDesc]
      simp
  · dsimp [sSup]
    rw [assoc, image.lift_fac, underlyingIso_hom_comp_eq_mk]

instance completeSemilatticeSup {B : C} : CompleteSemilatticeSup (Subobject B) where
  sSup := sSup
  le_sSup := le_sSup
  sSup_le := sSup_le

end Sup

section CompleteLattice

variable [LocallySmall.{w} C] [WellPowered.{w} C] [HasWidePullbacks.{w} C]
  [HasImages C] [HasCoproducts.{w} C] [InitialMonoClass C]

attribute [local instance] has_smallest_coproducts_of_hasCoproducts

instance {B : C} : CompleteLattice (Subobject B) :=
  { Subobject.semilatticeInf, Subobject.semilatticeSup, Subobject.boundedOrder,
    Subobject.completeSemilatticeInf, Subobject.completeSemilatticeSup with }

end CompleteLattice

lemma subsingleton_of_isInitial {X : C} (hX : IsInitial X) : Subsingleton (Subobject X) := by
  suffices ∀ (S : Subobject X), S = .mk (𝟙 _) from ⟨by simp [this]⟩
  intro S
  obtain ⟨A, i, _, rfl⟩ := S.mk_surjective
  have fac : hX.to A ≫ i = 𝟙 X := hX.hom_ext _ _
  let e : A ≅ X :=
    { hom := i
      inv := hX.to A
      hom_inv_id := by rw [← cancel_mono i, assoc, fac, id_comp, comp_id]
      inv_hom_id := fac }
  exact mk_eq_mk_of_comm i (𝟙 X) e (by simp [e])

lemma subsingleton_of_isZero {X : C} (hX : IsZero X) : Subsingleton (Subobject X) :=
  subsingleton_of_isInitial hX.isInitial

section ZeroObject

variable [HasZeroMorphisms C] [HasZeroObject C]

open ZeroObject

/-- A nonzero object has nontrivial subobject lattice. -/
theorem nontrivial_of_not_isZero {X : C} (h : ¬IsZero X) : Nontrivial (Subobject X) :=
  ⟨⟨mk (0 : 0 ⟶ X), mk (𝟙 X), fun w => h (IsZero.of_iso (isZero_zero C) (isoOfMkEqMk _ _ w).symm)⟩⟩

end ZeroObject

section SubobjectSubobject

/-- The subobject lattice of a subobject `Y` is order isomorphic to the interval `Set.Iic Y`. -/
def subobjectOrderIso {X : C} (Y : Subobject X) : Subobject (Y : C) ≃o Set.Iic Y where
  toFun Z :=
    ⟨Subobject.mk (Z.arrow ≫ Y.arrow),
      Set.mem_Iic.mpr (le_of_comm ((underlyingIso _).hom ≫ Z.arrow) (by simp))⟩
  invFun Z := Subobject.mk (ofLE _ _ Z.2)
  left_inv Z := mk_eq_of_comm _ (underlyingIso _) (by cat_disch)
  right_inv Z := Subtype.ext (mk_eq_of_comm _ (underlyingIso _) (by simp [← Iso.eq_inv_comp]))
  map_rel_iff' {W Z} := by
    dsimp
    constructor
    · intro h
      exact le_of_comm (((underlyingIso _).inv ≫ ofLE _ _ (Subtype.mk_le_mk.mp h) ≫
        (underlyingIso _).hom)) (by cat_disch)
    · intro h
      exact Subtype.mk_le_mk.mpr (le_of_comm
        ((underlyingIso _).hom ≫ ofLE _ _ h ≫ (underlyingIso _).inv) (by simp))

end SubobjectSubobject

end Subobject

end CategoryTheory
