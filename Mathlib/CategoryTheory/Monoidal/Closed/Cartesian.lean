/-
Copyright (c) 2020 Bhavik Mehta, Edward Ayers, Thomas Read. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Edward Ayers, Thomas Read
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Cartesian closed categories

A cartesian closed category is a category with `CartesianMonoidalCategory` and `MonoidalClosed`
instances. There used to be a separate definition `CartesianClosed`, with its own API, but over time
this ended up as a duplicate of the former. Now, `CartesianClosed` and the surrounding API has been
deprecated, and the API for `MonoidalClosed` should be used instead. This file now contains a few
basic constructions for cartesian closed categories.

-/

@[expose] public section

universe v v₂ u u₂

namespace CategoryTheory

open Category Limits MonoidalCategory CartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {X X' Y Y' Z : C}

instance CartesianMonoidalCategory.isLeftAdjoint_prod_functor
    (A : C) [Closed A] :
    (prod.functor.obj A).IsLeftAdjoint :=
  Functor.isLeftAdjoint_of_iso (CartesianMonoidalCategory.tensorLeftIsoProd A)

namespace CartesianClosed

-- Porting note: notation fails to elaborate with `quotPrecheck` on.
set_option quotPrecheck false in
/-- Morphisms obtained using an exponentiable object. -/
scoped notation:20 A " ⟹ " B:19 => (ihom A).obj B

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Delaborator for `Functor.obj` -/
@[app_delab Functor.obj]
meta def delabFunctorObjExp : Delab :=
    whenPPOption getPPNotation <| withOverApp 6 do
  let e ← getExpr
  guard <| e.isAppOfArity' ``Functor.obj 6
  let A ← withNaryArg 4 do
    let e ← getExpr
    guard <| e.isAppOfArity' ``ihom 5
    withNaryArg 3 delab
  let B ← withNaryArg 5 delab
  `($A ⟹ $B)

-- Porting note: notation fails to elaborate with `quotPrecheck` on.
set_option quotPrecheck false in
/-- Morphisms from an exponentiable object. -/
scoped notation:30 B " ^^ " A:30 => (ihom A).obj B

end CartesianClosed

open CartesianClosed

/-- The internal element which points at the given morphism. -/
def internalizeHom {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {A Y : C} [Closed A]
    (f : A ⟶ Y) : 𝟙_ C ⟶ A ⟹ Y :=
  MonoidalClosed.curry (fst _ _ ≫ f)

variable {A B : C} [Closed A]

open MonoidalClosed

/-- If an initial object `I` exists in a CCC, then `A ⨯ I ≅ I`. -/
@[simps]
def zeroMul {I : C} (t : IsInitial I) : A ⊗ I ≅ I where
  hom := snd _ _
  inv := t.to _
  hom_inv_id := by
    have : snd A I = uncurry (t.to _) := by
      rw [← curry_eq_iff]
      apply t.hom_ext
    rw [this, ← uncurry_natural_right, ← eq_curry_iff]
    apply t.hom_ext
  inv_hom_id := t.hom_ext _ _

/-- If an initial object `0` exists in a CCC, then `0 ⨯ A ≅ 0`. -/
def mulZero [BraidedCategory C] {I : C} (t : IsInitial I) : I ⊗ A ≅ I :=
  β_ _ _ ≪≫ zeroMul t

/-- If an initial object `0` exists in a CCC then `0^B ≅ 1` for any `B`. -/
def powZero [BraidedCategory C] {I : C} (t : IsInitial I) [MonoidalClosed C] : I ⟹ B ≅ 𝟙_ C where
  hom := default
  inv := curry ((mulZero t).hom ≫ t.to _)
  hom_inv_id := by
    rw [← curry_natural_left, curry_eq_iff, ← cancel_epi (mulZero t).inv]
    apply t.hom_ext

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism `pushout (f ▷ I) (A ◁ (∅ ⟶ W)) ≅ A ⊗ W` in a CCC with pushouts and an
initial object. -/
@[simps]
noncomputable def MonoidalCategory.Limits.pushout.isInitialWhiskerLeftIso
    [HasPushouts C] [CartesianMonoidalCategory C] [MonoidalClosed C]
    {A B : C} (f : A ⟶ B) {I : C} (i : IsInitial I) {W : C} :
    pushout (f ▷ I) (A ◁ i.to W) ≅ A ⊗ W where
  hom := pushout.desc ((i.ofIso (zeroMul i).symm).to _) (𝟙 _)
    ((i.ofIso (zeroMul i).symm).hom_ext _ _)
  inv := pushout.inr _ _
  hom_inv_id := pushout.hom_ext ((i.ofIso (zeroMul i).symm).hom_ext _ _) (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism `pushout  ((∅ ⟶ W) ▷ A) (I ◁ f) ≅ W ⊗ A` in a braided CCC with pushouts and
an initial object. -/
@[simps]
noncomputable def MonoidalCategory.Limits.pushout.isInitialWhiskerRightIso
    [HasPushouts C] [CartesianMonoidalCategory C] [MonoidalClosed C] [BraidedCategory C]
    {A B : C} (f : A ⟶ B) {I : C} (i : IsInitial I) {W : C} :
    pushout (i.to W ▷ A) (I ◁ f) ≅ W ⊗ A where
  hom := pushout.desc (𝟙 _) ((i.ofIso (mulZero i).symm).to _)
    ((i.ofIso (mulZero i).symm).hom_ext _ _)
  inv := pushout.inl _ _
  hom_inv_id := pushout.hom_ext (by simp) ((i.ofIso (mulZero i).symm).hom_ext _ _)

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism `pullback (A ⟹ W ⟶ A ⟹ ⋆) (B ⟹ ⋆ ⟶ A ⟹ ⋆) ≅ A ⟹ W` in a monoidal closed
category with pullbacks and a terminal object. -/
@[simps]
noncomputable def Limits.pullback.ihomMapIsTerminalIso
    [HasPullbacks C] [MonoidalCategory C] [MonoidalClosed C]
    {A B : C} (f : A ⟶ B) {T : C} (t : IsTerminal T) {W : C} :
    pullback ((ihom A).map (t.from W)) ((pre f).app T) ≅ (ihom A).obj W where
  hom := pullback.fst _ _
  inv := pullback.lift (𝟙 _) (curry (t.from _))
    (by rw [curry_pre_app, eq_curry_iff]; apply t.hom_ext)
  hom_inv_id :=
    have : (ihom B).IsRightAdjoint := Closed.adj.isRightAdjoint
    pullback.hom_ext (by simp) ((IsTerminal.isTerminalObj (ihom B) T t).hom_ext _ _)

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism `pullback (∅ ⟹ A ⟶ ∅ ⟹ B) (W ⟹ B ⟶ ∅ ⟹ B) ≅ W ⟹ B` in a braided CCC
with pullbacks and an initial object. -/
@[simps]
noncomputable def Limits.pullback.preAppIsInitialIso
    [HasPullbacks C] [CartesianMonoidalCategory C] [MonoidalClosed C] [BraidedCategory C]
    {A B : C} (f : A ⟶ B) {I : C} (i : IsInitial I) {W : C} :
    pullback ((ihom I).map f) ((pre (i.to W)).app B) ≅ (ihom W).obj B where
  hom := pullback.snd _ _
  inv := pullback.lift (curry ((i.ofIso (mulZero i).symm).to _)) (𝟙 _) (by
      rw [← curry_natural_right, curry_eq_iff]
      exact (i.ofIso (mulZero i).symm).hom_ext _ _)
  hom_inv_id := pullback.hom_ext (by
    simp only [Category.assoc, limit.lift_π, PullbackCone.mk_π_app,
      ← curry_natural_left, curry_eq_iff]
    exact (i.ofIso (mulZero i).symm).hom_ext _ _) (by simp)

set_option backward.isDefEq.respectTransparency false in
-- TODO: Generalise the below to its commuted variants.
-- TODO: Define a distributive category, so that zero_mul and friends can be derived from this.
/-- In a CCC with binary coproducts, the distribution morphism is an isomorphism. -/
@[deprecated "No replacement: use `asIso (coprodComparison (tensorLeft Z) _ _)` instead."
(since := "2025-12-22")]
noncomputable def prodCoprodDistrib [MonoidalCategory C] [HasBinaryCoproducts C]
    [MonoidalClosed C] (X Y Z : C) : (Z ⊗ X) ⨿ Z ⊗ Y ≅ Z ⊗ (X ⨿ Y) :=
  asIso (coprodComparison (tensorLeft Z) _ _)

/-- If an initial object `I` exists in a CCC then it is a strict initial object,
i.e. any morphism to `I` is an iso.
This actually shows a slightly stronger version: any morphism to an initial object from an
exponentiable object is an isomorphism.
-/
theorem strict_initial {I : C} (t : IsInitial I) (f : A ⟶ I) : IsIso f := by
  haveI : Mono f := by
    rw [← lift_snd (𝟙 A) f, ← zeroMul_hom t]
    exact mono_comp _ _
  haveI : IsSplitEpi f := IsSplitEpi.mk' ⟨t.to _, t.hom_ext _ _⟩
  apply isIso_of_mono_of_isSplitEpi

instance to_initial_isIso [HasInitial C] (f : A ⟶ ⊥_ C) : IsIso f :=
  strict_initial initialIsInitial _

/-- If an initial object `0` exists in a CCC then every morphism from it is monic. -/
theorem initial_mono {I : C} (B : C) (t : IsInitial I) [MonoidalClosed C] : Mono (t.to B) :=
  ⟨fun g h _ => by
    haveI := strict_initial t g
    haveI := strict_initial t h
    exact eq_of_inv_eq_inv (t.hom_ext _ _)⟩

instance Initial.mono_to [HasInitial C] (B : C) [MonoidalClosed C] : Mono (initial.to B) :=
  initial_mono B initialIsInitial

variable {D : Type u₂} [Category.{v₂} D]

section Functor

variable [CartesianMonoidalCategory D]

/-- Transport the property of being Cartesian closed across an equivalence of categories.

Note we didn't require any coherence between the choice of finite products here, since we transport
along the `prodComparison` isomorphism.
-/
@[implicit_reducible]
noncomputable def cartesianClosedOfEquiv (e : C ≌ D) [MonoidalClosed C] : MonoidalClosed D :=
  letI : e.inverse.Monoidal := .ofChosenFiniteProducts _
  MonoidalClosed.ofEquiv e.inverse e.symm.toAdjunction

end Functor

@[deprecated (since := "2025-12-22")] alias Exponentiable := Closed
@[deprecated (since := "2025-12-22")] alias Exponentiable.mk := Closed.mk
@[deprecated (since := "2025-12-22")] alias binaryProductExponentiable := tensorClosed
@[deprecated (since := "2025-12-22")] alias terminalExponentiable := unitClosed
@[deprecated (since := "2025-12-22")] alias CartesianClosed := MonoidalClosed
@[deprecated (since := "2025-12-22")] alias CartesianClosed.mk := MonoidalClosed.mk
@[deprecated (since := "2025-12-22")] alias exp := ihom
@[deprecated (since := "2025-12-22")] alias exp.adjunction := ihom.adjunction
@[deprecated (since := "2025-12-22")] alias exp.ev := ihom.ev
@[deprecated (since := "2025-12-22")] alias exp.coev := ihom.coev
@[deprecated (since := "2025-12-22")] alias exp.ev_coev := ihom.ev_coev
@[deprecated (since := "2025-12-22")] alias exp.coev_ev := ihom.coev_ev
@[deprecated (since := "2025-12-22")] alias exp.ev_coev_assoc := ihom.ev_coev_assoc
@[deprecated (since := "2025-12-22")] alias exp.coev_ev_assoc := ihom.coev_ev_assoc
@[deprecated (since := "2025-12-22")] alias CartesianClosed.curry := MonoidalClosed.curry
@[deprecated (since := "2025-12-22")] alias CartesianClosed.uncurry := MonoidalClosed.uncurry
@[deprecated (since := "2025-12-22")] alias CartesianClosed.homEquiv_apply_eq :=
  MonoidalClosed.homEquiv_apply_eq
@[deprecated (since := "2025-12-22")] alias CartesianClosed.homEquiv_symm_apply_eq :=
  MonoidalClosed.homEquiv_symm_apply_eq
@[deprecated (since := "2025-12-22")] alias CartesianClosed.curry_natural_left :=
  MonoidalClosed.curry_natural_left
@[deprecated (since := "2025-12-22")] alias CartesianClosed.curry_natural_left_assoc :=
  MonoidalClosed.curry_natural_left_assoc
@[deprecated (since := "2025-12-22")] alias CartesianClosed.curry_natural_right :=
  MonoidalClosed.curry_natural_right
@[deprecated (since := "2025-12-22")] alias CartesianClosed.curry_natural_right_assoc :=
  MonoidalClosed.curry_natural_right_assoc
@[deprecated (since := "2025-12-22")] alias CartesianClosed.uncurry_natural_right :=
  MonoidalClosed.uncurry_natural_right
@[deprecated (since := "2025-12-22")] alias CartesianClosed.uncurry_natural_right_assoc :=
  MonoidalClosed.uncurry_natural_right_assoc
@[deprecated (since := "2025-12-22")] alias CartesianClosed.uncurry_natural_left :=
  MonoidalClosed.uncurry_natural_left
@[deprecated (since := "2025-12-22")] alias CartesianClosed.uncurry_natural_left_assoc :=
  MonoidalClosed.uncurry_natural_left_assoc
@[deprecated (since := "2025-12-22")] alias CartesianClosed.uncurry_curry :=
  MonoidalClosed.uncurry_curry
@[deprecated (since := "2025-12-22")] alias CartesianClosed.curry_uncurry :=
  MonoidalClosed.curry_uncurry
@[deprecated (since := "2025-12-22")] alias CartesianClosed.curry_eq_iff :=
  MonoidalClosed.curry_eq_iff
@[deprecated (since := "2025-12-22")] alias CartesianClosed.eq_curry_iff :=
  MonoidalClosed.eq_curry_iff
@[deprecated (since := "2025-12-22")] alias CartesianClosed.uncurry_eq :=
  MonoidalClosed.uncurry_eq
@[deprecated (since := "2025-12-22")] alias CartesianClosed.curry_eq :=
  MonoidalClosed.curry_eq
@[deprecated (since := "2025-12-22")] alias CartesianClosed.uncurry_id_eq_ev :=
  MonoidalClosed.uncurry_id_eq_ev
@[deprecated (since := "2025-12-22")] alias CartesianClosed.curry_id_eq_coev :=
  MonoidalClosed.curry_id_eq_coev
@[deprecated (since := "2025-12-22")] alias CartesianClosed.curry_injective :=
  MonoidalClosed.curry_injective
@[deprecated (since := "2025-12-22")] alias CartesianClosed.uncurry_injective :=
  MonoidalClosed.uncurry_injective
@[deprecated (since := "2025-12-22")] alias expUnitNatIso := MonoidalClosed.unitNatIso
@[deprecated (since := "2025-12-22")] alias expUnitIsoSelf := MonoidalClosed.unitIsoSelf
@[deprecated (since := "2025-12-22")] alias pre := MonoidalClosed.pre
@[deprecated (since := "2025-12-22")] alias prod_map_pre_app_comp_ev :=
  MonoidalClosed.id_tensor_pre_app_comp_ev
@[deprecated (since := "2025-12-22")] alias uncurry_pre :=
  MonoidalClosed.uncurry_pre
@[deprecated (since := "2025-12-22")] alias coev_app_comp_pre_app :=
  MonoidalClosed.coev_app_comp_pre_app
@[deprecated (since := "2025-12-22")] alias pre_id :=
  MonoidalClosed.pre_id
@[deprecated (since := "2025-12-22")] alias pre_map :=
  MonoidalClosed.pre_map
@[deprecated (since := "2025-12-22")] alias internalHom :=
  MonoidalClosed.internalHom

end CategoryTheory
