/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Shapes.Connected
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Functor.Flat

/-! Localization

In this file, given a Grothendieck topology `J` on a category `C` and `X : C`, we construct
a Grothendieck topology `J.over X` on the category `Over X`. In order to do this,
we first construct a bijection `Sieve.overEquiv Y : Sieve Y ≃ Sieve Y.left`
for all `Y : Over X`. Then, as it is stated in SGA 4 III 5.2.1, a sieve of `Y : Over X`
is covering for `J.over X` if and only if the corresponding sieve of `Y.left`
is covering for `J`. As a result, the forgetful functor
`Over.forget X : Over X ⥤ X` is both cover-preserving and cover-lifting.

-/

@[expose] public section

universe v' v u' u

namespace CategoryTheory

open Category

variable {C : Type u} [Category.{v} C]

@[simp]
lemma Presieve.map_functorPullback_overForget {X : C} {Y : Over X} (R : Presieve Y.left) :
    Presieve.map (Over.forget X) (.functorPullback (Over.forget X) R) = R := by
  refine le_antisymm (map_functorPullback _) fun Z g hg ↦ ?_
  let g' : Over.mk (g ≫ Y.hom) ⟶ Y := Over.homMk g
  exact Presieve.map.of (u := g') hg

namespace Sieve

set_option backward.isDefEq.respectTransparency false in
/-- The equivalence `Sieve Y ≃ Sieve Y.left` for all `Y : Over X`. -/
def overEquiv {X : C} (Y : Over X) :
    Sieve Y ≃ Sieve Y.left where
  toFun S := Sieve.functorPushforward (Over.forget X) S
  invFun S' := Sieve.functorPullback (Over.forget X) S'
  left_inv S := by
    ext Z g
    dsimp [Presieve.functorPullback, Presieve.functorPushforward]
    constructor
    · rintro ⟨W, a, b, h, w⟩
      let c : Z ⟶ W := Over.homMk b
        (by rw [← Over.w g, w, assoc, Over.w a])
      rw [show g = c ≫ a by ext; exact w]
      exact S.downward_closed h _
    · intro h
      exact ⟨Z, g, 𝟙 _, h, by simp⟩
  right_inv S := by
    ext Z g
    dsimp [Presieve.functorPullback, Presieve.functorPushforward]
    constructor
    · rintro ⟨W, a, b, h, rfl⟩
      exact S.downward_closed h _
    · intro h
      exact ⟨Over.mk ((g ≫ Y.hom)), Over.homMk g, 𝟙 _, h, by simp⟩

@[simp]
lemma overEquiv_top {X : C} (Y : Over X) :
    overEquiv Y ⊤ = ⊤ := by
  ext Z g
  simp only [top_apply, iff_true]
  dsimp [overEquiv, Presieve.functorPushforward]
  exact ⟨Y, 𝟙 Y, g, by simp, by simp⟩

@[simp]
lemma overEquiv_symm_top {X : C} (Y : Over X) :
    (overEquiv Y).symm ⊤ = ⊤ :=
  (overEquiv Y).injective (by simp)

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma overEquiv_bot {X : C} (Y : Over X) : overEquiv Y ⊥ = ⊥ := by
  simp [overEquiv]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma overEquiv_symm_bot {X : C} (Y : Over X) : (overEquiv Y).symm ⊥ = ⊥ := by
  rw [overEquiv, Equiv.coe_fn_symm_mk, functorPullback_bot]

lemma overEquiv_le_overEquiv_iff {X : C} {Y : Over X} (R₁ R₂ : Sieve Y) :
    R₁.overEquiv Y ≤ R₂.overEquiv Y ↔ R₁ ≤ R₂ := by
  refine ⟨fun h ↦ ?_, fun h ↦ Sieve.functorPushforward_monotone _ _ h⟩
  replace h : (overEquiv Y).symm (R₁.overEquiv Y) ≤ (overEquiv Y).symm (R₂.overEquiv Y) :=
    Sieve.functorPullback_monotone _ _ h
  simpa using h

set_option backward.isDefEq.respectTransparency false in
lemma overEquiv_pullback {X : C} {Y₁ Y₂ : Over X} (f : Y₁ ⟶ Y₂) (S : Sieve Y₂) :
    overEquiv _ (S.pullback f) = (overEquiv _ S).pullback f.left := by
  ext Z g
  dsimp [overEquiv, Presieve.functorPushforward]
  constructor
  · rintro ⟨W, a, b, h, rfl⟩
    exact ⟨W, a ≫ f, b, h, by simp⟩
  · rintro ⟨W, a, b, h, w⟩
    let T := Over.mk (b ≫ W.hom)
    let c : T ⟶ Y₁ := Over.homMk g (by dsimp [T]; rw [← Over.w a, ← reassoc_of% w, Over.w f])
    let d : T ⟶ W := Over.homMk b
    refine ⟨T, c, 𝟙 Z, ?_, by simp [T, c]⟩
    rw [show c ≫ f = d ≫ a by ext; exact w]
    exact S.downward_closed h _

lemma overEquiv_symm_pullback {X : C} {Y₁ Y₂ : Over X} (f : Y₁ ⟶ Y₂) (S : Sieve Y₂.left) :
    (overEquiv Y₁).symm (pullback f.left S) = pullback f ((overEquiv Y₂).symm S) :=
  functorPullback_pullback _ _ _

@[simp]
lemma overEquiv_symm_iff {X : C} {Y : Over X} (S : Sieve Y.left) {Z : Over X} (f : Z ⟶ Y) :
    (overEquiv Y).symm S f ↔ S f.left := by
  rfl

lemma overEquiv_iff {X : C} {Y : Over X} (S : Sieve Y) {Z : C} (f : Z ⟶ Y.left) :
    overEquiv Y S f ↔ S (Over.homMk f : Over.mk (f ≫ Y.hom) ⟶ Y) := by
  obtain ⟨S, rfl⟩ := (overEquiv Y).symm.surjective S
  simp

set_option backward.isDefEq.respectTransparency false in
lemma overEquiv_generate {X : C} {Y : Over X} (R : Presieve Y) :
    overEquiv Y (.generate R) = .generate (Presieve.functorPushforward (Over.forget X) R) := by
  refine le_antisymm (fun Z g hg ↦ ?_) ?_
  · rw [overEquiv_iff] at hg
    obtain ⟨W, u, v, hv, huv⟩ := hg
    exact ⟨W.left, u.left, v.left, ⟨W, v, 𝟙 _, hv, by simp⟩, congr($(huv).left)⟩
  · rw [generate_le_iff]
    rintro Z g ⟨W, u, v, hu, rfl⟩
    exact (overEquiv_iff _ _).mpr ⟨W, Over.homMk v, u, hu, rfl⟩

set_option backward.isDefEq.respectTransparency false in
lemma overEquiv_symm_generate {X : C} {Y : Over X} (R : Presieve Y.left) :
    (overEquiv Y).symm (.generate R) =
      .generate (Presieve.functorPullback (Over.forget X) R) := by
  refine le_antisymm (fun Z g hg ↦ ?_) ?_
  · rw [overEquiv_symm_iff] at hg
    obtain ⟨W, p, q, hq, hpq⟩ := hg
    refine ⟨.mk (q ≫ Y.hom), Over.homMk p (by simp [reassoc_of% hpq]), Over.homMk q rfl, hq, ?_⟩
    ext
    exact hpq
  · rw [generate_le_iff]
    exact fun Z g hg ↦ le_generate _ _ _ hg

@[simp]
lemma functorPushforward_over_map {X Y : C} (f : X ⟶ Y) (Z : Over X) (S : Sieve Z.left) :
    Sieve.functorPushforward (Over.map f) ((Sieve.overEquiv Z).symm S) =
      (Sieve.overEquiv ((Over.map f).obj Z)).symm S := by
  ext W g
  constructor
  · rintro ⟨T, a, b, ha, rfl⟩
    exact S.downward_closed ha _
  · intro hg
    exact ⟨Over.mk (g.left ≫ Z.hom), Over.homMk g.left,
      Over.homMk (𝟙 _) (by simpa using Over.w g), hg, by cat_disch⟩

set_option backward.isDefEq.respectTransparency false in
lemma overEquiv_functorPullback_map {X Y : C} (f : X ⟶ Y) (U : Over X)
    (S : Sieve ((Over.map f).obj U)) :
    overEquiv U (S.functorPullback (Over.map f)) =
      overEquiv ((Over.map f).obj U) S := by
  ext Z g
  let u : (Over.map f).obj (Over.mk (g ≫ U.hom)) ⟶ Over.mk (g ≫ U.hom ≫ f) :=
    Over.homMk (𝟙 Z) (by simp)
  have heq : (Over.map f).map (Over.homMk (U := Over.mk (g ≫ U.hom)) g rfl) =
      u ≫ Over.homMk (V := (Over.map f).obj U) g rfl := by
    ext
    simp [u]
  have : IsIso u :=
    ⟨Over.homMk (𝟙 Z) (by simp), by ext; simp [u], by ext; simp [u]⟩
  rw [Sieve.overEquiv_iff, Sieve.overEquiv_iff]
  simp [Presieve.functorPullback, heq]

end Sieve

variable (J : GrothendieckTopology C)

namespace GrothendieckTopology

/-- The Grothendieck topology on the category `Over X` for any `X : C` that is
induced by a Grothendieck topology on `C`. -/
def over (X : C) : GrothendieckTopology (Over X) where
  sieves Y := Sieve.overEquiv Y ⁻¹' J Y.left
  top_mem' Y := by simp
  pullback_stable' Y₁ Y₂ S₁ f h₁ := by
    rw [Set.mem_preimage, Sieve.overEquiv_pullback]
    exact J.pullback_stable _ h₁
  transitive' Y S hS R hR := J.transitive hS _ fun Z f hf => by
    specialize hR ((Sieve.overEquiv_iff _ _).1 hf)
    rwa [Set.mem_preimage, Sieve.overEquiv_pullback] at hR

lemma mem_over_iff {X : C} {Y : Over X} (S : Sieve Y) :
    S ∈ (J.over X) Y ↔ Sieve.overEquiv _ S ∈ J Y.left := by
  rfl

lemma overEquiv_symm_mem_over {X : C} (Y : Over X) (S : Sieve Y.left) (hS : S ∈ J Y.left) :
    (Sieve.overEquiv Y).symm S ∈ (J.over X) Y := by
  simpa only [mem_over_iff, Equiv.apply_symm_apply] using hS

lemma over_forget_coverPreserving (X : C) :
    CoverPreserving (J.over X) J (Over.forget X) where
  cover_preserve hS := hS

set_option backward.isDefEq.respectTransparency false in
lemma over_forget_compatiblePreserving (X : C) :
    CompatiblePreserving J (Over.forget X) where
  compatible {_ Z _ _ hx Y₁ Y₂ W f₁ f₂ g₁ g₂ hg₁ hg₂ h} := by
    let W' : Over X := Over.mk (f₁ ≫ Y₁.hom)
    let g₁' : W' ⟶ Y₁ := Over.homMk f₁
    let g₂' : W' ⟶ Y₂ := Over.homMk f₂ (by simpa using h.symm =≫ Z.hom)
    exact hx g₁' g₂' hg₁ hg₂ (by ext; exact h)

instance (X : C) : (Over.forget X).IsCocontinuous (J.over X) J where
  cover_lift hS := J.overEquiv_symm_mem_over _ _ hS

instance (X : C) : (Over.forget X).IsContinuous (J.over X) J :=
  Functor.isContinuous_of_coverPreserving
    (over_forget_compatiblePreserving J X)
    (over_forget_coverPreserving J X)

/-- The pullback functor `Sheaf J A ⥤ Sheaf (J.over X) A` -/
abbrev overPullback (A : Type u') [Category.{v'} A] (X : C) :
    Sheaf J A ⥤ Sheaf (J.over X) A :=
  (Over.forget X).sheafPushforwardContinuous _ _ _

lemma over_map_coverPreserving {X Y : C} (f : X ⟶ Y) :
    CoverPreserving (J.over X) (J.over Y) (Over.map f) where
  cover_preserve {U S} hS := by
    obtain ⟨S, rfl⟩ := (Sieve.overEquiv U).symm.surjective S
    rw [Sieve.functorPushforward_over_map]
    apply overEquiv_symm_mem_over
    simpa [mem_over_iff] using hS

set_option backward.isDefEq.respectTransparency false in
lemma over_map_compatiblePreserving {X Y : C} (f : X ⟶ Y) :
    CompatiblePreserving (J.over Y) (Over.map f) where
  compatible {F Z _ x hx Y₁ Y₂ W f₁ f₂ g₁ g₂ hg₁ hg₂ h} := by
    let W' : Over X := Over.mk (f₁.left ≫ Y₁.hom)
    let g₁' : W' ⟶ Y₁ := Over.homMk f₁.left
    let g₂' : W' ⟶ Y₂ := Over.homMk f₂.left
      (by simpa using (Over.forget _).congr_map h.symm =≫ Z.hom)
    let e : (Over.map f).obj W' ≅ W := Over.isoMk (Iso.refl _)
      (by simpa [W'] using (Over.w f₁).symm)
    convert congr_arg (F.obj.map e.inv.op)
      (hx g₁' g₂' hg₁ hg₂ (by ext; exact (Over.forget _).congr_map h)) using 1
    all_goals
      dsimp [e, W', g₁', g₂']
      rw [← FunctorToTypes.map_comp_apply]
      apply congr_fun
      congr 1
      rw [← op_comp]
      congr 1
      ext
      simp

instance {X Y : C} (f : X ⟶ Y) : (Over.map f).IsContinuous (J.over X) (J.over Y) :=
  Functor.isContinuous_of_coverPreserving
    (over_map_compatiblePreserving J f)
    (over_map_coverPreserving J f)

instance {X Y : C} (f : X ⟶ Y) : (Over.map f).IsCocontinuous (J.over _) (J.over _) where
  cover_lift {U} S hS := by
    rw [J.mem_over_iff] at hS ⊢
    rwa [Sieve.overEquiv_functorPullback_map]

open Limits

lemma coverPreserving_overPullback [HasPullbacks C] {X Y : C} (f : X ⟶ Y) :
    CoverPreserving (J.over Y) (J.over X) (Over.pullback f) := by
  rw [← (Over.mapPullbackAdj f).isCocontinuous_iff_coverPreserving]
  infer_instance

instance [HasPullbacks C] {X Y : C} (f : X ⟶ Y) :
    (Over.pullback f).IsContinuous (J.over Y) (J.over X) :=
  (Over.mapPullbackAdj f).isContinuous_of_isCocontinuous _ _

section

variable {C : Type u'} [Category* C] [HasBinaryProducts C] {J : GrothendieckTopology C}

set_option backward.isDefEq.respectTransparency false in
theorem coverPreserving_over_star (X : C) :
    CoverPreserving J (J.over X) (Over.star X) where
  cover_preserve {U} S hs := by
    refine J.superset_covering ?_ (J.pullback_stable prod.snd hs)
    intro y f hf
    dsimp [Sieve.overEquiv]
    rw [← Presieve.functorPushforward_comp]
    refine ⟨_, _, prod.lift (f ≫ prod.fst) (𝟙 _), hf, Limits.prod.hom_ext ?_ ?_⟩ <;> simp

instance (X : C) : (Over.star X).IsContinuous J (J.over X) :=
  Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat (J.over X) (Over.star X)) (coverPreserving_over_star X)

end

section

variable (A : Type u') [Category.{v'} A]

/-- The pullback functor `Sheaf (J.over Y) A ⥤ Sheaf (J.over X) A` induced
by a morphism `f : X ⟶ Y`. -/
abbrev overMapPullback {X Y : C} (f : X ⟶ Y) :
    Sheaf (J.over Y) A ⥤ Sheaf (J.over X) A :=
  (Over.map f).sheafPushforwardContinuous _ _ _

section

variable {X Y : C} {f g : X ⟶ Y} (h : f = g)

/-- Two identical morphisms give isomorphic `overMapPullback` functors on sheaves. -/
@[simps!]
def overMapPullbackCongr :
    J.overMapPullback A f ≅ J.overMapPullback A g :=
  Functor.sheafPushforwardContinuousIso (Over.mapCongr _ _ h) _ _ _

lemma overMapPullbackCongr_eq_eqToIso :
    J.overMapPullbackCongr A h = eqToIso (by subst h; rfl) := by
  aesop

end

/-- Applying `overMapPullback` to the identity map gives the identity functor. -/
@[simps!]
def overMapPullbackId (X : C) :
    J.overMapPullback A (𝟙 X) ≅ 𝟭 _ :=
  Functor.sheafPushforwardContinuousId' (Over.mapId X) _ _

/-- The composition of two `overMapPullback` functors identifies to
`overMapPullback` for the composition. -/
@[simps!]
def overMapPullbackComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    J.overMapPullback A g ⋙ J.overMapPullback A f ≅
      J.overMapPullback A (f ≫ g) :=
  Functor.sheafPushforwardContinuousComp' (Over.mapComp f g).symm _ _ _ _

@[reassoc]
lemma overMapPullback_comp_id {X Y : C} (f : X ⟶ Y) :
    (J.overMapPullbackComp A f (𝟙 Y)).inv ≫
      Functor.whiskerRight (J.overMapPullbackId A Y).hom _ ≫ (Functor.leftUnitor _).hom =
    (overMapPullbackCongr _ _ (by simp)).hom := by
  ext
  dsimp
  simp only [overMapPullbackComp_inv_app_hom_app, overMapPullbackId_hom_app_hom_app,
    comp_id, ← Functor.map_comp, ← op_comp]
  congr
  cat_disch

@[reassoc]
lemma overMapPullback_id_comp {X Y : C} (f : X ⟶ Y) :
    (J.overMapPullbackComp A (𝟙 X) f).inv ≫
      Functor.whiskerLeft _ (J.overMapPullbackId A X).hom ≫ (Functor.rightUnitor _).hom =
    (overMapPullbackCongr _ _ (by simp)).hom := by
  ext
  dsimp
  simp only [overMapPullbackComp_inv_app_hom_app, overMapPullbackId_hom_app_hom_app,
    Functor.sheafPushforwardContinuous_obj_obj_map, Quiver.Hom.unop_op,
    comp_id, ← Functor.map_comp, ← op_comp]
  congr
  cat_disch

@[reassoc]
lemma overMapPullback_assoc {X Y Z T : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (J.overMapPullbackComp A f (g ≫ h)).inv ≫
      Functor.whiskerRight (J.overMapPullbackComp A g h).inv _ ≫
        (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft _ (J.overMapPullbackComp A f g).hom ≫
            (J.overMapPullbackComp A (f ≫ g) h).hom =
    (overMapPullbackCongr _ _ (by simp)).hom := by
  ext
  dsimp
  simp only [overMapPullbackComp_inv_app_hom_app,
    overMapPullbackComp_hom_app_hom_app, Functor.sheafPushforwardContinuous_obj_obj_map,
    Quiver.Hom.unop_op, ← Functor.map_comp, ← op_comp, id_comp, assoc]
  congr
  cat_disch

end

end GrothendieckTopology

variable {J}

/-- Given `F : Sheaf J A` and `X : C`, this is the pullback of `F` on `J.over X`. -/
abbrev Sheaf.over {A : Type u'} [Category.{v'} A] (F : Sheaf J A) (X : C) :
    Sheaf (J.over X) A := (J.overPullback A X).obj F

section

-- TODO: Generalize this section to arbitrary precoverages.

variable (K : Precoverage C) [K.HasPullbacks] [K.IsStableUnderBaseChange]

/-- The Grothendieck topology on `Over X`, obtained from localizing the topology generated
by the precoverage `K`, is generated by the preimage of `K`. -/
lemma over_toGrothendieck_eq_toGrothendieck_comap_forget (X : C) :
    K.toGrothendieck.over X = (K.comap (Over.forget X)).toGrothendieck := by
  refine le_antisymm ?_ ?_
  · intro ⟨Y, right, (s : Y ⟶ X)⟩ R hR
    obtain ⟨(R : Sieve Y), rfl⟩ := (Sieve.overEquiv _).symm.surjective R
    simp +instances only [GrothendieckTopology.mem_over_iff, Equiv.apply_symm_apply,
      ← Precoverage.toGrothendieck_toCoverage] at hR
    induction hR with
    | of Z S hS =>
      rw [Sieve.overEquiv_symm_generate]
      exact .of _ _ (by simpa)
    | top =>
      rw [Sieve.overEquiv_symm_top]
      simp
    | transitive Y R S hR H ih ih' =>
      refine GrothendieckTopology.transitive _ (ih s) _ fun Z g hg ↦ ?_
      obtain rfl : right = Z.right := Subsingleton.elim _ _
      rw [← Sieve.overEquiv_symm_pullback]
      exact ih' hg Z.hom
  · rw [Precoverage.toGrothendieck_le_iff_le_toPrecoverage]
    intro Y R hR
    rw [Precoverage.mem_comap_iff] at hR
    rw [GrothendieckTopology.mem_toPrecoverage_iff, GrothendieckTopology.mem_over_iff,
      Sieve.overEquiv, Equiv.coe_fn_mk, ← Sieve.generate_map_eq_functorPushforward]
    exact Precoverage.Saturate.of _ _ hR

end

set_option backward.isDefEq.respectTransparency false in
instance {X : C} (f : Over X) :
    f.iteratedSliceEquiv.inverse.IsDenseSubsite (J.over _) ((J.over _).over _) where
  functorPushforward_mem_iff := by
    simp [GrothendieckTopology.mem_over_iff, Sieve.overEquiv,
      ← Over.iteratedSliceBackward_forget_forget f, Sieve.functorPushforward_comp]

instance {X : C} (f : Over X) :
    f.iteratedSliceForward.IsContinuous ((J.over _).over _) (J.over _) :=
  inferInstanceAs% (f.iteratedSliceEquiv.functor.IsContinuous _ _)

instance {X : C} (f : Over X) :
    f.iteratedSliceForward.IsCocontinuous ((J.over _).over _) (J.over _) :=
  inferInstanceAs% (f.iteratedSliceEquiv.functor.IsCocontinuous _ _)

instance {X : C} (f : Over X) :
    f.iteratedSliceBackward.IsContinuous (J.over _) ((J.over _).over _) :=
  inferInstanceAs% (f.iteratedSliceEquiv.inverse.IsContinuous _ _)

instance {X : C} (f : Over X) :
    f.iteratedSliceBackward.IsCocontinuous (J.over _) ((J.over _).over _) :=
  inferInstanceAs% (f.iteratedSliceEquiv.inverse.IsCocontinuous _ _)

end CategoryTheory
