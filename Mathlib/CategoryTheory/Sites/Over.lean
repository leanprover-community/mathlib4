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

/-! # Localization

In this file, given a Grothendieck topology `J` on a category `C` and `X : C`, we construct
a Grothendieck topology `J.over X` on the category `Over X`. In order to do this,
we first construct a bijection `Sieve.overEquiv Y : Sieve Y ≃ Sieve Y.left`
for all `Y : Over X`. Then, as it is stated in SGA 4 III 5.2.1, a sieve of `Y : Over X`
is covering for `J.over X` if and only if the corresponding sieve of `Y.left`
is covering for `J`. As a result, the forgetful functor
`Over.forget X : Over X ⥤ X` is both cover-preserving and cover-lifting.

-/

@[expose] public section

universe w v' v u' u

namespace CategoryTheory

open Category

variable {C : Type u} [Category.{v} C]

namespace Presieve

@[simp]
lemma functorPullback_map_overForget {X : C} {Y : Over X} (S : Presieve Y) :
    (S.map (Over.forget X)).functorPullback (Over.forget X) = S := by
  let R : Presieve Y.left := fun Z g ↦ S (Over.homMk g : Over.mk (g ≫ Y.hom) ⟶ Y)
  suffices hR : (R.functorPullback (Over.forget X)) = S by
    rw [← hR, functorPullback_map_functorPullback]
  funext Z f
  obtain ⟨Z, fZ, rfl⟩ := Z.mk_surjective
  obtain ⟨g : Z ⟶ Y.left, rfl : g ≫ Y.hom = fZ, rfl⟩ := Over.homMk_surjective f
  rfl

@[simp]
lemma map_functorPullback_overForget {X : C} {Y : Over X} (R : Presieve Y.left) :
    (R.functorPullback (Over.forget X)).map (Over.forget X) = R :=
  le_antisymm (map_functorPullback _) fun Z g hg ↦
    map.of (u := (Over.homMk g : Over.mk (g ≫ Y.hom) ⟶ Y)) hg

/-- The equivalence `Presieve Y ≃ Presieve Y.left` for all `Y : Over X`. -/
@[simps]
def overEquiv {X : C} (Y : Over X) : Presieve Y ≃o Presieve Y.left where
  toFun S := map (Over.forget X) S
  invFun S' := functorPullback (Over.forget X) S'
  left_inv := functorPullback_map_overForget
  right_inv := map_functorPullback_overForget
  map_rel_iff' := ⟨fun h ↦ by simpa using functorPullback_monotone h, fun h ↦ map_monotone h⟩

end Presieve

namespace Sieve

@[simp]
lemma functorPushforward_overForget_arrows {X : C} {Y : Over X} (S : Sieve Y) :
    S.arrows.functorPushforward (Over.forget X) = S.arrows.map (Over.forget X) := by
  refine le_antisymm ?_ (S.arrows.map_le_functorPushforward (Over.forget X))
  rintro Z - ⟨W, fW, fZ, h, rfl⟩
  exact Presieve.map_map (S.downward_closed h (Over.homMk fZ : Over.mk (fZ ≫ W.hom) ⟶ W))

@[simp]
lemma functorPullback_functorPushforward_overForget {X : C} {Y : Over X} (S : Sieve Y) :
    (S.functorPushforward (Over.forget X)).functorPullback (Over.forget X) = S := by
  apply arrows_ext
  simp

@[simp]
lemma functorPushforward_functorPullback_overForget {X : C} {Y : Over X} (S : Sieve Y.left) :
    (S.functorPullback (Over.forget X)).functorPushforward (Over.forget X) = S := by
  apply arrows_ext
  simp [← arrows_generate_map_eq_functorPushforward]

/-- The equivalence `Sieve Y ≃ Sieve Y.left` for all `Y : Over X`. -/
@[simps]
def overEquiv {X : C} (Y : Over X) : Sieve Y ≃o Sieve Y.left where
  toFun := functorPushforward (Over.forget X)
  invFun := functorPullback (Over.forget X)
  left_inv := functorPullback_functorPushforward_overForget
  right_inv := functorPushforward_functorPullback_overForget
  map_rel_iff' := by
    rw [Equiv.coe_fn_mk]
    exact ⟨fun h ↦ by simpa using functorPullback_monotone _ _ h,
      fun h ↦ functorPushforward_monotone _ _ h⟩

@[deprecated (since := "2026-07-08")] alias overEquiv_top := map_top
@[deprecated (since := "2026-07-08")] alias overEquiv_symm_top := map_top
@[deprecated (since := "2026-07-08")] alias overEquiv_bot := map_bot
@[deprecated (since := "2026-07-08")] alias overEquiv_symm_bot := map_bot
@[deprecated (since := "2026-07-08")] alias overEquiv_le_overEquiv_iff := RelIso.map_rel_iff

set_option backward.defeqAttrib.useBackward true in
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

set_option backward.defeqAttrib.useBackward true in
lemma overEquiv_iff {X : C} {Y : Over X} (S : Sieve Y) {Z : C} (f : Z ⟶ Y.left) :
    overEquiv Y S f ↔ S (Over.homMk f : Over.mk (f ≫ Y.hom) ⟶ Y) := by
  obtain ⟨S, rfl⟩ := (overEquiv Y).symm.surjective S
  simp

lemma overEquiv_ofArrows {X : C} {Y : Over X} {I : Type*} (Z : I → Over X) (g : ∀ i, Z i ⟶ Y) :
    overEquiv Y (ofArrows Z g) = ofArrows (fun i => (Z i).left) (fun i => (g i).left) := by
  simp [Sieve.overEquiv, functorPushforward_ofArrows]

set_option backward.defeqAttrib.useBackward true in
lemma overEquiv_preOneHypercover_sieve₁ {X : C} {Y : Over X} (E : PreOneHypercover.{w} Y)
    {i₁ i₂ : E.I₀} {W : Over X} (p₁ : W ⟶ E.X i₁) (p₂ : W ⟶ E.X i₂) :
    overEquiv W (E.sieve₁ p₁ p₂) =
      (E.map (Over.forget X)).sieve₁ p₁.left p₂.left := by
  ext
  rw [overEquiv_iff]
  refine ⟨fun ⟨k, b, hb₁, hb₂⟩ ↦ ⟨k, b.left, congr($(hb₁).left), congr($(hb₂).left)⟩, ?_⟩
  intro ⟨k, b, hb₁, hb₂⟩
  exact ⟨k, Over.homMk b (by simpa using (hb₁ =≫ (E.X i₁).hom).symm), by cat_disch, by cat_disch⟩

lemma overEquiv_generate {X : C} {Y : Over X} (R : Presieve Y) :
    overEquiv Y (.generate R) = .generate (Presieve.functorPushforward (Over.forget X) R) := by
  refine le_antisymm (fun Z g hg ↦ ?_) ?_
  · rw [overEquiv_iff] at hg
    obtain ⟨W, u, v, hv, huv⟩ := hg
    exact ⟨W.left, u.left, v.left, ⟨W, v, 𝟙 _, hv, by simp⟩, congr($(huv).left)⟩
  · rw [generate_le_iff]
    rintro Z g ⟨W, u, v, hu, rfl⟩
    exact (overEquiv_iff _ _).mpr ⟨W, Over.homMk v, u, hu, rfl⟩

set_option backward.defeqAttrib.useBackward true in
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

set_option backward.defeqAttrib.useBackward true in
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

set_option backward.defeqAttrib.useBackward true in
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

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma overEquiv_functorPullback_post {D : Type*} [Category* D] (F : C ⥤ D) {X : C}
    (U : Over X) (S : Sieve ((Over.post F).obj U)) :
    (Sieve.overEquiv U) (Sieve.functorPullback (Over.post F) S) =
      Sieve.functorPullback F ((Sieve.overEquiv ((Over.post F).obj U)) S) := by
  refine le_antisymm ?_ ?_
  · dsimp [Sieve.overEquiv]
    rw [Sieve.functorPushforward_le_iff_le_functorPullback, ← Sieve.functorPullback_comp]
    simp_rw [← CategoryTheory.Over.post_forget_eq_forget_comp, Sieve.functorPullback_comp]
    exact Sieve.functorPullback_monotone _ _ (Sieve.le_functorPushforward_pullback _ _)
  · intro Z g hg
    rw [Sieve.overEquiv_iff]
    dsimp [Presieve.functorPullback]
    convert! (Sieve.overEquiv_iff _ _).mp hg
    simp

set_option backward.isDefEq.respectTransparency false in
lemma overEquiv_functorPushforward_post {D : Type*} [Category* D] (F : C ⥤ D) {X : C}
    (U : Over X) (S : Sieve U) :
    (Sieve.overEquiv _) (Sieve.functorPushforward (Over.post F) S) =
      Sieve.functorPushforward F ((Sieve.overEquiv _) S) := by
  simp [Sieve.overEquiv, ← Sieve.functorPushforward_comp, ← Over.post_forget_eq_forget_comp]

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
  simpa only [mem_over_iff, OrderIso.apply_symm_apply] using hS

lemma over_forget_coverPreserving (X : C) :
    CoverPreserving (J.over X) J (Over.forget X) where
  cover_preserve hS := hS

lemma over_forget_compatiblePreserving (X : C) :
    CompatiblePreserving J (Over.forget X) where
  compatible {_ Z _ _ hx Y₁ Y₂ W f₁ f₂ g₁ g₂ hg₁ hg₂ h} := by
    let W' : Over X := Over.mk (f₁ ≫ Y₁.hom)
    let g₁' : W' ⟶ Y₁ := Over.homMk f₁
    let g₂' : W' ⟶ Y₂ := Over.homMk f₂ (by simpa using! h.symm =≫ Z.hom)
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
    simpa [mem_over_iff] using! hS

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma over_map_compatiblePreserving {X Y : C} (f : X ⟶ Y) :
    CompatiblePreserving (J.over Y) (Over.map f) where
  compatible {F Z _ x hx Y₁ Y₂ W f₁ f₂ g₁ g₂ hg₁ hg₂ h} := by
    let W' : Over X := Over.mk (f₁.left ≫ Y₁.hom)
    let g₁' : W' ⟶ Y₁ := Over.homMk f₁.left
    let g₂' : W' ⟶ Y₂ := Over.homMk f₂.left
      (by simpa using! (Over.forget _).congr_map h.symm =≫ Z.hom)
    let e : (Over.map f).obj W' ≅ W := Over.isoMk (Iso.refl _)
      (by simpa [W'] using! (Over.w f₁).symm)
    convert congr_arg (F.obj.map e.inv.op)
      (hx g₁' g₂' hg₁ hg₂ (by ext; exact (Over.forget _).congr_map h)) using 1
    all_goals
      dsimp [e, W', g₁', g₂']
      rw [← Functor.map_comp_apply]
      apply ConcreteCategory.congr_hom
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

instance {D : Type*} [Category* D] (K : GrothendieckTopology D)
    (F : C ⥤ D) (X : C) [F.IsCocontinuous J K] :
    (Over.post (X := X) F).IsCocontinuous (J.over X) (K.over _) where
  cover_lift {U} S hS := by
    rw [GrothendieckTopology.mem_over_iff] at hS ⊢
    rw [Sieve.overEquiv_functorPullback_post]
    exact F.cover_lift J K hS

variable {J} in
lemma _root_.CategoryTheory.CoverPreserving.overPost {D : Type*} [Category* D]
    {K : GrothendieckTopology D} {F : C ⥤ D} (X : C) (h : CoverPreserving J K F) :
    CoverPreserving (J.over X) (K.over _) (Over.post (X := X) F) where
  cover_preserve {U} S hS := by
    rw [GrothendieckTopology.mem_over_iff] at hS ⊢
    rw [Sieve.overEquiv_functorPushforward_post]
    exact h.cover_preserve hS

set_option backward.defeqAttrib.useBackward true in
instance {J : GrothendieckTopology C} (X : C) :
    (Over.forget X).PreservesOneHypercovers (J.over _) J := by
  intro Y E
  refine ⟨?_, ?_⟩
  · dsimp
    rw [dsimp% PreZeroHypercover.sieve₀_map (F := Over.forget X)]
    exact E.mem₀
  · intro i₁ i₂ W p₁ p₂ w
    have := w =≫ Over.hom _
    simp only [Over.forget_obj, Over.forget_map, Category.assoc, Over.w] at this
    have := E.mem₁ i₁ i₂ (Over.homMk (U := Over.mk (p₁ ≫ Over.hom _)) p₁)
      (Over.homMk (U := Over.mk (p₁ ≫ Over.hom _)) p₂ this.symm) (by ext; simpa)
    rwa [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_preOneHypercover_sieve₁] at this

set_option backward.defeqAttrib.useBackward true in
instance {D : Type*} [Category* D] {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) (X : C) [Functor.PreservesOneHypercovers.{w} F J K] :
    Functor.PreservesOneHypercovers.{w} (Over.post F) (J.over X) (K.over _) := by
  intro Y E
  let E' := (E.map (Over.forget X) J).map F K
  refine ⟨?_, ?_⟩
  · dsimp [-Over.post_obj]
    rw [PreZeroHypercover.sieve₀_map, GrothendieckTopology.mem_over_iff,
      Sieve.functorPushforward_ofArrows, Sieve.overEquiv_ofArrows]
    exact E'.mem₀
  · intro i₁ i₂ W p₁ p₂ w
    simp_rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_preOneHypercover_sieve₁,
      ← PreOneHypercover.map_comp, Over.post_forget_eq_forget_comp, PreOneHypercover.map_comp]
    exact E'.mem₁ _ _ _ _ congr($(w).left)

instance {D : Type*} [Category* D] {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} (X : C) (Y : D) (f : F.obj X ⟶ Y)
    [(Over.post F).IsContinuous (J.over X) (K.over _)] :
    (Over.post F ⋙ Over.map f).IsContinuous (J.over X) (K.over Y) :=
  Functor.isContinuous_comp _ _ _ (K.over _) _

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

set_option backward.defeqAttrib.useBackward true in
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

set_option backward.defeqAttrib.useBackward true in
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

set_option backward.defeqAttrib.useBackward true in
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

set_option backward.defeqAttrib.useBackward true in
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

variable {A : Type u'} [Category.{v'} A]

set_option backward.defeqAttrib.useBackward true in
/-- For `f : X ⟶ Y`, `F.over Y` viewed as a sheaf on `Over X` is isomorphic to `F.Over X`. -/
@[simps! +dsimpLhs]
def Sheaf.pushforwardOverMapIso (F : Sheaf J A) {X Y : C} (f : X ⟶ Y) :
    ((Over.map f).sheafPushforwardContinuous A (J.over X) (J.over Y)).obj (F.over Y) ≅
      F.over X :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by simp))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- For `f : X ⟶ Y`, this is the morphism from `F.over Y` to the pushforward of `F.over X`
along `Over.pullback f` induced by `Limits.pullback.fst`. -/
@[simps]
noncomputable
def Sheaf.toPushforwardOverPullback [Limits.HasPullbacks C] (F : Sheaf J A)
    {X Y : C} (f : X ⟶ Y) :
    F.over Y ⟶ ((Over.pullback f).sheafPushforwardContinuous A _ _).obj (F.over X) where
  hom.app U := F.obj.map (.op <| Limits.pullback.fst _ _)
  hom.naturality := by simp [← Functor.map_comp, ← op_comp]

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
    simp +instances only [GrothendieckTopology.mem_over_iff, OrderIso.apply_symm_apply,
      ← Precoverage.toGrothendieck_toCoverage, Coverage.mem_toGrothendieck,
      Over.left] at hR
    induction hR with
    | of Z S hS =>
      rw [Sieve.overEquiv_symm_generate]
      exact .of _ _ (by simpa)
    | top =>
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
      Sieve.overEquiv, RelIso.coe_fn_mk, Equiv.coe_fn_mk,
      ← Sieve.generate_map_eq_functorPushforward]
    exact Precoverage.Saturate.of _ _ hR

end

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance {X : C} (f : Over X) :
    f.iteratedSliceEquiv.inverse.IsDenseSubsite (J.over _) ((J.over _).over _) where
  functorPushforward_mem_iff := by
    simp [GrothendieckTopology.mem_over_iff, Sieve.overEquiv,
      ← Over.iteratedSliceBackward_forget_forget f, Sieve.functorPushforward_comp]

instance {X : C} (f : Over X) :
    f.iteratedSliceForward.IsContinuous ((J.over _).over _) (J.over _) :=
  inferInstanceAs (f.iteratedSliceEquiv.functor.IsContinuous _ _)

instance {X : C} (f : Over X) :
    f.iteratedSliceForward.IsCocontinuous ((J.over _).over _) (J.over _) :=
  inferInstanceAs (f.iteratedSliceEquiv.functor.IsCocontinuous _ _)

instance {X : C} (f : Over X) :
    f.iteratedSliceBackward.IsContinuous (J.over _) ((J.over _).over _) :=
  inferInstanceAs (f.iteratedSliceEquiv.inverse.IsContinuous _ _)

instance {X : C} (f : Over X) :
    f.iteratedSliceBackward.IsCocontinuous (J.over _) ((J.over _).over _) :=
  inferInstanceAs (f.iteratedSliceEquiv.inverse.IsCocontinuous _ _)

end CategoryTheory
