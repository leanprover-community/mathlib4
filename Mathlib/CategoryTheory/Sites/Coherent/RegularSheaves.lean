/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Filippo A. E. Nuccio, Riccardo Brasca
-/
module

public import Mathlib.CategoryTheory.EffectiveEpi.Preserves
public import Mathlib.CategoryTheory.Limits.Final.ParallelPair
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Coherent.Basic
public import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
/-!

# Sheaves for the regular topology

This file characterises sheaves for the regular topology.

## Main results

* `equalizerCondition_iff_isSheaf`: In a preregular category with pullbacks, the sheaves for the
  regular topology are precisely the presheaves satisfying an equaliser condition with respect to
  effective epimorphisms.

* `isSheaf_of_projective`: In a preregular category in which every object is projective, every
  presheaf is a sheaf for the regular topology.
-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]

open Opposite Presieve Functor

/-- A presieve is *regular* if it consists of a single effective epimorphism. -/
class Presieve.regular {X : C} (R : Presieve X) : Prop where
  /-- `R` consists of a single epimorphism. -/
  single_epi : ∃ (Y : C) (f : Y ⟶ X), R = Presieve.ofArrows (fun (_ : Unit) ↦ Y)
    (fun (_ : Unit) ↦ f) ∧ EffectiveEpi f

namespace regularTopology

lemma equalizerCondition_w (P : Cᵒᵖ ⥤ D) {X B : C} {π : X ⟶ B} (c : PullbackCone π π) :
    P.map π.op ≫ P.map c.fst.op = P.map π.op ≫ P.map c.snd.op := by
  simp only [← Functor.map_comp, ← op_comp, c.condition]

/--
A contravariant functor on `C` satisfies `SingleEqualizerCondition` with respect to a morphism `π`
if it takes its kernel pair to an equalizer diagram.
-/
def SingleEqualizerCondition (P : Cᵒᵖ ⥤ D) ⦃X B : C⦄ (π : X ⟶ B) : Prop :=
  ∀ (c : PullbackCone π π) (_ : IsLimit c),
    Nonempty (IsLimit (Fork.ofι (P.map π.op) (equalizerCondition_w P c)))

/--
A contravariant functor on `C` satisfies `EqualizerCondition` if it takes kernel pairs of effective
epimorphisms to equalizer diagrams.
-/
def EqualizerCondition (P : Cᵒᵖ ⥤ D) : Prop :=
  ∀ ⦃X B : C⦄ (π : X ⟶ B) [EffectiveEpi π], SingleEqualizerCondition P π

/-- The equalizer condition is preserved by natural isomorphism. -/
theorem equalizerCondition_of_natIso {P P' : Cᵒᵖ ⥤ D} (i : P ≅ P')
    (hP : EqualizerCondition P) : EqualizerCondition P' := fun X B π _ c hc ↦
  ⟨Fork.isLimitOfIsos _ (hP π c hc).some _ (i.app _) (i.app _) (i.app _)⟩

set_option backward.isDefEq.respectTransparency false in
/-- Precomposing with a pullback-preserving functor preserves the equalizer condition. -/
theorem equalizerCondition_precomp_of_preservesPullback (P : Cᵒᵖ ⥤ D) (F : E ⥤ C)
    [∀ {X B} (π : X ⟶ B) [EffectiveEpi π], PreservesLimit (cospan π π) F]
    [F.PreservesEffectiveEpis] (hP : EqualizerCondition P) : EqualizerCondition (F.op ⋙ P) := by
  intro X B π _ c hc
  have h : P.map (F.map π).op = (F.op ⋙ P).map π.op := by simp
  refine ⟨(IsLimit.equivIsoLimit (ForkOfι.ext ?_ _ h)) ?_⟩
  · simp only [Functor.comp_map, op_map, Quiver.Hom.unop_op, ← map_comp, ← op_comp, c.condition]
  · refine (hP (F.map π) (PullbackCone.mk (F.map c.fst) (F.map c.snd) ?_) ?_).some
    · simp only [← map_comp, c.condition]
    · exact (isLimitMapConePullbackConeEquiv F c.condition)
        (isLimitOfPreserves F (hc.ofIsoLimit (PullbackCone.ext (Iso.refl _) (by simp) (by simp))))

/-- The canonical map to the explicit equalizer. -/
def mapToEqualizer (P : Cᵒᵖ ⥤ Type*) {W X B : C} (f : X ⟶ B)
    (g₁ g₂ : W ⟶ X) (w : g₁ ≫ f = g₂ ≫ f) :
    P.obj (op B) ⟶ { x : P.obj (op X) | P.map g₁.op x = P.map g₂.op x } :=
  TypeCat.ofHom fun t ↦
    ⟨P.map f.op t, by simp only [Set.mem_setOf_eq, ← comp_apply, ← Functor.map_comp, ← op_comp, w]⟩

@[deprecated (since := "2025-11-23")] alias MapToEqualizer := mapToEqualizer

theorem EqualizerCondition.bijective_mapToEqualizer_pullback' {P : Cᵒᵖ ⥤ Type*}
    (hP : EqualizerCondition P) {X B : C} {π : X ⟶ B} [EffectiveEpi π]
    (c : PullbackCone π π) (hc : IsLimit c) :
    Function.Bijective (mapToEqualizer P π c.fst c.snd c.condition) := by
  specialize hP π _ hc
  rw [Types.type_equalizer_iff_unique] at hP
  rw [Function.bijective_iff_existsUnique]
  intro ⟨b, hb⟩
  obtain ⟨a, ha₁, ha₂⟩ := hP b hb
  refine ⟨a, ?_, ?_⟩
  · ext
    simpa [mapToEqualizer] using ha₁
  · intro y h
    apply ha₂ y
    simpa [mapToEqualizer, Subtype.ext_iff] using h

theorem EqualizerCondition.bijective_mapToEqualizer_pullback {P : Cᵒᵖ ⥤ Type*}
    (hP : EqualizerCondition P) {X B : C} (π : X ⟶ B) [EffectiveEpi π] [HasPullback π π] :
    Function.Bijective
      (mapToEqualizer P π (pullback.fst π π) (pullback.snd π π) pullback.condition) :=
  bijective_mapToEqualizer_pullback' hP _ (pullback.isLimit _ _)

theorem EqualizerCondition.mk' (P : Cᵒᵖ ⥤ Type*)
    (hP : ∀ (X B : C) (π : X ⟶ B) [EffectiveEpi π] (c : PullbackCone π π) (_ : IsLimit c),
      Function.Bijective (mapToEqualizer P π c.fst c.snd c.condition)) :
    EqualizerCondition P := by
  intro X B π _ c hc
  specialize hP X B π c hc
  rw [Types.type_equalizer_iff_unique]
  rw [Function.bijective_iff_existsUnique] at hP
  intro b hb
  obtain ⟨a, ha₁, ha₂⟩ := hP ⟨b, hb⟩
  refine ⟨a, ?_, ?_⟩
  · simpa [Subtype.ext_iff, mapToEqualizer] using ha₁
  · intro y h
    apply ha₂ y
    simpa [mapToEqualizer, Subtype.ext_iff] using h

set_option backward.isDefEq.respectTransparency false in
theorem EqualizerCondition.mk (P : Cᵒᵖ ⥤ Type*)
    (hP : ∀ (X B : C) (π : X ⟶ B) [EffectiveEpi π] [HasPullback π π], Function.Bijective
    (mapToEqualizer P π (pullback.fst π π) (pullback.snd π π)
    pullback.condition)) : EqualizerCondition P := by
  intro X B π _ c hc
  have : HasPullback π π := ⟨c, hc⟩
  specialize hP X B π
  rw [Types.type_equalizer_iff_unique]
  rw [Function.bijective_iff_existsUnique] at hP
  intro b hb
  have h₁ : ((pullbackIsPullback π π).conePointUniqueUpToIso hc).hom ≫ c.fst =
    pullback.fst π π := by simp
  have hb' : P.map (pullback.fst π π).op b = P.map (pullback.snd _ _).op b := by
    rw [← h₁, op_comp, Functor.map_comp, comp_apply, hb]
    simp [← comp_apply, ← Functor.map_comp, ← op_comp]
  obtain ⟨a, ha₁, ha₂⟩ := hP ⟨b, hb'⟩
  refine ⟨a, ?_, ?_⟩
  · simpa [mapToEqualizer] using ha₁
  · simpa [mapToEqualizer] using ha₂

lemma equalizerCondition_w' (P : Cᵒᵖ ⥤ Type*) {X B : C} (π : X ⟶ B)
    [HasPullback π π] : P.map π.op ≫ P.map (pullback.fst π π).op =
    P.map π.op ≫ P.map (pullback.snd π π).op := by
  simp only [← Functor.map_comp, ← op_comp, pullback.condition]

set_option backward.isDefEq.respectTransparency false in
lemma mapToEqualizer_eq_comp (P : Cᵒᵖ ⥤ Type*) {X B : C} (π : X ⟶ B) [HasPullback π π] :
    mapToEqualizer P π (pullback.fst π π) (pullback.snd π π) pullback.condition =
    equalizer.lift (P.map π.op) (equalizerCondition_w' P π) ≫
    (Types.equalizerIso _ _).hom := by
  rw [← Iso.comp_inv_eq (α := Types.equalizerIso _ _)]
  apply equalizer.hom_ext
  aesop

set_option backward.isDefEq.respectTransparency false in
/-- An alternative phrasing of the explicit equalizer condition, using more categorical language. -/
theorem equalizerCondition_iff_isIso_lift (P : Cᵒᵖ ⥤ Type*) : EqualizerCondition P ↔
    ∀ (X B : C) (π : X ⟶ B) [EffectiveEpi π] [HasPullback π π],
      IsIso (equalizer.lift (P.map π.op) (equalizerCondition_w' P π)) := by
  constructor
  · intro hP X B π _ _
    have h := hP.bijective_mapToEqualizer_pullback π
    rw [← isIso_iff_bijective, mapToEqualizer_eq_comp] at h
    exact IsIso.of_isIso_comp_right (equalizer.lift (P.map π.op)
      (equalizerCondition_w' P π))
      (Types.equalizerIso _ _).hom
  · intro hP
    apply EqualizerCondition.mk
    intro X B π _ _
    rw [mapToEqualizer_eq_comp, ← isIso_iff_bijective]
    infer_instance

/-- `P` satisfies the equalizer condition iff its precomposition by an equivalence does. -/
theorem equalizerCondition_iff_of_equivalence (P : Cᵒᵖ ⥤ D)
    (e : C ≌ E) : EqualizerCondition P ↔ EqualizerCondition (e.op.inverse ⋙ P) :=
  ⟨fun h ↦ equalizerCondition_precomp_of_preservesPullback P e.inverse h, fun h ↦
    equalizerCondition_of_natIso (e.op.funInvIdAssoc P)
      (equalizerCondition_precomp_of_preservesPullback (e.op.inverse ⋙ P) e.functor h)⟩

set_option backward.isDefEq.respectTransparency false in
open WalkingParallelPair WalkingParallelPairHom in
theorem parallelPair_pullback_initial {X B : C} (π : X ⟶ B)
    (c : PullbackCone π π) (hc : IsLimit c) :
    (parallelPair (C := (Sieve.ofArrows (fun (_ : Unit) => X) (fun _ => π)).arrows.categoryᵒᵖ)
    (Y := op ((Presieve.categoryMk _ (c.fst ≫ π) ⟨_, c.fst, π, ofArrows.mk (), rfl⟩)))
    (X := op ((Presieve.categoryMk _ π (Sieve.ofArrows_mk _ _ Unit.unit))))
    ((ObjectProperty.homMk (Over.homMk c.fst)).op)
    ((ObjectProperty.homMk (Over.homMk c.snd c.condition.symm)).op)).Initial := by
  apply Limits.parallelPair_initial_mk
  · intro ⟨Z⟩
    obtain ⟨_, f, g, ⟨⟩, hh⟩ := Z.property
    let X' : (Presieve.ofArrows (fun () ↦ X) (fun () ↦ π)).category :=
      Presieve.categoryMk _ π (ofArrows.mk ())
    let f' : Z.obj.left ⟶ X'.obj.left := f
    exact ⟨(ObjectProperty.homMk (Over.homMk f')).op⟩
  · intro ⟨Z⟩ ⟨i⟩ ⟨j⟩
    have hi := Over.w i.hom
    have hj := Over.w j.hom
    dsimp at hi hj
    let ij := PullbackCone.IsLimit.lift hc i.hom.left j.hom.left (by simp [hi, hj])
    refine ⟨Quiver.Hom.op (ObjectProperty.homMk (Over.homMk ij)), ?_, ?_⟩
    all_goals congr; aesop

/--
Given a limiting pullback cone, the fork in `SingleEqualizerCondition` is limiting iff the diagram
in `Presheaf.isSheaf_iff_isLimit_coverage` is limiting.
-/
noncomputable def isLimit_forkOfι_equiv (P : Cᵒᵖ ⥤ D) {X B : C} (π : X ⟶ B)
    (c : PullbackCone π π) (hc : IsLimit c) :
    IsLimit (Fork.ofι (P.map π.op) (equalizerCondition_w P c)) ≃
    IsLimit (P.mapCone (Sieve.ofArrows (fun (_ : Unit) ↦ X) fun _ ↦ π).arrows.cocone.op) := by
  let S := (Sieve.ofArrows (fun (_ : Unit) => X) (fun _ => π)).arrows
  let X' := S.categoryMk π ⟨_, 𝟙 _, π, ofArrows.mk (), Category.id_comp _⟩
  let P' := S.categoryMk (c.fst ≫ π) ⟨_, c.fst, π, ofArrows.mk (), rfl⟩
  let fst : P' ⟶ X' := ObjectProperty.homMk (Over.homMk c.fst)
  let snd : P' ⟶ X' := ObjectProperty.homMk (Over.homMk c.snd c.condition.symm)
  let F : S.categoryᵒᵖ ⥤ D := S.diagram.op ⋙ P
  let G := parallelPair (P.map c.fst.op) (P.map c.snd.op)
  let H := parallelPair fst.op snd.op
  have : H.Initial := parallelPair_pullback_initial π c hc
  let i : H ⋙ F ≅ G := parallelPair.ext (Iso.refl _) (Iso.refl _) (by aesop) (by aesop)
  refine (IsLimit.equivOfNatIsoOfIso i.symm _ _ ?_).trans (Functor.Initial.isLimitWhiskerEquiv H _)
  refine Cone.ext (Iso.refl _) ?_
  rintro ⟨_ | _⟩
  all_goals aesop

lemma equalizerConditionMap_iff_nonempty_isLimit (P : Cᵒᵖ ⥤ D) ⦃X B : C⦄ (π : X ⟶ B)
    [HasPullback π π] : SingleEqualizerCondition P π ↔
      Nonempty (IsLimit (P.mapCone
        (Sieve.ofArrows (fun (_ : Unit) => X) (fun _ => π)).arrows.cocone.op)) := by
  constructor
  · intro h
    exact ⟨isLimit_forkOfι_equiv _ _ _ (pullbackIsPullback π π) (h _ (pullbackIsPullback π π)).some⟩
  · intro ⟨h⟩
    exact fun c hc ↦ ⟨(isLimit_forkOfι_equiv _ _ _ hc).symm h⟩

lemma equalizerCondition_iff_isSheaf (F : Cᵒᵖ ⥤ D) [Preregular C]
    [∀ {Y X : C} (f : Y ⟶ X) [EffectiveEpi f], HasPullback f f] :
    EqualizerCondition F ↔ Presheaf.IsSheaf (regularTopology C) F := by
  dsimp [regularTopology]
  rw [Presheaf.isSheaf_iff_isLimit_coverage]
  constructor
  · rintro hF X _ ⟨Y, f, rfl, _⟩
    exact (equalizerConditionMap_iff_nonempty_isLimit F f).1 (hF f)
  · intro hF Y X f _
    exact (equalizerConditionMap_iff_nonempty_isLimit F f).2 (hF _ ⟨_, f, rfl, inferInstance⟩)

lemma isSheafFor_regular_of_projective {X : C} (S : Presieve X) [S.regular] [Projective X]
    (F : Cᵒᵖ ⥤ Type*) : S.IsSheafFor F := by
  obtain ⟨Y, f, rfl, hf⟩ := Presieve.regular.single_epi (R := S)
  rw [isSheafFor_arrows_iff]
  refine fun x hx ↦ ⟨F.map (Projective.factorThru (𝟙 _) f).op <| x (), fun _ ↦ ?_, fun y h ↦ ?_⟩
  · simpa using (hx () () Y (𝟙 Y) (f ≫ (Projective.factorThru (𝟙 _) f)) (by simp)).symm
  · simp [← h (), ← comp_apply, ← Functor.map_comp, ← op_comp]

/-- Every presheaf is a sheaf for the regular topology if every object of `C` is projective. -/
theorem isSheaf_of_projective (F : Cᵒᵖ ⥤ D) [Preregular C] [∀ (X : C), Projective X] :
    Presheaf.IsSheaf (regularTopology C) F :=
  fun _ ↦ (isSheaf_coverage _ _).mpr fun S ⟨_, h⟩ ↦ have : S.regular := ⟨_, h⟩
    isSheafFor_regular_of_projective _ _

/-- Every Yoneda-presheaf is a sheaf for the regular topology. -/
lemma isSheaf_yoneda_obj [Preregular C] (W : C) :
    Presieve.IsSheaf (regularTopology C) (yoneda.obj W) := by
  rw [regularTopology, isSheaf_coverage]
  intro X S ⟨_, hS⟩
  have : S.regular := ⟨_, hS⟩
  obtain ⟨Y, f, rfl, hf⟩ := Presieve.regular.single_epi (R := S)
  have h_colim := isColimitOfEffectiveEpiStruct f hf.effectiveEpi.some
  rw [← Sieve.generateSingleton_eq, ← Presieve.ofArrows_pUnit] at h_colim
  intro x hx
  let x_ext := Presieve.FamilyOfElements.sieveExtend x
  have hx_ext := Presieve.FamilyOfElements.Compatible.sieveExtend hx
  let S := Sieve.generate (Presieve.ofArrows (fun () ↦ Y) (fun () ↦ f))
  obtain ⟨t, t_amalg, t_uniq⟩ :=
    (Sieve.forallYonedaIsSheaf_iff_colimit S).mpr ⟨h_colim⟩ W x_ext hx_ext
  refine ⟨t, ?_, ?_⟩
  · convert Presieve.isAmalgamation_restrict (Sieve.le_generate
      (Presieve.ofArrows (fun () ↦ Y) (fun () ↦ f))) _ _ t_amalg
    exact (Presieve.restrict_extend hx).symm
  · exact fun y hy ↦ t_uniq y <| Presieve.isAmalgamation_sieveExtend x y hy

/-- The regular topology on any preregular category is subcanonical. -/
instance subcanonical [Preregular C] : (regularTopology C).Subcanonical :=
  GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ isSheaf_yoneda_obj

end regularTopology

end CategoryTheory
