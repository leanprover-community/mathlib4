/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Filippo A. E. Nuccio, Riccardo Brasca
-/
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Preadditive.Projective
import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.CategoryTheory.Sites.Coherent.Basic
/-!

# Sheaves for the regular topology

This file characterises sheaves for the regular topology.

## Main results

* `isSheaf_iff_equalizerCondition`: In a preregular category with pullbacks, the sheaves for the
  regular topology are precisely the presheaves satisfying an equaliser condition with respect to
  effective epimorphisms.

* `isSheaf_of_projective`: In a preregular category in which every object is projective, every
  presheaf is a sheaf for the regular topology.
-/

namespace CategoryTheory

open Limits

variable {C D E : Type*} [Category C] [Category D] [Category E]

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

def SingleEqualizerCondition (P : Cᵒᵖ ⥤ D) ⦃X B : C⦄ (π : X ⟶ B) : Prop :=
  ∀ (c : PullbackCone π π) (_ : IsLimit c),
    Nonempty (IsLimit (Fork.ofι (P.map π.op) (equalizerCondition_w P c)))

/--
A contravariant functor on `C` satisfies `EqualizerCondition` if it takes kernel pairs of effective
epimorphisms to equalizer diagrams.
-/
def EqualizerCondition (P : Cᵒᵖ ⥤ D) : Prop :=
  ∀ ⦃X B : C⦄ (π : X ⟶ B) [EffectiveEpi π], SingleEqualizerCondition P π

/-- The equalizer condition is preserved by natural isomorphism. -/
theorem equalizerCondition_of_natIso {P P' : Cᵒᵖ ⥤ D} (i : P ≅ P')
    (hP : EqualizerCondition P) : EqualizerCondition P' := fun X B π _ c hc ↦
  ⟨Fork.isLimitOfIsos _ (hP π c hc).some _ (i.app _) (i.app _) (i.app _)⟩

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
def MapToEqualizer (P : Cᵒᵖ ⥤ Type*) {W X B : C} (f : X ⟶ B)
    (g₁ g₂ : W ⟶ X) (w : g₁ ≫ f = g₂ ≫ f) :
    P.obj (op B) → { x : P.obj (op X) | P.map g₁.op x = P.map g₂.op x } := fun t ↦
  ⟨P.map f.op t, by simp only [Set.mem_setOf_eq, ← FunctorToTypes.map_comp_apply, ← op_comp, w]⟩

theorem EqualizerCondition.bijective_mapToEqualizer_pullback (P : Cᵒᵖ ⥤ Type*)
    (hP : EqualizerCondition P) : ∀ (X B : C) (π : X ⟶ B) [EffectiveEpi π] [HasPullback π π],
    Function.Bijective
      (MapToEqualizer P π (pullback.fst (f := π) (g := π)) (pullback.snd (f := π) (g := π))
        pullback.condition) := by
  intro X B π _ _
  specialize hP π _ (pullbackIsPullback π π)
  rw [Types.type_equalizer_iff_unique] at hP
  rw [Function.bijective_iff_existsUnique]
  intro ⟨b, hb⟩
  obtain ⟨a, ha₁, ha₂⟩ := hP b hb
  refine ⟨a, ?_, ?_⟩
  · simpa [MapToEqualizer] using ha₁
  · simpa [MapToEqualizer] using ha₂

theorem EqualizerCondition.mk (P : Cᵒᵖ ⥤ Type*)
    (hP : ∀ (X B : C) (π : X ⟶ B) [EffectiveEpi π] [HasPullback π π], Function.Bijective
    (MapToEqualizer P π (pullback.fst (f := π) (g := π)) (pullback.snd (f := π) (g := π))
    pullback.condition)) : EqualizerCondition P := by
  intro X B π _ c hc
  have : HasPullback π π := ⟨c, hc⟩
  specialize hP X B π
  rw [Types.type_equalizer_iff_unique]
  rw [Function.bijective_iff_existsUnique] at hP
  intro b hb
  have h₁ : ((pullbackIsPullback π π).conePointUniqueUpToIso hc).hom ≫ c.fst =
    pullback.fst (f := π) (g := π) := by simp
  have hb' : P.map (pullback.fst (f := π) (g := π)).op b = P.map pullback.snd.op b := by
    rw [← h₁, op_comp, FunctorToTypes.map_comp_apply, hb]
    simp [← FunctorToTypes.map_comp_apply, ← op_comp]
  obtain ⟨a, ha₁, ha₂⟩ := hP ⟨b, hb'⟩
  refine ⟨a, ?_, ?_⟩
  · simpa [MapToEqualizer] using ha₁
  · simpa [MapToEqualizer] using ha₂

lemma equalizerCondition_iff_isIso_lift_w (P : Cᵒᵖ ⥤ Type*) {X B : C} (π : X ⟶ B)
    [HasPullback π π] : P.map π.op ≫ P.map (pullback.fst (f := π) (g := π)).op =
    P.map π.op ≫ P.map (pullback.snd).op := by
  simp only [← Functor.map_comp, ← op_comp, pullback.condition]

lemma mapToEqualizer_eq_comp (P : Cᵒᵖ ⥤ Type*) {X B : C} (π : X ⟶ B)
    [HasPullback π π] : MapToEqualizer P π pullback.fst pullback.snd pullback.condition =
    equalizer.lift (P.map π.op) (equalizerCondition_iff_isIso_lift_w P π) ≫
    (Types.equalizerIso _ _).hom := by
  rw [← Iso.comp_inv_eq (α := Types.equalizerIso _ _)]
  apply equalizer.hom_ext
  aesop

/-- An alternative phrasing of the explicit equalizer condition, using more categorical language. -/
theorem equalizerCondition_iff_isIso_lift (P : Cᵒᵖ ⥤ Type*) : EqualizerCondition P ↔
    ∀ (X B : C) (π : X ⟶ B) [EffectiveEpi π] [HasPullback π π], IsIso
    (equalizer.lift (P.map π.op) (equalizerCondition_iff_isIso_lift_w P π)) := by
  constructor
  · intro hP X B π _ _
    have h := hP.bijective_mapToEqualizer_pullback _ X B π
    rw [← isIso_iff_bijective, mapToEqualizer_eq_comp] at h
    exact IsIso.of_isIso_comp_right (equalizer.lift (P.map π.op)
      (equalizerCondition_iff_isIso_lift_w P π))
      (Types.equalizerIso _ _).hom
  · intro hP
    apply EqualizerCondition.mk
    intro X B π _ _
    rw [mapToEqualizer_eq_comp, ← isIso_iff_bijective]
    infer_instance

/-- `P` satisfies the equalizer condition iff its precomposition by an equivalence does. -/
theorem equalizerCondition_iff_of_equivalence (P : Cᵒᵖ ⥤ D)
    (e : C ≌ E) : EqualizerCondition P ↔ EqualizerCondition (e.op.inverse ⋙ P) :=
  ⟨fun h ↦ equalizerCondition_precomp_of_preservesPullback P e.inverse h, fun h ↦
    equalizerCondition_of_natIso (e.op.funInvIdAssoc P)
      (equalizerCondition_precomp_of_preservesPullback (e.op.inverse ⋙ P) e.functor h)⟩

theorem PullbackCone.IsLimit.uniq {X₁ X₂ Y B : C} {f₁ : X₁ ⟶ B} {f₂ : X₂ ⟶ B}
    (c : PullbackCone f₁ f₂) (hc : IsLimit c) (g₁ : Y ⟶ X₁) (g₂ : Y ⟶ X₂) (w : g₁ ≫ f₁ = g₂ ≫ f₂)
    (h : Y ⟶ c.pt) (w₁ : h ≫ c.fst = g₁) (w₂ : h ≫ c.snd = g₂) :
    h = PullbackCone.IsLimit.lift hc g₁ g₂ w := by
  apply hc.uniq (PullbackCone.mk _ _ w)
  intro j
  cases j with
  | none =>
    simp only [PullbackCone.mk_pt, cospan_one, PullbackCone.condition_one, PullbackCone.mk_π_app,
      const_obj_obj]
    rw [← Category.assoc, w₁]
  | some val =>
    cases val with
    | left =>
      simpa using w₁
    | right =>
      simpa using w₂

open WalkingParallelPair WalkingParallelPairHom in
noncomputable def blablabla (P : Cᵒᵖ ⥤ D) {X B : C} (π : X ⟶ B)
    (c : PullbackCone π π) (hc : IsLimit c) :
    IsLimit (Fork.ofι (P.map π.op) (equalizerCondition_w P c)) ≃
    IsLimit (P.mapCone (Sieve.ofArrows (fun (_ : Unit) ↦ X) fun _ ↦ π).arrows.cocone.op) := by
  let S := (Sieve.ofArrows (fun (_ : Unit) => X) (fun _ => π)).arrows
  let E := @FullSubcategory (Over B) (fun f ↦ S f.hom)
  let F : Eᵒᵖ ⥤ D := S.diagram.op ⋙ P
  let G := parallelPair (P.map c.fst.op) (P.map c.snd.op)
  let X' : E := ⟨Over.mk π, ⟨_, 𝟙 _, π, ofArrows.mk (), Category.id_comp _⟩⟩
  let P' : E := ⟨Over.mk (c.fst ≫ π),
    ⟨_, c.fst, π, ofArrows.mk (), rfl⟩⟩
  let fst : P' ⟶ X' := Over.homMk c.fst
  let snd : P' ⟶ X' := Over.homMk c.snd c.condition.symm
  let H := parallelPair fst.op snd.op
  have : H.Initial := {
    out := by
      intro ⟨Z⟩
      refine @isConnected_of_zigzag _ _ ?_ ?_
      · obtain ⟨_, f, g, ⟨⟩, hh⟩ := Z.property
        refine ⟨CostructuredArrow.mk (Y := zero) ?_⟩
        let f' : Z.obj.left ⟶ X'.obj.left := f
        refine (Over.homMk f').op
      · rintro ⟨⟨_ | _⟩, _, ⟨i⟩⟩ ⟨⟨_ | _⟩, _, ⟨j⟩⟩
        · have hi : i.left ≫ π = _ := i.w
          have hj : j.left ≫ π = _ := j.w
          have hij : i.left ≫ π = j.left ≫ π := by rw [hi, hj]; rfl
          let ij := PullbackCone.IsLimit.lift hc i.left j.left hij
          let cij : CostructuredArrow H ⟨Z⟩ :=
            CostructuredArrow.mk (⟨ij, (𝟙 _), (by simpa [H, ij] using hi)⟩ : H.obj one ⟶ ⟨Z⟩)
          let fig : (⟨zero, _, ⟨i⟩⟩ : CostructuredArrow H ⟨Z⟩).left ⟶ cij.left := left
          let fjg : (⟨zero, _, ⟨j⟩⟩ : CostructuredArrow H ⟨Z⟩).left ⟶ cij.left := right
          let fi : ⟨zero, _, ⟨i⟩⟩ ⟶ cij := CostructuredArrow.homMk fig (by
            erw [← op_comp]
            congr
            apply CostructuredArrow.hom_ext
            change PullbackCone.IsLimit.lift _ _ _ _ ≫ c.fst = _
            simp)
          let fj : ⟨zero, _, ⟨j⟩⟩ ⟶ cij := CostructuredArrow.homMk fjg (by
            erw [← op_comp]
            congr
            apply CostructuredArrow.hom_ext
            change PullbackCone.IsLimit.lift _ _ _ _ ≫ c.snd = _
            simp)
          refine ⟨[⟨zero, _, ⟨i⟩⟩, cij, ⟨zero, _, ⟨j⟩⟩], ?_⟩
          simp only [id_obj, const_obj_obj, List.chain_cons, or_self, List.Chain.nil, and_true,
            ne_eq, not_false_eq_true, List.getLast_cons, List.getLast_singleton']
          refine ⟨⟨𝟙 _⟩, ?_, ?_⟩
          · left
            exact ⟨fi⟩
          · right
            exact ⟨fj⟩
        · have hi : i.left ≫ π = _ := i.w
          let j' := j ≫ (H.map right).unop
          have hj : j'.left ≫ π = _ := j'.w
          have hij : i.left ≫ π = j'.left ≫ π := by rw [hi, hj]; rfl
          let ij := PullbackCone.IsLimit.lift hc i.left j'.left hij
          let cij : CostructuredArrow H ⟨Z⟩ :=
            CostructuredArrow.mk (⟨ij, (𝟙 _), (by simpa [H, ij] using hi)⟩ : H.obj one ⟶ ⟨Z⟩)
          let fig : (⟨zero, _, ⟨i⟩⟩ : CostructuredArrow H ⟨Z⟩).left ⟶ cij.left := left
          let fjg : (⟨zero, _, ⟨j'⟩⟩ : CostructuredArrow H ⟨Z⟩).left ⟶ cij.left := right
          let fi : ⟨zero, _, ⟨i⟩⟩ ⟶ cij := CostructuredArrow.homMk fig (by
            erw [← op_comp]
            congr
            apply CostructuredArrow.hom_ext
            change PullbackCone.IsLimit.lift _ _ _ _ ≫ c.fst = _
            simp)
          let fj : ⟨zero, _, ⟨j'⟩⟩ ⟶ cij := CostructuredArrow.homMk fjg (by
            erw [← op_comp]
            congr 1
            apply CostructuredArrow.hom_ext
            change PullbackCone.IsLimit.lift _ _ _ _ ≫ c.snd = _
            simp)
          refine ⟨[cij, ⟨zero, _, ⟨j ≫ (H.map right).unop⟩⟩, ⟨one, _, ⟨j⟩⟩], ?_⟩
          simp only [id_obj, const_obj_obj, List.chain_cons, List.Chain.nil, and_true, ne_eq,
            not_false_eq_true, List.getLast_cons, List.getLast_singleton']
          exact ⟨Or.inl ⟨fi⟩, Or.inr ⟨fj⟩, Or.inl
            ⟨CostructuredArrow.homMk right rfl⟩⟩
        · have hi := i.w
          have hj := j.w
          simp [- Over.w, H] at hi
          simp [- Over.w, H] at hj
          have hij : (i.left ≫ c.fst) ≫ π = j.left ≫ π := by simp [hi, hj]
          let ij := PullbackCone.IsLimit.lift hc (i.left ≫ c.fst) j.left hij
          let cij : CostructuredArrow H ⟨Z⟩ :=
            CostructuredArrow.mk (⟨ij, (𝟙 _), (by simpa [H, ij] using hi)⟩ : H.obj one ⟶ ⟨Z⟩)
          let fig : (⟨zero, _, ⟨i ≫ (H.map left).unop⟩⟩ :
              CostructuredArrow H ⟨Z⟩).left ⟶ cij.left := left
          let fjg : (⟨zero, _, ⟨j⟩⟩ : CostructuredArrow H ⟨Z⟩).left ⟶ cij.left := right
          let fi : ⟨zero, _, ⟨_⟩⟩ ⟶ cij := CostructuredArrow.homMk fig (by
            erw [← op_comp]
            congr 1
            apply CostructuredArrow.hom_ext
            change PullbackCone.IsLimit.lift _ _ _ _ ≫ c.fst = _
            simp only [id_obj, const_obj_obj, PullbackCone.IsLimit.lift_fst]
            rfl)
          let fj : ⟨zero, _, ⟨_⟩⟩ ⟶ cij := CostructuredArrow.homMk fjg (by
            erw [← op_comp]
            congr 1
            apply CostructuredArrow.hom_ext
            change PullbackCone.IsLimit.lift _ _ _ _ ≫ c.snd = _
            simp)
          refine ⟨[⟨zero, _, ⟨i ≫ (H.map left).unop⟩⟩, cij, ⟨zero, _, ⟨j⟩⟩], ?_⟩
          simp only [id_obj, const_obj_obj, List.chain_cons, List.Chain.nil, and_true, ne_eq,
            not_false_eq_true, List.getLast_cons, List.getLast_singleton']
          exact ⟨Or.inr ⟨CostructuredArrow.homMk left rfl⟩, Or.inl ⟨fi⟩, Or.inr ⟨fj⟩⟩
        · have hi := i.w
          have hj := j.w
          simp [- Over.w, H] at hi
          simp [- Over.w, H, c.condition] at hj
          have hij : (i.left ≫ c.fst) ≫ π = (j.left ≫ c.snd) ≫ π := by simp [hi, hj]
          let ij := PullbackCone.IsLimit.lift hc _ _ hij
          let cij : CostructuredArrow H ⟨Z⟩ :=
            CostructuredArrow.mk (⟨ij, (𝟙 _), (by simpa [H, ij] using hi)⟩ : H.obj one ⟶ ⟨Z⟩)
          let fig : (⟨zero, _, ⟨i ≫ (H.map left).unop⟩⟩ :
            CostructuredArrow H ⟨Z⟩).left ⟶ cij.left := left
          let fjg : (⟨zero, _, ⟨j ≫ (H.map right).unop⟩⟩ :
            CostructuredArrow H ⟨Z⟩).left ⟶ cij.left := right
          let fi : ⟨zero, _, ⟨_⟩⟩ ⟶ cij := CostructuredArrow.homMk fig (by
            erw [← op_comp]
            congr 1
            apply CostructuredArrow.hom_ext
            change PullbackCone.IsLimit.lift _ _ _ _ ≫ c.fst = _
            simp only [id_obj, const_obj_obj, PullbackCone.IsLimit.lift_fst]
            rfl)
          let fj : ⟨zero, _, ⟨_⟩⟩ ⟶ cij := CostructuredArrow.homMk fjg (by
            erw [← op_comp]
            congr 1
            apply CostructuredArrow.hom_ext
            change PullbackCone.IsLimit.lift _ _ _ _ ≫ c.snd = _
            simp only [id_obj, const_obj_obj, PullbackCone.IsLimit.lift_snd]
            rfl)
          refine ⟨[⟨zero, _, ⟨i ≫ (H.map left).unop⟩⟩, cij, ⟨zero, _, ⟨j ≫ (H.map right).unop⟩⟩,
            ⟨one, _, ⟨j⟩⟩], ?_⟩
          simp only [id_obj, const_obj_obj, List.chain_cons, List.Chain.nil, and_true, ne_eq,
            not_false_eq_true, List.getLast_cons, List.getLast_singleton']
          exact ⟨Or.inr ⟨CostructuredArrow.homMk left rfl⟩, Or.inl ⟨fi⟩, Or.inr ⟨fj⟩, Or.inl
            ⟨CostructuredArrow.homMk right rfl⟩⟩
  }
  let i : H ⋙ F ≅ G := parallelPair.ext (Iso.refl _) (Iso.refl _) (by aesop) (by aesop)
  refine (IsLimit.equivOfNatIsoOfIso i.symm _ _ ?_).trans (Functor.Initial.isLimitWhiskerEquiv H _)
  refine Cones.ext ?_ ?_
  · rfl
  · rintro ⟨_ | _⟩
    · simp only [id_obj, comp_obj, Functor.comp_map, Iso.refl_hom, id_eq, eq_mpr_eq_cast,
        const_obj_obj, parallelPair_map_right, Quiver.Hom.unop_op, Over.homMk_left, Iso.symm_hom,
        Cones.postcompose_obj_pt, Fork.ofι_pt, Cones.postcompose_obj_π, NatTrans.comp_app,
        Fork.ofι_π_app, parallelPair.ext_inv_app, Iso.refl_inv, Sieve.generate_apply,
        Cone.whisker_pt, mapCone_pt, Cocone.op_pt, Cocone.whisker_pt, Over.forgetCocone_pt,
        Cone.whisker_π, whiskerLeft_app, mapCone_π_app, op_obj, fullSubcategoryInclusion.obj,
        Over.forget_obj, Cocone.op_π, Cocone.whisker_ι, NatTrans.op_app, Over.forgetCocone_ι_app,
        Category.id_comp, i]
      erw [Category.comp_id]
      congr
    · simp only [id_obj, comp_obj, Functor.comp_map, Iso.refl_hom, id_eq, eq_mpr_eq_cast,
        const_obj_obj, parallelPair_map_right, Quiver.Hom.unop_op, Over.homMk_left, Iso.symm_hom,
        Cones.postcompose_obj_pt, Fork.ofι_pt, Cones.postcompose_obj_π, NatTrans.comp_app,
        Fork.ofι_π_app, parallelPair_obj_one, parallelPair.ext_inv_app, Iso.refl_inv,
        Category.assoc, Sieve.generate_apply, Cone.whisker_pt, mapCone_pt, Cocone.op_pt,
        Cocone.whisker_pt, Over.forgetCocone_pt, Cone.whisker_π, whiskerLeft_app, mapCone_π_app,
        op_obj, fullSubcategoryInclusion.obj, Over.forget_obj, Cocone.op_π, Cocone.whisker_ι,
        NatTrans.op_app, Over.forgetCocone_ι_app, Category.id_comp, i]
      erw [Category.comp_id, ← Functor.map_comp]
      congr

lemma equalizerConditionMap_iff_nonempty_isLimit (P : Cᵒᵖ ⥤ D) ⦃X B : C⦄ (π : X ⟶ B)
    [EffectiveEpi π] [HasPullback π π]:
    SingleEqualizerCondition P π ↔
      Nonempty (IsLimit (P.mapCone
        (Sieve.ofArrows (fun (_ : Unit) => X) (fun _ => π)).arrows.cocone.op)) := by
  constructor
  · intro h
    exact ⟨blablabla _ _ _ (pullbackIsPullback π π) (h _ (pullbackIsPullback π π)).some⟩
  · intro ⟨h⟩
    exact fun c hc ↦ ⟨(blablabla _ _ _ hc).symm h⟩

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

lemma EqualizerCondition.isSheafFor {B : C} {S : Presieve B} [S.regular] [S.hasPullbacks]
    {F : Cᵒᵖ ⥤ Type*} (hF : EqualizerCondition F) : S.IsSheafFor F := by
  obtain ⟨X, π, hS, πsurj⟩ := Presieve.regular.single_epi (R := S)
  subst hS
  rw [isSheafFor_arrows_iff_pullbacks]
  intro y h
  have : (Presieve.singleton π).hasPullbacks := by rw [← ofArrows_pUnit]; infer_instance
  have : HasPullback π π := hasPullbacks.has_pullbacks Presieve.singleton.mk Presieve.singleton.mk
  let c : PullbackCone π π := (IsPullback.of_hasPullback π π).cone
  have hc : IsLimit c := IsPullback.isLimit _
  specialize hF π c hc
  rw [Types.type_equalizer_iff_unique] at hF
  obtain ⟨t, ht⟩ := hF (y ()) (h () ())
  exact ⟨t, fun _ ↦ ht.1, fun _ h ↦ ht.2 _ (h _)⟩

lemma equalizerCondition_of_regular {F : Cᵒᵖ ⥤ Type*}
    (hSF : ∀ {B : C} (S : Presieve B) [S.regular] [S.hasPullbacks], S.IsSheafFor F) :
    EqualizerCondition F := by
  apply EqualizerCondition.mk
  intro X B π _ _
  have : (ofArrows (fun _ ↦ X) (fun _ ↦ π)).regular := ⟨X, π, rfl, inferInstance⟩
  have : (ofArrows (fun () ↦ X) (fun _ ↦ π)).hasPullbacks := ⟨
      fun hf _ hg ↦ (by cases hf; cases hg; infer_instance)⟩
  specialize hSF (ofArrows (fun () ↦ X) (fun _ ↦ π))
  rw [isSheafFor_arrows_iff_pullbacks] at hSF
  rw [Function.bijective_iff_existsUnique]
  intro ⟨x, hx⟩
  obtain ⟨t, ht, ht'⟩ := hSF (fun _ ↦ x) (fun _ _ ↦ hx)
  refine ⟨t, ?_, fun y h ↦ ht' y ?_⟩
  · simpa [MapToEqualizer] using ht ()
  · simpa [MapToEqualizer] using h

lemma isSheafFor_regular_of_projective {X : C} (S : Presieve X) [S.regular] [Projective X]
    (F : Cᵒᵖ ⥤ Type*) : S.IsSheafFor F := by
  obtain ⟨Y, f, rfl, hf⟩ := Presieve.regular.single_epi (R := S)
  rw [isSheafFor_arrows_iff]
  refine fun x hx ↦ ⟨F.map (Projective.factorThru (𝟙 _) f).op <| x (), fun _ ↦ ?_, fun y h ↦ ?_⟩
  · simpa using (hx () () Y (𝟙 Y) (f ≫ (Projective.factorThru (𝟙 _) f)) (by simp)).symm
  · simp only [← h (), ← FunctorToTypes.map_comp_apply, ← op_comp, Projective.factorThru_comp,
      op_id, FunctorToTypes.map_id_apply]

/-- A presheaf is a sheaf for the regular topology iff it satisfies `EqualizerCondition` -/
theorem EqualizerCondition.isSheaf_iff (F : Cᵒᵖ ⥤ Type*) [Preregular C]
    [h : ∀ {Y X : C} (f : Y ⟶ X) [EffectiveEpi f], HasPullback f f]  :
    Presieve.IsSheaf (regularTopology C) F ↔ EqualizerCondition F := by
  rw [← isSheaf_iff_isSheaf_of_type]
  exact (@equalizerCondition_iff_isSheaf _ _ _ _ F _ h).symm
    -- why doesn't typeclass inference find `h`?
  -- rw [regularTopology, Presieve.isSheaf_coverage]
  -- refine ⟨fun h ↦ equalizerCondition_of_regular fun S ⟨Y, f, hh⟩ _ ↦ h S ⟨Y, f, hh⟩, ?_⟩
  -- rintro h X S ⟨Y, f, rfl, hf⟩
  -- exact @isSheafFor _ _ _ _ ⟨Y, f, rfl, hf⟩ ⟨fun g _ h ↦ by cases g; cases h; infer_instance⟩ _ h

/-- Every presheaf is a sheaf for the regular topology if every object of `C` is projective. -/
theorem isSheaf_of_projective (F : Cᵒᵖ ⥤ Type*) [Preregular C] [∀ (X : C), Projective X] :
    IsSheaf (regularTopology C) F :=
  (isSheaf_coverage _ _).mpr fun S ⟨_, h⟩ ↦ have : S.regular := ⟨_, h⟩
    isSheafFor_regular_of_projective _ _

/-- Every Yoneda-presheaf is a sheaf for the regular topology. -/
lemma isSheaf_yoneda_obj [Preregular C] (W : C)  :
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
theorem subcanonical [Preregular C] : Sheaf.Subcanonical (regularTopology C) :=
  Sheaf.Subcanonical.of_yoneda_isSheaf _ isSheaf_yoneda_obj

end regularTopology

end CategoryTheory
