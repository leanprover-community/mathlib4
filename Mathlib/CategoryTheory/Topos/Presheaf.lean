-- TODO: At some point this will become an entire file about presheaf topoi,
-- but for now, it's just a general construction of subobject classifiers
-- in **PSh(C)** for a given `C`.

import Mathlib.CategoryTheory.Topos.Classifier
import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
import Mathlib.CategoryTheory.Subpresheaf.Sieves
import Mathlib.CategoryTheory.Subpresheaf.Subobject

import Mathlib.Tactic.LiftLets

namespace CategoryTheory
open Limits Opposite
universe w v₂ v₁ v u₂ u₁ u
variable {C : Type u} [Category.{v} C] --[HasPullbacks C]

@[pp_with_univ]
def SmallType := FullSubcategory Small.{w}

namespace SmallType
@[simps!]
instance : Category SmallType.{w} := inferInstanceAs (Category (FullSubcategory Small.{w}))
instance (X : SmallType.{w}) : Small.{w} (X.1) := X.2

@[simps!]
noncomputable def inclusion : SmallType.{w, u} ⥤ Type w where
  obj X := Shrink X.1
  map f := (equivShrink _) ∘ f ∘ (equivShrink _).symm

@[simps!]
noncomputable def lift (F : C ⥤ Type v) [∀ X, Small.{w} (F.obj X)] : C ⥤ Type w :=
  FullSubcategory.lift Small.{w} F inferInstance ⋙ inclusion

end SmallType

namespace Presheaf

#check (yoneda ⋙ (whiskeringRight Cᵒᵖ _ _).obj uliftFunctor.{w}).op ⋙ Subobject.presheaf _
#check yoneda.op ⋙ Subobject.presheaf (Cᵒᵖ ⥤ Type v)
#check (yoneda ⋙ (whiskeringRight Cᵒᵖᵒᵖ _ _).obj uliftFunctor.{w}).op

-- TODO: Adjust binding power of `⊤_` so that `⊤_ Cᵒᵖ ⥤ Type v` is parsed as `(⊤_ Cᵒᵖ) ⥤ Type v`
-- and not `⊤_ (Cᵒᵖ ⥤ Type v)`


open Functor in
def Functor.emptyFlipIsoConst {D : Type v₂} [Category.{u₂} D] :
    (empty (C ⥤ D)).flip ≅ (const C).obj (empty D) :=
  NatIso.ofComponents (fun _ ↦ emptyExt _ _)

open Functor in
noncomputable def Functor.terminalIsoPointwiseTerminal
    {D : Type v₂} [Category.{u₂} D] [HasTerminal D] :
    (⊤_ (C ⥤ D)) ≅ (Functor.const C).obj (⊤_ D) :=
  limitIsoFlipCompLim _ ≪≫ isoWhiskerRight Functor.emptyFlipIsoConst _
    ≪≫ NatIso.ofComponents (fun _ ↦ Iso.refl _)

open Functor in
@[simps!?]
noncomputable def Functor.reprW_ULift (F : Cᵒᵖ ⥤ Type max v v₁) [F.IsRepresentable] :
    ULiftHom.up.op ⋙ (ULiftHom.up ⋙ yoneda).obj (F.reprX) ≅ F :=
  NatIso.ofComponents
    (fun ⟨X⟩ ↦ {
      hom := fun ⟨f⟩ ↦ F.representableBy.homEquiv f,
      inv := fun f ↦ ULift.up <| F.representableBy.homEquiv.invFun f })
    (@fun ⟨X⟩ ⟨Y⟩ ⟨f⟩ ↦ by
      ext ⟨g⟩
      simp only [Functor.comp_obj, comp_map, yoneda_obj_map, types_comp_apply]
      simp [F.representableBy.homEquiv_comp]
      rfl )

/-- A natural transformation to a representable functor induces a sieve, even if the universe levels
are large. -/
@[simps]
def Sieve.sieveOfSubfunctorULift {X : C} {R : Cᵒᵖ ⥤ Type max w v}
    (f : R ⟶ yoneda.obj X ⋙ uliftFunctor.{w, v}) : Sieve X where
  arrows Y g := ∃ t, (f.app (op Y) t).down = g
  downward_closed := by
    rintro Y Z _ ⟨t, rfl⟩ g
    refine ⟨R.map g.op t, ?_⟩
    rw [FunctorToTypes.naturality _ _ f]
    simp

open Sieve in
theorem Sieve.sieveOfSubfunctorULift_functorInclusion {X : C} {S : Sieve X} :
    Sieve.sieveOfSubfunctorULift (whiskerRight S.functorInclusion uliftFunctor.{w, v}) = S := by
  ext; simp

/-- Isomorphic subfunctors of representable functors give equal sieves. -/
@[simp]
lemma Sieve.sieveOfSubfunctor_isIso
    {X : C} {R S : Cᵒᵖ ⥤ Type v} (η : S ⟶ yoneda.obj X) (ι : R ⟶ S) [IsIso ι] [Mono η] :
    Sieve.sieveOfSubfunctor (ι ≫ η) = Sieve.sieveOfSubfunctor η := by
  ext Z g
  simp only [Sieve.sieveOfSubfunctor_apply, yoneda_obj_obj, FunctorToTypes.comp]
  constructor <;> rintro ⟨t, ht⟩
  · use ι.app (op Z) t
  · use (inv ι).app (op Z) t; rw [← types_comp_apply _ (ι.app _), ← NatTrans.comp_app]; simp [ht]

@[simp]
lemma pullback_sieveOfSubfunctor
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (R : Cᵒᵖ ⥤ Type v) (η : R ⟶ yoneda.obj X.unop) [Mono η] :
    Sieve.pullback f.unop (Sieve.sieveOfSubfunctor η) =
      Sieve.sieveOfSubfunctor (pullback.snd η (yoneda.map f.unop)) := by
  ext Z g
  simp only [Sieve.pullback_apply, Sieve.sieveOfSubfunctor_apply, yoneda_obj_obj]
  simp_rw [Equiv.exists_congr_left (pullbackObjIso η _ _).toEquiv]
  constructor <;> rintro ⟨t, ht⟩
  · simp_rw [← yoneda_map_app (f.unop)] at ht
    use (Types.pullbackIsoPullback _ _ |>.inv ⟨⟨t, g⟩, ht⟩)
    simp [← pullbackObjIso_hom_comp_snd]
  · simp_rw [← yoneda_map_app (f.unop)]
    use pullback.fst (η.app _) _ t
    simp_rw [← types_comp_apply, pullback.condition]
    simp [← pullbackObjIso_hom_comp_snd] at ht
    simp [ht]


@[simps]
instance : @Trans (Type u) (Type u) (Type u) Iso Equiv Iso where
  trans ι ε := ι ≪≫ ε.toIso

@[simps]
instance : @Trans (Type u) (Type u) (Type u) Iso Equiv Equiv where
  trans ι ε := ι.toEquiv.trans ε

@[simps]
instance : @Trans (Type u) (Type u) (Type u) Equiv Iso Iso where
  trans ε ι := ε.toIso ≪≫ ι

@[simps]
instance : @Trans (Type u) (Type u) (Type u) Equiv Iso Equiv where
  trans ε ι := ε.trans ι.toEquiv

/-- Isomorphic subfunctors of representable functors give equal sieves. -/
@[simp]
lemma Sieve.sieveOfSubfunctorULift_isIso {X : C} {R S : Cᵒᵖ ⥤ Type max w v}
    (η : S ⟶ yoneda.obj X ⋙ uliftFunctor.{w}) (ι : R ⟶ S) [IsIso ι] [Mono η] :
    Sieve.sieveOfSubfunctorULift (ι ≫ η) = Sieve.sieveOfSubfunctorULift η := by
  ext Z g
  simp only [Sieve.sieveOfSubfunctorULift_apply, yoneda_obj_obj, FunctorToTypes.comp]
  constructor <;> rintro ⟨t, ht⟩
  · use ι.app (op Z) t
  · use (inv ι).app (op Z) t; rw [← types_comp_apply _ (ι.app _), ← NatTrans.comp_app]; simp [ht]

-- sieveOfSubfunctorULift (pullback.snd ϑ ((yonedaCompUliftFunctorEquiv G (unop X)).symm b))
@[simp]
lemma Sieve.pullback_sieveOfSubfunctorULift
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (R : Cᵒᵖ ⥤ Type max w v)
    (η : R ⟶ yoneda.obj X.unop ⋙ uliftFunctor.{w}) [Mono η] :
    Sieve.pullback f.unop (Sieve.sieveOfSubfunctorULift η) =
      Sieve.sieveOfSubfunctorULift
        (pullback.snd η (whiskerRight (yoneda.map f.unop) uliftFunctor.{w})) := by
  ext Z g
  simp only [Sieve.pullback_apply, Sieve.sieveOfSubfunctorULift_apply, yoneda_obj_obj]
  simp_rw [Equiv.exists_congr_left (pullbackObjIso η _ _).toEquiv]
  constructor <;> rintro ⟨t, ht⟩
  · apply_fun ULift.up at ht
    rw [← yoneda_map_app (f.unop), ULift.up_down] at ht
    use (Types.pullbackIsoPullback _ _ |>.inv ⟨⟨t, ⟨g⟩⟩, ht⟩)
    simp [← pullbackObjIso_hom_comp_snd]
  · simp_rw [← yoneda_map_app (f.unop)]
    use pullback.fst (η.app _) _ t
    simp_rw [← types_comp_apply, pullback.condition]
    simp [← pullbackObjIso_hom_comp_snd] at ht
    simp [ht]

/-- The explicit classifier in **PSh(C)**, given by the functor that sends
objects to the type of sieves on it and morphisms to the function `Sieve.pullback`. -/
@[simps]
def classifyingObj : Cᵒᵖ ⥤ Type max v u where
  obj X := Sieve X.unop
  map {X Y} f := Sieve.pullback f.unop

@[ext]
lemma classifyingObj_obj_ext {X : Cᵒᵖ} (x y : classifyingObj.obj X)
    (h : ∀ {Y} (f : Y ⟶ unop X), x.arrows f ↔ y.arrows f) : x = y := by
  unfold classifyingObj
  ext Y f; simp [h]

/-- The explicit truth morphism associated with `classifier`. -/
@[simps]
def classifyingTruth : Subpresheaf (C := C) classifyingObj where
  obj X := {(⊤ : Sieve X.unop)}
  map {X Y} f := by simp

@[simps!]
noncomputable def classifyingTruth_terminal :
    IsTerminal (classifyingTruth.toPresheaf : Cᵒᵖ ⥤ Type max v u) :=
  IsTerminal.ofIso terminalIsTerminal (by
    refine Functor.terminalIsoPointwiseTerminal ≪≫ ?_
    apply NatIso.ofComponents (fun X ↦ IsTerminal.uniqueUpToIso terminalIsTerminal <|
      Types.isTerminalEquivUnique _ |>.symm <| inferInstanceAs (Unique ({⊤} : Set (Sieve X.unop)))))


open Subpresheaf in
/-- The explicit classifying map `χ` associated with a mono `ϑ` and `classifier`. -/
@[simps]
def classifyingMap {F G : Cᵒᵖ ⥤ Type max v u} (ϑ : F ⟶ G) [Mono ϑ] : G ⟶ classifyingObj where
  app X x : Sieve X.unop :=
    sieveOfSection (equivalenceMonoOver G |>.inverse.obj (MonoOver.mk' ϑ)) x
  naturality ⦃X Y⦄ f := by ext x Z g; simp

#check pullbackObjIso

@[reassoc]
lemma pullbackObjIso_naturality_hom {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    [HasPullbacks C] {F G H : D ⥤ C} {ϑ : F ⟶ H} {η : G ⟶ H} {X Y : D} (f : X ⟶ Y) :
    (pullback ϑ η).map f ≫ (pullbackObjIso ϑ η Y).hom =
      (pullbackObjIso ϑ η X).hom ≫
        pullback.map (ϑ.app X) (η.app X) (ϑ.app Y) (η.app Y) (F.map f) (G.map f) (H.map f)
          (by simp) (by simp) := by ext <;> simp

@[reassoc]
lemma pullbackObjIso_naturality_inv {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    [HasPullbacks C] {F G H : D ⥤ C} {ϑ : F ⟶ H} {η : G ⟶ H} {X Y : D} (f : X ⟶ Y) :
    (pullbackObjIso ϑ η X).inv ≫ (pullback ϑ η).map f =
      pullback.map (ϑ.app X) (η.app X) (ϑ.app Y) (η.app Y) (F.map f) (G.map f) (H.map f)
        (by simp) (by simp) ≫ (pullbackObjIso ϑ η Y).inv := by
  symm; simp [Iso.eq_inv_comp, ← pullbackObjIso_naturality_hom_assoc]

#check Types.pullbackIsoPullback

@[reassoc]
lemma Types.pullbackIsoPullback_naturality_hom {α₁ α₂ β₁ β₂ γ₁ γ₂ : Type u}
    {f₁ : α₁ ⟶ γ₁} {g₁ : β₁ ⟶ γ₁} {f₂ : α₂ ⟶ γ₂} {g₂ : β₂ ⟶ γ₂}
    {πa : α₁ ⟶ α₂} {πb : β₁ ⟶ β₂} {πc : γ₁ ⟶ γ₂}
    (h₁ : f₁ ≫ πc = πa ≫ f₂) (h₂ : g₁ ≫ πc = πb ≫ g₂) :
    pullback.map f₁ g₁ f₂ g₂ πa πb πc h₁ h₂ ≫ (Types.pullbackIsoPullback f₂ g₂).hom =
      (Types.pullbackIsoPullback f₁ g₁).hom ≫
        Subtype.map (fun ⟨a₁, b₁⟩ ↦ ⟨πa a₁, πb b₁⟩) (fun ⟨a₁, b₁⟩ h ↦ by
          simp only at h
          simp_rw [← types_comp_apply, ← h₁, ← h₂, types_comp_apply, h] ) := by
  ext x
  all_goals
    simp only [types_comp_apply, Types.pullbackIsoPullback_hom_fst, Subtype.map_coe,
      Types.pullbackIsoPullback_hom_snd, Types.pullbackIsoPullback_hom_snd]
    simp_rw [← types_comp_apply]
    simp only [pullback.lift_fst, pullback.lift_snd]

@[reassoc]
lemma Types.pullbackIsoPullback_naturality_inv {α₁ α₂ β₁ β₂ γ₁ γ₂ : Type u}
    {f₁ : α₁ ⟶ γ₁} {g₁ : β₁ ⟶ γ₁} {f₂ : α₂ ⟶ γ₂} {g₂ : β₂ ⟶ γ₂}
    {πa : α₁ ⟶ α₂} {πb : β₁ ⟶ β₂} {πc : γ₁ ⟶ γ₂}
    (h₁ : f₁ ≫ πc = πa ≫ f₂) (h₂ : g₁ ≫ πc = πb ≫ g₂) :
    (Types.pullbackIsoPullback f₁ g₁).inv ≫ pullback.map f₁ g₁ f₂ g₂ πa πb πc h₁ h₂ =
      Subtype.map (fun ⟨a₁, b₁⟩ ↦ ⟨πa a₁, πb b₁⟩) (fun ⟨a₁, b₁⟩ h ↦ by
        simp only at h
        simp_rw [← types_comp_apply, ← h₁, ← h₂, types_comp_apply, h] ) ≫
      (Types.pullbackIsoPullback f₂ g₂).inv := by
  ext x
  all_goals
    simp only [types_comp_apply, Types.pullbackIsoPullback_inv_fst, Subtype.map_coe,
      Types.pullbackIsoPullback_inv_snd, Types.pullbackIsoPullback_inv_fst]
    simp only [← types_comp_apply _ (pullback.fst _ _), ← types_comp_apply _ (pullback.snd _ _)]
    simp only [pullback.lift_fst, pullback.lift_snd]
    simp


lemma preimage_eq_pullback {F G : Cᵒᵖ ⥤ Type max v u} (ϑ : F ⟶ G) (S : Subpresheaf G) :
    Subpresheaf.orderIsoSubobject F (Subpresheaf.preimage S ϑ) =
      (Subobject.pullback ϑ).obj (Subpresheaf.orderIsoSubobject G S) := by
  simp
  symm
  convert Subobject.pullback_obj_mk (f' := S.fromPreimage ϑ) ?h
  · refine IsPullback.of_iso_pullback ⟨?w⟩ ?ι ?h₁ ?h₂
    case w =>
      ext Y f
      simp [Subpresheaf.fromPreimage] at f ⊢
    case ι =>
      symm
      exact NatIso.ofComponents (fun X ↦
        calc (pullback S.ι ϑ).obj X
        _ ≅ _ := pullbackObjIso _ _ _
        _ ≅ _ := Types.pullbackIsoPullback _ _
        _ ≃ { p : (S.obj X) × F.obj X // ↑p.1 = ϑ.app X p.2 } :=
          Equiv.cast (by simp [Types.PullbackObj])
        _ ≃ (S.preimage ϑ).toPresheaf.obj X := {
          toFun | ⟨⟨s, x⟩, h⟩ => ⟨x, by simp [Set.mem_preimage, ←h]⟩
          invFun | ⟨x, h⟩ => ⟨⟨⟨ϑ.app X x, h⟩, x⟩, by simp⟩
          left_inv
          | ⟨⟨s, x⟩, h⟩ => by
            ext
            · simpa using h.symm
            · simp
          right_inv | ⟨x, h⟩ => by simp })
        (fun {X Y} f ↦ by
          ext x
          apply Subtype.ext
          simp only [Subpresheaf.preimage_obj, Subpresheaf.toPresheaf_obj, Trans.trans,
            Equiv.cast_refl, Iso.trans_assoc, Iso.trans_hom, Equiv.toIso_hom, Equiv.coe_fn_mk,
            types_comp_apply, Subpresheaf.toPresheaf_map_coe]
          erw [Equiv.refl_apply, Equiv.refl_apply]
          simp_rw [← types_comp_apply _ (Iso.hom _), pullbackObjIso_naturality_hom, Category.assoc,
          Types.pullbackIsoPullback_naturality_hom]
          simp )
    case h₁ =>
      ext X ⟨x, hx⟩
      apply Subtype.ext
      simp [Set.mem_preimage] at hx
      simp [Trans.trans]
      erw [Equiv.refl_apply]
      simp_rw [← types_comp_apply _ (Iso.inv _), ← types_comp_apply _ (pullback.fst S.ι _ |>.app X),
      Category.assoc, pullbackObjIso_inv_comp_fst, Types.pullbackIsoPullback_inv_fst]
      simp [Subpresheaf.fromPreimage]
    case h₂ =>
      ext X ⟨x, hx⟩
      simp [Trans.trans]
      simp [Set.mem_preimage] at hx
      erw [Equiv.refl_apply]
      simp_rw [← types_comp_apply _ (Iso.inv _), ← types_comp_apply _ (pullback.snd S.ι _ |>.app X),
      Category.assoc, pullbackObjIso_inv_comp_snd, Types.pullbackIsoPullback_inv_snd]


  -- ext X x
  -- simp [Subpresheaf.preimage_apply, Subpresheaf.orderIsoSubobject_apply, Subobject.pullback_apply]

open Subpresheaf in
/-- Pulling back `classifyingTruth` along a classifying map `classifyingMap ϑ` gives the original
subobject, up to isomorphism. -/
noncomputable def pullbackIso {F G : Cᵒᵖ ⥤ Type max v u} (ϑ : F ⟶ G) [hϑ : Mono ϑ] :
    pullback (classifyingMap ϑ) classifyingTruth.ι ≅ F :=
  have hϑ : ∀ X, (ϑ.app X).Injective := by
    simpa [NatTrans.mono_iff_mono_app, mono_iff_injective] using hϑ
  calc pullback (classifyingMap ϑ) classifyingTruth.ι
  _ ≅ _ := eqToIso (by simp_rw [← Subobject.underlyingIso_arrow (classifyingTruth.ι)]; rfl)
  _ ≅ _ := (pullbackLeftPullbackSndIso _ _ _).symm
  _ ≅ _ := (asIso (pullback.fst _ _))
  _ ≅ _ := pullbackSymmetry _ _
  _ ≅ _ := (Subobject.underlyingIso (pullback.snd _ _)).symm
  _ ≅ ↑(Subobject.mk (classifyingTruth.preimage (classifyingMap ϑ)).ι) :=
    eqToIso <| congrArg Subobject.underlying.obj w
  _ ≅ _ := Subobject.underlyingIso _
  _ ≅ _ := NatIso.ofComponents (fun X ↦ by
    rw [toPresheaf_obj, preimage_obj]
    apply Equiv.toIso
    exact {
      toFun
      | ⟨x, h⟩ => by
        simp [Sieve.ext_iff, sieveOfSection] at h
        specialize h (𝟙 X.unop)
        simpa using h.choose
      invFun x := ⟨ϑ.app X x, by ext; simp [sieveOfSection, ← FunctorToTypes.naturality]⟩
      left_inv
      | ⟨x, h⟩ => by
        ext
        simp [sieveOfSection]
        generalize_proofs h'
        exact h'.choose_spec
      right_inv x := by
        simp
        generalize_proofs h'
        exact hϑ X h'.choose_spec } )
    (fun {X Y} f ↦ by
      ext x
      simp [sieveOfSection]
      generalize_proofs h₁ h₂
      apply_fun (ϑ.app Y) using hϑ Y
      rw [h₁.choose_spec, FunctorToTypes.naturality, h₂.choose_spec])
where
  w : Subobject.mk (pullback.snd (Subobject.mk classifyingTruth.ι).arrow (classifyingMap ϑ)) =
      Subobject.mk (classifyingTruth.preimage (classifyingMap ϑ)).ι := by
    rw [← Subobject.pullback_obj, ← Subpresheaf.orderIsoSubobject_apply, ← preimage_eq_pullback,
      Subpresheaf.orderIsoSubobject_apply]

#check eqToHom_naturality

open Sieve Subpresheaf in
@[simps]
noncomputable def χ_ε {G : Cᵒᵖ ⥤ _} : Subobject G ≃ (G ⟶ classifyingObj) :=
  let «χ⁻¹» {G : Cᵒᵖ ⥤ _} (χ : G ⟶ classifyingObj) : Subpresheaf G :=
      { obj X := {x : G.obj X | χ.app X x = (⊤ : Sieve X.unop)}
        map {X Y} f x hx := by
          simp at hx
          simp [Set.mem_preimage, FunctorToTypes.naturality, hx] }
    have {G} (χ : G ⟶ classifyingObj) :
        orderIsoSubobject G («χ⁻¹» χ) = Subobject.mk (pullback.snd classifyingTruth.ι χ) := by
      simp [«χ⁻¹»]
      fapply Subobject.mk_eq_mk_of_comm
      · fapply NatIso.ofComponents
        · intro X
          refine ?_ ≪≫ (Types.pullbackIsoPullback _ _).symm ≪≫ (pullbackObjIso _ _ _).symm
          simp [Subpresheaf.toPresheaf, Types.PullbackObj]
          exact (Equiv.subtypeEquiv (Equiv.uniqueProd (G.obj X) _).symm <| by simp [eq_comm]).toIso
        · intro X Y f
          simp
          simp_rw [pullbackObjIso_naturality_inv, Types.pullbackIsoPullback_naturality_inv_assoc]
          ext x
          simp [Equiv.subtypeEquiv, Subpresheaf.toPresheaf]
          congr
      · ext X : 2
        simp
        ext ⟨x, hx⟩
        simp
        erw [Equiv.subtypeEquiv_apply]
        simp
  { toFun S := classifyingMap S.arrow
    invFun χ := Subobject.mk (pullback.snd classifyingTruth.ι χ)
    left_inv S := by
      simp_rw [← this]
      have : Mono S.arrow := inferInstance
      simp_rw [NatTrans.mono_iff_mono_app, mono_iff_injective] at this
      simp [«χ⁻¹», classifyingMap, toPresheaf, sieveOfSection, Sieve.ext_iff]
      fapply Subobject.mk_eq_of_comm
      · fapply NatIso.ofComponents
        · intro X
          simp [Subpresheaf.sieveOfSection, Sieve.ext_iff]
          exact
          { hom | ⟨x, hx⟩ => (hx (𝟙 _)).choose
            inv x := ⟨S.arrow.app _ x, fun ⦃Y⦄ f ↦ by simp [← FunctorToTypes.naturality]⟩
            hom_inv_id := by
              ext x
              simp
              generalize_proofs h
              exact h.choose_spec
            inv_hom_id := by
              ext x
              simp
              generalize_proofs h
              exact this X (h.choose_spec) }
        · intro X Y f
          ext x
          simp
          generalize_proofs h₁ h₂
          apply_fun S.arrow.app Y using this Y
          rw [h₁.choose_spec, FunctorToTypes.naturality, h₂.choose_spec]
      · ext X ⟨x, hx⟩
        simp
        generalize_proofs h
        exact h.choose_spec
    right_inv χ := by
      -- have := congr_arg_heq ()
      specialize @this G
      simp_rw [← funext_iff] at this
      rw [← this]
      ext X x Y f
      simp [«χ⁻¹», classifyingMap, FunctorToTypes.naturality, ← Sieve.mem_iff_pullback_eq_top] }

open Sieve Function Subpresheaf in
@[simps!]
noncomputable def classifier : Classifier (Cᵒᵖ ⥤ Type max v u) :=
  have isPullback {F G : Cᵒᵖ ⥤ _} (ϑ : F ⟶ G) [hϑ : Mono ϑ] :
      IsPullback ϑ (classifyingTruth_terminal.from F) (classifyingMap ϑ) classifyingTruth.ι := by
    simp_rw [NatTrans.mono_iff_mono_app, mono_iff_injective] at hϑ
    refine IsPullback.of_iso_pullback ⟨?w⟩
      (pullbackIso ϑ).symm ?h₁ (classifyingTruth_terminal.hom_ext _ _)
    case w =>
      ext X x Y f
      simp [IsTerminal.from, ← Set.mem_def (s := Set.univ), ← FunctorToTypes.naturality]
    case h₁ =>
      have : ∀ {H} (g : H ⟶ classifyingObj), HasPullback (classifyingMap ϑ) g := inferInstance
      ext X x
      simp [Trans.trans, pullbackIso,
      ← eqToHom_naturality (fun g ↦ pullback.fst (classifyingMap ϑ) g),
      Subobject.arrow_congr _ _ (pullbackIso.w ϑ).symm]
  Classifier.mk' (C := Cᵒᵖ ⥤ Type max v u) classifyingObj classifyingTruth.ι
    (classifyingTruth_terminal.from) classifyingMap @isPullback
  (fun {F G} ϑ hϑ from' χ' hχ' ↦ by
    apply_fun χ_ε.symm using χ_ε.symm.injective
    simp [χ_ε]
    fapply Subobject.mk_eq_mk_of_comm
    · exact pullbackSymmetry _ _ ≪≫ hχ'.isoPullback.symm ≪≫ (isPullback ϑ).isoPullback
        ≪≫ pullbackSymmetry _ _
    · simp)

instance : HasClassifier (Cᵒᵖ ⥤ Type max v u) := ⟨⟨classifier⟩⟩

end CategoryTheory.Presheaf
