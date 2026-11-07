/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Presentable.CardinalPure
public import Mathlib.CategoryTheory.Presentable.Presheaf
public import Mathlib.CategoryTheory.Presentable.Representation
public import Mathlib.CategoryTheory.Presentable.Type
public import Mathlib.CategoryTheory.Presentable.Uniformization
public import Mathlib.CategoryTheory.Subfunctor.Colimits
public import Mathlib.CategoryTheory.Subfunctor.Image

/-!
# ...

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

@[expose]
public section

universe w v₁ v₂

open CategoryTheory Limits

structure Cardinal.SharplyLT.HasEnoughPureSubobjects
    {κ κ' : Cardinal.{w}} [Fact κ.IsRegular] [Fact κ'.IsRegular] (h : κ.SharplyLT κ')
    (C : Type*) [Category* C] extends IsCardinalAccessibleCategory C κ where
  exists_isCardinalPure {X Y : C} (f : X ⟶ Y) [IsCardinalPresentable X κ'] :
    ∃ (X' : C) (_ : IsCardinalPresentable X' κ') (f' : X ⟶ X') (i : X' ⟶ Y),
      IsCardinalPure κ i ∧ f' ≫ i = f

lemma Cardinal.SharplyLT.HasEnoughPureSubobjects.trans
    {κ κ' : Cardinal.{w}} [Fact κ.IsRegular] [Fact κ'.IsRegular] {h : κ.SharplyLT κ'}
    {C : Type*} [Category* C] (hC : h.HasEnoughPureSubobjects C)
    {κ₀ : Cardinal.{w}} [Fact κ₀.IsRegular]
    [IsCardinalAccessibleCategory C κ₀] (h₀ : κ₀.SharplyLT κ) :
    (h₀.trans h).HasEnoughPureSubobjects C where
  exists_isCardinalPure {X Y} f _ := by
    obtain ⟨X', _, f', i, _, fac⟩ := hC.exists_isCardinalPure f
    exact ⟨X', inferInstance, f', i, IsCardinalPure.of_le h₀.le i, fac⟩

lemma Cardinal.SharplyLT.HasEnoughPureSubobjects.of_equivalence
    {κ κ' : Cardinal.{w}} [Fact κ.IsRegular] [Fact κ'.IsRegular]
    {h : κ.SharplyLT κ'} {C D : Type*} [Category* C] [Category* D]
    (hC : h.HasEnoughPureSubobjects C) (e : C ≌ D) :
    h.HasEnoughPureSubobjects D where
  toIsCardinalAccessibleCategory := by
    have := hC.toIsCardinalAccessibleCategory
    exact e.isCardinalAccessibleCategory _
  exists_isCardinalPure {X Y} f _ := by
    have := hC.toIsCardinalAccessibleCategory
    obtain ⟨X', _, f', i, _, fac⟩ := hC.exists_isCardinalPure (e.inverse.map f)
    refine ⟨e.functor.obj X', inferInstance, e.symm.toAdjunction.homEquiv _ _ f',
      (e.toAdjunction.homEquiv _ _).symm i, ?_,
      e.inverse.map_injective
        (by simpa [Adjunction.homEquiv_apply, Adjunction.homEquiv_symm_apply])⟩
    simp only [Adjunction.homEquiv_symm_apply, Equivalence.toAdjunction_counit]
    infer_instance

namespace CategoryTheory

variable {C : Type*} [Category* C]

instance {P : ObjectProperty C} (X : P.FullSubcategory) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalPresentable X κ] [P.ι.PreservesCardinalPresentable κ] :
    IsCardinalPresentable X.obj κ :=
  inferInstanceAs (IsCardinalPresentable (P.ι.obj X) κ)

lemma IsCardinalPure.of_full_of_faithful
    {κ : Cardinal.{w}} [Fact κ.IsRegular] {X Y : C} {f : X ⟶ Y}
    {D : Type*} [Category* D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.PreservesCardinalPresentable κ]
    (h : IsCardinalPure κ (F.map f) := by infer_instance) :
    IsCardinalPure κ f where
  exists_of_commSq sq := by
    obtain ⟨ρ, hρ⟩ := exists_of_commSq κ (sq.map F)
    exact ⟨F.preimage ρ, F.map_injective (by cat_disch)⟩

-- to be moved
section

open Opposite

lemma isCardinalPresentable_iff_isAccessible_shrinkCoyoneda [LocallySmall.{w} C]
    {X : C} {κ : Cardinal.{w}} [Fact κ.IsRegular] :
    IsCardinalPresentable X κ ↔ (shrinkCoyoneda.{w}.obj (op X)).IsCardinalAccessible κ := by
  refine ⟨fun _ ↦ inferInstance, fun _ ↦ ⟨fun J _ _ ↦ ?_⟩⟩
  have := (shrinkCoyoneda.{w}.obj (op X)).preservesColimitsOfShape_of_isCardinalAccessible κ J
  have := preservesColimitsOfShape_of_natIso (J := J) (shrinkCoyonedaObjCompUliftFunctorIso (op X))
  exact preservesColimitsOfShape_of_reflects_of_preserves _ uliftFunctor

lemma IsCardinalPresentable.of_full_of_faithful
    {X : C} {κ : Cardinal.{w}} [Fact κ.IsRegular] {D : Type*} [Category* D]
    [LocallySmall.{w} C] [LocallySmall.{w} D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.IsCardinalAccessible κ]
    (h : IsCardinalPresentable (F.obj X) κ := by infer_instance) :
    IsCardinalPresentable X κ := by
  rw [isCardinalPresentable_iff_isAccessible_shrinkCoyoneda.{w}] at h ⊢
  have : (F ⋙ shrinkCoyoneda.{w}.obj (F.op.obj (op X))).IsCardinalAccessible κ := by
    dsimp
    infer_instance
  exact Functor.isCardinalAccessible_of_natIso (asIso (shrinkCoyonedaMap F (op X))).symm _

end

namespace ObjectProperty

class IsClosedUnderCardinalPureSubobjects
    (P : ObjectProperty C) (κ : Cardinal.{w}) [Fact κ.IsRegular] : Prop where
  prop_of_isCardinalPure (P κ) {X Y : C} (f : X ⟶ Y) [IsCardinalPure κ f] (hY : P Y) : P X

export IsClosedUnderCardinalPureSubobjects (prop_of_isCardinalPure)

lemma IsClosedUnderCardinalPureSubobjects.isClosedUnderIsomorphisms
    (P : ObjectProperty C) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [P.IsClosedUnderCardinalPureSubobjects κ] :
    P.IsClosedUnderIsomorphisms where
  of_iso e h := P.prop_of_isCardinalPure κ e.inv h

lemma IsClosedUnderCardinalPureSubobjects.of_le {P : ObjectProperty C} {κ κ' : Cardinal.{w}}
    [Fact κ.IsRegular] [Fact κ'.IsRegular] (h : κ ≤ κ')
    [P.IsClosedUnderCardinalPureSubobjects κ] :
    P.IsClosedUnderCardinalPureSubobjects κ' where
  prop_of_isCardinalPure f _ hY := by
    have : IsCardinalPure κ f := .of_le h f
    exact P.prop_of_isCardinalPure κ f hY

end ObjectProperty

namespace IsCardinalAccessibleCategory

open ObjectProperty.IsClosedUnderCardinalFilteredColimits in
instance [EssentiallySmall.{w} C] (P : ObjectProperty (C ⥤ Type w))
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [P.IsClosedUnderCardinalFilteredColimits κ]
    [IsCardinalAccessibleCategory P.FullSubcategory κ]
    [P.ι.PreservesCardinalPresentable κ] :
    P.IsClosedUnderCardinalPureSubobjects κ where
  prop_of_isCardinalPure {F₁ F₂} f _ hF₂ := by
    let J := CostructuredArrow (isCardinalPresentable (C ⥤ Type w) κ).ι F₁
    let D : J ⥤ C ⥤ Type w :=
      CostructuredArrow.proj _ F₁ ⋙ (isCardinalPresentable (C ⥤ Type w) κ).ι
    let c : Cocone D := (Functor.LeftExtension.mk _ (Functor.rightUnitor _).inv).coconeAt F₁
    have hc : IsColimit c := (isCardinalPresentable _ κ).ι.denseAt F₁
    let D' : (P.inverseImage D).FullSubcategory ⥤ P.FullSubcategory :=
      P.lift (ObjectProperty.ι _ ⋙ D) (fun ⟨_, _⟩ ↦ by simpa)
    let e : D' ⋙ P.ι ≅ ObjectProperty.ι _ ⋙ D := Iso.refl _
    have := isFiltered_of_isCardinalFiltered J κ
    have : (P.inverseImage D).ι.Final := by
      rw [ObjectProperty.final_ι_iff_of_isFiltered]
      intro j
      have : IsCardinalPresentable (D.obj j) κ := by dsimp [D]; infer_instance
      let J' := CostructuredArrow (isCardinalPresentable P.FullSubcategory κ).ι ⟨F₂, hF₂⟩
      have := isCardinalClosedUnderColimitsOfShape P κ J'
      have : HasColimitsOfShape J' (Type w) :=
        hasColimitsOfShape_of_equivalence (equivSmallModel.{w} J').symm
      obtain ⟨Z, z, hz⟩ :=
        IsCardinalPresentable.exists_hom_of_isColimit κ (isColimitOfPreserves P.ι
          ((isCardinalPresentable P.FullSubcategory κ).ι.denseAt ⟨F₂, hF₂⟩)) (c.ι.app j ≫ f)
      have : IsCardinalPresentable Z.left.obj.obj κ :=
        inferInstanceAs (IsCardinalPresentable (P.ι.obj Z.left.obj) κ)
      dsimp at z hz
      rw [Category.id_comp] at hz
      obtain ⟨r, hr⟩ := IsCardinalPure.exists_of_commSq κ ⟨hz⟩
      exact ⟨CostructuredArrow.mk (Y := ⟨Z.left.obj.obj, inferInstance⟩) (by exact r),
        by exact Z.left.obj.property, ⟨CostructuredArrow.homMk (ObjectProperty.homMk (by exact z))⟩⟩
    have : IsCardinalFiltered (P.inverseImage D).FullSubcategory κ :=
      ObjectProperty.isCardinalFiltered ..
    have := isCardinalClosedUnderColimitsOfShape P κ (P.inverseImage D).FullSubcategory
    exact P.prop_of_isColimit
      ((IsColimit.precomposeHomEquiv e _).symm
        ((Functor.Final.isColimitWhiskerEquiv (P.inverseImage D).ι _).symm hc))
      (fun X ↦ (D'.obj X).property)

end IsCardinalAccessibleCategory

namespace ObjectProperty

-- to be moved
lemma isAccessible_ι (P : ObjectProperty C) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [P.IsClosedUnderCardinalFilteredColimits κ] [IsAccessibleCategory.{w} C] :
    Functor.IsAccessible.{w} P.ι := by
  obtain ⟨κ₁, _, _⟩ := IsAccessibleCategory.exists_cardinal.{w} C
  obtain ⟨κ₂, _, h, h₁⟩ := Cardinal.SharplyLT.exists_of_pair κ κ₁
  have := h₁.isCardinalAccessibleCategory C
  have : P.IsClosedUnderCardinalFilteredColimits κ₂ := .of_le h.le
  refine ⟨κ₂, inferInstance, ?_⟩
  infer_instance

-- key part of Proposition 2.32
lemma isClosedUnderCardinalPureSubobjects
    [EssentiallySmall.{w} C] (P : ObjectProperty (C ⥤ Type w))
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [P.IsClosedUnderCardinalFilteredColimits κ]
    [IsAccessibleCategory.{w} P.FullSubcategory] :
    ∃ (κ' : Cardinal.{w}) (_ : Fact κ'.IsRegular) (_ : κ.SharplyLT κ'),
      P.IsClosedUnderCardinalPureSubobjects κ' ∧
      IsCardinalAccessibleCategory P.FullSubcategory κ' ∧
      P.ι.IsCardinalAccessible κ' ∧
        P.ι.PreservesCardinalPresentable κ' := by
  obtain ⟨κ', _, h, _, _⟩ : ∃ (κ' : Cardinal.{w}) (_ : Fact κ'.IsRegular) (_ : κ.SharplyLT κ'),
      P.ι.PreservesCardinalPresentable κ' ∧
        IsCardinalAccessibleCategory.{w} P.FullSubcategory κ' := by
    have := P.isAccessible_ι κ
    obtain ⟨κ₁, _, _, _, _, _⟩ := IsCardinalAccessibleCategory.uniformization P.ι
    obtain ⟨κ₂, _, h, h₁⟩ := Cardinal.SharplyLT.exists_of_pair κ κ₁
    exact ⟨κ₂, inferInstance, h, h₁.preservesCardinalPresentable _,
      h₁.isCardinalAccessibleCategory _⟩
  have : P.IsClosedUnderCardinalFilteredColimits κ' := .of_le h.le
  exact ⟨κ', inferInstance, h, inferInstance, inferInstance, inferInstance, inferInstance⟩

end ObjectProperty

namespace IsCardinalAccessibleCategory

namespace step₁

variable {C : Type w} [SmallCategory C] {κ : Cardinal.{w}} [Fact κ.IsRegular]
   {F : C ⥤ Type w}

structure Span (P : ObjectProperty (C ⥤ Type w)) (S : Subfunctor F) where
  src : C ⥤ Type w
  tgt : C ⥤ Type w
  prop_src : P src
  prop_tgt : P tgt
  t : src ⟶ tgt
  l : src ⟶ S.toFunctor
  exists_r : ∃ (r : tgt ⟶ F), t ≫ r = l ≫ S.ι

namespace Span

variable {P : ObjectProperty (C ⥤ Type w)} {S : Subfunctor F}

instance [ObjectProperty.Small.{w} P] :
    Small.{w} (Span P S) := by
  let φ (s : Span P S) : Σ (src tgt : P.FullSubcategory),
      (src.obj ⟶ tgt.obj) × (src.obj ⟶ S.toFunctor) :=
    ⟨⟨s.src, s.prop_src⟩, ⟨s.tgt, s.prop_tgt⟩, s.t, s.l⟩
  refine small_of_injective (f := φ) (fun s s' h ↦ ?_)
  obtain ⟨src, tgt, _, _, t, l, _⟩ := s
  obtain ⟨src', tgt', _, _, t', l', _⟩ := s'
  obtain rfl : src = src' := congr($(h).1.obj)
  obtain rfl : tgt = tgt' := congr($(h).2.1.obj)
  simpa [φ] using h

noncomputable def r (s : Span P S) : s.tgt ⟶ F := s.exists_r.choose

@[reassoc]
lemma fac (s : Span P S) : s.t ≫ s.r = s.l ≫ S.ι := s.exists_r.choose_spec

end Span

variable (P : ObjectProperty (C ⥤ Type w)) (S : Subfunctor F)

noncomputable def step : Subfunctor F :=
  S ⊔ ⨆ (s : Span P S), Subfunctor.range s.r

variable {P S} in
noncomputable def Span.r' (s : Span P S) : s.tgt ⟶ (step P S).toFunctor :=
  Subfunctor.lift s.r (le_trans (by rfl) ((le_iSup _ s).trans le_sup_right))

@[reassoc (attr := simp)]
lemma Span.r'_ι (s : Span P S) : s.r' ≫ (step P S).ι = s.r := rfl

lemma le_step :
    S ≤ step P S :=
  le_sup_left

variable (κ) (hC : HasCardinalLT (Arrow C) κ) (hP : isCardinalPresentable _ κ = P.isoClosure)

noncomputable def iter (a : κ.ord.ToType) : Subfunctor F :=
  transfiniteIterate (step P) a S

lemma iter_succ (a : κ.ord.ToType) :
    iter κ P S (Order.succ a) = step P (iter κ P S a) := by
  have : NoMaxOrder κ.ord.ToType :=
    Cardinal.noMaxOrder (Cardinal.IsRegular.aleph0_le Fact.out)
  exact transfiniteIterate_succ _ _ _ (not_isMax _)

omit [Fact κ.IsRegular] in
lemma iter_of_isSuccLimit (a : κ.ord.ToType) (ha : Order.IsSuccLimit a) :
    iter κ P S a = ⨆ (b : Set.Iio a), iter κ P S b :=
  transfiniteIterate_limit _ _ _ ha

omit [Fact κ.IsRegular] in
lemma iter_monotone : Monotone (iter κ P S) := by
  intro j _ h
  have : Nonempty κ.ord.ToType := ⟨j⟩
  let : OrderBot (κ.ord.ToType) := WellFoundedLT.toOrderBot _
  exact monotone_transfiniteIterate _ _ (le_step P) h

noncomputable def subfunctor : Subfunctor F :=
  ⨆ (j : κ.ord.ToType), iter κ P S j

variable {κ} in
omit [Fact κ.IsRegular] in
lemma iter_le_subfunctor (S : Subfunctor F) (j : κ.ord.ToType) :
    iter κ P S j ≤ subfunctor κ P S :=
  le_iSup ..

lemma le_subfunctor : S ≤ subfunctor κ P S := by
  have : Nonempty κ.ord.ToType :=
    Cardinal.nonempty_ord_toType (Cardinal.IsRegular.ne_zero Fact.out)
  let : OrderBot (κ.ord.ToType) := WellFoundedLT.toOrderBot _
  have := iter_le_subfunctor (κ := κ) P S ⊥
  exact le_trans (by simp [iter]) (iter_le_subfunctor (κ := κ) P S ⊥)

@[implicit_reducible, simps!]
noncomputable def subfunctorCocone :
    Cocone (iter_monotone κ P S).functor where
  pt := subfunctor κ P S
  ι.app j := homOfLE (iter_le_subfunctor P S j)

noncomputable def isColimitSubfunctorCocone :
    IsColimit (subfunctorCocone κ P S) :=
  (Preorder.colimitCoconeOfIsLUB _ isLUB_iSup).isColimit

variable {κ P} in
include hP in
lemma isCardinalPure_subfunctor_ι (S : Subfunctor F) :
    IsCardinalPure κ (subfunctor κ P S).ι where
  exists_of_commSq {X' Y' t l r hX' hY'} sq := by
    wlog h : P X' ∧ P Y' generalizing X' Y'
    · obtain ⟨X, hX, ⟨e₁⟩⟩ : P.isoClosure X' := by rwa [← hP]
      obtain ⟨Y, hY, ⟨e₂⟩⟩ : P.isoClosure Y' := by rwa [← hP]
      have hX' := isCardinalPresentable_of_iso e₁ κ
      have hY' := isCardinalPresentable_of_iso e₂ κ
      have sq' : CommSq (e₁.inv ≫ t ≫ e₂.hom) (e₁.inv ≫ l)
        (e₂.inv ≫ r) (subfunctor κ P S).ι := ⟨by simp [sq.w]⟩
      obtain ⟨ρ, hρ⟩ := this (hX' := hX') (hY' := hY') sq' ⟨hX, hY⟩
      exact ⟨e₂.hom ≫ ρ, by cat_disch⟩
    obtain ⟨j, l', hl'⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ
      (isColimitOfPreserves Subfunctor.toFunctorFunctor
        (isColimitSubfunctorCocone κ P S)) l
    let s : Span P (iter κ P S j) :=
      { src := X'
        tgt := Y'
        prop_src := h.1
        prop_tgt := h.2
        t := t
        l := l'
        exists_r := ⟨r, by simp [sq.w, ← hl', Subfunctor.homOfLe_ι (iter_le_subfunctor P S j)]⟩ }
    refine ⟨s.r' ≫ Subfunctor.homOfLe (by rw [← iter_succ]; apply iter_le_subfunctor ), ?_⟩
    simp [← cancel_mono (Subfunctor.ι _), s.fac, ← hl', s,
      Subfunctor.homOfLe_ι (iter_le_subfunctor P S j)]

variable {κ P S} {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (hκ' : κ.SharplyLT κ')
  (hP' : HasCardinalLT P.FullSubcategory κ')

include hC hP hκ' in
lemma hasCardinalLT_hom {F G : C ⥤ Type w}
    (hF : P F) (hG : HasCardinalLT G.Elements (Order.succ (κ'.sigmaPowLT κ'))) :
    HasCardinalLT (F ⟶ G) (Order.succ (κ'.sigmaPowLT κ')) := by
  replace hF := P.le_isoClosure _ hF
  simp only [← hP, Presheaf.isCardinalPresentable_iff_hasCardinalLT_elements hC] at hF
  refine .of_injective ?_ _ NatTrans.injective_mapElements_obj
  simp only [hasCardinalLT_iff_cardinal_mk_lt, Order.lt_succ_iff, Cardinal.mk_pi,
    Cardinal.prod_const, Cardinal.lift_eq_id, id_eq] at hF hG ⊢
  refine le_trans ?_ (Cardinal.sigmaPowLT_pow_le κ' hκ'.lt)
  by_cases hG₀ : Cardinal.mk G.Elements = 0
  · simp only [hG₀]
    exact le_trans
      ((Cardinal.zero_power_le _).trans (Cardinal.one_le_aleph0.trans
        (le_trans (by simpa using Cardinal.IsRegular.aleph0_le Fact.out)
          (Cardinal.power_le_power_left
            (Cardinal.IsRegular.ne_zero Fact.out)
            (Cardinal.one_le_aleph0.trans (Cardinal.IsRegular.aleph0_le Fact.out))))))
      (Cardinal.power_le_power_right
        (Cardinal.le_sigmaPowLT κ'
          (le_trans (by simp) (Cardinal.IsRegular.aleph0_le Fact.out))))
  · exact (Cardinal.power_le_power_left hG₀ hF.le).trans (Cardinal.power_le_power_right hG)

include hC hP hκ' hP' in
lemma hasCardinalLT_span
    (hS : HasCardinalLT S.toFunctor.Elements (Order.succ (κ'.sigmaPowLT κ'))) :
    HasCardinalLT (Span P S) (Order.succ (κ'.sigmaPowLT κ')) := by
  have := κ'.fact_isRegular_succ_sigmaPowLT
  let φ (s : Span P S) : Σ (src tgt : P.FullSubcategory),
      (src.obj ⟶ tgt.obj) × (src.obj ⟶ S.toFunctor) :=
    ⟨⟨s.src, s.prop_src⟩, ⟨s.tgt, s.prop_tgt⟩, s.t, s.l⟩
  have hφ : Function.Injective φ := by
    rintro ⟨src, tgt, _, _, t, l, _⟩ ⟨src', tgt', _, _, t', l', _⟩ h
    obtain rfl : src = src' := congr($(h).1.obj)
    obtain rfl : tgt = tgt' := congr($(h).2.1.obj)
    obtain ⟨rfl, rfl⟩ : t = t' ∧ l = l' := by simpa [φ] using h
    rfl
  refine (hasCardinalLT_sigma _ _ (hP'.of_le (Cardinal.SharplyLT.sigmaPowLT κ').le)
    (fun src ↦ hasCardinalLT_sigma _ _ (hP'.of_le (Cardinal.SharplyLT.sigmaPowLT κ').le)
      fun tgt ↦ hasCardinalLT_prod (Cardinal.IsRegular.aleph0_le Fact.out)
        (hasCardinalLT_hom hC hP hκ' src.property ?_)
        (hasCardinalLT_hom hC hP hκ' src.property hS))).of_injective _ hφ
  have := P.le_isoClosure _ tgt.property
  simp only [← hP, Presheaf.isCardinalPresentable_iff_hasCardinalLT_elements hC] at this
  exact this.of_le (hκ'.le.trans (Cardinal.SharplyLT.sigmaPowLT κ').le)

include hC hP hκ' hP' in
lemma hasCardinalLT_step
    (hS : HasCardinalLT S.toFunctor.Elements (Order.succ (κ'.sigmaPowLT κ'))) :
    HasCardinalLT (step P S).toFunctor.Elements (Order.succ (κ'.sigmaPowLT κ')) := by
  have := κ'.fact_isRegular_succ_sigmaPowLT
  have hC' : HasCardinalLT (Arrow C) (Order.succ (κ'.sigmaPowLT κ')) := hC.of_le
    (hκ'.le.trans (Cardinal.SharplyLT.sigmaPowLT κ').le)
  refine Subfunctor.hasCardinalLT_elements_sup hS
    (Subfunctor.hasCardinalLT_elements_iSup
      (fun s ↦ .of_surjective ?_ _
        ((Subfunctor.toRange s.r).surjective_mapElements_obj_of_epi))
      (hasCardinalLT_span hC hP hκ' hP' hS))
    (Cardinal.IsRegular.aleph0_le Fact.out)
  have := P.le_isoClosure _ s.prop_tgt
  simp only [← hP, Presheaf.isCardinalPresentable_iff_hasCardinalLT_elements hC] at this
  exact this.of_le (hκ'.le.trans (Cardinal.SharplyLT.sigmaPowLT κ').le)

include hC hP hκ' hP' in
lemma hasCardinalLT_iter
    (hS : HasCardinalLT S.toFunctor.Elements (Order.succ (κ'.sigmaPowLT κ'))) (j : κ.ord.ToType) :
    HasCardinalLT (iter κ P S j).toFunctor.Elements (Order.succ (κ'.sigmaPowLT κ')) := by
  have := κ'.fact_isRegular_succ_sigmaPowLT
  have : Nonempty κ.ord.ToType := ⟨j⟩
  let : OrderBot (κ.ord.ToType) := WellFoundedLT.toOrderBot _
  induction j using SuccOrder.limitRecOn with
  | isMin a h =>
    obtain rfl := h.eq_bot
    simpa [iter]
  | succ j _ hj =>
    rw [iter_succ]
    exact hasCardinalLT_step hC hP hκ' hP' hj
  | isSuccLimit j h hj =>
    rw [iter_of_isSuccLimit _ _ _ _ h]
    exact Subfunctor.hasCardinalLT_elements_iSup (fun i ↦ hj _ i.property) (by
      refine HasCardinalLT.of_injective ?_ _ Subtype.val_injective
      simpa [hasCardinalLT_iff_cardinal_mk_lt] using hκ'.le.trans
        (Cardinal.le_sigmaPowLT κ' (le_trans (by simp) (Cardinal.IsRegular.aleph0_le Fact.out))))

include hC hP hκ' hP' in
lemma hasEnoughPureSubobjects_aux
    (hS : HasCardinalLT S.toFunctor.Elements (Order.succ (κ'.sigmaPowLT κ'))) :
    ∃ (S' : Subfunctor F) (_ : S ≤ S')
      (_ : HasCardinalLT S'.toFunctor.Elements (Order.succ (κ'.sigmaPowLT κ'))),
      IsCardinalPure κ S'.ι :=
  have := κ'.fact_isRegular_succ_sigmaPowLT
  ⟨_, le_subfunctor κ P S,
    Subfunctor.hasCardinalLT_elements_iSup (hasCardinalLT_iter hC hP hκ' hP' hS) (by
      simpa [hasCardinalLT_iff_cardinal_mk_lt] using hκ'.le.trans
        (κ'.le_sigmaPowLT (le_trans (by simp) (Cardinal.IsRegular.aleph0_le Fact.out)))),
      isCardinalPure_subfunctor_ι hP S⟩

include hC hP hκ' hP' in
lemma hasEnoughPureSubobjects :
    haveI := κ'.fact_isRegular_succ_sigmaPowLT
    (hκ'.trans (Cardinal.SharplyLT.sigmaPowLT κ')).HasEnoughPureSubobjects (C ⥤ Type w) :=
  have := κ'.fact_isRegular_succ_sigmaPowLT
  { exists_isCardinalPure {P' P} f _ := by
      have hC' : HasCardinalLT (Arrow C) (Order.succ (κ'.sigmaPowLT κ')) :=
        hC.of_le (hκ'.trans (Cardinal.SharplyLT.sigmaPowLT κ')).le
      obtain ⟨S', h₁, h₂, h₃⟩ :=
        hasEnoughPureSubobjects_aux hC hP hκ' hP' (by
          refine HasCardinalLT.of_surjective ?_ _
            (NatTrans.surjective_mapElements_obj_of_epi (Subfunctor.toRange f))
          rwa [← Presheaf.isCardinalPresentable_iff_hasCardinalLT_elements hC'])
      rw [← Presheaf.isCardinalPresentable_iff_hasCardinalLT_elements hC'] at h₂
      exact ⟨S'.toFunctor, inferInstance, Subfunctor.toRange f ≫ Subfunctor.homOfLe h₁,
        S'.ι, inferInstance, by simp⟩ }

end step₁

lemma step₁ (C : Type w) [SmallCategory C] (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    ∃ (κ' : Cardinal.{w}) (_ : Fact κ'.IsRegular) (h : κ.SharplyLT κ'),
      h.HasEnoughPureSubobjects (C ⥤ Type w) := by
  obtain ⟨κ₁, _, hκ₁⟩ := HasCardinalLT.exists_regular_cardinal (Arrow C)
  have : Fact κ₁.IsRegular := ⟨by assumption⟩
  obtain ⟨κ₂, _, h₀, h₁⟩ := Cardinal.SharplyLT.exists_of_pair κ κ₁
  have hκ₂ := hκ₁.of_le h₁.le
  have := Cardinal.fact_isRegular_succ_sigmaPowLT κ₂ κ₂
  obtain ⟨P, _, hP⟩ := ObjectProperty.EssentiallySmall.exists_eq_isoClosure.{w}
    (isCardinalPresentable (C ⥤ Type w) κ₂)
  have := Subtype P
  obtain ⟨κ₃, h₃, h₄⟩ := HasCardinalLT.exists_regular_cardinal P.FullSubcategory
  have : Fact κ₃.IsRegular := ⟨h₃⟩
  obtain ⟨κ₄, _, h₅, h₆⟩ := Cardinal.SharplyLT.exists_of_pair κ₂ κ₃
  have := κ₄.fact_isRegular_succ_sigmaPowLT
  exact ⟨Order.succ (κ₄.sigmaPowLT κ₄), inferInstance,
    h₀.trans (h₅.trans (Cardinal.SharplyLT.sigmaPowLT κ₄)),
    (step₁.hasEnoughPureSubobjects hκ₂ hP h₅ (h₄.of_le h₆.le)).trans h₀⟩

lemma _root_.Cardinal.SharplyLT.HasEnoughPureSubobjects.fullSubcategory
    {κ κ' : Cardinal.{w}} [Fact κ.IsRegular] [Fact κ'.IsRegular] {h : κ.SharplyLT κ'}
    {C : Type*} [Category* C] (hC : h.HasEnoughPureSubobjects C)
    (P : ObjectProperty C)
    [IsCardinalAccessibleCategory P.FullSubcategory κ]
    [P.IsClosedUnderCardinalFilteredColimits κ]
    [P.IsClosedUnderCardinalPureSubobjects κ]
    [P.ι.PreservesCardinalPresentable κ] :
    h.HasEnoughPureSubobjects P.FullSubcategory where
  exists_isCardinalPure {X Y} f _ := by
    have : P.IsClosedUnderCardinalFilteredColimits κ' := .of_le h.le
    have := hC.toIsCardinalAccessibleCategory
    have := h.isCardinalAccessibleCategory C
    have := h.preservesCardinalPresentable P.ι
    obtain ⟨X', _, f', i, _, fac⟩ := hC.exists_isCardinalPure f.hom
    exact ⟨⟨X', P.prop_of_isCardinalPure κ i Y.property⟩,
      .of_full_of_faithful P.ι (by assumption),
      ObjectProperty.homMk f', ObjectProperty.homMk i,
      IsCardinalPure.of_full_of_faithful P.ι (by assumption), by cat_disch⟩

lemma hasEnoughPureSubobjects (C : Type*) [Category* C]
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalAccessibleCategory C κ] :
    ∃ (κ' : Cardinal.{w}) (_ : Fact κ'.IsRegular) (h : κ.SharplyLT κ'),
      h.HasEnoughPureSubobjects C := by
  obtain ⟨A, _, P, _, _, ⟨e⟩⟩ :=
    IsCardinalAccessibleCategory.exists_equivalence_fullSubcategory C κ
  have : IsAccessibleCategory.{w} P.FullSubcategory := ⟨κ, inferInstance, inferInstance⟩
  obtain ⟨κ₁, _, h₁, _, _, _, _⟩ := P.isClosedUnderCardinalPureSubobjects κ
  obtain ⟨κ₂, inferInstance, h₂, H⟩ := step₁ A κ₁
  have : P.IsClosedUnderCardinalFilteredColimits κ₁ := .of_le h₁.le
  exact ⟨κ₂, inferInstance, h₁.trans h₂,
    ((H.fullSubcategory P).trans h₁).of_equivalence e.symm⟩

end IsCardinalAccessibleCategory

end CategoryTheory
