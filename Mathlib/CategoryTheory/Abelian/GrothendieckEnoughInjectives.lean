/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Presentable.GrothendieckAbelian
import Mathlib.CategoryTheory.SmallObject.Basic
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting
import Mathlib.Order.TransfiniteIteration
import Mathlib.SetTheory.Ordinal.Basic

/-!
# Grothendieck abelian categories have enough injectives

TODO

-/

universe w v u

lemma Cardinal.zero_lt_ord_iff (κ : Cardinal.{w}) : 0 < κ.ord ↔ κ ≠ 0 := by
  constructor
  · intro h h'
    simp only [h', ord_zero, lt_self_iff_false] at h
  · intro h
    by_contra!
    exact h (ord_eq_zero.1 (le_antisymm this (Ordinal.zero_le _)))

namespace CategoryTheory

open Category Opposite Limits ZeroObject

lemma IsFiltered.set_iio {J : Type w} [LinearOrder J] [OrderBot J]
    (j : J) (hj : Order.IsSuccLimit j) : IsFiltered (Set.Iio j) := by
  have : Nonempty (Set.Iio j) := ⟨⟨⊥, by
    simp only [Set.mem_Iio]
    by_contra!
    simp only [le_bot_iff] at this
    subst this
    have := hj.not_isMin
    simp at this⟩⟩
  infer_instance

noncomputable instance (o : Ordinal.{w}) : SuccOrder o.toType :=
  SuccOrder.ofLinearWellFoundedLT o.toType

variable {C : Type u} [Category.{v} C]

section

lemma Injective.hasLiftingProperty_of_isZero
    {A B I Z : C} (i : A ⟶ B) [Mono i] [Injective I] (p : I ⟶ Z) (hZ : IsZero Z) :
    HasLiftingProperty i p where
  sq_hasLift {f g} sq := ⟨⟨{
    l := Injective.factorThru f i
    fac_right := hZ.eq_of_tgt _ _ }⟩⟩

instance {A B I : C} (i : A ⟶ B)  [Mono i] [Injective I] [HasZeroObject C] (p : I ⟶ 0) :
    HasLiftingProperty i (p : I ⟶ 0) :=
  Injective.hasLiftingProperty_of_isZero i p (isZero_zero C)

lemma injective_iff_eq_zero [HasZeroMorphisms C] {I Z : C} (p : I ⟶ Z) (hZ : IsZero Z) :
    Injective I ↔ (MorphismProperty.monomorphisms C).rlp p := by
  obtain rfl := hZ.eq_of_tgt p 0
  constructor
  · intro _ A B i (_ : Mono i)
    exact Injective.hasLiftingProperty_of_isZero i 0 hZ
  · intro h
    constructor
    intro A B f i hi
    have := h _ hi
    have sq : CommSq f i (0 : I ⟶ Z) 0 := ⟨by simp⟩
    exact ⟨sq.lift, by simp⟩

lemma injective_iff_monomorphisms_rlp_zero [HasZeroMorphisms C] [HasZeroObject C] (I : C) :
    Injective I ↔ (MorphismProperty.monomorphisms C).rlp (0 : I ⟶ 0) :=
  injective_iff_eq_zero _ (isZero_zero C)

end

namespace Subobject

lemma mk_lt_mk_of_comm {X A₁ A₂ : C} {i₁ : A₁ ⟶ X} {i₂ : A₂ ⟶ X} [Mono i₁] [Mono i₂]
    (f : A₁ ⟶ A₂) (fac : f ≫ i₂ = i₁) (hf : ¬ IsIso f) :
    Subobject.mk i₁ < Subobject.mk i₂ := by
  obtain _ | h := (mk_le_mk_of_comm _ fac).lt_or_eq
  · assumption
  · exfalso
    refine hf ⟨ofMkLEMk i₂ i₁ (by rw [h]), ?_, ?_⟩
    · simp only [← cancel_mono i₁, assoc, ofMkLEMk_comp, fac, id_comp]
    · simp only [← cancel_mono i₂, assoc, ofMkLEMk_comp, fac, id_comp]

lemma mk_lt_mk_iff_of_comm {X A₁ A₂ : C} {i₁ : A₁ ⟶ X} {i₂ : A₂ ⟶ X} [Mono i₁] [Mono i₂]
    (f : A₁ ⟶ A₂) (fac : f ≫ i₂ = i₁) :
    Subobject.mk i₁ < Subobject.mk i₂ ↔ ¬ IsIso f :=
  ⟨fun h hf ↦ by simp only [mk_eq_mk_of_comm i₁ i₂ (asIso f) fac, lt_self_iff_false] at h,
    mk_lt_mk_of_comm f fac⟩

lemma map_mk {A X Y : C} (i : A ⟶ X) [Mono i] (f : X ⟶ Y) [Mono f] :
    (map f).obj (mk i) = mk (i ≫ f) :=
  rfl

lemma map_obj_injective {X Y : C} (f : X ⟶ Y) [Mono f] :
    Function.Injective (Subobject.map f).obj := by
  intro X₁ X₂ h
  induction' X₁ using Subobject.ind with X₁ i₁ _
  induction' X₂ using Subobject.ind with X₂ i₂ _
  simp only [map_mk] at h
  exact mk_eq_mk_of_comm _ _ (isoOfMkEqMk _ _ h) (by simp [← cancel_mono f])

lemma hasCardinalLT_of_mono {Y : C} {κ : Cardinal.{w}}
    (h : HasCardinalLT (Subobject Y) κ) {X : C} (f : X ⟶ Y) [Mono f] :
    HasCardinalLT (Subobject X) κ :=
  h.of_injective _ (map_obj_injective f)

end Subobject

section Preadditive

variable [Preadditive C]

variable {A B X Y : C} {f : A ⟶ X} {i : A ⟶ B} {j : X ⟶ Y} {g : B ⟶ Y}
  [HasBinaryBiproduct B X]

namespace CommSq

variable (h : CommSq f i j g)

@[simps]
noncomputable def shortComplex : ShortComplex C where
  f := biprod.lift i (-f)
  g := biprod.desc g j
  zero := by simp [h.w]

end CommSq

namespace IsPushout

variable (h : IsPushout f i j g)

noncomputable def isColimitCokernelCoforkShortComplex :
    IsColimit (CokernelCofork.ofπ _ h.shortComplex.zero) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun b hb ↦ h.desc (biprod.inr ≫ b) (biprod.inl ≫ b) (by
      dsimp at hb
      simp only [biprod.lift_eq, Preadditive.neg_comp,
        Preadditive.sub_comp, assoc, ← sub_eq_add_neg, sub_eq_zero] at hb
      exact hb.symm)) (by aesop_cat) (fun _ _ _ hm ↦ by
        refine h.hom_ext (by simpa using biprod.inr ≫= hm)
          (by simpa using biprod.inl ≫= hm))

lemma epi_shortComplex_g : Epi h.shortComplex.g := by
  rw [Preadditive.epi_iff_cancel_zero]
  intro _ b hb
  exact Cofork.IsColimit.hom_ext h.isColimitCokernelCoforkShortComplex
    (by simpa using hb)

end IsPushout

end Preadditive

instance [Abelian C] :
    (MorphismProperty.monomorphisms C).IsStableUnderCobaseChange where
  of_isPushout {X Y X' Y' g f inl inr} sq (hg : Mono g) := by
    let e : Arrow.mk (pushout.inl f g) ≅ Arrow.mk inl :=
      Arrow.isoMk (Iso.refl _)
        (IsColimit.coconePointUniqueUpToIso (colimit.isColimit (span f g))
          sq.isColimit)
    exact ((MorphismProperty.monomorphisms C).arrow_iso_iff e).1
      (MorphismProperty.monomorphisms.infer_property (pushout.inl f g))

section Abelian

namespace IsPushout

variable [Abelian C] {A B X Y : C} {f : A ⟶ X} {i : A ⟶ B} {j : X ⟶ Y} {g : B ⟶ Y}

lemma shortComplex_exact (h : IsPushout f i j g) : h.shortComplex.Exact :=
  h.shortComplex.exact_of_g_is_cokernel
    h.isColimitCokernelCoforkShortComplex

lemma hom_eq_add_up_to_refinements (h : IsPushout f i j g) {T : C} (y : T ⟶ Y) :
    ∃ (T' : C) (π : T' ⟶ T) (_ : Epi π) (b : T' ⟶ B) (x : T' ⟶ X),
      π ≫ y = b ≫ g + x ≫ j := by
  have := h.epi_shortComplex_g
  obtain ⟨T', π, _, z, hz⟩ := surjective_up_to_refinements_of_epi h.shortComplex.g y
  refine ⟨T', π, inferInstance, z ≫ biprod.fst, z ≫ biprod.snd, ?_⟩
  simp only [hz, assoc, ← Preadditive.comp_add]
  congr
  aesop_cat

lemma mono_of_isPushout_of_isPullback_of_mono {A B X Y : C}
    {f : A ⟶ X} {i : A ⟶ B} {j : X ⟶ Y} {g : B ⟶ Y}
    (h₁ : IsPushout f i j g) {Z : C} {j' : X ⟶ Z} {g' : B ⟶ Z}
    (h₂ : IsPullback f i j' g') (k : Y ⟶ Z)
    (fac₁ : j ≫ k = j') (fac₂ : g ≫ k = g') [Mono j'] : Mono k :=
  Preadditive.mono_of_cancel_zero _ (fun {T₀} y hy ↦ by
    obtain ⟨T₁, π, _, b, x, eq⟩ := hom_eq_add_up_to_refinements h₁ y
    have fac₃ : (-x) ≫ j' = b ≫ g' := by
      rw [Preadditive.neg_comp, neg_eq_iff_add_eq_zero, add_comm, ← fac₂, ← fac₁,
        ← assoc, ← assoc, ← Preadditive.add_comp, ← eq, assoc, hy, comp_zero]
    obtain ⟨x', hx'⟩ : ∃ x', π ≫ y = x' ≫ j := by
      refine ⟨x + h₂.lift (-x) b fac₃ ≫ f, ?_⟩
      rw [eq, Preadditive.add_comp, assoc, h₁.w, IsPullback.lift_snd_assoc, add_comm]
    rw [← cancel_epi π, comp_zero, reassoc_of% hx', fac₁] at hy
    obtain rfl := zero_of_comp_mono _ hy
    rw [zero_comp] at hx'
    rw [← cancel_epi π, hx', comp_zero])

end IsPushout

end Abelian

namespace IsDetecting

lemma isIso_iff_of_mono {S : Set C} (hS : IsDetecting S)
    {X Y : C} (f : X ⟶ Y) [Mono f] :
    IsIso f ↔ ∀ (s : S), Function.Surjective ((coyoneda.obj (op s.1)).map f) := by
  constructor
  · intro h
    rw [isIso_iff_yoneda_map_bijective] at h
    rintro ⟨A, _⟩
    exact (h A).2
  · intro hf
    apply hS
    rintro A hA g
    apply existsUnique_of_exists_of_unique
    · exact hf ⟨A, hA⟩ g
    · intro l₁ l₂ h₁ h₂
      rw [← cancel_mono f, h₁, h₂]

end IsDetecting

namespace IsGrothendieckAbelian

def generatingMonomorphisms (G : C) : MorphismProperty C :=
  MorphismProperty.ofHoms (fun (X : Subobject G) ↦ X.arrow)

lemma generatingMonomorphisms_le_monomorphisms (G : C) :
    generatingMonomorphisms G ≤ MorphismProperty.monomorphisms C := by
  rintro _ _ _ ⟨X⟩
  exact inferInstanceAs (Mono _)

variable (G : C)

abbrev generatingMonomorphismsPushouts := (generatingMonomorphisms G).pushouts

variable [Abelian C]

lemma isomorphisms_le_generatingMonomorphismsPushouts :
    MorphismProperty.isomorphisms C ≤ generatingMonomorphismsPushouts G :=
  MorphismProperty.isomorphisms_le_pushouts _ (fun _ ↦ ⟨_, _, _, ⟨⊤⟩, 0, inferInstance⟩)

variable {G}

namespace TransfiniteCompositionMonoPushouts

variable (hG : IsSeparator G)
include hG

lemma exists_generatingMonomorphismsPushouts {X Y : C} (p : X ⟶ Y) [Mono p]
    (hp : ¬ IsIso p) :
    ∃ (X' : C) (i : X ⟶ X') (p' : X' ⟶ Y) (_ : generatingMonomorphismsPushouts G i)
      (_ : ¬ IsIso i) (_ : Mono p'), i ≫ p' = p := by
  rw [hG.isDetector.isIso_iff_of_mono] at hp
  simp only [coyoneda_obj_obj, Subtype.forall, Set.mem_singleton_iff, forall_eq,
    Function.Surjective, not_forall, not_exists] at hp
  obtain ⟨f, hf⟩ := hp
  let φ : pushout (pullback.fst p f) (pullback.snd p f) ⟶ Y :=
    pushout.desc p f pullback.condition
  refine ⟨pushout (pullback.fst p f) (pullback.snd p f), pushout.inl _ _, φ,
    ⟨_, _, _, (Subobject.underlyingIso _).hom ≫ pullback.fst _ _,
    pushout.inr _ _, ⟨Subobject.mk (pullback.snd p f)⟩,
    (IsPushout.of_hasPushout (pullback.fst p f) (pullback.snd p f)).of_iso
      ((Subobject.underlyingIso _).symm) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (by simp) (by simp) (by simp) (by simp)⟩, ?_, ?_, by simp [φ]⟩
  · intro h
    rw [isIso_iff_yoneda_map_bijective] at h
    obtain ⟨a, ha⟩ := (h G).2 (pushout.inr _ _)
    exact hf a (by simpa [φ] using ha =≫ φ)
  · exact (IsPushout.of_hasPushout _ _).mono_of_isPushout_of_isPullback_of_mono
      (IsPullback.of_hasPullback p f) φ (by simp [φ]) (by simp [φ])

variable {X : C}

lemma exists_larger_subobject {X : C} (A : Subobject X) (hA : A ≠ ⊤) :
    ∃ (A' : Subobject X) (h : A < A'),
      generatingMonomorphismsPushouts G (Subobject.ofLE _ _ h.le) := by
  induction' A using Subobject.ind with Y f _
  obtain ⟨X', i, p', hi, hi', hp', fac⟩ := exists_generatingMonomorphismsPushouts hG f
    (by simpa only [Subobject.isIso_iff_mk_eq_top] using hA)
  refine ⟨Subobject.mk p', Subobject.mk_lt_mk_of_comm i fac hi',
    (MorphismProperty.arrow_mk_iso_iff _ ?_).2 hi⟩
  refine Arrow.isoMk (Subobject.underlyingIso f) (Subobject.underlyingIso p') ?_
  dsimp
  simp only [← cancel_mono p', assoc, fac,
    Subobject.underlyingIso_hom_comp_eq_mk, Subobject.ofLE_arrow]

open Classical in
noncomputable def largerSubobject (A : Subobject X) : Subobject X :=
  if hA : A = ⊤ then ⊤ else (exists_larger_subobject hG A hA).choose

variable (X) in
@[simp]
lemma largerSubobject_top : largerSubobject hG (⊤ : Subobject X) = ⊤ := dif_pos rfl

lemma lt_largerSubobject (A : Subobject X) (hA : A ≠ ⊤) :
    A < largerSubobject hG A := by
  dsimp only [largerSubobject]
  rw [dif_neg hA]
  exact (exists_larger_subobject hG A hA).choose_spec.choose

lemma le_largerSubobject (A : Subobject X) :
    A ≤ largerSubobject hG A := by
  by_cases hA : A = ⊤
  · subst hA
    simp only [largerSubobject_top, le_refl]
  · exact (lt_largerSubobject hG A hA).le

lemma generatingMonomorphismsPushouts_ofLE_le_largerSubobject (A : Subobject X) :
      generatingMonomorphismsPushouts G (Subobject.ofLE _ _ (le_largerSubobject hG A)) := by
  by_cases hA : A = ⊤
  · subst hA
    have := (Subobject.isIso_arrow_iff_eq_top (largerSubobject hG (⊤ : Subobject X))).2 (by simp)
    exact (MorphismProperty.arrow_mk_iso_iff _
      (Arrow.isoMk (asIso (Subobject.arrow _)) (asIso (Subobject.arrow _)) (by simp))).2
        (isomorphisms_le_generatingMonomorphismsPushouts G (𝟙 X)
          (MorphismProperty.isomorphisms.infer_property _))
  · refine (MorphismProperty.arrow_mk_iso_iff _ ?_).1
      (exists_larger_subobject hG A hA).choose_spec.choose_spec
    exact Arrow.isoMk (Iso.refl _)
      (Subobject.isoOfEq _ _ ((by simp [largerSubobject, dif_neg hA])))

variable [IsGrothendieckAbelian.{w} C]

lemma top_mem_range (A₀ : Subobject X) {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J]
  [WellFoundedLT J] (hJ : Cardinal.mk (Shrink (Subobject X)) < Cardinal.mk J) :
    ∃ (j : J), transfiniteIterate (largerSubobject hG) j A₀ = ⊤ :=
  top_mem_range_transfiniteIterate (largerSubobject hG) A₀ (lt_largerSubobject hG) (by simp)
    (fun h ↦ (lt_self_iff_false _).1 (lt_of_le_of_lt
      (Cardinal.mk_le_of_injective ((equivShrink.{w} (Subobject X)).injective.comp h)) hJ))

lemma exists_ordinal (A₀ : Subobject X) :
    ∃ (o : Ordinal.{w}) (j : o.toType), transfiniteIterate (largerSubobject hG) j A₀ = ⊤ := by
  let κ := Order.succ (Cardinal.mk (Shrink.{w} (Subobject X)))
  have : OrderBot κ.ord.toType := Ordinal.toTypeOrderBotOfPos (by
    rw [Cardinal.zero_lt_ord_iff]
    exact Cardinal.succ_ne_zero _)
  exact ⟨κ.ord, top_mem_range hG A₀ (lt_of_lt_of_le (Order.lt_succ _) (by simp))⟩

section

variable (A₀ : Subobject X) (J : Type w) [LinearOrder J] [OrderBot J] [SuccOrder J]
  [WellFoundedLT J]

@[simps]
noncomputable def functorToMonoOver : J ⥤ MonoOver X where
  obj j := MonoOver.mk' (transfiniteIterate (largerSubobject hG) j A₀).arrow
  map {j j'} f := MonoOver.homMk (Subobject.ofLE _ _
      (monotone_transfiniteIterate _ _ (le_largerSubobject hG) (leOfHom f)))

noncomputable abbrev functor : J ⥤ C :=
  functorToMonoOver hG A₀ J ⋙ MonoOver.forget _ ⋙ Over.forget _

instance : (functor hG A₀ J).IsWellOrderContinuous where
  nonempty_isColimit m hm := ⟨by
    have := IsFiltered.set_iio _ hm
    let c := (functorToMonoOver hG A₀ J ⋙ MonoOver.forget _).coconeLT m
    have : Mono c.pt.hom := by dsimp [c]; infer_instance
    apply IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup
      ((functorToMonoOver hG A₀ J).restrictionLT m) c
    dsimp [c]
    simp only [Subobject.mk_arrow]
    exact transfiniteIterate_limit (largerSubobject hG) A₀ m hm⟩

example (j : J) : ((functor hG A₀ J).restrictionLE j).IsWellOrderContinuous := inferInstance

lemma mono_functor_map_le_succ (j : J) (hj : ¬IsMax j) :
    generatingMonomorphismsPushouts G ((functor hG A₀ J).map (homOfLE (Order.le_succ j))) := by
  refine (MorphismProperty.arrow_mk_iso_iff _ ?_).2
    (generatingMonomorphismsPushouts_ofLE_le_largerSubobject hG
      (transfiniteIterate (largerSubobject hG) j A₀))
  exact Arrow.isoMk (Iso.refl _) (Subobject.isoOfEq _ _ (transfiniteIterate_succ _ _ _ hj))
    (by simp [MonoOver.forget])

end

section

variable {A : C} {f : A ⟶ X} [Mono f] {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J]
  [WellFoundedLT J]
  {j : J} (hj : transfiniteIterate (largerSubobject hG) j (Subobject.mk f) = ⊤)

noncomputable def arrowIso :
    Arrow.mk f ≅ Arrow.mk (((functor hG (Subobject.mk f) J).coconeLE j).ι.app ⊥) := by
  let t := transfiniteIterate (largerSubobject hG) j (Subobject.mk f)
  have := (Subobject.isIso_arrow_iff_eq_top t).mpr hj
  refine (Arrow.isoMk (Subobject.isoOfEq _ _ (transfiniteIterate_bot _ _) ≪≫
    Subobject.underlyingIso f) (asIso t.arrow) ?_).symm
  simp [MonoOver.forget]

variable (f)

include hj in
lemma generatingMonomorphismsPushouts_transfiniteCompositionOfShape :
    (generatingMonomorphismsPushouts G).transfiniteCompositionsOfShape (Set.Iic j) f := by
  refine (MorphismProperty.arrow_iso_iff _ (arrowIso hG hj)).2 ?_
  dsimp [MonoOver.forget]
  refine ⟨_, fun ⟨k, hk⟩ hk' ↦ ?_, _,
    (functor hG (Subobject.mk f) J).isColimitCoconeLE j⟩
  dsimp [MonoOver.forget]
  convert generatingMonomorphismsPushouts_ofLE_le_largerSubobject hG
    (transfiniteIterate (largerSubobject hG) k (Subobject.mk f)) using 2
  all_goals
  · rw [Set.Iic.succ_eq _ hk', transfiniteIterate_succ _ _ _ (Set.not_isMax_coe _ hk')]

end

end TransfiniteCompositionMonoPushouts

open TransfiniteCompositionMonoPushouts in
lemma generatingMonomorphismsPushouts_rlp [IsGrothendieckAbelian.{w} C] (hG : IsSeparator G) :
    (generatingMonomorphisms G).rlp = (MorphismProperty.monomorphisms C).rlp := by
  apply le_antisymm
  · intro X Y p hp A B i (_ : Mono i)
    obtain ⟨o, j, hj⟩ := exists_ordinal hG (Subobject.mk i)
    have ho : Nonempty o.toType := ⟨j⟩
    rw [o.toType_nonempty_iff_ne_zero] at ho
    let _ : OrderBot o.toType := by
      apply Ordinal.toTypeOrderBotOfPos
      by_contra!
      exact ho (by simpa using this)
    exact MorphismProperty.hasLiftingProperty_of_transfiniteCompositionsOfShape _ i
      (generatingMonomorphismsPushouts_transfiniteCompositionOfShape hG i hj) p
      (by simpa only [MorphismProperty.pushouts_rlp] using hp)
  · exact MorphismProperty.antitone_rlp (generatingMonomorphisms_le_monomorphisms _)

namespace monomorphisms_isStableUnderTransfiniteComposition

variable [IsGrothendieckAbelian.{w} C]
  {J : Type w} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
  {F : J ⥤ C} [F.IsWellOrderContinuous]
  (hF : ∀ (j : J), ¬IsMax j → Mono (F.map (homOfLE (Order.le_succ j))))
  {c : Cocone F} (hc : IsColimit c)

include hF

lemma mono_map_from_bot (j : J) :
    Mono (F.map (homOfLE (bot_le : ⊥ ≤ j))) := by
  induction j using SuccOrder.limitRecOn with
  | hm j hj =>
      obtain rfl : j = ⊥ := by simpa using hj
      simp only [homOfLE_refl, Functor.map_id]
      infer_instance
  | hs j hj hj' =>
      have := hF j hj
      rw [← homOfLE_comp bot_le (Order.le_succ j), F.map_comp]
      infer_instance
  | hl j hj hj' =>
      let φ : (Functor.const _).obj (F.obj ⊥) ⟶ F.restrictionLT j :=
        { app j := F.map (homOfLE bot_le)
          naturality j j' f := by
            dsimp
            rw [← F.map_comp, id_comp]
            rfl }
      have := IsFiltered.set_iio j hj
      have : ∀ j, Mono (φ.app j) := fun ⟨j, hj⟩ ↦ hj' j hj
      exact HasExactColimitsOfShape.map_mono φ
        (constCoconeIsColimit _ (F.obj ⊥)) (F.isColimitOfIsWellOrderContinuous j hj)
        (F.map (homOfLE bot_le)) (fun ⟨k, kj⟩ ↦ by
          dsimp
          rw [← F.map_comp, id_comp]
          rfl)

include hc

lemma mono_ι_app : Mono (c.ι.app ⊥) := by
  let φ : (Functor.const J).obj (F.obj ⊥) ⟶ F :=
    { app j := F.map (homOfLE bot_le)
      naturality j j' f := by
        dsimp
        rw [← F.map_comp, id_comp]
        rfl }
  have : ∀ (j : J), Mono (φ.app j) := mono_map_from_bot hF
  exact HasExactColimitsOfShape.map_mono φ
    (constCoconeIsColimit J (F.obj ⊥)) hc (c.ι.app ⊥) (by simp)

end monomorphisms_isStableUnderTransfiniteComposition

open monomorphisms_isStableUnderTransfiniteComposition in
instance monomorphisms_isStableUnderTransfiniteComposition [IsGrothendieckAbelian.{w} C] :
    MorphismProperty.IsStableUnderTransfiniteComposition.{w}
      (MorphismProperty.monomorphisms C) where
  isStableUnderTransfiniteCompositionOfShape J _ _ _ _ := ⟨by
    rintro _ _ _ ⟨F, hF, c, hc⟩
    exact mono_ι_app hF hc⟩

namespace enoughInjectives

variable [IsGrothendieckAbelian.{w} C] (G) (hG : IsSeparator G)
variable (J : Type w) [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
variable {X Y : C} (f : X ⟶ Y)

instance : HasIterationOfShape C J where
  hasColimitsOfShape_of_isSuccLimit j hj := inferInstance

instance {Z : C} (π : Z ⟶ Y) :
    HasCoproductsOfShape (SmallObject.FunctorObjIndex
      (Subobject.arrow (X := G)) π) C :=
  hasColimitsOfShape_of_equivalence (Discrete.equivalence (equivShrink.{w} _).symm)

instance {Z : C} (π : Z ⟶ Y) :
    HasExactColimitsOfShape (Discrete (SmallObject.FunctorObjIndex
      (Subobject.arrow (X := G)) π)) C :=
  HasExactColimitsOfShape.of_domain_equivalence C
    (Discrete.equivalence (equivShrink.{w} _).symm)

noncomputable def obj : C := SmallObject.obj (Subobject.arrow (X := G)) J f

noncomputable def ιObj : X ⟶ obj G J f := SmallObject.ιObj _ _ f

noncomputable def πObj : obj G J f ⟶ Y := SmallObject.πObj _ _ f

@[reassoc (attr := simp)]
lemma ιObj_πObj : ιObj G J f ≫ πObj G J f = f := by simp [ιObj, πObj]

open MorphismProperty in
lemma transfiniteCompositionsOfShape_ιObj :
    (monomorphisms C).transfiniteCompositionsOfShape J (ιObj G J f) := by
  refine monotone_transfiniteCompositionsOfShape ?_ _ _
    (SmallObject.transfiniteCompositionsOfShape_ιObj (Subobject.arrow (X := G)) J f)
  refine (monotone_pushouts ?_).trans (monomorphisms C).pushouts_le
  intro A B i hi
  rw [coproducts_iff] at hi
  obtain ⟨J, hi⟩ := hi
  refine (HasExactColimitsOfShape.monomorphisms_isStableUnderColimitsOfShape
    _ _).colimitsOfShape_le _ (monotone_colimitsOfShape ?_ _ _ hi)
  rintro _ _ _ ⟨i⟩
  apply MorphismProperty.monomorphisms.infer_property

instance : Mono (ιObj G J f) :=
  (MorphismProperty.monomorphisms C).transfiniteCompositionsOfShape_le _ _
    (transfiniteCompositionsOfShape_ιObj G J f)

variable [NoMaxOrder J]

open MorphismProperty in
instance (j j' : J) (φ : j ⟶ j') :
    Mono ((SmallObject.inductiveSystemForget (Subobject.arrow (X := G)) J f).map φ) := by
  apply (monomorphisms C).mem_map_of_transfinite_composition
  intro k hk
  rw [SmallObject.inductiveSystemForget_map_le_succ _ _ _ _ hk]
  apply RespectsIso.postcomp
  apply of_isPushout (IsPushout.of_hasPushout _ _) _
  exact (HasExactColimitsOfShape.monomorphisms_isStableUnderColimitsOfShape C _).colimMap _
    (fun ⟨j⟩ ↦ inferInstanceAs (Mono j.i.arrow))

variable {κ : Cardinal.{w}} [Fact κ.IsRegular] [IsCardinalFiltered J κ]
  (hκ : HasCardinalLT (Subobject G) κ)

variable {G}
include hG hκ in
lemma rlp_πObj : (MorphismProperty.monomorphisms C).rlp (πObj G J f) := by
  rw [← generatingMonomorphismsPushouts_rlp hG]
  have : ∀ (i : Subobject G),
    PreservesColimit (SmallObject.inductiveSystemForget (Subobject.arrow (X := G)) J f)
      (coyoneda.obj (op (Subobject.underlying.obj i))) := fun i ↦
    IsPresentable.preservesColimit_of_mono (Subobject.hasCardinalLT_of_mono hκ i.arrow) _
  exact SmallObject.rlp_πObj (Subobject.arrow (X := G)) J f

end enoughInjectives

instance (κ : Cardinal.{w}) [hκ : Fact κ.IsRegular] :
    IsCardinalFiltered κ.ord.toType κ :=
  isCardinalFiltered_preorder _ _ (fun ι f hs ↦ by
    have h : Function.Surjective (fun i ↦ (⟨f i, i, rfl⟩ : Set.range f)) := fun _ ↦ by aesop
    have pif := Cardinal.mk_le_of_surjective h
    obtain ⟨j, hj⟩ := Ordinal.lt_cof_type (α := κ.ord.toType) (r := (· < ·))
      (S := Set.range f) (lt_of_le_of_lt (Cardinal.mk_le_of_surjective h) (lt_of_lt_of_le hs
          (by simp [hκ.out.cof_eq])))
    exact ⟨j, fun i ↦ (hj (f i) (by simp)).le⟩)

instance enoughInjectives [IsGrothendieckAbelian.{w} C] :
    EnoughInjectives C where
  presentation X := by
    obtain ⟨κ, hκ', hκ⟩ := HasCardinalLT.exists_regular_cardinal.{w} (Subobject (separator C))
    have : Fact κ.IsRegular := ⟨hκ'⟩
    have : OrderBot κ.ord.toType := Ordinal.toTypeOrderBotOfPos (Cardinal.IsRegular.ord_pos hκ')
    have := Cardinal.noMaxOrder hκ'.aleph0_le
    exact ⟨{
      f := enoughInjectives.ιObj (separator C) κ.ord.toType (0 : X ⟶ 0)
      injective := by
          rw [injective_iff_monomorphisms_rlp_zero]
          convert enoughInjectives.rlp_πObj (isSeparator_separator C)
            κ.ord.toType (0 : X ⟶ 0) hκ
          apply (isZero_zero C).eq_of_tgt }⟩

end IsGrothendieckAbelian

end CategoryTheory
