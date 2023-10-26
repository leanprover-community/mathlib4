/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Limits.Shapes.CommSq
import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.CategoryTheory.Limits.VanKampen

#align_import category_theory.extensive from "leanprover-community/mathlib"@"178a32653e369dce2da68dc6b2694e385d484ef1"

/-!

# Extensive categories

## Main definitions
- `CategoryTheory.FinitaryExtensive`: A category is (finitary) extensive if it has finite
  coproducts, and binary coproducts are van Kampen.

## Main Results
- `CategoryTheory.hasStrictInitialObjects_of_finitaryExtensive`: The initial object
  in extensive categories is strict.
- `CategoryTheory.FinitaryExtensive.mono_inr_of_isColimit`: Coproduct injections are monic in
  extensive categories.
- `CategoryTheory.BinaryCofan.isPullback_initial_to_of_isVanKampen`: In extensive categories,
  sums are disjoint, i.e. the pullback of `X ⟶ X ⨿ Y` and `Y ⟶ X ⨿ Y` is the initial object.
- `CategoryTheory.types.finitaryExtensive`: The category of types is extensive.

## TODO

Show that the following are finitary extensive:
- the categories of sheaves over a site
- `Scheme`
- `AffineScheme` (`CommRingᵒᵖ`)

## References
- https://ncatlab.org/nlab/show/extensive+category
- [Carboni et al, Introduction to extensive and distributive categories][CARBONI1993145]

-/


open CategoryTheory.Limits

namespace CategoryTheory

universe v' u' v u

variable {J : Type v'} [Category.{u'} J] {C : Type u} [Category.{v} C]

section Extensive

variable {X Y : C}

/-- A category is (finitary) extensive if it has finite coproducts,
and binary coproducts are van Kampen.

TODO: Show that this is iff all finite coproducts are van Kampen. -/
class FinitaryExtensive (C : Type u) [Category.{v} C] : Prop where
  [hasFiniteCoproducts : HasFiniteCoproducts C]
  /-- In a finitary extensive category, all coproducts are van Kampen-/
  van_kampen' : ∀ {X Y : C} (c : BinaryCofan X Y), IsColimit c → IsVanKampenColimit c
#align category_theory.finitary_extensive CategoryTheory.FinitaryExtensive

attribute [instance] FinitaryExtensive.hasFiniteCoproducts

theorem FinitaryExtensive.vanKampen [FinitaryExtensive C] {F : Discrete WalkingPair ⥤ C}
    (c : Cocone F) (hc : IsColimit c) : IsVanKampenColimit c := by
  let X := F.obj ⟨WalkingPair.left⟩
  let Y := F.obj ⟨WalkingPair.right⟩
  have : F = pair X Y := by
    apply Functor.hext
    · rintro ⟨⟨⟩⟩ <;> rfl
    · rintro ⟨⟨⟩⟩ ⟨j⟩ ⟨⟨rfl : _ = j⟩⟩ <;> simp
  clear_value X Y
  subst this
  exact FinitaryExtensive.van_kampen' c hc
#align category_theory.finitary_extensive.van_kampen CategoryTheory.FinitaryExtensive.vanKampen

theorem FinitaryExtensive.mono_inr_of_isColimit [FinitaryExtensive C] {c : BinaryCofan X Y}
    (hc : IsColimit c) : Mono c.inr :=
  BinaryCofan.mono_inr_of_isVanKampen (FinitaryExtensive.vanKampen c hc)
#align category_theory.finitary_extensive.mono_inr_of_is_colimit CategoryTheory.FinitaryExtensive.mono_inr_of_isColimit

theorem FinitaryExtensive.mono_inl_of_isColimit [FinitaryExtensive C] {c : BinaryCofan X Y}
    (hc : IsColimit c) : Mono c.inl :=
  FinitaryExtensive.mono_inr_of_isColimit (BinaryCofan.isColimitFlip hc)
#align category_theory.finitary_extensive.mono_inl_of_is_colimit CategoryTheory.FinitaryExtensive.mono_inl_of_isColimit

instance [FinitaryExtensive C] (X Y : C) : Mono (coprod.inl : X ⟶ X ⨿ Y) :=
  (FinitaryExtensive.mono_inl_of_isColimit (coprodIsCoprod X Y) : _)

instance [FinitaryExtensive C] (X Y : C) : Mono (coprod.inr : Y ⟶ X ⨿ Y) :=
  (FinitaryExtensive.mono_inr_of_isColimit (coprodIsCoprod X Y) : _)

theorem FinitaryExtensive.isPullback_initial_to_binaryCofan [FinitaryExtensive C]
    {c : BinaryCofan X Y} (hc : IsColimit c) :
    IsPullback (initial.to _) (initial.to _) c.inl c.inr :=
  BinaryCofan.isPullback_initial_to_of_isVanKampen (FinitaryExtensive.vanKampen c hc)
#align category_theory.finitary_extensive.is_pullback_initial_to_binary_cofan CategoryTheory.FinitaryExtensive.isPullback_initial_to_binaryCofan

instance (priority := 100) hasStrictInitialObjects_of_finitaryExtensive [FinitaryExtensive C] :
    HasStrictInitialObjects C :=
  hasStrictInitial_of_isUniversal (FinitaryExtensive.vanKampen _
    ((BinaryCofan.isColimit_iff_isIso_inr initialIsInitial _).mpr (by
      dsimp
      infer_instance)).some).isUniversal
#align category_theory.has_strict_initial_objects_of_finitary_extensive CategoryTheory.hasStrictInitialObjects_of_finitaryExtensive

theorem finitaryExtensive_iff_of_isTerminal (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    (T : C) (HT : IsTerminal T) (c₀ : BinaryCofan T T) (hc₀ : IsColimit c₀) :
    FinitaryExtensive C ↔ IsVanKampenColimit c₀ := by
  refine' ⟨fun H => H.2 c₀ hc₀, fun H => _⟩
  constructor
  simp_rw [BinaryCofan.isVanKampen_iff] at H ⊢
  intro X Y c hc X' Y' c' αX αY f hX hY
  obtain ⟨d, hd, hd'⟩ :=
    Limits.BinaryCofan.IsColimit.desc' hc (HT.from _ ≫ c₀.inl) (HT.from _ ≫ c₀.inr)
  rw [H c' (αX ≫ HT.from _) (αY ≫ HT.from _) (f ≫ d) (by rw [← reassoc_of% hX, hd, Category.assoc])
      (by rw [← reassoc_of% hY, hd', Category.assoc])]
  obtain ⟨hl, hr⟩ := (H c (HT.from _) (HT.from _) d hd.symm hd'.symm).mp ⟨hc⟩
  rw [hl.paste_vert_iff hX.symm, hr.paste_vert_iff hY.symm]
#align category_theory.finitary_extensive_iff_of_is_terminal CategoryTheory.finitaryExtensive_iff_of_isTerminal

instance types.finitaryExtensive : FinitaryExtensive (Type u) := by
  classical
  rw [finitaryExtensive_iff_of_isTerminal (Type u) PUnit Types.isTerminalPunit _
      (Types.binaryCoproductColimit _ _)]
  apply BinaryCofan.isVanKampen_mk _ _ (fun X Y => Types.binaryCoproductColimit X Y) _
      fun f g => (Limits.Types.pullbackLimitCone f g).2
  · intros _ _ _ _ f hαX hαY
    constructor
    · refine' ⟨⟨hαX.symm⟩, ⟨PullbackCone.isLimitAux' _ _⟩⟩
      intro s
      have : ∀ x, ∃! y, s.fst x = Sum.inl y := by
        intro x
        cases' h : s.fst x with val val
        · simp only [Types.binaryCoproductCocone_pt, Functor.const_obj_obj, Sum.inl.injEq,
            exists_unique_eq']
        · apply_fun f at h
          cases ((congr_fun s.condition x).symm.trans h).trans (congr_fun hαY val : _).symm
      delta ExistsUnique at this
      choose l hl hl' using this
      exact ⟨l, (funext hl).symm, Types.isTerminalPunit.hom_ext _ _,
        fun {l'} h₁ _ => funext fun x => hl' x (l' x) (congr_fun h₁ x).symm⟩
    · refine' ⟨⟨hαY.symm⟩, ⟨PullbackCone.isLimitAux' _ _⟩⟩
      intro s
      have : ∀ x, ∃! y, s.fst x = Sum.inr y := by
        intro x
        cases' h : s.fst x with val val
        · apply_fun f at h
          cases ((congr_fun s.condition x).symm.trans h).trans (congr_fun hαX val : _).symm
        · simp only [Types.binaryCoproductCocone_pt, Functor.const_obj_obj, Sum.inr.injEq,
            exists_unique_eq']
      delta ExistsUnique at this
      choose l hl hl' using this
      exact ⟨l, (funext hl).symm, Types.isTerminalPunit.hom_ext _ _,
        fun {l'} h₁ _ => funext fun x => hl' x (l' x) (congr_fun h₁ x).symm⟩
  · intro Z f
    dsimp [Limits.Types.binaryCoproductCocone]
    delta Types.PullbackObj
    have : ∀ x, f x = Sum.inl PUnit.unit ∨ f x = Sum.inr PUnit.unit := by
      intro x
      rcases f x with (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
      exacts [Or.inl rfl, Or.inr rfl]
    let eX : { p : Z × PUnit // f p.fst = Sum.inl p.snd } ≃ { x : Z // f x = Sum.inl PUnit.unit } :=
      ⟨fun p => ⟨p.1.1, by convert p.2⟩, fun x => ⟨⟨_, _⟩, x.2⟩, fun _ => by ext; rfl,
        fun _ => by ext; rfl⟩
    let eY : { p : Z × PUnit // f p.fst = Sum.inr p.snd } ≃ { x : Z // f x = Sum.inr PUnit.unit } :=
      ⟨fun p => ⟨p.1.1, p.2.trans (congr_arg Sum.inr <| Subsingleton.elim _ _)⟩,
        fun x => ⟨⟨_, _⟩, x.2⟩, fun _ => by ext; rfl, fun _ => by ext; rfl⟩
    fapply BinaryCofan.isColimitMk
    · exact fun s x => dite _ (fun h => s.inl <| eX.symm ⟨x, h⟩)
        fun h => s.inr <| eY.symm ⟨x, (this x).resolve_left h⟩
    · intro s
      ext ⟨⟨x, ⟨⟩⟩, _⟩
      dsimp
      split_ifs <;> rfl
    · intro s
      ext ⟨⟨x, ⟨⟩⟩, hx⟩
      dsimp
      split_ifs with h
      · cases h.symm.trans hx
      · rfl
    · intro s m e₁ e₂
      ext x
      split_ifs
      · rw [← e₁]
        rfl
      · rw [← e₂]
        rfl
#align category_theory.types.finitary_extensive CategoryTheory.types.finitaryExtensive

section TopCat

/-- (Implementation) An auxiliary lemma for the proof that `TopCat` is finitary extensive. -/
-- Porting note : needs to add noncomputable modifier
noncomputable def finitaryExtensiveTopCatAux (Z : TopCat.{u})
    (f : Z ⟶ TopCat.of (Sum PUnit.{u + 1} PUnit.{u + 1})) :
    IsColimit (BinaryCofan.mk
      (TopCat.pullbackFst f (TopCat.binaryCofan (TopCat.of PUnit) (TopCat.of PUnit)).inl)
      (TopCat.pullbackFst f (TopCat.binaryCofan (TopCat.of PUnit) (TopCat.of PUnit)).inr)) := by
  have : ∀ x, f x = Sum.inl PUnit.unit ∨ f x = Sum.inr PUnit.unit := by
    intro x
    rcases f x with (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
    exacts [Or.inl rfl, Or.inr rfl]
  letI eX : { p : Z × PUnit // f p.fst = Sum.inl p.snd } ≃ { x : Z // f x = Sum.inl PUnit.unit } :=
    ⟨fun p => ⟨p.1.1, p.2.trans (congr_arg Sum.inl <| Subsingleton.elim _ _)⟩,
      fun x => ⟨⟨_, PUnit.unit⟩, x.2⟩, fun _ => by ext; rfl, fun _ => by ext; rfl⟩
  letI eY : { p : Z × PUnit // f p.fst = Sum.inr p.snd } ≃ { x : Z // f x = Sum.inr PUnit.unit } :=
    ⟨fun p => ⟨p.1.1, p.2.trans (congr_arg Sum.inr <| Subsingleton.elim _ _)⟩,
      fun x => ⟨⟨_, PUnit.unit⟩, x.2⟩, fun _ => by ext; rfl, fun _ => by ext; rfl⟩
  fapply BinaryCofan.isColimitMk
  classical -- Porting note: Added
  · refine' fun s => ⟨fun x => dite _
      (fun h => s.inl <| eX.symm ⟨x, h⟩) fun h => s.inr <| eY.symm ⟨x, (this x).resolve_left h⟩, _⟩
    rw [continuous_iff_continuousAt]
    intro x
    by_cases f x = Sum.inl PUnit.unit
    · revert h x
      apply (IsOpen.continuousOn_iff _).mp
      · rw [continuousOn_iff_continuous_restrict]
        convert_to Continuous fun x : { x | f x = Sum.inl PUnit.unit } =>
            s.inl ⟨(x.1, PUnit.unit), x.2⟩
        · ext ⟨x, hx⟩
          exact dif_pos hx
        -- Porting note : this `(BinaryCofan.inl s).2` was unnecessary
        have := (BinaryCofan.inl s).2
        continuity
      · convert f.2.1 _ openEmbedding_inl.open_range
        rename_i x
        exact ⟨fun h => ⟨_, h.symm⟩,
          fun ⟨e, h⟩ => h.symm.trans (congr_arg Sum.inl <| Subsingleton.elim _ _)⟩
    · revert h x
      apply (IsOpen.continuousOn_iff _).mp
      · rw [continuousOn_iff_continuous_restrict]
        convert_to Continuous fun x : { x | f x ≠ Sum.inl PUnit.unit } =>
            s.inr ⟨(x.1, PUnit.unit), (this _).resolve_left x.2⟩
        · ext ⟨x, hx⟩
          exact dif_neg hx
        -- Porting note : this `(BinaryCofan.inr s).2` was unnecessary
        have := (BinaryCofan.inr s).2
        continuity
      · convert f.2.1 _ openEmbedding_inr.open_range
        rename_i x
        change f x ≠ Sum.inl PUnit.unit ↔ f x ∈ Set.range Sum.inr
        trans f x = Sum.inr PUnit.unit
        · rcases f x with (⟨⟨⟩⟩ | ⟨⟨⟩⟩) <;>
            simp only [iff_self_iff, eq_self_iff_true, not_true, Ne.def, not_false_iff]
        · exact ⟨fun h => ⟨_, h.symm⟩,
            fun ⟨e, h⟩ => h.symm.trans (congr_arg Sum.inr <| Subsingleton.elim _ _)⟩
  · intro s
    ext ⟨⟨x, ⟨⟩⟩, (hx : f x = Sum.inl PUnit.unit)⟩
    change dite _ _ _ = _
    split_ifs with h
    · rfl
    · cases (h hx) -- Porting note : in Lean3 it is `rfl`
  · intro s
    ext ⟨⟨x, ⟨⟩⟩, hx⟩
    change dite _ _ _ = _
    split_ifs with h
    · cases h.symm.trans hx
    · rfl
  · intro s m e₁ e₂
    ext x
    change m x = dite _ _ _
    split_ifs
    · rw [← e₁]
      rfl
    · rw [← e₂]
      rfl
set_option linter.uppercaseLean3 false in
#align category_theory.finitary_extensive_Top_aux CategoryTheory.finitaryExtensiveTopCatAux

instance : FinitaryExtensive TopCat.{u} := by
  rw [finitaryExtensive_iff_of_isTerminal TopCat.{u} _ TopCat.isTerminalPUnit _
      (TopCat.binaryCofanIsColimit _ _)]
  apply BinaryCofan.isVanKampen_mk _ _ (fun X Y => TopCat.binaryCofanIsColimit X Y) _
      fun f g => TopCat.pullbackConeIsLimit f g
  · intro X' Y' αX αY f hαX hαY
    constructor
    · refine' ⟨⟨hαX.symm⟩, ⟨PullbackCone.isLimitAux' _ _⟩⟩
      intro s
      have : ∀ x, ∃! y, s.fst x = Sum.inl y := by
        intro x
        cases' h : s.fst x with val val
        · exact ⟨val, rfl, fun y h => Sum.inl_injective h.symm⟩
        · apply_fun f at h
          cases ((ConcreteCategory.congr_hom s.condition x).symm.trans h).trans
            (ConcreteCategory.congr_hom hαY val : _).symm
      delta ExistsUnique at this
      choose l hl hl' using this
      refine' ⟨⟨l, _⟩, ContinuousMap.ext fun a => (hl a).symm, TopCat.isTerminalPUnit.hom_ext _ _,
        fun {l'} h₁ _ => ContinuousMap.ext fun x =>
          hl' x (l' x) (ConcreteCategory.congr_hom h₁ x).symm⟩
      apply (embedding_inl (α := X') (β := Y')).toInducing.continuous_iff.mpr
      convert s.fst.2 using 1
      exact (funext hl).symm
    · refine' ⟨⟨hαY.symm⟩, ⟨PullbackCone.isLimitAux' _ _⟩⟩
      intro s
      have : ∀ x, ∃! y, s.fst x = Sum.inr y := by
        intro x
        cases' h : s.fst x with val val
        · apply_fun f at h
          cases ((ConcreteCategory.congr_hom s.condition x).symm.trans h).trans
            (ConcreteCategory.congr_hom hαX val : _).symm
        · exact ⟨val, rfl, fun y h => Sum.inr_injective h.symm⟩
      delta ExistsUnique at this
      choose l hl hl' using this
      refine' ⟨⟨l, _⟩, ContinuousMap.ext fun a => (hl a).symm, TopCat.isTerminalPUnit.hom_ext _ _,
        fun {l'} h₁ _ =>
          ContinuousMap.ext fun x => hl' x (l' x) (ConcreteCategory.congr_hom h₁ x).symm⟩
      apply (embedding_inr (α := X') (β := Y')).toInducing.continuous_iff.mpr
      convert s.fst.2 using 1
      exact (funext hl).symm
  · intro Z f
    exact finitaryExtensiveTopCatAux Z f

end TopCat

section Functor

universe v'' u''

variable {D : Type u''} [Category.{v''} D]

instance [HasPullbacks C] [FinitaryExtensive C] : FinitaryExtensive (D ⥤ C) :=
  haveI : HasFiniteCoproducts (D ⥤ C) := ⟨fun _ => Limits.functorCategoryHasColimitsOfShape⟩
  ⟨fun c hc => isVanKampenColimit_of_evaluation _ c fun _ =>
    FinitaryExtensive.vanKampen _ <| PreservesColimit.preserves hc⟩

theorem finitaryExtensive_of_preserves_and_reflects (F : C ⥤ D) [FinitaryExtensive D]
    [HasFiniteCoproducts C] [PreservesLimitsOfShape WalkingCospan F]
    [ReflectsLimitsOfShape WalkingCospan F] [PreservesColimitsOfShape (Discrete WalkingPair) F]
    [ReflectsColimitsOfShape (Discrete WalkingPair) F] : FinitaryExtensive C :=
  ⟨fun _ hc => (FinitaryExtensive.vanKampen _ (isColimitOfPreserves F hc)).of_mapCocone F⟩
#align category_theory.finitary_extensive_of_preserves_and_reflects CategoryTheory.finitaryExtensive_of_preserves_and_reflects

theorem finitaryExtensive_of_preserves_and_reflects_isomorphism (F : C ⥤ D) [FinitaryExtensive D]
    [HasFiniteCoproducts C] [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F]
    [PreservesColimitsOfShape (Discrete WalkingPair) F] [ReflectsIsomorphisms F] :
    FinitaryExtensive C := by
  haveI : ReflectsLimitsOfShape WalkingCospan F := reflectsLimitsOfShapeOfReflectsIsomorphisms
  haveI : ReflectsColimitsOfShape (Discrete WalkingPair) F :=
    reflectsColimitsOfShapeOfReflectsIsomorphisms
  exact finitaryExtensive_of_preserves_and_reflects F
#align category_theory.finitary_extensive_of_preserves_and_reflects_isomorphism CategoryTheory.finitaryExtensive_of_preserves_and_reflects_isomorphism

end Functor

end Extensive

end CategoryTheory
