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
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
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
- `CategoryTheory.FinitaryExtensive_TopCat`:
  The category `Top` is extensive.
- `CategoryTheory.FinitaryExtensive_functor`: The category `C ⥤ D` is extensive if `D`
  has all pullbacks and is extensive.
- `CategoryTheory.FinitaryExtensive.isVanKampen_finiteCoproducts`: Finite coproducts in a
  finitary extensive category are van Kampen.
## TODO

Show that the following are finitary extensive:
- `Scheme`
- `AffineScheme` (`CommRingᵒᵖ`)

## References
- https://ncatlab.org/nlab/show/extensive+category
- [Carboni et al, Introduction to extensive and distributive categories][CARBONI1993145]

-/


open CategoryTheory.Limits

namespace CategoryTheory

universe v' u' v u v'' u''

variable {J : Type v'} [Category.{u'} J] {C : Type u} [Category.{v} C]
variable {D : Type u''} [Category.{v''} D]

section Extensive

variable {X Y : C}

/-- A category has pullback of inclusions if it has all pullbacks along coproduct injections. -/
class HasPullbacksOfInclusions (C : Type u) [Category.{v} C] [HasBinaryCoproducts C] : Prop where
  [hasPullbackInl : ∀ {X Y Z : C} (f : Z ⟶ X ⨿ Y), HasPullback coprod.inl f]

attribute [instance] HasPullbacksOfInclusions.hasPullbackInl

/--
A functor preserves pullback of inclusions if it preserves all pullbacks along coproduct injections.
-/
class PreservesPullbacksOfInclusions {C : Type*} [Category C] {D : Type*} [Category D]
    (F : C ⥤ D) [HasBinaryCoproducts C] where
  [preservesPullbackInl : ∀ {X Y Z : C} (f : Z ⟶ X ⨿ Y), PreservesLimit (cospan coprod.inl f) F]

attribute [instance] PreservesPullbacksOfInclusions.preservesPullbackInl

/-- A category is (finitary) pre-extensive if it has finite coproducts,
and binary coproducts are universal. -/
class FinitaryPreExtensive (C : Type u) [Category.{v} C] : Prop where
  [hasFiniteCoproducts : HasFiniteCoproducts C]
  [hasPullbacksOfInclusions : HasPullbacksOfInclusions C]
  /-- In a finitary extensive category, all coproducts are van Kampen-/
  universal' : ∀ {X Y : C} (c : BinaryCofan X Y), IsColimit c → IsUniversalColimit c

attribute [instance] FinitaryPreExtensive.hasFiniteCoproducts
attribute [instance] FinitaryPreExtensive.hasPullbacksOfInclusions

/-- A category is (finitary) extensive if it has finite coproducts,
and binary coproducts are van Kampen. -/
class FinitaryExtensive (C : Type u) [Category.{v} C] : Prop where
  [hasFiniteCoproducts : HasFiniteCoproducts C]
  [hasPullbacksOfInclusions : HasPullbacksOfInclusions C]
  /-- In a finitary extensive category, all coproducts are van Kampen-/
  van_kampen' : ∀ {X Y : C} (c : BinaryCofan X Y), IsColimit c → IsVanKampenColimit c
#align category_theory.finitary_extensive CategoryTheory.FinitaryExtensive

attribute [instance] FinitaryExtensive.hasFiniteCoproducts
attribute [instance] FinitaryExtensive.hasPullbacksOfInclusions

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

namespace HasPullbacksOfInclusions

instance (priority := 100) [HasBinaryCoproducts C] [HasPullbacks C] :
    HasPullbacksOfInclusions C := ⟨⟩

variable [HasBinaryCoproducts C] [HasPullbacksOfInclusions C] {X Y Z : C} (f : Z ⟶ X ⨿ Y)

instance preservesPullbackInl' :
    HasPullback f coprod.inl :=
  hasPullback_symmetry _ _

instance hasPullbackInr' :
    HasPullback f coprod.inr := by
  have : IsPullback (𝟙 _) (f ≫ (coprod.braiding X Y).hom) f (coprod.braiding Y X).hom :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have := (IsPullback.of_hasPullback (f ≫ (coprod.braiding X Y).hom) coprod.inl).paste_horiz this
  simp only [coprod.braiding_hom, Category.comp_id, colimit.ι_desc, BinaryCofan.mk_pt,
    BinaryCofan.ι_app_left, BinaryCofan.mk_inl] at this
  exact ⟨⟨⟨_, this.isLimit⟩⟩⟩

instance hasPullbackInr :
    HasPullback coprod.inr f :=
  hasPullback_symmetry _ _

end HasPullbacksOfInclusions

namespace PreservesPullbacksOfInclusions

variable {D : Type*} [Category D] [HasBinaryCoproducts C] (F : C ⥤ D)

noncomputable
instance (priority := 100) [PreservesLimitsOfShape WalkingCospan F] :
    PreservesPullbacksOfInclusions F := ⟨⟩

variable [PreservesPullbacksOfInclusions F] {X Y Z : C} (f : Z ⟶ X ⨿ Y)

noncomputable
instance preservesPullbackInl' :
    PreservesLimit (cospan f coprod.inl) F :=
  preservesPullbackSymmetry _ _ _

noncomputable
instance preservesPullbackInr' :
    PreservesLimit (cospan f coprod.inr) F := by
  apply preservesLimitOfIsoDiagram (K₁ := cospan (f ≫ (coprod.braiding X Y).hom) coprod.inl)
  apply cospanExt (Iso.refl _) (Iso.refl _) (coprod.braiding X Y).symm <;> simp

noncomputable
instance preservesPullbackInr :
    PreservesLimit (cospan coprod.inr f) F :=
  preservesPullbackSymmetry _ _ _

end PreservesPullbacksOfInclusions

instance (priority := 100) FinitaryExtensive.toFinitaryPreExtensive [FinitaryExtensive C] :
    FinitaryPreExtensive C :=
  ⟨fun c hc ↦ (FinitaryExtensive.van_kampen' c hc).isUniversal⟩

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

instance (priority := 100) hasStrictInitialObjects_of_finitaryPreExtensive
    [FinitaryPreExtensive C] : HasStrictInitialObjects C :=
  hasStrictInitial_of_isUniversal (FinitaryPreExtensive.universal' _
    ((BinaryCofan.isColimit_iff_isIso_inr initialIsInitial _).mpr (by
      dsimp
      infer_instance)).some)
#align category_theory.has_strict_initial_objects_of_finitary_extensive CategoryTheory.hasStrictInitialObjects_of_finitaryPreExtensive

theorem finitaryExtensive_iff_of_isTerminal (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [HasPullbacksOfInclusions C]
    (T : C) (HT : IsTerminal T) (c₀ : BinaryCofan T T) (hc₀ : IsColimit c₀) :
    FinitaryExtensive C ↔ IsVanKampenColimit c₀ := by
  refine ⟨fun H => H.van_kampen' c₀ hc₀, fun H => ?_⟩
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
    · refine ⟨⟨hαX.symm⟩, ⟨PullbackCone.isLimitAux' _ ?_⟩⟩
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
    · refine ⟨⟨hαY.symm⟩, ⟨PullbackCone.isLimitAux' _ ?_⟩⟩
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
noncomputable def finitaryExtensiveTopCatAux (Z : TopCat.{u})
    (f : Z ⟶ TopCat.of (Sum PUnit.{u + 1} PUnit.{u + 1})) :
    IsColimit (BinaryCofan.mk
      (TopCat.pullbackFst f (TopCat.binaryCofan (TopCat.of PUnit) (TopCat.of PUnit)).inl)
      (TopCat.pullbackFst f (TopCat.binaryCofan (TopCat.of PUnit) (TopCat.of PUnit)).inr)) := by
  have h₁ : Set.range (TopCat.pullbackFst f (TopCat.binaryCofan (.of PUnit) (.of PUnit)).inl) =
      f ⁻¹' Set.range Sum.inl := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩; exact ⟨PUnit.unit, x.2.symm⟩
    · rintro x ⟨⟨⟩, hx⟩; refine ⟨⟨⟨x, PUnit.unit⟩, hx.symm⟩, rfl⟩
  have h₂ : Set.range (TopCat.pullbackFst f (TopCat.binaryCofan (.of PUnit) (.of PUnit)).inr) =
      f ⁻¹' Set.range Sum.inr := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩; exact ⟨PUnit.unit, x.2.symm⟩
    · rintro x ⟨⟨⟩, hx⟩; refine ⟨⟨⟨x, PUnit.unit⟩, hx.symm⟩, rfl⟩
  refine ((TopCat.binaryCofan_isColimit_iff _).mpr ⟨?_, ?_, ?_⟩).some
  · refine ⟨(Homeomorph.prodPUnit Z).embedding.comp embedding_subtype_val, ?_⟩
    convert f.2.1 _ isOpen_range_inl
  · refine ⟨(Homeomorph.prodPUnit Z).embedding.comp embedding_subtype_val, ?_⟩
    convert f.2.1 _ isOpen_range_inr
  · convert Set.isCompl_range_inl_range_inr.preimage f
set_option linter.uppercaseLean3 false in
#align category_theory.finitary_extensive_Top_aux CategoryTheory.finitaryExtensiveTopCatAux

instance finitaryExtensive_TopCat : FinitaryExtensive TopCat.{u} := by
  rw [finitaryExtensive_iff_of_isTerminal TopCat.{u} _ TopCat.isTerminalPUnit _
      (TopCat.binaryCofanIsColimit _ _)]
  apply BinaryCofan.isVanKampen_mk _ _ (fun X Y => TopCat.binaryCofanIsColimit X Y) _
      fun f g => TopCat.pullbackConeIsLimit f g
  · intro X' Y' αX αY f hαX hαY
    constructor
    · refine ⟨⟨hαX.symm⟩, ⟨PullbackCone.isLimitAux' _ ?_⟩⟩
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
      refine ⟨⟨l, ?_⟩, ContinuousMap.ext fun a => (hl a).symm, TopCat.isTerminalPUnit.hom_ext _ _,
        fun {l'} h₁ _ => ContinuousMap.ext fun x =>
          hl' x (l' x) (ConcreteCategory.congr_hom h₁ x).symm⟩
      apply (embedding_inl (X := X') (Y := Y')).toInducing.continuous_iff.mpr
      convert s.fst.2 using 1
      exact (funext hl).symm
    · refine ⟨⟨hαY.symm⟩, ⟨PullbackCone.isLimitAux' _ ?_⟩⟩
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
      refine ⟨⟨l, ?_⟩, ContinuousMap.ext fun a => (hl a).symm, TopCat.isTerminalPUnit.hom_ext _ _,
        fun {l'} h₁ _ =>
          ContinuousMap.ext fun x => hl' x (l' x) (ConcreteCategory.congr_hom h₁ x).symm⟩
      apply (embedding_inr (X := X') (Y := Y')).toInducing.continuous_iff.mpr
      convert s.fst.2 using 1
      exact (funext hl).symm
  · intro Z f
    exact finitaryExtensiveTopCatAux Z f

end TopCat

section Functor

theorem finitaryExtensive_of_reflective
    [HasFiniteCoproducts D] [HasPullbacksOfInclusions D] [FinitaryExtensive C]
    {Gl : C ⥤ D} {Gr : D ⥤ C} (adj : Gl ⊣ Gr) [Gr.Full] [Gr.Faithful]
    [∀ X Y (f : X ⟶ Gl.obj Y), HasPullback (Gr.map f) (adj.unit.app Y)]
    [∀ X Y (f : X ⟶ Gl.obj Y), PreservesLimit (cospan (Gr.map f) (adj.unit.app Y)) Gl]
    [PreservesPullbacksOfInclusions Gl] :
    FinitaryExtensive D := by
  have : PreservesColimitsOfSize Gl := adj.leftAdjointPreservesColimits
  constructor
  intros X Y c hc
  apply (IsVanKampenColimit.precompose_isIso_iff
    (isoWhiskerLeft _ (asIso adj.counit) ≪≫ Functor.rightUnitor _).hom).mp
  have : ∀ (Z : C) (i : Discrete WalkingPair) (f : Z ⟶ (colimit.cocone (pair X Y ⋙ Gr)).pt),
        PreservesLimit (cospan f ((colimit.cocone (pair X Y ⋙ Gr)).ι.app i)) Gl := by
    have : pair X Y ⋙ Gr = pair (Gr.obj X) (Gr.obj Y) := by
      apply Functor.hext
      · rintro ⟨⟨⟩⟩ <;> rfl
      · rintro ⟨⟨⟩⟩ ⟨j⟩ ⟨⟨rfl : _ = j⟩⟩ <;> simp
    rw [this]
    rintro Z ⟨_|_⟩ f <;> dsimp <;> infer_instance
  refine ((FinitaryExtensive.vanKampen _ (colimit.isColimit <| pair X Y ⋙ _)).map_reflective
    adj).of_iso (IsColimit.uniqueUpToIso ?_ ?_)
  · exact isColimitOfPreserves Gl (colimit.isColimit _)
  · exact (IsColimit.precomposeHomEquiv _ _).symm hc

instance finitaryExtensive_functor [HasPullbacks C] [FinitaryExtensive C] :
    FinitaryExtensive (D ⥤ C) :=
  haveI : HasFiniteCoproducts (D ⥤ C) := ⟨fun _ => Limits.functorCategoryHasColimitsOfShape⟩
  ⟨fun c hc => isVanKampenColimit_of_evaluation _ c fun _ =>
    FinitaryExtensive.vanKampen _ <| PreservesColimit.preserves hc⟩

noncomputable
instance {C} [Category C] {D} [Category D] (F : C ⥤ D)
    {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [IsIso f] : PreservesLimit (cospan f g) F :=
  have := hasPullback_of_left_iso f g
  preservesLimitOfPreservesLimitCone (IsPullback.of_hasPullback f g).isLimit
    ((isLimitMapConePullbackConeEquiv _ pullback.condition).symm
      (IsPullback.of_vert_isIso ⟨by simp only [← F.map_comp, pullback.condition]⟩).isLimit)

noncomputable
instance {C} [Category C] {D} [Category D] (F : C ⥤ D)
    {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [IsIso g] : PreservesLimit (cospan f g) F :=
  preservesPullbackSymmetry _ _ _

theorem finitaryExtensive_of_preserves_and_reflects (F : C ⥤ D) [FinitaryExtensive D]
    [HasFiniteCoproducts C] [HasPullbacksOfInclusions C]
    [PreservesPullbacksOfInclusions F]
    [ReflectsLimitsOfShape WalkingCospan F] [PreservesColimitsOfShape (Discrete WalkingPair) F]
    [ReflectsColimitsOfShape (Discrete WalkingPair) F] : FinitaryExtensive C := by
  constructor
  intros X Y c hc
  refine IsVanKampenColimit.of_iso ?_ (hc.uniqueUpToIso (coprodIsCoprod X Y)).symm
  have (i : Discrete WalkingPair) (Z : C) (f : Z ⟶ X ⨿ Y) :
    PreservesLimit (cospan f ((BinaryCofan.mk coprod.inl coprod.inr).ι.app i)) F := by
    rcases i with ⟨_|_⟩ <;> dsimp <;> infer_instance
  refine (FinitaryExtensive.vanKampen _
    (isColimitOfPreserves F (coprodIsCoprod X Y))).of_mapCocone F
#align category_theory.finitary_extensive_of_preserves_and_reflects CategoryTheory.finitaryExtensive_of_preserves_and_reflects

theorem finitaryExtensive_of_preserves_and_reflects_isomorphism (F : C ⥤ D) [FinitaryExtensive D]
    [HasFiniteCoproducts C] [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F]
    [PreservesColimitsOfShape (Discrete WalkingPair) F] [F.ReflectsIsomorphisms] :
    FinitaryExtensive C := by
  haveI : ReflectsLimitsOfShape WalkingCospan F := reflectsLimitsOfShapeOfReflectsIsomorphisms
  haveI : ReflectsColimitsOfShape (Discrete WalkingPair) F :=
    reflectsColimitsOfShapeOfReflectsIsomorphisms
  exact finitaryExtensive_of_preserves_and_reflects F
#align category_theory.finitary_extensive_of_preserves_and_reflects_isomorphism CategoryTheory.finitaryExtensive_of_preserves_and_reflects_isomorphism

end Functor

section FiniteCoproducts

theorem FinitaryPreExtensive.isUniversal_finiteCoproducts_Fin [FinitaryPreExtensive C] {n : ℕ}
    {F : Discrete (Fin n) ⥤ C} {c : Cocone F} (hc : IsColimit c) : IsUniversalColimit c := by
  let f : Fin n → C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor f :=
    Functor.hext (fun _ ↦ rfl) (by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; simp [f])
  clear_value f
  subst this
  induction' n with n IH
  · exact (isVanKampenColimit_of_isEmpty _ hc).isUniversal
  · apply IsUniversalColimit.of_iso _
      ((extendCofanIsColimit f (coproductIsCoproduct _) (coprodIsCoprod _ _)).uniqueUpToIso hc)
    apply @isUniversalColimit_extendCofan _ _ _ _ _ _ _ _ ?_
    · apply IH
      exact coproductIsCoproduct _
    · apply FinitaryPreExtensive.universal'
      exact coprodIsCoprod _ _
    · dsimp
      infer_instance

theorem FinitaryPreExtensive.isUniversal_finiteCoproducts [FinitaryPreExtensive C] {ι : Type*}
    [Finite ι] {F : Discrete ι ⥤ C} {c : Cocone F} (hc : IsColimit c) : IsUniversalColimit c := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  apply (IsUniversalColimit.whiskerEquivalence_iff (Discrete.equivalence e).symm).mp
  apply FinitaryPreExtensive.isUniversal_finiteCoproducts_Fin
  exact (IsColimit.whiskerEquivalenceEquiv (Discrete.equivalence e).symm) hc

theorem FinitaryExtensive.isVanKampen_finiteCoproducts_Fin [FinitaryExtensive C] {n : ℕ}
    {F : Discrete (Fin n) ⥤ C} {c : Cocone F} (hc : IsColimit c) : IsVanKampenColimit c := by
  let f : Fin n → C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor f :=
    Functor.hext (fun _ ↦ rfl) (by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; simp [f])
  clear_value f
  subst this
  induction' n with n IH
  · exact isVanKampenColimit_of_isEmpty _ hc
  · apply IsVanKampenColimit.of_iso _
      ((extendCofanIsColimit f (coproductIsCoproduct _) (coprodIsCoprod _ _)).uniqueUpToIso hc)
    apply @isVanKampenColimit_extendCofan _ _ _ _ _ _ _ _ ?_
    · apply IH
      exact coproductIsCoproduct _
    · apply FinitaryExtensive.van_kampen'
      exact coprodIsCoprod _ _
    · dsimp
      infer_instance

theorem FinitaryExtensive.isVanKampen_finiteCoproducts [FinitaryExtensive C] {ι : Type*}
    [Finite ι] {F : Discrete ι ⥤ C} {c : Cocone F} (hc : IsColimit c) : IsVanKampenColimit c := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  apply (IsVanKampenColimit.whiskerEquivalence_iff (Discrete.equivalence e).symm).mp
  apply FinitaryExtensive.isVanKampen_finiteCoproducts_Fin
  exact (IsColimit.whiskerEquivalenceEquiv (Discrete.equivalence e).symm) hc

lemma FinitaryPreExtensive.hasPullbacks_of_is_coproduct [FinitaryPreExtensive C] {ι : Type*}
    [Finite ι] {F : Discrete ι ⥤ C} {c : Cocone F} (hc : IsColimit c) (i : Discrete ι) {X : C}
    (g : X ⟶ _) : HasPullback g (c.ι.app i) := by
  classical
  let f : ι → C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor f :=
    Functor.hext (fun i ↦ rfl) (by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; simp [f])
  clear_value f
  subst this
  change Cofan f at c
  obtain ⟨i⟩ := i
  let e : ∐ f ≅ f i ⨿ (∐ fun j : ({i}ᶜ : Set ι) ↦ f j) :=
  { hom := Sigma.desc (fun j ↦ if h : j = i then eqToHom (congr_arg f h) ≫ coprod.inl else
      Sigma.ι (fun j : ({i}ᶜ : Set ι) ↦ f j) ⟨j, h⟩ ≫ coprod.inr)
    inv := coprod.desc (Sigma.ι f i) (Sigma.desc fun j ↦ Sigma.ι f j)
    hom_inv_id := by aesop_cat
    inv_hom_id := by
      ext j
      · simp
      · simp only [coprod.desc_comp, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app,
          eqToHom_refl, Category.id_comp, dite_true, BinaryCofan.mk_pt, BinaryCofan.ι_app_right,
          BinaryCofan.mk_inr, colimit.ι_desc_assoc, Discrete.functor_obj, Category.comp_id]
        exact dif_neg j.prop }
  let e' : c.pt ≅ f i ⨿ (∐ fun j : ({i}ᶜ : Set ι) ↦ f j) :=
    hc.coconePointUniqueUpToIso (getColimitCocone _).2 ≪≫ e
  have : coprod.inl ≫ e'.inv = c.ι.app ⟨i⟩ := by
    simp only [e', Iso.trans_inv, coprod.desc_comp, colimit.ι_desc, BinaryCofan.mk_pt,
      BinaryCofan.ι_app_left, BinaryCofan.mk_inl]
    exact colimit.comp_coconePointUniqueUpToIso_inv _ _
  clear_value e'
  rw [← this]
  have : IsPullback (𝟙 _) (g ≫ e'.hom) g e'.inv := IsPullback.of_horiz_isIso ⟨by simp⟩
  exact ⟨⟨⟨_, ((IsPullback.of_hasPullback (g ≫ e'.hom) coprod.inl).paste_horiz this).isLimit⟩⟩⟩

lemma FinitaryExtensive.mono_ι [FinitaryExtensive C] {ι : Type*} [Finite ι] {F : Discrete ι ⥤ C}
    {c : Cocone F} (hc : IsColimit c) (i : Discrete ι) :
    Mono (c.ι.app i) :=
  mono_of_cofan_isVanKampen (isVanKampen_finiteCoproducts hc) _

instance [FinitaryExtensive C] {ι : Type*} [Finite ι] (X : ι → C) (i : ι) :
    Mono (Sigma.ι X i) :=
  FinitaryExtensive.mono_ι (coproductIsCoproduct _) ⟨i⟩

lemma FinitaryExtensive.isPullback_initial_to [FinitaryExtensive C]
    {ι : Type*} [Finite ι] {F : Discrete ι ⥤ C}
    {c : Cocone F} (hc : IsColimit c) (i j : Discrete ι) (e : i ≠ j) :
    IsPullback (initial.to _) (initial.to _) (c.ι.app i) (c.ι.app j) :=
  isPullback_initial_to_of_cofan_isVanKampen (isVanKampen_finiteCoproducts hc) i j e

lemma FinitaryExtensive.isPullback_initial_to_sigma_ι [FinitaryExtensive C] {ι : Type*} [Finite ι]
    (X : ι → C) (i j : ι) (e : i ≠ j) :
    IsPullback (initial.to _) (initial.to _) (Sigma.ι X i) (Sigma.ι X j) :=
  FinitaryExtensive.isPullback_initial_to (coproductIsCoproduct _) ⟨i⟩ ⟨j⟩
    (ne_of_apply_ne Discrete.as e)

instance FinitaryPreExtensive.hasPullbacks_of_inclusions [FinitaryPreExtensive C] {X Z : C}
    {α : Type*} (f : X ⟶ Z) {Y : (a : α) → C} (i : (a : α) → Y a ⟶ Z) [Finite α]
    [hi : IsIso (Sigma.desc i)] (a : α) : HasPullback f (i a) := by
  apply FinitaryPreExtensive.hasPullbacks_of_is_coproduct (c := Cofan.mk Z i)
  exact @IsColimit.ofPointIso (t := Cofan.mk Z i) (P := _) hi

lemma FinitaryPreExtensive.sigma_desc_iso [FinitaryPreExtensive C] {α : Type} [Finite α] {X : C}
    {Z : α → C} (π : (a : α) → Z a ⟶ X) {Y : C} (f : Y ⟶ X) (hπ : IsIso (Sigma.desc π)) :
    IsIso (Sigma.desc ((fun _ ↦ pullback.fst) : (a : α) → pullback f (π a) ⟶ _)) := by
  suffices IsColimit (Cofan.mk _ ((fun _ ↦ pullback.fst) : (a : α) → pullback f (π a) ⟶ _)) by
    change IsIso (this.coconePointUniqueUpToIso (getColimitCocone _).2).inv
    infer_instance
  let this : IsColimit (Cofan.mk X π) := by
    refine @IsColimit.ofPointIso (t := Cofan.mk X π) (P := coproductIsCoproduct Z) ?_
    convert hπ
    simp [coproductIsCoproduct]
  refine (FinitaryPreExtensive.isUniversal_finiteCoproducts this
    (Cofan.mk _ ((fun _ ↦ pullback.fst) : (a : α) → pullback f (π a) ⟶ _))
    (Discrete.natTrans fun i ↦ pullback.snd) f ?_
    (NatTrans.equifibered_of_discrete _) ?_).some
  · ext
    simp [pullback.condition]
  · exact fun j ↦ IsPullback.of_hasPullback f (π j.as)

end FiniteCoproducts

end Extensive

end CategoryTheory
