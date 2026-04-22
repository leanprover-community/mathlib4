/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.VanKampen
public import Mathlib.CategoryTheory.Limits.MonoCoprod
public import Mathlib.CategoryTheory.Limits.Shapes.DisjointCoproduct

/-!

# Extensive categories

## Main definitions
- `CategoryTheory.FinitaryExtensive`: A category is (finitary) extensive if it has finite
  coproducts, and binary coproducts are van Kampen.

## Main Results
- `CategoryTheory.hasStrictInitialObjects_of_finitaryPreExtensive`: The initial object
  in finitary pre-extensive categories is strict.
- `CategoryTheory.FinitaryExtensive.mono_inr_of_isColimit`: Coproduct injections are monic in
  extensive categories.
- `CategoryTheory.BinaryCofan.isPullback_initial_to_of_isVanKampen`: In extensive categories,
  sums are disjoint, i.e. the pullback of `X ⟶ X ⨿ Y` and `Y ⟶ X ⨿ Y` is the initial object.
- `CategoryTheory.types.finitaryExtensive`: The category of types is extensive.
- `CategoryTheory.finitaryExtensive_TopCat`:
  The category `Top` is extensive.
- `CategoryTheory.finitaryExtensive_functor`: The category `D ⥤ C` is extensive if `C`
  has all pullbacks and is extensive.
- `CategoryTheory.FinitaryExtensive.isVanKampen_finiteCoproducts`: Finite coproducts in a
  finitary extensive category are van Kampen.

## References
- https://ncatlab.org/nlab/show/extensive+category
- [Carboni et al, Introduction to extensive and distributive categories][CARBONI1993145]

-/

@[expose] public section

open CategoryTheory.Limits Topology

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
class PreservesPullbacksOfInclusions {C : Type*} [Category* C] {D : Type*} [Category* D]
    (F : C ⥤ D) [HasBinaryCoproducts C] where
  [preservesPullbackInl : ∀ {X Y Z : C} (f : Z ⟶ X ⨿ Y), PreservesLimit (cospan coprod.inl f) F]

attribute [instance] PreservesPullbacksOfInclusions.preservesPullbackInl

/-- A category is (finitary) pre-extensive if it has finite coproducts,
and binary coproducts are universal. -/
class FinitaryPreExtensive (C : Type u) [Category.{v} C] : Prop where
  [hasFiniteCoproducts : HasFiniteCoproducts C]
  [hasPullbacksOfInclusions : HasPullbacksOfInclusions C]
  /-- In a finitary pre-extensive category, all binary coproducts are universal. -/
  universal' : ∀ {X Y : C} (c : BinaryCofan X Y), IsColimit c → IsUniversalColimit c

attribute [instance] FinitaryPreExtensive.hasFiniteCoproducts
attribute [instance] FinitaryPreExtensive.hasPullbacksOfInclusions

/-- A category is (finitary) extensive if it has finite coproducts,
and binary coproducts are van Kampen. -/
class FinitaryExtensive (C : Type u) [Category.{v} C] : Prop where
  [hasFiniteCoproducts : HasFiniteCoproducts C]
  [hasPullbacksOfInclusions : HasPullbacksOfInclusions C]
  /-- In a finitary extensive category, all binary coproducts are van Kampen. -/
  van_kampen' : ∀ {X Y : C} (c : BinaryCofan X Y), IsColimit c → IsVanKampenColimit c

attribute [instance] FinitaryExtensive.hasFiniteCoproducts
attribute [instance] FinitaryExtensive.hasPullbacksOfInclusions

theorem FinitaryExtensive.vanKampen [FinitaryExtensive C] {F : Discrete WalkingPair ⥤ C}
    (c : Cocone F) (hc : IsColimit c) : IsVanKampenColimit c := by
  let X := F.obj ⟨WalkingPair.left⟩
  let Y := F.obj ⟨WalkingPair.right⟩
  have : F = pair X Y := by
    apply Functor.hext
    · rintro ⟨⟨⟩⟩ <;> rfl
    · rintro ⟨⟨⟩⟩ ⟨j⟩ ⟨⟨rfl : _ = j⟩⟩ <;> simp [X, Y]
  clear_value X Y
  subst this
  exact FinitaryExtensive.van_kampen' c hc

namespace HasPullbacksOfInclusions

instance (priority := 100) [HasBinaryCoproducts C] [HasPullbacks C] :
    HasPullbacksOfInclusions C := ⟨⟩

variable [HasBinaryCoproducts C] [HasPullbacksOfInclusions C] {X Y Z : C} (f : Z ⟶ X ⨿ Y)

instance preservesPullbackInl' :
    HasPullback f coprod.inl :=
  hasPullback_symmetry _ _

set_option backward.isDefEq.respectTransparency false in
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

variable {D : Type*} [Category* D] [HasBinaryCoproducts C] (F : C ⥤ D)

noncomputable
instance (priority := 100) [PreservesLimitsOfShape WalkingCospan F] :
    PreservesPullbacksOfInclusions F := ⟨⟩

variable [PreservesPullbacksOfInclusions F] {X Y Z : C} (f : Z ⟶ X ⨿ Y)

noncomputable
instance preservesPullbackInl' :
    PreservesLimit (cospan f coprod.inl) F :=
  preservesPullback_symmetry _ _ _

set_option backward.isDefEq.respectTransparency false in
noncomputable
instance preservesPullbackInr' :
    PreservesLimit (cospan f coprod.inr) F := by
  apply preservesLimit_of_iso_diagram (K₁ := cospan (f ≫ (coprod.braiding X Y).hom) coprod.inl)
  apply cospanExt (Iso.refl _) (Iso.refl _) (coprod.braiding X Y).symm <;> simp

noncomputable
instance preservesPullbackInr :
    PreservesLimit (cospan coprod.inr f) F :=
  preservesPullback_symmetry _ _ _

end PreservesPullbacksOfInclusions

instance (priority := 100) FinitaryExtensive.toFinitaryPreExtensive [FinitaryExtensive C] :
    FinitaryPreExtensive C :=
  ⟨fun c hc ↦ (FinitaryExtensive.van_kampen' c hc).isUniversal⟩

theorem FinitaryExtensive.mono_inr_of_isColimit [FinitaryExtensive C] {c : BinaryCofan X Y}
    (hc : IsColimit c) : Mono c.inr :=
  BinaryCofan.mono_inr_of_isVanKampen (FinitaryExtensive.vanKampen c hc)

theorem FinitaryExtensive.mono_inl_of_isColimit [FinitaryExtensive C] {c : BinaryCofan X Y}
    (hc : IsColimit c) : Mono c.inl :=
  FinitaryExtensive.mono_inr_of_isColimit (BinaryCofan.isColimitFlip hc)

instance (priority := low) [FinitaryExtensive C] : MonoCoprod C where
  binaryCofan_inl _ _ _ hc := BinaryCofan.mono_inr_of_isVanKampen
    (FinitaryExtensive.vanKampen _ (BinaryCofan.isColimitFlip hc))

theorem FinitaryExtensive.isPullback_initial_to_binaryCofan [FinitaryExtensive C]
    {c : BinaryCofan X Y} (hc : IsColimit c) :
    IsPullback (initial.to _) (initial.to _) c.inl c.inr :=
  BinaryCofan.isPullback_initial_to_of_isVanKampen (FinitaryExtensive.vanKampen c hc)

instance (priority := 100) hasStrictInitialObjects_of_finitaryPreExtensive
    [FinitaryPreExtensive C] : HasStrictInitialObjects C :=
  hasStrictInitial_of_isUniversal (FinitaryPreExtensive.universal' _
    ((BinaryCofan.isColimit_iff_isIso_inr initialIsInitial _).mpr (by
      dsimp
      infer_instance)).some)

set_option backward.isDefEq.respectTransparency false in
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

instance types.finitaryExtensive : FinitaryExtensive (Type u) := by
  classical
  rw [finitaryExtensive_iff_of_isTerminal (Type u) PUnit Types.isTerminalPUnit _
      (Types.binaryCoproductColimit _ _)]
  apply BinaryCofan.isVanKampen_mk _ _ (fun X Y => Types.binaryCoproductColimit X Y) _
      fun f g => (Limits.Types.pullbackLimitCone f g).2
  · intro _ _ _ _ f hαX hαY
    constructor
    · refine ⟨⟨hαX.symm⟩, ⟨PullbackCone.isLimitAux' _ ?_⟩⟩
      intro s
      have : ∀ x, ∃! y, s.fst x = Sum.inl y := by
        intro x
        rcases h : s.fst x with val | val
        · simp only [Types.binaryCoproductCocone_pt, Functor.const_obj_obj, Sum.inl.injEq,
            existsUnique_eq']
        · apply_fun f at h
          cases ((congr_fun s.condition x).symm.trans h).trans (congr_fun hαY val :).symm
      delta ExistsUnique at this
      choose l hl hl' using this
      exact ⟨l, (funext hl).symm, Types.isTerminalPUnit.hom_ext _ _,
        fun {l'} h₁ _ => funext fun x => hl' x (l' x) (congr_fun h₁ x).symm⟩
    · refine ⟨⟨hαY.symm⟩, ⟨PullbackCone.isLimitAux' _ ?_⟩⟩
      intro s
      have : ∀ x, ∃! y, s.fst x = Sum.inr y := by
        intro x
        rcases h : s.fst x with val | val
        · apply_fun f at h
          cases ((congr_fun s.condition x).symm.trans h).trans (congr_fun hαX val :).symm
        · simp only [Types.binaryCoproductCocone_pt, Functor.const_obj_obj, Sum.inr.injEq,
            existsUnique_eq']
      delta ExistsUnique at this
      choose l hl hl' using this
      exact ⟨l, (funext hl).symm, Types.isTerminalPUnit.hom_ext _ _,
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

section TopCat

/-- (Implementation) An auxiliary lemma for the proof that `TopCat` is finitary extensive. -/
noncomputable def finitaryExtensiveTopCatAux (Z : TopCat.{u})
    (f : Z ⟶ TopCat.of (PUnit.{u + 1} ⊕ PUnit.{u + 1})) :
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
  · refine ⟨(Homeomorph.prodPUnit Z).isEmbedding.comp .subtypeVal, ?_⟩
    convert f.hom.2.1 _ isOpen_range_inl
  · refine ⟨(Homeomorph.prodPUnit Z).isEmbedding.comp .subtypeVal, ?_⟩
    convert f.hom.2.1 _ isOpen_range_inr
  · convert Set.isCompl_range_inl_range_inr.preimage f

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
        rcases h : s.fst x with val | val
        · exact ⟨val, rfl, fun y h => Sum.inl_injective h.symm⟩
        · apply_fun f at h
          cases ((ConcreteCategory.congr_hom s.condition x).symm.trans h).trans
            (ConcreteCategory.congr_hom hαY val :).symm
      delta ExistsUnique at this
      choose l hl hl' using this
      refine ⟨TopCat.ofHom ⟨l, ?_⟩, TopCat.ext fun a => (hl a).symm,
        TopCat.isTerminalPUnit.hom_ext _ _,
        fun {l'} h₁ _ => TopCat.ext fun x =>
          hl' x (l' x) (ConcreteCategory.congr_hom h₁ x).symm⟩
      apply (IsEmbedding.inl (X := X') (Y := Y')).isInducing.continuous_iff.mpr
      convert s.fst.hom.2 using 1
      exact (funext hl).symm
    · refine ⟨⟨hαY.symm⟩, ⟨PullbackCone.isLimitAux' _ ?_⟩⟩
      intro s
      have : ∀ x, ∃! y, s.fst x = Sum.inr y := by
        intro x
        rcases h : s.fst x with val | val
        · apply_fun f at h
          cases ((ConcreteCategory.congr_hom s.condition x).symm.trans h).trans
            (ConcreteCategory.congr_hom hαX val :).symm
        · exact ⟨val, rfl, fun y h => Sum.inr_injective h.symm⟩
      delta ExistsUnique at this
      choose l hl hl' using this
      refine ⟨TopCat.ofHom ⟨l, ?_⟩, TopCat.ext fun a => (hl a).symm,
        TopCat.isTerminalPUnit.hom_ext _ _,
        fun {l'} h₁ _ =>
          TopCat.ext fun x => hl' x (l' x) (ConcreteCategory.congr_hom h₁ x).symm⟩
      apply (IsEmbedding.inr (X := X') (Y := Y')).isInducing.continuous_iff.mpr
      convert s.fst.hom.2 using 1
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
  have : PreservesColimitsOfSize Gl := adj.leftAdjoint_preservesColimits
  constructor
  intro X Y c hc
  apply (IsVanKampenColimit.precompose_isIso_iff
    (Functor.isoWhiskerLeft _ (asIso adj.counit) ≪≫ Functor.rightUnitor _).hom).mp
  have : ∀ (Z : C) (i : Discrete WalkingPair) (f : Z ⟶ (colimit.cocone (pair X Y ⋙ Gr)).pt),
        PreservesLimit (cospan f ((colimit.cocone (pair X Y ⋙ Gr)).ι.app i)) Gl := by
    have : pair X Y ⋙ Gr = pair (Gr.obj X) (Gr.obj Y) := by
      apply Functor.hext
      · rintro ⟨⟨⟩⟩ <;> rfl
      · rintro ⟨⟨⟩⟩ ⟨j⟩ ⟨⟨rfl : _ = j⟩⟩ <;> simp
    rw [this]
    rintro Z ⟨_ | _⟩ f <;> dsimp <;> infer_instance
  refine ((FinitaryExtensive.vanKampen _ (colimit.isColimit <| pair X Y ⋙ _)).map_reflective
    adj).of_iso (IsColimit.uniqueUpToIso ?_ ?_)
  · exact isColimitOfPreserves Gl (colimit.isColimit _)
  · exact (IsColimit.precomposeHomEquiv _ _).symm hc

instance finitaryExtensive_functor [HasPullbacks C] [FinitaryExtensive C] :
    FinitaryExtensive (D ⥤ C) :=
  haveI : HasFiniteCoproducts (D ⥤ C) := ⟨fun _ => Limits.functorCategoryHasColimitsOfShape⟩
  ⟨fun c hc => isVanKampenColimit_of_evaluation _ c fun _ =>
    FinitaryExtensive.vanKampen _ <| isColimitOfPreserves _ hc⟩

instance {C} [Category* C] {D} [Category* D] (F : C ⥤ D)
    {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [IsIso f] : PreservesLimit (cospan f g) F :=
  have := hasPullback_of_left_iso f g
  preservesLimit_of_preserves_limit_cone (IsPullback.of_hasPullback f g).isLimit
    ((isLimitMapConePullbackConeEquiv _ pullback.condition).symm
      (IsPullback.of_vert_isIso ⟨by simp only [← F.map_comp, pullback.condition]⟩).isLimit)

instance {C} [Category* C] {D} [Category* D] (F : C ⥤ D)
    {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [IsIso g] : PreservesLimit (cospan f g) F :=
  preservesPullback_symmetry _ _ _

set_option backward.isDefEq.respectTransparency false in
theorem finitaryExtensive_of_preserves_and_reflects (F : C ⥤ D) [FinitaryExtensive D]
    [HasFiniteCoproducts C] [HasPullbacksOfInclusions C]
    [PreservesPullbacksOfInclusions F]
    [ReflectsLimitsOfShape WalkingCospan F] [PreservesColimitsOfShape (Discrete WalkingPair) F]
    [ReflectsColimitsOfShape (Discrete WalkingPair) F] : FinitaryExtensive C := by
  constructor
  intro X Y c hc
  refine IsVanKampenColimit.of_iso ?_ (hc.uniqueUpToIso (coprodIsCoprod X Y)).symm
  have (i : Discrete WalkingPair) (Z : C) (f : Z ⟶ X ⨿ Y) :
    PreservesLimit (cospan f ((BinaryCofan.mk coprod.inl coprod.inr).ι.app i)) F := by
    rcases i with ⟨_ | _⟩ <;> dsimp <;> infer_instance
  refine (FinitaryExtensive.vanKampen _
    (isColimitOfPreserves F (coprodIsCoprod X Y))).of_mapCocone F

theorem finitaryExtensive_of_preserves_and_reflects_isomorphism (F : C ⥤ D) [FinitaryExtensive D]
    [HasFiniteCoproducts C] [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F]
    [PreservesColimitsOfShape (Discrete WalkingPair) F] [F.ReflectsIsomorphisms] :
    FinitaryExtensive C := by
  haveI : ReflectsLimitsOfShape WalkingCospan F := reflectsLimitsOfShape_of_reflectsIsomorphisms
  haveI : ReflectsColimitsOfShape (Discrete WalkingPair) F :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact finitaryExtensive_of_preserves_and_reflects F

end Functor

section FiniteCoproducts

theorem FinitaryPreExtensive.isUniversal_finiteCoproducts_Fin [FinitaryPreExtensive C] {n : ℕ}
    {F : Discrete (Fin n) ⥤ C} {c : Cocone F} (hc : IsColimit c) : IsUniversalColimit c := by
  let f : Fin n → C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor f :=
    Functor.hext (fun _ ↦ rfl) (by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; simp [f])
  clear_value f
  subst this
  induction n with
  | zero => exact (isVanKampenColimit_of_isEmpty _ hc).isUniversal
  | succ n IH =>
    refine IsUniversalColimit.of_iso (@isUniversalColimit_extendCofan _ _ _ _ _ _
      (IH _ (coproductIsCoproduct _)) (FinitaryPreExtensive.universal' _ (coprodIsCoprod _ _)) ?_)
      ((extendCofanIsColimit f (coproductIsCoproduct _) (coprodIsCoprod _ _)).uniqueUpToIso hc)
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
  induction n with
  | zero => exact isVanKampenColimit_of_isEmpty _ hc
  | succ n IH =>
    apply IsVanKampenColimit.of_iso _
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

set_option backward.isDefEq.respectTransparency false in
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
    hom_inv_id := by cat_disch
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
    simp only [e, e', Iso.trans_inv, coprod.desc_comp, colimit.ι_desc, BinaryCofan.mk_pt,
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

-- TODO: generalize to arbitrary `ι` if `HasCoproductsOfShape ι C`.
instance (priority := low) [FinitaryExtensive C] {ι : Type*} [Finite ι] :
    CoproductsOfShapeDisjoint C ι where
  coproductDisjoint X := by
    refine ⟨fun {c} hc i j e s hs ↦ ?_, fun hc i ↦ FinitaryExtensive.mono_ι hc ⟨i⟩⟩
    exact ⟨initialIsInitial.ofIso ((FinitaryExtensive.isPullback_initial_to hc ⟨i⟩ ⟨j⟩
      (by simpa)).isoIsPullback _ _ (IsPullback.of_isLimit hs))⟩

instance FinitaryPreExtensive.hasPullbacks_of_inclusions [FinitaryPreExtensive C] {X Z : C}
    {α : Type*} (f : X ⟶ Z) {Y : (a : α) → C} (i : (a : α) → Y a ⟶ Z) [Finite α]
    [hi : IsIso (Sigma.desc i)] (a : α) : HasPullback f (i a) := by
  apply FinitaryPreExtensive.hasPullbacks_of_is_coproduct (c := Cofan.mk Z i)
  exact @IsColimit.ofPointIso (t := Cofan.mk Z i) (P := _) (i := hi)

lemma FinitaryPreExtensive.isIso_sigmaDesc_fst [FinitaryPreExtensive C] {α : Type} [Finite α]
    {X : C} {Z : α → C} (π : (a : α) → Z a ⟶ X) {Y : C} (f : Y ⟶ X) (hπ : IsIso (Sigma.desc π)) :
    IsIso (Sigma.desc ((fun _ ↦ pullback.fst _ _) : (a : α) → pullback f (π a) ⟶ _)) := by
  let c := (Cofan.mk _ ((fun _ ↦ pullback.fst _ _) : (a : α) → pullback f (π a) ⟶ _))
  apply c.nonempty_isColimit_iff_isIso_sigmaDesc.mp
  have hau : IsUniversalColimit (Cofan.mk X π) := FinitaryPreExtensive.isUniversal_finiteCoproducts
    ((Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mpr hπ).some
  refine hau.nonempty_isColimit_of_pullbackCone_left _ (𝟙 _) _ _ (fun i ↦ ?_)
    (PullbackCone.mk (𝟙 _) f (by simp)) (IsPullback.id_horiz f).isLimit _ (Iso.refl _)
    (by simp) (by simp [c]) (by simp [pullback.condition, c])
  exact pullback.isLimit _ _

set_option backward.isDefEq.respectTransparency false in
/-- If `C` has pullbacks and is finitary (pre-)extensive, pullbacks distribute over finite
coproducts, i.e., `∐ (Xᵢ ×[S] Yⱼ) ≅ (∐ Xᵢ) ×[S] (∐ Yⱼ)`.
For an `IsPullback` version, see `FinitaryPreExtensive.isPullback_sigmaDesc`. -/
instance FinitaryPreExtensive.isIso_sigmaDesc_map [HasPullbacks C] [FinitaryPreExtensive C]
    {ι ι' : Type*} [Finite ι] [Finite ι'] {S : C} {X : ι → C} {Y : ι' → C}
    (f : ∀ i, X i ⟶ S) (g : ∀ i, Y i ⟶ S) :
    IsIso (Sigma.desc fun (p : ι × ι') ↦
      pullback.map (f p.1) (g p.2) (Sigma.desc f) (Sigma.desc g) (Sigma.ι _ p.1)
        (Sigma.ι _ p.2) (𝟙 S) (by simp) (by simp)) := by
  let c : Cofan _ := Cofan.mk _ <| fun (p : ι × ι') ↦
      pullback.map (f p.1) (g p.2) (Sigma.desc f) (Sigma.desc g) (Sigma.ι _ p.1)
        (Sigma.ι _ p.2) (𝟙 S) (by simp) (by simp)
  apply c.nonempty_isColimit_iff_isIso_sigmaDesc.mp
  refine IsUniversalColimit.nonempty_isColimit_prod_of_pullbackCone
      (a := Cofan.mk _ <| fun i ↦ Sigma.ι _ i) (b := Cofan.mk _ <| fun i ↦ Sigma.ι _ i)
      ?_ ?_ f g (Sigma.desc f) (Sigma.desc g) (fun i j ↦ (pullback.cone (f i) (g j)))
      (fun i j ↦ pullback.isLimit (f i) (g j)) (pullback.cone _ _) ?_ (Iso.refl _)
  · exact FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct X)
  · exact FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct Y)
  · exact pullback.isLimit (Sigma.desc f) (Sigma.desc g)

set_option backward.isDefEq.respectTransparency false in
/-- If `C` has pullbacks and is finitary (pre-)extensive, pullbacks distribute over finite
coproducts, i.e., `∐ (Xᵢ ×[S] Yⱼ) ≅ (∐ Xᵢ) ×[S] (∐ Yⱼ)`.
For a variant, see `FinitaryPreExtensive.isIso_sigmaDesc_map`. -/
lemma FinitaryPreExtensive.isPullback_sigmaDesc [HasPullbacks C] [FinitaryPreExtensive C]
    {ι ι' : Type*} [Finite ι] [Finite ι'] {S : C} {X : ι → C} {Y : ι' → C}
    (f : ∀ i, X i ⟶ S) (g : ∀ i, Y i ⟶ S) :
    IsPullback
      (Limits.Sigma.desc fun (p : ι × ι') ↦ pullback.fst (f p.1) (g p.2) ≫ Sigma.ι X p.1)
      (Limits.Sigma.desc fun (p : ι × ι') ↦ pullback.snd (f p.1) (g p.2) ≫ Sigma.ι Y p.2)
      (Limits.Sigma.desc f) (Limits.Sigma.desc g) := by
  convert IsUniversalColimit.isPullback_prod_of_isColimit
      (d := Cofan.mk _ (Sigma.ι fun (p : ι × ι') ↦ pullback (f p.1) (g p.2)))
      (hd := coproductIsCoproduct (fun (p : ι × ι') ↦ pullback (f p.1) (g p.2)))
      (a := Cofan.mk _ <| fun i ↦ Sigma.ι _ i) (b := Cofan.mk _ <| fun i ↦ Sigma.ι _ i)
      ?_ ?_ f g (Sigma.desc f) (Sigma.desc g) (fun i j ↦ IsPullback.of_hasPullback (f i) (g j))
  · ext
    simp [Cofan.IsColimit.desc, Sigma.ι, coproductIsCoproduct]
  · ext
    simp [Cofan.IsColimit.desc, Sigma.ι, coproductIsCoproduct]
  · exact FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct X)
  · exact FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct Y)

end FiniteCoproducts

end Extensive

end CategoryTheory
