/-
Copyright (c) 2024 Dhyan Aranha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhyan Aranha
-/
import Mathlib

/-!
# The Affine Line with Doubled Origin

This file constructs the affine line with a doubled origin as a scheme.
It is defined as the pushout of two copies of the affine line 𝔸¹ glued along the
open subset 𝔸¹ - 0. We show that over Spec(ℤ) it is not separated.

## Main Definitions and Results

* `affineLine`: The affine line 𝔸¹ over ℤ.
* `affineLineWithDoubledOrigin`: The scheme constructed by gluing two copies of `affineLine`.
* `isPullback_of_isPushout_of_isOpenImmersion` : A pushout of open immersion of schemes is
   also a pullback.
* `not_isSeparated`: A proof that the affine line with doubled origin is not a separated scheme.

## Implementation Notes

We construct the scheme using `CategoryTheory.Limits.pushout` in the category of `Scheme`.
We then prove properties of this scheme by analyzing the induced maps on the underlying
topological spaces.

-/

noncomputable section

open Polynomial AlgebraicGeometry CategoryTheory CategoryTheory.Limits Scheme TopCat Topology
open LocallyRingedSpace.IsOpenImmersion


section TopCatLemmas

/-!
### Topological Lemmas

These lemmas relate pushouts in `Scheme` to pushouts in `TopCat` via the forgetful functor.
-/

/-- The forgetful functor to `TopCat` preserves pushouts. -/
lemma pushouts_forget {Z X Y P : TopCat} (f : Z ⟶ X) (g : Z ⟶ Y) (inl : X ⟶ P) (inr : Y ⟶ P)
    (h : IsPushout f g inl inr) :
    IsPushout ((forget TopCat).map f) ((forget TopCat).map g)
              ((forget TopCat).map inl) ((forget TopCat).map inr) :=
  h.map (forget TopCat)

/-- An open embedding in `TopCat` is a monomorphism. -/
lemma openEmbedding_isMono {X Y : TopCat} (f : X ⟶ Y) (hf : IsOpenEmbedding f) : Mono f :=
  (TopCat.mono_iff_injective f).mpr hf.injective

/--
In `TopCat`, the intersection of the ranges of the pushout inclusions equals the range of
the composition with the base map.
-/
lemma range_inter_top {Z X Y P : TopCat} (f : Z ⟶ X) (g : Z ⟶ Y) (inl : X ⟶ P) (inr : Y ⟶ P)
    (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g) (h : IsPushout f g inl inr) :
    Set.range inl ∩ Set.range inr = Set.range (f ≫ inl) := by
  have forget_comm_sq := (pushouts_forget f g inl inr h).toCommSq.w
  let P_cocone_in_set := PushoutCocone.mk ((forget TopCat).map inl) ((forget TopCat).map inr)
     forget_comm_sq
  have P_iscolim_in_set : IsColimit P_cocone_in_set :=
    (pushouts_forget f g inl inr h).isColimit
  have f_ismono := (openEmbedding_isMono f) hf
  have g_ismono := (openEmbedding_isMono g) hg
  have range_inter_forward : Set.range inl ∩ Set.range inr ⊆ Set.range (f ≫ inl) := by
    intro p hp
    have hinltype : ∃ x : (forget TopCat).obj X, (forget TopCat).map inl x = p := by
      exact hp.1
    have hinrtype : ∃ y : (forget TopCat).obj Y, (forget TopCat).map inr y = p := by
      exact hp.2
    rcases hinltype with ⟨xtype, _⟩
    rcases hinrtype with ⟨ytype, _⟩
    have h_inl_eq_inr_iff := Types.Pushout.inl_eq_inr_iff ((forget TopCat).map f)
          ((forget TopCat).map g) xtype ytype
    let types_pushout := Types.Pushout.isColimitCocone
                ((forget TopCat).map f) ((forget TopCat).map g)
    let iso := IsColimit.coconePointUniqueUpToIso types_pushout P_iscolim_in_set
    have h_comm : Types.Pushout.inl ((forget TopCat).map f) ((forget TopCat).map g) xtype =
              Types.Pushout.inr ((forget TopCat).map f) ((forget TopCat).map g) ytype := by
      have hcomp1 : (iso.hom) ((Types.Pushout.inl ((forget TopCat).map f) ((forget TopCat).map g))
        (xtype)) = ((forget TopCat).map inl) (xtype) := rfl
      have hcomp2 : (iso.hom) ((Types.Pushout.inr ((forget TopCat).map f) ((forget TopCat).map g))
         (ytype)) = ((forget TopCat).map inr) (ytype) := rfl
      have almost : (iso.hom) ((Types.Pushout.inl ((forget TopCat).map f) ((forget TopCat).map g))
        (xtype)) = (iso.hom) ((Types.Pushout.inr ((forget TopCat).map f) ((forget TopCat).map g))
        (ytype)) := by
        rw [hcomp1, hcomp2]
        simp_all only [ConcreteCategory.forget_map_eq_coe]
      exact (Iso.toEquiv iso).injective almost
    cat_disch
  have range_inter_reverse : Set.range (f ≫ inl) ⊆ Set.range inl ∩ Set.range inr := by
    intro p hp
    constructor
    · simp_all only [TopCat.hom_comp, ContinuousMap.coe_comp, Set.mem_range, Function.comp_apply]
      obtain ⟨z, _⟩ := hp
      use (Hom.hom f) z
    · simp_all only [TopCat.hom_comp, ContinuousMap.coe_comp, Set.mem_range, Function.comp_apply]
      obtain ⟨z, _⟩ := hp
      use (Hom.hom g) z
      have h_apply : (f ≫ inl) z = (g ≫ inr) z := by rw [h.toCommSq.w]
      simp_all only [TopCat.comp_app]
  exact Eq.symm (Set.Subset.antisymm range_inter_reverse range_inter_forward)

instance {X Y Z : Scheme} (f : Z ⟶ X) (g : Z ⟶ Y) [IsOpenImmersion f] [IsOpenImmersion g] :
    PreservesColimit (span f g) (Scheme.forgetToTop) := by
  change PreservesColimit _ (Scheme.forgetToLocallyRingedSpace ⋙
    LocallyRingedSpace.forgetToSheafedSpace ⋙ _)
  infer_instance

/-- The forgetful functor from Schemes to TopCat preserves pushouts of open immersions. -/
lemma pushout_in_TopCat {X Y Z T : Scheme} (f : Z ⟶ X) (g : Z ⟶ Y)
    [IsOpenImmersion f] [IsOpenImmersion g] (inl : X ⟶ T) (inr : Y ⟶ T)
    (h : IsPushout f g inl inr) :
    IsPushout (forgetToTop.map f) (forgetToTop.map g) (forgetToTop.map inl)
    (forgetToTop.map inr) :=
  h.map Scheme.forgetToTop

end TopCatLemmas


/-- Pushout of open immersions are open immersions -/
lemma inl_inr_isOpenImmersion {U X Y T : Scheme} (f : U ⟶ X) (g : U ⟶ Y)
    (inl : X ⟶ T) (inr : Y ⟶ T) (h : IsPushout f g inl inr)
    [IsOpenImmersion f] [IsOpenImmersion g] : IsOpenImmersion inl ∧ IsOpenImmersion inr := by
  let iso := h.isoPushout
  have inlpush : inl = pushout.inl _ _ ≫ iso.inv := h.inl_isoPushout_inv.symm
  have inrpush : inr = pushout.inr _ _ ≫ iso.inv := h.inr_isoPushout_inv.symm
  rw [inlpush, inrpush]
  constructor
  all_goals infer_instance


/--
The pushout square of open immersions is also a pullback square.
-/
lemma isPullback_of_isPushout_of_isOpenImmersion {U X Y T : Scheme} (f : U ⟶ X) (g : U ⟶ Y)
    (inl : X ⟶ T) (inr : Y ⟶ T) (h : IsPushout f g inl inr)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    IsPullback f g inl inr := by
  constructor
  · have f_embedd_TopCat : IsOpenEmbedding (forgetToTop.map f) := f.isOpenEmbedding
    have g_embedd_TopCat : IsOpenEmbedding (forgetToTop.map g) := g.isOpenEmbedding
    let top_push : IsPushout (forgetToTop.map f) (forgetToTop.map g) (forgetToTop.map inl)
        (forgetToTop.map inr) := h.map Scheme.forgetToTop
    have inl_inj_base : Function.Injective inl.base := by
      have := ((inl_inr_isOpenImmersion f g inl inr h).1.mono)
      exact Hom.injective inl
    have range_inter_top := range_inter_top (forgetToTop.map f) (forgetToTop.map g)
      (forgetToTop.map inl) (forgetToTop.map inr) f_embedd_TopCat g_embedd_TopCat top_push
    have range_inter : Set.range inl.base ∩ Set.range inr.base ⊆ Set.range (f ≫ inl).base :=
      Eq.subset range_inter_top
    constructor
    fapply PullbackCone.IsLimit.mk
    · intro s
      have range_subset : Set.range s.fst.base ⊆ f.opensRange := by
        rintro x ⟨w, rfl⟩
        have mem_inter : (inl.base (s.fst.base w)) ∈ Set.range inl.base ∩ Set.range inr.base := by
          refine ⟨Set.mem_range_self _, ?_⟩
          have eq_base : (s.fst ≫ inl).base w = (s.snd ≫ inr).base w := by
            rw [s.condition]
          simp_all only [Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp,
            ContinuousMap.comp_apply, Set.mem_range, exists_apply_eq_apply]
        obtain ⟨u, hu⟩ := range_inter mem_inter
        apply inl_inj_base at hu
        rw [← hu]
        exact Set.mem_range_self _
      exact IsOpenImmersion.lift f s.fst range_subset
    · intro s
      simp only [IsOpenImmersion.lift_fac]
    · intro s
      simp only
      have range_subset : Set.range s.fst.base ⊆ f.opensRange := by
        rintro x ⟨w, rfl⟩
        have mem_inter : (inl.base (s.fst.base w)) ∈ Set.range inl.base ∩ Set.range inr.base := by
          refine ⟨Set.mem_range_self _, ?_⟩
          have eq_base : (s.fst ≫ inl).base w = (s.snd ≫ inr).base w := by
            rw [s.condition]
          simp_all only [Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp,
            ContinuousMap.comp_apply, Set.mem_range, exists_apply_eq_apply]
        obtain ⟨u, hu⟩ := range_inter mem_inter
        apply inl_inj_base at hu
        rw [← hu]
        exact Set.mem_range_self _
      apply (inl_inr_isOpenImmersion f g inl inr h).2.mono.right_cancellation
      simp only [Category.assoc]
      rw [←h.toCommSq.w, ←Category.assoc, IsOpenImmersion.lift_fac f s.fst range_subset]
      apply s.condition
    · intro s m p q
      exact IsOpenImmersion.lift_uniq f s.fst _ _ p
  · exact h.toCommSq


section Diagonal

/--
The diagonal morphism factored through the pullback of the product.
-/
lemma diag_eq_pullback_diagonal (Y : Scheme) :
    diag Y ≫ (prodIsoPullback Y Y).hom = pullback.diagonal (terminal.from Y) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, prodIsoPullback_hom_fst, limit.lift_π, BinaryFan.mk_pt,
      BinaryFan.mk_fst, pullback.diagonal_fst]
  · simp only [Category.assoc, prodIsoPullback_hom_snd, limit.lift_π, BinaryFan.mk_pt,
      BinaryFan.mk_snd, pullback.diagonal_snd]

/--
The diagonal of a separated scheme is a closed immersion.
-/
lemma diag_isClosedImmersion (Y : Scheme) [IsSeparated (terminal.from Y)] :
    IsClosedImmersion (diag Y) := by
  have iso_closed : IsClosedImmersion (prodIsoPullback Y Y).hom := inferInstance
  have diag_pullback := diag_eq_pullback_diagonal Y
  have rhs_closed : IsClosedImmersion (pullback.diagonal (terminal.from Y)) := inferInstance
  have comp_closed : IsClosedImmersion (diag Y ≫ (prodIsoPullback Y Y).hom) := by
    rw [diag_pullback]
    infer_instance
  exact IsClosedImmersion.of_comp (diag Y) ((prodIsoPullback Y Y).hom)

/--
The equalizer inclusion of two morphisms into a separated scheme is a closed immersion.
-/
instance isClosedImmersion_equalizer_iota {X Y : Scheme} [IsSeparated (terminal.from Y)]
    (f g : X ⟶ Y) : IsClosedImmersion (equalizer.ι f g) := by
  refine MorphismProperty.of_isPullback (isPullback_equalizer_prod f g).flip ?_
  have h : diag Y = prod.lift (𝟙 Y) (𝟙 Y) := rfl
  rw [← h]
  exact diag_isClosedImmersion Y

end Diagonal

section Construction

/-- The affine line $\mathbb{A}^1 = \text{Spec}(\mathbb{Z}[X])$. -/
def affineLine : Scheme := Spec (.of ℤ[X])

/-- The open subset  \mathbb{A}^1 \setminus \{0\}$, defined as the basic open set $D(X)$. -/
def line_minusOrigin : affineLine.Opens := PrimeSpectrum.basicOpen (X : ℤ[X])

/-- The inclusion map $i : U \to \mathbb{A}^1$. -/
abbrev inclusion : line_minusOrigin.toScheme ⟶ affineLine := line_minusOrigin.ι

instance : IsOpenImmersion inclusion := inferInstance

/-- The open subscheme $U$ is nonempty. -/
lemma line_minusOrigin_nonempty : Nonempty line_minusOrigin.toScheme := by
  use ⟨⊥, Ideal.isPrime_bot⟩
  exact Polynomial.X_ne_zero

/-- The image of the inclusion map is nonempty. -/
lemma range_inclusion_nonempty : Set.Nonempty (Set.range inclusion.base) := by
  have h₁ := line_minusOrigin_nonempty
  exact Set.range_nonempty ⇑(ConcreteCategory.hom inclusion.base)

/-- The ideal generated by $X$ is prime in $\mathbb{Z}[X]$. -/
lemma X_isPrime : Ideal.IsPrime (Ideal.span {X} : Ideal ℤ[X]) := by
  rw [Ideal.span_singleton_prime Polynomial.X_ne_zero]
  exact Polynomial.prime_X

/-- The origin point defined by the ideal $(X)$. -/
def originPoint : affineLine := ⟨(Ideal.span {X} : Ideal ℤ[X]), X_isPrime⟩

/-- The origin is not in the image of the open immersion $i$. -/
lemma originPoint_not_in_range_inclusion : originPoint ∉ Set.range inclusion.base := by
  intro h
  rw [Scheme.Opens.range_ι] at h
  change originPoint ∈ PrimeSpectrum.basicOpen X at h
  rw [PrimeSpectrum.mem_basicOpen] at h
  apply h
  exact (Submodule.span_singleton_le_iff_mem X originPoint.asIdeal).mp fun ⦃x⦄ a ↦ a

/-- The origin is in the complement of the image of $i$. -/
lemma originPoint_mem_compl_range_inclusion :
    originPoint ∈ Set.compl (Set.range inclusion.base) :=
  originPoint_not_in_range_inclusion

/--
The **Affine Line with Doubled Origin**.
Constructed as the pushout of two copies of $\mathbb{A}^1$ glued along
 $U = \mathbb{A}^1 \setminus \{0\}$.
-/
def affineLineWithDoubledOrigin : Scheme := pushout inclusion inclusion

namespace AffineLineWithDoubledOrigin

/-- The inclusion of the first copy of $\mathbb{A}^1$. -/
def f : affineLine ⟶ affineLineWithDoubledOrigin := pushout.inl inclusion inclusion

/-- The inclusion of the second copy of $\mathbb{A}^1$. -/
def g : affineLine ⟶ affineLineWithDoubledOrigin := pushout.inr inclusion inclusion


/-- The defining pushout property. -/
lemma isPushout : IsPushout inclusion inclusion f g :=
  IsPushout.of_hasPushout inclusion inclusion

/-- The pushout square defining the scheme is also a pullback square. -/
lemma gluing_square_isPullback : IsPullback inclusion inclusion f g :=
  isPullback_of_isPushout_of_isOpenImmersion inclusion inclusion f g isPushout

/-- Commutativity of the pushout square. -/
lemma f_comp_eq_g_comp : inclusion ≫ f = inclusion ≫ g := isPushout.toCommSq.w

variable {Z : Scheme} (q : Z ⟶ affineLine)

/-- Lift a map $q: Z \to \mathbb{A}^1$ satisfying the equalizer condition to $U$. -/
def liftToOpen (h : q ≫ f = q ≫ g) : Z ⟶ line_minusOrigin.toScheme :=
  gluing_square_isPullback.lift q q h

/-- The lift factors $q$ through the inclusion. -/
theorem liftToOpen_fac (h : q ≫ f = q ≫ g) : liftToOpen q h ≫ inclusion = q :=
  gluing_square_isPullback.lift_fst q q h

/-- The lift is unique. -/
theorem liftToOpen_uniq (h : q ≫ f = q ≫ g) (l : Z ⟶ line_minusOrigin.toScheme)
    (hl : l ≫ inclusion = q) : l = liftToOpen q h := by
  apply gluing_square_isPullback.hom_ext
  · rw [hl]
    exact Eq.symm (liftToOpen_fac q h)
  · rw [hl]
    exact Eq.symm (liftToOpen_fac q h)

/-- The open subscheme $U$ is the equalizer of the two inclusions into the pushout. -/
instance line_minusOrigin_isEqualizer : IsLimit (Fork.ofι inclusion f_comp_eq_g_comp) :=
  Fork.IsLimit.mk' _ fun s => by
    let q := s.ι
    have hq : q ≫ f = q ≫ g := s.condition
    exact {
      val := liftToOpen q hq
      property := by
        constructor
        · apply liftToOpen_fac
        · intro m hm
          change m ≫ inclusion = q at hm
          apply liftToOpen_uniq q hq m hm
    }

/-- The canonical isomorphism between $U$ and the categorical equalizer. -/
def isoOpenToEqualizer : line_minusOrigin.toScheme ≅ equalizer f g :=
  IsLimit.conePointUniqueUpToIso line_minusOrigin_isEqualizer (limit.isLimit _)

lemma inclusion_eq_iso_comp_iota : inclusion = isoOpenToEqualizer.hom ≫ equalizer.ι f g := by
  symm
  exact IsLimit.conePointUniqueUpToIso_hom_comp
    line_minusOrigin_isEqualizer (limit.isLimit _) WalkingParallelPair.zero

/-- The inclusion $U \to \mathbb{A}^1$ is a closed immersion (if the scheme is separated). -/
lemma inclusion_isClosedImmersion [IsSeparated (terminal.from affineLineWithDoubledOrigin)] :
    IsClosedImmersion inclusion := by
  rw [inclusion_eq_iso_comp_iota]
  have h₁ : IsClosedImmersion isoOpenToEqualizer.hom := inferInstance
  have h₂ : IsClosedImmersion (equalizer.ι f g) := inferInstance
  exact IsClosedImmersion.comp isoOpenToEqualizer.hom (equalizer.ι f g)

instance : IrreducibleSpace affineLine := by
  unfold affineLine
  infer_instance

/--
$\mathbb{A}^1$ is not irreducible if the affine line with doubled origin is separated.
This leads to a contradiction, proving the latter is not separated.
-/
lemma affineLine_not_irreducible [IsSeparated (terminal.from affineLineWithDoubledOrigin)] :
    ¬ (IrreducibleSpace affineLine) := by
  intro _
  have h₁ : IsOpen (Set.range inclusion.base) := IsOpenImmersion.isOpen_range inclusion
  haveI : IsClosedImmersion inclusion := inclusion_isClosedImmersion
  have h₂ : IsClosed (Set.range inclusion.base) :=
    (Scheme.Hom.isClosedEmbedding inclusion).isClosed_range
  have h₃ : IsOpen (Set.compl (Set.range inclusion.base)) := h₂.isOpen_compl
  have h₅ : Set.Nonempty (Set.compl (Set.range inclusion.base)) :=
    ⟨originPoint, originPoint_mem_compl_range_inclusion⟩
  have h₆ : Set.Nonempty (Set.range inclusion.base) := range_inclusion_nonempty
  have h₇ : Disjoint (Set.range inclusion.base) (Set.compl (Set.range inclusion.base)) := by
    exact Set.disjoint_left.mpr fun ⦃a⦄ a_1 a_2 ↦ a_2 a_1
  have h₈ : ¬ Disjoint (Set.range inclusion.base) (Set.compl (Set.range inclusion.base)) :=
    Set.not_disjoint_iff_nonempty_inter.mpr (nonempty_preirreducible_inter h₁ h₃ h₆ h₅)
  contradiction


/--
**Main Theorem**: The Affine Line with Doubled Origin is not separated.
-/
theorem not_isSeparated : ¬ (IsSeparated (terminal.from affineLineWithDoubledOrigin)) := by
  intro h
  have : IrreducibleSpace affineLine := inferInstance
  have := affineLine_not_irreducible
  contradiction

end AffineLineWithDoubledOrigin
