/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.AlgebraicGeometry.Sites.QuasiCompact
import Mathlib.AlgebraicGeometry.Cover.Sigma
import Mathlib.CategoryTheory.Sites.Preserves

/-!
# The quasi-compact topology of a scheme

The `qc`-pretopology of a scheme wrt. to a morphism property `P` is the pretopology
given by quasi compact covers satisfying `P`.

We show that a presheaf is a sheaf in this topology if and only if it is a sheaf
in the Zariski topology and a sheaf on single object `P`-coverings of affine schemes.
-/

universe w' w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory

open Limits

variable {C : Type*} [Category C]

lemma Presieve.ofArrows_of_unique {S : C} {ι : Type*} [Unique ι] {X : ι → C} (f : ∀ i, X i ⟶ S) :
    ofArrows X f = singleton (f default) := by
  refine le_antisymm ?_ fun Y _ ⟨⟩ ↦ ⟨default⟩
  rw [ofArrows_le_iff]
  intro i
  obtain rfl : i = default := Subsingleton.elim _ _
  simp

-- TODO: this is almost in mathlib, with slightly less general universe assumptions on `F`
-- and with a wrong name
lemma Presieve.IsSheafFor.of_isSheafFor_pullback'' (F : Cᵒᵖ ⥤ Type*) {X : C}
    (S T : Sieve X)
    (hF : Presieve.IsSheafFor F S.arrows)
    (hF' : ∀ {Y : C} (f : Y ⟶ X), Presieve.IsSeparatedFor F (S.pullback f).arrows)
    (H : ∀ {Y : C} (f : Y ⟶ X), S f → Presieve.IsSheafFor F (T.pullback f).arrows) :
    Presieve.IsSheafFor F T.arrows := by
  intro t ht
  have ⦃Y : C⦄ (f : Y ⟶ X) (hf : S f) := H f hf (t.pullback f) (ht.pullback f)
  choose s hs huniq using this
  have hr : FamilyOfElements.Compatible s := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro Y Z f g hf
    refine (H (g ≫ f) (by simp [hf])).isSeparatedFor.ext fun U o ho ↦ ?_
    simp only [Sieve.pullback_apply] at ho
    dsimp only [FamilyOfElements.IsAmalgamation, FamilyOfElements.pullback] at hs
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, hs _ _ _ ho, hs _ _ _ (by simpa)]
    congr 1
    simp
  obtain ⟨t', ht', hunique⟩ := hF s hr
  refine ⟨t', fun Y f hf ↦ (hF' f).ext fun Z g hg ↦ ?_, fun y hy ↦ ?_⟩
  · rw [← FunctorToTypes.map_comp_apply, ← op_comp, ht' (g ≫ f) hg, ← t.comp_of_compatible _ ht]
    have := hs (g ≫ f) hg (𝟙 _)
    dsimp only [Presieve.FamilyOfElements.IsAmalgamation,
      Presieve.FamilyOfElements.pullback] at this
    simp only [Sieve.pullback_apply, Category.id_comp, op_id, FunctorToTypes.map_id_apply] at this
    rw [this]
    · congr 1
      simp
    · simp [hf]
  · refine hunique _ fun Y f hf ↦ huniq _ _ _ fun Z g hg ↦ ?_
    simp [Presieve.FamilyOfElements.pullback, ← hy _ hg]

lemma Presieve.IsSheafFor.of_isSheafFor_pullback
    (F : Cᵒᵖ ⥤ Type*) {X : C}
    (S : Presieve X) (T : Sieve X) [S.HasPairwisePullbacks]
    (hF : Presieve.IsSheafFor F S)
    (hF' : ∀ {Y : C} (f : Y ⟶ X), Presieve.IsSeparatedFor F ((Sieve.generate S).pullback f).arrows)
    (H' : ∀ {Y Z : C} (f : Y ⟶ X) (g : Z ⟶ X) (hf : S f) (hg : S g),
      haveI := HasPairwisePullbacks.has_pullbacks hf hg
      ∃ (R : Presieve (pullback f g)), Presieve.IsSeparatedFor F R ∧
        ∀ {W : C} (w : W ⟶ pullback f g),
          R w → Presieve.IsSeparatedFor F (T.pullback (w ≫ pullback.fst f g ≫ f)).arrows)
    (H : ∀ {Y : C} (f : Y ⟶ X), S f → Presieve.IsSheafFor F (T.pullback f).arrows) :
    Presieve.IsSheafFor F T.arrows := by
  intro t ht
  have ⦃Y : C⦄ (f : Y ⟶ X) (hf : S f) := H f hf (t.pullback f) (ht.pullback f)
  choose s hs huniq using this
  have hr : FamilyOfElements.Compatible s := by
    rw [pullbackCompatible_iff]
    intro Y Z f g hf hg
    haveI := HasPairwisePullbacks.has_pullbacks hf hg
    obtain ⟨R, hR, h⟩ := H' f g hf hg
    refine hR.ext fun W w hw ↦ (h w hw).ext fun U u hu ↦ ?_
    simp only [← FunctorToTypes.map_comp_apply, ← op_comp]
    dsimp only [FamilyOfElements.IsAmalgamation, FamilyOfElements.pullback] at hs
    rw [hs f hf (u ≫ w ≫ pullback.fst f g) (by simpa),
      hs g hg (u ≫ w ≫ pullback.snd f g) (by simpa [← pullback.condition])]
    congr 1
    simp [pullback.condition]
  obtain ⟨t', ht', hunique⟩ := hF s hr
  refine ⟨t', fun Y f hf ↦ (hF' f).ext fun Z g hg ↦ ?_, fun y hy ↦ ?_⟩
  · rw [← FunctorToTypes.map_comp_apply, ← op_comp]
    simp only [Sieve.pullback_apply, Sieve.generate_apply] at hg
    obtain ⟨W, w, u, hu, heq⟩ := hg
    simp only [← heq, op_comp, FunctorToTypes.map_comp_apply, ht' u hu]
    have : t (g ≫ f) (by simp [hf]) = t (w ≫ u) (by simp [heq, hf]) := by
      congr 1
      rw [heq]
    rw [← t.comp_of_compatible _ ht, this]
    apply hs
  · refine hunique _ fun Y f hf ↦ huniq _ _ _ fun Z g hg ↦ ?_
    simp [Presieve.FamilyOfElements.pullback, ← hy _ hg]

lemma Presieve.IsSheafFor.of_isSheafFor_pullback' (F : Cᵒᵖ ⥤ Type*) {X : C}
    (S T : Presieve X) [S.HasPairwisePullbacks]
    (hF : Presieve.IsSheafFor F S)
    (hF' : ∀ {Y : C} (f : Y ⟶ X), Presieve.IsSeparatedFor F ((Sieve.generate S).pullback f).arrows)
    (H' : ∀ {Y Z : C} (f : Y ⟶ X) (g : Z ⟶ X) (hf : S f) (hg : S g),
      haveI := HasPairwisePullbacks.has_pullbacks hf hg
      ∃ (R : Presieve (pullback f g)), Presieve.IsSeparatedFor F R ∧
        ∀ {W : C} (w : W ⟶ pullback f g),
          R w → Presieve.IsSeparatedFor F
            ((Sieve.generate T).pullback (w ≫ pullback.fst f g ≫ f)).arrows)
    (H : ∀ {Y : C} (f : Y ⟶ X),
      S f → Presieve.IsSheafFor F ((Sieve.generate T).pullback f).arrows) :
    Presieve.IsSheafFor F T := by
  rw [isSheafFor_iff_generate]
  apply Presieve.IsSheafFor.of_isSheafFor_pullback F S _ _ hF'
  · assumption
  · assumption
  · assumption

end CategoryTheory

namespace CategoryTheory

variable {C : Type*} [Category C] {X : C}

@[simps]
def PreZeroHypercover.restrictIndexHom (E : PreZeroHypercover.{w} X) {ι : Type w'}
    (f : ι → E.I₀) :
    (E.restrictIndex f).Hom E where
  s₀ := f
  h₀ _ := 𝟙 _

@[simp]
lemma PreZeroHypercover.presieve₀_restrictIndex_le {X : C} (E : PreZeroHypercover X) {ι : Type*}
    (f : ι → E.I₀) :
    (E.restrictIndex f).presieve₀ ≤ E.presieve₀ := by
  rw [Presieve.ofArrows_le_iff]
  intro i
  exact .mk _

lemma Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange_of_small
    {J : Precoverage C} [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [Small.{w} J] (P : Cᵒᵖ ⥤ Type*) :
    Presieve.IsSheaf J.toGrothendieck P ↔
      ∀ ⦃X : C⦄ (E : ZeroHypercover.{w} J X), Presieve.IsSheafFor P E.presieve₀ := by
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  refine ⟨fun h X E ↦ ?_, fun h X R hR ↦ ?_⟩
  · apply h
    exact E.mem₀
  · obtain ⟨E₀, rfl⟩ := R.exists_eq_preZeroHypercover
    rw [Presieve.isSheafFor_iff_generate]
    let E : ZeroHypercover J X := ⟨E₀, hR⟩
    apply Presieve.isSheafFor_subsieve
      (S := .generate <| (ZeroHypercover.restrictIndexOfSmall.{w} E).presieve₀)
    · exact Sieve.generate_mono (by simp [E])
    · intro Y f
      rw [← Sieve.pullbackArrows_comm, ← Presieve.isSheafFor_iff_generate,
        ← PreZeroHypercover.presieve₀_pullback₁, ← ZeroHypercover.pullback₂_toPreZeroHypercover]
      apply h

lemma Presieve.isSheafFor_ofArrows_comp_iff {F : Cᵒᵖ ⥤ Type*} {ι : Type*} {Y Z : ι → C}
    (g : ∀ i, Z i ⟶ X)
    (e : ∀ i, Y i ≅ Z i) :
    Presieve.IsSheafFor F (.ofArrows _ (fun i ↦ (e i).hom ≫ g i)) ↔
      Presieve.IsSheafFor F (.ofArrows _ g) := by
  have : Sieve.generate (.ofArrows _ g) =
      Sieve.generate (.ofArrows _ (fun i ↦ (e i).hom ≫ g i)) := by
    refine le_antisymm ?_ ?_
    · rw [Sieve.generate_le_iff]
      rintro - - ⟨i⟩
      exact ⟨_, (e i).inv, (e i).hom ≫ g i, ⟨i⟩, by simp⟩
    · rw [Sieve.generate_le_iff]
      rintro - - ⟨i⟩
      exact ⟨_, (e i).hom, _, ⟨i⟩, by simp⟩
  rw [Presieve.isSheafFor_iff_generate, ← this, ← Presieve.isSheafFor_iff_generate]

lemma isSheafFor_singleton_iff_of_iso
    {F : Cᵒᵖ ⥤ Type*} {S X Y : C} (f : X ⟶ S) (g : Y ⟶ S)
    (e : X ≅ Y) (he : e.hom ≫ g = f) :
    Presieve.IsSheafFor F (.singleton f) ↔ Presieve.IsSheafFor F (.singleton g) := by
  subst he
  rw [← Presieve.ofArrows_pUnit.{_, _, 0}, ← Presieve.ofArrows_pUnit,
    Presieve.isSheafFor_ofArrows_comp_iff]

@[gcongr]
lemma Pretopology.toGrothendieck_mono {C : Type*} [Category C] [HasPullbacks C]
    {J K : Pretopology C} (h : J ≤ K) : J.toGrothendieck ≤ K.toGrothendieck :=
  fun _ _ ⟨R, hR, hle⟩ ↦ ⟨R, h _ hR, hle⟩

attribute [grind .] GrothendieckTopology.pullback_stable GrothendieckTopology.transitive

@[gcongr]
lemma Precoverage.toPretopology_mono {C : Type*} [Category C] [Limits.HasPullbacks C]
    {J K : Precoverage C} [J.HasIsos] [J.IsStableUnderBaseChange] [J.IsStableUnderComposition]
    [K.HasIsos] [K.IsStableUnderBaseChange] [K.IsStableUnderComposition]
    (h : J ≤ K) : J.toPretopology ≤ K.toPretopology :=
  h

variable {C : Type*} [Category C]

/--
If
- `F` contravariantly maps (suitable) coproducts to products,
- (suitable) coproducts exist in `C`, and
- (suitable) coproducts distribute over pullbacks, then:

`F` is a sheaf for the single object covering `{ ∐ᵢ Yᵢ ⟶ X }`
if and only if it is a presieve for `{ fᵢ : Yᵢ ⟶ X }ᵢ`.

Note: The second two conditions are satisfied if `C` is (finitary) extensive.
-/
lemma Presieve.isSheafFor_sigmaDesc_iff {F : Cᵒᵖ ⥤ Type v} {X : C} {ι : Type*} [Small.{v} ι]
    {Y : ι → C}
    (f : ∀ i, Y i ⟶ X) [(ofArrows Y f).HasPairwisePullbacks]
    [HasCoproduct Y] [HasCoproduct fun (ij : ι × ι) ↦ pullback (f ij.1) (f ij.2)]
    [HasPullback (Limits.Sigma.desc f) (Limits.Sigma.desc f)]
    [PreservesLimit (Discrete.functor <| fun i ↦ op (Y i)) F]
    [PreservesLimit (Discrete.functor fun (ij : ι × ι) ↦ op (pullback (f ij.1) (f ij.2))) F]
    [IsIso (Limits.Sigma.desc fun (ij : ι × ι) ↦ Limits.pullback.map (f ij.fst) (f ij.snd)
      (Limits.Sigma.desc f) (Limits.Sigma.desc f) (Limits.Sigma.ι _ _) (Limits.Sigma.ι _ _) (𝟙 X)
      (by simp) (by simp))] :
    Presieve.IsSheafFor F (.singleton <| Limits.Sigma.desc f) ↔
      Presieve.IsSheafFor F (.ofArrows Y f) := by
  let e : (∐ fun (ij : ι × ι) ↦ pullback (f ij.1) (f ij.2)) ⟶
      pullback (Limits.Sigma.desc f) (Limits.Sigma.desc f) :=
    Limits.Sigma.desc fun ij ↦
    pullback.map _ _ _ _ (Limits.Sigma.ι _ _) (Limits.Sigma.ι _ _) (𝟙 X) (by simp) (by simp)
  rw [Equalizer.Presieve.isSheafFor_singleton_iff (pullback.cone _ _) (pullback.isLimit _ _),
    Equalizer.Presieve.Arrows.sheaf_condition]
  refine (Fork.isLimitEquivOfIsos _ _ ?_ ?_ ?_ ?_ ?_ ?_).nonempty_congr
  · exact F.mapIso (opCoproductIsoProduct Y) ≪≫ PreservesProduct.iso F _
  · exact F.mapIso (.op <| asIso e) ≪≫ F.mapIso (opCoproductIsoProduct _) ≪≫
      PreservesProduct.iso F _
  · exact Iso.refl _
  · refine Pi.hom_ext _ _ fun ij ↦ ?_
    simp only [Iso.trans_hom, Functor.mapIso_hom, PreservesProduct.iso_hom, Category.assoc,
      limit.cone_x, PullbackCone.fst_limit_cone, Iso.op_hom, asIso_hom, e, piComparison_comp_π,
      Equalizer.Presieve.Arrows.firstMap]
    rw [← F.map_comp, opCoproductIsoProduct_hom_comp_π, ← F.map_comp, ← op_comp, Sigma.ι_desc,
      ← F.map_comp, ← op_comp, pullback.lift_fst, Pi.lift_π, piComparison_comp_π_assoc,
      ← F.map_comp, ← F.map_comp]
    simp
  · refine Pi.hom_ext _ _ fun ij ↦ ?_
    simp only [Iso.trans_hom, Functor.mapIso_hom, PreservesProduct.iso_hom, Category.assoc,
      limit.cone_x, PullbackCone.snd_limit_cone, Iso.op_hom, asIso_hom, e, piComparison_comp_π,
      Equalizer.Presieve.Arrows.secondMap]
    rw [← F.map_comp, opCoproductIsoProduct_hom_comp_π, ← F.map_comp, ← op_comp, Sigma.ι_desc,
      ← F.map_comp, ← op_comp, pullback.lift_snd, Pi.lift_π, piComparison_comp_π_assoc,
      ← F.map_comp, ← F.map_comp]
    simp
  · refine Pi.hom_ext _ _ fun i ↦ ?_
    simp only [Fork.ofι_pt, Fork.ι_ofι, Iso.trans_hom, Functor.mapIso_hom, PreservesProduct.iso_hom,
      Category.assoc, piComparison_comp_π]
    rw [← F.map_comp, ← F.map_comp, opCoproductIsoProduct_hom_comp_π, ← op_comp, Sigma.ι_desc]
    simp [Equalizer.Presieve.Arrows.forkMap]

end CategoryTheory

namespace AlgebraicGeometry

open Scheme

variable {P : MorphismProperty Scheme.{u}}

@[simp]
lemma Scheme.Cover.ofArrows_sigma {S : Scheme.{u}} (𝒰 : S.Cover (precoverage P))
    [IsZariskiLocalAtSource P] :
    Presieve.ofArrows 𝒰.sigma.X 𝒰.sigma.f = Presieve.singleton (Sigma.desc 𝒰.f) := by
  refine le_antisymm ?_ ?_
  · intro T g ⟨i⟩
    exact Presieve.singleton_self _
  · intro T g ⟨⟩
    exact ⟨⟨⟩⟩

/-- The `qc`-precoverage of a scheme wrt. to a morphism property `P` is the precoverage
given by quasi compact covers satisfying `P`. -/
abbrev propqcPrecoverage (P : MorphismProperty Scheme.{u}) : Precoverage Scheme.{u} :=
  qcPrecoverage ⊓ Scheme.precoverage P

instance {P : MorphismProperty Scheme.{u}} {S : Scheme.{u}}
    (𝒰 : Scheme.Cover (propqcPrecoverage P) S) : QuasiCompactCover 𝒰.toPreZeroHypercover := by
  rw [← Scheme.presieve₀_mem_qcPrecoverage_iff]
  exact 𝒰.mem₀.1

@[simps toPreZeroHypercover]
abbrev Scheme.Cover.forgetQc {P : MorphismProperty Scheme.{u}} {S : Scheme.{u}}
    (𝒰 : Scheme.Cover (propqcPrecoverage P) S) :
    S.Cover (precoverage P) where
  __ := 𝒰.toPreZeroHypercover
  mem₀ := 𝒰.mem₀.2

instance {P : MorphismProperty Scheme.{u}} {S : Scheme.{u}}
    (𝒰 : Scheme.Cover (propqcPrecoverage P) S) :
    QuasiCompactCover 𝒰.forgetQc.toPreZeroHypercover := by
  dsimp; infer_instance

@[simps toPreZeroHypercover]
def Scheme.Cover.ofQuasiCompactCover {P : MorphismProperty Scheme.{u}} {S : Scheme.{u}}
    (𝒰 : Scheme.Cover (precoverage P) S) [qc : QuasiCompactCover 𝒰.1] :
    Scheme.Cover (propqcPrecoverage P) S where
  __ := 𝒰.toPreZeroHypercover
  mem₀ := ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr ‹_›, 𝒰.mem₀⟩

namespace QuasiCompactCover

def uliftaux {S : Scheme.{u}} (𝒰 : PreZeroHypercover S) [QuasiCompactCover 𝒰] :
    Type u :=
  Σ (U : S.affineOpens), Fin (exists_isAffineOpen_of_isCompact 𝒰 U.2.isCompact).choose

structure IdxAux {S : Scheme.{u}} (𝒰 : PreZeroHypercover S) [QuasiCompactCover 𝒰] : Type u where
  affineOpen : S.affineOpens
  idx : Fin (exists_isAffineOpen_of_isCompact 𝒰 affineOpen.2.isCompact).choose

noncomputable def ulift {S : Scheme.{u}} (𝒰 : PreZeroHypercover S) [QuasiCompactCover 𝒰] :
    PreZeroHypercover.{u} S :=
  𝒰.restrictIndex fun i : IdxAux 𝒰 ↦
    (exists_isAffineOpen_of_isCompact 𝒰 i.affineOpen.2.isCompact).choose_spec.choose i.idx

noncomputable
def uliftHom {S : Scheme.{u}} (𝒰 : PreZeroHypercover S) [QuasiCompactCover 𝒰] :
    (ulift 𝒰).Hom 𝒰 :=
  𝒰.restrictIndexHom _

instance {S : Scheme.{u}} (𝒰 : PreZeroHypercover S) [QuasiCompactCover 𝒰] :
    QuasiCompactCover (ulift 𝒰) where
  isCompactOpenCovered_of_isAffineOpen {U} hU :=
    let H := exists_isAffineOpen_of_isCompact 𝒰 hU.isCompact
    .of_finite (fun i : Fin H.choose ↦ ⟨⟨U, hU⟩, i⟩)
      (fun _ ↦ H.choose_spec.choose_spec.choose _)
      (fun _ ↦ H.choose_spec.choose_spec.choose_spec.left _ |>.isCompact)
      H.choose_spec.choose_spec.choose_spec.right

end QuasiCompactCover

noncomputable
def Scheme.Cover.ulift' {P : MorphismProperty Scheme.{u}}
    {S : Scheme.{u}} (𝒰 : S.Cover (precoverage P)) [QuasiCompactCover 𝒰.1] :
    Scheme.Cover.{u} (precoverage P) S where
  __ := 𝒰.ulift.toPreZeroHypercover.sum (QuasiCompactCover.ulift 𝒰.1)
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ⟨.inl x, 𝒰.covers _⟩, fun i ↦ ?_⟩
    induction i <;> exact 𝒰.map_prop _

instance (P : MorphismProperty Scheme.{u})
    {S : Scheme.{u}} (𝒰 : S.Cover (precoverage P)) [QuasiCompactCover 𝒰.1] :
    QuasiCompactCover (Scheme.Cover.ulift' 𝒰).1 :=
  .of_hom (PreZeroHypercover.sumInr _ _)

instance : Precoverage.Small.{u} (propqcPrecoverage P) where
  zeroHypercoverSmall {S} (𝒰 : S.Cover _) := by
    refine ⟨𝒰.forgetQc.ulift'.I₀, Sum.elim 𝒰.forgetQc.idx (QuasiCompactCover.uliftHom _).s₀,
      ⟨?_, ?_⟩⟩
    · rw [Scheme.presieve₀_mem_qcPrecoverage_iff]
      exact .of_hom (𝒱 := QuasiCompactCover.ulift 𝒰.1) ⟨Sum.inr, fun i ↦ 𝟙 _, by cat_disch⟩
    · rw [Scheme.presieve₀_mem_precoverage_iff]
      exact ⟨fun x ↦ ⟨Sum.inl x, 𝒰.forgetQc.covers _⟩, fun i ↦ 𝒰.forgetQc.map_prop _⟩

@[grind .]
lemma propqcPrecoverage_le_precoverage (P : MorphismProperty Scheme.{u}) :
    propqcPrecoverage P ≤ precoverage P :=
  inf_le_right

lemma mem_propqcPrecoverage_iff_exists_quasiCompactCover {P : MorphismProperty Scheme.{u}}
    {S : Scheme.{u}} {R : Presieve S} :
    R ∈ propqcPrecoverage P S ↔ ∃ (𝒰 : Scheme.Cover.{u + 1} (precoverage P) S),
      QuasiCompactCover 𝒰.toPreZeroHypercover ∧ R = 𝒰.presieve₀ := by
  rw [Precoverage.mem_iff_exists_zeroHypercover]
  refine ⟨fun ⟨𝒰, h⟩ ↦ ⟨𝒰.weaken <| propqcPrecoverage_le_precoverage P, ?_, h⟩,
    fun ⟨𝒰, _, h⟩ ↦ ⟨⟨𝒰.1, ⟨by simpa, 𝒰.mem₀⟩⟩, h⟩⟩
  rw [← Scheme.presieve₀_mem_qcPrecoverage_iff]
  exact 𝒰.mem₀.1

abbrev propqcTopology (P : MorphismProperty Scheme.{u}) : GrothendieckTopology Scheme.{u} :=
  (propqcPrecoverage P).toGrothendieck

lemma Scheme.Hom.singleton_mem_qcPrecoverage {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Surjective f] [QuasiCompact f] :
    Presieve.singleton f ∈ qcPrecoverage Y := by
  let E : Cover.{u} _ _ := f.cover (P := ⊤) trivial
  rw [qcPrecoverage, PreZeroHypercoverFamily.mem_precoverage_iff]
  refine ⟨(f.cover (P := ⊤) trivial).toPreZeroHypercover, ?_, by simp⟩
  simp only [qcCoverFamily_property, quasiCompactCover_iff]
  infer_instance

attribute [grind .] Scheme.Hom.surjective

@[simp]
lemma Scheme.Hom.singleton_mem_propqcPrecoverage [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (hf : P f) [Surjective f] [QuasiCompact f] :
    Presieve.singleton f ∈ propqcPrecoverage P Y := by
  refine ⟨f.singleton_mem_qcPrecoverage, ?_⟩
  grind [singleton_mem_precoverage_iff]

@[simp]
lemma Scheme.Hom.generate_singleton_mem_propqcTopology [P.IsMultiplicative]
    [P.IsStableUnderBaseChange] {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : P f) [Surjective f]
    [QuasiCompact f] : Sieve.generate (Presieve.singleton f) ∈ propqcTopology P Y := by
  apply Precoverage.generate_mem_toGrothendieck
  exact f.singleton_mem_propqcPrecoverage hf

@[simp]
lemma Scheme.Cover.generate_ofArrows_mem_propqcTopology [P.IsMultiplicative]
    [P.IsStableUnderBaseChange] {S : Scheme.{u}} (𝒰 : Cover.{u} (precoverage P) S)
    [QuasiCompactCover 𝒰.1] :
    .generate (.ofArrows 𝒰.X 𝒰.f) ∈ propqcTopology P S := by
  apply Precoverage.generate_mem_toGrothendieck
  refine ⟨?_, ?_⟩
  · rwa [presieve₀_mem_qcPrecoverage_iff]
  · exact 𝒰.mem₀

-- This holds more generally if `𝒰.J` is `u`-small, but we don't need that for now.
lemma Scheme.Cover.isSheafFor_sigma_iff {F : Scheme.{u}ᵒᵖ ⥤ Type w} [IsZariskiLocalAtSource P]
    (hF : Presieve.IsSheaf Scheme.zariskiTopology F)
    {S : Scheme.{u}} (𝒰 : S.Cover (precoverage P)) [Finite 𝒰.I₀] :
    Presieve.IsSheafFor F (.ofArrows 𝒰.sigma.X 𝒰.sigma.f) ↔
      Presieve.IsSheafFor F (.ofArrows 𝒰.X 𝒰.f) := by
  have : PreservesLimitsOfShape (Discrete (𝒰.I₀ × 𝒰.I₀)) F :=
    preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology hF
  have : PreservesLimitsOfShape (Discrete 𝒰.I₀) F :=
    preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology hF
  conv_rhs => rw [← Presieve.isSheafFor_sigmaDesc_iff]
  congr!
  rw [Scheme.Cover.ofArrows_sigma]

variable (P : MorphismProperty Scheme.{u})

lemma zariskiTopology_le_propqcTopology [P.IsMultiplicative] [IsZariskiLocalAtSource P] :
    zariskiTopology ≤ propqcTopology P := by
  apply Precoverage.toGrothendieck_mono
  rw [le_inf_iff]
  refine ⟨?_, ?_⟩
  · apply zariskiPrecoverage_le_qcPrecoverage
  · rw [precoverage, precoverage]
    gcongr
    apply MorphismProperty.precoverage_monotone
    intro X Y f hf
    apply IsZariskiLocalAtSource.of_isOpenImmersion

open Opposite

@[simps!]
noncomputable
def Scheme.affineCover' (X : Scheme.{u}) : X.OpenCover :=
  .mkOfCovers X.affineOpens (fun i ↦ i.1) (fun i ↦ i.1.ι) fun x ↦ by
    obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ ⊤ from trivial)
    exact ⟨⟨U, hU⟩, ⟨x, hx⟩, rfl⟩

variable {P} [P.IsStableUnderBaseChange]

lemma Scheme.Cover.Hom.isSheafFor {F : Scheme.{u}ᵒᵖ ⥤ Type*} {S : Scheme.{u}}
    {𝒰 𝒱 : S.Cover (precoverage P)}
    (f : 𝒰 ⟶ 𝒱)
    (H₁ : Presieve.IsSheafFor F (.ofArrows _ 𝒰.f))
    (H₂ : ∀ {X : Scheme.{u}} (f : X ⟶ S),
      Presieve.IsSeparatedFor F (.ofArrows (𝒰.pullback₂ f).X (𝒰.pullback₂ f).f)) :
    Presieve.IsSheafFor F (.ofArrows 𝒱.X 𝒱.f) := by
  rw [Presieve.isSheafFor_iff_generate]
  apply Presieve.isSheafFor_subsieve_aux (S := .generate (.ofArrows 𝒰.X 𝒰.f))
  · change Sieve.generate _ ≤ Sieve.generate _
    rw [Sieve.generate_le_iff]
    rintro - - ⟨i⟩
    rw [← f.w₀]
    exact ⟨_, f.h₀ i, 𝒱.f _, ⟨_⟩, rfl⟩
  · rwa [← Presieve.isSheafFor_iff_generate]
  · intro Y f hf
    rw [← Sieve.pullbackArrows_comm, ← Presieve.isSeparatedFor_iff_generate]
    rw [← Presieve.ofArrows_pullback]
    apply H₂

instance {S : Scheme.{u}} (𝒰 : S.AffineCover P) (i : 𝒰.I₀) : IsAffine (𝒰.cover.X i) :=
  inferInstanceAs <| IsAffine (Spec _)

instance {S : Scheme.{u}} [IsAffine S] (𝒰 : S.AffineCover P) [Finite 𝒰.I₀] :
    QuasiCompactCover 𝒰.cover.toPreZeroHypercover :=
  haveI : Finite 𝒰.cover.I₀ := ‹_›
  .of_finite

/-- A pre-sheaf is a sheaf for the `P`-qc topology if and only if it is a sheaf
for the Zariski topology and satisfies the sheaf property for all single object coverings
`{ f : Spec S ⟶ Spec R }` where `f` satisifies `P`. -/
@[stacks 022H]
nonrec lemma isSheaf_propqcTopology_iff [P.IsMultiplicative] (F : Scheme.{u}ᵒᵖ ⥤ Type*)
    [IsZariskiLocalAtSource P] :
    Presieve.IsSheaf (propqcTopology P) F ↔
      Presieve.IsSheaf Scheme.zariskiTopology F ∧
        ∀ {R S : CommRingCat.{u}} (f : R ⟶ S), P (Spec.map f) → Surjective (Spec.map f) →
          Presieve.IsSheafFor F (.singleton (Spec.map f)) := by
  refine ⟨fun hF ↦ ⟨?_, fun {R S} f hf hs ↦ ?_⟩, fun ⟨hzar, hff⟩ ↦ ?_⟩
  · exact Presieve.isSheaf_of_le _ (zariskiTopology_le_propqcTopology P) hF
  · apply hF.isSheafFor
    rw [← Hom.presieve₀_cover _ hf]
    exact Cover.generate_ofArrows_mem_propqcTopology _
  · rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange_of_small.{u}]
    intro T (𝒰 : Scheme.Cover _ _)
    wlog hT : ∃ (R : CommRingCat.{u}), T = Spec R generalizing T
    · let 𝒱 : T.OpenCover := T.affineCover
      have h (j : T.affineCover.I₀) : Presieve.IsSheafFor F
          (.ofArrows (𝒰.pullback₂ (𝒱.f j)).X (𝒰.pullback₂ (𝒱.f j)).f) :=
        this _ ⟨_, rfl⟩
      refine .of_isSheafFor_pullback' F (.ofArrows 𝒱.X 𝒱.f) _ ?_ ?_ ?_ ?_
      · exact hzar.isSheafFor _ _ 𝒱.mem_grothendieckTopology
      · intro Y f
        refine (hzar.isSheafFor _ _ ?_).isSeparatedFor
        rw [Sieve.generate_sieve, ← Sieve.pullbackArrows_comm,
          ← PreZeroHypercover.presieve₀_pullback₁]
        exact Scheme.Cover.mem_grothendieckTopology (𝒱.pullback₂ f)
      · rintro - - - - ⟨i⟩ ⟨j⟩
        use .ofArrows (pullback (𝒱.f i) (𝒱.f j)).affineCover.X
          (pullback (𝒱.f i) (𝒱.f j)).affineCover.f
        refine ⟨(hzar.isSheafFor _ _ <| Cover.mem_grothendieckTopology _).isSeparatedFor, ?_⟩
        · rintro - - ⟨k⟩
          rw [← Sieve.pullbackArrows_comm, ← Presieve.isSeparatedFor_iff_generate]
          apply Presieve.IsSheafFor.isSeparatedFor
          rw [← Presieve.ofArrows_pullback]
          exact this (𝒰.pullback₂ _) ⟨_, rfl⟩
      · rintro - - ⟨i⟩
        rw [← Sieve.pullbackArrows_comm, ← Presieve.ofArrows_pullback,
          ← Presieve.isSheafFor_iff_generate]
        exact this (𝒰.pullback₂ (𝒱.f i)) ⟨_, rfl⟩
    obtain ⟨R, rfl⟩ := hT
    wlog h𝒰 : (∀ i, IsAffine (𝒰.X i)) ∧ Finite 𝒰.I₀ generalizing R 𝒰
    · obtain ⟨𝒱, f, hfin, ho⟩ := QuasiCompactCover.exists_hom 𝒰.forgetQc
      have H (V : Scheme.{u}) (f : V ⟶ Spec R) : Presieve.IsSheafFor F
          (.ofArrows (𝒱.cover.pullback₂ f).X (𝒱.cover.pullback₂ f).f) := by
        let 𝒰V := V.affineCover
        refine .of_isSheafFor_pullback' F (.ofArrows 𝒰V.X 𝒰V.f) _ ?_ ?_ ?_ ?_
        · exact hzar.isSheafFor _ _ 𝒰V.mem_grothendieckTopology
        · intro Y f
          refine (hzar.isSheafFor _ _ ?_).isSeparatedFor
          rw [Sieve.generate_sieve, ← Sieve.pullbackArrows_comm,
            ← PreZeroHypercover.presieve₀_pullback₁]
          exact Scheme.Cover.mem_grothendieckTopology (𝒰V.pullback₂ f)
        · rintro - - - - ⟨i⟩ ⟨j⟩
          refine ⟨.ofArrows _ (pullback (𝒰V.f i) (𝒰V.f j)).affineCover.f, ?_, ?_⟩
          · exact hzar.isSheafFor _ _ (Cover.mem_grothendieckTopology _) |>.isSeparatedFor
          · rintro - - ⟨k⟩
            rw [← Sieve.pullbackArrows_comm, ← Presieve.ofArrows_pullback,
              ← Presieve.isSeparatedFor_iff_generate]
            refine (this _ (.ofQuasiCompactCover ((𝒱.cover.pullback₂ f).pullback₂ _)
                (qc := by dsimp; infer_instance))
              ⟨fun l ↦ ?_, hfin⟩).isSeparatedFor
            exact .of_isIso (pullbackLeftPullbackSndIso (𝒱.f l) f _).hom
        · rintro - - ⟨i⟩
          rw [← Sieve.pullbackArrows_comm, ← Presieve.ofArrows_pullback,
            ← Presieve.isSheafFor_iff_generate]
          let 𝒰' := (𝒱.cover.pullback₂ f).pullback₂ (𝒰V.f i)
          refine this _ (.ofQuasiCompactCover 𝒰' (qc := by dsimp [𝒰']; infer_instance))
            ⟨fun j ↦ .of_isIso (pullbackLeftPullbackSndIso (𝒱.f j) f (𝒰V.f i)).hom, hfin⟩
      refine Scheme.Cover.Hom.isSheafFor f ?_ fun f ↦ (H _ f).isSeparatedFor
      exact this _ (.ofQuasiCompactCover 𝒱.cover)
        ⟨fun i ↦ inferInstanceAs <| IsAffine (Spec _), hfin⟩
    obtain ⟨_, _⟩ := h𝒰
    let 𝒰' := 𝒰.forgetQc.sigma
    rw [← Scheme.Cover.forgetQc_toPreZeroHypercover,
      ← Scheme.Cover.isSheafFor_sigma_iff hzar, Presieve.ofArrows_of_unique]
    have : IsAffine (𝒰.forgetQc.sigma.X default) := by dsimp; infer_instance
    let f : Spec _ ⟶ Spec R := (𝒰.forgetQc.sigma.X default).isoSpec.inv ≫ 𝒰.forgetQc.sigma.f default
    obtain ⟨φ, hφ⟩ := Spec.map_surjective f
    rw [isSheafFor_singleton_iff_of_iso _ (Spec.map φ)
      (𝒰.forgetQc.sigma.X default).isoSpec (by simp [hφ, f])]
    refine hff _ ?_ ?_
    · simpa only [hφ, f] using IsZariskiLocalAtSource.comp (𝒰.forgetQc.sigma.map_prop _) _
    · simp only [hφ, f, Cover.sigma_I₀, PUnit.default_eq_unit, Cover.sigma_X, Cover.sigma_f, f]
      have : Surjective (Sigma.desc 𝒰.f) := inferInstanceAs <| Surjective (Sigma.desc 𝒰.forgetQc.f)
      infer_instance

end AlgebraicGeometry
