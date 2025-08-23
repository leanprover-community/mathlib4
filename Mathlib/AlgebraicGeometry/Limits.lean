/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# (Co)Limits of Schemes

We construct various limits and colimits in the category of schemes.

* The existence of fibred products was shown in `Mathlib/AlgebraicGeometry/Pullbacks.lean`.
* `Spec ℤ` is the terminal object.
* The preceding two results imply that `Scheme` has all finite limits.
* The empty scheme is the (strict) initial object.
* The disjoint union is the coproduct of a family of schemes, and the forgetful functor to
  `LocallyRingedSpace` and `TopCat` preserves them.

## TODO

* Spec preserves finite coproducts.

-/

suppress_compilation


universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

attribute [local instance] Opposite.small

namespace AlgebraicGeometry

/-- `Spec ℤ` is the terminal object in the category of schemes. -/
noncomputable def specZIsTerminal : IsTerminal Spec(ℤ) :=
  @IsTerminal.isTerminalObj _ _ _ _ Scheme.Spec _ inferInstance
    (terminalOpOfInitial CommRingCat.zIsInitial)

/-- `Spec ℤ` is the terminal object in the category of schemes. -/
noncomputable def specULiftZIsTerminal : IsTerminal Spec(ULift.{u} ℤ) :=
  @IsTerminal.isTerminalObj _ _ _ _ Scheme.Spec _ inferInstance
    (terminalOpOfInitial CommRingCat.isInitial)

instance : HasTerminal Scheme :=
  hasTerminal_of_hasTerminal_of_preservesLimit Scheme.Spec

instance : IsAffine (⊤_ Scheme.{u}) :=
  .of_isIso (PreservesTerminal.iso Scheme.Spec).inv

instance : HasFiniteLimits Scheme :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

instance (X : Scheme.{u}) : X.Over (⊤_ _) := ⟨terminal.from _⟩
instance {X Y : Scheme.{u}} [X.Over (⊤_ Scheme)] [Y.Over (⊤_ Scheme)] (f : X ⟶ Y) :
    @Scheme.Hom.IsOver _ _ f (⊤_ Scheme) ‹_› ‹_› := ⟨Subsingleton.elim _ _⟩

instance {X : Scheme} : Subsingleton (X.Over (⊤_ Scheme)) :=
  ⟨fun ⟨a⟩ ⟨b⟩ ↦ by simp [Subsingleton.elim a b]⟩

section Initial

/-- The map from the empty scheme. -/
@[simps]
def Scheme.emptyTo (X : Scheme.{u}) : ∅ ⟶ X :=
  ⟨{  base := TopCat.ofHom ⟨fun x => PEmpty.elim x, by fun_prop⟩
      c := { app := fun _ => CommRingCat.punitIsTerminal.from _ } }, fun x => PEmpty.elim x⟩

@[ext]
theorem Scheme.empty_ext {X : Scheme.{u}} (f g : ∅ ⟶ X) : f = g :=
  Scheme.Hom.ext' (Subsingleton.elim (α := ∅ ⟶ _) _ _)

theorem Scheme.eq_emptyTo {X : Scheme.{u}} (f : ∅ ⟶ X) : f = Scheme.emptyTo X :=
  Scheme.empty_ext f (Scheme.emptyTo X)

instance Scheme.hom_unique_of_empty_source (X : Scheme.{u}) : Unique (∅ ⟶ X) :=
  ⟨⟨Scheme.emptyTo _⟩, fun _ => Scheme.empty_ext _ _⟩

/-- The empty scheme is the initial object in the category of schemes. -/
def emptyIsInitial : IsInitial (∅ : Scheme.{u}) :=
  IsInitial.ofUnique _

@[simp]
theorem emptyIsInitial_to : emptyIsInitial.to = Scheme.emptyTo :=
  rfl

instance : IsEmpty (∅ : Scheme.{u}) :=
  show IsEmpty PEmpty by infer_instance

instance spec_punit_isEmpty : IsEmpty Spec(PUnit.{u+1}) :=
  inferInstanceAs <| IsEmpty (PrimeSpectrum PUnit)

instance (priority := 100) isOpenImmersion_of_isEmpty {X Y : Scheme} (f : X ⟶ Y)
    [IsEmpty X] : IsOpenImmersion f := by
  apply (config := { allowSynthFailures := true }) IsOpenImmersion.of_stalk_iso
  · exact .of_isEmpty (X := X) _
  · intro (i : X); exact isEmptyElim i

instance (priority := 100) isIso_of_isEmpty {X Y : Scheme} (f : X ⟶ Y) [IsEmpty Y] :
    IsIso f := by
  haveI : IsEmpty X := f.base.hom.1.isEmpty
  have : Epi f.base := by
    rw [TopCat.epi_iff_surjective]; rintro (x : Y)
    exact isEmptyElim x
  apply IsOpenImmersion.to_iso

/-- A scheme is initial if its underlying space is empty . -/
noncomputable def isInitialOfIsEmpty {X : Scheme} [IsEmpty X] : IsInitial X :=
  emptyIsInitial.ofIso (asIso <| emptyIsInitial.to _)

/-- `Spec 0` is the initial object in the category of schemes. -/
noncomputable def specPunitIsInitial : IsInitial Spec(PUnit.{u+1}) :=
  emptyIsInitial.ofIso (asIso <| emptyIsInitial.to _)

instance (priority := 100) isAffine_of_isEmpty {X : Scheme} [IsEmpty X] : IsAffine X :=
  .of_isIso (inv (emptyIsInitial.to X) ≫ emptyIsInitial.to Spec(PUnit))

instance : HasInitial Scheme.{u} :=
  hasInitial_of_unique ∅

instance initial_isEmpty : IsEmpty (⊥_ Scheme) :=
  ⟨fun x => ((initial.to Scheme.empty :).base x).elim⟩

theorem isAffineOpen_bot (X : Scheme) : IsAffineOpen (⊥ : X.Opens) :=
  @isAffine_of_isEmpty _ (inferInstanceAs (IsEmpty (∅ : Set X)))

instance : HasStrictInitialObjects Scheme :=
  hasStrictInitialObjects_of_initial_is_strict fun A f => by infer_instance

instance {X : Scheme} [IsEmpty X] (U : X.Opens) : Subsingleton Γ(X, U) := by
  obtain rfl : U = ⊥ := Subsingleton.elim _ _; infer_instance

-- This is also true for schemes with two points.
-- But there are non-affine schemes with three points.
instance (priority := low) {X : Scheme.{u}} [Subsingleton X] : IsAffine X := by
  cases isEmpty_or_nonempty X with
  | inl h => infer_instance
  | inr h =>
  obtain ⟨x⟩ := h
  obtain ⟨_, ⟨U, hU : IsAffine _, rfl⟩, hxU, -⟩ :=
    (isBasis_affine_open X).exists_subset_of_mem_open (a := x) (by trivial) isOpen_univ
  obtain rfl : U = ⊤ := by ext y; simpa [Subsingleton.elim y x]
  exact .of_isIso (Scheme.topIso X).inv

end Initial

section Coproduct

variable {ι : Type u} (f : ι → Scheme.{u})

variable {σ : Type v} (g : σ → Scheme.{u})

noncomputable
instance [Small.{u} σ] :
    CreatesColimitsOfShape (Discrete σ) Scheme.forgetToLocallyRingedSpace.{u} where

instance [Small.{u} σ] : PreservesColimitsOfShape (Discrete σ) Scheme.forgetToTop.{u} :=
  inferInstanceAs (PreservesColimitsOfShape (Discrete σ) (Scheme.forgetToLocallyRingedSpace ⋙
      LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget CommRingCat))

instance [Small.{u} σ] : HasColimitsOfShape (Discrete σ) Scheme.{u} :=
  ⟨fun _ ↦ hasColimit_of_created _ Scheme.forgetToLocallyRingedSpace⟩

lemma sigmaι_eq_iff (i j : ι) (x y) :
    (Sigma.ι f i).base x = (Sigma.ι f j).base y ↔
      (Sigma.mk i x : Σ i, f i) = Sigma.mk j y := by
  refine (Scheme.IsLocallyDirected.ι_eq_ι_iff _).trans ⟨?_, ?_⟩
  · rintro ⟨k, ⟨⟨⟨⟩⟩⟩, ⟨⟨⟨⟩⟩⟩, x, rfl, rfl⟩; simp
  · simp only [Discrete.functor_obj_eq_as, Sigma.mk.injEq]
    rintro ⟨rfl, e⟩
    obtain rfl := (heq_eq_eq x y).mp e
    exact ⟨⟨i⟩, 𝟙 _, 𝟙 _, x, by simp⟩

/-- The images of each component in the coproduct is disjoint. -/
lemma disjoint_opensRange_sigmaι (i j : ι) (h : i ≠ j) :
    Disjoint (Sigma.ι f i).opensRange (Sigma.ι f j).opensRange := by
  intro U hU hU' x hx
  obtain ⟨x, rfl⟩ := hU hx
  obtain ⟨y, hy⟩ := hU' hx
  obtain ⟨rfl⟩ := (sigmaι_eq_iff _ _ _ _ _).mp hy
  cases h rfl

/-- The cover of `∐ X` by the `Xᵢ`. -/
@[simps!]
noncomputable def sigmaOpenCover [Small.{u} σ] : (∐ g).OpenCover :=
  (Scheme.IsLocallyDirected.openCover (Discrete.functor g)).copy σ g (Sigma.ι _)
  (discreteEquiv.symm) (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- The underlying topological space of the coproduct is homeomorphic to the disjoint union. -/
noncomputable
def sigmaMk : (Σ i, f i) ≃ₜ (∐ f :) :=
  TopCat.homeoOfIso ((colimit.isoColimitCocone ⟨_, TopCat.sigmaCofanIsColimit _⟩).symm ≪≫
    (PreservesCoproduct.iso Scheme.forgetToTop f).symm)

@[simp]
lemma sigmaMk_mk (i) (x : f i) :
    sigmaMk f (.mk i x) = (Sigma.ι f i).base x := by
  change ((TopCat.sigmaCofan (fun x ↦ (f x).toTopCat)).inj i ≫
    (colimit.isoColimitCocone ⟨_, TopCat.sigmaCofanIsColimit _⟩).inv ≫ _) x =
      Scheme.forgetToTop.map (Sigma.ι f i) x
  congr 2
  refine (colimit.isoColimitCocone_ι_inv_assoc ⟨_, TopCat.sigmaCofanIsColimit _⟩ _ _).trans ?_
  exact ι_comp_sigmaComparison Scheme.forgetToTop _ _

open scoped Function in
private lemma isOpenImmersion_sigmaDesc_aux
    {X : Scheme.{u}} (α : ∀ i, f i ⟶ X) [∀ i, IsOpenImmersion (α i)]
    (hα : Pairwise (Disjoint on (Set.range <| α · |>.base))) :
    IsOpenImmersion (Sigma.desc α) := by
  rw [IsOpenImmersion.iff_stalk_iso]
  constructor
  · suffices Topology.IsOpenEmbedding ((Sigma.desc α).base ∘ sigmaMk f) by
      convert this.comp (sigmaMk f).symm.isOpenEmbedding; ext; simp
    refine .of_continuous_injective_isOpenMap ?_ ?_ ?_
    · fun_prop
    · rintro ⟨ix, x⟩ ⟨iy, y⟩ e
      have : (α ix).base x = (α iy).base y := by
        simpa [← Scheme.comp_base_apply] using e
      obtain rfl : ix = iy := by
        by_contra h
        exact Set.disjoint_iff_forall_ne.mp (hα h) ⟨x, rfl⟩ ⟨y, this.symm⟩ rfl
      rw [(α ix).isOpenEmbedding.injective this]
    · rw [isOpenMap_sigma]
      intro i
      simpa [← Scheme.comp_base_apply] using (α i).isOpenEmbedding.isOpenMap
  · intro x
    have ⟨y, hy⟩ := (Scheme.IsLocallyDirected.openCover (Discrete.functor f)).covers x
    rw [← hy]
    refine IsIso.of_isIso_fac_right
      (g := ((Scheme.IsLocallyDirected.openCover (Discrete.functor f)).map _).stalkMap y)
      (h := (X.presheaf.stalkCongr (.of_eq ?_)).hom ≫ (α _).stalkMap _) ?_
    · simp [← Scheme.comp_base_apply]
    · simp [← Scheme.stalkMap_comp, Scheme.stalkMap_congr_hom _ _ (colimit.ι_desc _ _)]

open scoped Function in
lemma isOpenImmersion_sigmaDesc [Small.{u} σ]
    {X : Scheme.{u}} (α : ∀ i, g i ⟶ X) [∀ i, IsOpenImmersion (α i)]
    (hα : Pairwise (Disjoint on (Set.range <| α · |>.base))) :
    IsOpenImmersion (Sigma.desc α) := by
  obtain ⟨ι, ⟨e⟩⟩ := Small.equiv_small (α := σ)
  convert IsOpenImmersion.comp ((Sigma.reindex e.symm g).inv) (Sigma.desc fun i ↦ α _)
  · refine Sigma.hom_ext _ _ fun i ↦ ?_
    obtain ⟨i, rfl⟩ := e.symm.surjective i
    simp
  · apply isOpenImmersion_sigmaDesc_aux
    intro i j hij
    exact hα (fun h ↦ hij (e.symm.injective h))

open scoped Function in
/-- `S` is the disjoint union of `Xᵢ` if the `Xᵢ` are covering, pairwise disjoint open subschemes
of `S`. -/
lemma nonempty_isColimit_cofanMk_of [Small.{u} σ]
    {X : σ → Scheme.{u}} {S : Scheme.{u}} (f : ∀ i, X i ⟶ S) [∀ i, IsOpenImmersion (f i)]
    (hcov : ⨆ i, (f i).opensRange = ⊤) (hdisj : Pairwise (Disjoint on (f · |>.opensRange))) :
    Nonempty (IsColimit <| Cofan.mk S f) := by
  have : IsOpenImmersion (Sigma.desc f) := by
    refine isOpenImmersion_sigmaDesc _ _ (fun i j hij ↦ ?_)
    simpa [Function.onFun_apply, disjoint_iff, Opens.ext_iff] using hdisj hij
  simp only [← Cofan.isColimit_iff_isIso_sigmaDesc (Cofan.mk S f), cofan_mk_inj, Cofan.mk_pt]
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  rw [eq_top_iff]
  intro x hx
  have : x ∈ ⨆ i, (f i).opensRange := by rwa [hcov]
  obtain ⟨i, y, rfl⟩ := by simpa only [Opens.iSup_mk, Opens.mem_mk, Set.mem_iUnion] using this
  use Sigma.ι X i |>.base y
  simp [← Scheme.comp_base_apply]

variable (X Y : Scheme.{u})

/-- (Implementation Detail)
The coproduct of the two schemes is given by indexed coproducts over `WalkingPair`. -/
noncomputable
def coprodIsoSigma : X ⨿ Y ≅ ∐ fun i : ULift.{u} WalkingPair ↦ i.1.casesOn X Y :=
  Sigma.whiskerEquiv Equiv.ulift.symm (fun _ ↦ by exact Iso.refl _)

lemma ι_left_coprodIsoSigma_inv : Sigma.ι _ ⟨.left⟩ ≫ (coprodIsoSigma X Y).inv = coprod.inl :=
  Sigma.ι_comp_map' _ _ _

lemma ι_right_coprodIsoSigma_inv : Sigma.ι _ ⟨.right⟩ ≫ (coprodIsoSigma X Y).inv = coprod.inr :=
  Sigma.ι_comp_map' _ _ _

instance : IsOpenImmersion (coprod.inl : X ⟶ X ⨿ Y) := by
  rw [← ι_left_coprodIsoSigma_inv]; infer_instance

instance : IsOpenImmersion (coprod.inr : Y ⟶ X ⨿ Y) := by
  rw [← ι_right_coprodIsoSigma_inv]; infer_instance

lemma isCompl_range_inl_inr :
    IsCompl (Set.range (coprod.inl : X ⟶ X ⨿ Y).base)
      (Set.range (coprod.inr : Y ⟶ X ⨿ Y).base) :=
  ((TopCat.binaryCofan_isColimit_iff _).mp
    ⟨mapIsColimitOfPreservesOfIsColimit Scheme.forgetToTop.{u} _ _ (coprodIsCoprod X Y)⟩).2.2

lemma isCompl_opensRange_inl_inr :
    IsCompl (coprod.inl : X ⟶ X ⨿ Y).opensRange (coprod.inr : Y ⟶ X ⨿ Y).opensRange := by
  convert isCompl_range_inl_inr X Y
  simp only [isCompl_iff, disjoint_iff, codisjoint_iff, ← TopologicalSpace.Opens.coe_inj]
  rfl

/-- The underlying topological space of the coproduct is homeomorphic to the disjoint union -/
noncomputable
def coprodMk : X ⊕ Y ≃ₜ (X ⨿ Y : Scheme.{u}) :=
  TopCat.homeoOfIso ((colimit.isoColimitCocone ⟨_, TopCat.binaryCofanIsColimit _ _⟩).symm ≪≫
    PreservesColimitPair.iso Scheme.forgetToTop X Y)

@[simp]
lemma coprodMk_inl (x : X) :
    coprodMk X Y (.inl x) = (coprod.inl : X ⟶ X ⨿ Y).base x := by
  change ((TopCat.binaryCofan X Y).inl ≫
    (colimit.isoColimitCocone ⟨_, TopCat.binaryCofanIsColimit _ _⟩).inv ≫ _) x =
      Scheme.forgetToTop.map coprod.inl x
  congr 2
  refine (colimit.isoColimitCocone_ι_inv_assoc ⟨_, TopCat.binaryCofanIsColimit _ _⟩ _ _).trans ?_
  exact coprodComparison_inl Scheme.forgetToTop

@[simp]
lemma coprodMk_inr (x : Y) :
    coprodMk X Y (.inr x) = (coprod.inr : Y ⟶ X ⨿ Y).base x := by
  change ((TopCat.binaryCofan X Y).inr ≫
    (colimit.isoColimitCocone ⟨_, TopCat.binaryCofanIsColimit _ _⟩).inv ≫ _) x =
      Scheme.forgetToTop.map coprod.inr x
  congr 2
  refine (colimit.isoColimitCocone_ι_inv_assoc ⟨_, TopCat.binaryCofanIsColimit _ _⟩ _ _).trans ?_
  exact coprodComparison_inr Scheme.forgetToTop

/-- The open cover of the coproduct of two schemes. -/
noncomputable
def coprodOpenCover.{w} : (X ⨿ Y).OpenCover where
  J := PUnit.{w + 1} ⊕ PUnit.{w + 1}
  obj x := x.elim (fun _ ↦ X) (fun _ ↦ Y)
  map x := x.rec (fun _ ↦ coprod.inl) (fun _ ↦ coprod.inr)
  f x := ((coprodMk X Y).symm x).elim (fun _ ↦ Sum.inl .unit) (fun _ ↦ Sum.inr .unit)
  covers x := by
    obtain ⟨x, rfl⟩ := (coprodMk X Y).surjective x
    simp only [Sum.elim_inl, Sum.elim_inr, Set.mem_range]
    rw [Homeomorph.symm_apply_apply]
    obtain (x | x) := x
    · simp only [Sum.elim_inl, coprodMk_inl, exists_apply_eq_apply]
    · simp only [Sum.elim_inr, coprodMk_inr, exists_apply_eq_apply]
  map_prop x := x.rec (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)

/-- If `X` and `Y` are open disjoint and covering open subschemes of `S`,
`S` is the disjoint union of `X` and `Y`. -/
lemma nonempty_isColimit_binaryCofanMk_of_isCompl {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) [IsOpenImmersion f] [IsOpenImmersion g]
    (hf : IsCompl f.opensRange g.opensRange) :
    Nonempty (IsColimit <| BinaryCofan.mk f g) := by
  let c' : Cofan fun j ↦ (WalkingPair.casesOn j X Y : Scheme.{u}) :=
    .mk S fun j ↦ WalkingPair.casesOn j f g
  let i : BinaryCofan.mk f g ≅ c' := Cofan.ext (Iso.refl _) (by rintro (b|b) <;> rfl)
  refine ⟨IsColimit.ofIsoColimit (Nonempty.some ?_) i.symm⟩
  let fi (j : WalkingPair) : WalkingPair.casesOn j X Y ⟶ S := WalkingPair.casesOn j f g
  convert nonempty_isColimit_cofanMk_of fi _ _
  · intro i
    cases i <;> (simp [fi]; infer_instance)
  · simpa [← WalkingPair.equivBool.symm.iSup_comp, iSup_bool_eq, ← codisjoint_iff] using hf.2
  · intro i j hij
    match i, j with
    | .left, .right => simpa [fi] using hf.1
    | .right, .left => simpa [fi] using hf.1.symm

variable (R S : Type u) [CommRing R] [CommRing S]

/-- The map `Spec R ⨿ Spec S ⟶ Spec (R × S)`.
This is an isomorphism as witnessed by an `IsIso` instance provided below. -/
noncomputable
def coprodSpec : Spec(R) ⨿ Spec(S) ⟶ Spec(R × S) :=
  coprod.desc (Spec.map (CommRingCat.ofHom <| RingHom.fst _ _))
    (Spec.map (CommRingCat.ofHom <| RingHom.snd _ _))

@[simp, reassoc]
lemma coprodSpec_inl : coprod.inl ≫ coprodSpec R S =
    Spec.map (CommRingCat.ofHom <| RingHom.fst R S) :=
  coprod.inl_desc _ _

@[simp, reassoc]
lemma coprodSpec_inr : coprod.inr ≫ coprodSpec R S =
    Spec.map (CommRingCat.ofHom <| RingHom.snd R S) :=
  coprod.inr_desc _ _

lemma coprodSpec_coprodMk (x) :
    (coprodSpec R S).base (coprodMk _ _ x) = (PrimeSpectrum.primeSpectrumProd R S).symm x := by
  apply PrimeSpectrum.ext
  obtain (x | x) := x <;>
    simp only [coprodMk_inl, coprodMk_inr, ← Scheme.comp_base_apply,
      coprodSpec, coprod.inl_desc, coprod.inr_desc]
  · change Ideal.comap _ _ = x.asIdeal.prod ⊤
    ext; simp [Ideal.prod, CommRingCat.ofHom]
  · change Ideal.comap _ _ = Ideal.prod ⊤ x.asIdeal
    ext; simp [Ideal.prod, CommRingCat.ofHom]

lemma coprodSpec_apply (x) :
    (coprodSpec R S).base x =
      (PrimeSpectrum.primeSpectrumProd R S).symm ((coprodMk Spec(R) Spec(S)).symm x) := by
  rw [← coprodSpec_coprodMk, Homeomorph.apply_symm_apply]

lemma isIso_stalkMap_coprodSpec (x) :
    IsIso ((coprodSpec R S).stalkMap x) := by
  obtain ⟨x | x, rfl⟩ := (coprodMk _ _).surjective x
  · have := Scheme.stalkMap_comp coprod.inl (coprodSpec R S) x
    rw [← IsIso.comp_inv_eq, Scheme.stalkMap_congr_hom _ (Spec.map _) (coprodSpec_inl R S)] at this
    rw [coprodMk_inl, ← this]
    letI := (RingHom.fst R S).toAlgebra
    have := IsLocalization.away_fst (R := R) (S := S)
    have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (RingHom.fst R S))) :=
      IsOpenImmersion.of_isLocalization (1, 0)
    infer_instance
  · have := Scheme.stalkMap_comp coprod.inr (coprodSpec R S) x
    rw [← IsIso.comp_inv_eq, Scheme.stalkMap_congr_hom _ (Spec.map _) (coprodSpec_inr R S)] at this
    rw [coprodMk_inr, ← this]
    letI := (RingHom.snd R S).toAlgebra
    have := IsLocalization.away_snd (R := R) (S := S)
    have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (RingHom.snd R S))) :=
      IsOpenImmersion.of_isLocalization (0, 1)
    infer_instance

instance : IsIso (coprodSpec R S) := by
  rw [isIso_iff_stalk_iso]
  refine ⟨?_, isIso_stalkMap_coprodSpec R S⟩
  convert_to IsIso (TopCat.isoOfHomeo (X := Spec(R × S)) <|
    PrimeSpectrum.primeSpectrumProdHomeo.trans (coprodMk Spec(R) Spec(S))).inv
  · ext x; exact coprodSpec_apply R S x
  · infer_instance

instance (R S : CommRingCat.{u}ᵒᵖ) : IsIso (coprodComparison Scheme.Spec R S) := by
  obtain ⟨R⟩ := R; obtain ⟨S⟩ := S
  have : coprodComparison Scheme.Spec (.op R) (.op S) ≫ (Spec.map
    ((limit.isoLimitCone ⟨_, CommRingCat.prodFanIsLimit R S⟩).inv ≫
      (opProdIsoCoprod R S).unop.inv)) = coprodSpec R S := by
    ext1
    · rw [coprodComparison_inl_assoc, coprodSpec, coprod.inl_desc, Scheme.Spec_map,
        ← Spec.map_comp, Category.assoc, Iso.unop_inv, opProdIsoCoprod_inv_inl,
        limit.isoLimitCone_inv_π]
      rfl
    · rw [coprodComparison_inr_assoc, coprodSpec, coprod.inr_desc, Scheme.Spec_map,
        ← Spec.map_comp, Category.assoc, Iso.unop_inv, opProdIsoCoprod_inv_inr,
        limit.isoLimitCone_inv_π]
      rfl
  rw [(IsIso.eq_comp_inv _).mpr this]
  infer_instance

instance : PreservesColimitsOfShape (Discrete WalkingPair) Scheme.Spec.{u} :=
  ⟨fun {_} ↦
    have (X Y : CommRingCat.{u}ᵒᵖ) := PreservesColimitPair.of_iso_coprod_comparison Scheme.Spec X Y
    preservesColimit_of_iso_diagram _ (diagramIsoPair _).symm⟩

instance : PreservesColimitsOfShape (Discrete PEmpty.{1}) Scheme.Spec.{u} := by
  have : IsEmpty (Scheme.Spec.obj (⊥_ CommRingCatᵒᵖ)) :=
    @Function.isEmpty _ _ spec_punit_isEmpty (Scheme.Spec.mapIso
      (initialIsoIsInitial (initialOpOfTerminal CommRingCat.punitIsTerminal))).hom.base
  have := preservesInitial_of_iso Scheme.Spec (asIso (initial.to _))
  exact preservesColimitsOfShape_pempty_of_preservesInitial _

instance {J : Type*} [Finite J] : PreservesColimitsOfShape (Discrete J) Scheme.Spec.{u} :=
  preservesFiniteCoproductsOfPreservesBinaryAndInitial _ _

/-- The canonical map `∐ Spec Rᵢ ⟶ Spec (Π Rᵢ)`.
This is an isomorphism when the product is finite. -/
noncomputable
def sigmaSpec (R : ι → CommRingCat) : (∐ fun i ↦ Spec (R i)) ⟶ Spec(Π i, R i) :=
  Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ i)))

@[reassoc (attr := simp)]
lemma ι_sigmaSpec (R : ι → CommRingCat) (i) :
    Sigma.ι _ i ≫ sigmaSpec R = Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ i)) :=
  Sigma.ι_desc _ _

instance (i) (R : ι → Type _) [∀ i, CommRing (R i)] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (R ·) i))) := by
  classical
  letI := (Pi.evalRingHom R i).toAlgebra
  have : IsLocalization.Away (Function.update (β := R) 0 i 1) (R i) := by
    apply IsLocalization.away_of_isIdempotentElem_of_mul
    · ext j; by_cases h : j = i <;> aesop
    · intro x y
      constructor
      · intro e; ext j; by_cases h : j = i <;> aesop
      · intro e; simpa using congr_fun e i
    · exact Function.surjective_eval _
  exact IsOpenImmersion.of_isLocalization (Function.update 0 i 1)

instance (R : ι → CommRingCat.{u}) : IsOpenImmersion (sigmaSpec R) := by
  classical
  apply isOpenImmersion_sigmaDesc
  intro ix iy h
  refine Set.disjoint_iff_forall_ne.mpr ?_
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ e
  have : DFinsupp.single (β := (R ·)) iy 1 iy ∈ y.asIdeal :=
    (PrimeSpectrum.ext_iff.mp e).le (x := DFinsupp.single iy 1)
      (show DFinsupp.single (β := (R ·)) iy 1 ix ∈ x.asIdeal by simp [h.symm])
  simp [← Ideal.eq_top_iff_one, y.2.ne_top] at this

instance [Finite ι] (R : ι → CommRingCat.{u}) : IsIso (sigmaSpec R) := by
  have : sigmaSpec R =
      (colimit.isoColimitCocone ⟨_,
        (IsColimit.precomposeHomEquiv Discrete.natIsoFunctor.symm _).symm (isColimitOfPreserves
          Scheme.Spec (Fan.IsLimit.op (CommRingCat.piFanIsLimit R)))⟩).hom := by
    ext1
    simp; rfl
  rw [this]
  infer_instance

instance [Finite ι] [∀ i, IsAffine (f i)] : IsAffine (∐ f) :=
  .of_isIso ((Sigma.mapIso (fun i ↦ (f i).isoSpec)).hom ≫ sigmaSpec _)

instance [IsAffine X] [IsAffine Y] : IsAffine (X ⨿ Y) :=
  .of_isIso ((coprod.mapIso X.isoSpec Y.isoSpec).hom ≫ coprodSpec _ _)

end Coproduct

instance : CartesianMonoidalCategory Scheme := .ofHasFiniteProducts
instance : BraidedCategory Scheme := .ofCartesianMonoidalCategory

end AlgebraicGeometry
