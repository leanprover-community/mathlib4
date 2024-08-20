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


universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- `Spec ℤ` is the terminal object in the category of schemes. -/
noncomputable def specZIsTerminal : IsTerminal (Spec (CommRingCat.of ℤ)) :=
  @IsTerminal.isTerminalObj _ _ _ _ Scheme.Spec _ inferInstance
    (terminalOpOfInitial CommRingCat.zIsInitial)

instance : HasTerminal Scheme :=
  hasTerminal_of_hasTerminal_of_preservesLimit Scheme.Spec

instance : IsAffine (⊤_ Scheme.{u}) :=
  isAffine_of_isIso (PreservesTerminal.iso Scheme.Spec).inv

instance : HasFiniteLimits Scheme :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

section Initial

/-- The map from the empty scheme. -/
@[simps]
def Scheme.emptyTo (X : Scheme.{u}) : ∅ ⟶ X :=
  ⟨{  base := ⟨fun x => PEmpty.elim x, by fun_prop⟩
      c := { app := fun U => CommRingCat.punitIsTerminal.from _ } }, fun x => PEmpty.elim x⟩

@[ext]
theorem Scheme.empty_ext {X : Scheme.{u}} (f g : ∅ ⟶ X) : f = g :=
  -- Porting note (#11041): `ext` regression
  LocallyRingedSpace.Hom.ext <| PresheafedSpace.ext _ _ (by ext a; exact PEmpty.elim a) <|
    NatTrans.ext <| funext fun a => by aesop_cat

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

instance spec_punit_isEmpty : IsEmpty (Spec (CommRingCat.of PUnit.{u+1})) :=
  inferInstanceAs <| IsEmpty (PrimeSpectrum PUnit)

instance (priority := 100) isOpenImmersion_of_isEmpty {X Y : Scheme} (f : X ⟶ Y)
    [IsEmpty X] : IsOpenImmersion f := by
  apply (config := { allowSynthFailures := true }) IsOpenImmersion.of_stalk_iso
  · exact .of_isEmpty (X := X) _
  · intro (i : X); exact isEmptyElim i

instance (priority := 100) isIso_of_isEmpty {X Y : Scheme} (f : X ⟶ Y) [IsEmpty Y] :
    IsIso f := by
  haveI : IsEmpty X := f.1.base.1.isEmpty
  have : Epi f.1.base := by
    rw [TopCat.epi_iff_surjective]; rintro (x : Y)
    exact isEmptyElim x
  apply IsOpenImmersion.to_iso

/-- A scheme is initial if its underlying space is empty . -/
noncomputable def isInitialOfIsEmpty {X : Scheme} [IsEmpty X] : IsInitial X :=
  emptyIsInitial.ofIso (asIso <| emptyIsInitial.to _)

/-- `Spec 0` is the initial object in the category of schemes. -/
noncomputable def specPunitIsInitial : IsInitial (Spec (.of PUnit.{u+1})) :=
  emptyIsInitial.ofIso (asIso <| emptyIsInitial.to _)

instance (priority := 100) isAffine_of_isEmpty {X : Scheme} [IsEmpty X] : IsAffine X :=
  isAffine_of_isIso (inv (emptyIsInitial.to X) ≫ emptyIsInitial.to (Spec (.of PUnit)))

instance : HasInitial Scheme.{u} :=
  hasInitial_of_unique ∅

instance initial_isEmpty : IsEmpty (⊥_ Scheme) :=
  ⟨fun x => ((initial.to Scheme.empty : _).1.base x).elim⟩

theorem isAffineOpen_bot (X : Scheme) : IsAffineOpen (⊥ : X.Opens) :=
  @isAffine_of_isEmpty _ (inferInstanceAs (IsEmpty (∅ : Set X)))

instance : HasStrictInitialObjects Scheme :=
  hasStrictInitialObjects_of_initial_is_strict fun A f => by infer_instance

end Initial

section Coproduct

variable {ι : Type u} (f : ι → Scheme.{u})


/-- (Implementation Detail) The glue data associated to a disjoint union. -/
@[simps]
noncomputable
def disjointGlueData' : GlueData' Scheme where
  J := ι
  U := f
  V _ _ _ := ∅
  f _ _ _ := Scheme.emptyTo _
  t _ _ _ := 𝟙 _
  t' _ _ _ _ _ _ := Limits.pullback.fst _ _ ≫ Scheme.emptyTo _
  t_fac _ _ _ _ _ _ := emptyIsInitial.strict_hom_ext _ _
  t_inv _ _ _ := Category.comp_id _
  cocycle _ _ _ _ _ _ := (emptyIsInitial.ofStrict (pullback.fst _ _)).hom_ext _ _
  f_mono _ _ := by dsimp only; infer_instance

/-- (Implementation Detail) The glue data associated to a disjoint union. -/
@[simps! J V U f t]
noncomputable
def disjointGlueData : Scheme.GlueData where
  __ := GlueData.ofGlueData' (disjointGlueData' f)
  f_open i j := by
    dsimp only [GlueData.ofGlueData', GlueData'.f', disjointGlueData']
    split <;> infer_instance

/-- (Implementation Detail) The cofan in `LocallyRingedSpace` associated to a disjoint union. -/
noncomputable
def toLocallyRingedSpaceCoproductCofan : Cofan (Scheme.toLocallyRingedSpace ∘ f) :=
  Cofan.mk (disjointGlueData f).toLocallyRingedSpaceGlueData.glued
    (disjointGlueData f).toLocallyRingedSpaceGlueData.ι

/-- (Implementation Detail)
The cofan in `LocallyRingedSpace` associated to a disjoint union is a colimit. -/
noncomputable
def toLocallyRingedSpaceCoproductCofanIsColimit :
    IsColimit (toLocallyRingedSpaceCoproductCofan f) := by
  fapply mkCofanColimit
  · refine fun t ↦ Multicoequalizer.desc _ _ t.inj ?_
    rintro ⟨i, j⟩
    simp only [GlueData.diagram, disjointGlueData_J, disjointGlueData_V, disjointGlueData_U,
      disjointGlueData_f, disjointGlueData_t, Category.comp_id, Category.assoc,
      GlueData.mapGlueData_J, disjointGlueData_J, GlueData.mapGlueData_V,
      disjointGlueData_V, Scheme.forgetToLocallyRingedSpace_obj, GlueData.mapGlueData_U,
      disjointGlueData_U, GlueData.mapGlueData_f, disjointGlueData_f, Category.comp_id,
      Scheme.forgetToLocallyRingedSpace_map, GlueData.mapGlueData_t, disjointGlueData_t]
    split_ifs with h
    · subst h
      simp only [eqToHom_refl, ↓reduceDIte, ← Category.assoc, GlueData'.f']
      congr
    · apply Limits.IsInitial.hom_ext
      rw [if_neg h]
      exact LocallyRingedSpace.emptyIsInitial
  · exact fun _ _ ↦ Multicoequalizer.π_desc _ _ _ _ _
  · intro i m h
    apply Multicoequalizer.hom_ext _ _ _ fun j ↦ ?_
    rw [Multicoequalizer.π_desc]
    exact h j

noncomputable
instance : CreatesColimit (Discrete.functor f) Scheme.forgetToLocallyRingedSpace :=
  createsColimitOfFullyFaithfulOfIso (disjointGlueData f).gluedScheme <|
    let F : Discrete.functor f ⋙ Scheme.forgetToLocallyRingedSpace ≅
      Discrete.functor (Scheme.toLocallyRingedSpace ∘ f) := Discrete.natIsoFunctor
    have := (IsColimit.precomposeHomEquiv F _).symm (toLocallyRingedSpaceCoproductCofanIsColimit f)
    (colimit.isoColimitCocone ⟨_, this⟩).symm

noncomputable
instance : CreatesColimitsOfShape (Discrete ι) Scheme.forgetToLocallyRingedSpace := by
  constructor
  intro K
  exact createsColimitOfIsoDiagram _ (Discrete.natIsoFunctor (F := K)).symm

noncomputable
instance : PreservesColimitsOfShape (Discrete ι) Scheme.forgetToTop :=
  inferInstanceAs (PreservesColimitsOfShape (Discrete ι) (Scheme.forgetToLocallyRingedSpace ⋙
      LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget CommRingCat))

instance : HasCoproducts.{u} Scheme.{u} :=
  fun _ ↦ ⟨fun _ ↦ hasColimit_of_created _ Scheme.forgetToLocallyRingedSpace⟩

instance : HasCoproducts.{0} Scheme.{u} := has_smallest_coproducts_of_hasCoproducts

noncomputable
instance {ι : Type} : PreservesColimitsOfShape (Discrete ι) Scheme.forgetToTop :=
  preservesColimitsOfShapeOfEquiv (Discrete.equivalence Equiv.ulift : Discrete (ULift.{u} ι) ≌ _) _

noncomputable
instance {ι : Type} : PreservesColimitsOfShape (Discrete ι) Scheme.forgetToLocallyRingedSpace :=
  preservesColimitsOfShapeOfEquiv (Discrete.equivalence Equiv.ulift : Discrete (ULift.{u} ι) ≌ _) _

/-- (Implementation Detail) Coproduct of schemes is isomorphic to the disjoint union. -/
noncomputable
def sigmaIsoGlued : ∐ f ≅ (disjointGlueData f).glued :=
  Scheme.fullyFaithfulForgetToLocallyRingedSpace.preimageIso
    (PreservesCoproduct.iso _ _ ≪≫
      colimit.isoColimitCocone ⟨_, toLocallyRingedSpaceCoproductCofanIsColimit f⟩ ≪≫
        (disjointGlueData f).isoLocallyRingedSpace.symm)

@[reassoc (attr := simp)]
lemma ι_sigmaIsoGlued_inv (i) : (disjointGlueData f).ι i ≫ (sigmaIsoGlued f).inv = Sigma.ι f i := by
  apply Scheme.forgetToLocallyRingedSpace.map_injective
  dsimp [sigmaIsoGlued]
  simp only [Category.assoc]
  refine ((disjointGlueData f).ι_gluedIso_hom_assoc Scheme.forgetToLocallyRingedSpace i _).trans ?_
  refine (colimit.isoColimitCocone_ι_inv_assoc
    ⟨_, toLocallyRingedSpaceCoproductCofanIsColimit f⟩ ⟨i⟩ _).trans ?_
  exact ι_comp_sigmaComparison Scheme.forgetToLocallyRingedSpace _ _

@[reassoc (attr := simp)]
lemma ι_sigmaIsoGlued_hom (i) :
    Sigma.ι f i ≫ (sigmaIsoGlued f).hom = (disjointGlueData f).ι i := by
  rw [← ι_sigmaIsoGlued_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id]

instance (i) : IsOpenImmersion (Sigma.ι f i) := by
  rw [← ι_sigmaIsoGlued_inv]
  infer_instance

lemma sigmaι_eq_iff (i j : ι) (x y) :
    (Sigma.ι f i).1.base x = (Sigma.ι f j).1.base y ↔
      (Sigma.mk i x : Σ i, f i) = Sigma.mk j y := by
  constructor
  · intro H
    rw [← ι_sigmaIsoGlued_inv, ← ι_sigmaIsoGlued_inv] at H
    erw [(TopCat.homeoOfIso
      (Scheme.forgetToTop.mapIso (sigmaIsoGlued f))).symm.injective.eq_iff] at H
    by_cases h : i = j
    · subst h
      simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
      exact ((disjointGlueData f).ι i).openEmbedding.inj H
    · obtain (e | ⟨z, _⟩) := (Scheme.GlueData.ι_eq_iff _ _ _ _ _).mp H
      · exact (h (Sigma.mk.inj_iff.mp e).1).elim
      · simp only [disjointGlueData_J, disjointGlueData_V, h, ↓reduceIte] at z
        cases z
  · rintro ⟨rfl⟩
    rfl

/-- The images of each component in the coproduct is disjoint. -/
lemma disjoint_opensRange_sigmaι (i j : ι) (h : i ≠ j) :
    Disjoint (Sigma.ι f i).opensRange (Sigma.ι f j).opensRange := by
  intro U hU hU' x hx
  obtain ⟨x, rfl⟩ := hU hx
  obtain ⟨y, hy⟩ := hU' hx
  obtain ⟨rfl⟩ := (sigmaι_eq_iff _ _ _ _ _).mp hy
  cases h rfl

lemma exists_sigmaι_eq (x : (∐ f : _)) : ∃ i y, (Sigma.ι f i).1.base y = x := by
  obtain ⟨i, y, e⟩ := (disjointGlueData f).ι_jointly_surjective ((sigmaIsoGlued f).hom.1.base x)
  refine ⟨i, y, (sigmaIsoGlued f).hom.openEmbedding.inj ?_⟩
  rwa [← Scheme.comp_val_base_apply, ι_sigmaIsoGlued_hom]

lemma iSup_opensRange_sigmaι : ⨆ i, (Sigma.ι f i).opensRange = ⊤ :=
  eq_top_iff.mpr fun x ↦ by simpa using exists_sigmaι_eq f x

/-- The open cover of the coproduct. -/
@[simps obj map]
noncomputable
def sigmaOpenCover : (∐ f).OpenCover where
  J := ι
  obj := f
  map := Sigma.ι f
  f x := (exists_sigmaι_eq f x).choose
  covers x := (exists_sigmaι_eq f x).choose_spec

/-- The underlying topological space of the coproduct is homeomorphic to the disjoint union. -/
noncomputable
def sigmaMk : (Σ i, f i) ≃ₜ (∐ f : _) :=
  TopCat.homeoOfIso ((colimit.isoColimitCocone ⟨_, TopCat.sigmaCofanIsColimit _⟩).symm ≪≫
    (PreservesCoproduct.iso Scheme.forgetToTop f).symm)

@[simp]
lemma sigmaMk_mk (i) (x : f i) :
    sigmaMk f (.mk i x) = (Sigma.ι f i).1.base x := by
  show ((TopCat.sigmaCofan (fun x ↦ (f x).toTopCat)).inj i ≫
    (colimit.isoColimitCocone ⟨_, TopCat.sigmaCofanIsColimit _⟩).inv ≫ _) x =
      Scheme.forgetToTop.map (Sigma.ι f i) x
  congr 1
  refine (colimit.isoColimitCocone_ι_inv_assoc ⟨_, TopCat.sigmaCofanIsColimit _⟩ _ _).trans ?_
  exact ι_comp_sigmaComparison Scheme.forgetToTop _ _

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
    IsCompl (Set.range (coprod.inl : X ⟶ X ⨿ Y).1.base)
      (Set.range (coprod.inr : Y ⟶ X ⨿ Y).1.base) :=
  ((TopCat.binaryCofan_isColimit_iff _).mp
    ⟨mapIsColimitOfPreservesOfIsColimit Scheme.forgetToTop _ _ (coprodIsCoprod X Y)⟩).2.2

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
    coprodMk X Y (.inl x) = (coprod.inl : X ⟶ X ⨿ Y).1.base x := by
  show ((TopCat.binaryCofan X Y).inl ≫
    (colimit.isoColimitCocone ⟨_, TopCat.binaryCofanIsColimit _ _⟩).inv ≫ _) x =
      Scheme.forgetToTop.map coprod.inl x
  congr 1
  refine (colimit.isoColimitCocone_ι_inv_assoc ⟨_, TopCat.binaryCofanIsColimit _ _⟩ _ _).trans ?_
  exact coprodComparison_inl Scheme.forgetToTop

@[simp]
lemma coprodMk_inr (x : Y) :
    coprodMk X Y (.inr x) = (coprod.inr : Y ⟶ X ⨿ Y).1.base x := by
  show ((TopCat.binaryCofan X Y).inr ≫
    (colimit.isoColimitCocone ⟨_, TopCat.binaryCofanIsColimit _ _⟩).inv ≫ _) x =
      Scheme.forgetToTop.map coprod.inr x
  congr 1
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
  IsOpen x := x.rec (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)

variable (R S : Type u) [CommRing R] [CommRing S]

/-- The map `Spec R ⨿ Spec S ⟶ Spec (R × S)`.
This is an isomorphism as witnessed by an `IsIso` instance provided below. -/
noncomputable
def coprodSpec : Spec (.of R) ⨿ Spec (.of S) ⟶ Spec (.of (R × S)) :=
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
    (coprodSpec R S).1.base (coprodMk _ _ x) = (PrimeSpectrum.primeSpectrumProd R S).symm x := by
  apply PrimeSpectrum.ext
  obtain (x | x) := x <;>
    simp only [coprodMk_inl, coprodMk_inr, ← Scheme.comp_val_base_apply,
      coprodSpec, coprod.inl_desc, coprod.inr_desc]
  · show Ideal.comap _ _ = x.asIdeal.prod ⊤
    ext; simp [Ideal.prod, CommRingCat.ofHom]
  · show Ideal.comap _ _ = Ideal.prod ⊤ x.asIdeal
    ext; simp [Ideal.prod, CommRingCat.ofHom]

lemma coprodSpec_apply (x) :
    (coprodSpec R S).1.base x = (PrimeSpectrum.primeSpectrumProd R S).symm
      ((coprodMk (Spec (.of R)) (Spec (.of S))).symm x) := by
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
  convert_to IsIso (TopCat.isoOfHomeo (X := Spec (.of (R × S))) <|
    PrimeSpectrum.primeSpectrumProdHomeo.trans (coprodMk (Spec (.of R)) (Spec (.of S)))).inv
  · ext x; exact coprodSpec_apply R S x
  · infer_instance

instance (R S : CommRingCatᵒᵖ) : IsIso (coprodComparison Scheme.Spec R S) := by
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

noncomputable
instance : PreservesColimitsOfShape (Discrete WalkingPair) Scheme.Spec :=
  ⟨fun {_} ↦
    have (X Y : CommRingCatᵒᵖ) := PreservesColimitPair.ofIsoCoprodComparison Scheme.Spec X Y
    preservesColimitOfIsoDiagram _ (diagramIsoPair _).symm⟩

noncomputable
instance : PreservesColimitsOfShape (Discrete PEmpty.{1}) Scheme.Spec := by
  have : IsEmpty (Scheme.Spec.obj (⊥_ CommRingCatᵒᵖ)) :=
    @Function.isEmpty _ _ spec_punit_isEmpty (Scheme.Spec.mapIso
      (initialIsoIsInitial (initialOpOfTerminal CommRingCat.punitIsTerminal))).hom.1.base
  have := preservesInitialOfIso Scheme.Spec (asIso (initial.to _))
  exact preservesColimitsOfShapePemptyOfPreservesInitial _

noncomputable
instance {J} [Fintype J] : PreservesColimitsOfShape (Discrete J) Scheme.Spec :=
  preservesFiniteCoproductsOfPreservesBinaryAndInitial _ _

noncomputable
instance {J : Type*} [Finite J] : PreservesColimitsOfShape (Discrete J) Scheme.Spec :=
  letI := (nonempty_fintype J).some
  preservesColimitsOfShapeOfEquiv (Discrete.equivalence (Fintype.equivFin _).symm) _

/-- The canonical map `∐ Spec Rᵢ ⟶ Spec (Π Rᵢ)`.
This is an isomorphism when the product is finite. -/
noncomputable
def sigmaSpec (R : ι → CommRingCat) : (∐ fun i ↦ Spec (R i)) ⟶ Spec (.of (Π i, R i)) :=
  Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ i)))

@[simp, reassoc]
lemma ι_sigmaSpec (R : ι → CommRingCat) (i) :
    Sigma.ι _ i ≫ sigmaSpec R = Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ i)) :=
  Sigma.ι_desc _ _

instance [Finite ι] (R : ι → CommRingCat) : IsIso (sigmaSpec R) := by
  have : sigmaSpec R =
      (colimit.isoColimitCocone ⟨_,
        (IsColimit.precomposeHomEquiv Discrete.natIsoFunctor.symm _).symm (isColimitOfPreserves
          Scheme.Spec (Fan.IsLimit.op (CommRingCat.piFanIsLimit R)))⟩).hom := by
    ext1; simp; rfl
  rw [this]
  infer_instance

instance [Finite ι] [∀ i, IsAffine (f i)] : IsAffine (∐ f) :=
  isAffine_of_isIso ((Sigma.mapIso (fun i ↦ (f i).isoSpec)).hom ≫ sigmaSpec _)

instance [IsAffine X] [IsAffine Y] : IsAffine (X ⨿ Y) :=
  isAffine_of_isIso ((coprod.mapIso X.isoSpec Y.isoSpec).hom ≫ coprodSpec _ _)

end Coproduct

end AlgebraicGeometry
