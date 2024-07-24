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
  LocallyRingedSpace.Hom.ext _ _ <| PresheafedSpace.ext _ _ (by ext a; exact PEmpty.elim a) <|
    NatTrans.ext _ _ <| funext fun a => by aesop_cat

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

open scoped Classical

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
    apply Multicoequalizer.hom_ext
    simp only [GlueData.diagram_r, disjointGlueData_J, GlueData.diagram_right, disjointGlueData_U,
      colimit.ι_desc, GlueData.diagram_l, GlueData.diagram_left, disjointGlueData_V, id_eq,
      eq_mpr_eq_cast, cast_eq, Multicofork.ofπ_pt, Multicofork.ofπ_ι_app]
    exact h

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

end Coproduct

end AlgebraicGeometry
