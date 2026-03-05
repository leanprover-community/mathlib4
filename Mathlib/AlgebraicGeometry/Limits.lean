/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Limits.MonoCoprod
public import Mathlib.CategoryTheory.Limits.Shapes.DisjointCoproduct
public import Mathlib.Tactic.SuppressCompilation
public import Mathlib.CategoryTheory.Limits.Constructions.ZeroObjects -- shake: keep
-- This import adds an instance which, despite failing to trigger,
-- is necessary for some typeclass syntheses in this file to succeed.

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

@[expose] public section

suppress_compilation


universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

attribute [local instance] Opposite.small

namespace AlgebraicGeometry

/-- `Spec ℤ` is the terminal object in the category of schemes. -/
noncomputable def specZIsTerminal : IsTerminal (Spec <| .of ℤ) :=
  @IsTerminal.isTerminalObj _ _ _ _ Scheme.Spec _ inferInstance
    (terminalOpOfInitial CommRingCat.zIsInitial)

/-- `Spec ℤ` is the terminal object in the category of schemes. -/
noncomputable def specULiftZIsTerminal : IsTerminal (Spec <| .of <| ULift.{u} ℤ) :=
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

instance spec_punit_isEmpty : IsEmpty (Spec <| .of PUnit.{u + 1}) :=
  inferInstanceAs <| IsEmpty (PrimeSpectrum PUnit)

instance (priority := 100) isOpenImmersion_of_isEmpty {X Y : Scheme} (f : X ⟶ Y)
    [IsEmpty X] : IsOpenImmersion f := by
  apply +allowSynthFailures IsOpenImmersion.of_isIso_stalkMap
  · exact .of_isEmpty (X := X) _
  · intro (i : X); exact isEmptyElim i

instance (priority := 100) isIso_of_isEmpty {X Y : Scheme} (f : X ⟶ Y) [IsEmpty Y] :
    IsIso f := by
  haveI : IsEmpty X := f.base.hom.1.isEmpty
  have : Epi f.base := by
    rw [TopCat.epi_iff_surjective]; rintro (x : Y)
    exact isEmptyElim x
  apply IsOpenImmersion.isIso

/-- A scheme is initial if its underlying space is empty . -/
noncomputable def isInitialOfIsEmpty {X : Scheme} [IsEmpty X] : IsInitial X :=
  emptyIsInitial.ofIso (asIso <| emptyIsInitial.to _)

/-- `Spec 0` is the initial object in the category of schemes. -/
noncomputable def specPUnitIsInitial : IsInitial (Spec <| .of PUnit.{u + 1}) :=
  emptyIsInitial.ofIso (asIso <| emptyIsInitial.to _)

@[deprecated (since := "2026-02-08")] alias specPunitIsInitial := specPUnitIsInitial

lemma isInitial_iff_isEmpty {X : Scheme.{u}} : Nonempty (IsInitial X) ↔ IsEmpty X :=
  ⟨fun ⟨h⟩ ↦ (h.uniqueUpToIso specPUnitIsInitial).hom.homeomorph.isEmpty,
    fun _ ↦ ⟨isInitialOfIsEmpty⟩⟩

instance (priority := 100) isAffine_of_isEmpty {X : Scheme} [IsEmpty X] : IsAffine X :=
  .of_isIso (inv (emptyIsInitial.to X) ≫ emptyIsInitial.to (Spec <| .of PUnit))

instance : HasInitial Scheme.{u} :=
  hasInitial_of_unique ∅

instance initial_isEmpty : IsEmpty (⊥_ Scheme) :=
  ⟨fun x => ((initial.to Scheme.empty :) x).elim⟩

theorem isAffineOpen_bot (X : Scheme) : IsAffineOpen (⊥ : X.Opens) :=
  @isAffine_of_isEmpty _ (inferInstanceAs (IsEmpty (∅ : Set X)))

instance : HasStrictInitialObjects Scheme :=
  hasStrictInitialObjects_of_initial_is_strict fun A f => by infer_instance

instance {X : Scheme} [IsEmpty X] (U : X.Opens) : Subsingleton Γ(X, U) := by
  obtain rfl : U = ⊥ := Subsingleton.elim _ _; infer_instance

-- This is also true for schemes with two points.
-- But there are non-affine schemes with three points.
/-- This is true in general for finite discrete schemes. See below. -/
instance (priority := low) {X : Scheme.{u}} [Subsingleton X] : IsAffine X := by
  cases isEmpty_or_nonempty X with
  | inl h => infer_instance
  | inr h =>
  obtain ⟨x⟩ := h
  obtain ⟨_, ⟨U, hU : IsAffine _, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (a := x) (by trivial) isOpen_univ
  obtain rfl : U = ⊤ := by ext y; simpa [Subsingleton.elim y x]
  exact .of_isIso (Scheme.topIso X).inv

theorem IsAffineOpen.of_subsingleton {X : Scheme} {U : X.Opens}
    (hU : Set.Subsingleton (U : Set X)) : IsAffineOpen U :=
  have : Subsingleton U := hU.coe_sort
  inferInstanceAs (IsAffine _)

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

set_option backward.isDefEq.respectTransparency false in
lemma sigmaι_eq_iff [Small.{u} σ] (i j : σ) (x y) :
    Sigma.ι g i x = Sigma.ι g j y ↔ (Sigma.mk i x : Σ i, g i) = Sigma.mk j y := by
  refine (Scheme.IsLocallyDirected.ι_eq_ι_iff _).trans ⟨?_, ?_⟩
  · rintro ⟨k, ⟨⟨⟨⟩⟩⟩, ⟨⟨⟨⟩⟩⟩, x, rfl, rfl⟩; simp
  · simp only [Discrete.functor_obj_eq_as, Sigma.mk.injEq]
    rintro ⟨rfl, e⟩
    obtain rfl := (heq_eq_eq x y).mp e
    exact ⟨⟨i⟩, 𝟙 _, 𝟙 _, x, by simp⟩

set_option backward.isDefEq.respectTransparency false in
/-- The images of each component in the coproduct is disjoint. -/
lemma disjoint_opensRange_sigmaι [Small.{u} σ] (i j : σ) (h : i ≠ j) :
    Disjoint (Sigma.ι g i).opensRange (Sigma.ι g j).opensRange := by
  intro U hU hU' x hx
  obtain ⟨x, rfl⟩ := hU hx
  obtain ⟨y, hy⟩ := hU' hx
  obtain ⟨rfl⟩ := (sigmaι_eq_iff _ _ _ _ _).mp hy
  cases h rfl

variable {g} in
lemma isEmpty_of_commSq_sigmaι_of_ne [Small.{u} σ] {i j : σ} {Z : Scheme.{u}} {a : Z ⟶ g i}
    {b : Z ⟶ g j} (h : CommSq a b (Sigma.ι g i) (Sigma.ι g j)) (hij : i ≠ j) :
    IsEmpty Z := by
  refine ⟨fun z ↦ ?_⟩
  fapply eq_bot_iff.mp <| disjoint_iff.mp <| disjoint_opensRange_sigmaι g i j hij
  · exact (a ≫ Sigma.ι g i).base z
  · exact ⟨⟨a.base z, rfl⟩, ⟨b.base z, by rw [← Scheme.Hom.comp_apply, h.w]⟩⟩

lemma isEmpty_pullback_sigmaι_of_ne [Small.{u} σ] {i j : σ} (hij : i ≠ j) :
    IsEmpty ↑(pullback (Sigma.ι g i) (Sigma.ι g j)) :=
  isEmpty_of_commSq_sigmaι_of_ne ⟨pullback.condition⟩ hij

set_option backward.isDefEq.respectTransparency false in
noncomputable instance [Small.{u} σ] : CoproductsOfShapeDisjoint Scheme.{u} σ where
  coproductDisjoint g := by
    refine .of_hasCoproduct (fun _ ↦ pullback.cone _ _) (fun _ ↦ pullback.isLimit _ _) ?_
    intro i j hij
    apply Nonempty.some
    rw [isInitial_iff_isEmpty]
    exact isEmpty_pullback_sigmaι_of_ne _ hij

instance : HasFiniteCoproducts Scheme.{u} where
  out := inferInstance

instance : MonoCoprod Scheme.{u} :=
  .mk' fun X Y ↦ ⟨.mk coprod.inl coprod.inr, coprodIsCoprod X Y, inferInstanceAs <| Mono coprod.inl⟩

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
    sigmaMk f (.mk i x) = Sigma.ι f i x := by
  change ((TopCat.sigmaCofan (fun x ↦ (f x).toTopCat)).inj i ≫
    (colimit.isoColimitCocone ⟨_, TopCat.sigmaCofanIsColimit _⟩).inv ≫ _) x =
      Scheme.forgetToTop.map (Sigma.ι f i) x
  congr 2
  refine (colimit.isoColimitCocone_ι_inv_assoc ⟨_, TopCat.sigmaCofanIsColimit _⟩ _ _).trans ?_
  exact ι_comp_sigmaComparison Scheme.forgetToTop _ _

set_option backward.isDefEq.respectTransparency false in
open scoped Function in
private lemma isOpenImmersion_sigmaDesc_aux
    {X : Scheme.{u}} (α : ∀ i, f i ⟶ X) [∀ i, IsOpenImmersion (α i)]
    (hα : Pairwise (Disjoint on (Set.range <| α ·))) :
    IsOpenImmersion (Sigma.desc α) := by
  rw [IsOpenImmersion.iff_isIso_stalkMap]
  constructor
  · suffices Topology.IsOpenEmbedding (Sigma.desc α ∘ sigmaMk f) by
      convert this.comp (sigmaMk f).symm.isOpenEmbedding; ext; simp
    refine .of_continuous_injective_isOpenMap ?_ ?_ ?_
    · fun_prop
    · rintro ⟨ix, x⟩ ⟨iy, y⟩ e
      have : α ix x = α iy y := by
        simpa [← Scheme.Hom.comp_apply] using e
      obtain rfl : ix = iy := by
        by_contra h
        exact Set.disjoint_iff_forall_ne.mp (hα h) ⟨x, rfl⟩ ⟨y, this.symm⟩ rfl
      rw [(α ix).isOpenEmbedding.injective this]
    · rw [isOpenMap_sigma]
      intro i
      simpa [← Scheme.Hom.comp_apply] using (α i).isOpenEmbedding.isOpenMap
  · intro x
    have ⟨y, hy⟩ := (Scheme.IsLocallyDirected.openCover (Discrete.functor f)).covers x
    rw [← hy]
    refine IsIso.of_isIso_fac_right
      (f := ((Scheme.IsLocallyDirected.openCover (Discrete.functor f)).f _).stalkMap y)
      (h := (X.presheaf.stalkCongr (.of_eq ?_)).hom ≫ (α _).stalkMap _) ?_
    · simp [← Scheme.Hom.comp_apply]
    · simp [← Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_congr_hom _ _ (colimit.ι_desc _ _)]

set_option backward.isDefEq.respectTransparency false in
open scoped Function in
lemma isOpenImmersion_sigmaDesc [Small.{u} σ]
    {X : Scheme.{u}} (α : ∀ i, g i ⟶ X) [∀ i, IsOpenImmersion (α i)]
    (hα : Pairwise (Disjoint on (Set.range <| α ·))) :
    IsOpenImmersion (Sigma.desc α) := by
  obtain ⟨ι, ⟨e⟩⟩ := Small.equiv_small (α := σ)
  convert IsOpenImmersion.comp ((Sigma.reindex e.symm g).inv) (Sigma.desc fun i ↦ α _)
  · refine Sigma.hom_ext _ _ fun i ↦ ?_
    obtain ⟨i, rfl⟩ := e.symm.surjective i
    simp
  · apply isOpenImmersion_sigmaDesc_aux
    intro i j hij
    exact hα (fun h ↦ hij (e.symm.injective h))

set_option backward.isDefEq.respectTransparency false in
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
  simp only [Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk S f), cofan_mk_inj, Cofan.mk_pt]
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  rw [eq_top_iff]
  intro x hx
  have : x ∈ ⨆ i, (f i).opensRange := by rwa [hcov]
  obtain ⟨i, y, rfl⟩ := by simpa only [Opens.iSup_mk, Opens.mem_mk, Set.mem_iUnion] using this
  use Sigma.ι X i y
  simp [← Scheme.Hom.comp_apply]

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

set_option backward.isDefEq.respectTransparency false in
instance : IsOpenImmersion (coprod.inl : X ⟶ X ⨿ Y) := by
  rw [← ι_left_coprodIsoSigma_inv]; infer_instance

set_option backward.isDefEq.respectTransparency false in
instance : IsOpenImmersion (coprod.inr : Y ⟶ X ⨿ Y) := by
  rw [← ι_right_coprodIsoSigma_inv]; infer_instance

lemma isCompl_range_inl_inr :
    IsCompl (Set.range (coprod.inl : X ⟶ X ⨿ Y)) (Set.range (coprod.inr : Y ⟶ X ⨿ Y)) :=
  ((TopCat.binaryCofan_isColimit_iff _).mp
    ⟨mapIsColimitOfPreservesOfIsColimit Scheme.forgetToTop.{u} _ _ (coprodIsCoprod X Y)⟩).2.2

set_option backward.isDefEq.respectTransparency false in
lemma isCompl_opensRange_inl_inr :
    IsCompl (coprod.inl : X ⟶ X ⨿ Y).opensRange (coprod.inr : Y ⟶ X ⨿ Y).opensRange := by
  convert isCompl_range_inl_inr X Y
  simp only [isCompl_iff, disjoint_iff, codisjoint_iff, ← TopologicalSpace.Opens.coe_inj]
  rfl

@[simp]
lemma inl_ne_inr (x : X) (y : Y) : (coprod.inl : X ⟶ X ⨿ Y) x ≠ (coprod.inr : Y ⟶ X ⨿ Y) y :=
  Set.disjoint_iff_forall_ne.mp (isCompl_range_inl_inr X Y).disjoint ⟨x, rfl⟩ ⟨y, rfl⟩

@[simp]
lemma inr_ne_inl (x : X) (y : Y) : (coprod.inr : Y ⟶ X ⨿ Y) y ≠ (coprod.inl : X ⟶ X ⨿ Y) x :=
  (inl_ne_inr _ _ _ _).symm

/-- The underlying topological space of the coproduct is homeomorphic to the disjoint union -/
noncomputable
def coprodMk : X ⊕ Y ≃ₜ (X ⨿ Y : Scheme.{u}) :=
  TopCat.homeoOfIso ((colimit.isoColimitCocone ⟨_, TopCat.binaryCofanIsColimit _ _⟩).symm ≪≫
    PreservesColimitPair.iso Scheme.forgetToTop X Y)

@[simp]
lemma coprodMk_inl (x : X) :
    coprodMk X Y (.inl x) = (coprod.inl : X ⟶ X ⨿ Y) x := by
  change ((TopCat.binaryCofan X Y).inl ≫
    (colimit.isoColimitCocone ⟨_, TopCat.binaryCofanIsColimit _ _⟩).inv ≫ _) x =
      Scheme.forgetToTop.map coprod.inl x
  congr 2
  refine (colimit.isoColimitCocone_ι_inv_assoc ⟨_, TopCat.binaryCofanIsColimit _ _⟩ _ _).trans ?_
  exact coprodComparison_inl Scheme.forgetToTop

@[simp]
lemma coprodMk_inr (x : Y) :
    coprodMk X Y (.inr x) = (coprod.inr : Y ⟶ X ⨿ Y) x := by
  change ((TopCat.binaryCofan X Y).inr ≫
    (colimit.isoColimitCocone ⟨_, TopCat.binaryCofanIsColimit _ _⟩).inv ≫ _) x =
      Scheme.forgetToTop.map coprod.inr x
  congr 2
  refine (colimit.isoColimitCocone_ι_inv_assoc ⟨_, TopCat.binaryCofanIsColimit _ _⟩ _ _).trans ?_
  exact coprodComparison_inr Scheme.forgetToTop

set_option backward.isDefEq.respectTransparency false in
/-- The open cover of the coproduct of two schemes. -/
noncomputable
def coprodOpenCover.{w} : (X ⨿ Y).OpenCover where
  I₀ := PUnit.{w + 1} ⊕ PUnit.{w + 1}
  X x := x.elim (fun _ ↦ X) (fun _ ↦ Y)
  f x := x.rec (fun _ ↦ coprod.inl) (fun _ ↦ coprod.inr)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun x ↦ x.rec (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)⟩
    use ((coprodMk X Y).symm x).elim (fun _ ↦ Sum.inl .unit) (fun _ ↦ Sum.inr .unit)
    obtain ⟨x, rfl⟩ := (coprodMk X Y).surjective x
    simp only [Sum.elim_inl, Sum.elim_inr, Set.mem_range]
    rw [Homeomorph.symm_apply_apply]
    obtain (x | x) := x
    · simp only [Sum.elim_inl, coprodMk_inl, exists_apply_eq_apply]
    · simp only [Sum.elim_inr, coprodMk_inr, exists_apply_eq_apply]

-- TODO: should infer_instance be considered normalising?
set_option backward.isDefEq.respectTransparency false in
set_option linter.flexible false in
/-- If `X` and `Y` are open disjoint and covering open subschemes of `S`,
`S` is the disjoint union of `X` and `Y`. -/
lemma nonempty_isColimit_binaryCofanMk_of_isCompl {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) [IsOpenImmersion f] [IsOpenImmersion g]
    (hf : IsCompl f.opensRange g.opensRange) :
    Nonempty (IsColimit <| BinaryCofan.mk f g) := by
  let c' : Cofan fun j ↦ (WalkingPair.casesOn j X Y : Scheme.{u}) :=
    .mk S fun j ↦ WalkingPair.casesOn j f g
  let i : BinaryCofan.mk f g ≅ c' := Cofan.ext (Iso.refl _) (by rintro (b | b) <;> rfl)
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

lemma isPullback_inl_inl_coprodMap {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') : IsPullback f coprod.inl coprod.inl (coprod.map f g) := by
  refine IsOpenImmersion.isPullback _ _ _ _ (by simp) ?_
  apply le_antisymm
  · rintro x ⟨y, hxy⟩
    obtain ⟨(x | x), rfl⟩ := (coprodMk _ _).surjective x
    · rw [← SetLike.mem_coe]; simp -- TODO : add `Scheme.Hom.mem_opensRange`
    · simp only [coprodMk_inr, ← Scheme.Hom.comp_apply, coprod.inr_map] at hxy
      cases Set.disjoint_iff_forall_ne.mp (isCompl_range_inl_inr _ _).1 ⟨y, rfl⟩ ⟨_, rfl⟩ hxy
  · rintro _ ⟨x, rfl⟩
    exact ⟨f x, by simp [← Scheme.Hom.comp_apply, - Scheme.Hom.comp_base]⟩

set_option backward.isDefEq.respectTransparency false in
lemma isPullback_inr_inr_coprodMap {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') : IsPullback g coprod.inr coprod.inr (coprod.map f g) :=
  (isPullback_inl_inl_coprodMap g f).of_iso (.refl _) (.refl _) (coprod.braiding _ _)
    (coprod.braiding _ _) (by simp) (by simp) (by simp) (by simp)

set_option backward.isDefEq.respectTransparency false in
instance : FinitaryExtensive Scheme where
  hasFiniteCoproducts.out := inferInstance
  van_kampen' {X Y} c hc := by
    suffices IsVanKampenColimit (BinaryCofan.mk (P := X ⨿ Y) coprod.inl coprod.inr) from
      this.of_iso (hc.uniqueUpToIso (coprodIsCoprod _ _)).symm
    refine BinaryCofan.isVanKampen_mk _ _ (fun _ _ ↦ coprodIsCoprod _ _) _
      (fun _ _ ↦ pullbackIsPullback _ _) ?_ ?_
    · intro X' Y' αX αY f h₁ h₂
      have h₁' (x : _) := congr($h₁ x).symm
      have h₂' (x : _) := congr($h₂ x).symm
      dsimp at h₁ h₂ h₁' h₂'
      refine ⟨(IsOpenImmersion.isPullback _ _ _ _ h₁.symm ?_).flip,
        (IsOpenImmersion.isPullback _ _ _ _ h₂.symm ?_).flip⟩ <;>
        ext x <;> obtain ⟨x | x, rfl⟩ := (coprodMk _ _).surjective x <;> simp_all
    · dsimp
      refine fun {Z} f ↦ (nonempty_isColimit_binaryCofanMk_of_isCompl _ _ ?_).some
      rw [Scheme.Hom.opensRange_pullbackFst, Scheme.Hom.opensRange_pullbackFst]
      convert (isCompl_range_inl_inr X Y).map (CompleteLatticeHom.setPreimage f)
      simp [isCompl_iff, disjoint_iff, codisjoint_iff, ← TopologicalSpace.Opens.coe_inj]

variable {X Y}

/-- The sections on coproducts of schemes are the (categorical) product of the sections
on the components -/
noncomputable def Scheme.coprodPresheafObjIso (U : (X ⨿ Y).Opens) :
    Γ(X ⨿ Y, U) ≅ Γ(X, coprod.inl (C := Scheme) ⁻¹ᵁ U) ⨯ Γ(Y, coprod.inr (C := Scheme) ⁻¹ᵁ U) :=
  letI ι₁ : X ⟶ X ⨿ Y := coprod.inl
  letI ι₂ : Y ⟶ X ⨿ Y := coprod.inr
  haveI h₁ : ι₁ ''ᵁ ι₁ ⁻¹ᵁ U ⊔ ι₂ ''ᵁ ι₂ ⁻¹ᵁ U = U := by
    simp_rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    rw [← inf_sup_right, (isCompl_opensRange_inl_inr X Y).sup_eq_top, top_inf_eq]
  haveI h₂ : ι₁ ''ᵁ ι₁ ⁻¹ᵁ U ⊓ ι₂ ''ᵁ ι₂ ⁻¹ᵁ U = ⊥ := by
    simp_rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    rw [← inf_inf_distrib_right, (isCompl_opensRange_inl_inr X Y).inf_eq_bot, bot_inf_eq]
  (X ⨿ Y).presheaf.mapIso (eqToIso h₁).op ≪≫
    ((X ⨿ Y).sheaf.isProductOfDisjoint _ _ h₂).conePointUniqueUpToIso (limit.isLimit _) ≪≫
    prod.mapIso (ι₁.appIso _) (ι₂.appIso _)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma Scheme.coprodPresheafObjIso_hom_fst (U : (X ⨿ Y).Opens) :
    (coprodPresheafObjIso U).hom ≫ prod.fst = (coprod.inl (C := Scheme)).app U := by
  simp [coprodPresheafObjIso, Hom.appIso_hom, ← Functor.map_comp, Subsingleton.elim _ (𝟙 _)]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma Scheme.coprodPresheafObjIso_hom_snd (U : (X ⨿ Y).Opens) :
    (coprodPresheafObjIso U).hom ≫ prod.snd = (coprod.inr (C := Scheme)).app U := by
  simp [coprodPresheafObjIso, Hom.appIso_hom, ← Functor.map_comp, Subsingleton.elim _ (𝟙 _)]

variable (R S : Type u) [CommRing R] [CommRing S]

/-- The map `Spec R ⨿ Spec S ⟶ Spec (R × S)`.
This is an isomorphism as witnessed by an `IsIso` instance provided below. -/
noncomputable
def coprodSpec : Spec (.of R) ⨿ Spec (.of S) ⟶ Spec (.of <| R × S) :=
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
    coprodSpec R S (coprodMk _ _ x) = (PrimeSpectrum.primeSpectrumProd R S).symm x := by
  apply PrimeSpectrum.ext
  obtain (x | x) := x <;>
    simp only [coprodMk_inl, coprodMk_inr, ← Scheme.Hom.comp_apply,
      coprodSpec, coprod.inl_desc, coprod.inr_desc]
  · change Ideal.comap _ _ = x.asIdeal.prod ⊤
    ext; simp [Ideal.prod, CommRingCat.ofHom]
  · change Ideal.comap _ _ = Ideal.prod ⊤ x.asIdeal
    ext; simp [Ideal.prod, CommRingCat.ofHom]

lemma coprodSpec_apply (x) :
    coprodSpec R S x = (PrimeSpectrum.primeSpectrumProd R S).symm ((coprodMk _ _).symm x) := by
  rw [← coprodSpec_coprodMk, Homeomorph.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
lemma isIso_stalkMap_coprodSpec (x) :
    IsIso ((coprodSpec R S).stalkMap x) := by
  obtain ⟨x | x, rfl⟩ := (coprodMk _ _).surjective x
  · have := Scheme.Hom.stalkMap_comp coprod.inl (coprodSpec R S) x
    rw [← IsIso.comp_inv_eq,
      Scheme.Hom.stalkMap_congr_hom _ (Spec.map _) (coprodSpec_inl R S)] at this
    rw [coprodMk_inl, ← this]
    letI := (RingHom.fst R S).toAlgebra
    have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (RingHom.fst R S))) :=
      IsOpenImmersion.of_isLocalization (1, 0)
    infer_instance
  · have := Scheme.Hom.stalkMap_comp coprod.inr (coprodSpec R S) x
    rw [← IsIso.comp_inv_eq,
      Scheme.Hom.stalkMap_congr_hom _ (Spec.map _) (coprodSpec_inr R S)] at this
    rw [coprodMk_inr, ← this]
    letI := (RingHom.snd R S).toAlgebra
    have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (RingHom.snd R S))) :=
      IsOpenImmersion.of_isLocalization (0, 1)
    infer_instance

instance : IsIso (coprodSpec R S) := by
  rw [isIso_iff_isIso_stalkMap]
  refine ⟨?_, isIso_stalkMap_coprodSpec R S⟩
  convert_to IsIso (TopCat.isoOfHomeo (X := Spec (.of <| R × S)) <|
    PrimeSpectrum.primeSpectrumProdHomeo.trans (coprodMk (Spec <| .of R) (Spec <| .of S))).inv
  · ext x; exact coprodSpec_apply R S x
  · infer_instance

set_option backward.isDefEq.respectTransparency false in
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
      (initialIsoIsInitial (initialOpOfTerminal CommRingCat.punitIsTerminal))).hom
  have := preservesInitial_of_iso Scheme.Spec (asIso (initial.to _))
  exact preservesColimitsOfShape_pempty_of_preservesInitial _

instance {J : Type*} [Finite J] : PreservesColimitsOfShape (Discrete J) Scheme.Spec.{u} :=
  preservesFiniteCoproductsOfPreservesBinaryAndInitial _ _

/-- The canonical map `∐ Spec Rᵢ ⟶ Spec (Π Rᵢ)`.
This is an isomorphism when the product is finite. -/
noncomputable
def sigmaSpec (R : ι → CommRingCat) : (∐ fun i ↦ Spec (R i)) ⟶ Spec (.of <| Π i, R i) :=
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

set_option backward.isDefEq.respectTransparency false in
instance [Finite ι] (R : ι → CommRingCat.{u}) : IsIso (sigmaSpec R) := by
  have : sigmaSpec R =
      (colimit.isoColimitCocone ⟨_,
        (IsColimit.precomposeHomEquiv Discrete.natIsoFunctor.symm _).symm (isColimitOfPreserves
          Scheme.Spec (Fan.IsLimit.op (CommRingCat.piFanIsLimit R)))⟩).hom := by
    ext1
    simp; rfl
  rw [this]
  infer_instance

instance [Finite σ] [∀ i, IsAffine (g i)] : IsAffine (∐ g) := by
  obtain ⟨ι, ⟨e⟩⟩ := Small.equiv_small.{u} (α := σ)
  have : Finite ι := e.finite_iff.mp ‹_›
  have (i : _) : IsAffine ((g ∘ e.symm) i) := by dsimp; infer_instance
  exact IsAffine.of_isIso ((Sigma.reindex e.symm g).inv ≫
    (Sigma.mapIso (fun i ↦ Scheme.isoSpec _)).hom ≫ sigmaSpec _)

instance [IsAffine X] [IsAffine Y] : IsAffine (X ⨿ Y) :=
  .of_isIso ((coprod.mapIso X.isoSpec Y.isoSpec).hom ≫ coprodSpec _ _)

set_option backward.isDefEq.respectTransparency false in
open scoped Function in
/-- A version with more restrictive universes. See `IsAffineOpen.iSup_of_disjoint`. -/
private lemma IsAffineOpen.iSup_of_disjoint_aux [Finite ι] {U : ι → X.Opens}
    (hU : ∀ i, IsAffineOpen (U i)) (hU' : Pairwise (Disjoint on U)) :
    IsAffineOpen (iSup U) := by
  have := isOpenImmersion_sigmaDesc _ (fun i ↦ (U i).ι)
    (fun i j e ↦ by convert hU' e using 0; simp [← Opens.coe_disjoint])
  convert isAffineOpen_opensRange (Sigma.desc fun i ↦ (U i).ι)
  · ext
    simp [(sigmaMk _).symm.exists_congr_left, ← Scheme.Hom.comp_apply, Scheme.Opens.exists_toScheme]
  · have (i : _) : IsAffine _ := hU i
    infer_instance

set_option backward.isDefEq.respectTransparency false in
open scoped Function in
lemma IsAffineOpen.iSup_of_disjoint [Finite σ] {U : σ → X.Opens}
    (hU : ∀ i, IsAffineOpen (U i)) (hU' : Pairwise (Disjoint on U)) :
    IsAffineOpen (iSup U) := by
  obtain ⟨ι, ⟨e⟩⟩ := Small.equiv_small.{u} (α := σ)
  have : Finite ι := e.finite_iff.mp ‹_›
  rw [← e.symm.iSup_congr fun _ ↦ rfl]
  exact .iSup_of_disjoint_aux (by simp [*]) fun i j h ↦ hU' (e.symm.injective.ne h)

set_option backward.isDefEq.respectTransparency false in
open scoped Function in
lemma IsAffineOpen.biSup_of_disjoint {s : Set σ} (hs : s.Finite)
    {U : σ → X.Opens} (hU : ∀ i ∈ s, IsAffineOpen (U i)) (hU' : s.Pairwise (Disjoint on U)) :
    IsAffineOpen (⨆ i ∈ s, U i) := by
  rw [← iSup_subtype'']
  have := hs.to_subtype
  exact .iSup_of_disjoint (by simpa) fun i j e ↦ hU' i.2 j.2 (by aesop)

set_option backward.isDefEq.respectTransparency false in
lemma IsAffineOpen.sup_of_disjoint {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (H : Disjoint U V) :
    IsAffineOpen (U ⊔ V) := by
  convert iSup_of_disjoint (U := fun i : Unit ⊕ Unit ↦ i.elim (fun _ ↦ U) (fun _ ↦ V)) (by simp_all)
    (by simp_all [_root_.Pairwise, Unique.forall_iff, ← Opens.coe_disjoint, disjoint_comm])
  aesop

instance (priority := low) [Finite X] [DiscreteTopology X] : IsAffine X :=
  have : IsAffineOpen (⨆ (x : X), (⟨{x}, isOpen_discrete _⟩ : X.Opens)) :=
    .iSup_of_disjoint (fun i ↦ .of_subsingleton Set.subsingleton_singleton)
      fun i j e ↦ by simpa [← TopologicalSpace.Opens.coe_disjoint]
  have : IsAffine (⊤ : X.Opens).toScheme := show IsAffineOpen _ by convert this; ext; simp
  .of_isIso X.topIso.inv

end Coproduct

instance {U X Y : Scheme} (f : U ⟶ X) (g : U ⟶ Y) [IsOpenImmersion f] [IsOpenImmersion g]
    (i : WalkingPair) : Mono ((span f g ⋙ Scheme.forget).map (WidePushoutShape.Hom.init i)) := by
  rw [mono_iff_injective]
  cases i
  · simpa using f.isOpenEmbedding.injective
  · simpa using g.isOpenEmbedding.injective

instance {U X Y : Scheme} (f : U ⟶ X) (g : U ⟶ Y) [IsOpenImmersion f] [IsOpenImmersion g]
    {i j : WalkingSpan} (t : i ⟶ j) : IsOpenImmersion ((span f g).map t) := by
  obtain (a | (a | a)) := t
  · simp only [WidePushoutShape.hom_id, CategoryTheory.Functor.map_id]
    infer_instance
  · simpa
  · simpa

-- Test that instances on locally directed colimits fire correctly.
example {U X Y : Scheme.{u}} (f : U ⟶ X) (g : U ⟶ Y)
    [IsOpenImmersion f] [IsOpenImmersion g] : HasPushout f g :=
  inferInstance

instance : CartesianMonoidalCategory Scheme := .ofHasFiniteProducts
instance : BraidedCategory Scheme := .ofCartesianMonoidalCategory

section IsAffine

lemma Scheme.isAffine_of_isLimit {I : Type*} [Category* I] {D : I ⥤ Scheme.{u}}
    (c : Cone D) (hc : IsLimit c) [∀ i, IsAffine (D.obj i)] :
    IsAffine c.pt := by
  let α : D ⟶ (D ⋙ Scheme.Γ.rightOp) ⋙ Scheme.Spec := D.whiskerLeft ΓSpec.adjunction.unit
  have (i : _) : IsIso (α.app i) := IsAffine.affine
  have : IsIso α := NatIso.isIso_of_isIso_app α
  have : c.pt ≅ Spec Γ(c.pt, ⊤) := hc.conePointUniqueUpToIso ((IsLimit.postcomposeHomEquiv
    (asIso α).symm _).symm (isLimitOfPreserves (Scheme.Γ.rightOp ⋙ Scheme.Spec) hc))
  exact .of_isIso this.hom

end IsAffine

end AlgebraicGeometry
