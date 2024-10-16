/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Justus Springer
-/
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Algebra.Module.LocalizedModule

/-!
# $Spec$ as a functor to locally ringed spaces.

We define the functor $Spec$ from commutative rings to locally ringed spaces.

## Implementation notes

We define $Spec$ in three consecutive steps, each with more structure than the last:

1. `Spec.toTop`, valued in the category of topological spaces,
2. `Spec.toSheafedSpace`, valued in the category of sheafed spaces and
3. `Spec.toLocallyRingedSpace`, valued in the category of locally ringed spaces.

Additionally, we provide `Spec.toPresheafedSpace` as a composition of `Spec.toSheafedSpace` with
a forgetful functor.

## Related results

The adjunction `Γ ⊣ Spec` is constructed in `Mathlib/AlgebraicGeometry/GammaSpecAdjunction.lean`.

-/


-- Explicit universe annotations were used in this file to improve performance #12737

noncomputable section

universe u v

namespace AlgebraicGeometry

open Opposite

open CategoryTheory

open StructureSheaf

open Spec (structureSheaf)

/-- The spectrum of a commutative ring, as a topological space.
-/
def Spec.topObj (R : CommRingCat.{u}) : TopCat :=
  TopCat.of (PrimeSpectrum R)

@[simp] theorem Spec.topObj_forget {R} : (forget TopCat).obj (Spec.topObj R) = PrimeSpectrum R :=
  rfl

/-- The induced map of a ring homomorphism on the ring spectra, as a morphism of topological spaces.
-/
def Spec.topMap {R S : CommRingCat.{u}} (f : R ⟶ S) : Spec.topObj S ⟶ Spec.topObj R :=
  PrimeSpectrum.comap f

@[simp]
theorem Spec.topMap_id (R : CommRingCat.{u}) : Spec.topMap (𝟙 R) = 𝟙 (Spec.topObj R) :=
  rfl

@[simp]
theorem Spec.topMap_comp {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    Spec.topMap (f ≫ g) = Spec.topMap g ≫ Spec.topMap f :=
  rfl

-- Porting note: `simps!` generate some garbage lemmas, so choose manually,
-- if more is needed, add them here
/-- The spectrum, as a contravariant functor from commutative rings to topological spaces.
-/
@[simps! obj map]
def Spec.toTop : CommRingCat.{u}ᵒᵖ ⥤ TopCat where
  obj R := Spec.topObj (unop R)
  map {_ _} f := Spec.topMap f.unop

/-- The spectrum of a commutative ring, as a `SheafedSpace`.
-/
@[simps]
def Spec.sheafedSpaceObj (R : CommRingCat.{u}) : SheafedSpace CommRingCat where
  carrier := Spec.topObj R
  presheaf := (structureSheaf R).1
  IsSheaf := (structureSheaf R).2

/-- The induced map of a ring homomorphism on the ring spectra, as a morphism of sheafed spaces.
-/
@[simps base c_app]
def Spec.sheafedSpaceMap {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Spec.sheafedSpaceObj S ⟶ Spec.sheafedSpaceObj R where
  base := Spec.topMap f
  c :=
    { app := fun U =>
        comap f (unop U) ((TopologicalSpace.Opens.map (Spec.topMap f)).obj (unop U)) fun _ => id
      naturality := fun {_ _} _ => RingHom.ext fun _ => Subtype.eq <| funext fun _ => rfl }

@[simp]
theorem Spec.sheafedSpaceMap_id {R : CommRingCat.{u}} :
    Spec.sheafedSpaceMap (𝟙 R) = 𝟙 (Spec.sheafedSpaceObj R) :=
  AlgebraicGeometry.PresheafedSpace.Hom.ext _ _ (Spec.topMap_id R) <| by
    ext
    dsimp
    erw [comap_id (by simp)]
    simp

theorem Spec.sheafedSpaceMap_comp {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    Spec.sheafedSpaceMap (f ≫ g) = Spec.sheafedSpaceMap g ≫ Spec.sheafedSpaceMap f :=
  AlgebraicGeometry.PresheafedSpace.Hom.ext _ _ (Spec.topMap_comp f g) <| by
    ext
    -- Porting note: was one liner
    -- `dsimp, rw category_theory.functor.map_id, rw category.comp_id, erw comap_comp f g, refl`
    rw [NatTrans.comp_app, sheafedSpaceMap_c_app, whiskerRight_app, eqToHom_refl]
    erw [(sheafedSpaceObj T).presheaf.map_id, Category.comp_id, comap_comp]
    rfl

/-- Spec, as a contravariant functor from commutative rings to sheafed spaces.
-/
@[simps]
def Spec.toSheafedSpace : CommRingCat.{u}ᵒᵖ ⥤ SheafedSpace CommRingCat where
  obj R := Spec.sheafedSpaceObj (unop R)
  map f := Spec.sheafedSpaceMap f.unop
  map_comp f g := by simp [Spec.sheafedSpaceMap_comp]

/-- Spec, as a contravariant functor from commutative rings to presheafed spaces.
-/
def Spec.toPresheafedSpace : CommRingCat.{u}ᵒᵖ ⥤ PresheafedSpace CommRingCat :=
  Spec.toSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace

@[simp]
theorem Spec.toPresheafedSpace_obj (R : CommRingCat.{u}ᵒᵖ) :
    Spec.toPresheafedSpace.obj R = (Spec.sheafedSpaceObj (unop R)).toPresheafedSpace :=
  rfl

theorem Spec.toPresheafedSpace_obj_op (R : CommRingCat.{u}) :
    Spec.toPresheafedSpace.obj (op R) = (Spec.sheafedSpaceObj R).toPresheafedSpace :=
  rfl

@[simp]
theorem Spec.toPresheafedSpace_map (R S : CommRingCat.{u}ᵒᵖ) (f : R ⟶ S) :
    Spec.toPresheafedSpace.map f = Spec.sheafedSpaceMap f.unop :=
  rfl

theorem Spec.toPresheafedSpace_map_op (R S : CommRingCat.{u}) (f : R ⟶ S) :
    Spec.toPresheafedSpace.map f.op = Spec.sheafedSpaceMap f :=
  rfl

theorem Spec.basicOpen_hom_ext {X : RingedSpace.{u}} {R : CommRingCat.{u}}
    {α β : X ⟶ Spec.sheafedSpaceObj R} (w : α.base = β.base)
    (h : ∀ r : R,
      let U := PrimeSpectrum.basicOpen r
      (toOpen R U ≫ α.c.app (op U)) ≫ X.presheaf.map (eqToHom (by rw [w])) =
        toOpen R U ≫ β.c.app (op U)) :
    α = β := by
  ext : 1
  · exact w
  · apply
      ((TopCat.Sheaf.pushforward _ β.base).obj X.sheaf).hom_ext _ PrimeSpectrum.isBasis_basic_opens
    intro r
    apply (StructureSheaf.to_basicOpen_epi R r).1
    simpa using h r

-- Porting note: `simps!` generate some garbage lemmas, so choose manually,
-- if more is needed, add them here
/-- The spectrum of a commutative ring, as a `LocallyRingedSpace`.
-/
@[simps! toSheafedSpace presheaf]
def Spec.locallyRingedSpaceObj (R : CommRingCat.{u}) : LocallyRingedSpace :=
  { Spec.sheafedSpaceObj R with
    localRing := fun x =>
      RingEquiv.localRing (A := Localization.AtPrime x.asIdeal)
        (Iso.commRingCatIsoToRingEquiv <| stalkIso R x).symm }

lemma Spec.locallyRingedSpaceObj_sheaf (R : CommRingCat.{u}) :
    (Spec.locallyRingedSpaceObj R).sheaf = structureSheaf R := rfl

lemma Spec.locallyRingedSpaceObj_sheaf' (R : Type u) [CommRing R] :
    (Spec.locallyRingedSpaceObj <| CommRingCat.of R).sheaf = structureSheaf R := rfl

lemma Spec.locallyRingedSpaceObj_presheaf_map (R : CommRingCat.{u}) {U V} (i : U ⟶ V) :
    (Spec.locallyRingedSpaceObj R).presheaf.map i =
    (structureSheaf R).1.map i := rfl

lemma Spec.locallyRingedSpaceObj_presheaf' (R : Type u) [CommRing R] :
    (Spec.locallyRingedSpaceObj <| CommRingCat.of R).presheaf = (structureSheaf R).1 := rfl

lemma Spec.locallyRingedSpaceObj_presheaf_map' (R : Type u) [CommRing R] {U V} (i : U ⟶ V) :
    (Spec.locallyRingedSpaceObj <| CommRingCat.of R).presheaf.map i =
    (structureSheaf R).1.map i := rfl

@[elementwise]
theorem stalkMap_toStalk {R S : CommRingCat.{u}} (f : R ⟶ S) (p : PrimeSpectrum S) :
    toStalk R (PrimeSpectrum.comap f p) ≫ (Spec.sheafedSpaceMap f).stalkMap p =
      f ≫ toStalk S p := by
  rw [← toOpen_germ S ⊤ p trivial, ← toOpen_germ R ⊤ (PrimeSpectrum.comap f p) trivial,
    Category.assoc]
  erw [PresheafedSpace.stalkMap_germ (Spec.sheafedSpaceMap f) ⊤ p trivial]
  rw [Spec.sheafedSpaceMap_c_app]
  erw [toOpen_comp_comap_assoc]
  rfl

/-- Under the isomorphisms `stalkIso`, the map `stalkMap (Spec.sheafedSpaceMap f) p` corresponds
to the induced local ring homomorphism `Localization.localRingHom`.
-/
@[elementwise]
theorem localRingHom_comp_stalkIso {R S : CommRingCat.{u}} (f : R ⟶ S) (p : PrimeSpectrum S) :
    (stalkIso R (PrimeSpectrum.comap f p)).hom ≫
        @CategoryStruct.comp _ _
          (CommRingCat.of (Localization.AtPrime (PrimeSpectrum.comap f p).asIdeal))
          (CommRingCat.of (Localization.AtPrime p.asIdeal)) _
          (Localization.localRingHom (PrimeSpectrum.comap f p).asIdeal p.asIdeal f rfl)
          (stalkIso S p).inv =
      (Spec.sheafedSpaceMap f).stalkMap p :=
  (stalkIso R (PrimeSpectrum.comap f p)).eq_inv_comp.mp <|
    (stalkIso S p).comp_inv_eq.mpr <|
      Localization.localRingHom_unique _ _ _ _ fun x => by
        -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644 and #8386
        rw [stalkIso_hom, stalkIso_inv]
        erw [comp_apply, comp_apply, localizationToStalk_of, stalkMap_toStalk_apply f p x,
            stalkToFiberRingHom_toStalk]

variable {R S: Type} [Semiring R] [Semiring S] {f : R →+* S} (p : Ideal S)

def IsLocalRingHom.mk (map_nonunit : ∀ (a : R), IsUnit (f a) → IsUnit a) : IsLocalRingHom f :=
  ⟨map_nonunit⟩

def IsLocalRingHom.map_nonunit (a : R) : IsUnit (f a) → IsUnit a := sorry

/--
The induced map of a ring homomorphism on the prime spectra, as a morphism of locally ringed spaces.
-/
@[simps toShHom]
def Spec.locallyRingedSpaceMap {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Spec.locallyRingedSpaceObj S ⟶ Spec.locallyRingedSpaceObj R :=
  LocallyRingedSpace.Hom.mk (Spec.sheafedSpaceMap f) fun p =>
    IsLocalHom.mk fun a ha => by
      -- Here, we are showing that the map on prime spectra induced by `f` is really a morphism of
      -- *locally* ringed spaces, i.e. that the induced map on the stalks is a local ring
      -- homomorphism.

      #adaptation_note /-- nightly-2024-04-01
      It's this `erw` that is blowing up. The implicit arguments differ significantly. -/
      haveI inst: IsLocalHom (Localization.localRingHom (PrimeSpectrum.comap f p).asIdeal p.asIdeal f rfl) := inferInstance
      #check (localizationToStalk (↑S) p)
      erw [← localRingHom_comp_stalkIso_apply] at ha
      -- Porting note: `f` had to be made explicit
      replace ha := IsLocalRingHom.map_nonunit
        (f := fun v => (localizationToStalk (↑S) p) ((Localization.localRingHom (PrimeSpectrum.comap f p).asIdeal p.asIdeal f rfl) v)) (stalkToFiberRingHom (↑R) ((PrimeSpectrum.comap f) p)) ha
        -- replace ha := IsLocalHom.map_nonunit (self := inst)
        -- (f := (Localization.localRingHom (PrimeSpectrum.comap f p).asIdeal p.asIdeal f rfl)) ((stalkToFiberRingHom (↑R) ((PrimeSpectrum.comap f) p)) a) ha
      convert RingHom.isUnit_map (stalkIso R (PrimeSpectrum.comap f p)).inv ha
      erw [← comp_apply, show stalkToFiberRingHom R _ = (stalkIso _ _).hom from rfl,
        Iso.hom_inv_id, id_apply]

@[simp]
theorem Spec.locallyRingedSpaceMap_id (R : CommRingCat.{u}) :
    Spec.locallyRingedSpaceMap (𝟙 R) = 𝟙 (Spec.locallyRingedSpaceObj R) :=
  LocallyRingedSpace.Hom.ext' <| by
    rw [Spec.locallyRingedSpaceMap_toShHom, Spec.sheafedSpaceMap_id]; rfl

theorem Spec.locallyRingedSpaceMap_comp {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    Spec.locallyRingedSpaceMap (f ≫ g) =
      Spec.locallyRingedSpaceMap g ≫ Spec.locallyRingedSpaceMap f :=
  LocallyRingedSpace.Hom.ext' <| by
    rw [Spec.locallyRingedSpaceMap_toShHom, Spec.sheafedSpaceMap_comp]; rfl

/-- Spec, as a contravariant functor from commutative rings to locally ringed spaces.
-/
@[simps]
def Spec.toLocallyRingedSpace : CommRingCat.{u}ᵒᵖ ⥤ LocallyRingedSpace where
  obj R := Spec.locallyRingedSpaceObj (unop R)
  map f := Spec.locallyRingedSpaceMap f.unop
  map_id R := by dsimp; rw [Spec.locallyRingedSpaceMap_id]
  map_comp f g := by dsimp; rw [Spec.locallyRingedSpaceMap_comp]

section SpecΓ

open AlgebraicGeometry.LocallyRingedSpace

/-- The counit morphism `R ⟶ Γ(Spec R)` given by `AlgebraicGeometry.StructureSheaf.toOpen`. -/
@[simps!]
def toSpecΓ (R : CommRingCat.{u}) : R ⟶ Γ.obj (op (Spec.toLocallyRingedSpace.obj (op R))) :=
  StructureSheaf.toOpen R ⊤

-- These lemmas have always been bad (#7657), but leanprover/lean4#2644 made `simp` start noticing
attribute [nolint simpNF] AlgebraicGeometry.toSpecΓ_apply_coe

instance isIso_toSpecΓ (R : CommRingCat.{u}) : IsIso (toSpecΓ R) := by
  cases R; apply StructureSheaf.isIso_to_global

@[reassoc]
theorem Spec_Γ_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) :
    f ≫ toSpecΓ S = toSpecΓ R ≫ Γ.map (Spec.toLocallyRingedSpace.map f.op).op := by
  -- Porting note: `ext` failed to pick up one of the three lemmas
  refine RingHom.ext fun x => Subtype.ext <| funext fun x' => ?_; symm
  apply Localization.localRingHom_to_map

/-- The counit (`SpecΓIdentity.inv.op`) of the adjunction `Γ ⊣ Spec` is an isomorphism. -/
@[simps! hom_app inv_app]
def LocallyRingedSpace.SpecΓIdentity : Spec.toLocallyRingedSpace.rightOp ⋙ Γ ≅ 𝟭 _ :=
  Iso.symm <| NatIso.ofComponents.{u,u,u+1,u+1} (fun R =>
    -- Porting note: In Lean3, this `IsIso` is synthesized automatically
    letI : IsIso (toSpecΓ R) := StructureSheaf.isIso_to_global _
    asIso (toSpecΓ R)) fun {X Y} f => by convert Spec_Γ_naturality (R := X) (S := Y) f

end SpecΓ

/-- The stalk map of `Spec M⁻¹R ⟶ Spec R` is an iso for each `p : Spec M⁻¹R`. -/
theorem Spec_map_localization_isIso (R : CommRingCat.{u}) (M : Submonoid R)
    (x : PrimeSpectrum (Localization M)) :
    IsIso
      ((Spec.toPresheafedSpace.map
        (CommRingCat.ofHom (algebraMap R (Localization M))).op).stalkMap x) := by
  erw [← localRingHom_comp_stalkIso]
  -- Porting note: replaced `apply (config := { instances := false })`.
  -- See https://github.com/leanprover/lean4/issues/2273
  refine IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' ?_ inferInstance)
  /- I do not know why this is defeq to the goal, but I'm happy to accept that it is. -/
  show
    IsIso (IsLocalization.localizationLocalizationAtPrimeIsoLocalization M
      x.asIdeal).toRingEquiv.toCommRingCatIso.hom
  infer_instance

namespace StructureSheaf

variable {R S : CommRingCat.{u}} (f : R ⟶ S) (p : PrimeSpectrum R)

/-- For an algebra `f : R →+* S`, this is the ring homomorphism `S →+* (f∗ 𝒪ₛ)ₚ` for a `p : Spec R`.
This is shown to be the localization at `p` in `isLocalizedModule_toPushforwardStalkAlgHom`.
-/
def toPushforwardStalk : S ⟶ (Spec.topMap f _* (structureSheaf S).1).stalk p :=
  StructureSheaf.toOpen S ⊤ ≫
    @TopCat.Presheaf.germ _ _ _ _ (Spec.topMap f _* (structureSheaf S).1) ⊤ p trivial

@[reassoc]
theorem toPushforwardStalk_comp :
    f ≫ StructureSheaf.toPushforwardStalk f p =
      StructureSheaf.toStalk R p ≫
        (TopCat.Presheaf.stalkFunctor _ _).map (Spec.sheafedSpaceMap f).c := by
  rw [StructureSheaf.toStalk, Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ]
  exact Spec_Γ_naturality_assoc f _

instance : Algebra R ((Spec.topMap f _* (structureSheaf S).1).stalk p) :=
  (f ≫ StructureSheaf.toPushforwardStalk f p).toAlgebra

theorem algebraMap_pushforward_stalk :
    algebraMap R ((Spec.topMap f _* (structureSheaf S).1).stalk p) =
      f ≫ StructureSheaf.toPushforwardStalk f p :=
  rfl

variable (R S)
variable [Algebra R S]

/--
This is the `AlgHom` version of `toPushforwardStalk`, which is the map `S ⟶ (f∗ 𝒪ₛ)ₚ` for some
algebra `R ⟶ S` and some `p : Spec R`.
-/
@[simps!]
def toPushforwardStalkAlgHom :
    S →ₐ[R] (Spec.topMap (algebraMap R S) _* (structureSheaf S).1).stalk p :=
  { StructureSheaf.toPushforwardStalk (algebraMap R S) p with commutes' := fun _ => rfl }

theorem isLocalizedModule_toPushforwardStalkAlgHom_aux (y) :
    ∃ x : S × p.asIdeal.primeCompl, x.2 • y = toPushforwardStalkAlgHom R S p x.1 := by
  obtain ⟨U, hp, s, e⟩ := TopCat.Presheaf.germ_exist
    -- Porting note: originally the first variable does not need to be explicit
    (Spec.topMap (algebraMap ↑R ↑S) _* (structureSheaf S).val) _ y
  obtain ⟨_, ⟨r, rfl⟩, hpr : p ∈ PrimeSpectrum.basicOpen r, hrU : PrimeSpectrum.basicOpen r ≤ U⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (show p ∈ U from hp) U.2
  change PrimeSpectrum.basicOpen r ≤ U at hrU
  replace e :=
    ((Spec.topMap (algebraMap R S) _* (structureSheaf S).1).germ_res_apply (homOfLE hrU)
          p hpr _).trans e
  set s' := (Spec.topMap (algebraMap R S) _* (structureSheaf S).1).map (homOfLE hrU).op s with h
  replace e : ((Spec.topMap (algebraMap R S) _* (structureSheaf S).val).germ _ p hpr) s' = y := by
    rw [h]; exact e
  clear_value s'; clear! U
  obtain ⟨⟨s, ⟨_, n, rfl⟩⟩, hsn⟩ :=
    @IsLocalization.surj _ _ _ _ _ _
      (StructureSheaf.IsLocalization.to_basicOpen S <| algebraMap R S r) s'
  refine ⟨⟨s, ⟨r, hpr⟩ ^ n⟩, ?_⟩
  rw [Submonoid.smul_def, Algebra.smul_def, algebraMap_pushforward_stalk, toPushforwardStalk,
    comp_apply, comp_apply]
  iterate 2
    erw [← (Spec.topMap (algebraMap R S) _* (structureSheaf S).1).germ_res_apply (homOfLE le_top)
      p hpr]
  rw [← e]
  -- Porting note: without this `change`, Lean doesn't know how to rewrite `map_mul`
  let f := TopCat.Presheaf.germ (Spec.topMap (algebraMap R S) _* (structureSheaf S).val) _ p hpr
  change f _ * f _ = f _
  rw [← map_mul, mul_comm]
  dsimp only [Subtype.coe_mk] at hsn
  rw [← map_pow (algebraMap R S)] at hsn
  congr 1

instance isLocalizedModule_toPushforwardStalkAlgHom :
    IsLocalizedModule p.asIdeal.primeCompl (toPushforwardStalkAlgHom R S p).toLinearMap := by
  apply IsLocalizedModule.mkOfAlgebra
  · intro x hx; rw [algebraMap_pushforward_stalk, toPushforwardStalk_comp]
    change IsUnit ((TopCat.Presheaf.stalkFunctor CommRingCat p).map
      (Spec.sheafedSpaceMap (algebraMap ↑R ↑S)).c _)
    exact (IsLocalization.map_units ((structureSheaf R).presheaf.stalk p) ⟨x, hx⟩).map _
  · apply isLocalizedModule_toPushforwardStalkAlgHom_aux
  · intro x hx
    rw [toPushforwardStalkAlgHom_apply, ← (toPushforwardStalk (algebraMap R S) p).map_zero,
      toPushforwardStalk] at hx
    -- Porting note: this `change` is manually rewriting `comp_apply`
    change _ = (TopCat.Presheaf.germ (Spec.topMap (algebraMap ↑R ↑S) _* (structureSheaf ↑S).val)
      ⊤ p trivial (toOpen S ⊤ 0)) at hx
    rw [map_zero] at hx
    change (forget CommRingCat).map _ _ = (forget _).map _ _ at hx
    obtain ⟨U, hpU, i₁, i₂, e⟩ := TopCat.Presheaf.germ_eq _ _ _ _ _ _ hx
    obtain ⟨_, ⟨r, rfl⟩, hpr, hrU⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (show p ∈ U.1 from hpU)
        U.2
    change PrimeSpectrum.basicOpen r ≤ U at hrU
    apply_fun (Spec.topMap (algebraMap R S) _* (structureSheaf S).1).map (homOfLE hrU).op at e
    simp only [Functor.op_map, map_zero, ← comp_apply, toOpen_res] at e
    have : toOpen S (PrimeSpectrum.basicOpen <| algebraMap R S r) x = 0 := by
      refine Eq.trans ?_ e; rfl
    have :=
      (@IsLocalization.mk'_one _ _ _ _ _ _
            (StructureSheaf.IsLocalization.to_basicOpen S <| algebraMap R S r) x).trans
        this
    obtain ⟨⟨_, n, rfl⟩, e⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp this
    refine ⟨⟨r, hpr⟩ ^ n, ?_⟩
    rw [Submonoid.smul_def, Algebra.smul_def]
    -- Porting note: manually rewrite `Submonoid.coe_pow`
    change (algebraMap R S) (r ^ n) * x = 0
    rw [map_pow]
    exact e

end StructureSheaf

end AlgebraicGeometry
