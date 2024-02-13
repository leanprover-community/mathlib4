/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Justus Springer
-/
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Algebra.Module.LocalizedModule

#align_import algebraic_geometry.Spec from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"

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


noncomputable section

universe u v

namespace AlgebraicGeometry

open Opposite

open CategoryTheory

open StructureSheaf

open Spec (structureSheaf)

/-- The spectrum of a commutative ring, as a topological space.
-/
def Spec.topObj (R : CommRingCat) : TopCat :=
  TopCat.of (PrimeSpectrum R)
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.Spec.Top_obj AlgebraicGeometry.Spec.topObj

/-- The induced map of a ring homomorphism on the ring spectra, as a morphism of topological spaces.
-/
def Spec.topMap {R S : CommRingCat} (f : R ⟶ S) : Spec.topObj S ⟶ Spec.topObj R :=
  PrimeSpectrum.comap f
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.Spec.Top_map AlgebraicGeometry.Spec.topMap

@[simp]
theorem Spec.topMap_id (R : CommRingCat) : Spec.topMap (𝟙 R) = 𝟙 (Spec.topObj R) :=
  PrimeSpectrum.comap_id
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.Spec.Top_map_id AlgebraicGeometry.Spec.topMap_id

theorem Spec.topMap_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T) :
    Spec.topMap (f ≫ g) = Spec.topMap g ≫ Spec.topMap f :=
  PrimeSpectrum.comap_comp _ _
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.Spec.Top_map_comp AlgebraicGeometry.Spec.topMap_comp

-- Porting note : `simps!` generate some garbage lemmas, so choose manually,
-- if more is needed, add them here
/-- The spectrum, as a contravariant functor from commutative rings to topological spaces.
-/
@[simps! obj map]
def Spec.toTop : CommRingCatᵒᵖ ⥤ TopCat where
  obj R := Spec.topObj (unop R)
  map {R S} f := Spec.topMap f.unop
  map_id R := by dsimp; rw [Spec.topMap_id]
  map_comp {R S T} f g := by dsimp; rw [Spec.topMap_comp]
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.Spec.to_Top AlgebraicGeometry.Spec.toTop

/-- The spectrum of a commutative ring, as a `SheafedSpace`.
-/
@[simps]
def Spec.sheafedSpaceObj (R : CommRingCat) : SheafedSpace CommRingCat where
  carrier := Spec.topObj R
  presheaf := (structureSheaf R).1
  IsSheaf := (structureSheaf R).2
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.Spec.SheafedSpace_obj AlgebraicGeometry.Spec.sheafedSpaceObj

/-- The induced map of a ring homomorphism on the ring spectra, as a morphism of sheafed spaces.
-/
@[simps]
def Spec.sheafedSpaceMap {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Spec.sheafedSpaceObj S ⟶ Spec.sheafedSpaceObj R where
  base := Spec.topMap f
  c :=
    { app := fun U =>
        comap f (unop U) ((TopologicalSpace.Opens.map (Spec.topMap f)).obj (unop U)) fun _ => id
      naturality := fun {_ _} _ => RingHom.ext fun _ => Subtype.eq <| funext fun _ => rfl }
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.Spec.SheafedSpace_map AlgebraicGeometry.Spec.sheafedSpaceMap

@[simp]
theorem Spec.sheafedSpaceMap_id {R : CommRingCat} :
    Spec.sheafedSpaceMap (𝟙 R) = 𝟙 (Spec.sheafedSpaceObj R) :=
  AlgebraicGeometry.PresheafedSpace.Hom.ext _ _ (Spec.topMap_id R) <| by
    ext U
    dsimp
    erw [PresheafedSpace.id_c_app, comap_id]; swap
    · rw [Spec.topMap_id, TopologicalSpace.Opens.map_id_obj_unop]
    simp [eqToHom_map]
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.Spec.SheafedSpace_map_id AlgebraicGeometry.Spec.sheafedSpaceMap_id

theorem Spec.sheafedSpaceMap_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T) :
    Spec.sheafedSpaceMap (f ≫ g) = Spec.sheafedSpaceMap g ≫ Spec.sheafedSpaceMap f :=
  AlgebraicGeometry.PresheafedSpace.Hom.ext _ _ (Spec.topMap_comp f g) <| by
    ext
    -- Porting note : was one liner
    -- `dsimp, rw category_theory.functor.map_id, rw category.comp_id, erw comap_comp f g, refl`
    rw [NatTrans.comp_app, sheafedSpaceMap_c_app, whiskerRight_app, eqToHom_refl]
    erw [(sheafedSpaceObj T).presheaf.map_id, Category.comp_id, comap_comp]
    rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.Spec.SheafedSpace_map_comp AlgebraicGeometry.Spec.sheafedSpaceMap_comp

/-- Spec, as a contravariant functor from commutative rings to sheafed spaces.
-/
@[simps]
def Spec.toSheafedSpace : CommRingCatᵒᵖ ⥤ SheafedSpace CommRingCat where
  obj R := Spec.sheafedSpaceObj (unop R)
  map f := Spec.sheafedSpaceMap f.unop
  map_id R := by dsimp; rw [Spec.sheafedSpaceMap_id]
  map_comp f g := by dsimp; rw [Spec.sheafedSpaceMap_comp]
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.Spec.to_SheafedSpace AlgebraicGeometry.Spec.toSheafedSpace

/-- Spec, as a contravariant functor from commutative rings to presheafed spaces.
-/
def Spec.toPresheafedSpace : CommRingCatᵒᵖ ⥤ PresheafedSpace.{_, _, u} CommRingCat :=
  Spec.toSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.Spec.to_PresheafedSpace AlgebraicGeometry.Spec.toPresheafedSpace

@[simp]
theorem Spec.toPresheafedSpace_obj (R : CommRingCatᵒᵖ) :
    Spec.toPresheafedSpace.obj R = (Spec.sheafedSpaceObj (unop R)).toPresheafedSpace :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.Spec.to_PresheafedSpace_obj AlgebraicGeometry.Spec.toPresheafedSpace_obj

theorem Spec.toPresheafedSpace_obj_op (R : CommRingCat) :
    Spec.toPresheafedSpace.obj (op R) = (Spec.sheafedSpaceObj R).toPresheafedSpace :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.Spec.to_PresheafedSpace_obj_op AlgebraicGeometry.Spec.toPresheafedSpace_obj_op

@[simp]
theorem Spec.toPresheafedSpace_map (R S : CommRingCatᵒᵖ) (f : R ⟶ S) :
    Spec.toPresheafedSpace.map f = Spec.sheafedSpaceMap f.unop :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.Spec.to_PresheafedSpace_map AlgebraicGeometry.Spec.toPresheafedSpace_map

theorem Spec.toPresheafedSpace_map_op (R S : CommRingCat) (f : R ⟶ S) :
    Spec.toPresheafedSpace.map f.op = Spec.sheafedSpaceMap f :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.Spec.to_PresheafedSpace_map_op AlgebraicGeometry.Spec.toPresheafedSpace_map_op

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
    -- Porting note : was a one-liner `simpa using h r`
    specialize h r
    simp only [sheafedSpaceObj_carrier, Functor.op_obj, unop_op, TopCat.Presheaf.pushforwardObj_obj,
      sheafedSpaceObj_presheaf, Category.assoc] at h
    rw [NatTrans.comp_app, ← h]
    congr
    simp
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.Spec.basic_open_hom_ext AlgebraicGeometry.Spec.basicOpen_hom_ext

-- Porting note : `simps!` generate some garbage lemmas, so choose manually,
-- if more is needed, add them here
/-- The spectrum of a commutative ring, as a `LocallyRingedSpace`.
-/
@[simps! toSheafedSpace]
def Spec.locallyRingedSpaceObj (R : CommRingCat) : LocallyRingedSpace :=
  { Spec.sheafedSpaceObj R with
    localRing := fun x =>
      RingEquiv.localRing (A := Localization.AtPrime x.asIdeal)
        (Iso.commRingCatIsoToRingEquiv <| stalkIso R x).symm }
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.Spec.LocallyRingedSpace_obj AlgebraicGeometry.Spec.locallyRingedSpaceObj

@[elementwise]
theorem stalkMap_toStalk {R S : CommRingCat} (f : R ⟶ S) (p : PrimeSpectrum S) :
    toStalk R (PrimeSpectrum.comap f p) ≫ PresheafedSpace.stalkMap (Spec.sheafedSpaceMap f) p =
      f ≫ toStalk S p := by
  erw [← toOpen_germ S ⊤ ⟨p, trivial⟩, ← toOpen_germ R ⊤ ⟨PrimeSpectrum.comap f p, trivial⟩,
    Category.assoc, PresheafedSpace.stalkMap_germ (Spec.sheafedSpaceMap f) ⊤ ⟨p, trivial⟩,
    Spec.sheafedSpaceMap_c_app, toOpen_comp_comap_assoc]
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.stalk_map_to_stalk AlgebraicGeometry.stalkMap_toStalk

/-- Under the isomorphisms `stalkIso`, the map `stalkMap (Spec.sheafedSpaceMap f) p` corresponds
to the induced local ring homomorphism `Localization.localRingHom`.
-/
@[elementwise]
theorem localRingHom_comp_stalkIso {R S : CommRingCat} (f : R ⟶ S) (p : PrimeSpectrum S) :
    (stalkIso R (PrimeSpectrum.comap f p)).hom ≫
        @CategoryStruct.comp _ _
          (CommRingCat.of (Localization.AtPrime (PrimeSpectrum.comap f p).asIdeal))
          (CommRingCat.of (Localization.AtPrime p.asIdeal)) _
          (Localization.localRingHom (PrimeSpectrum.comap f p).asIdeal p.asIdeal f rfl)
          (stalkIso S p).inv =
      PresheafedSpace.stalkMap (Spec.sheafedSpaceMap f) p :=
  (stalkIso R (PrimeSpectrum.comap f p)).eq_inv_comp.mp <|
    (stalkIso S p).comp_inv_eq.mpr <|
      Localization.localRingHom_unique _ _ _ _ fun x => by
        -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644 and #8386
        rw [stalkIso_hom, stalkIso_inv]
        erw [comp_apply, comp_apply, localizationToStalk_of, stalkMap_toStalk_apply f p x,
            stalkToFiberRingHom_toStalk]
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.local_ring_hom_comp_stalk_iso AlgebraicGeometry.localRingHom_comp_stalkIso

/--
The induced map of a ring homomorphism on the prime spectra, as a morphism of locally ringed spaces.
-/
@[simps]
def Spec.locallyRingedSpaceMap {R S : CommRingCat} (f : R ⟶ S) :
    Spec.locallyRingedSpaceObj S ⟶ Spec.locallyRingedSpaceObj R :=
  LocallyRingedSpace.Hom.mk (Spec.sheafedSpaceMap f) fun p =>
    IsLocalRingHom.mk fun a ha => by
      -- Here, we are showing that the map on prime spectra induced by `f` is really a morphism of
      -- *locally* ringed spaces, i.e. that the induced map on the stalks is a local ring
      -- homomorphism.
      erw [← localRingHom_comp_stalkIso_apply] at ha
      replace ha := (stalkIso S p).hom.isUnit_map ha
      rw [← comp_apply, show localizationToStalk S p = (stalkIso S p).inv from rfl,
        Iso.inv_hom_id, id_apply] at ha
      convert (ha.of_map).map (stalkIso R (PrimeSpectrum.comap f p)).inv
      erw [← comp_apply, show stalkToFiberRingHom R _ = (stalkIso _ _).hom from rfl,
           Iso.hom_inv_id, id_apply]
      -- note to reviewers: before refactor, this instance was found by instance search.
      -- maybe it's worth writing a version that has `hIJ` automatically? I guess instance
      -- search tried `rfl` before there.
      exact Localization.isLocalRingHom_localRingHom (PrimeSpectrum.comap f p).asIdeal _ f rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.Spec.LocallyRingedSpace_map AlgebraicGeometry.Spec.locallyRingedSpaceMap

@[simp]
theorem Spec.locallyRingedSpaceMap_id (R : CommRingCat) :
    Spec.locallyRingedSpaceMap (𝟙 R) = 𝟙 (Spec.locallyRingedSpaceObj R) :=
  LocallyRingedSpace.Hom.ext _ _ <| by
    rw [Spec.locallyRingedSpaceMap_val, Spec.sheafedSpaceMap_id]; rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.Spec.LocallyRingedSpace_map_id AlgebraicGeometry.Spec.locallyRingedSpaceMap_id

theorem Spec.locallyRingedSpaceMap_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T) :
    Spec.locallyRingedSpaceMap (f ≫ g) =
      Spec.locallyRingedSpaceMap g ≫ Spec.locallyRingedSpaceMap f :=
  LocallyRingedSpace.Hom.ext _ _ <| by
    rw [Spec.locallyRingedSpaceMap_val, Spec.sheafedSpaceMap_comp]; rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.Spec.LocallyRingedSpace_map_comp AlgebraicGeometry.Spec.locallyRingedSpaceMap_comp

/-- Spec, as a contravariant functor from commutative rings to locally ringed spaces.
-/
@[simps]
def Spec.toLocallyRingedSpace : CommRingCatᵒᵖ ⥤ LocallyRingedSpace where
  obj R := Spec.locallyRingedSpaceObj (unop R)
  map f := Spec.locallyRingedSpaceMap f.unop
  map_id R := by dsimp; rw [Spec.locallyRingedSpaceMap_id]
  map_comp f g := by dsimp; rw [Spec.locallyRingedSpaceMap_comp]
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.Spec.to_LocallyRingedSpace AlgebraicGeometry.Spec.toLocallyRingedSpace

section SpecΓ

open AlgebraicGeometry.LocallyRingedSpace

/-- The counit morphism `R ⟶ Γ(Spec R)` given by `AlgebraicGeometry.StructureSheaf.toOpen`.  -/
@[simps!]
def toSpecΓ (R : CommRingCat) : R ⟶ Γ.obj (op (Spec.toLocallyRingedSpace.obj (op R))) :=
  StructureSheaf.toOpen R ⊤
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.to_Spec_Γ AlgebraicGeometry.toSpecΓ

-- These lemmas have always been bad (#7657), but leanprover/lean4#2644 made `simp` start noticing
attribute [nolint simpNF] AlgebraicGeometry.toSpecΓ_apply_coe

instance isIso_toSpecΓ (R : CommRingCat) : IsIso (toSpecΓ R) := by
  cases R; apply StructureSheaf.isIso_to_global
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.is_iso_to_Spec_Γ AlgebraicGeometry.isIso_toSpecΓ

@[reassoc]
theorem Spec_Γ_naturality {R S : CommRingCat} (f : R ⟶ S) :
    f ≫ toSpecΓ S = toSpecΓ R ≫ Γ.map (Spec.toLocallyRingedSpace.map f.op).op := by
  -- Porting note : `ext` failed to pick up one of the three lemmas
  refine RingHom.ext fun x => Subtype.ext <| funext fun x' => ?_; symm;
  apply Localization.localRingHom_to_map
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.Spec_Γ_naturality AlgebraicGeometry.Spec_Γ_naturality

/-- The counit (`SpecΓIdentity.inv.op`) of the adjunction `Γ ⊣ Spec` is an isomorphism. -/
@[simps! hom_app inv_app]
def SpecΓIdentity : Spec.toLocallyRingedSpace.rightOp ⋙ Γ ≅ 𝟭 _ :=
  Iso.symm <| NatIso.ofComponents (fun R =>
    -- Porting note : In Lean3, this `IsIso` is synthesized automatically
    letI : IsIso (toSpecΓ R) := StructureSheaf.isIso_to_global _
    asIso (toSpecΓ R)) fun {X Y} f => by convert Spec_Γ_naturality (R := X) (S := Y) f
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.Spec_Γ_identity AlgebraicGeometry.SpecΓIdentity

end SpecΓ

/-- The stalk map of `Spec M⁻¹R ⟶ Spec R` is an iso for each `p : Spec M⁻¹R`. -/
theorem Spec_map_localization_isIso (R : CommRingCat) (M : Submonoid R)
    (x : PrimeSpectrum (Localization M)) :
    IsIso
      (PresheafedSpace.stalkMap
        (Spec.toPresheafedSpace.map (CommRingCat.ofHom (algebraMap R (Localization M))).op) x) := by
  erw [← localRingHom_comp_stalkIso]
  -- Porting note: replaced `apply (config := { instances := false })`.
  -- See https://github.com/leanprover/lean4/issues/2273
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ _ (?_)
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ (?_) _
  /- I do not know why this is defeq to the goal, but I'm happy to accept that it is. -/
  show
    IsIso (IsLocalization.localizationLocalizationAtPrimeIsoLocalization M
      x.asIdeal).toRingEquiv.toCommRingCatIso.hom
  infer_instance
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.Spec_map_localization_is_iso AlgebraicGeometry.Spec_map_localization_isIso

namespace StructureSheaf

variable {R S : CommRingCat.{u}} (f : R ⟶ S) (p : PrimeSpectrum R)

/-- For an algebra `f : R →+* S`, this is the ring homomorphism `S →+* (f∗ 𝒪ₛ)ₚ` for a `p : Spec R`.
This is shown to be the localization at `p` in `isLocalizedModule_toPushforwardStalkAlgHom`.
-/
def toPushforwardStalk : S ⟶ (Spec.topMap f _* (structureSheaf S).1).stalk p :=
  StructureSheaf.toOpen S ⊤ ≫
    @TopCat.Presheaf.germ _ _ _ _ (Spec.topMap f _* (structureSheaf S).1) ⊤ ⟨p, trivial⟩
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.structure_sheaf.to_pushforward_stalk AlgebraicGeometry.StructureSheaf.toPushforwardStalk

@[reassoc]
theorem toPushforwardStalk_comp :
    f ≫ StructureSheaf.toPushforwardStalk f p =
      StructureSheaf.toStalk R p ≫
        (TopCat.Presheaf.stalkFunctor _ _).map (Spec.sheafedSpaceMap f).c := by
  rw [StructureSheaf.toStalk]
  erw [Category.assoc]
  rw [TopCat.Presheaf.stalkFunctor_map_germ]
  exact Spec_Γ_naturality_assoc f _
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.structure_sheaf.to_pushforward_stalk_comp AlgebraicGeometry.StructureSheaf.toPushforwardStalk_comp

instance : Algebra R ((Spec.topMap f _* (structureSheaf S).1).stalk p) :=
  (f ≫ StructureSheaf.toPushforwardStalk f p).toAlgebra

theorem algebraMap_pushforward_stalk :
    algebraMap R ((Spec.topMap f _* (structureSheaf S).1).stalk p) =
      f ≫ StructureSheaf.toPushforwardStalk f p :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.structure_sheaf.algebra_map_pushforward_stalk AlgebraicGeometry.StructureSheaf.algebraMap_pushforward_stalk

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
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.structure_sheaf.to_pushforward_stalk_alg_hom AlgebraicGeometry.StructureSheaf.toPushforwardStalkAlgHom

theorem isLocalizedModule_toPushforwardStalkAlgHom_aux (y) :
    ∃ x : S × p.asIdeal.primeCompl, x.2 • y = toPushforwardStalkAlgHom R S p x.1 := by
  obtain ⟨U, hp, s, e⟩ := TopCat.Presheaf.germ_exist
    -- Porting note : originally the first variable does not need to be explicit
    (Spec.topMap (algebraMap ↑R ↑S) _* (structureSheaf S).val) _ y
  obtain ⟨_, ⟨r, rfl⟩, hpr : p ∈ PrimeSpectrum.basicOpen r, hrU : PrimeSpectrum.basicOpen r ≤ U⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (show p ∈ U from hp) U.2
  change PrimeSpectrum.basicOpen r ≤ U at hrU
  replace e :=
    ((Spec.topMap (algebraMap R S) _* (structureSheaf S).1).germ_res_apply (homOfLE hrU)
          ⟨p, hpr⟩ _).trans e
  set s' := (Spec.topMap (algebraMap R S) _* (structureSheaf S).1).map (homOfLE hrU).op s with h
  replace e : ((Spec.topMap (algebraMap R S) _* (structureSheaf S).val).germ ⟨p, hpr⟩) s' = y
  · rw [h]; exact e
  clear_value s'; clear! U
  obtain ⟨⟨s, ⟨_, n, rfl⟩⟩, hsn⟩ :=
    @IsLocalization.surj _ _ _ _ _ _
      (StructureSheaf.IsLocalization.to_basicOpen S <| algebraMap R S r) s'
  refine' ⟨⟨s, ⟨r, hpr⟩ ^ n⟩, _⟩
  rw [Submonoid.smul_def, Algebra.smul_def, algebraMap_pushforward_stalk, toPushforwardStalk,
    comp_apply, comp_apply]
  iterate 2
    erw [← (Spec.topMap (algebraMap R S) _* (structureSheaf S).1).germ_res_apply (homOfLE le_top)
      ⟨p, hpr⟩]
  rw [← e]
  -- Porting note : without this `change`, Lean doesn't know how to rewrite `map_mul`
  let f := TopCat.Presheaf.germ (Spec.topMap (algebraMap R S) _* (structureSheaf S).val) ⟨p, hpr⟩
  change f _ * f _ = f _
  rw [← map_mul, mul_comm]
  dsimp only [Subtype.coe_mk] at hsn
  rw [← map_pow (algebraMap R S)] at hsn
  congr 1
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.structure_sheaf.is_localized_module_to_pushforward_stalk_alg_hom_aux AlgebraicGeometry.StructureSheaf.isLocalizedModule_toPushforwardStalkAlgHom_aux

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
    -- Porting note : this `change` is manually rewriting `comp_apply`
    change _ = (TopCat.Presheaf.germ (Spec.topMap (algebraMap ↑R ↑S) _* (structureSheaf ↑S).val)
      (⟨p, trivial⟩ : (⊤ : TopologicalSpace.Opens (PrimeSpectrum R))) (toOpen S ⊤ 0)) at hx
    rw [map_zero] at hx
    change (forget CommRingCat).map _ _ = (forget _).map _ _ at hx
    obtain ⟨U, hpU, i₁, i₂, e⟩ := TopCat.Presheaf.germ_eq _ _ _ _ _ _ hx
    obtain ⟨_, ⟨r, rfl⟩, hpr, hrU⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (show p ∈ U.1 from hpU)
        U.2
    change PrimeSpectrum.basicOpen r ≤ U at hrU
    apply_fun (Spec.topMap (algebraMap R S) _* (structureSheaf S).1).map (homOfLE hrU).op at e
    simp only [TopCat.Presheaf.pushforwardObj_map, Functor.op_map, map_zero, ← comp_apply,
      toOpen_res] at e
    have : toOpen S (PrimeSpectrum.basicOpen <| algebraMap R S r) x = 0 := by
      refine' Eq.trans _ e; rfl
    have :=
      (@IsLocalization.mk'_one _ _ _ _ _ _
            (StructureSheaf.IsLocalization.to_basicOpen S <| algebraMap R S r) x).trans
        this
    obtain ⟨⟨_, n, rfl⟩, e⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp this
    refine' ⟨⟨r, hpr⟩ ^ n, _⟩
    rw [Submonoid.smul_def, Algebra.smul_def]
    -- Porting note : manually rewrite `Submonoid.coe_pow`
    change (algebraMap R S) (r ^ n) * x = 0
    rw [map_pow]
    exact e
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.structure_sheaf.is_localized_module_to_pushforward_stalk_alg_hom AlgebraicGeometry.StructureSheaf.isLocalizedModule_toPushforwardStalkAlgHom

end StructureSheaf

end AlgebraicGeometry
