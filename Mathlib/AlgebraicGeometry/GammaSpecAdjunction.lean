/-
Copyright (c) 2021 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Adjunction.Opposites
public import Mathlib.CategoryTheory.Adjunction.Reflective

/-!
# Adjunction between `Γ` and `Spec`

We define the adjunction `ΓSpec.adjunction : Γ ⊣ Spec` by defining the unit (`toΓSpec`,
in multiple steps in this file) and counit (done in `Spec.lean`) and checking that they satisfy
the left and right triangle identities. The constructions and proofs make use of
maps and lemmas defined and proved in structure_sheaf.lean extensively.

Notice that since the adjunction is between contravariant functors, you get to choose
one of the two categories to have arrows reversed, and it is equally valid to present
the adjunction as `Spec ⊣ Γ` (`Spec.to_LocallyRingedSpace.right_op ⊣ Γ`), in which
case the unit and the counit would switch to each other.

## Main definition

* `AlgebraicGeometry.identityToΓSpec` : The natural transformation `𝟭 _ ⟶ Γ ⋙ Spec`.
* `AlgebraicGeometry.ΓSpec.locallyRingedSpaceAdjunction` : The adjunction `Γ ⊣ Spec` from
  `CommRingᵒᵖ` to `LocallyRingedSpace`.
* `AlgebraicGeometry.ΓSpec.adjunction` : The adjunction `Γ ⊣ Spec` from
  `CommRingᵒᵖ` to `Scheme`.

-/

@[expose] public section

-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737


noncomputable section

universe u

open PrimeSpectrum

namespace AlgebraicGeometry

open Opposite

open CategoryTheory

open StructureSheaf

open Spec (structureSheaf)

open TopologicalSpace

open AlgebraicGeometry.LocallyRingedSpace

open TopCat.Presheaf

open TopCat.Presheaf.SheafCondition

namespace LocallyRingedSpace

variable (X : LocallyRingedSpace.{u})

/-- The canonical map from the underlying set to the prime spectrum of `Γ(X)`. -/
def toΓSpecFun : X → PrimeSpectrum (Γ.obj (op X)) := fun x =>
  comap (X.presheaf.Γgerm x).hom (IsLocalRing.closedPoint (X.presheaf.stalk x))

theorem notMem_prime_iff_unit_in_stalk (r : Γ.obj (op X)) (x : X) :
    r ∉ (X.toΓSpecFun x).asIdeal ↔ IsUnit (X.presheaf.Γgerm x r) := by
  simp [toΓSpecFun, IsLocalRing.closedPoint]

/-- The preimage of a basic open in `Spec Γ(X)` under the unit is the basic
open in `X` defined by the same element (they are equal as sets). -/
theorem toΓSpec_preimage_basicOpen_eq (r : Γ.obj (op X)) :
    X.toΓSpecFun ⁻¹' basicOpen r = SetLike.coe (X.toRingedSpace.basicOpen r) := by
      ext
      dsimp
      simp only [Set.mem_preimage, SetLike.mem_coe]
      rw [X.toRingedSpace.mem_top_basicOpen]
      exact notMem_prime_iff_unit_in_stalk ..

/-- `toΓSpecFun` is continuous. -/
theorem toΓSpec_continuous : Continuous X.toΓSpecFun := by
  rw [isTopologicalBasis_basic_opens.continuous_iff]
  rintro _ ⟨r, rfl⟩
  rw [X.toΓSpec_preimage_basicOpen_eq r]
  exact (X.toRingedSpace.basicOpen r).2

/-- The canonical (bundled) continuous map from the underlying topological
space of `X` to the prime spectrum of its global sections. -/
def toΓSpecBase : X.toTopCat ⟶ Spec.topObj (Γ.obj (op X)) :=
  TopCat.ofHom
  { toFun := X.toΓSpecFun
    continuous_toFun := X.toΓSpec_continuous }

variable (r : Γ.obj (op X))

/-- The preimage in `X` of a basic open in `Spec Γ(X)` (as an open set). -/
abbrev toΓSpecMapBasicOpen : Opens X :=
  (Opens.map X.toΓSpecBase).obj (basicOpen r)

/-- The preimage is the basic open in `X` defined by the same element `r`. -/
theorem toΓSpecMapBasicOpen_eq : X.toΓSpecMapBasicOpen r = X.toRingedSpace.basicOpen r :=
  Opens.ext (X.toΓSpec_preimage_basicOpen_eq r)

/-- The map from the global sections `Γ(X)` to the sections on the (preimage of) a basic open. -/
abbrev toToΓSpecMapBasicOpen :
    X.presheaf.obj (op ⊤) ⟶ X.presheaf.obj (op <| X.toΓSpecMapBasicOpen r) :=
  X.presheaf.map (X.toΓSpecMapBasicOpen r).leTop.op

/-- `r` is a unit as a section on the basic open defined by `r`. -/
theorem isUnit_res_toΓSpecMapBasicOpen : IsUnit (X.toToΓSpecMapBasicOpen r r) := by
  convert
    (X.presheaf.map <| (eqToHom <| X.toΓSpecMapBasicOpen_eq r).op).hom.isUnit_map
      (X.toRingedSpace.isUnit_res_basicOpen r)
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  congr

/-- Define the sheaf hom on individual basic opens for the unit. -/
def toΓSpecCApp :
    (structureSheaf <| Γ.obj <| op X).val.obj (op <| basicOpen r) ⟶
      X.presheaf.obj (op <| X.toΓSpecMapBasicOpen r) :=
  -- note: the explicit type annotations were not needed before
  -- https://github.com/leanprover-community/mathlib4/pull/19757
  CommRingCat.ofHom <|
    IsLocalization.Away.lift
      (R := Γ.obj (op X))
      (S := (structureSheaf ↑(Γ.obj (op X))).val.obj (op (basicOpen r)))
      r
      (isUnit_res_toΓSpecMapBasicOpen _ r)

/-- Characterization of the sheaf hom on basic opens,
direction ← (next lemma) is used at various places, but → is not used in this file. -/
theorem toΓSpecCApp_iff
    (f :
      (structureSheaf <| Γ.obj <| op X).val.obj (op <| basicOpen r) ⟶
        X.presheaf.obj (op <| X.toΓSpecMapBasicOpen r)) :
    CommRingCat.ofHom (algebraMap (Γ.obj (op X)) _) ≫ f = X.toToΓSpecMapBasicOpen r ↔
      f = X.toΓSpecCApp r := by
  have loc_inst := IsLocalization.to_basicOpen (Γ.obj (op X)) r
  refine ConcreteCategory.ext_iff.trans ?_
  rw [← @IsLocalization.Away.lift_comp _ _ _ _ _ _ _ r loc_inst _
      (X.isUnit_res_toΓSpecMapBasicOpen r)]
  constructor
  · intro h
    ext : 1
    exact IsLocalization.ringHom_ext (Submonoid.powers r) h
  apply congr_arg

theorem toΓSpecCApp_spec :
    CommRingCat.ofHom (algebraMap (Γ.obj (op X)) _) ≫ X.toΓSpecCApp r = X.toToΓSpecMapBasicOpen r :=
  (X.toΓSpecCApp_iff r _).2 rfl

/-- The sheaf hom on all basic opens, commuting with restrictions. -/
@[simps app]
def toΓSpecCBasicOpens :
    (inducedFunctor basicOpen).op ⋙ (structureSheaf (Γ.obj (op X))).1 ⟶
      (inducedFunctor basicOpen).op ⋙ ((TopCat.Sheaf.pushforward _ X.toΓSpecBase).obj X.𝒪).1 where
  app r := X.toΓSpecCApp r.unop
  naturality r s f := by
    apply (StructureSheaf.to_basicOpen_epi (Γ.obj (op X)) r.unop).1
    simp only [← Category.assoc]
    erw [X.toΓSpecCApp_spec r.unop]
    convert X.toΓSpecCApp_spec s.unop
    symm
    apply X.presheaf.map_comp

/-- The canonical morphism of sheafed spaces from `X` to the spectrum of its global sections. -/
@[simps! -isSimp]
def toΓSpecSheafedSpace : X.toSheafedSpace ⟶ Spec.toSheafedSpace.obj (op (Γ.obj (op X))) :=
  InducedCategory.homMk
    { base := X.toΓSpecBase
      c :=
        TopCat.Sheaf.restrictHomEquivHom (structureSheaf (Γ.obj (op X))).1 _ isBasis_basic_opens
          X.toΓSpecCBasicOpens }

theorem toΓSpecSheafedSpace_app_eq :
    X.toΓSpecSheafedSpace.hom.c.app (op (basicOpen r)) = X.toΓSpecCApp r := by
  apply TopCat.Sheaf.extend_hom_app _ _ _

@[reassoc] theorem toΓSpecSheafedSpace_app_spec (r : Γ.obj (op X)) :
    CommRingCat.ofHom (algebraMap (Γ.obj (op X)) _) ≫
        X.toΓSpecSheafedSpace.hom.c.app (op (basicOpen r)) =
      X.toToΓSpecMapBasicOpen r :=
  (X.toΓSpecSheafedSpace_app_eq r).symm ▸ X.toΓSpecCApp_spec r

/-- The map on stalks induced by the unit commutes with maps from `Γ(X)` to
stalks (in `Spec Γ(X)` and in `X`). -/
theorem toStalk_stalkMap_toΓSpec (x : X) :
    toStalk _ _ ≫ X.toΓSpecSheafedSpace.hom.stalkMap x = X.presheaf.Γgerm x := by
  rw [PresheafedSpace.Hom.stalkMap,
    ← algebraMap_germ (basicOpen (1 : Γ.obj (op X))) _ (by rw [basicOpen_one]; trivial),
    ← Category.assoc, Category.assoc (CommRingCat.ofHom _), stalkFunctor_map_germ, ← Category.assoc,
    X.toΓSpecSheafedSpace_app_eq, X.toΓSpecCApp_spec, Γgerm]
  erw [← stalkPushforward_germ _ _ X.presheaf ⊤]
  congr 1
  exact (X.toΓSpecBase _* X.presheaf).germ_res le_top.hom _ _

/-- The canonical morphism from `X` to the spectrum of its global sections. -/
@[simps! base]
def toΓSpec : X ⟶ Spec.locallyRingedSpaceObj (Γ.obj (op X)) :=
  LocallyRingedSpace.homMk (X.toΓSpecSheafedSpace) (fun x ↦ by
    let p : PrimeSpectrum (Γ.obj (op X)) := X.toΓSpecFun x
    constructor
    -- show stalk map is local hom ↓
    let S := (structureSheaf _).presheaf.stalk p
    rintro (t : S) ht
    obtain ⟨⟨r, s⟩, he⟩ := IsLocalization.surj p.asIdeal.primeCompl t
    dsimp at he
    set t' := _
    change t * t' = _ at he
    apply isUnit_of_mul_isUnit_left (y := t')
    rw [he]
    refine IsLocalization.map_units S (⟨r, ?_⟩ : p.asIdeal.primeCompl)
    apply (notMem_prime_iff_unit_in_stalk _ _ _).mpr
    rw [← toStalk_stalkMap_toΓSpec, CommRingCat.comp_apply]
    erw [← he]
    rw [map_mul]
    exact ht.mul <| (IsLocalization.map_units (R := Γ.obj (op X)) S s).map _)

/-- On a locally ringed space `X`, the preimage of the zero locus of the prime spectrum
of `Γ(X, ⊤)` under `toΓSpec` agrees with the associated zero locus on `X`. -/
lemma toΓSpec_preimage_zeroLocus_eq {X : LocallyRingedSpace.{u}}
    (s : Set (X.presheaf.obj (op ⊤))) :
    X.toΓSpec.base ⁻¹' PrimeSpectrum.zeroLocus s = X.toRingedSpace.zeroLocus s := by
  simp only [RingedSpace.zeroLocus]
  have (i : LocallyRingedSpace.Γ.obj (op X)) (_ : i ∈ s) :
      (SetLike.coe (X.toRingedSpace.basicOpen i))ᶜ =
        X.toΓSpec.base ⁻¹' ((PrimeSpectrum.basicOpen i).carrier)ᶜ := by
    symm
    rw [Set.preimage_compl, Opens.carrier_eq_coe]
    erw [X.toΓSpec_preimage_basicOpen_eq i]
  erw [Set.iInter₂_congr this]
  simp_rw [← Set.preimage_iInter₂, Opens.carrier_eq_coe, PrimeSpectrum.basicOpen_eq_zeroLocus_compl,
    compl_compl]
  rw [← PrimeSpectrum.zeroLocus_iUnion₂]
  simp

theorem comp_ring_hom_ext {X : LocallyRingedSpace.{u}} {R : CommRingCat.{u}} {f : R ⟶ Γ.obj (op X)}
    {β : X ⟶ Spec.locallyRingedSpaceObj R}
    (w : X.toΓSpec.base ≫ (Spec.locallyRingedSpaceMap f).base = β.base)
    (h :
      ∀ r : R,
        f ≫ X.presheaf.map (homOfLE le_top : (Opens.map β.base).obj (basicOpen r) ⟶ _).op =
          CommRingCat.ofHom (algebraMap _ _) ≫ β.c.app (op (basicOpen r))) :
    X.toΓSpec ≫ Spec.locallyRingedSpaceMap f = β := by
  refine LocallyRingedSpace.forgetToSheafedSpace.map_injective
    (Spec.basicOpen_hom_ext w ?_)
  intro r U
  erw [SheafedSpace.comp_hom_c_app, toOpen_comp_comap_assoc]
  dsimp
  rw [Category.assoc]
  erw [toΓSpecSheafedSpace_app_spec, ← X.presheaf.map_comp]
  exact h r

/-- `toSpecΓ _` is an isomorphism so these are mutually two-sided inverses. -/
theorem Γ_Spec_left_triangle : toSpecΓ (Γ.obj (op X)) ≫ X.toΓSpec.c.app (op ⊤) = 𝟙 _ := by
  unfold toSpecΓ
  have := X.toΓSpecSheafedSpace_app_spec 1
  unfold toToΓSpecMapBasicOpen toΓSpecMapBasicOpen at this
  rw! [basicOpen_one] at this
  convert this
  exact (X.presheaf.map_id ..).symm

end LocallyRingedSpace

/-- The unit as a natural transformation. -/
def identityToΓSpec : 𝟭 LocallyRingedSpace.{u} ⟶ Γ.rightOp ⋙ Spec.toLocallyRingedSpace where
  app := LocallyRingedSpace.toΓSpec
  naturality X Y f := by
    symm
    apply LocallyRingedSpace.comp_ring_hom_ext
    · ext1 x
      dsimp
      change PrimeSpectrum.comap (f.c.app (op ⊤)).hom (X.toΓSpecFun x) = Y.toΓSpecFun (f.base x)
      dsimp [toΓSpecFun]
      rw [← IsLocalRing.comap_closedPoint (f.stalkMap x).hom, ←
        PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply,
        ← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
      congr 2
      exact (PresheafedSpace.stalkMap_germ f.1 ⊤ x trivial).symm
    · intro r
      rw [LocallyRingedSpace.comp_c_app, ← Category.assoc]
      erw [Y.toΓSpecSheafedSpace_app_spec, f.c.naturality]
      rfl

namespace ΓSpec

theorem left_triangle (X : LocallyRingedSpace) :
    SpecΓIdentity.inv.app (Γ.obj (op X)) ≫ (identityToΓSpec.app X).c.app (op ⊤) = 𝟙 _ :=
  X.Γ_Spec_left_triangle

/-- `SpecΓIdentity` is iso so these are mutually two-sided inverses. -/
theorem right_triangle (R : CommRingCat) :
    identityToΓSpec.app (Spec.toLocallyRingedSpace.obj <| op R) ≫
        Spec.toLocallyRingedSpace.map (SpecΓIdentity.inv.app R).op =
      𝟙 _ := by
  apply LocallyRingedSpace.comp_ring_hom_ext
  · ext (p : PrimeSpectrum R)
    dsimp
    refine PrimeSpectrum.ext (Ideal.ext fun x => ?_)
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff ((structureSheaf R).presheaf.stalk p)
        p.asIdeal x]
    rfl
  · intro r; rfl

/-- The adjunction `Γ ⊣ Spec` from `CommRingᵒᵖ` to `LocallyRingedSpace`. -/
@[simps]
def locallyRingedSpaceAdjunction : Γ.rightOp ⊣ Spec.toLocallyRingedSpace.{u} where
  unit := identityToΓSpec
  counit := (NatIso.op SpecΓIdentity).inv
  left_triangle_components X := by
    simp only [Functor.id_obj, Functor.rightOp_obj, Γ_obj, Functor.comp_obj,
      Spec.toLocallyRingedSpace_obj, Spec.locallyRingedSpaceObj_toSheafedSpace,
      Spec.sheafedSpaceObj_carrier, Spec.sheafedSpaceObj_presheaf, Functor.rightOp_map, Γ_map,
      Quiver.Hom.unop_op, NatIso.op_inv, NatTrans.op_app, SpecΓIdentity_inv_app]
    exact congr_arg Quiver.Hom.op (left_triangle X)
  right_triangle_components R := by
    simp only [Spec.toLocallyRingedSpace_obj, Functor.id_obj, Functor.comp_obj, Functor.rightOp_obj,
      Γ_obj, Spec.locallyRingedSpaceObj_toSheafedSpace, Spec.sheafedSpaceObj_carrier,
      Spec.sheafedSpaceObj_presheaf, NatIso.op_inv, NatTrans.op_app, op_unop, SpecΓIdentity_inv_app,
      Spec.toLocallyRingedSpace_map, Quiver.Hom.unop_op]
    exact right_triangle R.unop


lemma toSpecΓ_unop (R : CommRingCatᵒᵖ) :
    AlgebraicGeometry.toSpecΓ (Opposite.unop R) = CommRingCat.ofHom (algebraMap _ _) := rfl

/-- `@[simp]`-normal form of `locallyRingedSpaceAdjunction_counit_app'`. -/
@[simp]
lemma toSpecΓ_of (R : Type u) [CommRing R] :
    AlgebraicGeometry.toSpecΓ (CommRingCat.of R) = CommRingCat.ofHom (algebraMap _ _) := rfl

lemma locallyRingedSpaceAdjunction_counit_app (R : CommRingCatᵒᵖ) :
    locallyRingedSpaceAdjunction.counit.app R =
      (CommRingCat.ofHom (algebraMap _ _)).op := rfl

lemma locallyRingedSpaceAdjunction_counit_app' (R : Type u) [CommRing R] :
    locallyRingedSpaceAdjunction.counit.app (op <| CommRingCat.of R) =
      (CommRingCat.ofHom (algebraMap _ _)).op := rfl

lemma unop_locallyRingedSpaceAdjunction_counit_app' (R : Type u) [CommRing R] :
    (locallyRingedSpaceAdjunction.counit.app (op <| CommRingCat.of R)).unop =
      (CommRingCat.ofHom (algebraMap _ _)) := rfl

lemma locallyRingedSpaceAdjunction_homEquiv_apply
    {X : LocallyRingedSpace} {R : CommRingCatᵒᵖ}
    (f : Γ.rightOp.obj X ⟶ R) :
    locallyRingedSpaceAdjunction.homEquiv X R f =
      identityToΓSpec.app X ≫ Spec.locallyRingedSpaceMap f.unop := rfl

lemma locallyRingedSpaceAdjunction_homEquiv_apply'
    {X : LocallyRingedSpace} {R : Type u} [CommRing R]
    (f : CommRingCat.of R ⟶ Γ.obj <| op X) :
    locallyRingedSpaceAdjunction.homEquiv X (op <| CommRingCat.of R) (op f) =
      identityToΓSpec.app X ≫ Spec.locallyRingedSpaceMap f := rfl

lemma toOpen_comp_locallyRingedSpaceAdjunction_homEquiv_app
    {X : LocallyRingedSpace} {R : Type u} [CommRing R]
    (f : Γ.rightOp.obj X ⟶ op (CommRingCat.of R)) (U) :
    CommRingCat.ofHom (algebraMap R _) ≫
      (locallyRingedSpaceAdjunction.homEquiv X (op <| CommRingCat.of R) f).c.app U =
    f.unop ≫ X.presheaf.map (homOfLE le_top).op := by
  dsimp
  rw [← StructureSheaf.algebraMap_self_map _ U _ (homOfLE le_top).op, Category.assoc,
    NatTrans.naturality _ (homOfLE (le_top (a := U.unop))).op,
    ← unop_locallyRingedSpaceAdjunction_counit_app']
  simp_rw [← Γ_map_op]
  rw [← Γ.rightOp_map_unop, ← Category.assoc, ← unop_comp]
  erw [← Adjunction.homEquiv_counit, Equiv.symm_apply_apply]
  rfl

/-- The adjunction `Γ ⊣ Spec` from `CommRingᵒᵖ` to `Scheme`. -/
def adjunction : Scheme.Γ.rightOp ⊣ Scheme.Spec.{u} where
  unit :=
  { app := fun X ↦ ⟨locallyRingedSpaceAdjunction.{u}.unit.app X.toLocallyRingedSpace⟩
    naturality := fun _ _ f ↦
      Scheme.Hom.ext' (locallyRingedSpaceAdjunction.{u}.unit.naturality f.toLRSHom) }
  counit := (NatIso.op Scheme.SpecΓIdentity.{u}).inv
  left_triangle_components Y :=
    locallyRingedSpaceAdjunction.left_triangle_components Y.toLocallyRingedSpace
  right_triangle_components R :=
    Scheme.Hom.ext' <| locallyRingedSpaceAdjunction.right_triangle_components R

theorem adjunction_homEquiv_apply {X : Scheme} {R : CommRingCatᵒᵖ}
    (f : (op <| Scheme.Γ.obj <| op X) ⟶ R) :
    ΓSpec.adjunction.homEquiv X R f = ⟨locallyRingedSpaceAdjunction.homEquiv X.1 R f⟩ := rfl

theorem adjunction_homEquiv_symm_apply {X : Scheme} {R : CommRingCatᵒᵖ}
    (f : X ⟶ Scheme.Spec.obj R) :
    (ΓSpec.adjunction.homEquiv X R).symm f =
      (locallyRingedSpaceAdjunction.homEquiv X.1 R).symm f.toLRSHom := rfl

theorem adjunction_counit_app' {R : CommRingCatᵒᵖ} :
    ΓSpec.adjunction.counit.app R = locallyRingedSpaceAdjunction.counit.app R := rfl

@[simp]
theorem adjunction_counit_app {R : CommRingCatᵒᵖ} :
    ΓSpec.adjunction.counit.app R = (Scheme.ΓSpecIso (unop R)).inv.op := rfl

/-- The canonical map `X ⟶ Spec Γ(X, ⊤)`. This is the unit of the `Γ-Spec` adjunction. -/
def _root_.AlgebraicGeometry.Scheme.toSpecΓ (X : Scheme.{u}) : X ⟶ Spec Γ(X, ⊤) :=
  ΓSpec.adjunction.unit.app X

@[simp]
theorem adjunction_unit_app {X : Scheme} :
    ΓSpec.adjunction.unit.app X = X.toSpecΓ := rfl

instance isIso_locallyRingedSpaceAdjunction_counit :
    IsIso.{u + 1, u + 1} locallyRingedSpaceAdjunction.counit :=
  (NatIso.op SpecΓIdentity).isIso_inv

instance isIso_adjunction_counit : IsIso ΓSpec.adjunction.counit := by
  apply +allowSynthFailures NatIso.isIso_of_isIso_app
  intro R
  rw [adjunction_counit_app]
  infer_instance

end ΓSpec

theorem Scheme.toSpecΓ_apply (X : Scheme.{u}) (x) :
    Scheme.toSpecΓ X x = Spec.map (X.presheaf.Γgerm x) (IsLocalRing.closedPoint _) := rfl

@[deprecated (since := "2025-10-17")] alias Scheme.toSpecΓ_base := Scheme.toSpecΓ_apply

@[reassoc]
theorem Scheme.toSpecΓ_naturality {X Y : Scheme.{u}} (f : X ⟶ Y) :
    f ≫ Y.toSpecΓ = X.toSpecΓ ≫ Spec.map f.appTop :=
  ΓSpec.adjunction.unit.naturality f

@[simp]
theorem Scheme.toSpecΓ_appTop (X : Scheme.{u}) :
    X.toSpecΓ.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).hom := by
  have := ΓSpec.adjunction.left_triangle_components X
  dsimp at this
  rw [← IsIso.eq_comp_inv] at this
  simp only [Category.id_comp] at this
  rw [← Quiver.Hom.op_inj.eq_iff, this, ← op_inv, IsIso.Iso.inv_inv]

@[simp]
theorem SpecMap_ΓSpecIso_hom (R : CommRingCat.{u}) :
    Spec.map ((Scheme.ΓSpecIso R).hom) = (Spec R).toSpecΓ := by
  have := ΓSpec.adjunction.right_triangle_components (op R)
  dsimp at this
  rwa [← IsIso.eq_comp_inv, Category.id_comp, ← Spec.map_inv, IsIso.Iso.inv_inv, eq_comm] at this

@[reassoc (attr := simp)]
theorem SpecMap_ΓSpecIso_inv_toSpecΓ (R : CommRingCat.{u}) :
    Spec.map (Scheme.ΓSpecIso R).inv ≫ (Spec R).toSpecΓ = 𝟙 _ := by
  rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.hom_inv_id, Spec.map_id]

@[reassoc (attr := simp)]
theorem toSpecΓ_SpecMap_ΓSpecIso_inv (R : CommRingCat.{u}) :
    (Spec R).toSpecΓ ≫ Spec.map (Scheme.ΓSpecIso R).inv = 𝟙 _ := by
  rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]

lemma Scheme.toSpecΓ_preimage_basicOpen (X : Scheme.{u}) (r : Γ(X, ⊤)) :
    X.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen r = X.basicOpen r := by
  rw [← basicOpen_eq_of_affine, Scheme.preimage_basicOpen, ← Scheme.Hom.appTop]
  congr
  rw [Scheme.toSpecΓ_appTop]
  exact Iso.inv_hom_id_apply (C := CommRingCat) _ _

-- -- Warning: this LHS of this lemma breaks the structure-sheaf abstraction.
-- @[reassoc (attr := simp)]
-- theorem toOpen_toSpecΓ_app {X : Scheme.{u}} (U) :
--     CommRingCat.ofHom (algebraMap _ ((Spec.structureSheaf _).presheaf.obj _)) ≫ X.toSpecΓ.app U =
--       X.presheaf.map (homOfLE (le_top)).op := by
--   sorry
--   rw [← StructureSheaf.toOpen_res _ _ _ (homOfLE le_top), Category.assoc,
--     NatTrans.naturality _ (homOfLE (le_top (a := U))).op]
--   change (ΓSpec.adjunction.counit.app (Scheme.Γ.rightOp.obj X)).unop ≫
--     (Scheme.Γ.rightOp.map (ΓSpec.adjunction.unit.app X)).unop ≫ _ = _
--   rw [← Category.assoc, ← unop_comp, ΓSpec.adjunction.left_triangle_components]
--   dsimp
--   exact Category.id_comp _

lemma ΓSpecIso_inv_ΓSpec_adjunction_homEquiv {X : Scheme.{u}} {B : CommRingCat} (φ : B ⟶ Γ(X, ⊤)) :
    (Scheme.ΓSpecIso B).inv ≫ ((ΓSpec.adjunction.homEquiv X (op B)) φ.op).appTop = φ := by
  simp only [Adjunction.homEquiv_apply, Scheme.Spec_map, Opens.map_top, Scheme.Hom.comp_app]
  simp

lemma ΓSpec_adjunction_homEquiv_eq {X : Scheme.{u}} {B : CommRingCat} (φ : B ⟶ Γ(X, ⊤)) :
    ((ΓSpec.adjunction.homEquiv X (op B)) φ.op).appTop = (Scheme.ΓSpecIso B).hom ≫ φ := by
  rw [← Iso.inv_comp_eq, ΓSpecIso_inv_ΓSpec_adjunction_homEquiv]

theorem ΓSpecIso_obj_hom {X : Scheme.{u}} (U : X.Opens) :
    (Scheme.ΓSpecIso Γ(X, U)).hom = (Spec.map U.topIso.inv).appTop ≫
      U.toScheme.toSpecΓ.appTop ≫ U.topIso.hom := by simp

/-! Immediate consequences of the adjunction. -/

/-- The functor `Spec.toLocallyRingedSpace : CommRingCatᵒᵖ ⥤ LocallyRingedSpace`
is fully faithful. -/
def Spec.fullyFaithfulToLocallyRingedSpace : Spec.toLocallyRingedSpace.FullyFaithful :=
  ΓSpec.locallyRingedSpaceAdjunction.fullyFaithfulROfIsIsoCounit

/-- Spec is a full functor. -/
instance : Spec.toLocallyRingedSpace.Full :=
  Spec.fullyFaithfulToLocallyRingedSpace.full

/-- Spec is a faithful functor. -/
instance : Spec.toLocallyRingedSpace.Faithful :=
  Spec.fullyFaithfulToLocallyRingedSpace.faithful

/-- The functor `Spec : CommRingCatᵒᵖ ⥤ Scheme` is fully faithful. -/
def Spec.fullyFaithful : Scheme.Spec.FullyFaithful :=
  ΓSpec.adjunction.fullyFaithfulROfIsIsoCounit

/-- Spec is a full functor. -/
instance Spec.full : Scheme.Spec.Full :=
  Spec.fullyFaithful.full

/-- Spec is a faithful functor. -/
instance Spec.faithful : Scheme.Spec.Faithful :=
  Spec.fullyFaithful.faithful

section

variable {R S : CommRingCat.{u}} {φ ψ : R ⟶ S} (f : Spec S ⟶ Spec R)

lemma Spec.map_inj : Spec.map φ = Spec.map ψ ↔ φ = ψ := by
  rw [iff_comm, ← Quiver.Hom.op_inj.eq_iff, ← Scheme.Spec.map_injective.eq_iff]
  rfl

lemma Spec.map_injective {R S : CommRingCat} : Function.Injective (Spec.map : (R ⟶ S) → _) :=
  fun _ _ ↦ Spec.map_inj.mp

@[simp]
lemma Spec.map_eq_id {R : CommRingCat} {ϕ : R ⟶ R} : Spec.map ϕ = 𝟙 (Spec R) ↔ ϕ = 𝟙 R := by
  simp [← map_inj]

/-- The preimage under Spec. -/
def Spec.preimage : R ⟶ S := (Scheme.Spec.preimage f).unop

@[simp] lemma Spec.map_preimage : Spec.map (Spec.preimage f) = f := Scheme.Spec.map_preimage f

@[simp] lemma Spec.map_preimage_unop (f : Spec R ⟶ Spec S) :
    Spec.map (Spec.fullyFaithful.preimage f).unop = f := Spec.fullyFaithful.map_preimage _

variable (φ) in
@[simp] lemma Spec.preimage_map : Spec.preimage (Spec.map φ) = φ :=
  Spec.map_injective (Spec.map_preimage (Spec.map φ))

/-- Useful for replacing `f` by `Spec.map φ` everywhere in proofs. -/
lemma Spec.map_surjective {R S : CommRingCat} :
    Function.Surjective (Spec.map : (R ⟶ S) → _) := by
  intro f
  use Spec.preimage f
  simp

/-- Spec is fully faithful -/
@[simps]
def Spec.homEquiv {R S : CommRingCat} : (Spec S ⟶ Spec R) ≃ (R ⟶ S) where
  toFun := Spec.preimage
  invFun := Spec.map
  left_inv := Spec.map_preimage
  right_inv := Spec.preimage_map

@[simp]
lemma Spec.preimage_id {R : CommRingCat} : Spec.preimage (𝟙 (Spec R)) = 𝟙 R :=
  Spec.map_injective (by simp)

@[simp, reassoc]
lemma Spec.preimage_comp {R S T : CommRingCat} (f : Spec R ⟶ Spec S) (g : Spec S ⟶ Spec T) :
    Spec.preimage (f ≫ g) = Spec.preimage g ≫ Spec.preimage f :=
  Spec.map_injective (by simp)

end

instance : Reflective Spec.toLocallyRingedSpace where
  L := Γ.rightOp
  adj := ΓSpec.locallyRingedSpaceAdjunction

instance Spec.reflective : Reflective Scheme.Spec where
  L := Scheme.Γ.rightOp
  adj := ΓSpec.adjunction

instance : LocallyRingedSpace.Γ.IsRightAdjoint :=
  ΓSpec.locallyRingedSpaceAdjunction.rightOp.isRightAdjoint

instance : Scheme.Γ.IsRightAdjoint := ΓSpec.adjunction.rightOp.isRightAdjoint

end AlgebraicGeometry
