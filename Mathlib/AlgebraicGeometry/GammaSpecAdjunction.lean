/-
Copyright (c) 2021 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Reflective

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

-- Explicit universe annotations were used in this file to improve performance #12737


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
  comap (X.presheaf.Γgerm x) (LocalRing.closedPoint (X.presheaf.stalk x))

theorem not_mem_prime_iff_unit_in_stalk (r : Γ.obj (op X)) (x : X) :
    r ∉ (X.toΓSpecFun x).asIdeal ↔ IsUnit (X.presheaf.Γgerm x r) := by
  erw [LocalRing.mem_maximalIdeal, Classical.not_not]

/-- The preimage of a basic open in `Spec Γ(X)` under the unit is the basic
open in `X` defined by the same element (they are equal as sets). -/
theorem toΓSpec_preimage_basicOpen_eq (r : Γ.obj (op X)) :
    X.toΓSpecFun ⁻¹' (basicOpen r).1 = (X.toRingedSpace.basicOpen r).1 := by
      ext
      erw [X.toRingedSpace.mem_top_basicOpen]; apply not_mem_prime_iff_unit_in_stalk

/-- `toΓSpecFun` is continuous. -/
theorem toΓSpec_continuous : Continuous X.toΓSpecFun := by
  rw [isTopologicalBasis_basic_opens.continuous_iff]
  rintro _ ⟨r, rfl⟩
  erw [X.toΓSpec_preimage_basicOpen_eq r]
  exact (X.toRingedSpace.basicOpen r).2

/-- The canonical (bundled) continuous map from the underlying topological
space of `X` to the prime spectrum of its global sections. -/
@[simps]
def toΓSpecBase : X.toTopCat ⟶ Spec.topObj (Γ.obj (op X)) where
  toFun := X.toΓSpecFun
  continuous_toFun := X.toΓSpec_continuous

-- These lemmas have always been bad (#7657), but lean4#2644 made `simp` start noticing
attribute [nolint simpNF] AlgebraicGeometry.LocallyRingedSpace.toΓSpecBase_apply

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
    (X.presheaf.map <| (eqToHom <| X.toΓSpecMapBasicOpen_eq r).op).isUnit_map
      (X.toRingedSpace.isUnit_res_basicOpen r)
  -- Porting note: `rw [comp_apply]` to `erw [comp_apply]`
  erw [← comp_apply, ← Functor.map_comp]
  congr

/-- Define the sheaf hom on individual basic opens for the unit. -/
def toΓSpecCApp :
    (structureSheaf <| Γ.obj <| op X).val.obj (op <| basicOpen r) ⟶
      X.presheaf.obj (op <| X.toΓSpecMapBasicOpen r) :=
  IsLocalization.Away.lift r (isUnit_res_toΓSpecMapBasicOpen _ r)

/-- Characterization of the sheaf hom on basic opens,
    direction ← (next lemma) is used at various places, but → is not used in this file. -/
theorem toΓSpecCApp_iff
    (f :
      (structureSheaf <| Γ.obj <| op X).val.obj (op <| basicOpen r) ⟶
        X.presheaf.obj (op <| X.toΓSpecMapBasicOpen r)) :
    toOpen _ (basicOpen r) ≫ f = X.toToΓSpecMapBasicOpen r ↔ f = X.toΓSpecCApp r := by
  -- Porting Note: Type class problem got stuck in `IsLocalization.Away.AwayMap.lift_comp`
  -- created instance manually. This replaces the `pick_goal` tactics
  have loc_inst := IsLocalization.to_basicOpen (Γ.obj (op X)) r
  rw [← @IsLocalization.Away.AwayMap.lift_comp _ _ _ _ _ _ _ r loc_inst _
      (X.isUnit_res_toΓSpecMapBasicOpen r)]
  --pick_goal 5; exact is_localization.to_basic_open _ r
  constructor
  · intro h
    exact IsLocalization.ringHom_ext (Submonoid.powers r) h
  apply congr_arg

theorem toΓSpecCApp_spec : toOpen _ (basicOpen r) ≫ X.toΓSpecCApp r = X.toToΓSpecMapBasicOpen r :=
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
@[simps]
def toΓSpecSheafedSpace : X.toSheafedSpace ⟶ Spec.toSheafedSpace.obj (op (Γ.obj (op X))) where
  base := X.toΓSpecBase
  c :=
    TopCat.Sheaf.restrictHomEquivHom (structureSheaf (Γ.obj (op X))).1 _ isBasis_basic_opens
      X.toΓSpecCBasicOpens

theorem toΓSpecSheafedSpace_app_eq :
    X.toΓSpecSheafedSpace.c.app (op (basicOpen r)) = X.toΓSpecCApp r := by
  apply TopCat.Sheaf.extend_hom_app _ _ _

-- Porting note: need a helper lemma `toΓSpecSheafedSpace_app_spec_assoc` to help compile
-- `toStalk_stalkMap_to_Γ_Spec`
@[reassoc] theorem toΓSpecSheafedSpace_app_spec (r : Γ.obj (op X)) :
    toOpen (Γ.obj (op X)) (basicOpen r) ≫ X.toΓSpecSheafedSpace.c.app (op (basicOpen r)) =
      X.toToΓSpecMapBasicOpen r :=
  (X.toΓSpecSheafedSpace_app_eq r).symm ▸ X.toΓSpecCApp_spec r

/-- The map on stalks induced by the unit commutes with maps from `Γ(X)` to
    stalks (in `Spec Γ(X)` and in `X`). -/
theorem toStalk_stalkMap_toΓSpec (x : X) :
    toStalk _ _ ≫ X.toΓSpecSheafedSpace.stalkMap x = X.presheaf.Γgerm x := by
  rw [PresheafedSpace.Hom.stalkMap]
  erw [← toOpen_germ _ (basicOpen (1 : Γ.obj (op X)))
      ⟨X.toΓSpecFun x, by rw [basicOpen_one]; trivial⟩]
  rw [← Category.assoc, Category.assoc (toOpen _ _)]
  erw [stalkFunctor_map_germ]
  rw [← Category.assoc, toΓSpecSheafedSpace_app_spec, Γgerm]
  rw [← stalkPushforward_germ _ X.toΓSpecBase X.presheaf ⊤]
  congr 1
  change (X.toΓSpecBase _* X.presheaf).map le_top.hom.op ≫ _ = _
  apply germ_res

/-- The canonical morphism from `X` to the spectrum of its global sections. -/
@[simps! val_base]
def toΓSpec : X ⟶ Spec.locallyRingedSpaceObj (Γ.obj (op X)) where
  val := X.toΓSpecSheafedSpace
  prop := by
    intro x
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
    apply (not_mem_prime_iff_unit_in_stalk _ _ _).mpr
    rw [← toStalk_stalkMap_toΓSpec]
    erw [comp_apply, ← he]
    rw [RingHom.map_mul]
    exact ht.mul <| (IsLocalization.map_units (R := Γ.obj (op X)) S s).map _

/-- On a locally ringed space `X`, the preimage of the zero locus of the prime spectrum
of `Γ(X, ⊤)` under `toΓSpec` agrees with the associated zero locus on `X`. -/
lemma toΓSpec_preimage_zeroLocus_eq {X : LocallyRingedSpace.{u}}
    (s : Set (X.presheaf.obj (op ⊤))) :
    X.toΓSpec.val.base ⁻¹' PrimeSpectrum.zeroLocus s = X.toRingedSpace.zeroLocus s := by
  simp only [RingedSpace.zeroLocus]
  have (i : LocallyRingedSpace.Γ.obj (op X)) (_ : i ∈ s) :
      ((X.toRingedSpace.basicOpen i).carrier)ᶜ =
        X.toΓSpec.val.base ⁻¹' (PrimeSpectrum.basicOpen i).carrierᶜ := by
    symm
    erw [Set.preimage_compl, X.toΓSpec_preimage_basicOpen_eq i]
  erw [Set.iInter₂_congr this]
  simp_rw [← Set.preimage_iInter₂, Opens.carrier_eq_coe, PrimeSpectrum.basicOpen_eq_zeroLocus_compl,
    compl_compl]
  rw [← PrimeSpectrum.zeroLocus_iUnion₂]
  simp

theorem comp_ring_hom_ext {X : LocallyRingedSpace.{u}} {R : CommRingCat.{u}} {f : R ⟶ Γ.obj (op X)}
    {β : X ⟶ Spec.locallyRingedSpaceObj R}
    (w : X.toΓSpec.1.base ≫ (Spec.locallyRingedSpaceMap f).1.base = β.1.base)
    (h :
      ∀ r : R,
        f ≫ X.presheaf.map (homOfLE le_top : (Opens.map β.1.base).obj (basicOpen r) ⟶ _).op =
          toOpen R (basicOpen r) ≫ β.1.c.app (op (basicOpen r))) :
    X.toΓSpec ≫ Spec.locallyRingedSpaceMap f = β := by
  ext1
  -- Porting note: was `apply Spec.basicOpen_hom_ext`
  refine Spec.basicOpen_hom_ext w ?_
  intro r U
  rw [LocallyRingedSpace.comp_val_c_app]
  erw [toOpen_comp_comap_assoc]
  rw [Category.assoc]
  erw [toΓSpecSheafedSpace_app_spec, ← X.presheaf.map_comp]
  exact h r

/-- `toSpecΓ _` is an isomorphism so these are mutually two-sided inverses. -/
theorem Γ_Spec_left_triangle : toSpecΓ (Γ.obj (op X)) ≫ X.toΓSpec.1.c.app (op ⊤) = 𝟙 _ := by
  unfold toSpecΓ
  rw [← toOpen_res _ (basicOpen (1 : Γ.obj (op X))) ⊤ (eqToHom basicOpen_one.symm)]
  erw [Category.assoc]
  rw [NatTrans.naturality, ← Category.assoc]
  erw [X.toΓSpecSheafedSpace_app_spec 1, ← Functor.map_comp]
  convert eqToHom_map X.presheaf _; rfl

end LocallyRingedSpace

/-- The unit as a natural transformation. -/
def identityToΓSpec : 𝟭 LocallyRingedSpace.{u} ⟶ Γ.rightOp ⋙ Spec.toLocallyRingedSpace where
  app := LocallyRingedSpace.toΓSpec
  naturality X Y f := by
    symm
    apply LocallyRingedSpace.comp_ring_hom_ext
    · ext1 x
      dsimp only [Spec.topMap, LocallyRingedSpace.toΓSpecFun]
      -- Porting note: Had to add the next four lines
      rw [comp_apply]
      dsimp [toΓSpecBase]
      -- The next six lines were `rw [ContinuousMap.coe_mk, ContinuousMap.coe_mk]` before
      -- leanprover/lean4#2644
      have : (ContinuousMap.mk (toΓSpecFun Y) (toΓSpec_continuous _)) (f.val.base x)
        = toΓSpecFun Y (f.val.base x) := by rw [ContinuousMap.coe_mk]
      erw [this]
      have : (ContinuousMap.mk (toΓSpecFun X) (toΓSpec_continuous _)) x
        = toΓSpecFun X x := by rw [ContinuousMap.coe_mk]
      erw [this]
      dsimp [toΓSpecFun]
      -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
      erw [← LocalRing.comap_closedPoint (f.stalkMap x), ←
        PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply]
      congr 2
      exact (PresheafedSpace.stalkMap_germ f.1 ⊤ ⟨x, trivial⟩).symm
    · intro r
      rw [LocallyRingedSpace.comp_val_c_app, ← Category.assoc]
      erw [Y.toΓSpecSheafedSpace_app_spec, f.1.c.naturality]
      rfl

namespace ΓSpec

theorem left_triangle (X : LocallyRingedSpace) :
    SpecΓIdentity.inv.app (Γ.obj (op X)) ≫ (identityToΓSpec.app X).val.c.app (op ⊤) = 𝟙 _ :=
  X.Γ_Spec_left_triangle

/-- `SpecΓIdentity` is iso so these are mutually two-sided inverses. -/
theorem right_triangle (R : CommRingCat) :
    identityToΓSpec.app (Spec.toLocallyRingedSpace.obj <| op R) ≫
        Spec.toLocallyRingedSpace.map (SpecΓIdentity.inv.app R).op =
      𝟙 _ := by
  apply LocallyRingedSpace.comp_ring_hom_ext
  · ext (p : PrimeSpectrum R)
    dsimp
    ext x
    erw [← IsLocalization.AtPrime.to_map_mem_maximal_iff ((structureSheaf R).presheaf.stalk p)
        p.asIdeal x]
    rfl
  · intro r; apply toOpen_res

/-- The adjunction `Γ ⊣ Spec` from `CommRingᵒᵖ` to `LocallyRingedSpace`. -/
-- Porting note: `simps` cause a time out, so `Unit` and `counit` will be added manually
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

lemma locallyRingedSpaceAdjunction_unit :
    locallyRingedSpaceAdjunction.unit = identityToΓSpec := rfl

lemma locallyRingedSpaceAdjunction_counit :
    locallyRingedSpaceAdjunction.counit = (NatIso.op SpecΓIdentity.{u}).inv := rfl

@[simp]
lemma locallyRingedSpaceAdjunction_counit_app (R : CommRingCatᵒᵖ) :
    locallyRingedSpaceAdjunction.counit.app R =
      (toOpen R.unop ⊤).op := rfl

@[simp]
lemma locallyRingedSpaceAdjunction_counit_app' (R : Type u) [CommRing R] :
    locallyRingedSpaceAdjunction.counit.app (op <| CommRingCat.of R) =
      (toOpen R ⊤).op := rfl

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
    StructureSheaf.toOpen R U.unop ≫
      (locallyRingedSpaceAdjunction.homEquiv X (op <| CommRingCat.of R) f).1.c.app U =
    f.unop ≫ X.presheaf.map (homOfLE le_top).op := by
  rw [← StructureSheaf.toOpen_res _ _ _ (homOfLE le_top), Category.assoc,
    NatTrans.naturality _ (homOfLE (le_top (a := U.unop))).op,
    show (toOpen R ⊤) = (toOpen R ⊤).op.unop from rfl,
    ← locallyRingedSpaceAdjunction_counit_app']
  simp_rw [← Γ_map_op]
  rw [← Γ.rightOp_map_unop, ← Category.assoc, ← unop_comp, ← Adjunction.homEquiv_counit,
    Equiv.symm_apply_apply]
  rfl

/-- The adjunction `Γ ⊣ Spec` from `CommRingᵒᵖ` to `Scheme`. -/
def adjunction : Scheme.Γ.rightOp ⊣ Scheme.Spec.{u} :=
  Adjunction.mk' {
    homEquiv := fun X Y ↦ locallyRingedSpaceAdjunction.{u}.homEquiv X.toLocallyRingedSpace Y
    unit :=
    { app := fun X ↦ locallyRingedSpaceAdjunction.{u}.unit.app X.toLocallyRingedSpace
      naturality := fun _ _ f ↦ locallyRingedSpaceAdjunction.{u}.unit.naturality f }
    counit := (NatIso.op Scheme.SpecΓIdentity.{u}).inv
    homEquiv_unit := rfl
    homEquiv_counit := rfl }

theorem adjunction_homEquiv_apply {X : Scheme} {R : CommRingCatᵒᵖ}
    (f : (op <| Scheme.Γ.obj <| op X) ⟶ R) :
    ΓSpec.adjunction.homEquiv X R f = locallyRingedSpaceAdjunction.homEquiv X.1 R f := rfl

theorem adjunction_homEquiv (X : Scheme) (R : CommRingCatᵒᵖ) :
    ΓSpec.adjunction.homEquiv X R = locallyRingedSpaceAdjunction.homEquiv X.1 R := rfl

theorem adjunction_homEquiv_symm_apply {X : Scheme} {R : CommRingCatᵒᵖ}
    (f : X ⟶ Scheme.Spec.obj R) :
    (ΓSpec.adjunction.homEquiv X R).symm f =
      (locallyRingedSpaceAdjunction.homEquiv X.1 R).symm f := rfl

theorem adjunction_counit_app' {R : CommRingCatᵒᵖ} :
    ΓSpec.adjunction.counit.app R = locallyRingedSpaceAdjunction.counit.app R := rfl

@[simp]
theorem adjunction_counit_app {R : CommRingCatᵒᵖ} :
    ΓSpec.adjunction.counit.app R = (Scheme.ΓSpecIso (unop R)).inv.op := rfl

-- This is not a simp lemma to respect the abstraction
theorem adjunction_unit_app {X : Scheme} :
    ΓSpec.adjunction.unit.app X = locallyRingedSpaceAdjunction.unit.app X.1 := rfl

@[reassoc (attr := simp)]
theorem adjunction_unit_naturality {X Y : Scheme.{u}} (f : X ⟶ Y) :
    f ≫ ΓSpec.adjunction.unit.app Y = ΓSpec.adjunction.unit.app X ≫ Spec.map (f.app ⊤) :=
  ΓSpec.adjunction.unit.naturality f

instance isIso_locallyRingedSpaceAdjunction_counit :
    IsIso.{u + 1, u + 1} locallyRingedSpaceAdjunction.counit :=
  (NatIso.op SpecΓIdentity).isIso_inv

instance isIso_adjunction_counit : IsIso ΓSpec.adjunction.counit := by
  apply (config := { allowSynthFailures := true }) NatIso.isIso_of_isIso_app
  intro R
  rw [adjunction_counit_app]
  infer_instance

@[simp]
theorem adjunction_unit_app_app_top (X : Scheme.{u}) :
    (ΓSpec.adjunction.unit.app X).app ⊤ = (Scheme.ΓSpecIso Γ(X, ⊤)).hom := by
  have := ΓSpec.adjunction.left_triangle_components X
  dsimp at this
  rw [← IsIso.eq_comp_inv] at this
  simp only [adjunction_counit_app, Functor.id_obj, Functor.comp_obj, Functor.rightOp_obj,
    Scheme.Γ_obj, Category.id_comp] at this
  rw [← Quiver.Hom.op_inj.eq_iff, this, ← op_inv, IsIso.Iso.inv_inv]

@[simp]
theorem SpecMap_ΓSpecIso_hom (R : CommRingCat.{u}) :
    Spec.map ((Scheme.ΓSpecIso R).hom) = adjunction.unit.app (Spec R) := by
  have := ΓSpec.adjunction.right_triangle_components (op R)
  dsimp at this
  rwa [← IsIso.eq_comp_inv, Category.id_comp, ← Spec.map_inv, IsIso.Iso.inv_inv, eq_comm] at this

lemma adjunction_unit_map_basicOpen (X : Scheme.{u}) (r : Γ(X, ⊤)) :
    (ΓSpec.adjunction.unit.app X ⁻¹ᵁ (PrimeSpectrum.basicOpen r)) = X.basicOpen r := by
  rw [← basicOpen_eq_of_affine]
  erw [Scheme.preimage_basicOpen]
  congr
  rw [ΓSpec.adjunction_unit_app_app_top]
  exact Iso.inv_hom_id_apply _ _

theorem toOpen_unit_app_val_c_app {X : Scheme.{u}} (U) :
    StructureSheaf.toOpen _ _ ≫ (ΓSpec.adjunction.unit.app X).val.c.app U =
      X.presheaf.map (homOfLE (by exact le_top)).op := by
  rw [← StructureSheaf.toOpen_res _ _ _ (homOfLE le_top), Category.assoc,
    NatTrans.naturality _ (homOfLE (le_top (a := U.unop))).op]
  show (ΓSpec.adjunction.counit.app (Scheme.Γ.rightOp.obj X)).unop ≫
    (Scheme.Γ.rightOp.map (ΓSpec.adjunction.unit.app X)).unop ≫ _ = _
  rw [← Category.assoc, ← unop_comp, ΓSpec.adjunction.left_triangle_components]
  dsimp
  exact Category.id_comp _

-- Warning: this LHS of this lemma breaks the structure-sheaf abstraction.
@[reassoc (attr := simp)]
theorem toOpen_unit_app_val_c_app' {X : Scheme.{u}} (U : Opens (PrimeSpectrum Γ(X, ⊤))) :
    toOpen Γ(X, ⊤) U ≫ (adjunction.unit.app X).app U =
      X.presheaf.map (homOfLE (by exact le_top)).op :=
  ΓSpec.toOpen_unit_app_val_c_app (op U)

end ΓSpec

theorem ΓSpecIso_obj_hom {X : Scheme.{u}} (U : X.Opens) :
    (Scheme.ΓSpecIso Γ(X, U)).hom = (Spec.map U.topIso.inv).app ⊤ ≫
      (ΓSpec.adjunction.unit.app U).app ⊤ ≫ U.topIso.hom := by
  rw [ΓSpec.adjunction_unit_app_app_top] -- why can't simp find this
  simp

/-! Immediate consequences of the adjunction. -/


/-- Spec preserves limits. -/
instance : Limits.PreservesLimits Spec.toLocallyRingedSpace :=
  ΓSpec.locallyRingedSpaceAdjunction.rightAdjointPreservesLimits

instance Spec.preservesLimits : Limits.PreservesLimits Scheme.Spec :=
  ΓSpec.adjunction.rightAdjointPreservesLimits

/-- The functor `Spec.toLocallyRingedSpace : CommRingCatᵒᵖ ⥤ LocallyRingedSpace`
is fully faithful.-/
def Spec.fullyFaithfulToLocallyRingedSpace : Spec.toLocallyRingedSpace.FullyFaithful :=
  ΓSpec.locallyRingedSpaceAdjunction.fullyFaithfulROfIsIsoCounit

/-- Spec is a full functor. -/
instance : Spec.toLocallyRingedSpace.Full :=
  Spec.fullyFaithfulToLocallyRingedSpace.full

/-- Spec is a faithful functor. -/
instance : Spec.toLocallyRingedSpace.Faithful :=
  Spec.fullyFaithfulToLocallyRingedSpace.faithful

/-- The functor `Spec : CommRingCatᵒᵖ ⥤ Scheme` is fully faithful.-/
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

/-- The preimage under Spec. -/
def Spec.preimage : R ⟶ S := (Scheme.Spec.preimage f).unop

@[simp] lemma Spec.map_preimage : Spec.map (Spec.preimage f) = f := Scheme.Spec.map_preimage f

variable (φ) in
@[simp] lemma Spec.preimage_map : Spec.preimage (Spec.map φ) = φ :=
  Spec.map_injective (Spec.map_preimage (Spec.map φ))

/-- Spec is fully faithful -/
@[simps]
def Spec.homEquiv {R S : CommRingCat} : (Spec S ⟶ Spec R) ≃ (R ⟶ S) where
  toFun := Spec.preimage
  invFun := Spec.map
  left_inv := Spec.map_preimage
  right_inv := Spec.preimage_map

end

instance : Spec.toLocallyRingedSpace.IsRightAdjoint :=
  (ΓSpec.locallyRingedSpaceAdjunction).isRightAdjoint

instance : Scheme.Spec.IsRightAdjoint :=
  (ΓSpec.adjunction).isRightAdjoint

instance : Reflective Spec.toLocallyRingedSpace where
  adj := ΓSpec.locallyRingedSpaceAdjunction

instance Spec.reflective : Reflective Scheme.Spec where
  adj := ΓSpec.adjunction

@[deprecated (since := "2024-07-02")]
alias LocallyRingedSpace.toΓSpec_preim_basicOpen_eq :=
  LocallyRingedSpace.toΓSpec_preimage_basicOpen_eq

end AlgebraicGeometry
