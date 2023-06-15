/-
Copyright (c) 2021 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu

! This file was ported from Lean 3 source module algebraic_geometry.Gamma_Spec_adjunction
! leanprover-community/mathlib commit d39590fc8728fbf6743249802486f8c91ffe07bc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicGeometry.Scheme
import Mathbin.CategoryTheory.Adjunction.Limits
import Mathbin.CategoryTheory.Adjunction.Reflective

/-!
# Adjunction between `Γ` and `Spec`

We define the adjunction `Γ_Spec.adjunction : Γ ⊣ Spec` by defining the unit (`to_Γ_Spec`,
in multiple steps in this file) and counit (done in Spec.lean) and checking that they satisfy
the left and right triangle identities. The constructions and proofs make use of
maps and lemmas defined and proved in structure_sheaf.lean extensively.

Notice that since the adjunction is between contravariant functors, you get to choose
one of the two categories to have arrows reversed, and it is equally valid to present
the adjunction as `Spec ⊣ Γ` (`Spec.to_LocallyRingedSpace.right_op ⊣ Γ`), in which
case the unit and the counit would switch to each other.

## Main definition

* `algebraic_geometry.identity_to_Γ_Spec` : The natural transformation `𝟭 _ ⟶ Γ ⋙ Spec`.
* `algebraic_geometry.Γ_Spec.LocallyRingedSpace_adjunction` : The adjunction `Γ ⊣ Spec` from
  `CommRingᵒᵖ` to `LocallyRingedSpace`.
* `algebraic_geometry.Γ_Spec.adjunction` : The adjunction `Γ ⊣ Spec` from
  `CommRingᵒᵖ` to `Scheme`.

-/


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

/-- The map from the global sections to a stalk. -/
def ΓToStalk (x : X) : Γ.obj (op X) ⟶ X.Presheaf.stalk x :=
  X.Presheaf.germ (⟨x, trivial⟩ : (⊤ : Opens X))
#align algebraic_geometry.LocallyRingedSpace.Γ_to_stalk AlgebraicGeometry.LocallyRingedSpace.ΓToStalk

/-- The canonical map from the underlying set to the prime spectrum of `Γ(X)`. -/
def toΓSpecFun : X → PrimeSpectrum (Γ.obj (op X)) := fun x =>
  comap (X.ΓToStalk x) (LocalRing.closedPoint (X.Presheaf.stalk x))
#align algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_fun AlgebraicGeometry.LocallyRingedSpace.toΓSpecFun

theorem not_mem_prime_iff_unit_in_stalk (r : Γ.obj (op X)) (x : X) :
    r ∉ (X.toΓSpecFun x).asIdeal ↔ IsUnit (X.ΓToStalk x r) := by
  erw [LocalRing.mem_maximalIdeal, Classical.not_not]
#align algebraic_geometry.LocallyRingedSpace.not_mem_prime_iff_unit_in_stalk AlgebraicGeometry.LocallyRingedSpace.not_mem_prime_iff_unit_in_stalk

/-- The preimage of a basic open in `Spec Γ(X)` under the unit is the basic
open in `X` defined by the same element (they are equal as sets). -/
theorem to_Γ_Spec_preim_basicOpen_eq (r : Γ.obj (op X)) :
    X.toΓSpecFun ⁻¹' (basicOpen r).1 = (X.toRingedSpace.basicOpen r).1 := by ext;
  erw [X.to_RingedSpace.mem_top_basic_open]; apply not_mem_prime_iff_unit_in_stalk
#align algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_preim_basic_open_eq AlgebraicGeometry.LocallyRingedSpace.to_Γ_Spec_preim_basicOpen_eq

/-- `to_Γ_Spec_fun` is continuous. -/
theorem to_Γ_Spec_continuous : Continuous X.toΓSpecFun :=
  by
  apply is_topological_basis_basic_opens.continuous
  rintro _ ⟨r, rfl⟩
  erw [X.to_Γ_Spec_preim_basic_open_eq r]
  exact (X.to_RingedSpace.basic_open r).2
#align algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_continuous AlgebraicGeometry.LocallyRingedSpace.to_Γ_Spec_continuous

/-- The canonical (bundled) continuous map from the underlying topological
space of `X` to the prime spectrum of its global sections. -/
@[simps]
def toΓSpecBase : X.toTopCat ⟶ Spec.topObj (Γ.obj (op X))
    where
  toFun := X.toΓSpecFun
  continuous_toFun := X.to_Γ_Spec_continuous
#align algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_base AlgebraicGeometry.LocallyRingedSpace.toΓSpecBase

variable (r : Γ.obj (op X))

/-- The preimage in `X` of a basic open in `Spec Γ(X)` (as an open set). -/
abbrev toΓSpecMapBasicOpen : Opens X :=
  (Opens.map X.toΓSpecBase).obj (basicOpen r)
#align algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_map_basic_open AlgebraicGeometry.LocallyRingedSpace.toΓSpecMapBasicOpen

/-- The preimage is the basic open in `X` defined by the same element `r`. -/
theorem toΓSpecMapBasicOpen_eq : X.toΓSpecMapBasicOpen r = X.toRingedSpace.basicOpen r :=
  Opens.ext (X.to_Γ_Spec_preim_basicOpen_eq r)
#align algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_map_basic_open_eq AlgebraicGeometry.LocallyRingedSpace.toΓSpecMapBasicOpen_eq

/-- The map from the global sections `Γ(X)` to the sections on the (preimage of) a basic open. -/
abbrev toToΓSpecMapBasicOpen :
    X.Presheaf.obj (op ⊤) ⟶ X.Presheaf.obj (op <| X.toΓSpecMapBasicOpen r) :=
  X.Presheaf.map (X.toΓSpecMapBasicOpen r).le_top.op
#align algebraic_geometry.LocallyRingedSpace.to_to_Γ_Spec_map_basic_open AlgebraicGeometry.LocallyRingedSpace.toToΓSpecMapBasicOpen

/-- `r` is a unit as a section on the basic open defined by `r`. -/
theorem isUnit_res_toΓSpecMapBasicOpen : IsUnit (X.toToΓSpecMapBasicOpen r r) :=
  by
  convert
    (X.presheaf.map <| (eq_to_hom <| X.to_Γ_Spec_map_basic_open_eq r).op).isUnit_map
      (X.to_RingedSpace.is_unit_res_basic_open r)
  rw [← comp_apply]
  erw [← functor.map_comp]
  congr
#align algebraic_geometry.LocallyRingedSpace.is_unit_res_to_Γ_Spec_map_basic_open AlgebraicGeometry.LocallyRingedSpace.isUnit_res_toΓSpecMapBasicOpen

/-- Define the sheaf hom on individual basic opens for the unit. -/
def toΓSpecCApp :
    (structureSheaf <| Γ.obj <| op X).val.obj (op <| basicOpen r) ⟶
      X.Presheaf.obj (op <| X.toΓSpecMapBasicOpen r) :=
  IsLocalization.Away.lift r (isUnit_res_toΓSpecMapBasicOpen _ r)
#align algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_c_app AlgebraicGeometry.LocallyRingedSpace.toΓSpecCApp

/-- Characterization of the sheaf hom on basic opens,
    direction ← (next lemma) is used at various places, but → is not used in this file. -/
theorem toΓSpecCApp_iff
    (f :
      (structureSheaf <| Γ.obj <| op X).val.obj (op <| basicOpen r) ⟶
        X.Presheaf.obj (op <| X.toΓSpecMapBasicOpen r)) :
    toOpen _ (basicOpen r) ≫ f = X.toToΓSpecMapBasicOpen r ↔ f = X.toΓSpecCApp r :=
  by
  rw [← IsLocalization.Away.AwayMap.lift_comp r (X.is_unit_res_to_Γ_Spec_map_basic_open r)]
  pick_goal 5; exact is_localization.to_basic_open _ r
  constructor
  · intro h; refine' IsLocalization.ringHom_ext _ _
    pick_goal 5; exact is_localization.to_basic_open _ r; exact h
  apply congr_arg
#align algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_c_app_iff AlgebraicGeometry.LocallyRingedSpace.toΓSpecCApp_iff

theorem toΓSpecCApp_spec : toOpen _ (basicOpen r) ≫ X.toΓSpecCApp r = X.toToΓSpecMapBasicOpen r :=
  (X.toΓSpecCApp_iff r _).2 rfl
#align algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_c_app_spec AlgebraicGeometry.LocallyRingedSpace.toΓSpecCApp_spec

/-- The sheaf hom on all basic opens, commuting with restrictions. -/
def toΓSpecCBasicOpens :
    (inducedFunctor basicOpen).op ⋙ (structureSheaf (Γ.obj (op X))).1 ⟶
      (inducedFunctor basicOpen).op ⋙ ((TopCat.Sheaf.pushforward X.toΓSpecBase).obj X.𝒪).1
    where
  app r := X.toΓSpecCApp r.unop
  naturality' r s f :=
    by
    apply (structure_sheaf.to_basic_open_epi (Γ.obj (op X)) r.unop).1
    simp only [← category.assoc]
    erw [X.to_Γ_Spec_c_app_spec r.unop]
    convert X.to_Γ_Spec_c_app_spec s.unop
    symm
    apply X.presheaf.map_comp
#align algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_c_basic_opens AlgebraicGeometry.LocallyRingedSpace.toΓSpecCBasicOpens

/-- The canonical morphism of sheafed spaces from `X` to the spectrum of its global sections. -/
@[simps]
def toΓSpecSheafedSpace : X.toSheafedSpace ⟶ Spec.toSheafedSpace.obj (op (Γ.obj (op X)))
    where
  base := X.toΓSpecBase
  c :=
    TopCat.Sheaf.restrictHomEquivHom (structureSheaf (Γ.obj (op X))).1 _ isBasis_basic_opens
      X.toΓSpecCBasicOpens
#align algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_SheafedSpace AlgebraicGeometry.LocallyRingedSpace.toΓSpecSheafedSpace

theorem toΓSpecSheafedSpace_app_eq :
    X.toΓSpecSheafedSpace.c.app (op (basicOpen r)) = X.toΓSpecCApp r :=
  TopCat.Sheaf.extend_hom_app _ _ _ _ _
#align algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_SheafedSpace_app_eq AlgebraicGeometry.LocallyRingedSpace.toΓSpecSheafedSpace_app_eq

theorem toΓSpecSheafedSpace_app_spec (r : Γ.obj (op X)) :
    toOpen _ (basicOpen r) ≫ X.toΓSpecSheafedSpace.c.app (op (basicOpen r)) =
      X.toToΓSpecMapBasicOpen r :=
  (X.toΓSpecSheafedSpace_app_eq r).symm ▸ X.toΓSpecCApp_spec r
#align algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_SheafedSpace_app_spec AlgebraicGeometry.LocallyRingedSpace.toΓSpecSheafedSpace_app_spec

/-- The map on stalks induced by the unit commutes with maps from `Γ(X)` to
    stalks (in `Spec Γ(X)` and in `X`). -/
theorem toStalk_stalkMap_to_Γ_Spec (x : X) :
    toStalk _ _ ≫ PresheafedSpace.stalkMap X.toΓSpecSheafedSpace x = X.ΓToStalk x :=
  by
  rw [PresheafedSpace.stalk_map]
  erw [←
    to_open_germ _ (basic_open (1 : Γ.obj (op X)))
      ⟨X.to_Γ_Spec_fun x, by rw [basic_open_one] <;> trivial⟩]
  rw [← category.assoc, category.assoc (to_open _ _)]
  erw [stalk_functor_map_germ]
  rw [← category.assoc (to_open _ _), X.to_Γ_Spec_SheafedSpace_app_spec 1]
  unfold Γ_to_stalk
  rw [← stalk_pushforward_germ _ X.to_Γ_Spec_base X.presheaf ⊤]
  congr 1
  change (X.to_Γ_Spec_base _* X.presheaf).map le_top.hom.op ≫ _ = _
  apply germ_res
#align algebraic_geometry.LocallyRingedSpace.to_stalk_stalk_map_to_Γ_Spec AlgebraicGeometry.LocallyRingedSpace.toStalk_stalkMap_to_Γ_Spec

/-- The canonical morphism from `X` to the spectrum of its global sections. -/
@[simps val_base]
def toΓSpec : X ⟶ Spec.locallyRingedSpaceObj (Γ.obj (op X))
    where
  val := X.toΓSpecSheafedSpace
  Prop := by
    intro x
    let p : PrimeSpectrum (Γ.obj (op X)) := X.to_Γ_Spec_fun x
    constructor
    -- show stalk map is local hom ↓
    let S := (structure_sheaf _).Presheaf.stalk p
    rintro (t : S) ht
    obtain ⟨⟨r, s⟩, he⟩ := IsLocalization.surj p.as_ideal.prime_compl t
    dsimp at he 
    apply isUnit_of_mul_isUnit_left
    rw [he]
    refine' IsLocalization.map_units S (⟨r, _⟩ : p.as_ideal.prime_compl)
    apply (not_mem_prime_iff_unit_in_stalk _ _ _).mpr
    rw [← to_stalk_stalk_map_to_Γ_Spec, comp_apply]
    erw [← he]
    rw [RingHom.map_mul]
    exact
      ht.mul
        ((IsLocalization.map_units S s : _).map
          (PresheafedSpace.stalk_map X.to_Γ_Spec_SheafedSpace x))
#align algebraic_geometry.LocallyRingedSpace.to_Γ_Spec AlgebraicGeometry.LocallyRingedSpace.toΓSpec

theorem comp_ring_hom_ext {X : LocallyRingedSpace} {R : CommRingCat} {f : R ⟶ Γ.obj (op X)}
    {β : X ⟶ Spec.locallyRingedSpaceObj R}
    (w : X.toΓSpec.1.base ≫ (Spec.locallyRingedSpaceMap f).1.base = β.1.base)
    (h :
      ∀ r : R,
        f ≫ X.Presheaf.map (homOfLE le_top : (Opens.map β.1.base).obj (basicOpen r) ⟶ _).op =
          toOpen R (basicOpen r) ≫ β.1.c.app (op (basicOpen r))) :
    X.toΓSpec ≫ Spec.locallyRingedSpaceMap f = β :=
  by
  ext1
  apply Spec.basic_open_hom_ext
  · intro r _
    rw [LocallyRingedSpace.comp_val_c_app]
    erw [to_open_comp_comap_assoc]
    rw [category.assoc]
    erw [to_Γ_Spec_SheafedSpace_app_spec, ← X.presheaf.map_comp]
    convert h r
  exact w
#align algebraic_geometry.LocallyRingedSpace.comp_ring_hom_ext AlgebraicGeometry.LocallyRingedSpace.comp_ring_hom_ext

/-- `to_Spec_Γ _` is an isomorphism so these are mutually two-sided inverses. -/
theorem Γ_Spec_left_triangle : toSpecΓ (Γ.obj (op X)) ≫ X.toΓSpec.1.c.app (op ⊤) = 𝟙 _ :=
  by
  unfold to_Spec_Γ
  rw [← to_open_res _ (basic_open (1 : Γ.obj (op X))) ⊤ (eq_to_hom basic_open_one.symm)]
  erw [category.assoc]
  rw [nat_trans.naturality, ← category.assoc]
  erw [X.to_Γ_Spec_SheafedSpace_app_spec 1, ← functor.map_comp]
  convert eq_to_hom_map X.presheaf _; rfl
#align algebraic_geometry.LocallyRingedSpace.Γ_Spec_left_triangle AlgebraicGeometry.LocallyRingedSpace.Γ_Spec_left_triangle

end LocallyRingedSpace

/-- The unit as a natural transformation. -/
def identityToΓSpec : 𝟭 LocallyRingedSpace.{u} ⟶ Γ.rightOp ⋙ Spec.toLocallyRingedSpace
    where
  app := LocallyRingedSpace.toΓSpec
  naturality' X Y f := by
    symm
    apply LocallyRingedSpace.comp_ring_hom_ext
    · ext1 x
      dsimp [Spec.Top_map, LocallyRingedSpace.to_Γ_Spec_fun]
      rw [← LocalRing.comap_closedPoint (PresheafedSpace.stalk_map _ x), ←
        PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply]
      congr 2
      exact (PresheafedSpace.stalk_map_germ f.1 ⊤ ⟨x, trivial⟩).symm
      infer_instance
    · intro r
      rw [LocallyRingedSpace.comp_val_c_app, ← category.assoc]
      erw [Y.to_Γ_Spec_SheafedSpace_app_spec, f.1.c.naturality]
      rfl
#align algebraic_geometry.identity_to_Γ_Spec AlgebraicGeometry.identityToΓSpec

namespace ΓSpec

theorem left_triangle (X : LocallyRingedSpace) :
    SpecΓIdentity.inv.app (Γ.obj (op X)) ≫ (identityToΓSpec.app X).val.c.app (op ⊤) = 𝟙 _ :=
  X.Γ_Spec_left_triangle
#align algebraic_geometry.Γ_Spec.left_triangle AlgebraicGeometry.ΓSpec.left_triangle

/-- `Spec_Γ_identity` is iso so these are mutually two-sided inverses. -/
theorem right_triangle (R : CommRingCat) :
    identityToΓSpec.app (Spec.toLocallyRingedSpace.obj <| op R) ≫
        Spec.toLocallyRingedSpace.map (SpecΓIdentity.inv.app R).op =
      𝟙 _ :=
  by
  apply LocallyRingedSpace.comp_ring_hom_ext
  · ext ((p : PrimeSpectrum R)x)
    erw [←
      IsLocalization.AtPrime.to_map_mem_maximal_iff ((structure_sheaf R).Presheaf.stalk p)
        p.as_ideal x]
    rfl
  · intro r; apply to_open_res
#align algebraic_geometry.Γ_Spec.right_triangle AlgebraicGeometry.ΓSpec.right_triangle

-- Removing this makes the following definition time out.
/-- The adjunction `Γ ⊣ Spec` from `CommRingᵒᵖ` to `LocallyRingedSpace`. -/
@[simps Unit counit]
def locallyRingedSpaceAdjunction : Γ.rightOp ⊣ Spec.toLocallyRingedSpace :=
  Adjunction.mkOfUnitCounit
    { Unit := identityToΓSpec
      counit := (NatIso.op SpecΓIdentity).inv
      left_triangle := by
        ext X; erw [category.id_comp]
        exact congr_arg Quiver.Hom.op (left_triangle X)
      right_triangle := by
        ext1; ext1 R; erw [category.id_comp]
        exact right_triangle R.unop }
#align algebraic_geometry.Γ_Spec.LocallyRingedSpace_adjunction AlgebraicGeometry.ΓSpec.locallyRingedSpaceAdjunction

attribute [local semireducible] Spec.to_LocallyRingedSpace

/-- The adjunction `Γ ⊣ Spec` from `CommRingᵒᵖ` to `Scheme`. -/
def adjunction : Scheme.Γ.rightOp ⊣ Scheme.spec :=
  locallyRingedSpaceAdjunction.restrictFullyFaithful Scheme.forgetToLocallyRingedSpace (𝟭 _)
    (NatIso.ofComponents (fun X => Iso.refl _) fun _ _ f => by simpa)
    (NatIso.ofComponents (fun X => Iso.refl _) fun _ _ f => by simpa)
#align algebraic_geometry.Γ_Spec.adjunction AlgebraicGeometry.ΓSpec.adjunction

theorem adjunction_homEquiv_apply {X : Scheme} {R : CommRingCatᵒᵖ}
    (f : (op <| Scheme.Γ.obj <| op X) ⟶ R) :
    ΓSpec.adjunction.homEquiv X R f = locallyRingedSpaceAdjunction.homEquiv X.1 R f := by
  dsimp [adjunction, adjunction.restrict_fully_faithful]; simp
#align algebraic_geometry.Γ_Spec.adjunction_hom_equiv_apply AlgebraicGeometry.ΓSpec.adjunction_homEquiv_apply

theorem adjunction_homEquiv (X : Scheme) (R : CommRingCatᵒᵖ) :
    ΓSpec.adjunction.homEquiv X R = locallyRingedSpaceAdjunction.homEquiv X.1 R :=
  Equiv.ext fun f => adjunction_homEquiv_apply f
#align algebraic_geometry.Γ_Spec.adjunction_hom_equiv AlgebraicGeometry.ΓSpec.adjunction_homEquiv

theorem adjunction_homEquiv_symm_apply {X : Scheme} {R : CommRingCatᵒᵖ}
    (f : X ⟶ Scheme.spec.obj R) :
    (ΓSpec.adjunction.homEquiv X R).symm f = (locallyRingedSpaceAdjunction.homEquiv X.1 R).symm f :=
  by congr 2; exact adjunction_hom_equiv _ _
#align algebraic_geometry.Γ_Spec.adjunction_hom_equiv_symm_apply AlgebraicGeometry.ΓSpec.adjunction_homEquiv_symm_apply

@[simp]
theorem adjunction_counit_app {R : CommRingCatᵒᵖ} :
    ΓSpec.adjunction.counit.app R = locallyRingedSpaceAdjunction.counit.app R :=
  by
  rw [← adjunction.hom_equiv_symm_id, ← adjunction.hom_equiv_symm_id,
    adjunction_hom_equiv_symm_apply]
  rfl
#align algebraic_geometry.Γ_Spec.adjunction_counit_app AlgebraicGeometry.ΓSpec.adjunction_counit_app

@[simp]
theorem adjunction_unit_app {X : Scheme} :
    ΓSpec.adjunction.Unit.app X = locallyRingedSpaceAdjunction.Unit.app X.1 := by
  rw [← adjunction.hom_equiv_id, ← adjunction.hom_equiv_id, adjunction_hom_equiv_apply]; rfl
#align algebraic_geometry.Γ_Spec.adjunction_unit_app AlgebraicGeometry.ΓSpec.adjunction_unit_app

attribute [local semireducible] LocallyRingedSpace_adjunction Γ_Spec.adjunction

instance isIso_locallyRingedSpaceAdjunction_counit : IsIso locallyRingedSpaceAdjunction.counit :=
  IsIso.of_iso_inv _
#align algebraic_geometry.Γ_Spec.is_iso_LocallyRingedSpace_adjunction_counit AlgebraicGeometry.ΓSpec.isIso_locallyRingedSpaceAdjunction_counit

instance isIso_adjunction_counit : IsIso ΓSpec.adjunction.counit :=
  by
  apply (config := { instances := false }) nat_iso.is_iso_of_is_iso_app
  intro R
  rw [adjunction_counit_app]
  infer_instance
#align algebraic_geometry.Γ_Spec.is_iso_adjunction_counit AlgebraicGeometry.ΓSpec.isIso_adjunction_counit

-- This is just
-- `(Γ_Spec.adjunction.unit.app X).1.c.app (op ⊤) = Spec_Γ_identity.hom.app (X.presheaf.obj (op ⊤))`
-- But lean times out when trying to unify the types of the two sides.
theorem adjunction_unit_app_app_top (X : Scheme) :
    @Eq
      ((Scheme.spec.obj (op <| X.Presheaf.obj (op ⊤))).Presheaf.obj (op ⊤) ⟶
        ((ΓSpec.adjunction.Unit.app X).1.base _* X.Presheaf).obj (op ⊤))
      ((ΓSpec.adjunction.Unit.app X).val.c.app (op ⊤))
      (SpecΓIdentity.Hom.app (X.Presheaf.obj (op ⊤))) :=
  by
  have := congr_app Γ_Spec.adjunction.left_triangle X
  dsimp at this 
  rw [← is_iso.eq_comp_inv] at this 
  simp only [Γ_Spec.LocallyRingedSpace_adjunction_counit, nat_trans.op_app, category.id_comp,
    Γ_Spec.adjunction_counit_app] at this 
  rw [← op_inv, nat_iso.inv_inv_app, quiver.hom.op_inj.eq_iff] at this 
  exact this
#align algebraic_geometry.Γ_Spec.adjunction_unit_app_app_top AlgebraicGeometry.ΓSpec.adjunction_unit_app_app_top

end ΓSpec

/-! Immediate consequences of the adjunction. -/


/-- Spec preserves limits. -/
instance : Limits.PreservesLimits Spec.toLocallyRingedSpace :=
  ΓSpec.locallyRingedSpaceAdjunction.rightAdjointPreservesLimits

instance Spec.preservesLimits : Limits.preservesLimits Scheme.spec :=
  ΓSpec.adjunction.rightAdjointPreservesLimits
#align algebraic_geometry.Spec.preserves_limits AlgebraicGeometry.Spec.preservesLimits

/-- Spec is a full functor. -/
instance : Full Spec.toLocallyRingedSpace :=
  rFullOfCounitIsIso ΓSpec.locallyRingedSpaceAdjunction

instance Spec.full : Full Scheme.spec :=
  rFullOfCounitIsIso ΓSpec.adjunction
#align algebraic_geometry.Spec.full AlgebraicGeometry.Spec.full

/-- Spec is a faithful functor. -/
instance : Faithful Spec.toLocallyRingedSpace :=
  R_faithful_of_counit_isIso ΓSpec.locallyRingedSpaceAdjunction

instance Spec.faithful : Faithful Scheme.spec :=
  R_faithful_of_counit_isIso ΓSpec.adjunction
#align algebraic_geometry.Spec.faithful AlgebraicGeometry.Spec.faithful

instance : IsRightAdjoint Spec.toLocallyRingedSpace :=
  ⟨_, ΓSpec.locallyRingedSpaceAdjunction⟩

instance : IsRightAdjoint Scheme.spec :=
  ⟨_, ΓSpec.adjunction⟩

instance : Reflective Spec.toLocallyRingedSpace :=
  ⟨⟩

instance Spec.reflective : Reflective Scheme.spec :=
  ⟨⟩
#align algebraic_geometry.Spec.reflective AlgebraicGeometry.Spec.reflective

end AlgebraicGeometry

