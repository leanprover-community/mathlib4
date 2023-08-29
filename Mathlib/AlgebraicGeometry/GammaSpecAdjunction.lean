/-
Copyright (c) 2021 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Reflective

#align_import algebraic_geometry.Gamma_Spec_adjunction from "leanprover-community/mathlib"@"d39590fc8728fbf6743249802486f8c91ffe07bc"

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

set_option linter.uppercaseLean3 false

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
def ΓToStalk (x : X) : Γ.obj (op X) ⟶ X.presheaf.stalk x :=
  X.presheaf.germ (⟨x, trivial⟩ : (⊤ : Opens X))
#align algebraic_geometry.LocallyRingedSpace.Γ_to_stalk AlgebraicGeometry.LocallyRingedSpace.ΓToStalk

/-- The canonical map from the underlying set to the prime spectrum of `Γ(X)`. -/
def toΓSpecFun : X → PrimeSpectrum (Γ.obj (op X)) := fun x =>
  comap (X.ΓToStalk x) (LocalRing.closedPoint (X.presheaf.stalk x))
#align algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_fun AlgebraicGeometry.LocallyRingedSpace.toΓSpecFun

theorem not_mem_prime_iff_unit_in_stalk (r : Γ.obj (op X)) (x : X) :
    r ∉ (X.toΓSpecFun x).asIdeal ↔ IsUnit (X.ΓToStalk x r) := by
  erw [LocalRing.mem_maximalIdeal, Classical.not_not]
  -- 🎉 no goals
#align algebraic_geometry.LocallyRingedSpace.not_mem_prime_iff_unit_in_stalk AlgebraicGeometry.LocallyRingedSpace.not_mem_prime_iff_unit_in_stalk

/-- The preimage of a basic open in `Spec Γ(X)` under the unit is the basic
open in `X` defined by the same element (they are equal as sets). -/
theorem toΓSpec_preim_basicOpen_eq (r : Γ.obj (op X)) :
    X.toΓSpecFun ⁻¹' (basicOpen r).1 = (X.toRingedSpace.basicOpen r).1 := by
      ext
      -- ⊢ x✝ ∈ toΓSpecFun X ⁻¹' (basicOpen r).carrier ↔ x✝ ∈ (RingedSpace.basicOpen (t …
      erw [X.toRingedSpace.mem_top_basicOpen]; apply not_mem_prime_iff_unit_in_stalk
      -- ⊢ x✝ ∈ toΓSpecFun X ⁻¹' (basicOpen r).carrier ↔ IsUnit (↑(germ (toRingedSpace  …
                                               -- 🎉 no goals
#align algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_preim_basic_open_eq AlgebraicGeometry.LocallyRingedSpace.toΓSpec_preim_basicOpen_eq

/-- `toΓSpecFun` is continuous. -/
theorem toΓSpec_continuous : Continuous X.toΓSpecFun := by
  apply isTopologicalBasis_basic_opens.continuous
  -- ⊢ ∀ (s : Set (PrimeSpectrum ↑(Γ.obj (op X)))), (s ∈ Set.range fun r => ↑(basic …
  rintro _ ⟨r, rfl⟩
  -- ⊢ IsOpen (toΓSpecFun X ⁻¹' (fun r => ↑(basicOpen r)) r)
  erw [X.toΓSpec_preim_basicOpen_eq r]
  -- ⊢ IsOpen (RingedSpace.basicOpen (toRingedSpace X) r).carrier
  exact (X.toRingedSpace.basicOpen r).2
  -- 🎉 no goals
#align algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_continuous AlgebraicGeometry.LocallyRingedSpace.toΓSpec_continuous

/-- The canonical (bundled) continuous map from the underlying topological
space of `X` to the prime spectrum of its global sections. -/
@[simps]
def toΓSpecBase : X.toTopCat ⟶ Spec.topObj (Γ.obj (op X)) where
  toFun := X.toΓSpecFun
  continuous_toFun := X.toΓSpec_continuous
#align algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_base AlgebraicGeometry.LocallyRingedSpace.toΓSpecBase

variable (r : Γ.obj (op X))

/-- The preimage in `X` of a basic open in `Spec Γ(X)` (as an open set). -/
abbrev toΓSpecMapBasicOpen : Opens X :=
  (Opens.map X.toΓSpecBase).obj (basicOpen r)
#align algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_map_basic_open AlgebraicGeometry.LocallyRingedSpace.toΓSpecMapBasicOpen

/-- The preimage is the basic open in `X` defined by the same element `r`. -/
theorem toΓSpecMapBasicOpen_eq : X.toΓSpecMapBasicOpen r = X.toRingedSpace.basicOpen r :=
  Opens.ext (X.toΓSpec_preim_basicOpen_eq r)
#align algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_map_basic_open_eq AlgebraicGeometry.LocallyRingedSpace.toΓSpecMapBasicOpen_eq

/-- The map from the global sections `Γ(X)` to the sections on the (preimage of) a basic open. -/
abbrev toToΓSpecMapBasicOpen :
    X.presheaf.obj (op ⊤) ⟶ X.presheaf.obj (op <| X.toΓSpecMapBasicOpen r) :=
  X.presheaf.map (X.toΓSpecMapBasicOpen r).leTop.op
#align algebraic_geometry.LocallyRingedSpace.to_to_Γ_Spec_map_basic_open AlgebraicGeometry.LocallyRingedSpace.toToΓSpecMapBasicOpen

/-- `r` is a unit as a section on the basic open defined by `r`. -/
theorem isUnit_res_toΓSpecMapBasicOpen : IsUnit (X.toToΓSpecMapBasicOpen r r) := by
  convert
    (X.presheaf.map <| (eqToHom <| X.toΓSpecMapBasicOpen_eq r).op).isUnit_map
      (X.toRingedSpace.isUnit_res_basicOpen r)
  -- Porting note : `rw [comp_apply]` to `erw [comp_apply]`
  erw [← comp_apply, ← Functor.map_comp]
  -- ⊢ ↑(toToΓSpecMapBasicOpen X r) r = ↑((toRingedSpace X).toPresheafedSpace.presh …
  congr
  -- 🎉 no goals
#align algebraic_geometry.LocallyRingedSpace.is_unit_res_to_Γ_Spec_map_basic_open AlgebraicGeometry.LocallyRingedSpace.isUnit_res_toΓSpecMapBasicOpen

/-- Define the sheaf hom on individual basic opens for the unit. -/
def toΓSpecCApp :
    (structureSheaf <| Γ.obj <| op X).val.obj (op <| basicOpen r) ⟶
      X.presheaf.obj (op <| X.toΓSpecMapBasicOpen r) :=
  IsLocalization.Away.lift r (isUnit_res_toΓSpecMapBasicOpen _ r)
#align algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_c_app AlgebraicGeometry.LocallyRingedSpace.toΓSpecCApp

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
  -- ⊢ toOpen (↑(Γ.obj (op X))) (basicOpen r) ≫ f = toToΓSpecMapBasicOpen X r ↔ f = …
  rw [← @IsLocalization.Away.AwayMap.lift_comp _ _ _ _ _ _ _ r loc_inst _
      (X.isUnit_res_toΓSpecMapBasicOpen r)]
  --pick_goal 5; exact is_localization.to_basic_open _ r
  constructor
  -- ⊢ toOpen (↑(Γ.obj (op X))) (basicOpen r) ≫ f = RingHom.comp (IsLocalization.Aw …
  · intro h
    -- ⊢ f = toΓSpecCApp X r
    --Porting Note: Type class problem got stuck, same as above
    refine' @IsLocalization.ringHom_ext _ _ _ _ _ _ _ _ loc_inst _ _ _
    -- ⊢ RingHom.comp f (algebraMap ↑(Γ.obj (op X)) ↑((structureSheaf ↑(Γ.obj (op X)) …
    exact h
    -- 🎉 no goals
    --pick_goal 5; exact is_localization.to_basic_open _ r; exact h
  apply congr_arg
  -- 🎉 no goals
#align algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_c_app_iff AlgebraicGeometry.LocallyRingedSpace.toΓSpecCApp_iff

theorem toΓSpecCApp_spec : toOpen _ (basicOpen r) ≫ X.toΓSpecCApp r = X.toToΓSpecMapBasicOpen r :=
  (X.toΓSpecCApp_iff r _).2 rfl
#align algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_c_app_spec AlgebraicGeometry.LocallyRingedSpace.toΓSpecCApp_spec

/-- The sheaf hom on all basic opens, commuting with restrictions. -/
@[simps app]
def toΓSpecCBasicOpens :
    (inducedFunctor basicOpen).op ⋙ (structureSheaf (Γ.obj (op X))).1 ⟶
      (inducedFunctor basicOpen).op ⋙ ((TopCat.Sheaf.pushforward X.toΓSpecBase).obj X.𝒪).1 where
  app r := X.toΓSpecCApp r.unop
  naturality r s f := by
    apply (StructureSheaf.to_basicOpen_epi (Γ.obj (op X)) r.unop).1
    -- ⊢ toOpen (↑(Γ.obj (op X))) (basicOpen r.unop) ≫ ((inducedFunctor basicOpen).op …
    simp only [← Category.assoc]
    -- ⊢ (toOpen (↑(Γ.obj (op X))) (basicOpen r.unop) ≫ ((inducedFunctor basicOpen).o …
    erw [X.toΓSpecCApp_spec r.unop]
    -- ⊢ (toOpen (↑(Γ.obj (op X))) (basicOpen r.unop) ≫ ((inducedFunctor basicOpen).o …
    convert X.toΓSpecCApp_spec s.unop
    -- ⊢ toToΓSpecMapBasicOpen X r.unop ≫ ((inducedFunctor basicOpen).op ⋙ ((TopCat.S …
    symm
    -- ⊢ toToΓSpecMapBasicOpen X s.unop = toToΓSpecMapBasicOpen X r.unop ≫ ((inducedF …
    apply X.presheaf.map_comp
    -- 🎉 no goals
#align algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_c_basic_opens AlgebraicGeometry.LocallyRingedSpace.toΓSpecCBasicOpens

/-- The canonical morphism of sheafed spaces from `X` to the spectrum of its global sections. -/
@[simps]
def toΓSpecSheafedSpace : X.toSheafedSpace ⟶ Spec.toSheafedSpace.obj (op (Γ.obj (op X))) where
  base := X.toΓSpecBase
  c :=
    TopCat.Sheaf.restrictHomEquivHom (structureSheaf (Γ.obj (op X))).1 _ isBasis_basic_opens
      X.toΓSpecCBasicOpens
#align algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_SheafedSpace AlgebraicGeometry.LocallyRingedSpace.toΓSpecSheafedSpace

-- Porting Note: Now need much more hand holding: all variables explicit, and need to tidy up
-- significantly, was `TopCat.Sheaf.extend_hom_app _ _ _ _`
theorem toΓSpecSheafedSpace_app_eq :
    X.toΓSpecSheafedSpace.c.app (op (basicOpen r)) = X.toΓSpecCApp r := by
  have := TopCat.Sheaf.extend_hom_app (Spec.toSheafedSpace.obj (op (Γ.obj (op X)))).presheaf
    ((TopCat.Sheaf.pushforward X.toΓSpecBase).obj X.𝒪)
    isBasis_basic_opens X.toΓSpecCBasicOpens r
  dsimp at this
  -- ⊢ NatTrans.app (toΓSpecSheafedSpace X).c (op (basicOpen r)) = toΓSpecCApp X r
  rw [←this]
  -- ⊢ NatTrans.app (toΓSpecSheafedSpace X).c (op (basicOpen r)) = NatTrans.app (↑( …
  dsimp
  -- ⊢ NatTrans.app (↑(TopCat.Sheaf.restrictHomEquivHom (structureSheaf ↑(X.preshea …
  congr
  -- 🎉 no goals

#align algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_SheafedSpace_app_eq AlgebraicGeometry.LocallyRingedSpace.toΓSpecSheafedSpace_app_eq

-- Porting note : need a helper lemma `toΓSpecSheafedSpace_app_spec_assoc` to help compile
-- `toStalk_stalkMap_to_Γ_Spec`
@[reassoc] theorem toΓSpecSheafedSpace_app_spec (r : Γ.obj (op X)) :
    toOpen (Γ.obj (op X)) (basicOpen r) ≫ X.toΓSpecSheafedSpace.c.app (op (basicOpen r)) =
      X.toToΓSpecMapBasicOpen r :=
  (X.toΓSpecSheafedSpace_app_eq r).symm ▸ X.toΓSpecCApp_spec r
#align algebraic_geometry.LocallyRingedSpace.to_Γ_Spec_SheafedSpace_app_spec AlgebraicGeometry.LocallyRingedSpace.toΓSpecSheafedSpace_app_spec

/-- The map on stalks induced by the unit commutes with maps from `Γ(X)` to
    stalks (in `Spec Γ(X)` and in `X`). -/
theorem toStalk_stalkMap_toΓSpec (x : X) :
    toStalk _ _ ≫ PresheafedSpace.stalkMap X.toΓSpecSheafedSpace x = X.ΓToStalk x := by
  rw [PresheafedSpace.stalkMap]
  -- ⊢ toStalk (↑(op (Γ.obj (op X))).unop) (↑(toΓSpecSheafedSpace X).base x) ≫ (sta …
  erw [← toOpen_germ _ (basicOpen (1 : Γ.obj (op X)))
      ⟨X.toΓSpecFun x, by rw [basicOpen_one]; trivial⟩]
  rw [← Category.assoc, Category.assoc (toOpen _ _)]
  -- ⊢ (toOpen (↑(Γ.obj (op X))) (basicOpen 1) ≫ germ (TopCat.Sheaf.presheaf (struc …
  erw [stalkFunctor_map_germ]
  -- ⊢ (toOpen (↑(Γ.obj (op X))) (basicOpen 1) ≫ NatTrans.app (toΓSpecSheafedSpace  …
  -- Porting note : was `rw [←assoc, toΓSpecSheafedSpace_app_spec]`, but Lean did not like it.
  rw [toΓSpecSheafedSpace_app_spec_assoc]
  -- ⊢ (toToΓSpecMapBasicOpen X 1 ≫ germ ((toΓSpecSheafedSpace X).base _* X.preshea …
  unfold ΓToStalk
  -- ⊢ (toToΓSpecMapBasicOpen X 1 ≫ germ ((toΓSpecSheafedSpace X).base _* X.preshea …
  rw [← stalkPushforward_germ _ X.toΓSpecBase X.presheaf ⊤]
  -- ⊢ (toToΓSpecMapBasicOpen X 1 ≫ germ ((toΓSpecSheafedSpace X).base _* X.preshea …
  congr 1
  -- ⊢ toToΓSpecMapBasicOpen X 1 ≫ germ ((toΓSpecSheafedSpace X).base _* X.presheaf …
  change (X.toΓSpecBase _* X.presheaf).map le_top.hom.op ≫ _ = _
  -- ⊢ (toΓSpecBase X _* X.presheaf).map (LE.le.hom (_ : { carrier := {x | ¬1 ∈ x.a …
  apply germ_res
  -- 🎉 no goals
#align algebraic_geometry.LocallyRingedSpace.to_stalk_stalk_map_to_Γ_Spec AlgebraicGeometry.LocallyRingedSpace.toStalk_stalkMap_toΓSpec

/-- The canonical morphism from `X` to the spectrum of its global sections. -/
@[simps! val_base]
def toΓSpec : X ⟶ Spec.locallyRingedSpaceObj (Γ.obj (op X)) where
  val := X.toΓSpecSheafedSpace
  prop := by
    intro x
    -- ⊢ IsLocalRingHom (PresheafedSpace.stalkMap (toΓSpecSheafedSpace X) x)
    let p : PrimeSpectrum (Γ.obj (op X)) := X.toΓSpecFun x
    -- ⊢ IsLocalRingHom (PresheafedSpace.stalkMap (toΓSpecSheafedSpace X) x)
    constructor
    -- ⊢ ∀ (a : ↑(PresheafedSpace.stalk (Spec.locallyRingedSpaceObj (Γ.obj (op X))).t …
    -- show stalk map is local hom ↓
    let S := (structureSheaf _).presheaf.stalk p
    -- ⊢ ∀ (a : ↑(PresheafedSpace.stalk (Spec.locallyRingedSpaceObj (Γ.obj (op X))).t …
    rintro (t : S) ht
    -- ⊢ IsUnit t
    obtain ⟨⟨r, s⟩, he⟩ := IsLocalization.surj p.asIdeal.primeCompl t
    -- ⊢ IsUnit t
    dsimp at he
    -- ⊢ IsUnit t
    set t' := _
    -- ⊢ IsUnit t
    change t * t' = _ at he
    -- ⊢ IsUnit t
    apply isUnit_of_mul_isUnit_left (y := t')
    -- ⊢ IsUnit (t * t')
    rw [he]
    -- ⊢ IsUnit (↑(toStalk (↑(X.presheaf.obj (op ⊤))) (toΓSpecFun X x)) r)
    refine' IsLocalization.map_units S (⟨r, _⟩ : p.asIdeal.primeCompl)
    -- ⊢ r ∈ Ideal.primeCompl p.asIdeal
    apply (not_mem_prime_iff_unit_in_stalk _ _ _).mpr
    -- ⊢ IsUnit (↑(ΓToStalk X x) r)
    rw [← toStalk_stalkMap_toΓSpec]
    -- ⊢ IsUnit (↑(toStalk (↑(op (Γ.obj (op X))).unop) (↑(toΓSpecSheafedSpace X).base …
    erw [comp_apply, ← he]
    -- ⊢ IsUnit (↑(PresheafedSpace.stalkMap (toΓSpecSheafedSpace X) x) (t * t'))
    rw [RingHom.map_mul]
    -- ⊢ IsUnit (↑(PresheafedSpace.stalkMap (toΓSpecSheafedSpace X) x) t * ↑(Presheaf …
    -- Porting note : `IsLocalization.map_units` and the goal needs to be simplified before Lean
    -- realize it is useful
    have := IsLocalization.map_units (R := Γ.obj (op X)) S s
    -- ⊢ IsUnit (↑(PresheafedSpace.stalkMap (toΓSpecSheafedSpace X) x) t * ↑(Presheaf …
    dsimp at this ⊢
    -- ⊢ IsUnit (↑(PresheafedSpace.stalkMap (toΓSpecSheafedSpace X) x) t * ↑(Presheaf …
    refine ht.mul <| this.map _
    -- 🎉 no goals
#align algebraic_geometry.LocallyRingedSpace.to_Γ_Spec AlgebraicGeometry.LocallyRingedSpace.toΓSpec

theorem comp_ring_hom_ext {X : LocallyRingedSpace} {R : CommRingCat} {f : R ⟶ Γ.obj (op X)}
    {β : X ⟶ Spec.locallyRingedSpaceObj R}
    (w : X.toΓSpec.1.base ≫ (Spec.locallyRingedSpaceMap f).1.base = β.1.base)
    (h :
      ∀ r : R,
        f ≫ X.presheaf.map (homOfLE le_top : (Opens.map β.1.base).obj (basicOpen r) ⟶ _).op =
          toOpen R (basicOpen r) ≫ β.1.c.app (op (basicOpen r))) :
    X.toΓSpec ≫ Spec.locallyRingedSpaceMap f = β := by
  ext1
  -- ⊢ (toΓSpec X ≫ Spec.locallyRingedSpaceMap f).val = β.val
  -- Porting note : need more hand holding here
  change (X.toΓSpec.1 ≫ _).base = _ at w
  -- ⊢ (toΓSpec X ≫ Spec.locallyRingedSpaceMap f).val = β.val
  apply Spec.basicOpen_hom_ext w
  -- ⊢ ∀ (r : ↑R),
  intro r U
  -- ⊢ (toOpen (↑R) U ≫ NatTrans.app ((toΓSpec X).val ≫ (Spec.locallyRingedSpaceMap …
  -- Porting note : changed `rw` to `erw`
  erw [LocallyRingedSpace.comp_val_c_app]
  -- ⊢ (toOpen (↑R) U ≫ NatTrans.app (Spec.locallyRingedSpaceMap f).val.c (op U) ≫  …
  erw [toOpen_comp_comap_assoc]
  -- ⊢ (CommRingCat.ofHom f ≫ toOpen (↑(Γ.obj (op X))) (↑(Opens.comap (PrimeSpectru …
  rw [Category.assoc]
  -- ⊢ CommRingCat.ofHom f ≫ (toOpen (↑(Γ.obj (op X))) (↑(Opens.comap (PrimeSpectru …
  erw [toΓSpecSheafedSpace_app_spec, ← X.presheaf.map_comp]
  -- ⊢ CommRingCat.ofHom f ≫ X.presheaf.map ((Opens.leTop (toΓSpecMapBasicOpen X (↑ …
  convert h r using 1
  -- 🎉 no goals
#align algebraic_geometry.LocallyRingedSpace.comp_ring_hom_ext AlgebraicGeometry.LocallyRingedSpace.comp_ring_hom_ext

/-- `toSpecΓ _` is an isomorphism so these are mutually two-sided inverses. -/
theorem Γ_Spec_left_triangle : toSpecΓ (Γ.obj (op X)) ≫ X.toΓSpec.1.c.app (op ⊤) = 𝟙 _ := by
  unfold toSpecΓ
  -- ⊢ toOpen ↑(Γ.obj (op X)) ⊤ ≫ NatTrans.app (toΓSpec X).val.c (op ⊤) = 𝟙 (Γ.obj  …
  rw [← toOpen_res _ (basicOpen (1 : Γ.obj (op X))) ⊤ (eqToHom basicOpen_one.symm)]
  -- ⊢ (toOpen (↑(Γ.obj (op X))) (basicOpen 1) ≫ (structureSheaf ↑(Γ.obj (op X))).v …
  erw [Category.assoc]
  -- ⊢ toOpen (↑(Γ.obj (op X))) (basicOpen 1) ≫ (structureSheaf ↑(Γ.obj (op X))).va …
  rw [NatTrans.naturality, ← Category.assoc]
  -- ⊢ (toOpen (↑(Γ.obj (op X))) (basicOpen 1) ≫ NatTrans.app (toΓSpec X).val.c (op …
  erw [X.toΓSpecSheafedSpace_app_spec 1, ← Functor.map_comp]
  -- ⊢ X.presheaf.map ((Opens.leTop (toΓSpecMapBasicOpen X 1)).op ≫ (Opens.map (toΓ …
  convert eqToHom_map X.presheaf _; rfl
  -- ⊢ op ⊤ = (Opens.map (toΓSpec X).val.base).op.obj (op ⊤)
                                    -- 🎉 no goals
#align algebraic_geometry.LocallyRingedSpace.Γ_Spec_left_triangle AlgebraicGeometry.LocallyRingedSpace.Γ_Spec_left_triangle

end LocallyRingedSpace

/-- The unit as a natural transformation. -/
def identityToΓSpec : 𝟭 LocallyRingedSpace.{u} ⟶ Γ.rightOp ⋙ Spec.toLocallyRingedSpace where
  app := LocallyRingedSpace.toΓSpec
  naturality X Y f := by
    symm
    -- ⊢ toΓSpec X ≫ (Γ.rightOp ⋙ Spec.toLocallyRingedSpace).map f = (𝟭 LocallyRinged …
    apply LocallyRingedSpace.comp_ring_hom_ext
    -- ⊢ (toΓSpec ((𝟭 LocallyRingedSpace).obj X)).val.base ≫ (Spec.locallyRingedSpace …
    · ext1 x
      -- ⊢ ↑((toΓSpec ((𝟭 LocallyRingedSpace).obj X)).val.base ≫ (Spec.locallyRingedSpa …
      dsimp [Spec.topMap, LocallyRingedSpace.toΓSpecFun]
      -- ⊢ ↑(toΓSpecBase X ≫ PrimeSpectrum.comap (NatTrans.app f.val.c (op ⊤))) x = ↑(f …
      --Porting Note: Had to add the next four lines
      rw [comp_apply, comp_apply]
      -- ⊢ ↑(PrimeSpectrum.comap (NatTrans.app f.val.c (op ⊤))) (↑(toΓSpecBase X) x) =  …
      dsimp [toΓSpecBase]
      -- ⊢ ↑(PrimeSpectrum.comap (NatTrans.app f.val.c (op ⊤))) (↑(ContinuousMap.mk (to …
      rw [ContinuousMap.coe_mk, ContinuousMap.coe_mk]
      -- ⊢ ↑(PrimeSpectrum.comap (NatTrans.app f.val.c (op ⊤))) (toΓSpecFun X x) = toΓS …
      dsimp [toΓSpecFun]
      -- ⊢ ↑(PrimeSpectrum.comap (NatTrans.app f.val.c (op ⊤))) (↑(PrimeSpectrum.comap  …
      rw [← LocalRing.comap_closedPoint (PresheafedSpace.stalkMap f.val x), ←
        PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply]
      congr 2
      -- ⊢ RingHom.comp (ΓToStalk X x) (NatTrans.app f.val.c (op ⊤)) = RingHom.comp (Pr …
      exact (PresheafedSpace.stalkMap_germ f.1 ⊤ ⟨x, trivial⟩).symm
      -- 🎉 no goals
    · intro r
      -- ⊢ (Γ.rightOp.map f).unop ≫ ((𝟭 LocallyRingedSpace).obj X).presheaf.map (homOfL …
      rw [LocallyRingedSpace.comp_val_c_app, ← Category.assoc]
      -- ⊢ (Γ.rightOp.map f).unop ≫ ((𝟭 LocallyRingedSpace).obj X).presheaf.map (homOfL …
      erw [Y.toΓSpecSheafedSpace_app_spec, f.1.c.naturality]
      -- ⊢ (Γ.rightOp.map f).unop ≫ ((𝟭 LocallyRingedSpace).obj X).presheaf.map (homOfL …
      rfl
      -- 🎉 no goals
#align algebraic_geometry.identity_to_Γ_Spec AlgebraicGeometry.identityToΓSpec

namespace ΓSpec

theorem left_triangle (X : LocallyRingedSpace) :
    SpecΓIdentity.inv.app (Γ.obj (op X)) ≫ (identityToΓSpec.app X).val.c.app (op ⊤) = 𝟙 _ :=
  X.Γ_Spec_left_triangle
#align algebraic_geometry.Γ_Spec.left_triangle AlgebraicGeometry.ΓSpec.left_triangle

/-- `SpecΓIdentity` is iso so these are mutually two-sided inverses. -/
theorem right_triangle (R : CommRingCat) :
    identityToΓSpec.app (Spec.toLocallyRingedSpace.obj <| op R) ≫
        Spec.toLocallyRingedSpace.map (SpecΓIdentity.inv.app R).op =
      𝟙 _ := by
  apply LocallyRingedSpace.comp_ring_hom_ext
  -- ⊢ (toΓSpec ((𝟭 LocallyRingedSpace).obj (Spec.toLocallyRingedSpace.obj (op R))) …
  · ext (p : PrimeSpectrum R)
    -- ⊢ ↑((toΓSpec ((𝟭 LocallyRingedSpace).obj (Spec.toLocallyRingedSpace.obj (op R) …
    change _ = p -- Porting note: Had to add this line to make `ext x` work.
    -- ⊢ ↑((toΓSpec ((𝟭 LocallyRingedSpace).obj (Spec.toLocallyRingedSpace.obj (op R) …
    ext x
    -- ⊢ x ∈ (↑((toΓSpec ((𝟭 LocallyRingedSpace).obj (Spec.toLocallyRingedSpace.obj ( …
    erw [← IsLocalization.AtPrime.to_map_mem_maximal_iff ((structureSheaf R).presheaf.stalk p)
        p.asIdeal x]
    rfl
    -- 🎉 no goals
  · intro r; apply toOpen_res
    -- ⊢ (NatTrans.app SpecΓIdentity.inv R).op.unop ≫ ((𝟭 LocallyRingedSpace).obj (Sp …
             -- 🎉 no goals
#align algebraic_geometry.Γ_Spec.right_triangle AlgebraicGeometry.ΓSpec.right_triangle

-- Porting note : the two unification hint is to help compile `locallyRingedSpaceAdjunction`
-- faster, from 900000 to normal maxHeartbeats
/-- opposite of composition of two functors -/
unif_hint uh_functor_op1 where ⊢
  Functor.op (Spec.toLocallyRingedSpace.rightOp ⋙ Γ) ≟
  Spec.toLocallyRingedSpace.{u} ⋙ Γ.rightOp in

/-- opposite of identity functor -/
unif_hint uh_functor_op2 where ⊢
  Functor.op (𝟭 CommRingCat.{u}) ≟ 𝟭 CommRingCatᵒᵖ in

/-- The adjunction `Γ ⊣ Spec` from `CommRingᵒᵖ` to `LocallyRingedSpace`. -/
--Porting Note: `simps` cause a time out, so `Unit` and `counit` will be added manually
def locallyRingedSpaceAdjunction : Γ.rightOp ⊣ Spec.toLocallyRingedSpace.{u} :=
  Adjunction.mkOfUnitCounit
    { unit := identityToΓSpec
      counit := (NatIso.op SpecΓIdentity).inv
      left_triangle := by
        ext X; erw [Category.id_comp]
        -- ⊢ NatTrans.app (whiskerRight identityToΓSpec Γ.rightOp ≫ (Functor.associator Γ …
               -- ⊢ NatTrans.app (whiskerRight identityToΓSpec Γ.rightOp ≫ whiskerLeft Γ.rightOp …
        exact congr_arg Quiver.Hom.op (left_triangle X)
        -- 🎉 no goals
      right_triangle := by
        ext R : 2
        -- ⊢ NatTrans.app (whiskerLeft Spec.toLocallyRingedSpace identityToΓSpec ≫ (Funct …
        -- Porting note : a little bit hand holding
        change identityToΓSpec.app _ ≫ 𝟙 _ ≫ Spec.toLocallyRingedSpace.map _ =
          𝟙 _
        simp_rw [Category.id_comp, show (NatIso.op SpecΓIdentity).inv.app R =
          (SpecΓIdentity.inv.app R.unop).op from rfl]
        exact right_triangle R.unop
        -- 🎉 no goals
        }
#align algebraic_geometry.Γ_Spec.LocallyRingedSpace_adjunction AlgebraicGeometry.ΓSpec.locallyRingedSpaceAdjunction

lemma locallyRingedSpaceAdjunction_unit :
  locallyRingedSpaceAdjunction.unit = identityToΓSpec := rfl
#align algebraic_geometry.Γ_Spec.LocallyRingedSpace_adjunction_unit AlgebraicGeometry.ΓSpec.locallyRingedSpaceAdjunction_unit

lemma locallyRingedSpaceAdjunction_counit :
  locallyRingedSpaceAdjunction.counit = (NatIso.op SpecΓIdentity.{u}).inv := rfl
#align algebraic_geometry.Γ_Spec.LocallyRingedSpace_adjunction_counit AlgebraicGeometry.ΓSpec.locallyRingedSpaceAdjunction_counit

-- Porting Note: Commented
--attribute [local semireducible] Spec.toLocallyRingedSpace

/-- The adjunction `Γ ⊣ Spec` from `CommRingᵒᵖ` to `Scheme`. -/
def adjunction : Scheme.Γ.rightOp ⊣ Scheme.Spec :=
  locallyRingedSpaceAdjunction.restrictFullyFaithful Scheme.forgetToLocallyRingedSpace (𝟭 _)
    (NatIso.ofComponents (fun X => Iso.refl _) )
    (NatIso.ofComponents (fun X => Iso.refl _) )
#align algebraic_geometry.Γ_Spec.adjunction AlgebraicGeometry.ΓSpec.adjunction

theorem adjunction_homEquiv_apply {X : Scheme} {R : CommRingCatᵒᵖ}
    (f : (op <| Scheme.Γ.obj <| op X) ⟶ R) :
    ΓSpec.adjunction.homEquiv X R f = locallyRingedSpaceAdjunction.homEquiv X.1 R f := by
  dsimp [adjunction, Adjunction.restrictFullyFaithful]
  -- ⊢ ↑(equivOfFullyFaithful Scheme.forgetToLocallyRingedSpace).symm (𝟙 X.toLocall …
  simp only [Category.comp_id, Category.id_comp]
  -- ⊢ ↑(equivOfFullyFaithful Scheme.forgetToLocallyRingedSpace).symm (↑(Adjunction …
  rfl --Porting Note: Added
  -- 🎉 no goals
#align algebraic_geometry.Γ_Spec.adjunction_hom_equiv_apply AlgebraicGeometry.ΓSpec.adjunction_homEquiv_apply

theorem adjunction_homEquiv (X : Scheme) (R : CommRingCatᵒᵖ) :
    ΓSpec.adjunction.homEquiv X R = locallyRingedSpaceAdjunction.homEquiv X.1 R :=
  Equiv.ext fun f => adjunction_homEquiv_apply f
#align algebraic_geometry.Γ_Spec.adjunction_hom_equiv AlgebraicGeometry.ΓSpec.adjunction_homEquiv

theorem adjunction_homEquiv_symm_apply {X : Scheme} {R : CommRingCatᵒᵖ}
    (f : X ⟶ Scheme.Spec.obj R) :
    (ΓSpec.adjunction.homEquiv X R).symm f = (locallyRingedSpaceAdjunction.homEquiv X.1 R).symm f :=
  by rw [adjunction_homEquiv]; rfl
     -- ⊢ ↑(Adjunction.homEquiv locallyRingedSpaceAdjunction X.toLocallyRingedSpace R) …
                               -- 🎉 no goals
#align algebraic_geometry.Γ_Spec.adjunction_hom_equiv_symm_apply AlgebraicGeometry.ΓSpec.adjunction_homEquiv_symm_apply

@[simp]
theorem adjunction_counit_app {R : CommRingCatᵒᵖ} :
    ΓSpec.adjunction.counit.app R = locallyRingedSpaceAdjunction.counit.app R := by
  rw [← Adjunction.homEquiv_symm_id, ← Adjunction.homEquiv_symm_id,
    adjunction_homEquiv_symm_apply]
  rfl
  -- 🎉 no goals
#align algebraic_geometry.Γ_Spec.adjunction_counit_app AlgebraicGeometry.ΓSpec.adjunction_counit_app

@[simp]
theorem adjunction_unit_app {X : Scheme} :
    ΓSpec.adjunction.unit.app X = locallyRingedSpaceAdjunction.unit.app X.1 := by
  rw [← Adjunction.homEquiv_id, ← Adjunction.homEquiv_id, adjunction_homEquiv_apply]; rfl
  -- ⊢ ↑(Adjunction.homEquiv locallyRingedSpaceAdjunction X.toLocallyRingedSpace (S …
                                                                                      -- 🎉 no goals
#align algebraic_geometry.Γ_Spec.adjunction_unit_app AlgebraicGeometry.ΓSpec.adjunction_unit_app

-- Porting Note: Commented
-- attribute [local semireducible] locallyRingedSpaceAdjunction ΓSpec.adjunction

instance isIso_locallyRingedSpaceAdjunction_counit : IsIso locallyRingedSpaceAdjunction.counit := by
  dsimp only [locallyRingedSpaceAdjunction, Adjunction.mkOfUnitCounit_counit]
  -- ⊢ IsIso (NatIso.op SpecΓIdentity).inv
  -- Porting Note: `dsimp` was unnecessary and had to make this explicit
  convert IsIso.of_iso_inv (NatIso.op SpecΓIdentity) using 1
  -- 🎉 no goals
#align algebraic_geometry.Γ_Spec.is_iso_LocallyRingedSpace_adjunction_counit AlgebraicGeometry.ΓSpec.isIso_locallyRingedSpaceAdjunction_counit

instance isIso_adjunction_counit : IsIso ΓSpec.adjunction.counit := by
  apply (config := { allowSynthFailures := true }) NatIso.isIso_of_isIso_app
  -- ⊢ ∀ (X : CommRingCatᵒᵖ), IsIso (NatTrans.app adjunction.counit X)
  intro R
  -- ⊢ IsIso (NatTrans.app adjunction.counit R)
  rw [adjunction_counit_app]
  -- ⊢ IsIso (NatTrans.app locallyRingedSpaceAdjunction.counit R)
  infer_instance
  -- 🎉 no goals
#align algebraic_geometry.Γ_Spec.is_iso_adjunction_counit AlgebraicGeometry.ΓSpec.isIso_adjunction_counit

theorem adjunction_unit_app_app_top (X : Scheme) :
    (ΓSpec.adjunction.unit.app X).1.c.app (op ⊤) =
    SpecΓIdentity.hom.app (X.presheaf.obj (op ⊤)) := by
  have := congr_app ΓSpec.adjunction.left_triangle X
  -- ⊢ NatTrans.app (NatTrans.app adjunction.unit X).val.c (op ⊤) = NatTrans.app Sp …
  dsimp at this
  -- ⊢ NatTrans.app (NatTrans.app adjunction.unit X).val.c (op ⊤) = NatTrans.app Sp …
  -- Porting Notes: Slightly changed some rewrites.
  -- Originally:
  --  rw [← is_iso.eq_comp_inv] at this
  --  simp only [Γ_Spec.LocallyRingedSpace_adjunction_counit, nat_trans.op_app, category.id_comp,
  --    Γ_Spec.adjunction_counit_app] at this
  --  rw [← op_inv, nat_iso.inv_inv_app, quiver.hom.op_inj.eq_iff] at this
  rw [← IsIso.eq_comp_inv] at this
  -- ⊢ NatTrans.app (NatTrans.app adjunction.unit X).val.c (op ⊤) = NatTrans.app Sp …
  simp only [adjunction_counit_app, locallyRingedSpaceAdjunction_counit, NatIso.op_inv,
    NatTrans.op_app, unop_op, Functor.id_obj, Functor.comp_obj, Functor.rightOp_obj,
    Spec.toLocallyRingedSpace_obj, Γ_obj, Spec.locallyRingedSpaceObj_toSheafedSpace,
    Spec.sheafedSpaceObj_carrier, Spec.sheafedSpaceObj_presheaf,
    SpecΓIdentity_inv_app, Category.id_comp] at this
  rw [← op_inv, Quiver.Hom.op_inj.eq_iff] at this
  -- ⊢ NatTrans.app (NatTrans.app adjunction.unit X).val.c (op ⊤) = NatTrans.app Sp …
  rw [SpecΓIdentity_hom_app]
  -- ⊢ NatTrans.app (NatTrans.app adjunction.unit X).val.c (op ⊤) = inv (toSpecΓ (X …
  convert this using 1
  -- 🎉 no goals
#align algebraic_geometry.Γ_Spec.adjunction_unit_app_app_top AlgebraicGeometry.ΓSpec.adjunction_unit_app_app_top

end ΓSpec

/-! Immediate consequences of the adjunction. -/


/-- Spec preserves limits. -/
instance : Limits.PreservesLimits Spec.toLocallyRingedSpace :=
  ΓSpec.locallyRingedSpaceAdjunction.rightAdjointPreservesLimits

instance Spec.preservesLimits : Limits.PreservesLimits Scheme.Spec :=
  ΓSpec.adjunction.rightAdjointPreservesLimits
#align algebraic_geometry.Spec.preserves_limits AlgebraicGeometry.Spec.preservesLimits

/-- Spec is a full functor. -/
instance : Full Spec.toLocallyRingedSpace :=
  rFullOfCounitIsIso ΓSpec.locallyRingedSpaceAdjunction

instance Spec.full : Full Scheme.Spec :=
  rFullOfCounitIsIso ΓSpec.adjunction
#align algebraic_geometry.Spec.full AlgebraicGeometry.Spec.full

/-- Spec is a faithful functor. -/
instance : Faithful Spec.toLocallyRingedSpace :=
  R_faithful_of_counit_isIso ΓSpec.locallyRingedSpaceAdjunction

instance Spec.faithful : Faithful Scheme.Spec :=
  R_faithful_of_counit_isIso ΓSpec.adjunction
#align algebraic_geometry.Spec.faithful AlgebraicGeometry.Spec.faithful

instance : IsRightAdjoint Spec.toLocallyRingedSpace :=
  ⟨_, ΓSpec.locallyRingedSpaceAdjunction⟩

instance : IsRightAdjoint Scheme.Spec :=
  ⟨_, ΓSpec.adjunction⟩

instance : Reflective Spec.toLocallyRingedSpace :=
  ⟨⟩

instance Spec.reflective : Reflective Scheme.Spec :=
  ⟨⟩
#align algebraic_geometry.Spec.reflective AlgebraicGeometry.Spec.reflective

end AlgebraicGeometry
