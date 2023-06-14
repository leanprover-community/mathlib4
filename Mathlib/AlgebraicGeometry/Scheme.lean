/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebraic_geometry.Scheme
! leanprover-community/mathlib commit 06c75afebd8b612d3b20fe836424298f2387ca53
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.Algebra.Category.Ring.Constructions

/-!
# The category of schemes

A scheme is a locally ringed space such that every point is contained in some open set
where there is an isomorphism of presheaves between the restriction to that open set,
and the structure sheaf of `Spec R`, for some commutative ring `R`.

A morphism of schemes is just a morphism of the underlying locally ringed spaces.

-/


noncomputable section

open TopologicalSpace

open CategoryTheory

open TopCat

open Opposite

namespace AlgebraicGeometry

/- ./././Mathport/Syntax/Translate/Command.lean:422:11: unsupported: advanced extends in structure -/
/-- We define `Scheme` as a `X : LocallyRingedSpace`,
along with a proof that every point has an open neighbourhood `U`
so that that the restriction of `X` to `U` is isomorphic,
as a locally ringed space, to `Spec.to_LocallyRingedSpace.obj (op R)`
for some `R : CommRing`.
-/
structure Scheme extends
    "./././Mathport/Syntax/Translate/Command.lean:422:11: unsupported: advanced extends in structure" where
  local_affine :
    ∀ x : to_LocallyRingedSpace,
      ∃ (U : OpenNhds x) (R : CommRingCat),
        Nonempty
          (to_LocallyRingedSpace.restrict U.OpenEmbedding ≅ Spec.toLocallyRingedSpace.obj (op R))
#align algebraic_geometry.Scheme AlgebraicGeometry.Scheme

namespace Scheme

-- There isn't nessecarily a morphism between two schemes.
/-- A morphism between schemes is a morphism between the underlying locally ringed spaces. -/
@[nolint has_nonempty_instance]
def Hom (X Y : Scheme) : Type _ :=
  X.toLocallyRingedSpace ⟶ Y.toLocallyRingedSpace
#align algebraic_geometry.Scheme.hom AlgebraicGeometry.Scheme.Hom

/-- Schemes are a full subcategory of locally ringed spaces.
-/
instance : Category Scheme :=
  { InducedCategory.category Scheme.toLocallyRingedSpace with Hom := Hom }

/-- The structure sheaf of a Scheme. -/
protected abbrev sheaf (X : Scheme) :=
  X.toSheafedSpace.Sheaf
#align algebraic_geometry.Scheme.sheaf AlgebraicGeometry.Scheme.sheaf

/-- The forgetful functor from `Scheme` to `LocallyRingedSpace`. -/
@[simps]
def forgetToLocallyRingedSpace : Scheme ⥤ LocallyRingedSpace :=
  inducedFunctor _
deriving Full, Faithful
#align algebraic_geometry.Scheme.forget_to_LocallyRingedSpace AlgebraicGeometry.Scheme.forgetToLocallyRingedSpace

@[simp]
theorem forgetToLocallyRingedSpace_preimage {X Y : Scheme} (f : X ⟶ Y) :
    Scheme.forgetToLocallyRingedSpace.preimage f = f :=
  rfl
#align algebraic_geometry.Scheme.forget_to_LocallyRingedSpace_preimage AlgebraicGeometry.Scheme.forgetToLocallyRingedSpace_preimage

/-- The forgetful functor from `Scheme` to `Top`. -/
@[simps]
def forgetToTop : Scheme ⥤ TopCat :=
  Scheme.forgetToLocallyRingedSpace ⋙ LocallyRingedSpace.forgetToTop
#align algebraic_geometry.Scheme.forget_to_Top AlgebraicGeometry.Scheme.forgetToTop

@[simp]
theorem id_val_base (X : Scheme) : (𝟙 X : _).1.base = 𝟙 _ :=
  rfl
#align algebraic_geometry.Scheme.id_val_base AlgebraicGeometry.Scheme.id_val_base

@[simp]
theorem id_app {X : Scheme} (U : (Opens X.carrier)ᵒᵖ) :
    (𝟙 X : _).val.c.app U =
      X.Presheaf.map (eqToHom (by induction U using Opposite.rec'; cases U; rfl)) :=
  PresheafedSpace.id_c_app X.toPresheafedSpace U
#align algebraic_geometry.Scheme.id_app AlgebraicGeometry.Scheme.id_app

@[reassoc]
theorem comp_val {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).val = f.val ≫ g.val :=
  rfl
#align algebraic_geometry.Scheme.comp_val AlgebraicGeometry.Scheme.comp_val

@[reassoc, simp]
theorem comp_coeBase {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).val.base = f.val.base ≫ g.val.base :=
  rfl
#align algebraic_geometry.Scheme.comp_coe_base AlgebraicGeometry.Scheme.comp_coeBase

@[reassoc, elementwise]
theorem comp_val_base {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).val.base = f.val.base ≫ g.val.base :=
  rfl
#align algebraic_geometry.Scheme.comp_val_base AlgebraicGeometry.Scheme.comp_val_base

@[reassoc, simp]
theorem comp_val_c_app {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
    (f ≫ g).val.c.app U = g.val.c.app U ≫ f.val.c.app _ :=
  rfl
#align algebraic_geometry.Scheme.comp_val_c_app AlgebraicGeometry.Scheme.comp_val_c_app

theorem congr_app {X Y : Scheme} {f g : X ⟶ Y} (e : f = g) (U) :
    f.val.c.app U = g.val.c.app U ≫ X.Presheaf.map (eqToHom (by subst e)) := by subst e; dsimp; simp
#align algebraic_geometry.Scheme.congr_app AlgebraicGeometry.Scheme.congr_app

theorem app_eq {X Y : Scheme} (f : X ⟶ Y) {U V : Opens Y.carrier} (e : U = V) :
    f.val.c.app (op U) =
      Y.Presheaf.map (eqToHom e.symm).op ≫
        f.val.c.app (op V) ≫ X.Presheaf.map (eqToHom (congr_arg (Opens.map f.val.base).obj e)).op :=
  by
  rw [← is_iso.inv_comp_eq, ← functor.map_inv, f.val.c.naturality, presheaf.pushforward_obj_map]
  congr
#align algebraic_geometry.Scheme.app_eq AlgebraicGeometry.Scheme.app_eq

instance is_locallyRingedSpace_iso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] :
    @IsIso LocallyRingedSpace _ _ _ f :=
  forgetToLocallyRingedSpace.map_isIso f
#align algebraic_geometry.Scheme.is_LocallyRingedSpace_iso AlgebraicGeometry.Scheme.is_locallyRingedSpace_iso

@[simp]
theorem inv_val_c_app {X Y : Scheme} (f : X ⟶ Y) [IsIso f] (U : Opens X.carrier) :
    (inv f).val.c.app (op U) =
      X.Presheaf.map
          (eqToHom <| by rw [is_iso.hom_inv_id]; ext1; rfl :
              (Opens.map (f ≫ inv f).1.base).obj U ⟶ U).op ≫
        inv (f.val.c.app (op <| (Opens.map _).obj U)) := by
  rw [is_iso.eq_comp_inv]
  erw [← Scheme.comp_val_c_app]
  rw [Scheme.congr_app (is_iso.hom_inv_id f), Scheme.id_app, ← functor.map_comp, eq_to_hom_trans,
    eq_to_hom_op]
  rfl
#align algebraic_geometry.Scheme.inv_val_c_app AlgebraicGeometry.Scheme.inv_val_c_app

/-- Given a morphism of schemes `f : X ⟶ Y`, and open sets `U ⊆ Y`, `V ⊆ f ⁻¹' U`,
this is the induced map `Γ(Y, U) ⟶ Γ(X, V)`. -/
abbrev Hom.appLe {X Y : Scheme} (f : X ⟶ Y) {V : Opens X.carrier} {U : Opens Y.carrier}
    (e : V ≤ (Opens.map f.1.base).obj U) : Y.Presheaf.obj (op U) ⟶ X.Presheaf.obj (op V) :=
  f.1.c.app (op U) ≫ X.Presheaf.map (homOfLE e).op
#align algebraic_geometry.Scheme.hom.app_le AlgebraicGeometry.Scheme.Hom.appLe

/-- The spectrum of a commutative ring, as a scheme.
-/
def specObj (R : CommRingCat) : Scheme where
  local_affine x := ⟨⟨⊤, trivial⟩, R, ⟨(Spec.toLocallyRingedSpace.obj (op R)).restrictTopIso⟩⟩
  toLocallyRingedSpace := Spec.locallyRingedSpaceObj R
#align algebraic_geometry.Scheme.Spec_obj AlgebraicGeometry.Scheme.specObj

@[simp]
theorem specObj_toLocallyRingedSpace (R : CommRingCat) :
    (specObj R).toLocallyRingedSpace = Spec.locallyRingedSpaceObj R :=
  rfl
#align algebraic_geometry.Scheme.Spec_obj_to_LocallyRingedSpace AlgebraicGeometry.Scheme.specObj_toLocallyRingedSpace

/-- The induced map of a ring homomorphism on the ring spectra, as a morphism of schemes.
-/
def specMap {R S : CommRingCat} (f : R ⟶ S) : specObj S ⟶ specObj R :=
  (Spec.locallyRingedSpaceMap f : Spec.locallyRingedSpaceObj S ⟶ Spec.locallyRingedSpaceObj R)
#align algebraic_geometry.Scheme.Spec_map AlgebraicGeometry.Scheme.specMap

@[simp]
theorem specMap_id (R : CommRingCat) : specMap (𝟙 R) = 𝟙 (specObj R) :=
  Spec.locallyRingedSpaceMap_id R
#align algebraic_geometry.Scheme.Spec_map_id AlgebraicGeometry.Scheme.specMap_id

theorem specMap_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T) :
    specMap (f ≫ g) = specMap g ≫ specMap f :=
  Spec.locallyRingedSpaceMap_comp f g
#align algebraic_geometry.Scheme.Spec_map_comp AlgebraicGeometry.Scheme.specMap_comp

/-- The spectrum, as a contravariant functor from commutative rings to schemes.
-/
@[simps]
def spec : CommRingCatᵒᵖ ⥤ Scheme where
  obj R := specObj (unop R)
  map R S f := specMap f.unop
  map_id' R := by rw [unop_id, Spec_map_id]
  map_comp' R S T f g := by rw [unop_comp, Spec_map_comp]
#align algebraic_geometry.Scheme.Spec AlgebraicGeometry.Scheme.spec

/-- The empty scheme.
-/
@[simps]
def empty.{u} : Scheme.{u} where
  carrier := TopCat.of PEmpty
  Presheaf := (CategoryTheory.Functor.const _).obj (CommRingCat.of PUnit)
  IsSheaf := Presheaf.isSheaf_of_isTerminal _ CommRingCat.punitIsTerminal
  LocalRing x := PEmpty.elim x
  local_affine x := PEmpty.elim x
#align algebraic_geometry.Scheme.empty AlgebraicGeometry.Scheme.empty

instance : EmptyCollection Scheme :=
  ⟨empty⟩

instance : Inhabited Scheme :=
  ⟨∅⟩

/-- The global sections, notated Gamma.
-/
def Γ : Schemeᵒᵖ ⥤ CommRingCat :=
  (inducedFunctor Scheme.toLocallyRingedSpace).op ⋙ LocallyRingedSpace.Γ
#align algebraic_geometry.Scheme.Γ AlgebraicGeometry.Scheme.Γ

theorem Γ_def : Γ = (inducedFunctor Scheme.toLocallyRingedSpace).op ⋙ LocallyRingedSpace.Γ :=
  rfl
#align algebraic_geometry.Scheme.Γ_def AlgebraicGeometry.Scheme.Γ_def

@[simp]
theorem Γ_obj (X : Schemeᵒᵖ) : Γ.obj X = (unop X).Presheaf.obj (op ⊤) :=
  rfl
#align algebraic_geometry.Scheme.Γ_obj AlgebraicGeometry.Scheme.Γ_obj

theorem Γ_obj_op (X : Scheme) : Γ.obj (op X) = X.Presheaf.obj (op ⊤) :=
  rfl
#align algebraic_geometry.Scheme.Γ_obj_op AlgebraicGeometry.Scheme.Γ_obj_op

@[simp]
theorem Γ_map {X Y : Schemeᵒᵖ} (f : X ⟶ Y) : Γ.map f = f.unop.1.c.app (op ⊤) :=
  rfl
#align algebraic_geometry.Scheme.Γ_map AlgebraicGeometry.Scheme.Γ_map

theorem Γ_map_op {X Y : Scheme} (f : X ⟶ Y) : Γ.map f.op = f.1.c.app (op ⊤) :=
  rfl
#align algebraic_geometry.Scheme.Γ_map_op AlgebraicGeometry.Scheme.Γ_map_op

section BasicOpen

variable (X : Scheme) {V U : Opens X.carrier} (f g : X.Presheaf.obj (op U))

/-- The subset of the underlying space where the given section does not vanish. -/
def basicOpen : Opens X.carrier :=
  X.toLocallyRingedSpace.toRingedSpace.basicOpen f
#align algebraic_geometry.Scheme.basic_open AlgebraicGeometry.Scheme.basicOpen

@[simp]
theorem mem_basicOpen (x : U) : ↑x ∈ X.basicOpen f ↔ IsUnit (X.Presheaf.germ x f) :=
  RingedSpace.mem_basicOpen _ _ _
#align algebraic_geometry.Scheme.mem_basic_open AlgebraicGeometry.Scheme.mem_basicOpen

@[simp]
theorem mem_basicOpen_top (f : X.Presheaf.obj (op ⊤)) (x : X.carrier) :
    x ∈ X.basicOpen f ↔ IsUnit (X.Presheaf.germ (⟨x, trivial⟩ : (⊤ : Opens _)) f) :=
  RingedSpace.mem_basicOpen _ f ⟨x, trivial⟩
#align algebraic_geometry.Scheme.mem_basic_open_top AlgebraicGeometry.Scheme.mem_basicOpen_top

@[simp]
theorem basicOpen_res (i : op U ⟶ op V) : X.basicOpen (X.Presheaf.map i f) = V ⊓ X.basicOpen f :=
  RingedSpace.basicOpen_res _ i f
#align algebraic_geometry.Scheme.basic_open_res AlgebraicGeometry.Scheme.basicOpen_res

-- This should fire before `basic_open_res`.
@[simp]
theorem basicOpen_res_eq (i : op U ⟶ op V) [IsIso i] :
    X.basicOpen (X.Presheaf.map i f) = X.basicOpen f :=
  RingedSpace.basicOpen_res_eq _ i f
#align algebraic_geometry.Scheme.basic_open_res_eq AlgebraicGeometry.Scheme.basicOpen_res_eq

@[sheaf_restrict]
theorem basicOpen_le : X.basicOpen f ≤ U :=
  RingedSpace.basicOpen_le _ _
#align algebraic_geometry.Scheme.basic_open_le AlgebraicGeometry.Scheme.basicOpen_le

@[simp]
theorem preimage_basicOpen {X Y : Scheme} (f : X ⟶ Y) {U : Opens Y.carrier}
    (r : Y.Presheaf.obj <| op U) :
    (Opens.map f.1.base).obj (Y.basicOpen r) =
      @Scheme.basicOpen X ((Opens.map f.1.base).obj U) (f.1.c.app _ r) :=
  LocallyRingedSpace.preimage_basicOpen f r
#align algebraic_geometry.Scheme.preimage_basic_open AlgebraicGeometry.Scheme.preimage_basicOpen

@[simp]
theorem basicOpen_zero (U : Opens X.carrier) : X.basicOpen (0 : X.Presheaf.obj <| op U) = ⊥ :=
  LocallyRingedSpace.basicOpen_zero _ U
#align algebraic_geometry.Scheme.basic_open_zero AlgebraicGeometry.Scheme.basicOpen_zero

@[simp]
theorem basicOpen_mul : X.basicOpen (f * g) = X.basicOpen f ⊓ X.basicOpen g :=
  RingedSpace.basicOpen_mul _ _ _
#align algebraic_geometry.Scheme.basic_open_mul AlgebraicGeometry.Scheme.basicOpen_mul

theorem basicOpen_of_isUnit {f : X.Presheaf.obj (op U)} (hf : IsUnit f) : X.basicOpen f = U :=
  RingedSpace.basicOpen_of_isUnit _ hf
#align algebraic_geometry.Scheme.basic_open_of_is_unit AlgebraicGeometry.Scheme.basicOpen_of_isUnit

end BasicOpen

end Scheme

theorem basicOpen_eq_of_affine {R : CommRingCat} (f : R) :
    (Scheme.spec.obj <| op R).basicOpen ((SpecΓIdentity.app R).inv f) = PrimeSpectrum.basicOpen f :=
  by
  ext
  erw [Scheme.mem_basic_open_top]
  suffices IsUnit (structure_sheaf.to_stalk R x f) ↔ f ∉ PrimeSpectrum.asIdeal x by exact this
  erw [← isUnit_map_iff (structure_sheaf.stalk_to_fiber_ring_hom R x),
    structure_sheaf.stalk_to_fiber_ring_hom_to_stalk]
  exact
    (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime (PrimeSpectrum.asIdeal x))
        (PrimeSpectrum.asIdeal x) f :
      _)
#align algebraic_geometry.basic_open_eq_of_affine AlgebraicGeometry.basicOpen_eq_of_affine

@[simp]
theorem basicOpen_eq_of_affine' {R : CommRingCat}
    (f : (Spec.toSheafedSpace.obj (op R)).Presheaf.obj (op ⊤)) :
    (Scheme.spec.obj <| op R).basicOpen f = PrimeSpectrum.basicOpen ((SpecΓIdentity.app R).Hom f) :=
  by
  convert basic_open_eq_of_affine ((Spec_Γ_identity.app R).Hom f)
  exact (iso.hom_inv_id_apply _ _).symm
#align algebraic_geometry.basic_open_eq_of_affine' AlgebraicGeometry.basicOpen_eq_of_affine'

end AlgebraicGeometry

