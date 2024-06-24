/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.CategoryTheory.Elementwise

#align_import algebraic_geometry.Scheme from "leanprover-community/mathlib"@"88474d1b5af6d37c2ab728b757771bced7f5194c"

/-!
# The category of schemes

A scheme is a locally ringed space such that every point is contained in some open set
where there is an isomorphism of presheaves between the restriction to that open set,
and the structure sheaf of `Spec R`, for some commutative ring `R`.

A morphism of schemes is just a morphism of the underlying locally ringed spaces.

-/

-- Explicit universe annotations were used in this file to improve perfomance #12737

set_option linter.uppercaseLean3 false

universe u

noncomputable section

open TopologicalSpace

open CategoryTheory

open TopCat

open Opposite

namespace AlgebraicGeometry

/-- We define `Scheme` as an `X : LocallyRingedSpace`,
along with a proof that every point has an open neighbourhood `U`
so that the restriction of `X` to `U` is isomorphic,
as a locally ringed space, to `Spec.toLocallyRingedSpace.obj (op R)`
for some `R : CommRingCat`.
-/
structure Scheme extends LocallyRingedSpace where
  local_affine :
    ∀ x : toLocallyRingedSpace,
      ∃ (U : OpenNhds x) (R : CommRingCat),
        Nonempty
          (toLocallyRingedSpace.restrict U.openEmbedding ≅ Spec.toLocallyRingedSpace.obj (op R))
#align algebraic_geometry.Scheme AlgebraicGeometry.Scheme

namespace Scheme

/-- A morphism between schemes is a morphism between the underlying locally ringed spaces. -/
-- @[nolint has_nonempty_instance] -- Porting note(#5171): linter not ported yet
def Hom (X Y : Scheme) : Type* :=
  X.toLocallyRingedSpace ⟶ Y.toLocallyRingedSpace
#align algebraic_geometry.Scheme.hom AlgebraicGeometry.Scheme.Hom

/-- Schemes are a full subcategory of locally ringed spaces.
-/
instance : Category Scheme :=
  { InducedCategory.category Scheme.toLocallyRingedSpace with Hom := Hom }

/-- `f ⁻¹ᵁ U` is notation for `(Opens.map f.1.base).obj U`,
  the preimage of an open set `U` under `f`. -/
scoped[AlgebraicGeometry] notation3:90 f:91 " ⁻¹ᵁ " U:90 =>
  (Opens.map (f : LocallyRingedSpace.Hom _ _).val.base).obj U

/-- `Γ(X, U)` is notation for `X.presheaf.obj (op U)`. -/
scoped[AlgebraicGeometry] notation3 "Γ(" X ", " U ")" =>
  (PresheafedSpace.presheaf (SheafedSpace.toPresheafedSpace
    (LocallyRingedSpace.toSheafedSpace (Scheme.toLocallyRingedSpace X)))).obj (op U)

@[continuity, fun_prop]
lemma Hom.continuous {X Y : Scheme} (f : X ⟶ Y) : Continuous f.1.base := f.1.base.2

/-- The structure sheaf of a scheme. -/
protected abbrev sheaf (X : Scheme) :=
  X.toSheafedSpace.sheaf
#align algebraic_geometry.Scheme.sheaf AlgebraicGeometry.Scheme.sheaf

instance : CoeSort Scheme Type* where
  coe X := X.carrier

/-- The forgetful functor from `Scheme` to `LocallyRingedSpace`. -/
@[simps!]
def forgetToLocallyRingedSpace : Scheme ⥤ LocallyRingedSpace :=
  inducedFunctor _
-- deriving Full, Faithful -- Porting note: no delta derive handler, see https://github.com/leanprover-community/mathlib4/issues/5020
#align algebraic_geometry.Scheme.forget_to_LocallyRingedSpace AlgebraicGeometry.Scheme.forgetToLocallyRingedSpace

/-- The forget functor `Scheme ⥤ LocallyRingedSpace` is fully faithful. -/
@[simps!]
def fullyFaithfulForgetToLocallyRingedSpace :
    forgetToLocallyRingedSpace.FullyFaithful :=
  fullyFaithfulInducedFunctor _

instance : forgetToLocallyRingedSpace.Full :=
  InducedCategory.full _

instance : forgetToLocallyRingedSpace.Faithful :=
  InducedCategory.faithful _

/-- The forgetful functor from `Scheme` to `TopCat`. -/
@[simps!]
def forgetToTop : Scheme ⥤ TopCat :=
  Scheme.forgetToLocallyRingedSpace ⋙ LocallyRingedSpace.forgetToTop
#align algebraic_geometry.Scheme.forget_to_Top AlgebraicGeometry.Scheme.forgetToTop

-- Porting note: Lean seems not able to find this coercion any more
instance hasCoeToTopCat : CoeOut Scheme TopCat where
  coe X := X.carrier

-- Porting note: added this unification hint just in case
/-- forgetful functor to `TopCat` is the same as coercion -/
unif_hint forgetToTop_obj_eq_coe (X : Scheme) where ⊢
  forgetToTop.obj X ≟ (X : TopCat)

@[simp]
theorem id_val_base (X : Scheme) : (𝟙 X : _).1.base = 𝟙 _ :=
  rfl
#align algebraic_geometry.Scheme.id_val_base AlgebraicGeometry.Scheme.id_val_base

@[simp]
theorem id_app {X : Scheme} (U : (Opens X)ᵒᵖ) :
    (𝟙 X : _).val.c.app U =
      X.presheaf.map (eqToHom (by induction' U with U; cases U; rfl)) :=
  PresheafedSpace.id_c_app X.toPresheafedSpace U
#align algebraic_geometry.Scheme.id_app AlgebraicGeometry.Scheme.id_app

@[reassoc]
theorem comp_val {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).val = f.val ≫ g.val :=
  rfl
#align algebraic_geometry.Scheme.comp_val AlgebraicGeometry.Scheme.comp_val

@[simp, reassoc] -- reassoc lemma does not need `simp`
theorem comp_coeBase {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).val.base = f.val.base ≫ g.val.base :=
  rfl
#align algebraic_geometry.Scheme.comp_coe_base AlgebraicGeometry.Scheme.comp_coeBase

-- Porting note: removed elementwise attribute, as generated lemmas were trivial.
@[reassoc]
theorem comp_val_base {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).val.base = f.val.base ≫ g.val.base :=
  rfl
#align algebraic_geometry.Scheme.comp_val_base AlgebraicGeometry.Scheme.comp_val_base

theorem comp_val_base_apply {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).val.base x = g.val.base (f.val.base x) := by
  simp
#align algebraic_geometry.Scheme.comp_val_base_apply AlgebraicGeometry.Scheme.comp_val_base_apply

@[simp, reassoc] -- reassoc lemma does not need `simp`
theorem comp_val_c_app {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
    (f ≫ g).val.c.app U = g.val.c.app U ≫ f.val.c.app _ :=
  rfl
#align algebraic_geometry.Scheme.comp_val_c_app AlgebraicGeometry.Scheme.comp_val_c_app

theorem congr_app {X Y : Scheme} {f g : X ⟶ Y} (e : f = g) (U) :
    f.val.c.app U = g.val.c.app U ≫ X.presheaf.map (eqToHom (by subst e; rfl)) := by
  subst e; dsimp; simp
#align algebraic_geometry.Scheme.congr_app AlgebraicGeometry.Scheme.congr_app

theorem app_eq {X Y : Scheme} (f : X ⟶ Y) {U V : Opens Y.carrier} (e : U = V) :
    f.val.c.app (op U) =
      Y.presheaf.map (eqToHom e.symm).op ≫
        f.val.c.app (op V) ≫
          X.presheaf.map (eqToHom (congr_arg (Opens.map f.val.base).obj e)).op := by
  rw [← IsIso.inv_comp_eq, ← Functor.map_inv, f.val.c.naturality, Presheaf.pushforwardObj_map]
  cases e
  rfl
#align algebraic_geometry.Scheme.app_eq AlgebraicGeometry.Scheme.app_eq

theorem eqToHom_c_app {X Y : Scheme} (e : X = Y) (U) :
    (eqToHom e).val.c.app U = eqToHom (by subst e; rfl) := by subst e; rfl

-- Porting note: in `AffineScheme.lean` file, `eqToHom_op` can't be used in `(e)rw` or `simp(_rw)`
-- when terms get very complicated. See `AlgebraicGeometry.IsAffineOpen.isLocalization_stalk_aux`.
lemma presheaf_map_eqToHom_op (X : Scheme) (U V : Opens X) (i : U = V) :
    X.presheaf.map (eqToHom i).op = eqToHom (i ▸ rfl) := by
  rw [eqToHom_op, eqToHom_map]

instance is_locallyRingedSpace_iso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] :
    @IsIso LocallyRingedSpace _ _ _ f :=
  forgetToLocallyRingedSpace.map_isIso f
#align algebraic_geometry.Scheme.is_LocallyRingedSpace_iso AlgebraicGeometry.Scheme.is_locallyRingedSpace_iso

instance val_base_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] : IsIso f.1.base :=
  Scheme.forgetToTop.map_isIso f
#align algebraic_geometry.Scheme.val_base_is_iso AlgebraicGeometry.Scheme.val_base_isIso

-- Porting note: need an extra instance here.
instance {X Y : Scheme} (f : X ⟶ Y) [IsIso f] (U) : IsIso (f.val.c.app U) :=
  haveI := PresheafedSpace.c_isIso_of_iso f.val
  NatIso.isIso_app_of_isIso _ _

@[simp]
theorem inv_val_c_app {X Y : Scheme} (f : X ⟶ Y) [IsIso f] (U : Opens X) :
    (inv f).val.c.app (op U) =
      X.presheaf.map
          (eqToHom <| by rw [IsIso.hom_inv_id]; ext1; rfl :
              (Opens.map (f ≫ inv f).1.base).obj U ⟶ U).op ≫
        inv (f.val.c.app (op <| (Opens.map _).obj U)) := by
  rw [IsIso.eq_comp_inv]
  erw [← Scheme.comp_val_c_app]
  rw [Scheme.congr_app (IsIso.hom_inv_id f), Scheme.id_app, ← Functor.map_comp, eqToHom_trans,
    eqToHom_op]
#align algebraic_geometry.Scheme.inv_val_c_app AlgebraicGeometry.Scheme.inv_val_c_app

theorem inv_val_c_app_top {X Y : Scheme} (f : X ⟶ Y) [IsIso f] :
    (inv f).val.c.app (op ⊤) = inv (f.val.c.app (op ⊤)) := by simp

/-- Given a morphism of schemes `f : X ⟶ Y`, and open sets `U ⊆ Y`, `V ⊆ f ⁻¹' U`,
this is the induced map `Γ(Y, U) ⟶ Γ(X, V)`. -/
abbrev Hom.appLe {X Y : Scheme} (f : X ⟶ Y) {V : Opens X} {U : Opens Y}
    (e : V ≤ f ⁻¹ᵁ U) : Γ(Y, U) ⟶ Γ(X, V) :=
  f.1.c.app (op U) ≫ X.presheaf.map (homOfLE e).op
#align algebraic_geometry.Scheme.hom.app_le AlgebraicGeometry.Scheme.Hom.appLe

/-- The spectrum of a commutative ring, as a scheme.
-/
def specObj (R : CommRingCat) : Scheme where
  local_affine _ := ⟨⟨⊤, trivial⟩, R, ⟨(Spec.toLocallyRingedSpace.obj (op R)).restrictTopIso⟩⟩
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

The simp normal form should be `Scheme.Spec.obj (op R)` (with the notation `𝖲𝗉𝖾𝖼 R`) and
`Scheme.Spec.map f.op` (with the notation `𝖲𝗉𝖾𝖼(f)`).
-/
def Spec : CommRingCatᵒᵖ ⥤ Scheme where
  obj R := specObj (unop R)
  map f := specMap f.unop
  map_id R := by simp
  map_comp f g := by simp [specMap_comp]
#align algebraic_geometry.Scheme.Spec AlgebraicGeometry.Scheme.Spec

/-- `𝖲𝗉𝖾𝖼 R` is notation for `Sceme.Spec.obj (op R)`. -/
scoped[AlgebraicGeometry] notation3 "𝖲𝗉𝖾𝖼 " R:20 => Scheme.Spec.obj (op R)

/-- `𝖲𝗉𝖾𝖼(f)` is notation for `Sceme.Spec.map f.op`. -/
scoped[AlgebraicGeometry] notation3 "𝖲𝗉𝖾𝖼(" f ")" => Scheme.Spec.map (Quiver.Hom.op f)

section

variable {R S : CommRingCat} (f : R ⟶ S)

-- The lemmas below are not tagged simp to respect the abstraction.
lemma Spec_obj_carrier (R) : (𝖲𝗉𝖾𝖼 R).carrier = PrimeSpectrum R := rfl
lemma Spec_obj_sheaf (R) : (𝖲𝗉𝖾𝖼 R).sheaf = Spec.structureSheaf R := rfl
lemma Spec_obj_presheaf (R) : (𝖲𝗉𝖾𝖼 R).presheaf = (Spec.structureSheaf R).1 := rfl
lemma Spec_map_base : 𝖲𝗉𝖾𝖼(f).1.base = PrimeSpectrum.comap f := rfl

set_option maxHeartbeats 800000 in
lemma Spec_map_c_app (U) :
    𝖲𝗉𝖾𝖼(f).1.c.app (op U) = StructureSheaf.comap f U (𝖲𝗉𝖾𝖼(f) ⁻¹ᵁ U) le_rfl := rfl

lemma Spec_map_appLE {U V} (e : U ≤ 𝖲𝗉𝖾𝖼(f) ⁻¹ᵁ V) :
    Hom.appLe 𝖲𝗉𝖾𝖼(f) e = StructureSheaf.comap f V U e := rfl

end

/-- The empty scheme.
-/
@[simps]
def empty : Scheme where
  carrier := TopCat.of PEmpty
  presheaf := (CategoryTheory.Functor.const _).obj (CommRingCat.of PUnit)
  IsSheaf := Presheaf.isSheaf_of_isTerminal _ CommRingCat.punitIsTerminal
  localRing x := PEmpty.elim x
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
theorem Γ_obj (X : Schemeᵒᵖ) : Γ.obj X = (unop X).presheaf.obj (op ⊤) :=
  rfl
#align algebraic_geometry.Scheme.Γ_obj AlgebraicGeometry.Scheme.Γ_obj

theorem Γ_obj_op (X : Scheme) : Γ.obj (op X) = Γ(X, ⊤) :=
  rfl
#align algebraic_geometry.Scheme.Γ_obj_op AlgebraicGeometry.Scheme.Γ_obj_op

@[simp]
theorem Γ_map {X Y : Schemeᵒᵖ} (f : X ⟶ Y) : Γ.map f = f.unop.1.c.app (op ⊤) :=
  rfl
#align algebraic_geometry.Scheme.Γ_map AlgebraicGeometry.Scheme.Γ_map

theorem Γ_map_op {X Y : Scheme} (f : X ⟶ Y) : Γ.map f.op = f.1.c.app (op ⊤) :=
  rfl
#align algebraic_geometry.Scheme.Γ_map_op AlgebraicGeometry.Scheme.Γ_map_op

/-- The counit (`SpecΓIdentity.inv.op`) of the adjunction `Γ ⊣ Spec` as an isomorphism. -/
-- This is not marked simp to respect the abstraction
@[simps! (config := .lemmasOnly) hom_app inv_app]
def SpecΓIdentity : Scheme.Spec.rightOp ⋙ Scheme.Γ ≅ 𝟭 _ :=
  Iso.symm <| NatIso.ofComponents.{u,u,u+1,u+1}
    (fun R => asIso (StructureSheaf.toOpen R ⊤))
    (fun {X Y} f => by convert Spec_Γ_naturality (R := X) (S := Y) f)

section BasicOpen

variable (X : Scheme) {V U : Opens X} (f g : Γ(X, U))

/-- The subset of the underlying space where the given section does not vanish. -/
def basicOpen : Opens X :=
  X.toLocallyRingedSpace.toRingedSpace.basicOpen f
#align algebraic_geometry.Scheme.basic_open AlgebraicGeometry.Scheme.basicOpen

@[simp]
theorem mem_basicOpen (x : U) : ↑x ∈ X.basicOpen f ↔ IsUnit (X.presheaf.germ x f) :=
  RingedSpace.mem_basicOpen _ _ _
#align algebraic_geometry.Scheme.mem_basic_open AlgebraicGeometry.Scheme.mem_basicOpen

theorem mem_basicOpen_top' {U : Opens X} (f : Γ(X, U)) (x : X) :
    x ∈ X.basicOpen f ↔ ∃ (m : x ∈ U), IsUnit (X.presheaf.germ (⟨x, m⟩ : U) f) := by
  fconstructor
  · rintro ⟨y, hy1, rfl⟩
    exact ⟨y.2, hy1⟩
  · rintro ⟨m, hm⟩
    exact ⟨⟨x, m⟩, hm, rfl⟩

@[simp]
theorem mem_basicOpen_top (f : Γ(X, ⊤)) (x : X) :
    x ∈ X.basicOpen f ↔ IsUnit (X.presheaf.germ (⟨x, trivial⟩ : (⊤ : Opens _)) f) :=
  RingedSpace.mem_basicOpen _ f ⟨x, trivial⟩
#align algebraic_geometry.Scheme.mem_basic_open_top AlgebraicGeometry.Scheme.mem_basicOpen_top

@[simp]
theorem basicOpen_res (i : op U ⟶ op V) : X.basicOpen (X.presheaf.map i f) = V ⊓ X.basicOpen f :=
  RingedSpace.basicOpen_res _ i f
#align algebraic_geometry.Scheme.basic_open_res AlgebraicGeometry.Scheme.basicOpen_res

-- This should fire before `basicOpen_res`.
@[simp 1100]
theorem basicOpen_res_eq (i : op U ⟶ op V) [IsIso i] :
    X.basicOpen (X.presheaf.map i f) = X.basicOpen f :=
  RingedSpace.basicOpen_res_eq _ i f
#align algebraic_geometry.Scheme.basic_open_res_eq AlgebraicGeometry.Scheme.basicOpen_res_eq

@[sheaf_restrict]
theorem basicOpen_le : X.basicOpen f ≤ U :=
  RingedSpace.basicOpen_le _ _
#align algebraic_geometry.Scheme.basic_open_le AlgebraicGeometry.Scheme.basicOpen_le

@[sheaf_restrict]
lemma basicOpen_restrict (i : V ⟶ U) (f : Γ(X, U)) :
    X.basicOpen (f |_ₕ i) ≤ X.basicOpen f :=
  (Scheme.basicOpen_res _ _ _).trans_le inf_le_right

@[simp]
theorem preimage_basicOpen {X Y : Scheme} (f : X ⟶ Y) {U : Opens Y} (r : Γ(Y, U)) :
    f ⁻¹ᵁ (Y.basicOpen r) = X.basicOpen (f.1.c.app (op U) r) :=
  LocallyRingedSpace.preimage_basicOpen f r
#align algebraic_geometry.Scheme.preimage_basic_open AlgebraicGeometry.Scheme.preimage_basicOpen

@[simp]
theorem basicOpen_zero (U : Opens X) : X.basicOpen (0 : Γ(X, U)) = ⊥ :=
  LocallyRingedSpace.basicOpen_zero _ U
#align algebraic_geometry.Scheme.basic_open_zero AlgebraicGeometry.Scheme.basicOpen_zero

@[simp]
theorem basicOpen_mul : X.basicOpen (f * g) = X.basicOpen f ⊓ X.basicOpen g :=
  RingedSpace.basicOpen_mul _ _ _
#align algebraic_geometry.Scheme.basic_open_mul AlgebraicGeometry.Scheme.basicOpen_mul

theorem basicOpen_of_isUnit {f : Γ(X, U)} (hf : IsUnit f) : X.basicOpen f = U :=
  RingedSpace.basicOpen_of_isUnit _ hf
#align algebraic_geometry.Scheme.basic_open_of_is_unit AlgebraicGeometry.Scheme.basicOpen_of_isUnit

instance algebra_section_section_basicOpen {X : Scheme} {U : Opens X} (f : Γ(X, U)) :
    Algebra Γ(X, U) Γ(X, X.basicOpen f) :=
  (X.presheaf.map (homOfLE <| X.basicOpen_le f : _ ⟶ U).op).toAlgebra

end BasicOpen

end Scheme

theorem basicOpen_eq_of_affine {R : CommRingCat} (f : R) :
    (𝖲𝗉𝖾𝖼 R).basicOpen ((Scheme.SpecΓIdentity.app R).inv f) = PrimeSpectrum.basicOpen f := by
  ext x
  erw [Scheme.mem_basicOpen_top]
  suffices IsUnit (StructureSheaf.toStalk R x f) ↔ f ∉ PrimeSpectrum.asIdeal x by exact this
  erw [← isUnit_map_iff (StructureSheaf.stalkToFiberRingHom R x),
    StructureSheaf.stalkToFiberRingHom_toStalk]
  exact
    (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime (PrimeSpectrum.asIdeal x))
        (PrimeSpectrum.asIdeal x) f :
      _)
#align algebraic_geometry.basic_open_eq_of_affine AlgebraicGeometry.basicOpen_eq_of_affine

@[simp]
theorem basicOpen_eq_of_affine' {R : CommRingCat} (f : Γ(𝖲𝗉𝖾𝖼 R, ⊤)) :
    (𝖲𝗉𝖾𝖼 R).basicOpen f = PrimeSpectrum.basicOpen ((Scheme.SpecΓIdentity.app R).hom f) := by
  convert basicOpen_eq_of_affine ((Scheme.SpecΓIdentity.app R).hom f)
  exact (Iso.hom_inv_id_apply (Scheme.SpecΓIdentity.app R) f).symm
#align algebraic_geometry.basic_open_eq_of_affine' AlgebraicGeometry.basicOpen_eq_of_affine'

theorem Scheme.Spec_map_presheaf_map_eqToHom {X : Scheme} {U V : Opens X} (h : U = V) (W) :
    𝖲𝗉𝖾𝖼(X.presheaf.map (eqToHom h).op).val.c.app W =
      eqToHom (by cases h; induction W using Opposite.rec'; dsimp; simp) := by
  have : Scheme.Spec.map (X.presheaf.map (𝟙 (op U))).op = 𝟙 _ := by
    rw [X.presheaf.map_id, op_id, Scheme.Spec.map_id]
  cases h
  refine (Scheme.congr_app this _).trans ?_
  simp [eqToHom_map]
#align algebraic_geometry.Scheme.Spec_map_presheaf_map_eqToHom AlgebraicGeometry.Scheme.Spec_map_presheaf_map_eqToHom

end AlgebraicGeometry
