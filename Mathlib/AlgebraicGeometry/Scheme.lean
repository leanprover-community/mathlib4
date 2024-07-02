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

namespace Hom

variable {X Y : Scheme.{u}} (f : Hom X Y) {U U' : Opens Y} {V V' : Opens X}

/-- Given a morphism of schemes `f : X ⟶ Y`, and open `U ⊆ Y`,
this is the induced map `Γ(Y, U) ⟶ Γ(X, f ⁻¹ᵁ U)`. -/
abbrev app (U : Opens Y) : Γ(Y, U) ⟶ Γ(X, f ⁻¹ᵁ U) :=
  f.1.c.app (op U)

@[reassoc]
lemma naturality (i : op U' ⟶ op U) :
    Y.presheaf.map i ≫ f.app U = f.app U' ≫ X.presheaf.map ((Opens.map f.1.base).map i.unop).op :=
  f.1.c.naturality i

/-- Given a morphism of schemes `f : X ⟶ Y`, and open sets `U ⊆ Y`, `V ⊆ f ⁻¹' U`,
this is the induced map `Γ(Y, U) ⟶ Γ(X, V)`. -/
def appLE (U : Opens Y) (V : Opens X) (e : V ≤ f ⁻¹ᵁ U) : Γ(Y, U) ⟶ Γ(X, V) :=
  f.app U ≫ X.presheaf.map (homOfLE e).op
#align algebraic_geometry.Scheme.hom.app_le AlgebraicGeometry.Scheme.Hom.appLE

@[reassoc (attr := simp)]
lemma appLE_map (e : V ≤ f ⁻¹ᵁ U) (i : op V ⟶ op V') :
    f.appLE U V e ≫ X.presheaf.map i = f.appLE U V' (i.unop.le.trans e) := by
  rw [Hom.appLE, Category.assoc, ← Functor.map_comp]
  rfl

@[reassoc]
lemma appLE_map' (e : V ≤ f ⁻¹ᵁ U) (i : V = V') :
    f.appLE U V' (i ▸ e) ≫ X.presheaf.map (eqToHom i).op = f.appLE U V e :=
  appLE_map _ _ _

@[reassoc (attr := simp)]
lemma map_appLE (e : V ≤ f ⁻¹ᵁ U) (i : op U' ⟶ op U) :
    Y.presheaf.map i ≫ f.appLE U V e =
      f.appLE U' V (e.trans ((Opens.map f.1.base).map i.unop).le) := by
  rw [Hom.appLE, f.naturality_assoc, ← Functor.map_comp]
  rfl

@[reassoc]
lemma map_appLE' (e : V ≤ f ⁻¹ᵁ U) (i : U' = U) :
    Y.presheaf.map (eqToHom i).op ≫ f.appLE U' V (i ▸ e) = f.appLE U V e :=
  map_appLE _ _ _

lemma app_eq_appLE {U : Opens Y} :
    f.app U = f.appLE U _ le_rfl := by
  simp [Hom.appLE]

lemma appLE_congr (e : V ≤ f ⁻¹ᵁ U) (e₁ : U = U') (e₂ : V = V')
    (P : ∀ {R S : Type u} [CommRing R] [CommRing S] (_ : R →+* S), Prop) :
    P (f.appLE U V e) ↔ P (f.appLE U' V' (e₁ ▸ e₂ ▸ e)) := by
  subst e₁; subst e₂; rfl

end Hom

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
theorem id_app {X : Scheme} (U : Opens X) :
    (𝟙 X : _).app U = 𝟙 _ := rfl
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
theorem comp_app {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
    (f ≫ g).app U = g.app U ≫ f.app _ :=
  rfl
#align algebraic_geometry.Scheme.comp_val_c_app AlgebraicGeometry.Scheme.comp_app

@[deprecated (since := "2024-06-23")] alias comp_val_c_app := comp_app
@[deprecated (since := "2024-06-23")] alias comp_val_c_app_assoc := comp_app_assoc

theorem appLE_comp_appLE {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U V W e₁ e₂) :
    g.appLE U V e₁ ≫ f.appLE V W e₂ =
      (f ≫ g).appLE U W (e₂.trans ((Opens.map f.1.base).map (homOfLE e₁)).le) := by
  dsimp [Hom.appLE]
  rw [Category.assoc, f.naturality_assoc, ← Functor.map_comp]
  rfl

@[simp, reassoc] -- reassoc lemma does not need `simp`
theorem comp_appLE {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U V e) :
    (f ≫ g).appLE U V e = g.app U ≫ f.appLE _ V e := by
  rw [g.app_eq_appLE, appLE_comp_appLE]

theorem congr_app {X Y : Scheme} {f g : X ⟶ Y} (e : f = g) (U) :
    f.app U = g.app U ≫ X.presheaf.map (eqToHom (by subst e; rfl)).op := by
  subst e; dsimp; simp
#align algebraic_geometry.Scheme.congr_app AlgebraicGeometry.Scheme.congr_app

theorem app_eq {X Y : Scheme} (f : X ⟶ Y) {U V : Opens Y.carrier} (e : U = V) :
    f.app U =
      Y.presheaf.map (eqToHom e.symm).op ≫
        f.app V ≫
          X.presheaf.map (eqToHom (congr_arg (Opens.map f.val.base).obj e)).op := by
  rw [← IsIso.inv_comp_eq, ← Functor.map_inv, f.val.c.naturality, Presheaf.pushforwardObj_map]
  cases e
  rfl
#align algebraic_geometry.Scheme.app_eq AlgebraicGeometry.Scheme.app_eq

theorem eqToHom_c_app {X Y : Scheme} (e : X = Y) (U) :
    (eqToHom e).app U = eqToHom (by subst e; rfl) := by subst e; rfl

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

instance {X Y : Scheme} (f : X ⟶ Y) [IsIso f] (U) : IsIso (f.app U) :=
  haveI := PresheafedSpace.c_isIso_of_iso f.val
  NatIso.isIso_app_of_isIso _ _

@[simp]
theorem inv_app {X Y : Scheme} (f : X ⟶ Y) [IsIso f] (U : Opens X) :
    (inv f).app U =
      X.presheaf.map (eqToHom (show (f ≫ inv f) ⁻¹ᵁ U = U by rw [IsIso.hom_inv_id]; rfl)).op ≫
        inv (f.app ((inv f) ⁻¹ᵁ U)) := by
  rw [IsIso.eq_comp_inv, ← Scheme.comp_app, Scheme.congr_app (IsIso.hom_inv_id f),
    Scheme.id_app, Category.id_comp]
#align algebraic_geometry.Scheme.inv_val_c_app AlgebraicGeometry.Scheme.inv_app

theorem inv_app_top {X Y : Scheme} (f : X ⟶ Y) [IsIso f] :
    (inv f).app ⊤ = inv (f.app ⊤) := by simp

end Scheme

/-- The spectrum of a commutative ring, as a scheme.
-/
def Spec (R : CommRingCat) : Scheme where
  local_affine _ := ⟨⟨⊤, trivial⟩, R, ⟨(Spec.toLocallyRingedSpace.obj (op R)).restrictTopIso⟩⟩
  toLocallyRingedSpace := Spec.locallyRingedSpaceObj R
#align algebraic_geometry.Scheme.Spec_obj AlgebraicGeometry.Spec

theorem Spec_toLocallyRingedSpace (R : CommRingCat) :
    (Spec R).toLocallyRingedSpace = Spec.locallyRingedSpaceObj R :=
  rfl
#align algebraic_geometry.Scheme.Spec_obj_to_LocallyRingedSpace AlgebraicGeometry.Spec_toLocallyRingedSpace

/-- The induced map of a ring homomorphism on the ring spectra, as a morphism of schemes.
-/
def Spec.map {R S : CommRingCat} (f : R ⟶ S) : Spec S ⟶ Spec R :=
  (Spec.locallyRingedSpaceMap f : Spec.locallyRingedSpaceObj S ⟶ Spec.locallyRingedSpaceObj R)
#align algebraic_geometry.Scheme.Spec_map AlgebraicGeometry.Spec.map

@[simp]
theorem Spec.map_id (R : CommRingCat) : Spec.map (𝟙 R) = 𝟙 (Spec R) :=
  Spec.locallyRingedSpaceMap_id R
#align algebraic_geometry.Scheme.Spec_map_id AlgebraicGeometry.Spec.map_id

@[reassoc, simp]
theorem Spec.map_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T) :
    Spec.map (f ≫ g) = Spec.map g ≫ Spec.map f :=
  Spec.locallyRingedSpaceMap_comp f g
#align algebraic_geometry.Scheme.Spec_map_comp AlgebraicGeometry.Spec.map_comp

/-- The spectrum, as a contravariant functor from commutative rings to schemes. -/
@[simps]
protected def Scheme.Spec : CommRingCatᵒᵖ ⥤ Scheme where
  obj R := Spec (unop R)
  map f := Spec.map f.unop
  map_id R := by simp
  map_comp f g := by simp
#align algebraic_geometry.Scheme.Spec AlgebraicGeometry.Scheme.Spec

lemma Spec.map_eqToHom {R S : CommRingCat} (e : R = S) :
    Spec.map (eqToHom e) = eqToHom (e ▸ rfl) := by
  subst e; exact Spec.map_id _

instance {R S : CommRingCat} (f : R ⟶ S) [IsIso f] : IsIso (Spec.map f) :=
  inferInstanceAs (IsIso <| Scheme.Spec.map f.op)

@[simp]
lemma Spec.map_inv {R S : CommRingCat} (f : R ⟶ S) [IsIso f] :
    Spec.map (inv f) = inv (Spec.map f) := by
  show Scheme.Spec.map (inv f).op = inv (Scheme.Spec.map f.op)
  rw [op_inv, ← Scheme.Spec.map_inv]

section

variable {R S : CommRingCat} (f : R ⟶ S)

-- The lemmas below are not tagged simp to respect the abstraction.
lemma Spec_carrier (R : CommRingCat.{u}) : (Spec R).carrier = PrimeSpectrum R := rfl
lemma Spec_sheaf (R : CommRingCat.{u}) : (Spec R).sheaf = Spec.structureSheaf R := rfl
lemma Spec_presheaf (R : CommRingCat.{u}) : (Spec R).presheaf = (Spec.structureSheaf R).1 := rfl
lemma Spec.map_base : (Spec.map f).1.base = PrimeSpectrum.comap f := rfl

set_option maxHeartbeats 800000 in
lemma Spec.map_app (U) :
    (Spec.map f).app U = StructureSheaf.comap f U (Spec.map f ⁻¹ᵁ U) le_rfl := rfl

lemma Spec.map_appLE {U V} (e : U ≤ Spec.map f ⁻¹ᵁ V) :
    (Spec.map f).appLE V U e = StructureSheaf.comap f V U e := rfl

end

namespace Scheme

/-- The empty scheme. -/
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
theorem Γ_obj (X : Schemeᵒᵖ) : Γ.obj X = Γ(unop X, ⊤) :=
  rfl
#align algebraic_geometry.Scheme.Γ_obj AlgebraicGeometry.Scheme.Γ_obj

theorem Γ_obj_op (X : Scheme) : Γ.obj (op X) = Γ(X, ⊤) :=
  rfl
#align algebraic_geometry.Scheme.Γ_obj_op AlgebraicGeometry.Scheme.Γ_obj_op

@[simp]
theorem Γ_map {X Y : Schemeᵒᵖ} (f : X ⟶ Y) : Γ.map f = f.unop.app ⊤ :=
  rfl
#align algebraic_geometry.Scheme.Γ_map AlgebraicGeometry.Scheme.Γ_map

theorem Γ_map_op {X Y : Scheme} (f : X ⟶ Y) : Γ.map f.op = f.app ⊤ :=
  rfl
#align algebraic_geometry.Scheme.Γ_map_op AlgebraicGeometry.Scheme.Γ_map_op

/--
The counit (`SpecΓIdentity.inv.op`) of the adjunction `Γ ⊣ Spec` as an isomorphism.
This is almost never needed in practical use cases. Use `ΓSpecIso` instead.
-/
def SpecΓIdentity : Scheme.Spec.rightOp ⋙ Scheme.Γ ≅ 𝟭 _ :=
  Iso.symm <| NatIso.ofComponents.{u,u,u+1,u+1}
    (fun R => asIso (StructureSheaf.toOpen R ⊤))
    (fun {X Y} f => by convert Spec_Γ_naturality (R := X) (S := Y) f)

variable (R : CommRingCat.{u})

/-- The global sections of `Spec R` is isomorphic to `R`. -/
def ΓSpecIso : Γ(Spec R, ⊤) ≅ R := SpecΓIdentity.app R

@[simp] lemma SpecΓIdentity_app : SpecΓIdentity.app R = ΓSpecIso R := rfl
@[simp] lemma SpecΓIdentity_hom_app : SpecΓIdentity.hom.app R = (ΓSpecIso R).hom := rfl
@[simp] lemma SpecΓIdentity_inv_app : SpecΓIdentity.inv.app R = (ΓSpecIso R).inv := rfl

@[reassoc (attr := simp)]
lemma ΓSpecIso_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (Spec.map f).app ⊤ ≫ (ΓSpecIso S).hom = (ΓSpecIso R).hom ≫ f := SpecΓIdentity.hom.naturality f

-- The RHS is not necessarily simpler than the LHS, but this direction coincides with the simp
-- direction of `NatTrans.naturality`.
@[reassoc (attr := simp)]
lemma ΓSpecIso_inv_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) :
    f ≫ (ΓSpecIso S).inv = (ΓSpecIso R).inv ≫ (Spec.map f).app ⊤ := SpecΓIdentity.inv.naturality f

-- This is not marked simp to respect the abstraction
lemma ΓSpecIso_inv : (ΓSpecIso R).inv = StructureSheaf.toOpen R ⊤ := rfl

lemma toOpen_eq (U) :
    (by exact StructureSheaf.toOpen R U) =
    (ΓSpecIso R).inv ≫ (Spec R).presheaf.map (homOfLE le_top).op := rfl

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
    f ⁻¹ᵁ (Y.basicOpen r) = X.basicOpen (f.app U r) :=
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
    (Spec R).basicOpen ((Scheme.ΓSpecIso R).inv f) = PrimeSpectrum.basicOpen f := by
  ext x
  simp only [SetLike.mem_coe, Scheme.mem_basicOpen_top, Opens.coe_top]
  suffices IsUnit (StructureSheaf.toStalk R x f) ↔ f ∉ PrimeSpectrum.asIdeal x by exact this
  erw [← isUnit_map_iff (StructureSheaf.stalkToFiberRingHom R x),
    StructureSheaf.stalkToFiberRingHom_toStalk]
  exact
    (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime (PrimeSpectrum.asIdeal x))
        (PrimeSpectrum.asIdeal x) f :
      _)
#align algebraic_geometry.basic_open_eq_of_affine AlgebraicGeometry.basicOpen_eq_of_affine

@[simp]
theorem basicOpen_eq_of_affine' {R : CommRingCat} (f : Γ(Spec R, ⊤)) :
    (Spec R).basicOpen f = PrimeSpectrum.basicOpen ((Scheme.ΓSpecIso R).hom f) := by
  convert basicOpen_eq_of_affine ((Scheme.ΓSpecIso R).hom f)
  exact (Iso.hom_inv_id_apply (Scheme.ΓSpecIso R) f).symm
#align algebraic_geometry.basic_open_eq_of_affine' AlgebraicGeometry.basicOpen_eq_of_affine'

theorem Scheme.Spec_map_presheaf_map_eqToHom {X : Scheme} {U V : Opens X} (h : U = V) (W) :
    (Spec.map (X.presheaf.map (eqToHom h).op)).app W = eqToHom (by cases h; dsimp; simp) := by
  have : Scheme.Spec.map (X.presheaf.map (𝟙 (op U))).op = 𝟙 _ := by
    rw [X.presheaf.map_id, op_id, Scheme.Spec.map_id]
  cases h
  refine (Scheme.congr_app this _).trans ?_
  simp [eqToHom_map]
#align algebraic_geometry.Scheme.Spec_map_presheaf_map_eqToHom AlgebraicGeometry.Scheme.Spec_map_presheaf_map_eqToHom

end AlgebraicGeometry
