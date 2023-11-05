/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.Algebra.Category.Ring.Constructions

#align_import algebraic_geometry.Scheme from "leanprover-community/mathlib"@"88474d1b5af6d37c2ab728b757771bced7f5194c"

/-!
# The category of schemes

A scheme is a locally ringed space such that every point is contained in some open set
where there is an isomorphism of presheaves between the restriction to that open set,
and the structure sheaf of `Spec R`, for some commutative ring `R`.

A morphism of schemes is just a morphism of the underlying locally ringed spaces.

-/

set_option linter.uppercaseLean3 false
noncomputable section

open TopologicalSpace

open CategoryTheory

open TopCat

open Opposite

namespace AlgebraicGeometry

/-- We define `Scheme` as an `X : LocallyRingedSpace`,
along with a proof that every point has an open neighbourhood `U`
so that that the restriction of `X` to `U` is isomorphic,
as a locally ringed space, to `Spec.toLocallyRingedSpace.obj (op R)`
for some `R : CommRingCat`.
-/
structure Scheme extends LocallyRingedSpace where
  local_affine :
    ∀ x : toLocallyRingedSpace,
      ∃ (U : OpenNhds x) (R : CommRingCat),
        Nonempty
          (toLocallyRingedSpace.restrict U.openEmbedding ≅ Spec.toLocallyRingedSpace.obj (op R))

namespace Scheme

/-- A morphism between schemes is a morphism between the underlying locally ringed spaces. -/
-- @[nolint has_nonempty_instance] -- Porting note: no such linter.
def Hom (X Y : Scheme) : Type* :=
  X.toLocallyRingedSpace ⟶ Y.toLocallyRingedSpace

/-- Schemes are a full subcategory of locally ringed spaces.
-/
instance : Category Scheme :=
  { InducedCategory.category Scheme.toLocallyRingedSpace with Hom := Hom }

-- porting note: added to ease automation
@[continuity]
lemma Hom.continuous {X Y : Scheme} (f : X ⟶ Y) : Continuous f.1.base := f.1.base.2

/-- The structure sheaf of a scheme. -/
protected abbrev sheaf (X : Scheme) :=
  X.toSheafedSpace.sheaf

instance : CoeSort Scheme (Type*) where
  coe X := X.carrier

/-- The forgetful functor from `Scheme` to `LocallyRingedSpace`. -/
@[simps!]
def forgetToLocallyRingedSpace : Scheme ⥤ LocallyRingedSpace :=
  inducedFunctor _
-- deriving Full, Faithful -- Porting note: no delta derive handler, see https://github.com/leanprover-community/mathlib4/issues/5020

instance : Full forgetToLocallyRingedSpace :=
  InducedCategory.full _

instance : Faithful forgetToLocallyRingedSpace :=
  InducedCategory.faithful _

@[simp]
theorem forgetToLocallyRingedSpace_preimage {X Y : Scheme} (f : X ⟶ Y) :
    Scheme.forgetToLocallyRingedSpace.preimage f = f :=
  rfl

/-- The forgetful functor from `Scheme` to `TopCat`. -/
@[simps!]
def forgetToTop : Scheme ⥤ TopCat :=
  Scheme.forgetToLocallyRingedSpace ⋙ LocallyRingedSpace.forgetToTop

-- Porting note : Lean seems not able to find this coercion any more
instance hasCoeToTopCat : CoeOut Scheme TopCat where
  coe X := X.carrier

-- Porting note : added this unification hint just in case
/-- forgetful functor to `TopCat` is the same as coercion -/
unif_hint forgetToTop_obj_eq_coe (X : Scheme) where ⊢
  forgetToTop.obj X ≟ (X : TopCat)

@[simp]
theorem id_val_base (X : Scheme) : (𝟙 X : _).1.base = 𝟙 _ :=
  rfl

@[simp]
theorem id_app {X : Scheme} (U : (Opens X.carrier)ᵒᵖ) :
    (𝟙 X : _).val.c.app U =
      X.presheaf.map (eqToHom (by induction' U with U; cases U; rfl)) :=
  PresheafedSpace.id_c_app X.toPresheafedSpace U

@[reassoc]
theorem comp_val {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).val = f.val ≫ g.val :=
  rfl

@[simp, reassoc] -- reassoc lemma does not need `simp`
theorem comp_coeBase {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).val.base = f.val.base ≫ g.val.base :=
  rfl

-- Porting note: removed elementwise attribute, as generated lemmas were trivial.
@[reassoc]
theorem comp_val_base {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).val.base = f.val.base ≫ g.val.base :=
  rfl

theorem comp_val_base_apply {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).val.base x = g.val.base (f.val.base x) := by
  simp

@[simp, reassoc] -- reassoc lemma does not need `simp`
theorem comp_val_c_app {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
    (f ≫ g).val.c.app U = g.val.c.app U ≫ f.val.c.app _ :=
  rfl

theorem congr_app {X Y : Scheme} {f g : X ⟶ Y} (e : f = g) (U) :
    f.val.c.app U = g.val.c.app U ≫ X.presheaf.map (eqToHom (by subst e; rfl)) := by
  subst e; dsimp; simp

theorem app_eq {X Y : Scheme} (f : X ⟶ Y) {U V : Opens Y.carrier} (e : U = V) :
    f.val.c.app (op U) =
      Y.presheaf.map (eqToHom e.symm).op ≫
        f.val.c.app (op V) ≫
          X.presheaf.map (eqToHom (congr_arg (Opens.map f.val.base).obj e)).op := by
  rw [← IsIso.inv_comp_eq, ← Functor.map_inv, f.val.c.naturality, Presheaf.pushforwardObj_map]
  cases e
  rfl

-- Porting note : in `AffineScheme.lean` file, `eqToHom_op` can't be used in `(e)rw` or `simp(_rw)`
-- when terms get very complicated. See `AlgebraicGeometry.IsAffineOpen.isLocalization_stalk_aux`.
lemma presheaf_map_eqToHom_op (X : Scheme) (U V : Opens X) (i : U = V) :
    X.presheaf.map (eqToHom i).op = eqToHom (i ▸ rfl) := by
  rw [eqToHom_op, eqToHom_map]

instance is_locallyRingedSpace_iso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] :
    @IsIso LocallyRingedSpace _ _ _ f :=
  forgetToLocallyRingedSpace.map_isIso f

-- Porting note: need an extra instance here.
instance {X Y : Scheme} (f : X ⟶ Y) [IsIso f] (U) : IsIso (f.val.c.app U) :=
  haveI := PresheafedSpace.c_isIso_of_iso f.val
  NatIso.isIso_app_of_isIso _ _

@[simp]
theorem inv_val_c_app {X Y : Scheme} (f : X ⟶ Y) [IsIso f] (U : Opens X.carrier) :
    (inv f).val.c.app (op U) =
      X.presheaf.map
          (eqToHom <| by rw [IsIso.hom_inv_id]; ext1; rfl :
              (Opens.map (f ≫ inv f).1.base).obj U ⟶ U).op ≫
        inv (f.val.c.app (op <| (Opens.map _).obj U)) := by
  rw [IsIso.eq_comp_inv]
  erw [← Scheme.comp_val_c_app]
  rw [Scheme.congr_app (IsIso.hom_inv_id f), Scheme.id_app, ← Functor.map_comp, eqToHom_trans,
    eqToHom_op]

/-- Given a morphism of schemes `f : X ⟶ Y`, and open sets `U ⊆ Y`, `V ⊆ f ⁻¹' U`,
this is the induced map `Γ(Y, U) ⟶ Γ(X, V)`. -/
abbrev Hom.appLe {X Y : Scheme} (f : X ⟶ Y) {V : Opens X.carrier} {U : Opens Y.carrier}
    (e : V ≤ (Opens.map f.1.base).obj U) : Y.presheaf.obj (op U) ⟶ X.presheaf.obj (op V) :=
  f.1.c.app (op U) ≫ X.presheaf.map (homOfLE e).op

/-- The spectrum of a commutative ring, as a scheme.
-/
def specObj (R : CommRingCat) : Scheme where
  local_affine _ := ⟨⟨⊤, trivial⟩, R, ⟨(Spec.toLocallyRingedSpace.obj (op R)).restrictTopIso⟩⟩
  toLocallyRingedSpace := Spec.locallyRingedSpaceObj R

@[simp]
theorem specObj_toLocallyRingedSpace (R : CommRingCat) :
    (specObj R).toLocallyRingedSpace = Spec.locallyRingedSpaceObj R :=
  rfl

/-- The induced map of a ring homomorphism on the ring spectra, as a morphism of schemes.
-/
def specMap {R S : CommRingCat} (f : R ⟶ S) : specObj S ⟶ specObj R :=
  (Spec.locallyRingedSpaceMap f : Spec.locallyRingedSpaceObj S ⟶ Spec.locallyRingedSpaceObj R)

@[simp]
theorem specMap_id (R : CommRingCat) : specMap (𝟙 R) = 𝟙 (specObj R) :=
  Spec.locallyRingedSpaceMap_id R

theorem specMap_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T) :
    specMap (f ≫ g) = specMap g ≫ specMap f :=
  Spec.locallyRingedSpaceMap_comp f g

/-- The spectrum, as a contravariant functor from commutative rings to schemes.
-/
-- porting note: removed @[simps]
-- TODO: We need to decide whether `Spec_obj` or `Spec.obj` the simp-normal form.
-- We probably want `Spec.obj`, but note
-- `locallyRingedSpaceObj` is currently the simp-normal form of `toLocallyRingedSpace.obj`.
def Spec : CommRingCatᵒᵖ ⥤ Scheme where
  obj R := specObj (unop R)
  map f := specMap f.unop
  map_id R := by simp
  map_comp f g := by simp [specMap_comp]

/-- The empty scheme.
-/
@[simps]
def empty.{u} : Scheme.{u} where
  carrier := TopCat.of PEmpty
  presheaf := (CategoryTheory.Functor.const _).obj (CommRingCat.of PUnit)
  IsSheaf := Presheaf.isSheaf_of_isTerminal _ CommRingCat.punitIsTerminal
  localRing x := PEmpty.elim x
  local_affine x := PEmpty.elim x

instance : EmptyCollection Scheme :=
  ⟨empty⟩

instance : Inhabited Scheme :=
  ⟨∅⟩

/-- The global sections, notated Gamma.
-/
def Γ : Schemeᵒᵖ ⥤ CommRingCat :=
  (inducedFunctor Scheme.toLocallyRingedSpace).op ⋙ LocallyRingedSpace.Γ

theorem Γ_def : Γ = (inducedFunctor Scheme.toLocallyRingedSpace).op ⋙ LocallyRingedSpace.Γ :=
  rfl

@[simp]
theorem Γ_obj (X : Schemeᵒᵖ) : Γ.obj X = (unop X).presheaf.obj (op ⊤) :=
  rfl

theorem Γ_obj_op (X : Scheme) : Γ.obj (op X) = X.presheaf.obj (op ⊤) :=
  rfl

@[simp]
theorem Γ_map {X Y : Schemeᵒᵖ} (f : X ⟶ Y) : Γ.map f = f.unop.1.c.app (op ⊤) :=
  rfl

theorem Γ_map_op {X Y : Scheme} (f : X ⟶ Y) : Γ.map f.op = f.1.c.app (op ⊤) :=
  rfl

section BasicOpen

variable (X : Scheme) {V U : Opens X.carrier} (f g : X.presheaf.obj (op U))

/-- The subset of the underlying space where the given section does not vanish. -/
def basicOpen : Opens X.carrier :=
  X.toLocallyRingedSpace.toRingedSpace.basicOpen f

@[simp]
theorem mem_basicOpen (x : U) : ↑x ∈ X.basicOpen f ↔ IsUnit (X.presheaf.germ x f) :=
  RingedSpace.mem_basicOpen _ _ _

@[aesop norm simp (rule_sets [Restrict])]
theorem mem_basicOpen_top' {U : Opens X} (f : X.presheaf.obj (op U)) (x : X.carrier) :
    x ∈ X.basicOpen f ↔ ∃ (m : x ∈ U), IsUnit (X.presheaf.germ (⟨x, m⟩ : U) f) := by
  fconstructor
  · rintro ⟨y, hy1, rfl⟩
    exact ⟨y.2, hy1⟩
  · rintro ⟨m, hm⟩
    exact ⟨⟨x, m⟩, hm, rfl⟩

@[simp]
theorem mem_basicOpen_top (f : X.presheaf.obj (op ⊤)) (x : X.carrier) :
    x ∈ X.basicOpen f ↔ IsUnit (X.presheaf.germ (⟨x, trivial⟩ : (⊤ : Opens _)) f) :=
  RingedSpace.mem_basicOpen _ f ⟨x, trivial⟩

@[simp]
theorem basicOpen_res (i : op U ⟶ op V) : X.basicOpen (X.presheaf.map i f) = V ⊓ X.basicOpen f :=
  RingedSpace.basicOpen_res _ i f

-- This should fire before `basicOpen_res`.
@[simp 1100]
theorem basicOpen_res_eq (i : op U ⟶ op V) [IsIso i] :
    X.basicOpen (X.presheaf.map i f) = X.basicOpen f :=
  RingedSpace.basicOpen_res_eq _ i f

@[sheaf_restrict]
theorem basicOpen_le : X.basicOpen f ≤ U :=
  RingedSpace.basicOpen_le _ _

@[simp]
theorem preimage_basicOpen {X Y : Scheme} (f : X ⟶ Y) {U : Opens Y.carrier}
    (r : Y.presheaf.obj <| op U) :
    (Opens.map f.1.base).obj (Y.basicOpen r) =
      @Scheme.basicOpen X ((Opens.map f.1.base).obj U) (f.1.c.app _ r) :=
  LocallyRingedSpace.preimage_basicOpen f r

@[simp]
theorem basicOpen_zero (U : Opens X.carrier) : X.basicOpen (0 : X.presheaf.obj <| op U) = ⊥ :=
  LocallyRingedSpace.basicOpen_zero _ U

@[simp]
theorem basicOpen_mul : X.basicOpen (f * g) = X.basicOpen f ⊓ X.basicOpen g :=
  RingedSpace.basicOpen_mul _ _ _

theorem basicOpen_of_isUnit {f : X.presheaf.obj (op U)} (hf : IsUnit f) : X.basicOpen f = U :=
  RingedSpace.basicOpen_of_isUnit _ hf

end BasicOpen

end Scheme

theorem basicOpen_eq_of_affine {R : CommRingCat} (f : R) :
    (Scheme.Spec.obj <| op R).basicOpen ((SpecΓIdentity.app R).inv f) =
      PrimeSpectrum.basicOpen f := by
  ext x
  erw [Scheme.mem_basicOpen_top]
  suffices IsUnit (StructureSheaf.toStalk R x f) ↔ f ∉ PrimeSpectrum.asIdeal x by exact this
  erw [← isUnit_map_iff (StructureSheaf.stalkToFiberRingHom R x),
    StructureSheaf.stalkToFiberRingHom_toStalk]
  exact
    (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime (PrimeSpectrum.asIdeal x))
        (PrimeSpectrum.asIdeal x) f :
      _)

@[simp]
theorem basicOpen_eq_of_affine' {R : CommRingCat}
    (f : (Spec.toSheafedSpace.obj (op R)).presheaf.obj (op ⊤)) :
    (Scheme.Spec.obj <| op R).basicOpen f =
      PrimeSpectrum.basicOpen ((SpecΓIdentity.app R).hom f) := by
  convert basicOpen_eq_of_affine ((SpecΓIdentity.app R).hom f)
  exact (Iso.hom_inv_id_apply (SpecΓIdentity.app R) f).symm

end AlgebraicGeometry
