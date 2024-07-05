/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Group
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Gluing

/-!
-/

universe u

section algebra_schemeOver
-- TODO: move these

variable (R A A') [CommRing R] [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']

open CategoryTheory Opposite AlgebraicGeometry

/-- -/
def Algebra.mkOver : Over (op <| CommRingCat.of R) :=
  .mk (op <| CommRingCat.ofHom <| algebraMap R A)

/-- -/
def AlgHom.equivHomOver : (A →ₐ[R] A') ≃ (Algebra.mkOver R A' ⟶ Algebra.mkOver R A) where
  toFun f := Over.homMk (op f.toRingHom) (unop_injective f.comp_algebraMap)
  invFun f := .mk f.left.unop fun r ↦ congr(Quiver.Hom.unop $(Over.w f) r)
  left_inv f := by ext1; simp
  right_inv f := by simp; rfl

variable {C D} [Category C] [Category D] (F : C ⥤ D)
/-- -/
@[simps!] def CategoryTheory.Functor.mapOver (c : C) : Over c ⥤ Over (F.obj c) :=
  Comma.map (F₁ := F) (F₂ := 𝟭 _) (F := F) (𝟙 _) { app := fun _ ↦ 𝟙 _ }

@[simp] lemma CategoryTheory.Functor.mapOver_hom (c : C) (c' : Over c) :
    ((F.mapOver c).obj c').hom = F.map c'.hom := by simp

/-- -/
noncomputable def Algebra.schemeSpecOver : Over (Scheme.Spec.obj <| op <| CommRingCat.of R) :=
  (Scheme.Spec.mapOver _).obj (Algebra.mkOver R A)

variable {F} in
/-- -/
def CategoryTheory.Functor.FullyFaithful.mapOver (ff : F.FullyFaithful) (c : C) :
    (F.mapOver c).FullyFaithful where
  preimage f := Over.homMk (ff.preimage f.left) (ff.map_injective <| by simpa using Over.w f)

/-- -/
noncomputable def AlgHom.equivSchemeOver :
    (A →ₐ[R] A') ≃ (Algebra.schemeSpecOver R A' ⟶ Algebra.schemeSpecOver R A) :=
  (AlgHom.equivHomOver R A A').trans (Spec.fullyFaithful.mapOver _).homEquiv

end algebra_schemeOver

inductive PBool : Type u | false | true

namespace CategoryTheory

variable {C : Type*} [Category C]

open Limits
attribute [local instance] hasPullback_of_left_iso hasPullback_of_right_iso

-- should we generalize J to arbitrary universe? and pullback to arbitrary IsPullback?
-- TODO: the name CategoryTheory.Limits.pullback_snd_iso_of_right_iso is wrong (should be fst)

@[reassoc, simp]
lemma pullback_snd_comp_inv_fst {c₁ c₂ c : C} {f₁ : c₁ ⟶ c} {f₂ : c₂ ⟶ c} [IsIso f₁] :
    pullback.snd ≫ inv pullback.fst = (pullbackSymmetry f₁ f₂).hom := by
  rw [IsIso.comp_inv_eq, pullbackSymmetry_hom_comp_fst]

suppress_compilation

/-- Construct a glue datum from a two monomorphisms with the same source. -/
@[simps] def GlueData.mk₂ {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂) [Mono f₁] [Mono f₂] :
    GlueData C where
  J := PBool
  U := PBool.rec U₁ U₂
  V b := b.1.rec (b.2.rec U₁ V) (b.2.rec V U₂)
  f := PBool.rec (PBool.rec (𝟙 U₁) f₁) (PBool.rec f₂ (𝟙 U₂))
  f_mono := by rintro ⟨_⟩ ⟨_⟩ <;> infer_instance
  f_hasPullback := by rintro ⟨_⟩ ⟨_⟩ ⟨_⟩ <;> dsimp only <;> infer_instance
  f_id := by rintro ⟨_⟩ <;> infer_instance
  t := PBool.rec (PBool.rec (𝟙 U₁) (𝟙 V)) (PBool.rec (𝟙 V) (𝟙 U₂))
  t_id := by rintro ⟨_⟩ <;> rfl
  t' := PBool.rec (PBool.rec (PBool.rec (𝟙 _) <| pullback.snd ≫ inv pullback.fst) <| PBool.rec
      (pullback.fst ≫ inv (pullback.fst (f := f₂))) <| pullback.fst (f := f₁) ≫ inv pullback.snd)
    (PBool.rec (PBool.rec (pullback.fst (f := f₂) ≫ inv pullback.snd) <| pullback.fst ≫
      inv (pullback.fst (f := f₁))) <| PBool.rec (pullback.snd ≫ inv pullback.fst) <| 𝟙 _)
    -- two out of eight can use pullbackSymmetry but this is easier for cocycle
  t_fac := by rintro ⟨_⟩ ⟨_⟩ ⟨_⟩ <;> simp [fst_eq_snd_of_mono_eq]
  cocycle := by rintro ⟨_⟩ ⟨_⟩ ⟨_⟩ <;>
    simp only [Category.assoc, IsIso.inv_hom_id_assoc, IsIso.hom_inv_id, Category.comp_id]

end CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Construct a glue datum from two open immersions with the same source. -/
@[simps!] noncomputable def GlueData.mk₂ {U₁ U₂ V : Scheme} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    [IsOpenImmersion f₁] [IsOpenImmersion f₂] : GlueData where
  __ := CategoryTheory.GlueData.mk₂ f₁ f₂
  f_open := by rintro ⟨_⟩ ⟨_⟩ <;> dsimp only [CategoryTheory.GlueData.mk₂_f] <;> infer_instance

end AlgebraicGeometry.Scheme

/-! ### The coordinate ring at infinity -/

namespace WeierstrassCurve.Projective

noncomputable section

open Polynomial AlgebraicGeometry

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The equation of the Weierstrass curve at infinity. -/
def polynomialInf : R[X][Y] :=
  letI x : R[X][Y] := C X;
  -x ^ 3 + Y * (1 + CC W.a₁ * x - CC W.a₂ * x ^ 2 + CC W.a₃ * Y - CC W.a₄ * x * Y - CC W.a₆ * Y ^ 2)

def polynomialZ : R[X][Y] :=
  1 + C (C W.a₁ * X - C W.a₂ * X ^ 2) + 2 * C (C W.a₃ - C W.a₄ * X) * Y - 3 * CC W.a₆ * Y ^ 2

lemma eval₂_polynomialInf {S} [CommRing S] [Algebra R S] (f : R[X] →ₐ[R] S)
    (x y z : S) (hx : x * z = f X) (hy : y * z = 1) :
    eval₂ f z (polynomialInf W) = z ^ 3 * aevalAEval x y (Affine.polynomial W) := by
  rw [← coe_eval₂RingHom]
  simp only [polynomialInf, map_add, map_neg, map_pow, coe_eval₂RingHom, eval₂_C, RingHom.coe_coe,
    map_mul, eval₂_X, map_sub, map_one, Affine.polynomial, aevalAEval_apply, aeval_C, aeval_X]
  conv in _ * z => rw [← one_mul z]
  conv in 1 + _ => rw [← one_pow 2]
  conv in _ * f X => rw [← one_mul (f X)]
  rw [← hx, ← hy]
  simp_rw [C_eq_algebraMap, AlgHom.commutes]
  ring

lemma eval₂_affine_polynomial {S} [CommRing S] [Algebra R S] (f : R[X] →ₐ[R] S)
    (x y z : S) (hx : x * y = f X) (hy : y * z = 1) :
    eval₂ f y (Affine.polynomial W) = y ^ 3 * aevalAEval x z (polynomialInf W) := by
  rw [← coe_eval₂RingHom]
  simp only [polynomialInf, map_add, map_neg, map_pow, coe_eval₂RingHom, eval₂_C, RingHom.coe_coe,
    map_mul, eval₂_X, map_sub, map_one, Affine.polynomial, aevalAEval_apply, aeval_C, aeval_X]
  conv in y ^ 2 => rw [← one_mul (y ^ 2), ← one_pow 2]
  rw [← one_mul (f <| C W.a₂)]
  conv in _ * y => rw [← one_mul y, ← one_mul (f <| C W.a₃)]
  conv in f (C W.a₄) => rw [← one_mul (f <| C W.a₄), ← one_pow 2]
  conv in f (C W.a₆) => rw [← one_mul (f <| C W.a₆), ← one_pow 3]
  rw [← hx, ← hy]
  simp only [C_eq_algebraMap, AlgHom.commutes]
  ring

/-- The coordinate ring at infinity. -/
abbrev CoordinateRingInf : Type u := AdjoinRoot (polynomialInf W)

/-- -/
abbrev CoordinateRingInf.mk : R[X][Y] →+* CoordinateRingInf W := AdjoinRoot.mk _

/-- The coordinate ring localized at Y. -/
abbrev LocalizationY : Type u := Localization.Away (Affine.CoordinateRing.mk W Y)

/-- The coordinate ring at infinity localized at Z. -/
abbrev LocalizationZ : Type u := Localization.Away (CoordinateRingInf.mk W Y)

/-- The R-algebra homomorphism from `CoordinateRingInf W` to `LocalizationY W`. -/
def coordinateRingInfToLoc : CoordinateRingInf W →ₐ[R] LocalizationY W where
  __ := AdjoinRoot.lift
      (aeval <| .mk (.mk W <| Polynomial.C X) ⟨_, 1, rfl⟩).toRingHom (.mk 1 ⟨_, 1, rfl⟩) <| by
    let f := IsScalarTower.toAlgHom R (Affine.CoordinateRing W) (LocalizationY W)
    rw [AlgHom.toRingHom_eq_coe, eval₂_polynomialInf _ _ (f <| .mk W <| C X) (f <| .mk W Y)]
    · rw [aevalAEval_algHom, AdjoinRoot.aevalAEval_X_Y, map_zero, mul_zero]
    · erw [← Algebra.smul_def, Localization.smul_mk, smul_eq_mul, mul_one, aeval_X]
    · erw [← Algebra.smul_def, Localization.smul_mk, smul_eq_mul, mul_one]
      simp_rw [pow_one]; exact Localization.mk_self ⟨_, _⟩
  commutes' r := (AdjoinRoot.lift_of _).trans (aeval_C _ _)

/-- The R-algebra homomorphism from `Affine.CoordinateRing W` to `LocalizationZ W`. -/
def coordinateRingToLoc : Affine.CoordinateRing W →ₐ[R] LocalizationZ W where
  __ := AdjoinRoot.lift
      (aeval <| .mk (.mk W <| Polynomial.C X) ⟨_, 1, rfl⟩).toRingHom (.mk 1 ⟨_, 1, rfl⟩) <| by
    let f := IsScalarTower.toAlgHom R (CoordinateRingInf W) (LocalizationZ W)
    rw [AlgHom.toRingHom_eq_coe, eval₂_affine_polynomial _ _ (f <| .mk W <| C X) _ (f <| .mk W Y)]
    · rw [aevalAEval_algHom, AdjoinRoot.aevalAEval_X_Y, map_zero, mul_zero]
    · erw [← Algebra.smul_def, Localization.smul_mk, smul_eq_mul, mul_one, aeval_X]
    · erw [mul_comm, ← Algebra.smul_def, Localization.smul_mk, smul_eq_mul, mul_one]
      simp_rw [pow_one]; exact Localization.mk_self ⟨_, _⟩
  commutes' r := (AdjoinRoot.lift_of _).trans (aeval_C _ _)

lemma coordinateRingToLoc_Y : coordinateRingToLoc W (.mk W Y) = .mk 1 ⟨_, 1, rfl⟩ := by
  rw [coordinateRingToLoc, AlgHom.coe_mk]
  exact (AdjoinRoot.lift_mk _ _).trans (eval₂_X _ _)

lemma coordinateRingToLoc_Z : coordinateRingInfToLoc W (.mk W Y) = .mk 1 ⟨_, 1, rfl⟩ := by
  rw [coordinateRingInfToLoc, AlgHom.coe_mk]
  exact (AdjoinRoot.lift_mk _ _).trans (eval₂_X _ _)

def locRingEquiv : LocalizationZ W ≃+* LocalizationY W :=
  .ofHomInv (Localization.awayLift (coordinateRingInfToLoc W) _ <|
      by erw [coordinateRingToLoc_Z]; apply Localization.isUnit_mk_one)
    (Localization.awayLift (coordinateRingToLoc W) _ <|
      by erw [coordinateRingInfToLoc_Y]; apply Localization.isUnit_mk_one)
    (IsLocalization.ringHom_ext (.powers <| CoordinateRingInf.mk W Y) <| by sorry)
    (IsLocalization.ringHom_ext (.powers <| Affine.CoordinateRing.mk W Y) <| by sorry)
    -- need a version of AdjoinRoot.algHom_ext that takes an R-AlgHom rather than R[X]-AlgHom

instance : Algebra (CoordinateRingInf W) (LocalizationY W) := (coordinateRingInfToLoc W).toAlgebra

def locAlgEquiv : LocalizationZ W ≃ₐ[CoordinateRingInf W] LocalizationY W where
  __ := locRingEquiv W
  commutes' := IsLocalization.Away.AwayMap.lift_eq _ _

instance : IsLocalization.Away (CoordinateRingInf.mk W Y) (LocalizationY W) :=
  IsLocalization.isLocalization_of_algEquiv (.powers <| CoordinateRingInf.mk W Y) (locAlgEquiv W)

open CategoryTheory in
lemma _root_.AlgebraicGeometry.IsOpenImmersion.of_isLocalization {R S} [CommRing R] [CommRing S]
    [Algebra R S] (f : R) [IsLocalization.Away f S] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  sorry -- https://github.com/leanprover-community/mathlib4/pull/14428/files#r1666189028

instance : IsOpenImmersion <| Spec.map <| CommRingCat.ofHom <|
    algebraMap (Affine.CoordinateRing W) (LocalizationY W) :=
  .of_isLocalization (Affine.CoordinateRing.mk W Y)

instance : IsOpenImmersion <| Spec.map <| CommRingCat.ofHom <|
    algebraMap (CoordinateRingInf W) (LocalizationY W) :=
  .of_isLocalization (CoordinateRingInf.mk W Y)

/-- Glue data for the projective Weierstrass curve. -/
def glueData : Scheme.GlueData := .mk₂
  (Spec.map <| CommRingCat.ofHom <| algebraMap (Affine.CoordinateRing W) <| LocalizationY W)
  (Spec.map <| CommRingCat.ofHom <| algebraMap (CoordinateRingInf W) <| LocalizationY W)

/-- The projective Weierstrass curve as a scheme. -/
def scheme : Scheme := (glueData W).glued

/-- The open cover by two affine opens of a projective Weierstrass curve. -/
def openCover : (scheme W).OpenCover := (glueData W).openCover

/-- The structure morphism of a projective Weierstrass curve. -/
def schemeToBase : scheme W ⟶ Spec ⟨R, inferInstance⟩ :=
  --(openCover W).glueMorphisms (PBool.rec _ _) _
  sorry -- is it easier to use AlgebraicGeometry.ΓSpec.adjunction directly?

-- def : Over (Spec ⟨R, inferInstance⟩) := ...
-- TODO: define the negation morphism on `scheme W` and `smoothLocus W`.

/-- The smooth locus of a projective Weierstrass curve. -/
def smoothLocus : TopologicalSpace.Opens (scheme W) where
  carrier := ((glueData W).ι .false).val.base ''
    ((PrimeSpectrum.basicOpen <| .mk W <| Affine.polynomialX W).1 ∪
      (PrimeSpectrum.basicOpen <| .mk W <| Affine.polynomialY W).1) ∪
    ((glueData W).ι .true).val.base '' (PrimeSpectrum.basicOpen <| .mk W <| polynomialZ W).1
  is_open' := by
    apply IsOpen.union <;> apply PresheafedSpace.IsOpenImmersion.base_open.isOpenMap
    on_goal 1 => apply IsOpen.union
    all_goals apply TopologicalSpace.Opens.is_open'

-- TODO: show this scheme is projective (in particular separated) over R,
-- and is integral if R is integral

-- TODO: produce AlgebraicGeometry.Scheme.AffineOpenCover for `scheme W`, `smoothLocus W`
--  and their fiber product with themselves over `R`.

-- define abbrevs X₁, X₂, Y₁, Y₂ as elements in `Affine.CoordinateRing W ⊗[R] Affine.CoordinateRing W` etc.

/- AlgebraicGeometry.Scheme.Pullback.gluing -/

-- TODO: define the notion of a group scheme G over a base scheme S.
-- (Do we want to use Adam Topaz's approach to define it as a "group object" in the category of schemes?)
-- Show that for a scheme T over S, G_S(T) (morphisms from T/S to G/S in the over category) is a group.

-- TODO: Show `smoothLocus W` is a group scheme over `Spec R`.
-- In fact, this extends to a group scheme action of `smoothLocus W` on `scheme W`.
-- Show if T is Spec of a field, we recover `WeierstrassCurve.Affine.Point W` and the group laws agree.

end

end WeierstrassCurve.Projective
