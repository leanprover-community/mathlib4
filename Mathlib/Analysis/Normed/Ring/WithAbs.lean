/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Analysis.Normed.Ring.TransferInstance

/-!
# `WithAbs` type synonym

`WithAbs v` is a copy of the semiring `R` with the same underlying ring structure, but assigned
`v`-dependent instances (such as `NormedRing`) where `v` is an absolute value on `R`.

## Main definitions
- `WithAbs` : type synonym for a semiring which depends on an absolute value. This is
  a function that takes an absolute value on a semiring and returns the semiring. This can be used
  to assign and infer instances on a semiring that depend on absolute values.
- `WithAbs.equivAux v` : the canonical (type) equivalence between `WithAbs v` and `R`.
- `WithAbs.equiv v` : The canonical ring equivalence between `WithAbs v` and `R`.
-/

@[expose] public section

open Topology

variable {R : Type*} {S : Type*} [Semiring S] [PartialOrder S]

/-- Type synonym for a semiring which depends on an absolute value. This is a function that takes
an absolute value on a semiring and returns the semiring. We use this to assign and infer instances
on a semiring that depend on absolute values.

This is also helpful when dealing with several absolute values on the same semiring. -/
structure WithAbs [Semiring R] (v : AbsoluteValue R S) where
  /-- Converts an element of `R` to an element of `WithAbs v`. -/
  toAbs (v) ::
  /-- Converts an element of `WithAbs v` to an element of `R`. -/
  ofAbs : R

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `toAbs p x` being printed as `{ ofAbs := x }` by `delabStructureInstance`. -/
@[app_delab WithAbs.toAbs]
meta def WithAbs.delabToAbs : Delab := delabApp

end Notation

namespace WithAbs

section semiring

variable [Semiring R] (v : AbsoluteValue R S)

lemma ofAbs_toAbs (x : R) : ofAbs (toAbs v x) = x := rfl
@[simp] lemma toAbs_ofAbs (x : WithAbs v) : toAbs v (ofAbs x) = x := rfl

lemma ofAbs_surjective : Function.Surjective (ofAbs (v := v)) :=
  Function.RightInverse.surjective <| ofAbs_toAbs _

lemma toAbs_surjective : Function.Surjective (toAbs v) :=
  Function.RightInverse.surjective <| toAbs_ofAbs _

lemma ofAbs_injective : Function.Injective (ofAbs (v := v)) :=
  Function.LeftInverse.injective <| toAbs_ofAbs _

lemma toAbs_injective : Function.Injective (toAbs v) :=
  Function.LeftInverse.injective <| ofAbs_toAbs _

lemma ofAbs_bijective : Function.Bijective (ofAbs (v := v)) :=
  ⟨ofAbs_injective v, ofAbs_surjective v⟩

lemma toAbs_bijective : Function.Bijective (toAbs v) :=
  ⟨toAbs_injective v, toAbs_surjective v⟩

/-- The canonical (type) equivalence between `WithAbs v` and `R`. See `WithAbs.equiv` for
the semiring equivalence. -/
def equivAux : WithAbs v ≃ R where
  toFun := ofAbs
  invFun := toAbs v
  left_inv _ := rfl
  right_inv _ := rfl

instance instNontrivial [Nontrivial R] : Nontrivial (WithAbs v) := (equivAux v).nontrivial
instance instUnique [Unique R] : Unique (WithAbs v) := (equivAux v).unique
instance instSemiring : Semiring (WithAbs v) := (equivAux v).semiring
instance instInhabited : Inhabited (WithAbs v) := ⟨0⟩

@[simp] lemma toAbs_zero : toAbs v (0 : R) = 0 := rfl
@[simp] lemma ofAbs_zero : ofAbs (0 : WithAbs v) = 0 := rfl

@[simp] lemma toAbs_one : toAbs v (1 : R) = 1 := rfl
@[simp] lemma ofAbs_one : ofAbs (1 : WithAbs v) = 1 := rfl

@[simp] lemma toAbs_add (x y : R) : toAbs v (x + y) = toAbs v x + toAbs v y := rfl
@[simp] lemma ofAbs_add (x y : WithAbs v) : ofAbs (x + y) = ofAbs x + ofAbs y := rfl

@[simp] lemma toAbs_eq_zero {x : R} : toAbs v x = 0 ↔ x = 0 := (toAbs_injective v).eq_iff
@[simp] lemma ofAbs_eq_zero {x : WithAbs v} : ofAbs x = 0 ↔ x = 0 := (ofAbs_injective v).eq_iff

@[simp] lemma toAbs_pow (x : R) (n : ℕ) : toAbs v (x ^ n) = toAbs v x ^ n := rfl
@[simp] lemma ofAbs_pow (x : WithAbs v) (n : ℕ) : ofAbs (x ^ n) = ofAbs x ^ n := rfl

/-- The canonical (semiring) equivalence between `WithAbs v` and `R`. -/
@[simps apply symm_apply]
def equiv : WithAbs v ≃+* R where
  toFun := ofAbs
  invFun := toAbs v
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

variable {T : Type*} [Semiring T] (w : AbsoluteValue T S)

/-- Lift a ring hom to `WithAbs`. -/
def map (f : R →+* T) : WithAbs v →+* WithAbs w :=
  (equiv w).symm.toRingHom.comp (f.comp (equiv v).toRingHom)

@[simp]
theorem map_id : WithAbs.map v v (RingHom.id R) = RingHom.id (WithAbs v) := rfl

theorem map_comp {U : Type*} [Semiring U] (u : AbsoluteValue U S) (f : T →+* U)
    (g : R →+* T) : map v u (f.comp g) = (map w u f).comp (map v w g) :=
  rfl

/-- Lift a `RingEquiv` to `WithAbs`. -/
def congr (f : R ≃+* T) : WithAbs v ≃+* WithAbs w where
  __ := (WithAbs.map v w f.toRingHom)
  invFun := (WithAbs.map w v f.symm.toRingHom)
  left_inv x := by simp [← RingHom.comp_apply, ← map_comp]
  right_inv x := by simp [← RingHom.comp_apply, ← map_comp]

@[simp]
theorem congr_refl : congr v v (RingEquiv.refl R) = RingEquiv.refl (WithAbs v) :=
  rfl

theorem congr_trans {U : Type*} [Semiring U] (u : AbsoluteValue U S)
    (f : T ≃+* U) (g : R ≃+* T) :
    congr v u (g.trans f) = (congr v w g).trans (congr w u f) :=
  rfl

theorem congr_symm (f : R ≃+* T) : (congr v w f).symm = congr w v f.symm := rfl

@[simp]
theorem ofAbs_congr_apply {x : WithAbs v} (f : R ≃+* T) :
    (congr v w f x).ofAbs = f x.ofAbs := rfl

@[simp]
theorem congr_toAbs_apply {x : R} (f : R ≃+* T) :
    congr v w f (toAbs v x) = toAbs w (f x) := rfl

@[simp]
theorem congr_symm_toAbs_apply {x : T} (f : R ≃+* T) :
    (congr v w f).symm (toAbs w x) = toAbs v (f.symm x) := rfl

/-- The canonical (semiring) equivalence between `WithAbs v` and `WithAbs w`, for any two
absolute values `v` and `w` on `R`. -/
@[deprecated "Use `WithAbs.congr` instead." (since := "2026-01-23")]
def equivWithAbs (v w : AbsoluteValue R S) : WithAbs v ≃+* WithAbs w :=
    congr v w (.refl R)

@[deprecated "Use `WithAbs.congr_symm` instead." (since := "2026-01-23")]
theorem equivWithAbs_symm (v w : AbsoluteValue R S) :
    (congr v w (.refl R)).symm = (congr w v (RingEquiv.refl R).symm) :=
  congr_symm _ _ _

@[deprecated "Use `WithAbs.ofAbs_congr_apply` instead." (since := "2026-01-23")]
theorem equiv_equivWithAbs_symm_apply {v w : AbsoluteValue R S} {x : WithAbs w} :
    equiv v ((congr v w (.refl R)).symm x) = equiv w x := ofAbs_congr_apply v w (.refl R)

@[deprecated "Use `WithAbs.congr_toAbs_apply` instead." (since := "2026-01-23")]
theorem equivWithAbs_equiv_symm_apply {v w : AbsoluteValue R S} {x : R} :
    congr v w (.refl R) ((equiv v).symm x) = (equiv w).symm x := congr_toAbs_apply _ _ _

@[deprecated "Use `WithAbs.congr_symm_toAbs_apply` instead." (since := "2026-01-23")]
theorem equivWithAbs_symm_equiv_symm_apply {v w : AbsoluteValue R S} {x : R} :
    (congr v w (.refl R)).symm ((equiv w).symm x) = (equiv v).symm x :=
  congr_symm_toAbs_apply _ _ _

end semiring

section comm_semiring

variable [CommSemiring R] (v : AbsoluteValue R S)

instance instCommSemiring : CommSemiring (WithAbs v) := (equiv v).commSemiring

end comm_semiring

section ring

variable [Ring R]

instance instRing (v : AbsoluteValue R S) : Ring (WithAbs v) := (equiv v).ring

noncomputable instance normedRing (v : AbsoluteValue R ℝ) : NormedRing (WithAbs v) :=
  letI := v.toNormedRing
  (equiv v).normedRing

lemma norm_eq_abv (v : AbsoluteValue R ℝ) (x : WithAbs v) :
    ‖x‖ = v (WithAbs.equiv v x) := rfl

lemma norm_eq_abv' (v : AbsoluteValue R ℝ) (x : R) :
    ‖(WithAbs.equiv v).symm x‖ = v x := rfl

variable (v : AbsoluteValue R S)

@[simp] lemma toAbs_sub (x y : R) : toAbs v (x - y) = toAbs v x - toAbs v y := rfl
@[simp] lemma ofAbs_sub (x y : WithAbs v) : ofAbs (x - y) = ofAbs x - ofAbs y := rfl

@[simp] lemma toAbs_neg (x : R) : toAbs v (-x) = - toAbs v x := rfl
@[simp] lemma ofAbs_neg (x : WithAbs v) : ofAbs (-x) = - ofAbs x := rfl

end ring

section comm_ring

variable [CommRing R] (v : AbsoluteValue R S)

instance instCommRing : CommRing (WithAbs v) := (equiv v).commRing

end comm_ring

section Module

variable {R T : Type*} [Semiring R] [Semiring T] [Module R T]

instance instModule_left (v : AbsoluteValue R S) : Module (WithAbs v) T :=
  .compHom T (equiv v).toRingHom

instance instModule_right (v : AbsoluteValue T S) : Module R (WithAbs v) := (equiv v).module R

variable (v : AbsoluteValue T S)

@[simp] lemma toAbs_smul (r : R) (t : T) : toAbs v (r • t) = r • toAbs v t := rfl
@[simp] lemma ofAbs_smul (r : R) (x : WithAbs v) : ofAbs (r • x) = r • ofAbs x := rfl

end Module

section algebra

variable {R T : Type*} [CommSemiring R] [Semiring T] [Algebra R T]

instance instAlgebra_left (v : AbsoluteValue R S) : Algebra (WithAbs v) T :=
  .compHom T (equiv v).toRingHom

theorem algebraMap_left_apply {v : AbsoluteValue R S} (x : WithAbs v) :
    algebraMap (WithAbs v) T x = algebraMap R T x.ofAbs := rfl

instance instAlgebra_right (v : AbsoluteValue T S) : Algebra R (WithAbs v) := (equiv v).algebra R

theorem algebraMap_right_apply {v : AbsoluteValue T S} (x : R) :
    algebraMap R (WithAbs v) x = toAbs v (algebraMap R T x):= rfl

theorem algebraMap_apply_ofAbs (v : AbsoluteValue R S) (w : AbsoluteValue T S) (x : WithAbs v) :
    (algebraMap (WithAbs v) (WithAbs w) x).ofAbs = algebraMap R T x.ofAbs := rfl

/-- The canonical algebra isomorphism from an `R`-algebra `R'` with an absolute value `v`
to `R'`. -/
def algEquiv (v : AbsoluteValue T S) : (WithAbs v) ≃ₐ[R] T := (equiv v).algEquiv R

end algebra

section is_scalar_tower

variable {R T : Type*} [CommSemiring R] [Semiring T]

instance instIsScalarTower [Module R T] (v : AbsoluteValue R S) : IsScalarTower R (WithAbs v) T :=
  .of_compHom R (WithAbs v) T

instance instIsScalarTowerLeft [Module R T] (v : AbsoluteValue R S) :
    IsScalarTower (WithAbs v) R T := .of_compHom (WithAbs v) R T

instance instIsScalarTowerRight [Algebra R T] (v : AbsoluteValue T S) :
    IsScalarTower R T (WithAbs v) := (equiv v).isScalarTower R T

end is_scalar_tower

end WithAbs

namespace AbsoluteValue

variable {K L S : Type*} [CommRing K] [IsSimpleRing K] [CommRing L] [Algebra K L] [PartialOrder S]
  [Nontrivial L] [Semiring S] (w : AbsoluteValue L S) (v : AbsoluteValue K S)

/-- An absolute value `w` of `L / K` lies over the absolute value `v` of `K` if `v` is the
restriction of `w` to `K`. -/
class LiesOver : Prop where
  comp_eq' : w.comp (algebraMap K L).injective = v

variable [w.LiesOver v]

theorem LiesOver.comp_eq : w.comp (algebraMap K L).injective = v := LiesOver.comp_eq'

end AbsoluteValue
