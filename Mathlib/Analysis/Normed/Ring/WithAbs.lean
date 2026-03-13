/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Analysis.Normed.Ring.TransferInstance
public import Mathlib.Topology.Algebra.Ring.Basic

/-!
# `WithAbs` type synonym

`WithAbs v` is a copy of the semiring `R` with the same underlying ring structure, but assigned
`v`-dependent instances (such as `NormedRing`) where `v` is an absolute value on `R`.

## Main definitions
- `WithAbs` : type synonym for a semiring which depends on an absolute value. This is
  a function that takes an absolute value on a semiring and returns the semiring. This can be used
  to assign and infer instances on a semiring that depend on absolute values.
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

section Semiring

variable [Semiring R] (v : AbsoluteValue R S)

instance : Semiring (WithAbs v) := Equiv.semiring { toFun := ofAbs, invFun := toAbs v }

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

@[simp] lemma toAbs_zero : toAbs v (0 : R) = 0 := rfl
@[simp] lemma ofAbs_zero : ofAbs (0 : WithAbs v) = 0 := rfl

@[simp] lemma toAbs_one : toAbs v (1 : R) = 1 := rfl
@[simp] lemma ofAbs_one : ofAbs (1 : WithAbs v) = 1 := rfl

@[simp] lemma toAbs_add (x y : R) : toAbs v (x + y) = toAbs v x + toAbs v y := rfl
@[simp] lemma ofAbs_add (x y : WithAbs v) : ofAbs (x + y) = ofAbs x + ofAbs y := rfl

@[simp] lemma toAbs_mul (x y : R) : toAbs v (x * y) = toAbs v x * toAbs v y := rfl
@[simp] lemma ofAbs_mul (x y : WithAbs v) : ofAbs (x * y) = ofAbs x * ofAbs y := rfl

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

instance [Nontrivial R] : Nontrivial (WithAbs v) := (equiv v).nontrivial
instance [Unique R] : Unique (WithAbs v) := (equiv v).unique
instance : Inhabited (WithAbs v) := ⟨0⟩

variable {T U : Type*} [Semiring T] [Semiring U] (w : AbsoluteValue T S) (u : AbsoluteValue U S)
  (f : R →+* T) (g : T →+* U)

/-- Lift a ring hom to `WithAbs`. -/
def map : WithAbs v →+* WithAbs w := (equiv w).symm.toRingHom.comp (f.comp (equiv v).toRingHom)

@[simp] theorem map_id : WithAbs.map v v (RingHom.id R) = RingHom.id (WithAbs v) := rfl
theorem map_comp : map v u (g.comp f) = (map w u g).comp (map v w f) := rfl
@[simp] theorem map_apply (x : WithAbs v) : map v w f x = toAbs w (f x.ofAbs) := rfl

variable (f : R ≃+* T) (g : T ≃+* U)

/-- Lift a `RingEquiv` to `WithAbs`. -/
def congr : WithAbs v ≃+* WithAbs w where
  __ := map v w f.toRingHom
  invFun := map w v f.symm.toRingHom
  left_inv x := by simp
  right_inv x := by simp

@[simp]
theorem congr_refl : congr v v (RingEquiv.refl R) = RingEquiv.refl (WithAbs v) := rfl
theorem congr_trans : congr v u (f.trans g) = (congr v w f).trans (congr w u g) := rfl
theorem congr_symm : (congr v w f).symm = congr w v f.symm := rfl
@[simp] theorem congr_apply (x : WithAbs v) : congr v w f x = toAbs w (f x.ofAbs) := rfl
@[simp] theorem congr_symm_apply (x : WithAbs w) :
    (congr v w f).symm x = toAbs v (f.symm x.ofAbs) := rfl

/-- The canonical (semiring) equivalence between `WithAbs v` and `WithAbs w`, for any two
absolute values `v` and `w` on `R`. -/
@[deprecated "Use `WithAbs.congr` instead." (since := "2026-03-02")]
def equivWithAbs (v w : AbsoluteValue R S) : WithAbs v ≃+* WithAbs w :=
    congr v w (.refl R)

@[deprecated "Use `WithAbs.congr_symm` instead." (since := "2026-03-02")]
theorem equivWithAbs_symm (v w : AbsoluteValue R S) :
    (congr v w (.refl R)).symm = (congr w v (RingEquiv.refl R).symm) :=
  congr_symm _ _ _

@[deprecated "Use `simp`." (since := "2026-03-02")]
theorem equiv_equivWithAbs_symm_apply {v w : AbsoluteValue R S} {x : WithAbs w} :
    equiv v ((congr v w (.refl R)).symm x) = equiv w x := by simp

@[deprecated "Use `simp`." (since := "2026-03-02")]
theorem equivWithAbs_equiv_symm_apply {v w : AbsoluteValue R S} {x : R} :
    congr v w (.refl R) ((equiv v).symm x) = (equiv w).symm x := by simp

@[deprecated "Use `simp`." (since := "2026-03-02")]
theorem equivWithAbs_symm_equiv_symm_apply {v w : AbsoluteValue R S} {x : R} :
    (congr v w (.refl R)).symm ((equiv w).symm x) = (equiv v).symm x := by simp

end Semiring

section CommSemiring

variable [CommSemiring R] (v : AbsoluteValue R S)

set_option backward.isDefEq.respectTransparency false in
instance : CommSemiring (WithAbs v) := fast_instance% (equiv v).commSemiring

end CommSemiring

section Ring

variable [Ring R]

set_option backward.isDefEq.respectTransparency false in
instance (v : AbsoluteValue R S) : Ring (WithAbs v) := fast_instance% (equiv v).ring

noncomputable instance normedRing (v : AbsoluteValue R ℝ) : NormedRing (WithAbs v) :=
  letI := v.toNormedRing
  (equiv v).normedRing

lemma norm_eq_apply_ofAbs (v : AbsoluteValue R ℝ) (x : WithAbs v) : ‖x‖ = v x.ofAbs := rfl
lemma norm_toAbs_eq (v : AbsoluteValue R ℝ) (x : R) : ‖toAbs v x‖ = v x := rfl

@[deprecated (since := "2026-03-02")] alias norm_eq_abv := norm_eq_apply_ofAbs
@[deprecated (since := "2026-03-02")] alias norm_eq_abv' := norm_toAbs_eq

variable (v : AbsoluteValue R S)

@[simp] lemma toAbs_sub (x y : R) : toAbs v (x - y) = toAbs v x - toAbs v y := rfl
@[simp] lemma ofAbs_sub (x y : WithAbs v) : ofAbs (x - y) = ofAbs x - ofAbs y := rfl

@[simp] lemma toAbs_neg (x : R) : toAbs v (-x) = - toAbs v x := rfl
@[simp] lemma ofAbs_neg (x : WithAbs v) : ofAbs (-x) = - ofAbs x := rfl

end Ring

section CommRing

variable [CommRing R] (v : AbsoluteValue R S)

set_option backward.isDefEq.respectTransparency false in
instance : CommRing (WithAbs v) := fast_instance% (equiv v).commRing

end CommRing

section Module

variable {R T : Type*} [Semiring R] (v : AbsoluteValue R S)

instance [SMul R T] : SMul (WithAbs v) T where
  smul x t := ofAbs x • t

theorem smul_left_def [SMul R T] (x : WithAbs v) (t : T) :
    x • t = ofAbs x • t := rfl

instance [SMul R T] [FaithfulSMul R T] : FaithfulSMul (WithAbs v) T where
  eq_of_smul_eq_smul h := ofAbs_injective v <| FaithfulSMul.eq_of_smul_eq_smul h

instance [SMul T R] : SMul T (WithAbs v) := (equiv v).smul T

theorem smul_right_def [SMul T R] (t : T) (x : WithAbs v) :
    t • x = toAbs v (t • x.ofAbs) := rfl

instance [SMul T R] [FaithfulSMul T R] : FaithfulSMul T (WithAbs v) where
  eq_of_smul_eq_smul h := by
    simp only [smul_right_def, toAbs.injEq] at h
    exact FaithfulSMul.eq_of_smul_eq_smul fun _ ↦ h (toAbs v _)

instance {P : Type*} [SMul T P] [SMul R T] [SMul R P] [IsScalarTower R T P] :
    IsScalarTower (WithAbs v) T P where
  smul_assoc := by simp [smul_left_def]

instance {P : Type*} [SMul P R] [SMul T R] [SMul P T]
    [IsScalarTower P T R] : IsScalarTower P T (WithAbs v) := (equiv v).isScalarTower P T

instance {P : Type*} [SMul P R] [SMul P T] [SMul R T]
    [IsScalarTower P R T] : IsScalarTower P (WithAbs v) T where
  smul_assoc := by simp [smul_right_def, smul_left_def]

/-- Not an instance because it causes non-reducible diamonds when `T = WithAbs v`. -/
@[implicit_reducible]
def moduleLeft [AddCommMonoid T] [Module R T] : Module (WithAbs v) T :=
  .compHom T (equiv v).toRingHom

@[deprecated (since := "2026-03-02")] alias instModule_left := moduleLeft

instance [Semiring T] [Module T R] : Module T (WithAbs v) :=
  fast_instance% (equiv v).module T

@[deprecated (since := "2026-03-02")] alias instModule_right := instModule

variable [Semiring T] [Module R T] (v : AbsoluteValue T S)

variable (R) in
/-- The canonical `R`-linear isomorphism between `WithAbs v` and `T`, when
`v : AbsoluteValue T S`. -/
def linearEquiv [Semiring T] [Module R T] (v : AbsoluteValue T S) :
    WithAbs v ≃ₗ[R] T := (equiv v).linearEquiv R

variable {v}

@[simp] theorem linearEquiv_apply (x : WithAbs v) : linearEquiv R v x = x.ofAbs := rfl
@[simp] theorem linearEquiv_symm_apply (x : T) : (linearEquiv R v).symm x = toAbs v x := rfl

end Module

section algebra

variable {R T : Type*} [CommSemiring R] [Semiring T] [Algebra R T]

variable (T) in
/-- Not an instance because it causes non-reducible diamonds when `T = WithAbs v`. -/
@[implicit_reducible]
def algebraLeft (v : AbsoluteValue R S) : Algebra (WithAbs v) T :=
  .compHom T (equiv v).toRingHom

attribute [local instance] algebraLeft in
theorem algebraMap_left_apply {v : AbsoluteValue R S} (x : WithAbs v) :
    algebraMap (WithAbs v) T x = algebraMap R T x.ofAbs := rfl

attribute [local instance] algebraLeft in
theorem algebraMap_left_injective (v : AbsoluteValue R S)
    (h : Function.Injective (algebraMap R T)) :
    Function.Injective (algebraMap (WithAbs v) T) :=
  h.comp (ofAbs_injective v)

instance (v : AbsoluteValue T S) : Algebra R (WithAbs v) :=
  fast_instance% (equiv v).algebra R

theorem algebraMap_right_apply {v : AbsoluteValue T S} (x : R) :
    algebraMap R (WithAbs v) x = toAbs v (algebraMap R T x) := rfl

theorem algebraMap_right_injective (v : AbsoluteValue T S)
    (h : Function.Injective (algebraMap R T)) : Function.Injective (algebraMap R (WithAbs v)) :=
  (toAbs_injective v).comp h

attribute [local instance] algebraLeft in
theorem ofAbs_algebraMap (v : AbsoluteValue R S) (w : AbsoluteValue T S) (x : WithAbs v) :
    (algebraMap (WithAbs v) (WithAbs w) x).ofAbs = algebraMap R T x.ofAbs := rfl

@[deprecated (since := "2026-03-02")] alias instAlgebra_left := algebraLeft
@[deprecated (since := "2026-03-02")] alias instAlgebra_right := instAlgebra

variable (R) in
/-- The canonical algebra isomorphism from an `R`-algebra `R'` with an absolute value `v`
to `R'`. -/
def algEquiv (v : AbsoluteValue T S) : (WithAbs v) ≃ₐ[R] T := (equiv v).algEquiv R

@[simp] theorem algEquiv_apply (v : AbsoluteValue T S) (x : WithAbs v) :
    algEquiv R v x = x.ofAbs := rfl
@[simp] theorem algEquiv_symm_apply (v : AbsoluteValue T S) (x : T) :
    (algEquiv R v).symm x = toAbs v x := rfl

end algebra

end WithAbs

namespace AbsoluteValue

variable {K L S : Type*} [CommRing K] [IsSimpleRing K] [CommRing L] [Algebra K L] [PartialOrder S]
  [Nontrivial L] [Semiring S]

/-- An absolute value `w` of `L / K` lies over the absolute value `v` of `K` if `v` is the
restriction of `w` to `K`. -/
class LiesOver (w : AbsoluteValue L S) (v : AbsoluteValue K S) : Prop where
  comp_eq (w) (v) : w.comp (algebraMap K L).injective = v

end AbsoluteValue
