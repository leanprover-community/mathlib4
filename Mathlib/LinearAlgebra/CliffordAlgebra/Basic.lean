/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Utensil Song
-/
import Mathlib.Algebra.RingQuot
import Mathlib.LinearAlgebra.TensorAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Isometry
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

#align_import linear_algebra.clifford_algebra.basic from "leanprover-community/mathlib"@"d46774d43797f5d1f507a63a6e904f7a533ae74a"

/-!
# Clifford Algebras

We construct the Clifford algebra of a module `M` over a commutative ring `R`, equipped with
a quadratic form `Q`.

## Notation

The Clifford algebra of the `R`-module `M` equipped with a quadratic form `Q` is
an `R`-algebra denoted `CliffordAlgebra Q`.

Given a linear morphism `f : M → A` from a module `M` to another `R`-algebra `A`, such that
`cond : ∀ m, f m * f m = algebraMap _ _ (Q m)`, there is a (unique) lift of `f` to an `R`-algebra
morphism from `CliffordAlgebra Q` to `A`, which is denoted `CliffordAlgebra.lift Q f cond`.

The canonical linear map `M → CliffordAlgebra Q` is denoted `CliffordAlgebra.ι Q`.

## Theorems

The main theorems proved ensure that `CliffordAlgebra Q` satisfies the universal property
of the Clifford algebra.
1. `ι_comp_lift` is the fact that the composition of `ι Q` with `lift Q f cond` agrees with `f`.
2. `lift_unique` ensures the uniqueness of `lift Q f cond` with respect to 1.

## Implementation details

The Clifford algebra of `M` is constructed as a quotient of the tensor algebra, as follows.
1. We define a relation `CliffordAlgebra.Rel Q` on `TensorAlgebra R M`.
   This is the smallest relation which identifies squares of elements of `M` with `Q m`.
2. The Clifford algebra is the quotient of the tensor algebra by this relation.

This file is almost identical to `Mathlib/LinearAlgebra/ExteriorAlgebra/Basic.lean`.
-/


variable {R : Type*} [CommRing R]

variable {M : Type*} [AddCommGroup M] [Module R M]

variable (Q : QuadraticForm R M)

variable {n : ℕ}

namespace CliffordAlgebra

open TensorAlgebra

/-- `Rel` relates each `ι m * ι m`, for `m : M`, with `Q m`.

The Clifford algebra of `M` is defined as the quotient modulo this relation.
-/
inductive Rel : TensorAlgebra R M → TensorAlgebra R M → Prop
  | of (m : M) : Rel (ι R m * ι R m) (algebraMap R _ (Q m))
#align clifford_algebra.rel CliffordAlgebra.Rel

end CliffordAlgebra

/-- The Clifford algebra of an `R`-module `M` equipped with a quadratic_form `Q`.
-/
def CliffordAlgebra :=
  RingQuot (CliffordAlgebra.Rel Q)
#align clifford_algebra CliffordAlgebra

namespace CliffordAlgebra

-- Porting note: Expanded `deriving Inhabited, Semiring, Algebra`
instance instInhabited : Inhabited (CliffordAlgebra Q) := RingQuot.instInhabited _
#align clifford_algebra.inhabited CliffordAlgebra.instInhabited
instance instRing : Ring (CliffordAlgebra Q) := RingQuot.instRing _
#align clifford_algebra.ring CliffordAlgebra.instRing

instance (priority := 900) instAlgebra' {R A M} [CommSemiring R] [AddCommGroup M] [CommRing A]
    [Algebra R A] [Module R M] [Module A M] (Q : QuadraticForm A M)
    [IsScalarTower R A M] :
    Algebra R (CliffordAlgebra Q) :=
  RingQuot.instAlgebra _

-- verify there are no diamonds
example : (algebraNat : Algebra ℕ (CliffordAlgebra Q)) = instAlgebra' _ := rfl
example : (algebraInt _ : Algebra ℤ (CliffordAlgebra Q)) = instAlgebra' _ := rfl

-- shortcut instance, as the other instance is slow
instance instAlgebra : Algebra R (CliffordAlgebra Q) := instAlgebra' _
#align clifford_algebra.algebra CliffordAlgebra.instAlgebra

instance {R S A M} [CommSemiring R] [CommSemiring S] [AddCommGroup M] [CommRing A]
    [Algebra R A] [Algebra S A] [Module R M] [Module S M] [Module A M] (Q : QuadraticForm A M)
    [IsScalarTower R A M] [IsScalarTower S A M] [SMulCommClass R S A] :
    SMulCommClass R S (CliffordAlgebra Q) :=
  RingQuot.instSMulCommClass _

instance {R S A M} [CommSemiring R] [CommSemiring S] [AddCommGroup M] [CommRing A]
    [SMul R S] [Algebra R A] [Algebra S A] [Module R M] [Module S M] [Module A M]
    [IsScalarTower R A M] [IsScalarTower S A M] [IsScalarTower R S A] (Q : QuadraticForm A M) :
    IsScalarTower R S (CliffordAlgebra Q) :=
  RingQuot.instIsScalarTower _

/-- The canonical linear map `M →ₗ[R] CliffordAlgebra Q`.
-/
def ι : M →ₗ[R] CliffordAlgebra Q :=
  (RingQuot.mkAlgHom R _).toLinearMap.comp (TensorAlgebra.ι R)
#align clifford_algebra.ι CliffordAlgebra.ι

/-- As well as being linear, `ι Q` squares to the quadratic form -/
@[simp]
theorem ι_sq_scalar (m : M) : ι Q m * ι Q m = algebraMap R _ (Q m) := by
  erw [← AlgHom.map_mul, RingQuot.mkAlgHom_rel R (Rel.of m), AlgHom.commutes]
  rfl
#align clifford_algebra.ι_sq_scalar CliffordAlgebra.ι_sq_scalar

variable {Q} {A : Type*} [Semiring A] [Algebra R A]

@[simp]
theorem comp_ι_sq_scalar (g : CliffordAlgebra Q →ₐ[R] A) (m : M) :
    g (ι Q m) * g (ι Q m) = algebraMap _ _ (Q m) := by
  rw [← AlgHom.map_mul, ι_sq_scalar, AlgHom.commutes]
#align clifford_algebra.comp_ι_sq_scalar CliffordAlgebra.comp_ι_sq_scalar

variable (Q)

/-- Given a linear map `f : M →ₗ[R] A` into an `R`-algebra `A`, which satisfies the condition:
`cond : ∀ m : M, f m * f m = Q(m)`, this is the canonical lift of `f` to a morphism of `R`-algebras
from `CliffordAlgebra Q` to `A`.
-/
@[simps symm_apply]
def lift : { f : M →ₗ[R] A // ∀ m, f m * f m = algebraMap _ _ (Q m) } ≃ (CliffordAlgebra Q →ₐ[R] A)
    where
  toFun f :=
    RingQuot.liftAlgHom R
      ⟨TensorAlgebra.lift R (f : M →ₗ[R] A), fun x y (h : Rel Q x y) => by
        induction h
        rw [AlgHom.commutes, AlgHom.map_mul, TensorAlgebra.lift_ι_apply, f.prop]⟩
  invFun F :=
    ⟨F.toLinearMap.comp (ι Q), fun m => by
      rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, comp_ι_sq_scalar]⟩
  left_inv f := by
    ext x
    -- porting note: removed `simp only` proof which gets stuck simplifying `LinearMap.comp_apply`
    exact (RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _).trans (TensorAlgebra.lift_ι_apply _ x)
  right_inv F :=
    -- porting note: replaced with proof derived from the one for `TensorAlgebra`
    RingQuot.ringQuot_ext' _ _ _ <|
      TensorAlgebra.hom_ext <|
        LinearMap.ext fun x => by
          exact
            (RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _).trans (TensorAlgebra.lift_ι_apply _ _)
#align clifford_algebra.lift CliffordAlgebra.lift

variable {Q}

@[simp]
theorem ι_comp_lift (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = algebraMap _ _ (Q m)) :
    (lift Q ⟨f, cond⟩).toLinearMap.comp (ι Q) = f :=
  Subtype.mk_eq_mk.mp <| (lift Q).symm_apply_apply ⟨f, cond⟩
#align clifford_algebra.ι_comp_lift CliffordAlgebra.ι_comp_lift

@[simp]
theorem lift_ι_apply (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = algebraMap _ _ (Q m)) (x) :
    lift Q ⟨f, cond⟩ (ι Q x) = f x :=
  (LinearMap.ext_iff.mp <| ι_comp_lift f cond) x
#align clifford_algebra.lift_ι_apply CliffordAlgebra.lift_ι_apply

@[simp]
theorem lift_unique (f : M →ₗ[R] A) (cond : ∀ m : M, f m * f m = algebraMap _ _ (Q m))
    (g : CliffordAlgebra Q →ₐ[R] A) : g.toLinearMap.comp (ι Q) = f ↔ g = lift Q ⟨f, cond⟩ := by
  convert (lift Q : _ ≃ (CliffordAlgebra Q →ₐ[R] A)).symm_apply_eq
  -- porting note: added `Subtype.mk_eq_mk`
  rw [lift_symm_apply, Subtype.mk_eq_mk]
#align clifford_algebra.lift_unique CliffordAlgebra.lift_unique

@[simp]
theorem lift_comp_ι (g : CliffordAlgebra Q →ₐ[R] A) :
    lift Q ⟨g.toLinearMap.comp (ι Q), comp_ι_sq_scalar _⟩ = g := by
  -- porting note: removed `rw [lift_symm_apply]; rfl`, changed `convert` to `exact`
  exact (lift Q : _ ≃ (CliffordAlgebra Q →ₐ[R] A)).apply_symm_apply g
#align clifford_algebra.lift_comp_ι CliffordAlgebra.lift_comp_ι

/-- See note [partially-applied ext lemmas]. -/
@[ext high]
theorem hom_ext {A : Type*} [Semiring A] [Algebra R A] {f g : CliffordAlgebra Q →ₐ[R] A} :
    f.toLinearMap.comp (ι Q) = g.toLinearMap.comp (ι Q) → f = g := by
  intro h
  apply (lift Q).symm.injective
  rw [lift_symm_apply, lift_symm_apply]
  simp only [h]
#align clifford_algebra.hom_ext CliffordAlgebra.hom_ext

-- This proof closely follows `TensorAlgebra.induction`
/-- If `C` holds for the `algebraMap` of `r : R` into `CliffordAlgebra Q`, the `ι` of `x : M`,
and is preserved under addition and muliplication, then it holds for all of `CliffordAlgebra Q`.

See also the stronger `CliffordAlgebra.left_induction` and `CliffordAlgebra.right_induction`.
-/
@[elab_as_elim]
theorem induction {C : CliffordAlgebra Q → Prop}
    (h_grade0 : ∀ r, C (algebraMap R (CliffordAlgebra Q) r)) (h_grade1 : ∀ x, C (ι Q x))
    (h_mul : ∀ a b, C a → C b → C (a * b)) (h_add : ∀ a b, C a → C b → C (a + b))
    (a : CliffordAlgebra Q) : C a := by
  -- the arguments are enough to construct a subalgebra, and a mapping into it from M
  let s : Subalgebra R (CliffordAlgebra Q) :=
    { carrier := C
      mul_mem' := @h_mul
      add_mem' := @h_add
      algebraMap_mem' := h_grade0 }
  -- porting note: Added `h`. `h` is needed for `of`.
  letI h : AddCommMonoid s := inferInstanceAs (AddCommMonoid (Subalgebra.toSubmodule s))
  let of : { f : M →ₗ[R] s // ∀ m, f m * f m = algebraMap _ _ (Q m) } :=
    ⟨(ι Q).codRestrict (Subalgebra.toSubmodule s) h_grade1, fun m => Subtype.eq <| ι_sq_scalar Q m⟩
  -- the mapping through the subalgebra is the identity
  have of_id : AlgHom.id R (CliffordAlgebra Q) = s.val.comp (lift Q of) := by
    ext
    simp
    -- porting note: `simp` can't apply this
    erw [LinearMap.codRestrict_apply]
  -- finding a proof is finding an element of the subalgebra
  -- porting note: was `convert Subtype.prop (lift Q of a); exact AlgHom.congr_fun of_id a`
  rw [← AlgHom.id_apply (R := R) a, of_id]
  exact Subtype.prop (lift Q of a)
#align clifford_algebra.induction CliffordAlgebra.induction

theorem mul_add_swap_eq_polar_of_forall_mul_self_eq {A : Type*} [Ring A] [Algebra R A]
    (f : M →ₗ[R] A) (hf : ∀ x, f x * f x = algebraMap _ _ (Q x)) (a b : M) :
    f a * f b + f b * f a = algebraMap R _ (QuadraticForm.polar Q a b) :=
  calc
    f a * f b + f b * f a = f (a + b) * f (a + b) - f a * f a - f b * f b := by
      rw [f.map_add, mul_add, add_mul, add_mul]; abel
    _ = algebraMap R _ (Q (a + b)) - algebraMap R _ (Q a) - algebraMap R _ (Q b) := by
      rw [hf, hf, hf]
    _ = algebraMap R _ (Q (a + b) - Q a - Q b) := by rw [← RingHom.map_sub, ← RingHom.map_sub]
    _ = algebraMap R _ (QuadraticForm.polar Q a b) := rfl

/-- An alternative way to provide the argument to `CliffordAlgebra.lift` when `2` is invertible.

To show a function squares to the quadratic form, it suffices to show that
`f x * f y + f y * f x = algebraMap _ _ (polar Q x y)` -/
theorem forall_mul_self_eq_iff {A : Type*} [Ring A] [Algebra R A] (h2 : IsUnit (2 : A))
    (f : M →ₗ[R] A) :
    (∀ x, f x * f x = algebraMap _ _ (Q x)) ↔
      (LinearMap.mul R A).compl₂ f ∘ₗ f + (LinearMap.mul R A).flip.compl₂ f ∘ₗ f =
        Q.polarBilin.toLin.compr₂ (Algebra.linearMap R A) := by
  simp_rw [FunLike.ext_iff]
  refine ⟨mul_add_swap_eq_polar_of_forall_mul_self_eq _, fun h x => ?_⟩
  change ∀ x y : M, f x * f y + f y * f x = algebraMap R A (QuadraticForm.polar Q x y) at h
  apply h2.mul_left_cancel
  rw [two_mul, two_mul, h x x, QuadraticForm.polar_self, two_mul, map_add]

/-- The symmetric product of vectors is a scalar -/
theorem ι_mul_ι_add_swap (a b : M) :
    ι Q a * ι Q b + ι Q b * ι Q a = algebraMap R _ (QuadraticForm.polar Q a b) :=
  mul_add_swap_eq_polar_of_forall_mul_self_eq _ (ι_sq_scalar _) _ _
#align clifford_algebra.ι_mul_ι_add_swap CliffordAlgebra.ι_mul_ι_add_swap

theorem ι_mul_comm (a b : M) :
    ι Q a * ι Q b = algebraMap R _ (QuadraticForm.polar Q a b) - ι Q b * ι Q a :=
  eq_sub_of_add_eq (ι_mul_ι_add_swap a b)
#align clifford_algebra.ι_mul_comm CliffordAlgebra.ι_mul_comm

/-- $aba$ is a vector. -/
theorem ι_mul_ι_mul_ι (a b : M) :
    ι Q a * ι Q b * ι Q a = ι Q (QuadraticForm.polar Q a b • a - Q a • b) := by
  rw [ι_mul_comm, sub_mul, mul_assoc, ι_sq_scalar, ← Algebra.smul_def, ← Algebra.commutes, ←
    Algebra.smul_def, ← map_smul, ← map_smul, ← map_sub]
#align clifford_algebra.ι_mul_ι_mul_ι CliffordAlgebra.ι_mul_ι_mul_ι

@[simp]
theorem ι_range_map_lift (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = algebraMap _ _ (Q m)) :
    (ι Q).range.map (lift Q ⟨f, cond⟩).toLinearMap = LinearMap.range f := by
  rw [← LinearMap.range_comp, ι_comp_lift]
#align clifford_algebra.ι_range_map_lift CliffordAlgebra.ι_range_map_lift

section Map

variable {M₁ M₂ M₃ : Type*}

variable [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]

variable [Module R M₁] [Module R M₂] [Module R M₃]

variable {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂} {Q₃ : QuadraticForm R M₃}

/-- Any linear map that preserves the quadratic form lifts to an `AlgHom` between algebras.

See `CliffordAlgebra.equivOfIsometry` for the case when `f` is a `QuadraticForm.IsometryEquiv`. -/
def map (f : Q₁ →qᵢ Q₂) :
    CliffordAlgebra Q₁ →ₐ[R] CliffordAlgebra Q₂ :=
  CliffordAlgebra.lift Q₁
    ⟨ι Q₂ ∘ₗ f.toLinearMap, fun m => (ι_sq_scalar _ _).trans <| RingHom.congr_arg _ <| f.map_app m⟩
#align clifford_algebra.map CliffordAlgebra.map

@[simp]
theorem map_comp_ι (f : Q₁ →qᵢ Q₂) :
    (map f).toLinearMap ∘ₗ ι Q₁ = ι Q₂ ∘ₗ f.toLinearMap :=
  ι_comp_lift _ _
#align clifford_algebra.map_comp_ι CliffordAlgebra.map_comp_ι

@[simp]
theorem map_apply_ι (f : Q₁ →qᵢ Q₂) (m : M₁) : map f (ι Q₁ m) = ι Q₂ (f m) :=
  lift_ι_apply _ _ m
#align clifford_algebra.map_apply_ι CliffordAlgebra.map_apply_ι

variable (Q₁) in
@[simp]
theorem map_id : map (QuadraticForm.Isometry.id Q₁) = AlgHom.id R (CliffordAlgebra Q₁) := by
  ext m; exact map_apply_ι _ m
#align clifford_algebra.map_id CliffordAlgebra.map_id

@[simp]
theorem map_comp_map (f : Q₂ →qᵢ Q₃) (g : Q₁ →qᵢ Q₂) :
    (map f).comp (map g) = map (f.comp g) := by
  ext m
  dsimp only [LinearMap.comp_apply, AlgHom.comp_apply, AlgHom.toLinearMap_apply, AlgHom.id_apply]
  rw [map_apply_ι, map_apply_ι, map_apply_ι, QuadraticForm.Isometry.comp_apply]
#align clifford_algebra.map_comp_map CliffordAlgebra.map_comp_map

@[simp]
theorem ι_range_map_map (f : Q₁ →qᵢ Q₂) :
    (ι Q₁).range.map (map f).toLinearMap = f.range.map (ι Q₂) :=
  (ι_range_map_lift _ _).trans (LinearMap.range_comp _ _)
#align clifford_algebra.ι_range_map_map CliffordAlgebra.ι_range_map_map

/-- Two `CliffordAlgebra`s are equivalent as algebras if their quadratic forms are
equivalent. -/
@[simps! apply]
def equivOfIsometry (e : Q₁.IsometryEquiv Q₂) : CliffordAlgebra Q₁ ≃ₐ[R] CliffordAlgebra Q₂ :=
  AlgEquiv.ofAlgHom (map e.toIsometry) (map e.symm.toIsometry)
    ((map_comp_map _ _).trans <| by
      convert map_id Q₂ using 2  -- porting note: replaced `_` with `Q₂`
      ext m
      exact e.toLinearEquiv.apply_symm_apply m)
    ((map_comp_map _ _).trans <| by
      convert map_id Q₁ using 2  -- porting note: replaced `_` with `Q₁`
      ext m
      exact e.toLinearEquiv.symm_apply_apply m)
#align clifford_algebra.equiv_of_isometry CliffordAlgebra.equivOfIsometry

@[simp]
theorem equivOfIsometry_symm (e : Q₁.IsometryEquiv Q₂) :
    (equivOfIsometry e).symm = equivOfIsometry e.symm :=
  rfl
#align clifford_algebra.equiv_of_isometry_symm CliffordAlgebra.equivOfIsometry_symm

@[simp]
theorem equivOfIsometry_trans (e₁₂ : Q₁.IsometryEquiv Q₂) (e₂₃ : Q₂.IsometryEquiv Q₃) :
    (equivOfIsometry e₁₂).trans (equivOfIsometry e₂₃) = equivOfIsometry (e₁₂.trans e₂₃) := by
  ext x
  exact AlgHom.congr_fun (map_comp_map _ _) x
#align clifford_algebra.equiv_of_isometry_trans CliffordAlgebra.equivOfIsometry_trans

@[simp]
theorem equivOfIsometry_refl :
    (equivOfIsometry <| QuadraticForm.IsometryEquiv.refl Q₁) = AlgEquiv.refl := by
  ext x
  exact AlgHom.congr_fun (map_id Q₁) x
#align clifford_algebra.equiv_of_isometry_refl CliffordAlgebra.equivOfIsometry_refl

end Map

variable (Q)

/-- If the quadratic form of a vector is invertible, then so is that vector. -/
def invertibleιOfInvertible (m : M) [Invertible (Q m)] : Invertible (ι Q m) where
  invOf := ι Q (⅟ (Q m) • m)
  invOf_mul_self := by
    rw [map_smul, smul_mul_assoc, ι_sq_scalar, Algebra.smul_def, ← map_mul, invOf_mul_self, map_one]
  mul_invOf_self := by
    rw [map_smul, mul_smul_comm, ι_sq_scalar, Algebra.smul_def, ← map_mul, invOf_mul_self, map_one]
#align clifford_algebra.invertible_ι_of_invertible CliffordAlgebra.invertibleιOfInvertible

/-- For a vector with invertible quadratic form, $v^{-1} = \frac{v}{Q(v)}$ -/
theorem invOf_ι (m : M) [Invertible (Q m)] [Invertible (ι Q m)] :
    ⅟ (ι Q m) = ι Q (⅟ (Q m) • m) := by
  letI := invertibleιOfInvertible Q m
  convert (rfl : ⅟ (ι Q m) = _)
#align clifford_algebra.inv_of_ι CliffordAlgebra.invOf_ι

theorem isUnit_ι_of_isUnit {m : M} (h : IsUnit (Q m)) : IsUnit (ι Q m) := by
  cases h.nonempty_invertible
  letI := invertibleιOfInvertible Q m
  exact isUnit_of_invertible (ι Q m)
#align clifford_algebra.is_unit_ι_of_is_unit CliffordAlgebra.isUnit_ι_of_isUnit

/-- $aba^{-1}$ is a vector. -/
theorem ι_mul_ι_mul_invOf_ι (a b : M) [Invertible (ι Q a)] [Invertible (Q a)] :
    ι Q a * ι Q b * ⅟ (ι Q a) = ι Q ((⅟ (Q a) * QuadraticForm.polar Q a b) • a - b) := by
  rw [invOf_ι, map_smul, mul_smul_comm, ι_mul_ι_mul_ι, ← map_smul, smul_sub, smul_smul, smul_smul,
    invOf_mul_self, one_smul]
#align clifford_algebra.ι_mul_ι_mul_inv_of_ι CliffordAlgebra.ι_mul_ι_mul_invOf_ι

/-- $a^{-1}ba$ is a vector. -/
theorem invOf_ι_mul_ι_mul_ι (a b : M) [Invertible (ι Q a)] [Invertible (Q a)] :
    ⅟ (ι Q a) * ι Q b * ι Q a = ι Q ((⅟ (Q a) * QuadraticForm.polar Q a b) • a - b) := by
  rw [invOf_ι, map_smul, smul_mul_assoc, smul_mul_assoc, ι_mul_ι_mul_ι, ← map_smul, smul_sub,
    smul_smul, smul_smul, invOf_mul_self, one_smul]
#align clifford_algebra.inv_of_ι_mul_ι_mul_ι CliffordAlgebra.invOf_ι_mul_ι_mul_ι

end CliffordAlgebra

namespace TensorAlgebra

variable {Q}

/-- The canonical image of the `TensorAlgebra` in the `CliffordAlgebra`, which maps
`TensorAlgebra.ι R x` to `CliffordAlgebra.ι Q x`. -/
def toClifford : TensorAlgebra R M →ₐ[R] CliffordAlgebra Q :=
  TensorAlgebra.lift R (CliffordAlgebra.ι Q)
#align tensor_algebra.to_clifford TensorAlgebra.toClifford

@[simp]
theorem toClifford_ι (m : M) : toClifford (TensorAlgebra.ι R m) = CliffordAlgebra.ι Q m := by
  simp [toClifford]
#align tensor_algebra.to_clifford_ι TensorAlgebra.toClifford_ι

end TensorAlgebra
