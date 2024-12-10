/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Kim Morrison
-/
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.MonoidAlgebra.Lift
import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# Algebra structure on monoid algebras

This file lifts the `k`-algebra structure on `A` to (`Add`)`MonoidAlgebra A G`.

## Main definitions

* `MonoidAlgebra.algebra`, `AddMonoidAlgebra.algebra`: (additive) monoid algebras are algebras.
* `MonoidAlgebra.lift`, `AddMonoidAlgebra.lift`: lift a monoid homomorphism `G →* A` to an algebra
  homomorphism `MonoidAlgebra k G →ₐ[k] A`.
-/

noncomputable section

open Finset

open Finsupp hiding single

universe u₁ u₂ u₃ u₄

variable (k : Type u₁) (G : Type u₂) (H : Type*) {R : Type*}

/-! ### Multiplicative monoids -/

namespace MonoidAlgebra

variable {k G}

/-! #### Algebra structure -/

section Algebra

/-- The instance `Algebra k (MonoidAlgebra A G)` whenever we have `Algebra k A`.

In particular this provides the instance `Algebra k (MonoidAlgebra k G)`.
-/
instance algebra {A : Type*} [CommSemiring k] [Semiring A] [Algebra k A] [Monoid G] :
    Algebra k (MonoidAlgebra A G) :=
  { singleOneRingHom.comp (algebraMap k A) with
    smul_def' := fun r a => by
      ext
      -- Porting note: Newly required.
      rw [Finsupp.coe_smul]
      simp [single_one_mul_apply, Algebra.smul_def, Pi.smul_apply]
    commutes' := fun r f => by
      refine Finsupp.ext fun _ => ?_
      simp [single_one_mul_apply, mul_single_one_apply, Algebra.commutes] }

/-- `Finsupp.single 1` as an `AlgHom` -/
@[simps! apply]
def singleOneAlgHom {A : Type*} [CommSemiring k] [Semiring A] [Algebra k A] [Monoid G] :
    A →ₐ[k] MonoidAlgebra A G :=
  { singleOneRingHom with
    commutes' := fun r => by
      ext
      simp
      rfl }

@[simp]
theorem coe_algebraMap {A : Type*} [CommSemiring k] [Semiring A] [Algebra k A] [Monoid G] :
    ⇑(algebraMap k (MonoidAlgebra A G)) = single 1 ∘ algebraMap k A :=
  rfl

theorem single_eq_algebraMap_mul_of [CommSemiring k] [Monoid G] (a : G) (b : k) :
    single a b = algebraMap k (MonoidAlgebra k G) b * of k G a := by simp

theorem single_algebraMap_eq_algebraMap_mul_of {A : Type*} [CommSemiring k] [Semiring A]
    [Algebra k A] [Monoid G] (a : G) (b : k) :
    single a (algebraMap k A b) = algebraMap k (MonoidAlgebra A G) b * of A G a := by simp

end Algebra

section lift

variable [CommSemiring k] [Monoid G] [Monoid H]
variable {A : Type u₃} [Semiring A] [Algebra k A] {B : Type*} [Semiring B] [Algebra k B]

/-- `liftNCRingHom` as an `AlgHom`, for when `f` is an `AlgHom` -/
def liftNCAlgHom (f : A →ₐ[k] B) (g : G →* B) (h_comm : ∀ x y, Commute (f x) (g y)) :
    MonoidAlgebra A G →ₐ[k] B :=
  { liftNCRingHom (f : A →+* B) g h_comm with
    commutes' := by simp [liftNCRingHom] }

/-- A `k`-algebra homomorphism from `MonoidAlgebra k G` is uniquely defined by its
values on the functions `single a 1`. -/
theorem algHom_ext ⦃φ₁ φ₂ : MonoidAlgebra k G →ₐ[k] A⦄
    (h : ∀ x, φ₁ (single x 1) = φ₂ (single x 1)) : φ₁ = φ₂ :=
  AlgHom.toLinearMap_injective <| Finsupp.lhom_ext' fun a => LinearMap.ext_ring (h a)

-- Porting note: The priority must be `high`.
/-- See note [partially-applied ext lemmas]. -/
@[ext high]
theorem algHom_ext' ⦃φ₁ φ₂ : MonoidAlgebra k G →ₐ[k] A⦄
    (h :
      (φ₁ : MonoidAlgebra k G →* A).comp (of k G) = (φ₂ : MonoidAlgebra k G →* A).comp (of k G)) :
    φ₁ = φ₂ :=
  algHom_ext <| DFunLike.congr_fun h

variable (k G A)

/-- Any monoid homomorphism `G →* A` can be lifted to an algebra homomorphism
`MonoidAlgebra k G →ₐ[k] A`. -/
def lift : (G →* A) ≃ (MonoidAlgebra k G →ₐ[k] A) where
  invFun f := (f : MonoidAlgebra k G →* A).comp (of k G)
  toFun F := liftNCAlgHom (Algebra.ofId k A) F fun _ _ => Algebra.commutes _ _
  left_inv f := by
    ext
    simp [liftNCAlgHom, liftNCRingHom]
  right_inv F := by
    ext
    simp [liftNCAlgHom, liftNCRingHom]

variable {k G H A}

theorem lift_apply' (F : G →* A) (f : MonoidAlgebra k G) :
    lift k G A F f = f.sum fun a b => algebraMap k A b * F a :=
  rfl

theorem lift_apply (F : G →* A) (f : MonoidAlgebra k G) :
    lift k G A F f = f.sum fun a b => b • F a := by simp only [lift_apply', Algebra.smul_def]

theorem lift_def (F : G →* A) : ⇑(lift k G A F) = liftNC ((algebraMap k A : k →+* A) : k →+ A) F :=
  rfl

@[simp]
theorem lift_symm_apply (F : MonoidAlgebra k G →ₐ[k] A) (x : G) :
    (lift k G A).symm F x = F (single x 1) :=
  rfl

@[simp]
theorem lift_single (F : G →* A) (a b) : lift k G A F (single a b) = b • F a := by
  rw [lift_def, liftNC_single, Algebra.smul_def, AddMonoidHom.coe_coe]

theorem lift_of (F : G →* A) (x) : lift k G A F (of k G x) = F x := by simp

theorem lift_unique' (F : MonoidAlgebra k G →ₐ[k] A) :
    F = lift k G A ((F : MonoidAlgebra k G →* A).comp (of k G)) :=
  ((lift k G A).apply_symm_apply F).symm

/-- Decomposition of a `k`-algebra homomorphism from `MonoidAlgebra k G` by
its values on `F (single a 1)`. -/
theorem lift_unique (F : MonoidAlgebra k G →ₐ[k] A) (f : MonoidAlgebra k G) :
    F f = f.sum fun a b => b • F (single a 1) := by
  conv_lhs =>
    rw [lift_unique' F]
    simp [lift_apply]

end lift

section

-- attribute [local reducible] MonoidAlgebra -- Porting note: `reducible` cannot be `local`.

variable (k)

/-- When `V` is a `k[G]`-module, multiplication by a group element `g` is a `k`-linear map. -/
def GroupSMul.linearMap [Monoid G] [CommSemiring k] (V : Type u₃) [AddCommMonoid V] [Module k V]
    [Module (MonoidAlgebra k G) V] [IsScalarTower k (MonoidAlgebra k G) V] (g : G) : V →ₗ[k] V where
  toFun v := single g (1 : k) • v
  map_add' x y := smul_add (single g (1 : k)) x y
  map_smul' _c _x := smul_algebra_smul_comm _ _ _

@[simp]
theorem GroupSMul.linearMap_apply [Monoid G] [CommSemiring k] (V : Type u₃) [AddCommMonoid V]
    [Module k V] [Module (MonoidAlgebra k G) V] [IsScalarTower k (MonoidAlgebra k G) V] (g : G)
    (v : V) : (GroupSMul.linearMap k V g) v = single g (1 : k) • v :=
  rfl

section

variable {k}
variable [Monoid G] [CommSemiring k] {V : Type u₃} {W : Type u₄} [AddCommMonoid V] [Module k V]
  [Module (MonoidAlgebra k G) V] [IsScalarTower k (MonoidAlgebra k G) V] [AddCommMonoid W]
  [Module k W] [Module (MonoidAlgebra k G) W] [IsScalarTower k (MonoidAlgebra k G) W]
  (f : V →ₗ[k] W)

/-- Build a `k[G]`-linear map from a `k`-linear map and evidence that it is `G`-equivariant. -/
def equivariantOfLinearOfComm
    (h : ∀ (g : G) (v : V), f (single g (1 : k) • v) = single g (1 : k) • f v) :
    V →ₗ[MonoidAlgebra k G] W where
  toFun := f
  map_add' v v' := by simp
  map_smul' c v := by
    -- Porting note: Was `apply`.
    refine Finsupp.induction c ?_ ?_
    · simp
    · intro g r c' _nm _nz w
      dsimp at *
      simp only [add_smul, f.map_add, w, add_left_inj, single_eq_algebraMap_mul_of, ← smul_smul]
      erw [algebraMap_smul (MonoidAlgebra k G) r, algebraMap_smul (MonoidAlgebra k G) r, f.map_smul,
        h g v, of_apply]

variable (h : ∀ (g : G) (v : V), f (single g (1 : k) • v) = single g (1 : k) • f v)

@[simp]
theorem equivariantOfLinearOfComm_apply (v : V) : (equivariantOfLinearOfComm f h) v = f v :=
  rfl

end

end

end MonoidAlgebra

namespace AddMonoidAlgebra

variable {k G H}

/-! #### Algebra structure -/

section Algebra

/-- The instance `Algebra R k[G]` whenever we have `Algebra R k`.

In particular this provides the instance `Algebra k k[G]`.
-/
instance algebra [CommSemiring R] [Semiring k] [Algebra R k] [AddMonoid G] :
    Algebra R k[G] :=
  { singleZeroRingHom.comp (algebraMap R k) with
    smul_def' := fun r a => by
      ext
      -- Porting note: Newly required.
      rw [Finsupp.coe_smul]
      simp [single_zero_mul_apply, Algebra.smul_def, Pi.smul_apply]
    commutes' := fun r f => by
      refine Finsupp.ext fun _ => ?_
      simp [single_zero_mul_apply, mul_single_zero_apply, Algebra.commutes] }

/-- `Finsupp.single 0` as an `AlgHom` -/
@[simps! apply]
def singleZeroAlgHom [CommSemiring R] [Semiring k] [Algebra R k] [AddMonoid G] : k →ₐ[R] k[G] :=
  { singleZeroRingHom with
    commutes' := fun r => by
      ext
      simp
      rfl }

@[simp]
theorem coe_algebraMap [CommSemiring R] [Semiring k] [Algebra R k] [AddMonoid G] :
    (algebraMap R k[G] : R → k[G]) = single 0 ∘ algebraMap R k :=
  rfl

end Algebra

section lift

variable [CommSemiring k] [AddMonoid G]
variable {A : Type u₃} [Semiring A] [Algebra k A] {B : Type*} [Semiring B] [Algebra k B]

/-- `liftNCRingHom` as an `AlgHom`, for when `f` is an `AlgHom` -/
def liftNCAlgHom (f : A →ₐ[k] B) (g : Multiplicative G →* B) (h_comm : ∀ x y, Commute (f x) (g y)) :
    A[G] →ₐ[k] B :=
  { liftNCRingHom (f : A →+* B) g h_comm with
    commutes' := by simp [liftNCRingHom] }

/-- A `k`-algebra homomorphism from `k[G]` is uniquely defined by its
values on the functions `single a 1`. -/
theorem algHom_ext ⦃φ₁ φ₂ : k[G] →ₐ[k] A⦄
    (h : ∀ x, φ₁ (single x 1) = φ₂ (single x 1)) : φ₁ = φ₂ :=
  @MonoidAlgebra.algHom_ext k (Multiplicative G) _ _ _ _ _ _ _ h

/-- See note [partially-applied ext lemmas]. -/
@[ext high]
theorem algHom_ext' ⦃φ₁ φ₂ : k[G] →ₐ[k] A⦄
    (h : (φ₁ : k[G] →* A).comp (of k G) = (φ₂ : k[G] →* A).comp (of k G)) :
    φ₁ = φ₂ :=
  algHom_ext <| DFunLike.congr_fun h

variable (k G A)

/-- Any monoid homomorphism `G →* A` can be lifted to an algebra homomorphism
`k[G] →ₐ[k] A`. -/
def lift : (Multiplicative G →* A) ≃ (k[G] →ₐ[k] A) :=
  { @MonoidAlgebra.lift k (Multiplicative G) _ _ A _ _ with
    invFun := fun f => (f : k[G] →* A).comp (of k G)
    toFun := fun F =>
      { @MonoidAlgebra.lift k (Multiplicative G) _ _ A _ _ F with
        toFun := liftNCAlgHom (Algebra.ofId k A) F fun _ _ => Algebra.commutes _ _ } }

variable {k G A}

theorem lift_apply' (F : Multiplicative G →* A) (f : MonoidAlgebra k G) :
    lift k G A F f = f.sum fun a b => algebraMap k A b * F (Multiplicative.ofAdd a) :=
  rfl

theorem lift_apply (F : Multiplicative G →* A) (f : MonoidAlgebra k G) :
    lift k G A F f = f.sum fun a b => b • F (Multiplicative.ofAdd a) := by
  simp only [lift_apply', Algebra.smul_def]

theorem lift_def (F : Multiplicative G →* A) :
    ⇑(lift k G A F) = liftNC ((algebraMap k A : k →+* A) : k →+ A) F :=
  rfl

@[simp]
theorem lift_symm_apply (F : k[G] →ₐ[k] A) (x : Multiplicative G) :
    (lift k G A).symm F x = F (single x.toAdd 1) :=
  rfl

theorem lift_of (F : Multiplicative G →* A) (x : Multiplicative G) :
    lift k G A F (of k G x) = F x := MonoidAlgebra.lift_of F x

@[simp]
theorem lift_single (F : Multiplicative G →* A) (a b) :
    lift k G A F (single a b) = b • F (Multiplicative.ofAdd a) :=
  MonoidAlgebra.lift_single F (.ofAdd a) b

lemma lift_of' (F : Multiplicative G →* A) (x : G) :
    lift k G A F (of' k G x) = F (Multiplicative.ofAdd x) :=
  lift_of F x

theorem lift_unique' (F : k[G] →ₐ[k] A) :
    F = lift k G A ((F : k[G] →* A).comp (of k G)) :=
  ((lift k G A).apply_symm_apply F).symm

/-- Decomposition of a `k`-algebra homomorphism from `MonoidAlgebra k G` by
its values on `F (single a 1)`. -/
theorem lift_unique (F : k[G] →ₐ[k] A) (f : MonoidAlgebra k G) :
    F f = f.sum fun a b => b • F (single a 1) := by
  conv_lhs =>
    rw [lift_unique' F]
    simp [lift_apply]

theorem algHom_ext_iff {φ₁ φ₂ : k[G] →ₐ[k] A} :
    (∀ x, φ₁ (Finsupp.single x 1) = φ₂ (Finsupp.single x 1)) ↔ φ₁ = φ₂ :=
  ⟨fun h => algHom_ext h, by rintro rfl _; rfl⟩

end lift

end AddMonoidAlgebra
