/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.LinearAlgebra.Finrank
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.SetTheory.Cardinal.Ordinal

#align_import algebra.quaternion from "leanprover-community/mathlib"@"cf7a7252c1989efe5800e0b3cdfeb4228ac6b40e"

/-!
# Quaternions

In this file we define quaternions `ℍ[R]` over a commutative ring `R`, and define some
algebraic structures on `ℍ[R]`.

## Main definitions

* `QuaternionAlgebra R a b`, `ℍ[R, a, b]` :
  [quaternion algebra](https://en.wikipedia.org/wiki/Quaternion_algebra) with coefficients `a`, `b`
* `Quaternion R`, `ℍ[R]` : the space of quaternions, a.k.a. `QuaternionAlgebra R (-1) (-1)`;
* `Quaternion.normSq` : square of the norm of a quaternion;

We also define the following algebraic structures on `ℍ[R]`:

* `Ring ℍ[R, a, b]`, `StarRing ℍ[R, a, b]`, and `Algebra R ℍ[R, a, b]` : for any commutative ring
  `R`;
* `Ring ℍ[R]`, `StarRing ℍ[R]`, and `Algebra R ℍ[R]` : for any commutative ring `R`;
* `IsDomain ℍ[R]` : for a linear ordered commutative ring `R`;
* `DivisionRing ℍ[R]` : for a linear ordered field `R`.

## Notation

The following notation is available with `open Quaternion` or `open scoped Quaternion`.

* `ℍ[R, c₁, c₂]` : `QuaternionAlgebra R c₁ c₂`
* `ℍ[R]` : quaternions over `R`.

## Implementation notes

We define quaternions over any ring `R`, not just `ℝ` to be able to deal with, e.g., integer
or rational quaternions without using real numbers. In particular, all definitions in this file
are computable.

## Tags

quaternion
-/


/-- Quaternion algebra over a type with fixed coefficients $a=i^2$ and $b=j^2$.
Implemented as a structure with four fields: `re`, `imI`, `imJ`, and `imK`. -/
@[ext]
structure QuaternionAlgebra (R : Type*) (a b : R) where
  /-- Real part of a quaternion. -/
  re : R
  imI : R
  imJ : R
  imK : R
#align quaternion_algebra QuaternionAlgebra
#align quaternion_algebra.re QuaternionAlgebra.re
#align quaternion_algebra.im_i QuaternionAlgebra.imI
#align quaternion_algebra.im_j QuaternionAlgebra.imJ
#align quaternion_algebra.im_k QuaternionAlgebra.imK

@[inherit_doc]
scoped[Quaternion] notation "ℍ[" R "," a "," b "]" => QuaternionAlgebra R a b
open Quaternion

namespace QuaternionAlgebra

/-- The equivalence between a quaternion algebra over `R` and `R × R × R × R`. -/
@[simps]
def equivProd {R : Type*} (c₁ c₂ : R) : ℍ[R,c₁,c₂] ≃ R × R × R × R where
  toFun a := ⟨a.1, a.2, a.3, a.4⟩
  invFun a := ⟨a.1, a.2.1, a.2.2.1, a.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
#align quaternion_algebra.equiv_prod QuaternionAlgebra.equivProd

/-- The equivalence between a quaternion algebra over `R` and `Fin 4 → R`. -/
@[simps symm_apply]
def equivTuple {R : Type*} (c₁ c₂ : R) : ℍ[R,c₁,c₂] ≃ (Fin 4 → R) where
  toFun a := ![a.1, a.2, a.3, a.4]
  invFun a := ⟨a 0, a 1, a 2, a 3⟩
  left_inv _ := rfl
  right_inv f := by ext ⟨_, _ | _ | _ | _ | _ | ⟨⟩⟩ <;> rfl
                                                        -- 🎉 no goals
                                                        -- 🎉 no goals
                                                        -- 🎉 no goals
                                                        -- 🎉 no goals
#align quaternion_algebra.equiv_tuple QuaternionAlgebra.equivTuple

@[simp]
theorem equivTuple_apply {R : Type*} (c₁ c₂ : R) (x : ℍ[R,c₁,c₂]) :
    equivTuple c₁ c₂ x = ![x.re, x.imI, x.imJ, x.imK] :=
  rfl
#align quaternion_algebra.equiv_tuple_apply QuaternionAlgebra.equivTuple_apply

@[simp]
theorem mk.eta {R : Type*} {c₁ c₂} (a : ℍ[R,c₁,c₂]) : mk a.1 a.2 a.3 a.4 = a := rfl
#align quaternion_algebra.mk.eta QuaternionAlgebra.mk.eta

variable {S T R : Type*} [CommRing R] {c₁ c₂ : R} (r x y z : R) (a b c : ℍ[R,c₁,c₂])

/-- The imaginary part of a quaternion. -/
def im (x : ℍ[R,c₁,c₂]) : ℍ[R,c₁,c₂] :=
  ⟨0, x.imI, x.imJ, x.imK⟩
#align quaternion_algebra.im QuaternionAlgebra.im

@[simp]
theorem im_re : a.im.re = 0 :=
  rfl
#align quaternion_algebra.im_re QuaternionAlgebra.im_re

@[simp]
theorem im_imI : a.im.imI = a.imI :=
  rfl
#align quaternion_algebra.im_im_i QuaternionAlgebra.im_imI

@[simp]
theorem im_imJ : a.im.imJ = a.imJ :=
  rfl
#align quaternion_algebra.im_im_j QuaternionAlgebra.im_imJ

@[simp]
theorem im_imK : a.im.imK = a.imK :=
  rfl
#align quaternion_algebra.im_im_k QuaternionAlgebra.im_imK

@[simp]
theorem im_idem : a.im.im = a.im :=
  rfl
#align quaternion_algebra.im_idem QuaternionAlgebra.im_idem

/-- Coercion `R → ℍ[R,c₁,c₂]`. -/
@[coe] def coe (x : R) : ℍ[R,c₁,c₂] := ⟨x, 0, 0, 0⟩

instance : CoeTC R ℍ[R,c₁,c₂] := ⟨coe⟩

@[simp, norm_cast]
theorem coe_re : (x : ℍ[R,c₁,c₂]).re = x := rfl
#align quaternion_algebra.coe_re QuaternionAlgebra.coe_re

@[simp, norm_cast]
theorem coe_imI : (x : ℍ[R,c₁,c₂]).imI = 0 := rfl
#align quaternion_algebra.coe_im_i QuaternionAlgebra.coe_imI

@[simp, norm_cast]
theorem coe_imJ : (x : ℍ[R,c₁,c₂]).imJ = 0 := rfl
#align quaternion_algebra.coe_im_j QuaternionAlgebra.coe_imJ

@[simp, norm_cast]
theorem coe_imK : (x : ℍ[R,c₁,c₂]).imK = 0 := rfl
#align quaternion_algebra.coe_im_k QuaternionAlgebra.coe_imK

theorem coe_injective : Function.Injective (coe : R → ℍ[R,c₁,c₂]) := fun _ _ h => congr_arg re h
#align quaternion_algebra.coe_injective QuaternionAlgebra.coe_injective

@[simp]
theorem coe_inj {x y : R} : (x : ℍ[R,c₁,c₂]) = y ↔ x = y :=
  coe_injective.eq_iff
#align quaternion_algebra.coe_inj QuaternionAlgebra.coe_inj

-- porting note: removed `simps`, added simp lemmas manually
instance : Zero ℍ[R,c₁,c₂] := ⟨⟨0, 0, 0, 0⟩⟩

@[simp] theorem zero_re : (0 : ℍ[R,c₁,c₂]).re = 0 := rfl
#align quaternion_algebra.has_zero_zero_re QuaternionAlgebra.zero_re

@[simp] theorem zero_imI : (0 : ℍ[R,c₁,c₂]).imI = 0 := rfl
#align quaternion_algebra.has_zero_zero_im_i QuaternionAlgebra.zero_imI

@[simp] theorem zero_imJ : (0 : ℍ[R,c₁,c₂]).imJ = 0 := rfl
#align quaternion_algebra.zero_zero_im_j QuaternionAlgebra.zero_imJ

@[simp] theorem zero_imK : (0 : ℍ[R,c₁,c₂]).imK = 0 := rfl
#align quaternion_algebra.zero_zero_im_k QuaternionAlgebra.zero_imK

@[simp] theorem zero_im : (0 : ℍ[R,c₁,c₂]).im = 0 := rfl

@[simp, norm_cast]
theorem coe_zero : ((0 : R) : ℍ[R,c₁,c₂]) = 0 := rfl
#align quaternion_algebra.coe_zero QuaternionAlgebra.coe_zero

instance : Inhabited ℍ[R,c₁,c₂] := ⟨0⟩

-- porting note: removed `simps`, added simp lemmas manually
instance : One ℍ[R,c₁,c₂] := ⟨⟨1, 0, 0, 0⟩⟩

@[simp] theorem one_re : (1 : ℍ[R,c₁,c₂]).re = 1 := rfl
#align quaternion_algebra.has_one_one_re QuaternionAlgebra.one_re

@[simp] theorem one_imI : (1 : ℍ[R,c₁,c₂]).imI = 0 := rfl
#align quaternion_algebra.has_one_one_im_i QuaternionAlgebra.one_imI

@[simp] theorem one_imJ : (1 : ℍ[R,c₁,c₂]).imJ = 0 := rfl
#align quaternion_algebra.one_one_im_j QuaternionAlgebra.one_imJ

@[simp] theorem one_imK : (1 : ℍ[R,c₁,c₂]).imK = 0 := rfl
#align quaternion_algebra.one_one_im_k QuaternionAlgebra.one_imK

@[simp] theorem one_im : (1 : ℍ[R,c₁,c₂]).im = 0 := rfl

@[simp, norm_cast]
theorem coe_one : ((1 : R) : ℍ[R,c₁,c₂]) = 1 := rfl
#align quaternion_algebra.coe_one QuaternionAlgebra.coe_one

-- porting note: removed `simps`, added simp lemmas manually
instance : Add ℍ[R,c₁,c₂] :=
  ⟨fun a b => ⟨a.1 + b.1, a.2 + b.2, a.3 + b.3, a.4 + b.4⟩⟩

@[simp] theorem add_re : (a + b).re = a.re + b.re := rfl
#align quaternion_algebra.has_add_add_re QuaternionAlgebra.add_re

@[simp] theorem add_imI : (a + b).imI = a.imI + b.imI := rfl
#align quaternion_algebra.has_add_add_im_i QuaternionAlgebra.add_imI

@[simp] theorem add_imJ : (a + b).imJ = a.imJ + b.imJ := rfl
#align quaternion_algebra.has_add_add_im_j QuaternionAlgebra.add_imJ

@[simp] theorem add_imK : (a + b).imK = a.imK + b.imK := rfl
#align quaternion_algebra.has_add_add_im_k QuaternionAlgebra.add_imK

@[simp] theorem add_im : (a + b).im = a.im + b.im :=
  QuaternionAlgebra.ext _ _ (zero_add _).symm rfl rfl rfl

@[simp]
theorem mk_add_mk (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R) :
    (mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂]) + mk b₁ b₂ b₃ b₄ = mk (a₁ + b₁) (a₂ + b₂) (a₃ + b₃) (a₄ + b₄) :=
  rfl
#align quaternion_algebra.mk_add_mk QuaternionAlgebra.mk_add_mk

@[simp, norm_cast]
theorem coe_add : ((x + y : R) : ℍ[R,c₁,c₂]) = x + y := by ext <;> simp
                                                                   -- 🎉 no goals
                                                                   -- 🎉 no goals
                                                                   -- 🎉 no goals
                                                                   -- 🎉 no goals
#align quaternion_algebra.coe_add QuaternionAlgebra.coe_add

-- porting note: removed `simps`, added simp lemmas manually
instance : Neg ℍ[R,c₁,c₂] := ⟨fun a => ⟨-a.1, -a.2, -a.3, -a.4⟩⟩

@[simp] theorem neg_re : (-a).re = -a.re := rfl
#align quaternion_algebra.has_neg_neg_re QuaternionAlgebra.neg_re

@[simp] theorem neg_imI : (-a).imI = -a.imI := rfl
#align quaternion_algebra.has_neg_neg_im_i QuaternionAlgebra.neg_imI

@[simp] theorem neg_imJ : (-a).imJ = -a.imJ := rfl
#align quaternion_algebra.has_neg_neg_im_j QuaternionAlgebra.neg_imJ

@[simp] theorem neg_imK : (-a).imK = -a.imK := rfl
#align quaternion_algebra.has_neg_neg_im_k QuaternionAlgebra.neg_imK

@[simp] theorem neg_im : (-a).im = -a.im :=
  QuaternionAlgebra.ext _ _ neg_zero.symm rfl rfl rfl

@[simp]
theorem neg_mk (a₁ a₂ a₃ a₄ : R) : -(mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂]) = ⟨-a₁, -a₂, -a₃, -a₄⟩ :=
  rfl
#align quaternion_algebra.neg_mk QuaternionAlgebra.neg_mk

@[simp, norm_cast]
theorem coe_neg : ((-x : R) : ℍ[R,c₁,c₂]) = -x := by ext <;> simp
                                                             -- 🎉 no goals
                                                             -- 🎉 no goals
                                                             -- 🎉 no goals
                                                             -- 🎉 no goals
#align quaternion_algebra.coe_neg QuaternionAlgebra.coe_neg

instance : Sub ℍ[R,c₁,c₂] :=
  ⟨fun a b => ⟨a.1 - b.1, a.2 - b.2, a.3 - b.3, a.4 - b.4⟩⟩

@[simp] theorem sub_re : (a - b).re = a.re - b.re := rfl
#align quaternion_algebra.has_sub_sub_re QuaternionAlgebra.sub_re

@[simp] theorem sub_imI : (a - b).imI = a.imI - b.imI := rfl
#align quaternion_algebra.has_sub_sub_im_i QuaternionAlgebra.sub_imI

@[simp] theorem sub_imJ : (a - b).imJ = a.imJ - b.imJ := rfl
#align quaternion_algebra.has_sub_sub_im_j QuaternionAlgebra.sub_imJ

@[simp] theorem sub_imK : (a - b).imK = a.imK - b.imK := rfl
#align quaternion_algebra.has_sub_sub_im_k QuaternionAlgebra.sub_imK

@[simp] theorem sub_im : (a - b).im = a.im - b.im :=
  QuaternionAlgebra.ext _ _ (sub_zero _).symm rfl rfl rfl

@[simp]
theorem mk_sub_mk (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R) :
    (mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂]) - mk b₁ b₂ b₃ b₄ = mk (a₁ - b₁) (a₂ - b₂) (a₃ - b₃) (a₄ - b₄) :=
  rfl
#align quaternion_algebra.mk_sub_mk QuaternionAlgebra.mk_sub_mk

@[simp, norm_cast]
theorem coe_im : (x : ℍ[R,c₁,c₂]).im = 0 :=
  rfl
#align quaternion_algebra.coe_im QuaternionAlgebra.coe_im

@[simp]
theorem re_add_im : ↑a.re + a.im = a :=
  QuaternionAlgebra.ext _ _ (add_zero _) (zero_add _) (zero_add _) (zero_add _)
#align quaternion_algebra.re_add_im QuaternionAlgebra.re_add_im

@[simp]
theorem sub_self_im : a - a.im = a.re :=
  QuaternionAlgebra.ext _ _ (sub_zero _) (sub_self _) (sub_self _) (sub_self _)
#align quaternion_algebra.sub_self_im QuaternionAlgebra.sub_self_im

@[simp]
theorem sub_self_re : a - a.re = a.im :=
  QuaternionAlgebra.ext _ _ (sub_self _) (sub_zero _) (sub_zero _) (sub_zero _)
#align quaternion_algebra.sub_self_re QuaternionAlgebra.sub_self_re

/-- Multiplication is given by

* `1 * x = x * 1 = x`;
* `i * i = c₁`;
* `j * j = c₂`;
* `i * j = k`, `j * i = -k`;
* `k * k = -c₁ * c₂`;
* `i * k = c₁ * j`, `k * i = -c₁ * j`;
* `j * k = -c₂ * i`, `k * j = c₂ * i`.  -/
instance : Mul ℍ[R,c₁,c₂] :=
  ⟨fun a b =>
    ⟨a.1 * b.1 + c₁ * a.2 * b.2 + c₂ * a.3 * b.3 - c₁ * c₂ * a.4 * b.4,
      a.1 * b.2 + a.2 * b.1 - c₂ * a.3 * b.4 + c₂ * a.4 * b.3,
      a.1 * b.3 + c₁ * a.2 * b.4 + a.3 * b.1 - c₁ * a.4 * b.2,
      a.1 * b.4 + a.2 * b.3 - a.3 * b.2 + a.4 * b.1⟩⟩

@[simp]
theorem mul_re : (a * b).re = a.1 * b.1 + c₁ * a.2 * b.2 + c₂ * a.3 * b.3 - c₁ * c₂ * a.4 * b.4 :=
  rfl
#align quaternion_algebra.has_mul_mul_re QuaternionAlgebra.mul_re

@[simp]
theorem mul_imI : (a * b).imI = a.1 * b.2 + a.2 * b.1 - c₂ * a.3 * b.4 + c₂ * a.4 * b.3 := rfl
#align quaternion_algebra.has_mul_mul_im_i QuaternionAlgebra.mul_imI

@[simp]
theorem mul_imJ : (a * b).imJ = a.1 * b.3 + c₁ * a.2 * b.4 + a.3 * b.1 - c₁ * a.4 * b.2 := rfl
#align quaternion_algebra.has_mul_mul_im_j QuaternionAlgebra.mul_imJ

@[simp] theorem mul_imK : (a * b).imK = a.1 * b.4 + a.2 * b.3 - a.3 * b.2 + a.4 * b.1 := rfl
#align quaternion_algebra.has_mul_mul_im_k QuaternionAlgebra.mul_imK

@[simp]
theorem mk_mul_mk (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R) :
    (mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂]) * mk b₁ b₂ b₃ b₄ =
      ⟨a₁ * b₁ + c₁ * a₂ * b₂ + c₂ * a₃ * b₃ - c₁ * c₂ * a₄ * b₄,
        a₁ * b₂ + a₂ * b₁ - c₂ * a₃ * b₄ + c₂ * a₄ * b₃,
        a₁ * b₃ + c₁ * a₂ * b₄ + a₃ * b₁ - c₁ * a₄ * b₂, a₁ * b₄ + a₂ * b₃ - a₃ * b₂ + a₄ * b₁⟩ :=
  rfl
#align quaternion_algebra.mk_mul_mk QuaternionAlgebra.mk_mul_mk

section

variable [SMul S R] [SMul T R] (s : S)

-- porting note: Lean 4 auto drops the unused `[Ring R]` argument
instance : SMul S ℍ[R,c₁,c₂] where smul s a := ⟨s • a.1, s • a.2, s • a.3, s • a.4⟩

instance [SMul S T] [IsScalarTower S T R] : IsScalarTower S T ℍ[R,c₁,c₂]
    where smul_assoc s t x := by ext <;> exact smul_assoc _ _ _
                                         -- 🎉 no goals
                                         -- 🎉 no goals
                                         -- 🎉 no goals
                                         -- 🎉 no goals

instance [SMulCommClass S T R] : SMulCommClass S T ℍ[R,c₁,c₂]
    where smul_comm s t x := by ext <;> exact smul_comm _ _ _
                                        -- 🎉 no goals
                                        -- 🎉 no goals
                                        -- 🎉 no goals
                                        -- 🎉 no goals

@[simp] theorem smul_re : (s • a).re = s • a.re := rfl
#align quaternion_algebra.smul_re QuaternionAlgebra.smul_re

@[simp] theorem smul_imI : (s • a).imI = s • a.imI := rfl
#align quaternion_algebra.smul_im_i QuaternionAlgebra.smul_imI

@[simp] theorem smul_imJ : (s • a).imJ = s • a.imJ := rfl
#align quaternion_algebra.smul_im_j QuaternionAlgebra.smul_imJ

@[simp] theorem smul_imK : (s • a).imK = s • a.imK := rfl
#align quaternion_algebra.smul_im_k QuaternionAlgebra.smul_imK

@[simp] theorem smul_im {S} [SMulZeroClass S R] (s : S) : (s • a).im = s • a.im :=
  QuaternionAlgebra.ext _ _ (smul_zero s).symm rfl rfl rfl

@[simp]
theorem smul_mk (re im_i im_j im_k : R) :
    s • (⟨re, im_i, im_j, im_k⟩ : ℍ[R,c₁,c₂]) = ⟨s • re, s • im_i, s • im_j, s • im_k⟩ :=
  rfl
#align quaternion_algebra.smul_mk QuaternionAlgebra.smul_mk

end

@[simp, norm_cast]
theorem coe_smul [SMulZeroClass S R] (s : S) (r : R) :
    (↑(s • r) : ℍ[R,c₁,c₂]) = s • (r : ℍ[R,c₁,c₂]) :=
  QuaternionAlgebra.ext _ _ rfl (smul_zero s).symm (smul_zero s).symm (smul_zero s).symm
#align quaternion_algebra.coe_smul QuaternionAlgebra.coe_smul

instance : AddCommGroup ℍ[R,c₁,c₂] :=
  (equivProd c₁ c₂).injective.addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (λ _ _ ↦ rfl) (λ _ _ ↦ rfl)

instance : AddCommGroupWithOne ℍ[R,c₁,c₂] where
  natCast n := ((n : R) : ℍ[R,c₁,c₂])
  natCast_zero := by simp
                     -- 🎉 no goals
  natCast_succ := by simp
                     -- 🎉 no goals
  intCast n := ((n : R) : ℍ[R,c₁,c₂])
  intCast_ofNat _ := congr_arg coe (Int.cast_ofNat _)
  intCast_negSucc n := by
    change coe _ = -coe _
    -- ⊢ ↑↑(Int.negSucc n) = -↑↑(n + 1)
    rw [Int.cast_negSucc, coe_neg]
    -- 🎉 no goals

@[simp, norm_cast]
theorem nat_cast_re (n : ℕ) : (n : ℍ[R,c₁,c₂]).re = n :=
  rfl
#align quaternion_algebra.nat_cast_re QuaternionAlgebra.nat_cast_re

@[simp, norm_cast]
theorem nat_cast_imI (n : ℕ) : (n : ℍ[R,c₁,c₂]).imI = 0 :=
  rfl
#align quaternion_algebra.nat_cast_im_i QuaternionAlgebra.nat_cast_imI

@[simp, norm_cast]
theorem nat_cast_imJ (n : ℕ) : (n : ℍ[R,c₁,c₂]).imJ = 0 :=
  rfl
#align quaternion_algebra.nat_cast_im_j QuaternionAlgebra.nat_cast_imJ

@[simp, norm_cast]
theorem nat_cast_imK (n : ℕ) : (n : ℍ[R,c₁,c₂]).imK = 0 :=
  rfl
#align quaternion_algebra.nat_cast_im_k QuaternionAlgebra.nat_cast_imK

@[simp, norm_cast]
theorem nat_cast_im (n : ℕ) : (n : ℍ[R,c₁,c₂]).im = 0 :=
  rfl
#align quaternion_algebra.nat_cast_im QuaternionAlgebra.nat_cast_im

@[norm_cast]
theorem coe_nat_cast (n : ℕ) : ↑(n : R) = (n : ℍ[R,c₁,c₂]) :=
  rfl
#align quaternion_algebra.coe_nat_cast QuaternionAlgebra.coe_nat_cast

@[simp, norm_cast]
theorem int_cast_re (z : ℤ) : (z : ℍ[R,c₁,c₂]).re = z :=
  rfl
#align quaternion_algebra.int_cast_re QuaternionAlgebra.int_cast_re

@[simp, norm_cast]
theorem int_cast_imI (z : ℤ) : (z : ℍ[R,c₁,c₂]).imI = 0 :=
  rfl
#align quaternion_algebra.int_cast_im_i QuaternionAlgebra.int_cast_imI

@[simp, norm_cast]
theorem int_cast_imJ (z : ℤ) : (z : ℍ[R,c₁,c₂]).imJ = 0 :=
  rfl
#align quaternion_algebra.int_cast_im_j QuaternionAlgebra.int_cast_imJ

@[simp, norm_cast]
theorem int_cast_imK (z : ℤ) : (z : ℍ[R,c₁,c₂]).imK = 0 :=
  rfl
#align quaternion_algebra.int_cast_im_k QuaternionAlgebra.int_cast_imK

@[simp, norm_cast]
theorem int_cast_im (z : ℤ) : (z : ℍ[R,c₁,c₂]).im = 0 :=
  rfl
#align quaternion_algebra.int_cast_im QuaternionAlgebra.int_cast_im

@[norm_cast]
theorem coe_int_cast (z : ℤ) : ↑(z : R) = (z : ℍ[R,c₁,c₂]) :=
  rfl
#align quaternion_algebra.coe_int_cast QuaternionAlgebra.coe_int_cast

instance instRing : Ring ℍ[R,c₁,c₂] where
  __ := inferInstanceAs (AddCommGroupWithOne ℍ[R,c₁,c₂])
  left_distrib _ _ _ := by ext <;> simp <;> ring
                                   -- ⊢ x✝².re * (x✝¹.re + x✝.re) + c₁ * x✝².imI * (x✝¹.imI + x✝.imI) + c₂ * x✝².imJ …
                                   -- ⊢ x✝².re * (x✝¹.imI + x✝.imI) + x✝².imI * (x✝¹.re + x✝.re) - c₂ * x✝².imJ * (x …
                                   -- ⊢ x✝².re * (x✝¹.imJ + x✝.imJ) + c₁ * x✝².imI * (x✝¹.imK + x✝.imK) + x✝².imJ *  …
                                   -- ⊢ x✝².re * (x✝¹.imK + x✝.imK) + x✝².imI * (x✝¹.imJ + x✝.imJ) - x✝².imJ * (x✝¹. …
                                            -- 🎉 no goals
                                            -- 🎉 no goals
                                            -- 🎉 no goals
                                            -- 🎉 no goals
  right_distrib _ _ _ := by ext <;> simp <;> ring
                                    -- ⊢ (x✝².re + x✝¹.re) * x✝.re + c₁ * (x✝².imI + x✝¹.imI) * x✝.imI + c₂ * (x✝².im …
                                    -- ⊢ (x✝².re + x✝¹.re) * x✝.imI + (x✝².imI + x✝¹.imI) * x✝.re - c₂ * (x✝².imJ + x …
                                    -- ⊢ (x✝².re + x✝¹.re) * x✝.imJ + c₁ * (x✝².imI + x✝¹.imI) * x✝.imK + (x✝².imJ +  …
                                    -- ⊢ (x✝².re + x✝¹.re) * x✝.imK + (x✝².imI + x✝¹.imI) * x✝.imJ - (x✝².imJ + x✝¹.i …
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
  zero_mul _ := by ext <;> simp
                           -- 🎉 no goals
                           -- 🎉 no goals
                           -- 🎉 no goals
                           -- 🎉 no goals
  mul_zero _ := by ext <;> simp
                           -- 🎉 no goals
                           -- 🎉 no goals
                           -- 🎉 no goals
                           -- 🎉 no goals
  mul_assoc _ _ _ := by ext <;> simp <;> ring
                                -- ⊢ (x✝².re * x✝¹.re + c₁ * x✝².imI * x✝¹.imI + c₂ * x✝².imJ * x✝¹.imJ - c₁ * c₂ …
                                -- ⊢ (x✝².re * x✝¹.re + c₁ * x✝².imI * x✝¹.imI + c₂ * x✝².imJ * x✝¹.imJ - c₁ * c₂ …
                                -- ⊢ (x✝².re * x✝¹.re + c₁ * x✝².imI * x✝¹.imI + c₂ * x✝².imJ * x✝¹.imJ - c₁ * c₂ …
                                -- ⊢ (x✝².re * x✝¹.re + c₁ * x✝².imI * x✝¹.imI + c₂ * x✝².imJ * x✝¹.imJ - c₁ * c₂ …
                                         -- 🎉 no goals
                                         -- 🎉 no goals
                                         -- 🎉 no goals
                                         -- 🎉 no goals
  one_mul _ := by ext <;> simp
                          -- 🎉 no goals
                          -- 🎉 no goals
                          -- 🎉 no goals
                          -- 🎉 no goals
  mul_one _ := by ext <;> simp
                          -- 🎉 no goals
                          -- 🎉 no goals
                          -- 🎉 no goals
                          -- 🎉 no goals

@[norm_cast, simp]
theorem coe_mul : ((x * y : R) : ℍ[R,c₁,c₂]) = x * y := by ext <;> simp
                                                                   -- 🎉 no goals
                                                                   -- 🎉 no goals
                                                                   -- 🎉 no goals
                                                                   -- 🎉 no goals
#align quaternion_algebra.coe_mul QuaternionAlgebra.coe_mul

-- TODO: add weaker `MulAction`, `DistribMulAction`, and `Module` instances (and repeat them
-- for `ℍ[R]`)
instance [CommSemiring S] [Algebra S R] : Algebra S ℍ[R,c₁,c₂] where
  smul := (· • ·)
  toFun s := coe (algebraMap S R s)
  map_one' := by simp only [map_one, coe_one]
                 -- 🎉 no goals
  map_zero' := by simp only [map_zero, coe_zero]
                  -- 🎉 no goals
                     -- 🎉 no goals
  map_mul' x y := by simp only [map_mul, coe_mul]
  map_add' x y := by simp only [map_add, coe_add]
                     -- 🎉 no goals
  smul_def' s x := by ext <;> simp [Algebra.smul_def]
                              -- 🎉 no goals
                              -- 🎉 no goals
                              -- 🎉 no goals
                              -- 🎉 no goals
                              -- 🎉 no goals
                              -- 🎉 no goals
                              -- 🎉 no goals
                              -- 🎉 no goals
  commutes' s x := by ext <;> simp [Algebra.commutes]

theorem algebraMap_eq (r : R) : algebraMap R ℍ[R,c₁,c₂] r = ⟨r, 0, 0, 0⟩ :=
  rfl
#align quaternion_algebra.algebra_map_eq QuaternionAlgebra.algebraMap_eq

section

variable (c₁ c₂)

/-- `QuaternionAlgebra.re` as a `LinearMap`-/
@[simps]
def reₗ : ℍ[R,c₁,c₂] →ₗ[R] R where
  toFun := re
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
#align quaternion_algebra.re_lm QuaternionAlgebra.reₗ

/-- `QuaternionAlgebra.imI` as a `LinearMap`-/
@[simps]
def imIₗ : ℍ[R,c₁,c₂] →ₗ[R] R where
  toFun := imI
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
#align quaternion_algebra.im_i_lm QuaternionAlgebra.imIₗ

/-- `QuaternionAlgebra.imJ` as a `LinearMap`-/
@[simps]
def imJₗ : ℍ[R,c₁,c₂] →ₗ[R] R where
  toFun := imJ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
#align quaternion_algebra.im_j_lm QuaternionAlgebra.imJₗ

/-- `QuaternionAlgebra.imK` as a `LinearMap`-/
@[simps]
def imKₗ : ℍ[R,c₁,c₂] →ₗ[R] R where
  toFun := imK
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
#align quaternion_algebra.im_k_lm QuaternionAlgebra.imKₗ

/-- `QuaternionAlgebra.equivTuple` as a linear equivalence. -/
def linearEquivTuple : ℍ[R,c₁,c₂] ≃ₗ[R] Fin 4 → R :=
  LinearEquiv.symm -- proofs are not `rfl` in the forward direction
    { (equivTuple c₁ c₂).symm with
      toFun := (equivTuple c₁ c₂).symm
      invFun := equivTuple c₁ c₂
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
#align quaternion_algebra.linear_equiv_tuple QuaternionAlgebra.linearEquivTuple

@[simp]
theorem coe_linearEquivTuple : ⇑(linearEquivTuple c₁ c₂) = equivTuple c₁ c₂ :=
  rfl
#align quaternion_algebra.coe_linear_equiv_tuple QuaternionAlgebra.coe_linearEquivTuple

@[simp]
theorem coe_linearEquivTuple_symm : ⇑(linearEquivTuple c₁ c₂).symm = (equivTuple c₁ c₂).symm :=
  rfl
#align quaternion_algebra.coe_linear_equiv_tuple_symm QuaternionAlgebra.coe_linearEquivTuple_symm

/-- `ℍ[R, c₁, c₂]` has a basis over `R` given by `1`, `i`, `j`, and `k`. -/
noncomputable def basisOneIJK : Basis (Fin 4) R ℍ[R,c₁,c₂] :=
  .ofEquivFun <| linearEquivTuple c₁ c₂
#align quaternion_algebra.basis_one_i_j_k QuaternionAlgebra.basisOneIJK

@[simp]
theorem coe_basisOneIJK_repr (q : ℍ[R,c₁,c₂]) :
    ⇑((basisOneIJK c₁ c₂).repr q) = ![q.re, q.imI, q.imJ, q.imK] :=
  rfl
#align quaternion_algebra.coe_basis_one_i_j_k_repr QuaternionAlgebra.coe_basisOneIJK_repr

instance : Module.Finite R ℍ[R,c₁,c₂] := .of_basis (basisOneIJK c₁ c₂)

instance : Module.Free R ℍ[R,c₁,c₂] := .of_basis (basisOneIJK c₁ c₂)

theorem rank_eq_four [StrongRankCondition R] : Module.rank R ℍ[R,c₁,c₂] = 4 := by
  rw [rank_eq_card_basis (basisOneIJK c₁ c₂), Fintype.card_fin]
  -- ⊢ ↑4 = 4
  norm_num
  -- 🎉 no goals
#align quaternion_algebra.rank_eq_four QuaternionAlgebra.rank_eq_four

theorem finrank_eq_four [StrongRankCondition R] : FiniteDimensional.finrank R ℍ[R,c₁,c₂] = 4 := by
  rw [FiniteDimensional.finrank, rank_eq_four, Cardinal.toNat_ofNat]
  -- 🎉 no goals
#align quaternion_algebra.finrank_eq_four QuaternionAlgebra.finrank_eq_four

end

@[norm_cast, simp]
theorem coe_sub : ((x - y : R) : ℍ[R,c₁,c₂]) = x - y :=
  (algebraMap R ℍ[R,c₁,c₂]).map_sub x y
#align quaternion_algebra.coe_sub QuaternionAlgebra.coe_sub

@[norm_cast, simp]
theorem coe_pow (n : ℕ) : (↑(x ^ n) : ℍ[R,c₁,c₂]) = (x : ℍ[R,c₁,c₂]) ^ n :=
  (algebraMap R ℍ[R,c₁,c₂]).map_pow x n
#align quaternion_algebra.coe_pow QuaternionAlgebra.coe_pow

theorem coe_commutes : ↑r * a = a * r :=
  Algebra.commutes r a
#align quaternion_algebra.coe_commutes QuaternionAlgebra.coe_commutes

theorem coe_commute : Commute (↑r) a :=
  coe_commutes r a
#align quaternion_algebra.coe_commute QuaternionAlgebra.coe_commute

theorem coe_mul_eq_smul : ↑r * a = r • a :=
  (Algebra.smul_def r a).symm
#align quaternion_algebra.coe_mul_eq_smul QuaternionAlgebra.coe_mul_eq_smul

theorem mul_coe_eq_smul : a * r = r • a := by rw [← coe_commutes, coe_mul_eq_smul]
                                              -- 🎉 no goals
#align quaternion_algebra.mul_coe_eq_smul QuaternionAlgebra.mul_coe_eq_smul

@[norm_cast, simp]
theorem coe_algebraMap : ⇑(algebraMap R ℍ[R,c₁,c₂]) = coe :=
  rfl
#align quaternion_algebra.coe_algebra_map QuaternionAlgebra.coe_algebraMap

theorem smul_coe : x • (y : ℍ[R,c₁,c₂]) = ↑(x * y) := by rw [coe_mul, coe_mul_eq_smul]
                                                         -- 🎉 no goals
#align quaternion_algebra.smul_coe QuaternionAlgebra.smul_coe

/-- Quaternion conjugate. -/
instance instStarQuaternionAlgebra : Star ℍ[R,c₁,c₂] where star a := ⟨a.1, -a.2, -a.3, -a.4⟩

@[simp] theorem re_star : (star a).re = a.re := rfl
#align quaternion_algebra.re_star QuaternionAlgebra.re_star

@[simp]
theorem imI_star : (star a).imI = -a.imI :=
  rfl
#align quaternion_algebra.im_i_star QuaternionAlgebra.imI_star

@[simp]
theorem imJ_star : (star a).imJ = -a.imJ :=
  rfl
#align quaternion_algebra.im_j_star QuaternionAlgebra.imJ_star

@[simp]
theorem imK_star : (star a).imK = -a.imK :=
  rfl
#align quaternion_algebra.im_k_star QuaternionAlgebra.imK_star

@[simp]
theorem im_star : (star a).im = -a.im :=
  QuaternionAlgebra.ext _ _ neg_zero.symm rfl rfl rfl
#align quaternion_algebra.im_star QuaternionAlgebra.im_star

@[simp]
theorem star_mk (a₁ a₂ a₃ a₄ : R) : star (mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂]) = ⟨a₁, -a₂, -a₃, -a₄⟩ :=
  rfl
#align quaternion_algebra.star_mk QuaternionAlgebra.star_mk

instance instStarRing : StarRing ℍ[R,c₁,c₂] where
  star_involutive x := by simp [Star.star]
                          -- 🎉 no goals
  star_add a b := by ext <;> simp [add_comm]
                             -- 🎉 no goals
                             -- ⊢ a.re * b.re + c₁ * a.imI * b.imI + c₂ * a.imJ * b.imJ - c₁ * c₂ * a.imK * b. …
                             -- ⊢ -(c₂ * a.imK * b.imJ) + (c₂ * a.imJ * b.imK - (a.re * b.imI + a.imI * b.re)) …
                             -- ⊢ c₁ * a.imK * b.imI - (a.re * b.imJ + c₁ * a.imI * b.imK + a.imJ * b.re) = -( …
                             -- ⊢ -(a.imK * b.re) + (a.imJ * b.imI - (a.re * b.imK + a.imI * b.imJ)) = -(b.re  …
                                      -- 🎉 no goals
                                      -- 🎉 no goals
                                      -- 🎉 no goals
                                      -- 🎉 no goals
                             -- 🎉 no goals
                             -- 🎉 no goals
                             -- 🎉 no goals
  star_mul a b := by ext <;> simp <;> ring

theorem self_add_star' : a + star a = ↑(2 * a.re) := by ext <;> simp [two_mul]
                                                                -- 🎉 no goals
                                                                -- 🎉 no goals
                                                                -- 🎉 no goals
                                                                -- 🎉 no goals
#align quaternion_algebra.self_add_star' QuaternionAlgebra.self_add_star'

theorem self_add_star : a + star a = 2 * a.re := by simp only [self_add_star', two_mul, coe_add]
                                                    -- 🎉 no goals
#align quaternion_algebra.self_add_star QuaternionAlgebra.self_add_star

theorem star_add_self' : star a + a = ↑(2 * a.re) := by rw [add_comm, self_add_star']
                                                        -- 🎉 no goals
#align quaternion_algebra.star_add_self' QuaternionAlgebra.star_add_self'

theorem star_add_self : star a + a = 2 * a.re := by rw [add_comm, self_add_star]
                                                    -- 🎉 no goals
#align quaternion_algebra.star_add_self QuaternionAlgebra.star_add_self

theorem star_eq_two_re_sub : star a = ↑(2 * a.re) - a :=
  eq_sub_iff_add_eq.2 a.star_add_self'
#align quaternion_algebra.star_eq_two_re_sub QuaternionAlgebra.star_eq_two_re_sub

instance : IsStarNormal a :=
  ⟨by
    rw [a.star_eq_two_re_sub]
    -- ⊢ Commute (↑(2 * a.re) - a) a
    exact (coe_commute (2 * a.re) a).sub_left (Commute.refl a)⟩
    -- 🎉 no goals

@[simp, norm_cast]
theorem star_coe : star (x : ℍ[R,c₁,c₂]) = x := by ext <;> simp
                                                           -- 🎉 no goals
                                                           -- 🎉 no goals
                                                           -- 🎉 no goals
                                                           -- 🎉 no goals
#align quaternion_algebra.star_coe QuaternionAlgebra.star_coe

@[simp] theorem star_im : star a.im = -a.im := im_star _
#align quaternion_algebra.star_im QuaternionAlgebra.star_im

@[simp]
theorem star_smul [Monoid S] [DistribMulAction S R] (s : S) (a : ℍ[R,c₁,c₂]) :
    star (s • a) = s • star a :=
  QuaternionAlgebra.ext _ _ rfl (smul_neg _ _).symm (smul_neg _ _).symm (smul_neg _ _).symm
#align quaternion_algebra.star_smul QuaternionAlgebra.star_smul

theorem eq_re_of_eq_coe {a : ℍ[R,c₁,c₂]} {x : R} (h : a = x) : a = a.re := by rw [h, coe_re]
                                                                              -- 🎉 no goals
#align quaternion_algebra.eq_re_of_eq_coe QuaternionAlgebra.eq_re_of_eq_coe

theorem eq_re_iff_mem_range_coe {a : ℍ[R,c₁,c₂]} :
    a = a.re ↔ a ∈ Set.range (coe : R → ℍ[R,c₁,c₂]) :=
  ⟨fun h => ⟨a.re, h.symm⟩, fun ⟨_, h⟩ => eq_re_of_eq_coe h.symm⟩
#align quaternion_algebra.eq_re_iff_mem_range_coe QuaternionAlgebra.eq_re_iff_mem_range_coe

section CharZero

variable [NoZeroDivisors R] [CharZero R]

@[simp]
theorem star_eq_self {c₁ c₂ : R} {a : ℍ[R,c₁,c₂]} : star a = a ↔ a = a.re := by
  simp [QuaternionAlgebra.ext_iff, neg_eq_iff_add_eq_zero, add_self_eq_zero]
  -- 🎉 no goals
#align quaternion_algebra.star_eq_self QuaternionAlgebra.star_eq_self

theorem star_eq_neg {c₁ c₂ : R} {a : ℍ[R,c₁,c₂]} : star a = -a ↔ a.re = 0 := by
  simp [QuaternionAlgebra.ext_iff, eq_neg_iff_add_eq_zero]
  -- 🎉 no goals
#align quaternion_algebra.star_eq_neg QuaternionAlgebra.star_eq_neg

end CharZero

-- Can't use `rw ← star_eq_self` in the proof without additional assumptions
theorem star_mul_eq_coe : star a * a = (star a * a).re := by ext <;> simp <;> ring
                                                                     -- 🎉 no goals
                                                                     -- ⊢ a.re * a.imI + -(a.imI * a.re) + c₂ * a.imJ * a.imK + -(c₂ * a.imK * a.imJ)  …
                                                                     -- ⊢ a.re * a.imJ + -(c₁ * a.imI * a.imK) + -(a.imJ * a.re) + c₁ * a.imK * a.imI  …
                                                                     -- ⊢ a.re * a.imK + -(a.imI * a.imJ) + a.imJ * a.imI + -(a.imK * a.re) = 0
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
#align quaternion_algebra.star_mul_eq_coe QuaternionAlgebra.star_mul_eq_coe

theorem mul_star_eq_coe : a * star a = (a * star a).re := by
  rw [← star_comm_self']
  -- ⊢ star a * a = ↑(star a * a).re
  exact a.star_mul_eq_coe
  -- 🎉 no goals
#align quaternion_algebra.mul_star_eq_coe QuaternionAlgebra.mul_star_eq_coe

open MulOpposite

/-- Quaternion conjugate as an `AlgEquiv` to the opposite ring. -/
def starAe : ℍ[R,c₁,c₂] ≃ₐ[R] ℍ[R,c₁,c₂]ᵐᵒᵖ :=
  { starAddEquiv.trans opAddEquiv with
    toFun := op ∘ star
    invFun := star ∘ unop
    map_mul' := fun x y => by simp
                              -- 🎉 no goals
    commutes' := fun r => by simp }
                             -- 🎉 no goals
#align quaternion_algebra.star_ae QuaternionAlgebra.starAe

@[simp]
theorem coe_starAe : ⇑(starAe : ℍ[R,c₁,c₂] ≃ₐ[R] _) = op ∘ star :=
  rfl
#align quaternion_algebra.coe_star_ae QuaternionAlgebra.coe_starAe

end QuaternionAlgebra

/-- Space of quaternions over a type. Implemented as a structure with four fields:
`re`, `im_i`, `im_j`, and `im_k`. -/
def Quaternion (R : Type*) [One R] [Neg R] :=
  QuaternionAlgebra R (-1) (-1)
#align quaternion Quaternion

-- mathport name: quaternion
scoped[Quaternion] notation "ℍ[" R "]" => Quaternion R

/-- The equivalence between the quaternions over `R` and `R × R × R × R`. -/
@[simps!]
def Quaternion.equivProd (R : Type*) [One R] [Neg R] : ℍ[R] ≃ R × R × R × R :=
  QuaternionAlgebra.equivProd _ _
#align quaternion.equiv_prod Quaternion.equivProd

/-- The equivalence between the quaternions over `R` and `Fin 4 → R`. -/
@[simps! symm_apply]
def Quaternion.equivTuple (R : Type*) [One R] [Neg R] : ℍ[R] ≃ (Fin 4 → R) :=
  QuaternionAlgebra.equivTuple _ _
#align quaternion.equiv_tuple Quaternion.equivTuple

@[simp]
theorem Quaternion.equivTuple_apply (R : Type*) [One R] [Neg R] (x : ℍ[R]) :
    Quaternion.equivTuple R x = ![x.re, x.imI, x.imJ, x.imK] :=
  rfl
#align quaternion.equiv_tuple_apply Quaternion.equivTuple_apply

namespace Quaternion

variable {S T R : Type*} [CommRing R] (r x y z : R) (a b c : ℍ[R])

export QuaternionAlgebra (re imI imJ imK)

/-- Coercion `R → ℍ[R]`. -/
@[coe] def coe : R → ℍ[R] := QuaternionAlgebra.coe

instance : CoeTC R ℍ[R] := ⟨coe⟩

instance instRing : Ring ℍ[R] := QuaternionAlgebra.instRing

instance : Inhabited ℍ[R] := inferInstanceAs <| Inhabited ℍ[R,-1,-1]

instance [SMul S R] : SMul S ℍ[R] := inferInstanceAs <| SMul S ℍ[R,-1,-1]

instance [SMul S T] [SMul S R] [SMul T R] [IsScalarTower S T R] : IsScalarTower S T ℍ[R] :=
  inferInstanceAs <| IsScalarTower S T ℍ[R,-1,-1]

instance [SMul S R] [SMul T R] [SMulCommClass S T R] : SMulCommClass S T ℍ[R] :=
  inferInstanceAs <| SMulCommClass S T ℍ[R,-1,-1]

protected instance algebra [CommSemiring S] [Algebra S R] : Algebra S ℍ[R] :=
  inferInstanceAs <| Algebra S ℍ[R,-1,-1]

-- porting note: added shortcut
instance : Star ℍ[R] := QuaternionAlgebra.instStarQuaternionAlgebra
instance : StarRing ℍ[R] := QuaternionAlgebra.instStarRing
instance : IsStarNormal a := inferInstanceAs <| IsStarNormal (R := ℍ[R,-1,-1]) a

@[ext]
theorem ext : a.re = b.re → a.imI = b.imI → a.imJ = b.imJ → a.imK = b.imK → a = b :=
  QuaternionAlgebra.ext a b
#align quaternion.ext Quaternion.ext

theorem ext_iff {a b : ℍ[R]} :
    a = b ↔ a.re = b.re ∧ a.imI = b.imI ∧ a.imJ = b.imJ ∧ a.imK = b.imK :=
  QuaternionAlgebra.ext_iff a b
#align quaternion.ext_iff Quaternion.ext_iff

/-- The imaginary part of a quaternion. -/
nonrec def im (x : ℍ[R]) : ℍ[R] := x.im
#align quaternion.im Quaternion.im

@[simp] theorem im_re : a.im.re = 0 := rfl
#align quaternion.im_re Quaternion.im_re

@[simp] theorem im_imI : a.im.imI = a.imI := rfl
#align quaternion.im_im_i Quaternion.im_imI

@[simp] theorem im_imJ : a.im.imJ = a.imJ := rfl
#align quaternion.im_im_j Quaternion.im_imJ

@[simp] theorem im_imK : a.im.imK = a.imK := rfl
#align quaternion.im_im_k Quaternion.im_imK

@[simp] theorem im_idem : a.im.im = a.im := rfl
#align quaternion.im_idem Quaternion.im_idem

@[simp] nonrec theorem re_add_im : ↑a.re + a.im = a := a.re_add_im
#align quaternion.re_add_im Quaternion.re_add_im

@[simp] nonrec theorem sub_self_im : a - a.im = a.re := a.sub_self_im
#align quaternion.sub_self_im Quaternion.sub_self_im

@[simp] nonrec theorem sub_self_re : a - ↑a.re = a.im := a.sub_self_re
#align quaternion.sub_self_re Quaternion.sub_self_re

@[simp, norm_cast]
theorem coe_re : (x : ℍ[R]).re = x := rfl
#align quaternion.coe_re Quaternion.coe_re

@[simp, norm_cast]
theorem coe_imI : (x : ℍ[R]).imI = 0 := rfl
#align quaternion.coe_im_i Quaternion.coe_imI

@[simp, norm_cast]
theorem coe_imJ : (x : ℍ[R]).imJ = 0 := rfl
#align quaternion.coe_im_j Quaternion.coe_imJ

@[simp, norm_cast]
theorem coe_imK : (x : ℍ[R]).imK = 0 := rfl
#align quaternion.coe_im_k Quaternion.coe_imK

@[simp, norm_cast]
theorem coe_im : (x : ℍ[R]).im = 0 := rfl
#align quaternion.coe_im Quaternion.coe_im

@[simp] theorem zero_re : (0 : ℍ[R]).re = 0 := rfl
#align quaternion.zero_re Quaternion.zero_re

@[simp] theorem zero_imI : (0 : ℍ[R]).imI = 0 := rfl
#align quaternion.zero_im_i Quaternion.zero_imI

@[simp] theorem zero_imJ : (0 : ℍ[R]).imJ = 0 := rfl
#align quaternion.zero_im_j Quaternion.zero_imJ

@[simp] theorem zero_imK : (0 : ℍ[R]).imK = 0 := rfl
#align quaternion.zero_im_k Quaternion.zero_imK

@[simp] theorem zero_im : (0 : ℍ[R]).im = 0 := rfl
#align quaternion.zero_im Quaternion.zero_im

@[simp, norm_cast]
theorem coe_zero : ((0 : R) : ℍ[R]) = 0 := rfl
#align quaternion.coe_zero Quaternion.coe_zero

@[simp] theorem one_re : (1 : ℍ[R]).re = 1 := rfl
#align quaternion.one_re Quaternion.one_re

@[simp] theorem one_imI : (1 : ℍ[R]).imI = 0 := rfl
#align quaternion.one_im_i Quaternion.one_imI

@[simp] theorem one_imJ : (1 : ℍ[R]).imJ = 0 := rfl
#align quaternion.one_im_j Quaternion.one_imJ

@[simp] theorem one_imK : (1 : ℍ[R]).imK = 0 := rfl
#align quaternion.one_im_k Quaternion.one_imK

@[simp] theorem one_im : (1 : ℍ[R]).im = 0 := rfl
#align quaternion.one_im Quaternion.one_im

@[simp, norm_cast]
theorem coe_one : ((1 : R) : ℍ[R]) = 1 := rfl
#align quaternion.coe_one Quaternion.coe_one

@[simp] theorem add_re : (a + b).re = a.re + b.re := rfl
#align quaternion.add_re Quaternion.add_re

@[simp] theorem add_imI : (a + b).imI = a.imI + b.imI := rfl
#align quaternion.add_im_i Quaternion.add_imI

@[simp] theorem add_imJ : (a + b).imJ = a.imJ + b.imJ := rfl
#align quaternion.add_im_j Quaternion.add_imJ

@[simp] theorem add_imK : (a + b).imK = a.imK + b.imK := rfl
#align quaternion.add_im_k Quaternion.add_imK

@[simp] nonrec theorem add_im : (a + b).im = a.im + b.im := a.add_im b
#align quaternion.add_im Quaternion.add_im

@[simp, norm_cast]
theorem coe_add : ((x + y : R) : ℍ[R]) = x + y :=
  QuaternionAlgebra.coe_add x y
#align quaternion.coe_add Quaternion.coe_add

@[simp] theorem neg_re : (-a).re = -a.re := rfl
#align quaternion.neg_re Quaternion.neg_re

@[simp] theorem neg_imI : (-a).imI = -a.imI := rfl
#align quaternion.neg_im_i Quaternion.neg_imI

@[simp] theorem neg_imJ : (-a).imJ = -a.imJ := rfl
#align quaternion.neg_im_j Quaternion.neg_imJ

@[simp] theorem neg_imK : (-a).imK = -a.imK := rfl
#align quaternion.neg_im_k Quaternion.neg_imK

@[simp] nonrec theorem neg_im : (-a).im = -a.im := a.neg_im
#align quaternion.neg_im Quaternion.neg_im

@[simp, norm_cast]
theorem coe_neg : ((-x : R) : ℍ[R]) = -x :=
  QuaternionAlgebra.coe_neg x
#align quaternion.coe_neg Quaternion.coe_neg

@[simp] theorem sub_re : (a - b).re = a.re - b.re := rfl
#align quaternion.sub_re Quaternion.sub_re

@[simp] theorem sub_imI : (a - b).imI = a.imI - b.imI := rfl
#align quaternion.sub_im_i Quaternion.sub_imI

@[simp] theorem sub_imJ : (a - b).imJ = a.imJ - b.imJ := rfl
#align quaternion.sub_im_j Quaternion.sub_imJ

@[simp] theorem sub_imK : (a - b).imK = a.imK - b.imK := rfl
#align quaternion.sub_im_k Quaternion.sub_imK

@[simp] nonrec theorem sub_im : (a - b).im = a.im - b.im := a.sub_im b
#align quaternion.sub_im Quaternion.sub_im

@[simp, norm_cast]
theorem coe_sub : ((x - y : R) : ℍ[R]) = x - y :=
  QuaternionAlgebra.coe_sub x y
#align quaternion.coe_sub Quaternion.coe_sub

@[simp]
theorem mul_re : (a * b).re = a.re * b.re - a.imI * b.imI - a.imJ * b.imJ - a.imK * b.imK :=
  (QuaternionAlgebra.mul_re a b).trans <| by simp only [one_mul, neg_mul, sub_eq_add_neg, neg_neg]
                                             -- 🎉 no goals
#align quaternion.mul_re Quaternion.mul_re

@[simp]
theorem mul_imI : (a * b).imI = a.re * b.imI + a.imI * b.re + a.imJ * b.imK - a.imK * b.imJ :=
  (QuaternionAlgebra.mul_imI a b).trans <| by simp only [one_mul, neg_mul, sub_eq_add_neg, neg_neg]
                                              -- 🎉 no goals
#align quaternion.mul_im_i Quaternion.mul_imI

@[simp]
theorem mul_imJ : (a * b).imJ = a.re * b.imJ - a.imI * b.imK + a.imJ * b.re + a.imK * b.imI :=
  (QuaternionAlgebra.mul_imJ a b).trans <| by simp only [one_mul, neg_mul, sub_eq_add_neg, neg_neg]
                                              -- 🎉 no goals
#align quaternion.mul_im_j Quaternion.mul_imJ

@[simp]
theorem mul_imK : (a * b).imK = a.re * b.imK + a.imI * b.imJ - a.imJ * b.imI + a.imK * b.re :=
  (QuaternionAlgebra.mul_imK a b).trans <| by simp only [one_mul, neg_mul, sub_eq_add_neg, neg_neg]
                                              -- 🎉 no goals
#align quaternion.mul_im_k Quaternion.mul_imK

@[simp, norm_cast]
theorem coe_mul : ((x * y : R) : ℍ[R]) = x * y := QuaternionAlgebra.coe_mul x y
#align quaternion.coe_mul Quaternion.coe_mul

@[norm_cast, simp]
theorem coe_pow (n : ℕ) : (↑(x ^ n) : ℍ[R]) = (x : ℍ[R]) ^ n :=
  QuaternionAlgebra.coe_pow x n
#align quaternion.coe_pow Quaternion.coe_pow

@[simp, norm_cast]
theorem nat_cast_re (n : ℕ) : (n : ℍ[R]).re = n := rfl
#align quaternion.nat_cast_re Quaternion.nat_cast_re

@[simp, norm_cast]
theorem nat_cast_imI (n : ℕ) : (n : ℍ[R]).imI = 0 := rfl
#align quaternion.nat_cast_im_i Quaternion.nat_cast_imI

@[simp, norm_cast]
theorem nat_cast_imJ (n : ℕ) : (n : ℍ[R]).imJ = 0 := rfl
#align quaternion.nat_cast_im_j Quaternion.nat_cast_imJ

@[simp, norm_cast]
theorem nat_cast_imK (n : ℕ) : (n : ℍ[R]).imK = 0 := rfl
#align quaternion.nat_cast_im_k Quaternion.nat_cast_imK

@[simp, norm_cast]
theorem nat_cast_im (n : ℕ) : (n : ℍ[R]).im = 0 := rfl
#align quaternion.nat_cast_im Quaternion.nat_cast_im

@[norm_cast]
theorem coe_nat_cast (n : ℕ) : ↑(n : R) = (n : ℍ[R]) := rfl
#align quaternion.coe_nat_cast Quaternion.coe_nat_cast

@[simp, norm_cast]
theorem int_cast_re (z : ℤ) : (z : ℍ[R]).re = z := rfl
#align quaternion.int_cast_re Quaternion.int_cast_re

@[simp, norm_cast]
theorem int_cast_imI (z : ℤ) : (z : ℍ[R]).imI = 0 := rfl
#align quaternion.int_cast_im_i Quaternion.int_cast_imI

@[simp, norm_cast]
theorem int_cast_imJ (z : ℤ) : (z : ℍ[R]).imJ = 0 := rfl
#align quaternion.int_cast_im_j Quaternion.int_cast_imJ

@[simp, norm_cast]
theorem int_cast_imK (z : ℤ) : (z : ℍ[R]).imK = 0 := rfl
#align quaternion.int_cast_im_k Quaternion.int_cast_imK

@[simp, norm_cast]
theorem int_cast_im (z : ℤ) : (z : ℍ[R]).im = 0 := rfl
#align quaternion.int_cast_im Quaternion.int_cast_im

@[norm_cast]
theorem coe_int_cast (z : ℤ) : ↑(z : R) = (z : ℍ[R]) := rfl
#align quaternion.coe_int_cast Quaternion.coe_int_cast

theorem coe_injective : Function.Injective (coe : R → ℍ[R]) :=
  QuaternionAlgebra.coe_injective
#align quaternion.coe_injective Quaternion.coe_injective

@[simp]
theorem coe_inj {x y : R} : (x : ℍ[R]) = y ↔ x = y :=
  coe_injective.eq_iff
#align quaternion.coe_inj Quaternion.coe_inj

@[simp]
theorem smul_re [SMul S R] (s : S) : (s • a).re = s • a.re :=
  rfl
#align quaternion.smul_re Quaternion.smul_re

@[simp] theorem smul_imI [SMul S R] (s : S) : (s • a).imI = s • a.imI := rfl
#align quaternion.smul_im_i Quaternion.smul_imI

@[simp] theorem smul_imJ [SMul S R] (s : S) : (s • a).imJ = s • a.imJ := rfl
#align quaternion.smul_im_j Quaternion.smul_imJ

@[simp] theorem smul_imK [SMul S R] (s : S) : (s • a).imK = s • a.imK := rfl
#align quaternion.smul_im_k Quaternion.smul_imK

@[simp]
nonrec theorem smul_im [SMulZeroClass S R] (s : S) : (s • a).im = s • a.im :=
  a.smul_im s
#align quaternion.smul_im Quaternion.smul_im

@[simp, norm_cast]
theorem coe_smul [SMulZeroClass S R] (s : S) (r : R) : (↑(s • r) : ℍ[R]) = s • (r : ℍ[R]) :=
  QuaternionAlgebra.coe_smul _ _
#align quaternion.coe_smul Quaternion.coe_smul

theorem coe_commutes : ↑r * a = a * r :=
  QuaternionAlgebra.coe_commutes r a
#align quaternion.coe_commutes Quaternion.coe_commutes

theorem coe_commute : Commute (↑r) a :=
  QuaternionAlgebra.coe_commute r a
#align quaternion.coe_commute Quaternion.coe_commute

theorem coe_mul_eq_smul : ↑r * a = r • a :=
  QuaternionAlgebra.coe_mul_eq_smul r a
#align quaternion.coe_mul_eq_smul Quaternion.coe_mul_eq_smul

theorem mul_coe_eq_smul : a * r = r • a :=
  QuaternionAlgebra.mul_coe_eq_smul r a
#align quaternion.mul_coe_eq_smul Quaternion.mul_coe_eq_smul

@[simp]
theorem algebraMap_def : ⇑(algebraMap R ℍ[R]) = coe :=
  rfl
#align quaternion.algebra_map_def Quaternion.algebraMap_def

theorem smul_coe : x • (y : ℍ[R]) = ↑(x * y) :=
  QuaternionAlgebra.smul_coe x y
#align quaternion.smul_coe Quaternion.smul_coe

instance : Module.Finite R ℍ[R] := inferInstanceAs <| Module.Finite R ℍ[R,-1,-1]
instance : Module.Free R ℍ[R] := inferInstanceAs <| Module.Free R ℍ[R,-1,-1]

theorem rank_eq_four [StrongRankCondition R] : Module.rank R ℍ[R] = 4 :=
  QuaternionAlgebra.rank_eq_four _ _
#align quaternion.rank_eq_four Quaternion.rank_eq_four

theorem finrank_eq_four [StrongRankCondition R] : FiniteDimensional.finrank R ℍ[R] = 4 :=
  QuaternionAlgebra.finrank_eq_four _ _
#align quaternion.finrank_eq_four Quaternion.finrank_eq_four

@[simp] theorem star_re : (star a).re = a.re := rfl
#align quaternion.star_re Quaternion.star_re

@[simp] theorem star_imI : (star a).imI = -a.imI := rfl
#align quaternion.star_im_i Quaternion.star_imI

@[simp] theorem star_imJ : (star a).imJ = -a.imJ := rfl
#align quaternion.star_im_j Quaternion.star_imJ

@[simp] theorem star_imK : (star a).imK = -a.imK := rfl
#align quaternion.star_im_k Quaternion.star_imK

@[simp] theorem star_im : (star a).im = -a.im := a.im_star
#align quaternion.star_im Quaternion.star_im

nonrec theorem self_add_star' : a + star a = ↑(2 * a.re) :=
  a.self_add_star'
#align quaternion.self_add_star' Quaternion.self_add_star'

nonrec theorem self_add_star : a + star a = 2 * a.re :=
  a.self_add_star
#align quaternion.self_add_star Quaternion.self_add_star

nonrec theorem star_add_self' : star a + a = ↑(2 * a.re) :=
  a.star_add_self'
#align quaternion.star_add_self' Quaternion.star_add_self'

nonrec theorem star_add_self : star a + a = 2 * a.re :=
  a.star_add_self
#align quaternion.star_add_self Quaternion.star_add_self

nonrec theorem star_eq_two_re_sub : star a = ↑(2 * a.re) - a :=
  a.star_eq_two_re_sub
#align quaternion.star_eq_two_re_sub Quaternion.star_eq_two_re_sub

@[simp, norm_cast]
theorem star_coe : star (x : ℍ[R]) = x :=
  QuaternionAlgebra.star_coe x
#align quaternion.star_coe Quaternion.star_coe

@[simp]
theorem im_star : star a.im = -a.im :=
  QuaternionAlgebra.im_star _
#align quaternion.im_star Quaternion.im_star

@[simp]
theorem star_smul [Monoid S] [DistribMulAction S R] (s : S) (a : ℍ[R]) :
    star (s • a) = s • star a :=
  QuaternionAlgebra.star_smul _ _
#align quaternion.star_smul Quaternion.star_smul

theorem eq_re_of_eq_coe {a : ℍ[R]} {x : R} (h : a = x) : a = a.re :=
  QuaternionAlgebra.eq_re_of_eq_coe h
#align quaternion.eq_re_of_eq_coe Quaternion.eq_re_of_eq_coe

theorem eq_re_iff_mem_range_coe {a : ℍ[R]} : a = a.re ↔ a ∈ Set.range (coe : R → ℍ[R]) :=
  QuaternionAlgebra.eq_re_iff_mem_range_coe
#align quaternion.eq_re_iff_mem_range_coe Quaternion.eq_re_iff_mem_range_coe

section CharZero

variable [NoZeroDivisors R] [CharZero R]

@[simp]
theorem star_eq_self {a : ℍ[R]} : star a = a ↔ a = a.re :=
  QuaternionAlgebra.star_eq_self
#align quaternion.star_eq_self Quaternion.star_eq_self

@[simp]
theorem star_eq_neg {a : ℍ[R]} : star a = -a ↔ a.re = 0 :=
  QuaternionAlgebra.star_eq_neg
#align quaternion.star_eq_neg Quaternion.star_eq_neg

end CharZero

nonrec theorem star_mul_eq_coe : star a * a = (star a * a).re :=
  a.star_mul_eq_coe
#align quaternion.star_mul_eq_coe Quaternion.star_mul_eq_coe

nonrec theorem mul_star_eq_coe : a * star a = (a * star a).re :=
  a.mul_star_eq_coe
#align quaternion.mul_star_eq_coe Quaternion.mul_star_eq_coe

open MulOpposite

/-- Quaternion conjugate as an `AlgEquiv` to the opposite ring. -/
def starAe : ℍ[R] ≃ₐ[R] ℍ[R]ᵐᵒᵖ :=
  QuaternionAlgebra.starAe
#align quaternion.star_ae Quaternion.starAe

@[simp]
theorem coe_starAe : ⇑(starAe : ℍ[R] ≃ₐ[R] ℍ[R]ᵐᵒᵖ) = op ∘ star :=
  rfl
#align quaternion.coe_star_ae Quaternion.coe_starAe

/-- Square of the norm. -/
def normSq : ℍ[R] →*₀ R where
  toFun a := (a * star a).re
  map_zero' := by simp only [star_zero, zero_mul, zero_re]
                  -- 🎉 no goals
  map_one' := by simp only [star_one, one_mul, one_re]
                 -- 🎉 no goals
  map_mul' x y := coe_injective <| by
    conv_lhs => rw [← mul_star_eq_coe, star_mul, mul_assoc, ← mul_assoc y, y.mul_star_eq_coe,
      coe_commutes, ← mul_assoc, x.mul_star_eq_coe, ← coe_mul]
#align quaternion.norm_sq Quaternion.normSq

theorem normSq_def : normSq a = (a * star a).re := rfl
#align quaternion.norm_sq_def Quaternion.normSq_def

theorem normSq_def' : normSq a = a.1 ^ 2 + a.2 ^ 2 + a.3 ^ 2 + a.4 ^ 2 := by
  simp only [normSq_def, sq, mul_neg, sub_neg_eq_add, mul_re, star_re, star_imI, star_imJ,
    star_imK]
#align quaternion.norm_sq_def' Quaternion.normSq_def'

theorem normSq_coe : normSq (x : ℍ[R]) = x ^ 2 := by
  rw [normSq_def, star_coe, ← coe_mul, coe_re, sq]
  -- 🎉 no goals
#align quaternion.norm_sq_coe Quaternion.normSq_coe

@[simp]
theorem normSq_star : normSq (star a) = normSq a := by simp [normSq_def']
                                                       -- 🎉 no goals
#align quaternion.norm_sq_star Quaternion.normSq_star

@[norm_cast]
theorem normSq_nat_cast (n : ℕ) : normSq (n : ℍ[R]) = (n : R) ^ 2 := by
  rw [← coe_nat_cast, normSq_coe]
  -- 🎉 no goals
#align quaternion.norm_sq_nat_cast Quaternion.normSq_nat_cast

@[norm_cast]
theorem normSq_int_cast (z : ℤ) : normSq (z : ℍ[R]) = (z : R) ^ 2 := by
  rw [← coe_int_cast, normSq_coe]
  -- 🎉 no goals
#align quaternion.norm_sq_int_cast Quaternion.normSq_int_cast

@[simp]
theorem normSq_neg : normSq (-a) = normSq a := by simp only [normSq_def, star_neg, neg_mul_neg]
                                                  -- 🎉 no goals
#align quaternion.norm_sq_neg Quaternion.normSq_neg

theorem self_mul_star : a * star a = normSq a := by rw [mul_star_eq_coe, normSq_def]
                                                    -- 🎉 no goals
#align quaternion.self_mul_star Quaternion.self_mul_star

theorem star_mul_self : star a * a = normSq a := by rw [star_comm_self, self_mul_star]
                                                    -- 🎉 no goals
#align quaternion.star_mul_self Quaternion.star_mul_self

theorem im_sq : a.im ^ 2 = -normSq a.im := by
  simp_rw [sq, ← star_mul_self, im_star, neg_mul, neg_neg]
  -- 🎉 no goals
#align quaternion.im_sq Quaternion.im_sq

theorem coe_normSq_add : (normSq (a + b) : ℍ[R]) = normSq a + a * star b + b * star a + normSq b :=
  by simp only [star_add, ← self_mul_star, mul_add, add_mul, add_assoc, add_left_comm]
     -- 🎉 no goals
#align quaternion.coe_norm_sq_add Quaternion.coe_normSq_add

theorem normSq_smul (r : R) (q : ℍ[R]) : normSq (r • q) = r ^ 2 * normSq q := by
  simp only [normSq_def', smul_re, smul_imI, smul_imJ, smul_imK, mul_pow, mul_add, smul_eq_mul]
  -- 🎉 no goals
#align quaternion.norm_sq_smul Quaternion.normSq_smul

theorem normSq_add (a b : ℍ[R]) : normSq (a + b) = normSq a + normSq b + 2 * (a * star b).re :=
  calc
    normSq (a + b) = normSq a + (a * star b).re + ((b * star a).re + normSq b) := by
      simp_rw [normSq_def, star_add, add_mul, mul_add, add_re]
      -- 🎉 no goals
    _ = normSq a + normSq b + ((a * star b).re + (b * star a).re) := by abel
                                                                        -- 🎉 no goals
                                                                        -- 🎉 no goals
    _ = normSq a + normSq b + 2 * (a * star b).re := by
      rw [← add_re, ← star_mul_star a b, self_add_star', coe_re]
      -- 🎉 no goals
#align quaternion.norm_sq_add Quaternion.normSq_add

end Quaternion

namespace Quaternion

variable {R : Type*}

section LinearOrderedCommRing

variable [LinearOrderedCommRing R] {a : ℍ[R]}

@[simp]
theorem normSq_eq_zero : normSq a = 0 ↔ a = 0 := by
  refine' ⟨fun h => _, fun h => h.symm ▸ normSq.map_zero⟩
  -- ⊢ a = 0
  rw [normSq_def', add_eq_zero_iff', add_eq_zero_iff', add_eq_zero_iff'] at h
  exact ext a 0 (pow_eq_zero h.1.1.1) (pow_eq_zero h.1.1.2) (pow_eq_zero h.1.2) (pow_eq_zero h.2)
  all_goals apply_rules [sq_nonneg, add_nonneg]
  -- 🎉 no goals
#align quaternion.norm_sq_eq_zero Quaternion.normSq_eq_zero

theorem normSq_ne_zero : normSq a ≠ 0 ↔ a ≠ 0 := normSq_eq_zero.not
#align quaternion.norm_sq_ne_zero Quaternion.normSq_ne_zero

@[simp]
theorem normSq_nonneg : 0 ≤ normSq a := by
  rw [normSq_def']
  -- ⊢ 0 ≤ a.re ^ 2 + a.imI ^ 2 + a.imJ ^ 2 + a.imK ^ 2
  apply_rules [sq_nonneg, add_nonneg]
  -- 🎉 no goals
#align quaternion.norm_sq_nonneg Quaternion.normSq_nonneg

@[simp]
theorem normSq_le_zero : normSq a ≤ 0 ↔ a = 0 :=
  normSq_nonneg.le_iff_eq.trans normSq_eq_zero
#align quaternion.norm_sq_le_zero Quaternion.normSq_le_zero

instance instNontrivial : Nontrivial ℍ[R] where
  exists_pair_ne := ⟨0, 1, mt (congr_arg re) zero_ne_one⟩

instance : NoZeroDivisors ℍ[R] where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} hab :=
    have : normSq a * normSq b = 0 := by rwa [← map_mul, normSq_eq_zero]
                                         -- 🎉 no goals
    (eq_zero_or_eq_zero_of_mul_eq_zero this).imp normSq_eq_zero.1 normSq_eq_zero.1

instance : IsDomain ℍ[R] := NoZeroDivisors.to_isDomain _

theorem sq_eq_normSq : a ^ 2 = normSq a ↔ a = a.re := by
  rw [← star_eq_self, ← star_mul_self, sq, mul_eq_mul_right_iff, eq_comm]
  -- ⊢ star a = a ∨ a = 0 ↔ star a = a
  exact or_iff_left_of_imp fun ha ↦ ha.symm ▸ star_zero _
  -- 🎉 no goals
#align quaternion.sq_eq_norm_sq Quaternion.sq_eq_normSq

theorem sq_eq_neg_normSq : a ^ 2 = -normSq a ↔ a.re = 0 := by
  simp_rw [← star_eq_neg]
  -- ⊢ a ^ 2 = -↑(↑normSq a) ↔ star a = -a
  obtain rfl | hq0 := eq_or_ne a 0
  -- ⊢ 0 ^ 2 = -↑(↑normSq 0) ↔ star 0 = -0
  · simp
    -- 🎉 no goals
  · rw [← star_mul_self, ← mul_neg, ← neg_sq, sq, mul_left_inj' (neg_ne_zero.mpr hq0), eq_comm]
    -- 🎉 no goals
#align quaternion.sq_eq_neg_norm_sq Quaternion.sq_eq_neg_normSq

end LinearOrderedCommRing

section Field

variable [LinearOrderedField R] (a b : ℍ[R])

@[simps (config := { isSimp := false })]
instance instInv : Inv ℍ[R] :=
  ⟨fun a => (normSq a)⁻¹ • star a⟩

instance instGroupWithZero : GroupWithZero ℍ[R] :=
  { Quaternion.instNontrivial,
    (by infer_instance : MonoidWithZero ℍ[R]) with
        -- 🎉 no goals
    inv := Inv.inv
    inv_zero := by rw [instInv_inv, star_zero, smul_zero]
                   -- 🎉 no goals
    mul_inv_cancel := fun a ha => by
      -- porting note: the aliased definition confuse TC search
      letI : Semiring ℍ[R] := inferInstanceAs (Semiring ℍ[R,-1,-1])
      -- ⊢ a * a⁻¹ = 1
      rw [instInv_inv, Algebra.mul_smul_comm (normSq a)⁻¹ a (star a), self_mul_star, smul_coe,
        inv_mul_cancel (normSq_ne_zero.2 ha), coe_one] }

@[norm_cast, simp]
theorem coe_inv (x : R) : ((x⁻¹ : R) : ℍ[R]) = (↑x)⁻¹ :=
  map_inv₀ (algebraMap R ℍ[R]) _
#align quaternion.coe_inv Quaternion.coe_inv

@[norm_cast, simp]
theorem coe_div (x y : R) : ((x / y : R) : ℍ[R]) = x / y :=
  map_div₀ (algebraMap R ℍ[R]) x y
#align quaternion.coe_div Quaternion.coe_div

@[norm_cast, simp]
theorem coe_zpow (x : R) (z : ℤ) : ((x ^ z : R) : ℍ[R]) = (x : ℍ[R]) ^ z :=
  map_zpow₀ (algebraMap R ℍ[R]) x z
#align quaternion.coe_zpow Quaternion.coe_zpow

-- porting note: split from `DivisionRing` instance
instance : RatCast ℍ[R] where
  ratCast := fun q => ↑(q : R)

@[simp, norm_cast]
theorem rat_cast_re (q : ℚ) : (q : ℍ[R]).re = q :=
  rfl
#align quaternion.rat_cast_re Quaternion.rat_cast_re

@[simp, norm_cast]
theorem rat_cast_imI (q : ℚ) : (q : ℍ[R]).imI = 0 :=
  rfl
#align quaternion.rat_cast_im_i Quaternion.rat_cast_imI

@[simp, norm_cast]
theorem rat_cast_imJ (q : ℚ) : (q : ℍ[R]).imJ = 0 :=
  rfl
#align quaternion.rat_cast_im_j Quaternion.rat_cast_imJ

@[simp, norm_cast]
theorem rat_cast_imK (q : ℚ) : (q : ℍ[R]).imK = 0 :=
  rfl
#align quaternion.rat_cast_im_k Quaternion.rat_cast_imK

@[simp, norm_cast]
theorem rat_cast_im (q : ℚ) : (q : ℍ[R]).im = 0 :=
  rfl
#align quaternion.rat_cast_im Quaternion.rat_cast_im

@[norm_cast]
theorem coe_rat_cast (q : ℚ) : ↑(q : R) = (q : ℍ[R]) :=
  rfl
#align quaternion.coe_rat_cast Quaternion.coe_rat_cast

-- porting note: moved below `coe_rat_cast`, as `coe_rat_cast` is needed in the `rw`s
instance : DivisionRing ℍ[R] :=
  { Quaternion.instGroupWithZero,
    Quaternion.instRing with
    ratCast_mk := fun n d hd h => by
      rw [←coe_rat_cast, Rat.cast_mk', coe_mul, coe_int_cast, coe_inv, coe_nat_cast]
      -- 🎉 no goals
    qsmul := (· • ·)
    qsmul_eq_mul' := fun q x => by
      rw [←coe_rat_cast, coe_mul_eq_smul]
      -- ⊢ (fun x x_1 => x • x_1) q x = ↑q • x
      ext <;> exact DivisionRing.qsmul_eq_mul' _ _ }
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals

--@[simp] Porting note: `simp` can prove it
theorem normSq_inv : normSq a⁻¹ = (normSq a)⁻¹ :=
  map_inv₀ normSq _
#align quaternion.norm_sq_inv Quaternion.normSq_inv

--@[simp] Porting note: `simp` can prove it
theorem normSq_div : normSq (a / b) = normSq a / normSq b :=
  map_div₀ normSq a b
#align quaternion.norm_sq_div Quaternion.normSq_div

--@[simp] Porting note: `simp` can prove it
theorem normSq_zpow (z : ℤ) : normSq (a ^ z) = normSq a ^ z :=
  map_zpow₀ normSq a z
#align quaternion.norm_sq_zpow Quaternion.normSq_zpow

@[norm_cast]
theorem normSq_rat_cast (q : ℚ) : normSq (q : ℍ[R]) = (q : ℍ[R]) ^ 2 := by
  rw [← coe_rat_cast, normSq_coe, coe_pow]
  -- 🎉 no goals
#align quaternion.norm_sq_rat_cast Quaternion.normSq_rat_cast

end Field

end Quaternion

namespace Cardinal

open Quaternion

local infixr:80 " ^ℕ " => @HPow.hPow Cardinal ℕ Cardinal _

section QuaternionAlgebra

variable {R : Type*} (c₁ c₂ : R)

private theorem pow_four [Infinite R] : #R ^ℕ 4 = #R :=
  power_nat_eq (aleph0_le_mk R) <| by simp
                                      -- 🎉 no goals

/-- The cardinality of a quaternion algebra, as a type. -/
theorem mk_quaternionAlgebra : #(ℍ[R,c₁,c₂]) = #R ^ℕ 4 := by
  rw [mk_congr (QuaternionAlgebra.equivProd c₁ c₂)]
  -- ⊢ #(R × R × R × R) = #R ^ 4
  simp only [mk_prod, lift_id]
  -- ⊢ #R * (#R * (#R * #R)) = #R ^ 4
  ring
  -- 🎉 no goals
#align cardinal.mk_quaternion_algebra Cardinal.mk_quaternionAlgebra

@[simp]
theorem mk_quaternionAlgebra_of_infinite [Infinite R] : #(ℍ[R,c₁,c₂]) = #R := by
  rw [mk_quaternionAlgebra, pow_four]
  -- 🎉 no goals
#align cardinal.mk_quaternion_algebra_of_infinite Cardinal.mk_quaternionAlgebra_of_infinite

/-- The cardinality of a quaternion algebra, as a set. -/
theorem mk_univ_quaternionAlgebra : #(Set.univ : Set ℍ[R,c₁,c₂]) = #R ^ℕ 4 := by
  rw [mk_univ, mk_quaternionAlgebra]
  -- 🎉 no goals
#align cardinal.mk_univ_quaternion_algebra Cardinal.mk_univ_quaternionAlgebra

--@[simp] Porting note: `simp` can prove it
theorem mk_univ_quaternionAlgebra_of_infinite [Infinite R] :
    #(Set.univ : Set ℍ[R,c₁,c₂]) = #R := by rw [mk_univ_quaternionAlgebra, pow_four]
                                            -- 🎉 no goals
#align cardinal.mk_univ_quaternion_algebra_of_infinite Cardinal.mk_univ_quaternionAlgebra_of_infinite

end QuaternionAlgebra

section Quaternion

variable (R : Type*) [One R] [Neg R]

/-- The cardinality of the quaternions, as a type. -/
@[simp]
theorem mk_quaternion : #(ℍ[R]) = #R ^ℕ 4 :=
  mk_quaternionAlgebra _ _
#align cardinal.mk_quaternion Cardinal.mk_quaternion

--@[simp] Porting note: LHS can be simplified to `#R^4`
theorem mk_quaternion_of_infinite [Infinite R] : #(ℍ[R]) = #R :=
  mk_quaternionAlgebra_of_infinite _ _
#align cardinal.mk_quaternion_of_infinite Cardinal.mk_quaternion_of_infinite

/-- The cardinality of the quaternions, as a set. -/
--@[simp] Porting note: `simp` can prove it
theorem mk_univ_quaternion : #(Set.univ : Set ℍ[R]) = #R ^ℕ 4 :=
  mk_univ_quaternionAlgebra _ _
#align cardinal.mk_univ_quaternion Cardinal.mk_univ_quaternion

--@[simp] Porting note: LHS can be simplified to `#R^4`
theorem mk_univ_quaternion_of_infinite [Infinite R] : #(Set.univ : Set ℍ[R]) = #R :=
  mk_univ_quaternionAlgebra_of_infinite _ _
#align cardinal.mk_univ_quaternion_of_infinite Cardinal.mk_univ_quaternion_of_infinite

end Quaternion

end Cardinal
