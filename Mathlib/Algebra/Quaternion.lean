/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Star.SelfAdjoint

import Mathlib.Algebra.Module.Torsion.Prod
public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Algebra.Ring.Action.Rat
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public meta import Mathlib.Tactic.Basic
public meta import Mathlib.Tactic.ToAdditive
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Ring.CharZero
import Mathlib.Algebra.Ring.Commute
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Logic.Nontrivial.Basic
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SetLike

/-!
# Quaternions

In this file we define quaternions `ℍ[R]` over a commutative ring `R`, and define some
algebraic structures on `ℍ[R]`.

## Main definitions

* `QuaternionAlgebra R a b c`, `ℍ[R, a, b, c]` :
  [Bourbaki, *Algebra I*][bourbaki1989] with coefficients `a`, `b`, `c`
  (Many other references such as Wikipedia assume $\operatorname{char} R ≠ 2$ therefore one can
  complete the square and WLOG assume $b = 0$.)
* `Quaternion R`, `ℍ[R]` : the space of quaternions, a.k.a.
  `QuaternionAlgebra R (-1) (0) (-1)`;
* `Quaternion.normSq` : square of the norm of a quaternion;

We also define the following algebraic structures on `ℍ[R]`:

* `Ring ℍ[R, a, b, c]`, `StarRing ℍ[R, a, b, c]`, and `Algebra R ℍ[R, a, b, c]` :
  for any commutative ring `R`;
* `Ring ℍ[R]`, `StarRing ℍ[R]`, and `Algebra R ℍ[R]` : for any commutative ring `R`;
* `IsDomain ℍ[R]` : for a linear ordered commutative ring `R`;
* `DivisionRing ℍ[R]` : for a linear ordered field `R`.

## Notation

The following notation is available with `open Quaternion` or `open scoped Quaternion`.

* `ℍ[R,c₁,c₂,c₃]` : `QuaternionAlgebra R c₁ c₂ c₃`
* `ℍ[R,c₁,c₂]` : `QuaternionAlgebra R c₁ 0 c₂`
* `ℍ[R]` : quaternions over `R`.

## Implementation notes

We define quaternions over any ring `R`, not just `ℝ` to be able to deal with, e.g., integer
or rational quaternions without using real numbers. In particular, all definitions in this file
are computable.

## Tags

quaternion
-/

@[expose] public section

open Module

/-- Quaternion algebra over a type with fixed coefficients where $i^2 = a + bi$ and $j^2 = c$,
denoted as `ℍ[R,a,b]`.
Implemented as a structure with four fields: `re`, `imI`, `imJ`, and `imK`. -/
@[ext]
structure QuaternionAlgebra (R : Type*) (a b c : R) where
  /-- Real part of a quaternion. -/
  re : R
  /-- First imaginary part (i) of a quaternion. -/
  imI : R
  /-- Second imaginary part (j) of a quaternion. -/
  imJ : R
  /-- Third imaginary part (k) of a quaternion. -/
  imK : R

initialize_simps_projections QuaternionAlgebra
  (as_prefix re, as_prefix imI, as_prefix imJ, as_prefix imK)

@[inherit_doc]
scoped[Quaternion] notation "ℍ[" R "," a "," b "," c "]" =>
    QuaternionAlgebra R a b c

@[inherit_doc]
scoped[Quaternion] notation "ℍ[" R "," a "," b "]" => QuaternionAlgebra R a 0 b

namespace QuaternionAlgebra
open Quaternion

/-- The equivalence between a quaternion algebra over `R` and `R × R × R × R`. -/
@[simps]
def equivProd {R : Type*} (c₁ c₂ c₃ : R) : ℍ[R,c₁,c₂,c₃] ≃ R × R × R × R where
  toFun a := ⟨a.1, a.2, a.3, a.4⟩
  invFun a := ⟨a.1, a.2.1, a.2.2.1, a.2.2.2⟩

/-- The equivalence between a quaternion algebra over `R` and `Fin 4 → R`. -/
@[simps symm_apply]
def equivTuple {R : Type*} (c₁ c₂ c₃ : R) : ℍ[R,c₁,c₂,c₃] ≃ (Fin 4 → R) where
  toFun a := ![a.1, a.2, a.3, a.4]
  invFun a := ⟨a 0, a 1, a 2, a 3⟩
  right_inv _ := by ext ⟨_, _ | _ | _ | _ | _ | ⟨⟩⟩ <;> rfl

@[simp]
theorem equivTuple_apply {R : Type*} (c₁ c₂ c₃ : R) (x : ℍ[R,c₁,c₂,c₃]) :
    equivTuple c₁ c₂ c₃ x = ![x.re, x.imI, x.imJ, x.imK] :=
  rfl

@[simp]
theorem mk.eta {R : Type*} {c₁ c₂ c₃} (a : ℍ[R,c₁,c₂,c₃]) : mk a.1 a.2 a.3 a.4 = a := rfl

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

instance [Subsingleton R] : Subsingleton ℍ[R,c₁,c₂,c₃] := (equivTuple c₁ c₂ c₃).subsingleton
instance [Nontrivial R] : Nontrivial ℍ[R,c₁,c₂,c₃] := (equivTuple c₁ c₂ c₃).surjective.nontrivial

section Zero
variable [Zero R]

/-- The imaginary part of a quaternion.

Note that unless `c₂ = 0`, this definition is not particularly well-behaved;
for instance, `QuaternionAlgebra.star_im` only says that the star of an imaginary quaternion
is imaginary under this condition. -/
def im (x : ℍ[R,c₁,c₂,c₃]) : ℍ[R,c₁,c₂,c₃] :=
  ⟨0, x.imI, x.imJ, x.imK⟩

@[simp]
theorem re_im : a.im.re = 0 :=
  rfl

@[simp]
theorem imI_im : a.im.imI = a.imI :=
  rfl

@[simp]
theorem imJ_im : a.im.imJ = a.imJ :=
  rfl

@[simp]
theorem imK_im : a.im.imK = a.imK :=
  rfl

@[simp]
theorem im_idem : a.im.im = a.im :=
  rfl

/-- Coercion `R → ℍ[R,c₁,c₂,c₃]`. -/
@[coe] def coe (x : R) : ℍ[R,c₁,c₂,c₃] := ⟨x, 0, 0, 0⟩

instance : CoeTC R ℍ[R,c₁,c₂,c₃] := ⟨coe⟩

@[simp, norm_cast]
theorem re_coe : (x : ℍ[R,c₁,c₂,c₃]).re = x := rfl

@[simp, norm_cast]
theorem imI_coe : (x : ℍ[R,c₁,c₂,c₃]).imI = 0 := rfl

@[simp, norm_cast]
theorem imJ_coe : (x : ℍ[R,c₁,c₂,c₃]).imJ = 0 := rfl

@[simp, norm_cast]
theorem imK_coe : (x : ℍ[R,c₁,c₂,c₃]).imK = 0 := rfl

theorem coe_injective : Function.Injective (coe : R → ℍ[R,c₁,c₂,c₃]) := fun _ _ h => congr_arg re h

@[simp]
theorem coe_inj {x y : R} : (x : ℍ[R,c₁,c₂,c₃]) = y ↔ x = y :=
  coe_injective.eq_iff

@[simps]
instance : Zero ℍ[R,c₁,c₂,c₃] := ⟨⟨0, 0, 0, 0⟩⟩

@[scoped simp] theorem im_zero : (0 : ℍ[R,c₁,c₂,c₃]).im = 0 := rfl

@[simp, norm_cast]
theorem coe_zero : ((0 : R) : ℍ[R,c₁,c₂,c₃]) = 0 := rfl

instance : Inhabited ℍ[R,c₁,c₂,c₃] := ⟨0⟩

section One
variable [One R]

@[simps]
instance : One ℍ[R,c₁,c₂,c₃] := ⟨⟨1, 0, 0, 0⟩⟩

@[scoped simp] theorem im_one : (1 : ℍ[R,c₁,c₂,c₃]).im = 0 := rfl

@[simp, norm_cast]
theorem coe_one : ((1 : R) : ℍ[R,c₁,c₂,c₃]) = 1 := rfl

end One
end Zero
section Add
variable [Add R]

@[simps]
instance : Add ℍ[R,c₁,c₂,c₃] :=
  ⟨fun a b => ⟨a.1 + b.1, a.2 + b.2, a.3 + b.3, a.4 + b.4⟩⟩

@[simp]
theorem mk_add_mk (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R) :
    (mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃]) + mk b₁ b₂ b₃ b₄ =
    mk (a₁ + b₁) (a₂ + b₂) (a₃ + b₃) (a₄ + b₄) :=
  rfl

/-- The additive equivalence between a quaternion algebra over `R` and `Fin 4 → R`. -/
def addEquivTuple (c₁ c₂ c₃ : R) : ℍ[R,c₁,c₂,c₃] ≃+ (Fin 4 → R) := (equivTuple ..).addEquiv

@[simp]
lemma coe_addEquivTuple (c₁ c₂ c₃ : R) : ⇑(addEquivTuple c₁ c₂ c₃) = equivTuple c₁ c₂ c₃ := rfl

@[simp] lemma coe_symm_addEquivTuple (c₁ c₂ c₃ : R) :
    ⇑(addEquivTuple c₁ c₂ c₃).symm = (equivTuple c₁ c₂ c₃).symm := rfl

/-- The additive equivalence between a quaternion algebra over `R` and `R × R × R × R`. -/
def addEquivProd (c₁ c₂ c₃ : R) : ℍ[R,c₁,c₂,c₃] ≃+ R × R × R × R := (equivProd ..).addEquiv

@[simp]
lemma coe_addEquivProd (c₁ c₂ c₃ : R) : ⇑(addEquivProd c₁ c₂ c₃) = equivProd c₁ c₂ c₃ := rfl

@[simp] lemma coe_symm_addEquivProd (c₁ c₂ c₃ : R) :
    ⇑(addEquivProd c₁ c₂ c₃).symm = (equivProd c₁ c₂ c₃).symm := rfl

end Add

section AddZeroClass
variable [AddZeroClass R]

@[simp] theorem im_add : (a + b).im = a.im + b.im :=
  QuaternionAlgebra.ext (zero_add _).symm rfl rfl rfl

@[simp, norm_cast]
theorem coe_add : ((x + y : R) : ℍ[R,c₁,c₂,c₃]) = x + y := by ext <;> simp

end AddZeroClass

section Neg
variable [Neg R]

@[simps]
instance : Neg ℍ[R,c₁,c₂,c₃] := ⟨fun a => ⟨-a.1, -a.2, -a.3, -a.4⟩⟩

@[simp]
theorem neg_mk (a₁ a₂ a₃ a₄ : R) : -(mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃]) = ⟨-a₁, -a₂, -a₃, -a₄⟩ :=
  rfl

end Neg

section AddGroup
variable [AddGroup R]

@[simp] theorem im_neg : (-a).im = -a.im :=
  QuaternionAlgebra.ext neg_zero.symm rfl rfl rfl

@[simp, norm_cast]
theorem coe_neg : ((-x : R) : ℍ[R,c₁,c₂,c₃]) = -x := by ext <;> simp

@[simps]
instance : Sub ℍ[R,c₁,c₂,c₃] :=
  ⟨fun a b => ⟨a.1 - b.1, a.2 - b.2, a.3 - b.3, a.4 - b.4⟩⟩

@[simp] theorem im_sub : (a - b).im = a.im - b.im :=
  QuaternionAlgebra.ext (sub_zero _).symm rfl rfl rfl

@[simp]
theorem mk_sub_mk (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R) :
    (mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃]) - mk b₁ b₂ b₃ b₄ =
    mk (a₁ - b₁) (a₂ - b₂) (a₃ - b₃) (a₄ - b₄) :=
  rfl

@[simp, norm_cast]
theorem im_coe : (x : ℍ[R,c₁,c₂,c₃]).im = 0 :=
  rfl

@[simp]
theorem re_add_im : ↑a.re + a.im = a :=
  QuaternionAlgebra.ext (add_zero _) (zero_add _) (zero_add _) (zero_add _)

@[simp]
theorem sub_im_self : a - a.im = a.re :=
  QuaternionAlgebra.ext (sub_zero _) (sub_self _) (sub_self _) (sub_self _)

@[simp]
theorem sub_re_self : a - a.re = a.im :=
  QuaternionAlgebra.ext (sub_self _) (sub_zero _) (sub_zero _) (sub_zero _)

end AddGroup

section Ring
variable [Ring R]

/-- Multiplication is given by

* `1 * x = x * 1 = x`;
* `i * i = c₁ + c₂ * i`;
* `j * j = c₃`;
* `i * j = k`, `j * i = c₂ * j - k`;
* `k * k = - c₁ * c₃`;
* `i * k = c₁ * j + c₂ * k`, `k * i = -c₁ * j`;
* `j * k = c₂ * c₃ - c₃ * i`, `k * j = c₃ * i`. -/
@[simps]
instance : Mul ℍ[R,c₁,c₂,c₃] :=
  ⟨fun a b =>
    ⟨a.1 * b.1 + c₁ * a.2 * b.2 + c₃ * a.3 * b.3 + c₂ * c₃ * a.3 * b.4 - c₁ * c₃ * a.4 * b.4,
      a.1 * b.2 + a.2 * b.1 + c₂ * a.2 * b.2 - c₃ * a.3 * b.4 + c₃ * a.4 * b.3,
      a.1 * b.3 + c₁ * a.2 * b.4 + a.3 * b.1 + c₂ * a.3 * b.2 - c₁ * a.4 * b.2,
      a.1 * b.4 + a.2 * b.3 + c₂ * a.2 * b.4 - a.3 * b.2 + a.4 * b.1⟩⟩

@[simp]
theorem mk_mul_mk (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R) :
    (mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃]) * mk b₁ b₂ b₃ b₄ =
    mk
      (a₁ * b₁ + c₁ * a₂ * b₂ + c₃ * a₃ * b₃ + c₂ * c₃ * a₃ * b₄ - c₁ * c₃ * a₄ * b₄)
      (a₁ * b₂ + a₂ * b₁ + c₂ * a₂ * b₂ - c₃ * a₃ * b₄ + c₃ * a₄ * b₃)
      (a₁ * b₃ + c₁ * a₂ * b₄ + a₃ * b₁ + c₂ * a₃ * b₂ - c₁ * a₄ * b₂)
      (a₁ * b₄ + a₂ * b₃ + c₂ * a₂ * b₄ - a₃ * b₂ + a₄ * b₁) :=
  rfl

end Ring
section SMul

variable [SMul S R] [SMul T R] (s : S)

@[simps]
instance : SMul S ℍ[R,c₁,c₂,c₃] where smul s a := ⟨s • a.1, s • a.2, s • a.3, s • a.4⟩

instance [SMul S T] [IsScalarTower S T R] : IsScalarTower S T ℍ[R,c₁,c₂,c₃] where
  smul_assoc s t x := by ext <;> exact smul_assoc _ _ _

instance [SMulCommClass S T R] : SMulCommClass S T ℍ[R,c₁,c₂,c₃] where
  smul_comm s t x := by ext <;> exact smul_comm _ _ _

@[simp] theorem im_smul {S} [CommRing R] [SMulZeroClass S R] (s : S) : (s • a).im = s • a.im :=
  QuaternionAlgebra.ext (smul_zero s).symm rfl rfl rfl

@[simp]
theorem smul_mk (re im_i im_j im_k : R) :
    s • (⟨re, im_i, im_j, im_k⟩ : ℍ[R,c₁,c₂,c₃]) = ⟨s • re, s • im_i, s • im_j, s • im_k⟩ :=
  rfl

end SMul

instance [Monoid S] [MulAction S R] : MulAction S ℍ[R,c₁,c₂,c₃] :=
  (equivProd ..).injective.mulAction _ fun _ _ ↦ rfl

instance [AddCommGroup R] : AddCommGroup ℍ[R,c₁,c₂,c₃] := by
  apply (equivProd c₁ c₂ c₃).injective.addCommGroup <;> intros <;> rfl

@[simp, norm_cast]
theorem coe_smul [Zero R] [SMulZeroClass S R] (s : S) (r : R) :
    (↑(s • r) : ℍ[R,c₁,c₂,c₃]) = s • (r : ℍ[R,c₁,c₂,c₃]) :=
  QuaternionAlgebra.ext rfl (smul_zero _).symm (smul_zero _).symm (smul_zero _).symm

instance [Semiring S] [AddCommGroup R] [DistribMulAction S R] : DistribMulAction S ℍ[R,c₁,c₂,c₃] :=
  (addEquivProd ..).injective.distribMulAction (addEquivProd c₁ c₂ c₃).toAddMonoidHom fun _ _ ↦ rfl

instance [Semiring S] [AddCommGroup R] [Module S R] : Module S ℍ[R,c₁,c₂,c₃] :=
  (addEquivProd ..).injective.module _ (addEquivProd c₁ c₂ c₃).toAddMonoidHom fun _ _ ↦ rfl

section AddCommGroupWithOne
variable [AddCommGroupWithOne R]

instance : AddCommGroupWithOne ℍ[R,c₁,c₂,c₃] where
  natCast n := ((n : R) : ℍ[R,c₁,c₂,c₃])
  natCast_zero := by simp
  natCast_succ := by simp
  intCast n := ((n : R) : ℍ[R,c₁,c₂,c₃])
  intCast_ofNat _ := congr_arg coe (Int.cast_natCast _)
  intCast_negSucc n := by
    change coe _ = -coe _
    rw [Int.cast_negSucc, coe_neg]

@[simp, norm_cast]
theorem re_natCast (n : ℕ) : (n : ℍ[R,c₁,c₂,c₃]).re = n :=
  rfl

@[simp, norm_cast]
theorem imI_natCast (n : ℕ) : (n : ℍ[R,c₁,c₂,c₃]).imI = 0 :=
  rfl

@[simp, norm_cast]
theorem imJ_natCast (n : ℕ) : (n : ℍ[R,c₁,c₂,c₃]).imJ = 0 :=
  rfl

@[simp, norm_cast]
theorem imK_natCast (n : ℕ) : (n : ℍ[R,c₁,c₂,c₃]).imK = 0 :=
  rfl

@[simp, norm_cast]
theorem im_natCast (n : ℕ) : (n : ℍ[R,c₁,c₂,c₃]).im = 0 :=
  rfl

@[norm_cast]
theorem coe_natCast (n : ℕ) : ↑(n : R) = (n : ℍ[R,c₁,c₂,c₃]) :=
  rfl

@[simp, norm_cast]
theorem re_intCast (z : ℤ) : (z : ℍ[R,c₁,c₂,c₃]).re = z :=
  rfl

@[scoped simp]
theorem re_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : ℍ[R,c₁,c₂,c₃]).re = ofNat(n) := rfl

@[scoped simp]
theorem imI_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : ℍ[R,c₁,c₂,c₃]).imI = 0 := rfl

@[scoped simp]
theorem imJ_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : ℍ[R,c₁,c₂,c₃]).imJ = 0 := rfl

@[scoped simp]
theorem imK_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : ℍ[R,c₁,c₂,c₃]).imK = 0 := rfl

@[scoped simp]
theorem im_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : ℍ[R,c₁,c₂,c₃]).im = 0 := rfl

@[simp, norm_cast]
theorem imI_intCast (z : ℤ) : (z : ℍ[R,c₁,c₂,c₃]).imI = 0 :=
  rfl

@[simp, norm_cast]
theorem imJ_intCast (z : ℤ) : (z : ℍ[R,c₁,c₂,c₃]).imJ = 0 :=
  rfl

@[simp, norm_cast]
theorem imK_intCast (z : ℤ) : (z : ℍ[R,c₁,c₂,c₃]).imK = 0 :=
  rfl

@[simp, norm_cast]
theorem im_intCast (z : ℤ) : (z : ℍ[R,c₁,c₂,c₃]).im = 0 :=
  rfl

@[norm_cast]
theorem coe_intCast (z : ℤ) : ↑(z : R) = (z : ℍ[R,c₁,c₂,c₃]) :=
  rfl

end AddCommGroupWithOne

-- For the remainder of the file we assume `CommRing R`.
variable [CommRing R]

instance instRing : Ring ℍ[R,c₁,c₂,c₃] where
  __ := (inferInstance : AddCommGroupWithOne ℍ[R,c₁,c₂,c₃])
  left_distrib _ _ _ := by ext <;> simp <;> ring
  right_distrib _ _ _ := by ext <;> simp <;> ring
  zero_mul _ := by ext <;> simp
  mul_zero _ := by ext <;> simp
  mul_assoc _ _ _ := by ext <;> simp <;> ring
  one_mul _ := by ext <;> simp
  mul_one _ := by ext <;> simp

@[norm_cast, simp]
theorem coe_mul : ((x * y : R) : ℍ[R,c₁,c₂,c₃]) = x * y := by ext <;> simp

@[norm_cast, simp]
lemma coe_ofNat {n : ℕ} [n.AtLeastTwo] :
    ((ofNat(n) : R) : ℍ[R,c₁,c₂,c₃]) = (ofNat(n) : ℍ[R,c₁,c₂,c₃]) :=
  rfl

instance [CommSemiring S] [Algebra S R] : Algebra S ℍ[R,c₁,c₂,c₃] where
  algebraMap :=
  { toFun s := coe (algebraMap S R s)
    map_one' := by simp only [map_one, coe_one]
    map_zero' := by simp only [map_zero, coe_zero]
    map_mul' x y := by simp only [map_mul, coe_mul]
    map_add' x y := by simp only [map_add, coe_add] }
  smul_def' s x := by ext <;> simp [Algebra.smul_def]
  commutes' s x := by ext <;> simp [Algebra.commutes]

theorem algebraMap_eq (r : R) : algebraMap R ℍ[R,c₁,c₂,c₃] r = ⟨r, 0, 0, 0⟩ :=
  rfl

theorem algebraMap_injective : (algebraMap R ℍ[R,c₁,c₂,c₃] : _ → _).Injective :=
  fun _ _ ↦ by simp [algebraMap_eq]

instance : IsTorsionFree R ℍ[R,c₁,c₂,c₃] :=
 (addEquivProd ..).injective.moduleIsTorsionFree _ fun _ _ ↦ rfl

section

variable (c₁ c₂ c₃)

/-- `QuaternionAlgebra.re` as a `LinearMap` -/
@[simps]
def reₗ : ℍ[R,c₁,c₂,c₃] →ₗ[R] R where
  toFun := re
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `QuaternionAlgebra.imI` as a `LinearMap` -/
@[simps]
def imIₗ : ℍ[R,c₁,c₂,c₃] →ₗ[R] R where
  toFun := imI
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `QuaternionAlgebra.imJ` as a `LinearMap` -/
@[simps]
def imJₗ : ℍ[R,c₁,c₂,c₃] →ₗ[R] R where
  toFun := imJ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `QuaternionAlgebra.imK` as a `LinearMap` -/
@[simps]
def imKₗ : ℍ[R,c₁,c₂,c₃] →ₗ[R] R where
  toFun := imK
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `QuaternionAlgebra.equivTuple` as a linear equivalence. -/
def linearEquivTuple : ℍ[R,c₁,c₂,c₃] ≃ₗ[R] Fin 4 → R := (equivTuple ..).linearEquiv _

@[simp]
theorem coe_linearEquivTuple :
    ⇑(linearEquivTuple c₁ c₂ c₃) = equivTuple c₁ c₂ c₃ := rfl

@[simp]
theorem coe_linearEquivTuple_symm :
    ⇑(linearEquivTuple c₁ c₂ c₃).symm = (equivTuple c₁ c₂ c₃).symm := rfl

/-- `ℍ[R,c₁,c₂,c₃]` has a basis over `R` given by `1`, `i`, `j`, and `k`. -/
noncomputable def basisOneIJK : Basis (Fin 4) R ℍ[R,c₁,c₂,c₃] :=
  .ofEquivFun <| linearEquivTuple c₁ c₂ c₃

@[simp]
theorem coe_basisOneIJK_repr (q : ℍ[R,c₁,c₂,c₃]) :
    ((basisOneIJK c₁ c₂ c₃).repr q) = ![q.re, q.imI, q.imJ, q.imK] :=
  rfl

instance : Module.Finite R ℍ[R,c₁,c₂,c₃] := .of_basis (basisOneIJK c₁ c₂ c₃)

instance : Module.Free R ℍ[R,c₁,c₂,c₃] := .of_basis (basisOneIJK c₁ c₂ c₃)

theorem rank_eq_four [StrongRankCondition R] : Module.rank R ℍ[R,c₁,c₂,c₃] = 4 := by
  rw [rank_eq_card_basis (basisOneIJK c₁ c₂ c₃), Fintype.card_fin]
  norm_num

theorem finrank_eq_four [StrongRankCondition R] : Module.finrank R ℍ[R,c₁,c₂,c₃] = 4 := by
  rw [Module.finrank, rank_eq_four, Cardinal.toNat_ofNat]

/-- There is a natural equivalence when swapping the first and third coefficients of a
  quaternion algebra if `c₂` is 0. -/
@[simps]
def swapEquiv : ℍ[R,c₁,0,c₃] ≃ₐ[R] ℍ[R,c₃,0,c₁] where
  toFun t := ⟨t.1, t.3, t.2, -t.4⟩
  invFun t := ⟨t.1, t.3, t.2, -t.4⟩
  left_inv _ := by simp
  right_inv _ := by simp
  map_mul' _ _ := by ext <;> simp <;> ring
  map_add' _ _ := by ext <;> simp [add_comm]
  commutes' _ := by simp [algebraMap_eq]

end

@[norm_cast, simp]
theorem coe_sub : ((x - y : R) : ℍ[R,c₁,c₂,c₃]) = x - y :=
  (algebraMap R ℍ[R,c₁,c₂,c₃]).map_sub x y

@[norm_cast, simp]
theorem coe_pow (n : ℕ) : (↑(x ^ n) : ℍ[R,c₁,c₂,c₃]) = (x : ℍ[R,c₁,c₂,c₃]) ^ n :=
  (algebraMap R ℍ[R,c₁,c₂,c₃]).map_pow x n

theorem coe_commutes : ↑r * a = a * r :=
  Algebra.commutes r a

theorem coe_commute : Commute (↑r) a :=
  coe_commutes r a

theorem coe_mul_eq_smul : ↑r * a = r • a :=
  (Algebra.smul_def r a).symm

theorem mul_coe_eq_smul : a * r = r • a := by rw [← coe_commutes, coe_mul_eq_smul]

@[norm_cast, simp]
theorem coe_algebraMap : ⇑(algebraMap R ℍ[R,c₁,c₂,c₃]) = coe :=
  rfl

theorem smul_coe : x • (y : ℍ[R,c₁,c₂,c₃]) = ↑(x * y) := by rw [coe_mul, coe_mul_eq_smul]

/-- Quaternion conjugate. -/
instance instStarQuaternionAlgebra : Star ℍ[R,c₁,c₂,c₃] where star a :=
  ⟨a.1 + c₂ * a.2, -a.2, -a.3, -a.4⟩

@[simp] theorem re_star : (star a).re = a.re + c₂ * a.imI := rfl

@[simp]
theorem imI_star : (star a).imI = -a.imI :=
  rfl

@[simp]
theorem imJ_star : (star a).imJ = -a.imJ :=
  rfl

@[simp]
theorem imK_star : (star a).imK = -a.imK :=
  rfl

@[simp]
theorem im_star : (star a).im = -a.im :=
  QuaternionAlgebra.ext neg_zero.symm rfl rfl rfl

@[simp]
theorem star_mk (a₁ a₂ a₃ a₄ : R) : star (mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃]) =
    ⟨a₁ + c₂ * a₂, -a₂, -a₃, -a₄⟩ := rfl

instance instStarRing : StarRing ℍ[R,c₁,c₂,c₃] where
  star_involutive x := by simp [Star.star]
  star_add a b := by ext <;> simp [add_comm]; ring
  star_mul a b := by ext <;> simp <;> ring

theorem self_add_star' : a + star a = ↑(2 * a.re + c₂ * a.imI) := by ext <;> simp [two_mul]; ring

theorem self_add_star : a + star a = 2 * a.re + c₂ * a.imI := by simp [self_add_star']

theorem star_add_self' : star a + a = ↑(2 * a.re + c₂ * a.imI) := by rw [add_comm, self_add_star']

theorem star_add_self : star a + a = 2 * a.re + c₂ * a.imI := by rw [add_comm, self_add_star]

theorem star_eq_two_re_sub : star a = ↑(2 * a.re + c₂ * a.imI) - a :=
  eq_sub_iff_add_eq.2 a.star_add_self'

lemma comm (r : R) (x : ℍ[R,c₁,c₂,c₃]) : r * x = x * r := by
  ext <;> simp [mul_comm]

instance : IsStarNormal a :=
  ⟨by
    rw [commute_iff_eq, a.star_eq_two_re_sub];
    ext <;> simp <;> ring⟩

@[simp, norm_cast]
theorem star_coe : star (x : ℍ[R,c₁,c₂,c₃]) = x := by ext <;> simp

@[simp] theorem star_im : star a.im = -a.im + c₂ * a.imI := by ext <;> simp

@[simp]
theorem star_smul [Monoid S] [DistribMulAction S R] [SMulCommClass S R R]
    (s : S) (a : ℍ[R,c₁,c₂,c₃]) :
    star (s • a) = s • star a :=
  QuaternionAlgebra.ext
    (by simp [mul_smul_comm]) (smul_neg _ _).symm (smul_neg _ _).symm (smul_neg _ _).symm

/-- A version of `star_smul` for the special case when `c₂ = 0`, without `SMulCommClass S R R`. -/
theorem star_smul' [Monoid S] [DistribMulAction S R] (s : S) (a : ℍ[R,c₁,0,c₃]) :
    star (s • a) = s • star a :=
  QuaternionAlgebra.ext (by simp) (smul_neg _ _).symm (smul_neg _ _).symm (smul_neg _ _).symm

theorem eq_re_of_eq_coe {a : ℍ[R,c₁,c₂,c₃]} {x : R} (h : a = x) : a = a.re := by rw [h, re_coe]

theorem eq_re_iff_mem_range_coe {a : ℍ[R,c₁,c₂,c₃]} :
    a = a.re ↔ a ∈ Set.range (coe : R → ℍ[R,c₁,c₂,c₃]) :=
  ⟨fun h => ⟨a.re, h.symm⟩, fun ⟨_, h⟩ => eq_re_of_eq_coe h.symm⟩

section CharZero

variable [NoZeroDivisors R] [CharZero R]

@[simp]
theorem star_eq_self {c₁ c₂ : R} {a : ℍ[R,c₁,c₂,c₃]} : star a = a ↔ a = a.re := by
  simp_all [QuaternionAlgebra.ext_iff, neg_eq_iff_add_eq_zero, add_self_eq_zero]

theorem star_eq_neg {c₁ : R} {a : ℍ[R,c₁,0,c₃]} : star a = -a ↔ a.re = 0 := by
  simp [QuaternionAlgebra.ext_iff, eq_neg_iff_add_eq_zero]

end CharZero

-- Can't use `rw ← star_eq_self` in the proof without additional assumptions
theorem star_mul_eq_coe : star a * a = (star a * a).re := by ext <;> simp <;> ring

theorem mul_star_eq_coe : a * star a = (a * star a).re := by
  rw [← star_comm_self']
  exact a.star_mul_eq_coe

open MulOpposite

/-- Quaternion conjugate as an `AlgEquiv` to the opposite ring. -/
def starAe : ℍ[R,c₁,c₂,c₃] ≃ₐ[R] ℍ[R,c₁,c₂,c₃]ᵐᵒᵖ :=
  { starAddEquiv.trans opAddEquiv with
    toFun := op ∘ star
    invFun := star ∘ unop
    map_mul' := fun x y => by simp
    commutes' := fun r => by simp }

@[simp]
theorem coe_starAe : ⇑(starAe : ℍ[R,c₁,c₂,c₃] ≃ₐ[R] _) = op ∘ star :=
  rfl

end QuaternionAlgebra

/-- Space of quaternions over a type, denoted as `ℍ[R]`.
Implemented as a structure with four fields: `re`, `im_i`, `im_j`, and `im_k`. -/
def Quaternion (R : Type*) [Zero R] [One R] [Neg R] :=
  QuaternionAlgebra R (-1) (0) (-1)

@[inherit_doc]
scoped[Quaternion] notation "ℍ[" R "]" => Quaternion R

open Quaternion

/-- The equivalence between the quaternions over `R` and `R × R × R × R`. -/
@[simps!]
def Quaternion.equivProd (R : Type*) [Zero R] [One R] [Neg R] : ℍ[R] ≃ R × R × R × R :=
  QuaternionAlgebra.equivProd _ _ _

/-- The equivalence between the quaternions over `R` and `Fin 4 → R`. -/
@[simps! symm_apply]
def Quaternion.equivTuple (R : Type*) [Zero R] [One R] [Neg R] : ℍ[R] ≃ (Fin 4 → R) :=
  QuaternionAlgebra.equivTuple _ _ _

@[simp]
theorem Quaternion.equivTuple_apply (R : Type*) [Zero R] [One R] [Neg R] (x : ℍ[R]) :
    Quaternion.equivTuple R x = ![x.re, x.imI, x.imJ, x.imK] :=
  rfl

instance {R : Type*} [Zero R] [One R] [Neg R] [Subsingleton R] : Subsingleton ℍ[R] :=
  inferInstanceAs <| Subsingleton <| ℍ[R,-1,0,-1]
instance {R : Type*} [Zero R] [One R] [Neg R] [Nontrivial R] : Nontrivial ℍ[R] :=
  inferInstanceAs <| Nontrivial <| ℍ[R,-1,0,-1]

namespace Quaternion

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

/-- Coercion `R → ℍ[R]`. -/
@[coe] def coe : R → ℍ[R] := QuaternionAlgebra.coe

instance : CoeTC R ℍ[R] := ⟨coe⟩

instance instRing : Ring ℍ[R] := inferInstanceAs <| Ring ℍ[R,-1,0,-1]

instance : Inhabited ℍ[R] := inferInstanceAs <| Inhabited ℍ[R,-1,0,-1]

instance [SMul S R] : SMul S ℍ[R] := inferInstanceAs <| SMul S ℍ[R,-1,0,-1]

instance [SMul S T] [SMul S R] [SMul T R] [IsScalarTower S T R] : IsScalarTower S T ℍ[R] :=
  inferInstanceAs <| IsScalarTower S T ℍ[R,-1,0,-1]

instance [SMul S R] [SMul T R] [SMulCommClass S T R] : SMulCommClass S T ℍ[R] :=
  inferInstanceAs <| SMulCommClass S T ℍ[R,-1,0,-1]

instance [Monoid S] [MulAction S R] : MulAction S ℍ[R] :=
  inferInstanceAs <| MulAction S ℍ[R,-1,0,-1]

instance [Semiring S] [DistribMulAction S R] : DistribMulAction S ℍ[R] :=
  inferInstanceAs <| DistribMulAction S ℍ[R,-1,0,-1]

instance [Semiring S] [Module S R] : Module S ℍ[R] :=
  inferInstanceAs <| Module S ℍ[R,-1,0,-1]

protected instance algebra [CommSemiring S] [Algebra S R] : Algebra S ℍ[R] :=
  inferInstanceAs <| Algebra S ℍ[R,-1,0,-1]

instance : Star ℍ[R] := inferInstanceAs <| Star ℍ[R,-1,0,-1]
instance : StarRing ℍ[R] := inferInstanceAs <| StarRing ℍ[R,-1,0,-1]
instance : IsStarNormal a := inferInstanceAs <| IsStarNormal (R := ℍ[R,-1,0,-1]) a

@[ext]
theorem ext : a.re = b.re → a.imI = b.imI → a.imJ = b.imJ → a.imK = b.imK → a = b :=
  QuaternionAlgebra.ext

/-- The imaginary part of a quaternion. -/
def im (x : ℍ[R]) : ℍ[R] := QuaternionAlgebra.im x

@[simp] theorem re_im : a.im.re = 0 := rfl

@[simp] theorem imI_im : a.im.imI = a.imI := rfl

@[simp] theorem imJ_im : a.im.imJ = a.imJ := rfl

@[simp] theorem imK_im : a.im.imK = a.imK := rfl

@[simp] theorem im_idem : a.im.im = a.im := rfl

@[simp] theorem re_add_im : ↑a.re + a.im = a := QuaternionAlgebra.re_add_im a

@[simp] theorem sub_im_self : a - a.im = a.re := QuaternionAlgebra.sub_im_self a

@[simp] theorem sub_re_self : a - ↑a.re = a.im := QuaternionAlgebra.sub_re_self a

@[simp, norm_cast]
theorem re_coe : (x : ℍ[R]).re = x := rfl

@[simp, norm_cast]
theorem imI_coe : (x : ℍ[R]).imI = 0 := rfl

@[simp, norm_cast]
theorem imJ_coe : (x : ℍ[R]).imJ = 0 := rfl

@[simp, norm_cast]
theorem imK_coe : (x : ℍ[R]).imK = 0 := rfl

@[simp, norm_cast]
theorem im_coe : (x : ℍ[R]).im = 0 := rfl

@[scoped simp] theorem re_zero : (0 : ℍ[R]).re = 0 := rfl

@[scoped simp] theorem imI_zero : (0 : ℍ[R]).imI = 0 := rfl

@[scoped simp] theorem imJ_zero : (0 : ℍ[R]).imJ = 0 := rfl

@[scoped simp] theorem imK_zero : (0 : ℍ[R]).imK = 0 := rfl

@[scoped simp] theorem im_zero : (0 : ℍ[R]).im = 0 := rfl

@[simp, norm_cast]
theorem coe_zero : ((0 : R) : ℍ[R]) = 0 := rfl

@[scoped simp] theorem re_one : (1 : ℍ[R]).re = 1 := rfl

@[scoped simp] theorem imI_one : (1 : ℍ[R]).imI = 0 := rfl

@[scoped simp] theorem imJ_one : (1 : ℍ[R]).imJ = 0 := rfl

@[scoped simp] theorem imK_one : (1 : ℍ[R]).imK = 0 := rfl

@[scoped simp] theorem im_one : (1 : ℍ[R]).im = 0 := rfl

@[simp, norm_cast]
theorem coe_one : ((1 : R) : ℍ[R]) = 1 := rfl

@[simp] theorem re_add : (a + b).re = a.re + b.re := rfl

@[simp] theorem imI_add : (a + b).imI = a.imI + b.imI := rfl

@[simp] theorem imJ_add : (a + b).imJ = a.imJ + b.imJ := rfl

@[simp] theorem imK_add : (a + b).imK = a.imK + b.imK := rfl

@[simp] theorem im_add : (a + b).im = a.im + b.im := QuaternionAlgebra.im_add a b

@[simp, norm_cast]
theorem coe_add : ((x + y : R) : ℍ[R]) = x + y :=
  QuaternionAlgebra.coe_add x y

@[simp] theorem re_neg : (-a).re = -a.re := rfl

@[simp] theorem imI_neg : (-a).imI = -a.imI := rfl

@[simp] theorem imJ_neg : (-a).imJ = -a.imJ := rfl

@[simp] theorem imK_neg : (-a).imK = -a.imK := rfl

@[simp] theorem im_neg : (-a).im = -a.im := QuaternionAlgebra.im_neg a

@[simp, norm_cast]
theorem coe_neg : ((-x : R) : ℍ[R]) = -x :=
  QuaternionAlgebra.coe_neg x

@[simp] theorem re_sub : (a - b).re = a.re - b.re := rfl

@[simp] theorem imI_sub : (a - b).imI = a.imI - b.imI := rfl

@[simp] theorem imJ_sub : (a - b).imJ = a.imJ - b.imJ := rfl

@[simp] theorem imK_sub : (a - b).imK = a.imK - b.imK := rfl

@[simp] theorem im_sub : (a - b).im = a.im - b.im := QuaternionAlgebra.im_sub a b

@[simp, norm_cast]
theorem coe_sub : ((x - y : R) : ℍ[R]) = x - y :=
  QuaternionAlgebra.coe_sub x y

@[simp]
theorem re_mul : (a * b).re = a.re * b.re - a.imI * b.imI - a.imJ * b.imJ - a.imK * b.imK :=
  (QuaternionAlgebra.re_mul a b).trans <| by simp [one_mul, neg_mul, sub_eq_add_neg, neg_neg]

@[simp]
theorem imI_mul : (a * b).imI = a.re * b.imI + a.imI * b.re + a.imJ * b.imK - a.imK * b.imJ :=
  (QuaternionAlgebra.imI_mul a b).trans <| by ring

@[simp]
theorem imJ_mul : (a * b).imJ = a.re * b.imJ - a.imI * b.imK + a.imJ * b.re + a.imK * b.imI :=
  (QuaternionAlgebra.imJ_mul a b).trans <| by ring

@[simp]
theorem imK_mul : (a * b).imK = a.re * b.imK + a.imI * b.imJ - a.imJ * b.imI + a.imK * b.re :=
  (QuaternionAlgebra.imK_mul a b).trans <| by ring

@[simp, norm_cast]
theorem coe_mul : ((x * y : R) : ℍ[R]) = x * y := QuaternionAlgebra.coe_mul x y

@[norm_cast, simp]
theorem coe_pow (n : ℕ) : (↑(x ^ n) : ℍ[R]) = (x : ℍ[R]) ^ n :=
  QuaternionAlgebra.coe_pow x n

@[simp, norm_cast]
theorem re_natCast (n : ℕ) : (n : ℍ[R]).re = n := rfl

@[simp, norm_cast]
theorem imI_natCast (n : ℕ) : (n : ℍ[R]).imI = 0 := rfl

@[simp, norm_cast]
theorem imJ_natCast (n : ℕ) : (n : ℍ[R]).imJ = 0 := rfl

@[simp, norm_cast]
theorem imK_natCast (n : ℕ) : (n : ℍ[R]).imK = 0 := rfl

@[simp, norm_cast]
theorem im_natCast (n : ℕ) : (n : ℍ[R]).im = 0 := rfl

@[norm_cast]
theorem coe_natCast (n : ℕ) : ↑(n : R) = (n : ℍ[R]) := rfl

@[simp, norm_cast]
theorem re_intCast (z : ℤ) : (z : ℍ[R]).re = z := rfl

@[simp, norm_cast]
theorem imI_intCast (z : ℤ) : (z : ℍ[R]).imI = 0 := rfl

@[simp, norm_cast]
theorem imJ_intCast (z : ℤ) : (z : ℍ[R]).imJ = 0 := rfl

@[simp, norm_cast]
theorem imK_intCast (z : ℤ) : (z : ℍ[R]).imK = 0 := rfl

@[simp, norm_cast]
theorem im_intCast (z : ℤ) : (z : ℍ[R]).im = 0 := rfl

@[norm_cast]
theorem coe_intCast (z : ℤ) : ↑(z : R) = (z : ℍ[R]) := rfl

theorem coe_injective : Function.Injective (coe : R → ℍ[R]) :=
  QuaternionAlgebra.coe_injective

@[simp]
theorem coe_inj {x y : R} : (x : ℍ[R]) = y ↔ x = y :=
  coe_injective.eq_iff

@[simp]
theorem re_smul [SMul S R] (s : S) : (s • a).re = s • a.re :=
  rfl

@[simp] theorem imI_smul [SMul S R] (s : S) : (s • a).imI = s • a.imI := rfl

@[simp] theorem imJ_smul [SMul S R] (s : S) : (s • a).imJ = s • a.imJ := rfl

@[simp] theorem imK_smul [SMul S R] (s : S) : (s • a).imK = s • a.imK := rfl

@[simp]
theorem im_smul [SMulZeroClass S R] (s : S) : (s • a).im = s • a.im :=
  QuaternionAlgebra.im_smul a s

@[simp, norm_cast]
theorem coe_smul [SMulZeroClass S R] (s : S) (r : R) : (↑(s • r) : ℍ[R]) = s • (r : ℍ[R]) :=
  QuaternionAlgebra.coe_smul _ _

theorem coe_commutes : ↑r * a = a * r :=
  QuaternionAlgebra.coe_commutes r a

theorem coe_commute : Commute (↑r) a :=
  QuaternionAlgebra.coe_commute r a

theorem coe_mul_eq_smul : ↑r * a = r • a :=
  QuaternionAlgebra.coe_mul_eq_smul r a

theorem mul_coe_eq_smul : a * r = r • a :=
  QuaternionAlgebra.mul_coe_eq_smul r a

@[simp]
theorem algebraMap_def : ⇑(algebraMap R ℍ[R]) = coe :=
  rfl

theorem algebraMap_injective : (algebraMap R ℍ[R] : _ → _).Injective :=
  QuaternionAlgebra.algebraMap_injective

theorem smul_coe : x • (y : ℍ[R]) = ↑(x * y) :=
  QuaternionAlgebra.smul_coe x y

instance : Module.Finite R ℍ[R] := inferInstanceAs <| Module.Finite R ℍ[R,-1,0,-1]
instance : Module.Free R ℍ[R] := inferInstanceAs <| Module.Free R ℍ[R,-1,0,-1]

theorem rank_eq_four [StrongRankCondition R] : Module.rank R ℍ[R] = 4 :=
  QuaternionAlgebra.rank_eq_four _ _ _

theorem finrank_eq_four [StrongRankCondition R] : Module.finrank R ℍ[R] = 4 :=
  QuaternionAlgebra.finrank_eq_four _ _ _

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem re_star : (star a).re = a.re := by
  rw [QuaternionAlgebra.re_star, zero_mul, add_zero]

@[simp] theorem imI_star : (star a).imI = -a.imI := rfl

@[simp] theorem imJ_star : (star a).imJ = -a.imJ := rfl

@[simp] theorem imK_star : (star a).imK = -a.imK := rfl

@[simp] theorem im_star : (star a).im = -a.im := QuaternionAlgebra.im_star a

theorem self_add_star' : a + star a = ↑(2 * a.re) := by
  simpa using QuaternionAlgebra.self_add_star' a

theorem self_add_star : a + star a = 2 * a.re := by
  simpa using QuaternionAlgebra.self_add_star a

theorem star_add_self' : star a + a = ↑(2 * a.re) := by
  simpa using QuaternionAlgebra.star_add_self' a

theorem star_add_self : star a + a = 2 * a.re := by
  simpa using QuaternionAlgebra.star_add_self a

theorem star_eq_two_re_sub : star a = ↑(2 * a.re) - a := by
  simpa using QuaternionAlgebra.star_eq_two_re_sub a

@[simp, norm_cast]
theorem star_coe : star (x : ℍ[R]) = x :=
  QuaternionAlgebra.star_coe x

@[simp]
theorem star_im : star a.im = -a.im := by ext <;> simp

@[simp]
theorem star_smul [Monoid S] [DistribMulAction S R] (s : S) (a : ℍ[R]) :
    star (s • a) = s • star a := QuaternionAlgebra.star_smul' s a

theorem eq_re_of_eq_coe {a : ℍ[R]} {x : R} (h : a = x) : a = a.re :=
  QuaternionAlgebra.eq_re_of_eq_coe h

theorem eq_re_iff_mem_range_coe {a : ℍ[R]} : a = a.re ↔ a ∈ Set.range (coe : R → ℍ[R]) :=
  QuaternionAlgebra.eq_re_iff_mem_range_coe

section CharZero

variable [NoZeroDivisors R] [CharZero R]

@[simp]
theorem star_eq_self {a : ℍ[R]} : star a = a ↔ a = a.re :=
  QuaternionAlgebra.star_eq_self

@[simp]
theorem star_eq_neg {a : ℍ[R]} : star a = -a ↔ a.re = 0 :=
  QuaternionAlgebra.star_eq_neg

end CharZero

theorem star_mul_eq_coe : star a * a = (star a * a).re :=
  QuaternionAlgebra.star_mul_eq_coe a

theorem mul_star_eq_coe : a * star a = (a * star a).re :=
  QuaternionAlgebra.mul_star_eq_coe a

open MulOpposite

/-- Quaternion conjugate as an `AlgEquiv` to the opposite ring. -/
def starAe : ℍ[R] ≃ₐ[R] ℍ[R]ᵐᵒᵖ :=
  QuaternionAlgebra.starAe

@[simp]
theorem coe_starAe : ⇑(starAe : ℍ[R] ≃ₐ[R] ℍ[R]ᵐᵒᵖ) = op ∘ star :=
  rfl

/-- Square of the norm. -/
def normSq : ℍ[R] →*₀ R where
  toFun a := (a * star a).re
  map_zero' := by simp only [star_zero, zero_mul, re_zero]
  map_one' := by simp only [star_one, one_mul, re_one]
  map_mul' x y := coe_injective <| by
    conv_lhs => rw [← mul_star_eq_coe, star_mul, mul_assoc, ← mul_assoc y, y.mul_star_eq_coe,
      coe_commutes, ← mul_assoc, x.mul_star_eq_coe, ← coe_mul]

theorem normSq_def : normSq a = (a * star a).re := rfl

theorem normSq_def' : normSq a = a.1 ^ 2 + a.2 ^ 2 + a.3 ^ 2 + a.4 ^ 2 := by
  simp only [normSq_def, sq, mul_neg, sub_neg_eq_add, re_mul, re_star, imI_star, imJ_star,
    imK_star]

theorem normSq_coe : normSq (x : ℍ[R]) = x ^ 2 := by
  rw [normSq_def, star_coe, ← coe_mul, re_coe, sq]

@[simp]
theorem normSq_star : normSq (star a) = normSq a := by simp [normSq_def']

@[norm_cast]
theorem normSq_natCast (n : ℕ) : normSq (n : ℍ[R]) = (n : R) ^ 2 := by
  rw [← coe_natCast, normSq_coe]

@[norm_cast]
theorem normSq_intCast (z : ℤ) : normSq (z : ℍ[R]) = (z : R) ^ 2 := by
  rw [← coe_intCast, normSq_coe]

@[simp]
theorem normSq_neg : normSq (-a) = normSq a := by simp only [normSq_def, star_neg, neg_mul_neg]

theorem self_mul_star : a * star a = normSq a := by rw [mul_star_eq_coe, normSq_def]

theorem star_mul_self : star a * a = normSq a := by rw [star_comm_self, self_mul_star]

theorem im_sq : a.im ^ 2 = -normSq a.im := by
  simp_rw [sq, ← star_mul_self, star_im, neg_mul, neg_neg]

theorem coe_normSq_add : normSq (a + b) = normSq a + a * star b + b * star a + normSq b := by
  simp only [star_add, ← self_mul_star, mul_add, add_mul, add_assoc, add_left_comm]

theorem normSq_smul (r : R) (q : ℍ[R]) : normSq (r • q) = r ^ 2 * normSq q := by
  simp only [normSq_def', re_smul, imI_smul, imJ_smul, imK_smul, mul_pow, mul_add, smul_eq_mul]

theorem normSq_add (a b : ℍ[R]) : normSq (a + b) = normSq a + normSq b + 2 * (a * star b).re :=
  calc
    normSq (a + b) = normSq a + (a * star b).re + ((b * star a).re + normSq b) := by
      simp_rw [normSq_def, star_add, add_mul, mul_add, re_add]
    _ = normSq a + normSq b + ((a * star b).re + (b * star a).re) := by abel
    _ = normSq a + normSq b + 2 * (a * star b).re := by
      rw [← re_add, ← star_mul_star a b, self_add_star', re_coe]

end Quaternion

namespace Quaternion

variable {R : Type*}

section LinearOrderedCommRing

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {a : ℍ[R]}

@[simp]
theorem normSq_eq_zero : normSq a = 0 ↔ a = 0 := by
  refine ⟨fun h => ?_, fun h => h.symm ▸ normSq.map_zero⟩
  rw [normSq_def', add_eq_zero_iff_of_nonneg, add_eq_zero_iff_of_nonneg, add_eq_zero_iff_of_nonneg]
    at h
  · apply ext a 0 <;> apply eq_zero_of_pow_eq_zero
    exacts [h.1.1.1, h.1.1.2, h.1.2, h.2]
  all_goals apply_rules [sq_nonneg, add_nonneg]

theorem normSq_ne_zero : normSq a ≠ 0 ↔ a ≠ 0 := normSq_eq_zero.not

@[simp]
theorem normSq_nonneg : 0 ≤ normSq a := by
  rw [normSq_def']
  apply_rules [sq_nonneg, add_nonneg]

@[simp]
theorem normSq_le_zero : normSq a ≤ 0 ↔ a = 0 :=
  normSq_nonneg.ge_iff_eq'.trans normSq_eq_zero

instance instNontrivial : Nontrivial ℍ[R] where
  exists_pair_ne := ⟨0, 1, mt (congr_arg QuaternionAlgebra.re) zero_ne_one⟩

instance : NoZeroDivisors ℍ[R] where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} hab :=
    have : normSq a * normSq b = 0 := by rwa [← map_mul, normSq_eq_zero]
    (eq_zero_or_eq_zero_of_mul_eq_zero this).imp normSq_eq_zero.1 normSq_eq_zero.1

instance : IsDomain ℍ[R] := NoZeroDivisors.to_isDomain _

theorem sq_eq_normSq : a ^ 2 = normSq a ↔ a = a.re := by
  rw [← star_eq_self, ← star_mul_self, sq, mul_eq_mul_right_iff, eq_comm]
  exact or_iff_left_of_imp fun ha ↦ ha.symm ▸ star_zero _

theorem sq_eq_neg_normSq : a ^ 2 = -normSq a ↔ a.re = 0 := by
  simp_rw [← star_eq_neg]
  obtain rfl | hq0 := eq_or_ne a 0
  · simp
  · rw [← star_mul_self, ← mul_neg, ← neg_sq, sq, mul_left_inj' (neg_ne_zero.mpr hq0), eq_comm]

end LinearOrderedCommRing

section Field

variable [Field R] (a b : ℍ[R])

instance instNNRatCast : NNRatCast ℍ[R] where nnratCast q := (q : R)
instance instRatCast : RatCast ℍ[R] where ratCast q := (q : R)

@[simp, norm_cast] lemma re_nnratCast (q : ℚ≥0) : (q : ℍ[R]).re = q := rfl
@[simp, norm_cast] lemma im_nnratCast (q : ℚ≥0) : (q : ℍ[R]).im = 0 := rfl
@[simp, norm_cast] lemma imI_nnratCast (q : ℚ≥0) : (q : ℍ[R]).imI = 0 := rfl
@[simp, norm_cast] lemma imJ_nnratCast (q : ℚ≥0) : (q : ℍ[R]).imJ = 0 := rfl
@[simp, norm_cast] lemma imK_nnratCast (q : ℚ≥0) : (q : ℍ[R]).imK = 0 := rfl
@[simp, norm_cast] lemma re_ratCast (q : ℚ) : (q : ℍ[R]).re = q := rfl
@[simp, norm_cast] lemma im_ratCast (q : ℚ) : (q : ℍ[R]).im = 0 := rfl
@[simp, norm_cast] lemma imI_ratCast (q : ℚ) : (q : ℍ[R]).imI = 0 := rfl
@[simp, norm_cast] lemma imJ_ratCast (q : ℚ) : (q : ℍ[R]).imJ = 0 := rfl
@[simp, norm_cast] lemma imK_ratCast (q : ℚ) : (q : ℍ[R]).imK = 0 := rfl

@[norm_cast] lemma coe_nnratCast (q : ℚ≥0) : ↑(q : R) = (q : ℍ[R]) := rfl

@[norm_cast] lemma coe_ratCast (q : ℚ) : ↑(q : R) = (q : ℍ[R]) := rfl

variable [LinearOrder R] [IsStrictOrderedRing R] (a b : ℍ[R])

@[simps -isSimp]
instance instInv : Inv ℍ[R] :=
  ⟨fun a => (normSq a)⁻¹ • star a⟩

instance instGroupWithZero : GroupWithZero ℍ[R] :=
  { Quaternion.instNontrivial with
    inv_zero := by rw [inv_def, star_zero, smul_zero]
    mul_inv_cancel := fun a ha => by
      rw [inv_def, Algebra.mul_smul_comm (normSq a)⁻¹ a (star a), self_mul_star, smul_coe,
        inv_mul_cancel₀ (normSq_ne_zero.2 ha), coe_one] }

@[norm_cast, simp]
theorem coe_inv (x : R) : ((x⁻¹ : R) : ℍ[R]) = (↑x)⁻¹ :=
  map_inv₀ (algebraMap R ℍ[R]) _

@[norm_cast, simp]
theorem coe_div (x y : R) : ((x / y : R) : ℍ[R]) = x / y :=
  map_div₀ (algebraMap R ℍ[R]) x y

@[norm_cast, simp]
theorem coe_zpow (x : R) (z : ℤ) : ((x ^ z : R) : ℍ[R]) = (x : ℍ[R]) ^ z :=
  map_zpow₀ (algebraMap R ℍ[R]) x z

instance instDivisionRing : DivisionRing ℍ[R] where
  __ := Quaternion.instRing
  __ := Quaternion.instGroupWithZero
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnratCast_def _ := by rw [← coe_nnratCast, NNRat.cast_def, coe_div, coe_natCast, coe_natCast]
  ratCast_def _ := by rw [← coe_ratCast, Rat.cast_def, coe_div, coe_intCast, coe_natCast]
  nnqsmul_def _ _ := by rw [← coe_nnratCast, coe_mul_eq_smul]; ext <;> exact NNRat.smul_def ..
  qsmul_def _ _ := by rw [← coe_ratCast, coe_mul_eq_smul]; ext <;> exact Rat.smul_def ..

theorem normSq_inv : normSq a⁻¹ = (normSq a)⁻¹ :=
  map_inv₀ normSq _

theorem normSq_div : normSq (a / b) = normSq a / normSq b :=
  map_div₀ normSq a b

theorem normSq_zpow (z : ℤ) : normSq (a ^ z) = normSq a ^ z :=
  map_zpow₀ normSq a z

@[norm_cast]
theorem normSq_ratCast (q : ℚ) : normSq (q : ℍ[R]) = (q : ℍ[R]) ^ 2 := by
  rw [← coe_ratCast, normSq_coe, coe_pow]

end Field

end Quaternion

namespace Cardinal

open Quaternion

section QuaternionAlgebra

variable {R : Type*} (c₁ c₂ c₃ : R)

private theorem pow_four [Infinite R] : #R ^ 4 = #R :=
  power_nat_eq (aleph0_le_mk R) <| by decide

/-- The cardinality of a quaternion algebra, as a type. -/
theorem mk_quaternionAlgebra : #(ℍ[R,c₁,c₂,c₃]) = #R ^ 4 := by
  rw [mk_congr (QuaternionAlgebra.equivProd c₁ c₂ c₃)]
  simp only [mk_prod, lift_id]
  ring

@[simp]
theorem mk_quaternionAlgebra_of_infinite [Infinite R] : #(ℍ[R,c₁,c₂,c₃]) = #R := by
  rw [mk_quaternionAlgebra, pow_four]

/-- The cardinality of a quaternion algebra, as a set. -/
theorem mk_univ_quaternionAlgebra : #(Set.univ : Set ℍ[R,c₁,c₂,c₃]) = #R ^ 4 := by
  rw [mk_univ, mk_quaternionAlgebra]

theorem mk_univ_quaternionAlgebra_of_infinite [Infinite R] :
    #(Set.univ : Set ℍ[R,c₁,c₂,c₃]) = #R := by rw [mk_univ_quaternionAlgebra, pow_four]

/-- Show the quaternion `⟨w, x, y, z⟩` as a string `"{ re := w, imI := x, imJ := y, imK := z }"`.

For the typical case of quaternions over ℝ, each component will show as a Cauchy sequence due to
the way Real numbers are represented.
-/
instance [Repr R] {a b c : R} : Repr ℍ[R,a,b,c] where
  reprPrec q _ :=
    s!"\{ re := {repr q.re}, imI := {repr q.imI}, imJ := {repr q.imJ}, imK := {repr q.imK} }"

end QuaternionAlgebra

section Quaternion

variable (R : Type*) [Zero R] [One R] [Neg R]

/-- The cardinality of the quaternions, as a type. -/
@[simp]
theorem mk_quaternion : #(ℍ[R]) = #R ^ 4 :=
  mk_quaternionAlgebra _ _ _

theorem mk_quaternion_of_infinite [Infinite R] : #(ℍ[R]) = #R :=
  mk_quaternionAlgebra_of_infinite _ _ _

/-- The cardinality of the quaternions, as a set. -/
theorem mk_univ_quaternion : #(Set.univ : Set ℍ[R]) = #R ^ 4 :=
  mk_univ_quaternionAlgebra _ _ _

theorem mk_univ_quaternion_of_infinite [Infinite R] : #(Set.univ : Set ℍ[R]) = #R :=
  mk_univ_quaternionAlgebra_of_infinite _ _ _

end Quaternion

end Cardinal
