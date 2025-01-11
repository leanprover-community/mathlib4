/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Yunzhou Xie
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.NoZeroSMulDivisors.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring.Basic

/-!
# General Quaternion Algebras
Following Bourbaki's definition of quaternion algebra over general rings and discussion
on zulip, we define quaternion algebras over a commutative ring `R` with three coefficients
`a, b, c` where `i^2 = a + bi`, `j^2 = c`, `k^2 = - (a * c)`, etc.

## Main Instances
- `QuaternionAlgebra'.instRing`: general quaternion algebra over a commutative ring `R` with
  coefficients `a, b, c` forms a ring.

## References

* [Bourbaki, *Algebra I*][bourbaki1989]

## Tags

Quaternion algebra, Noncommutative algebra
-/

/-- Quaternion algebra over a type with fixed coefficients `a, b, c`.
Implemented as a structure with four fields: `re`, `imI`, `imJ`, and `imK`. -/
@[ext]
structure QuaternionAlgebra' (R : Type*) (a b c : R) where
  /-- Real part of a quaternion. -/
  re : R
  /-- First imaginary part (i) of a quaternion. -/
  imI : R
  /-- Second imaginary part (j) of a quaternion. -/
  imJ : R
  /-- Third imaginary part (k) of a quaternion. -/
  imK : R

@[inherit_doc]
scoped[Quaternion] notation "ℍ[" R "," a "," b ", " c "]" =>
    QuaternionAlgebra' R a b c

open Quaternion

namespace QuaternionAlgebra'

/-- The equivalence between a quaternion algebra over `R` and `R × R × R × R`. -/
@[simps]
def equivProd {R : Type*} (c₁ c₂ c₃: R) : ℍ[R,c₁,c₂, c₃] ≃ R × R × R × R where
  toFun a := ⟨a.1, a.2, a.3, a.4⟩
  invFun a := ⟨a.1, a.2.1, a.2.2.1, a.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The equivalence between a quaternion algebra over `R` and `Fin 4 → R`. -/
@[simps symm_apply]
def equivTuple {R : Type*} (c₁ c₂ c₃: R) : ℍ[R,c₁,c₂, c₃] ≃ (Fin 4 → R) where
  toFun a := ![a.1, a.2, a.3, a.4]
  invFun a := ⟨a 0, a 1, a 2, a 3⟩
  left_inv _ := rfl
  right_inv f := by ext ⟨_, _ | _ | _ | _ | _ | ⟨⟩⟩ <;> rfl

@[simp]
theorem equivTuple_apply {R : Type*} (c₁ c₂ c₃: R) (x : ℍ[R,c₁,c₂, c₃]) :
    equivTuple c₁ c₂ c₃ x = ![x.re, x.imI, x.imJ, x.imK] :=
  rfl

@[simp]
theorem mk.eta {R : Type*} {c₁ c₂ c₃} (a : ℍ[R,c₁,c₂, c₃]) :
    mk a.1 a.2 a.3 a.4 = a := rfl


variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y z : R) (a b c : ℍ[R,c₁,c₂, c₃])
instance [Subsingleton R] : Subsingleton ℍ[R,c₁,c₂, c₃] := (equivTuple _ _ _).subsingleton
instance [Nontrivial R] : Nontrivial ℍ[R, c₁, c₂, c₃] := (equivTuple _ _ _).surjective.nontrivial

section Zero
variable [Zero R]

/-- Coercion `R → ℍ[R,c₁,c₂,c₃]`. -/
@[coe] def coe (x : R) : ℍ[R,c₁,c₂,c₃] := ⟨x, 0, 0, 0⟩

instance : CoeTC R ℍ[R,c₁,c₂,c₃] := ⟨coe⟩

@[simp, norm_cast]
theorem coe_re : (x : ℍ[R,c₁,c₂,c₃]).re = x := rfl

@[simp, norm_cast]
theorem coe_imI : (x : ℍ[R,c₁,c₂,c₃]).imI = 0 := rfl

@[simp, norm_cast]
theorem coe_imJ : (x : ℍ[R,c₁,c₂,c₃]).imJ = 0 := rfl

@[simp, norm_cast]
theorem coe_imK : (x : ℍ[R,c₁,c₂,c₃]).imK = 0 := rfl

theorem coe_injective : Function.Injective (coe : R → ℍ[R,c₁,c₂,c₃]) :=
    fun _ _ h => congr_arg re h

@[simp]
theorem coe_inj {x y : R} : (x : ℍ[R,c₁,c₂,c₃]) = y ↔ x = y :=
  coe_injective.eq_iff

-- Porting note: removed `simps`, added simp lemmas manually
instance : Zero ℍ[R,c₁,c₂,c₃] := ⟨⟨0, 0, 0, 0⟩⟩

@[simp] theorem zero_re : (0 : ℍ[R,c₁,c₂,c₃]).re = 0 := rfl

@[simp] theorem zero_imI : (0 : ℍ[R,c₁,c₂,c₃]).imI = 0 := rfl

@[simp] theorem zero_imJ : (0 : ℍ[R,c₁,c₂,c₃]).imJ = 0 := rfl

@[simp] theorem zero_imK : (0 : ℍ[R,c₁,c₂,c₃]).imK = 0 := rfl

@[simp, norm_cast]
theorem coe_zero : ((0 : R) : ℍ[R,c₁,c₂,c₃]) = 0 := rfl

instance : Inhabited ℍ[R,c₁,c₂,c₃] := ⟨0⟩

section One
variable [One R]
-- Porting note: removed `simps`, added simp lemmas manually
instance : One ℍ[R,c₁,c₂,c₃] := ⟨⟨1, 0, 0, 0⟩⟩

@[simp] theorem one_re : (1 : ℍ[R,c₁,c₂,c₃]).re = 1 := rfl

@[simp] theorem one_imI : (1 : ℍ[R,c₁,c₂,c₃]).imI = 0 := rfl

@[simp] theorem one_imJ : (1 : ℍ[R,c₁,c₂,c₃]).imJ = 0 := rfl

@[simp] theorem one_imK : (1 : ℍ[R,c₁,c₂,c₃]).imK = 0 := rfl

@[simp, norm_cast]
theorem coe_one : ((1 : R) : ℍ[R,c₁,c₂,c₃]) = 1 := rfl

end One

end Zero

section Add
variable [Add R]

-- Porting note: removed `simps`, added simp lemmas manually
instance : Add ℍ[R,c₁,c₂,c₃] :=
  ⟨fun a b => ⟨a.1 + b.1, a.2 + b.2, a.3 + b.3, a.4 + b.4⟩⟩

@[simp] theorem add_re : (a + b).re = a.re + b.re := rfl

@[simp] theorem add_imI : (a + b).imI = a.imI + b.imI := rfl

@[simp] theorem add_imJ : (a + b).imJ = a.imJ + b.imJ := rfl

@[simp] theorem add_imK : (a + b).imK = a.imK + b.imK := rfl

@[simp]
theorem mk_add_mk (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R) :
    (mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃]) + mk b₁ b₂ b₃ b₄ =
    mk (a₁ + b₁) (a₂ + b₂) (a₃ + b₃) (a₄ + b₄) :=
  rfl

end Add

section AddZeroClass
variable [AddZeroClass R]

@[simp, norm_cast]
theorem coe_add : ((x + y : R) : ℍ[R,c₁,c₂,c₃]) = x + y := by ext <;> simp

end AddZeroClass

section Neg
variable [Neg R]

-- Porting note: removed `simps`, added simp lemmas manually
instance : Neg ℍ[R,c₁,c₂,c₃] := ⟨fun a => ⟨-a.1, -a.2, -a.3, -a.4⟩⟩

@[simp] theorem neg_re : (-a).re = -a.re := rfl

@[simp] theorem neg_imI : (-a).imI = -a.imI := rfl

@[simp] theorem neg_imJ : (-a).imJ = -a.imJ := rfl

@[simp] theorem neg_imK : (-a).imK = -a.imK := rfl

@[simp]
theorem neg_mk (a₁ a₂ a₃ a₄ : R) : -(mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃]) = ⟨-a₁, -a₂, -a₃, -a₄⟩ :=
  rfl

end Neg

section AddGroup
variable [AddGroup R]

@[simp, norm_cast]
theorem coe_neg : ((-x : R) : ℍ[R,c₁,c₂,c₃]) = -x := by ext <;> simp

instance : Sub ℍ[R,c₁,c₂,c₃] :=
  ⟨fun a b => ⟨a.1 - b.1, a.2 - b.2, a.3 - b.3, a.4 - b.4⟩⟩

@[simp] theorem sub_re : (a - b).re = a.re - b.re := rfl

@[simp] theorem sub_imI : (a - b).imI = a.imI - b.imI := rfl
@[simp] theorem sub_imJ : (a - b).imJ = a.imJ - b.imJ := rfl

@[simp] theorem sub_imK : (a - b).imK = a.imK - b.imK := rfl

@[simp]
theorem mk_sub_mk (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R) :
    (mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃]) - mk b₁ b₂ b₃ b₄ =
    mk (a₁ - b₁) (a₂ - b₂) (a₃ - b₃) (a₄ - b₄) :=
  rfl

end AddGroup

section Ring
variable [Ring R]

/-- Multiplication is given by
## Fixed
 -/
instance : Mul ℍ[R,c₁,c₂,c₃] :=
  ⟨fun a b =>
    ⟨a.1 * b.1 + c₁ * a.2 * b.2 + c₃ * a.3 * b.3 + c₂ * c₃ * a.3 * b.4 - c₁ * c₃ * a.4 * b.4,
    a.1 * b.2 + a.2 * b.1 + c₂ * a.2 * b.2 - c₃ * a.3 * b.4 + c₃ * a.4 * b.3,
    a.1 * b.3 + c₁ * a.2 * b.4 + a.3 * b.1 + c₂ * a.3 * b.2 - c₁ * a.4 * b.2,
    a.1 * b.4 + a.2 * b.3 + c₂ * a.2 * b.4 - a.3 * b.2 + a.4 * b.1⟩⟩

@[simp]
theorem mul_re : (a * b).re = a.1 * b.1 + c₁ * a.2 * b.2 + c₃ * a.3 * b.3 +
    c₂ * c₃ * a.3 * b.4 - c₁ * c₃ * a.4 * b.4 := rfl

@[simp]
theorem mul_imI : (a * b).imI = a.1 * b.2 + a.2 * b.1 +
    c₂ * a.2 * b.2 - c₃ * a.3 * b.4 + c₃ * a.4 * b.3 := rfl

@[simp]
theorem mul_imJ : (a * b).imJ = a.1 * b.3 + c₁ * a.2 * b.4 + a.3 * b.1 +
    c₂ * a.3 * b.2 - c₁ * a.4 * b.2 := rfl

@[simp]
theorem mul_imK : (a * b).imK = a.1 * b.4 + a.2 * b.3 +
    c₂ * a.2 * b.4 - a.3 * b.2 + a.4 * b.1 := rfl

@[simp]
theorem mk_mul_mk (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R) :
    (mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃]) * mk b₁ b₂ b₃ b₄ =
    mk (a₁ * b₁ + c₁ * a₂ * b₂ + c₃ * a₃ * b₃ + c₂ * c₃ * a₃ * b₄ - c₁ * c₃ * a₄ * b₄)
    (a₁ * b₂ + a₂ * b₁ + c₂ * a₂ * b₂ - c₃ * a₃ * b₄ + c₃ * a₄ * b₃)
    (a₁ * b₃ + c₁ * a₂ * b₄ + a₃ * b₁ + c₂ * a₃ * b₂ - c₁ * a₄ * b₂)
    (a₁ * b₄ + a₂ * b₃ + c₂ * a₂ * b₄ - a₃ * b₂ + a₄ * b₁) :=
  rfl

end Ring
section SMul

variable [SMul S R] [SMul T R] (s : S)

instance : SMul S ℍ[R,c₁,c₂, c₃] where smul s a := ⟨s • a.1, s • a.2, s • a.3, s • a.4⟩

instance [SMul S T] [IsScalarTower S T R] : IsScalarTower S T ℍ[R,c₁,c₂,c₃] where
  smul_assoc s t x := by ext <;> exact smul_assoc _ _ _

instance [SMulCommClass S T R] : SMulCommClass S T ℍ[R,c₁,c₂,c₃] where
  smul_comm s t x := by ext <;> exact smul_comm _ _ _

@[simp] theorem smul_re : (s • a).re = s • a.re := rfl

@[simp] theorem smul_imI : (s • a).imI = s • a.imI := rfl

@[simp] theorem smul_imJ : (s • a).imJ = s • a.imJ := rfl

@[simp] theorem smul_imK : (s • a).imK = s • a.imK := rfl

@[simp]
theorem smul_mk (re im_i im_j im_k : R) :
    s • (⟨re, im_i, im_j, im_k⟩ : ℍ[R,c₁,c₂,c₃]) = ⟨s • re, s • im_i, s • im_j, s • im_k⟩ :=
  rfl

end SMul

@[simp, norm_cast]
theorem coe_smul [Zero R] [SMulZeroClass S R] (s : S) (r : R) :
    (↑(s • r) : ℍ[R,c₁,c₂,c₃]) = s • (r : ℍ[R,c₁,c₂,c₃]) :=
  QuaternionAlgebra'.ext rfl (smul_zero s).symm (smul_zero s).symm (smul_zero s).symm

instance [AddCommGroup R] : AddCommGroup ℍ[R,c₁,c₂,c₃] :=
  (equivProd c₁ c₂ c₃).injective.addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

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
theorem natCast_re (n : ℕ) : (n : ℍ[R,c₁,c₂,c₃]).re = n :=
  rfl

@[simp, norm_cast]
theorem natCast_imI (n : ℕ) : (n : ℍ[R,c₁,c₂,c₃]).imI = 0 :=
  rfl

@[simp, norm_cast]
theorem natCast_imJ (n : ℕ) : (n : ℍ[R,c₁,c₂,c₃]).imJ = 0 :=
  rfl

@[simp, norm_cast]
theorem natCast_imK (n : ℕ) : (n : ℍ[R,c₁,c₂,c₃]).imK = 0 :=
  rfl

@[norm_cast]
theorem coe_natCast (n : ℕ) : ↑(n : R) = (n : ℍ[R,c₁,c₂,c₃]) :=
  rfl

@[simp, norm_cast]
theorem intCast_re (z : ℤ) : (z : ℍ[R,c₁,c₂,c₃]).re = z :=
  rfl

@[simp, norm_cast]
theorem intCast_imI (z : ℤ) : (z : ℍ[R,c₁,c₂,c₃]).imI = 0 :=
  rfl

@[simp, norm_cast]
theorem intCast_imJ (z : ℤ) : (z : ℍ[R,c₁,c₂,c₃]).imJ = 0 :=
  rfl

@[simp, norm_cast]
theorem intCast_imK (z : ℤ) : (z : ℍ[R,c₁,c₂,c₃]).imK = 0 :=
  rfl

@[norm_cast]
theorem coe_intCast (z : ℤ) : ↑(z : R) = (z : ℍ[R,c₁,c₂,c₃]) :=
  rfl

end AddCommGroupWithOne

-- For the remainder of the file we assume `CommRing R`.
variable [CommRing R]

instance instRing : Ring ℍ[R,c₁,c₂,c₃] where
  __ := inferInstanceAs (AddCommGroupWithOne ℍ[R,c₁,c₂,c₃])
  left_distrib _ _ _ := by ext <;> simp <;> ring1!
  right_distrib _ _ _ := by ext <;> simp <;> ring1!
  zero_mul _ := by ext <;> simp
  mul_zero _ := by ext <;> simp
  mul_assoc α β γ := by
    ext <;> simp <;> ring1!
  one_mul _ := by ext <;> simp
  mul_one _ := by ext <;> simp

@[norm_cast, simp]
theorem coe_mul : ((x * y : R) : ℍ[R,c₁,c₂, c₃]) = x * y := by ext <;> simp

instance [CommSemiring S] [Algebra S R] : Algebra S ℍ[R,c₁,c₂,c₃] where
  smul := (· • ·)
  toFun s := coe (algebraMap S R s)
  map_one' := by simp only [map_one, coe_one]
  map_zero' := by simp only [map_zero, coe_zero]
  map_mul' x y := by simp only [map_mul, coe_mul]
  map_add' x y := by simp only [map_add, coe_add]
  smul_def' s x := by ext <;> simp [Algebra.smul_def]
  commutes' s x := by ext <;> simp [Algebra.commutes]

theorem algebraMap_eq (r : R) : algebraMap R ℍ[R,c₁,c₂,c₃] r = ⟨r, 0, 0, 0⟩ :=
  rfl

theorem algebraMap_injective : (algebraMap R ℍ[R,c₁,c₂,c₃] : _ → _).Injective :=
  fun _ _ ↦ by simp [algebraMap_eq]

instance [NoZeroDivisors R] : NoZeroSMulDivisors R ℍ[R,c₁,c₂,c₃] := ⟨by
  rintro t ⟨a, b, c, d⟩ h
  rw [or_iff_not_imp_left]
  intro ht
  simpa [QuaternionAlgebra'.ext_iff, ht] using h⟩

end QuaternionAlgebra'
