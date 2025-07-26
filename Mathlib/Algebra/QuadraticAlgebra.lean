/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Kenny Lau
-/

import Mathlib

/-!

# R[X] / (X² − a • X − b)

TODO: Add module docstring
-/
-- a + b α
universe u

/-- `R[X]/(X^2−a*X−b)` -/
@[ext]
structure QuadraticAlgebra (R : Type u) (a b : R) : Type u where
  /-- TODO: Add docstring -/
  re : R
  /-- TODO: Add docstring -/
  im : R

namespace QuadraticAlgebra

/-- The equivalence between quadratic algebra over `R` and `R × R`. -/
@[simps]
def equivProd {R : Type*} (a b : R) : QuadraticAlgebra R a b ≃ R × R where
  toFun z := (z.re, z.im)
  invFun p := ⟨p.1, p.2⟩

/-- The equivalence between quadratic algebra over `R` and `Fin 2 → R`. -/
@[simps symm_apply]
def equivTuple {R : Type*} (a b : R) : QuadraticAlgebra R a b ≃ (Fin 2 → R) where
  toFun a := ![a.1, a.2]
  invFun f := ⟨f 0, f 1⟩
  right_inv _ := funext fun i ↦ by fin_cases i <;> simp

@[simp]
theorem equivTuple_apply {R : Type*} (a b : R) (z : QuadraticAlgebra R a b) :
    equivTuple a b z = ![z.re, z.im] := rfl

@[simp]
theorem mk_eta {R : Type*} {a b} (z : QuadraticAlgebra R a b) :
    mk z.re z.im = z := rfl

variable {S T R : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

instance [Subsingleton R] : Subsingleton (QuadraticAlgebra R a b) := (equivTuple a b).subsingleton

instance [Nontrivial R] : Nontrivial (QuadraticAlgebra R a b) := (equivTuple a b).nontrivial

section Zero

variable [Zero R]

/-- Coercion `R → ℍ[R,c₁,c₂,c₃]`. -/
@[coe] def coe (x : R) : QuadraticAlgebra R a b := ⟨x, 0⟩

instance : CoeTC R (QuadraticAlgebra R a b) := ⟨coe⟩

@[simp, norm_cast]
theorem coe_re : (r : QuadraticAlgebra R a b).re = r := rfl

@[simp, norm_cast]
theorem coe_im : (r : QuadraticAlgebra R a b).im = 0 := rfl

theorem coe_injective : Function.Injective (coe : R → QuadraticAlgebra R a b) :=
  fun _ _ h => congr_arg re h

@[simp]
theorem coe_inj {x y : R} : (x : QuadraticAlgebra R a b) = y ↔ x = y :=
  coe_injective.eq_iff

instance : Zero (QuadraticAlgebra R a b) := ⟨⟨0, 0⟩⟩

@[scoped simp] theorem zero_re : (0 : QuadraticAlgebra R a b).re = 0 := rfl

@[scoped simp] theorem zero_im : (0 : QuadraticAlgebra R a b).im = 0 := rfl

@[simp, norm_cast]
theorem coe_zero : ((0 : R) : QuadraticAlgebra R a b) = 0 := rfl

instance : Inhabited (QuadraticAlgebra R a b) := ⟨0⟩

section One
variable [One R]

instance : One (QuadraticAlgebra R a b) := ⟨⟨1, 0⟩⟩

@[scoped simp] theorem one_re : (1 : QuadraticAlgebra R a b).re = 1 := rfl

@[scoped simp] theorem one_im : (1 : QuadraticAlgebra R a b).im = 0 := rfl

@[simp, norm_cast]
theorem coe_one : ((1 : R) : QuadraticAlgebra R a b) = 1 := rfl

end One

end Zero

section Add

variable [Add R]

instance : Add (QuadraticAlgebra R a b) where
  add z w := ⟨z.re + w.re, z.im + w.im⟩

@[simp] theorem add_re (z w : QuadraticAlgebra R a b) :
    (z + w).re = z.re + w.re := rfl

@[simp] theorem add_im (z w : QuadraticAlgebra R a b) :
    (z + w).im = z.im + w.im := rfl

@[simp]
theorem mk_add_mk (z w : QuadraticAlgebra R a b) :
    mk z.re z.im + mk w.re w.im = (mk (z.re + w.re) (z.im + w.im) : QuadraticAlgebra R a b) := rfl

end Add

section AddZeroClass

variable [AddZeroClass R]

@[simp]
theorem coe_add (x y : R) : ((x + y : R) : QuadraticAlgebra R a b) = x + y := by ext <;> simp

end AddZeroClass

section Neg

variable [Neg R]

instance : Neg (QuadraticAlgebra R a b) where neg z := ⟨-z.re, -z.im⟩

@[simp] theorem neg_re (z : QuadraticAlgebra R a b) : (-z).re = -z.re := rfl

@[simp] theorem neg_im (z : QuadraticAlgebra R a b) : (-z).im = -z.im := rfl

@[simp]
theorem neg_mk (x y : R) :
    - (mk x y : QuadraticAlgebra R a b) = ⟨-x, -y⟩ := rfl

end Neg

section AddGroup

@[simp]
theorem coe_neg [NegZeroClass R] (x : R) :
    ((-x : R) : QuadraticAlgebra R a b) = -x := by ext <;> simp

instance [Sub R] : Sub (QuadraticAlgebra R a b) where
  sub z w := ⟨z.re - w.re, z.im - w.im⟩

@[simp] theorem sub_re [Sub R] (z w : QuadraticAlgebra R a b) :
    (z - w).re = z.re - w.re := rfl

@[simp] theorem sub_im [Sub R] (z w : QuadraticAlgebra R a b) :
    (z - w).im = z.im - w.im := rfl

@[simp]
theorem mk_sub_mk [Sub R] (x1 y1 x2 y2 : R) :
    (mk x1 y1 : QuadraticAlgebra R a b) - mk x2 y2 = mk (x1 - x2) (y1 - y2) := rfl

end AddGroup

section Ring

variable [Mul R] [Add R]

instance : Mul (QuadraticAlgebra R a b) :=
  ⟨fun z w => ⟨z.1 * w.1 + b * z.2 * w.2, z.1 * w.2 + z.2 * w.1 + a * z.2 * w.2⟩⟩

@[simp] theorem mul_re (z w : QuadraticAlgebra R a b) :
    (z * w).re = z.re * w.re + b * z.im * w.im := rfl

@[simp] theorem mul_im (z w : QuadraticAlgebra R a b) :
    (z * w).im = z.re * w.im + z.im * w.re + a * z.im * w.im := rfl

@[simp]
theorem mk_mul_mk (x1 y1 x2 y2 : R) :
    (mk x1 y1 : QuadraticAlgebra R a b) * mk x2 y2 =
    mk (x1 * x2 + b * y1 * y2) (x1 * y2 + y1 * x2 + a * y1 * y2) := rfl

end Ring

section SMul

variable [SMul S R] [SMul T R] (s : S)

instance : SMul S (QuadraticAlgebra R a b) where smul s z := ⟨s • z.re, s • z.im⟩

instance [SMul S T] [IsScalarTower S T R] : IsScalarTower S T (QuadraticAlgebra R a b) where
  smul_assoc s t z := by ext <;> exact smul_assoc _ _ _

instance [SMulCommClass S T R] : SMulCommClass S T (QuadraticAlgebra R a b) where
  smul_comm s t z := by ext <;> exact smul_comm _ _ _

@[simp] theorem smul_re (s : S) (z : QuadraticAlgebra R a b) : (s • z).re = s • z.re := rfl

@[simp] theorem smul_im (s : S) (z : QuadraticAlgebra R a b) : (s • z).im = s • z.im := rfl

@[simp]
theorem smul_mk (s : S) (x y : R) :
    s • (mk x y : QuadraticAlgebra R a b) = mk (s • x) (s • y) := rfl

end SMul

section MulAction

instance [Monoid S] [MulAction S R] : MulAction S (QuadraticAlgebra R a b) where
  one_smul x := by ext <;> simp
  mul_smul x y b_1:= by ext <;> simp[mul_smul]

end MulAction

@[simp, norm_cast]
theorem coe_smul [Zero R] [SMulZeroClass S R] (s : S) (r : R) :
    (↑(s • r) : QuadraticAlgebra R a b) = s • (r : QuadraticAlgebra R a b) :=
  QuadraticAlgebra.ext rfl (smul_zero _).symm

instance [AddMonoid R] : AddMonoid (QuadraticAlgebra R a b) := by
  refine (equivProd a b).injective.addMonoid _ rfl ?_ ?_
  all_goals intros; rfl

instance [Monoid S] [AddMonoid R] [DistribMulAction S R] :
    DistribMulAction S (QuadraticAlgebra R a b) where
  smul_zero a_1:= by ext <;> simp
  smul_add a_1 x y := by ext <;> simp

instance [AddCommMonoid R] : AddCommMonoid (QuadraticAlgebra R a b) where
  __ := inferInstanceAs (AddMonoid (QuadraticAlgebra R a b))
  add_comm _ _ := by ext <;> simp [add_comm]

instance [Semiring S] [AddCommMonoid R] [Module S R] : Module S (QuadraticAlgebra R a b) where
  add_smul r s x:= by ext <;> simp[add_smul]
  zero_smul x:= by ext <;> simp

instance [AddGroup R] : AddGroup (QuadraticAlgebra R a b) := by
  refine (equivProd a b).injective.addGroup _ rfl ?_ ?_ ?_ ?_ ?_
  all_goals intros; rfl

instance [AddCommGroup R] : AddCommGroup (QuadraticAlgebra R a b) where
  __ := inferInstanceAs (AddGroup (QuadraticAlgebra R a b))
  __ := inferInstanceAs (AddCommMonoid (QuadraticAlgebra R a b))

section AddCommGroupWithOne

instance [AddCommMonoidWithOne R] : AddCommMonoidWithOne (QuadraticAlgebra R a b) where
  natCast n := ((n : R) : QuadraticAlgebra R a b)
  natCast_zero := by ext <;> simp
  natCast_succ n:= by ext <;> simp

variable [AddCommGroupWithOne R]

instance : AddCommGroupWithOne (QuadraticAlgebra R a b) where
  intCast n := ((n : R) : QuadraticAlgebra R a b)
  intCast_ofNat n:= by ext <;> simp <;> rfl
  intCast_negSucc n := by ext <;> simp <;> rfl

@[simp, norm_cast]
theorem natCast_re (n : ℕ) : (n : QuadraticAlgebra R a b).re = n := rfl

@[simp, norm_cast]
theorem natCast_im (n : ℕ) : (n : QuadraticAlgebra R a b).im = 0 := rfl

@[norm_cast]
theorem coe_natCast (n : ℕ) : ↑(n : R) = (n : QuadraticAlgebra R a b) := rfl

@[simp, norm_cast]
theorem intCast_re (n : ℤ) : (n : QuadraticAlgebra R a b).re = n := rfl

@[scoped simp]
theorem ofNat_re (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : QuadraticAlgebra R a b).re = ofNat(n) := rfl

@[scoped simp]
theorem ofNat_im (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : QuadraticAlgebra R a b).im = 0 := rfl

@[simp, norm_cast]
theorem intCast_im (n : ℤ) : (n : QuadraticAlgebra R a b).im = 0 := rfl

@[norm_cast]
theorem coe_intCast (n : ℤ) : ↑(n : R) = (n : QuadraticAlgebra R a b) := rfl

end AddCommGroupWithOne

section CommRing

instance instSemiring [CommSemiring R] : Semiring (QuadraticAlgebra R a b) where
  __ := inferInstanceAs (AddCommMonoidWithOne (QuadraticAlgebra R a b))
  left_distrib a_1 b_1 c:= by
    ext
    · simp [left_distrib]
      rw [add_assoc,add_comm (a_1.re * c.re),add_assoc,add_comm (b * a_1.im * c.im),add_assoc]
    · simp [left_distrib]
      rw [add_assoc (a_1.re * b_1.im),add_comm (a_1.re * c.im),add_assoc (a_1.re * b_1.im),
      add_assoc (a_1.im * b_1.re),add_assoc,add_comm (a_1.im * c.re + a_1.re * c.im),add_assoc,
      add_comm (a * a_1.im * c.im),add_comm (a_1.im * c.re)]
      simp [add_assoc]
  right_distrib a_1 b_1 c:= by ext <;> simp <;> ring
  zero_mul a_1 := by ext <;> simp
  mul_zero a_1:= by ext <;> simp
  mul_assoc a_1 b_1 c:= by ext <;> simp <;> ring
  one_mul a_1:= by ext <;> simp
  mul_one a_1:= by ext <;> simp

instance instCommSemiring [CommSemiring R] : CommSemiring (QuadraticAlgebra R a b) where
  __ := inferInstanceAs (Semiring (QuadraticAlgebra R a b))
  mul_comm z w := by ext <;> simp <;> ring

instance instRing [CommRing R] : Ring (QuadraticAlgebra R a b) where
  __ := inferInstanceAs (AddCommGroupWithOne (QuadraticAlgebra R a b))
  __ := inferInstanceAs (Semiring (QuadraticAlgebra R a b))

@[simp, norm_cast]
theorem coe_mul (x y : R) [Semiring R] :
    ((x * y : R) : QuadraticAlgebra R a b) = x * y := by ext <;> simp

@[simp, norm_cast]
theorem coe_ofNat (n : ℕ) [n.AtLeastTwo] [AddCommMonoidWithOne R] :
    ((ofNat(n) : R) : QuadraticAlgebra R a b) = (ofNat(n) : QuadraticAlgebra R a b) := by
  ext <;> rfl


instance [CommSemiring S] [CommSemiring R] [Algebra S R] :
    Algebra S (QuadraticAlgebra R a b) where
  algebraMap.toFun s := coe (algebraMap S R s)
  algebraMap.map_one' := by ext <;> simp
  algebraMap.map_mul' x y:= by ext <;> simp
  algebraMap.map_zero' := by ext <;> simp
  algebraMap.map_add' x y:= by ext <;> simp
  commutes' s z := by ext <;> simp [Algebra.commutes]
  smul_def' s x := by ext <;> simp [Algebra.smul_def]

variable [CommSemiring R]

theorem algebraMap_eq (r : R) : algebraMap R (QuadraticAlgebra R a b) r = ⟨r, 0⟩ := rfl

theorem algebraMap_injective : (algebraMap R (QuadraticAlgebra R a b) : _ → _).Injective :=
  fun _ _ ↦ by simp [algebraMap_eq]

instance [NoZeroDivisors R] : NoZeroSMulDivisors R (QuadraticAlgebra R a b) := ⟨by
  rintro t ⟨x, y⟩ h
  exact or_iff_not_imp_left.2 <| fun ht ↦ by simpa [QuadraticAlgebra.ext_iff, ht] using h⟩

end CommRing

end QuadraticAlgebra
