import Mathlib.LinearAlgebra.TensorAlgebra.Basic
import Mathlib.Tactic

variable (R : Type*) [CommSemiring R]

open TensorAlgebra Additive in
inductive SteinbergRel :
    (TensorAlgebra ℤ <| Additive Rˣ) →
    (TensorAlgebra ℤ <| Additive Rˣ) →
    Prop where
  | mk (a b : Rˣ) : (a : R) + b = 1 →
    SteinbergRel (ι _ (ofMul a) * ι _ (ofMul b)) 0

def MilnorK := RingQuot <| SteinbergRel R

instance : Ring (MilnorK R) :=
  inferInstanceAs <| Ring <| RingQuot <| SteinbergRel R

def tensorAlgebraToMilnorK : TensorAlgebra ℤ (Additive Rˣ) →+* MilnorK R :=
  RingQuot.mkRingHom _

namespace MilnorK

variable {R}

def ι (x : Rˣ) : MilnorK R :=
  tensorAlgebraToMilnorK _ <| .ι _ <| .ofMul x

syntax "{" term,+ "}ₘ" : term

macro_rules
  | `({$x:term}ₘ) => `(MilnorK.ι $x)
  | `({$x:term, $xs:term,*}ₘ) => `((MilnorK.ι $x) * {$xs:term,*}ₘ)

@[simp]
lemma ι_mul (x y : Rˣ) : {x * y}ₘ = {x}ₘ + {y}ₘ := by
  simp only [ι, ofMul_mul, map_add]

@[simp]
lemma ι_one : {(1 : Rˣ)}ₘ = 0 := by
  simp only [ι, ofMul_one, map_zero]

@[simp]
lemma ι_inv (x : Rˣ) : {x⁻¹}ₘ = -{x}ₘ := by
  simp only [ι, ofMul_inv, map_neg]

lemma eq_zero_of_steinberg (x y : Rˣ) (h : (x : R) + y = 1) : {x,y}ₘ = 0 := by
  dsimp [ι, tensorAlgebraToMilnorK]
  rw [← RingHom.map_mul, ← (RingQuot.mkRingHom (SteinbergRel R)).map_zero]
  apply RingQuot.mkRingHom_rel
  exact SteinbergRel.mk _ _ h

variable {F : Type*} [Field F]

@[simp]
lemma mul_neg_self (x : Fˣ) : {x,-x}ₘ = 0 := by
  by_cases h : 1 = x
  · simp [← h]
  · have hx1 : ((1 : F) - x) ≠ 0 := by
      rw [sub_ne_zero]
      contrapose! h
      ext
      assumption
    let y : Fˣ := Units.mk0 _ hx1
    have h' : 1 ≠ x⁻¹ := by
      simp only [ne_eq, one_eq_inv]
      contrapose! h
      exact h.symm
    have hx2 : (1 : F) - ↑(x⁻¹) ≠ 0 := by
      rw [sub_ne_zero]
      contrapose! h'
      ext
      assumption
    let z : Fˣ := Units.mk0 _ hx2
    have : {x, -x}ₘ + {x, -y * x⁻¹}ₘ = 0 := by
      rw [← mul_add, ← ι_mul]
      apply eq_zero_of_steinberg
      simp only [neg_mul, mul_neg, mul_inv_cancel_comm_assoc, neg_neg, Units.val_mk0,
        add_sub_cancel, y]
    calc
      {x, -x}ₘ = -{x, -y * x⁻¹}ₘ := by
        rwa [add_eq_zero_iff_eq_neg] at this
      _ = -{x, z}ₘ := by
        congr 3
        ext
        field_simp [y, z]
      _ = {x⁻¹, z}ₘ := by
        rw [neg_mul_eq_neg_mul, ι_inv]
      _ = 0 := by
        apply eq_zero_of_steinberg
        simp [z]

lemma mul_self (x : Fˣ) : {x, x}ₘ = {x, -1}ₘ := by
  conv =>
    enter [1, 2]
    rw [show x = (-x) * (-1) by simp]
  rw [ι_mul]
  simp only [mul_add, mul_neg_self, zero_add]

lemma mul_symm_eq_neg_mul (x y : Fˣ) : {x,y}ₘ = -{y,x}ₘ := by
  rw [← add_eq_zero_iff_eq_neg]
  calc
    _ = {x, -x}ₘ + {x, y}ₘ + {y, x}ₘ + {y, -y}ₘ := by simp
    _ = {x * y, -(x * y)}ₘ := by
      rw [ι_mul x y, add_mul]
      nth_rewrite 1 [show -(x * y) = (-x) * y by simp]
      nth_rewrite 1 [show -(x * y) = x * (-y) by simp]
      simp only [ι_mul, mul_neg_self, zero_add, add_zero, mul_add]
    _ = 0 := mul_neg_self _

end MilnorK
