/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang, Violeta Hernández Palacios
-/
import Mathlib.Algebra.Order.Archimedean.Class
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.RingTheory.Valuation.Basic

/-!
# Archimedean classes of a linearly ordered ring

Archimedean classes over a strictly linearly ordered ring form an abelian monoid itself.
Moreover, we show it is a valuation of the ring.

-/



namespace ArchimedeanClass
variable [LinearOrder M] [CommRing M] [IsStrictOrderedRing M]

instance : Zero (ArchimedeanClass M) where
  zero := mk 1

@[simp] theorem mk_one : mk (1 : M) = 0 := rfl

private theorem mk_mul_le_of_le {x₁ y₁ x₂ y₂ : M} (hx : mk x₁ ≤ mk x₂) (hy : mk y₁ ≤ mk y₂) :
    mk (x₁ * y₁) ≤ mk (x₂ * y₂) := by
  obtain ⟨m, hm⟩ := hx
  obtain ⟨n, hn⟩ := hy
  use m * n
  convert mul_le_mul hm hn (abs_nonneg _) (nsmul_nonneg (abs_nonneg _) _) using 1 <;>
    simp_rw [ArchimedeanOrder.val_of, abs_mul]
  ring

instance : Add (ArchimedeanClass M) where
  add := Quotient.lift₂ (fun x y ↦ .mk <| x.val * y.val) fun _ _ _ _ hx hy ↦
    (mk_mul_le_of_le hx.le hy.le).antisymm (mk_mul_le_of_le hx.ge hy.ge)

@[simp] theorem mk_mul (x y : M) : mk (x * y) = mk x + mk y := rfl

instance : SMul ℕ (ArchimedeanClass M) where
  smul n := lift (fun x ↦ mk (x ^ n)) fun x y h ↦ by
    induction n with
    | zero => simp
    | succ n IH => simp_rw [pow_succ, mk_mul, IH, h]

@[simp] theorem mk_pow (n : ℕ) (x : M) : mk (x ^ n) = n • mk x := rfl

instance : AddCommMagma (ArchimedeanClass M) where
  add_comm x y := by
    induction x with | mk x =>
    induction y with | mk y =>
    rw [← mk_mul, mul_comm, mk_mul]

private theorem zero_add' (x : ArchimedeanClass M) : 0 + x = x := by
  induction x with | mk x =>
  rw [← mk_one, ← mk_mul, one_mul]

private theorem add_assoc' (x y z : ArchimedeanClass M) : x + y + z = x + (y + z) := by
  induction x with | mk x =>
  induction y with | mk y =>
  induction z with | mk z =>
  simp_rw [← mk_mul, mul_assoc]

instance : AddCommMonoid (ArchimedeanClass M) where
  add_assoc := add_assoc'
  zero_add := zero_add'
  add_zero x := add_comm x _ ▸ zero_add' x
  nsmul n x := n • x
  nsmul_zero x := by induction x with | mk x => rw [← mk_pow, pow_zero, mk_one]
  nsmul_succ n x := by induction x with | mk x => rw [← mk_pow, pow_succ, mk_mul, mk_pow]

instance : IsOrderedAddMonoid (ArchimedeanClass M) where
  add_le_add_left x y h z := by
    induction x with | mk x =>
    induction y with | mk y =>
    induction z with | mk z =>
    rw [← mk_mul, ← mk_mul]
    exact mk_mul_le_of_le le_rfl h

noncomputable instance : LinearOrderedAddCommMonoidWithTop (ArchimedeanClass M) where
  top_add' x := by
    induction x with | mk x =>
    rw [← mk_zero, ← mk_mul, zero_mul]

end ArchimedeanClass


namespace ArchimedeanClass
variable {M : Type*} [CommRing M] [LinearOrder M] [IsStrictOrderedRing M]

instance : Zero (ArchimedeanClass M) where
  zero := ArchimedeanClass.mk 1

variable (M) in
@[simp]
theorem mk_one : mk (1 : M) = 0 := rfl

/-- Multipilication in `M` transfers to Addition in `ArchimedeanClass M`.
We denote this as an addition instead of multiplication for the following reasons:
* In the ring version of Hahn embedding theorem, `ArchimedeanClassₒ M` naturally becomes
  the additive abelian group for the ring `HahnSeries (ArchimedeanClassₒ M) ℝ`.
* The order we defined on `ArchimedeanClass M` matches the order on `AddValuation`, instead
  of the one on `Valuation`. -/
instance : Add (ArchimedeanClass M) where
  add := lift₂ (fun a b ↦ mk (a * b)) (by
    intro a₁ b₁ a₂ b₂ h₁ h₂
    rw [mk_eq_mk] at ⊢ h₁ h₂
    obtain ⟨⟨m₁, hm₁⟩, ⟨n₁, hn₁⟩⟩ := h₁
    obtain ⟨⟨m₂, hm₂⟩, ⟨n₂, hn₂⟩⟩ := h₂
    simp_rw [abs_mul]
    refine ⟨⟨m₁ * m₂, ?_⟩, ⟨n₁ * n₂, ?_⟩⟩ <;> rw [mul_smul_mul_comm]
    · exact mul_le_mul hm₁ hm₂ (by simp) (nsmul_nonneg (by simp) _)
    · exact mul_le_mul hn₁ hn₂ (by simp) (nsmul_nonneg (by simp) _))

theorem mk_mul (a b : M) : mk (a * b) = mk a + mk b := rfl

noncomputable
instance : LinearOrderedAddCommMonoidWithTop (ArchimedeanClass M) where
  add_assoc A B C := by
    induction A using ind with | mk a
    induction B using ind with | mk b
    induction C using ind with | mk c
    simp [← mk_mul, mul_assoc]
  add_comm A B :=  by
    induction A using ind with | mk a
    induction B using ind with | mk b
    simp [← mk_mul, mul_comm]
  zero_add A := by
    induction A using ind with | mk a
    simp [← mk_one, ← mk_mul]
  add_zero A := by
    induction A using ind with | mk a
    simp [← mk_one, ← mk_mul]
  nsmul := nsmulRec
  top_add' A := by
    induction A using ind with | mk a
    simp [← mk_zero, ← mk_mul]
  add_le_add_left A B h C := by
    induction A using ind with | mk a
    induction B using ind with | mk b
    induction C using ind with | mk c
    simp_rw [← mk_mul]
    rw [mk_le_mk] at ⊢ h
    simp_rw [abs_mul]
    obtain ⟨m, hm⟩ := h
    use m
    rw [mul_comm _ |a|, mul_comm _ |b|, nsmul_eq_mul, ← mul_assoc, ← nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hm (by simp)

theorem add_left_cancel_of_ne_top {A B C : ArchimedeanClass M} (hA : A ≠ ⊤) (h : A + B = A + C) :
    B = C := by
  induction A using ind with | mk a
  induction B using ind with | mk b
  induction C using ind with | mk c
  simp_rw [← mk_mul] at h
  rw [mk_eq_mk] at ⊢ h
  simp_rw [abs_mul] at h
  obtain ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ := h
  rw [mul_comm |a|, mul_comm |a|, nsmul_eq_mul, ← mul_assoc, ← nsmul_eq_mul] at hm hn
  refine ⟨⟨m, ?_⟩, ⟨n, ?_⟩⟩
  · apply le_of_mul_le_mul_right hm
    simpa using hA
  · apply le_of_mul_le_mul_right hn
    simpa using hA

variable (M) in
/-- Non-⊤ elements of `ArchimedeanClass M` form a submonoid, whose induced type is defeq to
  `ArchimedeanClass₀ M`. -/
def neTop : AddSubmonoid (ArchimedeanClass M) where
  carrier := {A | A ≠ ⊤}
  zero_mem' := by simp [← mk_one]
  add_mem' {A B} := by
    induction A using ind with | mk a
    induction B using ind with | mk b
    simpa [← mk_mul] using And.intro

theorem neTop_eq : neTop M = ArchimedeanClass₀ M := rfl

variable (M) in
/-- `ArchimedeanClass.mk` defines a `AddValuation` on ring `M`. -/
noncomputable
def addValuation : AddValuation M (ArchimedeanClass M) := AddValuation.of mk
  (by simp) (by simp) min_le_mk_add mk_mul

@[simp]
theorem addValuation_apply (a : M) : addValuation M a = mk a := rfl

variable {M : Type*} [Field M] [LinearOrder M] [IsStrictOrderedRing M]

instance : Neg (ArchimedeanClass M) where
  neg A := A.lift (fun a ↦ ArchimedeanClass.mk a⁻¹) (fun a b h ↦ by
    by_cases ha0 : a = 0
    · rw [ha0] at h
      have hb0 : b = 0 := by simpa using h.symm
      simp [ha0, hb0]
    · have h0' : mk a ≠ ⊤ := by simpa using ha0
      have hb0 : b ≠ 0 := by
        rw [← mk_eq_top_iff.ne, ← h]
        simpa using ha0
      apply add_left_cancel_of_ne_top h0'
      nth_rw 2 [h]
      simp [← mk_mul, ha0, hb0])

theorem mk_inv (a : M) : mk a⁻¹ = -(mk a) := rfl

noncomputable
instance : LinearOrderedAddCommGroupWithTop (ArchimedeanClass M) where
  zsmul := zsmulRec
  neg_top := by simp [← mk_zero, ← mk_inv]
  add_neg_cancel A h := by
    induction A using ind with | mk a
    simp [← mk_inv, ← mk_mul, mul_inv_cancel₀ (show a ≠ 0 by simpa using h)]

instance : Neg (neTop M) where
  neg A := ⟨-A, by
    by_contra!
    have h : A.val = ⊤ := by simpa [neTop, neg_eq_iff_eq_neg]
    exact A.prop h
  ⟩

@[simp]
theorem coe_neg (A : neTop M) : (-A : neTop M) = -(A : ArchimedeanClass M) := rfl

noncomputable
instance : AddCommGroup (neTop M) where
  zsmul := zsmulRec
  neg_add_cancel A := by
    apply Subtype.ext
    rw [add_comm]
    simpa using LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top A.prop

noncomputable
instance : AddCommGroup (ArchimedeanClass₀ M) := by
  rw [← neTop_eq]
  infer_instance

end ArchimedeanClass
