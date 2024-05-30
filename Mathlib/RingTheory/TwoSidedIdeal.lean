/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.RingTheory.Congruence
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic.Abel

/-!
# Two Sided Ideals

In this file, for any `Ring R`, we reinterpret `I : RingCon R` as a two sided ideal of a ring.

-/

section ideal

namespace RingCon

variable {R : Type*} [Ring R]

instance : SetLike (RingCon R) R where
  coe t := {r | t r 0}
  coe_injective' t₁ t₂ (h : {x | _} = {x | _}) := by
    refine RingCon.ext fun a b ↦ ⟨fun H ↦ ?_, fun H ↦ ?_⟩
    · have H' : a - b ∈ {x | t₁ x 0} := sub_self b ▸  t₁.sub H (t₁.refl b)
      rw [h] at H'
      convert t₂.add H' (t₂.refl b) using 1 <;> abel
    · have H' : a - b ∈ {x | t₂ x 0} := sub_self b ▸  t₂.sub H (t₂.refl b)
      rw [← h] at H'
      convert t₁.add H' (t₁.refl b) using 1 <;> abel

lemma le_iff (I J : RingCon R) : I ≤ J ↔ (I : Set R) ⊆ (J : Set R) := by
  constructor
  · intro h x hx
    exact h hx
  · intro h x y hxy
    have h' : J _ _ := h <| sub_self y ▸ I.sub hxy (I.refl y)
    convert J.add h' (J.refl y) <;>
    abel

lemma lt_iff (I J : RingCon R) : I < J ↔ (I : Set R) ⊂ (J : Set R) := by
  rw [lt_iff_le_and_ne, Set.ssubset_iff_subset_ne, le_iff]
  simp

variable (I : RingCon R)

lemma zero_mem : 0 ∈ I := I.refl 0

lemma add_mem {x y} (hx : x ∈ I) (hy : y ∈ I) : x + y ∈ I := by
  simpa using I.add hx hy

lemma neg_mem {x} (hx : x ∈ I) : -x ∈ I := by
  simpa using I.neg hx

lemma sub_mem {x y} (hx : x ∈ I) (hy : y ∈ I) : x - y ∈ I := by
  convert I.add_mem hx (I.neg_mem hy) using 1; abel

lemma mul_mem_left (x y) (hy : y ∈ I) : x * y ∈ I := by
  simpa using I.mul (I.refl x) hy

lemma mul_mem_right (x y) (hx : x ∈ I) : x * y ∈ I := by
  simpa using I.mul hx (I.refl y)

instance : Add I where add x y := ⟨x.1 + y.1, I.add_mem x.2 y.2⟩

instance : Zero I where zero := ⟨0, I.zero_mem⟩

instance : SMul ℕ I where
  smul n x := ⟨n • x.1, n.rec (by simpa using I.zero_mem) fun n hn ↦ by
    simpa only [Nat.succ_eq_add_one, add_smul, one_smul] using I.add_mem hn x.2⟩

instance : Neg I where neg x := ⟨-x.1, I.neg_mem x.2⟩

instance : Sub I where sub x y := ⟨x.1 - y.1, I.sub_mem x.2 y.2⟩

instance : SMul ℤ I where
  smul n x := ⟨n • x.1, n.rec (fun a ↦ a.rec (by simpa using I.zero_mem)
    (fun a ha ↦ by
      simp only [Nat.succ_eq_add_one, Int.ofNat_eq_coe, Nat.cast_add, Nat.cast_one,
        Int.cast_add, Int.cast_natCast, Int.cast_one, add_smul, one_smul]
      exact I.add_mem ha x.2))
    (fun a ↦ a.rec (by simpa using I.neg_mem x.2)
    (fun a ha ↦ by
      simp only [Nat.succ_eq_add_one, negSucc_zsmul, nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
        add_mul, one_mul, neg_add_rev] at ha ⊢
      exact I.add_mem (I.neg_mem x.2) ha))⟩

instance : AddCommGroup I :=
  Function.Injective.addCommGroup (fun (x : I) ↦ x.1) (fun _ _ h ↦ by ext; exact h)
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance : Module R I where
  smul r x := ⟨r * x.1, I.mul_mem_left _ _ x.2⟩
  one_smul x := by ext; show 1 * x.1 = x.1; simp
  mul_smul x y z := by
    ext; show (x * y) * z.1 = x * (y * z.1); simp [mul_assoc]
  smul_zero x := by
    ext; show x * 0 = 0; simp
  smul_add x y z := by
    ext; show x • (y.1 + z.1) = x • y.1 + x • z.1; simp [mul_add]
  add_smul x y z := by
    ext; show (x + y) • z.1 = x • z.1 + y • z.1; simp [add_mul]
  zero_smul x := by
    ext; show 0 * x.1 = 0; simp

instance : Module Rᵐᵒᵖ I where
  smul r x := ⟨x.1 * r.unop, I.mul_mem_right _ _ x.2⟩
  one_smul x := by ext; show x.1 * 1 = x.1; simp
  mul_smul x y z := by
    ext; show z.1 * (y.unop * x.unop) = (z.1 * y.unop) * x.unop; simp only [mul_assoc]
  smul_zero x := by
    ext; show 0 * _ = 0; simp only [zero_mul]
  smul_add x y z := by
    ext; show (y.1 + z.1) * _ = (y * _) + (z * _); simp only [right_distrib]
  add_smul x y z := by
    ext; show _ * (_ + _) = _ * _ + _ * _; simp only [left_distrib]
  zero_smul x := by
    ext; show _ * 0 = 0; simp only [mul_zero]

end RingCon

end ideal
