/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.Tactic.Abel
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.RingTheory.Congruence.Basic

/-!
# Two Sided Ideals

In this file, for any `Ring R`, we reinterpret `I : RingCon R` as a two-sided-ideal of a ring.

## Main definitions and results
* `RingCon.setLike`: Every `I : RingCon R` can be interpreted as a set of `R` where `x ∈ I` if and
  only if `I x 0`. In this sense, two-sided-ideals of `R` are exactly `RingCon R`.

* `RingCon.addCommGroup`: when viewing `I : RingCon R` as a set, it is an abelian group.


-/

open MulOpposite

section ideal

namespace RingCon

section NonUnitalNonAssocRing

variable {R : Type*} [NonUnitalNonAssocRing R] (I : RingCon R)

instance setLike : SetLike (RingCon R) R where
  coe t := {r | t r 0}
  coe_injective' t₁ t₂ (h : {x | _} = {x | _}) := by
    refine RingCon.ext fun a b ↦ ⟨fun H ↦ ?_, fun H ↦ ?_⟩
    · have H' : a - b ∈ {x | t₁ x 0} := sub_self b ▸ t₁.sub H (t₁.refl b)
      rw [h] at H'
      convert t₂.add H' (t₂.refl b) using 1 <;> abel
    · have H' : a - b ∈ {x | t₂ x 0} := sub_self b ▸ t₂.sub H (t₂.refl b)
      rw [← h] at H'
      convert t₁.add H' (t₁.refl b) using 1 <;> abel

lemma mem_iff (x : R) : x ∈ I ↔ I x 0 := Iff.rfl

lemma rel_iff (x y : R) : I x y ↔ x - y ∈ I := by
  rw [mem_iff]
  constructor
  · intro h; convert I.sub h (I.refl y); abel
  · intro h; convert I.add h (I.refl y) <;> abel

/--
the coercion from two-sided-ideals to sets is an order embedding
-/
@[simps]
def coeOrderEmbedding : RingCon R ↪o Set R where
  toFun := SetLike.coe
  inj' := SetLike.coe_injective
  map_rel_iff' {I J} := ⟨fun h x y hxy => by
    convert J.add (h <| sub_self y ▸ I.sub hxy (I.refl y)) (J.refl y) <;>
    abel, fun h _ h' => h h'⟩

lemma le_iff {I J : RingCon R} : I ≤ J ↔ (I : Set R) ⊆ (J : Set R) :=
  coeOrderEmbedding.map_rel_iff.symm

lemma lt_iff (I J : RingCon R) : I < J ↔ (I : Set R) ⊂ (J : Set R) := by
  rw [lt_iff_le_and_ne, Set.ssubset_iff_subset_ne, le_iff]
  simp

lemma zero_mem : 0 ∈ I := I.refl 0

lemma add_mem {x y} (hx : x ∈ I) (hy : y ∈ I) : x + y ∈ I := by simpa using I.add hx hy

lemma neg_mem {x} (hx : x ∈ I) : -x ∈ I := by simpa using I.neg hx

lemma sub_mem {x y} (hx : x ∈ I) (hy : y ∈ I) : x - y ∈ I := by simpa using I.sub hx hy

lemma mul_mem_left (x y) (hy : y ∈ I) : x * y ∈ I := by simpa using I.mul (I.refl x) hy

lemma mul_mem_right (x y) (hx : x ∈ I) : x * y ∈ I := by simpa using I.mul hx (I.refl y)

lemma nsmul_mem {x} (n : ℕ) (hx : x ∈ I) : n • x ∈ I := by simpa using I.nsmul _ hx

lemma zsmul_mem {x} (n : ℤ) (hx : x ∈ I) : n • x ∈ I := by simpa using I.zsmul _ hx

instance : AddSubgroupClass (RingCon R) R where
  zero_mem := zero_mem
  add_mem := @add_mem _ _
  neg_mem := @neg_mem _ _

instance : SMulMemClass (RingCon R) R R where
  smul_mem _ _ h := RingCon.mul_mem_left _ _ _ h

instance : SMulMemClass (RingCon R) Rᵐᵒᵖ R where
  smul_mem _ _ h := RingCon.mul_mem_right _ _ _ h

instance : Add I where add x y := ⟨x.1 + y.1, I.add_mem x.2 y.2⟩

instance : Zero I where zero := ⟨0, I.zero_mem⟩

instance : SMul ℕ I where smul n x := ⟨n • x.1, I.nsmul_mem n x.2⟩

instance : Neg I where neg x := ⟨-x.1, I.neg_mem x.2⟩

instance : Sub I where sub x y := ⟨x.1 - y.1, I.sub_mem x.2 y.2⟩

instance : SMul ℤ I where smul n x := ⟨n • x.1, I.zsmul_mem n x.2⟩

instance addCommGroup : AddCommGroup I :=
  Function.Injective.addCommGroup _ Subtype.coe_injective
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

end NonUnitalNonAssocRing

end RingCon

end ideal
