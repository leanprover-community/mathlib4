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

## Notes
`SetLike (RingCon R) R` makes sense for any `NonUnitalNonAssocRing R`.
But later for the `module` part, we will assume `R` is a ring.

-/

section ideal

namespace RingCon

section NonUnitalNonAssocRing

variable {R : Type*} [NonUnitalNonAssocRing R] (I : RingCon R)

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

lemma mem_iff (x : R) : x ∈ I ↔ I x 0 := Iff.rfl

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

lemma zero_mem : 0 ∈ I := I.refl 0

lemma add_mem {x y} (hx : x ∈ I) (hy : y ∈ I) : x + y ∈ I := by
  simpa using I.add hx hy

lemma neg_mem {x} (hx : x ∈ I) : -x ∈ I := by
  simpa using I.neg hx

lemma sub_mem {x y} (hx : x ∈ I) (hy : y ∈ I) : x - y ∈ I := by
  simpa using I.sub hx hy

lemma mul_mem_left (x y) (hy : y ∈ I) : x * y ∈ I := by
  simpa using I.mul (I.refl x) hy

lemma mul_mem_right (x y) (hx : x ∈ I) : x * y ∈ I := by
  simpa using I.mul hx (I.refl y)

instance : Add I where add x y := ⟨x.1 + y.1, I.add_mem x.2 y.2⟩

instance : Zero I where zero := ⟨0, I.zero_mem⟩

theorem nsmul (n : ℕ) {x y : R} (hx : I x y) : I (n • x) (n • y) := I.toAddCon.nsmul n hx

instance : SMul ℕ I where
  smul n x := ⟨n • x.1, by simpa using I.nsmul _ x.2⟩

instance : Neg I where neg x := ⟨-x.1, I.neg_mem x.2⟩

instance : Sub I where sub x y := ⟨x.1 - y.1, I.sub_mem x.2 y.2⟩

theorem zsmul (z : ℤ) {x y : R} (hx : I x y) : I (z • x) (z • y) := I.toAddCon.zsmul z hx

instance : SMul ℤ I where
  smul n x := ⟨n • x.1, by simpa using I.zsmul n x.2⟩

instance : AddCommGroup I :=
  Function.Injective.addCommGroup _ Subtype.coe_injective
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- The coercion into the ring as a `AddMonoidHom` -/
@[simp]
def coeAddMonoidHom : I →+ R where
  toFun := (↑)
  map_zero' := rfl
  map_add' _ _ := rfl

end NonUnitalNonAssocRing

section ring

variable {R : Type*} [Ring R] (I : RingCon R)

instance : SMul R I where smul r x := ⟨r • x.1, I.mul_mem_left _ _ x.2⟩

instance : SMul Rᵐᵒᵖ I where smul r x := ⟨r • x.1, I.mul_mem_right _ _ x.2⟩

instance : Module R I :=
  Function.Injective.module _ (coeAddMonoidHom I) Subtype.coe_injective fun _ _ => rfl

instance : Module Rᵐᵒᵖ I :=
  Function.Injective.module _ (coeAddMonoidHom I) Subtype.coe_injective fun _ _ => rfl

instance : SMulCommClass R Rᵐᵒᵖ I where
  smul_comm r s x := Subtype.ext <| smul_comm r s x.1

end ring

end RingCon

end ideal
