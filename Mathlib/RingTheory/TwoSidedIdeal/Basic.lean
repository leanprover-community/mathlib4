/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.Tactic.Abel
import Mathlib.Algebra.Ring.Opposite
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.RingTheory.Congruence.Opposite

/-!
# Two Sided Ideals

In this file, for any `Ring R`, we reinterpret `I : RingCon R` as a two-sided-ideal of a ring.

## Main definitions and results

* `TwoSidedIdeal`: For any `NonUnitalNonAssocRing R`, `TwoSidedIdeal R` is a wrapper around
  `RingCon R`.
* `TwoSidedIdeal.setLike`: Every `I : TwoSidedIdeal R` can be interpreted as a set of `R` where
  `x ∈ I` if and only if `I.ringCon x 0`.
* `TwoSidedIdeal.addCommGroup`: Every `I : TwoSidedIdeal R` is an abelian group.

-/

assert_not_exists LinearMap

open MulOpposite

section definitions

/--
A two-sided ideal of a ring `R` is a subset of `R` that contains `0` and is closed under addition,
negation, and absorbs multiplication on both sides.
-/
structure TwoSidedIdeal (R : Type*) [NonUnitalNonAssocRing R] where
  /-- every two-sided-ideal is induced by a congruence relation on the ring. -/
  ringCon : RingCon R

end definitions

namespace TwoSidedIdeal

section NonUnitalNonAssocRing

variable {R : Type*} [NonUnitalNonAssocRing R] (I : TwoSidedIdeal R)

instance [Nontrivial R] : Nontrivial (TwoSidedIdeal R) := by
  obtain ⟨I, J, h⟩ : Nontrivial (RingCon R) := inferInstance
  exact ⟨⟨I⟩, ⟨J⟩, by contrapose! h; aesop⟩

instance setLike : SetLike (TwoSidedIdeal R) R where
  coe t := {r | t.ringCon r 0}
  coe_injective'  := by
    rintro ⟨t₁⟩ ⟨t₂⟩ (h : {x | _} = {x | _})
    congr 1
    refine RingCon.ext fun a b ↦ ⟨fun H ↦ ?_, fun H ↦ ?_⟩
    · have H' : a - b ∈ {x | t₁ x 0} := sub_self b ▸ t₁.sub H (t₁.refl b)
      rw [h] at H'
      convert t₂.add H' (t₂.refl b) using 1 <;> abel
    · have H' : a - b ∈ {x | t₂ x 0} := sub_self b ▸ t₂.sub H (t₂.refl b)
      rw [← h] at H'
      convert t₁.add H' (t₁.refl b) using 1 <;> abel

lemma mem_iff (x : R) : x ∈ I ↔ I.ringCon x 0 := Iff.rfl

@[simp]
lemma mem_mk {x : R} {c : RingCon R} : x ∈ mk c ↔ c x 0 := Iff.rfl

@[simp, norm_cast]
lemma coe_mk {c : RingCon R} : (mk c : Set R) = {x | c x 0} := rfl

lemma rel_iff (x y : R) : I.ringCon x y ↔ x - y ∈ I := by
  rw [mem_iff]
  constructor
  · intro h; convert I.ringCon.sub h (I.ringCon.refl y); abel
  · intro h; convert I.ringCon.add h (I.ringCon.refl y) <;> abel

/--
the coercion from two-sided-ideals to sets is an order embedding
-/
@[simps]
def coeOrderEmbedding : TwoSidedIdeal R ↪o Set R where
  toFun := SetLike.coe
  inj' := SetLike.coe_injective
  map_rel_iff' {I J} := ⟨fun (h : (I : Set R) ⊆ (J : Set R)) _ h' ↦ h h', fun h _ h' ↦ h h'⟩

lemma le_iff {I J : TwoSidedIdeal R} : I ≤ J ↔ (I : Set R) ⊆ (J : Set R) := Iff.rfl

/-- Two-sided-ideals corresponds to congruence relations on a ring. -/
@[simps apply symm_apply]
def orderIsoRingCon : TwoSidedIdeal R ≃o RingCon R where
  toFun := TwoSidedIdeal.ringCon
  invFun := .mk
  map_rel_iff' {I J} := Iff.symm <| le_iff.trans ⟨fun h x y r => by rw [rel_iff] at r ⊢; exact h r,
    fun h x hx => by rw [SetLike.mem_coe, mem_iff] at hx ⊢; exact h hx⟩

lemma ringCon_injective : Function.Injective (TwoSidedIdeal.ringCon (R := R)) := by
  rintro ⟨x⟩ ⟨y⟩ rfl; rfl

lemma ringCon_le_iff {I J : TwoSidedIdeal R} : I ≤ J ↔ I.ringCon ≤ J.ringCon :=
  orderIsoRingCon.map_rel_iff.symm

@[ext]
lemma ext {I J : TwoSidedIdeal R} (h : ∀ x, x ∈ I ↔ x ∈ J) : I = J :=
  coeOrderEmbedding.injective (Set.ext h)

lemma lt_iff (I J : TwoSidedIdeal R) : I < J ↔ (I : Set R) ⊂ (J : Set R) := by
  rw [lt_iff_le_and_ne, Set.ssubset_iff_subset_ne, le_iff]
  simp

lemma zero_mem : 0 ∈ I := I.ringCon.refl 0

lemma add_mem {x y} (hx : x ∈ I) (hy : y ∈ I) : x + y ∈ I := by simpa using I.ringCon.add hx hy

lemma neg_mem {x} (hx : x ∈ I) : -x ∈ I := by simpa using I.ringCon.neg hx

instance : AddSubgroupClass (TwoSidedIdeal R) R where
  zero_mem := zero_mem
  add_mem := @add_mem _ _
  neg_mem := @neg_mem _ _

lemma sub_mem {x y} (hx : x ∈ I) (hy : y ∈ I) : x - y ∈ I := _root_.sub_mem hx hy

lemma mul_mem_left (x y) (hy : y ∈ I) : x * y ∈ I := by
  simpa using I.ringCon.mul (I.ringCon.refl x) hy

lemma mul_mem_right (x y) (hx : x ∈ I) : x * y ∈ I := by
  simpa using I.ringCon.mul hx (I.ringCon.refl y)

lemma nsmul_mem {x} (n : ℕ) (hx : x ∈ I) : n • x ∈ I := _root_.nsmul_mem hx _

lemma zsmul_mem {x} (n : ℤ) (hx : x ∈ I) : n • x ∈ I := _root_.zsmul_mem hx _

/--
The "set-theoretic-way" of constructing a two-sided ideal by providing:
- the underlying set `S`;
- a proof that `0 ∈ S`;
- a proof that `x + y ∈ S` if `x ∈ S` and `y ∈ S`;
- a proof that `-x ∈ S` if `x ∈ S`;
- a proof that `x * y ∈ S` if `y ∈ S`;
- a proof that `x * y ∈ S` if `x ∈ S`.
-/
def mk' (carrier : Set R)
    (zero_mem : 0 ∈ carrier)
    (add_mem : ∀ {x y}, x ∈ carrier → y ∈ carrier → x + y ∈ carrier)
    (neg_mem : ∀ {x}, x ∈ carrier → -x ∈ carrier)
    (mul_mem_left : ∀ {x y}, y ∈ carrier → x * y ∈ carrier)
    (mul_mem_right : ∀ {x y}, x ∈ carrier → x * y ∈ carrier) : TwoSidedIdeal R where
  ringCon :=
    { r := fun x y ↦ x - y ∈ carrier
      iseqv :=
      { refl := fun x ↦ by simpa using zero_mem
        symm := fun h ↦ by simpa using neg_mem h
        trans := fun {x y z} h1 h2 ↦ by
          simpa only [show x - z = (x - y) + (y - z) by abel] using add_mem h1 h2 }
      mul' := fun {a b c d} (h1 : a - b ∈ carrier) (h2 : c - d ∈ carrier) ↦ show _ ∈ carrier by
        rw [show a * c - b * d = a * (c - d) + (a - b) * d by rw [mul_sub, sub_mul]; abel]
        exact add_mem (mul_mem_left h2) (mul_mem_right h1)
      add' := fun {a b c d} (h1 : a - b ∈ carrier) (h2 : c - d ∈ carrier) ↦ show _ ∈ carrier by
        rw [show a + c - (b + d) = (a - b) + (c - d) by abel]
        exact add_mem h1 h2 }

@[simp]
lemma mem_mk' (carrier : Set R) (zero_mem add_mem neg_mem mul_mem_left mul_mem_right) (x : R) :
    x ∈ mk' carrier zero_mem add_mem neg_mem mul_mem_left mul_mem_right ↔ x ∈ carrier := by
  rw [mem_iff]
  simp [mk']

set_option linter.docPrime false in
@[simp]
lemma coe_mk' (carrier : Set R) (zero_mem add_mem neg_mem mul_mem_left mul_mem_right) :
    (mk' carrier zero_mem add_mem neg_mem mul_mem_left mul_mem_right : Set R) = carrier :=
  Set.ext <| mem_mk' carrier zero_mem add_mem neg_mem mul_mem_left mul_mem_right

instance : SMulMemClass (TwoSidedIdeal R) R R where
  smul_mem _ _ h := TwoSidedIdeal.mul_mem_left _ _ _ h

instance : SMulMemClass (TwoSidedIdeal R) Rᵐᵒᵖ R where
  smul_mem _ _ h := TwoSidedIdeal.mul_mem_right _ _ _ h

instance : Add I where add x y := ⟨x.1 + y.1, I.add_mem x.2 y.2⟩

instance : Zero I where zero := ⟨0, I.zero_mem⟩

instance : SMul ℕ I where smul n x := ⟨n • x.1, I.nsmul_mem n x.2⟩

instance : Neg I where neg x := ⟨-x.1, I.neg_mem x.2⟩

instance : Sub I where sub x y := ⟨x.1 - y.1, I.sub_mem x.2 y.2⟩

instance : SMul ℤ I where smul n x := ⟨n • x.1, I.zsmul_mem n x.2⟩

instance addCommGroup : AddCommGroup I :=
  Function.Injective.addCommGroup _ Subtype.coe_injective
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- The coercion into the ring as a `AddMonoidHom` -/
@[simps]
def coeAddMonoidHom : I →+ R where
  toFun := (↑)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- If `I` is a two-sided ideal of `R`, then `{op x | x ∈ I}` is a two-sided ideal in `Rᵐᵒᵖ`. -/
@[simps]
def op (I : TwoSidedIdeal R) : TwoSidedIdeal Rᵐᵒᵖ where
  ringCon := I.ringCon.op

@[simp]
lemma mem_op_iff {I : TwoSidedIdeal R} {x : Rᵐᵒᵖ} : x ∈ I.op ↔ x.unop ∈ I :=
  I.ringCon.comm'

@[simp, norm_cast]
lemma coe_op {I : TwoSidedIdeal R} : (I.op : Set Rᵐᵒᵖ) = MulOpposite.unop ⁻¹' I :=
  Set.ext fun _ => mem_op_iff


/-- If `I` is a two-sided ideal of `Rᵐᵒᵖ`, then `{x.unop | x ∈ I}` is a two-sided ideal in `R`. -/
@[simps]
def unop (I : TwoSidedIdeal Rᵐᵒᵖ) : TwoSidedIdeal R where
  ringCon := I.ringCon.unop

@[simp]
lemma mem_unop_iff {I : TwoSidedIdeal Rᵐᵒᵖ} {x : R} : x ∈ I.unop ↔ MulOpposite.op x ∈ I :=
  I.ringCon.comm'

@[simp, norm_cast]
lemma coe_unop {I : TwoSidedIdeal Rᵐᵒᵖ} : (I.unop : Set R) = MulOpposite.op ⁻¹' I :=
  Set.ext fun _ => mem_unop_iff

/--
Two-sided-ideals of `A` and that of `Aᵒᵖ` corresponds bijectively to each other.
-/
@[simps]
def opOrderIso : TwoSidedIdeal R ≃o TwoSidedIdeal Rᵐᵒᵖ where
  toFun := op
  invFun := unop
  map_rel_iff' {I' J'} := by simpa [ringCon_le_iff] using RingCon.opOrderIso.map_rel_iff

end NonUnitalNonAssocRing

end TwoSidedIdeal
