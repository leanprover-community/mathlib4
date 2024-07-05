/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.RingTheory.TwoSidedIdeal.BigOperators
import Mathlib.RingTheory.Congruence.Opposite
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Fintype.BigOperators
import Mathlib.RingTheory.Ideal.Basic


/-!
# Operations on Two-Sided-Ideals

This file defines operations on two-sided-ideals of a ring `R`.

## Main definitions and results
- `TwoSidedIdeal.span`: the span of `s ⊆ R` is the smallest two-sided-ideal containing the set.
- `TwoSidedIdeal.mem_span_iff_exists`: an element `x` is in the span of `s` if and only if it can be
  written as a finite sum of the form `∑ i, xL i * y i * xR i` where `xL i ∈ s`, `y i ∈ R`, and
  `xR i ∈ s`.

- `TwoSidedIdeal.comap`: pullback of a two-sided-ideal; defined as the preimage of a
  two-sided-ideal.
- `TwoSidedIdeal.map`: pushout of a two-sided-ideal; defined as the span of the image of a
  two-sided-ideal.
- `TwoSidedIdeal.ker`: the kernel of a ring homomorphism as a two-sided-ideal.
-/

namespace TwoSidedIdeal

section NonUnitalNonAssocRing

variable {R : Type*} [NonUnitalNonAssocRing R]

/--
The smallest two-sided-ideal containing a set.
-/
abbrev span (s : Set R) : TwoSidedIdeal R :=
  { ringCon := ringConGen (fun a b ↦ a - b ∈ s) }

lemma subset_span {s : Set R} : s ⊆ (span s : Set R) := by
  intro x hx
  rw [SetLike.mem_coe, mem_iff]
  exact RingConGen.Rel.of _ _ (by simpa using hx)

lemma mem_span_iff {s : Set R} {x} :
    x ∈ span s ↔ ∀ (I : TwoSidedIdeal R), s ⊆ I → x ∈ I := by
  refine ⟨?_, fun h => h _ subset_span⟩
  delta span
  rw [RingCon.ringConGen_eq]
  intro h I hI
  refine sInf_le (α := RingCon R) ?_ h
  intro x y hxy
  specialize hI hxy
  rwa [SetLike.mem_coe, ← rel_iff] at hI

end NonUnitalNonAssocRing

section NonAssocRing

variable {R S : Type*} [NonAssocRing R] [NonAssocRing S]
variable {F : Type*} [FunLike F R S] [RingHomClass F R S] (f : F)

/--
preimage of a two-sided-ideal is still two-sided -/
def comap (I : TwoSidedIdeal S) : TwoSidedIdeal R :=
{ ringCon := I.ringCon.comap f }

lemma mem_comap {I : TwoSidedIdeal S} {x : R} :
    x ∈ I.comap f ↔ f x ∈ I := by
  simp [comap, RingCon.comap, mem_iff]

/--
pushout of a two-sided-ideal defined as the span of the image of a two-sided-ideal under some ring
homomorphism.
-/
def map (I : TwoSidedIdeal R) : TwoSidedIdeal S :=
  span (f '' I)

lemma map_mono {I J : TwoSidedIdeal R} (h : I ≤ J) :
    map f I ≤ map f J := by
  intro x hx
  delta map at hx ⊢
  rw [mem_span_iff] at hx ⊢
  intro K hK
  refine hx K ?_
  rintro _ ⟨z, hz, rfl⟩
  exact hK ⟨z, h hz, rfl⟩

/--
kernel of a ring homomorphism as a two-sided-ideal.
-/
def ker (f : R →+* S) : TwoSidedIdeal R :=
  .mk'
    {r | f r = 0} (map_zero _) (by rintro _ _ (h1 : f _ = 0) (h2 : f _ = 0); simp [h1, h2])
    (by rintro _ (h : f _ = 0); simp [h]) (by rintro _ _ (h : f _ = 0); simp [h])
    (by rintro _ _ (h : f _ = 0); simp [h])

lemma mem_ker (f : R →+* S) {x : R} : x ∈ ker f ↔ f x = 0 := by
  delta ker; rw [mem_mk']; rfl
  · rintro _ _ (h1 : f _ = 0) (h2 : f _ = 0); simp [h1, h2]
  · rintro _ (h : f _ = 0); simp [h]
  · rintro _ _ (h : f _ = 0); simp [h]
  · rintro _ _ (h : f _ = 0); simp [h]

end NonAssocRing

section Ring

variable {R : Type*} [Ring R]

lemma mem_span_iff_exists {s : Set R} {x} :
    x ∈ span s ↔
    ∃ (ι : Type) (fin : Fintype ι) (xL : ι → R) (xR : ι → R) (y : ι → s),
      x = ∑ i : ι, xL i * (y i : R) * xR i := by
  let S : TwoSidedIdeal R := .mk'
    {x | ∃ (ι : Type) (fin : Fintype ι) (xL : ι → R) (xR : ι → R) (y : ι → s),
    x = ∑ i : ι, xL i * y i * xR i}
    ⟨Empty, Fintype.instEmpty, Empty.elim, Empty.elim, Empty.elim, by simp⟩
    (by
      rintro _ _ ⟨na, fina, xLa, xRa, ya, rfl⟩ ⟨nb, finb, xLb, xRb, yb, rfl⟩
      refine ⟨na ⊕ nb, inferInstance, Sum.elim xLa xLb, Sum.elim xRa xRb, Sum.elim ya yb, by simp⟩)
    (by
      rintro _ ⟨n, finn, xL, xR, y, rfl⟩
      exact ⟨n, finn, -xL, xR, y, by simp⟩)
    (by
      rintro a _ ⟨n, finn, xL, xR, y, rfl⟩
      exact ⟨n, finn, a • xL, xR, y, by simp [Finset.mul_sum, mul_assoc]⟩)
    (by
      rintro _ b ⟨n, finn, xL, xR, y, rfl⟩
      exact ⟨n, finn, xL, fun x ↦ xR x * b, y, by simp [Finset.sum_mul, mul_assoc]⟩)
  suffices eq1 : span s = S by
    rw [eq1]; simp [S, mem_mk']
  rw [span, RingCon.ringConGen_eq]
  refine ringCon_injective $ sInf_eq_of_forall_ge_of_forall_gt_exists_lt ?_ ?_
  · rintro I (hI : ∀ a b, _ → _)
    rw [← ringCon_le_iff, le_iff]
    intro x h
    simp only [SetLike.mem_coe, mem_mk', Set.mem_setOf_eq, S] at h
    obtain ⟨n, finn, xL, xR, y, rfl⟩ := h
    refine finsetSum_mem _ _ _ fun i _ => mul_mem_right _ _ _ $
      mul_mem_left _ _ _ $  hI (y i) 0 (by simp)
  · rintro I hI
    exact ⟨S.ringCon, fun a b H ↦ ⟨PUnit, inferInstance, fun _ ↦ 1, fun _ ↦ 1,
      fun _ ↦ ⟨a - b, by simp [H]⟩, by simp⟩, hI⟩

/-- Every two-sided-ideal is also a left-ideal. -/
def asIdeal : TwoSidedIdeal R →o Ideal R where
  toFun I :=
  { carrier := I
    add_mem' := I.add_mem
    zero_mem' := I.zero_mem
    smul_mem' := fun r x hx => I.mul_mem_left r x hx }
  monotone' _ _ h _ h' := h h'

lemma mem_asIdeal {I : TwoSidedIdeal R} {x : R} :
    x ∈ TwoSidedIdeal.asIdeal I ↔ x ∈ I := by simp [asIdeal]

/-- Every two-sided-ideal is also a right ideal. -/
def asIdealMop : TwoSidedIdeal R →o Ideal Rᵐᵒᵖ where
  toFun I := asIdeal $ ⟨I.ringCon.op⟩
  monotone' I J h x h' := by
    simp only [mem_asIdeal, mem_iff, RingCon.op_iff, MulOpposite.unop_zero] at h' ⊢
    exact J.rel_iff _ _ |>.2 $ h $ I.rel_iff 0 x.unop |>.1 h'

end Ring

section CommRing

variable {R : Type*} [CommRing R]

/--
When the ring is commutative, two-sided-ideals are exactly the same as left ideals.
-/
def orderIsoIdeal : TwoSidedIdeal R ≃o Ideal R where
  toFun := asIdeal
  invFun := fun I => .mk' I I.zero_mem I.add_mem I.neg_mem
    (fun _ {_} h => I.mul_mem_left _ h )
    (fun {x y} h => I.mul_mem_right y h )
  map_rel_iff' {I J} := by
    constructor
    · intro h x hx
      exact h hx
    · apply asIdeal.monotone'
  left_inv _ := by ext; simp [mem_mk', mem_asIdeal]
  right_inv _ := by ext; simp [mem_mk', mem_asIdeal]

end CommRing

end TwoSidedIdeal
