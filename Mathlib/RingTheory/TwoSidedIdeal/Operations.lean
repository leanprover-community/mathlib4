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
import Mathlib.Order.GaloisConnection


/-!
# Operations on Two-Sided-Ideals

This file defines operations on two-sided-ideals of a ring `R`.

## Main definitions and results
- `TwoSidedIdeal.span`: the span of `s ⊆ R` is the smallest two-sided-ideal containing the set.
- `TwoSidedIdeal.mem_span_iff_exists`: in a unital and associative ring, an element `x` is in the
  span of `s` if and only if it can be written as a finite sum of the form `∑ i, xL i * y i * xR i`
  where `xL i ∈ s`, `y i ∈ R`, and `xR i ∈ s`.

- `TwoSidedIdeal.comap`: pullback of a two-sided-ideal; defined as the preimage of a
  two-sided-ideal.
- `TwoSidedIdeal.map`: pushforward of a two-sided-ideal; defined as the span of the image of a
  two-sided-ideal.
- `TwoSidedIdeal.ker`: the kernel of a ring homomorphism as a two-sided-ideal.
-/

namespace TwoSidedIdeal

section NonUnitalNonAssocRing

variable {R S : Type*} [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
variable {F : Type*} [FunLike F R S] [AddMonoidHomClass F R S] [MulHomClass F R S]
variable (f : F)

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

lemma span_mono {s t : Set R} (h : s ⊆ t) : span s ≤ span t := by
  intro x hx
  rw [mem_span_iff] at hx ⊢
  exact fun I hI => hx I $ h.trans hI

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
    map f I ≤ map f J :=
  span_mono $ Set.image_mono h

/--
kernel of a ring homomorphism as a two-sided-ideal.
-/
def ker : TwoSidedIdeal R :=
  .mk'
    {r | f r = 0} (map_zero _) (by rintro _ _ (h1 : f _ = 0) (h2 : f _ = 0); simp [h1, h2])
    (by rintro _ (h : f _ = 0); simp [h]) (by rintro _ _ (h : f _ = 0); simp [h])
    (by rintro _ _ (h : f _ = 0); simp [h])

lemma mem_ker {x : R} : x ∈ ker f ↔ f x = 0 := by
  delta ker; rw [mem_mk']; rfl
  · rintro _ _ (h1 : f _ = 0) (h2 : f _ = 0); simp [h1, h2]
  · rintro _ (h : f _ = 0); simp [h]
  · rintro _ _ (h : f _ = 0); simp [h]
  · rintro _ _ (h : f _ = 0); simp [h]

end NonUnitalNonAssocRing

section NonUnitalRing

variable {R : Type*} [NonUnitalRing R]

open AddSubgroup in
/-- If `s : Set R` is absorbing under multiplication, then its `TwoSidedIdeal.span` coincides with
it's `AddSubgroup.closure`, as sets. -/
lemma mem_span_iff_mem_addSubgroup_closure_absorbing {s : Set R}
    (h_left : ∀ x y, y ∈ s → x * y ∈ s) (h_right : ∀ y x, y ∈ s → y * x ∈ s) {z : R} :
    z ∈ span s ↔ z ∈ closure s := by
  have h_left' {x y} (hy : y ∈ closure s) : x * y ∈ closure s := by
    have := (AddMonoidHom.mulLeft x).map_closure s ▸ mem_map_of_mem _ hy
    refine closure_mono ?_ this
    rintro - ⟨y, hy, rfl⟩
    exact h_left x y hy
  have h_right' {y x} (hy : y ∈ closure s) : y * x ∈ closure s := by
    have := (AddMonoidHom.mulRight x).map_closure s ▸ mem_map_of_mem _ hy
    refine closure_mono ?_ this
    rintro - ⟨y, hy, rfl⟩
    exact h_right y x hy
  let I : TwoSidedIdeal R := .mk' (closure s) (AddSubgroup.zero_mem _)
    (AddSubgroup.add_mem _) (AddSubgroup.neg_mem _) h_left' h_right'
  suffices z ∈ span s ↔ z ∈ I by simpa only [I, mem_mk', SetLike.mem_coe]
  rw [mem_span_iff]
  -- Suppose that for every ideal `J` with `s ⊆ J`, then `z ∈ J`. Apply this to `I` to get `z ∈ I`.
  refine ⟨fun h ↦ h I fun x hx ↦ ?mem_closure_of_forall, fun hz J hJ ↦ ?mem_ideal_of_subset⟩
  case mem_closure_of_forall => simpa only [I, SetLike.mem_coe, mem_mk'] using subset_closure hx
  /- Conversely, suppose that `z ∈ I` and that `J` is any ideal containing `s`. Then by the
  induction principle for `AddSubgroup`, we must also have `z ∈ J`. -/
  case mem_ideal_of_subset =>
    simp only [I, SetLike.mem_coe, mem_mk'] at hz
    induction hz using closure_induction' with
    | mem x hx => exact hJ hx
    | one => exact zero_mem _
    | mul x _ y _ hx hy => exact J.add_mem hx hy
    | inv x _ hx => exact J.neg_mem hx

open Pointwise Set

lemma set_mul_subset {s : Set R} {I : TwoSidedIdeal R} (h : s ⊆ I) (t : Set R):
    t * s ⊆ I := by
  rintro - ⟨r, -, x, hx, rfl⟩
  exact mul_mem_left _ _ _ (h hx)

lemma subset_mul_set {s : Set R} {I : TwoSidedIdeal R} (h : s ⊆ I) (t : Set R):
    s * t ⊆ I := by
  rintro - ⟨x, hx, r, -, rfl⟩
  exact mul_mem_right _ _ _ (h hx)

lemma mem_span_iff_mem_addSubgroup_closure_nonunital {s : Set R} {z : R} :
    z ∈ span s ↔ z ∈ AddSubgroup.closure (s ∪ s * univ ∪ univ * s ∪ univ * s * univ) := by
  trans z ∈ span (s ∪ s * univ ∪ univ * s ∪ univ * s * univ)
  · refine ⟨(span_mono (by simp only [Set.union_assoc, Set.subset_union_left]) ·), fun h ↦ ?_⟩
    refine mem_span_iff.mp h (span s) ?_
    simp only [union_subset_iff, union_assoc]
    exact ⟨subset_span, subset_mul_set subset_span _, set_mul_subset subset_span _,
      subset_mul_set (set_mul_subset subset_span _) _⟩
  · refine mem_span_iff_mem_addSubgroup_closure_absorbing ?_ ?_
    · rintro x y (((hy | ⟨y, hy, r, -, rfl⟩) | ⟨r, -, y, hy, rfl⟩) |
        ⟨-, ⟨r', -, y, hy, rfl⟩, r, -, rfl⟩)
      · exact .inl <| .inr <| ⟨x, mem_univ _, y, hy, rfl⟩
      · exact .inr <| ⟨x * y, ⟨x, mem_univ _, y, hy, rfl⟩, r, mem_univ _, mul_assoc ..⟩
      · exact .inl <| .inr <| ⟨x * r, mem_univ _, y, hy, mul_assoc ..⟩
      · refine .inr <| ⟨x * r' * y, ⟨x * r', mem_univ _, y, hy, ?_⟩, ⟨r, mem_univ _, ?_⟩⟩
        all_goals simp [mul_assoc]
    · rintro y x (((hy | ⟨y, hy, r, -, rfl⟩) | ⟨r, -, y, hy, rfl⟩) |
        ⟨-, ⟨r', -, y, hy, rfl⟩, r, -, rfl⟩)
      · exact .inl <| .inl <| .inr ⟨y, hy, x, mem_univ _, rfl⟩
      · exact .inl <| .inl <| .inr ⟨y, hy, r * x, mem_univ _, (mul_assoc ..).symm⟩
      · exact .inr <| ⟨r * y, ⟨r, mem_univ _, y, hy, rfl⟩, x, mem_univ _, rfl⟩
      · refine .inr <| ⟨r' * y, ⟨r', mem_univ _, y, hy, rfl⟩, r * x, mem_univ _, ?_⟩
        simp [mul_assoc]

proof_wanted mem_span_iff_exists_nonunital {s : Set R} {z : R} :
    z ∈ span s ↔
    ∃ (t : Finset R) (_ : (t : Set R) ⊆ s) (n : R → ℤ)
      (α : R → R) (β : R → R) (xy : R → R →₀ (R × R)),
      z = ∑ r ∈ t, (n r • r + α r * r + r * β r +
        ∑ i ∈ (xy r).support, (xy r i).1 * r * (xy r i).2)

end NonUnitalRing

section Ring

variable {R : Type*} [Ring R]

open Pointwise Set in
lemma mem_span_iff_mem_addSubgroup_closure {s : Set R} {z : R} :
    z ∈ span s ↔ z ∈ AddSubgroup.closure (univ * s * univ) := by
  trans z ∈ span (univ * s * univ)
  · refine ⟨(span_mono (fun x hx ↦ ?_) ·), fun hz ↦ ?_⟩
    · exact ⟨1 * x, ⟨1, mem_univ _, x, hx, rfl⟩, 1, mem_univ _, by simp⟩
    · exact mem_span_iff.mp hz (span s) <| subset_mul_set (set_mul_subset subset_span _) _
  · refine mem_span_iff_mem_addSubgroup_closure_absorbing ?_ ?_
    · intro x y hy
      rw [mul_assoc] at hy ⊢
      obtain ⟨r, -, y, hy, rfl⟩ := hy
      exact ⟨x * r, mem_univ _, y, hy, mul_assoc ..⟩
    · rintro - x ⟨y, hy, r, -, rfl⟩
      exact ⟨y, hy, r * x, mem_univ _, (mul_assoc ..).symm⟩

lemma mem_span_iff_exists {s : Set R} {x} :
    x ∈ span s ↔
    ∃ (ι : Type) (fin : Fintype ι) (xL : ι → R) (xR : ι → R) (y : ι → s),
      x = ∑ i : ι, xL i * (y i : R) * xR i := by
  let S : TwoSidedIdeal R := .mk'
    {x | ∃ (ι : Type) (fin : Fintype ι) (xL : ι → R) (xR : ι → R) (y : ι → s),
    x = ∑ i : ι, xL i * y i * xR i}
    ⟨Empty, inferInstance, Empty.elim, Empty.elim, Empty.elim, by simp⟩
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

/-- Given an ideal `I`, `span I` is the smallest two-sided-ideal containing `I`. -/
def fromIdeal : Ideal R →o TwoSidedIdeal R where
  toFun I := span I
  monotone' _ _ := span_mono

lemma mem_fromIdeal {I : Ideal R} {x : R} :
    x ∈ fromIdeal I ↔ x ∈ span I := by simp [fromIdeal]

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

lemma mem_asIdealMop {I : TwoSidedIdeal R} {x : Rᵐᵒᵖ} :
    x ∈ asIdealMop I ↔ x.unop ∈ I := by
  simpa [asIdealMop, asIdeal, TwoSidedIdeal.mem_iff, RingCon.op_iff] using
    ⟨I.ringCon.symm, I.ringCon.symm⟩

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
