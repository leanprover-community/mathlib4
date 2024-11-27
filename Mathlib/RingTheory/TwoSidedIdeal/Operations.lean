/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Jireh Loreaux
-/
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Module.Opposite
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.RingTheory.Congruence.Opposite
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.TwoSidedIdeal.Lattice

/-!
# Operations on two-sided ideals

This file defines operations on two-sided ideals of a ring `R`.

## Main definitions and results

- `TwoSidedIdeal.span`: the span of `s ⊆ R` is the smallest two-sided ideal containing the set.
- `TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure_nonunital`: in an associative but non-unital
  ring, an element `x` is in the two-sided ideal spanned by `s` if and only if `x` is in the closure
  of `s ∪ {y * a | y ∈ s, a ∈ R} ∪ {a * y | y ∈ s, a ∈ R} ∪ {a * y * b | y ∈ s, a, b ∈ R}` as an
  additive subgroup.
- `TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure`: in a unital and associative ring, an
  element  `x` is in the two-sided ideal spanned by `s` if and only if `x` is in the closure of
  `{a*y*b | a, b ∈ R, y ∈ s}` as an additive subgroup.


- `TwoSidedIdeal.comap`: pullback of a two-sided ideal; defined as the preimage of a
  two-sided ideal.
- `TwoSidedIdeal.map`: pushforward of a two-sided ideal; defined as the span of the image of a
  two-sided ideal.
- `TwoSidedIdeal.ker`: the kernel of a ring homomorphism as a two-sided ideal.

- `TwoSidedIdeal.gc`: `fromIdeal` and `asIdeal` form a Galois connection where
  `fromIdeal : Ideal R → TwoSidedIdeal R` is defined as the smallest two-sided ideal containing an
  ideal and `asIdeal : TwoSidedIdeal R → Ideal R` the inclusion map.
-/

namespace TwoSidedIdeal

section NonUnitalNonAssocRing

variable {R S : Type*} [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
variable {F : Type*} [FunLike F R S]
variable (f : F)

/--
The smallest two-sided ideal containing a set.
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
  exact fun I hI => hx I <| h.trans hI

/--
Pushout of a two-sided ideal. Defined as the span of the image of a two-sided ideal under a ring
homomorphism.
-/
def map (I : TwoSidedIdeal R) : TwoSidedIdeal S :=
  span (f '' I)

lemma map_mono {I J : TwoSidedIdeal R} (h : I ≤ J) :
    map f I ≤ map f J :=
  span_mono <| Set.image_mono h

variable [NonUnitalRingHomClass F R S]

/--
Preimage of a two-sided ideal, as a two-sided ideal. -/
def comap (I : TwoSidedIdeal S) : TwoSidedIdeal R :=
{ ringCon := I.ringCon.comap f }

lemma mem_comap {I : TwoSidedIdeal S} {x : R} :
    x ∈ I.comap f ↔ f x ∈ I := by
  simp [comap, RingCon.comap, mem_iff]


end NonUnitalNonAssocRing

section NonUnitalRing

variable {R : Type*} [NonUnitalRing R]

open AddSubgroup in
/-- If `s : Set R` is absorbing under multiplication, then its `TwoSidedIdeal.span` coincides with
its `AddSubgroup.closure`, as sets. -/
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
    induction hz using closure_induction with
    | mem x hx => exact hJ hx
    | one => exact zero_mem _
    | mul x y _ _ hx hy => exact J.add_mem hx hy
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

variable (I : TwoSidedIdeal R)

instance : SMul R I where smul r x := ⟨r • x.1, I.mul_mem_left _ _ x.2⟩

instance : SMul Rᵐᵒᵖ I where smul r x := ⟨r • x.1, I.mul_mem_right _ _ x.2⟩

instance leftModule : Module R I :=
  Function.Injective.module _ (coeAddMonoidHom I) Subtype.coe_injective fun _ _ ↦ rfl

@[simp]
lemma coe_smul {r : R} {x : I} : (r • x : R) = r * (x : R) := rfl

instance rightModule : Module Rᵐᵒᵖ I :=
  Function.Injective.module _ (coeAddMonoidHom I) Subtype.coe_injective fun _ _ ↦ rfl

@[simp]
lemma coe_mop_smul {r : Rᵐᵒᵖ} {x : I} : (r • x : R) = (x : R) * r.unop := rfl

instance : SMulCommClass R Rᵐᵒᵖ I where
  smul_comm r s x := Subtype.ext <| smul_comm r s x.1

/--
For any `I : RingCon R`, when we view it as an ideal, `I.subtype` is the injective `R`-linear map
`I → R`.
-/
@[simps]
def subtype : I →ₗ[R] R where
  toFun x := x.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
For any `RingCon R`, when we view it as an ideal in `Rᵒᵖ`, `subtype` is the injective `Rᵐᵒᵖ`-linear
map `I → Rᵐᵒᵖ`.
-/
@[simps]
def subtypeMop : I →ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ where
  toFun x := MulOpposite.op x.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Given an ideal `I`, `span I` is the smallest two-sided ideal containing `I`. -/
def fromIdeal : Ideal R →o TwoSidedIdeal R where
  toFun I := span I
  monotone' _ _ := span_mono

lemma mem_fromIdeal {I : Ideal R} {x : R} :
    x ∈ fromIdeal I ↔ x ∈ span I := by simp [fromIdeal]

/-- Every two-sided ideal is also a left ideal. -/
def asIdeal : TwoSidedIdeal R →o Ideal R where
  toFun I :=
  { carrier := I
    add_mem' := I.add_mem
    zero_mem' := I.zero_mem
    smul_mem' := fun r x hx => I.mul_mem_left r x hx }
  monotone' _ _ h _ h' := h h'

@[simp]
lemma mem_asIdeal {I : TwoSidedIdeal R} {x : R} :
    x ∈ asIdeal I ↔ x ∈ I := by simp [asIdeal]

lemma gc : GaloisConnection fromIdeal (asIdeal (R := R)) :=
  fun I J => ⟨fun h x hx ↦ h <| mem_span_iff.2 fun _ H ↦ H hx, fun h x hx ↦ by
    simp only [fromIdeal, OrderHom.coe_mk, mem_span_iff] at hx
    exact hx _ h⟩

@[simp]
lemma coe_asIdeal {I : TwoSidedIdeal R} : (asIdeal I : Set R) = I := rfl

/-- Every two-sided ideal is also a right ideal. -/
def asIdealOpposite : TwoSidedIdeal R →o Ideal Rᵐᵒᵖ where
  toFun I := asIdeal ⟨I.ringCon.op⟩
  monotone' I J h x h' := by
    simp only [mem_asIdeal, mem_iff, RingCon.op_iff, MulOpposite.unop_zero] at h' ⊢
    exact J.rel_iff _ _ |>.2 <| h <| I.rel_iff 0 x.unop |>.1 h'

lemma mem_asIdealOpposite {I : TwoSidedIdeal R} {x : Rᵐᵒᵖ} :
    x ∈ asIdealOpposite I ↔ x.unop ∈ I := by
  simpa [asIdealOpposite, asIdeal, TwoSidedIdeal.mem_iff, RingCon.op_iff] using
    ⟨I.ringCon.symm, I.ringCon.symm⟩

end Ring

section CommRing

variable {R : Type*} [CommRing R]

/--
When the ring is commutative, two-sided ideals are exactly the same as left ideals.
-/
def orderIsoIdeal : TwoSidedIdeal R ≃o Ideal R where
  toFun := asIdeal
  invFun := fromIdeal
  map_rel_iff' := ⟨fun h _ hx ↦ h hx, fun h ↦ asIdeal.monotone' h⟩
  left_inv _ := SetLike.ext fun _ ↦ mem_span_iff.trans <| by aesop
  right_inv J := SetLike.ext fun x ↦ mem_span_iff.trans
    ⟨fun h ↦ mem_mk' _ _ _ _ _ _ _ |>.1 <| h (mk'
      J J.zero_mem J.add_mem J.neg_mem (J.mul_mem_left _) (J.mul_mem_right _))
      (fun x => by simp), by aesop⟩

end CommRing

end TwoSidedIdeal

namespace Ideal
variable {R : Type*} [Ring R]

/-- Bundle an `Ideal` that is already two-sided as a `TwoSidedIdeal`. -/
def toTwoSided (I : Ideal R) (mul_mem_right : ∀ {x y}, x ∈ I → x * y ∈ I) : TwoSidedIdeal R :=
  TwoSidedIdeal.mk' I I.zero_mem I.add_mem I.neg_mem (I.smul_mem _) mul_mem_right

@[simp]
lemma mem_toTwoSided {I : Ideal R} {h} {x : R} :
    x ∈ I.toTwoSided h ↔ x ∈ I := by
  simp [toTwoSided]

@[simp]
lemma coe_toTwoSided (I : Ideal R) (h) : (I.toTwoSided h : Set R) = I := by
  simp [toTwoSided]

@[simp]
lemma toTwoSided_asIdeal (I : TwoSidedIdeal R) (h) : (TwoSidedIdeal.asIdeal I).toTwoSided h = I :=
  by ext; simp

@[simp]
lemma asIdeal_toTwoSided (I : Ideal R) (h) : TwoSidedIdeal.asIdeal (I.toTwoSided h) = I := by
  ext
  simp

instance : CanLift (Ideal R) (TwoSidedIdeal R) TwoSidedIdeal.asIdeal
    (fun I => ∀ {x y}, x ∈ I → x * y ∈ I) where
  prf I mul_mem_right := ⟨I.toTwoSided mul_mem_right, asIdeal_toTwoSided ..⟩

end Ideal
