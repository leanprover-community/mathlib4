/-
Copyright (c) 2024 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Algebra.Star.NonUnitalSubsemiring
import Mathlib.Algebra.Ring.Subsemiring.Basic

/-!
# Star subrings

A *-subring is a subring of a *-ring which is closed under *.
-/

universe v

/-- A (unital) star subsemiring is a non-associative ring which is closed under the `star`
operation. -/
structure StarSubsemiring (R : Type v) [NonAssocSemiring R] [Star R] : Type v
    extends Subsemiring R where
  /-- The `carrier` of a `StarSubsemiring` is closed under the `star` operation. -/
  star_mem' {a} : a ∈ carrier → star a ∈ carrier

section StarSubsemiring

namespace StarSubsemiring

/-- Reinterpret a `StarSubsemiring` as a `Subsemiring`. -/
add_decl_doc StarSubsemiring.toSubsemiring

instance setLike {R : Type v} [NonAssocSemiring R] [Star R] :
    SetLike (StarSubsemiring R) R where
  coe {s} := s.carrier
  coe_injective' p q h := by obtain ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩ := p; cases q; congr

initialize_simps_projections StarSubsemiring (carrier → coe, as_prefix coe)

variable {R : Type v} [NonAssocSemiring R] [StarRing R]

/-- The actual `StarSubsemiring` obtained from an element of a `StarSubsemiringClass`. -/
@[simps]
def ofClass {S R : Type*} [NonAssocSemiring R] [SetLike S R] [StarRing R] [SubsemiringClass S R]
    [StarMemClass S R] (s : S) : StarSubsemiring R where
  carrier := s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  one_mem' := one_mem _
  star_mem' := star_mem

instance (priority := 100) : CanLift (Set R) (StarSubsemiring R) (↑)
    (fun s ↦ 0 ∈ s ∧ (∀ {x y}, x ∈ s → y ∈ s → x + y ∈ s) ∧ 1 ∈ s ∧
      (∀ {x y}, x ∈ s → y ∈ s → x * y ∈ s) ∧ (∀ {x}, x ∈ s → star x ∈ s)) where
  prf s h :=
    ⟨ { carrier := s
        zero_mem' := h.1
        add_mem' := h.2.1
        one_mem' := h.2.2.1
        mul_mem' := h.2.2.2.1
        star_mem' := h.2.2.2.2 },
      rfl ⟩

instance starMemClass : StarMemClass (StarSubsemiring R) R where
  star_mem {s} := s.star_mem'

instance subsemiringClass : SubsemiringClass (StarSubsemiring R) R where
  add_mem {s} := s.add_mem'
  mul_mem {s} := s.mul_mem'
  zero_mem {s} := s.zero_mem'
  one_mem {s} := s.one_mem'

-- this uses the `Star` instance `s` inherits from `StarMemClass (StarSubsemiring R A) A`
instance starRing (s : StarSubsemiring R) : StarRing s :=
  { StarMemClass.instStar s with
    star_involutive := fun r => Subtype.ext (star_star (r : R))
    star_mul := fun r₁ r₂ => Subtype.ext (star_mul (r₁ : R) (r₂ : R))
    star_add := fun r₁ r₂ => Subtype.ext (star_add (r₁ : R) (r₂ : R)) }

instance semiring (s : StarSubsemiring R) : NonAssocSemiring s :=
  s.toSubsemiring.toNonAssocSemiring

theorem mem_carrier {s : StarSubsemiring R} {x : R} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

@[ext]
theorem ext {S T : StarSubsemiring R} (h : ∀ x : R, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

@[simp]
lemma coe_mk (S : Subsemiring R) (h) : ((⟨S, h⟩ : StarSubsemiring R) : Set R) = S := rfl

@[simp]
theorem mem_toSubsemiring {S : StarSubsemiring R} {x} : x ∈ S.toSubsemiring ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem coe_toSubsemiring (S : StarSubsemiring R) : (S.toSubsemiring : Set R) = S :=
  rfl

theorem toSubsemiring_injective :
    Function.Injective (toSubsemiring : StarSubsemiring R → Subsemiring R) := fun S T h =>
  ext fun x => by rw [← mem_toSubsemiring, ← mem_toSubsemiring, h]

theorem toSubsemiring_inj {S U : StarSubsemiring R} : S.toSubsemiring = U.toSubsemiring ↔ S = U :=
  toSubsemiring_injective.eq_iff

theorem toSubsemiring_le_iff {S₁ S₂ : StarSubsemiring R} :
    S₁.toSubsemiring ≤ S₂.toSubsemiring ↔ S₁ ≤ S₂ :=
  Iff.rfl

/-- Copy of a non-unital star subalgebra with a new `carrier` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (S : StarSubsemiring R) (s : Set R) (hs : s = ↑S) : StarSubsemiring R where
  toSubsemiring := Subsemiring.copy S.toSubsemiring s hs
  star_mem' := @fun a ha => hs ▸ (S.star_mem' (by simpa [hs] using ha) : star a ∈ (S : Set R))

@[simp, norm_cast]
theorem coe_copy (S : StarSubsemiring R) (s : Set R) (hs : s = ↑S) : (S.copy s hs : Set R) = s :=
  rfl

theorem copy_eq (S : StarSubsemiring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

section Center

variable (R)

/-- The center of a semiring `R` is the set of elements that commute and associate with everything
in `R` -/
def center (R) [NonAssocSemiring R] [StarRing R] : StarSubsemiring R where
  toSubsemiring := Subsemiring.center R
  star_mem' := Set.star_mem_center

end Center

end StarSubsemiring

end StarSubsemiring
section SubStarSemigroup

variable (A) [Mul A] [StarMul A]

namespace SubStarSemigroup

/-- The center of magma `A` is the set of elements that commute and associate
with everything in `A`, here realized as a `SubStarSemigroup`. -/
def center : SubStarSemigroup A :=
  { Subsemigroup.center A with
    star_mem' := Set.star_mem_center }

end SubStarSemigroup

end SubStarSemigroup
