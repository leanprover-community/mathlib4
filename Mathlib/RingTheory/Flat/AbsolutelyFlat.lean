import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.LocalRing.Defs

/-!
# The absolutely flatness of a ring


-/


-- Where should we place R ⧸ I is projective for f.g. I?

universe u
variable (R : Type u)

@[mk_iff] class IsVonNeumannRegularRing [Semiring R]: Prop where
  exists_pseudo_inverse : ∀ (a : R), ∃ (x : R), a = a * x * a

namespace IsVonNeumannRegularRing

section Semiring

variable [Semiring R]

lemma op_iff : IsVonNeumannRegularRing R ↔ IsVonNeumannRegularRing Rᵐᵒᵖ := by
  rw [isVonNeumannRegularRing_iff, isVonNeumannRegularRing_iff]
  refine ⟨fun h a ↦ ?_, fun h a ↦ ?_⟩
  · obtain ⟨x, hx⟩ := h (MulOpposite.unop a)
    use MulOpposite.op x
    rwa [← MulOpposite.unop_op x, ← MulOpposite.unop_mul, ← MulOpposite.unop_mul,
     MulOpposite.unop_inj, ← mul_assoc] at hx
  · obtain ⟨x, hx⟩ := h (MulOpposite.op a)
    use MulOpposite.unop x
    rwa [← MulOpposite.op_unop x, ← MulOpposite.op_mul, ← MulOpposite.op_mul,
     MulOpposite.op_inj, ← mul_assoc] at hx

theorem of_boolean_ring (h : ∀ x : R, x * x = x) : IsVonNeumannRegularRing R :=
  ⟨fun a ↦ ⟨1, by rw [mul_one, h a]⟩⟩

variable {R} in
theorem _root_.isVonNeumannRegularRing_of_surjective {S : Type*} [Semiring S] (f : R →+* S)
    (hf : Function.Surjective f) [IsVonNeumannRegularRing R] : IsVonNeumannRegularRing S := by
  refine (isVonNeumannRegularRing_iff S).mpr (fun s ↦ ?_)
  obtain ⟨r, rfl⟩ := hf s
  obtain ⟨x, hx⟩ := (isVonNeumannRegularRing_iff R).mp inferInstance r
  exact ⟨f x, by rw [← map_mul, ← map_mul, ← hx]⟩

end Semiring

section CommSemiring

variable [CommSemiring R]

-- This theorem in fact holds for non-commutative rings, so probably can be generalized to Semiring?
-- [Atiyah] Chapter 2, Exercise 27
theorem absolutelyFlat_TFAE :
    [(∀ {N : Type u} [AddCommMonoid N] [Module R N], Module.Flat R N),
      IsVonNeumannRegularRing R,
      ∀ {I : Ideal R}, I.FG → ∃ J : Ideal R, I ⊓ J = ⊥ ∧ I ⊔ J = ⊤].TFAE :=
  sorry

end CommSemiring

section Ring

variable [Ring R]

theorem exists_inverse_nonzero_of_isLocalRing [IsVonNeumannRegularRing R] [IsLocalRing R] :
    ∀ (x : R), x ≠ 0 → (∃ y : R, x * y = 1) := by
  intro x hx
  obtain ⟨y, hy⟩ := (isVonNeumannRegularRing_iff R).mp inferInstance x
  have : (1 - (x * y)) * (x * y) = 0 := by
    rw [← mul_assoc, sub_mul, one_mul, ← hy, sub_self, zero_mul]
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one (show (x * y) + (1 - x * y) = 1 by sorry)
    with (⟨u, hu⟩ | ⟨v, hv⟩)
  · sorry
  · sorry

end Ring

end IsVonNeumannRegularRing
