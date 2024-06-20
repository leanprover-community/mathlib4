/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Order.Group.PiLex
import Mathlib.Algebra.Polynomial.Reverse

#align_import map_floor from "leanprover-community/mathlib"@"328375597f2c0dd00522d9c2e5a33b6a6128feeb"

/-!
# Floors and ceils aren't preserved under ordered ring homomorphisms

Intuitively, if `f : α → β` is an ordered ring homomorphism, then floors and ceils should be
preserved by `f` because:
* `f` preserves the naturals/integers in `α` and `β` because it's a ring hom.
* `f` preserves what's between `n` and `n + 1` because it's monotone.

However, there is a catch. Potentially something whose floor was `n` could
get mapped to `n + 1`, and this has floor `n + 1`, not `n`. Note that this is at most an off by one
error.

This pathology disappears if you require `f` to be strictly monotone or `α` to be archimedean.

## The counterexample

Consider `ℤ[ε]` (`IntWithEpsilon`), the integers with infinitesimals adjoined. This is a linearly
ordered commutative floor ring (`IntWithEpsilon.linearOrderedCommRing`,
`IntWithEpsilon.floorRing`).

The map `f : ℤ[ε] → ℤ` that forgets about the epsilons (`IntWithEpsilon.forgetEpsilons`) is an
ordered ring homomorphism.

But it does not preserve floors (nor ceils) as `⌊-ε⌋ = -1` while `⌊f (-ε)⌋ = ⌊0⌋ = 0`
(`IntWithEpsilon.forgetEpsilons_floor_lt`, `IntWithEpsilon.lt_forgetEpsilons_ceil`).
-/


namespace Counterexample

noncomputable section

open Function Int Polynomial

open scoped Polynomial

/-- The integers with infinitesimals adjoined. -/
def IntWithEpsilon :=
  ℤ[X] deriving Nontrivial
#align counterexample.int_with_epsilon Counterexample.IntWithEpsilon

local notation "ℤ[ε]" => IntWithEpsilon

local notation "ε" => (X : ℤ[ε])

namespace IntWithEpsilon

instance nontrivial : Nontrivial IntWithEpsilon := inferInstance

-- Porting note: `inhabited` and `commRing` were `deriving` instances in mathlib3
instance commRing : CommRing IntWithEpsilon := Polynomial.commRing

instance inhabited : Inhabited IntWithEpsilon := ⟨69⟩

instance linearOrder : LinearOrder ℤ[ε] :=
  LinearOrder.lift' (toLex ∘ coeff) coeff_injective

instance orderedAddCommGroup : OrderedAddCommGroup ℤ[ε] := by
  refine (toLex.injective.comp coeff_injective).orderedAddCommGroup _ ?_ ?_ ?_ ?_ ?_ ?_ <;>
  (first | rfl | intros) <;> funext <;>
  (simp only [comp_apply, Pi.toLex_apply, coeff_add, coeff_neg, coeff_sub,
    ← nsmul_eq_mul, ← zsmul_eq_mul]; rfl)

theorem pos_iff {p : ℤ[ε]} : 0 < p ↔ 0 < p.trailingCoeff := by
  rw [trailingCoeff]
  refine
    ⟨?_, fun h =>
      ⟨p.natTrailingDegree, fun m hm => (coeff_eq_zero_of_lt_natTrailingDegree hm).symm, h⟩⟩
  rintro ⟨n, hn⟩
  convert hn.2
  exact (natTrailingDegree_le_of_ne_zero hn.2.ne').antisymm
    (le_natTrailingDegree (by rintro rfl; cases hn.2.false) fun m hm => (hn.1 _ hm).symm)
#align counterexample.int_with_epsilon.pos_iff Counterexample.IntWithEpsilon.pos_iff

instance : LinearOrderedCommRing ℤ[ε] :=
  { IntWithEpsilon.linearOrder, IntWithEpsilon.commRing, IntWithEpsilon.orderedAddCommGroup,
    IntWithEpsilon.nontrivial with
    zero_le_one := Or.inr ⟨0, by simp⟩
    mul_pos := fun p q => by simp_rw [pos_iff]; rw [trailingCoeff_mul]; exact mul_pos}

instance : FloorRing ℤ[ε] :=
  FloorRing.ofFloor _ (fun p => if (p.coeff 0 : ℤ[ε]) ≤ p then p.coeff 0 else p.coeff 0 - 1)
    fun p q => by
    simp_rw [← not_lt, not_iff_not]
    constructor
    · split_ifs with h
      · rintro ⟨_ | n, hn⟩
        · apply (sub_one_lt _).trans _
          simp at hn
          rwa [intCast_coeff_zero] at hn
        · dsimp at hn
          simp [hn.1 _ n.zero_lt_succ]
          rw [intCast_coeff_zero]; simp
      · exact fun h' => cast_lt.1 ((not_lt.1 h).trans_lt h')
    · split_ifs with h
      · exact fun h' => h.trans_le (cast_le.2 <| sub_one_lt_iff.1 h')
      · exact fun h' => ⟨0, by simp; rwa [intCast_coeff_zero]⟩

/-- The ordered ring homomorphisms from `ℤ[ε]` to `ℤ` that "forgets" the `ε`s. -/
def forgetEpsilons : ℤ[ε] →+*o ℤ where
  toFun p := coeff p 0
  map_zero' := coeff_zero _
  map_one' := coeff_one_zero
  map_add' _ _ := coeff_add _ _ _
  map_mul' := mul_coeff_zero
  monotone' := monotone_iff_forall_lt.2 (by
    rintro p q ⟨n, hn⟩
    cases' n with n
    · exact hn.2.le
    · exact (hn.1 _ n.zero_lt_succ).le)
#align counterexample.int_with_epsilon.forget_epsilons Counterexample.IntWithEpsilon.forgetEpsilons

@[simp]
theorem forgetEpsilons_apply (p : ℤ[ε]) : forgetEpsilons p = coeff p 0 :=
  rfl
#align counterexample.int_with_epsilon.forget_epsilons_apply Counterexample.IntWithEpsilon.forgetEpsilons_apply

/-- The floor of `n - ε` is `n - 1` but its image under `forgetEpsilons` is `n`, whose floor is
itself. -/
theorem forgetEpsilons_floor_lt (n : ℤ) :
    forgetEpsilons ⌊(n - ↑ε : ℤ[ε])⌋ < ⌊forgetEpsilons (n - ↑ε)⌋ := by
  suffices ⌊(n - ↑ε : ℤ[ε])⌋ = n - 1 by simp [this]
  have : (0 : ℤ[ε]) < ε := ⟨1, by simp⟩
  exact (if_neg <| by rw [coeff_sub, intCast_coeff_zero]; simp [this]).trans (by
    rw [coeff_sub, intCast_coeff_zero]; simp)
#align counterexample.int_with_epsilon.forget_epsilons_floor_lt Counterexample.IntWithEpsilon.forgetEpsilons_floor_lt

/-- The ceil of `n + ε` is `n + 1` but its image under `forgetEpsilons` is `n`, whose ceil is
itself. -/
theorem lt_forgetEpsilons_ceil (n : ℤ) :
    ⌈forgetEpsilons (n + ↑ε)⌉ < forgetEpsilons ⌈(n + ↑ε : ℤ[ε])⌉ := by
  rw [← neg_lt_neg_iff, ← map_neg, ← cast_neg, ← floor_neg, ← floor_neg, ← map_neg, neg_add', ←
    cast_neg]
  exact forgetEpsilons_floor_lt _
#align counterexample.int_with_epsilon.lt_forget_epsilons_ceil Counterexample.IntWithEpsilon.lt_forgetEpsilons_ceil

end IntWithEpsilon

end

end Counterexample
