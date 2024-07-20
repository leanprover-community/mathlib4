/-
Copyright (c) 2024 Lagrange Mathematics and Computing Research Center. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Bordg
-/
import Mathlib.Data.Rel
import Mathlib.Order.GaloisConnection

/-!
# The Galois Connection Induced by a Relation

In this file, we show that an arbitrary relation `R` between a pair of types `α` and `β` defines
a pair `leftDual` and `rightDual` of adjoint order-preserving maps between the corresponding posets
`Set α` and `(Set β)ᵒᵈ`.
We define `lFixedPoints` (resp. `rFixedPoints`) as the set of fixed points `J` (resp. `I`) of
`Set α` (resp. `(Set β)ᵒᵈ`) such that `rightDual (leftDual J) = J` (resp.
`leftDual (rightDual I) = I`).

## Main Results

⋆ `galoisConnection`: we prove that the maps `leftDual` and `rightDual` form a Galois connection.
⋆ `equivFixedPoints`: we prove that the said maps induce inverse bijections between the sets
of fixed points.

## References

⋆ Engendrement de topologies, démontrabilité et opérations sur les sous-topos, Olivia Caramello and
Laurent Lafforgue (in preparation)

## Tags

relation, Galois connection, induced bijection, fixed points
-/

section

universe u v

variable {α : Type u} {β : Type v} (R : Rel α β)

namespace Rel

/-! ### Pairs of adjoint maps defined by relations -/

open OrderDual

/-- `leftDual` maps any set `J` of elements of type `α` to the set `{b : β | ∀ a ∈ J, R a b}` of
elements `b` of type `β` such that `R a b` for every element `a` of `J`. -/
def leftDual (J : Set α) : (Set β)ᵒᵈ := toDual {b : β | ∀ ⦃a⦄, a ∈ J → R a b}

/-- `rightDual` maps any set `I` of elements of type `β` to the set `{a : α | ∀ b ∈ ofDual I, R a b}`
of elements `a` of type `α` such that `R a b` for every element `b` of `I`. -/
def rightDual (I : (Set β)ᵒᵈ) : Set α := {a : α | ∀ ⦃b⦄, b ∈ ofDual I → R a b}

/-- The pair of functions `leftDual` and `rightDual` forms a Galois connection. -/
theorem galoisConnection : GaloisConnection R.leftDual R.rightDual := by
    intros J I; apply Iff.trans (b := ∀ b ∈ ofDual I, ∀ a ∈ J, R a b)
    · constructor <;> intro h <;> apply h
    · constructor
      · intro h a ha b hb
        exact h (by simpa) hb a ha
      · intro h b hb a ha
        exact h (by simpa) hb

/-! ### Induced equivalences and generation processes -/

/-- `lFixedPoints` is the set of elements `J : Set α` satisfying `rightDual (leftDual J) = J`. -/
def lFixedPoints := {J : Set α | R.rightDual (R.leftDual J) = J}

/-- `rFixedPoints` is the set of elements `I : (Set β)ᵒᵈ` satisfying `leftDual (rightDual I) = I`.
-/
def rFixedPoints := {I : (Set β)ᵒᵈ | R.leftDual (R.rightDual I) = I}

open GaloisConnection

/-- `leftDual` maps every element `J` to `rFixedPoints`. -/
theorem leftDual_mem_rFixedPoint (J : Set α) : R.leftDual J ∈ R.rFixedPoints := by
    unfold rFixedPoints; apply le_antisymm
    · exact (galoisConnection R).l_u_le (R.leftDual J)
    · apply (galoisConnection R).monotone_l; exact (galoisConnection R).le_u_l J

/-- `rightDual` maps every element `I` to `lFixedPoints`. -/
theorem rightDual_mem_lFixedPoint (I : (Set β)ᵒᵈ) : R.rightDual I ∈ R.lFixedPoints := by
    unfold lFixedPoints; apply le_antisymm
    · apply (galoisConnection R).monotone_u; exact (galoisConnection R).l_u_le I
    · exact (galoisConnection R).le_u_l (R.rightDual I)

/-- The maps `leftDual` and `rightDual` induce inverse bijections between the sets of fixed points.
-/
def equivFixedPoints : R.lFixedPoints ≃ R.rFixedPoints where
  toFun := fun ⟨J, _⟩ => ⟨R.leftDual J, R.leftDual_mem_rFixedPoint J⟩
  invFun := fun ⟨I, _⟩ => ⟨R.rightDual I, R.rightDual_mem_lFixedPoint I⟩
  left_inv J := by cases' J with J hJ; simp; rw [hJ]
  right_inv I := by cases' I with I hI; simp; rw [hI]

theorem le_imp_u_l_le {J J' : Set α} (h : J' ∈ R.lFixedPoints) :
    J ≤ J' → R.rightDual (R.leftDual J) ≤ J' := by
  intro h₁
  rw[← h]
  apply (galoisConnection R).monotone_u
  apply (galoisConnection R).monotone_l
  exact h₁

theorem ge_imp_ge_l_u {I I' : (Set β)ᵒᵈ} (h : I' ∈ rFixedPoints R) :
    I' ≥ I → I' ≥ R.leftDual (R.rightDual I) := by
  intro h₁
  rw [← h]
  apply (galoisConnection R).monotone_l
  apply (galoisConnection R).monotone_u
  exact h₁

end Rel

end
