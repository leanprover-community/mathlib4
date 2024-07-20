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
theorem galoisConnection : GaloisConnection (leftDual R) (rightDual R) := by
    intros J I; apply Iff.trans (b := ∀ b ∈ ofDual I, ∀ a ∈ J, R a b)
    · constructor <;> intro h <;> apply h
    · constructor
      · intro h
        unfold rightDual
        intro a ha b hb
        apply h
        simpa
        exact ha
      · intro h
        intro b hb a ha
        apply h
        simpa
        exact hb

/-! ### Induced equivalences and generation processes -/

/-- `lFixedPoints` is the set of elements `J : Set α` satisfying `rightDual (leftDual J) = J`. -/
def lFixedPoints := {J : Set α | rightDual R (leftDual R J) = J}

/-- `rFixedPoints` is the set of elements `I : (Set β)ᵒᵈ` satisfying `leftDual (rightDual I) = I`.
-/
def rFixedPoints := {I : (Set β)ᵒᵈ | leftDual R (rightDual R I) = I}

open GaloisConnection

/-- `leftDual` maps every element `J` to `rFixedPoints`. -/
theorem is_rFixedPoint (J : Set α) : leftDual R J ∈ rFixedPoints R := by
    unfold rFixedPoints; apply le_antisymm
    · exact (galoisConnection R).l_u_le (leftDual R J)
    · apply (galoisConnection R).monotone_l; exact (galoisConnection R).le_u_l J

/-- `rightDual` maps every element `I` to `lFixedPoints`. -/
theorem is_lFixedPoint (I : (Set β)ᵒᵈ) : rightDual R I ∈ lFixedPoints R := by
    unfold lFixedPoints; apply le_antisymm
    · apply (galoisConnection R).monotone_u; exact (galoisConnection R).l_u_le I
    · exact (galoisConnection R).le_u_l (rightDual R I)

/-- The maps `leftDual` and `rightDual` induce inverse bijections between the sets of fixed points.
-/
def equivFixedPoints : lFixedPoints R ≃ rFixedPoints R where
    toFun := fun ⟨J, _⟩ => ⟨leftDual R J, is_rFixedPoint R J⟩
    invFun := fun ⟨I, _⟩ => ⟨rightDual R I, is_lFixedPoint R I⟩
    left_inv := by intro J; cases' J with J hJ; simp; rw [hJ]
    right_inv := by intro I; cases' I with I hI; simp; rw [hI]

theorem le_imp_u_l_le {J J' : Set α} (h : J' ∈ lFixedPoints R) :
        J ≤ J' → rightDual R (leftDual R J) ≤ J' := by
    intro h₁
    rw[← h]
    apply (galoisConnection R).monotone_u
    apply (galoisConnection R).monotone_l
    exact h₁

theorem ge_imp_ge_l_u {I I' : (Set β)ᵒᵈ} (h : I' ∈ rFixedPoints R) :
        I' ≥ I → I' ≥ leftDual R (rightDual R I) := by
    intro h₁
    rw [← h]
    apply (galoisConnection R).monotone_l
    apply (galoisConnection R).monotone_u
    exact h₁

end Rel

end
