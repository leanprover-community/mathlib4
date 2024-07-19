/-
Copyright (c) 2024 Lagrange Mathematics and Computing Research Center. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Anthony Bordg
-/
import Mathlib.Data.Rel
import Mathlib.Order.GaloisConnection

/-!
# The Galois Connection Induced by a Relation

In this file, we show that an arbitrary relation `R` between a pair of types `α` and `β` defines
a pair `l` and `u` of adjoint order-preserving maps between the corresponding posets
`Set α` and `(Set β)ᵒᵈ`.
We define `lFixedPoints` (resp. `uFixedPoints`) as the set of fixed points `J` (resp. `I`) of
`Set α` (resp. `(Set β)ᵒᵈ`) such that `u (l J) = J` (resp. `l (u I) = I`).

## Main Results

⋆ `to_galoisConnection`: we prove that the maps `l` and `u` form a Galois connection.
⋆ `instEquivFixedPoints`: we prove that the said maps induce inverse bijections between the sets
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

/-- `l` maps any set `J` of elements of type `α` to the set `{b : β | ∀ a ∈ J, R a b}` of
elements `b` of type `β` such that `R a b` for every element `a` of `J`. -/
def l (J : Set α) : (Set β)ᵒᵈ := toDual {b : β | ∀ a ∈ J, R a b}

/-- `u` maps any set `I` of elements of type `β` to the set `{a : α | ∀ b ∈ ofDual I, R a b}`
of elements `a` of type `α` such that `R a b` for every element `b` of `I`. -/
def u (I : (Set β)ᵒᵈ) : Set α := {a : α | ∀ b ∈ ofDual I, R a b}

/-- The pair of functions `l` and `u` forms a Galois connection. -/
theorem to_galoisConnection : GaloisConnection (l R) (u R) := by
    intros J I; apply Iff.trans (b := ∀ b ∈ ofDual I, ∀ a ∈ J, R a b)
    · constructor
      · intro h; apply h
      · intro h; apply h
    · constructor
      · intro h; unfold u; intro a ha b hb; apply h; simpa; exact ha
      · intro h; intro b hb a ha; apply h; simpa; exact hb

/-! ### Induced equivalences and generation processes -/

/-- `lFixedPoints` is the set of elements `J : Set α` satisfying `u (l J) = J`. -/
def lFixedPoints := {J : Set α | u R (l R J) = J}

/-- `uFixedPoints` is the set of elements `I : (Set β)ᵒᵈ` satisfying `l (u I) = I`. -/
def uFixedPoints := {I : (Set β)ᵒᵈ | l R (u R I) = I}

open GaloisConnection

/-- `l` maps every element `J` to `uFixedPoints`. -/
@[simp]
theorem is_uFixedPoint (J : Set α) : l R J ∈ uFixedPoints R := by
    unfold uFixedPoints; simp; apply le_antisymm
    · exact (to_galoisConnection R).l_u_le (l R J)
    · apply (to_galoisConnection R).monotone_l; exact (to_galoisConnection R).le_u_l J

/-- `u` maps every element `I` to `lFixedPoints`. -/
@[simp]
theorem is_lFixedPoint (I : (Set β)ᵒᵈ) : u R I ∈ lFixedPoints R := by
    unfold lFixedPoints; simp; apply le_antisymm
    · apply (to_galoisConnection R).monotone_u; exact (to_galoisConnection R).l_u_le I
    · exact (to_galoisConnection R).le_u_l (u R I)

/-- The maps `l` and `u` induce inverse bijections between the sets of fixed points. -/
instance instEquivFixedPoints : lFixedPoints R ≃ uFixedPoints R :=
    { toFun := fun ⟨J, _⟩ => ⟨l R J, is_uFixedPoint R J⟩
      invFun := fun ⟨I, _⟩ => ⟨u R I, is_lFixedPoint R I⟩
      left_inv := by
          intro J; simp; cases' J with J hJ; simp; rw[hJ]
      right_inv := by
          intro I; simp; cases' I with I hI; simp; rw[hI] }

theorem le_imp_u_l_le {J J' : Set α} (h : J' ∈ lFixedPoints R) : J ≤ J' → u R (l R J) ≤ J' := by
    intro h₁; rw[← h]; apply (to_galoisConnection R).monotone_u;
    apply (to_galoisConnection R).monotone_l; exact h₁

theorem ge_imp_ge_l_u {I I' : (Set β)ᵒᵈ} (h : I' ∈ uFixedPoints R) : I' ≥ I → I' ≥ l R (u R I) := by
    intro h₁; rw [← h]; apply (to_galoisConnection R).monotone_l;
    apply (to_galoisConnection R).monotone_u; exact h₁

end Rel
