import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Algebra.Quotient
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Group

variable {G : Type*} [Group G] (N : Subgroup G) [hN : N.Normal]

def Subgroup.sameCoset_equivalence : Equivalence (· * ·⁻¹ ∈ N) where
  refl _ := by
    convert N.one_mem
    group
  symm hxy := by
    convert N.inv_mem hxy using 1
    group
  trans hxy hyz := by
    convert N.mul_mem hxy hyz using 1
    group

instance : HasQuotient G (Subgroup G) where
  quotient' N := Quotient ({r := (· * ·⁻¹ ∈ N), iseqv := N.sameCoset_equivalence})

instance : One (G ⧸ N) where
  one := ⟦1⟧

instance : Mul (G ⧸ N) where
  mul := Quotient.lift₂ (⟦· * ·⟧) <| by
    intro a₁ b₁ a₂ b₂ (ha : _ ∈ N) (hb : _ ∈ N)
    suffices _ ∈ N from Quotient.sound this
    convert N.mul_mem ha (hN.conj_mem _ hb a₂) using 1
    group

instance : Inv (G ⧸ N) where
  inv := Quotient.lift (⟦· ⁻¹⟧) <| by
    intro a b (h : _ ∈ N)
    suffices _ ∈ N from Quotient.sound this
    convert hN.conj_mem _ (N.inv_mem h) a⁻¹ using 1
    group

instance : Group (G ⧸ N) := Group.ofLeftAxioms
  (assoc := fun a b c ↦ Quotient.inductionOn₃ a b c <| by
    intro a b c
    suffices _ ∈ N from Quotient.sound this
    convert N.one_mem
    group)
  (one_mul := Quotient.ind <| by
    intro a
    suffices _ ∈ N from Quotient.sound this
    convert N.one_mem
    group)
  (mul_left_inv := Quotient.ind <| by
    intro a
    suffices _ ∈ N from Quotient.sound this
    convert N.one_mem
    group)
