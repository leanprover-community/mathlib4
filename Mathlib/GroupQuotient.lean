import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Algebra.Quotient
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Group

variable {G : Type*} [Group G] (N : Subgroup G) [hN : N.Normal]

def Subgroup.sameCoset_equivalence : Equivalence (· * ·⁻¹ ∈ N) where
  refl := fun _ ↦ by
    convert N.one_mem
    group
  symm := fun hxy ↦ by
    convert N.inv_mem hxy using 1
    group
  trans := fun hxy hyz ↦ by
    convert N.mul_mem hxy hyz using 1
    group

instance : HasQuotient G (Subgroup G) where
  quotient' N := Quotient ({r := (· * ·⁻¹ ∈ N), iseqv := N.sameCoset_equivalence})

instance : One (G ⧸ N) where
  one := ⟦1⟧

instance : Mul (G ⧸ N) where
  mul := Quotient.lift₂ (⟦· * ·⟧) <| by
    intro a₁ b₁ a₂ b₂ (ha : _ ∈ N) (hb : _ ∈ N)
    apply Quotient.sound
    show _ ∈ N
    convert N.mul_mem ha (hN.conj_mem _ hb a₂) using 1
    group

instance : Inv (G ⧸ N) where
  inv := Quotient.lift (⟦· ⁻¹⟧) <| by
    intro a b (h : _ ∈ N)
    apply Quotient.sound
    show _ ∈ N
    convert hN.conj_mem _ (N.inv_mem h) a⁻¹ using 1
    group

instance : Group (G ⧸ N) := Group.ofLeftAxioms
  (assoc := fun a b c ↦ Quotient.inductionOn₃ a b c <| fun a b c ↦ Quotient.sound <| by
    show _ ∈ N
    convert N.one_mem
    group)
  (one_mul := Quotient.ind <| fun a ↦ Quotient.sound <| by
    show _ ∈ N
    convert N.one_mem
    group)
  (mul_left_inv := Quotient.ind <| fun a ↦ Quotient.sound <| by
    show _ ∈ N
    convert N.one_mem
    group)
