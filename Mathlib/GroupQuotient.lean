import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Analysis.Normed.Field.Basic

variable {G : Type*} [Group G] (N : Subgroup G) [hN : N.Normal]

def bar : Equivalence (· * ·⁻¹ ∈ N) where
  refl := fun _ ↦ by
    convert N.one_mem
    group
  symm := fun hxy ↦ by
    convert N.inv_mem hxy using 1
    group
  trans := fun hxy hyz ↦ by
    convert N.mul_mem hxy hyz using 1
    group

def foo : Setoid G where
  r := (· * ·⁻¹ ∈ N)
  iseqv := bar N

instance i₁ : One (Quotient (foo N)) where
  one := ⟦1⟧

instance i₂ : Mul (Quotient (foo N)) where
  mul := Quotient.lift₂ (⟦· * ·⟧) <| by
    intro a₁ b₁ a₂ b₂ (ha : _ ∈ N) (hb : _ ∈ N)
    simp
    show _ ∈ N
    convert N.mul_mem ha (hN.conj_mem _ hb a₂) using 1
    group

instance i₃ : Inv (Quotient (foo N)) where
  inv := Quotient.lift (⟦· ⁻¹⟧) <| by
    intro a b (h : _ ∈ N)
    simp
    show _ ∈ N
    convert hN.conj_mem _ (N.inv_mem h) a⁻¹ using 1
    group

instance : Group (Quotient (foo N)) := Group.ofLeftAxioms
  (assoc := fun a b c ↦ Quotient.inductionOn₃ a b c <| fun a b c ↦ Quotient.sound <| by
    show _ ∈ N
    convert N.one_mem
    group) -- ⊢ a * b * c * (a * (b * c))⁻¹ = 1
  (one_mul := Quotient.ind <| fun a ↦ Quotient.sound <| by
    show _ ∈ N
    convert N.one_mem
    group) -- ⊢ 1 * a * a⁻¹ = 1
  (mul_left_inv := Quotient.ind <| fun a ↦ Quotient.sound <| by
    show _ ∈ N
    convert N.one_mem
    group) -- ⊢ a⁻¹ * a * 1⁻¹ = 1

#min_imports -- debug this!
