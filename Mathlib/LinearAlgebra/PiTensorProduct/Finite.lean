/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.RingTheory.Finiteness.Basic

import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# A multiple tensor product of finitely generated modules is finitely generated

-/

public section

open TensorProduct

namespace PiTensorProduct

/-- The tensor product `⨂[R] i, M i` of a finite collection of finite modules `M i` over a
`CommSemiring` is finite.
-/
instance finite {R : Type*} [CommSemiring R] {ι : Type*} [Finite ι] {M : ι → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [∀ i, Module.Finite R (M i)] :
    Module.Finite R (⨂[R] i, M i) := by
  obtain ⟨n, hι⟩ : ∃ (n : ℕ), Nat.card ι = n := ⟨_, rfl⟩
  induction n generalizing ι with
  | zero =>
    let : IsEmpty ι := (Nat.card_eq_zero.mp hι).resolve_right (Finite.not_infinite ‹_›)
    exact Module.Finite.of_surjective
      (isEmptyEquiv ι).symm.toLinearMap
      (isEmptyEquiv ι).symm.surjective
  | succ n hn =>
    classical
    let : Nonempty ι := (Nat.card_pos_iff.mp (by omega)).left
    let i₀ := Classical.arbitrary ι
    have hi₀ : Nat.card ({i₀}ᶜ : Set ι) = n := by
      let := Fintype.ofFinite ι
      rw [← Fintype.card_eq_nat_card, Fintype.card_compl_set, Fintype.card_eq_nat_card, hι,
        Fintype.card_unique, add_tsub_cancel_right]
    let : Module.Finite R (⨂[R] (i : ({i₀}ᶜ : Set ι)), M i) := hn hi₀
    exact Module.Finite.of_surjective
      (equivPiTensorComplSingletonTensor R M i₀).symm.toLinearMap
      (equivPiTensorComplSingletonTensor R M i₀).symm.surjective

end PiTensorProduct
