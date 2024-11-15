/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Sophie Morel
-/

import Mathlib.LinearAlgebra.ExteriorPower.Generators
import Mathlib.LinearAlgebra.ExteriorPower.Pairing
import Mathlib.Order.Extension.Well

/-!
# Exterior powers of free modules are free

The main definition in this file is `Basis.exteriorPower`. Given a basis `b : Basis ι R M`,
we construct `b.exteriorPower n` which is a basis of the `R`-module `⋀[R]^n M` indexed
by `Fin n ↪o ι`, assuming `ι` is linearly ordered.

-/

section

variable (ι : Type*) [LinearOrder ι]

-- to be moved
noncomputable def finOrderEmbeddingEquiv (n : ℕ) :
    (Fin n ↪o ι) ≃ { s : Finset ι // s.card = n } where
  toFun f := ⟨Finset.mapEmbedding f.toEmbedding ⊤, by simp⟩
  invFun s := Finset.orderEmbOfFin s.1 s.2
  left_inv f := sorry
  right_inv := by
    rintro ⟨s, hs⟩
    dsimp
    simp only [Subtype.mk.injEq]
    exact Finset.coe_injective (by simp)

end

-- for LinearAlgebra.LinearIndependent
section

variable {ι R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- If `v : ι → M` is a family of vectors and there exists a family of linear forms
`dv : ι → (M →ₗ[R] R)` such that `dv i (v j)` is `1` for `i = j` and `0` for `i ≠ j`, then
`v` is linearly independent. -/
theorem linearIndependent_of_dualFamily (v : ι → M) (dv : ι → (M →ₗ[R] R))
    (h₁ : ∀ (a : ι) (b : ι), a ≠ b → (dv a) (v b) = 0) (h₂ : ∀ (a : ι), (dv a) (v a) = 1) :
    LinearIndependent R v := by
  rw [linearIndependent_iff']
  intro s g hrel i hi
  apply_fun (fun x => dv i x) at hrel
  simp only [map_sum, map_smul, smul_eq_mul, _root_.map_zero] at hrel
  rw [Finset.sum_eq_single i (fun j _ hj ↦ by rw [h₁ i j (Ne.symm hj), mul_zero])
    (fun hi' ↦ False.elim (hi' hi)), h₂ i, mul_one] at hrel
  exact hrel

end

open exteriorPower

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

namespace Basis

variable {ι : Type*} (b : Basis ι R M)

-- to be moved
section

lemma coord_apply_self (x : ι) : b.coord x (b x) = 1 := by
  simp only [coord_apply, repr_self, Finsupp.single_eq_same]

lemma coord_apply_ne {x y : ι} (hxy : x ≠ y) : b.coord x (b y) = 0 := by
  simp only [coord_apply, repr_self, Finsupp.single_eq_of_ne hxy.symm]

end

variable [LinearOrder ι] (n : ℕ)

lemma exteriorPower_linearIndependent :
    LinearIndependent R (ι := Fin n ↪o ι)
      (v := fun f ↦ ιMulti R n (b ∘ f)) := by
  refine linearIndependent_of_dualFamily _
    (fun f ↦ pairingDual R M n (ιMulti _ _ (b.coord ∘ f))) (fun i j hij ↦ ?_) (fun k ↦ ?_)
  · apply pairingDual_apply_apply_eq_zero
    · intros
      simp only [coord_apply, repr_self]
      rw [Finsupp.single_eq_of_ne]
      tauto
    · assumption
  · dsimp
    apply pairingDual_apply_apply_eq_one
    · simp
    · intros
      simp only [coord_apply, repr_self]
      rw [Finsupp.single_eq_of_ne]
      tauto

noncomputable def exteriorPower : Basis (Fin n ↪o ι) R (⋀[R]^n M) :=
  Basis.mk (b.exteriorPower_linearIndependent n)
    (by rw [exteriorPower.span_ιMulti_orderEmbedding_of_span_eq_top (hg := b.span_eq)])

variable {n}

@[simp]
lemma exteriorPower_apply (f : Fin n ↪o ι) :
    (b.exteriorPower n) f = ιMulti R n (b ∘ f) := by
  simp [exteriorPower]

lemma exteriorPower_coord (f : Fin n ↪o ι) :
    (b.exteriorPower n).coord f = pairingDual R M n (ιMulti _ _ (b.coord ∘ f)) := by
  refine (b.exteriorPower n).ext ?_
  intro g
  dsimp only [exteriorPower]
  by_cases h : f = g
  · subst h
    rw [coord_apply_self]
    simp only [coe_mk]
    symm
    apply pairingDual_apply_apply_eq_one
    · simp
    · intro x y hxy
      exact coord_apply_ne _ hxy
  · rw [coord_apply_ne _ h]
    simp only [coe_mk]
    symm
    apply pairingDual_apply_apply_eq_zero (h := h)
    intro x y hxy
    exact coord_apply_ne _ hxy

end Basis

namespace exteriorPower

variable (R M)

instance free [Module.Free R M] (n : ℕ) : Module.Free R (⋀[R]^n M) :=
  have : LinearOrder (Module.Free.ChooseBasisIndex R M) :=
    IsWellFounded.wellOrderExtension emptyWf.rel
  .of_basis ((Module.Free.chooseBasis R M).exteriorPower n)

section StrongRankCondition

variable [StrongRankCondition R]

/-- If `R` satisfies the strong rank condition and `M` is finite free of rank `r`, then
the `n`th exterior power of `M` is of finrank `Nat.choose r n`. -/
lemma finrank_eq [Module.Free R M] [Module.Finite R M] (n : ℕ) :
    Module.finrank R (⋀[R]^n M) =
    Nat.choose (Module.finrank R M) n := by
  have : LinearOrder (Module.Free.ChooseBasisIndex R M) :=
    IsWellFounded.wellOrderExtension emptyWf.rel
  let b := (Module.Free.chooseBasis R M)
  rw [Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis (b.exteriorPower n),
    Fintype.card_congr (finOrderEmbeddingEquiv _ n), Fintype.card_finset_len]

end StrongRankCondition

end exteriorPower
