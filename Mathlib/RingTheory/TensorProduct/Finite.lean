/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johan Commelin
-/
import Mathlib.RingTheory.Finiteness.TensorProduct
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Finiteness results related to tensor products

In this file we show that the supremum of two subalgebras that are finitely generated as modules,
is again finitely generated.

-/

theorem Subalgebra.finite_sup {K L : Type*} [CommSemiring K] [CommSemiring L] [Algebra K L]
    (E1 E2 : Subalgebra K L) [Module.Finite K E1] [Module.Finite K E2] :
    Module.Finite K ↥(E1 ⊔ E2) := by
  rw [← E1.range_val, ← E2.range_val, ← Algebra.TensorProduct.productMap_range]
  exact Module.Finite.range (Algebra.TensorProduct.productMap E1.val E2.val).toLinearMap

open TensorProduct in
lemma RingHom.surjective_of_tmul_eq_tmul_of_finite {R S}
    [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (h₁ : ∀ s : S, s ⊗ₜ[R] 1 = 1 ⊗ₜ s) : Function.Surjective (algebraMap R S) := by
  let R' := LinearMap.range (Algebra.ofId R S).toLinearMap
  rcases subsingleton_or_nontrivial (S ⧸ R') with h | _
  · rwa [Submodule.subsingleton_quotient_iff_eq_top, LinearMap.range_eq_top] at h
  have : Subsingleton ((S ⧸ R') ⊗[R] (S ⧸ R')) := by
    refine subsingleton_of_forall_eq 0 fun y ↦ ?_
    induction y with
    | zero => rfl
    | add a b e₁ e₂ => rwa [e₁, zero_add]
    | tmul x y =>
      obtain ⟨x, rfl⟩ := R'.mkQ_surjective x
      obtain ⟨y, rfl⟩ := R'.mkQ_surjective y
      obtain ⟨s, hs⟩ : ∃ s, 1 ⊗ₜ[R] s = x ⊗ₜ[R] y := by
        use x * y
        trans x ⊗ₜ 1 * 1 ⊗ₜ y
        · simp [h₁]
        · simp
      have : R'.mkQ 1 = 0 := (Submodule.Quotient.mk_eq_zero R').mpr ⟨1, map_one (algebraMap R S)⟩
      rw [← map_tmul R'.mkQ R'.mkQ, ← hs, map_tmul, this, zero_tmul]
  cases false_of_nontrivial_of_subsingleton ((S ⧸ R') ⊗[R] (S ⧸ R'))
