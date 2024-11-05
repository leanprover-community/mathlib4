/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Generators of multiple tensor products

Given a finite family of `R`-modules `M i`, if we have, for each `i`,
a family of generators of the module `M i`, then the tensor
products of these elements generate `⨂[R] i, M i`.

-/

open TensorProduct

variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
  {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  {N : Type*} [AddCommMonoid N] [Module R N]
  {γ : ι → Type*} {g : ⦃i : ι⦄ → (j : γ i) → M i}

lemma MultilinearMap.ext_of_span_eq_top
    (hg : ∀ i, Submodule.span R (Set.range (@g i)) = ⊤)
    {φ φ' : MultilinearMap R M N}
    (h : ∀ (j : (i : ι) → γ i), φ (fun i ↦ g (j i)) = φ' (fun i ↦ g (j i))) :
    φ = φ' := by
  obtain ⟨n, hn⟩ : ∃ (n : ℕ), Nat.card ι = n := ⟨_, rfl⟩
  revert ι
  induction n with
  | zero =>
      intro ι _ M _ _ γ g _ φ φ' h hι
      ext x
      have : IsEmpty ι := by
        rw [Nat.card_eq_zero] at hι
        obtain (_ | h) := hι
        · assumption
        · exfalso
          rw [← not_finite_iff_infinite] at h
          exact h inferInstance
      obtain rfl : x = fun i ↦ @g i (by apply isEmptyElim) := by
        ext i
        apply @isEmptyElim (a := i) _ _
      apply h
  | succ n hn =>
      intro ι _ M _ _ γ g hg φ φ' h hι
      have : Nonempty ι := sorry
      have i₀ : ι := Classical.arbitrary _
      let M' := fun (i : ({i₀}ᶜ : Set ι)) ↦ M i
      let c : MultilinearMap R M N → (M i₀ →ₗ[R] MultilinearMap R M' N) := fun ψ ↦
        { toFun := fun m₀ ↦
            { toFun := fun m' ↦ by
                -- better wait #18534
                sorry
              map_add' := sorry
              map_smul' := sorry }
          map_add' := sorry
          map_smul' := sorry }
      sorry

lemma PiTensorProduct.submodule_span_eq_top
    (hg : ∀ i, Submodule.span R (Set.range (@g i)) = ⊤) :
    Submodule.span R (Set.range (fun j : ((i : ι) → γ i) ↦
      ⨂ₜ[R] (i : ι), g (j i))) = ⊤ := by
  rw [← (Submodule.span R _).ker_mkQ, LinearMap.ker_eq_top]
  refine ext (MultilinearMap.ext_of_span_eq_top hg (fun j ↦ ?_))
  simp only [LinearMap.compMultilinearMap_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, LinearMap.zero_apply]
  exact Submodule.subset_span ⟨j, rfl⟩
