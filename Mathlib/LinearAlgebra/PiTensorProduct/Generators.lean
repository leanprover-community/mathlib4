/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Data.SubtypeNeLift
import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Generators of multiple tensor products

Given a finite family of `R`-modules `M i`, if we have, for each `i`,
a family of generators of the module `M i`, then the tensor products
of these elements generate `⨂[R] i, M i`.

In `LinearAlgebra.PiTensorProduct.Finite`, we deduce that if the modules `M i`
are finitely generated, then so is `⨂[R] i, M i`.

-/

open TensorProduct

namespace PiTensorProduct

variable (R : Type*)

section equivTensorPiTensorComplSingleto

variable {ι : Type*} [DecidableEq ι] (M : ι → Type*)
  [CommSemiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- The linear equivalence between `⨂[R] i, M i` and the tensor product of `M i₀`
(for some `i₀ : ι`) and the pi tensor product indexed by the complement of `{i₀}`. -/
noncomputable def equivTensorPiTensorComplSingleton (i₀ : ι) :
    (⨂[R] i, M i) ≃ₗ[R] (M i₀ ⊗[R] (⨂[R] (i : ({i₀}ᶜ : Set ι)), M i)) :=
  ((reindex R (s := M) (e := (unitSumSubtypeNeEquiv i₀).symm)).trans
    (tmulEquivDep R
        (fun i => M (unitSumSubtypeNeEquiv i₀ i))).symm).trans
      (LinearEquiv.rTensor _ (subsingletonEquiv (R := R) (M := M i₀) Unit.unit))

variable (i₀ : ι)

@[simp]
lemma equivTensorPiTensorComplSingleton_tprod (i₀ : ι) (m : ∀ i, M i) :
    equivTensorPiTensorComplSingleton R M i₀ (⨂ₜ[R] i, m i) =
      m i₀ ⊗ₜ (⨂ₜ[R] (j : ((Set.singleton i₀)ᶜ : Set ι)), m j) := by
  dsimp [equivTensorPiTensorComplSingleton]
  have h₁ : (reindex R M (unitSumSubtypeNeEquiv i₀).symm) (⨂ₜ[R] (i : ι), m i) =
      ⨂ₜ[R] j, m ((unitSumSubtypeNeEquiv i₀) j) := by
    simp_rw [reindex_tprod (R := R) (s := M), Equiv.symm_symm]
  have h₂ := tmulEquivDep_symm_apply (R := R)
    (N := fun i ↦ (M ((unitSumSubtypeNeEquiv i₀) i)))
  dsimp at h₁ h₂
  rw [h₁, h₂]
  exact (LinearEquiv.rTensor_tmul _ _ _ _).trans (by congr; simp)

@[simp]
lemma equivTensorPiTensorComplSingleton_symm_tmul (i₀ : ι)
    (x : M i₀) (m : ∀ (i : ((Set.singleton i₀)ᶜ : Set ι)), M i) :
    (equivTensorPiTensorComplSingleton R M i₀).symm
      (x ⊗ₜ (⨂ₜ[R] (j : ((Set.singleton i₀)ᶜ : Set ι)), m j)) =
      (⨂ₜ[R] i, Function.subtypeNeLift i₀ m x i) := by
  apply (equivTensorPiTensorComplSingleton R M i₀).injective
  simp only [LinearEquiv.apply_symm_apply, equivTensorPiTensorComplSingleton_tprod,
    Function.subtypeNeLift_self]
  congr
  ext ⟨i, hi⟩
  rw [Function.subtypeNeLift_of_neq]

end equivTensorPiTensorComplSingleto

variable {R} {ι : Type*} [Finite ι] {M : ι → Type*} {N : Type*} {γ : ι → Type*}

section AddCommMonoid
variable
  [CommSemiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [AddCommMonoid N] [Module R N]
  {g : ⦃i : ι⦄ → (j : γ i) → M i}

lemma ext_of_span_eq_top
    (hg : ∀ i, Submodule.span R (Set.range (@g i)) = ⊤)
    {φ φ' : (⨂[R] i, M i) →ₗ[R] N}
    (h : ∀ (j : (i : ι) → γ i),
      φ (tprod _ (fun i ↦ g (j i))) = φ' (tprod _ (fun i ↦ g (j i)))) :
    φ = φ' := by
  obtain ⟨n, hι⟩ : ∃ (n : ℕ), Nat.card ι = n := ⟨_, rfl⟩
  induction n generalizing ι with
  | zero =>
    ext x
    have : IsEmpty ι := (Nat.card_eq_zero.1 hι).resolve_right <| Finite.not_infinite ‹_›
    obtain rfl : x = fun i ↦ @g i (isEmptyElim i) := Subsingleton.elim _ _
    apply h
  | succ n hn =>
    classical
    have : Nonempty ι := ((Nat.card_pos_iff (α := ι)).1 (by omega)).1
    have i₀ : ι := Classical.arbitrary _
    let e := equivTensorPiTensorComplSingleton R M i₀
    obtain ⟨ψ, rfl⟩ : ∃ ψ, φ = LinearMap.comp ψ e.toLinearMap :=
      ⟨φ.comp e.symm.toLinearMap, by ext; simp⟩
    obtain ⟨ψ', rfl⟩ : ∃ ψ', φ' = LinearMap.comp ψ' e.toLinearMap :=
      ⟨φ'.comp e.symm.toLinearMap, by ext; simp⟩
    dsimp [e] at h
    congr 1
    apply (TensorProduct.lift.equiv _ _ _ _).symm.injective
    rw [Submodule.linearMap_eq_iff_of_span_eq_top _ _ (hg i₀)]
    rintro ⟨_, ⟨g₀, rfl⟩⟩
    apply hn (g := fun i (j : γ i.1) ↦ by exact g j)
    · intro i
      exact hg _
    · intro j
      simp only [lift.equiv_symm_apply]
      convert h (Function.subtypeNeLift i₀ j g₀) using 1
      all_goals
        simp only [equivTensorPiTensorComplSingleton_tprod, Function.subtypeNeLift_self]
        congr
        ext ⟨x, hx⟩
        congr
        rw [Function.subtypeNeLift_of_neq]
    · exact Nat.card_compl_of_card_eq_add _ (by simpa)

lemma _root_.MultilinearMap.ext_of_span_eq_top
    (hg : ∀ i, Submodule.span R (Set.range (@g i)) = ⊤)
    {φ φ' : MultilinearMap R M N}
    (h : ∀ (j : (i : ι) → γ i), φ (fun i ↦ g (j i)) = φ' (fun i ↦ g (j i))) :
    φ = φ' := by
  suffices lift φ = lift φ' by
    ext m
    simpa using DFunLike.congr_fun this (tprod _ m)
  exact PiTensorProduct.ext_of_span_eq_top hg (fun j ↦ by simpa using h j)

end AddCommMonoid


variable
  [CommRing R] [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [AddCommMonoid N] [Module R N]
  {g : ⦃i : ι⦄ → (j : γ i) → M i}

lemma submodule_span_eq_top
    (hg : ∀ i, Submodule.span R (Set.range (@g i)) = ⊤) :
    Submodule.span R (Set.range (fun j : ((i : ι) → γ i) ↦
      ⨂ₜ[R] (i : ι), g (j i))) = ⊤ := by
  rw [← (Submodule.span R _).ker_mkQ, LinearMap.ker_eq_top]
  refine ext_of_span_eq_top hg (fun j ↦ ?_)
  simp only [Submodule.mkQ_apply, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span ⟨j, rfl⟩

end PiTensorProduct
