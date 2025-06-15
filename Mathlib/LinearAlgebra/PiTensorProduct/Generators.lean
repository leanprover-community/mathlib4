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
a family of generators of the module `M i`, then the tensor products
of these elements generate `⨂[R] i, M i`.

In `LinearAlgebra.PiTensorProduct.Finite`, we deduce that if the modules `M i`
are finitely generated, then so is `⨂[R] i, M i`.

-/

namespace Set

/-- The bijection `Unit ⊕ (({i₀})ᶜ : Set ι) ≃ ι` for any `i₀ : ι` -/
noncomputable def sumSingletonComplEquiv {ι : Type*} (i₀ : ι) :
    Unit ⊕ (({i₀})ᶜ : Set ι) ≃ ι :=
  .ofBijective
    (fun x ↦ match x with
      | .inl _ => i₀
      | .inr ⟨i, _⟩ => i) (by
  constructor
  · rintro (_ | _) (_ | _) <;> aesop
  · intro i
    by_cases h : i = i₀
    · exact ⟨.inl Unit.unit, h.symm⟩
    · exact ⟨.inr ⟨i, by simpa using h⟩, rfl⟩)

@[simp]
lemma sumSingletonComplEquiv_inl {ι : Type*} (i₀ : ι) (u : Unit):
    sumSingletonComplEquiv i₀ (.inl u) = i₀ := rfl

@[simp]
lemma sumSingletonComplEquiv_inr {ι : Type*} (i₀ : ι) (i : ({i₀}ᶜ : Set ι)) :
    sumSingletonComplEquiv i₀ (.inr i) = i := rfl

end Set

-- to be moved
namespace Function

variable {ι : Type*} [DecidableEq ι] {M : ι → Type*} (i₀ : ι)
  (f : ∀ (i : ((Set.singleton i₀)ᶜ : Set ι)), M i) (x : M i₀)

/-- Given `i₀ : ι` and `x : M i₀`, this is (dependent) map `(i : ι) → M i`
whose value at `i₀` is `x` and which extends a given map on the complement of `{i₀}`. -/
def extendComplSingleton (i : ι) : M i :=
  if h : i = i₀ then by rw [h]; exact x else f ⟨i, h⟩

@[simp]
lemma extendComplSingleton_self : extendComplSingleton i₀ f x i₀ = x := dif_pos rfl

lemma extendComplSingleton_of_neq (i : ι) (h : i ≠ i₀) :
    extendComplSingleton i₀ f x i = f ⟨i, h⟩ := dif_neg h

@[simp]
lemma extendCompSingleton_restriction (φ : ∀ i, M i) (i₀ : ι) :
    extendComplSingleton i₀ (fun i ↦ φ i) (φ i₀) = φ := by
  ext i
  by_cases h : i = i₀
  · subst h
    simp
  · rw [extendComplSingleton_of_neq _ _ _ _ h]

end Function

open TensorProduct

namespace PiTensorProduct

variable (R : Type*) [CommRing R]

section equivTensorPiTensorComplSingleto

variable {ι : Type*} (M : ι → Type*)
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- The linear equivalence between `⨂[R] i, M i` and the tensor product of `M i₀`
(for some `i₀ : ι`) and the pi tensor product indexed by the complement of `{i₀}`. -/
noncomputable def equivTensorPiTensorComplSingleton (i₀ : ι) :
    (⨂[R] i, M i) ≃ₗ[R] (M i₀ ⊗[R] ⨂[R] (i : ((Set.singleton i₀)ᶜ : Set ι)), M i) :=
  ((reindex R (s := M) (e := (Set.sumSingletonComplEquiv i₀).symm)).trans
    (tmulEquivDep R
        (fun i => M (Set.sumSingletonComplEquiv i₀ i))).symm).trans
      (LinearEquiv.rTensor _ (subsingletonEquiv (R := R) (M := M i₀) Unit.unit))

variable (i₀ : ι)

@[simp]
lemma equivTensorPiTensorComplSingleton_tprod (i₀ : ι) (m : ∀ i, M i) :
    equivTensorPiTensorComplSingleton R M i₀ (⨂ₜ[R] i, m i) =
      m i₀ ⊗ₜ (⨂ₜ[R] (j : ((Set.singleton i₀)ᶜ : Set ι)), m j) := by
  dsimp [equivTensorPiTensorComplSingleton]
  erw [reindex_tprod (R := R) (s := M), tmulEquivDep_symm_apply]
  erw [LinearEquiv.rTensor_tmul]
  simp only [Set.sumSingletonComplEquiv_inl, Equiv.symm_symm, subsingletonEquiv_apply_tprod,
    Set.sumSingletonComplEquiv_inr]
  rfl

@[simp]
lemma equivTensorPiTensorComplSingleton_symm_tmul [DecidableEq ι] (i₀ : ι)
    (x : M i₀) (m : ∀ (i : ((Set.singleton i₀)ᶜ : Set ι)), M i) :
    (equivTensorPiTensorComplSingleton R M i₀).symm
      (x ⊗ₜ (⨂ₜ[R] (j : ((Set.singleton i₀)ᶜ : Set ι)), m j)) =
      (⨂ₜ[R] i, Function.extendComplSingleton i₀ m x i) := by
  apply (equivTensorPiTensorComplSingleton R M i₀).injective
  simp only [LinearEquiv.apply_symm_apply, equivTensorPiTensorComplSingleton_tprod,
    Function.extendComplSingleton_self]
  congr
  ext ⟨i, hi⟩
  rw [Function.extendComplSingleton_of_neq]

end equivTensorPiTensorComplSingleto

variable {R} {ι : Type*} [Finite ι]
  {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  {N : Type*} [AddCommGroup N] [Module R N]
  {γ : ι → Type*} {g : ⦃i : ι⦄ → (j : γ i) → M i}

lemma ext_of_span_eq_top
    (hg : ∀ i, Submodule.span R (Set.range (@g i)) = ⊤)
    {φ φ' : (⨂[R] i, M i) →ₗ[R] N}
    (h : ∀ (j : (i : ι) → γ i),
      φ (tprod _ (fun i ↦ g (j i))) = φ' (tprod _ (fun i ↦ g (j i)))) :
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
      classical
      simp only [lift.equiv_symm_apply]
      convert h (Function.extendComplSingleton i₀ j g₀) using 1
      all_goals
        simp only [equivTensorPiTensorComplSingleton_tprod,
          Function.extendComplSingleton_self]
        congr
        ext x
        congr
        rw [Function.extendComplSingleton_of_neq]
    · exact Nat.card_singleton_compl i₀ hι

lemma _root_.MultilinearMap.ext_of_span_eq_top
    (hg : ∀ i, Submodule.span R (Set.range (@g i)) = ⊤)
    {φ φ' : MultilinearMap R M N}
    (h : ∀ (j : (i : ι) → γ i), φ (fun i ↦ g (j i)) = φ' (fun i ↦ g (j i))) :
    φ = φ' := by
  suffices lift φ = lift φ' by
    ext m
    simpa using DFunLike.congr_fun this (tprod _ m)
  exact PiTensorProduct.ext_of_span_eq_top hg  (fun j ↦ by simpa using h j)

lemma submodule_span_eq_top
    (hg : ∀ i, Submodule.span R (Set.range (@g i)) = ⊤) :
    Submodule.span R (Set.range (fun j : ((i : ι) → γ i) ↦
      ⨂ₜ[R] (i : ι), g (j i))) = ⊤ := by
  rw [← (Submodule.span R _).ker_mkQ, LinearMap.ker_eq_top]
  refine ext_of_span_eq_top hg (fun j ↦ ?_)
  simp only [Submodule.mkQ_apply, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span ⟨j, rfl⟩

end PiTensorProduct
