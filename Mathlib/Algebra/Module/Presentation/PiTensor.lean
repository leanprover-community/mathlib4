/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Module.Presentation.Basic
import Mathlib.LinearAlgebra.PiTensorProduct

/-!
# Presentation of the tensor product of a (finite) family of modules

-/

universe w v u

open TensorProduct

namespace Function

variable {ι : Type*} [DecidableEq ι] {M : ι → Type*} (i₀ : ι)
  (f : ∀ (i : (Set.singleton i₀).compl), M i) (x : M i₀)

def extendComplSingleton (i : ι) : M i :=
  if h : i = i₀ then by rw [h]; exact x else f ⟨i, h⟩

@[simp]
lemma extendComplSingleton_self : extendComplSingleton i₀ f x i₀ = x := dif_pos rfl

lemma extendComplSingleton_of_neq (i : ι) (h : i ≠ i₀) :
    extendComplSingleton i₀ f x i = f ⟨i, h⟩ := dif_neg h

end Function

section

namespace PiTensorProduct

variable (R : Type u) [CommRing R]
  {ι : Type w} [DecidableEq ι] (M : ι → Type v)
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

def equivTensorPiTensorComplSingleton (i : ι) :
    (⨂[R] i, M i) ≃ₗ[R] (M i ⊗[R] ⨂[R] (i : (Set.singleton i).compl), M i) := sorry

@[simp]
lemma equivTensorPiTensorComplSingleton_tprod (i₀ : ι) (m : ∀ i, M i) :
    equivTensorPiTensorComplSingleton R M i₀ (⨂ₜ[R] i, m i) =
      m i₀ ⊗ₜ (⨂ₜ[R] (j : (Set.singleton i₀).compl), m j) := sorry

@[simp]
lemma equivTensorPiTensorComplSingleton_symm_tprod (i₀ : ι)
    (x : M i₀) (m : ∀ (i : (Set.singleton i₀).compl), M i) :
    (equivTensorPiTensorComplSingleton R M i₀).symm
      (x ⊗ₜ (⨂ₜ[R] (j : (Set.singleton i₀).compl), m j)) =
      (⨂ₜ[R] i, Function.extendComplSingleton i₀ m x i) := by
  apply (equivTensorPiTensorComplSingleton R M i₀).injective
  simp only [LinearEquiv.apply_symm_apply, equivTensorPiTensorComplSingleton_tprod,
    Function.extendComplSingleton_self]
  congr
  ext ⟨i, hi⟩
  rw [Function.extendComplSingleton_of_neq]

end PiTensorProduct

end

section

variable {ι : Type*} (G : ι → Type*) [DecidableEq ι]
  (i : ι) (y : (∀ (j : (Set.singleton i).compl), G j))

-- find a better name
def embedding : G i ↪ ∀ (j : ι), G j where
  toFun x j := if h : j = i then by rw [h]; exact x else y ⟨j, h⟩
  inj' x₁ x₂ h := by simpa using congr_fun h i

@[simp]
lemma embedding_apply_self (x : G i) : embedding G i y x i = x := dif_pos rfl

lemma embedding_apply_of_neq (x : G i) (j : ι) (h : j ≠ i) :
    embedding G i y x j = y ⟨j, h⟩ :=
  dif_neg h

end

open PiTensorProduct
namespace Module

variable {R : Type u} [CommRing R] {ι : Type w} {M : ι → Type v} [DecidableEq ι]
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

namespace Relations

variable (relations : ι → Relations R)

@[simps]
noncomputable def piTensor : Relations R where
  G := ∀ i, (relations i).G
  R := Sigma (fun (i₀ : ι) ↦ (relations i₀).R × (∀ (j : (Set.singleton i₀).compl), (relations j).G))
  relation := fun ⟨i₀, ⟨r, g⟩⟩ ↦
    Finsupp.embDomain (embedding (fun i ↦ (relations i).G) i₀ g) ((relations i₀).relation r)

namespace Solution

variable {relations} (solution : ∀ (i : ι), (relations i).Solution (M i))

@[simps]
noncomputable def piTensor : (Relations.piTensor relations).Solution (⨂[R] i, M i) where
  var g := ⨂ₜ[R] i, (solution i).var (g i)
  linearCombination_var_relation := by
    rintro ⟨i₀, r, g⟩
    dsimp
    let S := ⨂[R] (i : (Set.singleton i₀).compl), M i
    rw [Finsupp.linearCombination_embDomain]
    let φ : M i₀ →ₗ[R] ⨂[R] i, M i :=
      (equivTensorPiTensorComplSingleton R M i₀).symm.toLinearMap.comp
        ((TensorProduct.mk (R := R) (M := M i₀) (N := S)).flip (⨂ₜ[R] i, (solution i).var (g i)))
    convert (((solution i₀).postcomp φ).linearCombination_var_relation r)
    ext g
    dsimp [φ]
    rw [equivTensorPiTensorComplSingleton_symm_tprod]
    congr
    ext i
    by_cases hi : i = i₀
    · subst hi
      simp
    · rw [embedding_apply_of_neq, Function.extendComplSingleton_of_neq _ _ _ _ hi]

namespace IsPresentation

variable {solution} (h : ∀ i, (solution i).IsPresentation)

namespace piTensor

lemma isPresentation_of_isEmpty [hι : IsEmpty ι] :
    (Solution.piTensor solution).IsPresentation :=
  IsPresentationCore.isPresentation
    { desc := fun {N _ _} s ↦ PiTensorProduct.lift
        { toFun := fun _ ↦ s.var (IsEmpty.elim hι)
          map_add' := fun _ ↦ IsEmpty.elim hι
          map_smul' := fun _ ↦ IsEmpty.elim hι }
      postcomp_desc := fun s ↦ by
        ext x
        dsimp
        simp only [lift.tprod, MultilinearMap.coe_mk]
        congr
        funext i
        exact IsEmpty.elim hι i
      postcomp_injective := fun {N _ _ f f'} h ↦ by
        ext x
        have := Solution.congr_var h (IsEmpty.elim hι)
        simp only [postcomp_var, piTensor_var] at this
        simp only [LinearMap.compMultilinearMap_apply]
        convert this }

variable (i₀ : ι)
  (h₀ : (Solution.piTensor (fun (i : (Set.singleton i₀).compl) ↦ solution i)).IsPresentation)

include h h₀ in
lemma isPresentation_induction_step :
    (Solution.piTensor solution).IsPresentation :=
  have := h₀
  have := h
  sorry

end piTensor

include h in
lemma piTensor [Finite ι] : (Solution.piTensor solution).IsPresentation := by
  obtain ⟨n, hn⟩ : ∃ (n : ℕ), Nat.card ι = n := ⟨_, rfl⟩
  revert ι
  induction n with
  | zero =>
      intro ι M _ _ _ relations solution h _ h₀
      have : IsEmpty ι := by
        rw [Nat.card_eq_zero] at h₀
        have := not_finite_iff_infinite (α := ι)
        tauto
      apply piTensor.isPresentation_of_isEmpty
  | succ n hn =>
      intro ι M _ _ _ relations solution h _ hn'
      let i₀ := ((Nat.card_ne_zero (α := ι)).1 (by omega)).1.some
      refine piTensor.isPresentation_induction_step h i₀ (hn (fun _ ↦ h _) ?_)
      sorry

end IsPresentation

end Solution

end Relations

noncomputable def Presentation.piTensor [Finite ι] (pres : ∀ i, Presentation R (M i)) :
    Presentation R (⨂[R] i, M i) where
  toSolution := .piTensor (fun i ↦ (pres i).toSolution)
  toIsPresentation := .piTensor (fun i ↦ (pres i).toIsPresentation)

end Module
