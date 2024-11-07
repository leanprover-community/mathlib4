/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Module.Presentation.Tensor
import Mathlib.LinearAlgebra.PiTensorProduct

/-!
# Presentation of the tensor product of a (finite) family of modules

-/

universe w' w v u

open TensorProduct

namespace Function

variable {ι : Type*} [DecidableEq ι] {M : ι → Type*} (i₀ : ι)
  (f : ∀ (i : ((Set.singleton i₀)ᶜ : Set ι)), M i) (x : M i₀)

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
      m i₀ ⊗ₜ (⨂ₜ[R] (j : ((Set.singleton i₀)ᶜ : Set ι)), m j) := sorry

@[simp]
lemma equivTensorPiTensorComplSingleton_symm_tmul (i₀ : ι)
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

end PiTensorProduct

end

section

variable {ι : Type*} (G : ι → Type*) [DecidableEq ι]
  (i : ι) (y : (∀ (j : ((Set.singleton i)ᶜ : Set ι)), G j))

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
  R := Sigma (fun (i₀ : ι) ↦ (relations i₀).R ×
    (∀ (j : ((Set.singleton i₀)ᶜ : Set ι)), (relations j).G))
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
    let S := ⨂[R] (i : ((Set.singleton i₀)ᶜ : Set ι)), M i
    rw [Finsupp.linearCombination_embDomain]
    let φ : M i₀ →ₗ[R] ⨂[R] i, M i :=
      (equivTensorPiTensorComplSingleton R M i₀).symm.toLinearMap.comp
        ((TensorProduct.mk (R := R) (M := M i₀) (N := S)).flip (⨂ₜ[R] i, (solution i).var (g i)))
    convert (((solution i₀).postcomp φ).linearCombination_var_relation r)
    ext g
    dsimp [φ]
    erw [equivTensorPiTensorComplSingleton_symm_tmul]
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
    { desc := fun s ↦ PiTensorProduct.lift
        { toFun := fun _ ↦ s.var (IsEmpty.elim hι)
          map_update_add' := fun _ ↦ IsEmpty.elim hι
          map_update_smul' := fun _ ↦ IsEmpty.elim hι }
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
  (h₀ : (Solution.piTensor (fun (i : ((Set.singleton i₀)ᶜ : Set ι)) ↦ solution i)).IsPresentation)

namespace isPresentationCore_induction_step

variable {N : Type w'} [AddCommGroup N] [Module R N]
  (s : (Relations.piTensor relations).Solution N)

@[simps! G R]
noncomputable def presInd : Presentation R (⨂[R] (i : ι), M i) :=
  Presentation.ofLinearEquiv
    (Presentation.tensor (.ofIsPresentation (h i₀)) (.ofIsPresentation h₀))
    (equivTensorPiTensorComplSingleton R M i₀).symm

lemma presInd_var (g₀ : (relations i₀).G)
    (g : ∀ (i : ((Set.singleton i₀)ᶜ : Set ι)), (relations i).G) :
      (presInd h i₀ h₀).var ⟨g₀, g⟩ =
      ⨂ₜ[R] (i : ι), (solution i).var
        (Function.extendComplSingleton (M := fun i ↦ (relations i).G) i₀ g g₀ i) := by
  dsimp [presInd]
  erw [equivTensorPiTensorComplSingleton_symm_tmul]
  congr
  ext i
  by_cases hi : i = i₀
  · subst hi
    simp
  · simp only [Function.extendComplSingleton_of_neq _ _ _ _ hi]

lemma eq_presInd_var (g : ∀ i, (relations i).G):
    (⨂ₜ[R] (i : ι), (solution i).var (g i)) =
      (presInd h i₀ h₀).var ⟨g i₀, fun i ↦ g i⟩ := by
  rw [presInd_var, Function.extendCompSingleton_restriction]

end isPresentationCore_induction_step

open isPresentationCore_induction_step in
include h h₀ in
noncomputable def isPresentationCore_induction_step :
    Solution.IsPresentationCore.{w'} (Solution.piTensor solution) where
  desc {N _ _ } s := (presInd h i₀ h₀).desc
    { var := fun ⟨g₀, g⟩ ↦ s.var (Function.extendComplSingleton i₀ g g₀)
      linearCombination_var_relation := by
        rintro (⟨r₀, g⟩ | ⟨g₀, ⟨⟨i₁, h₁⟩, r₁, g⟩⟩)
        · simpa [presInd, Finsupp.linearCombination_embDomain]
            using s.linearCombination_var_relation ⟨i₀, r₀, g⟩
        · erw [Set.mem_compl_iff, Set.not_mem_singleton_iff] at h₁
          have := s.linearCombination_var_relation
            ⟨i₁, r₁, Function.extendComplSingleton
              (M := fun (i : ({i₁}ᶜ : Set ι)) ↦ (relations i).G) ⟨i₀, h₁.symm⟩
                (fun ⟨⟨i, hi₁⟩, hi₀⟩ ↦ g ⟨⟨i, by
                  rw [Set.mem_compl_iff] at hi₀ ⊢
                  erw [Set.not_mem_singleton_iff] at hi₀ ⊢
                  simpa only [ne_eq, Subtype.mk.injEq] using hi₀⟩, (by
                  rw [Set.mem_compl_iff]
                  erw [Set.not_mem_singleton_iff]
                  simpa only [ne_eq, Subtype.mk.injEq] using hi₁)⟩) g₀⟩
          dsimp at this
          rw [Finsupp.linearCombination_embDomain] at this
          dsimp [presInd]
          rw [Finsupp.linearCombination_embDomain, Finsupp.linearCombination_embDomain, ← this]
          congr
          ext g₁
          dsimp
          congr
          dsimp
          ext i
          by_cases hi₀ : i = i₀
          · subst hi₀
            rw [Function.extendComplSingleton_self,
              embedding_apply_of_neq _ _ _ _ _ h₁.symm,
              Function.extendComplSingleton_self]
          · by_cases hi₁ : i = i₁
            · subst hi₁
              rw [embedding_apply_self, Function.extendComplSingleton_of_neq _ _ _ _ h₁,
                embedding_apply_self]
            · rw [Function.extendComplSingleton_of_neq _ _ _ _ hi₀,
                embedding_apply_of_neq _ _ _ _ _ (by simpa using hi₁),
                embedding_apply_of_neq _ _ _ _ _ hi₁,
                Function.extendComplSingleton_of_neq _ _ _ _ (by simpa using hi₀)]
            }
  postcomp_desc s:= by
    ext g
    dsimp
    rw [eq_presInd_var h i₀ h₀, desc_var]
    dsimp
    rw [Function.extendCompSingleton_restriction]
  postcomp_injective h' := (presInd h i₀ h₀).postcomp_injective (by
    ext ⟨g₀, g⟩
    dsimp
    rw [presInd_var]
    exact Solution.congr_var h' (Function.extendComplSingleton i₀ g g₀))

include h h₀ in
lemma isPresentation_induction_step :
    (Solution.piTensor solution).IsPresentation :=
  (isPresentationCore_induction_step h i₀ h₀).isPresentation

end piTensor

include h in
lemma piTensor [Finite ι] : (Solution.piTensor solution).IsPresentation := by
  obtain ⟨n, hn⟩ : ∃ (n : ℕ), Nat.card ι = n := ⟨_, rfl⟩
  revert ι
  induction n with
  | zero =>
      intro ι M _ _ _ relations solution _ _ h₀
      have : IsEmpty ι := by
        rw [Nat.card_eq_zero] at h₀
        have := not_finite_iff_infinite (α := ι)
        tauto
      apply piTensor.isPresentation_of_isEmpty
  | succ n hn =>
      intro ι M _ _ _ relations solution h _ hn'
      let i₀ := ((Nat.card_ne_zero (α := ι)).1 (by omega)).1.some
      refine piTensor.isPresentation_induction_step h i₀ (hn (fun _ ↦ h _) ?_)
      have := Fintype.ofFinite ι
      rw [← add_left_inj 1, ← hn', Nat.card_eq_fintype_card (α := ι),
        ← Finset.card_compl_add_card {i₀}, Finset.card_singleton,
        Nat.card_eq_card_finite_toFinset (Set.toFinite _)]
      congr
      ext i
      simp only [Set.Finite.mem_toFinset, Set.mem_compl_iff, Finset.mem_compl,
        Finset.mem_singleton]
      rfl

end IsPresentation

end Solution

end Relations

@[simps! G R var]
noncomputable def Presentation.piTensor [Finite ι] (pres : ∀ i, Presentation R (M i)) :
    Presentation R (⨂[R] i, M i) where
  toSolution := .piTensor (fun i ↦ (pres i).toSolution)
  toIsPresentation := .piTensor (fun i ↦ (pres i).toIsPresentation)

end Module
