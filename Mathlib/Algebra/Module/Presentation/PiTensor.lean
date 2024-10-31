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

section

variable (R : Type u) [CommRing R]
  {ι₁ ι₂: Type w} (M : ι₁ ⊕ ι₂ → Type v) [DecidableEq ι₁] [DecidableEq ι₂]
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

namespace PiTensorProduct

namespace sumLinearEquiv

noncomputable def hom : ((⨂[R] i₁, M (.inl i₁)) ⊗[R] ⨂[R] i₂, M (.inr i₂)) →ₗ[R] ⨂[R] i, M i :=
  TensorProduct.lift
    { toFun := fun x₁ ↦ PiTensorProduct.lift (by
        sorry)
      map_add' := sorry
      map_smul' := sorry }

noncomputable def inv : (⨂[R] i, M i) →ₗ[R] ((⨂[R] i₁, M (.inl i₁)) ⊗[R] ⨂[R] i₂, M (.inr i₂)) :=
  PiTensorProduct.lift (by
    sorry)

end sumLinearEquiv

open sumLinearEquiv in
noncomputable def sumLinearEquiv :
    ((⨂[R] i₁, M (.inl i₁)) ⊗[R] ⨂[R] i₂, M (.inr i₂)) ≃ₗ[R] ⨂[R] i, M i :=
  LinearEquiv.ofLinear (hom R M) (inv R M) sorry sorry

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

namespace Module

variable {R : Type u} [CommRing R] {ι : Type w} {M : ι → Type v} [DecidableEq ι]
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

namespace Relations

variable (relations : ι → Relations R)

@[simps]
noncomputable def piTensor : Relations R where
  G := ∀ i, (relations i).G
  R := Sigma (fun (i : ι) ↦ (relations i).R × (∀ (j : (Set.singleton i).compl), (relations j).G))
  relation := fun ⟨i, ⟨r, g⟩⟩ ↦
    Finsupp.embDomain (embedding (fun i ↦ (relations i).G) i g) ((relations i).relation r)

namespace Solution

variable {relations} (solution : ∀ (i : ι), (relations i).Solution (M i))

noncomputable def piTensor : (Relations.piTensor relations).Solution (⨂[R] i, M i) where
  var g := ⨂ₜ[R] i, (solution i).var (g i)
  linearCombination_var_relation := by
    rintro ⟨i, r, g⟩
    dsimp
    rw [Finsupp.linearCombination_embDomain]
    have pif := (solution i).linearCombination_var_relation r
    sorry

end Solution

end Relations

end Module
