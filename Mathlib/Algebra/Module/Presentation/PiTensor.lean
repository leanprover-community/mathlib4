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

noncomputable def piTensor : Relations R where
  G := ∀ i, (relations i).G
  R := Sigma (fun (i : ι) ↦ (relations i).R × (∀ (j : (Set.singleton i).compl), (relations j).G))
  relation := fun ⟨i, ⟨r, g⟩⟩ ↦
    Finsupp.embDomain (embedding (fun i ↦ (relations i).G) i g) ((relations i).relation r)

end Relations

end Module
