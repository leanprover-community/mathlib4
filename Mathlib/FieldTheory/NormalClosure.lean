/-
Copyright (c) 2023 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import Mathlib.FieldTheory.Normal

/-!
# Normal closures

In this file we define the normal closure of an `IntermediateField`.
If `K` is an intermediate field of `L/F` (in mathlib this means that `K` is both a subfield of `L`
and an `F`-subalgebra of `L`), then `K.normalClosure` is the smallest intermediate field of `L/F`
that contains the image of every `F`-algebra embedding `K →ₐ[F] L`. This is the same as the
absolute normal closure (`normal_closure` in the root namespace), but with the benefit of being a
function `IntermediateField F L → IntermediateField F L`. In particular, the normal closure
definined in this file will mesh nicely with the Galois correspondence.

## Main Definitions

- `IntermediateField.normalClosure K` for `K : IntermediateField F L`.
-/

open BigOperators Polynomial

variable {F L : Type _} [Field F] [Field L] [Algebra F L] (K : IntermediateField F L)

namespace IntermediateField

/-- The normal closure of `K` in `L`. -/
noncomputable def normalClosure : IntermediateField F L :=
  (_root_.normalClosure F K L).restrictScalars F

lemma normalClosure_def : K.normalClosure = ⨆ f : K →ₐ[F] L, f.fieldRange :=
  rfl

namespace normalClosure

instance normal [Normal F L] : Normal F K.normalClosure :=
  _root_.normalClosure.normal F K L

instance finiteDimensional [FiniteDimensional F K] :
    FiniteDimensional F K.normalClosure :=
  normalClosure.is_finiteDimensional F K L

end normalClosure

variable {K}

lemma normalClosure_le_iff {K' : IntermediateField F L} :
    K.normalClosure ≤ K' ↔ ∀ f : K →ₐ[F] L, f.fieldRange ≤ K' :=
  iSup_le_iff

lemma fieldRange_le_normalClosure (f : K →ₐ[F] L) : f.fieldRange ≤ K.normalClosure :=
  le_iSup AlgHom.fieldRange f

variable (K)

lemma le_normalClosure : K ≤ K.normalClosure :=
K.fieldRange_val.symm.trans_le (fieldRange_le_normalClosure K.val)

lemma normalClosure_of_normal [Normal F K] : K.normalClosure = K :=
by simp only [normalClosure_def, AlgHom.fieldRange_of_normal, iSup_const]

variable [Normal F L]

lemma normalClosure_normalClosure : K.normalClosure.normalClosure = K.normalClosure :=
K.normalClosure.normalClosure_of_normal

lemma normalClosure_def' : K.normalClosure = ⨆ f : L →ₐ[F] L, K.map f := by
  refine' K.normalClosure_def.trans (le_antisymm (iSup_le (fun f ↦ _)) (iSup_le (fun f ↦ _)))
  · exact le_iSup_of_le (f.liftNormal L) (fun b ⟨a, h⟩ ↦ ⟨a, a.2, h ▸ f.liftNormal_commutes L a⟩)
  · exact le_iSup_of_le (f.comp K.val) (fun b ⟨a, h⟩ ↦ ⟨⟨a, h.1⟩, h.2⟩)

lemma normalClosure_def'' : K.normalClosure = ⨆ f : L ≃ₐ[F] L, K.map f := by
  refine' K.normalClosure_def'.trans (le_antisymm (iSup_le (fun f ↦ _)) (iSup_le (fun f ↦ _)))
  · exact le_iSup_of_le (f.restrictNormal' L)
      (fun b ⟨a, h⟩ ↦ ⟨a, h.1, h.2 ▸ f.restrictNormal_commutes L a⟩)
  · exact le_iSup_of_le f le_rfl

variable {K}

lemma normal_iff_normalClosure_eq : Normal F K ↔ K.normalClosure = K :=
⟨@normalClosure_of_normal F L _ _ _ K, fun h ↦ h ▸ normalClosure.normal K⟩

lemma normal_iff_normalClosure_le : Normal F K ↔ K.normalClosure ≤ K :=
normal_iff_normalClosure_eq.trans K.le_normalClosure.le_iff_eq.symm

lemma normal_iff_forall_fieldRange_le : Normal F K ↔ ∀ σ : K →ₐ[F] L, σ.fieldRange ≤ K :=
by rw [normal_iff_normalClosure_le, normalClosure_def, iSup_le_iff]

lemma normal_iff_forall_map_le : Normal F K ↔ ∀ σ : L →ₐ[F] L, K.map σ ≤ K :=
by rw [normal_iff_normalClosure_le, normalClosure_def', iSup_le_iff]

lemma normal_iff_forall_map_le' : Normal F K ↔ ∀ σ : L ≃ₐ[F] L, K.map ↑σ ≤ K :=
by rw [normal_iff_normalClosure_le, normalClosure_def'', iSup_le_iff]

lemma normal_iff_forall_fieldRange_eq : Normal F K ↔ ∀ σ : K →ₐ[F] L, σ.fieldRange = K :=
⟨@AlgHom.fieldRange_of_normal F L _ _ _ K, normal_iff_forall_fieldRange_le.2 ∘ fun h σ ↦ (h σ).le⟩

lemma normal_iff_forall_map_eq : Normal F K ↔ ∀ σ : L →ₐ[F] L, K.map σ = K := by
  refine' ⟨fun h σ ↦ K.fieldRange_val ▸ _, fun h ↦ normal_iff_forall_map_le.2 (fun σ ↦ (h σ).le)⟩
  rw [AlgHom.map_fieldRange, normal_iff_forall_fieldRange_eq.1 h, fieldRange_val]

lemma normal_iff_forall_map_eq' : Normal F K ↔ ∀ σ : L ≃ₐ[F] L, K.map ↑σ = K :=
⟨fun h σ ↦ normal_iff_forall_map_eq.1 h σ, fun h ↦ normal_iff_forall_map_le'.2 (fun σ ↦ (h σ).le)⟩

end IntermediateField
