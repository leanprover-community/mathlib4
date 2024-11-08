/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Generators

/-!
# Generators of exterior powers

If `g : ι → M` is a family of generators of a `R`-module, then we obtain that
the exterior products `ιMulti R _ (g ∘ x)` for `x : Fin n → ι` generate.
This result also hold if we consider only families `x : Fin n → ι` which correspond
to injective maps, and in case `ι` has a linear order, we may also consider
only order embeddings `x : Fin n → ι`.

-/

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] (n : ℕ)

open TensorProduct

namespace exteriorPower

/-- The canonical linear map `⨂[R]^n M →ₗ[R] ⋀[R]^n M`. -/
noncomputable def fromTensorPower : ⨂[R]^n M →ₗ[R] ⋀[R]^n M :=
  PiTensorProduct.lift (ιMulti _ _).toMultilinearMap

variable {M n} in
@[simp]
lemma fromTensorPower_tprod (x : Fin n → M) :
    fromTensorPower R M n (PiTensorProduct.tprod _ x) = ιMulti _ _ x := by
  simp [fromTensorPower]

lemma fromTensorPower_surjective : Function.Surjective (fromTensorPower R M n) := by
  rw [← LinearMap.range_eq_top, ← top_le_iff, ← ιMulti_span, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  exact ⟨PiTensorProduct.tprod _ x, by simp⟩

variable {R M} {ι : Type*} {g : ι → M}

lemma span_ιMulti_of_span_eq_top (hg : Submodule.span R (Set.range g) = ⊤) (n : ℕ) :
    Submodule.span R (Set.range (fun (x : Fin n → ι) ↦ ιMulti R _ (g ∘ x))) = ⊤ := by
  rw [← top_le_iff, ← LinearMap.range_eq_top.2 (fromTensorPower_surjective R M n),
    LinearMap.range_eq_map, ← PiTensorProduct.submodule_span_eq_top (R := R)
      (M := (fun (_ : Fin n) ↦ M)) (g := fun (_ : Fin n) ↦ g) (fun _ ↦ hg),
    Submodule.map_le_iff_le_comap, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  dsimp
  simp only [Set.mem_preimage, fromTensorPower_tprod, SetLike.mem_coe]
  exact Submodule.subset_span ⟨_, rfl⟩

instance finite [Module.Finite R M] : Module.Finite R (⋀[R]^n M) := by
  obtain ⟨k, g, hg⟩ := Module.Finite.exists_fin (R := R) (M := M)
  rw [Module.finite_def, ← span_ιMulti_of_span_eq_top hg n]
  exact Submodule.fg_span (Set.finite_range _)

lemma span_ιMulti_embedding_of_span_eq_top (hg : Submodule.span R (Set.range g) = ⊤) (n : ℕ) :
    Submodule.span R (Set.range (fun (x : Fin n ↪ ι) ↦ ιMulti R _ (g ∘ x))) = ⊤ := by
  rw [← top_le_iff, ← span_ιMulti_of_span_eq_top hg, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  dsimp
  by_cases hx : Function.Injective x
  · exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
  · suffices ιMulti R n (g ∘ x) = 0 by simp [this]
    simp only [Function.Injective, not_forall, Classical.not_imp] at hx
    obtain ⟨i, j, hx, hij⟩ := hx
    exact AlternatingMap.map_eq_zero_of_eq  _ _ (hij := hij) (by simp [hx])

-- to be moved
lemma _root_.Equiv.Perm.exists_orderEmbedding_of_finite
    {α β : Type*} [LinearOrder α] [LinearOrder β] [Finite α]
    (x : α ↪ β) : ∃ (σ : Equiv.Perm α) (f : α ↪o β), x ∘ σ = f := by
  have := Fintype.ofFinite α
  have e : (⊤ : Finset α) ≃o Finset.map x ⊤ :=
    ((⊤ : Finset α).orderIsoOfFin rfl).symm.trans ((Finset.map x ⊤).orderIsoOfFin (by simp))
  let f : α ↪o β :=
    { toFun := fun a ↦ (e ⟨a, by simp⟩).1
      inj' := fun a₁ a₂ h ↦ by
        simpa only [← Subtype.ext_iff, EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq] using h
      map_rel_iff' := by simp }
  have he (i : α) : ∃ (j : α), x j = e ⟨i, by simp⟩ := by
    simpa only [Finset.mem_map, Finset.top_eq_univ, Finset.mem_univ, true_and]
      using (e ⟨i, by simp⟩).2
  let g : α → α := fun i ↦ (he i).choose
  have hg (i : α) : x (g i) = e ⟨i, by simp⟩ := (he i).choose_spec
  have fac : x ∘ g = f := by ext; simp [f, hg]
  refine ⟨Equiv.ofBijective g ⟨?_, fun a ↦ ?_⟩, f, fac⟩
  · apply Function.Injective.of_comp (f := x)
    simpa only [fac] using RelEmbedding.injective f
  · refine ⟨(e.symm ⟨x a, by simp⟩).1, x.injective ?_⟩
    refine (congr_fun fac (e.symm ⟨x a, by simp⟩).1).trans ?_
    simpa only [f, Subtype.coe_eta, Finset.top_eq_univ, Subtype.ext_iff] using
      e.apply_symm_apply ⟨x a, by simp⟩

lemma span_ιMulti_orderEmbedding_of_span_eq_top [LinearOrder ι]
    (hg : Submodule.span R (Set.range g) = ⊤) (n : ℕ) :
    Submodule.span R (Set.range (fun (x : Fin n ↪o ι) ↦ ιMulti R _ (g ∘ x))) = ⊤ := by
  rw [← top_le_iff, ← span_ιMulti_embedding_of_span_eq_top hg, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  obtain ⟨σ, f, hf⟩ := Equiv.Perm.exists_orderEmbedding_of_finite x
  dsimp
  rw [(ιMulti R n).map_congr_perm (g ∘ x) σ, ← one_smul (M := R) (b := (ιMulti R n _)),
    ← smul_assoc]
  exact Submodule.smul_mem _ _ (Submodule.subset_span
    ⟨f, by simp only [Function.comp_assoc, hf]⟩)

end exteriorPower
