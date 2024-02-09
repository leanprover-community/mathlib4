/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.RingTheory.GradedAlgebra.Noetherian

/-!
# Hilbert Serre Theorem

-/

variable {A M : Type*}
variable [CommRing A] [AddCommGroup M] [Module A M]
variable [finite_module : Module.Finite A M] [noetherian_ring : IsNoetherianRing A]
variable (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
variable (ℳ : ℕ → AddSubgroup M) [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ]

open GradedRing.finite_algebra_over_degree_zero_subring
open GradedModule.finite_module_over_degree_zero_subring
open BigOperators

namespace HilbertSerre

section base_case

lemma eventually_eq_zero_of_empty_generatorSet
    (card_generator : (GradedRing.HomogeneousGeneratingSetOf.irrelevant 𝒜).toFinset.card = 0) :
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ (x : ℳ n), x = 0 := by
  classical
  rw [Finset.card_eq_zero] at card_generator

  let T := GradedModule.HomogeneousGeneratingSetOf.top A ℳ
  let deg : T.toFinset → ℕ := fun x ↦ T.deg x.2
  by_cases ne_empty : T.toFinset = ∅
  · refine ⟨1, fun n _ x ↦ ?_⟩
    have eq1 := kth_degree_eq_span 𝒜 ℳ n
    simp_rw [card_generator, Finset.subset_empty, Finsupp.support_eq_empty] at eq1
    replace eq1 := calc ⊤
      _ = _ := eq1
      _ = Submodule.span (𝒜 0) ∅ := by
          congr
          rw [Set.eq_empty_iff_forall_not_mem]
          rintro x ⟨ω, (hω : ω ∈ T.toFinset), -⟩
          rw [ne_empty] at hω
          simp only [Finset.not_mem_empty] at hω
      _ = ⊥ := by rw [Submodule.span_empty]
    rw [← Submodule.mem_bot (R := 𝒜 0), ← eq1]
    trivial

  let maxDeg : ℕ := Finset.image deg Finset.univ |>.max' (by
    simp only [Finset.univ_eq_attach, Finset.image_nonempty, Finset.attach_nonempty_iff]
    rw [Finset.nonempty_iff_ne_empty]
    exact ne_empty)

  refine ⟨maxDeg, fun n hn x ↦ ?_⟩
  have hn' (m : M) (hm : m ∈ T.toFinset) : T.deg hm < n
  · exact lt_of_le_of_lt (Finset.le_max' _ _ <| by aesop) hn

  have eq0 := kth_degree_eq_span 𝒜 ℳ n
  simp_rw [card_generator, Finset.subset_empty, Finsupp.support_eq_empty] at eq0
  replace eq0 := calc _
    _ = _ := eq0
    _ = Submodule.span (𝒜 0) {x : ℳ n | ∃ ω : M, ∃ (_ : ω ∈ T.toFinset), x = ω } := by
        congr
        ext x
        rw [Set.mem_setOf_eq, Set.mem_setOf_eq]
        refine exists_congr fun m ↦ exists_congr fun _ ↦ ⟨?_, ?_⟩
        · rintro ⟨_, rfl, -, h⟩; rwa [evalMonomial_zero, one_smul] at h
        · intro h
          refine ⟨_, rfl, ?_, h ▸ ?_⟩
          · erw [degreeMonomial_zero]; norm_num
          · rw [evalMonomial_zero, one_smul]
    _ = Submodule.span (𝒜 0) {x : ℳ n | (x : M) ∈ T.toFinset } := by
        congr
        ext x
        simp only [exists_prop, exists_eq_right', Set.mem_setOf_eq]
  have mem1 : x ∈ (⊤ : Submodule (𝒜 0) (ℳ n)) := ⟨⟩
  rw [eq0, mem_span_set] at mem1
  obtain ⟨f, support_le, (eq1 : ∑ i in f.support, f i • i = x)⟩ := mem1
  rw [Subtype.ext_iff, AddSubgroup.val_finset_sum] at eq1
  ext1
  rw [show (x : M) = GradedModule.proj ℳ n x from
    DirectSum.decompose_of_mem_same (hx := x.2) |>.symm, ← eq1, map_sum, AddSubgroup.coe_zero]
  refine Finset.sum_eq_zero fun x hx ↦ show GradedModule.proj ℳ n ((f x : A) • (x : M)) = 0 from ?_

  rw [GradedModule.proj_smul_mem_right 𝒜 ℳ (f x : A) (x : M) (T.mem_deg (support_le hx)),
    if_pos (le_of_lt <| hn' x (support_le hx)), GradedRing.proj_apply,
    DirectSum.decompose_of_mem_ne (hx := (f x).2), zero_smul]

  intro r
  rw [eq_comm, Nat.sub_eq_zero_iff_le] at r
  exact not_le_of_lt (hn' x (support_le hx)) r

lemma eventually_subsingleton_of_empty_generatorSet
    (card_generator : (GradedRing.HomogeneousGeneratingSetOf.irrelevant 𝒜).toFinset.card = 0) :
    ∃ N : ℕ, ∀ n : ℕ, N < n → Subsingleton (ℳ n) := by
  obtain ⟨N, h⟩ := eventually_eq_zero_of_empty_generatorSet 𝒜 ℳ card_generator
  exact ⟨N, fun n hn ↦ ⟨fun x y ↦ (h n hn x).trans (h n hn y).symm⟩⟩

end base_case

end HilbertSerre
