import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.SeparationQuotient.FiniteDimensional
import Mathlib.Data.Real.Irrational

open Function Set Metric Module Filter
open scoped Topology Finset

namespace Submodule

variable {K M : Type*} [DivisionRing K] [AddCommGroup M] [Module K M] {s : Set M} {x : M}
  [Module.Finite K (span K s)]

variable (K s) in
theorem exists_finset_span_eq_linearIndepOn :
    ∃ t : Finset M, ↑t ⊆ s ∧ t.card = finrank K (span K s) ∧
      span K t = span K s ∧ LinearIndepOn K id (t : Set M) := by
  rcases exists_linearIndependent K s with ⟨t, ht_sub, ht_span, ht_indep⟩
  obtain ⟨t, rfl, ht_card⟩ : ∃ u : Finset M, ↑u = t ∧ u.card = finrank K (span K s) := by
    rw [← Cardinal.mk_set_eq_nat_iff_finset, finrank_eq_rank, ← ht_span, rank_span_set ht_indep]
  exact ⟨t, ht_sub, ht_card, ht_span, ht_indep⟩

variable (K s) in
theorem exists_fun_fin_finrank_span_eq :
    ∃ f : Fin (finrank K (span K s)) → M, (∀ i, f i ∈ s) ∧ span K (range f) = span K s ∧
      LinearIndependent K f := by
  rcases exists_finset_span_eq_linearIndepOn K s with ⟨t, hts, ht_card, ht_span, ht_indep⟩
  set e := (Finset.equivFinOfCardEq ht_card).symm
  exact ⟨(↑) ∘ e, fun i ↦ hts (e i).2, by simpa, ht_indep.comp _ e.injective⟩

theorem mem_span_set_iff_exists_finsupp_le_finrank :
    x ∈ span K s ↔ ∃ c : M →₀ K, c.support.card ≤ finrank K (span K s) ∧
      ↑c.support ⊆ s ∧ c.sum (fun mi r ↦ r • mi) = x := by
  constructor
  · intro h
    rcases exists_finset_span_eq_linearIndepOn K s with ⟨t, ht_sub, ht_card, ht_span, ht_indep⟩
    rcases mem_span_set.mp (ht_span ▸ h) with ⟨c, hct, hx⟩
    refine ⟨c, ?_, hct.trans ht_sub, hx⟩
    exact ht_card ▸ Finset.card_mono hct
  · rintro ⟨c, -, hcs, hx⟩
    exact mem_span_set.mpr ⟨c, hcs, hx⟩

-- TODO:
-- theorem mem_span_set_iff_exists_fun_fin_finrank :
--     x ∈ span K s ↔ ∃ f : Fin (finrank K (span K s)) → K, ∃ g : Fin (finrank K (span K s)) → M,
--       (∀ i, g i ∈ s) ∧ ∑ i, f i • g i = x := by
    
end Submodule

namespace AddSubgroup

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]


private theorem mem_closure_of_forall_nhds_zero_mem_span_inter_aux {n : ℕ}
    (s : AddSubgroup (Fin n → ℝ)) {x : Fin n → ℝ}
    (H : ∀ U ∈ 𝓝 0, x ∈ Submodule.span ℝ (s ∩ U)) : x ∈ _root_.closure (s : Set (Fin n → ℝ)) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  rcases exists_pos_mul_lt hε n with ⟨δ, hδ₀, hδε⟩
  set U : Set (Fin n → ℝ) := ball 0 δ
  specialize H U (ball_mem_nhds _ (by positivity))
  rcases Submodule.mem_span_set_iff_exists_finsupp_le_finrank.mp H with ⟨c, hc_le, hc, rfl⟩
  refine ⟨c.sum fun mi r ↦ ⌊r⌋ • mi, ?_, ?_⟩
  · exact sum_mem fun x hx ↦ zsmul_mem (hc hx).1 _
  · calc
      _ ≤ ∑ _ ∈ c.support, δ := by
        refine dist_sum_sum_le_of_le _ fun v hv ↦ ?_
        simp only [dist_eq_norm, ← Int.cast_smul_eq_zsmul ℝ, ← sub_smul, norm_smul]
        rw [← one_mul δ]
        gcongr
        · simp [abs_of_nonneg (Int.fract_nonneg (c v)), (Int.fract_lt_one _).le]
        · apply le_of_lt
          simpa [U] using (hc hv).2
      _ ≤ n * δ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        gcongr
        exact hc_le.trans <| by simpa using (Submodule.span ℝ (s ∩ U)).finrank_le
      _ < ε := hδε

theorem mem_closure_of_forall_nhds_zero_mem_span_inter (s : AddSubgroup E) {x : E}
    (H : ∀ U ∈ 𝓝 (0 : E), x ∈ Submodule.span ℝ (s ∩ U)) : x ∈ _root_.closure (s : Set E) := by
  rcases exists_continuousLinearMap_fun_isInducing_isOpenQuotientMap ℝ E with ⟨n, f, hfi, hfoq⟩
  suffices f x ∈ _root_.closure (s.map f.toAddMonoidHom : Set (Fin n → ℝ)) by
    rwa [hfi.closure_eq_preimage_closure_image]
  apply mem_closure_of_forall_nhds_zero_mem_span_inter_aux
  intro U hU
  simp only [coe_map, LinearMap.toAddMonoidHom_coe, ContinuousLinearMap.coe_coe,
    ← image_inter_preimage, Submodule.span_image]
  exact Submodule.mem_map_of_mem <| H _ <| f.continuous.tendsto _ <| by rwa [map_zero]

theorem exists_linearMap_forall_int_of_not_accPt_zero (s : AddSubgroup E)
    (hs : ¬AccPt (0 : E) (𝓟 s)) : ∃ f : E →ₗ[ℝ] ℝ, f ≠ 0 ∧ ∀ a ∈ s, ∃ m : ℤ, f a = m := by
  
  sorry

theorem mem_closure_of_forall_linearMap_exists_irrational (s : AddSubgroup E) {x : E}
    (H : ∀ f : E →ₗ[ℝ] ℝ, f x ≠ 0 → ∃ a ∈ s, Irrational (f a)) :
    x ∈ _root_.closure (s : Set E) := by
  wlog hE : T2Space E
  · rw [SeparationQuotient.isInducing_mk.closure_eq_preimage_closure_image, mem_preimage]
    refine this (s.map (SeparationQuotient.mkCLM ℝ E).toAddMonoidHom) (fun f hf ↦ ?_) inferInstance
    rcases H (f ∘ₗ SeparationQuotient.mkCLM ℝ E) hf with ⟨a, has, hfa⟩
    exact ⟨_, mem_map_of_mem _ has, hfa⟩
  apply mem_closure_of_forall_nhds_zero_mem_span_inter
  intro U hU
  contrapose! H
  obtain ⟨f, hfx, hfsU⟩ : ∃ f : E →ₗ[ℝ] ℝ, f x ≠ 0 ∧ ∀ y ∈ s, y ∈ U → f y = 0 :=
    (Submodule.exists_le_ker_of_not_mem H).imp fun f ↦ And.imp_right fun h y hys hyU ↦
      h <| Submodule.subset_span ⟨hys, hyU⟩
  clear H
  have hfo : IsOpenMap f :=
    f.isOpenMap_of_finiteDimensional (f.surjective_of_ne_zero <| ne_of_apply_ne (· x) hfx)
  have := hfo.image_mem_nhds hU

end AddSubgroup
