/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Topology.UniformSpace.Equicontinuity

/-!
# Ascoli Theorem

## Main definitions
## Main statements
## Notation
## Implementation details
## References
## Tags
-/

open Set Filter Uniformity Function UniformConvergence

section prelim

variable {α β : Type*}

-- lemma totally_bounded_pi {ι : Type*} {α : ι → Type*} [Π i, uniform_space (α i)]
--   {t : set ι} {s : Π i, set (α i)} (hs : ∀ i ∈ t, totally_bounded (s i)) :
--   totally_bounded (t.pi s) :=
-- sorry

--lemma Pi.continuous_restrict {ι : Type*} (α : ι → Type*) [Π i, topological_space (α i)]
--  (s : set ι) : continuous (s.restrict : (Π i : ι, α i) → Π i : s, α i) :=
--continuous_pi (λ i, continuous_apply i)
--
--lemma Pi.continuous_restrict_iff {ι α : Type*} (β : ι → Type*) [topological_space α]
--  [Π i, topological_space (β i)] (s : set ι) {f : α → Π i, β i} :
--  continuous ((s.restrict : (Π i : ι, β i) → Π i : s, β i) ∘ f) ↔
--  ∀ i ∈ s, continuous (eval i ∘ f) :=
--by rw [set_coe.forall', continuous_pi_iff]; refl
--
--lemma Pi.uniform_continuous_restrict {ι : Type*} (α : ι → Type*) [Π i, uniform_space (α i)]
--  (s : set ι) : uniform_continuous (s.restrict : (Π i : ι, α i) → Π i : s, α i) :=
--uniform_continuous_pi.mpr (λ i, Pi.uniform_continuous_proj α i)
--
--lemma Pi.uniform_continuous_restrict_iff {ι α : Type*} (β : ι → Type*) [uniform_space α]
--  [Π i, uniform_space (β i)] (s : set ι) {f : α → Π i, β i} :
--  uniform_continuous ((s.restrict : (Π i : ι, β i) → Π i : s, β i) ∘ f) ↔
--  ∀ i ∈ s, uniform_continuous (eval i ∘ f) :=
--by rw [set_coe.forall', uniform_continuous_pi]; refl

end prelim

variable {ι X Y α β : Type*} [TopologicalSpace X] [UniformSpace α] [UniformSpace β]
variable {F : ι → X → α} {G : ι → β → α}

theorem Equicontinuous.comap_uniformFun_eq_comap_pi [CompactSpace X] (hF : Equicontinuous F) :
    (UniformFun.uniformSpace X α).comap (UniformFun.ofFun ∘ F) =
    (Pi.uniformSpace (fun _ ↦ α)).comap F := by
  let F' := UniformFun.ofFun ∘ F
  refine le_antisymm (UniformSpace.comap_mono UniformFun.uniformContinuous_toFun) ?_
  change comap _ _ ≤ comap _ _
  simp_rw [Pi.uniformity, Filter.comap_iInf, comap_comap, Function.comp]
  refine ((UniformFun.hasBasis_uniformity X α).comap (Prod.map F' F')).ge_iff.mpr ?_
  intro U hU
  rcases comp_comp_symm_mem_uniformity_sets hU with ⟨V, hV, Vsymm, hVU⟩
  let Ω : X → Set X := λ x => {y | ∀ i, (F i x, F i y) ∈ V}
  rcases CompactSpace.elim_nhds_subcover Ω (λ x => hF x V hV) with ⟨S, Scover⟩
  have : (⋂ s ∈ S, {ij : ι × ι | (F ij.1 s, F ij.2 s) ∈ V}) ⊆
      (Prod.map F' F') ⁻¹' UniformFun.gen X α U := by
    rintro ⟨i, j⟩ hij x
    rw [mem_iInter₂] at hij
    rcases mem_iUnion₂.mp (Scover.symm.subset <| mem_univ x) with ⟨s, hs, hsx⟩
    exact hVU (prod_mk_mem_compRel (prod_mk_mem_compRel
      (Vsymm.mk_mem_comm.mp (hsx i)) (hij s hs)) (hsx j))
  exact mem_of_superset
    (S.iInter_mem_sets.mpr fun x _ ↦ mem_iInf_of_mem x <| preimage_mem_comap hV) this

theorem Equicontinuous.uniformInducing_pi [UniformSpace ι] [CompactSpace X]
    (hF : Equicontinuous F) (F_ind : UniformInducing (UniformFun.ofFun ∘ F)) :
    UniformInducing F where

lemma theorem1' {𝔖 : Set (Set X)} (h𝔖 : ∀ K ∈ 𝔖, IsCompact K)
  (hF : ∀ K ∈ 𝔖, Equicontinuous ((K.restrict : (X → α) → (K → α)) ∘ F)) :
  (UniformOnFun.uniformSpace X α 𝔖).comap F =
    (⨅ K ∈ 𝔖, ⨅ x ∈ K, ‹UniformSpace α›.comap (eval x)).comap F := by
  rw [UniformOnFun.uniformSpace]
  simp_rw [UniformSpace.comap_iInf, ← UniformSpace.comap_comap]
  refine infi_congr (λ K, infi_congr $ λ hK, _),
  haveI : compact_space K := is_compact_iff_compact_space.mp (h𝔖 K hK),
  simp_rw [theorem1 (hF K hK), @uniform_space.comap_comap _ _ _ _ F,
            Pi.uniform_space, of_core_eq_to_core, uniform_space.comap_infi, infi_subtype],
  refine infi_congr (λ x, infi_congr $ λ hx, congr_arg _ _),
  rw ← uniform_space.comap_comap,
  exact congr_fun (congr_arg _ rfl) _,

lemma theorem1' {𝔖 : Set (Set X)} (h𝔖 : ∀ K ∈ 𝔖, IsCompact K)
    (hF : ∀ K ∈ 𝔖, Equicontinuous ((K.restrict : (X → α) → (K → α)) ∘ F)) :
    (UniformOnFun.uniformSpace X α 𝔖).comap F =
      (⨅ K ∈ 𝔖, ⨅ x ∈ K, ‹UniformSpace α›.comap (eval x)).comap F := by
  rw [UniformOnFun.uniformSpace]
  simp_rw [UniformSpace.comap_iInf, ← UniformSpace.comap_comap]
  refine iInf_congr (λ K => iInf_congr $ λ hK => ?_)
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp (h𝔖 K hK)
  simp_rw [theorem1 (hF K hK), UniformSpace.comap_comap,
            Pi.uniformSpace, UniformSpace.ofCoreEq_toCore, UniformSpace.comap_iInf, iInf_subtype]
  refine iInf_congr (λ x => iInf_congr $ λ hx => congr_arg _ ?_)
  rw [← UniformSpace.comap_comap]
  exact congr_fun (congr_arg _ rfl) _


#exit

lemma theorem1 [compact_space X] (hF : equicontinuous F) :
  (uniform_fun.uniform_space X α).comap F =
  (Pi.uniform_space (λ _, α)).comap F :=
begin
  refine le_antisymm (uniform_space.comap_mono $ le_iff_uniform_continuous_id.mpr $
    uniform_fun.uniform_continuous_to_fun) _,
  change comap _ (𝓤 _) ≤ comap _ (𝓤 _),
  simp_rw [Pi.uniformity, filter.comap_infi, filter.comap_comap, function.comp],
  refine ((uniform_fun.has_basis_uniformity X α).comap (prod.map F F)).ge_iff.mpr _,
  intros U hU,
  rcases comp_comp_symm_mem_uniformity_sets hU with ⟨V, hV, Vsymm, hVU⟩,
  let Ω : X → set X := λ x, {y | ∀ i, (F i x, F i y) ∈ V},
  rcases compact_space.elim_nhds_subcover Ω (λ x, hF x V hV) with ⟨S, Scover⟩,
  have : (⋂ s ∈ S, {ij : ι × ι | (F ij.1 s, F ij.2 s) ∈ V}) ⊆
    (prod.map F F) ⁻¹' uniform_fun.gen X α U,
  { rintro ⟨i, j⟩ hij x,
    rw mem_Inter₂ at hij,
    rcases mem_Union₂.mp (Scover.symm.subset $ mem_univ x) with ⟨s, hs, hsx⟩,
    exact hVU (prod_mk_mem_comp_rel (prod_mk_mem_comp_rel
      (Vsymm.mk_mem_comm.mp (hsx i)) (hij s hs)) (hsx j)) },
  exact mem_of_superset
    (S.Inter_mem_sets.mpr $ λ x hxS, mem_infi_of_mem x $ preimage_mem_comap hV) this,
end

lemma theorem1' {𝔖 : set (set X)} (h𝔖 : ∀ K ∈ 𝔖, is_compact K)
  (hF : ∀ K ∈ 𝔖, equicontinuous ((K.restrict : (X → α) → (K → α)) ∘ F)) :
  (uniform_on_fun.uniform_space X α 𝔖).comap F =
    (⨅ K ∈ 𝔖, ⨅ x ∈ K, ‹uniform_space α›.comap (eval x)).comap F :=
begin
  rw [uniform_on_fun.uniform_space],
  simp_rw [uniform_space.comap_infi, ← uniform_space.comap_comap],
  refine infi_congr (λ K, infi_congr $ λ hK, _),
  haveI : compact_space K := is_compact_iff_compact_space.mp (h𝔖 K hK),
  simp_rw [theorem1 (hF K hK), @uniform_space.comap_comap _ _ _ _ F,
            Pi.uniform_space, of_core_eq_to_core, uniform_space.comap_infi, infi_subtype],
  refine infi_congr (λ x, infi_congr $ λ hx, congr_arg _ _),
  rw ← uniform_space.comap_comap,
  exact congr_fun (congr_arg _ rfl) _,
end

lemma theorem1'' {𝔖 : set (set X)} (hcover : ⋃₀ 𝔖 = univ) (h𝔖 : ∀ K ∈ 𝔖, is_compact K)
  (hF : ∀ K ∈ 𝔖, equicontinuous ((K.restrict : (X → α) → (K → α)) ∘ F)) :
  (uniform_on_fun.uniform_space X α 𝔖).comap F = (Pi.uniform_space (λ _, α)).comap F :=
by simp_rw [theorem1' h𝔖 hF, Pi.uniform_space, of_core_eq_to_core, ←infi_sUnion, hcover, infi_true]

lemma ascoli₀ {𝔖 : set (set X)} {F : ι → X →ᵤ[𝔖] α} {l : filter ι} [l.ne_bot]
  (h1 : ∀ A ∈ 𝔖, is_compact A)
  (h2 : ∀ A ∈ 𝔖, equicontinuous (λ i, set.restrict A (F i)))
  (h3 : ∀ A ∈ 𝔖, ∀ x ∈ A, cauchy (map (eval x ∘ F) l)) :
  cauchy (map F l) :=
begin
  have : @@cauchy (⨅ A ∈ 𝔖, ⨅ x ∈ A, ‹uniform_space α›.comap (eval x)) (map F l),
  { simp_rw [cauchy_infi, ← cauchy_map_iff_comap],
    exact h3 },
  rw [cauchy_of_ne_bot, prod_map_map_eq, map_le_iff_le_comap] at ⊢ this,
  exact this.trans (theorem1' h1 h2).ge
end

lemma ascoli {𝔖 : set (set X)} {F : ι → X →ᵤ[𝔖] α}
  (h1 : ∀ A ∈ 𝔖, is_compact A)
  (h2 : ∀ A ∈ 𝔖, equicontinuous (λ i, set.restrict A (F i)))
  (h3 : ∀ A ∈ 𝔖, ∀ x ∈ A, totally_bounded (range (λ i, F i x))) :
  totally_bounded (range F) :=
begin
  simp_rw totally_bounded_iff_ultrafilter at ⊢ h3,
  intros f hf,
  have : F '' univ ∈ f,
  { rwa [image_univ, ← ultrafilter.mem_coe, ← le_principal_iff] },
  rw ← ultrafilter.of_comap_inf_principal_eq_of_map this,
  set g := ultrafilter.of_comap_inf_principal this,
  refine ascoli₀ h1 h2 (λ A hA x hx, h3 A hA x hx (g.map (eval x ∘ F)) $
    le_principal_iff.mpr $ range_mem_map)
end

lemma ascoli_set {𝔖 : set (set X)} {S : set (X →ᵤ[𝔖] α)}
  (h1 : ∀ A ∈ 𝔖, is_compact A)
  (h2 : ∀ A ∈ 𝔖, equicontinuous (λ f : S, set.restrict A (f : X →ᵤ[𝔖] α)))
  (h3 : ∀ A ∈ 𝔖, ∀ x ∈ A, totally_bounded (eval x '' S)) :
  totally_bounded S :=
begin
  rw ← @subtype.range_coe _ S,
  refine ascoli h1 h2 (λ A hA x hx, _),
  specialize h3 A hA x hx,
  rwa image_eq_range at h3
end

lemma ascoli_compact_closure {𝔖 : set (set X)}
  (F : Y → X →ᵤ[𝔖] α) {S : set Y}
  (h1 : ∀ A ∈ 𝔖, is_compact A)
  (h2 : ∀ A ∈ 𝔖, equicontinuous (λ y : S, set.restrict A (F y)))
  (h3 : ∀ A ∈ 𝔖, ∀ x ∈ A, continuous (eval x ∘ F))
  (h4 : ∀ A ∈ 𝔖, ∀ x ∈ A, is_compact (closure $ range (λ y : S, F y x))) :
  is_compact (range (F ∘ (coe : closure S → Y))) :=
begin
  rw is_compact_iff_totally_bounded_is_complete,
  split,
  { refine ascoli h1 (λ A hA, _)
      (λ A hA x hx, totally_bounded_subset _ (h4 A hA x hx).totally_bounded),
    { change equicontinuous ((λ y : Y, set.restrict A (F y)) ∘ (coe : closure S → Y)),
      exact equicontinuous.closure' (h2 A hA) ((Pi.continuous_restrict_iff _ A).mpr (h3 A hA)) },
    { change range (λ y : closure S, (eval x ∘ F : Y → α) y) ⊆
        closure (range (λ y : S, (eval x ∘ F : Y → α) y)),
      rw [← image_eq_range, ← image_eq_range],
      exact image_closure_subset_closure_image (h3 A hA x hx) } },
  { sorry }, -- need study of complete subsets of `X →ᵤ[𝔖] α`
end

lemma ascoli_compact_closure_set' {𝔖 : set (set X)} {S : set (X →ᵤ[𝔖] α)}
  (h1 : ∀ A ∈ 𝔖, is_compact A)
  (h2 : ∀ A ∈ 𝔖, equicontinuous (λ f : S, set.restrict A (f : X →ᵤ[𝔖] α)))
  (h3 : ∀ A ∈ 𝔖, ∀ x ∈ A, is_compact (closure $ eval x '' S)) :
  is_compact (closure S) :=
begin
  rw ← @subtype.range_coe _ (closure S),
  refine ascoli_compact_closure id h1 h2 (λ A hA x hx, sorry) (λ A hA x hx, _), -- easy sorry
  specialize h3 A hA x hx,
  rwa image_eq_range at h3
end
