/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Topology.UniformSpace.Equicontinuity
import Mathlib.Topology.UniformSpace.Equiv

/-!
# Ascoli Theorem

## Main definitions
## Main statements
## Notation
## Implementation details
## References
## Tags
-/

open Set Filter Uniformity Topology TopologicalSpace Function UniformConvergence

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

variable {ι X Y α β : Type*} [TopologicalSpace X] [u : UniformSpace α] [UniformSpace β]
variable {F : ι → X → α} {G : ι → β → α}

theorem Equicontinuous.comap_uniformFun_eq [CompactSpace X] (hF : Equicontinuous F) :
    (UniformFun.uniformSpace X α).comap F =
    (Pi.uniformSpace _).comap F := by
  -- The `≤` inequality is trivial
  refine le_antisymm (UniformSpace.comap_mono UniformFun.uniformContinuous_toFun) ?_
  -- A bit of rewriting to get a nice intermediate statement.
  change comap _ _ ≤ comap _ _
  simp_rw [Pi.uniformity, Filter.comap_iInf, comap_comap, Function.comp]
  refine ((UniformFun.hasBasis_uniformity X α).comap (Prod.map F F)).ge_iff.mpr ?_
  -- TODO: what are the names used in Bourbaki for the sets?
  -- Core of the proof: we need to show that, for any entourage `U` in `α`,
  -- the set `𝐓(U) := {(i,j) : ι × ι | ∀ x : X, (F i x, F j x) ∈ U}` belongs to the filter
  -- `⨅ x, comap ((i,j) ↦ (F i x, F j x)) (𝓤 α)`.
  -- In other words, we have to show that it contains a finite intersection of
  -- sets of the form `𝐒(V, x) := {(i,j) : ι × ι | (F i x, F j x) ∈ V}` for some
  -- `x : X` and `V ∈ 𝓤 α`.
  intro U hU
  -- We will do an `ε/3` argument, so we start by choosing a symmetric entourage `V ∈ 𝓤 α`
  -- such that `V ○ V ○ V ⊆ U`.
  rcases comp_comp_symm_mem_uniformity_sets hU with ⟨V, hV, Vsymm, hVU⟩
  -- Set `Ω x := {y | ∀ i, (F i x, F i y) ∈ V}`. The equicontinuity of `F` guarantees that
  -- each `Ω x` is a neighborhood of `x`.
  let Ω x : Set X := {y | ∀ i, (F i x, F i y) ∈ V}
  -- Hence, by compactness of `X`, we can find some `A ⊆ X` finite such that the `Ω a`s for `a ∈ A`
  -- still cover `X`.
  rcases CompactSpace.elim_nhds_subcover Ω (fun x ↦ hF x V hV) with ⟨A, Acover⟩
  -- We now claim that `⋂ a ∈ A, 𝐒(V, a) ⊆ 𝐓(U)`.
  have : (⋂ a ∈ A, {ij : ι × ι | (F ij.1 a, F ij.2 a) ∈ V}) ⊆
      (Prod.map F F) ⁻¹' UniformFun.gen X α U := by
    -- Given `(i, j) ∈ ⋂ a ∈ A, 𝐒(V, a)` and `x : X`, we have to prove that `(F i x, F j x) ∈ U`.
    rintro ⟨i, j⟩ hij x
    rw [mem_iInter₂] at hij
    -- We know that `x ∈ Ω a` for some `a ∈ A`, so that both `(F i x, F i a)` and `(F j a, F j x)`
    -- are in `V`.
    rcases mem_iUnion₂.mp (Acover.symm.subset <| mem_univ x) with ⟨a, ha, hax⟩
    -- Since `(i, j) ∈ 𝐒(V, a)` we also have `(F i a, F j a) ∈ V`, and finally we get
    -- `(F i x, F j x) ∈ V ○ V ○ V ⊆ U`.
    exact hVU (prod_mk_mem_compRel (prod_mk_mem_compRel
      (Vsymm.mk_mem_comm.mp (hax i)) (hij a ha)) (hax j))
  -- This completes the proof.
  exact mem_of_superset
    (A.iInter_mem_sets.mpr fun x _ ↦ mem_iInf_of_mem x <| preimage_mem_comap hV) this

lemma Equicontinuous.uniformInducing_uniformFun_iff_pi [UniformSpace ι] [CompactSpace X]
    (hF : Equicontinuous F) :
    UniformInducing (UniformFun.ofFun ∘ F) ↔ UniformInducing F := by
  rw [uniformInducing_iff_uniformSpace, uniformInducing_iff_uniformSpace, ← hF.comap_uniformFun_eq]
  rfl

lemma Equicontinuous.inducing_uniformFun_iff_pi [TopologicalSpace ι] [CompactSpace X]
    (hF : Equicontinuous F) :
    Inducing (UniformFun.ofFun ∘ F) ↔ Inducing F := by
  rw [inducing_iff, inducing_iff]
  change (_ = (UniformFun.uniformSpace X α |>.comap F |>.toTopologicalSpace)) ↔
         (_ = (Pi.uniformSpace _ |>.comap F |>.toTopologicalSpace))
  rw [hF.comap_uniformFun_eq]

theorem Equicontinuous.tendsto_uniformFun_iff_pi [CompactSpace X]
    (hF : Equicontinuous F) (ℱ : Filter ι) (f : X → α) :
    Tendsto (UniformFun.ofFun ∘ F) ℱ (𝓝 <| UniformFun.ofFun f) ↔
    Tendsto F ℱ (𝓝 f) := by
  rcases ℱ.eq_or_neBot with rfl | ℱ_ne
  · simp
  constructor <;> intro H
  · exact UniformFun.uniformContinuous_toFun.continuous.tendsto _|>.comp H
  · set S : Set (X → α) := closure (range F)
    set 𝒢 : Filter S := comap (↑) (map F ℱ)
    have hS : S.Equicontinuous := closure' (by rwa [equicontinuous_iff_range] at hF) continuous_id
    have ind : Inducing (UniformFun.ofFun ∘ (↑) : S → X →ᵤ α) :=
      hS.inducing_uniformFun_iff_pi.mpr ⟨rfl⟩
    have f_mem : f ∈ S := mem_closure_of_tendsto H range_mem_map
    have h𝒢ℱ : map (↑) 𝒢 = map F ℱ := Filter.map_comap_of_mem
      (Subtype.range_coe ▸ mem_of_superset range_mem_map subset_closure)
    have H' : Tendsto id 𝒢 (𝓝 ⟨f, f_mem⟩) := by
      rwa [tendsto_id', nhds_induced, ← map_le_iff_le_comap, h𝒢ℱ]
    rwa [ind.tendsto_nhds_iff, comp.right_id, ← tendsto_map'_iff, h𝒢ℱ] at H'

theorem Equicontinuous.comap_uniformOnFun_eq {𝔖 : Set (Set X)} (h𝔖 : ∀ K ∈ 𝔖, IsCompact K)
    (hF : ∀ K ∈ 𝔖, Equicontinuous (K.restrict ∘ F)) :
    (UniformOnFun.uniformSpace X α 𝔖).comap F =
    (Pi.uniformSpace _).comap ((⋃₀ 𝔖).restrict ∘ F) := by
  -- Recall that the uniform structure on `X →ᵤ[𝔖] α` is the one induced by all the maps
  -- `K.restrict : (X →ᵤ[𝔖] α) → (K →ᵤ α)` for `K ∈ 𝔖`. Its pullback along `F`, which is
  -- the LHS of our goal, is thus the uniform structure induced by the maps
  -- `K.restrict ∘ F : ι → (K →ᵤ α)` for `K ∈ 𝔖`.
  have H1 : (UniformOnFun.uniformSpace X α 𝔖).comap F =
      ⨅ (K ∈ 𝔖), (UniformFun.uniformSpace _ _).comap (K.restrict ∘ F) := by
    simp_rw [UniformOnFun.uniformSpace, UniformSpace.comap_iInf, UniformSpace.comap_comap]
  -- Now, note that a similar fact is true for the uniform structure on `X → α` induced by
  -- the map `(⋃₀ 𝔖).restrict : (X → α) → ((⋃₀ 𝔖) → α)`: it is equal to the one induced by
  -- all maps `K.restrict : (X → α) → (K → α)` for `K ∈ 𝔖`, which means that the RHS of our
  -- goal is the uniform structure induced by the maps `K.restrict ∘ F : ι → (K → α)` for `K ∈ 𝔖`.
  have H2 : (Pi.uniformSpace _).comap ((⋃₀ 𝔖).restrict ∘ F) =
      ⨅ (K ∈ 𝔖), (Pi.uniformSpace _).comap (K.restrict ∘ F) := by
    simp_rw [UniformSpace.comap_comap, Pi.uniformSpace_comap_restrict_sUnion (fun _ ↦ α) 𝔖,
      UniformSpace.comap_iInf]
  -- But, for `K ∈ 𝔖` fixed, we know that the uniform structures of `K →ᵤ α` and `K → α`
  -- induce, via the equicontinuous family `K.restrict ∘ F`, the same uniform structure on `ι`.
  have H3 : ∀ K ∈ 𝔖, (UniformFun.uniformSpace K α).comap (K.restrict ∘ F) =
      (Pi.uniformSpace _).comap (K.restrict ∘ F) := fun K hK ↦ by
    have : CompactSpace K := isCompact_iff_compactSpace.mp (h𝔖 K hK)
    exact (hF K hK).comap_uniformFun_eq
  -- Combining these three facts completes the proof.
  simp_rw [H1, H2, iInf_congr fun K ↦ iInf_congr fun hK ↦ H3 K hK]

lemma Equicontinuous.uniformInducing_uniformOnFun_iff_pi' [UniformSpace ι]
    {𝔖 : Set (Set X)} (h𝔖 : ∀ K ∈ 𝔖, IsCompact K)
    (hF : ∀ K ∈ 𝔖, Equicontinuous (K.restrict ∘ F)) :
    UniformInducing (UniformOnFun.ofFun 𝔖 ∘ F) ↔
    UniformInducing ((⋃₀ 𝔖).restrict ∘ F) := by
  rw [uniformInducing_iff_uniformSpace, uniformInducing_iff_uniformSpace,
      ← Equicontinuous.comap_uniformOnFun_eq h𝔖 hF]
  rfl

lemma Equicontinuous.uniformInducing_uniformOnFun_iff_pi [UniformSpace ι]
    {𝔖 : Set (Set X)} (𝔖_covers : ⋃₀ 𝔖 = univ) (h𝔖 : ∀ K ∈ 𝔖, IsCompact K)
    (hF : ∀ K ∈ 𝔖, Equicontinuous ((K.restrict : (X → α) → (K → α)) ∘ F)) :
    UniformInducing (UniformOnFun.ofFun 𝔖 ∘ F) ↔
    UniformInducing F := by
  rw [eq_univ_iff_forall] at 𝔖_covers
  let φ : ((⋃₀ 𝔖) → α) ≃ᵤ (X → α) := UniformEquiv.piCongrLeft (β := fun _ ↦ α)
    (Equiv.subtypeUnivEquiv 𝔖_covers)
  rw [Equicontinuous.uniformInducing_uniformOnFun_iff_pi' h𝔖 hF,
      show restrict (⋃₀ 𝔖) ∘ F = φ.symm ∘ F by rfl]
  exact ⟨fun H ↦ φ.uniformInducing.comp H, fun H ↦ φ.symm.uniformInducing.comp H⟩

lemma Equicontinuous.inducing_uniformOnFun_iff_pi' [TopologicalSpace ι]
    {𝔖 : Set (Set X)} (h𝔖 : ∀ K ∈ 𝔖, IsCompact K)
    (hF : ∀ K ∈ 𝔖, Equicontinuous (K.restrict ∘ F)) :
    Inducing (UniformOnFun.ofFun 𝔖 ∘ F) ↔
    Inducing ((⋃₀ 𝔖).restrict ∘ F) := by
  rw [inducing_iff, inducing_iff]
  change (_ = ((UniformOnFun.uniformSpace X α 𝔖).comap F).toTopologicalSpace) ↔
    (_ = ((Pi.uniformSpace _).comap ((⋃₀ 𝔖).restrict ∘ F)).toTopologicalSpace)
  rw [← Equicontinuous.comap_uniformOnFun_eq h𝔖 hF]

lemma Equicontinuous.inducing_uniformOnFun_iff_pi [TopologicalSpace ι]
    {𝔖 : Set (Set X)} (𝔖_covers : ⋃₀ 𝔖 = univ) (h𝔖 : ∀ K ∈ 𝔖, IsCompact K)
    (hF : ∀ K ∈ 𝔖, Equicontinuous (K.restrict ∘ F)) :
    Inducing (UniformOnFun.ofFun 𝔖 ∘ F) ↔
    Inducing F := by
  rw [eq_univ_iff_forall] at 𝔖_covers
  let φ : ((⋃₀ 𝔖) → α) ≃ₜ (X → α) := Homeomorph.piCongrLeft (β := fun _ ↦ α)
    (Equiv.subtypeUnivEquiv 𝔖_covers)
  rw [Equicontinuous.inducing_uniformOnFun_iff_pi' h𝔖 hF,
      show restrict (⋃₀ 𝔖) ∘ F = φ.symm ∘ F by rfl]
  exact ⟨fun H ↦ φ.inducing.comp H, fun H ↦ φ.symm.inducing.comp H⟩

-- TODO: find a way to factor common elements of this proof and the proof of
-- `Equicontinuous.comap_uniformOnFun_eq`
theorem Equicontinuous.tendsto_uniformOnFun_iff_pi'
    {𝔖 : Set (Set X)} (h𝔖 : ∀ K ∈ 𝔖, IsCompact K)
    (hF : ∀ K ∈ 𝔖, Equicontinuous (K.restrict ∘ F)) (ℱ : Filter ι) (f : X → α) :
    Tendsto (UniformOnFun.ofFun 𝔖 ∘ F) ℱ (𝓝 <| UniformOnFun.ofFun 𝔖 f) ↔
    Tendsto ((⋃₀ 𝔖).restrict ∘ F) ℱ (𝓝 <| (⋃₀ 𝔖).restrict f) := by
  rw [← Filter.tendsto_comap_iff (g := (⋃₀ 𝔖).restrict), ← nhds_induced]
  simp_rw [UniformOnFun.topologicalSpace_eq, Pi.induced_restrict_sUnion 𝔖 (π := fun _ ↦ α),
    nhds_iInf, nhds_induced, tendsto_iInf, tendsto_comap_iff]
  congrm ∀ K (hK : K ∈ 𝔖), ?_
  have : CompactSpace K := isCompact_iff_compactSpace.mp (h𝔖 K hK)
  rw [← (hF K hK).tendsto_uniformFun_iff_pi]
  rfl

theorem Equicontinuous.tendsto_uniformOnFun_iff_pi
    {𝔖 : Set (Set X)} (h𝔖 : ∀ K ∈ 𝔖, IsCompact K) (𝔖_covers : ⋃₀ 𝔖 = univ)
    (hF : ∀ K ∈ 𝔖, Equicontinuous (K.restrict ∘ F)) (ℱ : Filter ι) (f : X → α) :
    Tendsto (UniformOnFun.ofFun 𝔖 ∘ F) ℱ (𝓝 <| UniformOnFun.ofFun 𝔖 f) ↔
    Tendsto F ℱ (𝓝 f) := by
  rw [eq_univ_iff_forall] at 𝔖_covers
  let φ : ((⋃₀ 𝔖) → α) ≃ₜ (X → α) := Homeomorph.piCongrLeft (β := fun _ ↦ α)
    (Equiv.subtypeUnivEquiv 𝔖_covers)
  rw [Equicontinuous.tendsto_uniformOnFun_iff_pi' h𝔖 hF,
      show restrict (⋃₀ 𝔖) ∘ F = φ.symm ∘ F by rfl, show restrict (⋃₀ 𝔖) f = φ.symm f by rfl,
      φ.symm.inducing.tendsto_nhds_iff]

#check isClosed_iff_clusterPt

theorem Equicontinuous.isClosed_range_uniformOnFun_iff_pi'
    {𝔖 : Set (Set X)} (h𝔖 : ∀ K ∈ 𝔖, IsCompact K)
    (hF : ∀ K ∈ 𝔖, Equicontinuous (K.restrict ∘ F)) :
    IsClosed (range <| UniformOnFun.ofFun 𝔖 ∘ F) ↔
    IsClosed (range <| (⋃₀ 𝔖).restrict ∘ F) := by
  rcases isEmpty_or_nonempty α with _ | _
  · simp [isClosed_discrete]
  simp_rw [isClosed_iff_clusterPt, ClusterPt, ← Filter.map_top, ← Filter.push_pull', map_neBot_iff,
    inf_top_eq, ← exists_ultrafilter_iff, ← tendsto_iff_comap, UniformOnFun.toFun]
  refine ⟨fun H ↦ ?_, _⟩

theorem Equicontinuous.isClosedMap_uniformOnFun_iff_pi' [TopologicalSpace ι]
    {𝔖 : Set (Set X)} (h𝔖 : ∀ K ∈ 𝔖, IsCompact K) (𝔖_covers : ⋃₀ 𝔖 = univ)
    (hF : ∀ K ∈ 𝔖, Equicontinuous (K.restrict ∘ F)) :
    IsClosedMap (UniformOnFun.ofFun 𝔖 ∘ F) ↔
    IsClosedMap F := by
  sorry

theorem ArzelaAscoli.compactSpace_of_closed_inducing [TopologicalSpace ι] {𝔖 : Set (Set X)}
    (h𝔖 : ∀ K ∈ 𝔖, IsCompact K) (F_ind : Inducing (UniformOnFun.ofFun 𝔖 ∘ F))
    (F_cl : IsClosed (range <| UniformOnFun.ofFun 𝔖 ∘ F))
    (F_eqcont : ∀ K ∈ 𝔖, Equicontinuous (K.restrict ∘ F))
    (F_pointwiseCompact : ∀ x, ∃ K, IsCompact K ∧ ∀ i, F i x ∈ K) :
    CompactSpace ι := by
  have : Inducing (restrict (⋃₀ 𝔖) ∘ F) := by
    rwa [Equicontinuous.inducing_uniformOnFun_iff_pi' h𝔖 F_eqcont] at F_ind
  have F_closed : IsClosed <| range <| (⋃₀ 𝔖).restrict ∘ F := sorry
  choose K K_compact F_in_K using F_pointwiseCompact
  rw [← isCompact_univ_iff, ← this.isCompact_iff, image_univ]
  refine isCompact_of_isClosed_subset (isCompact_univ_pi fun x ↦ K_compact x) F_closed
    (range_subset_iff.mpr fun i ⟨x, _⟩ _ ↦ F_in_K x i)

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
