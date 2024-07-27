import Mathlib.Topology.Category.CompactlyGenerated

universe u v

open TopologicalSpace Filter Topology Set

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

abbrev CompactlyGeneratedSpace (X : Type u) [TopologicalSpace X] : Prop :=
  UCompactlyGeneratedSpace.{u} X

theorem compactlyGeneratedSpace_of_isClosed
    (h : ∀ (s : Set X), (∀ {K : Type u} [TopologicalSpace K], [CompactSpace K] → [T2Space K] →
      ∀ (f : K → X), Continuous f → IsClosed (f ⁻¹' s)) → IsClosed s) :
    CompactlyGeneratedSpace X := by
  refine uCompactlyGeneratedSpace_of_continuous_maps fun f h' ↦
    continuous_iff_isClosed.2 fun t ht ↦ h _ ?_
  intro K _ _ _ g hg
  exact ht.preimage (h' (CompHaus.of K) { toFun := g, continuous_toFun := hg })

theorem compactlyGeneratedSpace_of_isOpen
    (h : ∀ (s : Set X), (∀ {K : Type u} [TopologicalSpace K], [CompactSpace K] → [T2Space K] →
      ∀ (f : K → X), Continuous f → IsOpen (f ⁻¹' s)) → IsOpen s) :
    CompactlyGeneratedSpace X := by
  refine compactlyGeneratedSpace_of_isClosed fun s h' ↦ isOpen_compl_iff.1 <| h _ fun f hf ↦ ?_
  rw [preimage_compl, isOpen_compl_iff]
  exact h' f hf

theorem CompactlyGeneratedSpace.isClosed' [CompactlyGeneratedSpace X] {s : Set X}
    (hs : ∀ {K : Type u} [TopologicalSpace K], [CompactSpace K] → [T2Space K] →
      ∀ (f : K → X), Continuous f → IsClosed (f ⁻¹' s)) : IsClosed s := by
  rw [eq_compactlyGenerated (X := X), TopologicalSpace.compactlyGenerated, isClosed_coinduced,
    isClosed_sigma_iff]
  exact fun ⟨_, f⟩ ↦ hs f f.continuous

theorem CompactlyGeneratedSpace.isClosed [CompactlyGeneratedSpace X] {s : Set X}
    (hs : ∀ ⦃K⦄, IsCompact K → IsClosed (s ∩ K)) : IsClosed s := by
  refine isClosed' fun f hf ↦ ?_
  rw [← Set.preimage_inter_range]
  exact (hs (isCompact_range hf)).preimage hf

theorem CompactlyGeneratedSpace.isOpen' [CompactlyGeneratedSpace X] {s : Set X}
    (hs : ∀ {K : Type u} [TopologicalSpace K], [CompactSpace K] → [T2Space K] →
      ∀ (f : K → X), Continuous f → IsOpen (f ⁻¹' s)) : IsOpen s := by
  rw [eq_compactlyGenerated (X := X), TopologicalSpace.compactlyGenerated, isOpen_coinduced,
    isOpen_sigma_iff]
  exact fun ⟨_, f⟩ ↦ hs f f.continuous

theorem CompactlyGeneratedSpace.isOpen [CompactlyGeneratedSpace X] {s : Set X}
    (hs : ∀ ⦃K⦄, IsCompact K → IsOpen (s ∩ K)) : IsOpen s := by
  refine isOpen' fun f hf ↦ ?_
  rw [← Set.preimage_inter_range]
  exact (hs (isCompact_range hf)).preimage hf

theorem compactlyGeneratedSpace_of_coinduced {Y : Type u}
    [tX : TopologicalSpace X] [tY : TopologicalSpace Y]
    [CompactlyGeneratedSpace X] {f : X → Y} (hf : Continuous f) (ht : tY = coinduced f tX) :
    CompactlyGeneratedSpace Y := by
  refine compactlyGeneratedSpace_of_isClosed fun s h ↦ ?_
  rw [ht, isClosed_coinduced]
  refine CompactlyGeneratedSpace.isClosed' fun g hg ↦ h _ (hf.comp hg)

instance {S : Setoid X} [CompactlyGeneratedSpace X] : CompactlyGeneratedSpace (Quotient S) :=
  compactlyGeneratedSpace_of_coinduced continuous_quotient_mk' rfl

instance [CompactlyGeneratedSpace X] [CompactlyGeneratedSpace Y] :
    CompactlyGeneratedSpace (X ⊕ Y) := by
  refine compactlyGeneratedSpace_of_isClosed fun s h ↦ isClosed_sum_iff.2 ⟨?_, ?_⟩
  all_goals
    refine CompactlyGeneratedSpace.isClosed' ?_
    intro K _ _ _ f hf
  · let g : ULift.{v} K → X ⊕ Y := Sum.inl ∘ f ∘ ULift.down
    have hg : Continuous g := continuous_inl.comp <| hf.comp continuous_uLift_down
    exact (h g hg).preimage continuous_uLift_up
  · let g : ULift.{u} K → X ⊕ Y := Sum.inr ∘ f ∘ ULift.down
    have hg : Continuous g := continuous_inr.comp <| hf.comp continuous_uLift_down
    exact (h g hg).preimage continuous_uLift_up

instance {ι : Type u} {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    [∀ i, CompactlyGeneratedSpace (X i)] : CompactlyGeneratedSpace (Sigma X) := by
  refine compactlyGeneratedSpace_of_isClosed fun s h ↦ isClosed_sigma_iff.2 fun i ↦
    CompactlyGeneratedSpace.isClosed' ?_
  intro K _ _ _ f hf
  let g : ULift.{u} K → Sigma X := Sigma.mk i ∘ f ∘ ULift.down
  have hg : Continuous g := continuous_sigmaMk.comp <| hf.comp continuous_uLift_down
  exact (h g hg).preimage continuous_uLift_up

open OnePoint in
instance [SequentialSpace X] : CompactlyGeneratedSpace X := by
  refine compactlyGeneratedSpace_of_isClosed fun s h ↦
    SequentialSpace.isClosed_of_seq _ fun u p hu hup ↦ ?_
  let g : ULift.{u} (OnePoint ℕ) → X := (continuousMapMkNat u p hup) ∘ ULift.down
  change ULift.up ∞ ∈ g ⁻¹' s
  have : Filter.Tendsto (@OnePoint.some ℕ) Filter.atTop (𝓝 ∞) := by
    rw [← Nat.cofinite_eq_atTop, ← cocompact_eq_cofinite, ← coclosedCompact_eq_cocompact]
    exact tendsto_coe_nhds_infty
  apply IsClosed.mem_of_tendsto _ ((continuous_uLift_up.tendsto ∞).comp this)
  · simp only [Function.comp_apply, mem_preimage, eventually_atTop, ge_iff_le]
    exact ⟨0, fun b _ ↦ hu b⟩
  · exact h g ((continuousMapMkNat u p hup).continuous.comp continuous_uLift_down)

theorem compactlyGeneratedSpace_of_isClosed_of_t2 [T2Space X]
    (h : ∀ s, (∀ (K : Set X), IsCompact K → IsClosed (s ∩ K)) → IsClosed s) :
    CompactlyGeneratedSpace X := by
  refine compactlyGeneratedSpace_of_isClosed fun s hs ↦ h s fun K hK ↦ ?_
  rw [Set.inter_comm, ← Subtype.image_preimage_coe]
  apply hK.isClosed.isClosedMap_subtype_val
  have : CompactSpace ↑K := isCompact_iff_compactSpace.1 hK
  exact hs Subtype.val continuous_subtype_val

theorem compactlyGeneratedSpace_of_isOpen_of_t2 [T2Space X]
    (h : ∀ s, (∀ (K : Set X), IsCompact K → IsOpen ((Subtype.val) ⁻¹' s : Set ↑K)) → IsOpen s) :
    CompactlyGeneratedSpace X := by
  refine compactlyGeneratedSpace_of_isOpen fun s hs ↦ h s fun K hK ↦ ?_
  have : CompactSpace ↑K := isCompact_iff_compactSpace.1 hK
  exact hs Subtype.val continuous_subtype_val

instance [WeaklyLocallyCompactSpace X] [T2Space X] : CompactlyGeneratedSpace X := by
  refine compactlyGeneratedSpace_of_isClosed_of_t2 fun s h ↦ ?_
  rw [isClosed_iff_forall_filter]
  intro x ℱ hℱ₁ hℱ₂ hℱ₃
  rcases exists_compact_mem_nhds x with ⟨K, hK, K_mem⟩
  exact Set.mem_of_mem_inter_left <| isClosed_iff_forall_filter.1 (h _ hK) x ℱ hℱ₁
    (Filter.inf_principal ▸ le_inf hℱ₂ (le_trans hℱ₃ <| Filter.le_principal_iff.2 K_mem)) hℱ₃
