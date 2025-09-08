import Mathlib

open Filter Order TopologicalSpace Set
open scoped Topology

lemma foo {α : Type*} [TopologicalSpace α] [SecondCountableTopology α] {t : Set (Set α)}
    (ht : IsTopologicalBasis t) {u : Set α} (hu : IsOpen u) :
    ∃ s ⊆ t, s.Countable ∧ u = ⋃ a ∈ s, a := by
  have A : ∀ x ∈ u, ∃ a ∈ t, x ∈ a ∧ a ⊆ u :=
    fun x hx ↦ ht.exists_subset_of_mem_open hx hu
  choose! a hat xa au using A
  obtain ⟨T, T_count, hT⟩ : ∃ T : Set u, T.Countable ∧ ⋃ i ∈ T, a i = ⋃ (i : u), a i := by
    apply isOpen_iUnion_countable _
    rintro ⟨x, hx⟩
    exact ht.isOpen (hat x hx)
  refine ⟨(fun (x : u) ↦ a x) '' T, ?_, T_count.image _, ?_⟩
  · simp only [image_subset_iff]
    rintro ⟨x, xu⟩ -
    exact hat x xu
  rw [biUnion_image, hT]
  apply Subset.antisymm
  · intro x hx
    simp
    grind
  · simp
    grind

lemma bar {α : Type*} [TopologicalSpace α] [SecondCountableTopology α] {t : Set (Set α)}
    (ht : IsTopologicalBasis t) :
    ∃ s ⊆ t, s.Countable ∧ IsTopologicalBasis s := by
  have A : ∀ u ∈ countableBasis α, ∃ s ⊆ t, s.Countable ∧ u = ⋃ a ∈ s, a :=
    fun u hu ↦ foo ht ((isBasis_countableBasis α).isOpen hu)
  choose! s hst s_count hs using A
  refine ⟨⋃ u ∈ countableBasis α, s u, by simpa using hst,
    (countable_countableBasis α).biUnion s_count, ?_⟩
  apply isTopologicalBasis_of_isOpen_of_nhds
  · simp only [mem_iUnion, exists_prop, forall_exists_index, and_imp]
    have := @ht.isOpen
    grind
  · intro x v hx hv
    simp only [mem_iUnion, exists_prop]
    obtain ⟨u, u_mem, xu, uv⟩ : ∃ u ∈ countableBasis α, x ∈ u ∧ u ⊆ v :=
      (isBasis_countableBasis α).isOpen_iff.1 hv _ hx
    have : x ∈ ⋃ a ∈ s u, a := by
      convert xu
      exact (hs u u_mem).symm
    obtain ⟨w, ws, xw⟩ : ∃ w ∈ s u, x ∈ w := by simpa using this
    refine ⟨w, ⟨u, u_mem, ws⟩, xw, ?_⟩
    apply Subset.trans (Subset.trans _ (hs u u_mem).symm.subset) uv
    exact subset_iUnion₂_of_subset w ws fun ⦃a⦄ a ↦ a

#check TopologicalSpace.IsTopologicalBasis.eq_generateFrom

lemma bar2 {α : Type*} [ts : TopologicalSpace α] [SecondCountableTopology α] {t : Set (Set α)}
    (ht : ts = generateFrom t) :
    ∃ s ⊆ t, s.Countable ∧ ts = generateFrom s := by
  let t' := (fun f => ⋂₀ f) '' { f : Set (Set α) | f.Finite ∧ f ⊆ t }
  have : IsTopologicalBasis t' := TopologicalSpace.isTopologicalBasis_of_subbasis ht
  obtain ⟨s', s't', s'_count, hs'⟩ : ∃ s' ⊆ t', s'.Countable ∧ IsTopologicalBasis s' := bar this
  have A : ∀ u ∈ s', ∃ (f : Set (Set α)), f.Finite ∧ f ⊆ t ∧ ⋂₀ f = u :=
    fun u hu ↦ by simpa [t', and_assoc] using s't' hu
  choose! f f_fin ft hf using A
  refine ⟨⋃ u ∈ s', f u, by simpa using ft, ?_, ?_⟩
  · apply s'_count.biUnion
    intro u hu
    exact Finite.countable (f_fin u hu)
  · apply le_antisymm
    · apply le_generateFrom_iff_subset_isOpen.2
      simp only [iUnion_subset_iff]
      intro u hu v hv
      rw [ht]
      apply isOpen_generateFrom_of_mem
      exact ft u hu hv
    · rw [hs'.eq_generateFrom]
      apply le_generateFrom_iff_subset_isOpen.2
      intro u hu
      rw [← hf u hu, sInter_eq_biInter]
      change IsOpen[generateFrom _] (⋂ i ∈ f u, i)
      apply @Finite.isOpen_biInter _ _ (generateFrom (⋃ u ∈ s', f u)) _ _
      · apply f_fin u hu
      · intro i hi
        apply isOpen_generateFrom_of_mem
        simp
        grind










namespace WithTopOrderTopology

variable {ι : Type*} [Preorder ι]

scoped instance : TopologicalSpace (WithTop ι) := Preorder.topology _

scoped instance : OrderTopology (WithTop ι) := ⟨rfl⟩

lemma plouf [ts : TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι] :
    ∃ (c : Set ι), c.Countable ∧ ts = generateFrom { s | ∃ a ∈ c, s = Ioi a ∨ s = Iio a } := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨∅, by simp, Subsingleton.elim _ _⟩
  obtain ⟨t, t_subs, t_count, ht⟩ : ∃ t ⊆ { s | ∃ a, s = Ioi a ∨ s = Iio a },
      t.Countable ∧ ts = generateFrom t :=
    bar2 OrderTopology.topology_eq_generate_intervals
  have A : ∀ s ∈ t, ∃ a, s = Ioi a ∨ s = Iio a := t_subs
  choose! a ha using A
  refine ⟨a '' t, t_count.image _, ?_⟩



#exit

scoped instance [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι] :
    SecondCountableTopology (WithTop ι) := by
  sorry -- THE SORRY IS HERE ---------------------------------------------

end WithTopOrderTopology

namespace WithTop

open scoped WithTopOrderTopology

variable {ι : Type*}

noncomputable
abbrev ut [Nonempty ι] : WithTop ι → ι := WithTop.untopD (Classical.arbitrary ι)

variable [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]

lemma isEmbedding_coe : Topology.IsEmbedding ((↑) : ι → WithTop ι) := by
  refine WithTop.coe_strictMono.isEmbedding_of_ordConnected ?_
  rw [WithTop.range_coe]
  exact Set.ordConnected_Iio

lemma isOpenEmbedding_coe : Topology.IsOpenEmbedding ((↑) : ι → WithTop ι) :=
  ⟨isEmbedding_coe, by rw [WithTop.range_coe]; exact isOpen_Iio⟩

lemma nhds_coe {r : ι} : 𝓝 (r : WithTop ι) = (𝓝 r).map (↑) :=
  (isOpenEmbedding_coe.map_nhds_eq r).symm

lemma tendsto_ut [Nonempty ι] {a : WithTop ι} (ha : a ≠ ⊤) :
    Tendsto WithTop.ut (𝓝 a) (𝓝 a.ut) := by
  lift a to ι using ha
  rw [nhds_coe, tendsto_map'_iff]
  exact tendsto_id

lemma continuousOn_ut [Nonempty ι] : ContinuousOn WithTop.ut { a : WithTop ι | a ≠ ⊤ } :=
  fun _a ha ↦ ContinuousAt.continuousWithinAt (WithTop.tendsto_ut ha)

@[fun_prop]
lemma continuous_coe : Continuous ((↑) : ι → WithTop ι) :=
  isEmbedding_coe.continuous

variable (ι) in
noncomputable
def neTopEquiv [Nonempty ι] : { a : WithTop ι | a ≠ ⊤ } ≃ ι where
  toFun x := WithTop.ut x
  invFun x := ⟨x, WithTop.coe_ne_top⟩
  left_inv := fun x => Subtype.eq <| by
    lift (x : WithTop ι) to ι using x.2 with y
    simp
  right_inv x := by simp

variable (ι) in
noncomputable
def neTopHomeomorph [Nonempty ι] : { a : WithTop ι | a ≠ ⊤ } ≃ₜ ι where
  toEquiv := WithTop.neTopEquiv ι
  continuous_toFun := continuousOn_iff_continuous_restrict.1 continuousOn_ut
  continuous_invFun := continuous_coe.subtype_mk _

variable (ι) in
/-- If `ι` has a top element, then `WithTop ι` is homeomorphic to `ι ⊕ Unit`. -/
noncomputable
def sumHomeomorph [OrderTop ι] : WithTop ι ≃ₜ ι ⊕ Unit where
  toFun x := if h : x = ⊤ then Sum.inr () else Sum.inl x.ut
  invFun x := match x with
    | Sum.inl i => (i : WithTop ι)
    | Sum.inr () => ⊤
  left_inv x := by cases x <;> simp
  right_inv x := by cases x <;> simp
  continuous_toFun := by
    have h_fr : frontier ({⊤} : Set (WithTop ι)) = ∅ := by
      simp only [frontier, Set.finite_singleton, Set.Finite.isClosed, IsClosed.closure_eq]
      suffices interior ({⊤} : Set (WithTop ι)) = {⊤} by simp [this]
      rw [interior_eq_iff_isOpen]
      have : {⊤} = Set.Ioi ((⊤ : ι) : WithTop ι) := by ext; simp
      rw [this]
      exact isOpen_Ioi
    refine continuous_if' (by simp [h_fr]) (by simp [h_fr]) (by simp) ?_
    exact Continuous.comp_continuousOn (by fun_prop) continuousOn_ut
  continuous_invFun := continuous_sum_dom.mpr ⟨by fun_prop, by fun_prop⟩

end WithTop
