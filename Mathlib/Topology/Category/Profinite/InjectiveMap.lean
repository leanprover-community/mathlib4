import Mathlib.Topology.Connected
import Mathlib.Topology.Separation

universe u

theorem compactFiniteIntersection {α S : Type _} {U : Set α} [TopologicalSpace α] [CompactSpace α]
    (hU : IsOpen U) {F : S → Set α} (hF : ∀ s : S, IsClosed (F s)) (hFi : (⋂ s : S, F s) ⊆ U) :
    ∃ S₀ : Finset S, (⋂ s ∈ S₀, F s) ⊆ U := by
  have hUc : IsCompact (Uᶜ) := IsClosed.isCompact (isClosed_compl_iff.mpr hU)
  let UF : S → Set α := fun s => F sᶜ
  have hUo : ∀ s : S, IsOpen (UF s) := fun s => isOpen_compl_iff.mpr (hF s)
  have hsU : Uᶜ ⊆ ⋃ s : S, UF s :=
    by
    rw [Set.iUnion_eq_compl_iInter_compl]
    rw [Set.compl_subset_compl]
    -- dsimp [UF]
    intro x hx
    simp at hx
    apply hFi
    exact Set.mem_iInter.mpr hx
  · obtain ⟨S₀, h⟩ := IsCompact.elim_finite_subcover hUc UF hUo hsU
    use S₀
    rw [← Set.compl_subset_compl]
    rw [Set.iInter_eq_compl_iUnion_compl]
    simp only [Set.compl_iInter, Set.compl_iUnion]
    -- simp only [UF] at h
    intro u hu
    obtain ⟨t, i, hi⟩ := h hu
    use t
    constructor
    simp only [compl_compl, Set.iUnion_congr_Prop]
    exact i
    exact hi

def Quasicomponent {α : Type _} (x : α) [TopologicalSpace α] : Set α :=
  ⋂ Z : { Z : Set α // IsClopen Z ∧ x ∈ Z }, Z

theorem quasicomponentEqComponentOfCompactSpace {α : Type _} (x : α) [TopologicalSpace α]
    [CompactSpace α] [T2Space α] : connectedComponent x = Quasicomponent x :=
  by
  haveI h_normal : NormalSpace α := normalOfCompactT2
  have hQclosed : IsClosed (Quasicomponent x) :=
    by
    refine' isClosed_iInter _
    intro i
    exact i.property.1.2
  haveI hQinQ : Quasicomponent x ⊆ Quasicomponent x := by tauto
  have h' : x ∈ Quasicomponent x := by
    unfold Quasicomponent
    refine' Set.mem_iInter.mpr _
    intro i
    exact i.property.2
  ext y
  constructor
  · intro hy
    apply connectedComponent_subset_iInter_clopen
    exact hy
  · suffices h : IsPreconnected (Quasicomponent x)
    · unfold connectedComponent
      intro hy
      use Quasicomponent x
      constructor
      constructor
      exact h
      exact h'
      exact hy
    · rw [isPreconnected_iff_subset_of_fully_disjoint_closed hQclosed]
      intro X₁ X₂ hX₁ hX₂ hX₁uX₂ hX₁nX₂
      obtain ⟨U, V, h⟩ := normal_separation hX₁ hX₂ hX₁nX₂
      have hUVc : closure U ⊆ Vᶜ :=
        by
        rw [IsClosed.closure_subset_iff (isClosed_compl_iff.mpr h.2.1)]
        exact Disjoint.subset_compl_right h.2.2.2.2
      have hVUc : closure V ⊆ Uᶜ :=
        by
        rw [IsClosed.closure_subset_iff (isClosed_compl_iff.mpr h.1)]
        exact Disjoint.subset_compl_right h.2.2.2.2.symm
      let S := { s : Set α // IsClopen s ∧ x ∈ s }
      let F : S → Set α := fun s => s
      have hF : ∀ s : S, IsClosed (F s) := by
        intro s
        exact s.property.1.2
      have hUV : IsOpen (U ∪ V) := IsOpen.union h.1 h.2.1
      have h_inter : (⋂ s : S, F s) ⊆ U ∪ V := fun a ha =>
        Set.union_subset_union h.2.2.1 h.2.2.2.1 (hX₁uX₂ ha)
      obtain ⟨S₀, hS₀⟩ := compactFiniteIntersection hUV hF h_inter
      let F' := ⋂ (s ∈ S₀), (fun s : S => F s) s
      have hx : x ∈ X₁ ∪ X₂ := hX₁uX₂ h'
      cases hx
      · left
        have hFclopen : IsClopen F' :=
          by
          refine' isClopen_biInter_finset _
          intro i _
          simp only
          exact i.property.1
        have hFU : IsClopen (U ∩ F') := by
          constructor
          · exact IsOpen.inter h.1 (IsClopen.isOpen hFclopen)
          refine' isClosed_of_closure_subset _
          intro a ha
          have hUVF : (U ∪ V) ∩ F' = F' := by
            ext
            constructor
            exact fun hx1 => (Set.inter_subset_right (U ∪ V) F') hx1
            intro hx1
            constructor
            exact hS₀ hx1
            exact hx1
          have hUUV : closure U ∩ (U ∪ V) = U := by
            ext
            constructor
            · intro hx1
              cases hx1.2
              · assumption
              exfalso
              refine' hUVc hx1.1 _
              assumption
            · intro hx1
              constructor
              exact subset_closure hx1
              left
              exact hx1
          rw [← hUUV]
          rw [Set.inter_assoc]
          rw [hUVF]
          rw [← IsClosed.closure_eq hFclopen.2]
          exact closure_inter_subset_inter_closure U F' ha
        have hQUF : Quasicomponent x ⊆ U ∩ F' :=
          by
          have hxUF : x ∈ U ∩ F' := by
            constructor
            · refine' h.2.2.1 _
              assumption
            · simp only [Set.mem_iInter, Subtype.forall]
              intro a b _
              exact b.2
          have hUF : U ∩ F' ∈ { Z : Set α | IsClopen Z ∧ x ∈ Z } := ⟨hFU, hxUF⟩
          unfold Quasicomponent
          intro x1 hx1
          rw [Set.mem_iInter] at hx1
          exact hx1 ⟨U ∩ F', hUF⟩
        have hXQ : X₂ ∩ Quasicomponent x = ∅ :=
          by
          apply Set.eq_empty_of_subset_empty
          intro a ha
          have ha' := Set.inter_subset_inter_right X₂ hQUF ha
          have ha'' := Set.inter_subset_inter_left (U ∩ F') h.2.2.2.1 ha'
          rw [← Set.inter_assoc] at ha''
          rw [Set.inter_comm V U] at ha''
          rw [Set.disjoint_iff_inter_eq_empty.mp h.2.2.2.2] at ha''
          exact ha''.1
        intro a ha
        cases hX₁uX₂ ha
        · assumption
        exfalso
        refine' (Set.ext_iff.mp hXQ a).mp ⟨_, ha⟩
        assumption
      · right
        have hFclopen : IsClopen F' :=
          by
          refine' isClopen_biInter_finset _
          intro i _
          simp only
          exact i.property.1
        have hFU : IsClopen (V ∩ F') := by
          constructor
          · exact IsOpen.inter h.2.1 (IsClopen.isOpen hFclopen)
          refine' isClosed_of_closure_subset _
          intro a ha
          have hUVF : (U ∪ V) ∩ F' = F' := by
            ext
            constructor
            exact fun hx1 => (Set.inter_subset_right (U ∪ V) F') hx1
            intro hx1
            constructor
            exact hS₀ hx1
            exact hx1
          have hUUV : closure V ∩ (U ∪ V) = V := by
            ext
            constructor
            · intro hx1
              cases hx1.2
              swap
              · assumption
              exfalso
              refine' hVUc hx1.1 _
              assumption
            · intro hx1
              constructor
              exact subset_closure hx1
              right
              exact hx1
          rw [← hUUV]
          rw [Set.inter_assoc]
          rw [hUVF]
          rw [← IsClosed.closure_eq hFclopen.2]
          exact closure_inter_subset_inter_closure V F' ha
        have hQUF : Quasicomponent x ⊆ V ∩ F' :=
          by
          have hxUF : x ∈ V ∩ F' := by
            constructor
            · refine' h.2.2.2.1 _
              assumption
            · simp only [Set.mem_iInter, Subtype.forall]
              intro a b _
              exact b.2
          have hUF : V ∩ F' ∈ { Z : Set α | IsClopen Z ∧ x ∈ Z } := ⟨hFU, hxUF⟩
          unfold Quasicomponent
          intro x1 hx1
          rw [Set.mem_iInter] at hx1
          exact hx1 ⟨V ∩ F', hUF⟩
        have hXQ : X₁ ∩ Quasicomponent x = ∅ :=
          by
          apply Set.eq_empty_of_subset_empty
          intro a ha
          have ha' := Set.inter_subset_inter_right X₁ hQUF ha
          have ha'' := Set.inter_subset_inter_left (V ∩ F') h.2.2.1 ha'
          rw [← Set.inter_assoc] at ha''
          rw [Set.disjoint_iff_inter_eq_empty.mp h.2.2.2.2] at ha''
          exact ha''.1
        intro a ha
        cases hX₁uX₂ ha
        swap
        · assumption
        exfalso
        refine' (Set.ext_iff.mp hXQ a).mp ⟨_, ha⟩
        assumption

instance totally_separated_of_totally_disconnected_compact_hausdorff (α : Type _)
    [TopologicalSpace α] [hc : CompactSpace α] [htd : TotallyDisconnectedSpace α] [hh : T2Space α] :
    TotallySeparatedSpace α := by
  fconstructor
  intro x _ y _ hxy
  have hcompx : connectedComponent x = {x} :=
    totallyDisconnectedSpace_iff_connectedComponent_singleton.mp htd x
  have hcqx : connectedComponent x = Quasicomponent x :=
    quasicomponentEqComponentOfCompactSpace x
  rw [hcompx] at hcqx
  obtain ⟨V, Y, h⟩ := t2_separation hxy
  let S := { s : Set α // IsClopen s ∧ x ∈ s }
  let F : S → Set α := fun s => s
  have hF : ∀ s : S, IsClosed (F s) := by
    intro s
    exact s.property.1.2
  have h_inter : (⋂ s : S, F s) ⊆ V := fun a ha =>
    (Set.singleton_subset_iff.mpr h.2.2.1) ((Set.ext_iff.mp hcqx a).mpr ha)
  obtain ⟨S₀, hS₀⟩ := compactFiniteIntersection h.1 hF h_inter
  let U := ⋂ (s ∈ S₀), (fun s : S => F s) s
  have hU : IsClopen U := by
    refine' isClopen_biInter_finset _
    intro i _
    exact i.property.1
  have hxU : x ∈ U := by
    simp only [Set.mem_iInter, Subtype.forall]
    intro a b _
    exact b.2
  have hyUc : y ∈ Uᶜ :=
    by
    intro hyU
    have hy₁ := hS₀ hyU
    have hy₂ := h.2.2.2.1
    have : V ∩ Y ⊆ ∅ := Set.subset_empty_iff.mpr (Set.disjoint_iff_inter_eq_empty.mp h.2.2.2.2)
    exact this ⟨hy₁, hy₂⟩
  have huniv : Set.univ ⊆ U ∪ Uᶜ := (Set.Subset.antisymm_iff.mp (Set.union_compl_self U)).2
  have hdisjoint : Disjoint U (Uᶜ) := Set.disjoint_iff_inter_eq_empty.mpr (Set.inter_compl_self U)
  use U
  use Uᶜ
  exact ⟨hU.1, isOpen_compl_iff.mpr hU.2, hxU, hyUc, huniv, hdisjoint⟩
