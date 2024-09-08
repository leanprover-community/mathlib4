import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Set.Card

namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

def universalVerts (G : SimpleGraph V) : Set V := {v : V | ∀ w, v ≠ w → G.Adj w v}

lemma isClique_universalVerts (G : SimpleGraph V) : G.IsClique G.universalVerts := by
  intro x _ y hy hxy
  exact hy x hxy.symm

def deleteUniversalVerts (G : SimpleGraph V) : Subgraph G := ((⊤ : Subgraph G).deleteVerts (universalVerts G))

@[simp]
lemma deleteUniversalVerts_verts : G.deleteUniversalVerts.verts = Set.univ \ G.universalVerts := by
  unfold deleteUniversalVerts
  simp only [Subgraph.induce_verts, Subgraph.verts_top]

def oddVerts (G : SimpleGraph V) : Set V := Subtype.val '' ((fun c ↦ c.exists_rep.choose) '' {(c : ConnectedComponent G.deleteUniversalVerts.coe) | Odd (c.supp.ncard)})

lemma oddVerts_subset_deleteUniversalVerts : G.oddVerts ⊆ G.deleteUniversalVerts.verts := by
  intro _ hv
  rw [oddVerts, Set.mem_image] at hv
  obtain ⟨v, heq⟩ := hv
  rw [← heq.2]
  exact v.2

lemma odd_connectedComponent_of_oddVert {v : V} (h : v ∈ oddVerts G) :
  Odd ((G.deleteUniversalVerts.coe.connectedComponentMk ⟨v, oddVerts_subset_deleteUniversalVerts h⟩).supp.ncard) := by
    simp_rw [oddVerts, Set.mem_image] at h
    obtain ⟨w, ⟨⟨c, hc⟩, hw⟩⟩ := h
    rw [@Set.mem_setOf] at hc
    have : G.deleteUniversalVerts.coe.connectedComponentMk w = c := by
      rw [← hc.2]
      exact c.exists_rep.choose_spec
    rw [(SetCoe.ext hw.symm : ⟨v, oddVerts_subset_deleteUniversalVerts h⟩ = w), this]
    exact hc.1

lemma deleteVerts_verts_notmem_deleted {u : Set V} (a : ((⊤ : G.Subgraph).deleteVerts u).verts) : a.val ∉ u := a.prop.2


lemma disjoint_oddVerts_universalVerts : Disjoint G.oddVerts G.universalVerts := by
  rw [@Set.disjoint_left]
  intro v hv
  rw [oddVerts, Set.mem_image] at hv
  simp_rw [Set.mem_image] at hv
  obtain ⟨w, hw⟩ := hv
  obtain ⟨c, hc⟩ := hw.1
  rw [← hw.2, ← hc.2]
  exact deleteVerts_verts_notmem_deleted _

lemma aux {x : V} {cx : G.deleteUniversalVerts.coe.ConnectedComponent} (h : cx.exists_rep.choose.val = x) (hx : x ∈ G.deleteUniversalVerts.verts): G.deleteUniversalVerts.coe.connectedComponentMk ⟨x, hx⟩ = cx := by
    rw [← @ConnectedComponent.mem_supp_iff,← cx.exists_rep.choose_spec]
    subst h
    simp only [Subtype.coe_eta, ConnectedComponent.mem_supp_iff]
    unfold connectedComponentMk
    rfl

lemma compInj : Function.Injective (fun (v : G.oddVerts) => (G.deleteUniversalVerts.coe.connectedComponentMk ⟨v.1, oddVerts_subset_deleteUniversalVerts v.2⟩)) := by
    intro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    dsimp at *
    have hx' := oddVerts_subset_deleteUniversalVerts hx
    have hy' := oddVerts_subset_deleteUniversalVerts hy
    rw [oddVerts, ← Set.image_comp, Set.mem_image] at hx hy
    obtain ⟨cx, hcx⟩ := hx
    obtain ⟨cy, hcy⟩ := hy
    rw [aux hcx.2 hx', aux hcy.2 hy'] at hxy
    rw [Subtype.mk_eq_mk, ← hcx.2, ← hcy.2, hxy]

lemma not_in_universalVerts {v : V} (K : G.deleteUniversalVerts.coe.ConnectedComponent)
    (h : v ∈ Subtype.val '' K.supp) : v ∉ G.universalVerts := by
    intro hv
    rw [Set.mem_image] at h
    obtain ⟨v', hv'⟩ := h
    have := v'.2
    simp only [Subgraph.induce_verts, Subgraph.verts_top, Set.mem_diff] at this
    rw [hv'.2] at this
    exact this.2 hv

lemma memSuppOddIsRep {v : V} (K : G.deleteUniversalVerts.coe.ConnectedComponent)
  (h : v ∈ Subtype.val '' K.supp) (h' : v ∈ G.oddVerts) : K.exists_rep.choose.val = v := by
  unfold oddVerts at h'
  rw [Set.mem_image] at h'
  simp_rw [Set.mem_image] at h'
  obtain ⟨x, ⟨⟨c, hc⟩, hx⟩⟩ := h'
  rw [← hx, ← hc.2] at h ⊢
  rw [Subtype.val_injective.mem_set_image, SimpleGraph.ConnectedComponent.mem_supp_iff] at h
  unfold connectedComponentMk at h
  rw [c.exists_rep.choose_spec] at h
  rw [h]

lemma repMemOdd {K : G.deleteUniversalVerts.coe.ConnectedComponent}
    (h : Odd K.supp.ncard) : K.exists_rep.choose.val ∈ G.oddVerts := by
    unfold oddVerts
    rw [Set.mem_image]
    simp_rw [Set.mem_image]
    use K.exists_rep.choose
    refine ⟨?_, rfl⟩
    use K
    exact ⟨h, rfl⟩

lemma subgraph_coe (H : Subgraph G) {x y : H.verts} (h : H.coe.Adj x y) : G.Adj x.val y.val := h.adj_sub

-- Can be more generic
lemma isClique_lifts {K : G.deleteUniversalVerts.coe.ConnectedComponent}
    (h : G.deleteUniversalVerts.coe.IsClique K.supp) : G.IsClique (Subtype.val '' K.supp) := by
  intro x hx y hy hxy
  rw [Set.mem_image] at hx hy
  obtain ⟨x', hx'⟩ := hx
  obtain ⟨y', hy'⟩ := hy
  rw [← hx'.2, ← hy'.2] at hxy ⊢
  have := h hx'.1 hy'.1 (fun a => hxy (congrArg Subtype.val a))
  exact subgraph_coe G.deleteUniversalVerts this


theorem tutte_part' [Fintype V] [Inhabited V] [DecidableEq V] [DecidableRel G.Adj]
  (hveven : Even (Fintype.card V))
  (h : {c : G.deleteUniversalVerts.coe.ConnectedComponent | Odd (c.supp.ncard)}.ncard ≤ G.universalVerts.ncard)
  (h' : ∀ (K : G.deleteUniversalVerts.coe.ConnectedComponent), G.deleteUniversalVerts.coe.IsClique K.supp) :
    ∃ (M : Subgraph G), M.IsPerfectMatching := by
  classical
  simp only [← Set.Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at h

  have ⟨f, hf⟩ := Classical.inhabited_of_nonempty (Function.Embedding.nonempty_of_card_le h)

  have mem {v : V} (h : v ∈ G.oddVerts) : G.deleteUniversalVerts.coe.connectedComponentMk ⟨v, oddVerts_subset_deleteUniversalVerts h⟩ ∈ {c | Odd (Fintype.card ↑c.supp)} := by
    simpa [← Set.Nat.card_coe_set_eq, Nat.card_eq_fintype_card] using odd_connectedComponent_of_oddVert h


  let g : V → V := fun v ↦ if h : v ∈ G.oddVerts then f ⟨(G.deleteUniversalVerts.coe.connectedComponentMk ⟨v, oddVerts_subset_deleteUniversalVerts h⟩), mem h⟩ else Classical.arbitrary V

  have gMemS {v : V} (h : v ∈ G.oddVerts) : (g v) ∈ G.universalVerts := by
    unfold_let g
    dsimp
    split_ifs
    apply Subtype.coe_prop

  have hdg : Disjoint G.oddVerts (g '' G.oddVerts) := by
    rw [@Set.disjoint_left]
    intro v hv hgv
    apply Set.disjoint_left.mp disjoint_oddVerts_universalVerts hv
    rw [Set.mem_image] at hgv
    obtain ⟨v', hv'⟩ := hgv
    rw [← hv'.2]
    exact gMemS hv'.1

  have gInjOn : Set.InjOn g G.oddVerts := by
    unfold_let g
    dsimp
    rw [Set.injOn_iff_injective, Set.restrict_dite]
    intro x y hxy
    simp only at hxy
    have := hf <| Subtype.val_injective hxy
    rw [Subtype.mk.injEq] at this
    exact compInj this

  have hadj : ∀ v ∈ G.oddVerts, G.Adj v (g v) := by
    intro v hv
    have := gMemS hv
    rw [universalVerts, @Set.mem_setOf] at this
    apply this v
    intro h
    exact Set.disjoint_left.mp disjoint_oddVerts_universalVerts hv (h ▸ gMemS hv)

  let M1 : Subgraph G := Subgraph.ofFunction g hadj

  have hM1 : M1.IsMatching := by
    unfold_let M1
    exact Subgraph.isMatching_ofFunction g hadj gInjOn hdg

  have evenKsubM1 (K : G.deleteUniversalVerts.coe.ConnectedComponent) : Even ((Subtype.val '' K.supp) \ M1.verts).ncard := by
    by_cases h : Even (Subtype.val '' K.supp).ncard
    · have : Subtype.val '' K.supp \ M1.verts = Subtype.val '' K.supp := by
        unfold_let M1
        unfold oddVerts
        ext v
        refine ⟨fun hv ↦ hv.1, ?_⟩
        intro hv
        apply Set.mem_diff_of_mem hv
        intro hv'
        simp only [Subgraph.ofFunction_verts, Set.mem_union, Set.mem_image,
          Set.mem_setOf_eq, exists_exists_and_eq_and] at hv'
        cases' hv' with hl hr
        · obtain ⟨a, ha⟩ := hl
          have hc1 := a.exists_rep.choose_spec
          rw [← ha.2, ← hc1, Subtype.val_injective.mem_set_image, SimpleGraph.ConnectedComponent.mem_supp_iff] at hv
          rw [Nat.odd_iff_not_even] at ha
          apply ha.1
          have hc2 := (G.deleteUniversalVerts.coe.connectedComponentMk (a.exists_rep).choose).exists_rep.choose_spec
          rw [← hc1, ← hc2]
          rw [← hv, Set.ncard_image_of_injective _ Subtype.val_injective] at h
          exact h
        · obtain ⟨a, ha⟩ := hr
          rw [← ha.2] at hv
          exact not_in_universalVerts _ hv (gMemS (repMemOdd ha.1))
      rw [this]
      exact h
    · rw [← @Nat.odd_iff_not_even] at h
      have kMem : K.exists_rep.choose.val ∉ (Subtype.val '' K.supp \ M1.verts) := by
        rw [@Set.mem_diff]
        push_neg
        intro _
        unfold_let M1
        simp only [ne_eq, Subgraph.induce_verts, Subgraph.verts_top, Subgraph.ofFunction_verts,
          Set.mem_union, Set.mem_image]
        left
        exact repMemOdd (Set.ncard_image_of_injective _ Subtype.val_injective ▸ h)
      have : insert K.exists_rep.choose.val (Subtype.val '' K.supp \ M1.verts) = Subtype.val '' K.supp := by
        ext v
        simp only [Subgraph.induce_verts, Subgraph.verts_top, Set.mem_insert_iff,
          Set.mem_diff]
        constructor
        · intro h
          cases' h with hl hr
          · rw [hl, Subtype.val_injective.mem_set_image]
            exact ConnectedComponent.exists_rep_mem_supp _
          · exact hr.1
        · intro h
          by_cases hc : v = K.exists_rep.choose.val
          · left; exact hc
          · right
            refine ⟨h, ?_⟩
            unfold_let M1
            simp only [Subgraph.ofFunction_verts, Set.mem_union]
            push_neg
            constructor
            · intro h'
              apply hc
              exact (memSuppOddIsRep _ h h').symm
            · intro hv
              rw [Set.mem_image] at hv
              obtain ⟨v', hv'⟩ := hv
              have : v ∈ G.universalVerts := by
                rw [← hv'.2]
                exact gMemS hv'.1
              exact not_in_universalVerts _ h this

      rw [← this] at h

      rw [← Set.Finite.odd_card_insert_iff (Set.toFinite _) kMem]
      exact h
  have compMatching (K : G.deleteUniversalVerts.coe.ConnectedComponent) :
      ∃ M : Subgraph G, M.verts = Subtype.val '' K.supp \ M1.verts ∧ M.IsMatching := by
    have : G.IsClique (Subtype.val '' K.supp \ M1.verts) := (isClique_lifts (h' K)).subset Set.diff_subset
    rw [← isClique_even_iff_matches _ (Set.toFinite _ ) this]
    exact evenKsubM1 K

  let M2 : Subgraph G := (⨆ (K : G.deleteUniversalVerts.coe.ConnectedComponent), (compMatching K).choose)

  have hM2 : M2.IsMatching := by
    apply Subgraph.IsMatching.iSup (fun c => (compMatching c).choose_spec.2)
    intro i j hij
    rw [(compMatching i).choose_spec.2.support_eq_verts, (compMatching j).choose_spec.2.support_eq_verts,
      (compMatching i).choose_spec.1, (compMatching j).choose_spec.1]
    exact Set.disjoint_of_subset (Set.diff_subset) (Set.diff_subset) <| Set.disjoint_image_of_injective Subtype.val_injective (SimpleGraph.pairwise_disjoint_supp_connectedComponent _ hij)

  have disjointM12 : Disjoint M1.verts M2.verts := by
    rw [@Set.disjoint_right]
    intro v hv
    rw [Subgraph.verts_iSup, Set.mem_iUnion] at hv
    obtain ⟨K, hK⟩ := hv
    rw [(compMatching K).choose_spec.1] at hK
    exact hK.2

  have hM12 : (M1 ⊔ M2).IsMatching := by
    apply hM1.sup hM2
    rw [hM1.support_eq_verts, hM2.support_eq_verts]
    exact disjointM12

  have evensubM1M2 : Even ((Set.univ : Set V) \ (M1.verts ∪ M2.verts)).ncard := by
    rw [Set.ncard_diff (by intro v _; trivial), Nat.even_sub (Set.ncard_le_ncard (by intro v _; trivial))]
    rw [Fintype.card_eq_nat_card, ← Set.ncard_univ] at hveven
    simp only [hveven, true_iff]
    rw [Set.ncard_union_eq disjointM12, Nat.even_add, Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
    simp only [iff_true_left hM1.even_card, hM2.even_card]

  have sub : ((Set.univ : Set V) \ (M1.verts ∪ M2.verts)) ⊆ G.universalVerts := by
    rw [@Set.diff_subset_iff]
    intro v _
    by_cases h : v ∈ M1.verts ∪ G.universalVerts
    · cases' h with hl hr
      · left; left; exact hl
      · right; exact hr
    · rw [@Set.mem_union] at h
      push_neg at h
      left; right
      rw [@Subgraph.verts_iSup]
      rw [@Set.mem_iUnion]
      let K := G.deleteUniversalVerts.coe.connectedComponentMk ⟨v, by
        rw [deleteUniversalVerts_verts]
        simp only [Set.mem_diff, Set.mem_univ, true_and]
        exact h.2
        ⟩
      use K
      have := (compMatching K).choose_spec
      rw [this.1]
      simp only [Set.mem_diff, Set.mem_image, ConnectedComponent.mem_supp_iff, Subtype.exists,
        deleteUniversalVerts_verts, Set.mem_univ, true_and, exists_and_right, exists_eq_right,
        exists_prop, and_true]
      exact h.symm
  have subM1M2Clique : G.IsClique ((Set.univ : Set V) \ (M1.verts ∪ M2.verts)) := by
    exact G.isClique_universalVerts.subset sub

  obtain ⟨M3, hM3⟩ := (isClique_even_iff_matches _ (Set.toFinite _ ) subM1M2Clique).mp evensubM1M2

  let Mcon := M1 ⊔ M2 ⊔ M3
  use Mcon

  have MconSpan : Mcon.IsSpanning := by
    rw [@Subgraph.isSpanning_iff]
    rw [Subgraph.verts_sup, Subgraph.verts_sup]
    rw [hM3.1]
    exact Set.union_diff_cancel (by
      intro v _
      trivial)
  refine ⟨?_, MconSpan⟩
  unfold_let Mcon
  exact hM12.sup hM3.2 (by
    rw [hM12.support_eq_verts, hM3.2.support_eq_verts]
    rw [hM3.1]
    simp only [Subgraph.verts_sup]
    exact Disjoint.symm Set.disjoint_sdiff_left
    )
