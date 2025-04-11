import Mathlib.Combinatorics.MyGraph.Finite

#check Subtype.ext_val
universe u
variable {V : Type*}

/-- The type of graphs that have all vertices -/
abbrev FullGraph (V : Type*) := {G : MyGraph V // G.verts = Set.univ}

@[simps]
def FullGraph.mk {V : Type*} (adj : V → V → Prop) (hs : Symmetric adj)
    (hi : Irreflexive adj) : FullGraph V :=
  ⟨⟨Set.univ, adj, fun h ↦ by trivial, hs, hi⟩, rfl⟩

namespace FullGraph

@[coe] def toMyGraph : FullGraph V → MyGraph V := Subtype.val

instance  : Coe (FullGraph V) (MyGraph V) := ⟨toMyGraph⟩

initialize_simps_projections MyGraph (Adj → adj)

/-- The graph with no edges on a given vertex type `V`. -/
@[simp]
def emptyGraph (V : Type u) : FullGraph V :=
  FullGraph.mk (fun _ _ ↦ False) (fun _ _ h ↦ False.elim h) (fun _ a ↦ False.elim a)


open MyGraph

abbrev Adj (G : FullGraph V) : V → V → Prop :=
  G.val.Adj

lemma ext_iff {G H : FullGraph V} : G = H ↔ G.Adj = H.Adj := by
  rw [Subtype.ext_iff, MyGraph.ext_iff, G.2, H.2]
  simp

@[ext]
alias ⟨_, ext⟩ := ext_iff

lemma emptyGraph_adj {u v : V} : (emptyGraph V).Adj u v ↔ False := Iff.rfl

lemma coe_adj {G : FullGraph V} {v w : V} : (G : MyGraph V).Adj v w ↔ G.Adj v w := Iff.rfl

lemma coe_adj' {G : FullGraph V} {v w : V} :  G.Adj v w ↔ (G : MyGraph V).Adj v w := Iff.rfl

@[simp]
lemma coe_verts {G : FullGraph V} : (G : MyGraph V).verts = Set.univ  := G.2

@[simp]
lemma mem_verts {G : FullGraph V} (v : V) : v ∈ (G : MyGraph V).verts := by simp

lemma le_iff {G H : FullGraph V} : G ≤ H ↔ G.Adj ≤ H.Adj := by
  constructor <;> intro h
  · exact h.2
  · exact ⟨by rw [G.2, H.2], h⟩

lemma le_iff_coe_adj_le {G H : FullGraph V} :
    G ≤ H ↔ (G : MyGraph V).Adj ≤ (H : MyGraph V).Adj := le_iff

abbrev edgeSet (G : FullGraph V) := G.val.edgeSet


lemma edgeSet_coe {G : FullGraph V} : (G : MyGraph V).edgeSet = G.edgeSet:= rfl

@[norm_cast]
lemma mem_edgeSet_coe {G : FullGraph V} {e : (Sym2 V)} :
  e ∈ (G : MyGraph V).edgeSet ↔ e ∈ G.edgeSet  := by
  rw [edgeSet]
  rfl

@[simp 500]
lemma mem_edgeSet {G : FullGraph V} {u v : V} : s(u, v) ∈ G.edgeSet ↔ G.Adj u v := Iff.rfl

@[simp]
lemma edgeSet_subset_edgeSet {G H : FullGraph V} :
    G.edgeSet ⊆ H.edgeSet ↔ G ≤ H := by
  rw [le_iff, MyGraph.edgeSet_subset_edgeSet]

@[simp]
lemma edgeSet_ssubset_edgeSet {G H : FullGraph V} :
    G.edgeSet ⊂ H.edgeSet ↔ G < H := by
  constructor <;> intro h
  · apply lt_of_le_of_ne (edgeSet_subset_edgeSet.1 h.1)
    obtain ⟨e, he⟩ := Set.exists_of_ssubset h
    intro hf; apply he.2 <| hf.symm ▸ he.1
  · constructor
    · apply edgeSet_subset_edgeSet_of_le h.1
    · intro hf
      apply h.not_le <| edgeSet_subset_edgeSet.1 hf

@[norm_cast]
lemma coe_coe {G : FullGraph V} : ⟨(G : MyGraph V), G.prop⟩ = G := by
  ext u v
  nth_rw 2 [coe_adj']

theorem adj_injective : Function.Injective (Adj : FullGraph V → V → V → Prop) :=
  fun _ _ => FullGraph.ext

@[simp]
theorem adj_inj {G H : FullGraph V} : G.Adj = H.Adj ↔ G = H :=
  adj_injective.eq_iff

@[simp]
theorem edgeSet_inj {G H : FullGraph V} : G.edgeSet = H.edgeSet ↔ G = H := by
  rw [← adj_inj, edgeSet_eq_iff]

instance : Max (FullGraph V) :=
  ⟨fun G₁ G₂ => ⟨G₁ ⊔ G₂, by rw [sup_verts]; simp⟩⟩

instance : Min (FullGraph V) :=
  ⟨fun G₁ G₂ => ⟨G₁ ⊓ G₂, by rw [inf_verts]; simp⟩⟩

instance instSDiff : SDiff (FullGraph V) where
  sdiff G₁ G₂ := ⟨G₁ \ G₂, G₁.2⟩

instance hasCompl : HasCompl (FullGraph V) where
  compl G := ⟨Gᶜ, by rw [compl_verts]; simp⟩

instance instTop : Top (FullGraph V)  where top := ⟨⊤, rfl⟩

instance instBot : Bot (FullGraph V)  where bot := ⟨emptyGraph V, rfl⟩

@[simp]
lemma bot_adj {u v : V} : (⊥ : FullGraph V).Adj u v ↔ False :=
  emptyGraph_adj

lemma eq_bot_iff {G : FullGraph V} : G = ⊥ ↔ ∀ {u v}, ¬ G.Adj u v := by
  constructor <;> intro h
  · rw [h]; simp
  · rw [ext_iff] ; ext u v ; simpa using h

instance : SupSet (FullGraph V) where sSup s := ⟨toSpanning (sSup (toMyGraph '' s)),
  by rw [toSpanning]⟩

instance : InfSet (FullGraph V) where sInf s := ⟨sInf (toMyGraph '' s), by
  ext; simp only [sInf_verts, Set.mem_image, Subtype.exists, Set.iInter_exists, Set.mem_iInter,
    and_imp, Set.mem_univ, iff_true]
  intro x h h1 h2 h3; rw [MyGraph.ext_iff, coe_verts] at h3; rw [←h3.1]; trivial⟩


lemma coe_top : (⊤ : FullGraph V) = (⊤ : MyGraph V) := rfl


lemma coe_sup (G₁ G₂ : FullGraph V) : ↑(G₁ ⊔ G₂) = (G₁ ⊔ G₂ : MyGraph V) := rfl


lemma coe_inf (G₁ G₂ : FullGraph V) : ↑(G₁ ⊓ G₂) = (G₁ ⊓ G₂ : MyGraph V) := rfl


lemma coe_sdiff (G₁ G₂ : FullGraph V) : ↑(G₁ \ G₂) = (G₁ \ G₂ : MyGraph V) := rfl


lemma coe_compl (G : FullGraph V) : Gᶜ = (Gᶜ : MyGraph V) := rfl

@[simp]
lemma sup_adj  {u v : V} {G₁ G₂ : FullGraph V} : (G₁ ⊔ G₂).Adj u v ↔ G₁.Adj u v ∨ G₂.Adj u v := by
  simp [coe_adj', coe_sup]

@[simp]
lemma inf_adj  {u v : V} {G₁ G₂ : FullGraph V} : (G₁ ⊓ G₂).Adj u v ↔ G₁.Adj u v ∧ G₂.Adj u v := by
  simp [coe_adj', coe_inf]

@[simp]
lemma sdiff_adj  {u v : V} {G₁ G₂ : FullGraph V} :
    (G₁ \ G₂).Adj u v ↔ G₁.Adj u v ∧ ¬ G₂.Adj u v := by simp [coe_adj', coe_sdiff]

@[simp]
lemma compl_adj  {u v : V} {G₁ : FullGraph V} :
    (G₁ᶜ).Adj u v ↔ u ≠ v ∧ ¬G₁.Adj u v := by simp [coe_adj', coe_compl]

lemma coe_sInf (s : Set (FullGraph V)) : ↑(sInf s) = (sInf (toMyGraph '' s)) := rfl

lemma coe_sSup (s : Set (FullGraph V)) : ↑(sSup s) = (toSpanning (sSup (toMyGraph '' s))) := rfl

lemma coe_sSup_of_non_empty {s : Set (FullGraph V)} (h : s.Nonempty) :
  ↑(sSup s) = ((sSup (toMyGraph '' s))) := by
  rw [coe_sSup, toSpanning_eq_iff]
  ext x; simp only [sSup_verts, Set.mem_image, Subtype.exists, Set.iUnion_exists, Set.mem_iUnion,
    exists_prop, exists_and_right, Set.mem_univ, iff_true]
  obtain ⟨G, h⟩ := h
  use G, ⟨G.val, coe_verts, by simpa using h⟩
  simp

@[simp]
lemma sSup_of_empty {s : Set (FullGraph V)} (h : ¬ s.Nonempty) :
    (sSup s) = ⊥ := by
  rw [eq_bot_iff]
  intro u v hf
  rw [coe_adj', coe_sSup, toSpanning_adj, sSup_adj] at hf
  obtain ⟨G, ⟨_, h1, _, _, _, _⟩, h'⟩ := hf
  exact h ⟨_, h1⟩

@[simp]
theorem sSup_adj {s : Set (FullGraph V)} {a b : V} : (sSup s).Adj a b ↔ ∃ G ∈ s, Adj G a b := by
  by_cases hs : s.Nonempty
  · rw [coe_adj', coe_sSup_of_non_empty hs]
    constructor <;> intro h
    · simp only [MyGraph.sSup_adj, Set.mem_image, Subtype.exists] at h
      obtain ⟨G₁, ⟨G₂, h1, h2, h3⟩, h⟩ := h
      use ⟨G₂, h1⟩, h2
      rwa [coe_adj', h3]
    · simp only [MyGraph.sSup_adj, Set.mem_image, Subtype.exists]
      obtain ⟨G,hG, h1⟩ := h
      use G.toMyGraph, ⟨G.toMyGraph, coe_verts, by simpa [coe_coe] using hG⟩
      simpa
  · rw [sSup_of_empty hs]
    simp only [bot_adj, Subtype.exists, false_iff, not_exists, not_and]
    intro G hG h hf
    exact hs ⟨_, h⟩

@[simp]
theorem sInf_adj {s : Set (FullGraph V)} {a b : V} :
    (sInf s).Adj a b ↔ (∀ G ∈ s, Adj G a b) ∧ a ≠ b := by
  simp_rw [coe_adj', coe_sInf, MyGraph.sInf_adj, Set.mem_image, Subtype.exists,
    forall_exists_index, and_imp]
  constructor <;> intro h
  · refine ⟨?_, h.2⟩
    intro G hG
    apply h.1 G.toMyGraph G.toMyGraph coe_verts (by simpa) (by norm_cast)
  · refine ⟨?_, h.2⟩
    intro G G' hG' hs heq
    exact heq ▸ (h.1 _ hs)

variable {ι : Type*} {a b : V}
@[simp]
theorem iSup_adj {f : ι → FullGraph V} : (⨆ i, f i).Adj a b ↔ ∃ i, (f i).Adj a b := by
  simp [iSup]

@[simp]
theorem iInf_adj {f : ι → FullGraph V} : (⨅ i, f i).Adj a b ↔ (∀ i, (f i).Adj a b) ∧ a ≠ b := by
  simp [iInf]

/-- For graphs `G`, `H`, `G ≤ H` iff `∀ a b, G.Adj a b → H.Adj a b`. -/
instance distribLattice : DistribLattice (FullGraph V) :=
  Subtype.coe_injective.distribLattice _ coe_sup coe_inf

instance completeAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra (FullGraph V) :=
  { FullGraph.distribLattice with
    le := (· ≤ ·)
    sup := (· ⊔ ·)
    inf := (· ⊓ ·)
    compl := HasCompl.compl
    sdiff := (· \ ·)
    top := ⊤
    bot := ⊥
    le_top := fun x ↦ le_iff.2 (fun u v h ↦ h.ne)
    bot_le := fun x ↦ le_iff.2 (fun u v h ↦ h.elim)
    sdiff_eq := fun x y => by
      apply FullGraph.ext
      ext v w
      refine ⟨fun h => ⟨h.1, ⟨?_, ⟨h.2, by simp, by simp⟩⟩⟩, fun h => ⟨h.1, h.2.2.1⟩⟩
      rintro rfl
      apply MyGraph.loopless (x \ y).val _ h
    inf_compl_le_bot := by
      intro x; rw [le_iff]; intro u v h;
      rw [inf_adj] at h
      apply h.2.2.1 h.1
    top_le_sup_compl := by
      intro x; rw [le_iff]; intro u v h';
      rw [coe_adj', coe_top, top_adj] at h'
      by_cases h : x.Adj u v
      · exact Or.inl h
      · exact Or.inr ⟨h', h, by simp, by simp⟩
    sSup := sSup
    le_sSup := by
      intro s G hs
      rw [le_iff_coe_adj_le, coe_sSup_of_non_empty ⟨_, hs⟩]
      intro u v h
      simp only [MyGraph.sSup_adj, Set.mem_image, Subtype.exists]
      exact ⟨G.toMyGraph, ⟨G.toMyGraph, coe_verts, by simpa using hs, by norm_cast⟩, h⟩
    sSup_le := by
      intro s G hG
      by_cases hs : s.Nonempty
      · rw [le_iff_coe_adj_le, coe_sSup_of_non_empty hs]
        intro u v h
        simp only [MyGraph.sSup_adj, Set.mem_image, Subtype.exists] at h
        obtain ⟨G₁, ⟨G₂, h1, h2, h3⟩, h⟩ := h
        apply le_iff_coe_adj_le.1 <| hG _ h2
        rwa [h3]
      · rw [sSup_of_empty hs]
        exact le_iff.2 (fun u v h ↦ h.elim)
    sInf := sInf
    sInf_le := by
      intro s G hs
      rw [le_iff_coe_adj_le, coe_sInf]
      intro u v h
      simp only [MyGraph.sInf_adj, Set.mem_image, Subtype.exists] at h
      apply h.1 G.toMyGraph
      use G.toMyGraph, coe_verts, by simpa using hs
      norm_cast
    le_sInf := by
      intro s G hs
      rw [le_iff_coe_adj_le, coe_sInf]
      intro u v h
      simp only [MyGraph.sInf_adj, Set.mem_image, Subtype.exists, forall_exists_index, and_imp]
      exact ⟨fun _ _ _ h2 h3 ↦ h3 ▸ (le_iff_coe_adj_le.1 <| hs _ h2) _ _ h, h.ne⟩
    iInf_iSup_eq := fun f => by
      apply FullGraph.ext
      ext u v
      simp [iInf_adj, iSup_adj, Classical.skolem]}


section deleteEdges

abbrev deleteEdges (G : FullGraph V) (s : Set (Sym2 V)) : FullGraph V :=
    ⟨G.toMyGraph.deleteEdges s, by simp⟩

variable {G G' : FullGraph V} {s : Set (Sym2 V)}

@[norm_cast]
lemma coe_deleteEdges : G.deleteEdges s = (G : MyGraph V).deleteEdges s := rfl

@[simp]
theorem deleteEdges_adj {v w : V} : (G.deleteEdges s).Adj v w ↔ G.Adj v w ∧ ¬s(v, w) ∈ s :=
  Iff.rfl

instance instDecidableRel_deleteEdges_adj (G : FullGraph V) (s : Set (Sym2 V))
   [DecidableRel G.Adj] [DecidablePred (· ∈ s)]
   : DecidableRel (G.deleteEdges s).Adj :=
  fun u v => by rw [deleteEdges_adj]; infer_instance

@[simp] lemma deleteEdges_edgeSet (G G' : FullGraph V) : G.deleteEdges G'.edgeSet = G \ G' := by
  ext; simp_rw [deleteEdges_adj, sdiff_adj]
  simp only [coe_adj, MyGraph.mem_edgeSet]

theorem edgeSet_deleteEdges (s : Set (Sym2 V)) : (G.deleteEdges s).edgeSet = G.edgeSet \ s := by
  ext e; cases e; simp_rw [mem_edgeSet, deleteEdges_adj, Set.mem_diff, mem_edgeSet]

@[simp]
theorem deleteEdges_deleteEdges (s s' : Set (Sym2 V)) :
    (G'.deleteEdges s).deleteEdges s' = G'.deleteEdges (s ∪ s') := by
  ext; simp [and_assoc, not_or]

@[simp]
theorem deleteEdges_empty : G'.deleteEdges ∅ = G' := by
  ext; simp

@[simp] lemma deleteEdges_univ : G.deleteEdges Set.univ = ⊥ := by
  rw [eq_bot_iff]
  intro x y h
  simp at h

@[simp]
theorem deleteEdges_disjoint (h : Disjoint s G'.edgeSet) : G'.deleteEdges s = G' := by
  ext x y
  simp only [deleteEdges_adj, and_iff_left_iff_imp]
  intro h' hf
  apply h.not_mem_of_mem_left hf h'


@[simp]
theorem deleteEdges_le (s : Set (Sym2 V)) : G'.deleteEdges s ≤ G' := by
  apply le_iff.2
  intro u v h
  simpa using h.1

theorem deleteEdges_le_of_le {s s' : Set (Sym2 V)} (h : s ⊆ s') :
    G'.deleteEdges s' ≤ G'.deleteEdges s := by
  apply le_iff.2
  intro u v h'; simp only [deleteEdges_adj, le_Prop_eq, and_imp] at *
  exact ⟨h'.1, fun hf ↦ h'.2 (h hf)⟩

@[simp]
theorem deleteEdges_inter_edgeSet_left_eq :
    G'.deleteEdges (G'.edgeSet ∩ s) = G'.deleteEdges s := by
  ext ; simp +contextual [imp_false]

@[simp]
theorem deleteEdges_inter_edgeSet_right_eq :
    G'.deleteEdges (s ∩ G'.edgeSet) = G'.deleteEdges s := by
  ext ; simp +contextual [imp_false]

theorem deleteEdges_sdiff_eq_of_le {H : FullGraph V} (h : H ≤ G) :
    G.deleteEdges (G.edgeSet \ H.edgeSet) = H := by
  ext u v
  simp_rw [deleteEdges_adj, Set.mem_diff, mem_edgeSet,not_and, not_not]
  constructor <;> intro h'
  · exact h'.2 h'.1
  · exact ⟨le_iff.1 h _ _ h', fun _ ↦ h'⟩



end deleteEdges

section fromEdgeSet
variable {G G' : FullGraph V} {s t : Set (Sym2 V)}

abbrev fromEdgeSet (s : Set (Sym2 V)) : FullGraph V :=
    ⟨(MyGraph.fromEdgeSet s).toSpanning, by simp⟩

-- START HERE
end fromEdgeSet

section Finite

variable {G G₁ G₂ : FullGraph V} [Fintype G.edgeSet] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]

abbrev edgeFinset (G : FullGraph V) [Fintype G.edgeSet] := G.val.edgeFinset

theorem edgeFinset_inj : G₁.edgeFinset = G₂.edgeFinset ↔ G₁ = G₂ := by simp

theorem edgeFinset_subset_edgeFinset : G₁.edgeFinset ⊆ G₂.edgeFinset ↔ G₁ ≤ G₂ := by simp

theorem edgeFinset_ssubset_edgeFinset : G₁.edgeFinset ⊂ G₂.edgeFinset ↔ G₁ < G₂ := by simp

@[gcongr] alias ⟨_, edgeFinset_mono⟩ := edgeFinset_subset_edgeFinset

alias ⟨_, edgeFinset_strict_mono⟩ := edgeFinset_ssubset_edgeFinset

attribute [mono] edgeFinset_mono edgeFinset_strict_mono

end Finite

variable {G G₁ G₂ : FullGraph V}

@[simp]
lemma disjoint_edgeSet : Disjoint G₁.edgeSet G₂.edgeSet ↔ Disjoint G₁ G₂ := by
  nth_rw 2 [disjoint_iff_inf_le]
  constructor <;> intro h
  · apply le_iff.2
    intro u v; rw [bot_adj, coe_adj', coe_inf, MyGraph.inf_adj]
    simp only [coe_adj, le_Prop_eq, imp_false, not_and]
    intro hf
    simp only [Set.subset_empty_iff] at h
    rw [← mem_edgeSet]
    apply h.not_mem_of_mem_left (mem_edgeSet.1 hf)
  · rw [Set.disjoint_iff]
    intro e ⟨h1, h2⟩
    cases e with
    | h u v =>
      rw [mem_edgeSet] at *
      exfalso
      rw [le_iff] at h
      exact h _ _ ⟨h1, h2⟩

@[simp] lemma edgeSet_eq_empty : G.edgeSet = ∅ ↔ G = ⊥ := by
  rw [eq_bot_iff]
  constructor <;> intro h
  · intro u v h'
    exact Set.not_mem_empty _ (h ▸ mem_edgeSet.2 h')
  · contrapose! h
    obtain ⟨e, he⟩ := h
    cases e with
    | h u v => exact ⟨_,_, mem_edgeSet.1 he⟩

@[simp] lemma edgeSet_nonempty : G.edgeSet.Nonempty ↔ G ≠ ⊥ := by
  rw [Set.nonempty_iff_ne_empty, edgeSet_eq_empty.ne]

/-- This lemma, combined with `edgeSet_sdiff` and `edgeSet_from_edgeSet`,
allows proving `(G \ from_edgeSet s).edge_set = G.edgeSet \ s` by `simp`. -/
@[simp]
theorem edgeSet_sdiff_sdiff_isDiag (G : FullGraph V) (s : Set (Sym2 V)) :
    G.edgeSet \ (s \ { e | e.IsDiag }) = G.edgeSet \ s := by
  ext e
  simp only [Set.mem_diff, Set.mem_setOf_eq, not_and, not_not, and_congr_right_iff]
  intro h
  cases e with
  | h u v =>
    rw [mem_edgeSet] at h
    constructor <;> intro h1
    · intro hf
      have := h1 hf
      simp only [Sym2.isDiag_iff_proj_eq] at this
      exact G.toMyGraph.loopless _ (this ▸ h)
    · intro hf
      contradiction


end FullGraph
