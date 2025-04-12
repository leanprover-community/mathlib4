import Mathlib.Combinatorics.MyGraph.Finite

universe u
variable {V : Type*}

/-- The type of graphs that have all vertices -/
@[ext]
structure SpanningGraph (V : Type*) extends MyGraph V where
 isSpanning : verts = Set.univ

variable {G : SpanningGraph V}

#check G.Adj

@[simps]
def SpanningGraph.mk' {V : Type*} (adj : V → V → Prop) (hs : Symmetric adj)
    (hi : Irreflexive adj) : SpanningGraph V :=
  ⟨⟨Set.univ, adj, fun h ↦ by trivial, hs, hi⟩, rfl⟩

namespace SpanningGraph


instance  : Coe (SpanningGraph V) (MyGraph V) := ⟨toMyGraph⟩


initialize_simps_projections MyGraph (Adj → adj)

/-- The graph with no edges on a given vertex type `V`. -/
@[simp]
def emptyGraph (V : Type u) : SpanningGraph V :=
  SpanningGraph.mk' (fun _ _ ↦ False) (fun _ _ h ↦ False.elim h) (fun _ a ↦ False.elim a)


open MyGraph
@[ext]
lemma ext' {G H : SpanningGraph V} (h : G.Adj = H.Adj) : G = H  := by
  apply SpanningGraph.ext
  · rw [G.isSpanning, H.isSpanning]
  · exact h

lemma ext_iff' {G H : SpanningGraph V} : G = H ↔ G.Adj = H.Adj  := by
  constructor <;> intro h
  · subst h
    rfl
  · exact ext' h

lemma coe_injective {V : Type*}: Function.Injective (toMyGraph : SpanningGraph V → MyGraph V) := by
  intro _ _ h
  ext; rw [h]

lemma emptyGraph_adj {u v : V} : (emptyGraph V).Adj u v ↔ False := Iff.rfl

lemma coe_adj {G : SpanningGraph V} {v w : V} : (G : MyGraph V).Adj v w ↔ G.Adj v w := Iff.rfl

lemma coe_adj' {G : SpanningGraph V} {v w : V} :  G.Adj v w ↔ (G : MyGraph V).Adj v w := Iff.rfl

@[simp]
lemma coe_verts {G : SpanningGraph V} : (G : MyGraph V).verts = Set.univ  := G.isSpanning

@[simp]
lemma mem_verts {G : SpanningGraph V} (v : V) : v ∈ G.verts := by simp

@[simp]
lemma eq_verts (G H : SpanningGraph V) : G.verts = H.verts  := by
  rw [G.isSpanning, H.isSpanning]

instance : LE (SpanningGraph V) := ⟨fun G₁ G₂ => G₁.toMyGraph ≤ G₂⟩

lemma le_iff {G H : SpanningGraph V} : G ≤ H ↔ G.Adj ≤ H.Adj := by
  constructor <;> intro h
  · exact h.2
  · exact ⟨(eq_verts _ _).le, h⟩

@[simp]
lemma edgeSet_subset_edgeSet {G H : SpanningGraph V} :
    G.edgeSet ⊆ H.edgeSet ↔ G ≤ H := by
  rw [le_iff, MyGraph.edgeSet_subset_edgeSet]


-- @[norm_cast]
-- lemma coe_coe {G : SpanningGraph V} : ⟨(G : MyGraph V), G.prop⟩ = G := by
--   ext u v
--   nth_rw 2 [coe_adj']

-- theorem adj_injective : Function.Injective (MyGraph.Adj : SpanningGraph V → V → V → Prop) :=
--   fun _ _ => SpanningGraph.ext

@[simp]
theorem adj_inj {G H : SpanningGraph V} : G.Adj = H.Adj ↔ G = H := by rw [ext_iff']

@[simp]
theorem edgeSet_inj {G H : SpanningGraph V} : G.edgeSet = H.edgeSet ↔ G = H := by
  rw [← adj_inj, edgeSet_eq_iff]

instance : Max (SpanningGraph V) :=
  ⟨fun G₁ G₂ => ⟨G₁ ⊔ G₂, by rw [sup_verts]; simp⟩⟩

instance : Min (SpanningGraph V) :=
  ⟨fun G₁ G₂ => ⟨G₁ ⊓ G₂, by rw [inf_verts]; simp⟩⟩

instance instSDiff : SDiff (SpanningGraph V) where
  sdiff G₁ G₂ := ⟨G₁ \ G₂, G₁.2⟩

instance hasCompl : HasCompl (SpanningGraph V) where
  compl G := ⟨Gᶜ, by rw [compl_verts]; simp⟩

instance instTop : Top (SpanningGraph V)  where top := ⟨⊤, rfl⟩

@[simp]
lemma top_adj  {u v : V} : (⊤ : SpanningGraph V).Adj u v ↔ u ≠ v := Iff.rfl

instance instBot : Bot (SpanningGraph V)  where bot := ⟨emptyGraph V, rfl⟩

@[simp]
lemma coe_bot_adj : (⊥ : SpanningGraph V).Adj = (⊥ : MyGraph V).Adj := rfl

@[simp]
lemma bot_adj {u v : V} : (⊥ : SpanningGraph V).Adj u v ↔ False :=
  emptyGraph_adj

lemma eq_bot_iff {G : SpanningGraph V} : G = ⊥ ↔ ∀ {u v}, ¬ G.Adj u v := by
  constructor <;> intro h
  · rw [h]; simp
  · ext u v ; simpa using h

instance : SupSet (SpanningGraph V) where sSup s := ⟨toSpanning (sSup (toMyGraph '' s)),
  by rw [toSpanning]⟩

instance : InfSet (SpanningGraph V) where sInf s := ⟨sInf (toMyGraph '' s), by
  ext; simp only [sInf_verts, Set.mem_image, Subtype.exists, Set.iInter_exists, Set.mem_iInter,
    and_imp, Set.mem_univ, iff_true]
  intro x h h1 h2;
  rw [← h2]
  exact mem_verts _⟩

lemma coe_top : (⊤ : SpanningGraph V) = (⊤ : MyGraph V) := rfl

lemma coe_sup (G₁ G₂ : SpanningGraph V) : ↑(G₁ ⊔ G₂) = (G₁ ⊔ G₂ : MyGraph V) := rfl

lemma coe_inf (G₁ G₂ : SpanningGraph V) : ↑(G₁ ⊓ G₂) = (G₁ ⊓ G₂ : MyGraph V) := rfl

lemma coe_sdiff (G₁ G₂ : SpanningGraph V) : ↑(G₁ \ G₂) = (G₁ \ G₂ : MyGraph V) := rfl

lemma coe_compl (G : SpanningGraph V) : Gᶜ = (Gᶜ : MyGraph V) := rfl

@[simp]
lemma sup_adj  {u v : V} {G₁ G₂ : SpanningGraph V} : (G₁ ⊔ G₂).Adj u v ↔ G₁.Adj u v ∨ G₂.Adj u v :=
  Iff.rfl

@[simp]
lemma inf_adj  {u v : V} {G₁ G₂ : SpanningGraph V} : (G₁ ⊓ G₂).Adj u v ↔ G₁.Adj u v ∧ G₂.Adj u v :=
  Iff.rfl

@[simp]
lemma sdiff_adj  {u v : V} {G₁ G₂ : SpanningGraph V} :
    (G₁ \ G₂).Adj u v ↔ G₁.Adj u v ∧ ¬ G₂.Adj u v := Iff.rfl

@[simp]
lemma compl_adj  {u v : V} {G₁ : SpanningGraph V} :
    (G₁ᶜ).Adj u v ↔ u ≠ v ∧ ¬G₁.Adj u v := by simp [coe_adj', coe_compl]

lemma coe_sInf (s : Set (SpanningGraph V)) : ↑(sInf s) = (sInf (toMyGraph '' s)) := rfl

lemma coe_sSup (s : Set (SpanningGraph V)) : ↑(sSup s) = (toSpanning (sSup (toMyGraph '' s))) := rfl

lemma coe_sSup_of_non_empty {s : Set (SpanningGraph V)} (h : s.Nonempty) :
  ↑(sSup s) = ((sSup (toMyGraph '' s))) := by
  rw [coe_sSup, toSpanning_eq_iff]
  ext x; simp only [sSup_verts, Set.mem_image, Subtype.exists, Set.iUnion_exists, Set.mem_iUnion,
    exists_prop, exists_and_right, Set.mem_univ, iff_true]
  obtain ⟨G, h⟩ := h
  use G, ⟨_, h, rfl⟩
  exact mem_verts _

@[simp]
lemma sSup_of_empty {s : Set (SpanningGraph V)} (h : ¬ s.Nonempty) :
    (sSup s) = ⊥ := by
  rw [eq_bot_iff]
  intro u v hf
  rw [coe_adj', coe_sSup, toSpanning_adj, sSup_adj] at hf
  obtain ⟨G, ⟨_, h1, _, _, _, _⟩, h'⟩ := hf
  exact h ⟨_, h1⟩

@[simp]
theorem sSup_adj {s : Set (SpanningGraph V)} {a b : V} : (sSup s).Adj a b ↔ ∃ G ∈ s, Adj G a b := by
  by_cases hs : s.Nonempty
  · rw [coe_adj', coe_sSup_of_non_empty hs]
    constructor <;> intro h
    · simp only [MyGraph.sSup_adj, Set.mem_image, Subtype.exists] at h
      obtain ⟨G₁, ⟨G₂, h1, h2, h3⟩, h⟩ := h
      use G₂
    · simp only [MyGraph.sSup_adj, Set.mem_image, Subtype.exists]
      obtain ⟨G,hG, h1⟩ := h
      use G.toMyGraph, ⟨_, hG, rfl⟩
  · rw [sSup_of_empty hs]
    simp only [bot_adj, Subtype.exists, false_iff, not_exists, not_and]
    intro G hG _
    exact hs ⟨_, hG⟩

@[simp]
theorem sInf_adj {s : Set (SpanningGraph V)} {a b : V} :
    (sInf s).Adj a b ↔ (∀ G ∈ s, Adj G a b) ∧ a ≠ b := by
  simp only [coe_adj', coe_sInf, MyGraph.sInf_adj, Set.mem_image, Subtype.exists,
     forall_exists_index, and_imp]
  constructor <;> intro h
  · refine ⟨?_, h.2⟩
    intro G hG
    exact h.1 G.toMyGraph G hG rfl
  · refine ⟨?_, h.2⟩
    intro G G' hs heq
    exact heq ▸ (h.1 _ hs)

variable {ι : Type*} {a b : V}
@[simp]
theorem iSup_adj {f : ι → SpanningGraph V} : (⨆ i, f i).Adj a b ↔ ∃ i, (f i).Adj a b := by
  simp [iSup]

@[simp]
theorem iInf_adj {f : ι → SpanningGraph V} : (⨅ i, f i).Adj a b ↔ (∀ i, (f i).Adj a b) ∧ a ≠ b := by
  simp [iInf]

/-- For graphs `G`, `H`, `G ≤ H` iff `∀ a b, G.Adj a b → H.Adj a b`. -/
instance distribLattice : DistribLattice (SpanningGraph V) :=
  SpanningGraph.coe_injective.distribLattice _ coe_sup coe_inf

instance completeAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra (SpanningGraph V) :=
  { SpanningGraph.distribLattice with
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
      ext v w
      refine ⟨fun h => ⟨h.1, ⟨?_, ⟨h.2, by simp, by simp⟩⟩⟩, fun h => ⟨h.1, h.2.2.1⟩⟩
      rintro rfl
      apply (x \ y).loopless _ h
    inf_compl_le_bot := by
      intro x; rw [le_iff]; intro u v h;
      rw [inf_adj] at h
      apply h.2.2.1 h.1
    top_le_sup_compl := by
      intro x; rw [le_iff]; intro u v h';
      rw [coe_adj', top_adj] at h'
      by_cases h : x.Adj u v
      · exact Or.inl h
      · exact Or.inr ⟨h', h, by simp, by simp⟩
    sSup := sSup
    le_sSup := by
      intro s G hs
      rw [le_iff, coe_sSup_of_non_empty ⟨_, hs⟩]
      intro u v h
      simp only [MyGraph.sSup_adj, Set.mem_image, Subtype.exists]
      use G.toMyGraph, ⟨G, hs, rfl⟩
    sSup_le := by
      intro s G hG
      by_cases hs : s.Nonempty
      · rw [le_iff, coe_sSup_of_non_empty hs]
        intro u v h
        simp only [MyGraph.sSup_adj, Set.mem_image, Subtype.exists] at h
        obtain ⟨G₁, ⟨G₂, h1, h2, h3⟩, h⟩ := h
        apply le_iff.1 <| hG _ h1
        exact h
      · rw [sSup_of_empty hs]
        exact le_iff.2 (fun u v h ↦ h.elim)
    sInf := sInf
    sInf_le := by
      intro s G hs
      rw [le_iff, coe_sInf]
      intro u v h
      simp only [MyGraph.sInf_adj, Set.mem_image, Subtype.exists] at h
      apply h.1 G.toMyGraph
      use G, hs
    le_sInf := by
      intro s G hs
      rw [le_iff, coe_sInf]
      intro u v h
      simp only [MyGraph.sInf_adj, Set.mem_image, Subtype.exists, forall_exists_index, and_imp]
      refine ⟨fun x y hy heq ↦ heq ▸ (le_iff.1 <| hs _ hy) _ _ h, h.ne⟩
    iInf_iSup_eq := fun f => by
      apply SpanningGraph.ext'
      ext u v
      simp [iInf_adj, iSup_adj, Classical.skolem]}

@[simp]
lemma edgeSet_ssubset_edgeSet {G H : SpanningGraph V} :
    G.edgeSet ⊂ H.edgeSet ↔ G < H := by
  constructor <;> intro h
  · apply lt_of_le_of_ne (edgeSet_subset_edgeSet.1 h.1)
    obtain ⟨e, he⟩ := Set.exists_of_ssubset h
    intro hf; apply he.2 <| hf.symm ▸ he.1
  · constructor
    · apply edgeSet_subset_edgeSet_of_le h.1
    · intro hf
      apply h.not_le <| edgeSet_subset_edgeSet.1 hf


section Maps



variable {V W X : Type*} (G : SpanningGraph V) (G' : SpanningGraph W) {u v : V}


/-- A graph homomorphism is a map on vertex sets that respects adjacency relations.

The notation `G →g G'` represents the type of graph homomorphisms. -/
abbrev Hom := MyGraph.Hom (G : MyGraph V) (G' : MyGraph W)


/-- A graph embedding is an embedding `f` such that for vertices `v w : V`,
`G'.Adj (f v) (f w) ↔ G.Adj v w`. Its image is an induced subgraph of G'.

The notation `G ↪g G'` represents the type of graph embeddings. -/
abbrev Embedding := MyGraph.Embedding (G : MyGraph V) (G' : MyGraph W)


/-- A graph isomorphism is a bijective map on vertex sets that respects adjacency relations.

The notation `G ≃g G'` represents the type of graph isomorphisms.
-/
abbrev Iso := MyGraph.Iso (G : MyGraph V) (G' : MyGraph W)

@[inherit_doc] infixl:50 " →g " => Hom
@[inherit_doc] infixl:50 " ↪g " => Embedding
@[inherit_doc] infixl:50 " ≃g " => Iso




end Maps

section deleteEdges


abbrev deleteEdges (G : SpanningGraph V) (s : Set (Sym2 V)) : SpanningGraph V :=
    ⟨G.toMyGraph.deleteEdges s, by simp⟩

variable {G G' : SpanningGraph V} {s : Set (Sym2 V)}

lemma coe_deleteEdges : G.deleteEdges s = (G : MyGraph V).deleteEdges s := rfl

@[simp]
theorem deleteEdges_adj {v w : V} : (G.deleteEdges s).Adj v w ↔ G.Adj v w ∧ ¬s(v, w) ∈ s :=
  Iff.rfl

instance instDecidableRel_deleteEdges_adj (G : SpanningGraph V) (s : Set (Sym2 V))
   [DecidableRel G.Adj] [DecidablePred (· ∈ s)]
   : DecidableRel (G.deleteEdges s).Adj :=
  fun u v => by rw [deleteEdges_adj]; infer_instance

@[simp] lemma deleteEdges_edgeSet (G G' : SpanningGraph V) : G.deleteEdges G'.edgeSet = G \ G' := by
  ext; simp;

theorem edgeSet_deleteEdges (s : Set (Sym2 V)) : (G.deleteEdges s).edgeSet = G.edgeSet \ s := by
  ext e; cases e; simp

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

-- @[simp]
-- theorem deleteEdges_disjoint (h : Disjoint s G'.edgeSet) : G'.deleteEdges s = G' := by
--   ext x y
--   simp only [deleteEdges_adj, and_iff_left_iff_imp]
--   intro h' hf
--   apply h.not_mem_of_mem_left hf h'


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

theorem deleteEdges_sdiff_eq_of_le {H : SpanningGraph V} (h : H ≤ G) :
    G.deleteEdges (G.edgeSet \ H.edgeSet) = H := by
  ext u v
  simp only [MyGraph.deleteEdges_adj, Set.mem_diff, mem_edgeSet, not_and, not_not]
  constructor <;> intro h'
  · exact h'.2 h'.1
  · exact ⟨le_iff.1 h _ _ h', fun _ ↦ h'⟩



end deleteEdges

section fromEdgeSet
variable {G G' : SpanningGraph V} {s t : Set (Sym2 V)}

abbrev fromEdgeSet (s : Set (Sym2 V)) : SpanningGraph V :=
    ⟨(MyGraph.fromEdgeSet s).toSpanning, by simp⟩

@[simp]
lemma fromEdgeSet_adj {u v : V} : (fromEdgeSet s).Adj u v ↔  s(u, v) ∈ s ∧ u ≠ v := Iff.rfl

@[simp]
lemma edgeSet_fromEdgeSet : (fromEdgeSet s).edgeSet = s \ { e | e.IsDiag } := by
  rw [← MyGraph.edgeSet_fromEdgeSet]
  rfl


end fromEdgeSet


section Decidable

variable (V) (H : SpanningGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]

instance Bot.adjDecidable : DecidableRel (⊥ : SpanningGraph V).Adj :=
  inferInstanceAs <| DecidableRel fun _ _ => False

instance Sup.adjDecidable : DecidableRel (G ⊔ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w => G.Adj v w ∨ H.Adj v w

instance Inf.adjDecidable : DecidableRel (G ⊓ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w => G.Adj v w ∧ H.Adj v w

instance Sdiff.adjDecidable : DecidableRel (G \ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w => G.Adj v w ∧ ¬H.Adj v w


variable [DecidableEq V]

instance Top.adjDecidable : DecidableRel (⊤ : SpanningGraph V).Adj :=
  inferInstanceAs <| DecidableRel fun v w => v ≠ w


instance Compl.adjDecidable : DecidableRel (Gᶜ.Adj) := by
  intro u v
  rw [compl_adj]
  infer_instance



end Decidable
section Finite
open Finset
noncomputable instance [DecidableEq V] [Fintype V] : Fintype (SpanningGraph V) := by
  haveI h : Fintype (MyGraph V) := inferInstance
  apply h.ofInjective _ coe_injective

  -- refine .ofBijective
  --   (α := {H : Finset V × (V → V → Bool) //
  --    (∀ a b, H.2 a b → a ∈ H.1) ∧ (∀ a b, H.2 a b = H.2 b a) ∧ ∀ a, ¬ H.2 a a})
  --   (fun H ↦ ⟨H.1.1, fun a b ↦ H.1.2 a b, @H.2.1, fun a b h ↦ (h ▸ H.2.2.1 a b).symm,
  --     fun a h ↦ (H.2.2.2 _ h)⟩) ⟨?_, fun H ↦ ?_⟩
  -- · rintro ⟨⟨_, _⟩, -⟩ ⟨⟨_, _⟩, -⟩
  --   simp [funext_iff]
  -- · classical
  --   exact ⟨⟨(H.verts.toFinset, fun a b ↦ H.Adj a b), fun a b ↦
  --       by simpa using H.edge_vert, by simp [H.adj_comm]⟩, by simp⟩









variable {G G₁ G₂ : SpanningGraph V} [Fintype G.edgeSet] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]

-- abbrev edgeFinset (G : SpanningGraph V) [Fintype G.edgeSet] := G.edgeFinset

theorem edgeFinset_inj : G₁.edgeFinset = G₂.edgeFinset ↔ G₁ = G₂ := by simp

theorem edgeFinset_subset_edgeFinset : G₁.edgeFinset ⊆ G₂.edgeFinset ↔ G₁ ≤ G₂ := by simp

theorem edgeFinset_ssubset_edgeFinset : G₁.edgeFinset ⊂ G₂.edgeFinset ↔ G₁ < G₂ := by simp

alias ⟨_, edgeFinset_mono⟩ := edgeFinset_subset_edgeFinset

alias ⟨_, edgeFinset_strict_mono⟩ := edgeFinset_ssubset_edgeFinset

attribute [mono] edgeFinset_mono edgeFinset_strict_mono

instance fintypeEdgeSetTop [DecidableEq V] [Fintype V] :
    Fintype (⊤ : SpanningGraph V).edgeSet := by
  rw [coe_top, edgeSet_top]
  infer_instance

theorem card_edgeFinset_top_eq_card_choose_two [DecidableEq V] [Fintype V] :
    #(⊤ : SpanningGraph V).edgeFinset = (Fintype.card V).choose 2 := by
  simp_rw [Set.toFinset_card, coe_top, edgeSet_top, Set.coe_setOf, ← Sym2.card_subtype_not_diag]

section DeleteFar
open Finset
variable {𝕜 : Type*} [Ring 𝕜] [PartialOrder 𝕜]
   {p : SpanningGraph V → Prop} {r r₁ r₂ : 𝕜}

/-- A graph is `r`-*delete-far* from a property `p` if we must delete at least `r` edges from it to
get a graph with the property `p`. -/
def DeleteFar [Fintype G.edgeSet] (p : SpanningGraph V → Prop) (r : 𝕜) : Prop :=
  ∀ ⦃s⦄, s ⊆ G.edgeFinset → p (G.deleteEdges s) → r ≤ #s


theorem deleteFar_iff [Fintype (Sym2 V)] :
    G.DeleteFar p r ↔ ∀ ⦃H : SpanningGraph _⦄ [DecidableRel H.Adj],
      H ≤ G → p H → r ≤ #G.edgeFinset - #H.edgeFinset := by
  classical
  refine ⟨fun h H _ hHG hH ↦ ?_, fun h s hs hG ↦ ?_⟩
  · have := h (sdiff_subset (t := H.edgeFinset))
    simp only [deleteEdges_sdiff_eq_of_le hHG, edgeFinset_mono hHG, card_sdiff,
      card_le_card, coe_sdiff, coe_edgeFinset, Nat.cast_sub] at this
    have h1 : H = G.deleteEdges (G.edgeFinset \ H.edgeFinset) := by
      rw [le_iff] at hHG
      ext u v; simp only [Set.coe_toFinset, MyGraph.deleteEdges_adj, Set.mem_diff, mem_edgeSet,
        not_and, Decidable.not_not]
      constructor <;> intro h'
      · exact ⟨hHG u v h', fun _ ↦ h'⟩
      · exact h'.2 h'.1
    rw [h1,  ← Finset.coe_sdiff] at hH
    exact this hH
  · classical
    simpa [card_sdiff hs, edgeFinset_deleteEdges, -Set.toFinset_card, Nat.cast_sub,
      card_le_card hs] using h (G.deleteEdges_le s) hG


alias ⟨DeleteFar.le_card_sub_card, _⟩ := deleteFar_iff

theorem DeleteFar.mono (h : G.DeleteFar p r₂) (hr : r₁ ≤ r₂) : G.DeleteFar p r₁ := fun _ hs hG =>
  hr.trans <| h hs hG

end DeleteFar

end Finite

variable {G G₁ G₂ : SpanningGraph V}

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
theorem edgeSet_sdiff_sdiff_isDiag (G : SpanningGraph V) (s : Set (Sym2 V)) :
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

section maps

variable {V W X : Type*} {G : SpanningGraph V}

/-! ## Map and comap -/


protected def map (f : V ↪ W) (G : SpanningGraph V) :
  SpanningGraph W := ⟨toSpanning (G.toMyGraph.map f), by simp⟩

@[simp]
lemma map_eq_toSpanning {f : V ↪ W} {G : SpanningGraph V} :
    G.map f = ((G : MyGraph V).map f).toSpanning := rfl

instance instDecidableMapAdj {f : V ↪ W} {a b} [Decidable (Relation.Map G.Adj f f a b)] :
    Decidable ((G.map f).Adj a b) := ‹Decidable (Relation.Map G.Adj f f a b)›

@[simp]
theorem map_adj (f : V ↪ W) (G : SpanningGraph V) {u v : W} :
    (G.map f).Adj u v ↔ ∃ u' v' : V, G.Adj u' v' ∧ f u' = u ∧ f v' = v :=
  Iff.rfl

@[simp]
lemma coe_map (f : V ↪ W) : (G.map f : MyGraph W).Adj = ((G : MyGraph V).map f).Adj := by
  ext ; simp

protected def comap (f : V → W) (G : SpanningGraph W) :
  SpanningGraph V := ⟨toSpanning (G.toMyGraph.comap f), by simp⟩


@[simp]
lemma comap_eq_toSpanning {f : V → W} {G : SpanningGraph W} :
    G.comap f = ((G : MyGraph W).comap f).toSpanning := rfl

@[simp] lemma comap_adj {u v : V} {G : SpanningGraph W} {f : V → W} :
    (G.comap f).Adj u v ↔ G.Adj (f u) (f v) := Iff.rfl


@[simp] lemma comap_comap {G : SpanningGraph X} (f : V → W) (g : W → X) :
  (G.comap g).comap f = G.comap (g ∘ f) := rfl

instance instDecidableComapAdj (f : V → W) (G : MyGraph W) [DecidableRel G.Adj] :
    DecidableRel (G.comap f).Adj := fun _ _ ↦ ‹DecidableRel G.Adj› _ _

@[simp]
theorem comap_map_eq (f : V ↪ W) (G : SpanningGraph V) : (G.map f).comap f = G := by
  ext ; simp


lemma comap_symm (G : SpanningGraph V) (e : V ≃ W) :
    G.comap e.symm.toEmbedding = G.map e.toEmbedding := by
  ext u v; simp?
  constructor <;> intro h
  · use e.symm u, e.symm v, h
    simp
  · obtain ⟨a,b , h1,rfl ,rfl ⟩ := h
    simpa using h1

lemma map_symm (G : SpanningGraph W) (e : V ≃ W) :
    G.map e.symm.toEmbedding = G.comap e.toEmbedding := by rw [← comap_symm, e.symm_symm]

end maps


end SpanningGraph
