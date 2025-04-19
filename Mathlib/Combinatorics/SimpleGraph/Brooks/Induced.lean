
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Coloring
set_option linter.style.header false

/-

Develop some API for induced subgraphs as SimpleGraphs, i.e.
`(⊤ : Subgraph G).induce s).spanningCoe`

-/
namespace SimpleGraph
open Subgraph

variable {α : Type*} (G : SimpleGraph α)

abbrev neighborSetIn (s : Set α) (a : α) :=
  ((⊤ : Subgraph G).induce s).spanningCoe.neighborSet a

lemma mem_neighborSetIn {s : Set α} {a v : α} :
  v ∈ G.neighborSetIn s a ↔ a ∈ s ∧ v ∈ s ∧ G.Adj a v := by simp

lemma neighborSetIn_eq_inter_of_mem {s : Set α} {a : α} (ha : a ∈ s) :
    G.neighborSetIn s a = G.neighborSet a ∩ s := by
  aesop

@[simp]
lemma neighborSetIn_insert_eq (s : Set α) (a : α) :
    G.neighborSetIn (insert a s) a = { x | x ∈ s ∧ G.Adj a x} := by
  ext x; rw [mem_neighborSetIn]; simp only [Set.mem_insert_iff, true_or, true_and, Set.mem_setOf_eq,
    and_congr_left_iff, or_iff_right_iff_imp]
  rintro h rfl; exact (G.loopless _ h).elim

section withDecRel

variable [DecidableRel G.Adj] {s : Set α} [DecidablePred (· ∈ s)]

/-- If a graph is locally finite at a vertex, then so is a spanningCoe of a
subgraph of that graph. -/
instance finiteAt {G' : Subgraph G} (v : α) [DecidableRel G'.Adj]
    [Fintype (G.neighborSet v)] : Fintype (G'.neighborSet v) := by
  apply Set.fintypeSubset (G.neighborSet v) (G'.neighborSet_subset v)

instance finiteAtCoe {G' : Subgraph G} (v : α) [DecidableRel G'.Adj]
    [Fintype (G.neighborSet v)] : Fintype (G'.spanningCoe.neighborSet v) := by
  apply Set.fintypeSubset (G.neighborSet v) (G'.neighborSet_subset v)


abbrev neighborFinsetIn (s : Set α) (a : α)[DecidablePred (· ∈ s)]  [Fintype (G.neighborSet a)] :=
  ((⊤ : Subgraph G).induce s).spanningCoe.neighborFinset a

@[simp]
lemma neighborFinsetIn_insert_eq (s : Set α) (a : α) [DecidablePred (· ∈ s)] [DecidableEq α]
    [Fintype (G.neighborSet a)] :
    G.neighborFinsetIn (insert a s) a = (G.neighborFinset a).filter (· ∈ s) := by
  ext x; simp only [mem_neighborFinset, spanningCoe_adj, induce_adj, Set.mem_insert_iff, true_or,
    Subgraph.top_adj, true_and, Finset.mem_filter]
  constructor <;> intro h
  · cases h.1 with
    | inl h' => subst x; exact (G.loopless _ h.2).elim
    | inr h' => exact ⟨h.2, h'⟩
  · exact ⟨Or.inr h.2, h.1⟩

abbrev degreeIn (s : Set α) [DecidablePred (· ∈ s)] (a : α) [Fintype (G.neighborSet a)]  :=
  ((⊤ : Subgraph G).induce s).spanningCoe.degree a

lemma degreeIn_eq (s : Set α) [DecidablePred (· ∈ s)] (a : α) [Fintype (G.neighborSet a)] :
  G.degreeIn s a = ((⊤ : Subgraph G).induce s).degree a := by simp

variable {t : Set α} [DecidablePred (· ∈ t)]

variable {a : α}  [Fintype (G.neighborSet a)]

lemma degreeIn.mono (h : s ⊆ t) : G.degreeIn s a ≤ G.degreeIn t a := by
  rw [degreeIn_eq, degreeIn_eq]
  exact (degree_le' _ _ (induce_mono_right h) a)

variable (a) in
lemma degreeIn_le_degree : G.degreeIn s a ≤ G.degree a := by
  rw [degreeIn_eq]
  exact degree_le _ _

lemma neighborSet_subset_of_degree_le_degreeIn (h : G.degree a ≤ G.degreeIn s a) :
      G.neighborSet a ⊆ s := by
  rw [degree, degreeIn_eq, ← finset_card_neighborSet_eq_degree] at h
  intro v ha
  apply ((⊤ : Subgraph G).induce s).neighborSet_subset_verts a
  rwa [← Set.mem_toFinset, Finset.eq_of_subset_of_card_le (fun v ↦ by simp) h, mem_neighborFinset]

lemma degreeIn_lt_degree {v : α} (hv : v ∈ G.neighborSet a ∧ v ∉ s) :
    G.degreeIn s a < G.degree a :=
  lt_of_le_of_ne (G.degreeIn_le_degree a)
    fun h ↦ hv.2 <| G.neighborSet_subset_of_degree_le_degreeIn h.symm.le hv.1
end withDecRel
variable {s t : Set α} {n : ℕ}
/-- A `PartColoring n s` of `G` is a coloring of all vertices of `G` that is valid on the set `s` -/
abbrev PartColoring (n : ℕ) (s : Set α) :=
  ((⊤ : Subgraph G).induce s).spanningCoe.Coloring (Fin n)

variable {G}
namespace PartColoring

---TODO next
def copy (C: G.PartColoring n s) (h : s = t) :  G.PartColoring n t := h ▸ C


@[simp]
theorem copy_rfl  (C : G.PartColoring n s)  : C.copy rfl = C := rfl

@[simp]
theorem copy_copy {s t u} (C : G.PartColoring n s) (hs : s = t) (ht : t = u) :
    (C.copy hs).copy ht = C.copy (hs.trans ht) := by
  subst_vars
  rfl

def toColoring (C : G.PartColoring n Set.univ) : G.Coloring (Fin n) :=
    ⟨C, fun hab ↦ C.valid (by simpa using hab)⟩

end PartColoring

variable (G)

/-- We can color `{b}` with any valid color -/
def partColoringOfSingleton {m n : ℕ} (h : m < n) (b : α) : G.PartColoring n ({b} : Set α) where
  toFun := fun _ ↦ ⟨_, h⟩
  map_rel':= by simp

/-- `G.PartColorable n s` is the predicate for existence of a `PartColoring n s` of `G`. -/
abbrev PartColorable (n : ℕ) (s : Set α) := ((⊤ : Subgraph G).induce s).spanningCoe.Colorable n

lemma isPartColorable_zero_iff {s : Set α} : G.PartColorable 0 s ↔ IsEmpty α  := by
  rw [PartColorable, colorable_zero_iff]

variable {G} {n : ℕ} [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)]
/--
We can combine colorings of `s` and `t` if `∀ v w, v ∈ s → w ∈ t \ s → G.Adj v w → C₁ v ≠ C₂ w`
-/
def PartColoring.ofUnion (C₁ : G.PartColoring n s) (C₂ : G.PartColoring n t)
    (h : ∀ ⦃v w⦄, v ∈ s → w ∈ t \ s → G.Adj v w → C₁ v ≠ C₂ w) : G.PartColoring n (s ∪ t) where
  toFun := fun v ↦ ite (v ∈ s) (C₁ v) (C₂ v)
  map_rel' := by
      simp only [spanningCoe_adj, induce_adj, Set.mem_union, Subgraph.top_adj, top_adj, ne_eq,
        and_imp]
      intro v w hv' hw' hadj hf
      by_cases hv : v ∈ s
      · by_cases hw : w ∈ t
        · by_cases hws : w ∈ s
          · rw [if_pos hv, if_pos hws] at hf
            apply C₁.valid _ hf
            simpa using ⟨hv, hws, hadj⟩
          · rw [if_pos hv, if_neg hws] at hf
            exact h hv ⟨hw, hws⟩ hadj hf
        · by_cases hws : w ∈ s
          · rw [if_pos hv, if_pos hws] at hf
            apply C₁.valid _ hf
            simpa using ⟨hv, hws, hadj⟩
          · apply hws <| Or.resolve_right hw' hw
      · by_cases hw : w ∈ t
        · by_cases hws : w ∈ s
          · rw [if_neg hv, if_pos hws] at hf
            exact h hws ⟨Or.resolve_left hv' hv, hv⟩ hadj.symm hf.symm
          · rw [if_neg hv, if_neg hws] at hf
            apply C₂.valid _ hf
            simpa using ⟨Or.resolve_left hv' hv, hw, hadj⟩
        · by_cases hws : w ∈ s
          · rw [if_neg hv, if_pos hws] at hf
            apply h hws ⟨(Or.resolve_left hv' hv), hv⟩  hadj.symm hf.symm
          · apply hw
            apply Or.resolve_left hw' hws

lemma  PartColorable.insertNotAdj {b : α} {hs : G.PartColorable n s}
    (h : ∀ v, v ∈ s → ¬ G.Adj b v) : G.PartColorable n (insert b s) := by
  rw [Set.insert_eq]
  have hlt : 0 < n := by
    cases n with
    | zero => rw [isPartColorable_zero_iff] at hs; exfalso; exact IsEmpty.false b
    | succ n => exact Nat.zero_lt_succ _
  obtain ⟨C₂⟩ := hs
  classical
  exact ⟨(G.partColoringOfSingleton hlt b).ofUnion C₂ (by
    simp only [Set.mem_singleton_iff, Set.mem_diff, and_imp]
    rintro _ _ rfl hs _ had _; exact h _ hs had)⟩

variable {a : α}  [DecidableEq α]

/--
If we have an n-coloring of G on s then we can extend it to an n-coloring of `insert a s` unless
-- TO DO this should be on Sets not Finsets, we don't require `a` to have finite degree in G.
-/
lemma not_partColorable_insert (h : ¬ G.PartColorable n (insert a s))
    (C : G.PartColoring n s) : Set.SurjOn C { x | x ∈ s ∧ G.Adj a x} Set.univ := by
  contrapose! h
  rw [Set.SurjOn] at h
  obtain ⟨c, hc⟩ : ∃ c, ∀ x, G.Adj a x ∧ x ∈ s → C x ≠ c:= by
    contrapose! h;
    intro c _
    obtain ⟨x, hx1, hx2⟩ := h c
    simp only [Set.mem_image, Set.mem_setOf_eq]
    use x
    exact ⟨hx1.symm, hx2⟩
  let C' := C.ofUnion (G.partColoringOfSingleton c.prop a) (by
    simp only [Set.mem_diff, Set.mem_singleton_iff, ne_eq, and_imp, forall_eq_apply_imp_iff]
    intro v hv ha hadj
    apply hc _ ⟨hadj.symm ,hv⟩)
  simp [← Set.insert_eq] at C'
  exact ⟨C'⟩

variable [Fintype (G.neighborSet a)] in
lemma PartColorable_le_degreeIn_insert [DecidableRel G.Adj] (C : G.PartColoring n s)
  (h : G.degreeIn (insert a s) a < n) : G.PartColorable n (insert a s) := by
  by_contra! hc
  have := not_partColorable_insert hc C
  have := Finset.card_le_card_of_surjOn _ this
  simp only [Finset.card_univ, Fintype.card_fin] at this
  simp only [degreeIn, degree, neighborFinsetIn_insert_eq] at h
  omega

/-
/-- The color used by the greedy algorithm to extend `C` from `s` to `insert a s` -/
def extend (C : G.PartialColoring s) (a : α) : ℕ := min' _ <| C.unused a

lemma extend_le_degreeOn (C : G.PartialColoring s) (a : α) : C.extend a ≤ G.degreeOn s a := by
  have ⟨h1, _⟩ := mem_sdiff.1 <| min'_mem _ <| C.unused a
  simpa [Nat.lt_succ] using h1

lemma extend_lt_degree (C : G.PartialColoring s) {a v : α} (h1 : G.Adj a v) (h2 : v ∉ s) :
    C.extend a < G.degree a :=
  (extend_le_degreeOn _ _).trans_lt (degreeOn_lt_degree ⟨(mem_neighborFinset ..).2 h1, h2⟩)


lemma extend_eq_degreeOn (h : C.extend a = G.degreeOn s a) :
    ((G.neighborFinset a ∩ s) : Set α).InjOn C := by
  let t := range (G.degreeOn s a + 1)
  let u := (G.neighborFinset a ∩ s).image C
  have hmax := max'_le _ (C.unused a) _ <| fun y hy ↦ mem_range_succ_iff.1 <| (mem_sdiff.1 hy).1
  have hs : ∀ i, i ∈ t \ u → i = G.degreeOn s a :=
    fun i hi ↦ le_antisymm ((le_max' _ _ hi ).trans hmax)  (h ▸ min'_le _ _ hi)
  have h1 := card_eq_one.2 ⟨_, eq_singleton_iff_nonempty_unique_mem.2 ⟨C.unused a, hs⟩⟩
  have : #t - #u ≤ 1 :=  (h1 ▸ le_card_sdiff ..)
  rw [card_range] at this
  have h3 : G.degreeOn s a ≤ #u := by
    rwa [Nat.sub_le_iff_le_add, add_comm 1, Nat.succ_le_succ_iff] at this
  rw [← coe_inter]
  exact injOn_of_card_image_eq <| le_antisymm card_image_le h3

/-- If two neighbors of `a` have the same color in `s` then greedily coloring `a` uses a color
` < G.degreeOn s a` -/
lemma extend_lt_of_not_injOn (hus : u ∈ s) (hvs : v ∈ s) (hu : G.Adj a u) (hv : G.Adj a v)
    (hne : u ≠ v) (hj2 : C u = C v) : C.extend a < G.degreeOn s a := by
    apply (C.extend_le_degreeOn _).lt_of_ne
    intro hf
    apply hne
    apply extend_eq_degreeOn hf <;> simp_all

-/
open Walk
theorem PartColorable.of_tail_path {u v : α} {p : G.Walk u v} [Fintype (G.neighborSet v)]
    (hp : p.IsPath) (hlt : G.PartColorable n s) (hdisj : Disjoint s p.support.toFinset) :
    (G.PartColorable n (s ∪ p.support.tail.toFinset)) := by
  induction p generalizing s with
  | nil => simpa using hlt
  | @cons u v w h p ih =>
    rw [cons_isPath_iff] at hp
    rw [support_cons, List.toFinset_cons, Finset.coe_insert, Set.disjoint_insert_right] at hdisj
    have := ih hp.1 hlt hdisj.2
    obtain ⟨C⟩ := this
    rw [support_cons,List.tail, support_eq_cons, List.toFinset_cons, Finset.coe_insert,
        Set.union_comm, Set.insert_union, Set.union_comm]
    by_contra! hc
    have := not_partColorable_insert hc C
    
    sorry

end SimpleGraph
