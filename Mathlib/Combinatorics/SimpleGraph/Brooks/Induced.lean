
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Coloring
set_option linter.style.header false

/-

Develop some API for induced subgraphs as SimpleGraphs, i.e.
`(⊤ : Subgraph G).induce s).spanningCoe`
and partial colorings of `G` as colorings of these.
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
    G.neighborSetIn (insert a s) a = {x | x ∈ s ∧ G.Adj a x} := by
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


/--
`C₂ : G.PartColoring n t` extends `C₁ : G.PartColoring n s` if `s ⊆ t` and `C₂` agrees with `C₁`
on `s`
-/
abbrev PartColoring.extends (C₂ : G.PartColoring n t) (C₁ : G.PartColoring n s) : Prop :=
  s ⊆ t ∧ ∀ ⦃v⦄, v ∈ s → C₂ v = C₁ v

namespace PartColoring
variable {u : Set α} --[DecidablePred (· ∈ u)]
@[trans]
lemma extends_trans {C₃ : G.PartColoring n u} {C₂ : G.PartColoring n t} {C₁ : G.PartColoring n s}
    (h1 : C₂.extends C₁) (h2: C₃.extends C₂) : C₃.extends C₁ := by
  refine ⟨subset_trans h1.1 h2.1,?_⟩
  intro v hv
  rw [← h1.2 hv, h2.2 (h1.1 hv)]

@[simp]
def copy (C : G.PartColoring n s) (h : s = t) : G.PartColoring n t where
  toFun := C.toFun
  map_rel' := by
    subst h
    exact C.map_rel'

@[simp]
theorem copy_rfl  (C : G.PartColoring n s)  : C.copy rfl = C := rfl

@[simp]
theorem copy_copy {s t u} (C : G.PartColoring n s) (hs : s = t) (ht : t = u) :
    (C.copy hs).copy ht = C.copy (hs.trans ht) := by
  subst_vars
  rfl

@[simp]
lemma copy_def (C: G.PartColoring n s) (h : s = t) {v : α} :
  (C.copy h) v  = C v := rfl

@[simp]
lemma copy_extends {C₂ : G.PartColoring n t} {C₁ : G.PartColoring n s} (hc : C₂.extends C₁)
  {h : t = u} : (C₂.copy h).extends C₁ :=
    ⟨fun _ hx ↦ h ▸ hc.1 hx, fun _ hv ↦ by rw [copy_def]; exact hc.2 hv⟩

def toColoring (C : G.PartColoring n Set.univ) : G.Coloring (Fin n) :=
    ⟨C, fun hab ↦ C.valid (by simpa using hab)⟩

end PartColoring

variable (G)

/-- We can color `{a}` with any valid color -/
def partColoringOfSingleton {n : ℕ} (a : α) (c : Fin n) : G.PartColoring n ({a} : Set α) where
  toFun := fun _ ↦ c
  map_rel':= by simp

@[simp]
lemma partColoringOfSingleton_def {n : ℕ} {a v : α} {c : Fin n} :
  G.partColoringOfSingleton a c v = c := rfl
/-- `G.PartColorable n s` is the predicate for existence of a `PartColoring n s` of `G`. -/
abbrev PartColorable (n : ℕ) (s : Set α) := ((⊤ : Subgraph G).induce s).spanningCoe.Colorable n

lemma isPartColorable_zero_iff {s : Set α} : G.PartColorable 0 s ↔ IsEmpty α  := by
  rw [PartColorable, colorable_zero_iff]

variable {G} {n : ℕ} [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)]

/--
We can combine colorings of `s` and `t` if `∀ v w, v ∈ s → w ∈ t \ s → G.Adj v w → C₁ v ≠ C₂ w`
-/
def PartColoring.union (C₁ : G.PartColoring n s) (C₂ : G.PartColoring n t)
    (h : ∀ ⦃v w⦄, v ∈ s → w ∈ t \ s → G.Adj v w → C₁ v ≠ C₂ w) : G.PartColoring n (s ∪ t) where
  toFun := fun v ↦ ite (v ∈ s) (C₁ v) (C₂ v)
  map_rel' := by
      simp only [spanningCoe_adj, induce_adj, Set.mem_union, Subgraph.top_adj, top_adj, ne_eq,
        and_imp]
      intro v w hv' hw' hadj hf
      by_cases hv : v ∈ s
      · by_cases hws : w ∈ s
        · rw [if_pos hv, if_pos hws] at hf
          exact C₁.valid (by simpa using ⟨hv, hws, hadj⟩) hf
        · by_cases hw : w ∈ t
          · rw [if_pos hv, if_neg hws] at hf
            exact h hv ⟨hw, hws⟩ hadj hf
          · exact hws <| Or.resolve_right hw' hw
      · by_cases hws : w ∈ s
        · rw [if_neg hv, if_pos hws] at hf
          exact h hws ⟨Or.resolve_left hv' hv, hv⟩ hadj.symm hf.symm
        · by_cases hw : w ∈ t
          · rw [if_neg hv, if_neg hws] at hf
            exact C₂.valid (by simpa using ⟨Or.resolve_left hv' hv, hw, hadj⟩) hf
          · exact hw <| Or.resolve_left hw' hws

@[simp]
lemma PartColoring.union_def {v : α} (C₁ : G.PartColoring n s) (C₂ : G.PartColoring n t)
    (h : ∀ ⦃v w⦄, v ∈ s → w ∈ t \ s → G.Adj v w → C₁ v ≠ C₂ w) :
  (C₁.union C₂ h) v = ite (v ∈ s) (C₁ v) (C₂ v) := rfl

@[simp]
lemma PartColoring.union_extends (C₁ : G.PartColoring n s) (C₂ : G.PartColoring n t)
    (h : ∀ ⦃v w⦄, v ∈ s → w ∈ t \ s → G.Adj v w → C₁ v ≠ C₂ w) : (C₁.union C₂ h).extends C₁ := by
  refine ⟨Set.subset_union_left, ?_⟩
  intro v hv
  rw [union_def, if_pos hv]

@[simp]
lemma PartColoring.union_extends_disjoint (hd : Disjoint s t) (C₁ : G.PartColoring n s)
    (C₂ : G.PartColoring n t) (h : ∀ ⦃v w⦄, v ∈ s → w ∈ t \ s → G.Adj v w → C₁ v ≠ C₂ w) :
    (C₁.union C₂ h).extends C₂ := by
  refine ⟨Set.subset_union_right, ?_⟩
  intro v hv
  rw [union_def, if_neg (hd.not_mem_of_mem_right hv)]
variable [DecidableEq α]

/-- The extension of a coloring of `s` to `insert a s` using a color `c` that is not used by a
neighbor of `a` in `s` -/
protected def PartColoring.insert (a : α) (c : Fin n) (C₁ : G.PartColoring n s)
    (h : ∀ ⦃v⦄, v ∈ s → G.Adj a v → C₁ v ≠ c) : G.PartColoring n (insert a s) :=
  ((G.partColoringOfSingleton a c).union C₁ (by
    simp only [Set.mem_singleton_iff, Set.mem_diff, and_imp]
    rintro _ _ rfl h' h1 had h2
    exact h h' had h2.symm)).copy (by simp [Set.union_comm])

variable {a v : α} {c : Fin n}

@[simp]
lemma PartColoring.insert_def (C₁ : G.PartColoring n s) (h : ∀ ⦃v⦄, v ∈ s → G.Adj a v → C₁ v ≠ c) :
    (C₁.insert a c h) v = ite (v = a) c (C₁ v) := by
  rw [PartColoring.insert, copy_def, union_def]
  simp

@[simp]
lemma PartColoring.insert_extends {c : Fin n} (C₁ : G.PartColoring n s)
    (h : ∀ ⦃v⦄, v ∈ s → G.Adj a v → C₁ v ≠ c) :
    (C₁.insert a c h).extends (G.partColoringOfSingleton a c) := copy_extends (union_extends ..)

@[simp]
lemma PartColoring.insert_extends_disjoint (C₁ : G.PartColoring n s)
    (h : ∀ ⦃v⦄, v ∈ s → G.Adj a v → C₁ v ≠ c) (ha : a ∉ s) : (C₁.insert a c h).extends C₁ :=
  copy_extends <| union_extends_disjoint (Set.disjoint_singleton_left.mpr ha) ..

/-- If there is an unused color in the neighborhood of `a` under the coloring of `s` by `C₁` then
we can color `insert a s` greedily. -/
protected abbrev PartColoring.greedy (C₁ : G.PartColoring n s) (a : α) [Fintype (G.neighborSet a)]
    (h : (((G.neighborFinset a).filter (· ∈ s)).image C₁)ᶜ.Nonempty) :
    G.PartColoring n (insert a s) := by
  let c := Finset.min' _ h
  have h' : ∀ ⦃v⦄, v ∈ s → G.Adj a v → C₁ v ≠ c := by
    intro v hv had he
    apply Finset.mem_compl.1 <| Finset.min'_mem _ h
    exact Finset.mem_image.2 ⟨v, Finset.mem_filter.2 ⟨(G.mem_neighborFinset ..).2 had, hv⟩, he⟩
  exact C₁.insert a c h'

variable [DecidableRel G.Adj]

lemma PartColoring.greedy_of_degreeIn_lt (C₁ : G.PartColoring n s) (a : α)
    [Fintype (G.neighborSet a)] (h : G.degreeIn (insert a s) a < n) :
    (((G.neighborFinset a).filter (· ∈ s)).image C₁)ᶜ.Nonempty := by

  sorry
-- -- /--
-- -- If we have an n-coloring of G on s then we can extend it to an n-coloring of `insert a s`
-- unless
-- -- -/
-- -- lemma not_partColorable_insert (h : ¬ G.PartColorable n (insert a s))
-- --     (C : G.PartColoring n s) : Set.SurjOn C {x | x ∈ s ∧ G.Adj a x} Set.univ := by
-- --   contrapose! h
-- --   rw [Set.SurjOn] at h
-- --   obtain ⟨c, hc⟩ : ∃ c, ∀ x, G.Adj a x ∧ x ∈ s → C x ≠ c:= by
-- --     contrapose! h;
-- --     intro c _
-- --     obtain ⟨x, hx1, hx2⟩ := h c
-- --     simp only [Set.mem_image, Set.mem_setOf_eq]
-- --     use x
-- --     exact ⟨hx1.symm, hx2⟩
-- --   let C' := C.union (G.partColoringOfSingleton a c) (by
-- --     simp only [Set.mem_diff, Set.mem_singleton_iff, ne_eq, and_imp, forall_eq_apply_imp_iff]
-- --     intro v hv ha hadj
-- --     apply hc _ ⟨hadj.symm ,hv⟩)
-- --   exact ⟨C'.copy (by simp)⟩

-- variable [Fintype (G.neighborSet a)] in
-- lemma not_partColorable_insert' (h : ¬ G.PartColorable n (insert a s))
--     (C : G.PartColoring n s) : Set.SurjOn C ((G.neighborFinset a).filter (· ∈ s))
--     (Finset.univ : Finset (Fin n)) := by
--   convert not_partColorable_insert h C
--   · ext x; aesop
--   · exact Finset.coe_univ

-- lemma PartColorable_le_degreeIn_insert [DecidableRel G.Adj] (C : G.PartColoring n s)
--   (h : G.degreeIn (insert a s) a < n) : G.PartColorable n (insert a s) := by
--   by_contra! hc
--   have := not_partColorable_insert hc C
--   have := Finset.card_le_card_of_surjOn _ this
--   simp only [Finset.card_univ, Fintype.card_fin] at this
--   simp only [degreeIn, degree, neighborFinsetIn_insert_eq] at h
--   omega

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
theorem PartColorable.of_tail_path {u v : α} {p : G.Walk u v} [LocallyFinite G] (hp : p.IsPath)
    (hbdd : ∀ x, x ∈ p.support → G.degree x ≤ n) (hlt : G.PartColorable n s)
    (disj : Disjoint s p.support.toFinset) : G.PartColorable n (s ∪ p.support.tail.toFinset) := by
  induction p generalizing s with
  | nil => simpa using hlt
  | @cons u v w h p ih =>
    rw [cons_isPath_iff] at hp
    rw [support_cons, List.toFinset_cons, Finset.coe_insert, Set.disjoint_insert_right] at *
    have := ih hp.1 (fun x hx ↦ hbdd _ <| List.mem_cons_of_mem u hx) hlt disj.2
    obtain ⟨C⟩ := this
    rw [List.tail, support_eq_cons, List.toFinset_cons, Finset.coe_insert,
        Set.union_comm, Set.insert_union, Set.union_comm]
    by_contra! hc
    have := Finset.card_le_card_of_surjOn _ (not_partColorable_insert' hc C)
    simp only [Finset.card_univ, Fintype.card_fin, List.coe_toFinset, Set.mem_union,
      Set.mem_setOf_eq] at this
    have hv : G.degree v ≤ n := hbdd v (List.mem_cons_of_mem _ p.start_mem_support)
    rw [← card_neighborFinset_eq_degree] at hv
    have := Finset.eq_of_subset_of_card_le (Finset.filter_subset ..) (hv.trans this)
    have hu : u ∉ s ∪ p.support.tail.toFinset := by
      intro hf;
      cases hf with
      | inl hf => exact (disj.1 hf).elim
      | inr hf =>
        apply hp.2 (by apply List.mem_of_mem_tail; simpa using hf)
    have hu' : u ∈ G.neighborFinset v := by
      rw [mem_neighborFinset]; exact h.symm
    apply hu
    rw [Finset.ext_iff] at this
    have := (this u).2 hu'
    rw [Finset.mem_filter] at this
    simpa using this.2

open List
theorem PartColorable.of_path_notInj {u v x y : α} {p : G.Walk u v} [LocallyFinite G]
    (hp : p.IsPath) (hbdd : ∀ x, x ∈ p.support → G.degree x ≤ n) (C : G.PartColoring n s)
    (hxs : x ∈ s) (hys : y ∈ s) (hux : G.Adj u x) (huy : G.Adj u y) (hne : x ≠ y)
    (heq : C x = C y) (disj : Disjoint s p.support.toFinset) :
    G.PartColorable n (s ∪ p.support.toFinset) := by
  have hnx := fun hf ↦ Set.disjoint_left.1 disj hxs <| mem_toFinset.2 <| mem_of_mem_tail hf
  have hny := fun hf ↦ Set.disjoint_left.1 disj hys <| mem_toFinset.2 <| mem_of_mem_tail hf
  have hn := PartColorable.of_tail_path hp hbdd (by exact ⟨C⟩) disj
  intro a
  by_cases ha : a ∈ p.support
  · have := Greedy_of_tail_path hbdd hp hlt hdisj
    rw [support_eq_cons, Greedy_cons]
    by_cases hu : a = u
    · rw [if_pos hu]
      have heq : (C.Greedy p.support.tail) x = (C.Greedy p.support.tail) y := by
        rwa [Greedy_not_mem hnx, Greedy_not_mem hny]
      apply (extend_lt_of_not_injOn (mem_union_left _ hxs) (mem_union_left _ hys)
        hux huy hne heq).trans_le <| (degreeOn_le_degree ..).trans (hbdd _)
    ·  exact (if_neg hu) ▸ (this a)
  · rw [Greedy_not_mem ha]
    exact hlt a

  sorry


end SimpleGraph
