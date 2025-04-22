
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

open Finset
@[simp]
lemma degreeIn_insert_eq (s : Set α) (a : α) [DecidablePred (· ∈ s)] [DecidableEq α]
    [Fintype (G.neighborSet a)] :
    G.degreeIn (insert a s) a = #((G.neighborFinset a).filter (· ∈ s)) := by
  rw [← neighborFinsetIn_insert_eq]
  rfl

lemma degreeIn_insert_lt_degree {s : Set α} {a v : α} (h : G.Adj a v) (hv : v ∉ s)
  [DecidablePred (· ∈ s)] [DecidableEq α] [Fintype (G.neighborSet a)] :
    G.degreeIn (insert a s) a < G.degree a := by
  rw [degreeIn_insert_eq, ← card_neighborFinset_eq_degree]
  exact card_lt_card <| Finset.filter_ssubset.2 ⟨v, (G.mem_neighborFinset ..).2 h, hv⟩


variable {t : Set α} [DecidablePred (· ∈ t)]

variable {a : α}  [Fintype (G.neighborSet a)]

lemma degreeIn_mono (h : s ⊆ t) : G.degreeIn s a ≤ G.degreeIn t a := by
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

@[refl,simp]
lemma extends_refl {C₁ : G.PartColoring n s} : C₁.extends C₁ := ⟨subset_refl _,fun _ _ ↦ rfl⟩

variable {u : Set α}
@[trans,simp]
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

/-- We can color `{a}` with any valid color -/
def partColoringOfNotAdj {n : ℕ} {a b : α} (h : ¬ G.Adj a b) (c : Fin n) :
    G.PartColoring n ({a, b} : Set α) where
  toFun := fun _ ↦ c
  map_rel':= by
    intro x y hadj he
    cases hadj.1 <;> cases hadj.2.1 <;> subst_vars
    · exact G.loopless _ hadj.2.2
    · exact h hadj.2.2
    · exact h hadj.2.2.symm
    · exact G.loopless _ hadj.2.2

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
/-

def insertNotAdj {b : α} (C : G.PartialColoring s) (h : ∀ v, v ∈ s → ¬ G.Adj b v) (a : α) :
    G.PartialColoring (insert b s) where
  col   := fun v ↦ ite (v = b) (C a) (C v)
-/

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
lemma PartColoring.insert_extends_not_mem (C₁ : G.PartColoring n s)
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

lemma PartColoring.greedy_extends_not_mem (C₁ : G.PartColoring n s) (ha : a ∉ s)
    [Fintype (G.neighborSet a)] (h) : (C₁.greedy a h).extends C₁ := C₁.insert_extends_not_mem _ ha

lemma PartColoring.greedy_extends (C₁ : G.PartColoring n s) [Fintype (G.neighborSet a)] (h) :
  (C₁.greedy a h).extends (G.partColoringOfSingleton a (Finset.min' _ h)) := C₁.insert_extends _


variable [DecidableRel G.Adj]

lemma PartColoring.nonempty_of_degreeIn_lt (C₁ : G.PartColoring n s) (a : α)
    [Fintype (G.neighborSet a)] (h : G.degreeIn (insert a s) a < n) :
    (((G.neighborFinset a).filter (· ∈ s)).image C₁)ᶜ.Nonempty := by
  contrapose! h
  simp only [Finset.not_nonempty_iff_eq_empty, Finset.compl_eq_empty_iff] at h
  have := Finset.card_image_le (f:=C₁) (s := {x ∈ G.neighborFinset a | x ∈ s})
  simp only [h, Finset.card_univ, Fintype.card_fin] at this
  rwa [degreeIn_insert_eq]


lemma PartColoring.nonempty_of_degreeIn_le_not_inj {u v : α} (C₁ : G.PartColoring n s) (a : α)
    [Fintype (G.neighborSet a)] (h : G.degreeIn (insert a s) a ≤ n) (hus : u ∈ s) (hvs : v ∈ s)
    (hu : G.Adj a u) (hv : G.Adj a v) (hne : u ≠ v) (heq : C₁ u = C₁ v) :
    (((G.neighborFinset a).filter (· ∈ s)).image C₁)ᶜ.Nonempty := by
  cases h.lt_or_eq with
  | inl h => exact nonempty_of_degreeIn_lt C₁ a h
  | inr h =>
  contrapose! hne
  simp only [Finset.not_nonempty_iff_eq_empty, Finset.compl_eq_empty_iff] at hne
  rw [degreeIn_insert_eq, ← Fintype.card_fin n, ← Finset.card_univ] at h
  have h' := congr_arg Finset.card hne
  rw [← h] at h'
  exact Finset.injOn_of_card_image_eq h' (by simpa using ⟨hu, hus⟩) (by simpa using ⟨hv, hvs⟩) heq

open Walk List
/-- We can color greedily along a path to extend a coloring of `s` to a coloring of
`s ∪ p.support.tail.toFinset` if the vertices in the path have bounded degree -/
def PartColoring.of_tail_path {u v : α} {p : G.Walk u v} [LocallyFinite G] (C₁ : G.PartColoring n s)
    (hp : p.IsPath) (hbdd : ∀ x, x ∈ p.support → G.degree x ≤ n)
    (disj : Disjoint s {a | a ∈ p.support}) : G.PartColoring n (s ∪ {a | a ∈ p.support.tail}) := by
  match p with
  | .nil => exact C₁.copy (by simp)
  | .cons h p =>
    rename_i _ v
    rw [cons_isPath_iff] at hp
    simp_rw [support_cons, List.tail, List.mem_cons] at *
    have hd : Disjoint s {a | a ∈ p.support} := disj.mono_right (fun _ hx ↦ Or.inr hx)
    have hs := disj.mono_right (fun _ hx ↦ Or.inl hx)
    let C₂ := C₁.of_tail_path hp.1 (fun x hx ↦ hbdd _ <| Or.inr hx) hd
    have hps : p.support = v :: p.support.tail := by nth_rw 1 [support_eq_cons]
    have hu : u ∉ s ∪ { a | a ∈ p.support.tail} := by
      intro hf; apply hp.2
      have := hf.resolve_left (fun hu ↦ hs.not_mem_of_mem_left hu rfl)
      exact mem_of_mem_tail this
    have h' : G.degreeIn (insert v (s ∪ {a | a ∈ p.support.tail})) v < n :=
      (G.degreeIn_insert_lt_degree h.symm hu).trans_le (hbdd v (Or.inr p.start_mem_support))
    exact (C₂.greedy v (C₂.nonempty_of_degreeIn_lt v h')).copy (by
      ext x; nth_rw 2 [hps]; simp [or_left_comm])

lemma PartColoring.of_tail_path_extends {u v : α} {p : G.Walk u v} [LocallyFinite G]
    (C₁ : G.PartColoring n s) (hp : p.IsPath) (hbdd : ∀ x, x ∈ p.support → G.degree x ≤ n)
    (disj : Disjoint s {a | a ∈ p.support}) : (C₁.of_tail_path hp hbdd disj).extends C₁ := by
  cases p with
  | nil => exact copy_extends <| extends_refl ..
  | cons h p =>
    rename_i _ v
    have hps : p.support = v :: p.support.tail := by nth_rw 1 [support_eq_cons]
    apply copy_extends
    · apply extends_trans
      · apply C₁.of_tail_path_extends hp.of_cons
        · intro _ hx; apply hbdd
          rw [support_cons]
          exact mem_cons_of_mem _ hx
        · simp_rw [support_cons, List.mem_cons] at disj
          apply disj.mono_right (fun _ hx ↦ Or.inr hx)
      · apply greedy_extends_not_mem _
        intro hf
        cases hf with
        | inl hf =>
          apply disj.not_mem_of_mem_left hf
          simp
        | inr hf =>
          have := hp.of_cons.support_nodup ;
          rw [support_eq_cons] at this
          apply this.not_mem (by simpa using hf)
    · rw [support_cons, support_eq_cons]
      ext; simp [or_left_comm]

/-- We can color greedily along a path to extend a coloring of `s` to a coloring of
`s ∪ p.support.toFinset` if the vertices in the path have bounded degree and the start of the path
has two neighbors in `s` that are already colored with the same color. -/
def PartColoring.of_path_not_inj {u v x y : α} {p : G.Walk u v} [LocallyFinite G]
    (C₁ : G.PartColoring n s) (hp : p.IsPath) (hbdd : ∀ x, x ∈ p.support → G.degree x ≤ n)
    (disj : Disjoint s {a | a ∈ p.support}) (hxs : x ∈ s) (hys : y ∈ s) (hux : G.Adj u x)
    (huy : G.Adj u y) (hne : x ≠ y) (heq : C₁ x = C₁ y)  :
    G.PartColoring n (s ∪ {a | a ∈ p.support}) := by
  let C₂ := C₁.of_tail_path hp hbdd disj
  have heq' : C₂ x = C₂ y := by
    rwa [(C₁.of_tail_path_extends hp hbdd disj).2 hxs, (C₁.of_tail_path_extends hp hbdd disj).2 hys]
  exact (C₂.greedy u (C₂.nonempty_of_degreeIn_le_not_inj u
        ((degreeIn_le_degree ..).trans (hbdd u p.start_mem_support)) (Or.inl hxs) (Or.inl hys)
        hux huy hne heq')).copy (by ext; rw [support_eq_cons]; simp [or_left_comm])

lemma PartColoring.of_path_not_inj_extends {u v x y : α} {p : G.Walk u v} [LocallyFinite G]
    (C₁ : G.PartColoring n s) (hp : p.IsPath) (hbdd : ∀ x, x ∈ p.support → G.degree x ≤ n)
    (disj : Disjoint s {a | a ∈ p.support}) (hxs : x ∈ s) (hys : y ∈ s) (hux : G.Adj u x)
    (huy : G.Adj u y) (hne : x ≠ y) (heq : C₁ x = C₁ y) :
    (C₁.of_path_not_inj hp hbdd disj hxs hys hux huy hne heq).extends C₁ := by
  apply copy_extends
  · apply extends_trans (C₁.of_tail_path_extends hp hbdd disj)
    apply (C₁.of_tail_path hp hbdd disj).greedy_extends_not_mem
    intro hf
    cases hf with
    | inl hf => exact disj.not_mem_of_mem_left hf (by simp)
    | inr hf =>
      have := hp.support_nodup ;
      rw [support_eq_cons] at this
      exact this.not_mem (by simpa using hf)
  · nth_rw 2 [support_eq_cons]
    ext; simp [or_left_comm]

open Finset
variable {x₁ x₂ x₃ x₄ xⱼ xᵣ : α} {p : G.Walk xᵣ x₄}
omit [DecidableRel G.Adj] in
/-- Get the vertex set of the coloring we use in the 1st part of Brooks theorem into the appropriate
form -/
theorem Brooks1_aux (hj : xⱼ ∈ p.support) (hj2 : G.Adj xⱼ x₂) :
    {x₁, x₃} ∪ {a | a ∈ (p.dropUntil _ hj).support.tail} ∪
    {a | a ∈ ((p.takeUntil _ hj).concat hj2).reverse.support} =
    {a | a ∈ p.support} ∪ {x₃, x₂, x₁} := by
  rw [Set.pair_comm, support_reverse, support_concat]
  nth_rw 3 [← take_spec p hj]
  rw [support_append , List.concat_eq_append, List.reverse_append, List.reverse_cons]
  ext; aesop

variable {k : ℕ} [LocallyFinite G]
theorem Brooks1_exists {x₁ x₂ x₃ x₄ xⱼ xᵣ : α} {p : G.Walk xᵣ x₄} (hk : 3 ≤ k)
    (hbdd : ∀ v, G.degree v ≤ k) (hp : p.IsPath) (hj : xⱼ ∈ p.support) (hj2 : G.Adj xⱼ x₂)
    (h21 : G.Adj x₂ x₁) (h23 : G.Adj x₂ x₃) (hne : x₁ ≠ x₃) (h13 : ¬ G.Adj x₁ x₃)
    (h1 : x₁ ∉ p.support) (h2 : x₂ ∉ p.support) (h3 : x₃ ∉ p.support) :
   G.PartColorable k ({a | a ∈ p.support} ∪ {x₃, x₂, x₁}) := by
  have hdj := hp.dropUntil hj
  have htp := ((concat_isPath_iff _ hj2).2 ⟨hp.takeUntil hj,
              fun a ↦ h2 ((support_takeUntil_subset p hj) a)⟩).reverse
  have hdis1 : Disjoint {x₁, x₃} {a | a ∈ (p.dropUntil xⱼ hj).support} := by
    simp only [Set.disjoint_insert_left, Set.mem_setOf_eq, Set.disjoint_singleton_left]
    exact ⟨fun h ↦ h1 (p.support_dropUntil_subset hj h) ,
          fun h ↦ h3 (p.support_dropUntil_subset hj h)⟩
  let C₀ := (G.partColoringOfNotAdj h13 ⟨0, show 0 < k by omega⟩)
  let C₁ := C₀.of_tail_path hdj (fun _ _ ↦ hbdd _) hdis1
  have hj213 : C₁ x₁ = C₁ x₃ := by
    have := (C₀.of_tail_path_extends hdj (fun _ _ ↦ hbdd _) hdis1)
    rw [this.2 (by simp), this.2 (by simp)]; rfl
  exact ⟨(C₁.of_path_not_inj htp (fun _ _ ↦ hbdd _) (by
    apply Set.disjoint_union_left.2
    simp only [Walk.reverse_concat, support_cons, support_reverse, List.mem_cons, mem_reverse,
      Set.disjoint_insert_left, Set.mem_setOf_eq, not_or, Set.disjoint_singleton_left]
    refine ⟨⟨⟨h21.symm.ne, fun a ↦ h1 ((support_takeUntil_subset p hj) a)⟩, ⟨h23.symm.ne, fun a ↦ h3
      ((support_takeUntil_subset p hj) a)⟩⟩,?_⟩
    apply Set.disjoint_right.2
    rintro a (rfl | ha)
    · exact fun h ↦   h2 ((support_dropUntil_subset p hj) <| List.mem_of_mem_tail h)
    · rw [← take_spec p hj, append_isPath_iff] at hp; exact fun h ↦ hp.2.2 ha h)
    (by simp) (by simp) h21 h23 hne hj213).copy ((Brooks1_aux hj hj2))⟩

end SimpleGraph
